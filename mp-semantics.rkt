#lang racket

(require redex/reduction-semantics
         (only-in unstable/match))

(provide (all-defined-out))

; -----------------------------------------------------
; -------------------- SYNTAX -------------------------
; -----------------------------------------------------
(define-language lang
  (ctp (thread ...))
  (thread ([ploc cmd] ... ⊥))
  (cmd (assume e)
       (assert e)
       (x := e)
       (sendi aid src dst e ploc number)
       (recvi aid dst x ploc)
       (wait aid)
       )
  (move-⊥ move-list
          ⊥)
  (move-list ((dst src) ... ⊥))
 
  (aid-⊥ aid
         ⊥)

  (e (op e e)
     cmd ;; Fix semantics to always return a value for a cmd (default value) (< (wait aid) (x := e)) allowed?
     x
     v)
  (op =
      -
      +
      >
      <
      >=
      <=
      /=)
  (v number
     bool)
  (bool true
        false)
  (ploc id)
  (src ep)
  (dst ep)
  (ep number)
  (aid id)
  (x id)
  (id variable-not-otherwise-mentioned)
  (loc number)
  
  ; evaluation syntax
  
  ; Pending sends indexed firsts by dst and then src
  (send-set ([aid -> v] ...))
  (from-set mt
            (from-set [src -> send-set])) 
  (pending-s mt
                 (pending-s [dst -> from-set]))
  
  ; Pending receives indexed by dst
  (recv-set ([aid -> x] ...))
  (pending-r mt
                 (pending-r [dst -> recv-set]))
  
  
  
  
  ; Map of aid -> ep 
  (aid-map ((aid ep) ... ))
  
  ; Heap
  (h mt
     (h [loc -> v]))
  
  ; Local environment
  (eta mt
       (eta [x -> loc]))

  ; Status of trace
  (status success    ;everything's fine
          failure    ;assertion failed
          infeasable ;assumption failed
          error)     ;impossible to execute
  
  (machine-state (h eta aid-map pending-s pending-r ctp status))
  (queue-state (pending-s move-⊥ status))
  (expr-state (h eta aid-map pending-s pending-r e status k))
  (k ret
     (assert * -> k)
     (assume * -> k)
     (x := * -> k)
     (op * e -> k)
     (op v * -> k)
     )

   (ep-⊥ ep
         ⊥)
  
  )

;

; -----------------------------------------------------
; ------------- EXPRESSION REDUCTIONS -----------------
; -----------------------------------------------------

(define (apply-reduction-relation** red t)
  (match (apply-reduction-relation red t)
    [(list)
     t]
    [(list t)
     (apply-reduction-relation** red t)]))

(define machine-reductions
  (reduction-relation
   lang
   #:domain machine-state

   (--> (h eta aid-map pending-s pending-r 
           (thread_0 ... 
            ([ploc_0 cmd_0] [ploc_1 cmd_1] ... ⊥)
            thread_2 ...) status)
        (h_pr eta_pr aid-map_pr pending-s_pr pending-r_pr  
              (thread_0 ... ([ploc_1 cmd_1] ... ⊥) thread_2 ...)
               status_pr)
        ;(where false (check-pending-send cmd_0 pending-r aid-map pending-s))
       ; "Machine Step"
        (where (h_pr eta_pr aid-map_pr pending-s_pr pending-r_pr 
                     e status_pr ret)
               ,(apply-reduction-relation** expr-reductions
                                            (term (h eta aid-map pending-s
                                                     pending-r cmd_0
                                                     status ret))))
        )
   
   (--> (h eta aid-map pending-s pending-r q-set
           (thread_0 ... 
            ([ploc_0 cmd_0] [ploc_1 cmd_1] ... ⊥)
            thread_2 ...) status)
        (h eta aid-map pending-s pending-r q-set 
              (thread_0 ... ([ploc_0 cmd_0] [ploc_1 cmd_1] ... ⊥) thread_2 ...)
               status)
        "Machine Step for checking pending send"
        (where true (check-pending-send cmd_0 pending-r aid-map pending-s))
        ;"Machine Step"
        )
   ))
   

(define expr-reductions
  (reduction-relation
   lang
   #:domain expr-state
   
   (--> (h eta aid-map pending-s pending-r  x status k)
        (h eta aid-map pending-s pending-r  v status k)
        "Lookup Variable"
        (where v (h-lookup h (eta-lookup eta x))))
   
   (--> (h eta aid-map pending-s pending-r  (op e_0 e) status k)
        (h eta aid-map pending-s pending-r  e_0 status (op * e -> k))
        "Expr l-operand")
   (--> (h eta aid-map  pending-s pending-r  v status (op * e -> k))
        (h eta aid-map  pending-s pending-r  e status (op v * -> k))
        "Expr r-operand")
   (--> (h eta aid-map pending-s pending-r  v_r status (op v_l * -> k))
        (h eta aid-map pending-s pending-r  v_res status k)
        "Binary Operation Eval"
        (where v_res (apply-op op v_l v_r)))
   
   (--> (h eta aid-map pending-s pending-r  (assume e) status k)
        (h eta aid-map pending-s pending-r  e status (assume * -> k ))
        "Assume Pull Out Expr")
   (--> (h eta aid-map pending-s pending-r  v status (assume * -> k)) 
        (h eta aid-map pending-s pending-r  v status_pr k) 
        "Assume Cmd"
        (where status_pr (check-assume v status)))
   
   ;;Negate expression.
   (--> (h eta aid-map pending-s pending-r  (assert e) status k)
        (h eta aid-map pending-s pending-r  e status (assert * -> k))
        "Assert Pull Out Expr")
   (--> (h eta aid-map pending-s pending-r  v status (assert * -> k)) 
        (h eta aid-map pending-s pending-r  v status_pr k)
        "Assert Eval"
        (where status_pr (check-assert v status)))
   
   (--> (h eta aid-map pending-s pending-r  (x := e) status k)
        (h eta aid-map pending-s pending-r  e status (x := * -> k))
        "Assign Pull Out Expr")
   (--> (h eta aid-map pending-s pending-r  v status (x := * -> k))
        (h_pr eta aid-map pending-s pending-r  v status k)
        "Assign Expr"
        (where h_pr (h-extend* h [(eta-lookup eta x) -> v])))
   
   ;;Adds sendi cmd to aid-map and pending-s. - VALIDATED
   (--> (h eta ([aid_x ep_x] ...) pending-s pending-r 
           (sendi aid src dst x ploc number) status k)
        (h eta ([aid src] [aid_x ep_x] ...) pending-s_pr pending-r 
           true status k)
        "Sendi Cmd x -> v"
        (where v (h-lookup h (eta-lookup eta x)))
        (where pending-s_pr (add-send pending-s [aid -> src dst v])))
   
   ;;Adds recvi cmd to aid-map and pending-r. - VALIDATED
   (--> (h eta ([aid_x ep_x] ...) pending-s pending-r 
           (recvi aid dst x ploc) status k)
        (h eta ([aid dst] [aid_x ep_x] ...) pending-s pending-r_pr  
           true status k)
        "Recvi Cmd0"
        (where pending-r_pr (add-recv pending-r [aid -> dst x])))
   
   ;;aid returns false in function find-recv meaning it is not a recv but a send 
   (--> (h eta aid-map pending-s pending-r  (wait aid) status k)
        (h eta aid-map pending-s pending-r  true status k)
        "Sendi Wait Cmd"
        (where false (find-recv pending-r aid) ))
       
   (--> (h eta aid-map pending-s pending-r  (wait aid_r) 
           status k)
        (h_pr eta aid-map_pr pending-s_pr pending-r_pr  true 
              status k)
        "Recvi Wait Cmd"
        ;;check if aid_r is a receive
        (where true (find-recv pending-r aid_r) )
        ;;get this receive from aid-map
        (where (aid-map_0 dst) (get-ep aid-map aid_r))
        ;;remove this receive from pending-r    
        (where (variable pending-r_pr) (remove-pending-recv dst aid_r pending-r)) 
        ;;randomly find a send in pending-s, remove it from pending-s  --needs to be improved for "randomize"
        (where (aid_s v_s pending-s_pr)
               (find-available-send dst pending-s))
         ;;remove this send from aid-map
        (where (aid-map_pr src_s) (get-ep aid-map_0 aid_s))
        ;;match the receive and the send by assign variable x a value v  
        (where h_pr
               (h-extend* h [(eta-lookup eta variable) -> v_s]))
        )
   ))



; -----------------------------------------------------
; ------------------ HELPER FUNCTIONS -----------------
; -----------------------------------------------------

;; TODO: write function to update the SMT problem that can manage ⊥ return when the last structure is empty on a 
;; first send or receive call.

(define-metafunction lang
  get-last-send/replace : last src dst aid -> (last aid-⊥)
  [(get-last-send/replace ([ep-⊥_0 ep_0 aid_0] ... [src_s dst_r aid_s-last] [ep-⊥_1 ep_1 aid_1] ...) src_s dst_r aid_s)
   (([ep-⊥_0 ep_0 aid_0] ... [src_s dst_r aid_s] [ep-⊥_1 ep_1 aid_1] ...) aid_s-last)]
  [(get-last-send/replace ([ep-⊥_0 ep_0 aid_0] ...) src_s dst_r aid_s)
   (([ep-⊥_0 ep_0 aid_0] ... [src_s dst_r aid_s]) ⊥)])

(define-metafunction lang
  check-assert : v status -> status
  [(check-assert true status) status]
  [(check-assert false success) failure]
  [(check-assert false infeasable) infeasable]
  [(check-assert false error) error])

(define-metafunction lang
  check-assume : v status -> status
  [(check-assume true status) status]
  [(check-assume false success) infeasable]
  [(check-assume false failure) infeasable]
  [(check-assume false error) error])

(define (->bool v)
  (if v
      'true
      'false))

(define-metafunction lang
  h-max : h -> number
  [(h-max mt) -1]
  [(h-max (h [loc -> v]))
   ,(max (term loc) (term (h-max h)))])

(define-metafunction lang
  storelike-lookup : any any -> any
  [(storelike-lookup mt any_0)
   error]
  [(storelike-lookup (any_0 [any_t -> any_ans]) any_t)
   any_ans]
  [(storelike-lookup (any_0 [any_k -> any_v]) any_t)
   (storelike-lookup any_0 any_t)
   (side-condition (not (equal? (term any_k) (term any_t))))])


;;does `() mean an empty list
(define-metafunction lang
  storelike-outer : any -> (any any)
  [(storelike-outer mt) `((term error) (term error))]
  [(storelike-outer (any_0 [any_t -> any_ans])) `((term any_ans) (term any_t))]
  [(storelike-outer (any_0 [any_t -> '()])) (storelike-outer any_0)])

(define (id-<= a b)
  (string<=? (symbol->string a) (symbol->string b)))

(define (storelike-extend <= storelike k v)
  (match storelike
    ['mt `(mt [,k -> ,v])]
    [`(,storelike [,ki -> ,vi])
     (cond
       [(equal? k ki)
        `(,storelike [,ki -> ,v])]
       [(<= k ki)
        `(,(storelike-extend <= storelike k v) [,ki -> ,vi])]
       [else
        `((,storelike [,ki -> ,vi]) [,k -> ,v])])]))     

(define (storelike-extend* <= storelike extend*)
  (match extend*
    ['() storelike]
    [`([,k -> ,v] . ,extend*)
     (storelike-extend* <= (storelike-extend <= storelike k v) extend*)]))

(define-metafunction lang
  h-lookup : h loc -> v
  [(h-lookup h loc)
   (storelike-lookup h loc)])

(define-metafunction lang
  h-extend* : h [loc -> v] ... -> h
  [(h-extend* h [loc -> v] ...)
   ,(storelike-extend* <= (term h) (term ([loc -> v] ...)))])

(define-metafunction lang
  pending-r-extend* : pending-r [dst -> recv-set] ... -> pending-r
  [(pending-r-extend* pending-r [dst -> recv-set] ...)
   ,(storelike-extend* <= (term pending-r) (term ([dst -> recv-set] ...)))])

(define-metafunction lang
  from-set-extend* : from-set [src -> send-set] ... -> from-set
  [(from-set-extend* from-set [src -> send-set] ...)
   ,(storelike-extend* <= (term from-set) (term ([src -> send-set] ...)))])

(define-metafunction lang
  pending-s-extend* : pending-s [dst -> from-set] ... -> pending-s
  [(pending-s-extend* pending-s [dst -> from-set] ...)
   ,(storelike-extend* <= (term pending-s) (term ([dst -> from-set] ...)))])

(define-metafunction lang
  eta-lookup : eta x -> loc
  [(eta-lookup eta x)
   (storelike-lookup eta x)])

;return the size of a set
(define (get-size set)
  (match set
    [`() 0]
    [`([,key -> ,v]) 1]
    [`(,s [,key -> ,v]) (+ 1 (get-size (list s)))]))

;;Finds [key -> value] in set, and returns value
(define (get-value set key)
  (match set
    ['mt 'null]
    [`(,s [,k -> ,value]) (if (equal? k key) value (get-value s key))]))

(define (get-first set)
  (match set
    ['mt 'null]
    [`(,s [,k -> ,value]) `(,value ,k)]))

; get the key given a value for the set
(define (get-key set key)
  (match set
    ['mt 'null]
    [`(,s [,ep -> ,rset]) 
     (let ([res (get-key-pr rset key)]) 
       (if (equal? res 'null) (get-key s key) res))]
    ;[`(,s [,ep -> `(,rset [,rkey -> ,var])]) 'null]
    ))

(define (get-key-pr rset key)
  (match rset
    [`() 'null]
    [`([,rkey -> ,var]) (if (equal? rkey key) rkey 'null)]
    [`(,s [,rkey -> ,var]) (if (equal? rkey key) rkey (get-key-pr (list s) key))]))

;;Finds [key -> value] and modifies to [key -> v] or makes new entry,
;;then returns the new set
(define (set-value set key v)
  (match set
    ['mt `(mt [,key -> ,v])]
    [`(,s [,k -> ,value]) 
     (if (equal? k key) `(,s [,k -> ,v]) 
         (list (set-value s key v) `[,k -> ,value]))]))


;remove the first item in the set
(define (remove-first set)
  (match set
    [`() `(() 'null 'null)]
    [`(,s [,k ->,value]) `((,s) ,k ,value)]
    [`([,k -> ,value]) `(() ,k ,value)]))

(define (get-by-key set key)
  (match set
    [`(,s [,k ->,value]) 
     (if (equal? k key) `((,s) ,k ,value) 
                         (get-by-key s key))]
    [`([,k -> ,value])
     (if (equal? k key) `(,empty ,k ,value) 
                        `(([,k -> ,value]) 'null 'null))]))

(define (remove-pending-send set dst src)
  (match set
    ['mt 'mt]
    [`(,s [,d ->,fromset]) 
     (if (equal? d dst) 
         (let ([new-pending-fromset (remove-fromset fromset src)])
           (if (equal? new-pending-fromset 'mt)
               s
               `(,s [,d ->,new-pending-fromset])           
         ))
        `(,(remove-pending-send s dst src) [,d ->,fromset]))]
    ))

(define (remove-fromset set src)
  (match set
    ['mt 'mt]
    [`(,s [,sr ->,pending-sends])
     (if (equal? sr src) 
         (let ([new-pending-ss (remove-first-send pending-sends)])
           (if (equal? (get-size new-pending-ss) 0)
               s
               `(,s [,sr ->,new-pending-ss])           
         ))
        `(,(remove-fromset s src) [,sr ->,pending-sends]))]
))

(define (remove-first-send set)
  (match set
    [`(,s [,k ->,value]) `(,s)]
    [`([,k ->,value]) `()]
    [`() `()]))

(define (remove-pending-receive pending-rs dst aid)
  (match pending-rs
    ['mt 'mt]
    [`(,s [,d ->,pending-receives])
     (if (equal? d dst) 
         (let ([new-pending-rs (remove-receive-by-key pending-receives aid)])
           (if (equal? (get-size new-pending-rs) 0)
                s
               `(,s [,d ->,new-pending-rs])           
         ))
        `(,(remove-pending-receive s dst aid) [,d ->,pending-receives]))]
    )
)

(define (remove-receive-by-key pending-r aid)
  (match pending-r
    [`(,s [,a ->,value]) 
     (if (equal? a aid) `(,s) 
                         (remove-receive-by-key s aid))]
    [`([,a ->,value]) 
     (if (equal? a aid) `() 
                        `([,a ->,value]))]
    [`() `()]
    ))


(define-metafunction lang
  get-ep : aid-map aid -> (aid-map ep) 
  [(get-ep ([aid_x ep_x] ... [aid_y ep_y] [aid_z ep_z] ...) aid_y)
   (([aid_x ep_x] ... [aid_z ep_z] ...) ep_y)])



;
(define-metafunction lang
  get-recv : pending-r dst -> (pending-r [aid -> x])
  [(get-recv pending-r dst) 
   ,(let ([res (get-value (term pending-r) (term dst))])
      (list
       (set-value (term pending-r) (term dst) (cdr res))
       (car res)))])

(define-metafunction lang
  get-send : pending-s src dst -> (pending-s [aid -> v])
  [(get-send pending-s src dst) 
   ,(let ([fset (get-value (term pending-s) (term dst))])
             (let ([res (get-value fset (term src))])
      (list
       (set-value (term pending-s) (term dst)
                  (set-value fset (term src) (cdr res)))
       (car res))))])

;if aid is in pending-r, return true; otherwise, return false
(define-metafunction lang
  find-recv : pending-r aid -> bool
  [(find-recv pending-r aid)
   ,(let ([res (get-key (term pending-r) (term aid))])
      (if (equal? res 'null)
          (term false)
          (term true)))]) 


(define-metafunction lang
   check-pending-send : cmd pending-r aid-map pending-s -> bool
   [(check-pending-send (assume e) pending-r aid-map pending-s) ,(term false)]
   [(check-pending-send (assert e) pending-r aid-map pending-s) ,(term false)]
   [(check-pending-send (x := e) pending-r aid-map pending-s) ,(term false)]
   [(check-pending-send (sendi aid src dst e ploc number) pending-r aid-map pending-s) ,(term false)]
   [(check-pending-send (recvi aid dst x ploc) pending-r aid-map pending-s) ,(term false)]
   [(check-pending-send (wait aid) pending-r ([aid_x ep_x] ... [aid ep] [aid_y ep_y] ...) pending-s) 
    ,(let ([res (get-key (term pending-r) (term aid))])
      (if (equal? res 'null)
          (term false)
          (let ([available-sends (get-value (term pending-s) (term ep))])
             (if (equal? available-sends 'null)
             (term true)
             (term false))))) 
   ]
   )

(define-metafunction lang
  remove-pending-recv : dst aid pending-r -> (x pending-r_pr)
  [(remove-pending-recv dst aid pending-r)
   ,(let ([recv-set (get-value (term pending-r) (term dst))])
      (let ([rmd-recv-set (get-by-key recv-set (term aid))])
        (let ([new-pending-r 
              (remove-pending-receive (term pending-r) (term dst) (term aid))])
        `(,(caddr rmd-recv-set) ,new-pending-r 
          ;,(term (pending-r-extend*  pending-r [,(term dst) -> ,(car rmd-recv-set)]))
          )))
      )])


;;TODO: finding "randomsrc" instead of "firstsrc"
(define-metafunction lang
  find-available-send : dst pending-s -> (aid v pending-s)
  [(find-available-send dst pending-s)
   ,(let ([sendTodst-list (get-value (term pending-s) (term dst))])
      (let ([firstsrc-list (get-first  sendTodst-list)])
        (let ([rmd-send-set (remove-first (term ,(car firstsrc-list)))])
          (let ([new-pending-s 
                 (remove-pending-send (term pending-s) (term dst) (cadr firstsrc-list))
                 ])
          `(,(cadr rmd-send-set) ,(caddr rmd-send-set) ,new-pending-s 
          ; ,(term (pending-s-extend*  pending-s [,(term dst) -> [,(cadr firstsrc-list) -> (mt (0 -> ()))]
           ;,(term (from-set-extend*  ,sendTodst-list [,(cadr firstsrc-list) -> ,(car rmd-send-set)]))
           ;]))
           )
          )
          )
        )
      )])

;(define-metafunction lang
;  remove-send-by-key : dst src aid pending-s -> pending-s
;  [(remove-send-by-key dst src aid pending-s)
;   (let ([new-pending-s (remove-pending-send (term pending-s) (term dst) (cadr rmd-send-set))])
;          `(,(cadr rmd-send-set) ,(caddr rmd-send-set)  ,new-pending-s
          ; ,(term (pending-s-extend*  pending-s [,(term dst) -> [,(cadr firstsrc-list) -> (mt (0 -> ()))]
           ;,(term (from-set-extend*  ,sendTodst-list [,(cadr firstsrc-list) -> ,(car rmd-send-set)]))
           ;]))
  ;         )
 ;         )])


          

(define-metafunction lang
  add-recv : pending-r (aid -> dst x) -> pending-r
  [(add-recv pending-r (aid -> dst x))
   ,(let ([recv-set (get-value (term pending-r) (term dst))])
      (if (or (equal? recv-set 'null) (empty? recv-set))
          (set-value (term pending-r) (term dst) 
                     (list `(,(term aid) -> ,(term x))))
          (set-value (term pending-r) (term dst)
                     (my-append recv-set `(,(term aid) -> ,(term x))))))])

;add send to q-set
(define-metafunction lang
  add-send-pr :  dst aid v q-set status -> q-set
  [(add-send-pr dst aid v q-set status)
   ,(if (equal?  (term status) (term error)) 
        (term q-set)
        (let ([send-set (get-value (term q-set) (term dst))])
          (if (or (equal? send-set 'null) (empty? send-set))
              (set-value (term q-set) (term dst)
                         (list `(,(term aid) -> ,(term v))))
              (set-value (term q-set) (term dst)
                         (my-append send-set `(,(term aid) -> ,(term v)))))))])


;get the destination send command from the send-set, and mark all the visited sends. 
(define-metafunction lang
  mark-get-value : send-set recv-set aid h eta status -> (send-set recv-set aid h status)
  [(mark-get-value send-set recv-set aid h eta status)
   ,(match `(,(term send-set) ,(term recv-set))
      [`(() ()) `(,(term send-set) ,(term recv-set) 'null ,(term h) (term error))]
      [`(([,aid_s -> ,v ]) ([,aid_r -> ,x]))
     (if(equal? (term status) (term error))
          `(,(term send-set) ,(term recv-set) 'null ,(term h) ,(term error)) 
          (if (equal? aid_r (term aid))
              (if (equal? v (term ⊥))
               `(() () ,aid_s ,(term h) ,(term status))
               `(() () ,aid_s  ,(term (h-extend*  h [(eta-lookup eta ,x) -> ,v])) ,(term status))
               )
            `(,(term send-set) ,(term recv-set) 'null ,(term h) ,(term error))
           ))]
      [`((,s [,aid_s -> ,v ]) (,r [,aid_r -> ,x]))
       (if(equal? (term status) (term error))
          `(,(term send-set) ,(term recv-set) 'null ,(term h) ,(term error)) 
          (if (equal? aid_r (term aid))
              (if (equal? v (term ⊥))
               `(,(list s) ,(list r) ,aid_s ,(term h) ,(term status))
               `(,(list s) ,(list r) ,aid_s  ,(term (h-extend*  h [(eta-lookup eta ,x) -> ,v])) ,(term status))
               )
            (let ([res (term (mark-get-value ,(list s) ,(list r) aid h eta status))])
                (if (equal? v (term ⊥))
                    `(,(append (car res) `([,aid_s -> ,(term ⊥) ])) ,(append (cadr res) `([,aid_r -> ,x])) ,(caddr res) ,(cadddr res) ,(car(cddddr res)))
                    `(,(append (car res) `([,aid_s -> ,(term ⊥) ])) ,(append (cadr res) `([,aid_r -> ,x])) ,(caddr res) ,(term (h-extend* ,(cadddr res) [(eta-lookup eta ,x) -> ,v])) ,(car(cddddr res)))
                    ))
           ))]
      )])

;get the matched send given dst and the recv command, remove them from pending-r and q-set, and mark all the visited sends.
(define-metafunction lang
  get-mark-remove : h eta pending-r q-set dst aid status -> (h aid pending-r q-set status)
  [(get-mark-remove h eta pending-r q-set dst aid status)
   ,(let ([recv-set (get-value (term pending-r) (term dst))])
      (let ([send-set (get-value (term q-set) (term dst))])
      (if (or (equal? (get-size recv-set) 0) (equal? (get-size send-set) 0))
        `(,(term h) 'null ,(term pending-r) ,(term q-set) ,(term error))
        (if (equal? (get-size  recv-set) (get-size  send-set))
            (let ([res (term (mark-get-value ,send-set ,recv-set aid h eta status))])
              (if (equal? (car(cddddr res)) (term error))
                  `(,(term h) 'null ,(term pending-r) ,(term q-set) ,(term error))
                  `(,(cadddr res) ,(caddr res) ,(set-value (term pending-r) (term dst) (cadr res)) ,(set-value (term q-set) (term dst) (car res)) ,(car(cddddr res)))))
            `(,(term h) 'null ,(term pending-r) ,(term q-set) ,(term error))))))
   ])


(define-metafunction lang
  add-send : pending-s [aid -> src dst v] -> pending-s
  [(add-send pending-s [aid -> src dst v])
   ,(let ([fset (get-value (term pending-s) (term dst))])
      (if (equal? 'null fset)
          (set-value (term pending-s) (term dst) 
                     (set-value (term mt) (term src)
                                (list `(,(term aid) -> ,(term v)))))
          (let ([send-set (get-value fset (term src))])
            (if (or (equal? send-set 'null) (empty? send-set))
                (set-value (term pending-s) (term dst)
                           (set-value fset (term src)
                                      (list `(,(term aid) -> ,(term v)))))
                (set-value (term pending-s) (term dst)
                           (set-value fset (term src) 
                                      (my-append send-set `(,(term aid) -> ,(term v)))))))))])


(define-metafunction lang
  remove-send : src dst pending-s status -> (pending-s aid v status)
  [(remove-send src dst pending-s status)
   ,(let ([fset (get-value (term pending-s) (term dst))])
      (if (equal? 'null fset)
          `(,(term pending-s) 'null 0 (term error))
          (let ([send-set (get-value fset(term src))])
            (if (or (equal? send-set 'null) (empty? send-set))
                `(,(term pending-s) 'null 0 (term error))
                (let ([send-entry (remove-first send-set)])
                          `(,(set-value (term pending-s)(term dst)
                           (set-value fset (term src)
                                      (car send-entry))) ,(cadr send-entry) ,(caddr send-entry) ,(term status)))))))])

(define-metafunction lang
  make-send : aid src dst x ploc number -> any
  [(make-send aid src dst x ploc number) 
   (and (= (select aid ep) dst) (= (select aid event) ploc)
        (= (select aid value) x) (= (select aid id) number))])

(define-metafunction lang
  make-recv : aid dst x ploc -> any
  [(make-recv aid dst x ploc) (and (= (select aid ep) dst) (= (select aid event) ploc)
                                   (= (select aid var) x))])
(define-metafunction lang
  add-po : smt ploc_0 ploc_1 ... -> smt
  [(add-po smt ploc_0)
   (add-last-po smt ploc_0)]
  [(add-po ((any_d ...) (any_a ...)) ploc_0 ploc_1 ploc_2 ...) 
   (((define ploc_0 :: int) any_d ...)((HB ploc_0 ploc_1) any_a ...))])

(define-metafunction lang
  add-last-po : smt ploc_0 -> smt
  [(add-last-po ((any_d ...) asrts) ploc_0) (((define ploc_0 :: int) any_d ...) asrts)])

(define-metafunction lang
  apply-op : op v_1 v_2 -> v_r
  [(apply-op - number_l number_r) ,(- (term number_l) (term number_r))]
  [(apply-op + number_l number_r) ,(+ (term number_l) (term number_r))]
  [(apply-op /= bool_l bool_r) ,(->bool (not (symbol=? (term bool_l) (term bool_r))))]
  [(apply-op /= number_l number_r) ,(->bool (not (= (term number_l) (term number_r))))]
  [(apply-op = bool_l bool_r) ,(->bool (symbol=? (term bool_l) (term bool_r)))]
  [(apply-op = number_l number_r) ,(->bool (= (term number_l) (term number_r)))]
  [(apply-op > number_l number_r) ,(->bool (> (term number_l) (term number_r)))]
  [(apply-op < number_l number_r) ,(->bool (< (term number_l) (term number_r)))]
  [(apply-op >= number_l number_r) ,(->bool (>= (term number_l) (term number_r)))]
  [(apply-op <= number_l number_r) ,(->bool (<= (term number_l) (term number_r)))])

(define (my-append l x)
  (match l
    ['() (append x l)]
    [`([,k ->,value]) (list x `[,k -> ,value])]
    [`(,s [,k ->,value]) (append (my-append (list s) x) `([,k -> ,value]))]))

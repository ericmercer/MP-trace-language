#lang racket

(require redex/reduction-semantics
         (only-in unstable/match ==))

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
  (move-list ((dst src) ... ⊥))
  (move-⊥ move-list
          ⊥)
  (trace-entry (ploc move-⊥))
  (trace (trace-entry ...))
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
  
  ; Endpoint queues
  (v-⊥ v
       ⊥)
  (q ([aid -> v-⊥] ...))
  (q-set mt 
         q-set [dst -> q])
  
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
  
  (machine-state (h eta aid-map pending-s pending-r q-set ctp trace status smt))
  (queue-state (pending-s q-set (src,dst) status))
  (expr-state (h eta aid-map pending-s pending-r q-set push-move-⊥ e status k smt))
  (k ret
     (assert * -> k)
     (assume * -> k)
     (x := * -> k)
     (op * e -> k)
     (op v * -> k)
     )
  ; Add last to the state and update appropriately...just before smt...

  (smt (defs asrts)
       )
  (defs (any ...))
  (asrts (any ...))
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
   
   ; The HB relations and definitions enable the SMT solver
   ; to generate a total order on the error traces. If you remove
   ; the orders, then you need to resolve the partial order to
   ; create an actual error trace.
   
   ; first reduce the queue state if the trace-entry is a queue movement command
   ; second reduce the expr state
   (--> (h eta aid-map pending-s pending-r q-set
           (thread_0 ... 
            ([ploc_0 cmd_0] [ploc_1 cmd_1] ... ⊥)
            thread_2 ...)
           ([ploc_0 move-⊥] trace-entry_1 ...) status smt)
        (h_pr eta_pr aid-map_pr pending-s_prpr pending-r_pr q-set_prpr 
              (thread_0 ... ([ploc_1 cmd_1] ... ⊥) thread_2 ...)
              (trace-entry_1 ...) status_prpr smt_prpr)
        "Machine Step for queue movement"
        (where (pending-s_pr q-set_pr ⊥ status_pr)
               ,(apply-reduction-relation** queue-reductions
                                            (term (pending-s q-set move-⊥ status))))
       ; "Machine Step"
        (where (h_pr eta_pr aid-map_pr pending-s_prpr pending-r_pr q-set_prpr
                     e status_prpr ret smt_pr)
               ,(apply-reduction-relation** expr-reductions
                                            (term (h eta aid-map pending-s_pr
                                                     pending-r q-set_pr cmd_0
                                                     status_pr ret smt))))
        (where smt_prpr (add-po smt_pr ploc_0 ploc_1 ...)))
   
   ))


(define queue-reductions
  (reduction-relation
   lang
   #:domain queue-state
   
   (--> (pending-s q-set ((src dst) (src_0 dst_0) ... ⊥) status)
        (pending-s_pr q-set_pr ((src_0 dst_0) ... ⊥) status_pr)
        "Process queue movement"
        (where (pending-s_pr aid v status_pr) (remove-send src dst pending-s status))
        (where q-set_pr (add-send-pr dst aid v q-set status_pr)))
   
))
   

(define expr-reductions
  (reduction-relation
   lang
   #:domain expr-state
   
   (--> (h eta aid-map pending-s pending-r q-set x status k smt)
        (h eta aid-map pending-s pending-r q-set v status k smt)
        "Lookup Variable"
        (where v (h-lookup h (eta-lookup eta x))))
   
   (--> (h eta aid-map pending-s pending-r q-set (op e_0 e) status k smt)
        (h eta aid-map pending-s pending-r q-set e_0 status (op * e -> k) smt)
        "Expr l-operand")
   (--> (h eta aid-map  pending-s pending-r q-set v status (op * e -> k) smt)
        (h eta aid-map  pending-s pending-r q-set e status (op v * -> k) smt)
        "Expr r-operand")
   (--> (h eta aid-map pending-s pending-r q-set v_r status (op v_l * -> k) smt)
        (h eta aid-map pending-s pending-r q-set v_res status k smt)
        "Binary Operation Eval"
        (where v_res (apply-op op v_l v_r)))
   
   (--> (h eta aid-map pending-s pending-r q-set (assume e) status k
           (defs (any ...)))
        (h eta aid-map pending-s pending-r q-set e status (assume * -> k )
           (defs (e any ...)))
        "Assume Pull Out Expr")
   (--> (h eta aid-map pending-s pending-r q-set v status (assume * -> k) smt)
        (h eta aid-map pending-s pending-r q-set v status_pr k smt)
        "Assume Cmd"
        (where status_pr (check-assume v status)))
   
   ;;Negate expression and add it to the SMT assertions.
   (--> (h eta aid-map pending-s pending-r q-set (assert e) status k
            (defs (any ...)))
        (h eta aid-map pending-s pending-r q-set e status (assert * -> k)
           (defs ((not e) any ...)))
        "Assert Pull Out Expr")
   (--> (h eta aid-map pending-s pending-r q-set v status (assert * -> k) smt)
        (h eta aid-map pending-s pending-r q-set v status_pr k smt)
        "Assert Eval"
        (where status_pr (check-assert v status)))
   
   (--> (h eta aid-map pending-s pending-r q-set (x := e) status k
           (defs (any ...)))
        (h eta aid-map pending-s pending-r q-set e status (x := * -> k)
           (defs ((= x e) any ...)))
        "Assign Pull Out Expr")
   (--> (h eta aid-map pending-s pending-r q-set v status (x := * -> k) smt)
        (h_pr eta aid-map pending-s pending-r q-set v status k smt)
        "Assign Expr"
        (where h_pr (h-extend* h [(eta-lookup eta x) -> v])))
   
   ;;Adds sendi cmd to aid-map and pending-s. - VALIDATED
   (--> (h eta ([aid_x ep_x] ...) pending-s pending-r q-set
           (sendi aid src dst x ploc number) status k ((any_d ...) (any_a ...)))
        (h eta ([aid src] [aid_x ep_x] ...) pending-s_pr pending-r q-set
           true status k ((any_0 any_d ...) (any_1 any_a ...)))
        "Sendi Cmd x -> v"
        (where v (h-lookup h (eta-lookup eta x)))
        (where any_0 (define aid :: send))
        (where any_1 (make-send aid src dst x ploc number))
        (where pending-s_pr (add-send pending-s [aid -> src dst v])))
   
   ;;Adds recvi cmd to aid-map and pending-r. - VALIDATED
   (--> (h eta ([aid_x ep_x] ...) pending-s pending-r q-set
           (recvi aid dst x ploc) status k ((any_d ...) (any_a ...)))
        (h eta ([aid dst] [aid_x ep_x] ...) pending-s pending-r_pr q-set 
           true status k ((any_0 any_d ...) (any_1 any_a ...)))
        "Recvi Cmd0"
        (where pending-r_pr (add-recv pending-r [aid -> dst x]))
        (where any_0 (define aid :: recv))
        (where any_1 (make-recv aid dst x ploc)))
   
   (--> (h eta aid-map pending-s pending-r q-set (wait aid) status k smt)
        (h eta aid-map pending-s pending-r q-set true status k smt)
        "Sendi Wait Cmd"
        (where (find-recv aid) 'false))
   
   ;;Match on the receive wait
   ;; TODO: add the last structure to the state and update the smt problem and last as
   ;;       1) Add to smt (MATCH aid_r0 aid_s0) -- done
   ;;       2) Get and remove from last [src_r dst_r aid_s_last] and [dst_r aid_r_last] last
   ;;       3) Add to smt (HB (select aid_s_last match_p0) (select aid_s match_po)) -- done
   ;;       4) Add to last [src_r dst_r aid_s] and {dst_r aid_r]
   ;;       5) Complete any prior matches, if needed...
   ;; TODO: update all the other rules to ignore last (largely)
   
   
   ; Step of match: 
   ; 1)get the aid_r from pending-r, mark the corresponding send in q-set with "1"(visited)
   ; 2)add to smt structure
   ; 3)find-recv checks if aid_r is the recv command
   (--> (h eta aid-map pending-s pending-r q-set (wait aid_r) 
           status k (defs (any_a ...)))
        (h_pr eta aid-map_pr pending-s pending-r_pr q-set_pr true 
              status_prpr k
              (defs ((HB (select aid-⊥_s-last match_po) (select aid_s match_po))
                     (MATCH aid_r aid_s) any_a ...)))
        "Recvi Wait Cmd"
        (where (find-recv aid_r) 'true)
        (where (aid-map_0 dst_r) (get-ep aid-map aid_r))
        ;; get recv and corresponding send command, mark each send in front of the destination send (by set variable "mark" to 1)
        (where (h_pr aid_s pending-r_pr q-set_pr status_pr) 
               (get-mark-remove h eta aid-map pending-r q-set dst_r aid_r status))
        
        
        
;        (where (pending-r_pr [aid_r0 -> x_r]) (get-recv pending-r dst_r))
;        (where (aid-map_pr src_s) (get-ep aid-map_0 aid_s))
;        (where (pending-s_pr [aid_s0 -> v_s]) (get-send pending-s src_s dst_r))
;        (where h_pr (h-extend* h [(eta-lookup eta x_r) -> v_s]))
;        
;        (where (last_pr aid-⊥_s-last) (get-last-send/replace last src_s dst_r aid_s))
        
        )
   ))



; -----------------------------------------------------
; ------------------ HELPER FUNCTIONS -----------------
; -----------------------------------------------------

;; TODO: write function to update the SMT problem that can manage ⊥ return when the last structure is empty on a 
;; first send or receive call.

;(define-metafunction lang
;  get-last-send/replace : last src dst aid -> (last aid-⊥)
;  [(get-last-send/replace ([ep-⊥_0 ep_0 aid_0] ... [src_s dst_r aid_s-last] [ep-⊥_1 ep_1 aid_1] ...) src_s dst_r aid_s)
;   (([ep-⊥_0 ep_0 aid_0] ... [src_s dst_r aid_s] [ep-⊥_1 ep_1 aid_1] ...) aid_s-last)]
;  [(get-last-send/replace ([ep-⊥_0 ep_0 aid_0] ...) src_s dst_r aid_s)
;   (([ep-⊥_0 ep_0 aid_0] ... [src_s dst_r aid_s]) ⊥)])

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
  eta-lookup : eta x -> loc
  [(eta-lookup eta x)
   (storelike-lookup eta x)])

;return the size of a set
(define (get-size set)
  (match set
    ['mt 0]
    [`(,s [,key -> ,v]) (+ 1 (get-size s))]))

;;Finds [key -> value] in set, and returns value
(define (get-value set key)
  (match set
    ['mt 'null]
    [`(,s [,k -> ,value]) (if (equal? k key) value (get-value s key))]))

; get the key given a value for the set
(define (get-key set value)
  (match set
    ['mt 'null]
    [`(,s [,key -> ,v]) (if (equal? v value) key (get-key s value))]))

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
    ['mt `mt]
    [`(,s [,k ->,value]) `(,s ,k ,value)]))


;(define-metafunction lang
;  mark-get-value : send-set recv-set aid h eta status -> (send-set recv-set aid h status)
;  [(mark-get-value send-set recv-set aid h eta status)
;  ,(match `(,(term send-set) ,(term recv-set)) 
;    [`('mt 'mt) `(,(term send-set) ,(term recv-set) 'null ,(term h) (term error))]
;    [`(`(,s [,aid_s -> (,v ,mark)]) `(,r [,aid_r -> ,x]))
;       (if(equal? (term status) (term error))
;          `(,(term send-set) ,(term recv-set) 'null ,(term h) (term error)) 
;          (if (equal? aid_r (term aid))
;              (if (equal? mark 1)
;               `(,s ,r ,aid_s ,(term h) ,(term status))
;               `(,s ,r ,aid_s ,(term (h-extend* h [(eta-lookup eta x) -> v])) ,(term status))
;               )
;            (let ([res (mark-get-value s r aid h eta status)])
;                (if (equals? mark 1)
;                    `(,(list (car res) `[,aid_s -> (,v ,mark)]) ,(list (cadr res) `[,aid_r -> ,x]) ,(caddr res) ,(cadddr res) ,(car(cddddr res)))
;                    `(,(list (car res) `[,aid_s -> (,v 1)]) ,(list (cadr res) `[,aid_r -> ,x]) ,(caddr res) ,(h-extend* (cadddr res) [(eta-lookup eta x) -> v]) ,(car(cddddr res)))
;                    ))
;           ))])])


;get the destination send command from the send-set, and mark all the visited sends. 
(define (mark-get-value send-set recv-set aid h eta status)
  (match `(,send-set ,recv-set) 
    [`('mt 'mt) `(,send-set ,recv-set 'null ,h 'error)]
    [`(`(,s [,aid_s -> (,v ,mark)]) `(,r [,aid_r -> ,x]))
       (if(equal? status 'error)
          `(,send-set ,recv-set 'null ,h 'error) 
          (if (equal? aid_r aid)
              (if (equal? mark 1)
               `(,s ,r ,aid_s ,h ,status)
               `(,s ,r ,aid_s ,(term (h-extend* h [(eta-lookup eta x) -> v])) ,status)
               )
            (let ([res (mark-get-value s r aid h eta status)])
                (if (equal? mark 1)
                    `(,(list (car res) `[,aid_s -> (,v ,mark)]) ,(list (cadr res) `[,aid_r -> ,x]) ,(caddr res) ,(cadddr res) ,(car(cddddr res)))
                    `(,(list (car res) `[,aid_s -> (,v 1)]) ,(list (cadr res) `[,aid_r -> ,x]) ,(caddr res) ,(term (h-extend* (cadddr res) [(eta-lookup eta x) -> v])) ,(car(cddddr res)))
                    ))
           ))]))


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
  find-recv : aid -> bool
  [(find-recv aid)
   ,(let ([res (get-key (term pending-r) (term aid))])
      (if (equal? res 'null)
          'false
          'true))]) 

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
  add-send-pr : q-set (aid -> dst v) status -> q-set
  [(add-send-pr q-set (aid -> dst v) status)
   ,(if (equal?  (term status) (term error)) 
        (term q-set)
        (let ([send-set (get-value (term q-set) (term dst))])
          (if (or (equal? send-set 'null) (empty? send-set))
              (set-value (term q-set) (term dst)
                         (list `(,(term aid) -> (,(term v) 0))))
              (set-value (term q-set) (term dst)
                         (my-append send-set `(,(term aid) -> (,(term v) 0)))))))])

;get the matched send given dst and the recv command, remove them from pending-r and q-set, and mark all the visited sends.
(define-metafunction lang
  get-mark-remove : h eta aid-map pending-r q-set dst aid status -> (h aid pending-r q-set status)
  [(get-mark-remove aid-map pending-r q-set dst aid status)
   ,(let ([recv-set (get-value (term pending-r) (term dst))])
      (let ([send-set (get-value (term q-set) (term dst))])
      (if (or (equal? (get-size (term recv-set)) 0) (equal? (get-size (term send-set)) 0))
        `(,(term h) 'null ,(term pending-r) ,(term q-set) ,(term error))
        (if (equal? (get-size (term recv-set)) (get-size (term send-set)))
            (let ([res (mark-get-value (term send-set) (term recv-set) (term aid) (term h) (term eta) (term status))])
              (if (equal? (car(cddddr res)) (term error))
                  `(,(term h) 'null ,(term pending-r) ,(term q-set) ,(term error))
                  `(,(cadddr res) ,(caddr res) ,(cadr res) ,(car res) ,(car(cddddr res)))))
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
                                      (car send-entry))) ,(cadr send-entry) ,(cddr send-entry) ,(term status)))))))])

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
    (if (empty? l)
        (cons x l)
        (cons (car l) (my-append (cdr l) x))))
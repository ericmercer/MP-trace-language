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
       (wait aid aid)
       )
  (trace (trace-entry ...))
  (aid-⊥ aid
         ⊥)
  (trace-entry (ploc aid-⊥))
  (e (op e e)
     cmd
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
  (send-set ([aid -> v] ...))
  (from-set mt
            (from-set [src -> send-set])) 
  (ep-send-calls mt
                 (ep-send-calls [dst -> from-set]))
  
  ; ep in the receive set is a destination end-point.
  ; We are waiting at that end-point for a message.
  ; Queue of receives called form a single end-point.
  (recv-set ([aid -> x] ...))
  (ep-recv-calls mt
                 (ep-recv-calls [dst -> recv-set]))
  
  (aid-map ((aid ep) ... ))
  (h mt
     (h [loc -> v]))
  (eta mt
       (eta [x -> loc]))
  (status status-temp
          status-final)
  (status-temp
          success-temp    ;everything's fine
          failure-temp    ;assertion failed
          infeasable-temp ;assumption failed
          error-temp)     ;impossible to execute
  
  (status-final success-final
                failure-final
                infeasable-final
                error-final)
  (machine-state (h eta aid-map ep-send-calls ep-recv-calls ctp trace status smt))
  (expr-state (h eta aid-map ep-send-calls ep-recv-calls aid-⊥ e status k smt))
  (k ret
     (assert * -> k)
     (assume * -> k)
     (x := * -> k)
     (op * e -> k)
     (op v * -> k)
     (match * [aid -> dst x] -> k)
     (match [aid -> src dst v] [aid -> dst x] -> k)
     )
  (smt (defs asrts)
       )
  (defs (any ...))
  (asrts (any ...))
  )


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
   
   ; Modify traces to be (ploc ⊥) or (ploc aid) -- done
   ; Add new state entry in expression machine that is (⊥ or aid) -- done
   ; Rewrite machine rules to one rule on the new expression state -- done
   ; Rewrite expression rules to see the new member of expression state -- done
   ; Rewrite the wait rules to distinguish on ⊥ for wait-send and aid for wait-receive
   ;;;; Simplify to have a single "wait" command in grammar -- done (sortof)
   ;;;; Use the extra state member to track through the lookups and final match
   (--> (h eta aid-map ep-send-calls ep-recv-calls  
           (thread_0 ... 
            ([ploc_0 cmd_0] [ploc_1 cmd_1] ... ⊥)
            thread_2 ...)
           ([ploc_0 aid-⊥] trace-entry_1 ...) status smt)
        (h_pr eta_pr aid-map_pr ep-send-calls_pr ep-recv-calls_pr 
              (thread_0 ... ([ploc_1 cmd_1] ... ⊥) thread_2 ...)
              (trace-entry_1 ...) status_pr smt_prpr)
        "Machine Step"
        (where (h_pr eta_pr aid-map_pr ep-send-calls_pr ep-recv-calls_pr aid-⊥_pr
                     e status_pr ret smt_pr)
               ,(apply-reduction-relation** expr-reductions
                                            (term (h eta aid-map ep-send-calls
                                                     ep-recv-calls aid-⊥ cmd_0
                                                     status ret smt))))
        (where smt_prpr (add-po smt_pr ploc_0 ploc_1 ...)))
   ))

(define expr-reductions
  (reduction-relation
   lang
   #:domain expr-state
   
   (--> (h eta aid-map ep-send-calls ep-recv-calls ⊥ x status k smt)
        (h eta aid-map ep-send-calls ep-recv-calls ⊥ v status k smt)
        "Lookup Variable"
        (where v (h-lookup h (eta-lookup eta x))))
   
   (--> (h eta aid-map ep-send-calls ep-recv-calls ⊥ (op e_0 e) status k smt)
        (h eta aid-map ep-send-calls ep-recv-calls ⊥ e_0 status (op * e -> k) smt)
        "Expr l-operand")
   (--> (h eta aid-map  ep-send-calls ep-recv-calls ⊥ v status (op * e -> k) smt)
        (h eta aid-map  ep-send-calls ep-recv-calls ⊥ e status (op v * -> k) smt)
        "Expr r-operand")
   (--> (h eta aid-map ep-send-calls ep-recv-calls ⊥ v_r status (op v_l * -> k) smt)
        (h eta aid-map ep-send-calls ep-recv-calls ⊥ v_res status k smt)
        "Binary Operation Eval"
        (where v_res (apply-op op v_l v_r)))
   
   
   (--> (h eta aid-map ep-send-calls ep-recv-calls ⊥ (assume e) status k
           (defs (any ...)))
        (h eta aid-map ep-send-calls ep-recv-calls ⊥ e status (assume * -> k )
           (defs (e any ...)))
        "Assume Pull Out Expr")
   (--> (h eta aid-map ep-send-calls ep-recv-calls ⊥ v status (assume * -> k) smt)
        (h eta aid-map ep-send-calls ep-recv-calls ⊥ v status_pr k smt)
        "Assume Cmd"
        (where status_pr (check-assume v status)))
   
   ;;Negate expression and add it to the SMT assertions.
   (--> (h eta aid-map ep-send-calls ep-recv-calls ⊥ (assert e) status k
           (defs (any ...)))
        (h eta aid-map ep-send-calls ep-recv-calls ⊥ e status (assert * -> k)
           (defs ((not e) any ...)))
        "Assert Pull Out Expr")
   (--> (h eta aid-map ep-send-calls ep-recv-calls ⊥ v status (assert * -> k) smt)
        (h eta aid-map ep-send-calls ep-recv-calls ⊥ v status_pr k smt)
        "Assert Eval"
        (where status_pr (check-assert v status)))
   
   (--> (h eta aid-map ep-send-calls ep-recv-calls ⊥ (x := e) status k
           (defs (any ...)))
        (h eta aid-map ep-send-calls ep-recv-calls ⊥ e status (x := * -> k)
           (defs ((= x e) any ...)))
        "Assign Pull Out Expr")
   (--> (h eta aid-map ep-send-calls ep-recv-calls ⊥ v status (x := * -> k) smt)
        (h_pr eta aid-map ep-send-calls ep-recv-calls ⊥ v status k smt)
        "Assign Expr"
        (where h_pr (h-extend* h [(eta-lookup eta x) -> v])))
   
   ;;Adds sendi cmd to aid-map and ep-send-calls. - VALIDATED
   (--> (h eta ([aid_x ep_x] ...) ep-send-calls ep-recv-calls ⊥ 
           (sendi aid src dst x ploc number) status k ((any_d ...) (any_a ...)))
        (h eta ([aid src] [aid_x ep_x] ...) ep-send-calls_pr ep-recv-calls ⊥
           true status k ((any_0 any_d ...) (any_1 any_a ...)))
        "Sendi Cmd x -> v"
        (where v (h-lookup h (eta-lookup eta x)))
        (where any_0 (define aid :: send))
        (where any_1 (make-send aid src dst x ploc number))
        (where ep-send-calls_pr (add-send ep-send-calls [aid -> src dst v])))
   
   ;;Adds recvi cmd to aid-map and ep-recv-calls. - VALIDATED
   (--> (h eta ([aid_x ep_x] ...) ep-send-calls ep-recv-calls ⊥
           (recvi aid dst x ploc) status k ((any_d ...) (any_a ...)))
        (h eta ([aid dst] [aid_x ep_x] ...) ep-send-calls ep-recv-calls_pr ⊥ 
           true status k ((any_0 any_d ...) (any_1 any_a ...)))
        "Recvi Cmd0"
        (where ep-recv-calls_pr (add-recv ep-recv-calls [aid -> dst x]))
        (where any_0 (define aid :: recv))
        (where any_1 (make-recv aid dst x ploc)))
   
   ;;Eat the send wait. - VALIDATED
   (--> (h eta aid-map ep-send-calls ep-recv-calls ⊥ (wait aid) status k smt)
        (h eta aid-map ep-send-calls ep-recv-calls ⊥ true status k smt)
        "Eat Sendi Wait")
   
   ;;Take the recv out of aid-map. - VALIDATED
   (--> (h eta ([aid_x ep_x] ... [aid_r dst_0] [aid_y ep_y] ...) 
           ep-send-calls ep-recv-calls aid_s
           (wait aid_r) status k 
           ((any_d ...) (any_a ...)))
        (h eta ([aid_x ep_x] ... [aid_y ep_y] ...)
           ep-send-calls ep-recv-calls_pr ⊥
           (wait aid_r aid_s) status (match * [aid_r0 -> dst_0 x_r] -> k) 
           ((any_d ...) (any_a ...)))
        "Recvi Wait Cmd 0"
        (where (ep-recv-calls_pr [aid_r0 -> x_r]) (get-recv ep-recv-calls dst_0)))
   
   ;;Take the send out of aid-map VALIDATED
   (--> (h eta ([aid_x ep_x] ... [aid_s src_0] [aid_y ep_y] ...)
           ep-send-calls ep-recv-calls ⊥
           (wait aid_r aid_s) status
           (match * [aid_r0 -> dst_r x_r] -> k) smt)
        (h eta ([aid_x ep_x] ... [aid_y ep_y] ...)
           ep-send-calls_pr ep-recv-calls ⊥
           (wait aid_r aid_s) status
           (match [aid_s0 -> src_0 dst_r v_s] [aid_r0 -> dst_r x_r] -> k) smt)
        "Recvi Wait Cmd 1"
        (where (ep-send-calls_pr [aid_s0 -> v_s]) (get-send ep-send-calls src_0 dst_r)))
   
   ;;Then we do the match
   (--> (h eta aid-map ep-send-calls ep-recv-calls ⊥ (wait aid_r aid_s) 
           status (match [aid_s0 -> src dst v] [aid_r0 -> dst x] -> k)
           (defs (any_a ...)))
        (h_pr eta aid-map ep-send-calls ep-recv-calls ⊥ true 
              status_pr k 
              (defs ((MATCH aid_r0 aid_s0) any_a ...)))
        "Recvi Wait Cmd 2"
        (where h_pr (h-extend* h [(eta-lookup eta x) -> v]))
        (where status_pr ,(if (and (equal? (term aid_r) (term aid_r0)) 
                                   (equal? (term aid_s) (term aid_s0))) 
                              (term status) (term error-temp))))
   ))



; -----------------------------------------------------
; ------------------ HELPER FUNCTIONS -----------------
; -----------------------------------------------------

(define (fetch-from-set aid set)
  (term (sendi send1 ep0 ep1 a)))

(define-metafunction lang
  check-assert : v status -> status
  [(check-assert true status) status]
  [(check-assert false success-temp) failure-temp]
  [(check-assert false infeasable-temp) infeasable-temp]
  [(check-assert false error-temp) error-temp])

(define-metafunction lang
  check-assume : v status -> status
  [(check-assume true status) status]
  [(check-assume false success-temp) infeasable-temp]
  [(check-assume false failure-temp) infeasable-temp]
  [(check-assume false error-temp) error-temp])

(define (->bool v)
  (if v
      'true
      'false))

#;(define-metafunction lang
    length-bug : (any ...) -> number
    [(length-bug (any_0 ...))
     ,(length (term (any_0 ...)))])

(define-metafunction lang
  h-max : h -> number
  [(h-max mt) -1]
  [(h-max (h [loc -> v]))
   ,(max (term loc) (term (h-max h)))])

(define-metafunction lang
  h-malloc : h -> number
  [(h-malloc h)
   ,(add1 (term (h-max h)))])

(define-metafunction lang
  storelike-lookup : any any -> any
  [(storelike-lookup mt any_0)
   error-temp]
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

(define-metafunction lang
  eta-extend* : eta [x -> loc] ... -> eta
  [(eta-extend* eta [x -> loc] ...)
   ,(storelike-extend* id-<= (term eta) (term ([x -> loc] ...)))])

;;Finds [key -> value] in set, and returns value
(define (get-value set key)
  (match set
    ['mt 'null]
    [`(,s [,k -> ,value]) (if (equal? k key) value (get-value s key))]))

;;Finds [key -> value] and modifies to [key -> v] or makes new entry,
;;then returns the new set
(define (set-value set key v)
  (match set
    ['mt `(mt [,key -> ,v])]
    [`(,s [,k -> ,value]) 
     (if (equal? k key) `(,s [,k -> ,v]) 
         (list (set-value s key v) `[,k -> ,value]))]))

(define-metafunction lang
  get-recv : ep-recv-calls dst -> (ep-recv-calls [aid -> x])
  [(get-recv ep-recv-calls dst) 
   ,(let ([res (get-value (term ep-recv-calls) (term dst))])
      (list
       (set-value (term ep-recv-calls) (term dst) (cdr res))
       (car res)))])

(define-metafunction lang
  get-send : ep-send-calls src dst -> (ep-send-calls [aid -> v])
  [(get-send ep-send-calls src dst) 
   ,(letrec ([fset (get-value (term ep-send-calls) (term dst))]
             [res (get-value fset (term src))])
      (list
       (set-value (term ep-send-calls) (term dst)
                  (set-value fset (term src) (cdr res)))
       (car res)))])

(define-metafunction lang
  add-recv : ep-recv-calls (aid -> dst x) -> ep-recv-calls
  [(add-recv ep-recv-calls (aid -> dst x))
   ,(let ([recv-set (get-value (term ep-recv-calls) (term dst))])
      (if (or (equal? recv-set 'null) (empty? recv-set))
          (set-value (term ep-recv-calls) (term dst) 
                     (list `(,(term aid) -> ,(term x))))
          (set-value (term ep-recv-calls) (term dst)
                     (my-append recv-set `(,(term aid) -> ,(term x))))))])

(define-metafunction lang
  add-send : ep-send-calls [aid -> src dst v] -> ep-send-calls
  [(add-send ep-send-calls [aid -> src dst v])
   ,(let ([fset (get-value (term ep-send-calls) (term dst))])
      (if (equal? 'null fset)
          (set-value (term ep-send-calls) (term dst) 
                     (set-value (term mt) (term src)
                                (list `(,(term aid) -> ,(term v)))))
          (let ([send-set (get-value fset (term src))])
            (if (or (equal? send-set 'null) (empty? send-set))
                (set-value (term ep-send-calls) (term dst)
                           (set-value fset (term src)
                                      (list `(,(term aid) -> ,(term v)))))
                (set-value (term ep-send-calls) (term dst)
                           (set-value fset (term src) 
                                      (my-append send-set `(,(term aid) -> ,(term v)))))))))])

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

(define-metafunction lang
  finalize-status : status -> status
  [(finalize-status success-temp) success-final]
  [(finalize-status failure-temp) failure-final]
  [(finalize-status infeasable-temp) infeasable-final]
  [(finalize-status error-temp) error-final])

(define (my-append l x)
    (if (empty? l)
        (cons x l)
        (cons (car l) (my-append (cdr l) x))))
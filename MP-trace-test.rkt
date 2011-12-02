 #lang racket
(require redex/reduction-semantics
         "MP-trace.rkt")

(define-syntax-rule (test-term-equal lhs rhs)
  (test-equal (term lhs) (term rhs)))

(define-syntax-rule (test-->* red st mt ...)
  (test-predicate (-test-->* red mt ...) st))

(define ((-test-->* red . mts) st)
  (define not-seen (make-hash))
  (for ([mt (in-list mts)])
    (hash-set! not-seen mt #t))
  (let loop ([t st])
    (hash-remove! not-seen t)
    (or (zero? (hash-count not-seen))
        (let ([ts (apply-reduction-relation red t)])
          (ormap loop ts)))))

(define (step-->n red st n)
  (let loop ([t st] [i n])
    (if (= i 0)
        (let () (printf "Step ~a:\n~a\n" (- n i) t) #t)
        (let ([ts (apply-reduction-relation red t)] [is (- i 1)])
          (map (lambda (tt) (loop tt is)) ts)))))

(define mstate1a
  (term (((mt [0 -> 0]) [1 -> 0])
         ((mt [b -> 0]) [a -> 1])
         ()
         mt
         mt
         mt
         (([t0_0 (b := 5)]
           [t0_1 (sendi send1 0 1 b t0_1 1)]
           [t0_2 (wait send1)]
           ⊥)
          ([t1_0 (recvi recvA 1 a t1_0)]
           [t1_1 (wait recvA)]
           [t1_2 (assert (= a 5))]
           ⊥))
         ((t0_0 ⊥) (t0_1 ⊥) (t0_2 ⊥) (t1_0 ⊥) (t1_1 ((1 0) ⊥)) (t1_2 ⊥))
         success (()()))))

;(test-term-equal (get-last-send/replace () 0 1 send1) (([0 1 send1]) ⊥))
;(test-term-equal (get-last-send/replace ([0 1 send0]) 0 1 send1) (([0 1 send1]) send0))

(define mstate2a
  (term (((mt [0 -> 5]) [1 -> 0])
         ((mt [b -> 0]) [a -> 1])
         ()
         mt
         mt
         mt
         (([t0_1 (sendi send1 0 1 b t0_1 1)]
           [t0_2 (wait send1)]
           ⊥)
          ([t1_0 (recvi recvA 1 a t1_0)]
           [t1_1 (wait recvA)]
           [t1_2 (assert (= a 5))]
           ⊥))
         ((t0_1 ⊥) (t0_2 ⊥) (t1_0 ⊥) (t1_1 ((1 0) ⊥)) (t1_2 ⊥))
         success
         (((define t0_0 :: int))
          ((HB t0_0 t0_1)(= b 5)))
         )))

(define mstate3a
  (term (((mt [0 -> 5]) [1 -> 0])
         ((mt [b -> 0]) [a -> 1])
         ([send1 0])
         (mt [1 -> (mt [0 -> ([send1 -> 5])])])
         mt
         mt
         (([t0_2 (wait send1)]
           ⊥)
          ([t1_0 (recvi recvA 1 a t1_0)]
           [t1_1 (wait recvA)]
           [t1_2 (assert (= a 5))]
           ⊥))
         ((t0_2 ⊥) (t1_0 ⊥) (t1_1 ((1 0) ⊥)) (t1_2 ⊥))
         success
         (((define t0_1 :: int) (define send1 :: send) (define t0_0 :: int))
          ((HB t0_1 t0_2) (and (= (select send1 ep) 1) (= (select send1 event) t0_1) (= (select send1 value) b) (= (select send1 id) 1)) (HB t0_0 t0_1) (= b 5)))
         )))

(define mstate4a
  (term (((mt [0 -> 5]) [1 -> 0])
         ((mt [b -> 0]) [a -> 1])
         ([send1 0])
         (mt [1 -> (mt [0 -> ([send1 -> 5])])])
         mt
         mt
         ((⊥)
          ([t1_0 (recvi recvA 1 a t1_0)]
           [t1_1 (wait recvA)]
           [t1_2 (assert (= a 5))]
           ⊥))
         ((t1_0 ⊥) (t1_1 ((1 0) ⊥)) (t1_2 ⊥))
         success 
         (((define t0_2 :: int)(define t0_1 :: int)(define send1 :: send)(define t0_0 :: int))
          ((HB t0_1 t0_2)(and (= (select send1 ep) 1) (= (select send1 event) t0_1) (= (select send1 value) b) (= (select send1 id) 1)) (HB t0_0 t0_1) (= b 5)))
         )))

(define mstate5a
  (term (((mt [0 -> 5]) [1 -> 0])
         ((mt [b -> 0]) [a -> 1])
         ([recvA 1] [send1 0])
         (mt [1 -> (mt [0 -> ([send1 -> 5])])])
         (mt [1 -> ([recvA -> a])])
         mt
         ((⊥)
          ([t1_1 (wait recvA)]
           [t1_2 (assert (= a 5))]
           ⊥))
         ((t1_1 ((1 0) ⊥)) (t1_2 ⊥))
         success
         (((define t1_0 :: int)(define recvA :: recv)(define t0_2 :: int)(define t0_1 :: int)(define send1 :: send)(define t0_0 :: int))
          ((HB t1_0 t1_1)(and (= (select recvA ep) 1) (= (select recvA event) t1_0) (= (select recvA var) a))(HB t0_1 t0_2)(and (= (select send1 ep) 1) (= (select send1 event) t0_1) (= (select send1 value) b) (= (select send1 id) 1)) (HB t0_0 t0_1) (= b 5)))
         )))

(define qstate1
  (term ((mt [1 -> (mt [0 -> ([send1 -> 5])])])
         mt
         ((1 0) ⊥)
         success)))

(define qstate2
  (term ((mt [1 -> (mt [0 -> ()])])
         (mt [1 -> ([send1 -> 5])])
         (⊥)
         success)))

(define qstate3
  (term ((mt [1 -> (mt [0 -> ()])])
         (mt [1 -> ([send1 -> 5])])
         ⊥
         success)))

(test-predicate (redex-match lang queue-state) (term ,qstate3))

(test--> queue-reductions
         (term ,qstate1)
         (term ,qstate2))


(define mstate6a
  (term (((mt [0 -> 5]) [1 -> 5])
         ((mt [b -> 0]) [a -> 1])
         ()
         (mt [1 -> (mt [0 -> ()])])
         (mt [1 -> ()])
         (mt [1 -> ()])
         ((⊥)
          ([t1_2 (assert (= a 5))]
           ⊥))
         ((t1_2 ⊥))
         success 
         (((define t1_1 :: int)(define t1_0 :: int)(define recvA :: recv)(define t0_2 :: int)(define t0_1 :: int)(define send1 :: send)(define t0_0 :: int))
          ((HB t1_1 t1_2)(MATCH recvA send1)(HB t1_0 t1_1)(and (= (select recvA ep) 1) (= (select recvA event) t1_0) (= (select recvA var) a))(HB t0_1 t0_2)(and (= (select send1 ep) 1) (= (select send1 event) t0_1) (= (select send1 value) b) (= (select send1 id) 1)) (HB t0_0 t0_1) (= b 5)))
         )))



(define mstate7a
  (term (((mt [0 -> 5]) [1 -> 5])
         ((mt [b -> 0]) [a -> 1])
         ()
         (mt [1 -> (mt [0 -> ()])])
         (mt [1 -> ()])
         (mt [1 -> ()])
         ((⊥)
          (⊥))
         ()
         success
         (((define t1_2 :: int)(define t1_1 :: int)(define t1_0 :: int)(define recvA :: recv)(define t0_2 :: int)(define t0_1 :: int)(define send1 :: send)(define t0_0 :: int))
          ((not (= a 5))(HB t1_1 t1_2)(MATCH recvA send1)(HB t1_0 t1_1)(and (= (select recvA ep) 1) (= (select recvA event) t1_0) (= (select recvA var) a))(HB t0_1 t0_2)(and (= (select send1 ep) 1) (= (select send1 event) t0_1) (= (select send1 value) b) (= (select send1 id) 1)) (HB t0_0 t0_1) (= b 5)))
         )))



(define estate1c
  (term (((mt [0 -> 5]) [1 -> 5])
         ((mt [b -> 0]) [a -> 1])
         ()
         mt
         mt
         mt
         (assert (= a 4))
         success
         ret  (()()))))

(define estate2c
  (term (((mt [0 -> 5]) [1 -> 5])
         ((mt [b -> 0]) [a -> 1])
         ()
         mt
         mt
         mt
         (= a 4)
         success
         (assert * -> ret) (()((not (= a 4)))))))

(define estate3c
  (term (((mt [0 -> 5]) [1 -> 5])
         ((mt [b -> 0]) [a -> 1])
         ()
         mt
         mt
         mt
         a
         success
         (= * 4 -> (assert * -> ret)) (()((not (= a 4)))))))

(define estate4c
  (term (((mt [0 -> 5]) [1 -> 5])
         ((mt [b -> 0]) [a -> 1])
         ()
         mt
         mt
         mt
         5
         success
         (= * 4 -> (assert * -> ret)) (()((not (= a 4)))))))

(define estate5c
  (term (((mt [0 -> 5]) [1 -> 5])
         ((mt [b -> 0]) [a -> 1])
         ()
         mt
         mt
         mt
         4
         success
         (= 5 * -> (assert * -> ret)) (()((not (= a 4)))))))

(define estate6c
  (term (((mt [0 -> 5]) [1 -> 5])
         ((mt [b -> 0]) [a -> 1])
         ()
         mt
         mt
         mt
         false
         success
         (assert * -> ret)(()((not (= a 4)))))))

(define estate7c
  (term (((mt [0 -> 5]) [1 -> 5])
         ((mt [b -> 0]) [a -> 1])
         ()
         mt
         mt
         mt
         false
         failure
         ret (()((not (= a 4)))))))

(define estate-lt1
  (term (((mt [0 -> 5]) [1 -> 5])
         ((mt [b -> 0]) [a -> 1])
         ()
         mt
         mt
         mt
         5
         success
         (< 4 * -> ret)  (()()))))

(define estate-lt2
  (term (((mt [0 -> 5]) [1 -> 5])
         ((mt [b -> 0]) [a -> 1])
         ()
         mt
         mt
         mt
         true
         success
         ret  (()()))))

(define estate-ine1
  (term (((mt [0 -> 5]) [1 -> 5])
         ((mt [b -> 0]) [a -> 1])
         ()
         mt
         mt
         mt
         5
         success
         (/= 4 * -> ret) (()()))))

(define estate-ine2
  (term (((mt [0 -> 5]) [1 -> 5])
         ((mt [b -> 0]) [a -> 1])
         ()
         mt
         mt
         mt
         true
         success
         ret (()()))))

(define estate-bne1
  (term (((mt [0 -> 5]) [1 -> 5])
         ((mt [b -> 0]) [a -> 1])
         ()
         mt
         mt
         mt
         false
         success
         (/= true * -> ret) (()()))))

(define estate-bne2
  (term (((mt [0 -> 5]) [1 -> 5])
         ((mt [b -> 0]) [a -> 1])
         ()
         mt
         mt
         mt
         true
         success
         ret  (()()))))

(define estate-add1
  (term (((mt [0 -> 5]) [1 -> 5])
         ((mt [b -> 0]) [a -> 1])
         ()
         mt
         mt
         mt
         23
         success
         (+ 19 * -> ret) (()()))))

(define estate-add2
  (term (((mt [0 -> 5]) [1 -> 5])
         ((mt [b -> 0]) [a -> 1])
         ()
         mt
         mt
         mt
         42
         success
         ret  (()()))))



(define myh
  (term ((mt [0 -> 0]) [1 -> 5])))
(define myeta
  (term ((mt [b -> 0]) [a -> 1])))
(define mye (term (a := 5)))
(define mystatus (term infeasable))
(define myk (term ret))

(define mycombo
  (term (,myh ,myeta () mt mt mt ,mye ,mystatus ,myk (()()))))

(define estate1a
  (term (((mt [0 -> 0]) [1 -> 0])
         ((mt [b -> 0]) [a -> 1])
         ()
         mt
         mt
         mt
         (a := true)
         success
         ret  (()()))))

(define estate2a
  (term (((mt [0 -> 0]) [1 -> 0])
         ((mt [b -> 0]) [a -> 1])
         ()
         mt
         mt
         mt
         true
         success
         (a := * -> ret) (()((= a true))))))

(define estate3a
  (term (((mt [0 -> 0]) [1 -> true])
         ((mt [b -> 0]) [a -> 1])
         ()
         mt
         mt
         mt
         true
         success
         ret  (()((= a true))))))


(define estate1z
  (term (((mt [0 -> 0]) [1 -> 5])
         ((mt [b -> 0]) [a -> 1])
         ([send1 0] [send2 3] [recvA 1] [recvB 1])
         (mt [1 -> (mt [0 -> ()])])
         ((mt [0 -> ([recvB -> b])]) [1 -> ([recvA -> a])])
         ((mt [0 -> ([send2 -> 4])]) [1 -> ([send1 -> 5])])
         (wait recvA)
         success
         ret (()()))))


(define estate3z
  (term (((mt [0 -> 0]) [1 -> 5])
         ((mt [b -> 0]) [a -> 1])
         ([send2 3] [recvB 1])
         (mt [1 -> (mt [0 -> ()])])
         ((mt [0 -> ([recvB -> b])]) [1 -> ()])
         ((mt [0 -> ([send2 -> 4])]) [1 -> ()])
         true
         success
         ret (()((MATCH recvA send1))))))

(test-predicate (redex-match lang h) (term ,myh))
(test-predicate (redex-match lang eta) (term ,myeta))
(test-predicate (redex-match lang e) (term ,mye))
(test-predicate (redex-match lang status) (term ,mystatus))
(test-predicate (redex-match lang k) (term ,myk))

(test-predicate (redex-match lang expr-state) (term ,mycombo))

(test-predicate (redex-match lang machine-state) (term ,mstate1a))
(test-predicate (redex-match lang machine-state) (term ,mstate2a))
(test-predicate (redex-match lang machine-state) (term ,mstate3a))
(test-predicate (redex-match lang machine-state) (term ,mstate4a))
(test-predicate (redex-match lang machine-state) (term ,mstate5a))
(test-predicate (redex-match lang machine-state) (term ,mstate6a))
(test-predicate (redex-match lang machine-state) (term ,mstate7a))
(test-predicate (redex-match lang expr-state) (term ,estate1a))
(test-predicate (redex-match lang expr-state) (term ,estate2a))
(test-predicate (redex-match lang expr-state) (term ,estate3a))

(test-predicate (redex-match lang expr-state) (term ,estate1c))
(test-predicate (redex-match lang expr-state) (term ,estate2c))
(test-predicate (redex-match lang expr-state) (term ,estate3c))
(test-predicate (redex-match lang expr-state) (term ,estate4c))
(test-predicate (redex-match lang expr-state) (term ,estate5c))
(test-predicate (redex-match lang expr-state) (term ,estate6c))
(test-predicate (redex-match lang expr-state) (term ,estate7c))

(test-predicate (redex-match lang expr-state) (term ,estate1z))

(test--> expr-reductions
         (term ,estate-lt1)
         (term ,estate-lt2))

(test--> expr-reductions
         (term ,estate-ine1)
         (term ,estate-ine2))

(test--> expr-reductions
         (term ,estate-bne1)
         (term ,estate-bne2))

(test--> expr-reductions
         (term ,estate-add1)
         (term ,estate-add2))

(test--> expr-reductions
         (term ,estate1c)
         (term ,estate2c))

(test--> expr-reductions
         (term ,estate2c)
         (term ,estate3c))

(test--> expr-reductions
         (term ,estate3c)
         (term ,estate4c))

(test--> expr-reductions
         (term ,estate4c)
         (term ,estate5c))

(test--> expr-reductions
         (term ,estate5c)
         (term ,estate6c))

(test--> expr-reductions
         (term ,estate6c)
         (term ,estate7c))

(test--> expr-reductions
         (term ,estate1a)
         (term ,estate2a))

(test--> expr-reductions
         (term ,estate2a)
         (term ,estate3a))

; Initial included tests
(test--> machine-reductions
         (term ,mstate1a)
         (term ,mstate2a))

(test--> machine-reductions
         (term ,mstate2a)
         (term ,mstate3a))

(test--> machine-reductions
         (term ,mstate3a)
         (term ,mstate4a))

(test--> machine-reductions
         (term ,mstate4a)
         (term ,mstate5a))

(test--> machine-reductions
         (term ,mstate5a)
         (term ,mstate6a))

(test--> machine-reductions
         (term ,mstate6a)
         (term ,mstate7a))

(test--> expr-reductions
          (term ,estate1z)
          (term ,estate3z))

(define mstate1B
  (term (((((mt [0 -> 0]) [1 -> 0]) [2 -> 0]) [3 -> 10])
         ((((mt [a -> 0]) [b -> 1]) [c -> 2]) [d -> 3])
         ()
         mt
         mt
         mt
         (([t0_0 (sendi send1 0 1 d t0_0 1)]
           [t0_1 (c := 5)]
           [t0_2 (sendi send2 0 1 c t0_2 2)]
           [t0_3 (wait send1)]
           [t0_4 (wait send2)]
           ⊥)
          ([t1_0 (recvi recvA 1 a t1_0)]
           [t1_1 (recvi recvB 1 b t1_1)]
           [t1_2 (wait recvA)]
           [t1_3 (wait recvB)]
           [t1_4 (assert (= a 5))]
           ⊥))
         ((t0_0 ⊥) (t0_1 ⊥) (t0_2 ⊥) (t0_3 ⊥) (t0_4 ⊥) (t1_0 ⊥) (t1_1 ⊥) (t1_2 ((1 0) (1 0) ⊥)) (t1_3 ⊥) (t1_4 ⊥))
         success (()()))))

(define mstate2B
  (term (((((mt [0 -> 0]) [1 -> 0]) [2 -> 0]) [3 -> 10])
         ((((mt [a -> 0]) [b -> 1]) [c -> 2]) [d -> 3])
         ([send1 0])
         (mt [1 -> (mt [0 -> ([send1 -> 10])])])
         mt
         mt
         (([t0_1 (c := 5)]
           [t0_2 (sendi send2 0 1 c t0_2 2)]
           [t0_3 (wait send1)]
           [t0_4 (wait send2)]
           ⊥)
          ([t1_0 (recvi recvA 1 a t1_0)]
           [t1_1 (recvi recvB 1 b t1_1)]
           [t1_2 (wait recvA)]
           [t1_3 (wait recvB)]
           [t1_4 (assert (= a 5))]
           ⊥))
         ((t0_1 ⊥) (t0_2 ⊥) (t0_3 ⊥) (t0_4 ⊥) (t1_0 ⊥) (t1_1 ⊥) (t1_2 ((1 0) (1 0) ⊥)) (t1_3 ⊥) (t1_4 ⊥))
         success
         (((define t0_0 :: int)(define send1 :: send))
          ((HB t0_0 t0_1)(and (= (select send1 ep) 1) (= (select send1 event) t0_0) (= (select send1 value) d) (= (select send1 id) 1)))
          ))))

(define mstate3B
  (term (((((mt [0 -> 0]) [1 -> 0]) [2 -> 5]) [3 -> 10])
         ((((mt [a -> 0]) [b -> 1]) [c -> 2]) [d -> 3])
         ([send1 0])
         (mt [1 -> (mt [0 -> ([send1 -> 10])])])
         mt
         mt
         (([t0_2 (sendi send2 0 1 c t0_2 2)]
           [t0_3 (wait send1)]
           [t0_4 (wait send2)]
           ⊥)
          ([t1_0 (recvi recvA 1 a t1_0)]
           [t1_1 (recvi recvB 1 b t1_1)]
           [t1_2 (wait recvA)]
           [t1_3 (wait recvB)]
           [t1_4 (assert (= a 5))]
           ⊥))
         ((t0_2 ⊥) (t0_3 ⊥) (t0_4 ⊥) (t1_0 ⊥) (t1_1 ⊥) (t1_2 ((1 0) (1 0) ⊥)) (t1_3 ⊥) (t1_4 ⊥))
         success
         (((define t0_1 :: int)(define t0_0 :: int)(define send1 :: send))
          ((HB t0_1 t0_2)(= c 5)(HB t0_0 t0_1)(and (= (select send1 ep) 1) (= (select send1 event) t0_0) (= (select send1 value) d) (= (select send1 id) 1)))
          ))))

(define mstate4B
  (term (((((mt [0 -> 0]) [1 -> 0]) [2 -> 5]) [3 -> 10])
         ((((mt [a -> 0]) [b -> 1]) [c -> 2]) [d -> 3])
         ([send2 0] [send1 0])
         (mt [1 -> (mt [0 -> ([send2 -> 5] [send1 -> 10])])])
         mt
         mt
         (([t0_3 (wait send1)]
           [t0_4 (wait send2)]
           ⊥)
          ([t1_0 (recvi recvA 1 a t1_0)]
           [t1_1 (recvi recvB 1 b t1_1)]
           [t1_2 (wait recvA)]
           [t1_3 (wait recvB)]
           [t1_4 (assert (= a 5))]
           ⊥))
         ((t0_3 ⊥) (t0_4 ⊥) (t1_0 ⊥) (t1_1 ⊥) (t1_2 ((1 0) (1 0) ⊥)) (t1_3 ⊥) (t1_4 ⊥))
         success
         (((define t0_2 :: int)(define send2 :: send)(define t0_1 :: int)(define t0_0 :: int)(define send1 :: send))
          ((HB t0_2 t0_3)(and (= (select send2 ep) 1) (= (select send2 event) t0_2) (= (select send2 value) c) (= (select send2 id) 2))(HB t0_1 t0_2)(= c 5)(HB t0_0 t0_1)(and (= (select send1 ep) 1) (= (select send1 event) t0_0) (= (select send1 value) d) (= (select send1 id) 1)))
          ))))


(define mstate7B
  (term (((((mt [0 -> 0]) [1 -> 0]) [2 -> 5]) [3 -> 10])
         ((((mt [a -> 0]) [b -> 1]) [c -> 2]) [d -> 3])
         ([recvA 1] [send2 0] [send1 0])
         (mt [1 -> (mt [0 -> ([send2 -> 5] [send1 -> 10] )])])
         (mt [1 -> ([recvA -> a])])
         mt
         ((⊥)
          ([t1_1 (recvi recvB 1 b t1_1)]
           [t1_2 (wait recvA)]
           [t1_3 (wait recvB)]
           [t1_4 (assert (= a 5))]
           ⊥))
         ((t1_1 ⊥) (t1_2 ((1 0) (1 0) ⊥)) (t1_3 ⊥) (t1_4 ⊥))
         success
         (((define t1_0 :: int)
           (define recvA :: recv)
           (define t0_4 :: int)
           (define t0_3 :: int)
           (define t0_2 :: int)
           (define send2 :: send)
           (define t0_1 :: int)
           (define t0_0 :: int)
           (define send1 :: send))
          ((HB t1_0 t1_1)
           (and 
            (= (select recvA ep) 1)
            (= (select recvA event) t1_0)
            (= (select recvA var) a))
           (HB t0_3 t0_4)
           (HB t0_2 t0_3)
           (and 
            (= (select send2 ep) 1)
            (= (select send2 event) t0_2)
            (= (select send2 value) c)
            (= (select send2 id) 2))
           (HB t0_1 t0_2)
           (= c 5)
           (HB t0_0 t0_1)
           (and 
            (= (select send1 ep) 1) 
            (= (select send1 event) t0_0) 
            (= (select send1 value) d) 
            (= (select send1 id) 1)))
          )))) 


(define mstate8B
  (term (((((mt [0 -> 0]) [1 -> 0]) [2 -> 5]) [3 -> 10])
         ((((mt [a -> 0]) [b -> 1]) [c -> 2]) [d -> 3])
         ([recvB 1] [recvA 1] [send2 0] [send1 0])
         (mt [1 -> (mt [0 -> ([send2 -> 5] [send1 -> 10] )])])
         (mt [1 -> ([recvB -> b] [recvA -> a] )])
         mt
         ((⊥)
          ([t1_2 (wait recvA)]
           [t1_3 (wait recvB)]
           [t1_4 (assert (= a 5))]
           ⊥))
         ((t1_2 ((1 0) (1 0) ⊥)) (t1_3 ⊥) (t1_4 ⊥))
         success
         (((define t1_1 :: int)
           (define recvB :: recv)
           (define t1_0 :: int)
           (define recvA :: recv)
           (define t0_4 :: int)
           (define t0_3 :: int)
           (define t0_2 :: int)
           (define send2 :: send)
           (define t0_1 :: int)
           (define t0_0 :: int)
           (define send1 :: send))
          ((HB t1_1 t1_2)
           (and 
            (= (select recvB ep) 1)
            (= (select recvB event) t1_1)
            (= (select recvB var) b))           
           (HB t1_0 t1_1)
           (and 
            (= (select recvA ep) 1)
            (= (select recvA event) t1_0)
            (= (select recvA var) a))
           (HB t0_3 t0_4)
           (HB t0_2 t0_3)
           (and 
            (= (select send2 ep) 1)
            (= (select send2 event) t0_2)
            (= (select send2 value) c)
            (= (select send2 id) 2))
           (HB t0_1 t0_2)
           (= c 5)
           (HB t0_0 t0_1)
           (and 
            (= (select send1 ep) 1) 
            (= (select send1 event) t0_0) 
            (= (select send1 value) d) 
            (= (select send1 id) 1)))
          )))) 

(define mstate9B
  (term (((((mt [0 -> 10]) [1 -> 0]) [2 -> 5]) [3 -> 10])
         ((((mt [a -> 0]) [b -> 1]) [c -> 2]) [d -> 3])
         ([recvB 1][send2 0])
         (mt [1 -> (mt [0 -> ()])])
         (mt [1 -> ([recvB -> b])])
         (mt [1 -> ([send2 -> 5])])
         ((⊥)
          ([t1_3 (wait recvB)]
           [t1_4 (assert (= a 5))]
           ⊥))
         ((t1_3 ⊥) (t1_4 ⊥))
         success 
         (((define t1_2 :: int)
           (define t1_1 :: int)
           (define recvB :: recv)
           (define t1_0 :: int)
           (define recvA :: recv)
           (define t0_4 :: int)
           (define t0_3 :: int)
           (define t0_2 :: int)
           (define send2 :: send)
           (define t0_1 :: int)
           (define t0_0 :: int)
           (define send1 :: send))
          ((HB t1_2 t1_3) 
           (MATCH recvA send1)
           (HB t1_1 t1_2)
           (and 
            (= (select recvB ep) 1)
            (= (select recvB event) t1_1)
            (= (select recvB var) b))           
           (HB t1_0 t1_1)
           (and 
            (= (select recvA ep) 1)
            (= (select recvA event) t1_0)
            (= (select recvA var) a))
           (HB t0_3 t0_4)
           (HB t0_2 t0_3)
           (and 
            (= (select send2 ep) 1)
            (= (select send2 event) t0_2)
            (= (select send2 value) c)
            (= (select send2 id) 2))
           (HB t0_1 t0_2)
           (= c 5)
           (HB t0_0 t0_1)
           (and 
            (= (select send1 ep) 1) 
            (= (select send1 event) t0_0) 
            (= (select send1 value) d) 
            (= (select send1 id) 1)))
          )))) 

(define mstate12B
  (term (((((mt [0 -> 10]) [1 -> 5]) [2 -> 5]) [3 -> 10])
         ((((mt [a -> 0]) [b -> 1]) [c -> 2]) [d -> 3])
         ()
          (mt [1 -> (mt [0 -> ()])])
         (mt [1 -> ()])
         (mt [1 -> ()])
         ((⊥)
          (⊥))
         ()
         failure
         (((define t1_4 :: int)
           (define t1_3 :: int)
           (define t1_2 :: int)
           (define t1_1 :: int)
           (define recvB :: recv)
           (define t1_0 :: int)
           (define recvA :: recv)
           (define t0_4 :: int)
           (define t0_3 :: int)
           (define t0_2 :: int)
           (define send2 :: send)
           (define t0_1 :: int)
           (define t0_0 :: int)
           (define send1 :: send))
          ((not (= a 5))
           (HB t1_3 t1_4)
           (MATCH recvB send2)
           (HB t1_2 t1_3)
           (MATCH recvA send1)
           (HB t1_1 t1_2)
           (and 
            (= (select recvB ep) 1)
            (= (select recvB event) t1_1)
            (= (select recvB var) b))           
           (HB t1_0 t1_1)
           (and 
            (= (select recvA ep) 1)
            (= (select recvA event) t1_0)
            (= (select recvA var) a))
           (HB t0_3 t0_4)
           (HB t0_2 t0_3)
           (and 
            (= (select send2 ep) 1)
            (= (select send2 event) t0_2)
            (= (select send2 value) c)
            (= (select send2 id) 2))
           (HB t0_1 t0_2)
           (= c 5)
           (HB t0_0 t0_1)
           (and 
            (= (select send1 ep) 1) 
            (= (select send1 event) t0_0) 
            (= (select send1 value) d) 
            (= (select send1 id) 1)))
          )))) 

(test-predicate (redex-match lang machine-state) (term ,mstate1B))
(test-predicate (redex-match lang machine-state) (term ,mstate2B))
(test-predicate (redex-match lang machine-state) (term ,mstate3B))
(test-predicate (redex-match lang machine-state) (term ,mstate4B))
(test-predicate (redex-match lang machine-state) (term ,mstate7B))
(test-predicate (redex-match lang machine-state) (term ,mstate8B))
(test-predicate (redex-match lang machine-state) (term ,mstate9B))
(test-predicate (redex-match lang machine-state) (term ,mstate12B))

(test--> machine-reductions
         (term ,mstate1B)
         (term ,mstate2B))

(test--> machine-reductions
         (term ,mstate2B)
         (term ,mstate3B))

(test--> machine-reductions
         (term ,mstate3B)
         (term ,mstate4B))

(test-->* machine-reductions
            (term ,mstate4B)
            (term ,mstate7B))

(test--> machine-reductions
         (term ,mstate7B)
         (term ,mstate8B))

(test--> machine-reductions
         (term ,mstate8B)
         (term ,mstate9B))


(test-->* machine-reductions
            (term ,mstate9B)
            (term ,mstate12B))

(define add1
  (term ((mt [0 -> 0]) 
         (mt [a -> 0]) 
         () 
         mt 
         mt 
         mt
         (([t0_0 (a := (+ 3 4))] ⊥)) 
         ((t0_0 ⊥)) 
         success
         (()()))))

(define addX
  (term ((mt [0 -> 7]) 
         (mt [a -> 0]) 
         ()
         mt 
         mt 
         mt
         ((⊥)) 
         () 
         success
         (((define t0_0 :: int))((= a (+ 3 4)))))))

(define sub1
  (term ((mt [0 -> 0]) 
         (mt [a -> 0]) 
         () 
         mt 
         mt 
         mt
         (([t0_0 (a := (- 3 4))] ⊥)) 
         ((t0_0 ⊥)) 
         success  
         (()()))))

(define subX
  (term ((mt [0 -> -1]) 
         (mt [a -> 0]) 
         ()
         mt 
         mt 
         mt
         ((⊥)) 
         () 
         success
         (((define t0_0 :: int))((= a (- 3 4)))))))

(define ne1
  (term ((mt [0 -> 0]) 
         (mt [a -> 0]) 
         () 
         mt
         mt 
         mt
         (([t0_0 (a := (/= 3 4))] ⊥)) 
         ((t0_0 ⊥)) 
         success 
         (()()))))

(define neX
  (term ((mt [0 -> true]) 
         (mt [a -> 0]) 
         ()
         mt
         mt 
         mt
         ((⊥)) 
         () 
         success
         (((define t0_0 :: int))((= a (/= 3 4)))))))

(define ass1
  (term (((mt [0 -> 2]) [1 -> 5])
         ((mt [a -> 0]) [b -> 1]) 
         () 
         mt 
         mt 
         mt
         (([t0_0 (assume (= (+ a b) 4))] ⊥))
         ((t0_0 ⊥)) 
         success
         (()()))))

(define assX
  (term (((mt [0 -> 2]) [1 -> 5]) 
         ((mt [a -> 0]) [b -> 1]) 
         () 
         mt 
         mt
         mt
         ((⊥)) 
         () 
         infeasable 
         (((define t0_0 :: int))((= (+ a b) 4))))))

(define ass1-e
  (term (((mt [0 -> 2]) [1 -> 5])
         ((mt [a -> 0]) [b -> 1]) 
         () 
         mt 
         mt
         mt
         (assume (= 2 3))
         success 
         ret
         (()()))))
(define ass2-e
  (term (((mt [0 -> 2]) [1 -> 5])
         ((mt [a -> 0]) [b -> 1]) 
         ()
         mt 
         mt 
         mt
         (= 2 3) 
         success 
         (assume * -> ret) 
         (()((= 2 3))))))
(define ass3-e
  (term (((mt [0 -> 2]) [1 -> 5])
         ((mt [a -> 0]) [b -> 1]) 
         ()
         mt 
         mt 
         mt
         2 
         success 
         (= * 3 -> (assume * -> ret))
         (()((= 2 3))))))
(define ass4-e
  (term (((mt [0 -> 2]) [1 -> 5]) 
         ((mt [a -> 0]) [b -> 1]) 
         () 
         mt 
         mt 
         mt 
         3 
         success 
         (= 2 * -> (assume * -> ret)) 
         (()((= 2 3))))))
(define ass5-e
  (term (((mt [0 -> 2]) [1 -> 5]) 
         ((mt [a -> 0]) [b -> 1]) 
         ()
         mt
         mt 
         mt 
         false 
         success 
         (assume * -> ret) 
         (()((= 2 3))))))
(define ass6-e
  (term (((mt [0 -> 2]) [1 -> 5]) 
         ((mt [a -> 0]) [b -> 1]) 
         () mt 
         mt
         mt
         false 
         infeasable 
         ret 
         (()((= 2 3))))))

(test-predicate (redex-match lang machine-state) (term ,add1))
(test-predicate (redex-match lang machine-state) (term ,addX))
(test-predicate (redex-match lang machine-state) (term ,sub1))
(test-predicate (redex-match lang machine-state) (term ,subX))
(test-predicate (redex-match lang machine-state) (term ,ne1))
(test-predicate (redex-match lang machine-state) (term ,neX))
(test-predicate (redex-match lang machine-state) (term ,ass1))
(test-predicate (redex-match lang machine-state) (term ,assX))
(test-predicate (redex-match lang expr-state) (term ,ass1-e))
(test-predicate (redex-match lang expr-state) (term ,ass2-e))
(test-predicate (redex-match lang expr-state) (term ,ass3-e))
(test-predicate (redex-match lang expr-state) (term ,ass4-e))
(test-predicate (redex-match lang expr-state) (term ,ass5-e))
(test-predicate (redex-match lang expr-state) (term ,ass6-e))

(test--> machine-reductions
         (term ,add1)
         (term ,addX))

(test--> machine-reductions
         (term ,sub1)
         (term ,subX))

(test--> machine-reductions
         (term ,ne1)
         (term ,neX))

(test--> machine-reductions
         (term ,ass1)
         (term ,assX))


(test--> expr-reductions
         (term ,ass1-e)
         (term ,ass2-e))

(test--> expr-reductions
         (term ,ass2-e)
         (term ,ass3-e))

(test--> expr-reductions
         (term ,ass3-e)
         (term ,ass4-e))

(test--> expr-reductions
         (term ,ass4-e)
         (term ,ass5-e))

(test--> expr-reductions
         (term ,ass5-e)
         (term ,ass6-e))

(define example1
  (term (((mt [0 -> 4]) [1 -> 0])
         ((mt [b -> 0]) [a -> 1])
         ()
         mt
         mt
         mt
         (([t0_0 (sendi send1 0 1 b t0_0 1)]
           [t0_1 (wait send1)]
           ⊥)
          ([t1_0 (recvi recvA 1 a t1_0)]
           [t1_1 (wait recvA)]
           [t1_2 (assume (> a 0))]
           [t1_3 (assert (= a 5))]
           ⊥))
         ((t0_0 ⊥) (t0_1 ⊥) (t1_0 ⊥) (t1_1 ((1 0) ⊥)) (t1_2 ⊥) (t1_3 ⊥))
         success  (()()))))

(define example2
  (term (((mt [0 -> 4]) [1 -> 0])
         ((mt [b -> 0]) [a -> 1])
         ((send1 0))
         (mt (1 -> (mt (0 -> ((send1 -> 4))))))
         mt
         mt
         (([t0_1 (wait send1)]
           ⊥)
          ([t1_0 (recvi recvA 1 a t1_0)]
           [t1_1 (wait recvA)]
           [t1_2 (assume (> a 0))]
           [t1_3 (assert (= a 5))]
           ⊥))
         ((t0_1 ⊥) (t1_0 ⊥) (t1_1 ((1 0) ⊥)) (t1_2 ⊥) (t1_3 ⊥))
         success (((define t0_0 :: int) (define send1 :: send)) ((HB t0_0 t0_1) (and (= (select send1 ep) 1) (= (select send1 event) t0_0) (= (select send1 value) b) (= (select send1 id) 1)))))))

(test-predicate (redex-match lang machine-state) (term ,example1))
(test-predicate (redex-match lang machine-state) (term ,example2))

(test--> machine-reductions
         (term ,example1)
         (term ,example2))

(define waitRelax
  (term (((((mt [0 -> 4]) [1 -> 8]) [2 -> 0] ) [3 -> 0])
         ((((mt [a -> 0]) [b -> 1]) [c -> 2]) [d -> 3])
         ()
         mt
         mt
         mt
         (([t0_0 (sendi send1 0 1 a t0_0 1)]
           [t0_1 (wait send1)]
           ⊥)
          ([t1_0 (recvi recvC 1 c t1_0)]
           [t1_1 (recvi recvD 1 d t1_0)]
           [t1_3 (wait recvD)]
           [t1_4 (wait recvC)]
           [t1_5 (assume (= c 4))]
           [t1_6 (assert (= d 8))]
           ⊥)
          ([t2_0 (sendi send2 2 1 b t0_0 1)]
           [t2_1 (wait send2)]
           ⊥))
         ((t0_0 ⊥) (t2_0 ⊥) (t1_0 ⊥) (t1_1 ⊥) (t1_3 ((1 0) (1 2) ⊥)) (t1_4 ⊥) (t2_1 ⊥) (t0_1 ⊥) (t1_5 ⊥) (t1_6 ⊥))
         success (()()))))

(define justBefore
    (term (((((mt (0 -> 4)) (1 -> 8)) (2 -> 0)) (3 -> 0)) 
           ((((mt (a -> 0)) (b -> 1)) (c -> 2)) (d -> 3)) 
           ((recvD 1) (recvC 1) (send2 0) (send1 0)) 
           (mt (1 -> (mt (0 -> ([send2 -> 8] [send1 -> 4]))))) 
           (mt (1 -> ((recvD -> d) (recvC -> c)))) 
           mt
           (((t0_1 (wait send1)) ⊥) 
            ((t1_3 (wait recvC))
             (t1_4 (wait recvD)) 
             (t1_5 (assume (= c 4))) 
             (t1_6 (assert (= d 8))) ⊥) 
            ((t2_1 (wait send2)) ⊥)) 
           ((t1_3 ((1 0) (1 2) ⊥)) (t1_4 ⊥) (t2_1 ⊥) (t0_1 ⊥) (t1_5 ⊥) (t1_6 ⊥)) 
           success (()()))))

(define justBefore-es
  (term (((((mt (0 -> 4)) (1 -> 8)) (2 -> 0)) (3 -> 0)) 
         ((((mt (a -> 0)) (b -> 1)) (c -> 2)) (d -> 3)) 
         ((recvD 1) (recvC 1) (send2 0) (send1 0)) 
         (mt (1 -> (mt (0 -> ())))) 
         (mt (1 -> ((recvD -> d) (recvC -> c))))
         (mt (1 -> ((send2 -> 8) (send1 -> 4))))
         (wait recvC) 
         success ret (()()))))

(define waitRelax2
  (term (((((mt [0 -> 4]) [1 -> 8]) [2 -> 0] ) [3 -> 0])
         ((((mt [a -> 0]) [b -> 1]) [c -> 2]) [d -> 3])
         ()
         mt
         mt
         mt
         (([t0_0 (sendi send1 0 1 a t0_0 1)]
           [t0_1 (wait send1)]
           ⊥)
          ([t1_0 (recvi recvC 1 c t1_0)]
           [t1_1 (recvi recvD 1 d t1_0)]
           [t1_3 (wait recvC)]
           [t1_4 (wait recvD)]
           [t1_5 (assume (= c 4))]
           [t1_6 (assert (= d 8))]
           ⊥)
          ([t2_0 (sendi send2 2 1 b t0_0 1)]
           [t2_1 (wait send2)]
           ⊥))
         ((t0_0 ⊥) (t2_0 ⊥) (t1_0 ⊥) (t1_1 ⊥) (t1_3 ((1 0) (1 2) ⊥)) (t1_4 ⊥) (t2_1 ⊥) (t0_1 ⊥) (t1_5 ⊥) (t1_6 ⊥))
         success (()()))))

(test-predicate (redex-match lang machine-state) (term ,waitRelax))
(test-predicate (redex-match lang machine-state) (term ,justBefore))
(test-predicate (redex-match lang expr-state) (term ,justBefore-es))

;(step-->n machine-reductions example2 2)
;(step-->n machine-reductions waitRelax2 5)
;(step-->n machine-reductions waitRelax 5)
;(step-->n expr-reductions  justBefore-es 2)

(define topher-scenario
  (term (
         (((mt [1 -> 0]) [2 -> 0]) [3 -> 0])
         (((mt [A -> 1]) [B -> 2]) [C -> 3])
         ()
         mt
         mt
         mt
         (
          ([t0_0 (recvi recvA 0 A t0_0)]
           [t0_1 (recvi recvB 0 B t0_1)]
           [t0_2 (assume (> B 0))]
           [t0_3 (assert (/= A 1))]
           ⊥)
          ([t1_0 (recvi recvC 1 C t1_0)]
           [t1_1 (sendi send3 1 0 1 t1_1 3)]
           ⊥)
          ([t2_0 (sendi send1 2 1 2 t2_0 1)]
           [t2_1 (sendi send2 2 0 3 t2_1 2)]
           ⊥))
         ((t2_0 ⊥) 
          (t1_0 send1) 
          (t1_1 ⊥)
          (t2_1 ⊥)
          (t0_0 send2) 
          (t0_1 send3) 
          (t0_2 ⊥)
          (t0_3 ⊥))
         success
         () (()()))))

;(test-predicate (redex-match lang machine-state) topher-scenario)
;(pretty-print (step-->n machine-reductions topher-scenario 2))


(define topher-scenario-wait
(term (((((((mt [1 -> 0]) [2 -> 0]) [3 -> 0]) [4 -> 1]) [5 -> 2]) [6 -> 3])
((((((mt [A -> 1]) [B -> 2]) [C -> 3]) [e -> 4]) [f -> 5]) [g -> 6])
()
mt
mt
mt
((
[t0_0 (recvi recvA 0 A t0_0)]
[t0_1 (wait recvA)]
[t0_2 (recvi recvB 0 B t0_2)]
[t0_3 (wait recvB)]
[t0_4 (assume (> B 0))]
[t0_5 (assert (= A 1))]
⊥
)
(
[t1_0 (recvi recvC 1 C t1_0)]
[t1_1 (wait recvC)]
[t1_2 (sendi send3 1 0 e t1_2 3)]
[t1_3 (wait send3)]
⊥
)
(
[t2_0 (sendi send1 2 1 f t2_0 1)]
[t2_1 (wait send1)]
[t2_2 (sendi send2 2 0 g t2_2 2)]
[t2_3 (wait send2)]
⊥
)
)
((t2_0 ⊥) (t2_1 ⊥) (t1_0 ⊥) (t1_1 ((1 2) ⊥)) (t1_2 ⊥) (t1_3 ⊥) (t2_2 ⊥) (t2_3 ⊥) (t0_0 ⊥) (t0_1 ((0 1) (0 2) ⊥)) (t0_2 ⊥) (t0_3 ⊥) (t0_4 ⊥) (t0_5 ⊥))
success
(()()))
))

(test-predicate (redex-match lang machine-state) topher-scenario-wait)
#;(pretty-print (step-->n machine-reductions topher-scenario-wait 1))
#;(pretty-print (step-->n machine-reductions topher-scenario-wait 2))
#;(pretty-print (step-->n machine-reductions topher-scenario-wait 3))
#;(pretty-print (step-->n machine-reductions topher-scenario-wait 4))
#;(pretty-print (step-->n machine-reductions topher-scenario-wait 5))
#;(pretty-print (step-->n machine-reductions topher-scenario-wait 6))
#;(pretty-print (step-->n machine-reductions topher-scenario-wait 7))
#;(pretty-print (step-->n machine-reductions topher-scenario-wait 8))
#;(pretty-print (step-->n machine-reductions topher-scenario-wait 9))
#;(pretty-print (step-->n machine-reductions topher-scenario-wait 14))

(define small-test
(term ((((mt [1 -> 0]) [2 -> 0]) [3 -> 0])
(((mt [A -> 1]) [B -> 2]) [C -> 3])
()
mt
mt
mt
(
(
[t0_0 (recvi recvA 0 A t0_0)]
[t0_1 (wait recvA)]
[t0_2 (assert (= 1 A))]
⊥
)
(
[t1_0 (sendi send1 1 0 C t1_0 1)]
[t1_1 (wait send1)]
⊥
)
)
((t1_0 ⊥) (t1_1 ⊥) (t0_0 ⊥) (t0_1 ((0 1) ⊥)) (t0_2 ⊥)) 
success
(()()))
))

;(test-predicate (redex-match lang machine-state) small-test)
;(pretty-print (step-->n machine-reductions small-test 1))
;(pretty-print (step-->n machine-reductions small-test 2))
;(pretty-print (step-->n machine-reductions small-test 3))
;(pretty-print (step-->n machine-reductions small-test 4))
;(pretty-print (step-->n machine-reductions small-test 5))

(define small-test1
(term (((((mt [1 -> 0]) [2 -> 0]) [3 -> 0])[4 -> 4])
((((mt [A -> 1]) [B -> 2]) [C -> 3])[e -> 4])
()
mt
mt
mt
(
(
[t0_0 (sendi send1 0 1 e t0_0 1)]
[t0_1 (wait send1)]
⊥
)
(
[t1_0 (recvi recvA 1 A t1_0)]
[t1_1 (wait recvA)]
[t1_2 (assert (= 4 A))]
⊥
)
)
((t0_0 ⊥) (t0_1 ⊥) (t1_0 ⊥) (t1_1 ((1 0) ⊥)) (t1_2 ⊥)) 
success
(()()))
))

(test-predicate (redex-match lang machine-state) small-test1)
(pretty-print (step-->n machine-reductions small-test1 1))
(pretty-print (step-->n machine-reductions small-test1 2))
(pretty-print (step-->n machine-reductions small-test1 3))
(pretty-print (step-->n machine-reductions small-test1 4))
(pretty-print (step-->n machine-reductions small-test1 5))

(test-results)

 #lang racket
(require redex/reduction-semantics
         "mp-semantics.rkt")

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
         success
         )))

(define mstate6a
  (term (((mt (0 -> 5)) (1 -> 0)) 
         ((mt (b -> 0)) (a -> 1)) 
         ((recvA 1) (send1 0)) 
         (mt (1 -> (mt (0 -> ((send1 -> 5)))))) 
         (mt (1 -> ((recvA -> a)))) 
         mt 
         ((⊥) 
          ((t1_2 (assert (= a 5))) 
           ⊥)) 
         success
         )))


(define mstate7a
  (term (((mt [0 -> 5]) [1 -> 5])
         ((mt [b -> 0]) [a -> 1])
         ()
         (mt [1 -> (mt [0 -> ()])])
         (mt [1 -> ()])
         (mt [1 -> ()])
         ((⊥)
          ([t1_2 (assert (= a 5))]
           ⊥))
         success 
         )))


(test--> machine-reductions
         (term ,mstate5a)
         (term ,mstate6a))




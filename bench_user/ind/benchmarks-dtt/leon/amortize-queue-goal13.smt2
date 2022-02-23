;(set-logic ALL_SUPPORTED)

(declare-fun less (Int Int) Bool)
(assert (not (less 0 0)))
(assert (forall ((x Int)) (=> (>= x 0) (less 0 (+ 1 x)))))
(assert (forall ((x Int) (y Int)) (=> (and (>= x 0) (>= y 0)) (= (less (+ 1 x) (+ 1 y)) (less x y)))))
; less equivalent
(assert (forall ((x Int) (y Int)) (=> (and (>= x 0) (>= y 0)) (= (less x y) (< x y)))))

(define-fun leq ((x Int) (y Int)) Bool (or (= x y) (less x y)))

(declare-fun plus (Int Int) Int)
(assert (forall ((n Int)) (=> (>= n 0) (= (plus 0 n) n))))
(assert (forall ((n Int) (m Int)) (=> (and (>= n 0) (>= m 0)) (= (plus (+ 1 n) m) (+ 1 (plus n m))))))
; plus equivalent
(assert (forall ((n Int) (m Int)) (=> (and (>= n 0) (>= m 0)) (= (plus n m) (+ n m)))))

; lists      
(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))

(declare-fun append (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (append nil x) x)))
(assert (forall ((x Int) (y Lst) (z Lst)) (= (append (cons x y) z) (cons x (append y z)))))

(declare-fun len (Lst) Int)
(assert (= (len nil) 0))
(assert (forall ((x Int) (y Lst)) (= (len (cons x y)) (+ 1 (len y)))))
; since returns Nat, we can assume this "lemma"
(assert (forall ((x Lst)) (>= (len x) 0)))

(declare-fun butlast (Lst) Lst)
(assert (= (butlast nil) nil))
(assert (forall ((x Int) (y Lst)) (= (butlast (cons x y)) (ite (= y nil) nil (cons x (butlast y))))))

(declare-fun qreva (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (qreva nil x) x)))
(assert (forall ((x Lst) (y Lst) (z Int)) (= (qreva (cons z x) y) (qreva x (cons z y)))))

(declare-fun qrev (Lst) Lst)
(assert (forall ((x Lst)) (= (qrev x) (qreva x nil))))

; queues
(declare-datatypes () ((Queue (queue (front Lst) (back Lst)))))

(declare-fun queue-to-lst (Queue) Lst)
(assert (forall ((x Lst) (y Lst)) (= (queue-to-lst (queue x y)) (append x (qrev y)))))

(declare-fun qlen (Queue) Int)
(assert (forall ((x Lst) (y Lst)) (= (qlen (queue x y)) (plus (len x) (len y)))))
; since returns Nat, we can assume this "lemma"
(assert (forall ((q Queue)) (>= (qlen q) 0)))

(declare-fun isAmortized (Queue) Bool)
(assert (forall ((x Lst) (y Lst)) (= (isAmortized (queue x y)) (leq (len y) (len x)))))

(declare-fun isEmpty (Queue) Bool)
(assert (forall ((x Lst) (y Lst)) (= (isEmpty (queue x y)) (and (= x nil) (= y nil)))))

(declare-fun amortizeQueue (Lst Lst) Queue)
(assert (forall ((x Lst) (y Lst)) (= (amortizeQueue x y) (ite (leq (len y) (len x)) (queue x y) (queue (append x (qrev y)) nil)))))

(declare-fun enqueue (Queue Int) Queue)
(assert (forall ((x Lst) (y Lst) (n Int)) (= (enqueue (queue x y) n) (amortizeQueue x (cons n y)))))

(declare-fun qpop (Queue) Queue)
(assert (forall ((x Lst) (y Lst) (n Int)) (= (qpop (queue x (cons n y))) (queue x y))))
(assert (forall ((x Lst)) (= (qpop (queue x nil)) (queue (butlast x) nil))))

; proven
(assert 
(forall ((x Lst) (y Lst)) (= (len (append x y)) (plus (len x) (len y))))  ; G-amortize-queue-1 
)
(assert 
(forall ((x Lst) (y Lst)) (= (len (qreva x y)) (plus (len x) (len y)))) ; G-amortize-queue-2 
)
(assert 
(forall ((x Lst)) (= (len (qrev x)) (len x))) ; G-amortize-queue-3 
)
(assert 
(forall ((x Lst) (y Lst)) (= (plus (len x) (len y)) (qlen (queue x y)))) ; G-amortize-queue-4 
)
(assert 
(forall ((x Lst) (y Int)) (= (+ 1 (len (butlast (cons y x)))) (len (cons y x)))) ; G-amortize-queue-5 
)
(assert 
(forall ((q Queue) (n Int)) (= (qlen (enqueue q n)) (+ 1 (qlen q)))) ; G-amortize-queue-6 
)
(assert 
(forall ((q Queue) (n Int)) (=> (and (isAmortized q) (not (isEmpty q))) (= (+ 1 (qlen (qpop q))) (qlen q)))) ; G-amortize-queue-7 
)
(assert 
(forall ((x Lst)) (= (append x nil) x)) ; G-amortize-queue-8 
)
(assert 
(forall ((x Lst) (n Int) (y Lst)) (= (butlast (append x (cons n y))) (append x (butlast (cons n y))))) ; G-amortize-queue-9 
)
(assert 
(forall ((x Lst) (y Lst) (z Lst)) (= (qreva (qreva x y) z) (qreva y (append x z)))) ; G-amortize-queue-10 
)
(assert 
(forall ((x Lst) (y Lst) (z Lst)) (= (append x (append y z)) (append (append x y) z))) ; G-amortize-queue-11 
)
(assert 
(forall ((x Lst) (y Lst)) (= (queue-to-lst (queue x y)) (queue-to-lst (amortizeQueue x y)))) ; G-amortize-queue-12 
)

; conjecture
(assert (not 
(forall ((x Lst) (y Lst)) (= (butlast (queue-to-lst (queue x y))) (queue-to-lst (qpop (queue x y))))) ; G-amortize-queue-13 
))
(check-sat)

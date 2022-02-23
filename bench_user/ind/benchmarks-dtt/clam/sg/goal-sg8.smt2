
(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))
(declare-datatypes () ((Tree (node (data Int) (left Tree) (right Tree)) (leaf))))
(declare-datatypes () ((Pair (mkpair (first Int) (second Int)))
                       (ZLst (zcons (zhead Pair) (ztail ZLst)) (znil))))
(declare-fun less (Int Int) Bool)
(declare-fun plus (Int Int) Int)
(declare-fun mult (Int Int) Int)
(declare-fun qmult (Int Int Int) Int)
(declare-fun exp (Int Int) Int)
(declare-fun qexp (Int Int Int) Int)
(declare-fun fac (Int) Int)
(declare-fun qfac (Int Int) Int)
(declare-fun double (Int) Int)
(declare-fun half (Int) Int)
(declare-fun even (Int) Bool)
(declare-fun append (Lst Lst) Lst)
(declare-fun len (Lst) Int)
(declare-fun drop (Int Lst) Lst)
(declare-fun take (Int Lst) Lst)
(declare-fun count (Int Lst) Int)
(declare-fun mem (Int Lst) Bool)
(declare-fun rev (Lst) Lst)
(declare-fun qreva (Lst Lst) Lst)
(declare-fun insort (Int Lst) Lst)
(declare-fun sorted (Lst) Bool)
(declare-fun sort (Lst) Lst)
(declare-fun rotate (Int Lst) Lst)
(declare-fun revflat (Tree) Lst)
(declare-fun qrevaflat (Tree Lst) Lst)
(declare-fun lst-mem (Int (Set Int)) Bool)
(declare-fun lst-subset ((Set Int) (Set Int)) Bool)
(declare-fun lst-eq ((Set Int) (Set Int)) Bool)
(declare-fun lst-intersection ((Set Int) (Set Int)) (Set Int))
(declare-fun lst-union ((Set Int) (Set Int)) (Set Int))
(define-fun leq ((x Int) (y Int)) Bool (or (= x y) (less x y)))
(assert (forall ((x Int)) (= (drop x nil) nil)))
(assert (forall ((x Lst)) (= (drop 0 x) x)))
(assert (forall ((x Int) (y Int) (z Lst)) (=> (>= x 0) (= (drop (+ x 1) (cons y z)) (drop x z)))))

; sub-goals
(assert 
(forall ((w Int) (x Int) (y Int) (z Lst)) (=> (and (>= w 0) (>= x 0)) (= (drop (+ 1 w) (drop x (cons y z))) (drop w (drop x z)))))  ; G54 
)
(assert 
(forall ((v Int) (w Int) (x Int) (y Int) (z Lst)) (=> (and (>= v 0) (>= w 0)) (= (drop (+ 1 v) (drop (+ 1 w) (cons x (cons y z)))) (drop (+ 1 v) (drop w (cons x z))))))  ; G55 
)

; conjecture
(assert (not 
(forall ((x Int) (y Int) (z Lst)) (=> (and (>= x 0) (>= y 0)) (= (drop x (drop y z)) (drop y (drop x z)))))  ; G8 
))
(check-sat)

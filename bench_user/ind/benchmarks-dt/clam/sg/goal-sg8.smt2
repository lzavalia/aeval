
(declare-datatypes () ((Nat (succ (pred Nat)) (zero))))
(declare-datatypes () ((Lst (cons (head Nat) (tail Lst)) (nil))))
(declare-datatypes () ((Tree (node (data Nat) (left Tree) (right Tree)) (leaf))))
(declare-datatypes () ((Pair (mkpair (first Nat) (second Nat)))
                       (ZLst (zcons (zhead Pair) (ztail ZLst)) (znil))))
(declare-fun less (Nat Nat) Bool)
(declare-fun plus (Nat Nat) Nat)
(declare-fun mult (Nat Nat) Nat)
(declare-fun qmult (Nat Nat Nat) Nat)
(declare-fun exp (Nat Nat) Nat)
(declare-fun qexp (Nat Nat Nat) Nat)
(declare-fun fac (Nat) Nat)
(declare-fun qfac (Nat Nat) Nat)
(declare-fun double (Nat) Nat)
(declare-fun half (Nat) Nat)
(declare-fun even (Nat) Bool)
(declare-fun append (Lst Lst) Lst)
(declare-fun len (Lst) Nat)
(declare-fun drop (Nat Lst) Lst)
(declare-fun take (Nat Lst) Lst)
(declare-fun count (Nat Lst) Nat)
(declare-fun mem (Nat Lst) Bool)
(declare-fun rev (Lst) Lst)
(declare-fun qreva (Lst Lst) Lst)
(declare-fun insort (Nat Lst) Lst)
(declare-fun sorted (Lst) Bool)
(declare-fun sort (Lst) Lst)
(declare-fun rotate (Nat Lst) Lst)
(declare-fun revflat (Tree) Lst)
(declare-fun qrevaflat (Tree Lst) Lst)
(declare-fun lst-mem (Nat Lst) Bool)
(declare-fun lst-subset (Lst Lst) Bool)
(declare-fun lst-eq (Lst Lst) Bool)
(declare-fun lst-intersection (Lst Lst) Lst)
(declare-fun lst-union (Lst Lst) Lst)
(define-fun leq ((x Nat) (y Nat)) Bool (or (= x y) (less x y)))
(assert (forall ((x Nat)) (= (drop x nil) nil)))
(assert (forall ((x Lst)) (= (drop zero x) x)))
(assert (forall ((x Nat) (y Nat) (z Lst)) (= (drop (succ x) (cons y z)) (drop x z))))

; sub-goals
(assert 
(forall ((w Nat) (x Nat) (y Nat) (z Lst)) (= (drop (succ w) (drop x (cons y z))) (drop w (drop x z))))  ; G54 
)
(assert 
(forall ((v Nat) (w Nat) (x Nat) (y Nat) (z Lst)) (= (drop (succ v) (drop (succ w) (cons x (cons y z)))) (drop (succ v) (drop w (cons x z)))))  ; G55 
)

; conjecture
(assert (not 
(forall ((x Nat) (y Nat) (z Lst)) (= (drop x (drop y z)) (drop y (drop x z))))  ; G8 
))
(check-sat)

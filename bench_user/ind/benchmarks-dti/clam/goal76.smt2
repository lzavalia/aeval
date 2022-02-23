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
(declare-fun nat-to-int (Nat) Int)
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
(declare-fun lst-to-set (Lst) (Set Nat))
(define-fun leq ((x Nat) (y Nat)) Bool (or (= x y) (less x y)))
(assert (forall ((x Nat)) (>= (nat-to-int x) 0)))
(assert (forall ((x Nat) (y Nat)) (=> (= (nat-to-int x) (nat-to-int y)) (= x y))))
(assert (= (nat-to-int zero) 0))
(assert (forall ((x Nat)) (= (nat-to-int (succ x)) (+ 1 (nat-to-int x)))))
(assert (forall ((x Lst)) (= (qrevaflat leaf x) x)))
(assert (forall ((d Nat) (l Tree) (r Tree) (x Lst)) (= (qrevaflat (node d l r) x) (qrevaflat l (cons d (qrevaflat r x))))))
(assert (forall ((x Lst)) (= (append nil x) x)))
(assert (forall ((x Nat) (y Lst) (z Lst)) (= (append (cons x y) z) (cons x (append y z)))))
(assert (= (rev nil) nil))
(assert (forall ((x Nat) (y Lst)) (= (rev (cons x y)) (append (rev y) (cons x nil)))))
(assert (forall ((x Lst)) (= (qreva nil x) x)))
(assert (forall ((x Lst) (y Lst) (z Nat)) (= (qreva (cons z x) y) (qreva x (cons z y)))))
(assert (= (revflat leaf) nil))
(assert (forall ((d Nat) (l Tree) (r Tree)) (= (revflat (node d l r)) (append (revflat l) (cons d (revflat r))))))
(assert (not 
(forall ((x Tree) (y Lst)) (= (append (revflat x) y) (qrevaflat x y))) ; G76 
))
(check-sat)

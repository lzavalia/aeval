(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))
(declare-datatypes () ((Tree (node (data Int) (left Tree) (right Tree)) (leaf))))
(declare-datatypes () ((Pair (mkpair (first Int) (second Int)))
                       (ZLst (zcons (zhead Pair) (ztail ZLst)) (znil))))
(declare-fun P (Int) Bool)
(declare-fun f (Int) Int)
(declare-fun less (Int Int) Bool)
(declare-fun plus (Int Int) Int)
(declare-fun minus (Int Int) Int)
(declare-fun mult (Int Int) Int)
(declare-fun nmax (Int Int) Int)
(declare-fun nmin (Int Int) Int)
(declare-fun append (Lst Lst) Lst)
(declare-fun len (Lst) Int)
(declare-fun drop (Int Lst) Lst)
(declare-fun take (Int Lst) Lst)
(declare-fun count (Int Lst) Int)
(declare-fun last (Lst) Int)
(declare-fun butlast (Lst) Lst)
(declare-fun mem (Int Lst) Bool)
(declare-fun delete (Int Lst) Lst)
(declare-fun rev (Lst) Lst)
(declare-fun lmap (Lst) Lst)
(declare-fun filter (Lst) Lst)
(declare-fun dropWhile (Lst) Lst)
(declare-fun takeWhile (Lst) Lst)
(declare-fun ins1 (Int Lst) Lst)
(declare-fun insort (Int Lst) Lst)
(declare-fun sorted (Lst) Bool)
(declare-fun sort (Lst) Lst)
(declare-fun zip (Lst Lst) ZLst)
(declare-fun zappend (ZLst ZLst) ZLst)
(declare-fun zdrop (Int ZLst) ZLst)
(declare-fun ztake (Int ZLst) ZLst)
(declare-fun zrev (ZLst) ZLst)
(declare-fun mirror (Tree) Tree)
(declare-fun height (Tree) Int)
(define-fun leq ((x Int) (y Int)) Bool (or (= x y) (less x y)))
(assert (forall ((x Int)) (=> (>= x 0) (= (less (+ 1 x) 0) false))))
(assert (forall ((x Int)) (=> (>= x 0) (= (less 0 (+ 1 x)) true))))
(assert (forall ((x Int) (y Int)) (=> (and (>= x 0) (>= y 0)) (= (less (+ 1 x) (+ 1 y)) (less x y)))))
(assert (forall ((x Int) (y Int)) (=> (and (>= x 0) (>= y 0)) (= (less x y) (< x y)))))
(assert (forall ((x Int)) (= (mem x nil) false)))
(assert (forall ((x Int) (y Int) (z Lst)) (= (mem x (cons y z)) (or (= x y) (mem x z)))))
(assert (forall ((i Int)) (= (insort i nil) (cons i nil))))
(assert (forall ((i Int) (x Int) (y Lst)) (= (insort i (cons x y)) (ite (less i x) (cons i (cons x y)) (cons x (insort i y))))))
(assert (= (sort nil) nil))
(assert (forall ((x Int) (y Lst)) (= (sort (cons x y)) (insort x (sort y)))))
(assert (not 
(forall ((x Int) (y Int) (l Lst)) (=> (not (= x y)) (= (mem x (insort y l)) (mem x l)))) ; G73 
))
(check-sat)

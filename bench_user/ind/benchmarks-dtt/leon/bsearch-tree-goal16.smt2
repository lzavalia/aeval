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

(declare-fun nmax (Int Int) Int)
(assert (forall ((n Int) (m Int)) (= (nmax n m) (ite (less n m) m n))))

; lists      
(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))

(declare-fun append (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (append nil x) x)))
(assert (forall ((x Int) (y Lst) (z Lst)) (= (append (cons x y) z) (cons x (append y z)))))

(declare-fun len (Lst) Int)
(assert (= (len nil) 0))
(assert (forall ((x Int) (y Lst)) (= (len (cons x y)) (+ 1 (len y)))))
; since len returns Nat, we can assume this "lemma"
(assert (forall ((x Lst)) (>= (len x) 0)))

(declare-fun mem (Int Lst) Bool)
(assert (forall ((x Int)) (not (mem x nil))))
(assert (forall ((x Int) (y Int) (z Lst)) (= (mem x (cons y z)) (or (= x y) (mem x z)))))

; (binary search) tree
(declare-datatypes () ((Tree (node (data Int) (left Tree) (right Tree)) (leaf))))

(declare-fun tinsert (Tree Int) Tree)
(assert (forall ((i Int)) (= (tinsert leaf i) (node i leaf leaf))))
(assert (forall ((r Tree) (l Tree) (d Int) (i Int)) (= (tinsert (node d l r) i) (ite (less d i) (node d l (tinsert r i)) (node d (tinsert l i) r)))))

(declare-fun height (Tree) Int)
(assert (= (height leaf) 0))
(assert (forall ((x Int) (y Tree) (z Tree)) (= (height (node x y z)) (+ 1 (nmax (height y) (height z))))))
; since returns Nat, we can assume this "lemma"
(assert (forall ((x Tree)) (>= (height x) 0)))

(declare-fun tinsert-all (Tree Lst) Tree)
(assert (forall ((x Tree)) (= (tinsert-all x nil) x)))
(assert (forall ((x Tree) (n Int) (l Lst)) (= (tinsert-all x (cons n l)) (tinsert (tinsert-all x l) n))))

(declare-fun tsize (Tree) Int)
(assert (= (tsize leaf) 0))
(assert (forall ((x Int) (l Tree) (r Tree)) (= (tsize (node x l r)) (+ 1 (plus (tsize l) (tsize r))))))
; since returns Nat, we can assume this "lemma"
(assert (forall ((x Tree)) (>= (tsize x) 0)))

(declare-fun tremove (Tree Int) Tree)
(assert (forall ((i Int)) (= (tremove leaf i) leaf)))
(assert (forall ((i Int) (d Int) (l Tree) (r Tree)) (=> (less i d) (= (tremove (node d l r) i) (node d (tremove l i) r)))))
(assert (forall ((i Int) (d Int) (l Tree) (r Tree)) (=> (less d i) (= (tremove (node d l r) i) (node d l (tremove r i))))))
(assert (forall ((d Int) (r Tree)) (= (tremove (node d leaf r) d) r)))
(assert (forall ((d Int) (ld Int) (ll Tree) (lr Tree) (r Tree)) (= (tremove (node d (node ld ll lr) r) d) (node ld (tremove (node ld ll lr) ld) r))))

(declare-fun tremove-all (Tree Lst) Tree)
(assert (forall ((x Tree)) (= (tremove-all x nil) x)))
(assert (forall ((x Tree) (n Int) (l Lst)) (= (tremove-all x (cons n l)) (tremove-all (tremove x n) l))))

(declare-fun tcontains (Tree Int) Bool)
(assert (forall ((i Int)) (not (tcontains leaf i))))
(assert (forall ((d Int) (l Tree) (r Tree) (i Int)) (= (tcontains (node d l r) i) (or (= d i) (tcontains l i) (tcontains r i)))))

(declare-fun tsorted (Tree) Bool)
(assert (tsorted leaf))
(assert (forall ((d Int) (l Tree) (r Tree)) (= (tsorted (node d l r)) (and (tsorted l) (tsorted r)
                                                                           (forall ((x Int)) (=> (tcontains l x) (leq x d)))
                                                                           (forall ((x Int)) (=> (tcontains r x) (less d x)))))))
                                                                           
(declare-fun tmember (Tree Int) Bool)
(assert (forall ((x Int)) (not (tmember leaf x))))
(assert (forall ((d Int) (l Tree) (r Tree) (i Int)) (= (tmember (node d l r) i) (ite (= i d) true (tmember (ite (less d i) r l) i)))))
                              
(declare-fun content (Tree) Lst)
(assert (= (content leaf) nil))
(assert (forall ((d Int) (l Tree) (r Tree)) (= (content (node d l r)) (append (content l) (cons d (content r))))))

; proven
(assert 
(forall ((t Tree) (n Int)) (= (tsize (tinsert t n)) (+ 1 (tsize t)))) ; G-bsearch-tree-1 
)
(assert 
(forall ((l Lst) (t Tree)) (leq (tsize t) (tsize (tinsert-all t l)))) ; G-bsearch-tree-2 
)
(assert 
(forall ((l Lst) (t Tree)) (= (tsize (tinsert-all t l)) (plus (tsize t) (len l)))) ; G-bsearch-tree-3 
)
(assert 
(forall ((t Tree) (n Int)) (leq (tsize (tremove t n)) (tsize t))) ; G-bsearch-tree-4 
)
(assert 
(forall ((l Lst) (t Tree)) (leq (tsize (tremove-all t l)) (tsize t))) ; G-bsearch-tree-5 
)
(assert 
(forall ((x Tree) (i Int)) (tcontains (tinsert x i) i)) ; G-bsearch-tree-6 
)
(assert 
(forall ((i Int) (x Tree) (j Int)) (= (or (= i j) (tcontains x j)) (tcontains (tinsert x i) j))) ; G-bsearch-tree-7 
)
(assert 
(forall ((x Tree) (i Int)) (=> (tsorted x) (tsorted (tinsert x i)))) ; G-bsearch-tree-8 
)
(assert 
(forall ((x Tree) (i Int)) (tmember (tinsert x i) i)) ; G-bsearch-tree-9 
)
(assert 
(forall ((i Int) (x Tree) (j Int)) (= (or (= i j) (tmember x j)) (tmember (tinsert x i) j))) ; G-bsearch-tree-10 
)
(assert 
(forall ((i Int) (x Tree)) (=> (tsorted x) (= (tcontains x i) (tmember x i)))) ; G-bsearch-tree-11 
)
(assert 
(forall ((i Int) (x Tree)) (=> (tmember x i) (tcontains x i))) ; G-bsearch-tree-12 
)
(assert 
(forall ((l Lst) (x Tree) (n Int)) (= (tinsert-all (tinsert x n) l) (tinsert-all x (append l (cons n nil))))) ; G-bsearch-tree-13 
)
(assert 
(forall ((x Lst)) (tsorted (tinsert-all leaf x))) ; G-bsearch-tree-14 
)
(assert 
(forall ((x Lst) (i Int)) (= (mem i x) (tcontains (tinsert-all leaf x) i))) ; G-bsearch-tree-15 
)

; conjecture
(assert (not 
(forall ((x Lst) (y Lst) (i Int)) (= (mem i (append x y)) (or (mem i x) (mem i y)))) ; G-bsearch-tree-16 
))
(check-sat)

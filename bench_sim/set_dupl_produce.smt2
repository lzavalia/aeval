(declare-sort Elem)
(declare-datatypes () ((Lst (cons (head Elem) (tail Lst)) (nil))))

(declare-fun R (Lst (Array Elem Bool)) Bool)

(declare-fun C (Elem Lst) Bool)
(assert (forall ((x Elem)) (= (C x nil) false)))
(assert (forall ((x Elem) (y Elem) (xs Lst)) (= (C x (cons y xs)) (or (= x y) (C x xs)))))

(assert (forall ((A (Array Elem Bool))) (= (R nil A) (forall ((a Elem)) (= false (select A a))))))
(assert (forall ((xs Lst) (out Elem) (A (Array Elem Bool)))
    (= (R (cons out xs) A) (and (select A out)
        (ite (C out xs) (R xs A) (R xs (store A out false)))))))

; extra lemma 1 
(assert (forall ((xs Lst) (A (Array Elem Bool)) (x Elem) (y Elem))
  (=> (and (R xs A) (C y xs)) (= A (store A y true)))))

; extra lemma 2
(assert (forall ((xs Lst) (A (Array Elem Bool)) (x Elem))
  (=> (and (R xs A) (not (C x xs))) (= A (store A x false)))))

; producing op check:

(assert (not
  (forall ((xs Lst) (in Elem) (A (Array Elem Bool)))
    (=> (R xs A) (R (cons in xs) (store A in true))))))
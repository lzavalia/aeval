(set-logic HORN)

(declare-datatypes ((treeOfInt 0) )
(((node-treeOfInt (data-treeOfInt Int) (left-treeOfInt treeOfInt) (right-treeOfInt treeOfInt)) (leaf-treeOfInt))))
(declare-datatypes ((listOfInt 0) )
(((cons-listOfInt (head-listOfInt Int) (tail-listOfInt listOfInt)) (nil-listOfInt))))

(declare-fun tinsert (treeOfInt Int treeOfInt) Bool)
(declare-fun tsize (treeOfInt Int) Bool)
(declare-fun tinsertall (treeOfInt listOfInt treeOfInt) Bool)
(declare-fun len (listOfInt Int) Bool)
(declare-fun ff () Bool)

(assert
  (forall ( (A Int) )
    (=>
      (= A 0)
      (len nil-listOfInt A)
    )
  )
)
(assert
  (forall ( (A Int) (B listOfInt) (C Int) (D Int) )
    (=>
      (and
        (= C (+ 1 D))
        (len B D)
      )
      (len (cons-listOfInt A B) C)
    )
  )
)
(assert
  (forall ( (A Int) )
    (=>
      (= A 0)
      (tsize leaf-treeOfInt A)
    )
  )
)
(assert
  (forall ( (A Int) (B treeOfInt) (C treeOfInt) (D Int) (E Int) (F Int) (G Int) )
    (=>
      (and
        (= D (+ 1 E))
        (= (+ F G) E)
        (tsize B F)
        (tsize C G)
      )
      (tsize (node-treeOfInt A B C)  D)
    )
  )
)
(assert
  (forall ( (A Int) )
    (tinsert leaf-treeOfInt A (node-treeOfInt A leaf-treeOfInt leaf-treeOfInt) )
  )
)
(assert
  (forall ( (A Int) (B treeOfInt) (C treeOfInt) (D Int) (E treeOfInt) )
    (=>
      (and
        (<= A (- D 1))
        (tinsert C D E)
      )
      (tinsert (node-treeOfInt A B C)  D (node-treeOfInt A B E) )
    )
  )
)
(assert
  (forall ( (A Int) (B treeOfInt) (C treeOfInt) (D Int) (E treeOfInt) )
    (=>
      (and
        (>= A D)
        (tinsert B D E)
      )
      (tinsert (node-treeOfInt A B C)  D (node-treeOfInt A E C) )
    )
  )
)
(assert
  (forall ( (A treeOfInt) )
    (tinsertall A nil-listOfInt A)
  )
)
(assert
  (forall ( (A treeOfInt) (B Int) (C listOfInt) (D treeOfInt) (E treeOfInt) )
    (=>
      (and
        (tinsertall A C E)
        (tinsert E B D)
      )
      (tinsertall A (cons-listOfInt B C) D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E treeOfInt) (F listOfInt) (G treeOfInt) )
    (=>
      (and
        (not (= A B))
        (= (+ C D) A)
        (tinsertall E F G)
        (tsize G B)
        (tsize E C)
        (len F D)
      )
      ff
    )
  )
)

(assert (not ff))
(check-sat)

(set-logic HORN)

(declare-datatypes ((treeOfInt 0) )
(((node-treeOfInt (data-treeOfInt Int) (left-treeOfInt treeOfInt) (right-treeOfInt treeOfInt)) (leaf-treeOfInt))))
(declare-datatypes ((listOfInt 0) )
(((cons-listOfInt (head-listOfInt Int) (tail-listOfInt listOfInt)) (nil-listOfInt))))

(declare-fun tinsert (treeOfInt Int treeOfInt) Bool)
(declare-fun tsize (treeOfInt Int) Bool)
(declare-fun ff () Bool)

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
  (forall ( (A Int) (B Int) (C treeOfInt) (D Int) (E treeOfInt) )
    (=>
      (and
        (not (= (- A B) 1))
        (tinsert C D E)
        (tsize E A)
        (tsize C B)
      )
      ff
    )
  )
)

(assert (not ff))
(check-sat)

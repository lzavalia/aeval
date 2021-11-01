(set-logic HORN)

(declare-datatypes ((treeOfInt 0) )
(((node-treeOfInt (data-treeOfInt Int) (left-treeOfInt treeOfInt) (right-treeOfInt treeOfInt)) (leaf-treeOfInt))))
(declare-datatypes ((listOfInt 0) )
(((cons-listOfInt (head-listOfInt Int) (tail-listOfInt listOfInt)) (nil-listOfInt))))

(declare-fun tinsert (treeOfInt Int treeOfInt) Bool)
(declare-fun tmember (treeOfInt Int Bool) Bool)
(declare-fun ff () Bool)

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
  (forall ( (A Int) (B Bool) )
    (=>
      (= B false)
      (tmember leaf-treeOfInt A B)
    )
  )
)
(assert
  (forall ( (A Int) (B treeOfInt) (C treeOfInt) (D Bool) )
    (=>
      (= D true)
      (tmember (node-treeOfInt A B C)  A D)
    )
  )
)
(assert
  (forall ( (A Int) (B treeOfInt) (C treeOfInt) (D Int) (E Bool) (F Bool) )
    (=>
      (and
        (>= (- D A) 1)
        (tmember C D E)
        (< A D)
      )
      (tmember (node-treeOfInt A B C)  D E)
    )
  )
)
(assert
  (forall ( (A Int) (B treeOfInt) (C treeOfInt) (D Int) (E Bool) (F Bool) )
    (=>
      (and
        (<= (- D A) (- 1))
        (tmember B D E)
        (>= A D)
      )
      (tmember (node-treeOfInt A B C)  D E)
    )
  )
)

(assert
  (forall ( (A Bool) (B treeOfInt) (C Int) (D treeOfInt) )
    (=>
      (and
        (not (= A true))
        (tinsert B C D)
        (tmember D C A)
      )
      ff
    )
  )
)

(assert (not ff))
(check-sat)

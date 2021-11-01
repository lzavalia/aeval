(set-logic HORN)

(declare-datatypes ((treeOfInt 0) )
(((node-treeOfInt (data-treeOfInt Int) (left-treeOfInt treeOfInt) (right-treeOfInt treeOfInt)) (leaf-treeOfInt))))
(declare-datatypes ((listOfInt 0) )
(((cons-listOfInt (head-listOfInt Int) (tail-listOfInt listOfInt)) (nil-listOfInt))))

(declare-fun tinsert (treeOfInt Int treeOfInt) Bool)
 (declare-fun tsorted (treeOfInt Bool) Bool)
(declare-fun tallleq (treeOfInt Int Bool) Bool)
(declare-fun tallgt (treeOfInt Int Bool) Bool)
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
  (forall ( (A Bool) )
    (=>
      (= A true)
      (tsorted leaf-treeOfInt A)
    )
  )
)
(assert
  (forall ( (A Int) (B treeOfInt) (C treeOfInt) (D Bool) )
    (=>
      (and
        (= D true)
        (tsorted B D)
        (tsorted C D)
        (tallleq B A D)
        (tallgt C A D)
      )
      (tsorted (node-treeOfInt A B C)  D)
    )
  )
)
(assert
  (forall ( (A Int) (B treeOfInt) (C treeOfInt) (D Bool) )
    (=>
      (and
        (= D false)
        (tsorted B D)
      )
      (tsorted (node-treeOfInt A B C)  D)
    )
  )
)
(assert
  (forall ( (A Int) (B treeOfInt) (C treeOfInt) (D Bool) )
    (=>
      (and
        (= D false)
        (tsorted C D)
      )
      (tsorted (node-treeOfInt A B C)  D)
    )
  )
)
(assert
  (forall ( (A Int) (B treeOfInt) (C treeOfInt) (D Bool) )
    (=>
      (and
        (= D false)
        (tallleq B A D)
      )
      (tsorted (node-treeOfInt A B C)  D)
    )
  )
)
(assert
  (forall ( (A Int) (B treeOfInt) (C treeOfInt) (D Bool) )
    (=>
      (and
        (= D false)
        (tallgt C A D)
      )
      (tsorted (node-treeOfInt A B C)  D)
    )
  )
)

(assert
  (forall ( (A Int) (B Bool) )
    (=>
      (= B true)
      (tallleq leaf-treeOfInt A B)
    )
  )
)
(assert
  (forall ( (A Int) (B treeOfInt) (C treeOfInt) (D Int) (E Bool) )
    (=>
      (and
        (= E true)
        (<= A D)
        (tallleq B D E)
        (tallleq C D E)
      )
      (tallleq (node-treeOfInt A B C)  D E)
    )
  )
)
(assert
  (forall ( (A Int) (B treeOfInt) (C treeOfInt) (D Int) (E Bool) )
    (=>
      (and
        (= E false)
        (>= A (+ D 1))
      )
      (tallleq (node-treeOfInt A B C)  D E)
    )
  )
)
(assert
  (forall ( (A Int) (B treeOfInt) (C treeOfInt) (D Int) (E Bool) )
    (=>
      (and
        (= E false)
        (tallleq B D E)
      )
      (tallleq (node-treeOfInt A B C)  D E)
    )
  )
)
(assert
  (forall ( (A Int) (B treeOfInt) (C treeOfInt) (D Int) (E Bool) )
    (=>
      (and
        (= E false)
        (tallleq C D E)
      )
      (tallleq (node-treeOfInt A B C)  D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) )
    (=>
      (= B true)
      (tallgt leaf-treeOfInt A B)
    )
  )
)
(assert
  (forall ( (A Int) (B treeOfInt) (C treeOfInt) (D Int) (E Bool) )
    (=>
      (and
        (= E true)
        (>= A (+ D 1))
        (tallgt B D E)
        (tallgt C D E)
      )
      (tallgt (node-treeOfInt A B C)  D E)
    )
  )
)
(assert
  (forall ( (A Int) (B treeOfInt) (C treeOfInt) (D Int) (E Bool) )
    (=>
      (and
        (= E false)
        (<= A D)
      )
      (tallgt (node-treeOfInt A B C)  D E)
    )
  )
)
(assert
  (forall ( (A Int) (B treeOfInt) (C treeOfInt) (D Int) (E Bool) )
    (=>
      (and
        (= E false)
        (tallgt B D E)
      )
      (tallgt (node-treeOfInt A B C)  D E)
    )
  )
)
(assert
  (forall ( (A Int) (B treeOfInt) (C treeOfInt) (D Int) (E Bool) )
    (=>
      (and
        (= E false)
        (tallgt C D E)
      )
      (tallgt (node-treeOfInt A B C)  D E)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C treeOfInt) (D Int) (E treeOfInt) )
    (=>
      (and
        (= A true)
        (not (= B true))
        (tinsert C D E)
        (tsorted E B)
        (tsorted C A)
      )
      ff
    )
  )
)

(assert (not ff))
(check-sat)

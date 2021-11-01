(set-logic HORN)

(declare-datatypes ((treeOfInt 0) )
(((node-treeOfInt (data-treeOfInt Int) (left-treeOfInt treeOfInt) (right-treeOfInt treeOfInt)) (leaf-treeOfInt))))
(declare-datatypes ((listOfInt 0) )
(((cons-listOfInt (head-listOfInt Int) (tail-listOfInt listOfInt)) (nil-listOfInt))))

(declare-fun tmember (treeOfInt Int Bool) Bool)
(declare-fun tcontains (treeOfInt Int Bool) Bool)
(declare-fun ff () Bool)

(assert
  (forall ( (A Int) (B Bool) )
    (=>
      (= B false)
      (tcontains leaf-treeOfInt A B)
    )
  )
)
(assert
  (forall ( (A Int) (B treeOfInt) (C treeOfInt) (D Bool) )
    (=>
      (= D true)
      (tcontains (node-treeOfInt A B C)  A D)
    )
  )
)
(assert
  (forall ( (A Int) (B treeOfInt) (C treeOfInt) (D Int) (E Bool) )
    (=>
      (and
        (= E true)
        (tcontains B D E)
      )
      (tcontains (node-treeOfInt A B C)  D E)
    )
  )
)
(assert
  (forall ( (A Int) (B treeOfInt) (C treeOfInt) (D Int) (E Bool) )
    (=>
      (and
        (= E true)
        (tcontains C D E)
      )
      (tcontains (node-treeOfInt A B C)  D E)
    )
  )
)
(assert
  (forall ( (A Int) (B treeOfInt) (C treeOfInt) (D Int) (E Bool) )
    (=>
      (and
        (= E false)
        (>= (- D A) 1)
        (tcontains B D E)
        (tcontains C D E)
      )
      (tcontains (node-treeOfInt A B C)  D E)
    )
  )
)
(assert
  (forall ( (A Int) (B treeOfInt) (C treeOfInt) (D Int) (E Bool) )
    (=>
      (and
        (= E false)
        (<= (- D A) (- 1))
        (tcontains B D E)
        (tcontains C D E)
      )
      (tcontains (node-treeOfInt A B C)  D E)
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
  (forall ( (A Bool) (B Bool) (C treeOfInt) (D Int) )
    (=>
      (and
        (= A true)
        (not (= B true))
        (tcontains C D B)
        (tmember C D A)
      )
      ff
    )
  )
)

(assert (not ff))
(check-sat)

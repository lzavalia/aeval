(set-logic HORN)

(declare-datatypes ((treeOfInt 0) )
(((node-treeOfInt (data-treeOfInt Int) (left-treeOfInt treeOfInt) (right-treeOfInt treeOfInt)) (leaf-treeOfInt))))
(declare-datatypes ((listOfInt 0) )
(((cons-listOfInt (head-listOfInt Int) (tail-listOfInt listOfInt)) (nil-listOfInt))))

(declare-fun tinsert (treeOfInt Int treeOfInt) Bool)
(declare-fun tinsertall (treeOfInt listOfInt treeOfInt) Bool)
(declare-fun tcontains (treeOfInt Int Bool) Bool)
(declare-fun mem (Int listOfInt Bool) Bool)

(declare-fun ff () Bool)

(assert
  (forall ( (A Int) (B Bool) )
    (=>
      (= B false)
      (mem A nil-listOfInt B)
    )
  )
)
(assert
  (forall ( (A Int) (B listOfInt) (C Bool) )
    (=>
      (= C true)
      (mem A (cons-listOfInt A B) C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C listOfInt) (D Bool) )
    (=>
      (and
        (= D true)
        (mem A C D)
      )
      (mem A (cons-listOfInt B C) D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C listOfInt) (D Bool) )
    (=>
      (and
        (= D false)
        (>= (- B A) 1)
        (mem A C D)
      )
      (mem A (cons-listOfInt B C) D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C listOfInt) (D Bool) )
    (=>
      (and
        (= D false)
        (<= (- B A) (- 1))
        (mem A C D)
      )
      (mem A (cons-listOfInt B C) D)
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
  (forall ( (A Bool) (B Bool) (C Int) (D listOfInt) (E treeOfInt) )
    (=>
      (and
        (not (= A B))
        (mem C D A)
        (tinsertall leaf-treeOfInt D E)
        (tcontains E C B)
      )
      ff
    )
  )
)

(assert (not ff))
(check-sat)

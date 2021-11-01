(set-logic HORN)

(declare-datatypes ((treeOfInt 0) )
(((node-treeOfInt (data-treeOfInt Int) (left-treeOfInt treeOfInt) (right-treeOfInt treeOfInt)) (leaf-treeOfInt))))
(declare-datatypes ((listOfInt 0) )
(((cons-listOfInt (head-listOfInt Int) (tail-listOfInt listOfInt)) (nil-listOfInt))))

(declare-fun tinsert (treeOfInt Int treeOfInt) Bool)
(declare-fun tinsertall (treeOfInt listOfInt treeOfInt) Bool)
(declare-fun mem (Int listOfInt Bool) Bool)
(declare-fun append (listOfInt listOfInt listOfInt) Bool)
(declare-fun content (treeOfInt listOfInt) Bool)
(declare-fun tcontains (treeOfInt Int Bool) Bool)


(declare-fun ff () Bool)

(assert
  (forall ( (A listOfInt) )
    (append nil-listOfInt A A)
  )
)
(assert
  (forall ( (A Int) (B listOfInt) (C listOfInt) (D listOfInt) )
    (=>
      (append B C D)
      (append (cons-listOfInt A B) C (cons-listOfInt A D))
    )
  )
)
(assert
    (content leaf-treeOfInt nil-listOfInt)
)
(assert
  (forall ( (A Int) (B treeOfInt) (C treeOfInt) (D listOfInt) (E listOfInt) (F listOfInt) )
    (=>
      (and
        (content B E)
        (content C F)
        (append E (cons-listOfInt A F) D)
      )
      (content (node-treeOfInt A B C)  D)
    )
  )
)
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
  (forall ( (A Bool) (B Bool) (C treeOfInt) (D Int) (E listOfInt) )
    (=>
      (and
        (not (= A B))
        (tcontains C D A)
        (content C E)
        (mem D E B)
      )
      ff
    )
  )
)

(assert (not ff))
(check-sat)

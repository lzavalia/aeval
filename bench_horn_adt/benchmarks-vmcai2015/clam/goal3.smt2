(set-logic HORN)

(declare-datatypes ((listOfInt 0) )
(((cons-listOfInt (head-listOfInt Int) (tail-listOfInt listOfInt)) (nil-listOfInt))))

(declare-fun len (listOfInt Int) Bool)
(declare-fun append (listOfInt listOfInt listOfInt) Bool)
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
  (forall ( (A Int) (B Int) (C Int) (D Int) (E listOfInt) (F listOfInt) (G listOfInt) )
    (=>
      (and
        (not (= A B))
        (= (+ C D) A)
        (append E F G)
        (len G B)
        (len E C)
        (len F D)
      )
      ff
    )
  )
)

(assert (not ff))
(check-sat)

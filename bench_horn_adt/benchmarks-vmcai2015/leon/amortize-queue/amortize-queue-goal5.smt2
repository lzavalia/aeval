(set-logic HORN)

(declare-datatypes ((listOfInt 0) )
(((cons-listOfInt (head-listOfInt Int) (tail-listOfInt listOfInt)) (nil-listOfInt))))
(declare-datatypes ((queueOfInt 0) )
(((queue-queueOfInt (front-queueOfInt listOfInt) (back-queueOfInt listOfInt)) )))

(declare-fun len (listOfInt Int) Bool)
(declare-fun butlast (listOfInt listOfInt) Bool)
(declare-fun ff () Bool)

(assert
    (butlast nil-listOfInt nil-listOfInt)
)
(assert
  (forall ( (A Int) )
    (butlast (cons-listOfInt A nil-listOfInt) nil-listOfInt)
  )
)
(assert
  (forall ( (A Int) (B Int) (C listOfInt) (D listOfInt) )
    (=>
      (butlast (cons-listOfInt B C) D)
      (butlast (cons-listOfInt A (cons-listOfInt B C)) (cons-listOfInt A D))
    )
  )
)
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
  (forall ( (A Int) (B Int) (C Int) (D listOfInt) (E listOfInt) )
    (=>
      (and
        (not (= (- A B) 1))
        (butlast (cons-listOfInt C D) E)
        (len E B)
        (len (cons-listOfInt C D) A)
      )
      ff
    )
  )
)

(assert (not ff))
(check-sat)

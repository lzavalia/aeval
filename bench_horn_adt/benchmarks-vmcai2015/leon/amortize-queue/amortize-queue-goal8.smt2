(set-logic HORN)

(declare-datatypes ((listOfInt 0) )
(((cons-listOfInt (head-listOfInt Int) (tail-listOfInt listOfInt)) (nil-listOfInt))))
(declare-datatypes ((queueOfInt 0) )
(((queue-queueOfInt (front-queueOfInt listOfInt) (back-queueOfInt listOfInt)) )))

(declare-fun append (listOfInt listOfInt listOfInt) Bool)
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
  (forall ( (A listOfInt) (B listOfInt) )
    (=>
      (and
        (append A nil-listOfInt B)
        (not (= A B))
      )
      ff
    )
  )
)

(assert (not ff))
(check-sat)

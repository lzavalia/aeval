(set-logic HORN)

(declare-datatypes ((listOfInt 0) )
(((cons-listOfInt (head-listOfInt Int) (tail-listOfInt listOfInt)) (nil-listOfInt))))
(declare-datatypes ((queueOfInt 0) )
(((queue-queueOfInt (front-queueOfInt listOfInt) (back-queueOfInt listOfInt)) )))

(declare-fun qlen (queueOfInt Int) Bool)
(declare-fun len (listOfInt Int) Bool)
(declare-fun ff () Bool)

(assert
  (forall ( (A listOfInt) (B listOfInt) (C Int) (D Int) (E Int) )
    (=>
      (and
        (len A D)
        (len B E)
      )
      (qlen (queue-queueOfInt A B)  (+ D E))
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
  (forall ( (A Int) (B Int) (C Int) (D Int) (E listOfInt) (F listOfInt) )
    (=>
      (and
        (not (= A B))
        (= (+ C D) B)
        (len E C)
        (len F D)
        (qlen (queue-queueOfInt E F)  A)
      )
      ff
    )
  )
)

(assert (not ff))
(check-sat)

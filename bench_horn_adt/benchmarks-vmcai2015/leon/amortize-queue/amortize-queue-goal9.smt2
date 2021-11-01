(set-logic HORN)

(declare-datatypes ((listOfInt 0) )
(((cons-listOfInt (head-listOfInt Int) (tail-listOfInt listOfInt)) (nil-listOfInt))))
(declare-datatypes ((queueOfInt 0) )
(((queue-queueOfInt (front-queueOfInt listOfInt) (back-queueOfInt listOfInt)) )))

(declare-fun append (listOfInt listOfInt listOfInt) Bool)
(declare-fun butlast (listOfInt listOfInt) Bool)
(declare-fun len (listOfInt Int) Bool)
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
  (forall ( (A Bool) (B listOfInt) (C Int) (D listOfInt) (E listOfInt) (F listOfInt) (G listOfInt) (H listOfInt) )
    (=>
      (and
        (append B (cons-listOfInt C D) E)
        (butlast E F)
        (butlast (cons-listOfInt C D) G)
        (append B G H)
        (not (= F H))
      )
      ff
    )
  )
)

(assert (not ff))
(check-sat)

(set-logic HORN)

(declare-datatypes ((listOfInt 0) )
(((cons-listOfInt (head-listOfInt Int) (tail-listOfInt listOfInt)) (nil-listOfInt))))
(declare-datatypes ((queueOfInt 0) )
(((queue-queueOfInt (front-queueOfInt listOfInt) (back-queueOfInt listOfInt)) )))

(declare-fun append (listOfInt listOfInt listOfInt) Bool)
(declare-fun butlast (listOfInt listOfInt) Bool)
(declare-fun len (listOfInt Int) Bool)
(declare-fun qreva (listOfInt listOfInt listOfInt) Bool)
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
  (forall ( (A listOfInt) )
    (qreva nil-listOfInt A A)
  )
)
(assert
  (forall ( (A Int) (B listOfInt) (C listOfInt) (D listOfInt) )
    (=>
      (qreva B (cons-listOfInt A C) D)
      (qreva (cons-listOfInt A B) C D)
    )
  )
)
(assert
  (forall ( (A listOfInt) (B listOfInt) (C listOfInt) (D listOfInt) (E listOfInt) (F listOfInt) (G listOfInt) )
    (=>
      (and
        (qreva A B D)
        (qreva D C E)
        (append A C F)
        (qreva B F G)
        (not (= E G))
      )
      ff
    )
  )
)

(assert (not ff))
(check-sat)
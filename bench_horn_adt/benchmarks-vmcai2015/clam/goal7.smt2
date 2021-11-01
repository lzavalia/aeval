(set-logic HORN)

(declare-datatypes ((listOfInt 0) )
(((cons-listOfInt (head-listOfInt Int) (tail-listOfInt listOfInt)) (nil-listOfInt))))

(declare-fun append (listOfInt listOfInt listOfInt) Bool)
(declare-fun rev (listOfInt listOfInt) Bool)
(declare-fun len (listOfInt Int) Bool)
(declare-fun qreva (listOfInt listOfInt listOfInt) Bool)
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
    (rev nil-listOfInt nil-listOfInt)
)
(assert
  (forall ( (A Int) (B listOfInt) (C listOfInt) (D listOfInt) )
    (=>
      (and
        (rev B D)
        (append D (cons-listOfInt A nil-listOfInt) C)
      )
      (rev (cons-listOfInt A B) C)
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
  (forall ( (A Int) (B Int) (C Int) (D Int) (E listOfInt) (F listOfInt) (G listOfInt) )
    (=>
      (and
        (= (+ C D) A)
        (not (= A B))
        (qreva E F G)
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

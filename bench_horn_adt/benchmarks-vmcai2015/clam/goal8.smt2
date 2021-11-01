(set-logic HORN)

(declare-datatypes ((listOfInt 0) )
(((cons-listOfInt (head-listOfInt Int) (tail-listOfInt listOfInt)) (nil-listOfInt))))

(declare-fun drop (Int listOfInt listOfInt) Bool)
(declare-fun ff () Bool)

(assert
  (forall ( (A Int) )
    (drop A nil-listOfInt nil-listOfInt)
  )
)
(assert
  (forall ( (A Int) (B listOfInt) )
    (=>
      (= A 0)
      (drop A B B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C listOfInt) (D listOfInt) (E Int) )
    (=>
      (and
        (= A (+ 1 E))
        (>= E 0)
        (drop E C D)
      )
      (drop A (cons-listOfInt B C) D)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Int) (D listOfInt) (E listOfInt) (F listOfInt) (G listOfInt) (H listOfInt) )
    (=>
      (and
        (>= B 0)
        (>= C 0)
        (drop C D E)
        (drop B E F)
        (drop B D G)
        (drop C G H)
        (not (= F H))
      )
      ff
    )
  )
)

(assert (not ff))
(check-sat)

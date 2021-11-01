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
  (forall ( (A Bool) (B Int) (C Int) (D Int) (E listOfInt) (F listOfInt) (G listOfInt) (H listOfInt) (I listOfInt) (J listOfInt) (K listOfInt) )
    (=>
      (and
        (>= B 0)
        (>= C 0)
        (>= D 0)
        (drop C E F)
        (drop B F G)
        (drop D G H)
        (drop D E I)
        (drop B I J)
        (drop C J K)
        (not (= H K))
      )
      ff
    )
  )
)

(assert (not ff))
(check-sat)

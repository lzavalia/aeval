(set-logic HORN)

(declare-datatypes ((listOfInt 0) )
(((cons-listOfInt (head-listOfInt Int) (tail-listOfInt listOfInt)) (nil-listOfInt))))

(declare-fun rev (listOfInt listOfInt) Bool)
(declare-fun append (listOfInt listOfInt listOfInt) Bool)
(declare-fun ff () Bool)

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
  (forall ( (A Bool) (B listOfInt) (C listOfInt) (D listOfInt) (E listOfInt) (F listOfInt) (G listOfInt) (H listOfInt) (I listOfInt) (J listOfInt) (K listOfInt) )
    (=>
      (and
        (append B C D)
        (rev D E)
        (rev E F)
        (rev B G)
        (rev G H)
        (rev C I)
        (rev I J)
        (append H J K)
        (not (= F K))
      )
      ff
    )
  )
)

(assert (not ff))
(check-sat)

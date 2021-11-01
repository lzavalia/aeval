(set-logic HORN)

(declare-datatypes ((listOfInt 0) )
(((cons-listOfInt (head-listOfInt Int) (tail-listOfInt listOfInt)) (nil-listOfInt))))

(declare-fun rev (listOfInt listOfInt) Bool)
(declare-fun append (listOfInt listOfInt listOfInt) Bool)
(declare-fun id_list (listOfInt listOfInt) Bool)
(declare-fun len (listOfInt Int) Bool)
(declare-fun rotate (Int listOfInt listOfInt) Bool)
(declare-fun ff () Bool)

(assert
    (id_list nil-listOfInt nil-listOfInt)
)
(assert
  (forall ( (A Int) (B listOfInt) (C listOfInt) )
    (=>
      (id_list B C)
      (id_list (cons-listOfInt A B) (cons-listOfInt A C))
    )
  )
)
(assert
  (forall ( (A Int) (B listOfInt) )
    (=>
      (= A 0)
      (rotate A B B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) )
    (=>
      (and
        (= A (+ 1 B))
        (>= B 0)
      )
      (rotate A nil-listOfInt nil-listOfInt)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C listOfInt) (D listOfInt) (E Int) (F listOfInt) )
    (=>
      (and
        (= A (+ 1 E))
        (>= E 0)
        (append C (cons-listOfInt B nil-listOfInt) F)
        (rotate E F D)
      )
      (rotate A (cons-listOfInt B C) D)
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
  (forall ( (A Bool) (B listOfInt) (C Int) (D listOfInt) (E listOfInt) (F listOfInt) (G listOfInt) )
    (=>
      (and
        (len B C)
        (append B D E)
        (rotate C E F)
        (append D B G)
        (not (= F G))
      )
      ff
    )
  )
)

(assert (not ff))
(check-sat)

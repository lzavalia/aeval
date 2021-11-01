(set-logic HORN)

(declare-datatypes ((treeOfInt 0) )
(((node-treeOfInt (data-treeOfInt Int) (left-treeOfInt treeOfInt) (right-treeOfInt treeOfInt)) (leaf-treeOfInt))))
(declare-datatypes ((listOfInt 0) )
(((cons-listOfInt (head-listOfInt Int) (tail-listOfInt listOfInt)) (nil-listOfInt))))

(declare-fun tinsert (treeOfInt Int treeOfInt) Bool)
(declare-fun tinsertall (treeOfInt listOfInt treeOfInt) Bool)
(declare-fun mem (Int listOfInt Bool) Bool)
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
  (forall ( (A Int) (B Bool) )
    (=>
      (= B false)
      (mem A nil-listOfInt B)
    )
  )
)
(assert
  (forall ( (A Int) (B listOfInt) (C Bool) )
    (=>
      (= C true)
      (mem A (cons-listOfInt A B) C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C listOfInt) (D Bool) )
    (=>
      (and
        (= D true)
        (mem A C D)
      )
      (mem A (cons-listOfInt B C) D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C listOfInt) (D Bool) )
    (=>
      (and
        (= D false)
        (>= (- B A) 1)
        (mem A C D)
      )
      (mem A (cons-listOfInt B C) D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C listOfInt) (D Bool) )
    (=>
      (and
        (= D false)
        (<= (- B A) (- 1))
        (mem A C D)
      )
      (mem A (cons-listOfInt B C) D)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D listOfInt) (E listOfInt) (F listOfInt) (G Int) )
    (=>
      (and
        (= A true)
        (not (= B true))
        (= C false)
        (append D E F)
        (mem G F A)
        (mem G D B)
        (mem G E C)
      )
      ff
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D listOfInt) (E listOfInt) (F listOfInt) (G Int) )
    (=>
      (and
        (= A true)
        (= B false)
        (not (= C true))
        (append D E F)
        (mem G F A)
        (mem G D B)
        (mem G E C)
      )
      ff
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C listOfInt) (D listOfInt) (E listOfInt) (F Int) )
    (=>
      (and
        (not (= A true))
        (= B true)
        (append C D E)
        (mem F E A)
        (mem F C B)
      )
      ff
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C listOfInt) (D listOfInt) (E listOfInt) (F Int) )
    (=>
      (and
        (not (= A true))
        (= B true)
        (append C D E)
        (mem F E A)
        (mem F D B)
      )
      ff
    )
  )
)

(assert (not ff))
(check-sat)

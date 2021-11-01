(set-logic HORN)

(declare-datatypes ((heapOfInt 0) )
(((heap-heapOfInt (rk-heapOfInt Int) (value-heapOfInt Int) (left-heapOfInt heapOfInt) (right-heapOfInt heapOfInt)) (hleaf-heapOfInt))))
(declare-datatypes ((listOfInt 0) )
(((cons-listOfInt (head-listOfInt Int) (tail-listOfInt listOfInt)) (nil-listOfInt))))

(declare-fun len (listOfInt Int) Bool)
(declare-fun rightheight (heapOfInt Int) Bool)
(declare-fun rank (heapOfInt Int) Bool)
(declare-fun mergea (Int heapOfInt heapOfInt heapOfInt) Bool)
(declare-fun merge (heapOfInt heapOfInt heapOfInt) Bool)
(declare-fun hsize (heapOfInt Int) Bool)
(declare-fun hasleftistproperty (heapOfInt Bool) Bool)
(declare-fun hinsert (heapOfInt Int heapOfInt) Bool)
(declare-fun hinsertall (listOfInt heapOfInt heapOfInt) Bool)
(declare-fun heapsorta (heapOfInt listOfInt) Bool)
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
  (forall ( (A Int) )
    (=>
      (= A 0)
      (rightheight hleaf-heapOfInt A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C heapOfInt) (D heapOfInt) (E Int) (F Int) )
    (=>
      (and
        (= E (+ 1 F))
        (rightheight D F)
      )
      (rightheight (heap-heapOfInt A B C D)  E)
    )
  )
)
(assert
  (forall ( (A Int) )
    (=>
      (= A 0)
      (rank hleaf-heapOfInt A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C heapOfInt) (D heapOfInt) )
    (rank (heap-heapOfInt A B C D)  A)
  )
)
(assert
  (forall ( (A Int) (B heapOfInt) (C heapOfInt) (D Int) (E Bool) (F Int) (G Int) (H Int) )
    (=>
      (and
        (= D (+ 1 F))
        (<= G H)
        (rank B H)
        (rank C G)
        (rank C F)
      )
      (mergea A B C (heap-heapOfInt D A B C) )
    )
  )
)
(assert
  (forall ( (A Int) (B heapOfInt) (C heapOfInt) (D Int) (E Bool) (F Int) (G Int) (H Int) )
    (=>
      (and
        (= D (+ 1 F))
        (> G H)
        (rank B H)
        (rank C G)
        (rank B F)
      )
      (mergea A B C (heap-heapOfInt D A C B) )
    )
  )
)

(assert
  (forall ( (A heapOfInt) )
    (merge A hleaf-heapOfInt A)
  )
)
(assert
  (forall ( (A heapOfInt) )
    (merge hleaf-heapOfInt A A)
  )
)
(assert
  (forall ( (A Int) (B Int) (C heapOfInt) (D heapOfInt) (E Int) (F Int) (G heapOfInt) (H heapOfInt) (I heapOfInt) (J Bool) (K heapOfInt) )
    (=>
      (and
        (< F B)
        (mergea B C K I)
        (merge D (heap-heapOfInt E F G H)  K)
      )
      (merge (heap-heapOfInt A B C D)  (heap-heapOfInt E F G H)  I)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C heapOfInt) (D heapOfInt) (E Int) (F Int) (G heapOfInt) (H heapOfInt) (I heapOfInt) (J Bool) (K heapOfInt) )
    (=>
      (and
        (>= F B)
        (mergea F G K I)
        (merge (heap-heapOfInt A B C D)  H K)
      )
      (merge (heap-heapOfInt A B C D)  (heap-heapOfInt E F G H)  I)
    )
  )
)
(assert
  (forall ( (A Bool) )
    (=>
      (= A true)
      (hasleftistproperty hleaf-heapOfInt A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C heapOfInt) (D heapOfInt) (E Bool) (F Int) (G Int) (H Int) )
    (=>
      (and
        (= E true)
        (= A (+ 1 F))
        (hasleftistproperty C E)
        (hasleftistproperty D E)
        (<= G H)
        (rightheight C H)
        (rightheight D G)
        (rightheight D F)
      )
      (hasleftistproperty (heap-heapOfInt A B C D)  E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C heapOfInt) (D heapOfInt) (E Bool) )
    (=>
      (and
        (= E false)
        (hasleftistproperty C E)
      )
      (hasleftistproperty (heap-heapOfInt A B C D)  E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C heapOfInt) (D heapOfInt) (E Bool) )
    (=>
      (and
        (= E false)
        (hasleftistproperty D E)
      )
      (hasleftistproperty (heap-heapOfInt A B C D)  E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C heapOfInt) (D heapOfInt) (E Bool) (F Int) (G Int) )
    (=>
      (and
        (= E false)
        (> F G)
        (rightheight C G)
        (rightheight D F)
      )
      (hasleftistproperty (heap-heapOfInt A B C D)  E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C heapOfInt) (D heapOfInt) (E Bool) (F Int) )
    (=>
      (and
        (= E false)
        (not (= A (+ 1 F)))
        (rightheight D F)
      )
      (hasleftistproperty (heap-heapOfInt A B C D)  E)
    )
  )
)
(assert
  (forall ( (A Int) )
    (=>
      (= A 0)
      (hsize hleaf-heapOfInt A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C heapOfInt) (D heapOfInt) (E Int) (F Int) (G Int) (H Int) )
    (=>
      (and
        (= E (+ 1 F))
        (hsize C G)
        (hsize D H)
        (= F (+ G H))
      )
      (hsize (heap-heapOfInt A B C D)  E)
    )
  )
)
(assert
  (forall ( (A heapOfInt) (B Int) (C heapOfInt) (D Int) )
    (=>
      (and
        (= D 1)
        (merge (heap-heapOfInt D B hleaf-heapOfInt hleaf-heapOfInt)  A C)
      )
      (hinsert A B C)
    )
  )
)
(assert
  (forall ( (A heapOfInt) )
    (hinsertall nil-listOfInt A A)
  )
)
(assert
  (forall ( (A Int) (B listOfInt) (C heapOfInt) (D heapOfInt) (E heapOfInt) )
    (=>
      (and
        (hinsertall B C E)
        (hinsert E A D)
      )
      (hinsertall (cons-listOfInt A B) C D)
    )
  )
)
(assert
    (heapsorta hleaf-heapOfInt nil-listOfInt)
)
(assert
  (forall ( (A Int) (B Int) (C heapOfInt) (D heapOfInt) (E listOfInt) (F heapOfInt) )
    (=>
      (and
        (merge C D F)
        (heapsorta F E)
      )
      (heapsorta (heap-heapOfInt A B C D)  (cons-listOfInt B E))
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Int) (D heapOfInt) (E listOfInt) )
    (=>
      (and
        (= A true)
        (not (= B C))
        (>= (- B C) 1)
        (heapsorta D E)
        (len E C)
        (hsize D B)
        (hasleftistproperty D A)
      )
      ff
    )
  )
)

(assert (not ff))
(check-sat)

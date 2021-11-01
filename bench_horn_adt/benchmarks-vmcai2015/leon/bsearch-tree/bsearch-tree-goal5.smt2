(set-logic HORN)

(declare-datatypes ((treeOfInt 0) )
(((node-treeOfInt (data-treeOfInt Int) (left-treeOfInt treeOfInt) (right-treeOfInt treeOfInt)) (leaf-treeOfInt))))
(declare-datatypes ((listOfInt 0) )
(((cons-listOfInt (head-listOfInt Int) (tail-listOfInt listOfInt)) (nil-listOfInt))))

(declare-fun tsize (treeOfInt Int) Bool)
(declare-fun tremove (treeOfInt Int treeOfInt) Bool)
(declare-fun tremoveall (treeOfInt listOfInt treeOfInt) Bool)
(declare-fun ff () Bool)

(assert
  (forall ( (A Int) )
    (tremove leaf-treeOfInt A leaf-treeOfInt)
  )
)
(assert
  (forall ( (A Int) (B treeOfInt) (C treeOfInt) (D Int) (E treeOfInt) )
    (=>
      (and
        (<= D (- A 1))
        (tremove B D E)
      )
      (tremove (node-treeOfInt A B C)  D (node-treeOfInt A E C) )
    )
  )
)
(assert
  (forall ( (A Int) (B treeOfInt) (C treeOfInt) (D Int) (E treeOfInt) )
    (=>
      (and
        (<= A (- D 1))
        (tremove C D E)
      )
      (tremove (node-treeOfInt A B C)  D (node-treeOfInt A B E) )
    )
  )
)
(assert
  (forall ( (A Int) (B treeOfInt) )
    (tremove (node-treeOfInt A leaf-treeOfInt B)  A B)
  )
)
(assert
  (forall ( (A Int) (B Int) (C treeOfInt) (D treeOfInt) (E treeOfInt) (F treeOfInt) )
    (=>
      (tremove (node-treeOfInt B C D)  B F)
      (tremove (node-treeOfInt A (node-treeOfInt B C D)  E)  A (node-treeOfInt B F E) )
    )
  )
)

(assert
  (forall ( (A Int) )
    (=>
      (= A 0)
      (tsize leaf-treeOfInt A)
    )
  )
)
(assert
  (forall ( (A Int) (B treeOfInt) (C treeOfInt) (D Int) (E Int) (F Int) (G Int) )
    (=>
      (and
        (= D (+ 1 E))
        (= (+ F G) E)
        (tsize B F)
        (tsize C G)
      )
      (tsize (node-treeOfInt A B C)  D)
    )
  )
)
(assert
  (forall ( (A treeOfInt) )
    (tremoveall A nil-listOfInt A)
  )
)
(assert
  (forall ( (A treeOfInt) (B Int) (C listOfInt) (D treeOfInt) (E treeOfInt) )
    (=>
      (and
        (tremove A B E)
        (tremoveall E C D)
      )
      (tremoveall A (cons-listOfInt B C) D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C treeOfInt) (D listOfInt) (E treeOfInt) )
    (=>
      (and
        (not (<= A B))
        (tremoveall C D E)
        (tsize E A)
        (tsize C B)
      )
      ff
    )
  )
)

(assert (not ff))
(check-sat)

(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))

(declare-fun len (Lst) Int)
(assert (= (len nil) 0))
(assert (forall ((x Int) (y Lst)) (= (len (cons x y)) (+ 1 (len y)))))

(declare-fun sum (Lst) Int)
(assert (= (sum nil) 0))
(assert (forall ((x Int) (y Lst)) (= (sum (cons x y)) (+ x (sum y)))))
                      
(declare-fun map_inc (Lst) Lst)
(assert (= (map_inc nil) nil))
(assert (forall ((x Int) (y Lst))
  (= (map_inc (cons x y)) (cons (+ x 1) (map_inc y)))))

(assert (not (forall ((xs Lst))
  (= (sum (map_inc xs)) (+ (sum xs) (len xs))))))

(check-sat)

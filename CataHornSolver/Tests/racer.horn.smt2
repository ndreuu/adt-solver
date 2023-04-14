(declare-datatype list ((nil) (cons (car Int) (cdr list))))

(declare-fun Inv (list Int Int) Bool)
(declare-fun length (list Int) Bool)

(assert (length nil 0))
(assert (forall ((x Int) (xs list) (n Int))
  (=> (length xs n) (length (cons x xs) (+ n 1)))))

(assert (Inv nil 0 0))
(assert (forall ((x1 Int) (xs1 list) (n1 Int))
  (=> (and (length xs1 n1) (length (cons x1 xs1) (+ n1 1))) (Inv (cons x1 xs1) (+ n1 1) (+ n1 1)))))



;(assert (forall ((y list) (i Int)) (=> (length y i) (Inv y i i))))
(assert (forall ((y2 list) (i2 Int) (j2 Int) (y12 list) (j12 Int) (tmp2 Int))
  (=> (and (Inv y2 i2 j2) (length y2 j2) (= y2 (cons tmp2 y12)) (length y12 j12)) (Inv y12 (- i2 1) j2))))
(assert (forall ((y3 list) (i3 Int) (j3 Int))
  (=> (and (Inv y3 i3 j3) (length y3 j3) (< i3 0)) false)))



(check-sat)
(get-model)

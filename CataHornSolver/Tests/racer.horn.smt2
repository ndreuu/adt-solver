(declare-datatype list ((nil) (cons (car Int) (cdr list))))

(declare-fun Inv (list Int Int) Bool)
(declare-fun length (list Int) Bool)

(assert (length nil 0))
(assert (forall ((x1 Int) (xs1 list) (n1 Int))
  (=> (length xs1 n1) (length (cons x1 xs1) (+ n1 1)))))



(assert (Inv nil 0 0))

(assert (forall ((xs2 list) (x2 Int) (n2 Int)) 
    (=> (and (length xs2 n2) (length (cons x2 xs2) (+ n2 1))) (Inv (cons x2 xs2) (+ n2 1) (+ n2 1)))))



;(assert (forall ((y list) (i Int)) (=> (length y i) (Inv y i i))))




(assert (forall ((y3 list) (i23 Int) (j3 Int) (y13 list) (j13 Int) (tmp3 Int))
  (=> (and (Inv y3 i23 j3)  (length y3 j3) (= y3 (cons tmp3 y13)) (length y13 j13)) (Inv y13 (- i23 1) j13))))


(assert (forall ((y4 list) (i14 Int) (j4 Int))
  (=> (and (Inv y4 i14 j4) (length y4 j4) (< i14 0)) false)))

(check-sat)
(get-model)



;(=> (and (Inv y i  j) (length y j) (< i 0)) false))
;(=> (and (Inv y -2 j) (length y j) (< i 0)) false))

;(Inv (cons x xs) (-2) (-2))

;(=> (and (length xs (-3)) (length (cons x xs) (+ (-3) 1))) (Inv (cons x xs) (+ (-3) 1) (+ (-3) 1)))

;(define-fun c_3 () Int 0)
;(define-fun c_2 () Int 1)
;(define-fun c_1 () Int 0)
;(define-fun c_0 () Int 0)
;(define-fun nil () Int 0)
;(define-fun cons ((car Int) (cdr Int)) Int (+ 0 (+ (* 1 car) (* 0 cdr))))



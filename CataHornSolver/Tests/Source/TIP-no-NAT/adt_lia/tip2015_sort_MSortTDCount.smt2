(set-logic HORN)
(define-fun Z_724 () Int 0)
(define-fun S_210 ((x Int)) Int (+ x 1))
(declare-fun unS_257 (Int Int) Bool)
(declare-fun isZ_201 (Int) Bool)
(declare-fun isS_201 (Int) Bool)
(assert (forall ((x_18440 Int))
	(unS_257 x_18440 (S_210 x_18440))))
(assert (isZ_201 Z_724))
(assert (forall ((x_18442 Int))
	(isS_201 (S_210 x_18442))))
(declare-fun add_133 (Int Int Int) Bool)
(declare-fun minus_131 (Int Int Int) Bool)
(declare-fun mult_128 (Int Int Int) Bool)
(define-fun div_128 ((z Int) (x Int) (y Int)) Bool (= z (div x y)))
(assert (forall ((z Int) (x Int) (y Int)) (=> (= z (+ x y)) (add_133 z x y))))
(assert (forall ((z Int) (x Int) (y Int)) (=> (= z (- x y)) (minus_131 z x y))))
(assert (forall ((z Int) (x Int) (y Int)) (=> (= z (* x y)) (mult_128 z x y))))
(declare-datatypes ((list_96 0)) (((nil_104) (cons_96 (head_192 Int) (tail_192 list_96)))))
(declare-fun diseqlist_96 (list_96 list_96) Bool)
(declare-fun head_193 (Int list_96) Bool)
(declare-fun tail_193 (list_96 list_96) Bool)
(declare-fun isnil_104 (list_96) Bool)
(declare-fun iscons_96 (list_96) Bool)
(assert (forall ((x_18448 Int) (x_18449 list_96))
	(head_193 x_18448 (cons_96 x_18448 x_18449))))
(assert (forall ((x_18448 Int) (x_18449 list_96))
	(tail_193 x_18449 (cons_96 x_18448 x_18449))))
(assert (isnil_104 nil_104))
(assert (forall ((x_18451 Int) (x_18452 list_96))
	(iscons_96 (cons_96 x_18451 x_18452))))
(assert (forall ((x_18453 Int) (x_18454 list_96))
	(diseqlist_96 nil_104 (cons_96 x_18453 x_18454))))
(assert (forall ((x_18455 Int) (x_18456 list_96))
	(diseqlist_96 (cons_96 x_18455 x_18456) nil_104)))
(assert (forall ((x_18457 Int) (x_18458 list_96) (x_18459 Int) (x_18460 list_96))
	(=> (distinct x_18457 x_18459) (diseqlist_96 (cons_96 x_18457 x_18458) (cons_96 x_18459 x_18460)))))
(assert (forall ((x_18457 Int) (x_18458 list_96) (x_18459 Int) (x_18460 list_96))
	(=> (diseqlist_96 x_18458 x_18460) (diseqlist_96 (cons_96 x_18457 x_18458) (cons_96 x_18459 x_18460)))))
(declare-fun take_21 (list_96 Int list_96) Bool)
(assert (forall ((x_18385 Int) (y_704 list_96))
	(=> (<= x_18385 Z_724) (take_21 nil_104 x_18385 y_704))))
(assert (forall ((x_18434 Int) (x_18399 list_96) (z_719 Int) (xs_223 list_96) (x_18385 Int))
	(=> (and (> x_18385 Z_724) (take_21 x_18399 x_18434 xs_223) (minus_131 x_18434 x_18385 (S_210 Z_724))) (take_21 (cons_96 z_719 x_18399) x_18385 (cons_96 z_719 xs_223)))))
(assert (forall ((x_18385 Int) (y_704 list_96))
	(=> (<= x_18385 Z_724) (take_21 nil_104 x_18385 y_704))))
(assert (forall ((x_18385 Int))
	(=> (> x_18385 Z_724) (take_21 nil_104 x_18385 nil_104))))
(declare-fun lmerge_4 (list_96 list_96 list_96) Bool)
(assert (forall ((x_18403 list_96) (x_18388 Int) (x_18389 list_96) (z_720 Int) (x_18387 list_96))
	(=> (and (<= z_720 x_18388) (lmerge_4 x_18403 x_18387 (cons_96 x_18388 x_18389))) (lmerge_4 (cons_96 z_720 x_18403) (cons_96 z_720 x_18387) (cons_96 x_18388 x_18389)))))
(assert (forall ((x_18405 list_96) (x_18388 Int) (x_18389 list_96) (z_720 Int) (x_18387 list_96))
	(=> (and (> z_720 x_18388) (lmerge_4 x_18405 (cons_96 z_720 x_18387) x_18389)) (lmerge_4 (cons_96 x_18388 x_18405) (cons_96 z_720 x_18387) (cons_96 x_18388 x_18389)))))
(assert (forall ((z_720 Int) (x_18387 list_96))
	(lmerge_4 (cons_96 z_720 x_18387) (cons_96 z_720 x_18387) nil_104)))
(assert (forall ((x_18407 list_96))
	(lmerge_4 x_18407 nil_104 x_18407)))
(declare-fun length_8 (Int list_96) Bool)
(assert (forall ((x_18408 Int) (x_18409 Int) (y_706 Int) (l_10 list_96))
	(=> (and (length_8 x_18409 l_10) (add_133 x_18408 (S_210 Z_724) x_18409)) (length_8 x_18408 (cons_96 y_706 l_10)))))
(assert (length_8 Z_724 nil_104))
(declare-fun drop_23 (list_96 Int list_96) Bool)
(assert (forall ((x_18411 list_96) (x_18391 Int))
	(=> (<= x_18391 Z_724) (drop_23 x_18411 x_18391 x_18411))))
(assert (forall ((x_18436 Int) (x_18412 list_96) (z_721 Int) (xs_224 list_96) (x_18391 Int))
	(=> (and (> x_18391 Z_724) (drop_23 x_18412 x_18436 xs_224) (minus_131 x_18436 x_18391 (S_210 Z_724))) (drop_23 x_18412 x_18391 (cons_96 z_721 xs_224)))))
(assert (forall ((x_18414 list_96) (x_18391 Int))
	(=> (<= x_18391 Z_724) (drop_23 x_18414 x_18391 x_18414))))
(assert (forall ((x_18391 Int))
	(=> (> x_18391 Z_724) (drop_23 nil_104 x_18391 nil_104))))
(declare-fun msorttd_2 (list_96 list_96) Bool)
(assert (forall ((x_18417 list_96) (x_18418 list_96) (x_18419 list_96) (x_18420 list_96) (x_18421 list_96) (x_18416 Int) (k_6 Int) (x_18393 Int) (x_18394 list_96) (y_708 Int))
	(=> (and (take_21 x_18418 k_6 (cons_96 y_708 (cons_96 x_18393 x_18394))) (msorttd_2 x_18419 x_18418) (drop_23 x_18420 k_6 (cons_96 y_708 (cons_96 x_18393 x_18394))) (msorttd_2 x_18421 x_18420) (lmerge_4 x_18417 x_18419 x_18421) (length_8 x_18416 (cons_96 y_708 (cons_96 x_18393 x_18394))) (div_128 k_6 x_18416 (S_210 (S_210 Z_724)))) (msorttd_2 x_18417 (cons_96 y_708 (cons_96 x_18393 x_18394))))))
(assert (forall ((y_708 Int))
	(msorttd_2 (cons_96 y_708 nil_104) (cons_96 y_708 nil_104))))
(assert (msorttd_2 nil_104 nil_104))
(declare-fun count_16 (Int Int list_96) Bool)
(assert (forall ((x_18425 Int) (x_18426 Int) (ys_59 list_96) (x_18395 Int))
	(=> (and (count_16 x_18426 x_18395 ys_59) (add_133 x_18425 (S_210 Z_724) x_18426)) (count_16 x_18425 x_18395 (cons_96 x_18395 ys_59)))))
(assert (forall ((x_18427 Int) (z_723 Int) (ys_59 list_96) (x_18395 Int))
	(=> (and (distinct x_18395 z_723) (count_16 x_18427 x_18395 ys_59)) (count_16 x_18427 x_18395 (cons_96 z_723 ys_59)))))
(assert (forall ((x_18395 Int))
	(count_16 Z_724 x_18395 nil_104)))
(assert (forall ((x_18430 list_96) (x_18431 Int) (x_18432 Int) (x_18396 Int) (xs_225 list_96))
	(=> (and (distinct x_18431 x_18432) (msorttd_2 x_18430 xs_225) (count_16 x_18431 x_18396 x_18430) (count_16 x_18432 x_18396 xs_225)) false)))
(check-sat)

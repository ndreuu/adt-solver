(set-logic HORN)
(define-fun Z_1968 () Int 0)
(define-fun S_441 ((x Int)) Int (+ x 1))
(declare-datatypes ((Bool_326 0)) (((false_326) (true_326))))
(declare-fun diseqBool_151 (Bool_326 Bool_326) Bool)
(declare-fun isfalse_151 (Bool_326) Bool)
(declare-fun istrue_151 (Bool_326) Bool)
(assert (isfalse_151 false_326))
(assert (istrue_151 true_326))
(assert (diseqBool_151 false_326 true_326))
(assert (diseqBool_151 true_326 false_326))
(declare-fun and_326 (Bool_326 Bool_326 Bool_326) Bool)
(declare-fun or_333 (Bool_326 Bool_326 Bool_326) Bool)
(declare-fun hence_326 (Bool_326 Bool_326 Bool_326) Bool)
(declare-fun not_331 (Bool_326 Bool_326) Bool)
(assert (and_326 false_326 false_326 false_326))
(assert (and_326 false_326 true_326 false_326))
(assert (and_326 false_326 false_326 true_326))
(assert (and_326 true_326 true_326 true_326))
(assert (or_333 false_326 false_326 false_326))
(assert (or_333 true_326 true_326 false_326))
(assert (or_333 true_326 false_326 true_326))
(assert (or_333 true_326 true_326 true_326))
(assert (hence_326 true_326 false_326 false_326))
(assert (hence_326 false_326 true_326 false_326))
(assert (hence_326 true_326 false_326 true_326))
(assert (hence_326 true_326 true_326 true_326))
(assert (not_331 true_326 false_326))
(assert (not_331 false_326 true_326))
(declare-fun projS_165 (Int Int) Bool)
(declare-fun isZ_408 (Int) Bool)
(declare-fun isS_408 (Int) Bool)
(assert (forall ((x_54578 Int))
	(projS_165 x_54578 (S_441 x_54578))))
(assert (isZ_408 Z_1968))
(assert (forall ((x_54580 Int))
	(isS_408 (S_441 x_54580))))
(declare-datatypes ((list_231 0)) (((nil_261) (cons_231 (head_462 Int) (tail_462 list_231)))))
(declare-fun diseqlist_231 (list_231 list_231) Bool)
(declare-fun head_463 (Int list_231) Bool)
(declare-fun tail_463 (list_231 list_231) Bool)
(declare-fun isnil_261 (list_231) Bool)
(declare-fun iscons_231 (list_231) Bool)
(assert (forall ((x_54586 Int) (x_54587 list_231))
	(head_463 x_54586 (cons_231 x_54586 x_54587))))
(assert (forall ((x_54586 Int) (x_54587 list_231))
	(tail_463 x_54587 (cons_231 x_54586 x_54587))))
(assert (isnil_261 nil_261))
(assert (forall ((x_54589 Int) (x_54590 list_231))
	(iscons_231 (cons_231 x_54589 x_54590))))
(assert (forall ((x_54591 Int) (x_54592 list_231))
	(diseqlist_231 nil_261 (cons_231 x_54591 x_54592))))
(assert (forall ((x_54593 Int) (x_54594 list_231))
	(diseqlist_231 (cons_231 x_54593 x_54594) nil_261)))
(assert (forall ((x_54595 Int) (x_54596 list_231) (x_54597 Int) (x_54598 list_231))
	(=> (distinct x_54595 x_54597) (diseqlist_231 (cons_231 x_54595 x_54596) (cons_231 x_54597 x_54598)))))
(assert (forall ((x_54595 Int) (x_54596 list_231) (x_54597 Int) (x_54598 list_231))
	(=> (diseqlist_231 x_54596 x_54598) (diseqlist_231 (cons_231 x_54595 x_54596) (cons_231 x_54597 x_54598)))))
(declare-fun x_54541 (Bool_326 Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (<= x y) (x_54541 true_326 x y))))
(assert (forall ((x Int) (y Int)) (=> (not (<= x y)) (x_54541 false_326 x y))))
(declare-fun insert_30 (list_231 Int list_231) Bool)
(assert (forall ((z_1970 Int) (xs_630 list_231) (x_54544 Int))
	(=> (x_54541 true_326 x_54544 z_1970) (insert_30 (cons_231 x_54544 (cons_231 z_1970 xs_630)) x_54544 (cons_231 z_1970 xs_630)))))
(assert (forall ((x_54558 list_231) (z_1970 Int) (xs_630 list_231) (x_54544 Int))
	(=> (and (insert_30 x_54558 x_54544 xs_630) (x_54541 false_326 x_54544 z_1970)) (insert_30 (cons_231 z_1970 x_54558) x_54544 (cons_231 z_1970 xs_630)))))
(assert (forall ((x_54544 Int))
	(insert_30 (cons_231 x_54544 nil_261) x_54544 nil_261)))
(declare-fun isort_29 (list_231 list_231) Bool)
(assert (forall ((x_54560 list_231) (x_54561 list_231) (y_2205 Int) (xs_631 list_231))
	(=> (and (isort_29 x_54561 xs_631) (insert_30 x_54560 y_2205 x_54561)) (isort_29 x_54560 (cons_231 y_2205 xs_631)))))
(assert (isort_29 nil_261 nil_261))
(declare-fun x_54546 (Bool_326 Bool_326 Bool_326) Bool)
(assert (forall ((x_54564 Bool_326))
	(x_54546 x_54564 true_326 x_54564)))
(assert (forall ((y_2206 Bool_326))
	(x_54546 false_326 false_326 y_2206)))
(declare-fun sorted_2 (Bool_326 list_231) Bool)
(assert (forall ((x_54566 Bool_326) (x_54567 Bool_326) (x_54568 Bool_326) (y_2208 Int) (xs_632 list_231) (y_2207 Int))
	(=> (and (x_54541 x_54567 y_2207 y_2208) (sorted_2 x_54568 (cons_231 y_2208 xs_632)) (x_54546 x_54566 x_54567 x_54568)) (sorted_2 x_54566 (cons_231 y_2207 (cons_231 y_2208 xs_632))))))
(assert (forall ((y_2207 Int))
	(sorted_2 true_326 (cons_231 y_2207 nil_261))))
(assert (sorted_2 true_326 nil_261))
(assert (forall ((x_54572 list_231) (x_54549 list_231))
	(=> (and (isort_29 x_54572 x_54549) (sorted_2 false_326 x_54572)) false)))
(check-sat)

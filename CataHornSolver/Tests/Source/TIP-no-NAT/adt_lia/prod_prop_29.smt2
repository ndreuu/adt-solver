(set-logic HORN)
(define-fun Z_2077 () Int 0)
(define-fun S_478 ((x Int)) Int (+ x 1))
(declare-fun unS_695 (Int Int) Bool)
(declare-fun isZ_445 (Int) Bool)
(declare-fun isS_445 (Int) Bool)
(assert (forall ((x_55618 Int))
	(unS_695 x_55618 (S_478 x_55618))))
(assert (isZ_445 Z_2077))
(assert (forall ((x_55620 Int))
	(isS_445 (S_478 x_55620))))
(declare-fun add_373 (Int Int Int) Bool)
(declare-fun minus_368 (Int Int Int) Bool)
(declare-fun le_347 (Int Int) Bool)
(declare-fun ge_347 (Int Int) Bool)
(declare-fun lt_367 (Int Int) Bool)
(declare-fun gt_350 (Int Int) Bool)
(declare-fun mult_347 (Int Int Int) Bool)
(declare-fun div_347 (Int Int Int) Bool)
(declare-fun mod_349 (Int Int Int) Bool)
(assert (forall ((y_2313 Int))
	(add_373 y_2313 Z_2077 y_2313)))
(assert (forall ((x_55602 Int) (y_2313 Int) (r_420 Int))
	(=> (add_373 r_420 x_55602 y_2313) (add_373 (S_478 r_420) (S_478 x_55602) y_2313))))
(assert (forall ((y_2313 Int))
	(minus_368 Z_2077 Z_2077 y_2313)))
(assert (forall ((x_55602 Int) (y_2313 Int) (r_420 Int))
	(=> (minus_368 r_420 x_55602 y_2313) (minus_368 (S_478 r_420) (S_478 x_55602) y_2313))))
(assert (forall ((y_2313 Int))
	(le_347 Z_2077 y_2313)))
(assert (forall ((x_55602 Int) (y_2313 Int))
	(=> (le_347 x_55602 y_2313) (le_347 (S_478 x_55602) (S_478 y_2313)))))
(assert (forall ((y_2313 Int))
	(ge_347 y_2313 Z_2077)))
(assert (forall ((x_55602 Int) (y_2313 Int))
	(=> (ge_347 x_55602 y_2313) (ge_347 (S_478 x_55602) (S_478 y_2313)))))
(assert (forall ((y_2313 Int))
	(lt_367 Z_2077 (S_478 y_2313))))
(assert (forall ((x_55602 Int) (y_2313 Int))
	(=> (lt_367 x_55602 y_2313) (lt_367 (S_478 x_55602) (S_478 y_2313)))))
(assert (forall ((y_2313 Int))
	(gt_350 (S_478 y_2313) Z_2077)))
(assert (forall ((x_55602 Int) (y_2313 Int))
	(=> (gt_350 x_55602 y_2313) (gt_350 (S_478 x_55602) (S_478 y_2313)))))
(assert (forall ((y_2313 Int))
	(mult_347 Z_2077 Z_2077 y_2313)))
(assert (forall ((x_55602 Int) (y_2313 Int) (r_420 Int) (z_2078 Int))
	(=> (and (mult_347 r_420 x_55602 y_2313) (add_373 z_2078 r_420 y_2313)) (mult_347 z_2078 (S_478 x_55602) y_2313))))
(assert (forall ((x_55602 Int) (y_2313 Int))
	(=> (lt_367 x_55602 y_2313) (div_347 Z_2077 x_55602 y_2313))))
(assert (forall ((x_55602 Int) (y_2313 Int) (r_420 Int) (z_2078 Int))
	(=> (and (ge_347 x_55602 y_2313) (minus_368 z_2078 x_55602 y_2313) (div_347 r_420 z_2078 y_2313)) (div_347 (S_478 r_420) x_55602 y_2313))))
(assert (forall ((x_55602 Int) (y_2313 Int))
	(=> (lt_367 x_55602 y_2313) (mod_349 x_55602 x_55602 y_2313))))
(assert (forall ((x_55602 Int) (y_2313 Int) (r_420 Int) (z_2078 Int))
	(=> (and (ge_347 x_55602 y_2313) (minus_368 z_2078 x_55602 y_2313) (mod_349 r_420 z_2078 y_2313)) (mod_349 r_420 x_55602 y_2313))))
(declare-datatypes ((list_249 0)) (((nil_279) (cons_249 (head_498 Int) (tail_498 list_249)))))
(declare-fun diseqlist_249 (list_249 list_249) Bool)
(declare-fun head_499 (Int list_249) Bool)
(declare-fun tail_499 (list_249 list_249) Bool)
(declare-fun isnil_279 (list_249) Bool)
(declare-fun iscons_249 (list_249) Bool)
(assert (forall ((x_55604 Int) (x_55605 list_249))
	(head_499 x_55604 (cons_249 x_55604 x_55605))))
(assert (forall ((x_55604 Int) (x_55605 list_249))
	(tail_499 x_55605 (cons_249 x_55604 x_55605))))
(assert (isnil_279 nil_279))
(assert (forall ((x_55607 Int) (x_55608 list_249))
	(iscons_249 (cons_249 x_55607 x_55608))))
(assert (forall ((x_55609 Int) (x_55610 list_249))
	(diseqlist_249 nil_279 (cons_249 x_55609 x_55610))))
(assert (forall ((x_55611 Int) (x_55612 list_249))
	(diseqlist_249 (cons_249 x_55611 x_55612) nil_279)))
(assert (forall ((x_55613 Int) (x_55614 list_249) (x_55615 Int) (x_55616 list_249))
	(=> (distinct x_55613 x_55615) (diseqlist_249 (cons_249 x_55613 x_55614) (cons_249 x_55615 x_55616)))))
(assert (forall ((x_55613 Int) (x_55614 list_249) (x_55615 Int) (x_55616 list_249))
	(=> (diseqlist_249 x_55614 x_55616) (diseqlist_249 (cons_249 x_55613 x_55614) (cons_249 x_55615 x_55616)))))
(declare-fun qrev_2 (list_249 list_249 list_249) Bool)
(assert (forall ((x_55590 list_249) (z_2075 Int) (xs_666 list_249) (y_2310 list_249))
	(=> (qrev_2 x_55590 xs_666 (cons_249 z_2075 y_2310)) (qrev_2 x_55590 (cons_249 z_2075 xs_666) y_2310))))
(assert (forall ((x_55592 list_249))
	(qrev_2 x_55592 nil_279 x_55592)))
(declare-fun x_55586 (list_249 list_249 list_249) Bool)
(assert (forall ((x_55594 list_249) (z_2076 Int) (xs_667 list_249) (y_2311 list_249))
	(=> (x_55586 x_55594 xs_667 y_2311) (x_55586 (cons_249 z_2076 x_55594) (cons_249 z_2076 xs_667) y_2311))))
(assert (forall ((x_55595 list_249))
	(x_55586 x_55595 nil_279 x_55595)))
(declare-fun rev_14 (list_249 list_249) Bool)
(assert (forall ((x_55596 list_249) (x_55597 list_249) (y_2312 Int) (xs_668 list_249))
	(=> (and (rev_14 x_55597 xs_668) (x_55586 x_55596 x_55597 (cons_249 y_2312 nil_279))) (rev_14 x_55596 (cons_249 y_2312 xs_668)))))
(assert (rev_14 nil_279 nil_279))
(assert (forall ((x_55600 list_249) (x_55601 list_249) (x_55589 list_249))
	(=> (and (diseqlist_249 x_55601 x_55589) (qrev_2 x_55600 x_55589 nil_279) (rev_14 x_55601 x_55600)) false)))
(check-sat)

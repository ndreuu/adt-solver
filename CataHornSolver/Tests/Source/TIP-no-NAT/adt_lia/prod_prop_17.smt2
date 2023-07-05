(set-logic HORN)
(define-fun Z_2069 () Int 0)
(define-fun S_475 ((x Int)) Int (+ x 1))
(declare-fun unS_691 (Int Int) Bool)
(declare-fun isZ_442 (Int) Bool)
(declare-fun isS_442 (Int) Bool)
(assert (forall ((x_55549 Int))
	(unS_691 x_55549 (S_475 x_55549))))
(assert (isZ_442 Z_2069))
(assert (forall ((x_55551 Int))
	(isS_442 (S_475 x_55551))))
(declare-fun add_371 (Int Int Int) Bool)
(declare-fun minus_366 (Int Int Int) Bool)
(declare-fun le_345 (Int Int) Bool)
(declare-fun ge_345 (Int Int) Bool)
(declare-fun lt_365 (Int Int) Bool)
(declare-fun gt_348 (Int Int) Bool)
(declare-fun mult_345 (Int Int Int) Bool)
(declare-fun div_345 (Int Int Int) Bool)
(declare-fun mod_347 (Int Int Int) Bool)
(assert (forall ((y_2306 Int))
	(add_371 y_2306 Z_2069 y_2306)))
(assert (forall ((x_55533 Int) (y_2306 Int) (r_418 Int))
	(=> (add_371 r_418 x_55533 y_2306) (add_371 (S_475 r_418) (S_475 x_55533) y_2306))))
(assert (forall ((y_2306 Int))
	(minus_366 Z_2069 Z_2069 y_2306)))
(assert (forall ((x_55533 Int) (y_2306 Int) (r_418 Int))
	(=> (minus_366 r_418 x_55533 y_2306) (minus_366 (S_475 r_418) (S_475 x_55533) y_2306))))
(assert (forall ((y_2306 Int))
	(le_345 Z_2069 y_2306)))
(assert (forall ((x_55533 Int) (y_2306 Int))
	(=> (le_345 x_55533 y_2306) (le_345 (S_475 x_55533) (S_475 y_2306)))))
(assert (forall ((y_2306 Int))
	(ge_345 y_2306 Z_2069)))
(assert (forall ((x_55533 Int) (y_2306 Int))
	(=> (ge_345 x_55533 y_2306) (ge_345 (S_475 x_55533) (S_475 y_2306)))))
(assert (forall ((y_2306 Int))
	(lt_365 Z_2069 (S_475 y_2306))))
(assert (forall ((x_55533 Int) (y_2306 Int))
	(=> (lt_365 x_55533 y_2306) (lt_365 (S_475 x_55533) (S_475 y_2306)))))
(assert (forall ((y_2306 Int))
	(gt_348 (S_475 y_2306) Z_2069)))
(assert (forall ((x_55533 Int) (y_2306 Int))
	(=> (gt_348 x_55533 y_2306) (gt_348 (S_475 x_55533) (S_475 y_2306)))))
(assert (forall ((y_2306 Int))
	(mult_345 Z_2069 Z_2069 y_2306)))
(assert (forall ((x_55533 Int) (y_2306 Int) (r_418 Int) (z_2070 Int))
	(=> (and (mult_345 r_418 x_55533 y_2306) (add_371 z_2070 r_418 y_2306)) (mult_345 z_2070 (S_475 x_55533) y_2306))))
(assert (forall ((x_55533 Int) (y_2306 Int))
	(=> (lt_365 x_55533 y_2306) (div_345 Z_2069 x_55533 y_2306))))
(assert (forall ((x_55533 Int) (y_2306 Int) (r_418 Int) (z_2070 Int))
	(=> (and (ge_345 x_55533 y_2306) (minus_366 z_2070 x_55533 y_2306) (div_345 r_418 z_2070 y_2306)) (div_345 (S_475 r_418) x_55533 y_2306))))
(assert (forall ((x_55533 Int) (y_2306 Int))
	(=> (lt_365 x_55533 y_2306) (mod_347 x_55533 x_55533 y_2306))))
(assert (forall ((x_55533 Int) (y_2306 Int) (r_418 Int) (z_2070 Int))
	(=> (and (ge_345 x_55533 y_2306) (minus_366 z_2070 x_55533 y_2306) (mod_347 r_418 z_2070 y_2306)) (mod_347 r_418 x_55533 y_2306))))
(declare-datatypes ((list_248 0)) (((nil_278) (cons_248 (head_496 Int) (tail_496 list_248)))))
(declare-fun diseqlist_248 (list_248 list_248) Bool)
(declare-fun head_497 (Int list_248) Bool)
(declare-fun tail_497 (list_248 list_248) Bool)
(declare-fun isnil_278 (list_248) Bool)
(declare-fun iscons_248 (list_248) Bool)
(assert (forall ((x_55535 Int) (x_55536 list_248))
	(head_497 x_55535 (cons_248 x_55535 x_55536))))
(assert (forall ((x_55535 Int) (x_55536 list_248))
	(tail_497 x_55536 (cons_248 x_55535 x_55536))))
(assert (isnil_278 nil_278))
(assert (forall ((x_55538 Int) (x_55539 list_248))
	(iscons_248 (cons_248 x_55538 x_55539))))
(assert (forall ((x_55540 Int) (x_55541 list_248))
	(diseqlist_248 nil_278 (cons_248 x_55540 x_55541))))
(assert (forall ((x_55542 Int) (x_55543 list_248))
	(diseqlist_248 (cons_248 x_55542 x_55543) nil_278)))
(assert (forall ((x_55544 Int) (x_55545 list_248) (x_55546 Int) (x_55547 list_248))
	(=> (distinct x_55544 x_55546) (diseqlist_248 (cons_248 x_55544 x_55545) (cons_248 x_55546 x_55547)))))
(assert (forall ((x_55544 Int) (x_55545 list_248) (x_55546 Int) (x_55547 list_248))
	(=> (diseqlist_248 x_55545 x_55547) (diseqlist_248 (cons_248 x_55544 x_55545) (cons_248 x_55546 x_55547)))))
(declare-fun x_55514 (list_248 list_248 list_248) Bool)
(assert (forall ((x_55519 list_248) (z_2068 Int) (xs_664 list_248) (y_2303 list_248))
	(=> (x_55514 x_55519 xs_664 y_2303) (x_55514 (cons_248 z_2068 x_55519) (cons_248 z_2068 xs_664) y_2303))))
(assert (forall ((x_55520 list_248))
	(x_55514 x_55520 nil_278 x_55520)))
(declare-fun rev_13 (list_248 list_248) Bool)
(assert (forall ((x_55521 list_248) (x_55522 list_248) (y_2304 Int) (xs_665 list_248))
	(=> (and (rev_13 x_55522 xs_665) (x_55514 x_55521 x_55522 (cons_248 y_2304 nil_278))) (rev_13 x_55521 (cons_248 y_2304 xs_665)))))
(assert (rev_13 nil_278 nil_278))
(assert (forall ((x_55525 list_248) (x_55526 list_248) (x_55527 list_248) (x_55528 list_248) (x_55529 list_248) (x_55530 list_248) (x_55531 list_248) (x_55532 list_248) (x_55517 list_248) (y_2305 list_248))
	(=> (and (diseqlist_248 x_55527 x_55532) (x_55514 x_55525 x_55517 y_2305) (rev_13 x_55526 x_55525) (rev_13 x_55527 x_55526) (rev_13 x_55528 x_55517) (rev_13 x_55529 x_55528) (rev_13 x_55530 y_2305) (rev_13 x_55531 x_55530) (x_55514 x_55532 x_55529 x_55531)) false)))
(check-sat)

(set-logic HORN)
(define-fun Z_2017 () Int 0)
(define-fun S_457 ((x Int)) Int (+ x 1))
(define-fun Z_2013 () Int 0)
(define-fun S_456 ((x Int)) Int (+ x 1))
(declare-fun unS_669 (Int Int) Bool)
(declare-fun isZ_424 (Int) Bool)
(declare-fun isS_424 (Int) Bool)
(assert (forall ((x_55027 Int))
	(unS_669 x_55027 (S_457 x_55027))))
(assert (isZ_424 Z_2017))
(assert (forall ((x_55029 Int))
	(isS_424 (S_457 x_55029))))
(declare-fun add_360 (Int Int Int) Bool)
(declare-fun minus_355 (Int Int Int) Bool)
(declare-fun le_334 (Int Int) Bool)
(declare-fun ge_334 (Int Int) Bool)
(declare-fun lt_354 (Int Int) Bool)
(declare-fun gt_337 (Int Int) Bool)
(declare-fun mult_334 (Int Int Int) Bool)
(declare-fun div_334 (Int Int Int) Bool)
(declare-fun mod_336 (Int Int Int) Bool)
(assert (forall ((y_2254 Int))
	(add_360 y_2254 Z_2017 y_2254)))
(assert (forall ((x_55001 Int) (y_2254 Int) (r_407 Int))
	(=> (add_360 r_407 x_55001 y_2254) (add_360 (S_457 r_407) (S_457 x_55001) y_2254))))
(assert (forall ((y_2254 Int))
	(minus_355 Z_2017 Z_2017 y_2254)))
(assert (forall ((x_55001 Int) (y_2254 Int) (r_407 Int))
	(=> (minus_355 r_407 x_55001 y_2254) (minus_355 (S_457 r_407) (S_457 x_55001) y_2254))))
(assert (forall ((y_2254 Int))
	(le_334 Z_2017 y_2254)))
(assert (forall ((x_55001 Int) (y_2254 Int))
	(=> (le_334 x_55001 y_2254) (le_334 (S_457 x_55001) (S_457 y_2254)))))
(assert (forall ((y_2254 Int))
	(ge_334 y_2254 Z_2017)))
(assert (forall ((x_55001 Int) (y_2254 Int))
	(=> (ge_334 x_55001 y_2254) (ge_334 (S_457 x_55001) (S_457 y_2254)))))
(assert (forall ((y_2254 Int))
	(lt_354 Z_2017 (S_457 y_2254))))
(assert (forall ((x_55001 Int) (y_2254 Int))
	(=> (lt_354 x_55001 y_2254) (lt_354 (S_457 x_55001) (S_457 y_2254)))))
(assert (forall ((y_2254 Int))
	(gt_337 (S_457 y_2254) Z_2017)))
(assert (forall ((x_55001 Int) (y_2254 Int))
	(=> (gt_337 x_55001 y_2254) (gt_337 (S_457 x_55001) (S_457 y_2254)))))
(assert (forall ((y_2254 Int))
	(mult_334 Z_2017 Z_2017 y_2254)))
(assert (forall ((x_55001 Int) (y_2254 Int) (r_407 Int) (z_2018 Int))
	(=> (and (mult_334 r_407 x_55001 y_2254) (add_360 z_2018 r_407 y_2254)) (mult_334 z_2018 (S_457 x_55001) y_2254))))
(assert (forall ((x_55001 Int) (y_2254 Int))
	(=> (lt_354 x_55001 y_2254) (div_334 Z_2017 x_55001 y_2254))))
(assert (forall ((x_55001 Int) (y_2254 Int) (r_407 Int) (z_2018 Int))
	(=> (and (ge_334 x_55001 y_2254) (minus_355 z_2018 x_55001 y_2254) (div_334 r_407 z_2018 y_2254)) (div_334 (S_457 r_407) x_55001 y_2254))))
(assert (forall ((x_55001 Int) (y_2254 Int))
	(=> (lt_354 x_55001 y_2254) (mod_336 x_55001 x_55001 y_2254))))
(assert (forall ((x_55001 Int) (y_2254 Int) (r_407 Int) (z_2018 Int))
	(=> (and (ge_334 x_55001 y_2254) (minus_355 z_2018 x_55001 y_2254) (mod_336 r_407 z_2018 y_2254)) (mod_336 r_407 x_55001 y_2254))))
(declare-datatypes ((Bool_334 0)) (((false_334) (true_334))))
(declare-fun diseqBool_154 (Bool_334 Bool_334) Bool)
(declare-fun isfalse_154 (Bool_334) Bool)
(declare-fun istrue_154 (Bool_334) Bool)
(assert (isfalse_154 false_334))
(assert (istrue_154 true_334))
(assert (diseqBool_154 false_334 true_334))
(assert (diseqBool_154 true_334 false_334))
(declare-fun and_334 (Bool_334 Bool_334 Bool_334) Bool)
(declare-fun or_341 (Bool_334 Bool_334 Bool_334) Bool)
(declare-fun hence_334 (Bool_334 Bool_334 Bool_334) Bool)
(declare-fun not_339 (Bool_334 Bool_334) Bool)
(assert (and_334 false_334 false_334 false_334))
(assert (and_334 false_334 true_334 false_334))
(assert (and_334 false_334 false_334 true_334))
(assert (and_334 true_334 true_334 true_334))
(assert (or_341 false_334 false_334 false_334))
(assert (or_341 true_334 true_334 false_334))
(assert (or_341 true_334 false_334 true_334))
(assert (or_341 true_334 true_334 true_334))
(assert (hence_334 true_334 false_334 false_334))
(assert (hence_334 false_334 true_334 false_334))
(assert (hence_334 true_334 false_334 true_334))
(assert (hence_334 true_334 true_334 true_334))
(assert (not_339 true_334 false_334))
(assert (not_339 false_334 true_334))
(declare-datatypes ((list_238 0)) (((nil_268) (cons_238 (head_476 Int) (tail_476 list_238)))))
(declare-fun diseqlist_238 (list_238 list_238) Bool)
(declare-fun head_477 (Int list_238) Bool)
(declare-fun tail_477 (list_238 list_238) Bool)
(declare-fun isnil_268 (list_238) Bool)
(declare-fun iscons_238 (list_238) Bool)
(assert (forall ((x_55005 Int) (x_55006 list_238))
	(head_477 x_55005 (cons_238 x_55005 x_55006))))
(assert (forall ((x_55005 Int) (x_55006 list_238))
	(tail_477 x_55006 (cons_238 x_55005 x_55006))))
(assert (isnil_268 nil_268))
(assert (forall ((x_55008 Int) (x_55009 list_238))
	(iscons_238 (cons_238 x_55008 x_55009))))
(assert (forall ((x_55010 Int) (x_55011 list_238))
	(diseqlist_238 nil_268 (cons_238 x_55010 x_55011))))
(assert (forall ((x_55012 Int) (x_55013 list_238))
	(diseqlist_238 (cons_238 x_55012 x_55013) nil_268)))
(assert (forall ((x_55014 Int) (x_55015 list_238) (x_55016 Int) (x_55017 list_238))
	(=> (distinct x_55014 x_55016) (diseqlist_238 (cons_238 x_55014 x_55015) (cons_238 x_55016 x_55017)))))
(assert (forall ((x_55014 Int) (x_55015 list_238) (x_55016 Int) (x_55017 list_238))
	(=> (diseqlist_238 x_55015 x_55017) (diseqlist_238 (cons_238 x_55014 x_55015) (cons_238 x_55016 x_55017)))))
(declare-fun projS_179 (Int Int) Bool)
(declare-fun isZ_423 (Int) Bool)
(declare-fun isS_423 (Int) Bool)
(assert (forall ((x_55019 Int))
	(projS_179 x_55019 (S_456 x_55019))))
(assert (isZ_423 Z_2013))
(assert (forall ((x_55021 Int))
	(isS_423 (S_456 x_55021))))
(declare-fun length_47 (Int list_238) Bool)
(assert (forall ((x_54982 Int) (y_2249 Int) (xs_645 list_238))
	(=> (length_47 x_54982 xs_645) (length_47 (S_456 x_54982) (cons_238 y_2249 xs_645)))))
(assert (length_47 Z_2013 nil_268))
(declare-fun even_3 (Bool_334 Int) Bool)
(assert (forall ((x_54984 Bool_334) (z_2014 Int))
	(=> (even_3 x_54984 z_2014) (even_3 x_54984 (S_456 (S_456 z_2014))))))
(assert (even_3 false_334 (S_456 Z_2013)))
(assert (even_3 true_334 Z_2013))
(declare-fun x_54976 (Int Int Int) Bool)
(assert (forall ((x_54989 Int) (z_2015 Int) (y_2251 Int))
	(=> (x_54976 x_54989 z_2015 y_2251) (x_54976 (S_456 x_54989) (S_456 z_2015) y_2251))))
(assert (forall ((x_54990 Int))
	(x_54976 x_54990 Z_2013 x_54990)))
(declare-fun x_54978 (list_238 list_238 list_238) Bool)
(assert (forall ((x_54992 list_238) (z_2016 Int) (xs_646 list_238) (y_2252 list_238))
	(=> (x_54978 x_54992 xs_646 y_2252) (x_54978 (cons_238 z_2016 x_54992) (cons_238 z_2016 xs_646) y_2252))))
(assert (forall ((x_54993 list_238))
	(x_54978 x_54993 nil_268 x_54993)))
(assert (forall ((x_54994 list_238) (x_54995 Int) (x_54996 Bool_334) (x_54997 Int) (x_54998 Int) (x_54999 Int) (x_55000 Bool_334) (x_54980 list_238) (y_2253 list_238))
	(=> (and (diseqBool_154 x_54996 x_55000) (x_54978 x_54994 x_54980 y_2253) (length_47 x_54995 x_54994) (even_3 x_54996 x_54995) (length_47 x_54997 y_2253) (length_47 x_54998 x_54980) (x_54976 x_54999 x_54997 x_54998) (even_3 x_55000 x_54999)) false)))
(check-sat)
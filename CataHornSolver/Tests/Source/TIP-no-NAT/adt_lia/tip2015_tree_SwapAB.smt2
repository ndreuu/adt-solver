(set-logic HORN)
(define-fun Z_790 () Int 0)
(define-fun S_225 ((x Int)) Int (+ x 1))
(declare-fun unS_283 (Int Int) Bool)
(declare-fun isZ_214 (Int) Bool)
(declare-fun isS_214 (Int) Bool)
(assert (forall ((x_21394 Int))
	(unS_283 x_21394 (S_225 x_21394))))
(assert (isZ_214 Z_790))
(assert (forall ((x_21396 Int))
	(isS_214 (S_225 x_21396))))
(declare-fun add_149 (Int Int Int) Bool)
(declare-fun minus_144 (Int Int Int) Bool)
(declare-fun le_141 (Int Int) Bool)
(declare-fun ge_141 (Int Int) Bool)
(declare-fun lt_145 (Int Int) Bool)
(declare-fun gt_142 (Int Int) Bool)
(declare-fun mult_141 (Int Int Int) Bool)
(declare-fun div_141 (Int Int Int) Bool)
(declare-fun mod_141 (Int Int Int) Bool)
(assert (forall ((y_785 Int))
	(add_149 y_785 Z_790 y_785)))
(assert (forall ((x_21392 Int) (y_785 Int) (r_168 Int))
	(=> (add_149 r_168 x_21392 y_785) (add_149 (S_225 r_168) (S_225 x_21392) y_785))))
(assert (forall ((y_785 Int))
	(minus_144 Z_790 Z_790 y_785)))
(assert (forall ((x_21392 Int) (y_785 Int) (r_168 Int))
	(=> (minus_144 r_168 x_21392 y_785) (minus_144 (S_225 r_168) (S_225 x_21392) y_785))))
(assert (forall ((y_785 Int))
	(le_141 Z_790 y_785)))
(assert (forall ((x_21392 Int) (y_785 Int))
	(=> (le_141 x_21392 y_785) (le_141 (S_225 x_21392) (S_225 y_785)))))
(assert (forall ((y_785 Int))
	(ge_141 y_785 Z_790)))
(assert (forall ((x_21392 Int) (y_785 Int))
	(=> (ge_141 x_21392 y_785) (ge_141 (S_225 x_21392) (S_225 y_785)))))
(assert (forall ((y_785 Int))
	(lt_145 Z_790 (S_225 y_785))))
(assert (forall ((x_21392 Int) (y_785 Int))
	(=> (lt_145 x_21392 y_785) (lt_145 (S_225 x_21392) (S_225 y_785)))))
(assert (forall ((y_785 Int))
	(gt_142 (S_225 y_785) Z_790)))
(assert (forall ((x_21392 Int) (y_785 Int))
	(=> (gt_142 x_21392 y_785) (gt_142 (S_225 x_21392) (S_225 y_785)))))
(assert (forall ((y_785 Int))
	(mult_141 Z_790 Z_790 y_785)))
(assert (forall ((x_21392 Int) (y_785 Int) (r_168 Int) (z_791 Int))
	(=> (and (mult_141 r_168 x_21392 y_785) (add_149 z_791 r_168 y_785)) (mult_141 z_791 (S_225 x_21392) y_785))))
(assert (forall ((x_21392 Int) (y_785 Int))
	(=> (lt_145 x_21392 y_785) (div_141 Z_790 x_21392 y_785))))
(assert (forall ((x_21392 Int) (y_785 Int) (r_168 Int) (z_791 Int))
	(=> (and (ge_141 x_21392 y_785) (minus_144 z_791 x_21392 y_785) (div_141 r_168 z_791 y_785)) (div_141 (S_225 r_168) x_21392 y_785))))
(assert (forall ((x_21392 Int) (y_785 Int))
	(=> (lt_145 x_21392 y_785) (mod_141 x_21392 x_21392 y_785))))
(assert (forall ((x_21392 Int) (y_785 Int) (r_168 Int) (z_791 Int))
	(=> (and (ge_141 x_21392 y_785) (minus_144 z_791 x_21392 y_785) (mod_141 r_168 z_791 y_785)) (mod_141 r_168 x_21392 y_785))))
(declare-datatypes ((Bool_141 0)) (((false_141) (true_141))))
(declare-fun diseqBool_61 (Bool_141 Bool_141) Bool)
(declare-fun isfalse_61 (Bool_141) Bool)
(declare-fun istrue_61 (Bool_141) Bool)
(assert (isfalse_61 false_141))
(assert (istrue_61 true_141))
(assert (diseqBool_61 false_141 true_141))
(assert (diseqBool_61 true_141 false_141))
(declare-fun and_141 (Bool_141 Bool_141 Bool_141) Bool)
(declare-fun or_142 (Bool_141 Bool_141 Bool_141) Bool)
(declare-fun hence_141 (Bool_141 Bool_141 Bool_141) Bool)
(declare-fun not_141 (Bool_141 Bool_141) Bool)
(assert (and_141 false_141 false_141 false_141))
(assert (and_141 false_141 true_141 false_141))
(assert (and_141 false_141 false_141 true_141))
(assert (and_141 true_141 true_141 true_141))
(assert (or_142 false_141 false_141 false_141))
(assert (or_142 true_141 true_141 false_141))
(assert (or_142 true_141 false_141 true_141))
(assert (or_142 true_141 true_141 true_141))
(assert (hence_141 true_141 false_141 false_141))
(assert (hence_141 false_141 true_141 false_141))
(assert (hence_141 true_141 false_141 true_141))
(assert (hence_141 true_141 true_141 true_141))
(assert (not_141 true_141 false_141))
(assert (not_141 false_141 true_141))
(declare-datatypes ((list_104 0)) (((nil_114) (cons_104 (head_208 Int) (tail_208 list_104)))))
(declare-fun diseqlist_104 (list_104 list_104) Bool)
(declare-fun head_209 (Int list_104) Bool)
(declare-fun tail_209 (list_104 list_104) Bool)
(declare-fun isnil_114 (list_104) Bool)
(declare-fun iscons_104 (list_104) Bool)
(assert (forall ((x_21404 Int) (x_21405 list_104))
	(head_209 x_21404 (cons_104 x_21404 x_21405))))
(assert (forall ((x_21404 Int) (x_21405 list_104))
	(tail_209 x_21405 (cons_104 x_21404 x_21405))))
(assert (isnil_114 nil_114))
(assert (forall ((x_21407 Int) (x_21408 list_104))
	(iscons_104 (cons_104 x_21407 x_21408))))
(assert (forall ((x_21409 Int) (x_21410 list_104))
	(diseqlist_104 nil_114 (cons_104 x_21409 x_21410))))
(assert (forall ((x_21411 Int) (x_21412 list_104))
	(diseqlist_104 (cons_104 x_21411 x_21412) nil_114)))
(assert (forall ((x_21413 Int) (x_21414 list_104) (x_21415 Int) (x_21416 list_104))
	(=> (distinct x_21413 x_21415) (diseqlist_104 (cons_104 x_21413 x_21414) (cons_104 x_21415 x_21416)))))
(assert (forall ((x_21413 Int) (x_21414 list_104) (x_21415 Int) (x_21416 list_104))
	(=> (diseqlist_104 x_21414 x_21416) (diseqlist_104 (cons_104 x_21413 x_21414) (cons_104 x_21415 x_21416)))))
(declare-datatypes ((Tree_4 0)) (((Node_5 (projNode_30 Tree_4) (projNode_31 Int) (projNode_32 Tree_4)) (Nil_115))))
(declare-fun diseqTree_4 (Tree_4 Tree_4) Bool)
(declare-fun projNode_33 (Tree_4 Tree_4) Bool)
(declare-fun projNode_34 (Int Tree_4) Bool)
(declare-fun projNode_35 (Tree_4 Tree_4) Bool)
(declare-fun isNode_5 (Tree_4) Bool)
(declare-fun isNil_115 (Tree_4) Bool)
(assert (forall ((x_21417 Tree_4) (x_21418 Int) (x_21419 Tree_4))
	(projNode_33 x_21417 (Node_5 x_21417 x_21418 x_21419))))
(assert (forall ((x_21417 Tree_4) (x_21418 Int) (x_21419 Tree_4))
	(projNode_34 x_21418 (Node_5 x_21417 x_21418 x_21419))))
(assert (forall ((x_21417 Tree_4) (x_21418 Int) (x_21419 Tree_4))
	(projNode_35 x_21419 (Node_5 x_21417 x_21418 x_21419))))
(assert (forall ((x_21422 Tree_4) (x_21423 Int) (x_21424 Tree_4))
	(isNode_5 (Node_5 x_21422 x_21423 x_21424))))
(assert (isNil_115 Nil_115))
(assert (forall ((x_21425 Tree_4) (x_21426 Int) (x_21427 Tree_4))
	(diseqTree_4 (Node_5 x_21425 x_21426 x_21427) Nil_115)))
(assert (forall ((x_21428 Tree_4) (x_21429 Int) (x_21430 Tree_4))
	(diseqTree_4 Nil_115 (Node_5 x_21428 x_21429 x_21430))))
(assert (forall ((x_21431 Tree_4) (x_21432 Int) (x_21433 Tree_4) (x_21434 Tree_4) (x_21435 Int) (x_21436 Tree_4))
	(=> (diseqTree_4 x_21431 x_21434) (diseqTree_4 (Node_5 x_21431 x_21432 x_21433) (Node_5 x_21434 x_21435 x_21436)))))
(assert (forall ((x_21431 Tree_4) (x_21432 Int) (x_21433 Tree_4) (x_21434 Tree_4) (x_21435 Int) (x_21436 Tree_4))
	(=> (distinct x_21432 x_21435) (diseqTree_4 (Node_5 x_21431 x_21432 x_21433) (Node_5 x_21434 x_21435 x_21436)))))
(assert (forall ((x_21431 Tree_4) (x_21432 Int) (x_21433 Tree_4) (x_21434 Tree_4) (x_21435 Int) (x_21436 Tree_4))
	(=> (diseqTree_4 x_21433 x_21436) (diseqTree_4 (Node_5 x_21431 x_21432 x_21433) (Node_5 x_21434 x_21435 x_21436)))))
(declare-fun swap_0 (Tree_4 Int Int Tree_4) Bool)
(assert (forall ((x_21346 Int) (y_781 Int))
	(swap_0 Nil_115 x_21346 y_781 Nil_115)))
(assert (forall ((x_21354 Tree_4) (x_21355 Tree_4) (p_107 Tree_4) (q_39 Tree_4) (x_21346 Int) (y_781 Int))
	(=> (and (swap_0 x_21354 x_21346 y_781 p_107) (swap_0 x_21355 x_21346 y_781 q_39)) (swap_0 (Node_5 x_21354 y_781 x_21355) x_21346 y_781 (Node_5 p_107 x_21346 q_39)))))
(assert (forall ((x_21357 Tree_4) (x_21358 Tree_4) (p_107 Tree_4) (x_21347 Int) (q_39 Tree_4) (x_21346 Int))
	(=> (and (distinct x_21347 x_21346) (swap_0 x_21357 x_21346 x_21347 p_107) (swap_0 x_21358 x_21346 x_21347 q_39)) (swap_0 (Node_5 x_21357 x_21346 x_21358) x_21346 x_21347 (Node_5 p_107 x_21347 q_39)))))
(assert (forall ((x_21360 Tree_4) (x_21361 Tree_4) (p_107 Tree_4) (q_39 Tree_4) (x_21346 Int) (y_781 Int))
	(=> (and (swap_0 x_21360 x_21346 y_781 p_107) (swap_0 x_21361 x_21346 y_781 q_39)) (swap_0 (Node_5 x_21360 y_781 x_21361) x_21346 y_781 (Node_5 p_107 x_21346 q_39)))))
(assert (forall ((x_21363 Tree_4) (x_21364 Tree_4) (p_107 Tree_4) (x_21347 Int) (q_39 Tree_4) (x_21346 Int) (y_781 Int))
	(=> (and (distinct x_21347 x_21346) (distinct x_21347 y_781) (swap_0 x_21363 x_21346 y_781 p_107) (swap_0 x_21364 x_21346 y_781 q_39)) (swap_0 (Node_5 x_21363 x_21347 x_21364) x_21346 y_781 (Node_5 p_107 x_21347 q_39)))))
(declare-fun elem_8 (Bool_141 Int list_104) Bool)
(assert (forall ((xs_246 list_104) (x_21348 Int))
	(elem_8 true_141 x_21348 (cons_104 x_21348 xs_246))))
(assert (forall ((x_21366 Bool_141) (z_788 Int) (xs_246 list_104) (x_21348 Int))
	(=> (and (distinct z_788 x_21348) (elem_8 x_21366 x_21348 xs_246)) (elem_8 x_21366 x_21348 (cons_104 z_788 xs_246)))))
(assert (forall ((x_21348 Int))
	(elem_8 false_141 x_21348 nil_114)))
(declare-fun x_21349 (list_104 list_104 list_104) Bool)
(assert (forall ((x_21370 list_104) (z_789 Int) (xs_247 list_104) (y_783 list_104))
	(=> (x_21349 x_21370 xs_247 y_783) (x_21349 (cons_104 z_789 x_21370) (cons_104 z_789 xs_247) y_783))))
(assert (forall ((x_21371 list_104))
	(x_21349 x_21371 nil_114 x_21371)))
(declare-fun flatten_4 (list_104 Tree_4) Bool)
(assert (flatten_4 nil_114 Nil_115))
(assert (forall ((x_21373 list_104) (x_21374 list_104) (x_21375 list_104) (x_21376 list_104) (p_108 Tree_4) (y_784 Int) (q_40 Tree_4))
	(=> (and (flatten_4 x_21374 p_108) (flatten_4 x_21375 q_40) (x_21349 x_21376 (cons_104 y_784 nil_114) x_21375) (x_21349 x_21373 x_21374 x_21376)) (flatten_4 x_21373 (Node_5 p_108 y_784 q_40)))))
(assert (forall ((x_21383 list_104) (x_21381 list_104) (x_21378 Tree_4) (x_21379 list_104) (p_109 Tree_4) (a_26 Int) (b_17 Int))
	(=> (and (flatten_4 x_21383 p_109) (elem_8 true_141 a_26 x_21383) (flatten_4 x_21381 p_109) (elem_8 true_141 b_17 x_21381) (swap_0 x_21378 a_26 b_17 p_109) (flatten_4 x_21379 x_21378) (elem_8 false_141 a_26 x_21379)) false)))
(assert (forall ((x_21390 list_104) (x_21388 list_104) (x_21385 Tree_4) (x_21386 list_104) (p_109 Tree_4) (a_26 Int) (b_17 Int))
	(=> (and (flatten_4 x_21390 p_109) (elem_8 true_141 a_26 x_21390) (flatten_4 x_21388 p_109) (elem_8 true_141 b_17 x_21388) (swap_0 x_21385 a_26 b_17 p_109) (flatten_4 x_21386 x_21385) (elem_8 false_141 b_17 x_21386)) false)))
(check-sat)

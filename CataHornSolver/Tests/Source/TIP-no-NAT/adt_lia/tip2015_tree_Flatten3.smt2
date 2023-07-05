(set-logic HORN)
(define-fun Z_1889 () Int 0)
(define-fun S_417 ((x Int)) Int (+ x 1))
(declare-fun unS_623 (Int Int) Bool)
(declare-fun isZ_384 (Int) Bool)
(declare-fun isS_384 (Int) Bool)
(assert (forall ((x_53710 Int))
	(unS_623 x_53710 (S_417 x_53710))))
(assert (isZ_384 Z_1889))
(assert (forall ((x_53712 Int))
	(isS_384 (S_417 x_53712))))
(declare-fun add_335 (Int Int Int) Bool)
(declare-fun minus_332 (Int Int Int) Bool)
(declare-fun le_311 (Int Int) Bool)
(declare-fun ge_311 (Int Int) Bool)
(declare-fun lt_331 (Int Int) Bool)
(declare-fun gt_314 (Int Int) Bool)
(declare-fun mult_311 (Int Int Int) Bool)
(declare-fun div_311 (Int Int Int) Bool)
(declare-fun mod_313 (Int Int Int) Bool)
(assert (forall ((y_2122 Int))
	(add_335 y_2122 Z_1889 y_2122)))
(assert (forall ((x_53674 Int) (y_2122 Int) (r_382 Int))
	(=> (add_335 r_382 x_53674 y_2122) (add_335 (S_417 r_382) (S_417 x_53674) y_2122))))
(assert (forall ((y_2122 Int))
	(minus_332 Z_1889 Z_1889 y_2122)))
(assert (forall ((x_53674 Int) (y_2122 Int) (r_382 Int))
	(=> (minus_332 r_382 x_53674 y_2122) (minus_332 (S_417 r_382) (S_417 x_53674) y_2122))))
(assert (forall ((y_2122 Int))
	(le_311 Z_1889 y_2122)))
(assert (forall ((x_53674 Int) (y_2122 Int))
	(=> (le_311 x_53674 y_2122) (le_311 (S_417 x_53674) (S_417 y_2122)))))
(assert (forall ((y_2122 Int))
	(ge_311 y_2122 Z_1889)))
(assert (forall ((x_53674 Int) (y_2122 Int))
	(=> (ge_311 x_53674 y_2122) (ge_311 (S_417 x_53674) (S_417 y_2122)))))
(assert (forall ((y_2122 Int))
	(lt_331 Z_1889 (S_417 y_2122))))
(assert (forall ((x_53674 Int) (y_2122 Int))
	(=> (lt_331 x_53674 y_2122) (lt_331 (S_417 x_53674) (S_417 y_2122)))))
(assert (forall ((y_2122 Int))
	(gt_314 (S_417 y_2122) Z_1889)))
(assert (forall ((x_53674 Int) (y_2122 Int))
	(=> (gt_314 x_53674 y_2122) (gt_314 (S_417 x_53674) (S_417 y_2122)))))
(assert (forall ((y_2122 Int))
	(mult_311 Z_1889 Z_1889 y_2122)))
(assert (forall ((x_53674 Int) (y_2122 Int) (r_382 Int) (z_1890 Int))
	(=> (and (mult_311 r_382 x_53674 y_2122) (add_335 z_1890 r_382 y_2122)) (mult_311 z_1890 (S_417 x_53674) y_2122))))
(assert (forall ((x_53674 Int) (y_2122 Int))
	(=> (lt_331 x_53674 y_2122) (div_311 Z_1889 x_53674 y_2122))))
(assert (forall ((x_53674 Int) (y_2122 Int) (r_382 Int) (z_1890 Int))
	(=> (and (ge_311 x_53674 y_2122) (minus_332 z_1890 x_53674 y_2122) (div_311 r_382 z_1890 y_2122)) (div_311 (S_417 r_382) x_53674 y_2122))))
(assert (forall ((x_53674 Int) (y_2122 Int))
	(=> (lt_331 x_53674 y_2122) (mod_313 x_53674 x_53674 y_2122))))
(assert (forall ((x_53674 Int) (y_2122 Int) (r_382 Int) (z_1890 Int))
	(=> (and (ge_311 x_53674 y_2122) (minus_332 z_1890 x_53674 y_2122) (mod_313 r_382 z_1890 y_2122)) (mod_313 r_382 x_53674 y_2122))))
(declare-datatypes ((list_217 0)) (((nil_245) (cons_217 (head_434 Int) (tail_434 list_217)))))
(declare-fun diseqlist_217 (list_217 list_217) Bool)
(declare-fun head_435 (Int list_217) Bool)
(declare-fun tail_435 (list_217 list_217) Bool)
(declare-fun isnil_245 (list_217) Bool)
(declare-fun iscons_217 (list_217) Bool)
(assert (forall ((x_53676 Int) (x_53677 list_217))
	(head_435 x_53676 (cons_217 x_53676 x_53677))))
(assert (forall ((x_53676 Int) (x_53677 list_217))
	(tail_435 x_53677 (cons_217 x_53676 x_53677))))
(assert (isnil_245 nil_245))
(assert (forall ((x_53679 Int) (x_53680 list_217))
	(iscons_217 (cons_217 x_53679 x_53680))))
(assert (forall ((x_53681 Int) (x_53682 list_217))
	(diseqlist_217 nil_245 (cons_217 x_53681 x_53682))))
(assert (forall ((x_53683 Int) (x_53684 list_217))
	(diseqlist_217 (cons_217 x_53683 x_53684) nil_245)))
(assert (forall ((x_53685 Int) (x_53686 list_217) (x_53687 Int) (x_53688 list_217))
	(=> (distinct x_53685 x_53687) (diseqlist_217 (cons_217 x_53685 x_53686) (cons_217 x_53687 x_53688)))))
(assert (forall ((x_53685 Int) (x_53686 list_217) (x_53687 Int) (x_53688 list_217))
	(=> (diseqlist_217 x_53686 x_53688) (diseqlist_217 (cons_217 x_53685 x_53686) (cons_217 x_53687 x_53688)))))
(declare-datatypes ((Tree_9 0)) (((Node_15 (projNode_90 Tree_9) (projNode_91 Int) (projNode_92 Tree_9)) (Nil_246))))
(declare-fun diseqTree_9 (Tree_9 Tree_9) Bool)
(declare-fun projNode_93 (Tree_9 Tree_9) Bool)
(declare-fun projNode_94 (Int Tree_9) Bool)
(declare-fun projNode_95 (Tree_9 Tree_9) Bool)
(declare-fun isNode_15 (Tree_9) Bool)
(declare-fun isNil_246 (Tree_9) Bool)
(assert (forall ((x_53689 Tree_9) (x_53690 Int) (x_53691 Tree_9))
	(projNode_93 x_53689 (Node_15 x_53689 x_53690 x_53691))))
(assert (forall ((x_53689 Tree_9) (x_53690 Int) (x_53691 Tree_9))
	(projNode_94 x_53690 (Node_15 x_53689 x_53690 x_53691))))
(assert (forall ((x_53689 Tree_9) (x_53690 Int) (x_53691 Tree_9))
	(projNode_95 x_53691 (Node_15 x_53689 x_53690 x_53691))))
(assert (forall ((x_53694 Tree_9) (x_53695 Int) (x_53696 Tree_9))
	(isNode_15 (Node_15 x_53694 x_53695 x_53696))))
(assert (isNil_246 Nil_246))
(assert (forall ((x_53697 Tree_9) (x_53698 Int) (x_53699 Tree_9))
	(diseqTree_9 (Node_15 x_53697 x_53698 x_53699) Nil_246)))
(assert (forall ((x_53700 Tree_9) (x_53701 Int) (x_53702 Tree_9))
	(diseqTree_9 Nil_246 (Node_15 x_53700 x_53701 x_53702))))
(assert (forall ((x_53703 Tree_9) (x_53704 Int) (x_53705 Tree_9) (x_53706 Tree_9) (x_53707 Int) (x_53708 Tree_9))
	(=> (diseqTree_9 x_53703 x_53706) (diseqTree_9 (Node_15 x_53703 x_53704 x_53705) (Node_15 x_53706 x_53707 x_53708)))))
(assert (forall ((x_53703 Tree_9) (x_53704 Int) (x_53705 Tree_9) (x_53706 Tree_9) (x_53707 Int) (x_53708 Tree_9))
	(=> (distinct x_53704 x_53707) (diseqTree_9 (Node_15 x_53703 x_53704 x_53705) (Node_15 x_53706 x_53707 x_53708)))))
(assert (forall ((x_53703 Tree_9) (x_53704 Int) (x_53705 Tree_9) (x_53706 Tree_9) (x_53707 Int) (x_53708 Tree_9))
	(=> (diseqTree_9 x_53705 x_53708) (diseqTree_9 (Node_15 x_53703 x_53704 x_53705) (Node_15 x_53706 x_53707 x_53708)))))
(declare-fun flatten_10 (list_217 Tree_9) Bool)
(assert (flatten_10 nil_245 Nil_246))
(assert (forall ((x_53660 list_217) (z_1887 Int) (r_381 Tree_9))
	(=> (flatten_10 x_53660 r_381) (flatten_10 (cons_217 z_1887 x_53660) (Node_15 Nil_246 z_1887 r_381)))))
(assert (forall ((x_53661 list_217) (p_393 Tree_9) (x_53654 Int) (q_125 Tree_9) (z_1887 Int) (r_381 Tree_9))
	(=> (flatten_10 x_53661 (Node_15 p_393 x_53654 (Node_15 q_125 z_1887 r_381))) (flatten_10 x_53661 (Node_15 (Node_15 p_393 x_53654 q_125) z_1887 r_381)))))
(declare-fun x_53655 (list_217 list_217 list_217) Bool)
(assert (forall ((x_53664 list_217) (z_1888 Int) (xs_601 list_217) (y_2120 list_217))
	(=> (x_53655 x_53664 xs_601 y_2120) (x_53655 (cons_217 z_1888 x_53664) (cons_217 z_1888 xs_601) y_2120))))
(assert (forall ((x_53665 list_217))
	(x_53655 x_53665 nil_245 x_53665)))
(declare-fun flatten_11 (list_217 Tree_9) Bool)
(assert (flatten_11 nil_245 Nil_246))
(assert (forall ((x_53667 list_217) (x_53668 list_217) (x_53669 list_217) (x_53670 list_217) (p_394 Tree_9) (y_2121 Int) (q_126 Tree_9))
	(=> (and (flatten_11 x_53668 p_394) (flatten_11 x_53669 q_126) (x_53655 x_53670 (cons_217 y_2121 nil_245) x_53669) (x_53655 x_53667 x_53668 x_53670)) (flatten_11 x_53667 (Node_15 p_394 y_2121 q_126)))))
(assert (forall ((x_53672 list_217) (x_53673 list_217) (p_395 Tree_9))
	(=> (and (diseqlist_217 x_53672 x_53673) (flatten_10 x_53672 p_395) (flatten_11 x_53673 p_395)) false)))
(check-sat)

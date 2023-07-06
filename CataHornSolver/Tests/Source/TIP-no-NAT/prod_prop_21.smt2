(set-logic HORN)
(define-fun Z_1934 () Int 0)
(define-fun S_429 ((x Int)) Int (+ x 1))
(define-fun Z_1931 () Int 0)
(define-fun S_428 ((x Int)) Int (+ x 1))
(declare-fun unS_639 (Int Int) Bool)
(declare-fun isZ_396 (Int) Bool)
(declare-fun isS_396 (Int) Bool)
(assert (forall ((x_54205 Int))
	(unS_639 x_54205 (S_429 x_54205))))
(assert (isZ_396 Z_1934))
(assert (forall ((x_54207 Int))
	(isS_396 (S_429 x_54207))))
(declare-fun add_345 (Int Int Int) Bool)
(declare-fun minus_340 (Int Int Int) Bool)
(declare-fun le_319 (Int Int) Bool)
(declare-fun ge_319 (Int Int) Bool)
(declare-fun lt_339 (Int Int) Bool)
(declare-fun gt_322 (Int Int) Bool)
(declare-fun mult_319 (Int Int Int) Bool)
(declare-fun div_319 (Int Int Int) Bool)
(declare-fun mod_321 (Int Int Int) Bool)
(assert (forall ((y_2169 Int))
	(add_345 y_2169 Z_1934 y_2169)))
(assert (forall ((x_54181 Int) (y_2169 Int) (r_392 Int))
	(=> (add_345 r_392 x_54181 y_2169) (add_345 (S_429 r_392) (S_429 x_54181) y_2169))))
(assert (forall ((y_2169 Int))
	(minus_340 Z_1934 Z_1934 y_2169)))
(assert (forall ((x_54181 Int) (y_2169 Int) (r_392 Int))
	(=> (minus_340 r_392 x_54181 y_2169) (minus_340 (S_429 r_392) (S_429 x_54181) y_2169))))
(assert (forall ((y_2169 Int))
	(le_319 Z_1934 y_2169)))
(assert (forall ((x_54181 Int) (y_2169 Int))
	(=> (le_319 x_54181 y_2169) (le_319 (S_429 x_54181) (S_429 y_2169)))))
(assert (forall ((y_2169 Int))
	(ge_319 y_2169 Z_1934)))
(assert (forall ((x_54181 Int) (y_2169 Int))
	(=> (ge_319 x_54181 y_2169) (ge_319 (S_429 x_54181) (S_429 y_2169)))))
(assert (forall ((y_2169 Int))
	(lt_339 Z_1934 (S_429 y_2169))))
(assert (forall ((x_54181 Int) (y_2169 Int))
	(=> (lt_339 x_54181 y_2169) (lt_339 (S_429 x_54181) (S_429 y_2169)))))
(assert (forall ((y_2169 Int))
	(gt_322 (S_429 y_2169) Z_1934)))
(assert (forall ((x_54181 Int) (y_2169 Int))
	(=> (gt_322 x_54181 y_2169) (gt_322 (S_429 x_54181) (S_429 y_2169)))))
(assert (forall ((y_2169 Int))
	(mult_319 Z_1934 Z_1934 y_2169)))
(assert (forall ((x_54181 Int) (y_2169 Int) (r_392 Int) (z_1935 Int))
	(=> (and (mult_319 r_392 x_54181 y_2169) (add_345 z_1935 r_392 y_2169)) (mult_319 z_1935 (S_429 x_54181) y_2169))))
(assert (forall ((x_54181 Int) (y_2169 Int))
	(=> (lt_339 x_54181 y_2169) (div_319 Z_1934 x_54181 y_2169))))
(assert (forall ((x_54181 Int) (y_2169 Int) (r_392 Int) (z_1935 Int))
	(=> (and (ge_319 x_54181 y_2169) (minus_340 z_1935 x_54181 y_2169) (div_319 r_392 z_1935 y_2169)) (div_319 (S_429 r_392) x_54181 y_2169))))
(assert (forall ((x_54181 Int) (y_2169 Int))
	(=> (lt_339 x_54181 y_2169) (mod_321 x_54181 x_54181 y_2169))))
(assert (forall ((x_54181 Int) (y_2169 Int) (r_392 Int) (z_1935 Int))
	(=> (and (ge_319 x_54181 y_2169) (minus_340 z_1935 x_54181 y_2169) (mod_321 r_392 z_1935 y_2169)) (mod_321 r_392 x_54181 y_2169))))
(declare-datatypes ((list_224 0)) (((nil_254) (cons_224 (head_448 Int) (tail_448 list_224)))))
(declare-fun diseqlist_224 (list_224 list_224) Bool)
(declare-fun head_449 (Int list_224) Bool)
(declare-fun tail_449 (list_224 list_224) Bool)
(declare-fun isnil_254 (list_224) Bool)
(declare-fun iscons_224 (list_224) Bool)
(assert (forall ((x_54183 Int) (x_54184 list_224))
	(head_449 x_54183 (cons_224 x_54183 x_54184))))
(assert (forall ((x_54183 Int) (x_54184 list_224))
	(tail_449 x_54184 (cons_224 x_54183 x_54184))))
(assert (isnil_254 nil_254))
(assert (forall ((x_54186 Int) (x_54187 list_224))
	(iscons_224 (cons_224 x_54186 x_54187))))
(assert (forall ((x_54188 Int) (x_54189 list_224))
	(diseqlist_224 nil_254 (cons_224 x_54188 x_54189))))
(assert (forall ((x_54190 Int) (x_54191 list_224))
	(diseqlist_224 (cons_224 x_54190 x_54191) nil_254)))
(assert (forall ((x_54192 Int) (x_54193 list_224) (x_54194 Int) (x_54195 list_224))
	(=> (distinct x_54192 x_54194) (diseqlist_224 (cons_224 x_54192 x_54193) (cons_224 x_54194 x_54195)))))
(assert (forall ((x_54192 Int) (x_54193 list_224) (x_54194 Int) (x_54195 list_224))
	(=> (diseqlist_224 x_54193 x_54195) (diseqlist_224 (cons_224 x_54192 x_54193) (cons_224 x_54194 x_54195)))))
(declare-fun projS_153 (Int Int) Bool)
(declare-fun isZ_395 (Int) Bool)
(declare-fun isS_395 (Int) Bool)
(assert (forall ((x_54197 Int))
	(projS_153 x_54197 (S_428 x_54197))))
(assert (isZ_395 Z_1931))
(assert (forall ((x_54199 Int))
	(isS_395 (S_428 x_54199))))
(declare-fun length_41 (Int list_224) Bool)
(assert (forall ((x_54167 Int) (y_2165 Int) (xs_614 list_224))
	(=> (length_41 x_54167 xs_614) (length_41 (S_428 x_54167) (cons_224 y_2165 xs_614)))))
(assert (length_41 Z_1931 nil_254))
(declare-fun x_54160 (list_224 list_224 list_224) Bool)
(assert (forall ((x_54170 list_224) (z_1932 Int) (xs_615 list_224) (y_2166 list_224))
	(=> (x_54160 x_54170 xs_615 y_2166) (x_54160 (cons_224 z_1932 x_54170) (cons_224 z_1932 xs_615) y_2166))))
(assert (forall ((x_54171 list_224))
	(x_54160 x_54171 nil_254 x_54171)))
(declare-fun rotate_5 (list_224 Int list_224) Bool)
(assert (forall ((x_54172 list_224) (x_54173 list_224) (x_54163 Int) (x_54164 list_224) (z_1933 Int))
	(=> (and (x_54160 x_54173 x_54164 (cons_224 x_54163 nil_254)) (rotate_5 x_54172 z_1933 x_54173)) (rotate_5 x_54172 (S_428 z_1933) (cons_224 x_54163 x_54164)))))
(assert (forall ((z_1933 Int))
	(rotate_5 nil_254 (S_428 z_1933) nil_254)))
(assert (forall ((x_54176 list_224))
	(rotate_5 x_54176 Z_1931 x_54176)))
(assert (forall ((x_54177 Int) (x_54178 list_224) (x_54179 list_224) (x_54180 list_224) (x_54165 list_224) (y_2168 list_224))
	(=> (and (diseqlist_224 x_54179 x_54180) (length_41 x_54177 x_54165) (x_54160 x_54178 x_54165 y_2168) (rotate_5 x_54179 x_54177 x_54178) (x_54160 x_54180 y_2168 x_54165)) false)))
(check-sat)
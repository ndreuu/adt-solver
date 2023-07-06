(set-logic HORN)
(define-fun Z_403 () Int 0)
(define-fun S_143 ((x Int)) Int (+ x 1))
(declare-datatypes ((Bool_74 0)) (((false_74) (true_74))))
(declare-fun diseqBool_31 (Bool_74 Bool_74) Bool)
(declare-fun isfalse_31 (Bool_74) Bool)
(declare-fun istrue_31 (Bool_74) Bool)
(assert (isfalse_31 false_74))
(assert (istrue_31 true_74))
(assert (diseqBool_31 false_74 true_74))
(assert (diseqBool_31 true_74 false_74))
(declare-fun and_74 (Bool_74 Bool_74 Bool_74) Bool)
(declare-fun or_74 (Bool_74 Bool_74 Bool_74) Bool)
(declare-fun hence_74 (Bool_74 Bool_74 Bool_74) Bool)
(declare-fun not_74 (Bool_74 Bool_74) Bool)
(assert (and_74 false_74 false_74 false_74))
(assert (and_74 false_74 true_74 false_74))
(assert (and_74 false_74 false_74 true_74))
(assert (and_74 true_74 true_74 true_74))
(assert (or_74 false_74 false_74 false_74))
(assert (or_74 true_74 true_74 false_74))
(assert (or_74 true_74 false_74 true_74))
(assert (or_74 true_74 true_74 true_74))
(assert (hence_74 true_74 false_74 false_74))
(assert (hence_74 false_74 true_74 false_74))
(assert (hence_74 true_74 false_74 true_74))
(assert (hence_74 true_74 true_74 true_74))
(assert (not_74 true_74 false_74))
(assert (not_74 false_74 true_74))
(declare-fun projS_139 (Int Int) Bool)
(declare-fun isZ_143 (Int) Bool)
(declare-fun isS_143 (Int) Bool)
(assert (forall ((x_3921 Int))
	(projS_139 x_3921 (S_143 x_3921))))
(assert (isZ_143 Z_403))
(assert (forall ((x_3923 Int))
	(isS_143 (S_143 x_3923))))
(declare-datatypes ((list_63 0)) (((nil_63) (cons_63 (head_126 Int) (tail_126 list_63)))))
(declare-fun diseqlist_63 (list_63 list_63) Bool)
(declare-fun head_127 (Int list_63) Bool)
(declare-fun tail_127 (list_63 list_63) Bool)
(declare-fun isnil_63 (list_63) Bool)
(declare-fun iscons_63 (list_63) Bool)
(assert (forall ((x_3929 Int) (x_3930 list_63))
	(head_127 x_3929 (cons_63 x_3929 x_3930))))
(assert (forall ((x_3929 Int) (x_3930 list_63))
	(tail_127 x_3930 (cons_63 x_3929 x_3930))))
(assert (isnil_63 nil_63))
(assert (forall ((x_3932 Int) (x_3933 list_63))
	(iscons_63 (cons_63 x_3932 x_3933))))
(assert (forall ((x_3934 Int) (x_3935 list_63))
	(diseqlist_63 nil_63 (cons_63 x_3934 x_3935))))
(assert (forall ((x_3936 Int) (x_3937 list_63))
	(diseqlist_63 (cons_63 x_3936 x_3937) nil_63)))
(assert (forall ((x_3938 Int) (x_3939 list_63) (x_3940 Int) (x_3941 list_63))
	(=> (distinct x_3938 x_3940) (diseqlist_63 (cons_63 x_3938 x_3939) (cons_63 x_3940 x_3941)))))
(assert (forall ((x_3938 Int) (x_3939 list_63) (x_3940 Int) (x_3941 list_63))
	(=> (diseqlist_63 x_3939 x_3941) (diseqlist_63 (cons_63 x_3938 x_3939) (cons_63 x_3940 x_3941)))))
(declare-fun len_12 (Int list_63) Bool)
(assert (forall ((x_3898 Int) (y_318 Int) (xs_117 list_63))
	(=> (len_12 x_3898 xs_117) (len_12 (S_143 x_3898) (cons_63 y_318 xs_117)))))
(assert (len_12 Z_403 nil_63))
(declare-fun last_7 (Int list_63) Bool)
(assert (forall ((x_3900 Int) (x_3889 Int) (x_3890 list_63) (y_319 Int))
	(=> (last_7 x_3900 (cons_63 x_3889 x_3890)) (last_7 x_3900 (cons_63 y_319 (cons_63 x_3889 x_3890))))))
(assert (forall ((x_3902 Int))
	(last_7 x_3902 (cons_63 x_3902 nil_63))))
(assert (last_7 Z_403 nil_63))
(declare-fun drop_14 (list_63 Int list_63) Bool)
(assert (forall ((x_1493 list_63) (x_1483 Int) (x_1484 list_63) (z_147 Int))
	(=> (and (>= z_147 0)  (drop_14 x_1493 z_147 x_1484)) (drop_14 x_1493 (S_143 z_147) (cons_63 x_1483 x_1484)))))
(assert (forall ((z_147 Int))
	(drop_14 nil_63 z_147 nil_63)))
(assert (forall ((n Int) (x_1496 list_63))
	(=> (<= n 0) (drop_14 x_1496 n x_1496))))
(declare-fun x_3894 (Bool_74 Int Int) Bool)
(assert (forall ((x_3908 Bool_74) (x_3896 Int) (z_406 Int))
	(=> (and (>= x_3896 0) (>= z_406 0) (x_3894 x_3908 x_3896 z_406)) (x_3894 x_3908 (S_143 x_3896) (S_143 z_406)))))
(assert (forall ((z_406 Int))
	(=> (>= z_406 0) (x_3894 true_74 Z_403 (S_143 z_406)))))
(assert (forall ((x_3895 Int))
	(x_3894 false_74 x_3895 Z_403)))
(assert (forall ((x_3915 Int) (x_3912 list_63) (x_3913 Int) (x_3914 Int) (n_30 Int) (xs_118 list_63))
	(=> (and (distinct x_3913 x_3914) (len_12 x_3915 xs_118) (x_3894 true_74 n_30 x_3915) (drop_14 x_3912 n_30 xs_118) (last_7 x_3913 x_3912) (last_7 x_3914 xs_118)) false)))
(check-sat)
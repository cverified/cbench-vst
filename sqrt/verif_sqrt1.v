Require Import VST.floyd.proofauto.
Require Import sqrt1.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Require Import sqrt1_f.

Lemma Float32_cmp_eq: forall x y, Float32.cmp Clt x y = 
  match Binary.Bcompare 24 128 x y with Some Lt => true | _ => false end.
Proof.
intros.
Transparent Float32.cmp.
reflexivity.
Opaque Float32.cmp.
Qed.

Lemma Float32_add_eq: Float32.add = float_add Float32.binop_nan .
Proof.
Transparent Float32.add.
unfold Float32.add, float_add.
Opaque Float32.add.
extensionality x y.
auto.
Qed.

Lemma Float32_div_eq: Float32.div = float_div Float32.binop_nan .
Proof.
Transparent Float32.div.
unfold Float32.div, float_div.
Opaque Float32.div.
extensionality x y.
auto.
Qed.

Lemma Float32_of_int_2_eq: Float32.of_int (Int.repr 2) = float2.
Proof.
Transparent Float32.of_int.
unfold Float32.of_int, float2.
Opaque Float32.of_int.
change (Int.signed (Int.repr 2)) with 2%Z.
unfold IEEE754_extra.BofZ.
simpl.
apply f_equal.
apply proof_irr.
Qed.

Definition fsqrt (x: float32) : float32 :=
  if Float32.cmp Cle x (Float32.of_int (Int.repr 0)) 
  then (Float32.of_int (Int.repr 0)) 
  else
  let y := if Float32.cmp Cge x (Float32.of_int (Int.repr 1))
               then x else Float32.of_int (Int.repr 1)  in
  main_loop Float32.binop_nan (x,y).

Require Import Reals.
Open Scope R_scope.

Lemma fsqrt_correct:
 forall x, 
  1 <= Binary.B2R 24 128 x < Rdefinitions.Rinv 2 * Binary.B2R 24 128 predf32max ->
  Rbasic_fun.Rabs (Binary.B2R 24 128 (fsqrt x) - R_sqrt.sqrt (Binary.B2R 24 128 x)) <=
       5 / (2 ^ 23) * R_sqrt.sqrt (Binary.B2R 24 128 x).
Proof.
intros.
unfold fsqrt.
change (Float32.of_int (Int.repr 0)) with (Binary.B754_zero 24 128 false).
change (Float32.of_int (Int.repr 1)) with (Binary.Bone 24 128 (eq_refl _) (eq_refl _)).
Transparent Float32.cmp.
unfold Float32.cmp.
Opaque Float32.cmp.
unfold Float32.compare.
unfold cmp_of_comparison.
rewrite fsqrt_correct_aux0 by auto.
destruct (fsqrt_correct_aux1 x H).
rewrite H0 by auto.
apply main_loop_correct_1_max; auto.
rewrite H0 by auto.
apply main_loop_correct_1_max; auto.
Qed.
Close Scope R_scope.

Definition sqrt_newton_spec :=
   DECLARE _sqrt_newton
   WITH x: float32
   PRE [ tfloat ]
       PROP ()
       PARAMS (Vsingle x) GLOBALS()
       SEP ()
    POST [ tfloat ]
       PROP ()
       LOCAL (temp ret_temp (Vsingle (fsqrt x)))
       SEP ().

Definition Gprog : funspecs :=
         [sqrt_newton_spec].

Lemma body_sqrt_newton:  semax_body Vprog Gprog f_sqrt_newton sqrt_newton_spec.
Proof.
start_function.
forward_if.
forward.
entailer!.
simpl.
unfold fsqrt. rewrite H. auto.
pose (t := if Float32.cmp Cge x (Float32.of_int (Int.repr 1))
                    then x else Float32.of_int (Int.repr 1)).
forward_if (temp _t'1 (Vsingle t)).
forward.
entailer!.
subst t; rewrite H0; auto.
forward.
entailer!.
subst t; rewrite H0; auto.
forward.
deadvars!.
forward_loop
   (EX y:float32, PROP(main_loop Float32.binop_nan (x,y) = fsqrt x)
                 (LOCAL (temp _x (Vsingle x); temp _y (Vsingle y)) SEP()))
 continue: (EX y z:float32, PROP((if Float32.cmp Clt y z
                                then main_loop Float32.binop_nan  (x,y) else y) = fsqrt x)
                     (LOCAL (temp _x (Vsingle x); temp _y (Vsingle y); 
                                  temp _z (Vsingle z)) 
                     SEP()))
   break: (PROP()(LOCAL (temp _y (Vsingle (fsqrt x))) SEP())).
-
Exists t.
entailer!.
unfold fsqrt.
rewrite H.
fold t. auto.
-
Intros y.
forward.
forward.
do 2 EExists; entailer!.
rewrite Float32_div_eq, Float32_add_eq.
change (float_div _ (float_add _ _ _) _) with (body_exp Float32.binop_nan x y).
rewrite main_loop_equation in H0.
rewrite Float32_cmp_eq.
destruct (Binary.Bcompare 24 128 (body_exp Float32.binop_nan x y) y); try destruct c; auto.
Intros y z.
forward_if.
+
forward.
Exists y.
entailer!.
rewrite H1 in H0.
auto.
+
forward.
entailer!.
rewrite H1 in H0.
f_equal; auto.
-
forward.
Qed.

Require Import VST.floyd.proofauto.
Require Import sqrt1.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Require Import sqrt1_f.

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

Require Import Reals.
Open Scope R_scope.
Definition sqrt_newton_spec2 :=
   DECLARE _sqrt_newton
   WITH x: float32
   PRE [ tfloat ]
       PROP ( 1 <= float32_to_real x < (1/2) * float32_to_real predf32max)
       PARAMS (Vsingle x) GLOBALS()
       SEP ()
    POST [ tfloat ]
       PROP (Rabs (float32_to_real (fsqrt x) - R_sqrt.sqrt (float32_to_real x)) <=
                             5 / (2 ^ 23) * R_sqrt.sqrt (float32_to_real x))
       LOCAL (temp ret_temp (Vsingle (fsqrt x)))
       SEP ().
Close Scope R_scope.

Lemma sub_sqrt: funspec_sub (snd sqrt_newton_spec) (snd sqrt_newton_spec2).
Proof.
apply NDsubsume_subsume.
split; auto.
unfold snd.
hnf; intros.
split; auto. intros x [? ?]. Exists x emp.
simpl in x.
normalize.
match goal with |- context [PROPx (?A::_)] => set (P:=A) end.
set (C := (Rdiv 5  (pow 2 23))).
unfold_for_go_lower; normalize. simpl; entailer!; intros.
entailer!.
apply fsqrt_correct; auto.
replace (Rdefinitions.Rinv 2) with (Rdiv 1 2); auto.
unfold Rdiv.
rewrite Rmult_1_l; auto.
Qed.

Print float.
Lemma body_sqrt_newton2:  semax_body Vprog Gprog f_sqrt_newton sqrt_newton_spec2.
Proof.
eapply semax_body_funspec_sub.
apply body_sqrt_newton.
apply sub_sqrt.
repeat constructor; intro H; simpl in H; decompose [or] H; try discriminate; auto.
Qed.


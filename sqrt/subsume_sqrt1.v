Require Import VST.floyd.proofauto.
Require Import sqrt1.

Require Import float_lemmas sqrt1_f verif_sqrt1.
Require Import sqrt1_f_correct.
Require Import Reals.
Open Scope R_scope.

Definition sqrt_newton_spec2 :=
   DECLARE _sqrt_newton
   WITH x: float32
   PRE [ tfloat ]
       PROP ( 1 <= float32_to_real x < (1/2) * float32_to_real predf32max)
       PARAMS (Vsingle x)
       SEP ()
    POST [ tfloat ]
       PROP (Rabs (float32_to_real (fsqrt x) - R_sqrt.sqrt (float32_to_real x)) <=
                             5 / (2 ^ 23) * R_sqrt.sqrt (float32_to_real x))
       RETURN (Vsingle (fsqrt x))
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
apply (fsqrt_correct x); auto.
replace (Rdefinitions.Rinv 2) with (Rdiv 1 2); auto.
unfold Rdiv.
rewrite Rmult_1_l; auto.
Qed.

Lemma body_sqrt_newton2:  semax_body Vprog Gprog f_sqrt_newton sqrt_newton_spec2.
Proof.
eapply semax_body_funspec_sub.
apply body_sqrt_newton.
apply sub_sqrt.
repeat constructor; intro H; simpl in H; decompose [or] H; try discriminate; auto.
Qed.


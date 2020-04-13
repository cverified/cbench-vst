Require Import VST.floyd.proofauto.
Require Import fac3.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Require Import fac_facts.

Definition fac_spec :=
 DECLARE _fac
  WITH n: Z
  PRE  [ tint ] 
     PROP(0 <= n <= 12)
     PARAMS (Vint (Int.repr n)) GLOBALS()
     SEP ()
  POST [ tint ]  
     PROP() 
     LOCAL (temp ret_temp (Vint (Int.repr (fac n))))
     SEP().

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog tt gv
  POST [ tint ]  
     PROP() 
     LOCAL (temp ret_temp (Vint (Int.repr (fac 5))))
     SEP(TT).

Definition Gprog : funspecs :=
        ltac:(with_library prog [fac_spec; main_spec]).

Lemma body_fac:  semax_body Vprog Gprog f_fac fac_spec.
Proof.
start_function.
forward.
forward_while (EX i:Z, EX f: Z,
          PROP(0 <= i <= n; 1 <= f; (fac i * f = fac n)%Z) 
          LOCAL (temp _n (Vint (Int.repr i)); temp _f (Vint (Int.repr f)))
          SEP()).
Exists n 1. entailer!.
entailer!.
forward.
forward.
forward.
entailer!. {
rewrite Int.signed_repr.
2:{
pose proof (fac_in_range n H).
split.
rep_omega.
assert (f <= fac n); [ | rep_omega].
rewrite <- (Z.mul_1_l f).
rewrite <- H2.
apply Z.mul_le_mono_nonneg_r; try rep_omega.
change 1 with (fac 1).
apply fac_mono. omega.
}
rewrite Int.signed_repr by rep_omega.
pose proof (fac_in_range n H).
split.
apply Z.le_trans with 0. rep_omega.
apply Z.mul_nonneg_nonneg; omega.
apply Z.le_trans with (f * fac i)%Z.
apply Z.mul_le_mono_nonneg_l; try rep_omega.
rewrite fac_equation. rewrite if_true by omega.
apply Z.le_trans with (i * 1)%Z. omega.
apply Z.mul_le_mono_nonneg_l; try rep_omega.
change (fac 0 <= fac (i-1)).
apply fac_mono. omega.
rewrite Z.mul_comm. rewrite H2. omega.
}

Exists (i-1, f*i)%Z.
entailer!.
split. omega.
split.
apply Z.le_trans with (f * 1)%Z.
omega.
apply Z.mul_le_mono_nonneg_l; try rep_omega.
rewrite fac_equation in H2. rewrite if_true in H2 by omega.
rewrite <- H2.
rewrite (Z.mul_comm i).
rewrite (Z.mul_comm f).
rewrite Z.mul_assoc.
auto.
rewrite <- (Int.repr_signed (Int.repr i)) in HRE.
apply repr_inj_signed in HRE; try rep_omega.
rewrite Int.signed_repr in HRE by rep_omega. subst.
change (fac 0) with 1 in H2.
rewrite Z.mul_1_l in H2.
subst.
forward.
Qed.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
forward_call.
omega.
forward.
Qed.

Existing Instance NullExtension.Espec.

Lemma prog_correct: semax_prog prog tt Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons body_fac.
semax_func_cons body_main.
Qed.
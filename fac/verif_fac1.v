Require Import VST.floyd.proofauto.
Require Import fac1.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Require Import fac_facts.

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog tt gv
  POST [ tint ]  
     PROP() 
     LOCAL (temp ret_temp (Vint (Int.repr (fac 5))))
     SEP(TT).

Definition Gprog : funspecs :=
        ltac:(with_library prog [main_spec]).

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
forward.
assert (fac 5 <= Int.max_signed) by (compute; congruence).
assert (0 < 5 <= 12) by rep_omega.
forget 5 as n.
forward.
forward_loop (EX i:Z,
  PROP (1 <= i <= n+1)
  LOCAL (temp _f (Vint (Int.repr (fac (i-1)))); temp _i (Vint (Int.repr i)); temp _n (Vint (Int.repr n)))
  SEP(has_ext tt))
   break: (PROP () LOCAL (temp _f (Vint (Int.repr (fac n)))) SEP(has_ext tt)). 
- repeat step!.
-
Intros i. forward_if (i <= n). forward. entailer!.
forward. entailer!.
assert (n=i-1) by omega. subst. auto.
forward. entailer!.
rewrite !Int.signed_repr; try rep_omega.
replace (fac (i-1) * i)%Z with (fac i).
apply fac_in_range; omega.
rewrite fac_equation. rewrite if_true by rep_omega.
rewrite Z.mul_comm. auto.
apply fac_in_range; omega.
forward.
Exists (i+1).
entailer!.
rewrite fac_equation. rewrite if_true by omega.
f_equal; f_equal.
rewrite Z.add_simpl_r.
rewrite Z.mul_comm. auto.
-
forward.
Qed.

Existing Instance NullExtension.Espec.

Lemma prog_correct: semax_prog prog tt Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons body_main.
Qed.


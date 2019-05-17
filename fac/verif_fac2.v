Require Import VST.floyd.proofauto.
Require Import fac2.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Require Import fac_facts.

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog nil gv
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
forward.
forward.
forward_loop (EX r:Z,
  PROP (1 <= r <= n)
  LOCAL (temp _u (Vint (Int.repr (fac r))); 
              temp _r (Vint (Int.repr r)); 
              temp _n (Vint (Int.repr n)))
  SEP())
   break: (PROP () LOCAL (temp _u (Vint (Int.repr (fac n)))) SEP()). 
- repeat step!.
-
Intros r.
forward.
forward_if (r < n). forward. entailer!.
forward. entailer!.
assert (r=n) by omega. subst. auto.
forward.
forward_loop (EX s:Z,
  PROP (1 <= s <= r)
  LOCAL (temp _u (Vint (Int.repr (s * fac r))); 
              temp _v (Vint (Int.repr (fac r)));
              temp _s (Vint (Int.repr s));
              temp _r (Vint (Int.repr r)); 
              temp _n (Vint (Int.repr n)))
  SEP())
   break: (PROP ()
              LOCAL (temp _u (Vint (Int.repr (fac (r+1))));
                         temp _r (Vint (Int.repr r)); 
                         temp _n (Vint (Int.repr n)))
               SEP()).
+
Exists 1; entailer!.
+
pose proof (fac_mono 0 r).
spec H3; [omega|]. change (fac 0) with 1 in H3.
pose proof (fac_mono r (n-1)).
spec H4; [omega|].
assert (fac (n-1) <= fac 11).
apply fac_mono. omega.
set (x := fac 11) in *. compute in x. subst x.
Intros s.
assert (0 <= s * fac r) by (apply Z.mul_nonneg_nonneg; omega).
assert (s * fac r + fac r <= fac (r+1)). {
  rewrite (fac_equation (r+1)).
  rewrite if_true by omega.
  rewrite Z.add_simpl_r.
  replace (s * fac r + fac r) with ((s+1)*(fac r))%Z by (rewrite Z.mul_add_distr_r; omega).
  apply Z.mul_le_mono_nonneg_r; omega.
}
assert (fac (r+1) <= fac n) by (apply fac_mono; omega).
forward.
forward.
forward.
forward_if (s < r).
forward.
entailer!.
forward.
entailer!.
assert (s=r) by omega.
subst s.
replace (r * fac r + fac r) with ((r+1)*(fac r))%Z by (rewrite Z.mul_add_distr_r; omega).
rewrite (fac_equation (r+1)). rewrite if_true by omega.
rewrite Z.add_simpl_r.
auto.
Exists (s+1).
entailer!.
rewrite Z.mul_add_distr_r.
rewrite Z.mul_1_l. auto.
+
forward.
Exists (r+1).
entailer!.
-
forward.
Qed.

Existing Instance NullExtension.Espec.

Lemma prog_correct: semax_prog prog Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons body_main.
Qed.

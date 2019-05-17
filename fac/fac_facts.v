Require Import VST.floyd.functional_base.

Function fac (n: Z) {measure Z.to_nat n}:= 
 if Z_gt_dec n 0 then Z.mul n (fac (n-1)) else 1.
Proof.
intros.
apply Z2Nat.inj_lt; omega.
Defined.

Lemma fac_mono: forall i j, 0 <= i <= j -> fac i <= fac j.
Proof.
intros.
replace j with (i + Z.of_nat (Z.to_nat (j-i)))
 by (rewrite Z2Nat.id; omega).
destruct H as [? _].
induction (Z.to_nat (j - i)).
simpl. rewrite Z.add_0_r; omega.
rewrite inj_S. unfold Z.succ.
rewrite Z.add_assoc. 
eapply Z.le_trans; try eassumption.
rewrite (fac_equation (_ + _ + _)).
rewrite if_true by omega.
rewrite Z.add_simpl_r.
apply Z.le_trans with (1 * fac (i + Z.of_nat n))%Z.
omega.
apply Z.mul_le_mono_nonneg_r; [ | omega].
assert (0 <= fac i); try omega.
clear - H.
replace i with (Z.of_nat (Z.to_nat i)).
2: rewrite Z2Nat.id; omega.
clear.
induction (Z.to_nat i).
compute; congruence.
rewrite inj_S.
unfold Z.succ.
rewrite fac_equation.
rewrite if_true by omega.
rewrite Z.add_simpl_r.
apply Z.mul_nonneg_nonneg; auto.
clear.
pose proof (Nat2Z.is_nonneg n); omega.
Qed.

Lemma fac_in_range: 
  forall i, 0 <= i <= 12 ->Int.min_signed <= fac i <= Int.max_signed.
Proof.
intros.
split.
pose proof (fac_mono 0 i).
spec H0; [omega|].
change (fac 0) with 1 in H0.
rep_omega.
pose proof (fac_mono i 12).
spec H0; [omega |].
apply Z.le_trans with (fac 12); auto.
compute; congruence.
Qed.

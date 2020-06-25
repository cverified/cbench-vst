From Flocq Require Core Binary.
From Coquelicot Require Import Coquelicot.
Require Import Reals Gappa.Gappa_library Psatz.
Import Defs Raux FLT Generic_fmt Gappa_definitions Binary Ulp.
Require Import FunInd Recdef.
Require Import float_lemmas.

From compcert.lib Require Import Floats Integers.

Transparent Float32.div Float32.add Float32.cmp.

(* Correctness of floating-point absolute value.  We don't need this
   for sqrt, but it's useful elsewhere. *)
Lemma fabs_float32_lemma:
  forall x: float32,
  Float32.of_bits (Int.and (Float32.to_bits x) (Int.repr 2147483647)) =
  Float32.abs x.
Proof.
Admitted.

Definition sqrt_approx_f (x: float32) : float32 :=
  Float32.of_bits
  (Int.add (Int.shru (Float32.to_bits x) (Int.repr 1))
     (Int.repr 532676608)).

Definition float32_to_real := Binary.B2R 24 128.


Lemma bits_of_b32_range:
  forall x, 0 <= Bits.bits_of_b32 x < 2^32.
Proof.
intros.
apply (Bits.bits_of_binary_float_range); reflexivity.
Qed.

Lemma bits_of_b32_range':
  forall x, 0 <= Bits.bits_of_b32 x <= Int.max_unsigned.
Proof.
intros.
pose proof (bits_of_b32_range x).
change Int.max_unsigned with (2^32-1).
lia.
Qed.

Lemma add_repr: forall i j, Int.add (Int.repr i) (Int.repr j) = Int.repr (i+j).
Proof. intros.
  rewrite Int.add_unsigned.
 apply Int.eqm_samerepr.
 unfold Int.eqm.
 apply Int.eqm_add; apply Int.eqm_sym; apply Int.eqm_unsigned_repr.
Qed.

Lemma sqrt_approx_eq:
 forall x, sqrt_approx_f x = 
       Bits.b32_of_bits (Bits.bits_of_b32 x / 2 + 532676608).
Proof.
intros.
unfold sqrt_approx_f.
Transparent Float32.of_bits.
Transparent Float32.to_bits.
unfold Float32.of_bits, Float32.to_bits.
Opaque Float32.of_bits.
Opaque Float32.to_bits.
unfold Int.shru.
rewrite Int.unsigned_repr by apply bits_of_b32_range'.
rewrite Int.unsigned_repr by (compute; split; congruence).
rewrite add_repr.
rewrite <- Z.div2_spec, Z.div2_div.
assert  (0 <= Bits.bits_of_b32 x / 2 < 2 ^ 31)%Z.
 apply Coqlib.Zdiv_interval_1.
 compute; congruence. reflexivity. reflexivity.
 apply bits_of_b32_range.
rewrite Int.unsigned_repr
  by (change Int.max_unsigned with (2^31 + 2^31 -1)%Z; lia).
auto.
Qed.

Lemma bound_mantissa_Z : 
  forall (m: positive) (e: Z), bounded ms es m e = true ->
     (Z.pos m < 2 ^ ms)%Z.
Proof.
intros.
apply bound_mantissa_nat in H.
apply inj_lt in H.
rewrite positive_nat_Z in H.
change 2%nat with (Z.to_nat 2) in H.
rewrite <- Zto_nat_pow in H by (compute; congruence).
rewrite Z2Nat.id in H; auto.
apply Z.pow_nonneg.
compute; congruence.
Qed.

Lemma sqrt_approx_correct:
 forall x, 
  is_finite_strict ms es x = true ->
  Bsign ms es x = false ->
  (Rbasic_fun.Rabs (float32_to_real (sqrt_approx_f x) - R_sqrt.sqrt (float32_to_real x)) <=
       (1 + 1/16) * R_sqrt.sqrt (float32_to_real x))%R.
Proof.
intros.
rewrite sqrt_approx_eq.
unfold float32_to_real.
fold ms. fold es.
match goal with |- context [_ / 2 + ?zz] => 
     change zz with (2^(ms'-1) * (es-1))
end.
unfold Bits.b32_of_bits, Bits.bits_of_b32.
unfold Bits.binary_float_of_bits.
change 23 with ms'.
match goal with |- context [Bits.bits_of_binary_float _ ?y] =>
  change y with (Z.log2 es + 1)
end.
rewrite B2R_FF2B.
unfold Bits.bits_of_binary_float.
set (ebits := Z.log2 es).
destruct x; inversion H; clear H.
rename e0 into H1.
destruct s; inversion H0; clear H0.
set (x := (B754_finite _ _ _ _ _ _)).
destruct (Z.leb_spec 0 (Z.pos m - 2 ^ ms')).
{
set (e' := (e - (3 - 2 ^ (ebits + 1 - 1) - (ms' + 1)) + 1)).
unfold Bits.join_bits.
rewrite Z.shiftl_mul_pow2 by (compute; congruence).
change (2^ms') with (2^(ms'-1)*2) at 1.
rewrite Z.mul_assoc.
rewrite Z.div_add_l by lia.
rewrite (Z.add_comm (_ * _ ^ _)).
rewrite <- Z.add_assoc.
rewrite (Z.mul_comm (_ ^ _)).
rewrite <- Z.mul_add_distr_r.
rewrite Z.add_0_l.
subst e'.
rewrite <- Z.sub_sub_distr.
rewrite <- Z.sub_sub_distr.
rewrite <- (Z.add_opp_r e).
rewrite (Z.add_simpl_r ebits 1).
replace (- (3 - 2 ^ ebits - (ms' + 1) - 1 - (es - 1)))
  with ( 2 ^ ebits + ms' + (es - 2))
  by lia.
rewrite <- Z.div_add by lia.
rewrite <- Z.mul_assoc.
rewrite <- Z.sub_sub_distr.
rewrite <- (Z.mul_1_l (_ ^ _)) at 1.
rewrite <- Z.mul_sub_distr_r.
replace (1 - (e + (2 ^ ebits + ms' + (es - 2))))
     with (-(e+(2^ebits + ms' + es - 3))) by lia.
rewrite Z.mul_opp_l, Z.sub_opp_r.
rewrite Z.mul_assoc.
rewrite Z.div_add by lia.
admit.
}
{
admit.
}
Admitted.







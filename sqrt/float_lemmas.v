From Flocq Require Core Binary.
Import Defs Raux FLT Generic_fmt Binary Ulp.
Require Import Psatz.
Require Import Recdef.

Require Export compcert.lib.Floats.
Definition binop_nan := Float32.binop_nan.

Definition float32_of_Z : Z -> float32 := 
     IEEE754_extra.BofZ 24 128 eq_refl eq_refl.

Definition float_to_nat (z: float32) : nat :=
  match z with
   | B754_zero _ => 2 ^ Z.to_nat 280
   | B754_infinity sign => if sign then 0 else 2 ^ Z.to_nat 600
   | B754_nan _ _ _ => O
   | B754_finite sign m e _ =>
     if sign then
        2 ^ Z.to_nat 280
        - Pos.to_nat m * 2 ^ Z.to_nat(e + 149)
     else
        2 ^ Z.to_nat 280
        + Pos.to_nat m * 2 ^ Z.to_nat(e + 149)
  end.

Lemma pow2_pos x : (0 < 2 ^ x)%nat.
Proof.  induction x as [ | x IH]; try (simpl; lia).  Qed.

Open Scope Z_scope.

Lemma bounded_bound_exp m e : 
  Binary.bounded 24 128 m e = true -> -149 <= e <= 104.
Proof.
intros vc; unfold Binary.bounded in vc.
destruct (andb_prop _ _ vc) as [vc1 vc2].
apply (canonical_canonical_mantissa _ _ false) in vc1.
apply Zle_bool_imp_le in vc2.
split;[simpl in vc1 |- *; clear vc vc2 | exact vc2].
revert vc1.
unfold canonical, F2R, cexp; simpl; unfold FLT_exp.
destruct (mag radix2 (IZR (Z.pos m) * bpow radix2 e) - 24);
  intros v; rewrite v; apply Z.le_max_r.  
Qed.

Lemma Zto_nat_pow x y : 0 <= x -> 0 <= y -> (Z.to_nat (x ^ y)) = 
         (Z.to_nat x ^ Z.to_nat y)%nat.
Proof.
intros x0 y0.
pattern y; apply Zlt_0_ind;[clear y y0| exact y0].
intros y IH y0.
apply Zle_lt_or_eq in y0; destruct y0 as [ygt0 | yeq0].
  assert (0 <= (y - 1)) by lia.
  assert (y1 : y = y - 1 + 1) by ring.
  rewrite y1, Z.pow_add_r, Z.pow_1_r, Z2Nat.inj_mul; try lia.
    rewrite Z2Nat.inj_add; try lia.  
    rewrite Nat.pow_add_r.
    rewrite IH; try lia.
  replace (Z.to_nat 1) with 1%nat by reflexivity.
  rewrite Nat.pow_1_r; reflexivity.
now apply Z.pow_nonneg.
rewrite <- yeq0; reflexivity.
Qed.

Lemma bound_mantissa_digits m k :
  Z.pos (Digits.digits2_pos m) <= k ->
  (Pos.to_nat m < 2 ^ Z.to_nat k)%nat.
Proof.
intros nd.
assert (0 <= k).
  apply Z.le_trans with (2 := nd); lia.
rewrite Digits.Zpos_digits2_pos in nd.
replace (Pos.to_nat m) with (Z.to_nat (Z.pos m)) by reflexivity; try lia.
replace (2 ^ Z.to_nat k)%nat with (Z.to_nat (2 ^ k)) by ( apply Zto_nat_pow; lia).
  rewrite <- Z2Nat.inj_lt; try lia.
  apply (Digits.Zpower_gt_Zdigits radix2 k (Z.pos m)).
  lia.
now apply Z.pow_nonneg.
Qed.

Lemma lower_bound_mantissa_digits m :
  (2 ^ (Pos.to_nat (Digits.digits2_pos m) - 1) <= Pos.to_nat m)%nat.
Proof.
replace (Pos.to_nat m) with (Z.to_nat (Z.pos m)) by reflexivity.
replace (Pos.to_nat (Digits.digits2_pos m)) with
  (Z.to_nat (Z.pos (Digits.digits2_pos m))) by reflexivity.
replace 1%nat with (Z.to_nat 1) at 2 by reflexivity.
rewrite <- Z2Nat.inj_sub;[ | lia].
replace (2 ^ Z.to_nat (Z.pos (Digits.digits2_pos m) - 1))%nat with
  (Z.to_nat (2 ^ (Z.pos (Digits.digits2_pos m) - 1)))
   by ( apply Zto_nat_pow; lia).
rewrite <- Z2Nat.inj_le;[ | apply Z.lt_le_incl, Z.pow_pos_nonneg; lia | lia].
rewrite Digits.Zpos_digits2_pos.
rewrite <- (Z.abs_eq (Z.pos m)) at 2;[ | lia].
apply (Digits.Zpower_le_Zdigits radix2); lia.
Qed.

Lemma bound_mantissa_nat m e :
  Binary.bounded 24 128 m e = true ->
  (Pos.to_nat m < 2 ^ 24)%nat.
Proof.
intros v.
apply (bound_mantissa_digits m 24); try lia.
unfold Binary.bounded in v.
unfold canonical_mantissa in v.
apply andb_prop in v; destruct v as [v _].
apply Zeq_bool_eq in v; unfold FLT_exp in v.
destruct (Z_le_gt_dec (3 - 128 - 24) (Z.pos (Digits.digits2_pos m) + e - 24))
      as [l | r].
  rewrite Z.max_l in v; [lia | assumption].
lia.
Qed.

Lemma lower_bound_mantissa_nat e m :
  -149 < e ->
  Binary.bounded 24 128 m e = true ->
  (2 ^ 23 <= Pos.to_nat m)%nat.
Proof.
intros elb v.
apply le_trans with (2 := lower_bound_mantissa_digits m).
unfold Binary.bounded in v.
unfold canonical_mantissa in v.
apply andb_prop in v; destruct v as [v _].
apply Zeq_bool_eq in v; unfold FLT_exp in v.
destruct (Z_le_gt_dec (3 - 128 - 24) (Z.pos (Digits.digits2_pos m) + e - 24))
      as [l | r].
  rewrite Z.max_l in v; [ | assumption].
  assert (vd : Z.pos (Digits.digits2_pos m) = 24) by lia.
  injection vd; intros vd'; rewrite vd'.
  now apply Nat.pow_le_mono_r.
lia.
Qed.

Lemma bound_float : forall x e, Binary.bounded 24 128 x e = true ->
              (Pos.to_nat x * 2 ^ Z.to_nat (e + 149) < 2 ^ Z.to_nat 280)%nat.
Proof.
intros x e v.
apply lt_trans with (2 ^ 24 * 2 ^ Z.to_nat (e + 149))%nat.
apply Nat.mul_lt_mono_pos_r.
    now apply pow2_pos.
  now apply (bound_mantissa_nat x e).
rewrite <- Nat.pow_add_r.
apply Nat.pow_lt_mono_r; try lia.
assert (tmp := bounded_bound_exp _ _ v); lia.
Qed.

Lemma float_to_nat_lt a b :
  Float32.cmp Integers.Clt a b = true ->
    (float_to_nat a < float_to_nat b)%nat.
Proof.
intros.
assert (Bcompare 24 128 a b = Some Lt). {
Transparent Float32.cmp.
unfold Float32.cmp in H.
Opaque Float32.cmp.
unfold cmp_of_comparison in H.
unfold Float32.compare in H.
 destruct (Bcompare 24 128 a b) as [ [ | | ] | ]; auto; discriminate.
} clear H. rename H0 into H. revert a b H.
destruct a as [da | da | da1 da2 da3 | signa ma ea vca];
  destruct b as [db | db | db1 db2 db3 | signb mb eb vcb]; try
  discriminate.
- unfold Bcompare, float_to_nat.
  case db;[discriminate | intros _; apply Nat.pow_lt_mono_r; lia].
- unfold Bcompare, float_to_nat.
  case signb;[ discriminate | intros].
  apply Nat.le_lt_trans with (2 ^ Z.to_nat 280 + 0)%nat.
    now rewrite Nat.add_0_r; apply le_n.
  apply Nat.add_lt_mono_l, Nat.mul_pos_pos.
    now apply Pos2Nat.is_pos.  
   now apply pow2_pos.
- unfold Bcompare, float_to_nat.
  case da; [now intros; apply pow2_pos | discriminate ].
- unfold Bcompare, float_to_nat.
  now case da; case db; try discriminate; intros; apply pow2_pos.
- unfold Bcompare, float_to_nat.
  case da;[intros | discriminate].
  case signb.
    apply lt_minus_O_lt.
    now apply bound_float.
  apply Nat.add_pos_r.
  apply Nat.mul_pos; split;[lia | apply pow2_pos].
- unfold Bcompare, float_to_nat.
  case signa;[ intros | discriminate].
  assert (tech : forall a b, (0 < a -> 0 < b -> a - b < a)%nat).
    intros a b a0 b0; destruct a as [ | a]; destruct b as [ | b]; lia.
  apply tech;[| apply Nat.mul_pos; split;[lia |]]; apply pow2_pos.
- unfold Bcompare, float_to_nat.
  case db;[discriminate | intros _].
  case signa.
    apply lt_trans with (2 ^ Z.to_nat 280)%nat.
  assert (tech : forall a b, (0 < a -> 0 < b -> a - b < a)%nat).
    intros a b a0 b0; destruct a as [ | a]; destruct b as [ | b]; lia.
  apply tech;[| apply Nat.mul_pos; split;[lia |]]; apply pow2_pos.
  apply Nat.pow_lt_mono_r; lia.  
  apply lt_trans with (2 ^ Z.to_nat 280 + 2 ^ Z.to_nat 280)%nat.
    apply Nat.add_lt_mono_l.
    now apply bound_float.
  assert (tech : forall x, (x + x = 2 ^ 1 * x)%nat) by (intros; simpl; ring).
  rewrite tech, <- Nat.pow_add_r; apply Nat.pow_lt_mono_r; lia.
- unfold Bcompare, float_to_nat.
  case signa; case signb; try discriminate.
  * assert (tech : (forall a b c, b <= a -> c <= a -> c < b -> a - b < a - c)%nat).
      intros a b c ba ca cb; lia.
    destruct (ea ?= eb) eqn:eaeb; try discriminate.
     destruct (CompOpp (Pos.compare_cont Eq ma mb)) eqn:mamb; try discriminate.
     destruct (Pos.compare_cont Eq ma mb) eqn: mamb'; try discriminate.
     apply nat_of_P_gt_Gt_compare_morphism in mamb'.
     intros _; apply tech.
         now apply Nat.lt_le_incl, bound_float.
       now apply Nat.lt_le_incl, bound_float.
     rewrite (Z.compare_eq _ _ eaeb).
     rewrite <- Nat.mul_lt_mono_pos_r;[lia | apply pow2_pos].
    intros _; apply tech.
        now apply Nat.lt_le_incl, bound_float.
      now apply Nat.lt_le_incl, bound_float.
    rewrite Z.compare_gt_iff in eaeb.
    replace ea with (ea - eb + eb) by ring.
    assert (ebb := bounded_bound_exp _ _ vcb).
    rewrite <- Z.add_assoc, (Z2Nat.inj_add (ea - eb)), Nat.pow_add_r; try lia.
    rewrite Nat.mul_assoc; apply Nat.mul_lt_mono_pos_r; try apply pow2_pos.
    apply Nat.lt_le_trans with (1 := bound_mantissa_nat _ _ vcb).
    apply Nat.le_trans with ((2 ^ 23) * 2 ^ Z.to_nat (ea - eb))%nat; cycle 1.
      apply Nat.mul_le_mono_pos_r;[now apply pow2_pos | ].
      apply (lower_bound_mantissa_nat ea);[lia | assumption].
    replace (ea - eb) with (1 + (ea - eb -1)) by ring.
    rewrite Nat.pow_succ_r', Nat.mul_comm.
    apply Nat.mul_le_mono_l; rewrite Z2Nat.inj_add;[ | lia | lia].
    rewrite Nat.pow_add_r.
    replace 2%nat with (2 * 1)%nat at 1 by ring.
    now apply Nat.mul_le_mono_l, pow2_pos.
  * intros _.
    apply bound_float in vca; apply bound_float in vcb.
    enough (0 < Pos.to_nat mb * 2 ^ Z.to_nat (eb + 149) /\
            0 < Pos.to_nat ma * 2 ^ Z.to_nat (ea + 149))%nat by lia.
    split; apply Nat.mul_pos_pos; try apply pow2_pos; lia.
  * destruct (ea ?= eb) eqn:eaeb; try discriminate.
     destruct (Pos.compare_cont Eq ma mb) eqn:mamb; try discriminate.
     apply nat_of_P_lt_Lt_compare_morphism in mamb.
     intros _; apply Nat.add_lt_mono_l.
     rewrite (Z.compare_eq _ _ eaeb).
     rewrite <- Nat.mul_lt_mono_pos_r;[lia | apply pow2_pos].
    intros _; apply Nat.add_lt_mono_l.
    rewrite Z.compare_lt_iff in eaeb.
    replace eb with (eb - ea + ea) by ring.
    assert (eba := bounded_bound_exp _ _ vca).
    rewrite <- Z.add_assoc, (Z2Nat.inj_add (eb - ea)), Nat.pow_add_r; try lia.
    rewrite Nat.mul_assoc; apply Nat.mul_lt_mono_pos_r; try apply pow2_pos.
    apply Nat.lt_le_trans with (1 := bound_mantissa_nat _ _ vca).
    apply Nat.le_trans with ((2 ^ 23) * 2 ^ Z.to_nat (eb - ea))%nat; cycle 1.
      apply Nat.mul_le_mono_pos_r;[now apply pow2_pos | ].
      apply (lower_bound_mantissa_nat eb);[lia | assumption].
    replace (eb - ea) with (1 + (eb - ea -1)) by ring.
    rewrite Nat.pow_succ_r', Nat.mul_comm.
    apply Nat.mul_le_mono_l; rewrite Z2Nat.inj_add;[ | lia | lia].
    rewrite Nat.pow_add_r.
    replace 2%nat with (2 * 1)%nat at 1 by ring.
    now apply Nat.mul_le_mono_l, pow2_pos.
Qed.

From Flocq Require Core Binary.
Require Import Reals Gappa.Gappa_library Psatz.
Import Defs Raux FLT Generic_fmt Gappa_definitions Binary Ulp.
Require Import FunInd Recdef.
(* This file is generated from sqrt1.g *)
Require from_g.

Definition float32 := binary_float 24 128.

Definition round' x := 
   round radix2 (FLT_exp (-149) 24) (round_mode mode_NE) x.

Notation f32_exp := (FLT_exp (-149) 24).

Notation r2 := Gappa_definitions.radix2.

Open Scope R_scope.

Lemma from_g_proof (x y : R) :
  1 <= x <= 4 ->
  sqrt x - 16 * bpow r2 (-23) <= y <= sqrt x + 3 ->
  - 9 * bpow r2 (-24) <= round' (round'(y + round' (x / y)) / 2) -
   (y + (x / y)) / 2 <=
  9 * bpow r2 (-24).
Proof.
intros intx inty.
set (b := sqrt x).
assert (1 <= b <= 2).
  rewrite <- sqrt_1.
  replace 2 with (sqrt(2 ^ 2)) by (rewrite sqrt_pow2; try lra).
  split; apply sqrt_le_1_alt; lra.
set (e := (y - sqrt x)).
rewrite <- (sqrt_sqrt x) by lra.
replace y with (b + e) by (unfold b, e; ring).
fold b.
assert (-16 * bpow r2 (-23) <= e <= 3) by (unfold e; lra).
generalize (from_g.l1 b e).
unfold from_g.s1, from_g.s2, from_g.s3, from_g.i1, from_g.i2, from_g.i3, BND.
cbv [lower upper].
change rndNE with (round_mode mode_NE).
replace (float2R from_g.f1) with 1 by (compute; lra).
replace (float2R from_g.f2) with 2 by (compute; lra).
replace (float2R from_g.f3) with (-16 * bpow r2 (-23)) by (compute; lra).
replace (float2R from_g.f4) with 3 by (compute; lra).
replace (float2R from_g.f5) with (-9 * bpow r2 (-24)) by (compute; lra).
replace (float2R from_g.f6) with (9 * bpow r2 (-24)) by (compute; lra).
change (Float1 2) with 2.
change (round r2 f32_exp (round_mode mode_NE)
     (round r2 f32_exp (round_mode mode_NE)
        (b + e + round r2 f32_exp (round_mode mode_NE) (b * b / (b + e))) /
      2)) with
 (round' (round' ((b + e) + round' (b * b / (b + e))) / 2)).
lra.
Qed.

Definition B2R' x := B2R 24 128 x.

Open Scope Z_scope.

Set Asymmetric Patterns.

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

Definition float_to_exp (z : float32) : Z :=
  match z with
  | B754_finite _ m e _ => e
  | _ => 0
  end.

Lemma Rabs_INR (n : nat) : Rabs(INR n) = INR n.
Proof.
apply Rabs_pos_eq, pos_INR.
Qed.

Lemma natpow_Zpow (x y : nat) : Z.of_nat (x ^ y) =
  Z.of_nat x ^ Z.of_nat y.
Proof.
induction y as [ | y IH].
  reflexivity.
rewrite <- Zpower_nat_Z.
simpl.
now rewrite Nat2Z.inj_mul, IH, <- Zpower_nat_Z.
Qed.

Lemma IZR_INR_Z2N n :
  0 <= n -> IZR n = INR (Z.to_nat n).
Proof.
destruct n as [ | p | p]; auto; try lia.
now unfold Z.to_nat, IZR; rewrite INR_IPR.
Qed.

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

Lemma bound_exp_float32 (z : float32) :
  -149 <= float_to_exp z <= 104.
Proof.
destruct z as [dummy | dummy | dum1 dum2 dum3 | sign m e vc];
  try (split; intros; discriminate).
now simpl; apply (bounded_bound_exp m).
Qed.

Lemma pow2_pos x : (0 < 2 ^ x)%nat.
Proof.  induction x as [ | x IH]; try (simpl; lia).  Qed.

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


Lemma float_to_nat_Clt a b :
  Bcompare 24 128 a b = Some Lt ->
    (float_to_nat a < float_to_nat b)%nat.
Proof.
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

Lemma Float32cmp_correct x y :
  is_finite 24 128 x = true ->
  is_finite 24 128 y = true ->
  Bcompare 24 128 x y = Some Lt ->
  (B2R' x < B2R' y)%R.
Proof.
intros finx finy.
rewrite Bcompare_correct; auto.
fold (B2R' x) (B2R' y).
destruct (Rcompare (B2R' x) (B2R' y)) eqn:test;
 simpl; try discriminate.
now apply Rcompare_Lt_inv in test.
Qed.

Definition main_loop_measure (p : float32 * float32) : nat :=
  float_to_nat (snd p).

Definition float2 := B754_finite 24 128 false (2 ^ 23) (-22) eq_refl.

Definition float1 := B754_finite 24 128 false (2 ^ 23) (-23) eq_refl.

Lemma float2_val : B2R 24 128 float2 = 2%R.
Proof.  compute; lra. Qed.

Lemma float1_val : B2R 24 128 float1 = 1%R.
Proof.  compute; lra. Qed.


Definition dummy_nan (x y : float32) :=
  exist (fun e => is_nan _ _ e = true) (B754_nan 24 128 false 1 eq_refl)
        eq_refl.

Definition float_add (x y : float32) : float32 :=
  Bplus 24 128 eq_refl eq_refl dummy_nan mode_NE x y.

Definition float_div (x y : float32) :=
  Bdiv 24 128 eq_refl eq_refl dummy_nan mode_NE x y.

Definition body_exp (x y : float32) :=
  float_div (float_add y (float_div x y)) float2.

(* The beauty of it is that we don't need to know what computation is performed,
  only the test matters. *)
Function main_loop (p : float32 * float32) {measure main_loop_measure} :
   float32 :=
  match p with
  | (x, y) =>
    match Bcompare 24 128 (body_exp x y) y with
    | Some Lt => main_loop (x, body_exp x y)
    | _ => body_exp x y
    end
  end.
Proof.
now intros p x y eqxy c cq; apply float_to_nat_Clt.
Qed.

Open Scope R_scope.

Definition ulp1 := bpow radix2 (-23).

Lemma pure_decrease_16 (x y : R) :
  1 <= x <= 4 -> sqrt x + 16 * ulp1 <= y <= x ->
  sqrt x <= (y + x / y) / 2 < y - 8 * ulp1.
Proof.
intros intx inty.
assert (1 <= sqrt x).
  now rewrite <- sqrt_1; apply sqrt_le_1_alt.
assert (0 < ulp1) by (unfold ulp1; simpl; lra).
rewrite <- (sqrt_sqrt x) at 2 3 by lra.
replace ((y + (sqrt x * sqrt x) / y) / 2) with
   (sqrt x + (y - sqrt x) / 2 * ((y - sqrt x)/ y)) by (field; lra).
split.
  enough (0 <= (y - sqrt x) / 2 * ((y - sqrt x) / y)) by lra.
  apply Rmult_le_pos;[lra | apply Rmult_le_pos;[lra | ] ].
  apply Rlt_le, Rinv_0_lt_compat; lra.
apply Rlt_le_trans with (sqrt x + ((y - sqrt x) / 2) * 1);[ | lra].
apply Rplus_lt_compat_l, Rmult_lt_compat_l; try lra.
apply Rmult_lt_reg_r with y;[lra |unfold Rdiv; rewrite Rmult_assoc, Rinv_l ].
  lra.   
lra.
Qed.

Lemma decrease_above_16 (x y : R) :
  1 <= x <= 4 -> sqrt x + 16 * ulp1 <= y <= x ->
  sqrt x - 16 * ulp1 <= round' (round' (y + round' (x / y)) / 2) < y.
Proof.
intros intx inty.
assert (0 < ulp1 < / 1024) by (unfold ulp1; simpl; lra).
assert (tmp := from_g_proof x y intx).
assert (1 <= sqrt x).
  now rewrite <- sqrt_1; apply sqrt_le_1_alt.
assert (sqrt x - 16 * bpow r2 (-23) <= y <= sqrt x + 3) by (fold ulp1; lra).
split.
  apply Rle_trans with ((y + x / y) / 2 - 9 * bpow r2 (-24));[ | lra].
  assert (tmp2 := pure_decrease_16 _ _ intx inty).
  enough (9 * bpow r2 (-24) < 16 * ulp1);[ | compute]; lra.
apply Rle_lt_trans with ((y + x / y) / 2 + 9 * bpow r2 (-24));[lra | ].
clear tmp.
assert (tmp2 := pure_decrease_16 _ _ intx inty).
assert (step : (y + x / y) / 2 + 8 * ulp1 < y) by lra.
apply Rlt_trans with (2 := step).
apply Rplus_lt_compat_l.
unfold ulp1; simpl; lra.
Qed.

Lemma converge_below_16 (x y : R) :
  1 <= x <= 4 -> sqrt x - 16 * ulp1 <= y <= sqrt x + 16 * ulp1 ->
  -5 * ulp1 <= round' (round' (y + round' (x / y)) / 2) - sqrt x <= 5 * ulp1.
Proof.
intros intx inty.
assert (1 <= sqrt x).
  now rewrite <- sqrt_1; apply sqrt_le_1_alt.
assert (0 < ulp1 < / 1024) by (unfold ulp1; simpl; lra).
assert (bigy : sqrt x - 16 * bpow r2 (-23) <= y <= sqrt x + 3).
  fold ulp1; lra.
assert (tmp := from_g_proof x y intx bigy).
assert (ulp1 = 2 * bpow r2 (-24)) by (unfold ulp1; simpl; lra).
enough (-bpow r2 (-24) <= (y + (x / y)) / 2 - sqrt x <= bpow r2 (-24)) by lra.
rewrite <- (sqrt_sqrt x) at 1 3 by lra.
replace ((y + (sqrt x * sqrt x) / y) / 2 - sqrt x) with
   ((y - sqrt x) ^ 2 / (2 * y)) by (field; lra).
apply Rabs_le_inv; rewrite Rabs_pos_eq; cycle 1.
  apply Rmult_le_pos;[apply pow2_ge_0 | apply Rlt_le, Rinv_0_lt_compat]; lra.
apply Rle_trans with ((y - sqrt x) ^ 2 / 1).
apply Rmult_le_compat_l;[apply pow2_ge_0 | apply Rinv_le_contravar;lra].
unfold Rdiv; rewrite Rinv_1, Rmult_1_r.
replace (bpow r2 (-24)) with (bpow r2 (-12) ^ 2) by (compute; lra).
assert (ulp1 = bpow r2 (-23)) by reflexivity.
destruct (Rle_dec y (sqrt x)).
  replace ((y - sqrt x) ^ 2) with ((sqrt x - y) ^ 2) by ring.
  apply pow_incr; split;[lra | ].
  apply Rle_trans with (16 * bpow r2 (-23));[ |compute]; lra.
apply pow_incr; split;[lra | ].
apply Rle_trans with (16 * bpow r2 (-23));[ | compute]; lra.
Qed.

Section From_floating_point_numbers_to_reals.

Lemma round1 m: round radix2 f32_exp (round_mode m) 1 = 1%R.
Proof.
assert (for1 : generic_format radix2 f32_exp 1).
  replace 1%R with (F2R (Float radix2 (cond_Zopp false (2 ^ 23)) (-23))).
    now apply generic_format_canonical, (canonical_canonical_mantissa 24 128).
  compute; lra.
now apply round_generic; auto; apply valid_rnd_round_mode.
Qed.

Lemma round'1 : round' 1 = 1%R.
Proof. now apply round1. Qed.

Lemma round'2 : round' 2 = 2%R.
Proof.
assert (for2 : generic_format radix2 (FLT_exp (3 - 128 - 24) 24) 2).
  replace 2%R with (F2R (Float radix2 (cond_Zopp false (2 ^ 23)) (-22))).
    now apply generic_format_canonical, canonical_canonical_mantissa.
  compute; lra.
now apply round_generic; auto; apply valid_rnd_round_mode.
Qed.

Lemma round'h : round' (/2) = (/2)%R.
Proof.
assert (for2 : generic_format radix2 (FLT_exp (3 - 128 - 24) 24) (/2)).
  replace (/2)%R with (F2R (Float radix2 (cond_Zopp false (2 ^ 23)) (-24))).
    now apply generic_format_canonical, canonical_canonical_mantissa.
  compute; lra.
now apply round_generic; auto; apply valid_rnd_round_mode.
Qed.

Lemma round'q : round' (/4) = (/4)%R.
Proof.
assert (for4 : generic_format radix2 (FLT_exp (3 - 128 - 24) 24) (/4)).
  replace (/4)%R with (F2R (Float radix2 (cond_Zopp false (2 ^ 23)) (-25))).
    now apply generic_format_canonical, canonical_canonical_mantissa.
  compute; lra.
now apply round_generic; auto; apply valid_rnd_round_mode.
Qed.


Lemma round'4 : round' 4 = 4%R.
Proof.
assert (for2 : generic_format radix2 (FLT_exp (3 - 128 - 24) 24) 4).
  replace 4%R with (F2R (Float radix2 (cond_Zopp false (2 ^ 23)) (-21))).
    now apply generic_format_canonical, canonical_canonical_mantissa.
  compute; lra.
now apply round_generic; auto; apply valid_rnd_round_mode.
Qed.

Lemma round'65 : round' (bpow r2 65) = bpow r2 65.
Proof.
assert (for2 : generic_format radix2 (FLT_exp (3 - 128 - 24) 24) (bpow r2 65)).
  replace (bpow r2 65) with
         (F2R (Float radix2 (cond_Zopp false (2 ^ 23)) 42)).
    now apply generic_format_canonical, canonical_canonical_mantissa.
  compute; lra.
now apply round_generic; auto; apply valid_rnd_round_mode.
Qed.

Lemma round_le' (x y : R) : (x <= y)%R -> (round' x <= round' y)%R.
Proof.
intros xley.
apply round_le; auto.
  now apply (fexp_correct 24 128).
now apply valid_rnd_round_mode.
Qed.

Definition f32max : float32 :=
    B754_finite 24 128 false (2 ^ 24 - 1) 104 eq_refl.

Lemma f32max_val : B2R 24 128 f32max = 
  ((bpow radix2 24 - 1) * bpow radix2 104)%R.
unfold B2R, f32max, Fnum, F2R; simpl.
simpl Defs.Fexp.
rewrite Pos2Z.inj_sub by reflexivity.
rewrite Pos2Z.inj_pow.
rewrite !Z.pow_pos_fold.
rewrite minus_IZR.
reflexivity.
Qed.

(* a conservative bound that can be improved. *)
Definition predf32max : float32 :=
    B754_finite 24 128 false (2 ^ 23) 103 eq_refl.

Lemma predf32max_val : B2R 24 128 predf32max = 
  ((bpow radix2 23) * bpow radix2 103)%R.
Proof.
unfold B2R, F2R, Fexp; simpl.
rewrite Pos2Z.inj_pow.
now rewrite !Z.pow_pos_fold.
Qed.

Lemma boundf32max : (B2R' f32max < bpow radix2 128)%R.
Proof.
now apply (bounded_lt_emax 24 128).
Qed.

Lemma boundpredf32max : (2 * B2R' predf32max <= B2R' f32max)%R.
Proof.
compute; lra.
Qed.

Definition body_exp_R x y := round' (round' (y + round' (x / y)) / 2).

Lemma round_B2R' x : round' (B2R' x) = B2R' x.
Proof.
assert (tmp := generic_format_FLT radix2 _ 24 _ 
                   (FLT_format_B2R 24 128 eq_refl x)).
now apply round_generic;[ apply valid_rnd_round_mode | exact tmp ].
Qed.

Lemma body_exp_div_x_y_bounds1 x y :
  (/2 <= B2R' x)%R ->
  (/2 <= B2R' y)%R ->
  (0 <= B2R' x / B2R' y <= 2 * B2R' x)%R.
Proof.
set (x' := B2R' x); set (y':= B2R' y).
intros intx inty.
assert (ygt0 : y' <> 0%R) by lra.
split.
  apply Rmult_le_reg_r with y';[lra | ].
  now unfold Rdiv; rewrite Rmult_assoc, Rinv_l; lra.
apply Rmult_le_reg_r with y';[lra | ].
unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r; [ nra | lra].
Qed.

Lemma body_exp_div_x_y_bounds x y :
  (/2 <= B2R' x)%R ->
  (/2 <= B2R' y)%R ->
  (0 <= round' (B2R' x / B2R' y)
     <= round' (2 * B2R' x))%R.
Proof.
set (x' := B2R' x); set (y':= B2R' y).
intros intx inty.
assert (ygt0 : y' <> 0%R) by lra.
assert (divint : (0 <= x' / y' <= 2 * x')%R).
  now apply body_exp_div_x_y_bounds1.
split.
  rewrite <- (round_0 radix2 f32_exp (round_mode mode_NE)).
  now apply round_le'; tauto.
apply round_le'; tauto.
Qed.

(* The upper constraint on x is too strict, but good enough for now. *)
Lemma body_exp_sum_bounds x y :
  (/2 <= B2R' x <  /2 * B2R' predf32max)%R ->
  (/2 <= B2R' y < B2R' predf32max)%R ->
  (/2 <= round' (B2R' y +
          round' (B2R' x / B2R' y))
     <= B2R' f32max)%R.
Proof.
set (x' := B2R' x); set (y':= B2R' y).
intros intx inty.
assert (int1 : (0 <= round' (x' / y') <= round' (2 * x'))%R).
  now apply body_exp_div_x_y_bounds.
destruct (Rlt_le_dec x' (bpow radix2 64)) as [xlow | xhigh].
  split.
    rewrite <- round'h.
    apply round_le'; lra.
  assert (r2xb : round' (2 * x') <= bpow r2 65).
    rewrite <- round'65.    
    apply round_le'.
    replace (bpow r2 65) with (2 * bpow r2 64);[| compute]; lra.
  apply Rle_trans with (bpow r2 127)%R;[ | compute; lra].
  assert (two127 : (bpow r2 127 =
                  (B2R' (B754_finite 24 128 false (2 ^ 23) 104 eq_refl)))%R).
    compute; lra.
  rewrite two127, <- round_B2R'.
  apply round_le'; rewrite <- two127.
  apply Rle_trans with (B2R' predf32max + bpow r2 65);[ | compute; lra].
  lra.
rewrite <- round'h, <- round_B2R'.
assert (sqrtemax : sqrt (bpow radix2 128) = bpow radix2 64).
  apply sqrt_lem_1; try apply bpow_ge_0.
  now rewrite <- bpow_plus.
destruct (Rlt_le_dec y' (sqrt x')) as [ylow | yhigh].
  assert (y' < bpow radix2 64)%R.
    apply Rlt_trans with (1 := ylow).
    rewrite <-sqrtemax.
    apply sqrt_lt_1_alt.
    split; [ lra | ].
    apply Rlt_trans with (1 := proj2 intx).
    compute; lra.
  split; apply round_le'; try lra.
  apply Rle_trans with (bpow radix2 64 + B2R' predf32max)%R; cycle 1.
    compute; lra.
    apply Rplus_le_compat; [lra | ].
  apply Rle_trans with (1 := proj2 int1).
  rewrite <- round_B2R'; apply round_le'; lra.
split; apply round_le'; try lra.
assert (0 < sqrt x')%R.
  apply sqrt_lt_R0; lra.
assert (divsqrt : (x' / y' <= sqrt x')%R).
  apply Rmult_le_reg_r with y';[lra | ].
    unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r;[ | lra].
    rewrite <- (sqrt_sqrt x') at 1;[ | lra].
    now apply Rmult_le_compat_l;[lra | ].
apply Rle_trans with (B2R' predf32max + bpow radix2 64)%R.
  apply Rplus_le_compat;[lra | ].
  assert (two64 : (bpow radix2 64 =
                  (B2R' (B754_finite 24 128 false (2 ^ 23) 41 eq_refl)))%R).
    compute; lra.
  rewrite two64, <- round_B2R'; apply round_le'; rewrite <- two64.
apply Rle_trans with (1 := divsqrt).
  rewrite <- sqrtemax; apply Rlt_le, sqrt_lt_1_alt; split;[lra | ].
  apply Rlt_trans with (2 := boundf32max).
  assert (tmp := boundpredf32max); lra.
compute; lra.
Qed.

Lemma body_exp_bounds x y :
  (/2 <= B2R' x < /2 * B2R' predf32max)%R ->
  (/2 <= B2R' y < B2R' predf32max)%R ->
  (/4 <= body_exp_R (B2R' x) (B2R' y) <= B2R' f32max)%R.
Proof.
set (x' := B2R' x); set (y':= B2R' y).
intros intx inty.
assert ((/2 <= round' (y' + round' (x' / y')) <= B2R' f32max)%R).
  now apply body_exp_sum_bounds.
unfold body_exp_R.
rewrite <- round'q, <- round_B2R'.
split.
  apply round_le'; lra.
apply round_le'; lra.
Qed.

Lemma body_exp_finite_value x y :
  is_finite 24 128 x = true ->
  is_finite 24 128 y = true ->
  (/2 <= B2R' x < /2 * B2R' predf32max)%R ->
  (/2 <= B2R' y < B2R' predf32max)%R ->
  B2R' (body_exp x y) = round' (round' (B2R' y + round' (B2R' x / B2R' y)) / 2) /\
  is_finite 24 128 (body_exp x y) = true.
Proof.
intros finx finy intx' inty'.
assert (yn0 : B2R' y <> 0%R) by lra.
unfold body_exp, float_div.
assert (tmp := body_exp_bounds x y intx' inty').
assert (tm2 := body_exp_sum_bounds x
                                     y
                    intx' inty').
assert (tm3 := body_exp_div_x_y_bounds x
                                     y
                    (proj1 intx') (proj1 inty')).
unfold body_exp_R in tmp, tm2, tm3.
assert (tm4 := Bdiv_correct 24 128 eq_refl eq_refl dummy_nan mode_NE x y yn0).
assert (divlt : Rabs (round' (B2R' x / B2R' y)) < bpow radix2 128).
  rewrite Rabs_pos_eq;[ | lra].
  assert (tmp5:= conj boundpredf32max boundf32max).
  apply Rle_lt_trans with (B2R' predf32max);[ | lra].
  rewrite <- (round_B2R' predf32max).
  apply Rle_trans with (1 := proj2 tm3); apply round_le'; lra.
rewrite Rlt_bool_true in tm4;[ | exact divlt].
destruct tm4 as [vdivxy [findivxy signdivxy]].
clear divlt.
unfold float_add.
set (divxy := Bdiv 24 128 eq_refl eq_refl dummy_nan mode_NE x y).
fold divxy in signdivxy, findivxy, vdivxy.
fold (B2R' divxy) in vdivxy.
set (divxy' := B2R' divxy); fold divxy' in vdivxy.
assert (findivxy' : is_finite 24 128 divxy = true).
  now rewrite findivxy, finx.
assert (pluslt : Rabs (round' (B2R' y + divxy')) < bpow radix2 128).
  rewrite vdivxy.
  change (3 - 128 -24)%Z with (-149)%Z.
  fold (B2R' x); fold (B2R' y); fold (round' (B2R' x / B2R' y)).
  rewrite Rabs_pos_eq by lra.
  now assert (tmp5:= conj boundpredf32max boundf32max); lra.
assert (tm6 := Bplus_correct 24 128 eq_refl eq_refl dummy_nan mode_NE y
                     divxy finy findivxy').
rewrite Rlt_bool_true in tm6;[ | exact pluslt].
fold (B2R' divxy) in tm6; fold divxy' in tm6; fold (B2R' y) in tm6.
change (3 - 128 -24)%Z with (-149)%Z in tm6.
fold (round' (B2R' y + divxy')) in tm6.
destruct tm6 as [vsum [finsum signsum]].
assert (fin2 : is_finite 24 128 float2 = true) by reflexivity.
assert (b2n0 : B2R' float2 <> 0%R) by now compute; lra.
assert (tm4 := Bdiv_correct 24 128 eq_refl eq_refl dummy_nan mode_NE
                   (Bplus 24 128 eq_refl eq_refl dummy_nan mode_NE y
          (Bdiv 24 128 eq_refl eq_refl dummy_nan mode_NE x y))
                   _ b2n0).
  set (bexp :=   Bdiv 24 128 eq_refl eq_refl dummy_nan mode_NE
              (Bplus 24 128 eq_refl eq_refl dummy_nan mode_NE y
                 (Bdiv 24 128 eq_refl eq_refl dummy_nan mode_NE x y))
              float2).
fold bexp in tm4.
set (sum := (Bplus 24 128 eq_refl eq_refl dummy_nan mode_NE y
                       divxy)).
fold divxy sum in vsum, finsum, signsum, tm4.
assert (explt : Rabs (round' (B2R' sum / B2R' float2)) < bpow radix2 128).
  replace (B2R' float2) with 2%R by (now compute; lra).
   fold (B2R' sum) in vsum; rewrite vsum; rewrite vdivxy.
  change (3 - 128 -24)%Z with (-149)%Z; fold (B2R' x) (B2R' y).
   fold (round' (B2R' x / B2R' y)) divxy'.
  rewrite Rabs_pos_eq;[ | lra].
  now assert (tmp5:= conj boundpredf32max boundf32max); lra.
rewrite Rlt_bool_true in tm4;[ | exact explt].
change (3 - 128 -24)%Z with (-149)%Z in tm4.
destruct tm4 as [vexp [finexp signexp]].
replace (B2R' float2) with 2%R in vexp by now compute; lra.
unfold bexp in vexp; rewrite vsum in vexp.
rewrite vdivxy in vexp.
replace (B2R 24 128 float2) with 2%R in vexp by (compute; lra).
split;[exact vexp | rewrite finsum in finexp;exact finexp].
Qed.

Lemma body_exp_val x y:
  1 <= B2R' x <= 4 -> /2 <= B2R' y <= 5 ->
  B2R' (body_exp x y) =
  round' (round' (B2R' y + round' (B2R' x / B2R' y )) / 2).
Proof.
assert (4 < B2R' predf32max) by (compute; lra).
intros intx inty.
assert (finx : is_finite 24 128 x = true).
  destruct x; auto; compute in intx; lra.
assert (finy : is_finite 24 128 y = true).
  destruct y; auto; compute in inty; lra.
assert (intx' : /2 <= B2R' x < /2 * B2R' predf32max).
  split;[apply Rle_trans with (2 := proj1 intx); lra | ].
  apply Rle_lt_trans with (1 := proj2 intx); compute; lra.
assert (inty' : /2 <= B2R' y < B2R' predf32max).
  split;[apply Rle_trans with (2 := proj1 inty); lra | ].
  apply Rle_lt_trans with (1 := proj2 inty); compute; lra.
assert (tmp := body_exp_finite_value x y finx finy intx' inty').
tauto.
Qed.

Lemma positive_finite x : 0 < B2R' x -> is_finite _ _ x = true.
Proof. destruct x; simpl; auto; lra. Qed.

Section main_loop_reasoning.

Variable x : float32.

Hypothesis intx : 1 <= B2R' x <= 4.

Definition invariant (p : float32 * float32) :=
    fst p = x /\
    (sqrt (B2R' x) - 16 * ulp1 <= B2R' (snd p) <= 
       Rmax (B2R' x) (sqrt (B2R' x) + 5 * ulp1))%R.


Lemma invariant_test x' y :
  invariant (x', y) -> Bcompare _ _ (body_exp x y) y <> Some Lt ->
  ~ (B2R' (body_exp x y) < B2R' y).
Proof.
intros [xx' inty]; simpl in inty; clear x' xx'.
assert (0 < ulp1 < / 1024) by (unfold ulp1; simpl; lra).
assert (1 <= sqrt (B2R' x)).
  now rewrite <- sqrt_1; apply sqrt_le_1_alt.
assert (sqrt (B2R' x) <= 2).
  replace 2 with (sqrt(2 ^ 2)) by (rewrite sqrt_pow2; try lra).
  apply sqrt_le_1_alt; lra.
assert (intx' : / 2 <= B2R' x < / 2 * B2R' predf32max).
  split;[apply Rle_trans with (2 := proj1 intx);lra | ].
  apply Rle_lt_trans with (1 := proj2 intx); compute; lra.
assert (vpmax: B2R' predf32max = 2 ^ 126) by (compute; lra).
assert (vmax: B2R' f32max = (2 ^ 24 - 1) * 2 ^ 104) by (compute; lra).
assert (inty' : / 2 <= B2R' y < B2R' predf32max).
  split;[apply Rle_trans with (2 := proj1 inty); lra | ].
  enough (Rmax (B2R' x) (sqrt (B2R' x) + 5 * ulp1) < B2R' predf32max) by lra.
  destruct (Rle_dec (B2R' x) (sqrt (B2R' x) + 5 * ulp1)).
    rewrite Rmax_right; lra.
  rewrite Rmax_left; lra.
assert (expb := body_exp_bounds x y intx' inty').
rewrite vmax in expb.
assert (finx : is_finite _ _ x = true).
  apply positive_finite; lra.
assert (finy : is_finite _ _ y = true).
  apply positive_finite; lra.
destruct (body_exp_finite_value x y finx finy intx' inty') as [vb finb].
assert (B2R' y < 2 ^ 126).
  replace (2 ^ 126) with (B2R' predf32max) by (compute; lra).
  lra.  
clear -finb finy.
rewrite Bcompare_correct; auto.
destruct (Rcompare _ _) eqn:vcmp.
    apply Rcompare_Eq_inv in vcmp; unfold B2R'; lra.
  now intros abs; case abs.
apply Rcompare_Gt_inv in vcmp; unfold B2R'; lra.
Qed.

Lemma invariant_spec :
  forall x y,  Bcompare _ _ (body_exp x y) y = Some Lt ->
              invariant (x, y) ->
              invariant (x, body_exp x y).
Proof.
intros x' y cmp [cnd1 cnd2]; simpl in cnd1; rewrite cnd1 in cnd2 |- *.
clear cnd1; split;[reflexivity | ].
simpl.
assert (1 <= sqrt (B2R' x)).
  now rewrite <- sqrt_1; apply sqrt_le_1_alt.
assert (sqrt (B2R' x) <= 2).
  replace 2 with (sqrt(2 ^ 2)) by (rewrite sqrt_pow2; try lra).
  apply sqrt_le_1_alt; lra.
assert (0 < ulp1 < / 1024) by (unfold ulp1; simpl; lra).

destruct (Rle_dec (B2R' y) (sqrt (B2R' x) + 16 * ulp1)) as [yl16 | yg16].
  assert (tmp:= converge_below_16 _ (B2R' y) intx (conj (proj1 cnd2) yl16)).
  assert (tmp1 := converge_below_16 _ (B2R' y) intx (conj (proj1 cnd2) yl16)).
  rewrite body_exp_val; simpl in cnd2; try lra.
  split; [lra | ].
  apply Rle_trans with (sqrt (B2R' x) + 5 * ulp1).
    lra.
  apply Rmax_r.
destruct (Rle_dec (B2R' x) (sqrt (B2R' x) + 5 * ulp1)) as [xclose | xfar].
  rewrite Rmax_right in cnd2 by auto; simpl in cnd2.
  assert (yl16 : B2R' y <= sqrt (B2R' x) + 16 * ulp1) by lra.
  assert (tmp1 := converge_below_16 _ (B2R' y) intx (conj (proj1 cnd2) yl16)).
  split; [| rewrite Rmax_right]; lra.
simpl in cnd2; rewrite Rmax_left in cnd2 by lra.
assert (yg16' : sqrt (B2R' x) + 16 * ulp1 <= B2R' y) by lra.
rewrite body_exp_val; simpl in cnd2; try lra.
assert (tmp := decrease_above_16 _ (B2R' y) intx (conj yg16' (proj2 cnd2))).
split;[ | rewrite Rmax_left]; lra.
Qed.

Definition final (v : float32) :=
  sqrt (B2R' x) - 5 * ulp1 <= B2R' v <= sqrt (B2R' x) + 5 * ulp1.

Lemma invariant_initial : invariant (x, x).
Proof.
assert (0 < ulp1 < / 1024) by (unfold ulp1; simpl; lra).
split;[reflexivity | ]; simpl; split.
  apply Rle_trans with (sqrt (B2R' x));[lra | ].
  assert (1 <= sqrt (B2R' x)).
    now rewrite <- sqrt_1; apply sqrt_le_1_alt.
  rewrite <- (Rmult_1_r (sqrt (B2R' x))).
  rewrite <- (sqrt_sqrt (B2R' x)) at 2 by lra.
  apply Rmult_le_compat_l; lra.
now apply Rmax_l.
Qed.

Lemma invariant_final :
  forall x' y, invariant (x', y) ->
     Bcompare 24 128 (body_exp x y) y <> Some Lt ->
     final (body_exp x' y).
Proof.
intros x' y iv test.
assert (0 < ulp1 < / 1024) by (unfold ulp1; simpl; lra).
assert (sqrt (B2R' x) <= 2).
  replace 2 with (sqrt(2 ^ 2)) by (rewrite sqrt_pow2; try lra).
  apply sqrt_le_1_alt; lra.
assert (1 <= sqrt (B2R' x)).
  now rewrite <- sqrt_1; apply sqrt_le_1_alt.
apply (invariant_test _ _ iv) in test.
destruct iv as [cnd1 cnd2]; simpl in cnd1, cnd2; rewrite cnd1; clear x' cnd1.
revert test.
unfold final; rewrite body_exp_val; try lra; cycle 1.
  destruct (Rle_dec (B2R' x) (sqrt (B2R' x) + 5 * ulp1)).
    rewrite Rmax_right in cnd2; lra.
  rewrite Rmax_left in cnd2; lra.
intros test.
destruct (Rle_dec (B2R' y) (sqrt (B2R' x) + 16 * ulp1)) as [yl16 | yg16].
  assert (tmp := converge_below_16 _ _ intx (conj (proj1 cnd2) yl16)); lra.
assert (inty : sqrt (B2R' x) + 16 * ulp1 <= B2R' y <= B2R' x).
  destruct (Rle_dec (B2R' x) (sqrt (B2R' x) + 5 * ulp1)).
    rewrite Rmax_right in cnd2; lra.
  rewrite Rmax_left in cnd2; lra.
assert (tmp := decrease_above_16 _ (B2R' y) intx inty); lra.
Qed.

Lemma main_loop_prop :
  final (main_loop (x, x)).
Proof.
generalize invariant_initial.
apply main_loop_ind.
  now intros p x' y pxy test IH v; apply IH, invariant_spec.
intros p x' y pxy test vtest cndtest iv. 
apply invariant_final; auto.
destruct iv as [cnd1 cnd2]; rewrite <- cnd1; simpl; rewrite vtest.
destruct test as [c |] eqn: tq; try discriminate.
destruct c; try discriminate; contradiction.
Qed.

End main_loop_reasoning.

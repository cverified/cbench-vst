From Flocq Require Core Binary.
From Coquelicot Require Import Coquelicot.
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
  sqrt x - 32 * bpow r2 (-23) <= y <= sqrt x + 3 ->
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
assert (-32 * bpow r2 (-23) <= e <= 3) by (unfold e; lra).
generalize (from_g.l1 b e).
unfold from_g.s1, from_g.s2, from_g.s3, from_g.i1, from_g.i2, from_g.i3, BND.
cbv [lower upper].
change rndNE with (round_mode mode_NE).
replace (float2R from_g.f1) with 1 by (compute; lra).
replace (float2R from_g.f2) with 2 by (compute; lra).
replace (float2R from_g.f3) with (-32 * bpow r2 (-23)) by (compute; lra).
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

Lemma pure_decrease_2u (lbs ubx u x y : R) :
  0 < lbs -> 0 < x -> lbs <= sqrt x -> 0 < u ->
  sqrt x + 2 * u <= y <= ubx ->
  sqrt x <= (y + x / y) / 2 < y - u.
Proof.
intros lbs0 x0 lbss intu inty.
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
  1 <= x <= 4 -> sqrt x + 16 * ulp1 * sqrt x <= y <= 4 ->
  sqrt x - 16 * ulp1 <= round' (round' (y + round' (x / y)) / 2) < y.
Proof.
intros intx inty.
assert (intu : 0 < ulp1 < / 1024) by (unfold ulp1; simpl; lra).
assert (ugt0 : 0 < 8 * ulp1) by lra.
assert (tmp := from_g_proof x y intx).
assert (sg1 : 1 <= sqrt x).
  now rewrite <- sqrt_1; apply sqrt_le_1_alt.
assert (sqrt x <= 2).
  replace 2 with (sqrt (2 ^ 2)) by (rewrite sqrt_pow2; lra).
  apply sqrt_le_1_alt; lra.
assert (xgt0 : 0 < x) by lra.
assert (inty' : sqrt x - 32 * bpow r2 (-23) <= y <= sqrt x + 3) by (fold ulp1; nra).
assert (inty2 : sqrt x + 2 * (8 * bpow r2 (-23)) <= y <= 4) by (fold ulp1; nra).
assert (tmp2 := pure_decrease_2u 1 4 _ x y Rlt_0_1 xgt0 sg1 ugt0 inty2).
split.
  apply Rle_trans with ((y + x / y) / 2 - 9 * bpow r2 (-24));[ | lra].
  enough (9 * bpow r2 (-24) < 16 * ulp1);[ | compute]; lra.
apply Rle_lt_trans with ((y + x / y) / 2 + 9 * bpow r2 (-24));[lra | ].
assert (step : (y + x / y) / 2 + 8 * ulp1 < y) by lra.
apply Rlt_trans with (2 := step).
apply Rplus_lt_compat_l.
unfold ulp1; simpl; lra.
Qed.

Lemma converge_below_16 (x y : R) :
  1 <= x <= 4 -> sqrt x - 16 * ulp1 * sqrt x <= y <= sqrt x + 16 * ulp1 * sqrt x ->
  -5 * ulp1 <= round' (round' (y + round' (x / y)) / 2) - sqrt x
     <= 5 * ulp1.
Proof.
intros intx inty.
assert (1 <= sqrt x).
  now rewrite <- sqrt_1; apply sqrt_le_1_alt.
assert (0 < ulp1 < / 1024) by (unfold ulp1; simpl; lra).
assert (sqrt x <= 2).
  replace 2 with (sqrt (2 ^ 2)) by (rewrite sqrt_pow2; lra).
  apply sqrt_le_1_alt; lra.
assert (bigy : sqrt x - 32 * bpow r2 (-(23)) <= y <= sqrt x + 3).
  split.
    apply Rle_trans with (2 := proj1 inty).
    apply Rplus_le_compat_l, Ropp_le_contravar.
    replace (32 * bpow r2 (-(23))) with (16 * bpow r2 (-(23)) * 2) by ring.
    apply Rmult_le_compat_l;[compute | ]; lra.
  apply Rle_trans with (1 := proj2 inty); apply Rplus_le_compat_l.
  apply Rle_trans with (16 * ulp1 * 2);[ | compute; lra].
  apply Rmult_le_compat_l;[compute | ]; lra.
assert (ygt0 : /2 < y).
  apply Rlt_le_trans with (2 := proj1 bigy).
  apply Rlt_le_trans with (1 - 32 * bpow r2 (- (23))).
    compute; lra.
  now apply Rplus_le_compat_r.
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
  apply Rle_trans with (32 * bpow r2 (-23));[ |compute]; nra.
apply pow_incr; split;[lra | ].
apply Rle_trans with (32 * bpow r2 (-23));[ | compute]; nra.
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
  /2 <= x -> /2 <= y -> 0 < x / y <= 2 * x.
Proof.
intros intx inty.
assert (ygt0 : y <> 0) by lra.
split.
  apply Rmult_lt_reg_r with y;[lra | ].
  now unfold Rdiv; rewrite Rmult_assoc, Rinv_l; lra.
apply Rmult_le_reg_r with y;[lra | ].
unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r; [ nra | lra].
Qed.

Lemma body_exp_div_x_y_bounds x y :
  /2 <= x -> /2 <= y ->
  0 <= round' (x / y) <= round' (2 * x).
Proof.
intros intx inty.
assert (ygt0 : y <> 0) by lra.
assert (divint : 0 < x / y <= 2 * x).
  now apply body_exp_div_x_y_bounds1.
split.
  rewrite <- (round_0 radix2 f32_exp (round_mode mode_NE)).
  now apply round_le'; lra.
apply round_le'; tauto.
Qed.

(* The upper constraint on x is too strict, but good enough for now. *)
Lemma body_exp_sum_bounds x y :
  (/2 <= x <  /2 * B2R' predf32max)%R ->
  (/2 <= y < B2R' predf32max)%R ->
  (/2 <= round' (y + round' (x / y)) <= B2R' f32max)%R.
Proof.
intros intx inty.
assert (int1 : (0 <= round' (x / y) <= round' (2 * x))%R).
  now apply body_exp_div_x_y_bounds.
destruct (Rlt_le_dec x (bpow radix2 64)) as [xlow | xhigh].
  split.
    rewrite <- round'h.
    apply round_le'; lra.
  assert (r2xb : round' (2 * x) <= bpow r2 65).
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
destruct (Rlt_le_dec y (sqrt x)) as [ylow | yhigh].
  assert (y < bpow radix2 64)%R.
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
assert (0 < sqrt x)%R.
  apply sqrt_lt_R0; lra.
assert (divsqrt : (x / y <= sqrt x)%R).
  apply Rmult_le_reg_r with y;[lra | ].
    unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r;[ | lra].
    rewrite <- (sqrt_sqrt x) at 1;[ | lra].
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
  (/2 <= x < /2 * B2R' predf32max)%R ->
  (/2 <= y < B2R' predf32max)%R -> /4 <= body_exp_R x y <= B2R' f32max.
Proof.
intros intx inty.
assert ((/2 <= round' (y + round' (x / y)) <= B2R' f32max)%R).
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
assert (tmp := body_exp_bounds _ _ intx' inty').
assert (tm2 := body_exp_sum_bounds _ _ intx' inty').
assert (tm3 := body_exp_div_x_y_bounds _ _ (proj1 intx') (proj1 inty')).
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

End From_floating_point_numbers_to_reals.

Lemma float32_bound_ulp x :
  bpow r2 (-126) <= x -> 0 < ulp radix2 f32_exp x <= x / bpow radix2 23.
Proof.
intros intx.
assert (0 < bpow r2 (-126)) by (simpl; lra).
assert (xn0 : x <> 0%R) by lra.
assert (t := ulp_neq_0 r2 f32_exp _ xn0).
rewrite t; unfold cexp.
assert (-125 <= mag_val _ _ (mag r2 x))%Z.
apply mag_ge_bpow; rewrite Rabs_pos_eq by lra; assumption.
unfold FLT_exp; rewrite Z.max_l by lia.
split;[now apply bpow_gt_0 | ].
apply Rmult_le_reg_r with (bpow r2 23);[now apply bpow_gt_0 | ].
unfold Rdiv; rewrite <- bpow_plus, Rmult_assoc, Rinv_l, Rmult_1_r; cycle 1.
  now apply Rgt_not_eq; apply bpow_gt_0.
apply Rle_trans with (bpow r2 (mag r2 x - 1)).
  now apply bpow_le; lia.
now generalize (bpow_mag_le r2 _ xn0); rewrite Rabs_pos_eq by lra.
Qed.

Lemma cexp_bpow : forall x e, x <> 0%R ->
  (-149 < cexp radix2 f32_exp x)%Z ->
  (-149 < e + cexp radix2 f32_exp x)%Z ->
  cexp radix2 f32_exp (x * bpow radix2 e)%R = (cexp radix2 f32_exp x + e)%Z.
Proof.
intros x e xn0 xbnds ebnds.
revert xbnds ebnds.
unfold cexp, f32_exp, FLT_exp.
rewrite mag_mult_bpow; auto.
destruct (Z_le_gt_dec (3 - 128 - 24) (mag radix2 x - 24)).
  rewrite Z.max_l; lia.
rewrite Z.max_r; lia.
Qed.

Lemma mantissa_bpow x e :
  x <> 0%R ->
  (-149 < cexp radix2 f32_exp x)%Z ->
  (-149 < e + cexp radix2 f32_exp x)%Z ->
  scaled_mantissa radix2 f32_exp (x * bpow radix2 e) =
  scaled_mantissa radix2 f32_exp x.
Proof.
unfold scaled_mantissa.
intros xn0 cndx cnde; rewrite cexp_bpow; auto.
rewrite !Rmult_assoc, <- !bpow_plus.
apply f_equal with (f := fun u => (x * bpow radix2 u)%R); ring.
Qed.

Lemma round_mult_bpow x e :
  (x <> 0)%R ->
  (-149 < cexp radix2 f32_exp x)%Z ->
  (-149 < e + cexp radix2 f32_exp x)%Z ->
  round' (x * bpow radix2 e) = round' x * bpow radix2 e.
Proof.
intros xn0 canx inte.
unfold round', round, Defs.F2R; simpl.
rewrite mantissa_bpow by tauto.
rewrite cexp_bpow by tauto.
now rewrite bpow_plus, Rmult_assoc.
Qed.

Lemma round_proof (x y : R) :
  round' y = y ->
  1 <= x <= B2R' predf32max ->
  sqrt x + 16 * bpow r2 (-(23)) * sqrt x <= y <= x ->
  - (5 / bpow r2 24 * y) <= round' (round'(y + round' (x / y)) / 2) -
   (y + (x / y)) / 2 <=
  5 / bpow r2 (24) * y.
Proof.
intros ry intx inty.
replace (sqrt x + 16 * bpow r2 (-(23)) * sqrt x) with 
  (sqrt x * (1 + 16 * bpow r2 (-(23)))) in inty by ring.
assert (ele1 : bpow r2 (-126) <= 1) by (simpl; lra).
assert (sge0 : (1 <= sqrt x)%R).
  now rewrite <- sqrt_1; apply sqrt_le_1_alt; lra.
assert (0 < bpow r2 (-(23)) < /1024) by (simpl; lra).
assert (sx0 : (sqrt x <> 0)%R) by lra.
set (e := y - sqrt x).
assert (0 < y) by (simpl in inty; lra).
assert (yge1 : 1 <= y).
  apply Rle_trans with (2 := proj1 inty).
  rewrite <- (Rmult_1_r 1) at 1; apply Rmult_le_compat; lra.
assert (boundxy1 : (x / y < sqrt x * (1 - 15 * bpow r2 (-(23))))%R).
  unfold Rdiv; apply Rmult_lt_reg_r with y;[lra | ].
  rewrite Rmult_assoc, Rinv_l, Rmult_1_r;[ | lra].
  rewrite <- (sqrt_sqrt x) at 1;[ | lra].
  rewrite Rmult_assoc; apply Rmult_lt_compat_l;[lra | ].
  apply Rmult_lt_reg_l with (/ (1 - 15 * bpow r2 (-(23)))).
    apply Rinv_0_lt_compat; simpl; lra.
  rewrite <- Rmult_assoc, Rinv_l, Rmult_1_l by (simpl; lra).
  apply Rlt_le_trans with (2 := proj1 inty).
  rewrite (Rmult_comm (sqrt x)); apply Rmult_lt_compat_r;[|simpl];lra.
assert (ulpsgt0 : 0 < ulp r2 f32_exp (sqrt x)).
  apply float32_bound_ulp; lra.
assert (x / y < y).
  apply Rlt_trans with (sqrt x * 1).
    apply Rlt_le_trans with (1:= boundxy1).
    apply Rmult_le_compat_l;[| simpl ]; lra.
    apply Rlt_le_trans with (2 := proj1 inty).
    apply Rmult_lt_compat_l;[| compute]; lra.
assert (y + round' (x / y) <= 2 * y).
  assert (sqrt x <= y * ( 1 - bpow r2 (-(23)))).
    apply Rmult_le_reg_r with (/ (1 - bpow r2 (- (23)))).
      apply Rinv_0_lt_compat; compute; lra.
    rewrite Rmult_assoc, Rinv_r, Rmult_1_r by (compute; lra).
    apply Rle_trans with (2 := proj1 inty).
    apply Rmult_le_compat_l;[lra | ].
    assert (tech : forall a, a <> 1 -> / (1 - a) = 1 + a + (a ^ 2) / (1 - a)).
      now intros; field; lra.
    rewrite tech by (compute; lra).
    rewrite !Rplus_assoc; apply Rplus_le_compat_l.
    replace 16 with (1 + 15) by ring; rewrite Rmult_plus_distr_r, Rmult_1_l.
    apply Rplus_le_compat_l.
    apply Rmult_le_reg_r with (1 - bpow r2 (-(23)));[lra | ].
    unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
    compute; lra.
  enough (round' (x / y) <= y) by lra. (* simpler if round' y = y *)
  rewrite <- ry at 2; apply round_le'; lra.
assert (1 <= mag r2 y)%Z.
  apply mag_ge_bpow; rewrite Rabs_pos_eq;[simpl | ]; lra.
assert (boundsum : round' (y + round' (x / y)) <= 2 * y).
  replace (2 * y) with (round' y * bpow r2 1) by (rewrite ry; simpl; lra).
  rewrite <- round_mult_bpow; try lra; unfold cexp, FLT_exp; try lia.
  apply round_le'; simpl; lra.  
assert (0 < x / y).
  apply Rmult_lt_0_compat;[lra | apply Rinv_0_lt_compat; lra].
assert (0 <= round' (x / y)).
  rewrite <- (round_0 r2 f32_exp (round_mode mode_NE)).
  apply round_le; try typeclasses eauto; lra.
assert (rsum : Rabs (round' (y + round' (x / y)) - (y + round' (x / y))) <=
            ulp r2 f32_exp y * 2).
  apply Rle_trans with (1 := error_le_ulp r2 f32_exp (round_mode mode_NE)
                             (y + round' (x / y))).
  replace 2 with (bpow r2 1) by (compute; lra).
  rewrite <- ulp_FLT_exact_shift; try lra; try lia.
  apply ulp_le; try typeclasses eauto.
  replace (bpow r2 1) with 2 by (simpl; lra).
  rewrite !Rabs_pos_eq; try lra.    
apply (Rmult_le_compat_r (/ 2)) in rsum;[|lra ].
rewrite Rmult_assoc, Rinv_r, Rmult_1_r in rsum;[ | lra].
replace (/2) with (Rabs (/2)) in rsum by (rewrite Rabs_pos_eq; lra).
rewrite <- Rabs_mult, Rmult_minus_distr_r in rsum. 
assert (rdiv : Rabs (round' (x / y) - x / y) <= ulp r2 f32_exp y).
  assert (tmp := error_le_ulp r2 f32_exp (round_mode mode_NE) (x / y)).
  fold (round' (x / y)) in tmp; apply Rle_trans with (1 := tmp).
  apply ulp_le; try typeclasses eauto; rewrite !Rabs_pos_eq; lra.
assert (rsum' : Rabs ((y + round' (x / y)) / 2 - (y + x / y) / 2) <=
                    ulp r2 f32_exp y / 2).
  unfold Rdiv at 1 3 5; rewrite <- Rmult_minus_distr_r, Rabs_mult.
  rewrite (Rabs_pos_eq (/ 2)) by lra.
  apply Rmult_le_compat_r; [lra | ].
  replace (y + round' (x / y) - (y + x / y)) with (round' (x / y) - x / y); lra.
apply Rabs_def2b.
assert (tech : forall c a b, Rabs(a - b) <= Rabs (a - c) + Rabs (c - b)).
  intros c a b; replace (a - b) with ((a - c) + (c - b)) by ring.
  now apply Rabs_triang.
apply Rle_trans with (1 := tech (round' (y + round' (x / y)) / 2) _ _).
replace (5 / bpow r2 24 * y) with
   (y / bpow r2 23  + (y / bpow r2 23  + y / bpow r2 23 * /2) ) by (simpl; lra).
apply Rplus_le_compat.
  apply Rle_trans with 
    (1 := error_le_ulp r2 f32_exp _ (round' (y + round' (x / y)) / 2)).
  apply Rle_trans with 
      (2 := proj2 (float32_bound_ulp _ (Rle_trans _ _ _ ele1 yge1))).
  apply ulp_le; try typeclasses eauto.
  rewrite !Rabs_pos_eq; try lra.
  enough (0 <= round' (y + round' (x / y))) by lra.
  replace 0 with (round' 0) by (apply round_0; typeclasses eauto).
  apply round_le'; lra.
apply Rle_trans with (1 := tech ((y + round' (x / y)) / 2) _ _).
apply Rplus_le_compat.
apply Rle_trans with (1 := rsum).
  apply (proj2 (float32_bound_ulp _ (Rle_trans _ _ _ ele1 yge1))).
apply Rle_trans with (1 := rsum').
apply Rmult_le_compat_r;[lra | apply float32_bound_ulp; lra].
Qed.

Lemma ffderive x y :
  y <> 0 ->
  is_derive (fun z => (z + x / z)/2 - 5 * bpow r2 (-(24)) * z) y
       ((1 - x / y ^ 2) / 2 - 5 * bpow r2 (-(24))).
Proof.
intros yn0; auto_derive; auto.
simpl; field; compute; lra.
Qed.

Lemma ff_above x y :
  (1 <= x) -> sqrt x * (1 + 16 * ulp1) <= y ->
  0 < (1 - x / y ^ 2) / 2 - 5 * bpow r2 (-(24)).
Proof.
intros xge1 yges.
assert (sge0 : (1 <= sqrt x)%R).
  now rewrite <- sqrt_1; apply sqrt_le_1_alt; lra.
assert (ygt0 : 0 < y).
  apply Rlt_le_trans with (2 := yges).
  apply Rmult_lt_0_compat;[ | compute]; try lra.
assert (y <> 0) by lra.
assert (0 < y ^ 2) by (apply pow2_gt_0; assumption).
assert (y ^ 2 <> 0) by now apply Rgt_not_eq.
enough (10 * bpow r2 (-(24)) < 1 - x / y ^ 2) by lra.
apply Rmult_lt_reg_r with (y ^ 2);[ assumption | ].
unfold Rdiv; rewrite Rmult_minus_distr_r, Rmult_1_l.
rewrite (Rmult_assoc x), Rinv_l, Rmult_1_r by auto.
enough (x < (1 - 10 * bpow r2 (-(24))) * y ^ 2) by lra.
apply Rlt_le_trans with (x * ((1 + 16 * ulp1) ^ 2 * (1 - 10 * bpow r2 (-(24))))).
  rewrite <- (Rmult_1_r x) at 1.
  apply Rmult_lt_compat_l;[ | unfold ulp1; simpl];lra.
rewrite <- Rmult_assoc, (Rmult_comm (1 - _)).
apply Rmult_le_compat_r;[unfold ulp1; simpl; lra | ].
replace x with (sqrt x ^ 2) by (simpl; rewrite Rmult_1_r, sqrt_sqrt; lra).
rewrite <- Rpow_mult_distr; apply pow_incr; split;[ | tauto].
apply Rmult_le_pos;[ | unfold ulp1; simpl]; lra.
Qed.

Lemma pure_above x y :
  (1 <= x) -> sqrt x * (1 + 16 * ulp1) <= y ->
  sqrt x * (1 - 16 * ulp1) <= (y + x / y) / 2 - 5 * bpow r2 (-(24)) * y.
Proof.
intros xge1 yges.
set (y' := sqrt x * (1 + 16 * ulp1)).
assert (sge0 : (1 <= sqrt x)%R).
  now rewrite <- sqrt_1; apply sqrt_le_1_alt; lra.
assert (expand : (y' + x / y') / 2 =
  sqrt x + sqrt x * ((16 * ulp1) ^ 2 / (2 * (1 + 16 * ulp1)))).
  rewrite <- (sqrt_sqrt x) at 1 by lra.
unfold y'; field; split;[compute |]; lra.
apply Rle_trans with ((y' + x / y') / 2 - 5 * bpow r2 (-(24)) * y').
  rewrite expand; unfold y'.
  rewrite <- (Rmult_1_r (sqrt x)) at 2. 
  rewrite <- Rmult_plus_distr_l, (Rmult_comm (5 * bpow r2 (-(24)))), Rmult_assoc.
  rewrite <- Rmult_minus_distr_l.
  apply Rmult_le_compat_l;[ | compute ]; lra.
set (f z := (z + x / z) / 2 - 5 * bpow r2 (-(24)) * z).
change (f y' <= f y).
destruct (Req_dec y y') as [yy' | yny'].
  rewrite yy'; apply Req_le, eq_refl.
assert (ygty' : y' < y) by (unfold y' in yny' |- *; lra).
assert (0 < y').
  unfold y'; apply Rmult_lt_0_compat;[ | compute]; lra.
assert (ders :forall t, y' <= t <= y -> forall k, (k <= 1)%nat -> ex_derive_n f k t).
  intros t intt [ | k'] deg; inversion deg; try solve[simpl; auto].
    simpl; exists ((1 - x / t ^ 2) / 2 - 5 * bpow r2 (-(24))).
    apply ffderive; lra.
  assert (abs : (S k' <= 0)%nat) by assumption; inversion abs.
destruct (Taylor_Lagrange f 0 y' y ygty' ders) as [c [intc Pc]].
rewrite Pc; clear Pc; simpl; replace (1 / 1) with 1 by field.
unfold Rdiv; rewrite Rinv_1, !Rmult_1_l, !Rmult_1_r.
enough (0 <= (y - y') * Derive (fun z => f z) c) by lra.
apply Rmult_le_pos;[lra | ].
assert (cn0 : c <> 0) by lra.
rewrite (is_derive_unique (fun z : R => f z) c _ (ffderive x c cn0)).
apply Rlt_le, ff_above; auto; apply Rlt_le, (proj1 intc).
Qed.

Lemma body_exp_decrease16' x y:
  round' y = y ->
  1 <= x <= B2R 24 128 predf32max ->
  sqrt x + 16 * bpow r2 (-(23)) * sqrt x <= y <= x ->
  sqrt x * (1 - 16 * ulp1) <= body_exp_R x y < y.
Proof.
intros ry intx inty.
assert (sge0 : (1 <= sqrt x)%R).
  now rewrite <- sqrt_1; apply sqrt_le_1_alt; lra.
assert (yge1 : 1 <= y).
  apply Rle_trans with (2 := proj1 inty).
  replace (sqrt x + 16 * bpow r2 (- (23)) * sqrt x) with
          (sqrt x * (1 + 16 * bpow r2 (- (23)))) by ring.
  rewrite <- (Rmult_1_r 1) at 1; apply Rmult_le_compat; simpl; lra.
assert (sgt0 : 0 < sqrt x) by lra.
assert (xgt0 : 0 < x) by lra.
assert (u8gt0 : 0 < 8 * ulp1 * sqrt x) by (unfold ulp1; simpl; lra).
assert (inty' : sqrt x - 16 * ulp1 * sqrt x <= y <= x).
  split;[ | lra].
  apply Rle_trans with (2 := proj1 inty).
  apply Rplus_le_compat_l; rewrite Ropp_mult_distr_l.
  apply Rmult_le_compat_r;[ | unfold ulp1; simpl]; lra.
assert (inty2 : sqrt x + 2 * (8 * bpow r2 (-(23)) * sqrt x) <= y <= x).
  rewrite <- !Rmult_assoc; assumption.
split.
  apply Rle_trans with ((y + x / y) / 2 - 5 / bpow r2 24 * y).
    apply pure_above; try lra.
    rewrite Rmult_plus_distr_l, Rmult_1_r, (Rmult_comm (sqrt x)); tauto.
  apply Rplus_le_reg_l with (- ((y + x / y) / 2)).
  unfold Rminus; rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l, Rplus_comm.
  exact (proj1 (round_proof _ _ ry intx inty)).
apply Rle_lt_trans with ((y + x / y) / 2 + 5 / bpow r2 24 * y).
  apply Rplus_le_reg_l with (- ((y + x / y) / 2)).
  rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l, Rplus_comm.
  exact (proj2 (round_proof _ _ ry intx inty)).
assert (0 < bpow r2 (-(23)) < / 1024) by (simpl; lra).
assert (0 < y) by nra.
assert (egt0 : 0 < 5 * bpow r2 (- (23)) * y).
  apply Rmult_lt_0_compat;[simpl | ]; lra.  
assert (inty3 : sqrt x + 2 * (5 * bpow r2 (-(23)) * y) <= y <= x).
  split;[ | tauto].
  enough (sqrt x <= y * (1 - 2 * (5 * bpow r2 (-(23))))) by lra.
  apply Rmult_le_reg_r with (/ (1 - 2 * (5 * bpow r2 (- (23))))).
    apply Rinv_0_lt_compat; simpl; lra.
  rewrite Rmult_assoc, Rinv_r, Rmult_1_r by lra.
  apply Rle_trans with (2 := proj1 inty).
  replace (sqrt x + 16 * bpow r2 (- (23)) * sqrt x) with
    (sqrt x * (1 + 16 * bpow r2 (- (23)))) by ring.
  apply Rmult_le_compat_l;[lra | ].
  simpl; lra.
assert (tmp := pure_decrease_2u 1 x (5 * bpow r2 (-(23)) * y) x y Rlt_0_1 xgt0 
               sge0 egt0 inty3).
apply Rplus_lt_reg_r with (- (5 * bpow r2 (- (23)) * y)).
apply Rle_lt_trans with (2 := proj2 tmp).
enough (0 < 5 * bpow r2 (- (23)) * y - 5 / bpow r2 24 * y) by lra.
rewrite <- Rmult_minus_distr_r; apply Rmult_lt_0_compat;[simpl | ];lra.
Qed.

Lemma positive_finite x : 0 < B2R' x -> is_finite _ _ x = true.
Proof. destruct x; simpl; auto; lra. Qed.

Section above1.

Variables x : float32.

Definition invariant (p : float32 * float32) :=
    fst p = x /\
    (sqrt (B2R' x) - 16 * ulp1 * sqrt (B2R' x) <= B2R' (snd p) <= 
       Rmax (B2R' x) (sqrt (B2R' x) + 5 * ulp1 * sqrt (B2R' x)))%R.

Definition final (v : float32) :=
  sqrt (B2R' x) - 5 * ulp1 <= B2R' v <= sqrt (B2R' x) + 5 * ulp1.

Hypothesis intx : 1 <= B2R' x < /2 * B2R' predf32max.

Lemma invariant_test x' y :
  invariant (x', y) -> Bcompare _ _ (body_exp x y) y <> Some Lt ->
  ~ (B2R' (body_exp x y) < B2R' y).
Proof.
intros [xx' inty]; simpl in inty; clear x' xx'.
assert (0 < ulp1 < / 1024) by (unfold ulp1; simpl; lra).
assert (1 <= sqrt (B2R' x)).
  now rewrite <- sqrt_1; apply sqrt_le_1_alt.
assert (sqrt (B2R' x) <= 2 ^ 63).
  replace (2 ^ 63) with (sqrt ((2 ^ 63) ^ 2)) by  (rewrite sqrt_pow2; lra).
  replace ((2 ^ 63) ^ 2) with (2 ^ 126) by lra.
  apply sqrt_le_1_alt; apply Rlt_le, Rlt_le_trans with (1 := proj2 intx).
  unfold B2R'; rewrite predf32max_val; simpl; lra.
assert (intx' : / 2 <= B2R' x < / 2 * B2R' predf32max).
  split;[apply Rle_trans with (2 := proj1 intx);lra | tauto].
assert (vpmax: B2R' predf32max = 2 ^ 126) by (compute; lra).
assert (vmax: B2R' f32max = (2 ^ 24 - 1) * 2 ^ 104) by (compute; lra).
assert (inty' : / 2 <= B2R' y < B2R' predf32max).
  split;[apply Rle_trans with (2 := proj1 inty); nra | ].
  enough (Rmax (B2R' x) (sqrt (B2R' x) + 5 * ulp1 * sqrt (B2R' x))
                 < B2R' predf32max) by lra.
  destruct (Rle_dec (B2R' x) (sqrt (B2R' x) + 5 * ulp1 * sqrt (B2R' x))).
    rewrite Rmax_right;[nra | lra].
  rewrite Rmax_left; lra.
assert (expb := body_exp_bounds (B2R' x) (B2R' y) intx' inty').
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

End above1.

Section interval_1_4.

Variable x : float32.

Hypothesis intx : 1 <= B2R' x <= 4.

Let widen_1_4_to_max : 1 <= B2R' x < /2 * B2R' predf32max.
Proof.
unfold B2R' at 3; rewrite predf32max_val; simpl; lra.
Qed.

Lemma invariant_test_1_4 x' y :
  invariant x (x', y) -> Bcompare _ _ (body_exp x y) y <> Some Lt ->
  ~ (B2R' (body_exp x y) < B2R' y).
Proof.
apply invariant_test; assumption.
Qed.

Lemma invariant_initial : invariant x (x, x).
Proof.
assert (0 < ulp1 < / 1024) by (unfold ulp1; simpl; lra).
assert (sge0 : (1 <= sqrt (B2R' x))%R).
  now rewrite <- sqrt_1; apply sqrt_le_1_alt; lra.
split;[reflexivity | ]; simpl; split.
  apply Rle_trans with (sqrt (B2R' x)).
    rewrite <- (Rmult_1_l (sqrt (B2R' x))) at 1 3.
    rewrite <- Rmult_minus_distr_r; apply Rmult_le_compat_r;[ | compute]; lra.
  assert (1 <= sqrt (B2R' x)).
    now rewrite <- sqrt_1; apply sqrt_le_1_alt.
  rewrite <- (Rmult_1_r (sqrt (B2R' x))).
  rewrite <- (sqrt_sqrt (B2R' x)) at 2 by lra.
  apply Rmult_le_compat_l; lra.
now apply Rmax_l.
Qed.

Lemma invariant_final :
  forall x' y, invariant x (x', y) ->
     Bcompare 24 128 (body_exp x y) y <> Some Lt ->
     final x (body_exp x' y).
Proof.
intros x' y iv test.
assert (0 < ulp1 < / 1024) by (unfold ulp1; simpl; lra).
assert (sqrt (B2R' x) <= 2).
  replace 2 with (sqrt(2 ^ 2)) by (rewrite sqrt_pow2; try lra).
  apply sqrt_le_1_alt; lra.
assert (1 <= sqrt (B2R' x)).
  now rewrite <- sqrt_1; apply sqrt_le_1_alt.
apply (invariant_test _ widen_1_4_to_max _ _ iv) in test.
destruct iv as [cnd1 cnd2]; simpl in cnd1, cnd2; rewrite cnd1; clear x' cnd1.
revert test.
unfold final; rewrite body_exp_val; try lra; cycle 1.
  split.
    apply Rle_trans with (2 := proj1 cnd2).
    rewrite <- (Rmult_1_l (sqrt _)) at 1; rewrite <- Rmult_minus_distr_r.
    rewrite <- (Rmult_1_r (/ 2)); apply Rmult_le_compat; lra. 
  destruct (Rle_dec (B2R' x) (sqrt (B2R' x) + 5 * ulp1 * sqrt (B2R' x))).
    rewrite Rmax_right in cnd2;[nra | lra].
  rewrite Rmax_left in cnd2; lra.
intros test.
destruct (Rle_dec (B2R' y) (sqrt (B2R' x) + 16 * ulp1 * sqrt (B2R' x)))
   as [yl16 | yg16].
  assert (tmp := converge_below_16 _ _ intx (conj (proj1 cnd2) yl16)); lra.
assert (inty : sqrt (B2R' x) + 16 * ulp1 * sqrt (B2R' x) <= B2R' y <= B2R' x).
  destruct (Rle_dec (B2R' x) (sqrt (B2R' x) + 5 * ulp1 * sqrt (B2R' x))).
    rewrite Rmax_right in cnd2 by lra.
    case yg16; apply Rle_trans with (1 := proj2 cnd2).
    apply Rplus_le_compat_l; rewrite <- (Rmult_1_r (5 * ulp1)).
    apply Rmult_le_compat; lra.
    split;[lra | ].
  rewrite Rmax_left in cnd2; lra.
assert (yl4 : B2R' y <= 4) by lra.
assert (tmp := decrease_above_16 _ (B2R' y) intx (conj (proj1 inty) yl4)); lra.
Qed.

Lemma invariant_spec_1_4 :
  forall x' y,  Bcompare _ _ (body_exp x' y) y = Some Lt ->
              invariant x (x', y) ->
              invariant x (x', body_exp x' y).
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
destruct (Rle_dec (B2R' y) (sqrt (B2R' x) + 16 * ulp1 * sqrt (B2R' x)))
     as [yl16 | yg16].
  assert (tmp:= converge_below_16 _ (B2R' y) intx (conj (proj1 cnd2) yl16)).
  assert (tmp1 := converge_below_16 _ (B2R' y) intx (conj (proj1 cnd2) yl16)).
  rewrite body_exp_val; simpl in cnd2;[ |lra |nra ].
  split; [nra | ].
  apply Rle_trans with (sqrt (B2R' x) + 5 * ulp1).
    lra.
  apply Rle_trans with (2 := Rmax_r _ _); nra.
destruct (Rle_dec (B2R' x) (sqrt (B2R' x) + 5 * ulp1 * sqrt (B2R' x)))
   as [xclose | xfar].
  rewrite Rmax_right in cnd2 by auto; simpl in cnd2.
  assert (yl16 : B2R' y <= sqrt (B2R' x) + 16 * ulp1 * sqrt (B2R' x)) by nra.
  assert (tmp1 := converge_below_16 _ (B2R' y) intx (conj (proj1 cnd2) yl16)).
  split; [| rewrite Rmax_right]; lra.
simpl in cnd2; rewrite Rmax_left in cnd2 by lra.
assert (yg16' : sqrt (B2R' x) + 16 * ulp1 * sqrt (B2R' x) <= B2R' y) by lra.
rewrite body_exp_val; simpl in cnd2; try lra.
assert (yl4 : B2R' y <= 4) by lra.
assert (tmp := decrease_above_16 _ (B2R' y) intx (conj yg16' yl4)).
split;[ | rewrite Rmax_left; lra].
apply Rle_trans with (2 := proj1 tmp).
apply Rplus_le_compat_l, Ropp_le_contravar.
rewrite <- (Rmult_1_r (16 * ulp1)) at 1.
apply Rmult_le_compat_l;[compute |];lra.
Qed.

Lemma main_loop_prop :
  final x (main_loop (x, x)).
Proof.
generalize invariant_initial.
apply main_loop_ind.
  now intros p x' y pxy test IH v; apply IH, invariant_spec_1_4.
intros p x' y pxy test vtest cndtest iv. 
apply invariant_final; auto.
destruct iv as [cnd1 cnd2]; rewrite <- cnd1; simpl; rewrite vtest.
destruct test as [c |] eqn: tq; try discriminate.
destruct c; try discriminate; contradiction.
Qed.

End interval_1_4.

Lemma cexp_32 e r :
  (-126 < e)%Z ->
  (bpow radix2 (e - 1) <= r < bpow radix2 e)%R ->
  cexp radix2 f32_exp r = (e - 24)%Z.
Proof.
intros ce inte.
unfold cexp, f32_exp, FLT_exp.
assert (r0 : (0 <= r)%R).
  assert (tmp := bpow_ge_0 radix2 (e - 1)); lra.
assert (vln : mag_val radix2 _ (mag radix2 r) = e).
  now  apply mag_unique; rewrite Rabs_pos_eq.
rewrite vln.
apply Z.max_l; lia.
Qed.

Lemma body_exp_value_scale x' y' e:
  (1 <= x' <= 4)%R ->
  / 2 * sqrt x' <= y' <= 2 * sqrt x' ->
  (-125 < e)%Z ->
  (-149 < (2 * e) + cexp radix2 f32_exp x')%Z ->
  (round' (round' (y' + round' (x' / y')) / 2) * bpow radix2 e =
  round' (round' (y' * bpow radix2 e +
              round' ((x' * bpow radix2 (2 * e)) /
                      (y' * bpow radix2 e))) / 2))%R.
Proof.
intros intx inty elb inte.
assert (1 <= sqrt x')%R.
  rewrite <- sqrt_1.
  apply sqrt_le_1_alt; lra.
assert (yn0 : y' <> 0%R) by lra.
assert (bpgt0 : (0 < bpow radix2 e)%R) by apply bpow_gt_0.
assert (sqrtle : (sqrt x' <= x')%R).
  enough (1 * sqrt x' <= x')%R by lra.
  rewrite <- (sqrt_sqrt x') at 2 by lra.
  apply Rmult_le_compat_r; lra.
assert (sle2 : (sqrt x' <= 2)%R).
  rewrite <- (sqrt_pow2 2) by lra.
  apply sqrt_le_1_alt; lra.
assert (qgth : (/2 <= x' / y')%R).
  apply Rmult_le_reg_r with y';[lra | ].
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
  lra.
assert (qgt0 : (0 < x' / y')%R) by lra.
replace (2 * e)%Z with (e + e)%Z by ring.
rewrite bpow_plus.
replace (x' * (bpow radix2 e * bpow radix2 e) / (y' * bpow radix2 e))%R with
    ((x' / y') * bpow radix2 e)%R by now field; lra.
assert (rh : (round' (/2) = /2)%R).
  apply round_generic; try typeclasses eauto.
  replace (/2)%R with (bpow radix2 (-1)) by (compute; lra).
  apply generic_format_bpow'.
    apply FLT_exp_valid; reflexivity.
  apply Z.lt_le_incl; reflexivity.
assert (rqgth : (/2 <= round' (x' / y'))%R).
  rewrite <- rh; apply round_le'; lra.
assert (sumgt1 : (1 <= y' + round' (x' / y'))%R) by lra.
assert (rsumgt1 : (1 <= round' (y' + round' (x' / y')))%R).
  rewrite <- round'1; apply round_le'; lra.
assert (expgeh : (/2 <= round' (y' + round' (x' / y')) / 2)%R) by lra.
assert (rexpgeh : (/2 <= round' (round' (y' + round' (x' / y')) / 2))%R).
  now rewrite <- rh; apply round_le'.
assert (qle2s : x' / y' <= 2 * sqrt x').
  rewrite <- (sqrt_sqrt x') at 1 by lra.
  unfold Rdiv; rewrite Rmult_assoc, Rmult_comm.
  apply Rmult_le_compat_r;[lra | ].
  apply Rmult_le_reg_r with y';[lra |].
  rewrite Rmult_assoc, Rinv_l, Rmult_1_r; lra.
assert (qle4 : (x' / y' <= 4)%R) by lra.
assert (rqle2 : (round' (x' / y') <= 4)%R).
  now rewrite <- round'4; apply round_le'.
assert (-24 <= cexp r2 f32_exp (x' / y') <= -21)%Z.
  destruct (Rle_lt_dec 1 (x' / y')).
    destruct (Rle_lt_dec 2 (x' / y')).
      destruct (Rle_lt_dec 4 (x' / y')).
        rewrite (cexp_32 3);[lia | lia| simpl bpow; split; lra].
      rewrite (cexp_32 2);[lia | lia| simpl bpow; split; lra].
    rewrite (cexp_32 1);[lia | lia| simpl bpow; split; lra].
  rewrite (cexp_32 0);[lia | lia| simpl bpow; split; lra].
rewrite round_mult_bpow; try lra; try lia.
rewrite <- Rmult_plus_distr_r.
assert (r6 : round' 6 = 6%R).
  assert (ccexp : (6 <> 0 -> -21 <= 0)%Z) by lia.
  generalize (generic_format_F2R radix2 f32_exp 6 0 ).
  replace (cexp radix2 f32_exp (F2R {|Defs.Fnum := 6; Defs.Fexp := 0|})) with
     (-21)%Z; cycle 1.
    unfold cexp; simpl.
    replace (mag_val radix2 _
                    (mag radix2 (F2R {|Defs.Fnum :=6; Defs.Fexp :=0|}))) with
    3%Z.
      reflexivity.
    symmetry; apply mag_unique.
    replace (F2R {| Defs.Fnum := 6; Defs.Fexp := 0|}) with 6%R by (compute; lra).
    rewrite Rabs_pos_eq by lra.
    compute; lra.
  replace (F2R {| Defs.Fnum := 6; Defs.Fexp := 0|}) with 6%R by (compute; lra).
  intros tmp; assert (gf6 := tmp ccexp); clear tmp.
  apply round_generic; try typeclasses eauto.
  exact gf6.
assert (sumle6: (y' + round' (x' / y') <= 6)%R).
  destruct (Rle_dec y' (sqrt x'));[lra | ].
    enough (round' (x' / y') <= 2) by lra.
    assert (x' / y' <= 2).
      rewrite <- (sqrt_sqrt x') by lra.
      apply Rmult_le_reg_r with y';[lra | ].
      unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
      apply Rle_trans with (2 * sqrt x'); try lra.
      apply Rmult_le_compat_r; lra.
    now rewrite <- round'2; apply round_le'.
assert (rsumle6 : (round' (y' + round' (x' / y')) <= 6)%R).
  now rewrite <- r6; apply round_le'.
assert (exple4: (round' (y' + round' (x' / y')) / 2 <= 4)%R) by lra.
assert (-23 <= (cexp r2 f32_exp (y' + round' (x' / y'))) <= -21)%Z.
  destruct (Rle_lt_dec 2 (y' + round' (x' / y'))).
    destruct (Rle_lt_dec 4 (y' + round' (x' / y'))).
      rewrite (cexp_32 3);[lia | lia| simpl bpow; split; lra].
    rewrite (cexp_32 2);[lia | lia| simpl bpow; split; lra].
  rewrite (cexp_32 1);[lia | lia| simpl bpow; split; lra].
assert (-24 <= (cexp r2 f32_exp (round' (y' + round' (x' / y')) / 2)) <= -22)%Z.
  destruct (Rle_lt_dec 1 (round' (y' + round' (x' / y')) / 2)).
    destruct (Rle_lt_dec 2 (round' (y' + round' (x' / y')) / 2)).
      rewrite (cexp_32 2);[lia | lia| simpl bpow; split; lra].
    rewrite (cexp_32 1);[lia | lia| simpl bpow; split; lra].
  rewrite (cexp_32 0);[lia | lia| simpl bpow; split; lra].
rewrite round_mult_bpow; try lra; try lia.
assert (tech : forall a b, ((a * b) / 2 = (a / 2) * b)%R)
   by (intros; field; lra).
rewrite tech.
rewrite round_mult_bpow; try lra; try lia.
Qed.

Section interval_1_max.

Variable x : float32.

Hypothesis intx : 1 <= B2R' x < /2 * B2R' predf32max.

Definition r4 := Build_radix 4 eq_refl.

Lemma r2r4 e : bpow r2 (2 * e) = bpow r4 e.
Proof.
rewrite !bpow_powerRZ, !powerRZ_Rpower; try (simpl; lra).
change (IZR r2) with 2%R.
change (IZR r4) with 4%R.
replace 4 with (Rpower 2 2).
  now rewrite Rpower_mult, mult_IZR.
rewrite <- powerRZ_Rpower; simpl; lra.
Qed.

Lemma bpow_0 w : bpow w 0 = 1.
Proof. reflexivity. Qed.

Lemma bpow_square r w : bpow r w ^ 2 = bpow r (2 * w).
Proof.
replace (2 * w)%Z with (w + w)%Z by ring.
rewrite bpow_plus; ring.
Qed.

Lemma invariant_spec_max  x' y :
       Bcompare 24 128 (body_exp x' y) y = Some Lt ->
       invariant x (x', y) -> invariant x (x', body_exp x' y).
Proof.
destruct (Rle_lt_dec (B2R' x) 4) as [xle4 | xgt4].
  apply invariant_spec_1_4; lra.
assert (0 < ulp1 < /1024) by (compute; lra).
assert (1 <= sqrt (B2R' x)).
  now rewrite <- sqrt_1; apply sqrt_le_1_alt.
assert (sxh : sqrt (B2R' x) < B2R' x / 2).
  set (f z := z / 2 - sqrt z).    
  assert (f4 : f 4 = 0).
    unfold f; replace 4 with (2 ^ 2) by lra; rewrite sqrt_pow2; lra.
  assert (df : forall z, 0 < z -> is_derive f z (/2 - /(2 * sqrt z))).
    unfold f; intros z zgt0; auto_derive;[lra | field].
    now apply Rgt_not_eq, sqrt_lt_R0.
  assert (dfs : forall t, 4 <= t <= B2R' x -> forall k, (k <= 1)%nat ->
            ex_derive_n f k t).
    intros t intt [ | [ | k']] kl; simpl; auto.
    exists (/2  - / (2 * sqrt t)); apply df; lra.
    inversion kl; assert (abs : (S (S k') <= 0)%nat) by easy; inversion abs.
  destruct (Taylor_Lagrange f 0 4 (B2R' x) xgt4 dfs) as [c [intc Pc]].
  assert (h : 0 < f (B2R' x)).
    assert (cgt0 : 0 < c) by lra.
    rewrite Pc; simpl.
    rewrite (is_derive_unique (fun x :R => f x) c _ (df c cgt0)).
    unfold Rdiv; rewrite f4, Rmult_0_r, Rinv_1, !Rmult_1_r, Rplus_0_l.
    apply Rmult_lt_0_compat;[lra | ].
    assert (2 < sqrt c).
      replace 2 with (sqrt (2 ^ 2)) by (rewrite sqrt_pow2; lra).
      apply sqrt_lt_1_alt; lra.
    apply Rlt_Rminus, Rinv_lt_contravar; lra.
  unfold f in h; lra.
intros test [cnd1 cnd2]; simpl in cnd1; rewrite cnd1 in cnd2 |- *.
cbv [snd] in cnd2; clear cnd1.
assert (ry : round' (B2R' y) = B2R' y) by (apply round_B2R').
assert (maxval : B2R' predf32max = 2 ^ 126).
  unfold B2R'; rewrite predf32max_val; compute; lra.
assert (finx : is_finite 24 128 x = true) by (apply positive_finite; lra).
assert (0 < B2R' y).
  apply Rlt_le_trans with (2 := proj1 cnd2).
  rewrite <- (Rmult_1_l (sqrt (B2R' x))) at 1.
  rewrite <- Rmult_minus_distr_r; apply Rmult_lt_0_compat;[compute|]; lra.
assert (finy : is_finite 24 128 y = true) by (apply positive_finite; auto).
assert (inx' : 1 <= B2R' x <= B2R' predf32max).
  rewrite maxval in intx |- *; lra.
cbv [snd] in cnd2.
assert (xfar : sqrt (B2R' x) + 5 * ulp1 * sqrt (B2R' x) <= B2R' x).
  rewrite <- (Rmult_1_l (sqrt _)) at 1; rewrite <- Rmult_plus_distr_r.
  replace (B2R' x) with (B2R' x / 2 * 2) at 2 by field.
  rewrite (Rmult_comm (1 + _)); apply Rmult_le_compat; lra.
rewrite Rmax_left in cnd2 by lra.
assert (inx2 : /2 <= B2R' x < /2 * B2R' predf32max) by lra.
assert (iny2 : /2 <= B2R' y < B2R' predf32max).
  split; [| lra].
  apply Rle_trans with (2:= proj1 cnd2).
  rewrite <- (Rmult_1_l (sqrt (B2R' x))) at 1; rewrite <- (Rmult_1_r (/2)).
  rewrite <- Rmult_minus_distr_r.
  apply Rmult_le_compat;[| |compute | ]; lra.
destruct (body_exp_finite_value _ _ finx finy inx2 iny2) as [bval finval].
clear finx finy inx2 iny2.
destruct (Rle_lt_dec (sqrt (B2R' x) + 16 * bpow r2 (-(23)) * sqrt (B2R' x))
             (B2R' y)) as [ybig | yclose].
  unfold invariant;split;[easy | cbv [snd] in cnd2 |- *].
  rewrite Rmax_left by lra.
  rewrite bval.
  destruct (body_exp_decrease16' _ _ ry inx' (conj ybig (proj2 cnd2)))
      as [lb  ub].
  rewrite Rmult_minus_distr_l, Rmult_1_r, (Rmult_comm (sqrt _)) in lb.
  split; [exact lb | apply Rle_trans with (2 := (proj2 cnd2)) ].
  apply Rlt_le; exact ub.
set (e := mag_val _ _ (mag r4 (B2R' x))).
set (x2 := B2R' x * bpow r2 (-(2 * (e - 1)))).
set (y2 := B2R' y * bpow r2 (- (e - 1))).
assert (yval : B2R' y = y2 * bpow r2 (e - 1)).
  unfold y2; rewrite Rmult_assoc, <- bpow_plus, Z.add_opp_diag_l, bpow_0; ring.
assert (xval : B2R' x = x2 * bpow r2 (2 * (e - 1))).
  unfold x2; rewrite Rmult_assoc, <- bpow_plus, Z.add_opp_diag_l, bpow_0; ring.
assert (xn0 : B2R' x <> 0) by lra.
assert (inx2 : 1 <= x2 <= 4).
  split;
    (apply Rmult_le_reg_r with (bpow r2 (2 * (e - 1)));
      [apply bpow_gt_0 |
       rewrite <- xval, r2r4, <- (Rabs_pos_eq (B2R' x)) by lra]).
    now rewrite Rmult_1_l; apply bpow_mag_le.
  replace 4 with (bpow r4 1) by (compute; lra).
  rewrite <- bpow_plus; ring_simplify (1 + (e - 1))%Z.
  now apply Rlt_le, bpow_mag_gt.
assert (ybnds : /2 * sqrt x2 <= y2 <= 2 * sqrt x2).
  split;
    (apply Rmult_le_reg_r with (bpow r2 (e - 1));[apply bpow_gt_0 | ];
     rewrite <- yval, <- (sqrt_pow2 (bpow r2 (e - 1))) by (apply bpow_ge_0);
    rewrite Rmult_assoc, <- sqrt_mult, bpow_square;[ | lra | apply pow2_ge_0];
    rewrite <- xval).
    apply Rle_trans with (2 := proj1 cnd2).      
    rewrite <- (Rmult_1_l (sqrt (B2R' x))) at 2.
    rewrite <- Rmult_minus_distr_r.
    apply Rmult_le_compat_r;[| compute ]; lra.
  apply Rlt_le, Rlt_le_trans with (1 := yclose).
  rewrite <- (Rmult_1_l (sqrt (B2R' x))) at 1.
  rewrite <- Rmult_plus_distr_r.
  apply Rmult_le_compat_r;[ | compute]; lra.
assert (mx'bound : (0 < mag r2 (B2R' x))%Z).
  apply mag_gt_bpow; simpl; rewrite Rabs_pos_eq; lra.
assert ((2 > 0)%Z /\ (0 < 2)%Z) as [twogt0 twogt0'] by lia.
assert (ediv2 : e = (mag_val _ _ (mag r2 (B2R' x)) / 2 +
                     mag_val _ _ (mag r2 (B2R' x)) mod 2)%Z).
  unfold e; apply mag_unique; rewrite Rabs_pos_eq by lra.
  destruct (mag r2 (B2R' x)) as [v vp].
  simpl; destruct (vp xn0) as [vle vgt].
  rewrite Rabs_pos_eq in vle, vgt by lra.
  rewrite <- !r2r4.
  assert (cases : (v mod 2 = 0)%Z \/ (v mod 2 = 1)%Z).
    assert (tmp := Z.mod_pos_bound v 2 twogt0'); lia.
  assert (veq := Z_div_mod_eq v _ twogt0).
  destruct cases as [even | odd].
    rewrite even, Z.add_0_r in veq |- *.
    rewrite Z.mul_sub_distr_l, <- veq, Z.mul_1_r; split; [ | lra].
    replace (v - 2)%Z with ((v - 1) + (-(1)))%Z by ring.
    rewrite bpow_plus; replace (bpow r2 (-(1))) with (/2) by (compute; lra).
    lra.
  rewrite odd in veq |- *.
  rewrite Z.mul_sub_distr_l, !Z.mul_add_distr_l.
  replace (2 * (v / 2) + 2 * 1 - 2 * 1)%Z with (v - 1)%Z
      by (rewrite veq at 1; ring).
  replace (2 * (v / 2) + 2 * 1)%Z with (v + 1)%Z
      by (rewrite veq at 1; ring).
  split;[lra | rewrite bpow_plus; replace (bpow r2 1) with 2 by (compute; lra)].
  lra.
assert (-23 <= (cexp r2 f32_exp x2) <= -21)%Z.
  destruct (Rle_lt_dec 2 x2).
    destruct (Rle_lt_dec 4 x2).
      rewrite (cexp_32 3);[lia | lia| simpl bpow; split; lra].
    rewrite (cexp_32 2);[lia | lia| simpl bpow; split; lra].
  rewrite (cexp_32 1);[lia | lia| simpl bpow; split; lra].
assert (cx'bounds : (-149  < 2 * (e - 1) + cexp r2 f32_exp x2)%Z).
  assert (bm := Z.mod_pos_bound (mag r2 (B2R' x)) 2 twogt0').
  assert (tmp := (Z_div_mod_eq (mag r2 (B2R' x)) 2) twogt0).
  lia.
assert (egt : (-125 < (e - 1))%Z).
  assert (bm := Z.mod_pos_bound (mag r2 (B2R' x)) 2 twogt0').
  assert (tmp := (Z_div_mod_eq (mag r2 (B2R' x)) 2) twogt0).
  lia.
split;[easy | cbv [snd]; rewrite bval].
assert (t := body_exp_value_scale _ _ _ inx2 ybnds egt cx'bounds).
rewrite xval, yval, <- t.
rewrite sqrt_mult, <- bpow_square;[ | lra | apply bpow_ge_0]. 
rewrite sqrt_pow2.
assert (invariant x2 (x2, y2)).
 <- Rmult_assoc, <- Rmult_minus_distr_r;[ | apply bpow_ge_0].
rewrite <- Rmult_assoc, <- Rmult_plus_distr_r.
split.

End.


Lemma main_loop_correct x :
  1 <= B2R 24 128 x <= 4 ->
  Rabs (B2R 24 128 (main_loop (x, x)) - sqrt (B2R 24 128 x)) <= 5 / (2 ^ 23).
Proof.
set (s := sqrt _); set (m := B2R _ _ (main_loop _)); set (e := _ / _).
intros intx; apply Rabs_le.
enough (s - e <= m <= s + e) by lra.
replace e with (5 * ulp1) by (unfold ulp1, e; simpl; lra).
now apply main_loop_prop.
Qed.

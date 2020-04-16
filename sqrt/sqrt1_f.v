From Flocq Require Core Binary.
From Coquelicot Require Import Coquelicot.
Require Import Reals Gappa.Gappa_library Psatz.
Import Defs Raux FLT Generic_fmt Gappa_definitions Binary Ulp.
Require Import FunInd Recdef.
(* This file is generated from sqrt1.g *)
Require from_g.

Lemma Rdiv_1_r x : x / 1 = x.
Proof.
now unfold Rdiv; rewrite Rinv_1, Rmult_1_r.
Qed.

Lemma Rdiv_cancel x y : y <> 0 -> x / y * y = x.
Proof.
intro yn0; unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r; lra.
Qed.

Lemma Rdiv_le_swap x y z : 0 < y -> x <= z * y -> x / y <= z.
Proof.
intros y0 cnd; apply Rmult_le_reg_r with y;[lra | ].
rewrite Rdiv_cancel; lra.
Qed.

Lemma Rdiv_lt_swap x y z : 0 < y -> x < z * y -> x / y < z.
Proof.
intros y0 cnd; apply Rmult_lt_reg_r with y;[lra | ].
rewrite Rdiv_cancel; lra.
Qed.

Definition float32 := binary_float 24 128.

Definition round' x := 
   round radix2 (FLT_exp (-149) 24) (round_mode mode_NE) x.

Notation f32_exp := (FLT_exp (-149) 24).

Notation r2 := Gappa_definitions.radix2.

Notation cexp' := (cexp r2 f32_exp).

Open Scope R_scope.

Lemma sqrt_1_4 x :
  1 <= x <= 4 -> 1 <= sqrt x <= 2.
Proof.
intros intx.
rewrite <- sqrt_1; rewrite <- (sqrt_pow2 2) by lra.
replace (2 ^ 2) with 4 by ring.
split; apply sqrt_le_1_alt; lra.
Qed.

Lemma sqrt_above_4_lb x : 4 < x -> sqrt x < x / 2.
Proof.
intros xgt4.
set (f z := z / 2 - sqrt z).    
assert (f4 : f 4 = 0).
  unfold f; replace 4 with (2 ^ 2) by lra; rewrite sqrt_pow2; lra.
assert (df : forall z, 0 < z -> is_derive f z (/ 2 - /(2 * sqrt z))).
  unfold f; intros z zgt0; auto_derive;[lra | field].
  now apply Rgt_not_eq, sqrt_lt_R0.
assert (dfs : forall t, 4 <= t <= x -> forall k, (k <= 1)%nat ->
            ex_derive_n f k t).
  intros t intt [ | [ | k']] kl; simpl; auto.
    exists (/ 2  - / (2 * sqrt t)); apply df; lra.
  inversion kl; assert (abs : (S (S k') <= 0)%nat) by easy; inversion abs.
destruct (Taylor_Lagrange f 0 4 x xgt4 dfs) as [c [intc Pc]].
assert (h : 0 < f x).
  assert (cgt0 : 0 < c) by lra.
  rewrite Pc; simpl.
  rewrite (is_derive_unique (fun x :R => f x) c _ (df c cgt0)).
  rewrite !Rdiv_1_r, Rmult_1_l, Rmult_1_r, f4, Rplus_0_l.
  apply Rmult_lt_0_compat;[lra | ].
 assert (2 < sqrt c).
    replace 2 with (sqrt (2 ^ 2)) by (rewrite sqrt_pow2; lra).
    apply sqrt_lt_1_alt; lra.
  apply Rlt_Rminus, Rinv_lt_contravar; lra.
unfold f in h; lra.
Qed.

Lemma from_g_proof (x y : R) :
  1 <= x <= 4 ->
  sqrt x - 32 * bpow r2 (- (23)) <= y <= sqrt x + 3 ->
  - (9) * bpow r2 (- (24)) <= round' (round'(y + round' (x / y)) / 2) -
   (y + (x / y)) / 2 <=
  9 * bpow r2 (- (24)).
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
assert (- (32) * bpow r2 (-(23)) <= e <= 3) by (unfold e; lra).
generalize (from_g.l1 b e).
unfold from_g.s1, from_g.s2, from_g.s3, from_g.i1, from_g.i2, from_g.i3, BND.
cbv [lower upper].
change rndNE with (round_mode mode_NE).
replace (float2R from_g.f1) with 1 by (compute; lra).
replace (float2R from_g.f2) with 2 by (compute; lra).
replace (float2R from_g.f3) with (- (32) * bpow r2 (-(23))) by (compute; lra).
replace (float2R from_g.f4) with 3 by (compute; lra).
replace (float2R from_g.f5) with (-9 * bpow r2 (- (24))) by (compute; lra).
replace (float2R from_g.f6) with (9 * bpow r2 (- (24))) by (compute; lra).
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

Definition main_loop_measure (p : float32 * float32) : nat :=
  float_to_nat (snd p).

Definition float2 := B754_finite 24 128 false (2 ^ 23) (-22) eq_refl.

Section NAN.
Variable the_nan : float32 -> float32 -> {x0 : float32 | is_nan 24 128 x0 = true}.

Definition float_add (x y : float32) : float32 :=
  Bplus 24 128 eq_refl eq_refl the_nan mode_NE x y.

Definition float_div (x y : float32) :=
  Bdiv 24 128 eq_refl eq_refl the_nan mode_NE x y.

Definition body_exp (x y : float32) :=
  float_div (float_add y (float_div x y)) float2.

(* The beauty of it is that we don't need to know what computation is performed,
  only the test matters. *)
Function main_loop (p : float32 * float32) {measure main_loop_measure} :
   float32 :=
  match p with
  | (x, y) =>
   let z := body_exp x y in 
    match Bcompare 24 128 z y with
    | Some Lt => main_loop (x, z)
    | _ => z
    end
  end.
Proof.
now intros p x y eqxy c cq; apply float_to_nat_Clt.
Qed.

Open Scope R_scope.

Definition ulp1 := bpow radix2 (- (23)).

Lemma sub_16_ulp_2 v : 1 <= v -> / 2 * v < v - 16 * ulp1 * v.
Proof.
intros v1; rewrite <- (Rmult_1_l v) at 2; rewrite <- Rmult_minus_distr_r.
apply Rmult_lt_compat_r; [ | compute]; lra.
Qed.

Lemma add_16_ulp_2 v : 1 <= v -> v + 16 * ulp1 * v < 2 * v.
Proof.
intros v1; rewrite <- (Rmult_1_l v) at 1; rewrite <- Rmult_plus_distr_r.
apply Rmult_lt_compat_r; [ | compute]; lra.
Qed.

Lemma pure_decrease_2u (lbs u x y : R) :
  0 < lbs -> 0 < x -> lbs <= sqrt x -> 0 < u ->
  sqrt x + 2 * u <= y ->
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
apply Rdiv_lt_swap; lra.
Qed.

Lemma decrease_above_16 (x y : R) :
  1 <= x <= 4 -> sqrt x + 16 * ulp1 * sqrt x <= y <= 4 ->
  sqrt x - 16 * ulp1 <= round' (round' (y + round' (x / y)) / 2) < y.
Proof.
intros intx inty.
assert (intu : 0 < ulp1 < / 1024) by (unfold ulp1; simpl; lra).
assert (ugt0 : 0 < 8 * ulp1) by lra.
assert (tmp := from_g_proof x y intx).
destruct (sqrt_1_4 _ intx) as [sg1 sl2].
assert (xgt0 : 0 < x) by lra.
assert (inty' : sqrt x - 32 * bpow r2 (- (23)) <= y <= sqrt x + 3) 
  by (fold ulp1; nra).
assert (inty2 : sqrt x + 2 * (8 * bpow r2 (- (23))) <= y)
  by (fold ulp1; nra).
assert (tmp2 := pure_decrease_2u 1 _ x y Rlt_0_1 xgt0 sg1 ugt0 inty2).
assert (9 * bpow r2 (- (24)) < 16 * ulp1) by (compute; lra).
assert (tmp' := tmp inty').
split.
  apply Rle_trans with ((y + x / y) / 2 - 9 * bpow r2 (- (24))); lra.
apply Rle_lt_trans with ((y + x / y) / 2 + 9 * bpow r2 (-(24)));[lra | ].
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
destruct (sqrt_1_4 _ intx) as [sg1 sl2].
assert (0 < ulp1 < / 1024) by (unfold ulp1; simpl; lra).
assert (bigy : sqrt x - 32 * bpow r2 (- (23)) <= y <= sqrt x + 3).
  split.
    apply Rle_trans with (2 := proj1 inty).
    apply Rplus_le_compat_l, Ropp_le_contravar.
    replace (32 * bpow r2 (- (23))) with (16 * bpow r2 (- (23)) * 2) by ring.
    apply Rmult_le_compat_l;[compute | ]; lra.
  apply Rle_trans with (1 := proj2 inty); apply Rplus_le_compat_l.
  apply Rle_trans with (16 * ulp1 * 2);[ | compute; lra].
  apply Rmult_le_compat_l;[compute | ]; lra.
assert (ygt0 : / 2 < y).
  apply Rlt_le_trans with (2 := proj1 bigy).
  apply Rlt_le_trans with (1 - 32 * bpow r2 (- (23))).
    compute; lra.
  now apply Rplus_le_compat_r.
assert (tmp := from_g_proof x y intx bigy).
assert (ulp1 = 2 * bpow r2 (- (24))) by (unfold ulp1; simpl; lra).
enough (-bpow r2 (- (24)) <= (y + (x / y)) / 2 - sqrt x <= bpow r2 (- (24)))
  by lra.
rewrite <- (sqrt_sqrt x) at 1 3 by lra.
replace ((y + (sqrt x * sqrt x) / y) / 2 - sqrt x) with
   ((y - sqrt x) ^ 2 / (2 * y)) by (field; lra).
apply Rabs_le_inv; rewrite Rabs_pos_eq; cycle 1.
  apply Rmult_le_pos;[apply pow2_ge_0 | apply Rlt_le, Rinv_0_lt_compat]; lra.
apply Rle_trans with ((y - sqrt x) ^ 2 / 1).
apply Rmult_le_compat_l;[apply pow2_ge_0 | apply Rinv_le_contravar;lra].
rewrite Rdiv_1_r.
replace (bpow r2 (- (24))) with (bpow r2 (-(12)) ^ 2) by (compute; lra).
assert (ulp1 = bpow r2 (-23)) by reflexivity.
destruct (Rle_dec y (sqrt x)).
  replace ((y - sqrt x) ^ 2) with ((sqrt x - y) ^ 2) by ring.
  apply pow_incr; split;[lra | ].
  apply Rle_trans with (32 * bpow r2 (- (23)));[ |compute]; nra.
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

Lemma round'h : round' (/ 2) = (/ 2)%R.
Proof.
assert (for2 : generic_format radix2 (FLT_exp (3 - 128 - 24) 24) (/ 2)).
  replace (/ 2)%R with (F2R (Float radix2 (cond_Zopp false (2 ^ 23)) (-24))).
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
  / 2 <= x -> / 2 <= y -> 0 < x / y <= 2 * x.
Proof.
intros intx inty.
assert (ygt0 : y <> 0) by lra.
split.
  apply Rmult_lt_reg_r with y;[lra | ].
  rewrite Rdiv_cancel; lra.
apply Rdiv_le_swap; nra.
Qed.

Lemma body_exp_div_x_y_bounds x y :
  / 2 <= x -> / 2 <= y ->
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
  (/ 2 <= x <  / 2 * B2R' predf32max)%R ->
  (/ 2 <= y <= B2R' predf32max)%R ->
  (/ 2 <= round' (y + round' (x / y)) <= B2R' f32max)%R.
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
  apply Rdiv_le_swap;[lra | ].
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
  (/ 2 <= x < / 2 * B2R' predf32max)%R ->
  (/ 2 <= y <= B2R' predf32max)%R -> /4 <= body_exp_R x y <= B2R' f32max.
Proof.
intros intx inty.
assert ((/ 2 <= round' (y + round' (x / y)) <= B2R' f32max)%R).
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
  (/ 2 <= B2R' x < / 2 * B2R' predf32max)%R ->
  (/ 2 <= B2R' y <= B2R' predf32max)%R ->
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
assert (tm4 := Bdiv_correct 24 128 eq_refl eq_refl the_nan mode_NE x y yn0).
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
set (divxy := Bdiv 24 128 eq_refl eq_refl the_nan mode_NE x y).
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
assert (tm6 := Bplus_correct 24 128 eq_refl eq_refl the_nan mode_NE y
                     divxy finy findivxy').
rewrite Rlt_bool_true in tm6;[ | exact pluslt].
fold (B2R' divxy) in tm6; fold divxy' in tm6; fold (B2R' y) in tm6.
change (3 - 128 -24)%Z with (-149)%Z in tm6.
fold (round' (B2R' y + divxy')) in tm6.
destruct tm6 as [vsum [finsum signsum]].
assert (fin2 : is_finite 24 128 float2 = true) by reflexivity.
assert (b2n0 : B2R' float2 <> 0%R) by now compute; lra.
assert (tm4 := Bdiv_correct 24 128 eq_refl eq_refl the_nan mode_NE
                   (Bplus 24 128 eq_refl eq_refl the_nan mode_NE y
          (Bdiv 24 128 eq_refl eq_refl the_nan mode_NE x y))
                   _ b2n0).
  set (bexp :=   Bdiv 24 128 eq_refl eq_refl the_nan mode_NE
              (Bplus 24 128 eq_refl eq_refl the_nan mode_NE y
                 (Bdiv 24 128 eq_refl eq_refl the_nan mode_NE x y))
              float2).
fold bexp in tm4.
set (sum := (Bplus 24 128 eq_refl eq_refl the_nan mode_NE y
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
  1 <= B2R' x < / 2 * B2R' predf32max -> / 2 <= B2R' y <= B2R' predf32max ->
  B2R' (body_exp x y) =
  round' (round' (B2R' y + round' (B2R' x / B2R' y )) / 2).
Proof.
intros intx inty.
assert (finx : is_finite 24 128 x = true).
  destruct x; auto; compute in intx; lra.
assert (finy : is_finite 24 128 y = true).
  destruct y; auto; compute in inty; lra.
assert (intx' : / 2 <= B2R' x < / 2 * B2R' predf32max).
  lra.
assert (inty' : / 2 <= B2R' y <= B2R' predf32max).
  lra.
assert (tmp := body_exp_finite_value x y finx finy intx' inty').
tauto.
Qed.

Lemma body_exp_finite x y:
  1 <= B2R' x < / 2 * B2R' predf32max -> / 2 <= B2R' y <= B2R' predf32max ->
  is_finite 24 128 (body_exp x y) = true.
Proof.
intros intx inty.
assert (finx : is_finite 24 128 x = true).
  destruct x; auto; compute in intx; lra.
assert (finy : is_finite 24 128 y = true).
  destruct y; auto; compute in inty; lra.
assert (intx' : / 2 <= B2R' x < / 2 * B2R' predf32max).
  lra.
assert (inty' : / 2 <= B2R' y <= B2R' predf32max).
  lra.
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
rewrite Rdiv_cancel, <- bpow_plus;[ | now apply Rgt_not_eq; apply bpow_gt_0].
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
  sqrt x + 16 * bpow r2 (- (23)) * sqrt x <= y <= B2R' predf32max ->
  - (5 / bpow r2 24 * y) <= round' (round'(y + round' (x / y)) / 2) -
   (y + (x / y)) / 2 <=
  5 / bpow r2 (24) * y.
Proof.
intros ry intx inty.
replace (sqrt x + 16 * bpow r2 (- (23)) * sqrt x) with 
  (sqrt x * (1 + 16 * bpow r2 (- (23)))) in inty by ring.
assert (ele1 : bpow r2 (-126) <= 1) by (simpl; lra).
assert (sge0 : (1 <= sqrt x)%R).
  now rewrite <- sqrt_1; apply sqrt_le_1_alt; lra.
assert (0 < bpow r2 (- (23)) < / 1024) by (simpl; lra).
assert (sx0 : (sqrt x <> 0)%R) by lra.
set (e := y - sqrt x).
assert (0 < y) by (simpl in inty; lra).
assert (yge1 : 1 <= y).
  apply Rle_trans with (2 := proj1 inty).
  rewrite <- (Rmult_1_r 1) at 1; apply Rmult_le_compat; lra.
assert (boundxy1 : (x / y < sqrt x * (1 - 15 * bpow r2 (- (23))))%R).
  apply Rdiv_lt_swap;[lra | ].
  rewrite <- (sqrt_sqrt x) at 1;[ | lra].
  rewrite Rmult_assoc; apply Rmult_lt_compat_l;[lra | ].
  apply Rmult_lt_reg_l with (/ (1 - 15 * bpow r2 (- (23)))).
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
  assert (sqrt x <= y * ( 1 - bpow r2 (- (23)))).
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
    apply Rdiv_le_swap;[ | compute]; lra.
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
replace (/ 2) with (Rabs (/ 2)) in rsum by (rewrite Rabs_pos_eq; lra).
rewrite <- Rabs_mult, Rmult_minus_distr_r in rsum. 
assert (rdiv : Rabs (round' (x / y) - x / y) <= ulp r2 f32_exp y).
  assert (tmp := error_le_ulp r2 f32_exp (round_mode mode_NE) (x / y)).
  fold (round' (x / y)) in tmp; apply Rle_trans with (1 := tmp).
  apply ulp_le; try typeclasses eauto; rewrite !Rabs_pos_eq; lra.
assert (rsum' : Rabs ((y + round' (x / y)) / 2 - (y + x / y) / 2) <=
                    ulp r2 f32_exp y / 2).
  rewrite <- Rdiv_minus_distr; unfold Rdiv at 1 4;rewrite Rabs_mult.
  rewrite (Rabs_pos_eq (/ 2)) by lra.
  apply Rmult_le_compat_r; [lra | ].
  replace (y + round' (x / y) - (y + x / y)) with (round' (x / y) - x / y); lra.
apply Rabs_def2b.
assert (tech : forall c a b, Rabs(a - b) <= Rabs (a - c) + Rabs (c - b)).
  intros c a b; replace (a - b) with ((a - c) + (c - b)) by ring.
  now apply Rabs_triang.
apply Rle_trans with (1 := tech (round' (y + round' (x / y)) / 2) _ _).
replace (5 / bpow r2 24 * y) with
   (y / bpow r2 23  + (y / bpow r2 23  + y / bpow r2 23 * / 2) ) by (simpl; lra).
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
  is_derive (fun z => (z + x / z)/ 2 - 5 * bpow r2 (-(24)) * z) y
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
rewrite Rmult_minus_distr_r, Rmult_1_l, Rdiv_cancel by auto.
enough (x < (1 - 10 * bpow r2 (-(24))) * y ^ 2) by lra.
apply Rlt_le_trans with (x * ((1 + 16 * ulp1) ^ 2 *
                               (1 - 10 * bpow r2 (-(24))))).
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
rewrite Rdiv_1_r, Rmult_1_l, Rmult_1_r.
enough (0 <= (y - y') * Derive (fun z => f z) c) by lra.
apply Rmult_le_pos;[lra | ].
assert (cn0 : c <> 0) by lra.
rewrite (is_derive_unique (fun z : R => f z) c _ (ffderive x c cn0)).
apply Rlt_le, ff_above; auto; apply Rlt_le, (proj1 intc).
Qed.

Lemma body_exp_decrease16' x y:
  round' y = y ->
  1 <= x <= B2R 24 128 predf32max ->
  sqrt x + 16 * bpow r2 (- (23)) * sqrt x <= y <= B2R' predf32max ->
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
assert (inty' : sqrt x - 16 * ulp1 * sqrt x <= y <= B2R' predf32max).
  split;[ | lra].
  apply Rle_trans with (2 := proj1 inty).
  apply Rplus_le_compat_l; rewrite Ropp_mult_distr_l.
  apply Rmult_le_compat_r;[ | unfold ulp1; simpl]; lra.
assert (inty2 : sqrt x + 2 * (8 * bpow r2 (- (23)) * sqrt x) <= y
                  <= B2R' predf32max).
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
assert (0 < bpow r2 (- (23)) < / 1024) by (simpl; lra).
assert (0 < y) by nra.
assert (egt0 : 0 < 5 * bpow r2 (- (23)) * y).
  apply Rmult_lt_0_compat;[simpl | ]; lra.  
assert (inty3 : sqrt x + 2 * (5 * bpow r2 (- (23)) * y) <= y).
  enough (sqrt x <= y * (1 - 2 * (5 * bpow r2 (- (23))))) by lra.
  apply Rmult_le_reg_r with (/ (1 - 2 * (5 * bpow r2 (- (23))))).
    apply Rinv_0_lt_compat; simpl; lra.
  rewrite Rmult_assoc, Rinv_r, Rmult_1_r by lra.
  apply Rle_trans with (2 := proj1 inty).
  replace (sqrt x + 16 * bpow r2 (- (23)) * sqrt x) with
    (sqrt x * (1 + 16 * bpow r2 (- (23)))) by ring.
  apply Rmult_le_compat_l;[lra | ].
  simpl; lra.
assert (tmp := pure_decrease_2u 1 (5 * bpow r2 (- (23)) * y) x y Rlt_0_1 xgt0 
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

Definition invariantR x' y' :=
  sqrt x' - 16 * ulp1 * sqrt x' <= y' <= B2R' predf32max.

Definition invariant (p : float32 * float32) :=
    fst p = x /\ invariantR (B2R' x) (B2R' (snd p)).

Definition finalR x' y' := 
  sqrt x' - 5 * ulp1 * sqrt x' <= y' <= sqrt x' + 5 * ulp1 * sqrt x'.

Definition final (v : float32) := finalR (B2R' x) (B2R' v).

Hypothesis intx : 1 <= B2R' x < / 2 * B2R' predf32max.

Lemma invariant_test x' y :
  invariant (x', y) -> Bcompare _ _ (body_exp x y) y <> Some Lt ->
  ~ (B2R' (body_exp x y) < B2R' y).
Proof.
unfold invariant, invariantR; intros [xx' inty]; cbv[snd] in inty; clear x' xx'.
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
assert (inty' : / 2 <= B2R' y <= B2R' predf32max).
  split;[apply Rle_trans with (2 := proj1 inty); nra | ].
  enough (Rmax (B2R' x) (sqrt (B2R' x) + 5 * ulp1 * sqrt (B2R' x))
                 < B2R' predf32max) by lra.
  destruct (Rle_dec (B2R' x) (sqrt (B2R' x) + 5 * ulp1 * sqrt (B2R' x))).
    rewrite Rmax_right;[nra | lra].
  rewrite Rmax_left; lra.
assert (expb := body_exp_bounds (B2R' x) (B2R' y) intx' inty').
rewrite vmax in expb.
assert (bval : B2R' (body_exp x y) = body_exp_R (B2R' x) (B2R' y)).
  apply body_exp_val; lra.
assert (B2R' y <= 2 ^ 126).
  replace (2 ^ 126) with (B2R' predf32max) by (compute; lra).
  lra.  
assert (is_finite _ _ (body_exp x y) = true).
  apply body_exp_finite; lra.
rewrite Bcompare_correct; auto;[ | apply positive_finite; lra].
destruct (Rcompare _ _) eqn:vcmp.
    apply Rcompare_Eq_inv in vcmp; unfold B2R'; lra.
  now intros abs; case abs.
apply Rcompare_Gt_inv in vcmp; unfold B2R'; lra.
Qed.

End above1.

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

Lemma cexp_1_8 x : 
   1 <= x < 8 ->
   (-23 <= cexp' x <= -21)%Z.
Proof.
intros intx.
destruct (Rle_lt_dec 4 x).
  rewrite (cexp_32 3);[lia | lia| simpl bpow; split; lra].
destruct (Rle_lt_dec 2 x).
  rewrite (cexp_32 2);[lia | lia| simpl bpow; split; lra].
rewrite (cexp_32 1);[lia | lia| simpl bpow; split; lra].
Qed.

Lemma body_exp_decrease4 x y :
  1 <= x <= 4 ->
  4 < y <= B2R 24 128 predf32max ->
  sqrt x - 16 * ulp1 * sqrt x <= body_exp_R x y < y.
Proof.
intros intx inty.
assert (dlt1 : x / y < 1).
  apply Rdiv_lt_swap;[| rewrite Rmult_1_l]; lra.
assert (rdle1 : round' (x / y) <= 1).
  rewrite <- round'1; apply round_le'; lra.
assert (dge0 : 0 <= x / y).
  apply Rmult_le_reg_r with y;[| rewrite Rdiv_cancel]; lra.
assert (rdge0 : 0 <= round' (x / y)).
  rewrite <- (round_0 r2 f32_exp (round_mode mode_NE)).
  now apply round_le'.
assert (sl5 : y + round' (x / y) <= 5 / 4 * y) by lra.
assert (sge4 : 4 < y + round' (x / y)) by lra.
assert (sgt0 : 0 < y + round' (x / y)) by lra.
assert (rsg4 : 4 <= round' (y + round' (x / y))).
  rewrite <- round'4; apply round_le'; lra.
assert (rsl5 : round' (y + round' (x / y)) <= 11 / 8 * y).
  assert (tmp := error_le_ulp r2 f32_exp (round_mode mode_NE)
             (y + round' (x / y))).
  apply Rabs_def2b in tmp.
  assert (a : bpow r2 (-149 + 24 - 1) <= Rabs (y + round' (x / y))).
    rewrite Rabs_pos_eq by lra.
    apply Rle_trans with (2 := Rlt_le _ _ sge4); compute; lra.
  generalize (ulp_FLT_le r2 (-149) 24 _ a); rewrite Rabs_pos_eq by lra.
  intros tm2.
  fold (round' (y + round'(x/y))) in tmp.
  apply Rle_trans with 
    (5 / 4 * y + (y + round' (x / y)) * bpow r2 (1 - 24) );[lra | ].
  enough ((y + round' (x / y)) * bpow r2 (1 - 24) <= / 8 * y) by lra.
  apply Rle_trans with (5 / 4 * y * bpow r2 (1 - 24)).
    apply Rmult_le_compat_r;[apply bpow_ge_0 | lra].
  rewrite <- (Rmult_comm y), Rmult_assoc, (Rmult_comm y).
  apply Rmult_le_compat_r; [ | compute]; lra.
assert (round' (y + round' (x / y)) / 2 <= 11 / 16 * y) by lra.
assert (bge2 : 2 <= round' (y + round' (x / y)) / 2) by lra.
assert (tmp := error_le_ulp r2 f32_exp (round_mode mode_NE)
             (round' (y + round' (x / y)) / 2)).
apply Rabs_def2b in tmp; fold (round' (round' (y + round' (x / y)) / 2)) in tmp.
fold (body_exp_R x y) in tmp.
assert (a : bpow r2 (-149 + 24 - 1) <= Rabs (round' (y + round' (x / y)) / 2)).
  rewrite Rabs_pos_eq by lra.
  apply Rle_trans with (2 := bge2); compute; lra.
generalize (ulp_FLT_le r2 (-149) 24 _ a); rewrite Rabs_pos_eq by lra.
intros tm2.
split.
  assert (sge1 := sqrt_1_4 x intx).
  apply Rle_trans with (round' (sqrt x)).
    assert (tm3 := error_le_ulp r2 f32_exp (round_mode mode_NE) (sqrt x)).
    assert (a2 : bpow r2 (-149 + 24 - 1) <= Rabs (sqrt x)).
      rewrite Rabs_pos_eq by lra.
      apply Rle_trans with (2 := proj1 sge1); compute; lra.
    generalize (ulp_FLT_le r2 (-149) 24 _ a2); rewrite Rabs_pos_eq by lra.
    change (bpow r2 (1 - 24)) with ulp1; intros tm4.
    apply Rabs_def2b in tm3; fold (round' (sqrt x)) in tm3; lra.
  unfold body_exp_R; apply round_le'; lra.
enough (body_exp_R x y <= 3 / 4 * y) by lra.
apply Rle_trans with (11 / 16 * y +
                round' (y + round' (x / y)) / 2 * bpow r2 (1 - 24));[lra | ].
enough (round' (y + round' (x / y)) / 2 * bpow r2 (1 - 24) <= / 16 * y) by lra.
apply Rle_trans with (11 / 16 * y * bpow r2 (1 - 24)).
  apply Rmult_le_compat_r;[apply bpow_ge_0 | lra].
rewrite <- (Rmult_comm y), Rmult_assoc, (Rmult_comm y).
apply Rmult_le_compat_r; [ | compute]; lra.
Qed.

Section interval_1_4.

Variable x : float32.

Hypothesis intx : 1 <= B2R' x <= 4.

Let widen_1_4_to_max : 1 <= B2R' x < / 2 * B2R' predf32max.
Proof.
unfold B2R' at 3; rewrite predf32max_val; simpl; lra.
Qed.

Let sge0 : 1 <= sqrt (B2R' x).
Proof.
now rewrite <- sqrt_1; apply sqrt_le_1_alt; lra.
Qed.

Let sle2 : (sqrt (B2R' x) <= 2).
Proof.
replace 2 with (sqrt(2 ^ 2)) by (rewrite sqrt_pow2; try lra).
apply sqrt_le_1_alt; lra.
Qed.

Let ulp1_small : 0 < ulp1 < / 1024.
Proof. unfold ulp1; simpl; lra. Qed.

(*
Lemma widen_for_y y :
  invariantR (B2R' x) y -> / 2 <= y <= 5.
Proof.
unfold invariantR; intros iv; split.
  apply Rle_trans with (2 := proj1 iv).
  apply Rlt_le, Rle_lt_trans with (2 := sub_16_ulp_2 _ sge0); lra.
apply Rle_trans with (1 := proj2 iv).
destruct (Rle_dec (B2R' x) (sqrt (B2R' x) + 5 * ulp1 * sqrt (B2R' x))).
  rewrite Rmax_right by lra.
  apply Rle_trans with (sqrt (B2R' x) + 16 * ulp1 * sqrt (B2R' x));[nra | ].
  apply Rlt_le, Rlt_le_trans with (1 := add_16_ulp_2 _ sge0); lra.
rewrite Rmax_left; lra.
Qed.
*)

Lemma invariant_test_1_4 x' y :
  invariant x (x', y) -> Bcompare _ _ (body_exp x y) y <> Some Lt ->
  ~ (body_exp_R (B2R' x) (B2R' y) < B2R' y).
Proof.
unfold invariant, invariantR.
intros iv test.
assert (test' := invariant_test x widen_1_4_to_max _ _ iv test).
cbv [snd] in iv.
assert (px : 0 < B2R' x) by lra.
assert (hy : /2 <= B2R' y).
  apply Rle_trans with (2 := (proj1 (proj2 iv))).
  rewrite <- (Rmult_1_l (sqrt _)) at 1; rewrite <- Rmult_minus_distr_r.
  apply Rle_trans with ( 3 / 4 * 1);[lra | ].
  apply Rmult_le_compat; lra.
assert (py : 0 < B2R' y) by lra.
assert (t := body_exp_finite_value x y (positive_finite _ px)
        (positive_finite _ py)).
rewrite (fun h1 h2 => proj1 (t h1 h2)) in test';[exact test' | lra| lra].
Qed.

Lemma invariant_finalR x' y :
  1 <= x' <= 4 ->
  1 <= sqrt x' ->
  round' y = y ->
  invariantR x' y ->
  ~ body_exp_R x' y < y -> finalR x' (body_exp_R x' y).
Proof.
unfold invariantR.
intros intx' sge1 ry cnd2 test.
destruct (Rle_dec y (sqrt x' + 16 * ulp1 * sqrt x')) as [yl16 | yg16].
  unfold finalR.
  assert (tmp := converge_below_16 _ _ intx' (conj (proj1 cnd2) yl16)).
  unfold body_exp_R.
  split;[apply Rle_trans with (sqrt x' - 5 * ulp1);[nra | lra] |
         apply Rle_trans with (sqrt x' + 5 * ulp1);[lra | nra]].
assert (inty : sqrt x' + 16 * ulp1 * sqrt x' <= y <= B2R' predf32max).
  lra.
assert (wi : 1 <= x' <= B2R' predf32max).
  split;[ | apply Rle_trans with (1 := proj2 intx'); compute]; lra.
assert (tmp := body_exp_decrease16' x' y ry wi inty).
case test; exact (proj2 tmp).
Qed.

Lemma invariant_final :
  forall x' y, invariant x (x', y) ->
     Bcompare 24 128 (body_exp x y) y <> Some Lt ->
     final x (body_exp x' y).
Proof.
unfold invariant, invariantR; intros x' y iv test.
assert (0 < ulp1 < / 1024) by (unfold ulp1; simpl; lra).
assert (sqrt (B2R' x) <= 2).
  replace 2 with (sqrt(2 ^ 2)) by (rewrite sqrt_pow2; try lra).
  apply sqrt_le_1_alt; lra.
assert (1 <= sqrt (B2R' x)).
  now rewrite <- sqrt_1; apply sqrt_le_1_alt.
destruct iv as [cnd1 cnd2]; cbv [snd fst] in cnd1, cnd2.
assert (bv : B2R' (body_exp x y) = body_exp_R (B2R' x) (B2R' y)).
  apply body_exp_val; [assumption | ].
  split.
    apply Rle_trans with (2 := proj1 cnd2).
    rewrite <- (Rmult_1_l (sqrt _)) at 1; rewrite <- Rmult_minus_distr_r.
    rewrite <- (Rmult_1_r (/ 2)); apply Rmult_le_compat; lra. 
  lra.
unfold final; rewrite cnd1, bv.
apply (invariant_finalR (B2R' x) (B2R' y));[easy | easy | | easy | ].
  now apply round_B2R'.
apply (invariant_test_1_4 x); [split; easy | exact test].
Qed.

Lemma invariant_spec_1_4_R  x' y :
  1 <= x' <= 4 ->
  1 <= sqrt x' <= 2->
  invariantR x' y ->
  invariantR x' (body_exp_R x' y).
Proof.
unfold invariantR; intros intx' sge1 (* test *) cnd2.
destruct (Rle_dec y (sqrt x' + 16 * ulp1 * sqrt x'))
     as [yl16 | yg16].
  assert (tmp:= converge_below_16 _ y intx' (conj (proj1 cnd2) yl16)).
  unfold body_exp_R; split; [nra | ].
  apply Rle_trans with (sqrt x' + 5 * ulp1).
    lra.
  apply Rle_trans with (2 + 5 * ulp1);[ | compute]; lra.
destruct (Rle_lt_dec y 4) as [yl4 | yg4].
  assert (yg16' : sqrt x' + 16 * ulp1 * sqrt x' <= y) by lra.
  assert (tmp := decrease_above_16 _ y intx' (conj yg16' yl4)).
  fold (body_exp_R x' y) in tmp.
  split;[ | lra].
  apply Rle_trans with (2 := proj1 tmp), Rplus_le_compat_l.
  apply Ropp_le_contravar.
  rewrite <- (Rmult_1_r (_ * _)) at 1; apply Rmult_le_compat_l; lra.
assert (inty : 4 < y <= B2R' predf32max) by lra.
assert (tmp := body_exp_decrease4 _ _ intx' inty); lra.
Qed.

Lemma invariant_spec_1_4 :
  forall x' y, invariant x (x', y) -> invariant x (x', body_exp x' y).
Proof.
unfold invariant.
intros x' y [cnd1 cnd2]; simpl in cnd1; rewrite cnd1 in cnd2 |- *.
clear cnd1; split;[reflexivity | ].
cbv [snd] in cnd2 |- *; unfold invariantR in cnd2 |- *.
rewrite body_exp_val; [ | lra | nra].
now apply invariant_spec_1_4_R.
Qed.

End interval_1_4.

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
assert (bpgt0 : (0 < bpow radix2 e)%R) by apply bpow_gt_0.
assert (sqrtle : (sqrt x' <= x')%R).
  enough (1 * sqrt x' <= x')%R by lra.
  rewrite <- (sqrt_sqrt x') at 2 by lra.
  apply Rmult_le_compat_r; lra.
assert (sle2 : (sqrt x' <= 2)%R).
  rewrite <- (sqrt_pow2 2) by lra.
  apply sqrt_le_1_alt; lra.
assert (qgth : (/ 2 <= x' / y')%R).
  apply Rmult_le_reg_r with y';[lra | ].
  rewrite Rdiv_cancel; lra.
replace (2 * e)%Z with (e + e)%Z by ring.
rewrite bpow_plus.
replace (x' * (bpow radix2 e * bpow radix2 e) / (y' * bpow radix2 e))%R with
    ((x' / y') * bpow radix2 e)%R by now field; lra.
assert (rqgth : (/ 2 <= round' (x' / y'))%R).
  rewrite <- round'h; apply round_le'; lra.
assert (sumgt1 : (1 <= y' + round' (x' / y'))%R) by lra.
assert (rsumgt1 : (1 <= round' (y' + round' (x' / y')))%R).
  rewrite <- round'1; apply round_le'; lra.
assert (expgeh : (/ 2 <= round' (y' + round' (x' / y')) / 2)%R) by lra.
assert (rexpgeh : (/ 2 <= round' (round' (y' + round' (x' / y')) / 2))%R).
  now rewrite <- round'h; apply round_le'.
assert (qle2s : x' / y' <= 2 * sqrt x').
  rewrite <- (sqrt_sqrt x') at 1 by lra.
  apply Rdiv_le_swap;[lra | rewrite (Rmult_comm 2), Rmult_assoc].
  apply Rmult_le_compat_l;lra.
assert (qle4 : (x' / y' <= 4)%R) by lra.
assert (rqle2 : (round' (x' / y') <= 4)%R).
  now rewrite <- round'4; apply round_le'.
assert (-24 <= cexp' (x' / y') <= -21)%Z.
  destruct (Rlt_le_dec (x' / y') 1).
    rewrite (cexp_32 0);[lia | lia| simpl bpow; split; lra].
  enough (-(23) <= cexp' (x' / y') <= -21)%Z by lia.
  apply cexp_1_8; lra.
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
      apply Rdiv_le_swap; [lra | ].
      apply Rle_trans with (2 * sqrt x'); try lra.
      rewrite <- (sqrt_sqrt x') at 1 by lra.
      apply Rmult_le_compat_r; lra.
    now rewrite <- round'2; apply round_le'.
assert (rsumle6 : (round' (y' + round' (x' / y')) <= 6)%R).
  now rewrite <- r6; apply round_le'.
assert (exple4: (round' (y' + round' (x' / y')) / 2 <= 4)%R) by lra.
assert (-23 <= (cexp' (y' + round' (x' / y'))) <= -21)%Z.
  apply cexp_1_8; lra.
assert (-24 <= (cexp' (round' (y' + round' (x' / y')) / 2)) <= -22)%Z.
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

Lemma scale_data x y :
  4 <= x <= /2 * (B2R' predf32max) ->
  sqrt x - 16 * ulp1 * sqrt x <= y <= sqrt x + 16 * ulp1 * sqrt x ->
  exists e : Z, exists x2, exists y2,
    1 <= x2 <= 4 /\
    sqrt x2 - 16 * ulp1 * sqrt x2 <= y2 <= sqrt x2 + 16 * ulp1 * sqrt x2 /\
    x = x2 * bpow r2 (2 * e) /\ y = y2 * bpow r2 e /\
    (1 <= e <= 64)%Z /\
    body_exp_R x y = body_exp_R x2 y2 * bpow r2 e.
Proof.
intros intx inty.
set (e := (mag r4 x - 1)%Z).
set (x2 := x * bpow r2 (-(2 * e))).
set (y2 := y * bpow r2 (- e)).
assert (yval : y = y2 * bpow r2 e).
  unfold y2; rewrite Rmult_assoc, <- bpow_plus, Z.add_opp_diag_l, bpow_0; ring.
assert (xval : x = x2 * bpow r2 (2 * e)).
  unfold x2; rewrite Rmult_assoc, <- bpow_plus, Z.add_opp_diag_l, bpow_0; ring.
assert (xn0 : x <> 0) by lra.
assert (inx2 : 1 <= x2 <= 4).
  split;
    (apply Rmult_le_reg_r with (bpow r2 (2 * e));
      [apply bpow_gt_0 |
       rewrite <- xval, r2r4, <- (Rabs_pos_eq (x)) by lra]).
    now rewrite Rmult_1_l; apply bpow_mag_le.
  replace 4 with (bpow r4 1) by (compute; lra).
  rewrite <- bpow_plus; unfold e.
  ring_simplify (1 + (mag r4 (x) - 1))%Z.
  now apply Rlt_le, bpow_mag_gt.
assert (s2q : sqrt x2 = sqrt (x) * bpow r2 (- e)).
  unfold x2; rewrite sqrt_mult, Zopp_mult_distr_r, <- bpow_square;
    [ | lra | apply bpow_ge_0].
  now rewrite sqrt_pow2 by apply bpow_ge_0.
assert (y2close : 
   sqrt x2 - 16 * ulp1 * sqrt x2 <= y2 <= sqrt x2 + 16 * ulp1 * sqrt x2).
  rewrite s2q, <- !Rmult_assoc, <- Rmult_minus_distr_r, <- Rmult_plus_distr_r.
  split; apply Rmult_le_compat_r; try apply bpow_ge_0; lra.
assert (s2bnds : 1 <= sqrt x2 <= 2) by (apply sqrt_1_4; lra).
assert (ybnds : / 2 * sqrt x2 <= y2 <= 2 * sqrt x2).
  split;apply Rlt_le;[apply Rlt_le_trans with (2 := proj1 y2close);
         apply sub_16_ulp_2; lra|
         apply Rle_lt_trans with (1 := proj2 y2close);
         apply add_16_ulp_2; lra].
assert (mx'bound : (2 < mag r2 (x) < 127)%Z).
  split.
    apply mag_gt_bpow; simpl; rewrite Rabs_pos_eq; lra.
  enough (mag r2 x <= 126)%Z by lia.
  apply mag_le_bpow; auto; rewrite Rabs_pos_eq by lra.
  replace (bpow r2 126) with (B2R' predf32max);[lra | ].
  unfold B2R'; rewrite predf32max_val, <- bpow_plus; reflexivity.
assert ((2 > 0)%Z /\ (0 < 2)%Z) as [twogt0 twogt0'] by lia.
assert (ediv2 : e = (mag_val _ _ (mag r2 (x)) / 2 +
                     mag_val _ _ (mag r2 (x)) mod 2 - 1)%Z).
  unfold e; apply f_equal with (f := fun a => (a - 1)%Z).
  apply mag_unique; rewrite Rabs_pos_eq by lra.
  destruct (mag r2 (x)) as [v vp].
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
    rewrite bpow_plus; replace (bpow r2 (-(1))) with (/ 2) by (compute; lra).
    lra.
  rewrite odd in veq |- *.
  rewrite Z.mul_sub_distr_l, !Z.mul_add_distr_l.
  replace (2 * (v / 2) + 2 * 1 - 2 * 1)%Z with (v - 1)%Z
      by (rewrite veq at 1; ring).
  replace (2 * (v / 2) + 2 * 1)%Z with (v + 1)%Z
      by (rewrite veq at 1; ring).
  split;[lra | rewrite bpow_plus; replace (bpow r2 1) with 2 by (compute; lra)].
  lra.
assert (-23 <= (cexp' x2) <= -21)%Z.
  apply cexp_1_8; lra.
assert (ege1 : (1 <= e <= 64)%Z).
  destruct (Z.eq_dec (mag r2 (x)) 3) as [mx3 | mxgt3].
    rewrite mx3 in ediv2; simpl in ediv2; lia.
  assert (2 <= mag r2 x / 2)%Z.
    change 2%Z with (4 / 2)%Z; apply Z_div_le;[reflexivity | lia].
  assert (mag r2 x / 2 <= 63)%Z.
    change 63%Z with (127 / 2)%Z; apply Z_div_le;[reflexivity | lia].
  enough (0 <= mag r2 (x) mod 2 < 2)%Z by lia.
  assert (tmp := Z.mod_pos_bound (mag r2 (x)) 2); lia.
assert (cx'bounds : (-149  < 2 * e + cexp' x2)%Z) by lia.
assert (egt : (-125 < e)%Z) by lia.
exists e, x2, y2.
split;[easy | ].
split;[easy | ].
split;[easy | ].
split;[easy | ].
split;[easy | ].
generalize (body_exp_value_scale x2 y2 e inx2 ybnds egt cx'bounds).
rewrite <- yval, <- xval; symmetry; tauto.
Qed.

Section interval_1_max.

Variable x : float32.

Hypothesis intx : 1 <= B2R' x < / 2 * B2R' predf32max.

Lemma invariant_spec_1_max  x' y :
       Bcompare 24 128 (body_exp x' y) y = Some Lt ->
       invariant x (x', y) -> invariant x (x', body_exp x' y).
Proof.
unfold invariant, invariantR.
destruct (Rle_lt_dec (B2R' x) 4) as [xle4 | xgt4].
  intros _; apply invariant_spec_1_4; lra.
assert (ulp1_small : 0 < ulp1 < / 1024) by (compute; lra).
assert (sge0 : 1 <= sqrt (B2R' x)).
  now rewrite <- sqrt_1; apply sqrt_le_1_alt.
assert (sxh : sqrt (B2R' x) < B2R' x / 2).
  apply sqrt_above_4_lb; assumption.
intros test [cnd1 cnd2]; simpl in cnd1; rewrite cnd1 in cnd2 |- *.
cbv [snd] in cnd2; clear cnd1.
assert (ry : round' (B2R' y) = B2R' y) by (apply round_B2R').
assert (maxval : B2R' predf32max = 2 ^ 126).
  unfold B2R'; rewrite predf32max_val; compute; lra.
assert (0 < B2R' y).
  apply Rlt_le_trans with (2 := proj1 cnd2).
  rewrite <- (Rmult_1_l (sqrt (B2R' x))) at 1.
  rewrite <- Rmult_minus_distr_r; apply Rmult_lt_0_compat;[compute|]; lra.
assert (inx' : 1 <= B2R' x <= B2R' predf32max).
  rewrite maxval in intx |- *; lra.
cbv [snd] in cnd2.
assert (xfar : sqrt (B2R' x) + 5 * ulp1 * sqrt (B2R' x) <= B2R' x).
  apply Rle_trans with (sqrt (B2R' x) + 16 * ulp1 * sqrt (B2R' x));[nra | ].
  apply Rlt_le, Rlt_le_trans with (1 := add_16_ulp_2 _ sge0); lra.
assert (inx2 : / 2 <= B2R' x < / 2 * B2R' predf32max) by lra.
assert (iny2 : / 2 <= B2R' y <= B2R' predf32max).
  split; [| lra].
  apply Rle_trans with (2:= proj1 cnd2).
  apply Rlt_le, Rle_lt_trans with (2 := sub_16_ulp_2 _ sge0); lra.
destruct (Rle_lt_dec (sqrt (B2R' x) + 16 * bpow r2 (- (23)) * sqrt (B2R' x))
             (B2R' y)) as [ybig | yclose].
  unfold invariant;split;[easy | cbv [snd] in cnd2 |- *].
  rewrite body_exp_val; try lra.
  destruct (body_exp_decrease16' _ _ ry inx' (conj ybig (proj2 cnd2)))
      as [lb  ub].
  rewrite Rmult_minus_distr_l, Rmult_1_r, (Rmult_comm (sqrt _)) in lb.
  split; [exact lb | apply Rle_trans with (2 := (proj2 cnd2)) ].
  apply Rlt_le; exact ub.
destruct (scale_data _ _ (conj (Rlt_le _ _ xgt4) (Rlt_le _ _ (proj2 intx)))
              (conj (proj1 cnd2) (Rlt_le _ _ yclose))) as
    [e [x2 [y2 [intx2 [inty2 [xval [yval [ege1 bval']]]]]]]].
assert (ints2 := sqrt_1_4 _ intx2).
split;[easy | ].
assert (sval : sqrt (B2R' x) =  bpow r2 e * sqrt x2).
  rewrite xval, sqrt_mult, <- bpow_square;[ | lra | apply bpow_ge_0].
  rewrite sqrt_pow2, Rmult_comm;[easy | apply bpow_ge_0].
cbn [snd].
rewrite body_exp_val; try lra.
fold (body_exp_R (B2R' x) (B2R' y)); rewrite bval'.
assert (tmp := converge_below_16 x2 y2 intx2 inty2).
fold (body_exp_R x2 y2) in tmp.
rewrite sval, (Rmult_comm (bpow _ _)), <- Rmult_assoc, <- Rmult_minus_distr_r.
split.
  apply Rmult_le_compat_r;[apply bpow_ge_0 | ].
  apply Rle_trans with (sqrt x2 - 5 * ulp1);[ | lra ].
  apply Rplus_le_compat_l, Ropp_le_contravar.
  rewrite <- (Rmult_1_r (_ * _)) at 1; apply Rmult_le_compat; lra.
apply Rle_trans with (2 * sqrt (B2R' x));[ | lra].
rewrite sval, (Rmult_comm (bpow _ _)), <- Rmult_assoc.
apply Rmult_le_compat_r;[apply bpow_ge_0 | lra].
Qed.

Lemma invariant_final_1_max x' y :
  invariant x (x', y) ->
  Bcompare 24 128 (body_exp x y) y <> Some Lt ->
  final x (body_exp x' y).
Proof.
unfold invariant, invariantR.
destruct (Rle_lt_dec (B2R' x) 4) as [xle4 | xgt4].
  apply invariant_final; auto; lra.
assert (ulp1_small : 0 < ulp1 < / 1024) by (compute; lra).
assert (sge0 : 1 <= sqrt (B2R' x)).
  now rewrite <- sqrt_1; apply sqrt_le_1_alt.
assert (sxh : sqrt (B2R' x) < B2R' x / 2).
  apply sqrt_above_4_lb; assumption.
intros [cnd1 cnd2] test; simpl in cnd1; rewrite cnd1 in cnd2 |- *.
assert (test' := invariant_test _ intx _ _ (conj cnd1 cnd2) test).
cbv [snd] in cnd2; clear cnd1.
assert (ry : round' (B2R' y) = B2R' y) by (apply round_B2R').
assert (maxval : B2R' predf32max = 2 ^ 126).
  unfold B2R'; rewrite predf32max_val; compute; lra.
assert (0 < B2R' y).
  apply Rlt_le_trans with (2 := proj1 cnd2).
  rewrite <- (Rmult_1_l (sqrt (B2R' x))) at 1.
  rewrite <- Rmult_minus_distr_r; apply Rmult_lt_0_compat;[compute|]; lra.
assert (inx' : 1 <= B2R' x <= B2R' predf32max).
  rewrite maxval in intx |- *; lra.
cbv [snd] in cnd2.
assert (xfar : sqrt (B2R' x) + 5 * ulp1 * sqrt (B2R' x) <= B2R' x).
  apply Rle_trans with (sqrt (B2R' x) + 16 * ulp1 * sqrt (B2R' x)).
    apply Rplus_le_compat_l; apply Rmult_le_compat_r; lra.
  apply Rlt_le, Rlt_le_trans with (1 := add_16_ulp_2 _ sge0); lra.
assert (inx2 : / 2 <= B2R' x < / 2 * B2R' predf32max) by lra.
assert (iny2 : / 2 <= B2R' y <= B2R' predf32max).
  split; [| lra].
  apply Rle_trans with (2:= proj1 cnd2).
  apply Rlt_le, Rle_lt_trans with (2 := sub_16_ulp_2 _ sge0); lra.
destruct (Rle_lt_dec (sqrt (B2R' x) + 16 * bpow r2 (- (23)) * sqrt (B2R' x))
             (B2R' y)) as [ybig | yclose].
  destruct (body_exp_decrease16' _ _ ry inx' (conj ybig (proj2 cnd2)))
      as [lb  ub].
  case test'; cbv [snd]; rewrite body_exp_val; [|lra | lra]. 
  fold (body_exp_R (B2R' x) (B2R' y)); lra.
destruct (scale_data _ _ (conj (Rlt_le _ _ xgt4) (Rlt_le _ _ (proj2 intx)))
              (conj (proj1 cnd2) (Rlt_le _ _ yclose))) as
    [e [x2 [y2 [intx2 [inty2 [xval [yval [ege1 bval']]]]]]]].
unfold final; cbv [snd] in test'.
rewrite body_exp_val in test' |- *;[ | lra | lra | lra | lra].
fold (body_exp_R (B2R' x) (B2R' y)) in test' |- *.
rewrite bval'.
assert (ints2 := sqrt_1_4 _ intx2).
assert (test2 : ~ body_exp_R x2 y2 < y2).
  intros t2; case test'; fold (body_exp_R (B2R' x) (B2R' y)).
  now rewrite bval', yval; apply Rmult_lt_compat_r;[apply bpow_gt_0 | ].
assert (iv2 : invariantR x2 y2).
  split;[lra | ].
  apply Rle_trans with (B2R' y);[ | lra].
  rewrite <- (Rmult_1_r y2), yval; apply Rmult_le_compat_l.
   apply Rle_trans with (2 := proj1 inty2).
   rewrite <- (Rmult_1_l (sqrt _)) at 1.
   rewrite <- Rmult_minus_distr_r; apply Rmult_le_pos;[compute | ]; lra.
  replace 1 with (bpow r2 0) by (compute; lra).
  apply bpow_le; lia.
assert (-24 <= cexp' (B2R' y))%Z.
  apply (cexp_ge_bpow r2 f32_exp (B2R' y) 0).
  replace (bpow r2 (0 - 1)) with (/ 2) by (compute; lra).
  rewrite Rabs_pos_eq; lra.
assert (ry2 : round' y2 = y2).
  assert (y2v : y2 = B2R' y * bpow r2 (-e)).
    rewrite yval, Rmult_assoc, <- bpow_plus, Z.add_opp_diag_r; simpl; ring.
  rewrite y2v, round_mult_bpow, ry; auto; try lra; lia.
assert (sval : sqrt (B2R' x) =  bpow r2 e * sqrt x2).
  rewrite xval, sqrt_mult, <- bpow_square;[ | lra | apply bpow_ge_0].
  rewrite sqrt_pow2, Rmult_comm;[easy | apply bpow_ge_0].
unfold finalR.
rewrite sval, (Rmult_comm (bpow _ _)), <- Rmult_assoc, <-Rmult_minus_distr_r.
rewrite <- Rmult_plus_distr_r.
assert (tmp := converge_below_16 x2 y2 intx2 inty2).
fold (body_exp_R x2 y2) in tmp.
assert (5 * ulp1 <= 5 * ulp1 * sqrt x2).
  rewrite <- (Rmult_1_r (_ * _)) at 1.
  apply Rmult_le_compat; lra.
split; apply Rmult_le_compat_r; try apply bpow_ge_0; lra.
Qed.

Lemma invariant_initial_1_max : invariant x (x, x).
Proof.
  assert (1 <= sqrt (B2R' x)).
    now rewrite <- sqrt_1; apply sqrt_le_1_alt.
split;[reflexivity | ]; simpl; split.
  apply Rle_trans with (sqrt (B2R' x)).
    rewrite <- (Rmult_1_l (sqrt (B2R' x))) at 1 3.
    rewrite <- Rmult_minus_distr_r; apply Rmult_le_compat_r;[ | compute]; lra.
  rewrite <- (Rmult_1_r (sqrt (B2R' x))).
  rewrite <- (sqrt_sqrt (B2R' x)) at 2 by lra.
  apply Rmult_le_compat_l; lra.
lra.
Qed.

Lemma main_loop_1_max :
  final x (main_loop (x, x)).
generalize invariant_initial_1_max.
apply main_loop_ind.
  now intros p x' y pxy z test IH v; apply IH, invariant_spec_1_max.
intros p x' y pxy z test vtest cndtest iv. 
apply invariant_final_1_max; auto.
subst z.
destruct iv as [cnd1 cnd2]; rewrite <- cnd1; simpl; rewrite vtest.
destruct test as [c |] eqn: tq; try discriminate.
destruct c; try discriminate; contradiction.
Qed.

End interval_1_max.

Lemma main_loop_correct_1_max x :
  1 <= B2R 24 128 x < /2 * B2R 24 128 predf32max ->
  Rabs (B2R 24 128 (main_loop (x, x)) - sqrt (B2R 24 128 x)) <=
       5 / (2 ^ 23) * sqrt (B2R 24 128 x).
Proof.
set (s := sqrt _); set (m := B2R _ _ (main_loop _)); set (e := _ / _ * _).
intros intx; apply Rabs_le.
enough (s - e <= m <= s + e) by lra.
replace e with (5 * ulp1 * s); cycle 1.
   unfold e, ulp1, s; rewrite bpow_opp; compute; lra.
now apply main_loop_1_max.
Qed.

End NAN.

Definition dummy_nan (x y : float32) :=
  exist (fun e => is_nan _ _ e = true) (B754_nan 24 128 false 1 eq_refl)
        eq_refl.

Open Scope R_scope.
Lemma fsqrt_correct_aux0:
 forall x, 
  1 <= Binary.B2R 24 128 x < Rdefinitions.Rinv 2 * Binary.B2R 24 128 predf32max ->
  Binary.Bcompare 24 128 x (Binary.B754_zero 24 128 false) = Some Gt.
Proof.
intros x [xge1 _].
rewrite Bcompare_correct; auto.
apply f_equal; simpl; apply Rcompare_Gt; lra.
destruct x; auto; simpl in xge1; lra.
Qed.

Lemma fsqrt_correct_aux1:
 forall x, 
  1 <= Binary.B2R 24 128 x < Rdefinitions.Rinv 2 * Binary.B2R 24 128 predf32max ->
  Binary.Bcompare 24 128 x (Binary.Bone 24 128 (eq_refl _) (eq_refl _)) = Some Gt \/
  Binary.Bcompare 24 128 x (Binary.Bone 24 128 (eq_refl _) (eq_refl _)) = Some Eq.
intros x [[xgt1 | xeq1] _].
  left.
  rewrite Bcompare_correct;[ |  | auto].
  apply f_equal; apply Rcompare_Gt.
  rewrite Bone_correct; assumption.
  destruct x; simpl in xgt1; auto; lra.
right.
rewrite Bcompare_correct;[ |  | auto].
apply f_equal; apply Rcompare_Eq.
rewrite Bone_correct; symmetry; assumption.
destruct x; simpl in xeq1; auto; lra.
Qed.

Require Import compcert.lib.Floats.
Require Import compcert.lib.Axioms.
Import Integers.

Definition float32_to_real := Binary.B2R 24 128.

Lemma Float32_cmp_eq: forall x y, Float32.cmp Clt x y = 
  match Binary.Bcompare 24 128 x y with Some Lt => true | _ => false end.
Proof.
intros.
Transparent Float32.cmp.
reflexivity.
Opaque Float32.cmp.
Qed.

Lemma Float32_add_eq: Float32.add = float_add Float32.binop_nan .
Proof.
Transparent Float32.add.
unfold Float32.add, float_add.
Opaque Float32.add.
do 2 (apply extensionality; intro); auto.
Qed.

Lemma Float32_div_eq: Float32.div = float_div Float32.binop_nan .
Proof.
Transparent Float32.div.
unfold Float32.div, float_div.
Opaque Float32.div.
do 2 (apply extensionality; intro); auto.
Qed.

Lemma Float32_of_int_2_eq: Float32.of_int (Int.repr 2) = float2.
Proof.
Transparent Float32.of_int.
unfold Float32.of_int, float2.
Opaque Float32.of_int.
change (Int.signed (Int.repr 2)) with 2%Z.
unfold IEEE754_extra.BofZ.
simpl.
apply f_equal.
apply proof_irr.
Qed.

Definition fsqrt (x: float32) : float32 :=
  if Float32.cmp Cle x (Float32.of_int (Int.repr 0)) 
  then (Float32.of_int (Int.repr 0)) 
  else
  let y := if Float32.cmp Cge x (Float32.of_int (Int.repr 1))
               then x else Float32.of_int (Int.repr 1)  in
  main_loop Float32.binop_nan (x,y).

Open Scope R_scope.


Lemma fsqrt_correct:
 forall x, 
  1 <= float32_to_real x < Rdefinitions.Rinv 2 * float32_to_real predf32max ->
  Rbasic_fun.Rabs (float32_to_real (fsqrt x) - R_sqrt.sqrt (float32_to_real x)) <=
       5 / (2 ^ 23) * R_sqrt.sqrt (float32_to_real x).
Proof.
intros.
unfold fsqrt.
change (Float32.of_int (Int.repr 0)) with (Binary.B754_zero 24 128 false).
change (Float32.of_int (Int.repr 1)) with (Binary.Bone 24 128 (eq_refl _) (eq_refl _)).
Transparent Float32.cmp.
unfold Float32.cmp.
Opaque Float32.cmp.
unfold Float32.compare.
unfold cmp_of_comparison.
rewrite fsqrt_correct_aux0 by auto.
destruct (fsqrt_correct_aux1 x H).
rewrite H0 by auto.
apply main_loop_correct_1_max; auto.
rewrite H0 by auto.
apply main_loop_correct_1_max; auto.
Qed.
Close Scope R_scope.



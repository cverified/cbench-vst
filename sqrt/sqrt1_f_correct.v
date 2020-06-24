From Flocq Require Core Binary.
From Coquelicot Require Import Coquelicot.
Require Import Reals Gappa.Gappa_library Psatz.
Import Defs Raux FLT Generic_fmt Gappa_definitions Binary Ulp.
Require Import FunInd Recdef.

Require Import float_lemmas.
Require Import sqrt1_f.
Require from_g.  (* This file is generated from sqrt1.g *)


Definition float2 := float_of_Z 2.

Definition body_exp x y := float_div (float_plus y (float_div x y)) float2.

Notation f_exp := (FLT_exp fmin ms).

Definition round' x := round radix2 f_exp (round_mode mode_NE) x.

Notation r2 := Gappa_definitions.radix2.

Notation cexp' := (cexp r2 f_exp).

Open Scope R_scope.

Lemma Rdiv_1_r x : x / 1 = x.
Proof.
now unfold Rdiv; rewrite Rinv_1, Rmult_1_r.
Qed.

Lemma Rdiv_cancel x y : y <> 0 -> x / y * y = x.
Proof.
intro yn0; unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r; lra.
Qed.

Lemma Rdiv_le_swap_lr x y z : 0 < y -> x <= z * y -> x / y <= z.
Proof.
intros y0 cnd; apply Rmult_le_reg_r with y;[lra | ].
rewrite Rdiv_cancel; lra.
Qed.

Lemma Rdiv_le_swap_rl x y z : 0 < y -> x * y <= z -> x <= z / y.
Proof.
intros y0 cnd; apply Rmult_le_reg_r with y;[lra | ].
rewrite Rdiv_cancel; lra.
Qed.

Lemma Rdiv_lt_swap_lr x y z : 0 < y -> x < z * y -> x / y < z.
Proof.
intros y0 cnd; apply Rmult_lt_reg_r with y;[lra | ].
rewrite Rdiv_cancel; lra.
Qed.

Lemma Rdiv_lt_swap_rl x y z : 0 < y -> x * y < z -> x < z / y.
Proof.
intros y0 cnd; apply Rmult_lt_reg_r with y;[lra | ].
rewrite Rdiv_cancel; lra.
Qed.

Lemma Rabs_div x y : y <> 0 -> Rabs (x / y) = Rabs x / Rabs y.
Proof.
now intros yn0; unfold Rdiv; rewrite Rabs_mult, Rabs_Rinv.
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
  sqrt x - 32 * bpow r2 (- ms') <= y <= sqrt x + 3 ->
  - (9) * bpow r2 (- (ms)) <= round' (round'(y + round' (x / y)) / 2) -
   (y + (x / y)) / 2 <=
  9 * bpow r2 (- (ms)).
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
assert (- (32) * bpow r2 (- ms') <= e <= 3) by (unfold e; lra).
generalize (from_g.l1 b e).
unfold from_g.s1, from_g.s2, from_g.s3, from_g.i1, from_g.i2, from_g.i3, BND.
fold ms fmin.
cbv [lower upper].
change rndNE with (round_mode mode_NE).
replace (float2R from_g.f1) with 1 by (compute; lra).
replace (float2R from_g.f2) with 2 by (compute; lra).
replace (float2R from_g.f3) with (- (32) * bpow r2 (- ms')) by (compute; lra).
replace (float2R from_g.f4) with 3 by (compute; lra).
replace (float2R from_g.f5) with (-9 * bpow r2 (- (ms))) by (compute; lra).
replace (float2R from_g.f6) with (9 * bpow r2 (- (ms))) by (compute; lra).
change (Float1 2) with 2.
change (round r2 f_exp (round_mode mode_NE)
     (round r2 f_exp (round_mode mode_NE)
        (b + e + round r2 f_exp (round_mode mode_NE) (b * b / (b + e))) /
      2)) with
 (round' (round' ((b + e) + round' (b * b / (b + e))) / 2)).
lra.
Qed.

Lemma fminlt1 : bpow radix2 fmin < 1.
Proof.
change 1 with (bpow radix2 0); apply bpow_lt; reflexivity.
Qed.

Lemma least_sqrt x :
  bpow radix2 fmin <= x ->
  bpow radix2 (1 - halfes - halfms) < sqrt x.
Proof.
intros xgmin.
assert (sqrte : bpow radix2 (1 - halfes - halfms) =
          sqrt (bpow radix2 (- (es + ms - 2)))).
  symmetry; apply sqrt_lem_1.
      now apply bpow_ge_0.
    now apply bpow_ge_0.
 rewrite <- bpow_plus; apply f_equal; reflexivity.
rewrite sqrte; apply sqrt_lt_1_alt; split;[apply bpow_ge_0 | ].
now apply Rlt_le_trans with (2 := xgmin); apply bpow_lt.
Qed.

Definition B2R' x := B2R ms es x.

Open Scope Z_scope.

Open Scope R_scope.

Definition ulp1 := bpow radix2 (- ms').

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
assert (inty' : sqrt x - 32 * bpow r2 (- ms') <= y <= sqrt x + 3)
  by (fold ulp1; nra).
assert (inty2 : sqrt x + 2 * (8 * bpow r2 (- ms')) <= y)
  by (fold ulp1; nra).
assert (tmp2 := pure_decrease_2u 1 _ x y Rlt_0_1 xgt0 sg1 ugt0 inty2).
assert (9 * bpow r2 (- (ms)) < 16 * ulp1) by (compute; lra).
assert (tmp' := tmp inty').
split.
  apply Rle_trans with ((y + x / y) / 2 - 9 * bpow r2 (- (ms))); lra.
apply Rle_lt_trans with ((y + x / y) / 2 + 9 * bpow r2 (-(ms)));[lra | ].
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
assert (bigy : sqrt x - 32 * bpow r2 (- ms') <= y <= sqrt x + 3).
  split.
    apply Rle_trans with (2 := proj1 inty).
    apply Rplus_le_compat_l, Ropp_le_contravar.
    replace (32 * bpow r2 (- ms')) with (16 * bpow r2 (- ms') * 2) by ring.
    apply Rmult_le_compat_l;[compute | ]; lra.
  apply Rle_trans with (1 := proj2 inty); apply Rplus_le_compat_l.
  apply Rle_trans with (16 * ulp1 * 2);[ | compute; lra].
  apply Rmult_le_compat_l;[compute | ]; lra.
assert (ygt0 : / 2 < y).
  apply Rlt_le_trans with (2 := proj1 bigy).
  apply Rlt_le_trans with (1 - 32 * bpow r2 (- ms')).
    compute; lra.
  now apply Rplus_le_compat_r.
assert (tmp := from_g_proof x y intx bigy).
assert (ulp1 = 2 * bpow r2 (- (ms))) by (unfold ulp1; simpl; lra).
enough (-bpow r2 (- (ms)) <= (y + (x / y)) / 2 - sqrt x <= bpow r2 (- (ms)))
  by lra.
rewrite <- (sqrt_sqrt x) at 1 3 by lra.
replace ((y + (sqrt x * sqrt x) / y) / 2 - sqrt x) with
   ((y - sqrt x) ^ 2 / (2 * y)) by (field; lra).
apply Rabs_le_inv; rewrite Rabs_pos_eq; cycle 1.
  apply Rmult_le_pos;[apply pow2_ge_0 | apply Rlt_le, Rinv_0_lt_compat]; lra.
apply Rle_trans with ((y - sqrt x) ^ 2 / 1).
apply Rmult_le_compat_l;[apply pow2_ge_0 | apply Rinv_le_contravar;lra].
rewrite Rdiv_1_r.
replace (bpow r2 (- (ms))) with (bpow r2 (-(12)) ^ 2) by (compute; lra).
assert (ulp1 = bpow r2 (- ms')) by reflexivity.
destruct (Rle_dec y (sqrt x)).
  replace ((y - sqrt x) ^ 2) with ((sqrt x - y) ^ 2) by ring.
  apply pow_incr; split;[lra | ].
  apply Rle_trans with (32 * bpow r2 (- ms'));[ |compute]; nra.
apply pow_incr; split;[lra | ].
apply Rle_trans with (32 * bpow r2 (- ms'));[ | compute]; nra.
Qed.

Section From_floating_point_numbers_to_reals.

Definition f_min : float :=
  B754_finite ms es false 1 fmin eq_refl.

Lemma f_min_val : B2R' f_min = bpow r2 fmin.
Proof. compute; lra. Qed.

Lemma round_B2R' x : round' (B2R' x) = B2R' x.
Proof.
assert (tmp := generic_format_FLT radix2 _ ms _
                   (FLT_format_B2R ms es eq_refl x)).
now apply round_generic;[ apply valid_rnd_round_mode | exact tmp ].
Qed.

Lemma round_bpow e : (fmin <= e < es)%Z -> round' (bpow r2 e) = bpow r2 e.
Proof.
intros inte.
destruct (Z.eq_dec fmin e) as [bottom | nobottom].
  now rewrite <- bottom, <- f_min_val, round_B2R'.
destruct (Z_le_dec (2 - es) e) as [normal | subnormal].
  set (m := (2 ^ match ms' with Z.pos v => v |_ => 1 end)%positive).
  assert (bprf : Binary.bounded ms es m (e - ms') = true).
    unfold Binary.bounded, canonical_mantissa.
    rewrite andb_true_iff; split; cycle 1.
      rewrite <- Zle_is_le_bool; unfold fmin, es, ms', ms in inte, normal|- *.
      lia.
    assert (vm : Z.pos (Digits.digits2_pos m) = ms) by reflexivity.
    rewrite vm; unfold FLT_exp.
    apply Zeq_bool_true; rewrite Zmax_left; [ring | ].
    unfold fmin, ms', ms, es in inte, normal |- *; lia.
  assert (v : bpow r2 e = B2R'
           (B754_finite ms es false
               (2 ^ match ms' with Z.pos v => v | _ => 1 end)
               (e - ms') bprf)).
    unfold B2R', B2R, F2R; simpl Defs.Fnum; simpl Defs.Fexp.
    rewrite Pos2Z.inj_pow_pos, IZR_Zpower_pos.
    rewrite <- (bpow_powerRZ r2), <- bpow_plus; apply f_equal.
    unfold ms', ms; ring.
  now rewrite v; apply round_B2R'.
assert (bprf : Binary.bounded ms es (Z.to_pos (2 ^ (e - fmin))) fmin = true).
  unfold Binary.bounded, canonical_mantissa, FLT_exp.
  rewrite Z2Pos.inj_pow; try lia.
  rewrite Digits.Zpos_digits2_pos, <- Z2Pos.inj_pow, Z2Pos.id; cycle 1.
        apply (Zpower_gt_0 r2); unfold fmin in inte |- *; lia.
      lia.
    lia.
  rewrite andb_true_iff; split;[ | reflexivity].
  apply Zeq_bool_true.
  rewrite Digits.Zdigits_Zpower; try lia.
  rewrite Zmax_right;[unfold fmin, ms, es; ring | ].
  unfold fmin, ms, es in inte, nobottom, subnormal |- *; lia.
set (v := B754_finite ms es false _ fmin bprf).
assert (ev : bpow r2 e = B2R' v).
  unfold B2R', B2R; simpl; unfold F2R, Defs.Fnum, Defs.Fexp.
  rewrite Z2Pos.id; cycle 1. 
    apply (Zpower_gt_0 r2); lia.
  rewrite <- (Z2Nat.id (e - fmin)); try lia.
  rewrite <- pow_IZR, pow_powerRZ, Z2Nat.id; try lia.
  rewrite <- (bpow_powerRZ r2), <- bpow_plus; apply f_equal; ring.
now rewrite ev, round_B2R'.
Qed.

Lemma round'1 : round' 1 = 1%R.
Proof. apply (round_bpow 0); unfold fmin, es; lia. Qed.

Lemma round'2 : round' 2 = 2%R.
Proof. apply (round_bpow 1); unfold fmin, es; lia. Qed.

Lemma round'h : round' (/ 2) = (/ 2)%R.
Proof. apply (round_bpow (- 1)); unfold fmin, es; lia. Qed.

Lemma round'q : round' (/4) = (/4)%R.
Proof.  apply (round_bpow (- 2)); unfold fmin, es; lia. Qed.

Lemma round'4 : round' 4 = 4%R.
Proof. apply (round_bpow 2); unfold fmin, es; lia. Qed.

Lemma round'65 : round' (bpow r2 (halfes  + 1)) = bpow r2 (halfes + 1).
Proof.
apply round_bpow; unfold fmin, es, halfes; lia.
Qed.

Lemma round_le' (x y : R) : (x <= y)%R -> (round' x <= round' y)%R.
Proof.
intros xley.
apply round_le; auto.
  now apply (fexp_correct ms es).
now apply valid_rnd_round_mode.
Qed.

Lemma round1 m: round radix2 f_exp (round_mode m) 1 = 1%R.
Proof.
assert (for1 : generic_format radix2 f_exp 1).
  replace 1%R with (F2R (Float radix2 (cond_Zopp false (2 ^ 23)) (-23))).
    now apply generic_format_canonical, (canonical_canonical_mantissa 24 128).
  compute; lra.
now apply round_generic; auto; apply valid_rnd_round_mode.
Qed.

Definition f_max : float :=
    B754_finite ms es false
    (2 ^ match ms with Z.pos v => v | _ => 1 end - 1) (es - ms) eq_refl.

Lemma f32maxgt1 : 1 < B2R' f_max.
Proof.
compute; lra.
Qed.

(* a conservative bound that can be improved. *)
Definition predf_max : float :=
    B754_finite ms es false
     (2 ^ match ms' with Z.pos v => v | _ => 1 end) (es - ms - 1) eq_refl.

Lemma predf_max_val : B2R ms es predf_max =
  ((bpow radix2 ms') * bpow radix2 (es - ms - 1))%R.
Proof.
unfold B2R, F2R, Fexp; simpl.
rewrite Pos2Z.inj_pow.
now rewrite !Z.pow_pos_fold.
Qed.

Lemma boundf_max : (1 < B2R' f_max < bpow radix2 es)%R.
Proof.
compute; lra.
Qed.

Lemma predf_maxgt1 : 1 + 16 * ulp1 < B2R' predf_max.
Proof. compute; lra. Qed.

Lemma boundpredf_max : (2 * B2R' predf_max <= B2R' f_max)%R.
Proof.
compute; lra.
Qed.

Definition body_exp_R x y := round' (round' (y + round' (x / y)) / 2).

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

Lemma body_exp_div_x_y_bounds1' x y :
  bpow r2 fmin <= x < 1 -> bpow r2 (2 - es) <= y <= 2 ->
  0 < x / y <= B2R' predf_max.
Proof.
intros intx inty.
assert (xgt0 : 0 < x).
  now apply Rlt_le_trans with (2 := proj1 intx), bpow_gt_0.
assert (ygt0 : 0 < y).
  now apply Rlt_le_trans with (2 := proj1 inty), bpow_gt_0.
split.
  apply Rdiv_lt_swap_rl; lra.
apply Rdiv_le_swap_lr;[lra | ].
unfold B2R'; rewrite predf_max_val, <- bpow_plus.
replace (ms' + (es - ms - 1))%Z with (es - 2)%Z by (unfold ms'; ring).
apply Rle_trans with (bpow r2 (es - 2) * bpow r2 (2 - es)).
  rewrite <- bpow_plus.
  replace (es - 2 + (2 - es))%Z with (0)%Z by ring.
  simpl; lra.
apply Rmult_le_compat_l;[apply bpow_ge_0 | ]; tauto.
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
  rewrite <- (round_0 radix2 f_exp (round_mode mode_NE)).
  now apply round_le'; lra.
apply round_le'; tauto.
Qed.

Lemma body_exp_div_x_y_bounds' x y :
  bpow r2 fmin <= x < 1 -> bpow r2 (2 - es) <= y <= 2 ->
  0 <= round' (x / y) <= B2R' predf_max.
Proof.
intros intx inty.
assert (xgt0 : 0 < x).
  now apply Rlt_le_trans with (2 := proj1 intx), bpow_gt_0.
assert (ygt0 : 0 < y).
  now apply Rlt_le_trans with (2 := proj1 inty), bpow_gt_0.
split.
  rewrite <- (round_0 radix2 f_exp (round_mode mode_NE)).
  now apply round_le', Rlt_le, Rdiv_lt_0_compat.
rewrite <- round_B2R'.
apply round_le'.
assert (tmp := body_exp_div_x_y_bounds1' _ _ intx inty); tauto.
Qed.

(* The upper constraint on x is too strict, but good enough for now. *)
Lemma body_exp_sum_bounds x y :
  (/ 2 <= x <  / 2 * B2R' predf_max)%R ->
  (/ 2 <= y <= B2R' predf_max)%R ->
  (/ 2 <= round' (y + round' (x / y)) <= B2R' f_max)%R.
Proof.
intros intx inty.
assert (int1 : (0 <= round' (x / y) <= round' (2 * x))%R).
  now apply body_exp_div_x_y_bounds.
destruct (Rlt_le_dec x (bpow radix2 halfes)) as [xlow | xhigh].
  split.
    rewrite <- round'h.
    apply round_le'; lra.
  assert (r2xb : round' (2 * x) <= bpow r2 (halfes + 1)).
    rewrite <- round'65.    
    apply round_le'.
    replace (bpow r2 (halfes + 1)) with (2 * bpow r2 halfes);[| compute]; lra.
  apply Rle_trans with (bpow r2 (es - 1))%R;[ | compute; lra].
  rewrite <- round_bpow;[ | unfold fmin, es; lia].
  apply round_le'.
  apply Rle_trans with (B2R' predf_max + bpow r2 (halfes + 1));
         [ | compute; lra].
  lra.
rewrite <- round'h, <- round_B2R'.
assert (sqrtemax : sqrt (bpow radix2 es) = bpow radix2 (halfes)).
  apply sqrt_lem_1; try apply bpow_ge_0.
  now rewrite <- bpow_plus.
destruct (Rlt_le_dec y (sqrt x)) as [ylow | yhigh].
  assert (y < bpow radix2 (halfes))%R.
    apply Rlt_trans with (1 := ylow).
    rewrite <-sqrtemax.
    apply sqrt_lt_1_alt.
    split; [ lra | ].
    apply Rlt_trans with (1 := proj2 intx).
    compute; lra.
  split; apply round_le'; try lra.
  apply Rle_trans with (bpow radix2 (halfes) + B2R' predf_max)%R; cycle 1.
    compute; lra.
    apply Rplus_le_compat; [lra | ].
  apply Rle_trans with (1 := proj2 int1).
  rewrite <- round_B2R'; apply round_le'; lra.
split; apply round_le'; try lra.
assert (0 < sqrt x)%R.
  apply sqrt_lt_R0; lra.
assert (divsqrt : (x / y <= sqrt x)%R).
  apply Rdiv_le_swap_lr;[lra | ].
    rewrite <- (sqrt_sqrt x) at 1;[ | lra].
    now apply Rmult_le_compat_l;[lra | ].
apply Rle_trans with (B2R' predf_max + bpow radix2 (halfes))%R.
  apply Rplus_le_compat;[lra | ].
  rewrite <- round_bpow;[ | unfold fmin, halfes, es; lia].
  apply round_le'.
  apply Rle_trans with (1 := divsqrt).
  rewrite <- sqrtemax; apply Rlt_le, sqrt_lt_1_alt; split;[lra | ].
  apply Rlt_trans with (2 := (proj2 boundf_max)).
  assert (tmp := boundpredf_max); lra.
compute; lra.
Qed.

Lemma body_exp_sum_bounds' x y :
  round' y = y ->
  bpow r2 fmin <= x < 1 -> bpow r2 (2 - es) <= y <= 2 ->
  (y <= round' (y + round' (x / y)) <= B2R' f_max)%R.
Proof.
intros ry intx inty.
assert (int1 : (0 <= round' (x / y) <= B2R' predf_max)%R).
  now apply body_exp_div_x_y_bounds'.
rewrite <- ry at 1; split;[apply round_le'; lra | ].
rewrite <- round_B2R'; apply round_le'.
apply Rle_trans with (2 := boundpredf_max).
rewrite double; apply Rplus_le_compat;[ | tauto].
apply Rle_trans with (1 := proj2 inty); compute; lra.
Qed.

Lemma body_exp_bounds x y :
  (/ 2 <= x < / 2 * B2R' predf_max)%R ->
  (/ 2 <= y <= B2R' predf_max)%R -> /4 <= body_exp_R x y <= B2R' f_max.
Proof.
intros intx inty.
assert ((/ 2 <= round' (y + round' (x / y)) <= B2R' f_max)%R).
  now apply body_exp_sum_bounds.
unfold body_exp_R.
rewrite <- round'q, <- round_B2R'.
split.
  apply round_le'; lra.
apply round_le'; lra.
Qed.

Lemma body_exp_bounds' x y :
  round' y = y ->
  bpow r2 fmin <= x < 1 -> bpow r2 (2 - es) <= y <= 2 ->
  (bpow r2 (1 - es) <= round' (round' (y + round' (x / y)) / 2) <=
      B2R' f_max)%R.
Proof.
intros ry intx inty.
assert (int1: y <= round' (y + round' (x / y)) <= B2R' f_max).
  now apply body_exp_sum_bounds'.
split.
  rewrite <- round_bpow;[ | unfold fmin, es; lia].
  apply round_le'.
  apply Rle_trans with (y / 2); cycle 1.
    apply Rmult_le_compat_r;[lra | tauto].
  apply Rdiv_le_swap_rl;[lra |].
  change 2 with (bpow r2 1); rewrite <- bpow_plus.
  replace (1 - es + 1)%Z with (2 - es)%Z by ring; tauto.
rewrite <- round_B2R'; apply round_le'.
enough (0 < y) by lra.
now apply Rlt_le_trans with (2 := proj1 inty); apply bpow_gt_0.
Qed.

Lemma body_exp_finite_value x y :
  is_finite ms es x = true ->
  is_finite ms es y = true ->
  (/ 2 <= B2R' x < / 2 * B2R' predf_max)%R ->
  (/ 2 <= B2R' y <= B2R' predf_max)%R ->
  B2R' (body_exp x y) = round' (round' (B2R' y + round' (B2R' x / B2R' y)) / 2) /\
  is_finite ms es (body_exp x y) = true.
Proof.
intros finx finy intx' inty'.
assert (yn0 : B2R' y <> 0%R) by lra.
unfold body_exp, float_div.
assert (tmp := body_exp_bounds _ _ intx' inty').
assert (tm2 := body_exp_sum_bounds _ _ intx' inty').
assert (tm3 := body_exp_div_x_y_bounds _ _ (proj1 intx') (proj1 inty')).
unfold body_exp_R in tmp, tm2, tm3.
assert (tm4 := Bdiv_correct ms es eq_refl eq_refl binop_nan mode_NE x y yn0).
assert (divlt : Rabs (round' (B2R' x / B2R' y)) < bpow radix2 es).
  rewrite Rabs_pos_eq;[ | lra].
  assert (tmp5:= conj boundpredf_max boundf_max).
  apply Rle_lt_trans with (B2R' predf_max);[ | lra].
  rewrite <- (round_B2R' predf_max).
  apply Rle_trans with (1 := proj2 tm3); apply round_le'; lra.
rewrite Rlt_bool_true in tm4;[ | exact divlt].
destruct tm4 as [vdivxy [findivxy signdivxy]].
clear divlt.
unfold float_plus.
set (divxy := Bdiv ms es eq_refl eq_refl binop_nan mode_NE x y).
fold divxy in signdivxy, findivxy, vdivxy.
fold (B2R' divxy) in vdivxy.
set (divxy' := B2R' divxy); fold divxy' in vdivxy.
assert (findivxy' : is_finite ms es divxy = true).
  now rewrite findivxy, finx.
assert (pluslt : Rabs (round' (B2R' y + divxy')) < bpow radix2 es).
  rewrite vdivxy.
  change (3 - es -ms)%Z with (fmin)%Z.
  fold (B2R' x); fold (B2R' y); fold (round' (B2R' x / B2R' y)).
  rewrite Rabs_pos_eq by lra.
  now assert (tmp5:= conj boundpredf_max boundf_max); lra.
assert (tm6 := Bplus_correct ms es eq_refl eq_refl binop_nan mode_NE y
                     divxy finy findivxy').
rewrite Rlt_bool_true in tm6;[ | exact pluslt].
fold (B2R' divxy) in tm6; fold divxy' in tm6; fold (B2R' y) in tm6.
change (3 - es -ms)%Z with (fmin)%Z in tm6.
fold (round' (B2R' y + divxy')) in tm6.
destruct tm6 as [vsum [finsum signsum]].
assert (fin2 : is_finite ms es float2 = true) by reflexivity.
assert (b2n0 : B2R' float2 <> 0%R) by now compute; lra.
assert (tm4 := Bdiv_correct ms es eq_refl eq_refl binop_nan mode_NE
                   (Bplus ms es eq_refl eq_refl binop_nan mode_NE y
          (Bdiv ms es eq_refl eq_refl binop_nan mode_NE x y))
                   _ b2n0).
  set (bexp :=   Bdiv ms es eq_refl eq_refl binop_nan mode_NE
              (Bplus ms es eq_refl eq_refl binop_nan mode_NE y
                 (Bdiv ms es eq_refl eq_refl binop_nan mode_NE x y))
              float2).
fold bexp in tm4.
set (sum := (Bplus ms es eq_refl eq_refl binop_nan mode_NE y
                       divxy)).
fold divxy sum in vsum, finsum, signsum, tm4.
assert (explt : Rabs (round' (B2R' sum / B2R' float2)) < bpow radix2 es).
  replace (B2R' float2) with 2%R by (now compute; lra).
   fold (B2R' sum) in vsum; rewrite vsum; rewrite vdivxy.
  change (3 - es -ms)%Z with (fmin)%Z; fold (B2R' x) (B2R' y).
   fold (round' (B2R' x / B2R' y)) divxy'.
  rewrite Rabs_pos_eq;[ | lra].
  now assert (tmp5:= conj boundpredf_max boundf_max); lra.
rewrite Rlt_bool_true in tm4;[ | exact explt].
change (3 - es -ms)%Z with (fmin)%Z in tm4.
destruct tm4 as [vexp [finexp signexp]].
replace (B2R' float2) with 2%R in vexp by now compute; lra.
unfold bexp in vexp; rewrite vsum in vexp.
rewrite vdivxy in vexp.
replace (B2R ms es float2) with 2%R in vexp by (compute; lra).
split;[exact vexp | rewrite finsum in finexp;exact finexp].
Qed.

Lemma body_exp_finite_value' x y :
  is_finite ms es x = true ->
  is_finite ms es y = true ->
  bpow r2 fmin <= B2R' x < 1 ->
  bpow r2 (2 - es) <= B2R' y <= 2->
  B2R' (body_exp x y) = round' (round' (B2R' y + round' (B2R' x / B2R' y)) / 2) /\
  is_finite ms es (body_exp x y) = true.
Proof.
intros finx finy intx' inty'.
assert (ygt0 : 0 < B2R' y).
  now apply Rlt_le_trans with (2 := proj1 inty'), bpow_gt_0.
assert (yn0 : B2R' y <> 0%R) by lra.
unfold body_exp, float_div.
assert (tmp := body_exp_bounds' _ _ (round_B2R' _) intx' inty').
assert (tm2 := body_exp_sum_bounds' _ _ (round_B2R' _) intx' inty').
assert (tm3 := body_exp_div_x_y_bounds' _ _ intx' inty').
unfold body_exp_R in tmp, tm2, tm3.
assert (tm4 := Bdiv_correct ms es eq_refl eq_refl binop_nan mode_NE x y yn0).
assert (divlt : Rabs (round' (B2R' x / B2R' y)) < bpow radix2 es).
  rewrite Rabs_pos_eq;[ | lra].
  assert (tmp5:= conj boundpredf_max boundf_max).
  apply Rle_lt_trans with (B2R' predf_max);[ | lra].
  rewrite <- (round_B2R' predf_max).
  rewrite round_B2R'; tauto.
rewrite Rlt_bool_true in tm4;[ | exact divlt].
destruct tm4 as [vdivxy [findivxy signdivxy]].
clear divlt.
unfold float_plus.
set (divxy := Bdiv ms es eq_refl eq_refl binop_nan mode_NE x y).
fold divxy in signdivxy, findivxy, vdivxy.
fold (B2R' divxy) in vdivxy.
set (divxy' := B2R' divxy); fold divxy' in vdivxy.
assert (findivxy' : is_finite ms es divxy = true).
  now rewrite findivxy, finx.
assert (pluslt : Rabs (round' (B2R' y + divxy')) < bpow radix2 es).
  rewrite vdivxy.
  change (3 - es -ms)%Z with (fmin)%Z.
  fold (B2R' x); fold (B2R' y); fold (round' (B2R' x / B2R' y)).
  rewrite Rabs_pos_eq by lra.
  now assert (tmp5:= conj boundpredf_max boundf_max); lra.
assert (tm6 := Bplus_correct ms es eq_refl eq_refl binop_nan mode_NE y
                     divxy finy findivxy').
rewrite Rlt_bool_true in tm6;[ | exact pluslt].
fold (B2R' divxy) in tm6; fold divxy' in tm6; fold (B2R' y) in tm6.
change (3 - es -ms)%Z with (fmin)%Z in tm6.
fold (round' (B2R' y + divxy')) in tm6.
destruct tm6 as [vsum [finsum signsum]].
assert (fin2 : is_finite ms es float2 = true) by reflexivity.
assert (b2n0 : B2R' float2 <> 0%R) by now compute; lra.
assert (tm4 := Bdiv_correct ms es eq_refl eq_refl binop_nan mode_NE
                   (Bplus ms es eq_refl eq_refl binop_nan mode_NE y
          (Bdiv ms es eq_refl eq_refl binop_nan mode_NE x y))
                   _ b2n0).
  set (bexp :=   Bdiv ms es eq_refl eq_refl binop_nan mode_NE
              (Bplus ms es eq_refl eq_refl binop_nan mode_NE y
                 (Bdiv ms es eq_refl eq_refl binop_nan mode_NE x y))
              float2).
fold bexp in tm4.
set (sum := (Bplus ms es eq_refl eq_refl binop_nan mode_NE y
                       divxy)).
fold divxy sum in vsum, finsum, signsum, tm4.
assert (0 < bpow r2 (1 - es)) by apply bpow_gt_0.
assert (explt : Rabs (round' (B2R' sum / B2R' float2)) < bpow radix2 es).
  replace (B2R' float2) with 2%R by (now compute; lra).
   fold (B2R' sum) in vsum; rewrite vsum; rewrite vdivxy.
  change (3 - es -ms)%Z with (fmin)%Z; fold (B2R' x) (B2R' y).
   fold (round' (B2R' x / B2R' y)) divxy'.
  rewrite Rabs_pos_eq;[ | lra].
  now assert (tmp5:= conj boundpredf_max boundf_max); lra.
rewrite Rlt_bool_true in tm4;[ | exact explt].
change (3 - es -ms)%Z with (fmin)%Z in tm4.
destruct tm4 as [vexp [finexp signexp]].
replace (B2R' float2) with 2%R in vexp by now compute; lra.
unfold bexp in vexp; rewrite vsum in vexp.
rewrite vdivxy in vexp.
replace (B2R ms es float2) with 2%R in vexp by (compute; lra).
split;[exact vexp | rewrite finsum in finexp;exact finexp].
Qed.

Lemma body_exp_val' x y:
  bpow r2 fmin <= B2R' x < 1 ->
  bpow r2 (2 - es) <= B2R' y <= 2 ->
  B2R' (body_exp x y) =
  round' (round' (B2R' y + round' (B2R' x / B2R' y )) / 2).
Proof.
intros intx inty.
assert (finx : is_finite ms es x = true).
  destruct x; auto; compute in intx; lra.
assert (finy : is_finite ms es y = true).
  destruct y; auto; compute in inty; lra.
assert (tmp := body_exp_finite_value' x y finx finy intx inty).
tauto.
Qed.

Lemma body_exp_val x y:
  1 <= B2R' x < / 2 * B2R' predf_max -> / 2 <= B2R' y <= B2R' predf_max ->
  B2R' (body_exp x y) =
  round' (round' (B2R' y + round' (B2R' x / B2R' y )) / 2).
Proof.
intros intx inty.
assert (finx : is_finite 24 128 x = true).
  destruct x; auto; compute in intx; lra.
assert (finy : is_finite 24 128 y = true).
  destruct y; auto; compute in inty; lra.
assert (intx' : / 2 <= B2R' x < / 2 * B2R' predf_max).
  lra.
assert (inty' : / 2 <= B2R' y <= B2R' predf_max).
  lra.
assert (tmp := body_exp_finite_value x y finx finy intx' inty').
tauto.
Qed.

Lemma body_exp_finite x y:
  1 <= B2R' x < / 2 * B2R' predf_max -> / 2 <= B2R' y <= B2R' predf_max ->
  is_finite ms es (body_exp x y) = true.
Proof.
intros intx inty.
assert (finx : is_finite ms es x = true).
  destruct x; auto; compute in intx; lra.
assert (finy : is_finite ms es y = true).
  destruct y; auto; compute in inty; lra.
assert (intx' : / 2 <= B2R' x < / 2 * B2R' predf_max).
  lra.
assert (inty' : / 2 <= B2R' y <= B2R' predf_max).
  lra.
assert (tmp := body_exp_finite_value x y finx finy intx' inty').
tauto.
Qed.

End From_floating_point_numbers_to_reals.

Lemma float_bound_ulp x :
  bpow r2 (-(es - 2)) <= x -> 0 < ulp radix2 f_exp x <= x / bpow radix2 ms'.
Proof.
intros intx.
assert (0 < bpow r2 (-(es - 2))) by (simpl; lra).
assert (xn0 : x <> 0%R) by lra.
assert (t := ulp_neq_0 r2 f_exp _ xn0).
rewrite t; unfold cexp.
assert (lbm : (-(es - 3) <= mag_val _ _ (mag r2 x))%Z).
  apply mag_ge_bpow; rewrite Rabs_pos_eq by lra; assumption.
unfold FLT_exp; rewrite Z.max_l; cycle 1.
  unfold fmin, ms, es in lbm |- *; lia.
split;[now apply bpow_gt_0 | ].
apply Rdiv_le_swap_rl;[now apply bpow_gt_0 | ].
rewrite <- bpow_plus.
apply Rle_trans with (bpow r2 (mag r2 x - 1)).
  apply bpow_le; unfold ms'; lia.
now generalize (bpow_mag_le r2 _ xn0); rewrite Rabs_pos_eq by lra.
Qed.

Lemma cexp_bpow : forall x e, x <> 0%R ->
  (fmin < cexp radix2 f_exp x)%Z ->
  (fmin < e + cexp radix2 f_exp x)%Z ->
  cexp radix2 f_exp (x * bpow radix2 e)%R = (cexp radix2 f_exp x + e)%Z.
Proof.
intros x e xn0 xbnds ebnds.
revert xbnds ebnds.
unfold cexp, f_exp, FLT_exp.
rewrite mag_mult_bpow; auto.
destruct (Z_le_gt_dec (3 - es - ms) (mag radix2 x - ms)) as [l | r].
  rewrite Z.max_l; [lia | ].
  unfold fmin, es, ms in l |- *; lia.
rewrite Z.max_r; [lia | ].
unfold fmin, es, ms in r |- *; lia.
Qed.

Lemma mantissa_bpow x e :
  x <> 0%R ->
  (fmin < cexp radix2 f_exp x)%Z ->
  (fmin < e + cexp radix2 f_exp x)%Z ->
  scaled_mantissa radix2 f_exp (x * bpow radix2 e) =
  scaled_mantissa radix2 f_exp x.
Proof.
unfold scaled_mantissa.
intros xn0 cndx cnde; rewrite cexp_bpow; auto.
rewrite !Rmult_assoc, <- !bpow_plus.
apply f_equal with (f := fun u => (x * bpow radix2 u)%R); ring.
Qed.

Lemma round_mult_bpow x e :
  (x <> 0)%R ->
  (fmin < cexp radix2 f_exp x)%Z ->
  (fmin < e + cexp radix2 f_exp x)%Z ->
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
  bpow radix2 fmin <= x <= B2R' predf_max ->
  sqrt x + 16 * bpow r2 (- ms') * sqrt x <= y <= B2R' predf_max ->
  - (5 / bpow r2 ms * y) <= round' (round'(y + round' (x / y)) / 2) -
   (y + (x / y)) / 2 <=
  5 / bpow r2 (ms) * y.
Proof.
intros ry intx inty.
assert (xgt0 : 0 < x).
  now apply Rlt_le_trans with (2 := proj1 intx), bpow_gt_0.
replace (sqrt x + 16 * bpow r2 (- ms') * sqrt x) with
  (sqrt x * (1 + 16 * bpow r2 (- ms'))) in inty by ring.
assert (sgtmin : bpow r2 (1 - halfes - halfms) < sqrt x).
  apply least_sqrt; tauto.
assert (0 < sqrt x) by (apply Rlt_trans with (2 := sgtmin), bpow_gt_0).
assert (0 < bpow r2 (- ms') < / 1024) by (simpl; lra).
assert (sx0 : (sqrt x <> 0)%R) by now apply Rgt_not_eq.
set (e := y - sqrt x).
assert (0 < y) by (simpl in inty; lra).
assert (eley : bpow r2 (-(es - 2)) <= y).
  apply Rle_trans with (2 := proj1 inty).
  apply Rle_trans with (sqrt x * 1).
    rewrite Rmult_1_r.
    apply Rlt_le, Rlt_trans with (2 := sgtmin).
    apply bpow_lt; reflexivity.
  apply Rmult_le_compat_l;[|compute]; lra.
assert (boundxy1 : (x / y < sqrt x * (1 - 15 * bpow r2 (- ms')))%R).
  apply Rdiv_lt_swap_lr;[lra | ].
  rewrite <- (sqrt_sqrt x) at 1;[ | assert (tmp := bpow_gt_0 r2 fmin); lra].
  rewrite Rmult_assoc; apply Rmult_lt_compat_l;[lra | ].
  apply Rmult_lt_reg_l with (/ (1 - 15 * bpow r2 (- ms'))).
    apply Rinv_0_lt_compat; simpl; lra.
  rewrite <- Rmult_assoc, Rinv_l, Rmult_1_l by (simpl; lra).
  apply Rlt_le_trans with (2 := proj1 inty).
  rewrite (Rmult_comm (sqrt x)); apply Rmult_lt_compat_r;[|simpl];lra.
assert (ulpsgt0 : 0 < ulp r2 f_exp (sqrt x)).
  apply float_bound_ulp, Rlt_le, Rlt_trans with (2 := sgtmin).
  apply bpow_lt; reflexivity.
assert (x / y < y).
  apply Rlt_trans with (sqrt x * 1).
    apply Rlt_le_trans with (1:= boundxy1).
    apply Rmult_le_compat_l;[| simpl ]; lra.
    apply Rlt_le_trans with (2 := proj1 inty).
    apply Rmult_lt_compat_l;[| compute]; lra.
assert (y + round' (x / y) <= 2 * y).
  assert (sqrt x <= y * ( 1 - bpow r2 (- ms'))).
    apply Rmult_le_reg_r with (/ (1 - bpow r2 (- ms'))).
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
    apply Rdiv_le_swap_lr;[ | compute]; lra.
  enough (round' (x / y) <= y) by lra. (* simpler if round' y = y *)
  rewrite <- ry at 2; apply round_le'; lra.
assert (maglb : ((1 - halfes - halfms) + 1 <= mag r2 y)%Z).
  apply mag_ge_bpow; rewrite Z.add_simpl_r, Rabs_pos_eq;[ | lra ].
  apply Rle_trans with (2 := proj1 inty).
  apply Rle_trans with (sqrt x * 1);[lra | ].
  apply Rmult_le_compat_l;[|compute ]; lra.
assert (boundsum : round' (y + round' (x / y)) <= 2 * y).
  replace (2 * y) with (round' y * bpow r2 1) by (rewrite ry; simpl; lra).
  rewrite <- round_mult_bpow; try lra; unfold cexp, FLT_exp; try lia.
  apply round_le'; simpl; lra.  
  unfold fmin, halfes, halfms, es, ms in maglb |- *; lia.
assert (0 < x / y).
  apply Rmult_lt_0_compat;[lra | apply Rinv_0_lt_compat; lra].
assert (0 <= round' (x / y)).
  rewrite <- (round_0 r2 f_exp (round_mode mode_NE)).
  apply round_le; try typeclasses eauto; lra.
assert (rsum : Rabs (round' (y + round' (x / y)) - (y + round' (x / y))) <=
            ulp r2 f_exp y * 2).
  apply Rle_trans with (1 := error_le_ulp r2 f_exp (round_mode mode_NE)
                             (y + round' (x / y))).
  replace 2 with (bpow r2 1) by (compute; lra).
  rewrite <- ulp_FLT_exact_shift;
    [ | lra |unfold fmin, halfes, halfms, ms in maglb |- *; lia |
         unfold fmin, halfes, halfms, ms in maglb |- *; lia].
  apply ulp_le; try typeclasses eauto.
  replace (bpow r2 1) with 2 by (simpl; lra).
  rewrite !Rabs_pos_eq; lra.
apply (Rmult_le_compat_r (/ 2)) in rsum;[|lra ].
rewrite Rmult_assoc, Rinv_r, Rmult_1_r in rsum;[ | lra].
replace (/ 2) with (Rabs (/ 2)) in rsum by (rewrite Rabs_pos_eq; lra).
rewrite <- Rabs_mult, Rmult_minus_distr_r in rsum. 
assert (rdiv : Rabs (round' (x / y) - x / y) <= ulp r2 f_exp y).
  assert (tmp := error_le_ulp r2 f_exp (round_mode mode_NE) (x / y)).
  fold (round' (x / y)) in tmp; apply Rle_trans with (1 := tmp).
  apply ulp_le; try typeclasses eauto; rewrite !Rabs_pos_eq; lra.
assert (rsum' : Rabs ((y + round' (x / y)) / 2 - (y + x / y) / 2) <=
                    ulp r2 f_exp y / 2).
  rewrite <- Rdiv_minus_distr, Rabs_div, (Rabs_pos_eq 2) by lra.
  apply Rmult_le_compat_r; [lra | ].
  replace (y + round' (x / y) - (y + x / y)) with (round' (x / y) - x / y); lra.
apply Rabs_def2b.
assert (tech : forall c a b, Rabs(a - b) <= Rabs (a - c) + Rabs (c - b)).
  intros c a b; replace (a - b) with ((a - c) + (c - b)) by ring.
  now apply Rabs_triang.
apply Rle_trans with (1 := tech (round' (y + round' (x / y)) / 2) _ _).
replace (5 / bpow r2 ms * y) with
   (y / bpow r2 ms'  + (y / bpow r2 ms'  + y / bpow r2 ms' * / 2) ) by (simpl; lra).
apply Rplus_le_compat.
  apply Rle_trans with 
    (1 := error_le_ulp r2 f_exp _ (round' (y + round' (x / y)) / 2)).
  apply Rle_trans with (ulp r2 f_exp y); cycle 1.
     exact (proj2 (float_bound_ulp _ eley)).
  apply ulp_le; try typeclasses eauto.
  rewrite !Rabs_pos_eq; try lra.
  enough (0 <= round' (y + round' (x / y))) by lra.
  replace 0 with (round' 0) by (apply round_0; typeclasses eauto).
  apply round_le'; lra.
apply Rle_trans with (1 := tech ((y + round' (x / y)) / 2) _ _).
apply Rplus_le_compat.
apply Rle_trans with (1 := rsum).
  apply (proj2 (float_bound_ulp _ eley)).
apply Rle_trans with (1 := rsum').
apply Rmult_le_compat_r;[lra | apply float_bound_ulp; lra].
Qed.

Lemma ffderive x y :
  y <> 0 ->
  is_derive (fun z => (z + x / z)/ 2 - 5 * bpow r2 (-(ms)) * z) y
       ((1 - x / y ^ 2) / 2 - 5 * bpow r2 (-(ms))).
Proof.
intros yn0; auto_derive; auto.
simpl; field; compute; lra.
Qed.

Lemma ff_positive x y :
  (0 < x) -> sqrt x * (1 + 16 * ulp1) <= y ->
  0 < (1 - x / y ^ 2) / 2 - 5 * bpow r2 (-(ms)).
Proof.
intros xge1 yges.
assert (sgt0 : 0 < sqrt x).
  now apply sqrt_lt_R0.
assert (ygt0 : 0 < y).
  apply Rlt_le_trans with (2 := yges).
  apply Rmult_lt_0_compat;[ | compute]; try lra.
assert (y <> 0) by lra.
assert (0 < y ^ 2) by (apply pow2_gt_0; assumption).
assert (y ^ 2 <> 0) by now apply Rgt_not_eq.
enough (10 * bpow r2 (-(ms)) < 1 - x / y ^ 2) by lra.
apply Rmult_lt_reg_r with (y ^ 2);[ assumption | ].
rewrite Rmult_minus_distr_r, Rmult_1_l, Rdiv_cancel by auto.
enough (x < (1 - 10 * bpow r2 (-(ms))) * y ^ 2) by lra.
apply Rlt_le_trans with (x * ((1 + 16 * ulp1) ^ 2 *
                               (1 - 10 * bpow r2 (-(ms))))).
  rewrite <- (Rmult_1_r x) at 1.
  apply Rmult_lt_compat_l;[ | unfold ulp1; simpl];lra.
rewrite <- Rmult_assoc, (Rmult_comm (1 - _)).
apply Rmult_le_compat_r;[unfold ulp1; simpl; lra | ].
replace x with (sqrt x ^ 2) by (simpl; rewrite Rmult_1_r, sqrt_sqrt; lra).
rewrite <- Rpow_mult_distr; apply pow_incr; split;[ | tauto].
apply Rmult_le_pos;[ | unfold ulp1; simpl]; lra.
Qed.

Lemma pure_lb x y :
  (bpow r2 fmin <= x) -> sqrt x * (1 + 16 * ulp1) <= y ->
  sqrt x * (1 - 16 * ulp1) <= (y + x / y) / 2 - 5 * bpow r2 (-(ms)) * y.
Proof.
intros xlb yges.
set (y' := sqrt x * (1 + 16 * ulp1)).
assert (sgmin : bpow r2  (- (es + ms - 2) / 2) < sqrt x).
  apply least_sqrt; tauto.
assert (sgt0 : 0 < sqrt x).
  now apply Rlt_trans with (2 := sgmin); apply bpow_gt_0.
assert (xgt0 : 0 < x).
  now (apply Rlt_le_trans with (2 := xlb); apply bpow_gt_0).
assert (expand : (y' + x / y') / 2 =
  sqrt x + sqrt x * ((16 * ulp1) ^ 2 / (2 * (1 + 16 * ulp1)))).
  rewrite <- (sqrt_sqrt x) at 1 by lra.
  unfold y'; field; split;[compute |]; lra.
apply Rle_trans with ((y' + x / y') / 2 - 5 * bpow r2 (-(ms)) * y').
  rewrite expand; unfold y'.
  rewrite <- (Rmult_1_r (sqrt x)) at 2. 
  rewrite <- Rmult_plus_distr_l, (Rmult_comm (5 * bpow r2 (-(ms)))).
  rewrite Rmult_assoc, <- Rmult_minus_distr_l.
  apply Rmult_le_compat_l;[ | compute ]; lra.
set (f z := (z + x / z) / 2 - 5 * bpow r2 (-(ms)) * z).
change (f y' <= f y).
destruct (Req_dec y y') as [yy' | yny'].
  now rewrite yy'; apply Req_le, eq_refl.
assert (ygty' : y' < y) by (unfold y' in yny' |- *; lra).
assert (0 < y').
  unfold y'; apply Rmult_lt_0_compat;[ | compute]; lra.
assert (ders :forall t, y' <= t <= y -> forall k, (k <= 1)%nat ->
  ex_derive_n f k t).
  intros t intt [ | k'] deg; inversion deg; try solve[simpl; auto].
    simpl; exists ((1 - x / t ^ 2) / 2 - 5 * bpow r2 (-(ms))).
    apply ffderive; lra.
  assert (abs : (S k' <= 0)%nat) by assumption; inversion abs.
destruct (Taylor_Lagrange f 0 y' y ygty' ders) as [c [intc Pc]].
rewrite Pc; clear Pc; simpl; replace (1 / 1) with 1 by field.
rewrite Rdiv_1_r, Rmult_1_l, Rmult_1_r.
enough (0 <= (y - y') * Derive (fun z => f z) c) by lra.
apply Rmult_le_pos;[lra | ].
assert (cn0 : c <> 0) by lra.
rewrite (is_derive_unique (fun z : R => f z) c _ (ffderive x c cn0)).
now apply Rlt_le, ff_positive; auto; apply Rlt_le, (proj1 intc).
Qed.

Lemma body_exp_decrease16' x y:
  round' y = y ->
  1 <= x <= B2R ms es predf_max ->
  sqrt x + 16 * bpow r2 (- ms') * sqrt x <= y <= B2R' predf_max ->
  sqrt x * (1 - 16 * ulp1) <= body_exp_R x y < y.
Proof.
intros ry intx inty.
assert (sge0 : (1 <= sqrt x)%R).
  now rewrite <- sqrt_1; apply sqrt_le_1_alt; lra.
assert (yge1 : 1 <= y).
  apply Rle_trans with (2 := proj1 inty).
  replace (sqrt x + 16 * bpow r2 (- ms') * sqrt x) with
          (sqrt x * (1 + 16 * bpow r2 (- ms'))) by ring.
  rewrite <- (Rmult_1_r 1) at 1; apply Rmult_le_compat; simpl; lra.
assert (sgt0 : 0 < sqrt x) by lra.
assert (xgt0 : 0 < x) by lra.
assert (u8gt0 : 0 < 8 * ulp1 * sqrt x) by (unfold ulp1; simpl; lra).
assert (inty' : sqrt x - 16 * ulp1 * sqrt x <= y <= B2R' predf_max).
  split;[ | lra].
  apply Rle_trans with (2 := proj1 inty).
  apply Rplus_le_compat_l; rewrite Ropp_mult_distr_l.
  apply Rmult_le_compat_r;[ | unfold ulp1; simpl]; lra.
assert (inty2 : sqrt x + 2 * (8 * bpow r2 (- ms') * sqrt x) <= y
                  <= B2R' predf_max).
  rewrite <- !Rmult_assoc; assumption.
assert (intx2 : bpow r2 fmin <= x <= B2R ms es predf_max).
  split;[apply Rlt_le, Rlt_le_trans with 1;[apply fminlt1 | tauto] | tauto].
split.
  apply Rle_trans with ((y + x / y) / 2 - 5 / bpow r2 ms * y).
    apply pure_lb;[assert (tmp := fminlt1); lra | ].
    rewrite Rmult_plus_distr_l, Rmult_1_r, (Rmult_comm (sqrt x)); tauto.
  apply Rplus_le_reg_l with (- ((y + x / y) / 2)).
  unfold Rminus; rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l, Rplus_comm.
  exact (proj1 (round_proof _ _ ry intx2 inty)).
apply Rle_lt_trans with ((y + x / y) / 2 + 5 / bpow r2 ms * y).
  apply Rplus_le_reg_l with (- ((y + x / y) / 2)).
  rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l, Rplus_comm.
  exact (proj2 (round_proof _ _ ry intx2 inty)).
assert (0 < bpow r2 (- ms') < / 1024) by (simpl; lra).
assert (0 < y) by nra.
assert (egt0 : 0 < 5 * bpow r2 (- ms') * y).
  apply Rmult_lt_0_compat;[simpl | ]; lra.  
assert (inty3 : sqrt x + 2 * (5 * bpow r2 (- ms') * y) <= y).
  enough (sqrt x <= y * (1 - 2 * (5 * bpow r2 (- ms')))) by lra.
  apply Rmult_le_reg_r with (/ (1 - 2 * (5 * bpow r2 (- ms')))).
    apply Rinv_0_lt_compat; simpl; lra.
  rewrite Rmult_assoc, Rinv_r, Rmult_1_r by lra.
  apply Rle_trans with (2 := proj1 inty).
  replace (sqrt x + 16 * bpow r2 (- ms') * sqrt x) with
    (sqrt x * (1 + 16 * bpow r2 (- ms'))) by ring.
  apply Rmult_le_compat_l;[lra | ].
  simpl; lra.
assert (tmp := pure_decrease_2u 1 (5 * bpow r2 (- ms') * y) x y Rlt_0_1 xgt0 
               sge0 egt0 inty3).
apply Rplus_lt_reg_r with (- (5 * bpow r2 (- ms') * y)).
apply Rle_lt_trans with (2 := proj2 tmp).
enough (0 < 5 * bpow r2 (- ms') * y - 5 / bpow r2 ms * y) by lra.
rewrite <- Rmult_minus_distr_r; apply Rmult_lt_0_compat;[simpl | ];lra.
Qed.

Lemma body_exp_decrease16l x y:
  round' y = y ->
  bpow radix2 fmin <= x <= 1 ->
  sqrt x + 16 * bpow r2 (- ms') * sqrt x <= y <= 1 + 16 * ulp1 ->
  sqrt x * (1 - 16 * ulp1) <= body_exp_R x y < y.
Proof.
intros ry intx inty.
assert (sgtfmin : (bpow radix2 (- (es + ms - 2) / 2) < sqrt x)%R).
  assert (sqrte : bpow radix2 (- (es + ms - 2) / 2) =
          sqrt (bpow radix2 (- (es + ms - 2)))).
    symmetry; apply sqrt_lem_1.
        now apply bpow_ge_0.
      now apply bpow_ge_0.
    now rewrite <- bpow_plus; apply f_equal; reflexivity.
  rewrite sqrte; apply sqrt_lt_1_alt; split;[apply bpow_ge_0 | ].
  now apply Rlt_le_trans with (2 := proj1 intx); apply bpow_lt.
assert (yge1 : bpow r2 (- (es + ms - 2) / 2) <= y).
  apply Rle_trans with (2 := proj1 inty).
  apply Rlt_le, Rlt_le_trans with (1 := sgtfmin).
  rewrite <- (Rplus_0_r (sqrt x)) at 1.
  apply Rplus_le_compat_l, Rmult_le_pos;[ | now apply sqrt_ge_0].
  now apply Rmult_le_pos;[lra | apply bpow_ge_0].
assert (lbgt0 : 0 < bpow r2 (- (es + ms - 2) / 2)) by apply bpow_gt_0.
assert (fmingt0 : 0 < bpow r2 fmin) by apply bpow_gt_0.
assert (sgt0 : 0 < sqrt x) by lra.
assert (xgt0 : 0 < x) by lra.
assert (u8gt0 : 0 < 8 * ulp1 * sqrt x) by (unfold ulp1; simpl; lra).
assert (inty' : sqrt x - 16 * ulp1 * sqrt x <= y <= B2R' predf_max).
  split;[ | assert (tmp := predf_maxgt1); lra].
  apply Rle_trans with (2 := proj1 inty).
  apply Rplus_le_compat_l; rewrite Ropp_mult_distr_l.
  apply Rmult_le_compat_r;[ | unfold ulp1; simpl]; lra.
assert (inty2 : sqrt x + 2 * (8 * bpow r2 (- ms') * sqrt x) <= y
                  <= B2R' predf_max).
  rewrite <- !Rmult_assoc; split;[tauto | assert (tmp := predf_maxgt1); lra].
assert (intx2 : bpow r2 fmin <= x <= B2R ms es predf_max).
  split;[tauto| apply Rlt_le, Rle_lt_trans with 1;[tauto |]].
  apply Rlt_trans with (2 := predf_maxgt1); compute; lra.
assert (rpf :
  -(5 / bpow r2 ms * y) <= round' (round' (y + round' (x / y)) / 2)
         - (y + (x / y)) / 2 <=
  5 / bpow r2 ms * y).
  apply round_proof; auto; split;[tauto |].
  apply Rlt_le, Rle_lt_trans with (2 := predf_maxgt1); tauto.
split.
  apply Rle_trans with ((y + x / y) / 2 - 5 / bpow r2 ms * y).
    apply pure_lb; try lra.
    rewrite Rmult_plus_distr_l, Rmult_1_r, (Rmult_comm (sqrt x)); tauto.
  apply Rplus_le_reg_l with (- ((y + x / y) / 2)).
  unfold Rminus; rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l, Rplus_comm.
  exact (proj1 rpf).
apply Rle_lt_trans with ((y + x / y) / 2 + 5 / bpow r2 ms * y).
  apply Rplus_le_reg_l with (- ((y + x / y) / 2)).
  rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l, Rplus_comm.
  exact (proj2 rpf).
assert (0 < bpow r2 (- ms') < / 1024) by (simpl; lra).
assert (0 < y) by nra.
assert (egt0 : 0 < 5 * bpow r2 (- ms') * y).
  apply Rmult_lt_0_compat;[simpl | ]; lra.
assert (inty3 : sqrt x + 2 * (5 * bpow r2 (- ms') * y) <= y).
  enough (sqrt x <= y * (1 - 2 * (5 * bpow r2 (- ms')))) by lra.
  apply Rmult_le_reg_r with (/ (1 - 2 * (5 * bpow r2 (- ms')))).
    apply Rinv_0_lt_compat; simpl; lra.
  rewrite Rmult_assoc, Rinv_r, Rmult_1_r by lra.
  apply Rle_trans with (2 := proj1 inty).
  replace (sqrt x + 16 * bpow r2 (- ms') * sqrt x) with
    (sqrt x * (1 + 16 * bpow r2 (- ms'))) by ring.
  apply Rmult_le_compat_l;[lra | ].
  simpl; lra.
assert (tmp := pure_decrease_2u (bpow r2 (- (es + ms - 2) / 2))
  (5 * bpow r2 (- ms') * y) x y (bpow_gt_0 _ _) xgt0
  (Rlt_le _ _ sgtfmin) egt0 inty3).
apply Rplus_lt_reg_r with (- (5 * bpow r2 (- ms') * y)).
apply Rle_lt_trans with (2 := proj2 tmp).
enough (0 < 5 * bpow r2 (- ms') * y - 5 / bpow r2 ms * y) by lra.
rewrite <- Rmult_minus_distr_r; apply Rmult_lt_0_compat;[simpl | ];lra.
Qed.

Lemma positive_finite x : 0 < B2R' x -> is_finite _ _ x = true.
Proof. destruct x; simpl; auto; lra. Qed.

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

Section above1.

Variables x : float.

Definition invariantR x' y' :=
  sqrt x' - 16 * ulp1 * sqrt x' <= y' <= B2R' predf_max.

Definition invariant (p : float * float) :=
    fst p = x /\ invariantR (B2R' x) (B2R' (snd p)).

Definition finalR x' y' := 
  sqrt x' - 5 * ulp1 * sqrt x' <= y' <= sqrt x' + 5 * ulp1 * sqrt x'.

Definition final (v : float) := finalR (B2R' x) (B2R' v).

Hypothesis intx : 1 <= B2R' x < / 2 * B2R' predf_max.

Lemma invariant_test x' y :
  invariant (x', y) ->
  float_cmp Integers.Clt (body_exp x y) y = false ->
  ~ (B2R' (body_exp x y) < B2R' y).
Proof.
unfold invariant, invariantR; intros [xx' inty]; cbv[snd] in inty; clear x' xx'.
assert (0 < ulp1 < / 1024) by (unfold ulp1; simpl; lra).
assert (1 <= sqrt (B2R' x)).
  now rewrite <- sqrt_1; apply sqrt_le_1_alt.
assert (intx' : / 2 <= B2R' x < / 2 * B2R' predf_max).
  split;[apply Rle_trans with (2 := proj1 intx);lra | tauto].
assert (inty' : / 2 <= B2R' y <= B2R' predf_max).
  split;[apply Rle_trans with (2 := proj1 inty); nra | tauto].
assert (finy : is_finite ms es y = true).
  apply positive_finite; lra.
assert (finx : is_finite ms es x = true).
  apply positive_finite; lra.
assert (is_finite ms es (body_exp x y) = true).
  apply body_exp_finite; lra.
unfold float_cmp, float_compare.
rewrite Bcompare_correct; auto.
destruct (Rcompare _ _) eqn:vcmp.
    apply Rcompare_Eq_inv in vcmp; unfold B2R'; lra.
  now intros abs; case abs.
apply Rcompare_Gt_inv in vcmp; unfold B2R'; lra.
Qed.


End above1.

Lemma cexp_32 e r :
  (-(es - 2) < e)%Z ->
  (bpow radix2 (e - 1) <= r < bpow radix2 e)%R ->
  cexp radix2 f_exp r = (e - ms)%Z.
Proof.
intros ce inte.
unfold cexp, f_exp, FLT_exp.
assert (r0 : (0 <= r)%R).
  assert (tmp := bpow_ge_0 radix2 (e - 1)); lra.
assert (vln : mag_val radix2 _ (mag radix2 r) = e).
  now  apply mag_unique; rewrite Rabs_pos_eq.
rewrite vln.
apply Z.max_l; unfold fmin, ms, es in ce |- *; lia.
Qed.

Lemma cexp_1_8 x : 
   1 <= x < 8 ->
   (- ms' <= cexp' x <= -(ms - 3))%Z.
Proof.
intros intx.
destruct (Rle_lt_dec 4 x).
  rewrite (cexp_32 3); unfold ms', ms, es;[lia |lia |].
  simpl bpow; split; lra.
destruct (Rle_lt_dec 2 x).
  rewrite (cexp_32 2); unfold ms', ms, es;[lia |lia |].
  simpl bpow; split; lra.
rewrite (cexp_32 1); unfold ms', ms, es;[lia |lia |].
simpl bpow; split; lra.
Qed.

Lemma body_exp_decrease4 x y :
  1 <= x <= 4 ->
  4 < y <= B2R ms es predf_max ->
  sqrt x - 16 * ulp1 * sqrt x <= body_exp_R x y < y.
Proof.
intros intx inty.
assert (dlt1 : x / y < 1).
  apply Rdiv_lt_swap_lr;[| rewrite Rmult_1_l]; lra.
assert (rdle1 : round' (x / y) <= 1).
  rewrite <- round'1; apply round_le'; lra.
assert (dge0 : 0 <= x / y) by (apply Rdiv_le_swap_rl; lra).
assert (rdge0 : 0 <= round' (x / y)).
  rewrite <- (round_0 r2 f_exp (round_mode mode_NE)).
  now apply round_le'.
assert (sl5 : y + round' (x / y) <= 5 / 4 * y) by lra.
assert (sge4 : 4 < y + round' (x / y)) by lra.
assert (sgt0 : 0 < y + round' (x / y)) by lra.
assert (rsg4 : 4 <= round' (y + round' (x / y))).
  rewrite <- round'4; apply round_le'; lra.
assert (rsl5 : round' (y + round' (x / y)) <= 11 / 8 * y).
  assert (tmp := error_le_ulp r2 f_exp (round_mode mode_NE)
             (y + round' (x / y))).
  apply Rabs_def2b in tmp.
  assert (a : bpow r2 (fmin + ms - 1) <= Rabs (y + round' (x / y))).
    rewrite Rabs_pos_eq by lra.
    apply Rle_trans with (2 := Rlt_le _ _ sge4); compute; lra.
  generalize (ulp_FLT_le r2 (fmin) ms _ a); rewrite Rabs_pos_eq by lra.
  intros tm2.
  fold (round' (y + round'(x/y))) in tmp.
  apply Rle_trans with 
    (5 / 4 * y + (y + round' (x / y)) * bpow r2 (1 - ms) );[lra | ].
  enough ((y + round' (x / y)) * bpow r2 (1 - ms) <= / 8 * y) by lra.
  apply Rle_trans with (5 / 4 * y * bpow r2 (1 - ms)).
    apply Rmult_le_compat_r;[apply bpow_ge_0 | lra].
  rewrite <- (Rmult_comm y), Rmult_assoc, (Rmult_comm y).
  apply Rmult_le_compat_r; [ | compute]; lra.
assert (round' (y + round' (x / y)) / 2 <= 11 / 16 * y) by lra.
assert (bge2 : 2 <= round' (y + round' (x / y)) / 2) by lra.
assert (tmp := error_le_ulp r2 f_exp (round_mode mode_NE)
             (round' (y + round' (x / y)) / 2)).
apply Rabs_def2b in tmp; fold (round' (round' (y + round' (x / y)) / 2)) in tmp.
fold (body_exp_R x y) in tmp.
assert (a : bpow r2 (fmin + ms - 1) <= Rabs (round' (y + round' (x / y)) / 2)).
  rewrite Rabs_pos_eq by lra.
  apply Rle_trans with (2 := bge2); compute; lra.
generalize (ulp_FLT_le r2 (fmin) ms _ a); rewrite Rabs_pos_eq by lra.
intros tm2.
split.
  assert (sge1 := sqrt_1_4 x intx).
  apply Rle_trans with (round' (sqrt x)).
    assert (tm3 := error_le_ulp r2 f_exp (round_mode mode_NE) (sqrt x)).
    assert (a2 : bpow r2 (fmin + ms - 1) <= Rabs (sqrt x)).
      rewrite Rabs_pos_eq by lra.
      apply Rle_trans with (2 := proj1 sge1); compute; lra.
    generalize (ulp_FLT_le r2 (fmin) ms _ a2); rewrite Rabs_pos_eq by lra.
    change (bpow r2 (1 - ms)) with ulp1; intros tm4.
    apply Rabs_def2b in tm3; fold (round' (sqrt x)) in tm3; lra.
  unfold body_exp_R; apply round_le'; lra.
enough (body_exp_R x y <= 3 / 4 * y) by lra.
apply Rle_trans with (11 / 16 * y +
                round' (y + round' (x / y)) / 2 * bpow r2 (1 - ms));[lra | ].
enough (round' (y + round' (x / y)) / 2 * bpow r2 (1 - ms) <= / 16 * y) by lra.
apply Rle_trans with (11 / 16 * y * bpow r2 (1 - ms)).
  apply Rmult_le_compat_r;[apply bpow_ge_0 | lra].
rewrite <- (Rmult_comm y), Rmult_assoc, (Rmult_comm y).
apply Rmult_le_compat_r; [ | compute]; lra.
Qed.

Section interval_1_4.

Variable x : float.

Hypothesis intx : 1 <= B2R' x <= 4.

Let widen_1_4_to_max : 1 <= B2R' x < / 2 * B2R' predf_max.
Proof.
unfold B2R' at 3; rewrite predf_max_val; simpl; lra.
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

Lemma invariant_test_1_4 x' y :
  invariant x (x', y) -> 
  float_cmp Integers.Clt (body_exp x y) y = false ->
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
assert (inty : sqrt x' + 16 * ulp1 * sqrt x' <= y <= B2R' predf_max).
  lra.
assert (wi : 1 <= x' <= B2R' predf_max).
  split;[ | apply Rle_trans with (1 := proj2 intx'); compute]; lra.
assert (tmp := body_exp_decrease16' x' y ry wi inty).
case test; exact (proj2 tmp).
Qed.

Lemma invariant_final :
  forall x' y, invariant x (x', y) ->
    float_cmp Integers.Clt (body_exp x y) y = false ->
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
assert (inty : 4 < y <= B2R' predf_max) by lra.
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


Lemma body_exp_value_scale' x' y' e:
  (1 <= x' <= 4)%R ->
  / 2 * sqrt x' <= y' <= 2 * sqrt x' ->
  (-(es - 3) < e)%Z ->
  (fmin < (2 * e) + cexp radix2 f_exp x')%Z ->
  (round' (round' (y' + round' (x' / y')) / 2) * bpow radix2 e =
  round' (round' (y' * bpow radix2 e +
              round' ((x' * bpow radix2 (2 * e)) /
                      (y' * bpow radix2 e))) / 2))%R.
Proof.
intros intx inty (* elb *) inte.
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
assert (qgth : (/ 2 <= x' / y')%R) by (apply Rdiv_le_swap_rl; lra).
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
  apply Rdiv_le_swap_lr;[lra | rewrite (Rmult_comm 2), Rmult_assoc].
  apply Rmult_le_compat_l;lra.
assert (qle4 : (x' / y' <= 4)%R) by lra.
assert (rqle2 : (round' (x' / y') <= 4)%R).
  now rewrite <- round'4; apply round_le'.
assert (cexpb: (-ms <= cexp' (x' / y') <= -(ms - 3))%Z).
  destruct (Rlt_le_dec (x' / y') 1).
    rewrite (cexp_32 0);unfold ms', ms, es;[lia | lia| simpl bpow; split; lra].
  enough (it : (- ms' <= cexp' (x' / y') <= -(ms - 3))%Z).
    split;[unfold ms' in it; lia | lia].
  apply cexp_1_8; lra.
rewrite round_mult_bpow; unfold fmin, ms, es in cexpb, inte(*,elb*) |- *;
    [ | lra | lia | lia].
rewrite <- Rmult_plus_distr_r.
assert (r6 : round' 6 = 6%R).
  assert (ccexp : (6 <> 0 -> - (ms - 3) <= 0)%Z) by (unfold ms; lia).
  generalize (generic_format_F2R radix2 f_exp 6 0 ).
  replace (cexp radix2 f_exp (F2R {|Defs.Fnum := 6; Defs.Fexp := 0|})) with
     (- (ms - 3))%Z; cycle 1.
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
      apply Rdiv_le_swap_lr; [lra | ].
      apply Rle_trans with (2 * sqrt x'); try lra.
      rewrite <- (sqrt_sqrt x') at 1 by lra.
      apply Rmult_le_compat_r; lra.
    now rewrite <- round'2; apply round_le'.
assert (rsumle6 : (round' (y' + round' (x' / y')) <= 6)%R).
  now rewrite <- r6; apply round_le'.
assert (exple4: (round' (y' + round' (x' / y')) / 2 <= 4)%R) by lra.
assert (sb : (- ms' <= (cexp' (y' + round' (x' / y'))) <= - (ms - 3))%Z).
  apply cexp_1_8; lra.
assert (rsb : (-ms <= (cexp' (round' (y' + round' (x' / y')) / 2)) <=
                           - (ms - 2))%Z).
  destruct (Rle_lt_dec 1 (round' (y' + round' (x' / y')) / 2)).
    destruct (Rle_lt_dec 2 (round' (y' + round' (x' / y')) / 2)).
      rewrite (cexp_32 2); unfold ms, es;
        [lia | lia| simpl bpow; split; lra].
    rewrite (cexp_32 1); unfold ms, es; [lia | lia| simpl bpow; split; lra].
  rewrite (cexp_32 0); unfold ms, es; [lia | lia| simpl bpow; split; lra].
rewrite round_mult_bpow; unfold fmin, ms', ms in sb |- *;[ | lra | lia| lia].
assert (tech : forall a b, ((a * b) / 2 = (a / 2) * b)%R)
   by (intros; field; lra).
rewrite tech.
rewrite round_mult_bpow;unfold fmin, ms in rsb |- *;[lra | lra | | ]; lia.
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
  bpow r2 (6 - es) <= x <= /2 * (B2R' predf_max) ->
  sqrt x - 16 * ulp1 * sqrt x <= y <= sqrt x + 16 * ulp1 * sqrt x ->
  exists e : Z, exists x2, exists y2,
    1 <= x2 <= 4 /\
    sqrt x2 - 16 * ulp1 * sqrt x2 <= y2 <= sqrt x2 + 16 * ulp1 * sqrt x2 /\
    x = x2 * bpow r2 (2 * e) /\ y = y2 * bpow r2 e /\
    ((fmin + 1) / 2 <= e <= halfes)%Z /\
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
assert (lowpow_gt_0 : 0 < bpow r2 (6 - es)) by apply bpow_gt_0.
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
assert (mx'bound : (6 - es < mag r2 (x) < es - 1)%Z).
  split.
    apply mag_gt_bpow; simpl; rewrite Rabs_pos_eq; [ | lra].
    apply Rle_trans with (2 := proj1 intx); compute; lra.
  enough (mag r2 x <= es - 2)%Z by lia.
  apply mag_le_bpow; auto; rewrite Rabs_pos_eq by lra.
  replace (bpow r2 (es - 2)) with (B2R' predf_max);[lra | ].
  unfold B2R'; rewrite predf_max_val, <- bpow_plus; reflexivity.
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
assert (cex2b : (- ms' <= (cexp' x2) <= -(ms - 3))%Z).
  apply cexp_1_8; lra.
assert (egemin : (2 - halfes <= e <= halfes)%Z).
  assert (mdiv2lb : (3 - halfes <= mag r2 x / 2)%Z).
    replace (3 - halfes)%Z with ((6 - es) / 2)%Z by reflexivity.
    apply Z_div_le;[reflexivity | lia].
  assert (tmp := Z.mod_pos_bound (mag r2 (x)) 2 eq_refl).
  assert (steplb : (2 - halfes <= e)%Z).
     unfold fmin in mdiv2lb |- *; lia.
  split;[ | enough (mdiv2ub : (mag r2 x / 2 <= halfes)%Z) by lia]; cycle 1.
    replace halfes with (es / 2)%Z by reflexivity.
    apply Z_div_le;[reflexivity | lia].
  lia.
assert (cx'bounds : (fmin  < 2 * e + cexp' x2)%Z).
  unfold halfes, fmin, ms', ms, es in cex2b, egemin |- *; lia.
exists e, x2, y2.
assert (eint : (2 - halfes - halfms <= e <= halfes)%Z).
  split;[ | tauto].
unfold halfms; lia.
split;[easy | ].
split;[easy | ].
split;[easy | ].
split;[easy | ].
split;[easy | ].
assert (egt : (- (es - 3) < e)%Z).
  unfold halfes, halfms,es in eint |- * ; lia.
generalize (body_exp_value_scale' x2 y2 e inx2 ybnds egt cx'bounds).
rewrite <- yval, <- xval; symmetry; tauto.
Qed.


Section interval_1_max.

Variable x : float.

Hypothesis intx : 1 <= B2R' x < / 2 * B2R' predf_max.

Lemma invariant_spec_1_max  x' y :
       float_cmp Integers.Clt (body_exp x' y)  y = true ->
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
assert (maxval : B2R' predf_max = 2 ^ 126).
  unfold B2R'; rewrite predf_max_val; compute; lra.
assert (0 < B2R' y).
  apply Rlt_le_trans with (2 := proj1 cnd2).
  rewrite <- (Rmult_1_l (sqrt (B2R' x))) at 1.
  rewrite <- Rmult_minus_distr_r; apply Rmult_lt_0_compat;[compute|]; lra.
assert (inx' : 1 <= B2R' x <= B2R' predf_max).
  rewrite maxval in intx |- *; lra.
cbv [snd] in cnd2.
assert (xfar : sqrt (B2R' x) + 5 * ulp1 * sqrt (B2R' x) <= B2R' x).
  apply Rle_trans with (sqrt (B2R' x) + 16 * ulp1 * sqrt (B2R' x));[nra | ].
  apply Rlt_le, Rlt_le_trans with (1 := add_16_ulp_2 _ sge0); lra.
assert (inx2 : / 2 <= B2R' x < / 2 * B2R' predf_max) by lra.
assert (iny2 : / 2 <= B2R' y <= B2R' predf_max).
  split; [| lra].
  apply Rle_trans with (2:= proj1 cnd2).
  apply Rlt_le, Rle_lt_trans with (2 := sub_16_ulp_2 _ sge0); lra.
destruct (Rle_lt_dec (sqrt (B2R' x) + 16 * bpow r2 (- ms') * sqrt (B2R' x))
             (B2R' y)) as [ybig | yclose].
  split;[easy | cbv [snd] in cnd2 |- *].
  rewrite body_exp_val; try lra.
  destruct (body_exp_decrease16' _ _ ry inx' (conj ybig (proj2 cnd2)))
      as [lb  ub].
  rewrite Rmult_minus_distr_l, Rmult_1_r, (Rmult_comm (sqrt _)) in lb.
  split; [exact lb | apply Rle_trans with (2 := (proj2 cnd2)) ].
  apply Rlt_le; exact ub.
assert (xint' : bpow r2 (6 - es) <= B2R' x <= / 2 * B2R' predf_max).
  split;[simpl | ]; lra.
destruct (scale_data _ _ xint'
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
  float_cmp Integers.Clt (body_exp x y) y = false ->
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
assert (maxval : B2R' predf_max = 2 ^ 126).
  unfold B2R'; rewrite predf_max_val; compute; lra.
assert (0 < B2R' y).
  apply Rlt_le_trans with (2 := proj1 cnd2).
  rewrite <- (Rmult_1_l (sqrt (B2R' x))) at 1.
  rewrite <- Rmult_minus_distr_r; apply Rmult_lt_0_compat;[compute|]; lra.
assert (inx' : 1 <= B2R' x <= B2R' predf_max).
  rewrite maxval in intx |- *; lra.
cbv [snd] in cnd2.
assert (xfar : sqrt (B2R' x) + 5 * ulp1 * sqrt (B2R' x) <= B2R' x).
  apply Rle_trans with (sqrt (B2R' x) + 16 * ulp1 * sqrt (B2R' x)).
    apply Rplus_le_compat_l; apply Rmult_le_compat_r; lra.
  apply Rlt_le, Rlt_le_trans with (1 := add_16_ulp_2 _ sge0); lra.
assert (inx2 : / 2 <= B2R' x < / 2 * B2R' predf_max) by lra.
assert (iny2 : / 2 <= B2R' y <= B2R' predf_max).
  split; [| lra].
  apply Rle_trans with (2:= proj1 cnd2).
  apply Rlt_le, Rle_lt_trans with (2 := sub_16_ulp_2 _ sge0); lra.
destruct (Rle_lt_dec (sqrt (B2R' x) + 16 * bpow r2 (- ms') * sqrt (B2R' x))
             (B2R' y)) as [ybig | yclose].
  destruct (body_exp_decrease16' _ _ ry inx' (conj ybig (proj2 cnd2)))
      as [lb  ub].
  case test'; cbv [snd]; rewrite body_exp_val; [|lra | lra]. 
  fold (body_exp_R (B2R' x) (B2R' y)); lra.
assert (intx_for_scale : bpow r2 (6 - es) <= B2R' x <= / 2 * B2R' predf_max).
  split;[ apply Rle_trans with (2 := proj1 intx); compute |]; lra.
destruct (scale_data _ _ intx_for_scale
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
  apply Rle_trans with (1 := proj2 inty2).
  rewrite <- (Rmult_1_l (sqrt x2)) at 1; rewrite <- Rmult_plus_distr_r.
  apply Rle_trans with (2 * 2);[ | compute; lra].
  apply Rmult_le_compat; lra.
assert (cexpms : (-ms <= cexp' (B2R' y))%Z).
  apply (cexp_ge_bpow r2 f_exp (B2R' y) 0).
  replace (bpow r2 (0 - 1)) with (/ 2) by (compute; lra).
  rewrite Rabs_pos_eq; lra.
assert (ry2 : round' y2 = y2).
  assert (y2v : y2 = B2R' y * bpow r2 (-e)).
    rewrite yval, Rmult_assoc, <- bpow_plus, Z.add_opp_diag_r; simpl; ring.
  rewrite y2v, round_mult_bpow, ry; unfold fmin, ms, es in cexpms, ege1 |- *;
    [lra | lra | | ]; try lia.
  unfold halfes in ege1; lia.
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
intros p x' y pxy z vtest iv. 
apply invariant_final_1_max; auto.
subst z. 
unfold body_exp.
destruct iv as [cnd1 cnd2]; rewrite <- cnd1; simpl.
unfold float_cmp in vtest. unfold Floats.cmp_of_comparison in vtest.
destruct (float_compare _ _) as [ [ | | ] | ] eqn:?H; try discriminate; auto.
Qed.

End interval_1_max.


Definition invariantlR x y :=
  sqrt x - 16 * ulp1 * sqrt x <= y <= 1 + 16 * ulp1.

Section interval_min_1.

Variable x : float.

Definition invariantl (p : float * float) :=
    fst p = x /\ invariantlR (B2R' x) (B2R' (snd p)).

Hypothesis intx : bpow r2 (6 - es) <= B2R' x < 1.

Lemma invariantl_spec_min_1  x' y :
       float_cmp Integers.Clt (body_exp x' y) y = true ->
       invariantl (x', y) -> invariantl (x', body_exp x' y).
Proof.
intro.
unfold float_cmp, Floats.cmp_of_comparison,float_compare  in H.
destruct (Bcompare ms es (body_exp x' y) y) as [ [ | | ]|]eqn:?H; try discriminate.
clear H; rename H0 into H. revert H.
unfold invariantl, invariantlR.
assert (ulp1_small : 0 < ulp1 < / 1024) by (compute; lra).
assert (sgmin : bpow r2  (- (es + ms - 2) / 2) < sqrt (B2R' x)).
  apply least_sqrt; apply Rle_trans with (2 := proj1 intx); simpl; lra.
assert (sgt0 : 0 < sqrt (B2R' x)).
  now apply Rlt_trans with (2 := sgmin), bpow_gt_0.
intros test [cnd1 cnd2]; simpl in cnd1; rewrite cnd1 in cnd2 |- *.
cbv [snd] in cnd2; clear cnd1.
assert (ry : round' (B2R' y) = B2R' y) by (apply round_B2R').
assert (maxval : B2R' predf_max = 2 ^ 126).
  unfold B2R'; rewrite predf_max_val; compute; lra.
assert (0 < B2R' y).
  apply Rlt_le_trans with (2 := proj1 cnd2).
  rewrite <- (Rmult_1_l (sqrt (B2R' x))) at 1.
  rewrite <- Rmult_minus_distr_r; apply Rmult_lt_0_compat;[compute|]; lra.
assert (inx' : bpow r2 fmin <= B2R' x <= 1).
  split;[apply Rle_trans with (2 := proj1 intx); simpl | ]; lra.
cbv [snd] in cnd2.
destruct (Rle_lt_dec (sqrt (B2R' x) + 16 * bpow r2 (- ms') * sqrt (B2R' x))
             (B2R' y)) as [ybig | yclose].
  assert (ylb2 : bpow r2 (- (es + ms - 2) / 2) <= B2R' y).
    apply Rlt_le, Rlt_le_trans with (1 := sgmin).
    apply Rle_trans with (2 := ybig).
    rewrite <- (Rplus_0_r (sqrt (B2R' x))) at 1.
    apply Rplus_le_compat_l, Rmult_le_pos;[apply Rmult_le_pos;[lra | ] | lra].
    now apply bpow_ge_0.
  split;[easy | cbv [snd] in cnd2 |- *].
  rewrite body_exp_val';[ | lra | split;[ | lra]]; cycle 1.
    apply Rle_trans with (2 := ylb2), bpow_le; unfold es, ms.
    compute; discriminate.
  destruct (body_exp_decrease16l _ _ ry inx' (conj ybig (proj2 cnd2)))
      as [lb  ub].
  rewrite Rmult_minus_distr_l, Rmult_1_r, (Rmult_comm (sqrt _)) in lb.
  split; [exact lb | apply Rle_trans with (2 := (proj2 cnd2)) ].
  apply Rlt_le; exact ub.
assert (xint' : bpow r2 (6 - es) <= B2R' x <= / 2 * B2R' predf_max).
  split;[tauto | ]; lra.
destruct (scale_data _ _ xint'
              (conj (proj1 cnd2) (Rlt_le _ _ yclose))) as
    [e [x2 [y2 [intx2 [inty2 [xval [yval [ege1 bval']]]]]]]].
assert (ints2 := sqrt_1_4 _ intx2).
split;[easy | ].
assert (sval : sqrt (B2R' x) =  bpow r2 e * sqrt x2).
  rewrite xval, sqrt_mult, <- bpow_square;[ | lra | apply bpow_ge_0].
  rewrite sqrt_pow2, Rmult_comm;[easy | apply bpow_ge_0].
cbn [snd].
rewrite body_exp_val'; try lra; cycle 1.
  split;[ | lra].
  apply Rle_trans with (2 := proj1 cnd2).
  rewrite <- (Rmult_1_l (sqrt _)) at 1.
  rewrite <- Rmult_minus_distr_r.
  replace (bpow r2 (2 - es)) with (/2 * (bpow r2 (3 - es))) by (simpl; lra).
  apply Rmult_le_compat; try lra.
    now apply bpow_ge_0.
  apply Rlt_le, Rlt_trans with (2 := sgmin).
  apply bpow_lt; reflexivity.
fold (body_exp_R (B2R' x) (B2R' y)); rewrite bval'.
assert (tmp := converge_below_16 x2 y2 intx2 inty2).
fold (body_exp_R x2 y2) in tmp.
rewrite sval, (Rmult_comm (bpow _ _)), <- Rmult_assoc, <- Rmult_minus_distr_r.
split.
  apply Rmult_le_compat_r;[apply bpow_ge_0 | ].
  apply Rle_trans with (sqrt x2 - 5 * ulp1);[ | lra ].
  apply Rplus_le_compat_l, Ropp_le_contravar.
  rewrite <- (Rmult_1_r (_ * _)) at 1; apply Rmult_le_compat; lra.
assert (ele0 : (e <= -1)%Z).
  enough (e < 0)%Z by lia.
  assert (bpow r2 (2 * e) < 1).
    apply Rmult_lt_reg_l with x2;[lra | ].
    apply Rlt_le_trans with 1.
      rewrite <- xval; tauto.
    rewrite Rmult_1_r; tauto.
  enough (2 * e < 0)%Z by lia.
  rewrite <- Z.nle_gt; intros abs; apply (bpow_le r2) in abs.
  simpl (bpow r2 0) in abs; lra.
apply Rle_trans with (sqrt x2 * bpow r2 e + 5 * ulp1 * bpow r2 e).
rewrite <- Rmult_plus_distr_r; apply Rmult_le_compat_r;[apply bpow_ge_0 | lra].
apply Rplus_le_compat;[ | ]; cycle 1.
  apply Rle_trans with (5 * ulp1 * bpow r2 (-1)); [ | simpl; lra].
  apply Rmult_le_compat_l;[lra | apply bpow_le; tauto].
replace 1 with (2 * bpow r2 (-1)) by (simpl; lra).
apply Rmult_le_compat; try lra.
  now apply bpow_ge_0.
apply bpow_le; tauto.
Qed.

Lemma invariant_test' x' y :
  invariantl (x', y) -> Bcompare ms es (body_exp x y) y <> Some Lt ->
  ~ (B2R' (body_exp x y) < B2R' y).
Proof.
unfold invariantl, invariantlR; intros [xx' inty]; cbv[snd] in inty.
clear x' xx'.
assert (0 < ulp1 < / 1024) by (unfold ulp1; simpl; lra).
assert (0 < bpow r2 (6 - es)) by apply bpow_gt_0.
assert (slb : bpow r2 (1 - halfes - halfms) < sqrt (B2R' x)).
  apply least_sqrt; apply Rle_trans with (2 := proj1 intx).
  apply bpow_le; unfold fmin, ms, es; lia.
assert (0 < sqrt (B2R' x)).
  now apply Rlt_trans with (2 := slb); apply bpow_gt_0.
assert (intx' : bpow r2 fmin <= B2R' x < 1).
  split;[ | tauto].
  apply Rle_trans with (2 := proj1 intx); apply bpow_le; unfold fmin, es; lia.
assert (inty' : bpow r2 (2 - es) <= B2R' y <= 2).
  split.
    apply Rle_trans with (2 := proj1 inty).
    rewrite <- (Rmult_1_l (sqrt _)) at 1; rewrite <- Rmult_minus_distr_r.
    replace (bpow r2 (2 - es)) with (/ 2 * (bpow r2 (3 - es))); cycle 1.
      simpl; lra.
    apply Rmult_le_compat; try lra.
      now apply bpow_ge_0.
    apply Rlt_le, Rlt_trans with (2 := slb), bpow_lt; reflexivity.
  apply Rle_trans with (1 := proj2 inty); unfold ulp1; simpl; lra.
assert (finy : is_finite ms es y = true).
  apply positive_finite; nra.
assert (finx : is_finite ms es x = true).
  apply positive_finite; lra.
assert (tmp := body_exp_finite_value' _ _ finx finy intx' inty').
assert (is_finite ms es (body_exp x y) = true) by tauto.
rewrite Bcompare_correct;[ | assumption | assumption ].
fold (B2R' (body_exp x y)); fold (B2R' y).
rewrite (proj1 tmp).
destruct (Rcompare _ _) eqn:vcmp;[ | intros abs; case abs; easy | ]; intros _.
  apply Rcompare_Eq_inv in vcmp; lra.
apply Rcompare_Gt_inv in vcmp; lra.
Qed.

Lemma invariant_final_min_1 x' y :
  invariantl (x', y) ->
  float_cmp Integers.Clt (body_exp x y) y = false ->
(*  Bcompare ms es (body_exp x y) y <> Some Lt -> *)
  final x (body_exp x' y).
Proof.
intros H H0'.
assert  (Bcompare ms es (body_exp x y) y <> Some Lt).
unfold float_cmp, Floats.cmp_of_comparison,float_compare  in H0'.
intro. rewrite H0 in H0'. discriminate. clear H0'.
revert H H0.
unfold invariantl, invariantlR.
assert (ulp1_small : 0 < ulp1 < / 1024) by (compute; lra).
assert (sgmin : bpow r2  (1 - halfes - halfms) < sqrt (B2R' x)).
  apply least_sqrt; apply Rle_trans with (2 := proj1 intx); simpl; lra.
assert (sgt0 : 0 < sqrt (B2R' x)).
  now apply Rlt_trans with (2 := sgmin), bpow_gt_0.
intros [cnd1 cnd2] test; simpl in cnd1; rewrite cnd1 in cnd2 |- *.
assert (test' := invariant_test' _ _ (conj cnd1 cnd2) test).
cbv [snd] in cnd2, test'; clear cnd1.
assert (ry : round' (B2R' y) = B2R' y) by (apply round_B2R').
assert (maxval : B2R' predf_max = 2 ^ 126).
  unfold B2R'; rewrite predf_max_val; compute; lra.
assert (0 < B2R' y).
  apply Rlt_le_trans with (2 := proj1 cnd2).
  rewrite <- (Rmult_1_l (sqrt (B2R' x))) at 1.
  rewrite <- Rmult_minus_distr_r; apply Rmult_lt_0_compat;[compute|]; lra.
assert (inx' : bpow r2 fmin <= B2R' x < 1).
  split;[apply Rle_trans with (2 := proj1 intx); apply bpow_le | lra].
  apply Z.lt_le_incl; reflexivity.
assert (inx2 : bpow r2 fmin <= B2R' x <= 1) by lra.
assert (finx : is_finite ms es x = true).
  now apply positive_finite, Rlt_le_trans with (2 := proj1 intx), bpow_gt_0.
assert (finy : is_finite ms es y = true) by now apply positive_finite.
assert (iny' : bpow r2 (2 - es) <= B2R' y <= 2).
  split;[apply Rle_trans with (2 := proj1 cnd2) |
         apply Rle_trans with (1 := proj2 cnd2)].
    rewrite <- (Rmult_1_l (sqrt _)) at 1; rewrite <- Rmult_minus_distr_r.
    replace (bpow r2 (2 - es)) with (/ 2 * bpow r2 (3 - es)) by (simpl; lra).
    apply Rmult_le_compat; try lra;[ now apply bpow_ge_0 | ].
    apply Rlt_le, Rlt_trans with (2 := sgmin), bpow_lt; reflexivity.
  unfold ulp1; simpl; lra.
assert (tmp := body_exp_finite_value' _ _ finx finy inx' iny').
unfold final, finalR; rewrite (proj1 tmp) in test' |- *.
destruct (Rle_lt_dec (sqrt (B2R' x) + 16 * ulp1 * sqrt (B2R' x))
             (B2R' y)) as [ybig | yclose].
  destruct (body_exp_decrease16l _ _ ry inx2 (conj ybig (proj2 cnd2)))
      as [lb  ub].
  case test'; exact ub.
assert (inx3 : bpow r2 (6 - es) <= B2R' x <= / 2 * B2R' predf_max).
  split;[tauto | unfold B2R'; rewrite predf_max_val, <- bpow_plus].
  apply Rlt_le, Rlt_trans with (1 := proj2 intx); simpl; lra.
assert (iny3 : sqrt (B2R' x) - 16 * ulp1 * sqrt (B2R' x) <= B2R' y
                <= sqrt (B2R' x) + 16 * ulp1 * sqrt (B2R' x)) by lra.
destruct (scale_data (B2R' x) (B2R' y) inx3 iny3) as
    [e [x2 [y2 [intx2 [inty2 [xval [yval [ege1 bval']]]]]]]].
fold (body_exp_R (B2R' x) (B2R' y)) in test' |- *.
rewrite bval'.
assert (ints2 := sqrt_1_4 _ intx2).
assert (test2 : ~ body_exp_R x2 y2 < y2).
  intros t2; case test'; fold (body_exp_R (B2R' x) (B2R' y)).
  now rewrite bval', yval; apply Rmult_lt_compat_r;[apply bpow_gt_0 | ].
assert (iv2 : invariantR x2 y2).
  split;[lra | ].
  apply Rle_trans with (2 * 2);[ | lra].
  apply Rle_trans with (1 := proj2 inty2).
  rewrite <- (Rmult_1_l (sqrt _)) at 1; rewrite <- Rmult_plus_distr_r.
  apply Rmult_le_compat; lra.
assert (cexplb : (1 - halfes - ms - halfms <= cexp' (B2R' y))%Z).
  apply (cexp_ge_bpow r2 f_exp (B2R' y) (1 - halfes - halfms)).
  rewrite Rabs_pos_eq by lra.
  replace (1 - halfes - halfms - 1)%Z with ((1 - halfes - halfms) + (- 1))%Z
    by ring.
  rewrite bpow_plus; apply Rle_trans with (2 := proj1 cnd2).
  rewrite <- (Rmult_1_l (sqrt _)) at 1; rewrite <- Rmult_minus_distr_r.
  rewrite Rmult_comm; apply Rmult_le_compat; try lra; try apply bpow_ge_0.
  simpl; lra.
assert (y2gt0 : 0 < y2).
  apply Rlt_le_trans with (2 := proj1 inty2).
  rewrite <- (Rmult_1_l (sqrt _)) at 1; rewrite <- Rmult_minus_distr_r.
  apply Rmult_lt_0_compat; lra.
assert (elt1 : (e <= 2)%Z).
  enough (~(2 < e)%Z) by lia.
  intros abs; apply (bpow_lt r2) in abs.
  apply (Rmult_lt_compat_l y2) in abs; auto.
  rewrite <- yval in abs.
  enough (abs' : 2 < B2R' y) by lra.
  apply Rle_lt_trans with (2 := abs).
  replace 2 with ((/ 2 * 1) * bpow r2 2) by (simpl; lra).
  apply Rmult_le_compat_r;[apply bpow_ge_0 | ].
  apply Rle_trans with (2 := proj1 inty2).
  rewrite <- (Rmult_1_l (sqrt _)) at 1; rewrite <- Rmult_minus_distr_r.
  apply Rmult_le_compat; lra.
assert (ry2 : round' y2 = y2).
  assert (y2v : y2 = B2R' y * bpow r2 (-e)).
    rewrite yval, Rmult_assoc, <- bpow_plus, Z.add_opp_diag_r; simpl; ring.
  rewrite y2v, round_mult_bpow, ry; unfold fmin, ms, es in cexplb, ege1 |- *;
    [lra | lra | | ]; try lia.
    unfold halfes, halfms in cexplb; lia.
  unfold halfes, halfms in ege1, cexplb; lia.
assert (sval : sqrt (B2R' x) =  bpow r2 e * sqrt x2).
  rewrite xval, sqrt_mult, <- bpow_square;[ | lra | apply bpow_ge_0].
  rewrite sqrt_pow2, Rmult_comm;[easy | apply bpow_ge_0].
rewrite sval, (Rmult_comm (bpow _ _)), <- Rmult_assoc, <-Rmult_minus_distr_r.
rewrite <- Rmult_plus_distr_r.
assert (tmp' := converge_below_16 x2 y2 intx2 inty2).
fold (body_exp_R x2 y2) in tmp'.
assert (5 * ulp1 <= 5 * ulp1 * sqrt x2).
  rewrite <- (Rmult_1_r (_ * _)) at 1.
  apply Rmult_le_compat; lra.
split; apply Rmult_le_compat_r; try apply bpow_ge_0; lra.
Qed.

Lemma invariant_initial_min_1 :
   invariantl (x, Binary.Bone ms es eq_refl eq_refl).
Proof.
split;[reflexivity | ]; simpl; split.
  apply Rle_trans with (sqrt (B2R' x)).
    rewrite <- (Rmult_1_l (sqrt (B2R' x))) at 1 3.
    rewrite <- Rmult_minus_distr_r; apply Rmult_le_compat_r.
      now apply sqrt_ge_0.
    unfold ulp1; simpl; lra.
  apply Rle_trans with 1;[ | compute; lra].
  rewrite <- sqrt_1; apply sqrt_le_1_alt; lra.
compute; lra.
Qed.


Lemma main_loop_min_1 :
  final x (main_loop (x, Binary.Bone ms es eq_refl eq_refl)).
generalize invariant_initial_min_1.
apply main_loop_ind.
  now intros p x' y pxy z test IH v; apply IH, invariantl_spec_min_1.
intros p x' y pxy z test iv.
change (float_div (float_plus y (float_div x' y)) (float_of_Z 2))
with (body_exp x' y) in z.
apply invariant_final_min_1; auto.
subst z. 
destruct iv as [cnd1 cnd2].
rewrite <- cnd1. simpl fst. auto.
Qed.

End interval_min_1.

Definition f_min' :=
  B754_finite ms es false
  match (2 ^ ms')%Z with Z.pos v => v | _ => 1 end
  (6 - es - ms') eq_refl.

Lemma f_min'_val : B2R' f_min' = bpow r2 (6 - es).
Proof. compute; lra. Qed.


Lemma main_loop_correct_min_1 x :
  B2R' f_min' <= B2R' x < 1 ->
  Rabs (B2R' (main_loop (x, Binary.Bone ms es eq_refl eq_refl)) - sqrt (B2R' x)) <=
   5 / (2 ^ Z.to_nat ms') * sqrt (B2R' x).
Proof.
set (s := sqrt _); set (m := B2R' (main_loop _)); set (e := _ / _ * _).
intros intx; apply Rabs_le.
enough (s - e <= m <= s + e) by lra.
replace e with (5 * ulp1 * s); cycle 1.
  unfold e, ulp1, s; rewrite bpow_opp; compute; lra.
now apply main_loop_min_1; rewrite <- f_min'_val.
Qed.

Lemma main_loop_correct_1_max x :
  1 <= B2R ms es x < /2 * B2R ms es predf_max ->
  Rabs (B2R ms es (main_loop (x, x)) - sqrt (B2R ms es x)) <=
       5 / (2 ^ Z.to_nat ms') * sqrt (B2R ms es x).
Proof.
set (s := sqrt _); set (m := B2R ms es (main_loop _)); set (e := _ / _ * _).
intros intx; apply Rabs_le.
enough (s - e <= m <= s + e) by lra.
replace e with (5 * ulp1 * s); cycle 1.
   unfold e, ulp1, s; rewrite bpow_opp; compute; lra.
now apply main_loop_1_max.
Qed.

Open Scope R_scope.

Lemma fsqrt_correct_aux0:
 forall x, 
  Binary.B2R ms es f_min'
   <= Binary.B2R ms es x < Rdefinitions.Rinv 2 * Binary.B2R ms es predf_max ->
  float_cmp Integers.Cle x (float_of_Z 0) = false.
(*
  Binary.Bcompare ms es x (Binary.B754_zero ms es false) = Some Gt.
*)
Proof.
fold (B2R' f_min'); rewrite f_min'_val.
assert (0 < bpow r2 (6 - es)) by apply bpow_gt_0.
intros x [xge_min _].
unfold float_cmp, Floats.cmp_of_comparison, float_compare.
rewrite Bcompare_correct; auto.
rewrite Rcompare_Gt; auto.
change (float_of_Z 0) with (Binary.B754_zero ms es false).
simpl. lra.
apply positive_finite; unfold B2R'; lra.
Qed.

Lemma fsqrt_correct_aux1:
 forall x, 
  1 <= Binary.B2R ms es x < Rdefinitions.Rinv 2 * Binary.B2R ms es predf_max ->
  float_cmp Integers.Cge x (float_of_Z 1) = true.
Proof.
change (float_of_Z 1) with (Bone ms es eq_refl eq_refl).
intros x [[xgt1 | xeq1] _].
-
  unfold float_cmp, Floats.cmp_of_comparison, float_compare.
  rewrite Bcompare_correct;[ |  | auto].
  rewrite Rcompare_Gt; auto.
  rewrite Bone_correct; assumption.
  destruct x; simpl in xgt1; auto; lra.
-
  unfold float_cmp, Floats.cmp_of_comparison, float_compare.
  rewrite Bcompare_correct;[ |  | auto].
  rewrite Rcompare_Eq; auto.
  rewrite Bone_correct; symmetry; assumption.
  destruct x; simpl in xeq1; auto; lra.
Qed.

Open Scope R_scope.

Lemma fsqrt_aux2: 
  forall x, {B2R' x < 1} + {1 <= B2R' x}.
Admitted.

Lemma fsqrt_aux3:
  forall x, B2R' x < 1 -> float_cmp Integers.Cge x (float_of_Z 1) = false.
Admitted.

Lemma fsqrt_correct:
 forall x, 
  B2R' f_min' <= B2R' x < Rdefinitions.Rinv 2 * B2R' predf_max ->
  Rbasic_fun.Rabs (B2R' (fsqrt x) - R_sqrt.sqrt (B2R' x)) <=
       5 / (2 ^ Z.to_nat ms') * R_sqrt.sqrt (B2R' x).
Proof.
intros.
unfold fsqrt.
rewrite fsqrt_correct_aux0 by auto.
assert (finx : is_finite ms es x = true).
  apply positive_finite.
  apply Rlt_le_trans with  (2 := proj1 H).
  compute; lra.
assert (fin_one : is_finite ms es (Bone ms es eq_refl eq_refl) = true).
  now apply is_finite_Bone.
destruct (fsqrt_aux2 x) as [H0|H0].
-
rewrite fsqrt_aux3; auto.
apply main_loop_correct_min_1; split;[ auto | tauto].
apply H.
-
rewrite fsqrt_correct_aux1.
apply main_loop_correct_1_max; split;[ auto | tauto].
unfold B2R' in *.
lra.
Qed.

Close Scope R_scope.



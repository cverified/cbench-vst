Require Import VST.floyd.functional_base.

Definition fsqrt_terminate (xy: float32*float32) : nat :=
  let (x,y) := xy in
  let z := Float32.abs (Float32.sub x (Float32.mul y y))
  in match z with 
     | Binary.B754_zero _ => O
     | Binary.B754_infinity _ => O
     | Binary.B754_nan _ _ _=> O
     | Binary.B754_finite _ m e _ => Pos.to_nat m
     end.

Lemma fsqrt_terminates: forall x y,
 Float32.cmp Clt
  (Float32.div (Float32.add y (Float32.div x y))
     (Float32.of_int (Int.repr 2))) y = true ->
(fsqrt_terminate
   (x,
   Float32.div (Float32.add y (Float32.div x y))
     (Float32.of_int (Int.repr 2))) < fsqrt_terminate (x, y))%nat.
Proof.
Admitted.

Function fsqrt_loop (xy : float32*float32) {measure fsqrt_terminate xy} :
       float32 :=
 let '(x,y) := xy in
 let z' := y in
 let y' :=  Float32.div (Float32.add z' (Float32.div x z'))
                         (Float32.of_int (Int.repr 2)) in
 if Float32.cmp Clt y' z'
 then fsqrt_loop (x,y')
 else y'.
Proof.
intros.
subst.
apply fsqrt_terminates; auto.
Defined.

Definition fsqrt (x: float32) : float32 :=
  if Float32.cmp Cle x (Float32.of_int (Int.repr 0)) 
  then (Float32.of_int (Int.repr 0)) 
  else
  let y := if Float32.cmp Cge x (Float32.of_int (Int.repr 1))
               then x else Float32.of_int (Int.repr 1)  in
  fsqrt_loop (x,y).

Lemma fsqrt_result_aux: 
  forall x y: float32,
Float32.cmp Cgt x Float32.zero = true ->
Float32.cmp Cge y (Float32.of_int (Int.repr 1)) = true ->
Float32.cmp Cge y x = true ->
Float32.cmp Ceq (Float32.mul (fsqrt_loop (x, y)) (fsqrt_loop (x, y))) x =
true.
Admitted.

Lemma fsqrt_result:
  forall x, 
  Float32.cmp Cge x (Float32.of_int (Int.repr 0)) = true ->
  Float32.cmp Ceq (Float32.mul (fsqrt x) (fsqrt x)) x = true.
Proof.
intros.
unfold fsqrt.
rewrite Float32.cmp_ge_gt_eq, orb_true_iff in H. 
destruct H.
2:{ 
rewrite Float32.cmp_le_lt_eq.
rewrite H.
rewrite orb_true_r.
change (Float32.mul (Float32.of_int (Int.repr 0)) (Float32.of_int (Int.repr 0)))
  with (Float32.of_int (Int.repr 0)).
rewrite <- Float32.cmp_swap. auto.
}
rewrite Float32.cmp_le_lt_eq.
destruct (Float32.cmp Clt x (Float32.of_int (Int.repr 0))) eqn:?H.
contradiction (Float32.cmp_lt_gt_false _ _ H0 H).
simpl.
destruct (Float32.cmp Ceq x (Float32.of_int (Int.repr 0))) eqn:?H.
contradiction (Float32.cmp_gt_eq_false _ _ H H1).
clear H0 H1.
set (y := if Float32.cmp Cge x (Float32.of_int (Int.repr 1))
        then x
        else Float32.of_int (Int.repr 1)).
assert (Float32.cmp Cge y (Float32.of_int (Int.repr 1)) = true).
subst y.
destruct (Float32.cmp Cge x (Float32.of_int (Int.repr 1))) eqn:?H.
auto.
reflexivity.
assert (Float32.cmp Cge y x = true). {
 subst y.
destruct (Float32.cmp Cge x (Float32.of_int (Int.repr 1))) eqn:?H.
-
rewrite Float32.cmp_ge_gt_eq.
rewrite orb_true_iff. right.
clear - H.
Transparent Float32.cmp.
unfold Float32.cmp in *.
Opaque Float32.cmp.
simpl in *.
unfold Float32.compare in *.
change (Float32.of_int (Int.repr 0)) with (Binary.B754_zero 24 128 false) in H.
destruct x; simpl in H; try destruct s; inv  H; simpl.
reflexivity.
rewrite Z.compare_refl.
rewrite Pcompare_refl.
auto.
-
rewrite Float32.cmp_ge_gt_eq.
rewrite Float32.cmp_ge_gt_eq in H1. rewrite orb_false_iff in H1.
destruct H1.
rewrite <- Float32.cmp_swap in H2. simpl in H2.
rewrite H2.
rewrite orb_false_r.
clear - H1 H2 H.
change (Float32.of_int (Int.repr 0)) with (Binary.B754_zero 24 128 false) in H.
destruct x; try destruct s; inv H; auto.
change (Float32.of_int (Int.repr 1)) 
  with (Binary.B754_finite 24 128 false 8388608 (-23)
         (proj1
            (Binary.binary_round_correct 24 128 eq_refl eq_refl
               Binary.mode_NE false 1 0))) in *.
set (p := proj1
             (Binary.binary_round_correct 24 128 eq_refl eq_refl
                Binary.mode_NE false 1 0)) in *. clearbody p.
Transparent Float32.cmp.
unfold Float32.cmp in *.
Opaque Float32.cmp.
unfold Float32.compare in *.
simpl.
destruct e; auto.
unfold cmp_of_comparison in *.
unfold Binary.Bcompare in *.
rewrite <- Pos.compare_antisym.
forget 8388608%positive as K.
change (Z.neg p0) with (- (Z.pos p0)) in *.
change (-23)%Z with (Z.opp 23) in H1,H2.
forget 23%positive as J.
rewrite Z.compare_opp in H2,H1.
simpl Z.compare in H1,H2.
rewrite Pos.compare_antisym in H1.
destruct (p0 ?= J)%positive eqn:?H.
simpl in H1,H2|-*.
rewrite <- (Pos.compare_cont_antisym _ _ Eq) in H1.
destruct (Pos.compare_cont Eq K m); auto.
simpl in H1.
inv H1.
auto.
}
clearbody y.
apply fsqrt_result_aux; auto.
Qed.


Require Import VST.floyd.functional_base.

Parameter fsqrt_terminate: forall xy: float32*float32, nat.

Axiom fsqrt_terminates: forall x y,
 Float32.cmp Clt
  (Float32.div (Float32.add y (Float32.div x y))
     (Float32.of_int (Int.repr 2))) y = true ->
(fsqrt_terminate
   (x,
   Float32.div (Float32.add y (Float32.div x y))
     (Float32.of_int (Int.repr 2))) < fsqrt_terminate (x, y))%nat.

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
admit.  (* OK *)
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
admit. (* OK *)
rewrite Float32.cmp_ge_gt_eq.
rewrite Float32.cmp_ge_gt_eq in H1. rewrite orb_false_iff in H1.
destruct H1.
rewrite <- Float32.cmp_swap in H2. simpl in H2.
rewrite H2.
rewrite orb_false_r.
admit. (* OK *)
}
clearbody y.
Admitted.

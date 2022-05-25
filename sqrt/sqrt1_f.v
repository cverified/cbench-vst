From Flocq3 Require Core Binary.
Import Raux.
Require Import Psatz.
Require Import Recdef.
Require Import float_lemmas.
Import Integers.

Definition main_loop_measure (p : float * float) : nat :=
  float_to_nat (snd p).

Function main_loop (xy : float * float) {measure main_loop_measure} : float :=
    let (x,y) := xy in 
   let z := float_div (float_plus y (float_div x y)) (float_of_Z 2) in 
    if float_cmp Clt z y then  main_loop (x, z) else z.
Proof.
intros; apply float_to_nat_lt; auto.
Qed.

Definition fsqrt (x: float) : float :=
  if float_cmp Cle x (float_of_Z 0) 
  then (float_of_Z 0) 
  else
  let y := if float_cmp Cge x (float_of_Z 1)
               then x else float_of_Z 1  in
  main_loop (x,y).


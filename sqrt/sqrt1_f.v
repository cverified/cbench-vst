From Flocq Require Core Binary.
Import Defs Raux FLT Generic_fmt Binary Ulp.
Require Import Psatz.
Require Import Recdef.
Require Import float_lemmas.

Definition main_loop_measure (p : float32 * float32) : nat :=
  float_to_nat (snd p).

(* The beauty of it is that we don't need to know what computation is performed,
  only the test matters. *)
Function main_loop (p : float32 * float32) {measure main_loop_measure} :
   float32 :=
    let (x,y) := p in 
   let z := Float32.div (Float32.add y (Float32.div x y)) (float32_of_Z 2) in 
    if Float32.cmp Integers.Clt z y then  main_loop (x, z) else z.
Proof.
intros; apply float_to_nat_lt; auto.
Qed.

Definition fsqrt (x: float32) : float32 :=
  if Float32.cmp Integers.Cle x (float32_of_Z 0) 
  then (float32_of_Z 0) 
  else
  let y := if Float32.cmp Integers.Cge x (float32_of_Z 1)
               then x else float32_of_Z 1  in
  main_loop (x,y).


From Flocq Require Core Binary.
From Coquelicot Require Import Coquelicot.
Require Import Reals Gappa.Gappa_library Psatz.
Import Defs Raux FLT Generic_fmt Gappa_definitions Binary Ulp.
Require Import FunInd Recdef.

From compcert.lib Require Import Floats Integers.

Transparent Float32.div Float32.add Float32.cmp.

(* Correctness of floating-point absolute value *)
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

Open Scope R_scope.
Lemma sqrt_approx_correct:
 forall x, 
  Rbasic_fun.Rabs (float32_to_real (sqrt_approx_f x) - R_sqrt.sqrt (float32_to_real x)) <=
       (1 + 1/15) * R_sqrt.sqrt (float32_to_real x).
Proof.
Admitted.
Close Scope R_scope.






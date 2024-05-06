Require Import VST.floyd.proofauto.
Require Import sqrt3.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition sqrt_approx_f (x: float32) : float32 :=
  Float32.of_bits
  (Int.add (Int.shru (Float32.to_bits x) (Int.repr 1))
     (Int.repr 532676608)).

Definition sqrt_approx_spec :=
   DECLARE _sqrt_approx
   WITH x: float32
   PRE [ tfloat ]
       PROP () PARAMS (Vsingle x) SEP ()
    POST [ tfloat ]
       PROP () RETURN (Vsingle (sqrt_approx_f x)) SEP ().

Definition Gprog : funspecs :=
         [sqrt_approx_spec].

Lemma body_sqrt_approx:  semax_body Vprog Gprog f_sqrt_approx sqrt_approx_spec.
Proof.
start_function.
forward.
forward.
forward.
forward.
forward.
entailer!.
Qed.


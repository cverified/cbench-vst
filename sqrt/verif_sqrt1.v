Require Import VST.floyd.proofauto.
Require Import sqrt1.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Require Import float_lemmas sqrt1_f.

Definition sqrt_newton_spec :=
   DECLARE _sqrt_newton
   WITH x: float32
   PRE [ tfloat ]
       PROP () PARAMS (Vsingle x) SEP ()
    POST [ tfloat ]
       PROP () RETURN (Vsingle (fsqrt x)) SEP ().

Definition Gprog : funspecs :=
         [sqrt_newton_spec].

Lemma body_sqrt_newton:  semax_body Vprog Gprog f_sqrt_newton sqrt_newton_spec.
Proof.
start_function.
forward_if. (* if (x<=0) *)
forward.  (*  return 0; *) {
   entailer!.
   unfold fsqrt.
   change (float_of_Z ?A) with (Float32.of_int (Int.repr A)).
   change float_cmp with Float32.cmp.
   rewrite H. auto.
}
pose (t := if Float32.cmp Cge x (Float32.of_int (Int.repr 1))
                    then x else Float32.of_int (Int.repr 1)).
forward_if  (* if (x >= 1) *) 
     (temp _t'1 (Vsingle t)).
forward. (* t'1=x; *) {
  entailer!.
  subst t; rewrite H0; auto.
}
forward. (* t'1=1; *) {
  entailer!.
  subst t; rewrite H0; auto.
}
forward. (* y = t'1; *)
forward_loop
   (EX y:float32, PROP(main_loop (x,y) = fsqrt x)
                 (LOCAL (temp _x (Vsingle x); temp _y (Vsingle y)) SEP()))
 continue: (EX y z:float32, PROP((if Float32.cmp Clt y z
                                then main_loop  (x,y) else y) = fsqrt x)
                     (LOCAL (temp _x (Vsingle x); temp _y (Vsingle y); 
                                  temp _z (Vsingle z)) 
                     SEP()))
   break: (PROP()(LOCAL (temp _y (Vsingle (fsqrt x))) SEP())).
-  (* Prove that precondition implies loop invariant *)
Exists t.
entailer!.
unfold fsqrt.
change (float_of_Z ?A) with (Float32.of_int (Int.repr A)).
change float_cmp with Float32.cmp.
rewrite H.
fold t. auto.
-  (* body of loop *)
Intros y.
forward. (* z=y; *)
forward. (* y=(z+x/z)/2; *)
    (* end of loop body; prove invariant is reestablished *)
do 2 EExists; entailer!.
rewrite main_loop_equation in H0.
auto.
-  (* ... while (y<z);  *)
Intros y z.
forward_if.  (* if (y<z) *)
+
forward.  (* skip; *)
Exists y.
entailer!.
rewrite H1 in H0.
auto.
+
forward.  (* break; *)
entailer!.
rewrite H1 in H0.
f_equal; auto.
-
forward. (* return y; *)
Qed.

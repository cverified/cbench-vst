Require Import VST.floyd.proofauto.
Require Import sqrt1.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Require Import model_sqrt1.

Definition sqrt_newton_spec :=
   DECLARE _sqrt_newton
   WITH x: float32
   PRE [ _x OF tfloat ]
       PROP ()
       LOCAL (temp _x (Vsingle x))
       SEP ()
    POST [ tfloat ]
       PROP ()
       LOCAL (temp ret_temp (Vsingle (fsqrt x)))
       SEP ().

Definition Gprog : funspecs :=
         [sqrt_newton_spec].

Lemma body_sqrt_newton:  semax_body Vprog Gprog f_sqrt_newton sqrt_newton_spec.
Proof.
start_function.
forward_if.
forward.
entailer!.
simpl.
unfold fsqrt. rewrite H. auto.
pose (t := if Float32.cmp Cge x (Float32.of_int (Int.repr 1))
                    then x else Float32.of_int (Int.repr 1)).
forward_if (temp _t'1 (Vsingle t)).
forward.
entailer!.
subst t; rewrite H0; auto.
forward.
entailer!.
subst t; rewrite H0; auto.
forward.
deadvars!.
forward_loop
   (EX y:float32, PROP(fsqrt_loop (x,y) = fsqrt x)
                 (LOCAL (temp _x (Vsingle x); temp _y (Vsingle y)) SEP()))
 continue: (EX y z:float32, PROP((if Float32.cmp Clt y z
                                then fsqrt_loop (x,y) else y) = fsqrt x)
                     (LOCAL (temp _x (Vsingle x); temp _y (Vsingle y); 
                                  temp _z (Vsingle z)) 
                     SEP()))
   break: (PROP()(LOCAL (temp _y (Vsingle (fsqrt x))) SEP())).
-
Exists t.
entailer!.
unfold fsqrt.
rewrite H.
fold t. auto.
-
Intros y.
forward.
forward.
do 2 EExists; entailer!.
set (y' :=  Float32.div (Float32.add y (Float32.div x y))
       (Float32.of_int (Int.repr 2))).
rewrite <- H0; clear H0.
symmetry.
rewrite fsqrt_loop_equation.
fold y'.
auto.
-
Intros y z.
forward_if.
+
forward.
Exists y.
entailer!.
rewrite H1 in H0.
auto.
+
forward.
entailer!.
rewrite H1 in H0.
f_equal; auto.
-
forward.
Qed.

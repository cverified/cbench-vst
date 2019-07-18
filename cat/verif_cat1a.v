Require Import VST.progs.io_specs.
Require Import VST.floyd.proofauto.
Require Import cat1a.
Require Import ITree.ITree.
Require Import ITree.Eq.Eq.
(*Import ITreeNotations.*)
Notation "t1 >>= k2" := (ITree.bind t1 k2)
  (at level 50, left associativity) : itree_scope.
Notation "x <- t1 ;; t2" := (ITree.bind t1 (fun x => t2))
  (at level 100, t1 at next level, right associativity) : itree_scope.
Notation "t1 ;; t2" := (ITree.bind t1 (fun _ => t2))
  (at level 100, right associativity) : itree_scope.
Notation "' p <- t1 ;; t2" :=
  (ITree.bind t1 (fun x_ => match x_ with p => t2 end))
(at level 100, t1 at next level, p pattern, right associativity) : itree_scope.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition putchar_spec := DECLARE _putchar putchar_spec.
Definition getchar_spec := DECLARE _getchar getchar_spec.

Definition cat_loop : IO_itree :=
   ITree.aloop (fun _ => inl (c <- read stdin;; write stdout c)) tt.

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre_ext prog cat_loop nil gv
  POST [ tint ] main_post prog nil gv.

Definition Gprog : funspecs := ltac:(with_library prog [putchar_spec; getchar_spec;
  main_spec]).

Lemma cat_loop_eq : cat_loop ≈ (c <- read stdin;; write stdout c;; cat_loop).
Proof.
  intros.
  unfold cat_loop; rewrite unfold_aloop.
  unfold ITree._aloop.
  rewrite tau_eutt, bind_bind.
  apply eqit_bind; try reflexivity.
  intros [].
  apply eqit_bind; try reflexivity.
  intros []; reflexivity.
Qed.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  sep_apply (has_ext_ITREE(file_id := nat)).
  forward_loop (PROP () LOCAL () SEP (ITREE cat_loop))
    break: (PROP () LOCAL () SEP (ITREE cat_loop)).
  - entailer!.
  - rewrite cat_loop_eq.
    forward_call (fun c => write stdout c;; cat_loop).
    Intros c.
    forward.
    forward_if.
    + if_tac.
      { apply f_equal with (f := Int.repr) in H1; rewrite Int.repr_signed in H1; contradiction. }
      forward_call (Byte.repr (Int.signed c), cat_loop).
      { entailer!.
        unfold Vubyte.
        rewrite Byte.unsigned_repr, Int.repr_signed by omega; auto. }
      Intros r.
      forward_if.
      { forward. (* putchar fails; no guarantee about remaining ops *) }
      forward.
      if_tac.
      { apply f_equal with (f := Int.repr) in H4; rewrite Int.repr_signed in H4; contradiction. }
      entailer!.
    + rewrite if_true.
      forward.
      rewrite cat_loop_eq; entailer!.
      { subst.
        rewrite neg_repr, Int.signed_repr by rep_omega; auto. }
  - forward.
Qed.

Definition ext_link := ext_link_prog prog.

Instance Espec : OracleKind := IO_Espec ext_link.

Lemma prog_correct:
  semax_prog_ext prog cat_loop Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons_ext.
{ simpl; Intro i.
  apply typecheck_return_value; auto. }
semax_func_cons_ext.
{ simpl; Intro i'.
  apply typecheck_return_value; auto. }
semax_func_cons body_main.
Qed.

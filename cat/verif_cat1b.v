Require Import VST.floyd.proofauto.
Require Import Top.io_specs_cap.
Require Import Top.cat1.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition event := IO_cap_event +' @IO_event nat.

Definition putchar_spec := DECLARE _putchar putchar_cap_spec(E := event).
Definition getchar_spec := DECLARE _getchar getchar_spec(E := event).

Definition cat_loop : IO_itree :=
   ITree.iter (fun _ => c <- read stdin;; write_cap stdout c; Ret (inl tt)) tt.

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog cat_loop gv
  POST [ tint ] main_post prog gv.

Definition Gprog : funspecs := ltac:(with_library prog [putchar_spec; getchar_spec;
  main_spec]).

Lemma cat_loop_eq : cat_loop ≈ (c <- read stdin;; write_cap stdout c;; cat_loop).
Proof.
  intros.
  unfold cat_loop; rewrite unfold_aloop.
  unfold ITree._aloop.
  rewrite tau_eutt, bind_bind.
  apply eqit_bind; [intro | reflexivity].
  apply eqit_bind; [intros []|]; reflexivity.
Qed.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  sep_apply (has_ext_ITREE(E := event)).
  forward_loop (PROP () LOCAL () SEP (ITREE cat_loop))
    break: (PROP () LOCAL () SEP (ITREE cat_loop)).
  - entailer!.
  - rewrite cat_loop_eq.
    forward_call (fun c => write_cap stdout c;; cat_loop).
    Intros c.
    forward.
    forward_if.
    + if_tac.
      { apply f_equal with (f := Int.repr) in H1; rewrite Int.repr_signed in H1; contradiction. }
      forward_call (Byte.repr (Int.signed c), cat_loop).
      { entailer!.
        unfold Vubyte.
        rewrite Byte.unsigned_repr, Int.repr_signed by lia; auto. }
      entailer!.
    + rewrite if_true.
      forward.
      rewrite cat_loop_eq; entailer!.
      { subst.
        rewrite neg_repr, Int.signed_repr by rep_lia; auto. }
  - forward.
Qed.

Definition ext_link := ext_link_prog prog.

Instance Espec : OracleKind := IO_Espec(E := event) ext_link.

Lemma prog_correct:
  semax_prog prog cat_loop Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons_ext.
{ simpl; Intro j.
  apply typecheck_return_value with (t := Tint16signed); auto. }
semax_func_cons_ext.
{ apply typecheck_return_value with (t := Tint16signed); auto; apply I. }
semax_func_cons body_main.
Qed.

Require Import VST.floyd.proofauto.
Require Import Top.io_specs_rollback.
Require Import Top.cat1.
Require Import ITree.Eq.Eqit.

Unset SsrRewrite.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition event := nondetE +' @IO_event nat.

Section IO.

Context `{!VSTGS (@IO_itree event) Σ}.

Definition putchar_spec := DECLARE _putchar putchar_spec(E := event).
Definition getchar_spec := DECLARE _getchar getchar_spec(E := event).

Open Scope itree_scope.
Definition cat_loop : IO_itree :=
   ITree.iter (E := event) (fun _ => c <- read stdin;; or (write stdout c) (Ret tt);; Ret (inl tt)) tt.

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog cat_loop gv
  POST [ tint ] main_post prog gv.

Definition Gprog : funspecs := ltac:(with_library prog [putchar_spec; getchar_spec;
  main_spec]).

Lemma cat_loop_eq : cat_loop ≈ (c <- read stdin;; or (write stdout c;; cat_loop) (cat_loop)).
Proof.
  intros.
  unfold cat_loop; rewrite unfold_iter.
  unfold ITree.iter.
  rewrite bind_bind.
  apply eqit_bind; [reflexivity | intro ].
  unfold or; rewrite !bind_vis.
  apply eqit_Vis; intros [|].
  - rewrite bind_bind; apply eqit_bind; [| intros []]; try reflexivity.
    rewrite bind_ret_l.
    apply eqit_Tau_l; reflexivity.
  - rewrite !bind_ret_l.
    apply eqit_Tau_l; reflexivity.
Qed.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  pose proof (has_ext_ITREE(E := event)).
  sep_apply (has_ext_ITREE(E := event)).
  forward_loop (PROP () LOCAL () SEP (ITREE cat_loop))
    break: (PROP () LOCAL () SEP (ITREE cat_loop)).
  - entailer!.
  - rewrite cat_loop_eq.
    forward_call_io (fun c => or (write stdout c;; cat_loop) (cat_loop)).
    Intros c.
    forward.
    forward_if.
    + if_tac.
     * apply f_equal with (f := Int.repr) in H2. rewrite Int.repr_signed in H2; contradiction.
     * forward_call_io (Byte.repr (Int.signed c), cat_loop).
      -- entailer!.
        unfold Vubyte. simpl.
        rewrite Byte.unsigned_repr, Int.repr_signed by lia; auto.
      -- apply or_case1.
      -- Intros r. entailer!.
         if_tac; [|apply derives_refl].
         apply ITREE_impl'.
         apply or_case2.
    + rewrite if_true
       by (subst; rewrite neg_repr, Int.signed_repr by rep_lia; auto).
      forward.
      rewrite cat_loop_eq; entailer!.
  - forward.
Qed.

Definition ext_link := ext_link_prog prog.

#[local] Instance IO_Espec : ext_spec IO_itree := IO_ext_spec(E := event) ext_link.

Lemma prog_correct:
  semax_prog prog cat_loop Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons_ext.
{ destruct x; monPred.unseal; simpl; Intro j.
  apply typecheck_return_value with (t := Tint16signed); auto. }
semax_func_cons_ext.
{ destruct x as ((?, ?), ?); monPred.unseal; simpl; Intro j.
  apply typecheck_return_value with (t := Tint16signed); auto; apply I. }
semax_func_cons body_main.
Qed.

End IO.

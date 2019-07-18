Require Import VST.floyd.proofauto.
Require Import fio_specs.
Require Import cat2.
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

Instance file_struct : FileStruct := {| FILEid := ___sFILE64; reent := __reent; f_stdin := __stdin; f_stdout := __stdout |}.

Definition fwrite_spec := DECLARE _fwrite fwrite_spec.
Definition fread_spec := DECLARE _fread fread_spec.
Definition get_reent_spec := DECLARE ___getreent get_reent_spec.

Notation buf_size := 131072%nat.
Notation buf_size_Z := 131072%Z.

Definition cat_loop : IO_itree :=
   ITree.aloop (fun _ => inl (c <- read_list stdin buf_size;; write_list stdout c)) tt.

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre_ext prog cat_loop nil gv
  POST [ tint ] main_post prog nil gv.

Definition Gprog : funspecs := ltac:(with_library prog [get_reent_spec; fwrite_spec; fread_spec;
  main_spec]).

Lemma cat_loop_eq : cat_loop ≈ (c <- read_list stdin buf_size;; write_list stdout c;; cat_loop).
Proof.
  intros.
  unfold cat_loop; rewrite unfold_aloop.
  unfold ITree._aloop.
  rewrite tau_eutt, bind_bind.
  apply eqit_bind; try reflexivity.
  intro; apply eqit_bind; try reflexivity.
  intros []; reflexivity.
Qed.

Lemma buf_size_eq : Z.to_nat buf_size_Z = buf_size.
Proof. reflexivity. Qed.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  sep_apply (has_ext_ITREE(file_id := nat)).
  sep_apply init_stdio; Intros reentp inp outp inp' outp'; simpl in inp', outp'.
  change (reptype (tptr (Tstruct ___sFILE64 noattr))) with val in *.
  repeat match goal with H : JMeq _ _ |- _ => apply JMeq_eq in H; subst end.
  forward_loop (PROP () LOCAL (gvars gv) SEP (reent_struct reentp;
   field_at Ews (Tstruct reent noattr) [StructField f_stdin] inp reentp;
   field_at Ews (Tstruct reent noattr) [StructField f_stdout] outp reentp;
   file_at stdin inp; file_at stdout outp; ITREE cat_loop;
   data_at_ Ews (tarray tschar 131072) (gv _buf)))
    break: (PROP () LOCAL (gvars gv) SEP (reent_struct reentp;
   field_at Ews (Tstruct reent noattr) [StructField f_stdin] inp reentp;
   field_at Ews (Tstruct reent noattr) [StructField f_stdout] outp reentp;
   file_at stdin inp; file_at stdout outp; ITREE cat_loop;
   data_at_ Ews (tarray tschar 131072) (gv _buf))).
  - entailer!.
  - forward_call.
    forward.
    erewrite ITREE_ext by (apply cat_loop_eq). (* for some reason, rewrite cat_loop_eq is slow here *)
    forward_call (Ews, gv _buf, 1, buf_size_Z, stdin, inp, fun c => write_list stdout c;; cat_loop).
    { simpl Z.mul; rewrite buf_size_eq; simpl; cancel. }
    Intros bytes.
    assert_PROP (Zlength bytes = buf_size_Z) as Hbytes.
    { entailer!.
      rewrite Zlength_map in *; auto. }
    forward.
    forward.
    forward_if.
    forward_call.
    forward.
    forward_call (Ews, gv _buf, buf_size_Z, bytes, 1, buf_size_Z, @nil val, stdout, outp, cat_loop).
    { rewrite app_nil_r; cancel. }
    entailer!.
    { forward.
      discriminate. (* At the moment, we assume that fread blocks until it can fill the buffer, but this probably isn't realistic. *) }
  - forward.
Qed.

Definition ext_link := ext_link_prog prog.

Instance Espec : OracleKind := IO_Espec ext_link.

Lemma prog_correct:
  semax_prog_ext prog cat_loop Vprog Gprog.
Proof.
Time prove_semax_prog. (* giant struct makes this run forever (or just for a long time) *)
semax_func_cons_ext.
{ simpl; Intro i.
  apply typecheck_return_value; auto. }
semax_func_cons_ext.
{ simpl; Intro i'.
  apply typecheck_return_value; auto. }
semax_func_cons body_main.
Qed.*)
Admitted.

Require Import VST.floyd.proofauto.
Require Import Top.fio_specs.
Require Import Top.cat2.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Instance file_struct : FileStruct := {| FILEid := ___sFILE64; reent := __reent; f_stdin := __stdin; f_stdout := __stdout |}.

Definition event := nondetE +' @IO_event file_id.

Definition fwrite_spec := DECLARE _fwrite fwrite_spec(E := event).
Definition fread_spec := DECLARE _fread fread_spec(E := event).
Definition get_reent_spec := DECLARE ___getreent get_reent_spec.

Notation buf_size := 131072%nat.
Notation buf_size_Z := 131072%Z.

Definition cat_loop : IO_itree(E := event) :=
   ITree.iter (fun _ => c <- read_list stdin buf_size;; write_list stdout c;; Ret (inl tt)) tt.

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog cat_loop gv
  POST [ tint ] main_post prog gv.

Definition Gprog : funspecs := ltac:(with_library prog [get_reent_spec; fwrite_spec; fread_spec;
  main_spec]).

Lemma cat_loop_eq : cat_loop ≈ (c <- read_list stdin buf_size;; write_list stdout c;; cat_loop).
Proof.
  intros.
  unfold cat_loop; rewrite unfold_iter.
  unfold ITree._iter.
  rewrite bind_bind.
  apply eqit_bind; try reflexivity.
  intro; rewrite bind_bind; apply eqit_bind; try reflexivity.
  intros [].
  rewrite bind_ret_l, tau_eutt; reflexivity.
Qed.

Lemma buf_size_eq : Z.to_nat buf_size_Z = buf_size.
Proof. reflexivity. Qed.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  sep_apply (has_ext_ITREE(E := event)).
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
    forward.
    forward.
    forward_if.
    forward_call.
    forward.
    forward_call (Ews, gv _buf, buf_size_Z, bytes, 1, Zlength bytes,
      repeat Vundef (Z.to_nat (buf_size_Z - Zlength bytes)), stdout, outp, cat_loop).
    { rewrite Z.mul_1_l; auto. }
    entailer!.
    { forward.
      entailer!.
      assert (Zlength bytes = 0) as ?%Zlength_nil_inv; [|subst; simpl; rewrite bind_ret_l; auto].
      rewrite Zlength_app, Zlength_map, repeat_list_repeat, Zlength_list_repeat' in H1.
      assert (0 <= 1 * 131072 - Zlength bytes) by omega.
      rewrite Int.unsigned_repr in *; rep_omega. }
  - forward.
Qed.

Definition ext_link := ext_link_prog prog.

Instance Espec : OracleKind := IO_Espec ext_link.

Lemma prog_correct:
  semax_prog prog cat_loop Vprog Gprog.
Proof.
(*Time prove_semax_prog. (* giant struct makes this run forever *)
semax_func_cons_ext.
{ simpl; Intro i.
  apply typecheck_return_value; auto. }
semax_func_cons_ext.
{ simpl; Intro i'.
  apply typecheck_return_value; auto. }
semax_func_cons body_main.
Qed.*)
Admitted.

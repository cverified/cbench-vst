Require Import VST.floyd.proofauto.
Require Import VST.veric.juicy_extspec.
Require Export VST.floyd.printf.
Require Import ITree.ITree.
Require Export ITree.Eq.Eq.
Require Export ITree.Eq.SimUpToTaus.
(* Import ITreeNotations. *) (* one piece conflicts with subp notation *)
Notation "t1 >>= k2" := (ITree.bind t1 k2)
  (at level 50, left associativity) : itree_scope.
Notation "x <- t1 ;; t2" := (ITree.bind t1 (fun x => t2))
  (at level 100, t1 at next level, right associativity) : itree_scope.
Notation "t1 ;; t2" := (ITree.bind t1 (fun _ => t2))
  (at level 100, right associativity) : itree_scope.
Notation "' p <- t1 ;; t2" :=
  (ITree.bind t1 (fun x_ => match x_ with p => t2 end))
(at level 100, t1 at next level, p pattern, right associativity) : itree_scope.

Fixpoint read_list_aux {file_id : Type} f n d : itree (@IO_event file_id) (list byte) :=
  match n with
  | O => Ret d
  | S n' => x <- read f ;; read_list_aux f n' (x :: d)
  end.

Definition read_list {file_id : Type} f n : itree (@IO_event file_id) (list byte) := read_list_aux f n [].

Class FileStruct := { abs_file :> FileId; FILEid : ident; reent : ident; f_stdin : ident; f_stdout : ident }.

Instance nat_id : FileId := { file_id := nat; stdin := 0%nat; stdout := 1%nat }.

Section fio_specs.

Context {CS : compspecs}.
Context `{FileStruct}.

Axiom reent_struct : val -> mpred.

Axiom init_stdio : emp |-- EX p : val, EX inp : val, EX outp : val, EX inp' : _, EX outp' : _,
  !!(JMeq inp' inp /\ JMeq outp' outp) && reent_struct p *
  field_at Ews (Tstruct reent noattr) [StructField f_stdin] inp' p *
  field_at Ews (Tstruct reent noattr) [StructField f_stdout] outp' p *
  file_at stdin inp * file_at stdout outp.

Definition get_reent_spec :=
  WITH p : val
  PRE [ ]
    PROP ()
    LOCAL ()
    SEP (reent_struct p)
  POST [ tptr (Tstruct reent noattr) ]
    PROP ()
    LOCAL (temp ret_temp p)
    SEP (reent_struct p).

Definition fwrite_spec {CS : compspecs} :=
  WITH sh : share, buf : val, len : Z, msg : list byte, sz : Z, count : Z, rest : list val, f : _, fp : val, k : IO_itree
  PRE [ 1%positive OF tptr tvoid, 2%positive OF tuint, 3%positive OF tuint, 4%positive OF tptr (Tstruct FILEid noattr) ]
    PROP (readable_share sh; Zlength msg = (sz * count)%Z)
    LOCAL (temp 1%positive buf; temp 2%positive (Vint (Int.repr sz));
               temp 3%positive (Vint (Int.repr count)); temp 4%positive fp)
    SEP (ITREE (write_list f msg;; k); file_at f fp;
           data_at sh (tarray tschar len) (map Vbyte msg ++ rest) buf)
  POST [ tuint ]
    PROP ()
    LOCAL (temp ret_temp (Vint (Int.repr (Zlength msg))))
    SEP (ITREE k; file_at f fp;
           data_at sh (tarray tschar len) (map Vbyte msg ++ rest) buf).

Definition fread_spec {CS : compspecs} :=
  WITH sh : share, buf : val, sz : Z, count : Z, f : _, fp : val, k : list byte -> IO_itree
  PRE [ 1%positive OF tptr tvoid, 2%positive OF tuint, 3%positive OF tuint, 4%positive OF tptr (Tstruct FILEid noattr) ]
    PROP (writable_share sh)
    LOCAL (temp 1%positive buf; temp 2%positive (Vint (Int.repr sz));
               temp 3%positive (Vint (Int.repr count)); temp 4%positive fp)
    SEP (ITREE (r <- read_list f (Z.to_nat (sz * count)) ;; k r); file_at f fp; data_at_ sh (tarray tschar (sz * count)) buf)
  POST [ tuint ]
   EX msg : list byte,
    PROP ()
    LOCAL (temp ret_temp (Vint (Int.repr (sz * count))))
    SEP (ITREE (k msg); file_at f fp; data_at sh (tarray tschar (sz * count)) (map Vbyte msg) buf).

(* Build the external specification. *)
Definition IO_void_Espec : OracleKind := ok_void_spec (@IO_itree nat).

Definition IO_specs {CS : compspecs} (ext_link : string -> ident) :=
  [(ext_link "__getreent"%string, get_reent_spec); (ext_link "fwrite"%string, fwrite_spec);
   (ext_link "fread"%string, fread_spec)].

Definition IO_Espec {CS : compspecs} (ext_link : string -> ident) : OracleKind :=
  add_funspecs IO_void_Espec ext_link (IO_specs ext_link).

End fio_specs.

Require Import VST.floyd.proofauto.
Require Import VST.veric.juicy_extspec.
Require Export VST.floyd.printf.
Require Export ITree.Eq.Eq.
Require Export ITree.Eq.SimUpToTaus.
Require Export ITree.Events.Nondeterminism.
Notation "x <- t1 ;; t2" := (ITree.bind t1 (fun x => t2))
  (at level 100, t1 at next level, right associativity) : itree_scope.
Notation "' p <- t1 ;; t2" :=
  (ITree.bind t1 (fun x_ => match x_ with p => t2 end))
(at level 100, t1 at next level, p pattern, right associativity) : itree_scope.

Lemma or_case1 : forall {E R} `{nondetE -< E} a b, sutt eq a (or(R := R) a b).
Proof.
  intros; unfold or.
Admitted.

Lemma or_case2 : forall {E R} `{nondetE -< E} a b, sutt eq b (or(R := R) a b).
Proof.
  intros; unfold or.
Admitted.

Instance nat_id : FileId := { file_id := nat; stdin := 0%nat; stdout := 1%nat }.

Section fio_specs.

Context {E : Type -> Type} `{nondetE -< E} `{@IO_event file_id -< E}.

Fixpoint read_list_aux f n d : itree E (list byte) :=
  match n with
  | O => Ret d
  | S n' => or (x <- read f ;; read_list_aux f n' (x :: d)) (read_list_aux f n' d)
  end.

Definition read_list f n : itree E (list byte) := read_list_aux f n [].

Context {CS : compspecs}.
Context `{FileStruct}.

(* In reality, this might also fail to write all the characters (unless it's a capability version). *)
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
    SEP (ITREE (r <- read_list f (Z.to_nat (sz * count)) ;; k r); file_at f fp;
           data_at_ sh (tarray tschar (sz * count)) buf)
  POST [ tuint ]
   EX msg : list byte,
    PROP ()
    LOCAL (temp ret_temp (Vint (Int.repr (Zlength msg))))
    SEP (ITREE (k msg); file_at f fp;
           data_at sh (tarray tschar (sz * count)) (map Vbyte msg ++ repeat Vundef (Z.to_nat (sz * count - Zlength msg))) buf).

(* Build the external specification. *)
Definition IO_void_Espec : OracleKind := ok_void_spec (@IO_itree E).

Definition IO_specs {CS : compspecs} (ext_link : string -> ident) :=
  [(ext_link "__getreent"%string, get_reent_spec); (ext_link "fwrite"%string, fwrite_spec);
   (ext_link "fread"%string, fread_spec)].

Definition IO_Espec {CS : compspecs} (ext_link : string -> ident) : OracleKind :=
  add_funspecs IO_void_Espec ext_link (IO_specs ext_link).

End fio_specs.

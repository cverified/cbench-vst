Require Import VST.veric.juicy_extspec.
Require Import VST.floyd.proofauto.
Require Export VST.floyd.io_events.
Require Export ITree.ITree.
Require Export ITree.Eq.Eq.
Notation "x <- t1 ;; t2" := (ITree.bind t1 (fun x => t2))
  (at level 100, t1 at next level, right associativity) : itree_scope.
Notation "' p <- t1 ;; t2" :=
  (ITree.bind t1 (fun x_ => match x_ with p => t2 end))
(at level 100, t1 at next level, p pattern, right associativity) : itree_scope.

Definition stdin := 0%nat.
Definition stdout := 1%nat.

Inductive IO_cap_event : Type -> Type :=
| EWriteCap : nat -> byte -> IO_cap_event unit.

Section specs.

Context {E : Type -> Type} `{IO_cap_event -< E}.

Definition write_cap f c := embed (EWriteCap f c).

Context `{@IO_event nat -< E}.

(* A write_cap event guarantees that the write will succeed, either because the OS has set aside
  resources sufficient to guarantee it, or because it will block until it succeeds. *)
Definition putchar_cap_spec :=
  WITH c : byte, k : IO_itree
  PRE [ 1%positive OF tint ]
    PROP ()
    LOCAL (temp 1%positive (Vubyte c))
    SEP (ITREE (write_cap stdout c ;; k))
  POST [ tint ]
    PROP ()
    LOCAL (temp ret_temp (Vubyte c))
    SEP (ITREE k).

Definition getchar_spec :=
  WITH k : byte -> IO_itree
  PRE [ ]
    PROP ()
    LOCAL ()
    SEP (ITREE (r <- read stdin ;; k r))
  POST [ tint ]
   EX i : int,
    PROP (-1 <= Int.signed i <= Byte.max_unsigned)
    LOCAL (temp ret_temp (Vint i))
    SEP (ITREE (if eq_dec (Int.signed i) (-1) then (r <- read stdin ;; k r) else k (Byte.repr (Int.signed i)))).

(* Build the external specification. *)
Definition IO_void_Espec : OracleKind := ok_void_spec (@IO_itree E).

Definition IO_specs (ext_link : string -> ident) :=
  [(ext_link "putchar"%string, putchar_cap_spec); (ext_link "getchar"%string, getchar_spec)].

Definition IO_Espec (ext_link : string -> ident) : OracleKind := add_funspecs IO_void_Espec ext_link (IO_specs ext_link).

End specs.

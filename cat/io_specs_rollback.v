Require Import VST.veric.juicy_extspec.
Require Import VST.floyd.proofauto.
Require Export VST.floyd.io_events.
Require Export ITree.ITree.
Require Export ITree.Eq.SimUpToTaus.
Require Export ITree.Events.Nondeterminism.

(* these should be in ITrees *)
Instance Reflexive_sutt {E R} : RelationClasses.Reflexive (@sutt E R R eq).
Proof. intro; apply eutt_sutt; reflexivity. Qed.

Lemma or_case1 : forall {E R} `{nondetE -< E} a b, sutt eq a (or(R := R) a b).
Proof.
  intros; unfold or.
Admitted.

Lemma or_case2 : forall {E R} `{nondetE -< E} a b, sutt eq b (or(R := R) a b).
Proof.
  intros; unfold or.
Admitted.

Definition stdin := 0%nat.
Definition stdout := 1%nat.

Section specs.

Context {E : Type -> Type} `{IO_event(file_id := nat) -< E}.

(* If putchar fails, we shouldn't be forced to commit to writing. *)
Definition putchar_spec :=
  WITH c : byte, k : IO_itree, t : IO_itree
  PRE [ 1%positive OF tint ]
    PROP (sutt eq (write stdout c;; k) t)
    LOCAL (temp 1%positive (Vubyte c))
    SEP (ITREE t)
  POST [ tint ]
   EX i : int,
    PROP (Int.signed i = -1 \/ Int.signed i = Byte.unsigned c)
    LOCAL (temp ret_temp (Vint i))
    SEP (ITREE (if eq_dec (Int.signed i) (-1) then t else k)).

Definition getchar_spec :=
  WITH k : byte -> IO_itree, t : IO_itree
  PRE [ ]
    PROP (sutt eq (r <- read stdin ;; k r) t)
    LOCAL ()
    SEP (ITREE t)
  POST [ tint ]
   EX i : int,
    PROP (-1 <= Int.signed i <= Byte.max_unsigned)
    LOCAL (temp ret_temp (Vint i))
    SEP (ITREE (if eq_dec (Int.signed i) (-1) then t else k (Byte.repr (Int.signed i)))).

(* Build the external specification. *)
Definition IO_void_Espec : OracleKind := ok_void_spec (@IO_itree E).

Definition IO_specs (ext_link : string -> ident) :=
  [(ext_link "putchar"%string, putchar_spec); (ext_link "getchar"%string, getchar_spec)].

Definition IO_Espec (ext_link : string -> ident) : OracleKind := add_funspecs IO_void_Espec ext_link (IO_specs ext_link).

End specs.

Ltac forward_call_io w := lazymatch goal with |- context[ITREE ?t] => forward_call (w, t); try reflexivity end.

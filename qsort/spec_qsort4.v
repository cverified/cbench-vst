Require Import VST.floyd.proofauto.
Require Import qsort4a.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Fixpoint no_volatiles' {cs: compspecs} (rank: nat) (t: type) :=
  match t with
  | Tvoid => true
  | Tint _ _ a => negb (attr_volatile a)
  | Tlong _ a => negb (attr_volatile a)
  | Tfloat _ a => negb (attr_volatile a)
  | Tpointer _ a => negb (attr_volatile a)
  | Tarray _ _ a => negb (attr_volatile a)
  | Tfunction _ _ _ => true
  | Tstruct id a => 
      match rank with O => false | S rank' =>
       match cenv_cs ! id with
                           Some co => 
                              andb (negb (attr_volatile co.(co_attr)))
                              (forallb (no_volatiles' rank')
                                 (map snd co.(co_members)))
                           | None => false
                           end end
  | Tunion id a => 
      match rank with O => false | S rank' =>
       match cenv_cs ! id with
                           Some co => 
                              andb (negb (attr_volatile co.(co_attr)))
                              (forallb (no_volatiles' rank')
                                 (map snd co.(co_members)))
                           | None => false
                           end end             
 end.

Definition no_volatiles {cs: compspecs} (t: type) : Prop :=
 no_volatiles' (rank_type cenv_cs t) t = true.

Definition memcpy_spec {cs: compspecs} :=
  DECLARE _memcpy 
  WITH wsh: share, rsh: share, d: val, s: val,  v : sigT reptype
  PRE [ tptr tvoid, tptr tvoid, size_t ]
    PROP(writable_share wsh; readable_share rsh;
             no_volatiles (projT1 v)) 
    PARAMS(d; s; Vptrofs (Ptrofs.repr (sizeof (projT1 v)))) GLOBALS ()
    SEP(data_at_ wsh (projT1 v) d;
          data_at rsh (projT1 v) (projT2 v) s)
  POST [ tptr tvoid ]
    PROP() 
    LOCAL(temp ret_temp d)
    SEP(data_at wsh (projT1 v) (projT2 v) d;
          data_at rsh (projT1 v) (projT2 v) s).

Require Import float_lemmas.
Require Import Permutation.
Definition compare_type :=
   tptr (Tfunction (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tint cc_default).

Record le_order (t: Type) := {
 ord_le: t -> t -> Prop;
 ord_le_trans: transitive t ord_le;
 ord_le_total: forall x y, ord_le x x -> ord_le y y -> ord_le x y \/ ord_le y x
}.
Arguments ord_le {t} _ _ _.

Definition ord_eq {t} ord x y := @ord_le t ord x y /\ @ord_le t ord y x.
Definition ord_ge {t} ord x y := @ord_le t ord y x.
Definition ord_def {t} ord x := @ord_le t ord x x.
Definition ord_lt {t} ord x y := @ord_le t ord x y /\ ~@ord_le t ord y x.

Definition compare_spec (t: type) (ord: le_order (reptype t)) :=
  WITH shp: share, shq: share, p: val, q: val, x: reptype t, y: reptype t
  PRE [ tptr tvoid, tptr tvoid ]
    PROP (readable_share shp; readable_share shq; ord_def ord x; ord_def ord y)
    PARAMS (p; q) GLOBALS()
    SEP (data_at shp t x p; data_at shq t y q)
  POST [ tint ]
   EX c:Datatypes.comparison,
    PROP (match c with
              | Eq => ord_eq ord x y
              | Lt => ord_lt ord x y
              | Gt => ord_lt ord y x
             end)
    LOCAL (temp ret_temp (Vint (Int.repr 
                (match c with
              | Eq => 0
              | Lt => -1
              | Gt => 1
             end))))
    SEP (data_at shp t x p; data_at shq t y q).

Record qsort_witness {cs: compspecs} := {
 qsort_t: type;
 qsort_ok: 
             complete_legal_cosu_type qsort_t = true /\
             align_compatible_rec cenv_cs qsort_t 0 /\
             no_volatiles qsort_t;
 qsort_ord: le_order (reptype qsort_t);
 qsort_al: list (reptype qsort_t);
 qsort_def: Forall (ord_def qsort_ord) qsort_al
}.

Definition qsort_spec {cs: compspecs} :=
 DECLARE _qsort
  WITH sh: share, base: val, compar: val, wit: qsort_witness
  PRE  [ (*_base *) tptr tvoid, (*_nmemb *) size_t, 
           (* _size *) size_t, (*  _compar *) compare_type ]
    PROP(writable_share sh;
             sizeof (qsort_t wit) <= 1024; 
             Zlength (qsort_al wit) <= Int.max_signed;
             Zlength (qsort_al wit) * sizeof (qsort_t wit) <= Int.max_signed)
    PARAMS(base; 
                 Vint (Int.repr (Zlength (qsort_al wit)));
                 Vint (Int.repr (sizeof (qsort_t wit))); 
                  compar)  
    GLOBALS ()
    SEP(func_ptr' (compare_spec (qsort_t wit) (qsort_ord wit)) compar;
          data_at sh (tarray (qsort_t wit) (Zlength (qsort_al wit))) (qsort_al wit) base)
  POST [ tvoid ]
    EX bl: list (reptype (qsort_t wit)),
     PROP(Permutation (qsort_al wit) bl; 
              sorted (ord_le (qsort_ord wit)) bl) 
     LOCAL ()
    SEP (data_at sh (tarray (qsort_t wit) (Zlength (qsort_al wit))) bl base).

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog tt gv
  POST [ tint ]  
     PROP() 
     LOCAL (temp ret_temp (Vint (Int.repr 0)))
     SEP(TT).

Definition f_le (x y: val) := def_float x /\ def_float y /\ f_cmp Cle x y.

Definition double_le_order : le_order val.
refine (Build_le_order val f_le _ _).
-
intros.
hnf; intros.
destruct H as [? [? ?]].
destruct H0 as [? [? ?]].
split3; auto.
eapply f_cmp_le_trans; eassumption.
-
intros.
destruct H as [? [? ?]].
destruct H0 as [? [? ?]].
destruct x; try contradiction.
destruct y; try contradiction.
rename f into x. rename f0 into y.
pose proof (f_cmp_false Cle x y H H0).
simpl in H5.
pose proof (f_cmp_swap Cgt (Vfloat x) (Vfloat y)).
simpl in H6.
unfold f_le.
simpl.
destruct (Float.cmp Cle x y) eqn:?H.
intuition.
spec H5. auto.
specialize (H6 H5); clear H5.
right.
split3; auto.
rewrite Float.cmp_le_lt_eq.
rewrite orb_true_iff.
auto.
Defined.

Definition compar_double_spec :=
  DECLARE _compar_double 
  (compare_spec tdouble double_le_order).

Definition N6: Z := proj1_sig (opaque_constant 666666).
Definition N6_eq: N6 = 666666  := proj2_sig (opaque_constant _).
Hint Rewrite N6_eq : rep_omega.

Require Import float_lemmas.

Definition Gprog : funspecs :=
  [ qsort_spec; compar_double_spec; memcpy_spec ].










Require Import VST.floyd.proofauto.
Require Import malloc2.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Open Scope logic.  (* this should not be necessary *)

Definition HEAPSIZE := proj1_sig (opaque_constant 1000).
Definition HEAPSIZE_eq : HEAPSIZE = 1000 := proj2_sig (opaque_constant _).
Hint Rewrite HEAPSIZE_eq : rep_lia.

Definition tcell := Tunion _cell noattr.

Definition idT := ltac:(
   let x := constr:(fn_return f_T_alloc) in
   let x := eval simpl in x in
   match x with tptr (Tstruct ?i _) => exact i end).

Definition tT := Tstruct idT noattr.

Fixpoint freelistrep (n: nat) (x: val) : mpred :=
 match n with
 | S n' => 
    EX y:val, 
      data_at Ews tcell (inr y) x  *  freelistrep n' y
 | O => 
    !! (x = nullval) && emp
 end.

Arguments freelistrep n x : simpl never.

(** Whenever you define a new spatial operator, such as
 ** [listrep] here, it's useful to populate two hint databases.
 ** The [saturate_local] hint is a lemma that extracts
 ** pure propositional facts from a spatial fact.
 ** The [valid_pointer] hint is a lemma that extracts a
 ** valid-pointer fact from a spatial lemma.
 **)

Lemma freelistrep_local_facts:
  forall n p,
   freelistrep n p |--
   !! (is_pointer_or_null p /\ (p=nullval <-> n=O)).
Proof.
intros.
revert p; induction n; intros; unfold freelistrep; fold freelistrep; simpl.
- entailer!. intuition.
- Intros y. entailer!.
split; intro. subst p. destruct H; contradiction. inv H2.
Qed.

Hint Resolve freelistrep_local_facts : saturate_local.

Lemma freelistrep_valid_pointer:
  forall n p,
   freelistrep n p |-- valid_pointer p.
Proof.
 destruct n; unfold freelistrep; fold freelistrep;
 intros; normalize.
 auto with valid_pointer.
 apply sepcon_valid_pointer1.
 apply data_at_valid_ptr; auto.
 simpl;  computable.
Qed.

Hint Resolve freelistrep_valid_pointer : valid_pointer.

Definition mem_mgr (k: Z) (gv: globals) :=
 EX r:Z, EX n: nat, EX p: val, 
   !! (0 <= r <= HEAPSIZE /\ k = (HEAPSIZE-r)+(Z.of_nat n)
       /\ field_compatible (tarray tcell HEAPSIZE) nil (gv _heap)) &&
   data_at Ews (tptr tcell) p (gv _first_free) *
   freelistrep n p *
   data_at Ews (tptr tcell) 
           (field_address0 (tarray tcell HEAPSIZE) [ArraySubsc r] (gv _heap))
           (gv _limit) *
   data_at_ Ews (tarray tcell (HEAPSIZE-r)) 
       (field_address0 (tarray tcell HEAPSIZE) [ArraySubsc r] (gv _heap)).

Definition T_alloc_token (p: val) : mpred :=
  !! (field_compatible tcell [] p) && data_at_ Ews tT p -* data_at_ Ews tcell p.

Definition T_alloc_spec :=
   DECLARE _T_alloc
   WITH k: Z, gv: globals
   PRE [ ]
       PROP ()
       PARAMS() GLOBALS(gv)
       SEP (mem_mgr k gv)
    POST [ tptr tT ] EX p:val,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (if zlt 0 k
             then (mem_mgr (k-1) gv * data_at_ Ews tT p * T_alloc_token p)
             else (!!(p=nullval) &&  mem_mgr k gv)).

Definition T_free_spec :=
   DECLARE _T_free
   WITH p: val, k: Z, gv: globals
   PRE [ tptr tT ]
       PROP ()
       PARAMS (p) GLOBALS (gv)
       SEP (data_at_ Ews tT p; T_alloc_token p; mem_mgr k gv)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (mem_mgr (k+1) gv).

Definition vstrcpy_spec :=
   DECLARE _vstrcpy
   WITH bl: list byte, d: val, shd: share, n: Z, s: val, shs: share
   PRE [ tptr tschar, tptr tschar ]
     PROP(writable_share shd; readable_share shs; Zlength bl < n)
     PARAMS(d;s) GLOBALS()
     SEP(data_at_ shd (tarray tschar n) d; cstring shs bl s)
   POST [ tvoid ]
     PROP() LOCAL() SEP(cstringn shd bl n d; cstring shs bl s).

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog tt gv
  POST [ tint ]  
     PROP() 
     LOCAL (temp ret_temp (Vint (Int.repr 0)))
     SEP(TT).

Definition Gprog : funspecs :=
         [T_alloc_spec; T_free_spec; vstrcpy_spec; main_spec].

Lemma init_mem_mgr:
 forall (gv: globals),
data_at Ews tuint (Vint (Int.repr 0)) (gv _first_free) *
   data_at Ews (tptr (Tunion _cell noattr))
     (offset_val 0 (gv _heap)) (gv _limit) * 
   data_at_ Ews (tarray (Tunion _cell noattr) 1000) (gv _heap) |--
 mem_mgr 1000 gv.
Proof.
intros.
unfold mem_mgr.
rewrite <- HEAPSIZE_eq.
Exists 0 O nullval.
unfold freelistrep.
entailer!.
rewrite <- data_at_nullptr.
change size_t with tuint.
unfold field_address0.
rewrite if_true.
2:{ 
 apply field_compatible0_ArraySubsc0.
 auto with field_compatible.
 split; auto; simpl; rep_lia.
}
simpl.
normalize.
cancel.
Qed.

Ltac strip_int_repr L :=
 match L with
 | Int.repr ?a :: ?L' => let bl := strip_int_repr L' in 
                                 let cl := constr:(a::bl) in
                                 cl
 | nil => constr:(@nil Z)
 end.

Ltac process_stringlit :=
 match goal with
 | |- context [data_at Ers (tarray tschar ?n)
    (map (Vint oo cast_int_int I8 Signed) ?L) (_ ?id)] =>
    let bl := strip_int_repr L in
   let v := fresh id "_val" in
   pose (v := map Vbyte (map Byte.repr bl));
    change (map (Vint oo cast_int_int I8 Signed) L)
     with v
  end.

Lemma data_at__tT_eq:
  forall p sh,
  field_compatible tT nil p ->
   data_at_ sh tT p = data_at_ sh (tarray tschar 42) p.
Proof.
intros.
rewrite data_at__memory_block.
rewrite data_at__memory_block.
rewrite !prop_true_andp; auto.
destruct H as [? [? [? [? ?]]]].
split3; auto.
split3; auto.
destruct p; try contradiction.
red.
apply align_compatible_rec_Tarray.
intros.
eapply align_compatible_rec_by_value; [reflexivity | ].
apply Z.divide_1_l.
Qed.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
sep_apply init_mem_mgr.
repeat process_stringlit.
forward_call (1000, gv).
if_tac; try lia.
Intros p.
assert_PROP (field_compatible tT nil p) by entailer!.
forward_call (map Byte.repr [102; 111; 111], p, Ews, 42, 
                    gv ___stringlit_1, Ers).
rewrite data_at__tT_eq by auto.
unfold cstring.
rewrite prop_true_andp.
cancel.
clear; intro.
compute in H.
decompose [or] H; try discriminate; auto. 
repeat apply seq_assoc1.
match goal with |- semax _ ?pre _ _ =>
 apply semax_seq' with pre
end.
admit.  (* printf *)
forward_call (p, 1000-1, gv).
unfold cstringn.
Intros.
rewrite data_at__tT_eq by auto.
cancel.
forward.
Admitted.

Lemma field_at_union_convert: 
  (* shouldn't need this if unfold_data_at worked correctly *)
  forall q p, 
    field_at Ews (Tunion _cell noattr) [UnionField _next_free] q p
           |-- data_at Ews (tptr tcell) q p.
Proof.
 intros.
 entailer!.
 unfold field_at.
 Intros. simpl. unfold at_offset. normalize.
 unfold data_at, field_at, at_offset; simpl.
 normalize. fold tcell.
 apply andp_right; auto.
 apply prop_right.
 destruct H as [? [? [? [? ?]]]].
 split3; auto. split3; simpl; auto.
 destruct p; try contradiction.
 simpl in H2|-*. lia.
 destruct p; try contradiction.
 red. red in H3.
 eapply align_compatible_rec_Tunion_inv' in H3.
 instantiate (1:= _next_free) in H3.
 simpl field_type in H3.
 eapply align_compatible_rec_by_value_inv in H3; [ | reflexivity].
 eapply align_compatible_rec_by_value; [reflexivity | ].
 auto.
 compute; auto.
Qed.

Lemma fold_alloc_token: forall p,
 data_at_ Ews tcell p |-- data_at_ Ews tT p * T_alloc_token p.
Proof.
intros.
 unfold T_alloc_token.
 rewrite data_at__memory_block.
 Intros.
 rewrite !prop_true_andp by auto.
 change (sizeof tcell) with (sizeof tT + (sizeof tcell - sizeof tT)).
 make_Vptr p.
 rewrite <- (Ptrofs.repr_unsigned i) in *.
 rewrite memory_block_split.
 2,3: compute; congruence.
 2:{  simpl. destruct H as [_ [? [? _]]].
 red in H0. rewrite Ptrofs.repr_unsigned in H0. simpl in H0. rep_lia. }
 apply sepcon_derives.
 -
  rewrite data_at__memory_block.
  rewrite prop_true_andp; auto.
 destruct H as [? [? [? [? ?]]]].
 split3; auto. split3; auto.
 simpl in H1|-*. lia.
 unfold tT. 
 eapply align_compatible_rec_Tstruct.
 simpl. reflexivity.
 intros.
 simpl in H4.
 if_tac in H4; [ | inv H4].
 subst i0.
 inv H5. inv H4.
 apply align_compatible_rec_Tarray. intros.
 eapply align_compatible_rec_by_value; [reflexivity |].
 apply Z.divide_1_l.
-
 apply wand_sepcon_adjoint.
 cancel.
 rewrite data_at__memory_block.
 Intros. auto.
Qed.

Lemma body_T_alloc: semax_body Vprog Gprog f_T_alloc T_alloc_spec.
Proof.
start_function.
unfold mem_mgr.
Intros r n p.
forward.
forward_if (
   EX q:val, PROP ( ) LOCAL (temp _ptr q)
         SEP (if zlt 0 k
              then mem_mgr (k - 1) gv * data_at_ Ews tT q * T_alloc_token q
              else !! (q = nullval) && mem_mgr k gv)).
-
destruct n; unfold freelistrep; fold freelistrep.
+
Intros. subst. contradiction.
+
Intros q.
assert_PROP (field_compatible tcell nil p) as FCcell by entailer!.
unfold tcell.
unfold_data_at (data_at Ews (Tunion _ _) _ _).
forward.
forward.
forward.
Exists p.
entailer!.
rewrite if_true by (rewrite inj_S; lia).
unfold mem_mgr.
Exists r n q.
entailer!.
eapply derives_trans; [ | apply fold_alloc_token].
sep_apply field_at_union_convert.
unfold spacer.
rewrite if_false by computable.
unfold at_offset.
sep_apply data_at_data_at_.
rewrite data_at__memory_block.
Intros.
rewrite data_at__memory_block.
rewrite prop_true_andp by auto.
change (sizeof tcell) with (4+(44-4)).
make_Vptr p.
 rewrite <- (Ptrofs.repr_unsigned i) in *.
rewrite memory_block_split.
 simpl sizeof. simpl Z.sub.
 unfold offset_val.
 rewrite ptrofs_add_repr.
 cancel.
 computable.
 computable.
 simpl.
 clear - FCcell.
 destruct FCcell as [_ [_ [? _]]].
 simpl in H.
 rewrite Ptrofs.repr_unsigned in H. 
 rep_lia.
-
 forward.
 forward_if.
 +
 set (A := (_ * freelistrep _ _)%logic). clearbody A.
 clear - H.
 unfold field_address0.
 if_tac.
 2: entailer!; destruct H3; contradiction.
 simpl.
 make_Vptr (gv _heap).
 simpl.
 unfold test_order_ptrs.
 simpl.
 destruct (peq b b); [ | contradiction n; auto].
 simpl.
 clear e.
 rewrite data_at__memory_block. Intros.
 apply andp_right; apply sepcon_weak_valid_pointer2.
 eapply derives_trans.
 apply memory_block_weak_valid_pointer with (i:=0).
 simpl. rewrite Z.max_r by lia. lia.
 simpl. rewrite Z.max_r by lia.
 admit.
 auto. normalize.
 
 eapply derives_trans.
 apply memory_block_weak_valid_pointer with (i:=(44 * (HEAPSIZE-r))%Z).
 simpl. rewrite Z.max_r by lia. lia.
 simpl. rewrite Z.max_r by lia.
 admit.
 auto.
 simpl.
 normalize.
 apply derives_refl'. f_equal. f_equal. f_equal. f_equal.
 rewrite HEAPSIZE_eq. lia. 
 +
  forward.
  Exists (Vint (Int.repr 0)).
  entailer!.
Admitted.





















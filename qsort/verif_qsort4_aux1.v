Require Import VST.floyd.proofauto.
Require Import qsort4a.
Require Import spec_qsort4.
Require Import float_lemmas.
Require Import Permutation.
Open Scope logic. 

Lemma no_saturate_hack:
  forall sh t n al p,
    data_at sh (tarray t n) al p |-- !!True.
Proof.
intros. apply prop_right. auto.
Qed.


Lemma data_at__change1 {cs: compspecs}:
  forall sh t p,
    headptr p ->
    complete_legal_cosu_type t = true ->
    sizeof t < Ptrofs.modulus ->
    align_compatible_rec cenv_cs t 0 ->
    data_at_ sh (tarray tuchar (sizeof t)) p |-- data_at_ sh t p.
Proof.
intros.
entailer!.
pose proof (sizeof_pos t).
rewrite <- memory_block_data_at_ by auto.
simpl. normalize. 
rewrite (memory_block_data_at_ sh t); auto.
apply headptr_field_compatible; auto.
apply I.
Qed.


Lemma data_at__change2 {cs: compspecs}:
  forall sh t p,
    data_at_ sh t p |-- data_at_ sh (tarray tuchar (sizeof t)) p.
Proof.
intros.
entailer!.
pose proof (sizeof_pos t).
rewrite <- memory_block_data_at_ by auto.
rewrite <- memory_block_data_at_; auto.
simpl.
normalize.
destruct H as [? [? [? [? ?]]]].
split3; auto.
split3; auto.
red in H2|-*. destruct p; try contradiction.
simpl.
normalize.
red in H3|-*. destruct p; try contradiction.
apply align_compatible_rec_Tarray.
intros.
simpl.
eapply align_compatible_rec_by_value.
reflexivity.
simpl.
apply Z.divide_1_l.
Qed.

Lemma split2_data_at_Tarray_fold' {cs: compspecs} sh t n n1 n2 (v v' v1 v2: list (reptype t)) p:
   0 <= n1 <= n ->
   n <= Zlength v' ->
   v = (sublist 0 n v') ->
   v1 = (sublist 0 n1 v') ->
   v2 = (sublist n1 n v') ->
   n = n1 + n2 ->
   data_at sh (Tarray t n1 noattr) v1 p *
   data_at sh (Tarray t n2 noattr) v2
        (field_address0 (Tarray t n noattr) (ArraySubsc n1::nil) p)
   |--
   data_at sh (Tarray t n noattr) v p.
Proof.
intros.
eapply derives_trans.
2: apply (split2_data_at_Tarray_fold sh t n n1 v v' v1 v2 p); auto.
assert (n2 = (n-n1)) by lia.
subst n2.
auto.
Qed.

Lemma field_adr_ofs:
 forall i t N base, 0 <= i <= N ->
   field_compatible (tarray t N) [] base ->
   field_address0 (Tarray t N noattr) [ArraySubsc i] base =
   offset_val (i * sizeof t) base.
Proof.
 intros.
 unfold field_address0.
 rewrite if_true. f_equal.
 unfold nested_field_offset; simpl.
 rewrite Z.add_0_l, Z.mul_comm. auto.
 auto with field_compatible.
Qed.

Definition loop_i :=
                  (Sloop
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'1)
                          (Ederef
                            (Etempvar _compar (tptr (Tfunction
                                                      (Tcons (tptr tvoid)
                                                        (Tcons (tptr tvoid)
                                                          Tnil)) tint
                                                      cc_default)))
                            (Tfunction
                              (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil))
                              tint cc_default))
                          ((Ebinop Oadd
                             (Ecast (Etempvar _base (tptr tvoid))
                               (tptr tuchar))
                             (Ebinop Omul (Etempvar _i tint)
                               (Etempvar _size tulong) tulong) (tptr tuchar)) ::
                           (Evar _pivot (tarray tuchar 1024)) :: nil))
                        (Sifthenelse (Ebinop Olt (Etempvar _t'1 tint)
                                       (Econst_int (Int.repr 0) tint) tint)
                          Sskip
                          Sbreak))
                      (Sset _i
                        (Ebinop Oadd (Etempvar _i tint)
                          (Econst_int (Int.repr 1) tint) tint)))
                    Sskip).

Lemma qsort_loop_i:
 forall (Espec : OracleKind)
   (sh : share) (base compar : val) (t : type)
   (Hok : complete_legal_cosu_type t = true /\
      align_compatible_rec cenv_cs t 0 /\ no_volatiles t)
   (ord : le_order (reptype t))
   (v_pivot v_tmp : val)
   (SH : writable_share sh)
   (bl : list (reptype t)),
   let N := Zlength bl in 
   forall (H0 : N <= Int.max_signed)
    (H1 : N * sizeof t <= Ptrofs.max_signed)
    (H : 0 <= sizeof t <= 1024)
    (Hbase : field_compatible (tarray t N) [] base)
    (Hmn : 0 < N - 1)
    (FR1 : list mpred)
    (pivot : reptype t)
    (i j : Z)
    (H4 : 0 <= i)
    (H7 : Forall (ord_ge ord pivot) (sublist 0 i bl))
    (H8 : Forall (ord_le ord pivot) (sublist (j + 1) N bl))
    (H8b : ord_le ord pivot (Znth (N - 1) bl))
    (H10 : Exists (ord_eq ord pivot) (sublist 0 i bl) \/
      j = N - 1 /\ ord_eq ord pivot (Znth (N - 1) bl))
    (Hpivot : ord_def ord pivot)
    (Hdef_bl : Forall (ord_def ord) bl)
    (H6 : i <= j < N),
semax (func_tycontext f_qsort Vprog Gprog [])
  (PROP ( )
   LOCAL (temp _i (Vint (Int.repr i));
   temp _j (Vint (Int.repr j));
   temp _n (Vint (Int.repr (N - 1)));
   temp _m (Vint (Int.repr 0));
   lvar _tmp (tarray tuchar 1024) v_tmp;
   lvar _pivot (tarray tuchar 1024) v_pivot;
   temp _base base; temp _size (Vlong (Int64.repr (sizeof t)));
   temp _compar compar)
   SEP (data_at sh (tarray t N) bl base;
   data_at Tsh t pivot v_pivot; data_at_ Tsh t v_tmp;
   FRZL FR1; func_ptr' (compare_spec t ord) compar))
   loop_i
  (normal_ret_assert
     (EX i0 : Z,
      PROP (0 <= i0 <= j + 1; i0 < N;
      Forall (ord_ge ord pivot) (sublist 0 i0 bl);
      ord_le ord pivot (Znth i0 bl);
      Exists (ord_eq ord pivot) (sublist 0 i0 bl) \/
      j = N - 1 /\ ord_eq ord pivot (Znth (N - 1) bl))
      LOCAL (temp _i (Vint (Int.repr i0));
      temp _j (Vint (Int.repr j));
      temp _n (Vint (Int.repr (N - 1)));
      temp _m (Vint (Int.repr 0));
      lvar _tmp (tarray tuchar 1024) v_tmp;
      lvar _pivot (tarray tuchar 1024) v_pivot;
      temp _base base;
      temp _size (Vlong (Int64.repr (sizeof t)));
      temp _compar compar)
      SEP (data_at sh (tarray t N) bl base;
      data_at Tsh t pivot v_pivot; data_at_ Tsh t v_tmp;
      FRZL FR1; func_ptr' (compare_spec t ord) compar))%assert).
Proof.
intros.
abbreviate_semax.
unfold loop_i.
forward_loop (EX i:Z,
      PROP(0<=i<=j+1; i<N;
              Forall ( ord_ge ord pivot) (sublist 0 i bl);
              Exists ( ord_eq ord pivot) (sublist 0 i bl) \/
              j = (N-1) /\  ord_eq ord pivot (Znth (N-1) bl))
      LOCAL (temp _i (Vint (Int.repr i)); temp _j (Vint (Int.repr j));
                temp _n (Vint (Int.repr (N-1)));
                temp _m (Vint (Int.repr 0));
                lvar _tmp (tarray tuchar 1024) v_tmp;
                lvar _pivot (tarray tuchar 1024) v_pivot;
                temp _base base; temp _size (Vlong (Int64.repr (sizeof t)));
                temp _compar compar)
       SEP (data_at sh (tarray t N) bl base;
              data_at Tsh t pivot v_pivot; data_at_ Tsh t v_tmp;
              FRZL FR1; func_ptr' (compare_spec t ord) compar)).
 - (* precondition of i loop *)
   Exists i.
   entailer!.
 - (* body of i loop *)
   clear dependent i.
   rename H into H'.
   Intros i.
   forward_call (sh, Tsh, offset_val (i*sizeof t) base, v_pivot, Znth i bl, pivot).
(*
  split.
  assert (0 <= i*sizeof t); [ | rep_lia].
  apply Z.mul_nonneg_nonneg; rep_lia.
  eapply Z.le_trans; try apply H1.
  apply Zmult_le_compat_r.
  lia.
  lia.
*)
  {
  simpl.
  unfold tarray. 
  sep_apply (split2_data_at_Tarray_unfold sh t N i).
  lia.
  sep_apply (split2_data_at_Tarray_unfold sh t (N-i) 1).
  lia.
  autorewrite with sublist.
  rewrite (sublist_one i (1+i)) by lia.
  fold (tarray t 1).
  erewrite data_at_singleton_array_eq by reflexivity.
  rewrite field_adr_ofs by (auto; lia).
  cancel.
  }
(* split3; auto.
 split; auto.*)
 eapply Forall_Znth; eauto. lia.
 Intros vret.
 rewrite <- (data_at_singleton_array_eq sh t (Znth i bl) [Znth i bl]) by reflexivity.
 rewrite <- (field_adr_ofs i t N) by (auto; lia).
 change (tarray t 1) with (Tarray t 1 noattr).
 sep_apply (split2_data_at_Tarray_fold' sh t (N-i) 1 (N-i-1)
   (sublist 0 (N-i) (sublist i N bl)) (sublist i N bl)
    [Znth i bl] (sublist (1 + i) N bl)
   (field_address0 (Tarray t N noattr) [ArraySubsc i] base));
   auto; try lia.
  (* Time  list_solve. (* 272 seconds.  *) *)
  Zlength_solve.  (* 0.1 seconds *)
  rewrite sublist_one; autorewrite with sublist; auto.
  clear; lia.
  lia.
  autorewrite with sublist. auto.
  sep_apply (split2_data_at_Tarray_fold' sh t N i (N-i) bl bl); try lia; auto.
  autorewrite with sublist. auto.
  autorewrite with sublist; auto.  
  destruct vret.
 + (* Eq *)
  forward_if. lia.
  clear H6.
  forward.
  Exists i.
  entailer!. apply H5.
 + (* Lt *)
  forward_if. 2: lia.
  clear H6.
  forward.
  Exists (i+1).
  entailer!.
  set (N := Zlength bl) in *.
  assert (i<>j+1). {
    intro; subst.
    assert (ord_le ord pivot (Znth 0 (sublist (j+1) N bl))).
      eapply Forall_Znth; auto; autorewrite with sublist; lia.
    autorewrite with sublist in H13.
    clear - H5 H13.
    destruct H5. contradiction.
  }
  split3; try lia.
  assert (i<>N-1); [ | lia].
  intro. subst i.
  clear - H8b H5. destruct H5. contradiction.
  split. rewrite (sublist_split 0 i) by lia. rewrite Forall_app; split; auto.
  rewrite sublist_one by lia. repeat constructor.
  clear - H5. destruct H5. red. auto.
  destruct H4.
  left. rewrite (sublist_split 0 i) by lia. rewrite Exists_app.
  left; auto.
  right; auto.
 + (* Gt *)
  forward_if. lia.
  clear H6.
  forward.
  Exists i.
  entailer!. destruct H5; auto.
Qed.

Definition loop_j :=
                    (Sloop
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'2)
                            (Ederef
                              (Etempvar _compar (tptr (Tfunction
                                                        (Tcons (tptr tvoid)
                                                          (Tcons (tptr tvoid)
                                                            Tnil)) tint
                                                        cc_default)))
                              (Tfunction
                                (Tcons (tptr tvoid)
                                  (Tcons (tptr tvoid) Tnil)) tint cc_default))
                            ((Ebinop Oadd
                               (Ecast (Etempvar _base (tptr tvoid))
                                 (tptr tuchar))
                               (Ebinop Omul (Etempvar _j tint)
                                 (Etempvar _size tulong) tulong)
                               (tptr tuchar)) ::
                             (Evar _pivot (tarray tuchar 1024)) :: nil))
                          (Sifthenelse (Ebinop Ogt (Etempvar _t'2 tint)
                                         (Econst_int (Int.repr 0) tint) tint)
                            Sskip
                            Sbreak))
                        (Sset _j
                          (Ebinop Osub (Etempvar _j tint)
                            (Econst_int (Int.repr 1) tint) tint)))
                      Sskip).

Lemma qsort_loop_j:
 forall (Espec : OracleKind)
  (sh : share) (base compar : val) (t : type)
  (Hok : complete_legal_cosu_type t = true /\
      align_compatible_rec cenv_cs t 0 /\ no_volatiles t)
  (ord : le_order (reptype t))
  (v_pivot  v_tmp : val)
  (SH : writable_share sh) 
  (bl : list (reptype t)),
  let N := Zlength bl : Z in 
  forall (H0 : N <= Int.max_signed)
  (H1 : N * sizeof t <= Ptrofs.max_signed)
  (H : 0 <= sizeof t <= 1024) 
  (Hbase : field_compatible (tarray t N) [] base)
  (Hmn : 0 < N - 1)
  (FR1 : list mpred)
  (pivot : reptype t) 
  (j : Z) 
  (H8 : Forall (ord_le ord pivot) (sublist (j + 1) N bl))
  (H8b : ord_le ord pivot (Znth (N - 1) bl))
  (Hpivot : ord_def ord pivot)
  (Hdef_bl : Forall (ord_def ord) bl)
  (i : Z) 
  (H4 : 0 <= i <= j + 1)
  (H7 : i < N) 
  (H13 : Forall (ord_ge ord pivot) (sublist 0 i bl))
  (H14 : ord_le ord pivot (Znth i bl)) 
  (H10 : Exists (ord_eq ord pivot) (sublist 0 i bl) \/
      j = N - 1 /\ ord_eq ord pivot (Znth (N - 1) bl))
  (H6' : 0 <= j < N),
semax (func_tycontext f_qsort Vprog Gprog [])
  (PROP ( )
   LOCAL (temp _i (Vint (Int.repr i));
   temp _j (Vint (Int.repr j));
   temp _n (Vint (Int.repr (N - 1)));
   temp _m (Vint (Int.repr 0));
   lvar _tmp (tarray tuchar 1024) v_tmp;
   lvar _pivot (tarray tuchar 1024) v_pivot;
   temp _base base; temp _size (Vlong (Int64.repr (sizeof t)));
   temp _compar compar)
   SEP (data_at sh (tarray t N) bl base;
   data_at Tsh t pivot v_pivot; data_at_ Tsh t v_tmp;
   FRZL FR1; func_ptr' (compare_spec t ord) compar)) loop_j
  (normal_ret_assert
     (EX j' : Z,
      PROP (0 <= j' <= j /\ i - 1 <= j';
      Forall (ord_lt ord pivot)
        (sublist (j' + 1) (j + 1) bl);
      ord_le ord (Znth j' bl) pivot)
      LOCAL (temp _i (Vint (Int.repr i));
      temp _j (Vint (Int.repr j'));
      temp _n (Vint (Int.repr (N - 1)));
      temp _m (Vint (Int.repr 0));
      lvar _tmp (tarray tuchar 1024) v_tmp;
      lvar _pivot (tarray tuchar 1024) v_pivot;
      temp _base base;
      temp _size (Vlong (Int64.repr (sizeof t)));
      temp _compar compar)
      SEP (data_at sh (tarray t N) bl base;
      data_at Tsh t pivot v_pivot; data_at_ Tsh t v_tmp;
      FRZL FR1; func_ptr' (compare_spec t ord) compar))%assert).
Proof.
intros.
abbreviate_semax.
unfold loop_j.
 forward_loop (EX j':Z,
      PROP(0<=j'<=j /\ i-1<=j';
              Forall (ord_lt ord pivot) (sublist (j'+1) (j+1) bl))
   LOCAL (temp _i (Vint (Int.repr i));
   temp _j (Vint (Int.repr j'));
   temp _n (Vint (Int.repr (N - 1)));
   temp _m (Vint (Int.repr 0));
   lvar _tmp (tarray tuchar 1024) v_tmp;
   lvar _pivot (tarray tuchar 1024) v_pivot;
   temp _base base; temp _size (Vlong (Int64.repr (sizeof t)));
   temp _compar compar)
   SEP (data_at sh (tarray t N) bl base;
   data_at Tsh t pivot v_pivot; data_at_ Tsh t v_tmp;
   FRZL FR1; func_ptr' (compare_spec t ord) compar)).
- 
    Exists j; entailer!.
    autorewrite with sublist. constructor.
-
   Intros j'.
   forward_call (sh, Tsh, offset_val (j'*sizeof t) base, v_pivot, Znth j' bl, pivot).
(*   change (@sizeof _ t) with (sizeof t).
  split.
  assert (0 <= j'*sizeof t); [ | rep_lia].
  apply Z.mul_nonneg_nonneg; rep_lia.
  eapply Z.le_trans; try apply H1.
  apply Zmult_le_compat_r.
  lia.
  lia.*)
  {
  simpl.
  unfold tarray. 
  sep_apply (split2_data_at_Tarray_unfold sh t N j').
  lia.
  sep_apply (split2_data_at_Tarray_unfold sh t (N-j') 1).
  lia.
  autorewrite with sublist.
  rewrite (sublist_one j' (1+j')) by lia.
  fold (tarray t 1).
  erewrite data_at_singleton_array_eq by reflexivity.
  rewrite field_adr_ofs by (auto; lia).
  cancel.
  }
(* split3; auto.
 split; auto.
*)
 eapply Forall_Znth; auto. lia.
 Intros vret.
 rewrite <- (data_at_singleton_array_eq sh t (Znth j' bl) [Znth j' bl]) by reflexivity.
 rewrite <- (field_adr_ofs j' t N) by (auto; lia).
 change (tarray t 1) with (Tarray t 1 noattr).
 sep_apply (split2_data_at_Tarray_fold' sh t (N-j') 1 (N-j'-1)
   (sublist 0 (N-j') (sublist j' N bl)) (sublist j' N bl)
    [Znth j' bl] (sublist (1 + j') N bl)
   (field_address0 (Tarray t N noattr) [ArraySubsc j'] base));
   auto; try lia.
  Zlength_solve.  (* list_solve.  *)
  rewrite sublist_one; autorewrite with sublist; auto.
  clear; lia.
  lia.
  autorewrite with sublist. auto.
  sep_apply (split2_data_at_Tarray_fold' sh t N j' (N-j') bl bl); try lia; auto.
  autorewrite with sublist. auto.
  autorewrite with sublist; auto.  
  destruct vret.
 + (* Eq *)
  forward_if. lia.
  clear H9.
  forward.
  Exists j'.
  entailer!.
  destruct H6; auto.
 + (* Lt *)
  forward_if. lia.
  clear H9.
  forward.
  Exists j'.
  entailer!.
  destruct H6; auto.
 + (* Gt *)
  forward_if. 2: lia.
  clear H9.
  forward.
  Exists (j'-1).
  entailer!.
  set (N := Zlength bl) in *.
  clear Pcompar H16 H15 H12 H11 H9 PNcompar PNbase Pv_pivot0.
  clear HPv_pivot Pv_pivot Pv_tmp0 HPv_tmp Pv_tmp.
  clear Delta_specs Hbase sh SH Hok.
  assert (j'<>0). {
    intro; subst.
    assert (i=0 \/ i=1) by lia. destruct H9.
    subst. 
    destruct H10. autorewrite with sublist in H9.
    inv H9. destruct H9. subst j.
    autorewrite with sublist in *.
    destruct H10.
    assert (ord_lt ord pivot (Znth (N-2) (sublist 1 N bl))).
     apply Forall_Znth; auto. autorewrite with sublist; lia.
    autorewrite with sublist in H11. replace (N-2+1) with (N-1) in H11 by lia.
    destruct H11. contradiction.
    subst i.
    clear H3 H4 Hpivot Hdef_bl H7 H2 H1 H FR1 Espec base compar.
    rewrite sublist_one in H13 by lia. inv H13.
    destruct H6; contradiction.
  }
  rewrite Z.sub_add.     
  split3; try lia.
  assert (j'<>i-1); [ | lia].
  intro; subst j'.
  assert (0 < i <= j+1) by lia. clear H4 H2 H3 H9.
  rewrite Z.sub_add in H5.
  assert (ord_ge ord pivot (Znth (i-1) (sublist 0 i bl))).
    apply Forall_Znth; auto. autorewrite with sublist; lia.
  autorewrite with sublist in H2.
  destruct H6; contradiction.
  rewrite (sublist_split j' (j'+1)) by lia. rewrite Forall_app; split; auto.
  rewrite sublist_one by lia. constructor; [ | constructor].
  auto.  
Qed.

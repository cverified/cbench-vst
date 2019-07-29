Require Import VST.floyd.proofauto.
Require Import qsort4a.
Require Import spec_qsort4.
Require Import verif_qsort4_aux1.
Require Import float_lemmas.
Require Import Permutation.
Set Nested Proofs Allowed.


Lemma field_compatible_subarray' {cs: compspecs}:
 forall i j N t p,
 field_compatible (tarray t N) nil p ->
 0 <= i <= j ->
 j <= N ->
 field_compatible (tarray t (j-i)) nil (offset_val (i*sizeof t) p).
Proof.
intros.
destruct H as [? [? [? [? ?]]]].
destruct p; try contradiction.
pose proof (sizeof_pos t).
assert (0 <= sizeof t * i <= sizeof t * j).
split.
apply Z.mul_nonneg_nonneg; omega.
apply Z.mul_le_mono_nonneg_l; try omega.
assert (sizeof t * j <= sizeof t * N).
apply Z.mul_le_mono_nonneg_l; try omega.
pose proof (Ptrofs.unsigned_range i0).
split3; auto.
split3; auto.
-
simpl in H3|-*.
rewrite Z.max_r in * by omega.
rewrite <- (Ptrofs.repr_unsigned i0).
rewrite ptrofs_add_repr.
rewrite (Z.mul_comm i).
rewrite Ptrofs.unsigned_repr.
rewrite <- Z.add_assoc.
rewrite <- Z.mul_add_distr_l.
replace (i+(j-i)) with j by omega.
omega.
rep_omega.
-
pose proof (align_compatible_nested_field_array (tarray t N) nil i j (Vptr b i0)).
simpl nested_field_array_type in H10.
change (Tarray t (j - i) (no_alignas_attr noattr))
  with (tarray t (j-i)) in H10.
simpl offset_val in H10.
simpl offset_val.
rewrite Z.add_0_l in H10.
rewrite (Z.mul_comm).
apply H10.
simpl; split; auto; try omega.
simpl; split; auto; try omega.
assumption.
assumption.
auto.
Qed.

Lemma field_compatible_subarray'' {cs: compspecs}:
 forall j N t p,
 field_compatible (tarray t N) nil p ->
 0 <= j <= N ->
 field_compatible (tarray t j) nil p.
Proof.
intros.
apply (field_compatible_subarray' 0 j) in H; auto; try omega.
rewrite Z.sub_0_r in H. 
rewrite Z.mul_0_l in H.
normalize in H.
Qed.

Definition call_memcpy_ij :=
                           (Scall None
                            (Evar _memcpy (Tfunction
                                            (Tcons (tptr tvoid)
                                              (Tcons (tptr tvoid)
                                                (Tcons tuint Tnil)))
                                            (tptr tvoid) cc_default))
                            ((Ebinop Oadd
                               (Ecast (Etempvar _base (tptr tvoid))
                                 (tptr tuchar))
                               (Ebinop Omul (Etempvar _i tint)
                                 (Etempvar _size tuint) tuint) (tptr tuchar)) ::
                             (Ebinop Oadd
                               (Ecast (Etempvar _base (tptr tvoid))
                                 (tptr tuchar))
                               (Ebinop Omul (Etempvar _j tint)
                                 (Etempvar _size tuint) tuint) (tptr tuchar)) ::
                             (Etempvar _size tuint) :: nil)).

Lemma forward_illegal_memcpy:
 forall (Espec : OracleKind)
  (sh : share) (base : val) (t : type)
  (Hok : complete_legal_cosu_type t = true /\
      align_compatible_rec cenv_cs t 0 /\ no_volatiles t)
  (bl : list (reptype t))
  (SH : writable_share sh),
  let N := Zlength bl in 
  forall (H0 : N <= Int.max_signed)
  (H1 : N * sizeof t <= Int.max_signed)
  (H'' : 0 <= sizeof t <= 1024)
  (Hbase : field_compatible (tarray t N) [] base)
  (i : Z)
  (H : 0 <= i < N),
semax (func_tycontext f_qsort Vprog Gprog [])
  (PROP ( )
   LOCAL (temp _i (Vint (Int.repr i));
   temp _j (Vint (Int.repr i)); temp _base base;
   temp _size (Vint (Int.repr (sizeof t))))
   SEP (data_at sh t (Znth i bl)
          (field_address0 (Tarray t (i + 1) noattr)
             [ArraySubsc i] base)))
  call_memcpy_ij
  (normal_ret_assert
     (PROP ( )
      LOCAL (temp _i (Vint (Int.repr i));
      temp _j (Vint (Int.repr i)); temp _base base;
      temp _size (Vint (Int.repr (sizeof t))))
      SEP (data_at sh t (Znth i bl)
             (field_address0 (Tarray t (i + 1) noattr)
                [ArraySubsc i] base)))).
Admitted.  (* This program has a bug!  According to the C specification,
                 it is illegal to call memcpy with overlapping arguments,
                 but i=j here.  *)

Lemma forward_call_memcpy_ij:
 forall (Espec : OracleKind)
   (sh : share) (base : val)
    (t : type) 
   (Hok : complete_legal_cosu_type t = true /\
      align_compatible_rec cenv_cs t 0 /\ no_volatiles t)
    (bl : list (reptype t))
    (SH : writable_share sh),
    let N := Zlength bl in 
   forall (H0 : N <= Int.max_signed)
    (H1 : N * sizeof t <= Int.max_signed)
    (H'' : 0 <= sizeof t <= 1024)
    (Hbase : field_compatible (tarray t N) [] base)
    (Hmn : 0 < N - 1)
    (i j : Z)
    (H5 : j < N)
    (H6 : 0 <= i <= j),
  semax (func_tycontext f_qsort Vprog Gprog [])
  (PROP ( )
   LOCAL (temp _i (Vint (Int.repr i));
        temp _j (Vint (Int.repr j));
        temp _base base; temp _size (Vint (Int.repr (sizeof t))))
   SEP (data_at sh (Tarray t N noattr) bl base))
  call_memcpy_ij
  (normal_ret_assert
     (PROP ( )
   LOCAL (temp _i (Vint (Int.repr i));
        temp _j (Vint (Int.repr j));
        temp _base base; temp _size (Vint (Int.repr (sizeof t))))
      SEP (data_at sh (Tarray t N noattr)
             (upd_Znth i bl (Znth j bl)) base))).
Proof.
intros.
destruct (zeq i j).
-
(* Yes, it really is possible that i=j here;
  just sort the sequence [0;1] and it will happen.
  And it is "undefined behavior" to call memcpy with
  overlapping source and destination.   Therefore
  this program has a bug. *)
subst j.
assert (0 <= i < N) by omega.
clear Hmn H6 H5.
replace (upd_Znth i bl (Znth i bl)) with bl.
2:{
rewrite upd_Znth_unfold.
rewrite <- (sublist_one i (i+1)) by omega.
autorewrite with sublist.
auto.
}
 erewrite (split2_data_at_Tarray sh t N (i+1))
     with (v' := bl);
    try (autorewrite with sublist; try omega; reflexivity).
  erewrite (split2_data_at_Tarray sh t (i+1) i)
     with (v' := bl);
  try (autorewrite with sublist; try omega; reflexivity).
  rewrite (sublist_one i) by list_solve.
  replace (i+1-i) with 1 by (clear; omega).
  fold (tarray t 1).
  erewrite data_at_singleton_array_eq by reflexivity.
  Intros.
 apply (semax_pre_post' 
   (PROP ( )
   (LOCALx
      ([temp _i (Vint (Int.repr i));
       temp _j (Vint (Int.repr i)); temp _base base;
       temp _size (Vint (Int.repr (sizeof t)))] ++ [])
      (SEPx
         ([data_at sh t (Znth i bl)
             (field_address0 (Tarray t (i + 1) noattr)
                [ArraySubsc i] base)] ++
          [data_at sh (Tarray t i noattr) 
             (sublist 0 i bl) base;          
          data_at sh (Tarray t (N - (i + 1)) noattr)
            (sublist (i + 1) N bl)
            (field_address0 (Tarray t N noattr)
               [ArraySubsc (i + 1)] base)]))))
     (PROP ( )
      (LOCALx
         ([temp _i (Vint (Int.repr i));
          temp _j (Vint (Int.repr i)); 
          temp _base base;
          temp _size (Vint (Int.repr (sizeof t)))] ++ [])
         (SEPx
            ([data_at sh t (Znth i bl)
             (field_address0 (Tarray t (i + 1) noattr)
                [ArraySubsc i] base)] ++
          [data_at sh (Tarray t i noattr) 
             (sublist 0 i bl) base;          
          data_at sh (Tarray t (N - (i + 1)) noattr)
            (sublist (i + 1) N bl)
            (field_address0 (Tarray t N noattr)
               [ArraySubsc (i + 1)] base)]))))).
apply andp_left2; go_lowerx; entailer!.
apply andp_left2; go_lowerx; entailer!.
apply semax_frame_PQR.
auto with closed.
apply forward_illegal_memcpy; auto.
-
assert (0 <= i < j) by omega.
clear n H6.
unfold call_memcpy_ij.
forward_call (sh, sh, offset_val (i*sizeof t) base, offset_val (j*sizeof t) base, 
                            existT reptype t (Znth j bl)).
  change (@sizeof _ t) with (sizeof t).
  rewrite !Int.signed_repr by rep_omega.
  split; split.
  assert (0 <= i*sizeof t); [ | rep_omega].
  apply Z.mul_nonneg_nonneg; rep_omega.
  eapply Z.le_trans; try apply H1.
  apply Zmult_le_compat_r.
  omega.
  omega.
  assert (0 <= j*sizeof t); [ | rep_omega].
  apply Z.mul_nonneg_nonneg; rep_omega.
  eapply Z.le_trans; try apply H1.
  apply Zmult_le_compat_r.
  omega.
  omega.
  simpl.
  sep_apply (split2_data_at_Tarray_unfold sh t N j).
  omega.
  rewrite (field_adr_ofs) by (auto; omega).
  sep_apply (split2_data_at_Tarray_unfold sh t (N-j) 1).
  omega.
  rewrite (sublist_one 0 1) by list_solve.
  fold (tarray t 1).
  erewrite data_at_singleton_array_eq by reflexivity.
  autorewrite with sublist.
  cancel.
  sep_apply (split2_data_at_Tarray_unfold sh t j i).
  omega.
  autorewrite with sublist.
  rewrite (field_adr_ofs); auto; try omega.
  2: eapply (field_compatible_subarray'' j N); eauto; omega.
  sep_apply (split2_data_at_Tarray_unfold sh t (j-i) 1).
  omega.
  rewrite (sublist_one 0 1) by list_solve.
  autorewrite with sublist.
  fold (tarray t 1).
  erewrite data_at_singleton_array_eq by reflexivity.
  cancel.
  split3; auto.
 simpl. destruct Hok as [_ [_ ?]]; auto.
 entailer!.
 simpl.
 match goal with |- ?A |-- _ => set (LHS := A) end.
 erewrite (split2_data_at_Tarray sh t N (j+1))
     with (v' := upd_Znth i bl (Znth j bl) );
    try (autorewrite with sublist; try omega; reflexivity).
  erewrite (split2_data_at_Tarray sh t (j+1) j)
     with (v' := upd_Znth i bl (Znth j bl) );
  try (autorewrite with sublist; try omega; reflexivity).
  rewrite (sublist_one j) by list_solve.
  rewrite upd_Znth_diff by list_solve.
  replace (j+1-j) with 1 by (clear; omega).
  fold (tarray t 1).
  erewrite data_at_singleton_array_eq by reflexivity.
  erewrite (split2_data_at_Tarray sh t j (i+1))
     with (v' := upd_Znth i bl (Znth j bl) );
    try (autorewrite with sublist; try omega; reflexivity).
  erewrite (split2_data_at_Tarray sh t (i+1) i)
     with (v' := upd_Znth i bl (Znth j bl) );
  try (autorewrite with sublist; try omega; reflexivity).
  rewrite (sublist_one i) by list_solve.
  rewrite upd_Znth_same by list_solve.
  replace (i+1-i) with 1 by (clear; omega).
  fold (tarray t 1).
  erewrite data_at_singleton_array_eq by reflexivity.
  rewrite sublist_upd_Znth_l by omega.
  rewrite sublist_upd_Znth_r by omega.
  rewrite sublist_upd_Znth_r by omega.
  subst LHS.
  rewrite (field_adr_ofs); auto; try omega.
  2: apply (field_compatible_subarray' i j N _ _ Hbase); eauto; omega.
  rewrite (field_adr_ofs); auto; try omega.
  2: eapply (field_compatible_subarray' _ _ _ _ _ Hbase);
        try apply Hbase; omega.
  rewrite (field_adr_ofs); auto; try omega.
  2: eapply (field_compatible_subarray'');
        try apply Hbase; omega.
  rewrite (field_adr_ofs); auto; try omega.
  2: eapply (field_compatible_subarray'');
        try apply Hbase; omega.
  rewrite (field_adr_ofs); auto; try omega.
  2: eapply (field_compatible_subarray'');
        try apply Hbase; omega.
  rewrite (field_adr_ofs); auto; try omega.
  rewrite !offset_offset_val.
  rewrite <- !Z.mul_add_distr_r.
  replace  (j - i - 1) with (j-(i+1)) by (clear; omega).
  replace  (N - j - 1) with (N-(j+1)) by (clear; omega).
  rewrite !(Z.add_comm 1).
  cancel.
Qed.

Definition qsort_then2 :=
                     (Ssequence
                        (Scall None
                          (Evar _memcpy (Tfunction
                                          (Tcons (tptr tvoid)
                                            (Tcons (tptr tvoid)
                                              (Tcons tuint Tnil)))
                                          (tptr tvoid) cc_default))
                          ((Evar _tmp (tarray tuchar 1024)) ::
                           (Ebinop Oadd
                             (Ecast (Etempvar _base (tptr tvoid))
                               (tptr tuchar))
                             (Ebinop Omul (Etempvar _i tint)
                               (Etempvar _size tuint) tuint) (tptr tuchar)) ::
                           (Etempvar _size tuint) :: nil))
                        (Ssequence
                          call_memcpy_ij
                          (Ssequence
                            (Scall None
                              (Evar _memcpy (Tfunction
                                              (Tcons (tptr tvoid)
                                                (Tcons (tptr tvoid)
                                                  (Tcons tuint Tnil)))
                                              (tptr tvoid) cc_default))
                              ((Ebinop Oadd
                                 (Ecast (Etempvar _base (tptr tvoid))
                                   (tptr tuchar))
                                 (Ebinop Omul (Etempvar _j tint)
                                   (Etempvar _size tuint) tuint)
                                 (tptr tuchar)) ::
                               (Evar _tmp (tarray tuchar 1024)) ::
                               (Etempvar _size tuint) :: nil))
                            (Ssequence
                              (Sset _i
                                (Ebinop Oadd (Etempvar _i tint)
                                  (Econst_int (Int.repr 1) tint) tint))
                              (Sset _j
                                (Ebinop Osub (Etempvar _j tint)
                                  (Econst_int (Int.repr 1) tint) tint)))))).

Lemma verif_qsort_then2:
 forall (Espec : OracleKind) (sh : share) (base compar : val)
    (t : type) 
    (Hok : complete_legal_cosu_type t = true /\
      align_compatible_rec cenv_cs t 0 /\ no_volatiles t)
    (ord : le_order (reptype t))
    (al bl : list (reptype t))
    (v_pivot v_tmp : val)
    (SH : writable_share sh),
    let N := Zlength bl in 
    forall (H0 : N <= Int.max_signed)
    (H1 : N * sizeof t <= Int.max_signed)
     (H'' : 0 <= sizeof t <= 1024)
    (Hbase : field_compatible (tarray t N) [] base)
    (Hmn : 0 < N - 1)
    (FR1 : list mpred)
    (pivot : reptype t)
    (H8b : ord_le ord pivot (Znth (N - 1) bl))
    (H9 : Permutation al bl) 
    (Hpivot : ord_def ord pivot) 
    (Hdef_bl : Forall (ord_def ord) bl)
    (i : Z) 
    (H13 : Forall (ord_ge ord pivot) (sublist 0 i bl)) 
    (H14 : ord_le ord pivot (Znth i bl))
    (j : Z)
    (H15 : ord_le ord (Znth j bl) pivot)
    (H10 : Exists (ord_eq ord pivot) (sublist 0 i bl) \/
      j = N - 1 /\ ord_eq ord pivot (Znth (N - 1) bl))
    (H12 : Forall (ord_le ord pivot) (sublist (j + 1) N bl))
    (H5 : 0 <= j < N)
    (H6 : 0 <= i <= j),
semax (func_tycontext f_qsort Vprog Gprog [])
  (PROP ( )
   LOCAL (temp _i (Vint (Int.repr i));
   temp _j (Vint (Int.repr j));
   temp _n (Vint (Int.repr (N - 1)));
   temp _m (Vint (Int.repr 0));
   lvar _tmp (tarray tuchar 1024) v_tmp;
   lvar _pivot (tarray tuchar 1024) v_pivot;
   temp _base base; temp _size (Vint (Int.repr (sizeof t)));
   temp _compar compar)
   SEP (data_at sh (tarray t N) bl base;
   data_at Tsh t pivot v_pivot; data_at_ Tsh t v_tmp;
   FRZL FR1; func_ptr' (compare_spec t ord) compar))
  qsort_then2
  (normal_ret_assert
     (EX (i0 j0 : Z) (bl0 : list (reptype t)),
      PROP (Permutation al bl0; 0 <= i0 <= N; 
      -1 <= j0 < N; j0 >= i0 - 2;
      Forall (ord_ge ord pivot) (sublist 0 i0 bl0);
      Forall (ord_le ord pivot) (sublist (j0 + 1) N bl0);
      ord_le ord pivot (Znth (N - 1) bl0);
      Exists (ord_eq ord pivot) (sublist 0 i0 bl0) \/
      j0 = N - 1 /\ ord_eq ord pivot (Znth (N - 1) bl0);
      j0 = i0 - 2 -> ord_eq ord pivot (Znth (i0 - 1) bl0))
      LOCAL (temp _i (Vint (Int.repr i0));
      temp _j (Vint (Int.repr j0));
      temp _n (Vint (Int.repr (N - 1)));
      temp _m (Vint (Int.repr 0));
      lvar _tmp (tarray tuchar 1024) v_tmp;
      lvar _pivot (tarray tuchar 1024) v_pivot;
      temp _base base;
      temp _size (Vint (Int.repr (sizeof t)));
      temp _compar compar)
      SEP (data_at sh (tarray t N) bl0 base;
      data_at Tsh t pivot v_pivot; data_at_ Tsh t v_tmp;
      FRZL FR1; func_ptr' (compare_spec t ord) compar))%assert).
Proof.
intros.
unfold qsort_then2.
abbreviate_semax.
freeze FR2 := (FRZL _) (data_at _ _ _ v_pivot) (func_ptr' _ _).

(* memcpy(tmp, a(i), size); *)
forward_call (Tsh, sh, v_tmp, offset_val (i*sizeof t) base, 
                            existT reptype t (Znth i bl)).
  change (@sizeof _ t) with (sizeof t).
  rewrite Int.signed_repr by rep_omega.
  split.
  assert (0 <= i*sizeof t); [ | rep_omega].
  apply Z.mul_nonneg_nonneg; rep_omega.
  eapply Z.le_trans; try apply H1.
  apply Zmult_le_compat_r.
  omega.
  omega.
  simpl.
  sep_apply (split2_data_at_Tarray_unfold sh t N i).
  omega.
  sep_apply (split2_data_at_Tarray_unfold sh t (N-i) 1).
  omega.
  rewrite (sublist_one 0 1) by list_solve.
  rewrite (field_adr_ofs) by (auto; omega).
  autorewrite with sublist.
  fold (tarray t 1).
  erewrite data_at_singleton_array_eq by reflexivity.
 cancel.
 split3; auto.
 simpl. destruct Hok as [_ [_ ?]]; auto.
 simpl.
 rewrite <- (data_at_singleton_array_eq sh t (Znth i bl) (sublist i (i+1) bl)).
  2: rewrite sublist_one by omega; auto.
 change (tarray t 1) with (Tarray t 1 noattr).
 sep_apply (split2_data_at_Tarray_fold' sh t (N-i) 1 (N-i-1) (sublist i N bl) (sublist i N bl));
 try (autorewrite with sublist; auto; try omega).
 f_equal. omega.
 rewrite <- (field_adr_ofs _ _ N) by (auto; omega).
 sep_apply (split2_data_at_Tarray_fold' sh t N i (N-i) bl bl);
   try (autorewrite with sublist; auto; try omega).

apply semax_seq'
 with  (PROP ( )
   LOCAL (temp _i (Vint (Int.repr i));
   temp _j (Vint (Int.repr j));
   temp _n (Vint (Int.repr (N - 1)));
   temp _m (Vint (Int.repr 0));
   lvar _tmp (tarray tuchar 1024) v_tmp;
   lvar _pivot (tarray tuchar 1024) v_pivot;
   temp _base base; temp _size (Vint (Int.repr (sizeof t)));
   temp _compar compar)
   SEP (data_at sh (Tarray t N noattr) (upd_Znth i bl (Znth j bl)) base;
   data_at Tsh t (Znth i bl) v_tmp; FRZL FR2)).
 clearbody FR2. clear POSTCONDITION MORE_COMMANDS FR1.

(* memcpy(a(i), a(j), size); *)
 apply (semax_pre_post'
 ( PROP ( )
   (LOCALx ([temp _i (Vint (Int.repr i));
   temp _j (Vint (Int.repr j));
   temp _base base; temp _size (Vint (Int.repr (sizeof t)))]
  ++ [temp _n (Vint (Int.repr (N - 1)));
   temp _m (Vint (Int.repr 0));
   lvar _tmp (tarray tuchar 1024) v_tmp;
   lvar _pivot (tarray tuchar 1024) v_pivot; 
   temp _compar compar])
   (SEPx ([data_at sh (Tarray t N noattr) bl base] ++ 
     [data_at Tsh t (Znth i bl) v_tmp; FRZL FR2]))))
 (PROP ( )
   (LOCALx ([temp _i (Vint (Int.repr i));
   temp _j (Vint (Int.repr j));
   temp _base base; temp _size (Vint (Int.repr (sizeof t)))]
  ++ [temp _n (Vint (Int.repr (N - 1)));
   temp _m (Vint (Int.repr 0));
   lvar _tmp (tarray tuchar 1024) v_tmp;
   lvar _pivot (tarray tuchar 1024) v_pivot; 
   temp _compar compar])
   (SEPx ([data_at sh (Tarray t N noattr) (upd_Znth i bl (Znth j bl)) base] ++ 
     [data_at Tsh t (Znth i bl) v_tmp; FRZL FR2]))))).
 unfold app; apply andp_left2; go_lowerx; entailer!.
 unfold app; apply andp_left2; go_lowerx; entailer!.
 apply semax_frame_PQR.
 auto 50 with closed.

 apply forward_call_memcpy_ij; auto; omega.

  set (bl' := upd_Znth i bl (Znth j bl)).
  abbreviate_semax.


  (* memcpy(a(j), tmp), size); *)
  forward_call (sh, Tsh, offset_val (j*sizeof t) base, v_tmp, 
                            existT reptype t (Znth i bl)).
  change (@sizeof _ t) with (sizeof t).
  rewrite Int.signed_repr by rep_omega.
  split.
  assert (0 <= j*sizeof t); [ | rep_omega].
  apply Z.mul_nonneg_nonneg; rep_omega.
  eapply Z.le_trans; try apply H1.
  apply Zmult_le_compat_r.
  omega.
  omega.
  simpl.
  sep_apply (split2_data_at_Tarray_unfold sh t N j).
  omega.
  sep_apply (split2_data_at_Tarray_unfold sh t (N-j) 1).
  omega.
  rewrite (sublist_one 0 1) by (subst bl'; list_solve).
  rewrite (field_adr_ofs) by (auto; omega).
  autorewrite with sublist.
  fold (tarray t 1).
  erewrite data_at_singleton_array_eq by reflexivity.
  cancel.
 split3; auto.
 simpl. destruct Hok as [_ [_ ?]]; auto.
 simpl.
 pose (bl'' := upd_Znth j bl' (Znth i bl)).
 rewrite <- (data_at_singleton_array_eq sh t (Znth i bl) (sublist j (j+1) bl'')).
 2:{ subst bl'' bl'. rewrite sublist_one by list_solve. f_equal.
     rewrite upd_Znth_same by list_solve; auto. }
 change (tarray t 1) with (Tarray t 1 noattr).
 sep_apply (split2_data_at_Tarray_fold' sh t (N-j) 1 (N-j-1) (sublist j N bl'') (sublist j N bl''));
 try (subst bl'' bl'; autorewrite with sublist; auto; try omega).
 f_equal. clear; omega.
 destruct (zeq i j). subst.
 rewrite upd_Znth_unfold. autorewrite with sublist. auto.
 rewrite upd_Znth_unfold. autorewrite with sublist.
 rewrite upd_Znth_unfold. autorewrite with sublist.
 f_equal; clear; omega.
 rewrite <- (field_adr_ofs _ _ N) by (auto; omega).
 sep_apply (split2_data_at_Tarray_fold' sh t N j (N-j));
   try (autorewrite with sublist; auto; try omega).
 destruct (zeq i j). subst.
 rewrite upd_Znth_unfold. autorewrite with sublist. auto.
 rewrite (sublist_upd_Znth_l _ j 0 j); try list_solve; auto.
 forward.
 forward.
 Exists (i+1) (j-1) (upd_Znth j (upd_Znth i bl (Znth j bl)) (Znth i bl)).
 entailer!.
 clear H2 H3 H4 H7 H PNbase PNcompar Pv_pivot0 HPv_pivot.
 clear Delta_specs Delta FR2 Pv_tmp HPv_tmp Pv_tmp0 Pv_pivot.
 autorewrite with sublist.
 split3; [ | | split3; [ | | split3]].
 +
 eapply Permutation_trans; try apply H9.
 rewrite upd_Znth_unfold. autorewrite with sublist.
 rewrite upd_Znth_unfold.
 rewrite sublist_app; autorewrite with sublist; try list_solve.
 rewrite sublist_app; autorewrite with sublist; try list_solve.
 change (Z.succ 0) with 1.
 destruct (zeq i j).
  *
 subst.
 autorewrite with sublist.
 rewrite <- sublist_same at 1 by reflexivity.
 rewrite (sublist_split 0 j (Zlength bl)) by omega.
 apply Permutation_app_head.
 rewrite (sublist_split j (j+1) (Zlength bl)) by omega.
 rewrite sublist_one by omega.
 apply Permutation_app_head.
 replace (Zlength bl - j - 1 + (j + 1)) with (Zlength bl) by (clear; omega).
 apply Permutation_refl.
 *
 autorewrite with sublist.
 replace (j - i - 1 + (i + 1)) with j by omega.
 replace (j + 1 - i - 1 + (i + 1)) with (j+1) by omega.
 replace (Zlength bl - i - 1 + (i + 1)) with (Zlength bl) by omega.
 rewrite <- !app_assoc.
 rewrite <- sublist_same at 1 by reflexivity.
 rewrite (sublist_split 0 i (Zlength bl)) by omega.
 apply Permutation_app_head.
 rewrite (sublist_same 0 1) by list_solve.
 rewrite (sublist_split i (j+1) (Zlength bl)) by list_solve.
 rewrite !app_assoc.
 apply Permutation_app_tail.
 rewrite (sublist_split i (i+1) (j+1)) by list_solve.
 rewrite Permutation_app_comm.
 rewrite (sublist_one i (i+1)) by list_solve.
 apply Permutation_app_tail.
 rewrite (sublist_split (i+1) j (j+1)) by list_solve.
 rewrite Permutation_app_comm.
 rewrite (sublist_one j (j+1)) by list_solve.
 apply Permutation_refl.
 +
 destruct (zeq i j).
 subst.
 autorewrite with sublist.
 rewrite (sublist_split 0 j) by list_solve.
 rewrite Forall_app.
 rewrite sublist_upd_Znth_l by (autorewrite with sublist; omega).
 rewrite sublist_upd_Znth_l by (autorewrite with sublist; omega).
 split; auto.
 rewrite sublist_one by list_solve.
 rewrite upd_Znth_same by list_solve.
 constructor; [ | constructor].
 red. auto.
 rewrite sublist_upd_Znth_l by (autorewrite with sublist; omega).
 rewrite (sublist_split 0 i) by list_solve.
 rewrite Forall_app.
 rewrite sublist_upd_Znth_l by (autorewrite with sublist; omega).
 split; auto.
 rewrite sublist_one by list_solve.
 rewrite upd_Znth_same by list_solve.
 constructor; [ | constructor].
 red. auto.
 +
 rewrite upd_Znth_unfold. autorewrite with sublist.
 rewrite upd_Znth_unfold. autorewrite with sublist.
 change (Z.succ 0) with 1.
 constructor.
 auto.
 replace (j + 1 - i - 1 + (i + 1)) with (j+1) by (clear; omega).
 replace (Zlength bl - i - 1 + (i + 1)) with (Zlength bl) by (clear; omega).
 auto.
 +
 rewrite upd_Znth_unfold. autorewrite with sublist.
 rewrite upd_Znth_unfold. autorewrite with sublist.
 change (Z.succ 0) with 1.
 replace (j + 1 - i - 1 + (i + 1)) with (j+1) by (clear; omega).
 replace (Zlength bl - i - 1 + (i + 1)) with (Zlength bl) by (clear; omega).
 destruct (zeq j (Zlength bl - 1)).
 subst. autorewrite with sublist. auto.
 autorewrite with sublist.
 replace (Zlength bl - 1 - j - Z.succ 0 + (j + 1)) with (Zlength bl - 1) by (clear; omega).
 replace (Znth (Zlength bl - 1) bl)
   with (Znth (Zlength bl - (j+2)) (sublist (j+1) (Zlength bl) bl)).
2:{ rewrite Znth_sublist by list_solve.
     f_equal. omega. }
 apply Forall_Znth; try assumption.
  list_solve.
 +
 destruct H10.
 left.
 rewrite (sublist_split 0 i) by list_solve.
 rewrite Exists_app. left.
 rewrite sublist_upd_Znth_l by (autorewrite with sublist; omega).
 rewrite sublist_upd_Znth_l by (autorewrite with sublist; omega).
 auto.
 destruct H.
 subst j.
 left.
 rewrite upd_Znth_unfold. autorewrite with sublist.
 rewrite (sublist_split 0 i) by list_solve.
 rewrite Exists_app; right.
 rewrite sublist_one by list_solve.
 constructor.
 destruct (zeq i (Zlength bl - 1)).
 subst. autorewrite with sublist. auto.
 rewrite app_Znth1 by list_solve.
 autorewrite with sublist.
 rewrite upd_Znth_same by list_solve.
 auto.
 +
 assert (j=i) by omega. subst j.
 rewrite upd_Znth_same by list_solve.
 auto.
 +
 assert (j=i) by omega. subst j.
 rewrite upd_Znth_same by list_solve.
 auto.
+
 thaw FR2. cancel.
Qed.

Lemma body_qsort:  semax_body Vprog Gprog f_qsort qsort_spec.
Proof.
start_function.
destruct wit as [t Hok ord al Hdef_al].
simpl qsort_t in *. simpl qsort_al in *. simpl qsort_ord in *.
rename H into H'.
assert (H: 0 <= sizeof t <= 1024). {
  split; auto. pose proof (sizeof_pos t); omega.
}
clear H'.
assert_PROP (field_compatible (tarray t (Zlength al)) nil base) as Hbase by entailer!.
Hint Resolve no_saturate_hack: saturate_local.
forward.
forward.
set (N := Zlength al) in *.
rewrite sub_repr.
deadvars!.
forward_if (EX bl:list (reptype t), 
              PROP(Permutation al bl; sorted  (ord_le ord) bl) 
              LOCAL(temp _n (Vint (Int.repr (N - 1)));
                         temp _m (Vint (Int.repr 0));
                         lvar _tmp (tarray tuchar 1024) v_tmp;
                         lvar _pivot (tarray tuchar 1024) v_pivot;
                         temp _base base;
                         temp _size (Vint (Int.repr (sizeof t)));
                         temp _compar compar)
              SEP(data_at_ Tsh (tarray tuchar 1024) v_tmp;
                    data_at_ Tsh (tarray tuchar 1024) v_pivot;
                    func_ptr' (compare_spec t ord) compar;
                    data_at sh (tarray t N) bl base)).
2:{
forward. Exists al. entailer!.
destruct al. constructor.
destruct al. constructor.
elimtype False.
subst N. rewrite !Zlength_cons in H2. clear - H2. rep_omega.
}
2:{
Intros bl.
forward.
Exists bl.
entailer!.
unfold func_ptr'. apply andp_left2; auto.
}
change (data_at_ Tsh (tarray tuchar 1024)) with 
   (data_at Tsh (tarray tuchar 1024) (list_repeat (Z.to_nat 1024) Vundef)).
replace (Z.to_nat 1024) with (Z.to_nat (sizeof t + (1024-sizeof t)))
 by (f_equal; omega).
rewrite <- list_repeat_app' by omega.
rewrite !(split2_data_at_Tarray_app (sizeof t) 1024) by list_solve.
Intros.
freeze FR1 := (data_at _ (tarray _ (1024 - _)) _ _) (data_at _ (tarray _ (_ - _)) _ _) .
simpl in FR1.
change (data_at Tsh (tarray tuchar (sizeof t)) _)
  with (data_at_ Tsh (tarray tuchar (sizeof t))).
sep_apply data_at__change1; try solve [destruct Hok as [? [? ?]]; auto; rep_omega].
sep_apply data_at__change1; try solve [destruct Hok as [? [? ?]]; auto; rep_omega].
forward_call (Tsh, sh, v_pivot, offset_val ((N-1)*sizeof t) base, 
                            existT reptype t (Znth (N-1) al)).
  change (@sizeof _ t) with (sizeof t).
  rewrite Int.signed_repr by rep_omega.
  split.
  assert (0 <= (N-1)*sizeof t); [ | rep_omega].
  apply Z.mul_nonneg_nonneg; rep_omega.
  eapply Z.le_trans; try apply H1.
  apply Zmult_le_compat_r.
  omega.
  omega.
  simpl.
  sep_apply (split2_data_at_Tarray_unfold sh t N (N-1)).
  omega.
  rewrite (sublist_one (N-1) N) by omega.
  replace (N - (N-1)) with 1 by (clear; omega).
  fold (tarray t 1).
  erewrite data_at_singleton_array_eq by reflexivity.
  rewrite field_adr_ofs by (auto; omega). 
 cancel.
 split3; auto.
 simpl. destruct Hok as [_ [_ ?]]; auto.
 simpl.
 set (pivot := Znth (N-1) al).
 pose (n := N-1).
 rewrite <- (data_at_singleton_array_eq sh t pivot [pivot] (offset_val _ base))
   by reflexivity.
 rewrite <- (field_adr_ofs _ _ N) by (auto; omega).
 change (tarray t 1) with (Tarray t 1 noattr).
 pose proof (split2_data_at_Tarray_fold' sh t N (N-1) 1 al al
                (sublist 0 (N-1) al) (sublist (N-1) N al) base).
 rewrite (sublist_one (N-1) N) in H3 by list_solve.
 fold pivot in H3.
 sep_apply H3; auto; try omega.
 autorewrite with sublist; auto.
 clear H3.
 forward.
 forward.
 pose proof I.
 forward_while (EX i:Z, EX j:Z, EX bl: list (reptype t),
      PROP(0<=i<=N; True; -1<=j<N; j >= i-2;
              Forall (ord_ge ord pivot) (sublist 0 i bl);
              Forall (ord_le ord pivot) (sublist (j+1) N bl);
              ord_le ord pivot (Znth (N-1) bl);
              Permutation al bl;
              Exists (ord_eq ord pivot) (sublist 0 i bl) \/ j=n /\ ord_eq ord pivot (Znth (N-1) bl);
              j=i-2 -> ord_eq ord pivot (Znth (i-1) bl))
      LOCAL (temp _i (Vint (Int.repr i)); temp _j (Vint (Int.repr j));
                temp _n (Vint (Int.repr (N-1)));
                temp _m (Vint (Int.repr 0));
                lvar _tmp (tarray tuchar 1024) v_tmp;
                lvar _pivot (tarray tuchar 1024) v_pivot;
                temp _base base; temp _size (Vint (Int.repr (sizeof t)));
                temp _compar compar)
       SEP (data_at sh (Tarray t N noattr) bl base;
              data_at Tsh t pivot v_pivot; data_at_ Tsh t v_tmp;
              FRZL FR1; func_ptr' (compare_spec t ord) compar)).
- (* precondition of main while loop *)
Exists 0 (N-1) al.
entailer!.
autorewrite with sublist.
split3.
constructor.
constructor. subst pivot.
split; auto.
fold (ord_def ord (Znth (N-1) al)).
apply Forall_Znth; auto. omega.
right; split; auto.
pattern (Znth (N-1) al).
apply Forall_Znth; auto. omega.
eapply Forall_impl; try apply Hdef_al.
intros. split; auto.
- (* tc_expr of main while loop *)
entailer!.
- (* body of main while loop *)
assert (Hpivot: ord_def ord pivot)
   by (eapply Forall_Znth; try eassumption; omega).
clearbody pivot.
rename H7 into H6b.
rename H8 into H7. rename H9 into H8. 
rename H10 into H8b. rename H11 into H9. rename H12 into H10.
rename H13 into H8c.
assert (Hij: i <= j) by omega.
rename H2 into Hmn.
assert (Zlength al = Zlength bl). {
 rewrite !Zlength_correct. f_equal. apply Permutation_length; auto.
}
assert (Hdef_bl: Forall (ord_def ord) bl) by (eapply Forall_perm; eauto).
subst N n.
rewrite H2 in *.
clear H8c H6b HRE Hdef_al.
set (N := Zlength bl) in *.
set (n := N-1) in *.
pose proof I. move H2 before Hmn.
clear H5. assert (H5: 0<=j) by omega.
fold (tarray t N).
apply semax_seq' with (EX i:Z,
      PROP(0<=i<=j+1; i<N;
              Forall ( ord_ge ord pivot) (sublist 0 i bl);
             ord_le ord pivot (Znth i bl);
              Exists ( ord_eq ord pivot) (sublist 0 i bl) \/
              j = (N-1) /\  ord_eq ord pivot (Znth (N-1) bl))
      LOCAL (temp _i (Vint (Int.repr i)); temp _j (Vint (Int.repr j));
                temp _n (Vint (Int.repr n));
                temp _m (Vint (Int.repr 0));
                lvar _tmp (tarray tuchar 1024) v_tmp;
                lvar _pivot (tarray tuchar 1024) v_pivot;
                temp _base base; temp _size (Vint (Int.repr (sizeof t)));
                temp _compar compar)
       SEP (data_at sh (tarray t N) bl base;
              data_at Tsh t pivot v_pivot; data_at_ Tsh t v_tmp;
              FRZL FR1; func_ptr' (compare_spec t ord) compar)).
apply qsort_loop_i; auto; omega.
 (* after i loop *)
 clear dependent i.
 Intros i.
 rename H12 into H14. rename H13 into H12.
 rename H10 into H13. rename H12 into H10.
 apply semax_seq' with (EX j':Z,
      PROP(0<=j'<=j /\ i-1<=j';
              Forall (ord_lt ord pivot) (sublist (j'+1) (j+1) bl);
              ord_le ord (Znth j' bl) pivot)
      LOCAL (temp _i (Vint (Int.repr i)); temp _j (Vint (Int.repr j'));
                 temp _n (Vint (Int.repr (N-1)));
                 temp _m (Vint (Int.repr 0));
                 lvar _tmp (tarray tuchar 1024) v_tmp;
                 lvar _pivot (tarray tuchar 1024) v_pivot;
                 temp _base base; temp _size (Vint (Int.repr (sizeof t)));
                 temp _compar compar)
       SEP (data_at sh (tarray t N) bl base;
              data_at Tsh t pivot v_pivot; data_at_ Tsh t v_tmp;
              FRZL FR1; func_ptr' (compare_spec t ord) compar)).
apply qsort_loop_j; auto.
omega.
 (* after the j loop *)
 rename H into H''.
  Intros j'. subst n.
  rename H12 into H'. clear H5. assert (H5: 0<=j<N) by omega.
  clear H6. rename H15 into H6. rename H16 into H15.
  assert (H10': Exists ( ord_eq ord pivot) (sublist 0 i bl) \/
      j' = N-1 /\  ord_eq ord pivot (Znth (N-1) bl)). {
   destruct H10; auto. destruct H10; subst j.
   destruct (zeq j' (N-1)); auto.
   left.
   apply Forall_Znth with (i0:=(N-1)-j'-1) in H6; 
     try (autorewrite with sublist; omega). 
   autorewrite with sublist in H6.
   replace (N-1 - j' - 1 + (j' + 1)) with (N-1) in H6 by omega.
   elimtype False.
   clear - H12 H6.
   red in H12,H6. destruct H12, H6. contradiction.
  }
  assert (Forall (ord_le ord pivot) (sublist (j' + 1) N bl)).
  rewrite (sublist_split _ (j+1)) by omega.
  rewrite Forall_app. split; auto.
  eapply Forall_impl; try apply H6.
  clear; intros. destruct H; auto.
  clear H6.
  assert (j'<N) by omega.
  destruct H as [H _].
  destruct H4 as [H4 _]. clear H5 H8.
  assert (H8c': j'=i-2 -> Znth (i-1) bl = pivot). {
    intros. subst j'. omega.
  }
  clear j H10. rename H8c' into H8c.
  pose proof (conj H H6). clear H H6.
  rename j' into j. rename H10' into H10.
  forward_if
    (EX i:Z, EX j:Z, EX bl: list (reptype t), 
   PROP (Permutation al bl; 0<=i<=N; -1<=j<N; j >= i-2;
             Forall ( ord_ge ord pivot) (sublist 0 i bl);
             Forall (ord_le ord pivot) (sublist (j + 1) N bl);
             ord_le ord pivot (Znth (N-1) bl);
             Exists ( ord_eq ord pivot) (sublist 0 i bl) \/
             j = N-1 /\  ord_eq ord pivot (Znth (N-1) bl);
             j = i - 2 ->  ord_eq ord pivot (Znth (i - 1) bl))
   LOCAL (temp _i (Vint (Int.repr i)); temp _j (Vint (Int.repr j));
               temp _n (Vint (Int.repr (N - 1)));
               temp _m (Vint (Int.repr 0));
               lvar _tmp (tarray tuchar 1024) v_tmp;
               lvar _pivot (tarray tuchar 1024) v_pivot;
               temp _base base; temp _size (Vint (Int.repr (sizeof t)));
               temp _compar compar)
   SEP (data_at sh (tarray t N) bl base;
   data_at Tsh t pivot v_pivot; data_at_ Tsh t v_tmp;
   FRZL FR1; func_ptr' (compare_spec t ord) compar)).
 +
  apply verif_qsort_then2; auto; omega.
 +
       forward.
       Exists i j bl.
       entailer!.
 +
       Intros i2 j2 bl2.
       Exists (i2,j2,bl2).
       rewrite H2 in *.
       entailer!.
-
    assert (Zlength al = Zlength bl). {
     rewrite !Zlength_correct. f_equal. apply Permutation_length; auto.
    }
   assert (Hdef_bl: Forall (ord_def ord) bl).
     eapply Forall_perm; try apply Hdef_al; auto.
   rewrite <- (sublist_same 0 N bl) by omega.
   rewrite (sublist_split 0 (j+1) _ bl) by omega.
   fold (tarray t N).
   rewrite (split2_data_at_Tarray_app (j+1)) by list_solve.
   rewrite split_func_ptr'.
   Intros.
   assert (Hdef_blj: Forall (ord_def ord) (sublist 0 (j+1) bl)).
    apply Forall_sublist; auto.
   pose (w1 := Build_qsort_witness _ t Hok ord _ Hdef_blj).
   forward_call (sh, base, compar, w1).
   entailer!. autorewrite with sublist. auto.
   simpl. autorewrite with sublist. cancel.
   simpl.
   change (@sizeof _ t) with (@sizeof (@cenv_cs CompSpecs) t).
   split3; auto; try omega.
   autorewrite with sublist. split; try rep_omega.
   eapply Z.le_trans; try apply H1.
   apply Z.mul_le_mono_nonneg_r; omega.
   simpl PROPx. simpl qsort_t. clear w1 Hdef_blj.
   Intros cl.  
   sep_apply (split2_data_at_Tarray_unfold sh t (N-(j+1)) (i-(j+1))).
   omega.
   rewrite !sublist_sublist by omega.
   replace (i - (j + 1) + (j + 1)) with i by omega.
   replace (N - (j + 1) + (j + 1)) with N by omega.
   replace (N - (j + 1) - (i - (j + 1))) with (N-i) by omega.
   unfold tarray.
   rewrite (field_adr_ofs (j+1))  by (auto; omega).
   rewrite (field_adr_ofs (i-(j+1))); auto; try omega.
  2:{ generalize Hbase; intro Hbase'.
       apply (field_compatible_Tarray_split t (j+1) N) in Hbase'; try omega.
       destruct Hbase' as [_ Hbase']. unfold tarray in Hbase'.
       rewrite field_adr_ofs in Hbase'; auto; try rep_omega.
    }
   rewrite offset_offset_val.
   replace      ((j + 1) * sizeof t + (i - (j + 1)) * sizeof t)%Z
     with (i * sizeof t)%Z.
  2:{ rewrite <- Z.mul_add_distr_r. f_equal. omega. }
   rewrite split_func_ptr'.
   Intros.
   assert (Hdef_blj': Forall (ord_def ord) (sublist i N bl)).
    apply Forall_sublist; auto.
   pose (w2 := Build_qsort_witness _ t Hok ord _ Hdef_blj').
   forward_call (sh, offset_val (i * sizeof t) base, compar, w2).
   change (@sizeof _ t) with (sizeof t).
   rewrite Int.signed_repr by rep_omega.
  split.
  assert (0 <= i*sizeof t); [ | rep_omega].
  apply Z.mul_nonneg_nonneg; rep_omega.
  eapply Z.le_trans; try apply H1.
  apply Zmult_le_compat_r.
  omega.
  omega.
  simpl.
  apply prop_right.
  split3; auto.
  normalize.
  split; auto.
  autorewrite with sublist.
  f_equal. f_equal. f_equal. omega.
  simpl.
  autorewrite with sublist.
  cancel.
  simpl. autorewrite with sublist.
  change (@sizeof _ t) with (sizeof t).
  split3; auto; try omega.
  split; try rep_omega.
   eapply Z.le_trans; try apply H1.
   apply Z.mul_le_mono_nonneg_r; omega.

   Intros dl.
   simpl qsort_al in *; simpl qsort_t in *; simpl qsort_ord in *.
   clear w2.
   Exists (cl ++ sublist (j+1) i bl ++ dl).
   thaw FR1.
   entailer!.
   split.
   eapply Permutation_trans; [eassumption |].
   eapply Permutation_trans.
   2:{ apply Permutation_app. eassumption.
        apply Permutation_app. apply Permutation_refl. eassumption. }
   autorewrite with sublist. apply Permutation_refl.
   apply sorted_app with pivot; auto.
   apply ord_le_trans.
   apply sorted_app with pivot; auto.
   apply ord_le_trans.
   assert (Zlength (sublist (j+1) i bl) = i-(j+1)) by list_solve.
   clear - H28 H7.
   destruct (sublist (j+1) i bl). constructor.
   destruct l. constructor.
   autorewrite with sublist in H28.
   rep_omega.
   replace (sublist (j+1) i bl) with (sublist (j+1) i (sublist 0 i bl))
     by (autorewrite with sublist; auto).
   eapply Forall_sublist.
   eapply Forall_impl; try apply H8.
   clear. auto.
   eapply Forall_perm; try apply H17.
   replace (sublist i N bl) with (sublist (i-(j+1)) (N-(j+1)) (sublist (j+1) N bl))
     by (autorewrite with sublist; auto).
   eapply Forall_sublist.  
   auto.
   eapply Forall_perm; try apply H15.
   replace (sublist 0 (j+1) bl) with (sublist 0 (j+1) (sublist 0 i bl)) 
     by (autorewrite with sublist; auto).
   eapply Forall_sublist.  
   auto.
   apply Forall_app; split.
   replace (sublist (j+1) i bl) with (sublist 0 (i-(j+1)) (sublist (j+1) N bl)) 
     by (autorewrite with sublist; auto).
   eapply Forall_sublist.  
   auto.
   eapply Forall_perm; try apply H17.
   replace (sublist i N bl) with (sublist (i-(j+1)) (N-(j+1)) (sublist (j+1) N bl))
     by (autorewrite with sublist; auto).
   eapply Forall_sublist.  
   auto.
   pose proof (Permutation_Zlength H17). autorewrite with sublist in H28.
   erewrite split2_data_at_Tarray_app; [ | reflexivity | list_solve ].
   erewrite split2_data_at_Tarray_app; [ | reflexivity | list_solve ].
   autorewrite with sublist.
   unfold tarray.
   rewrite !(field_adr_ofs _ _ N) by (auto; omega).
   rewrite H23.
   rewrite !field_adr_ofs; auto with field_compatible; try omega.
  2:{ generalize Hbase; intro Hbase'.
       apply (field_compatible_Tarray_split t (j+1) N) in Hbase'; try omega.
       destruct Hbase' as [_ Hbase']. unfold tarray in Hbase'.
       rewrite field_adr_ofs in Hbase'; auto; try rep_omega.
    }
   rewrite !offset_offset_val.
   rewrite <- !Z.mul_add_distr_r.
   change (sizeof tuchar) with 1. rewrite !Z.mul_1_r.
   replace (j+1+(i-(j+1))) with i by (clear; omega).
   replace (N - (j + 1) - (i - (j + 1))) with (N-i) by (clear; omega).
   cancel.
   sep_apply (data_at_data_at_ Tsh t).
   sep_apply (data_at__change2 Tsh t).
   sep_apply (data_at__change2 Tsh t).
   fold (tarray tuchar 1024).
   change (data_at_ Tsh (tarray tuchar 1024)) with 
      (data_at Tsh (tarray tuchar 1024) (list_repeat (Z.to_nat 1024) Vundef)).
   replace (Z.to_nat 1024) with (Z.to_nat (sizeof t + (1024-sizeof t)))
     by (f_equal; omega).
   rewrite <- list_repeat_app' by omega.
   rewrite !(split2_data_at_Tarray_app (sizeof t) 1024) by list_solve.
   unfold tarray.
   rewrite !field_adr_ofs; auto with field_compatible; try omega.
   change (sizeof tuchar) with 1. rewrite !Z.mul_1_r.
   simpl.
   change (@sizeof _ t) with (sizeof t).
   cancel.
Qed.











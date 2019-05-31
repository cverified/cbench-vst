Require Import VST.floyd.proofauto.
Require Import qsort1.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Require Import float_lemmas.
Require Import Permutation.
Definition N: Z := 666666.

Lemma N_eq: N = ltac:(let n := eval compute in N in exact n).
Proof. reflexivity. Qed.
Hint Rewrite N_eq : rep_omega.
Opaque N.


Theorem Forall_perm: forall {A} (f: A -> Prop) al bl,
  Permutation al bl ->
  Forall f al -> Forall f bl.
Proof.
  induction 1; simpl; intros; auto.
  inv H0; constructor; auto.
  inv H. inv H3. constructor; auto.
Qed.

Lemma Exists_app:
  forall {A} (P: A->Prop) (l1 l2: list A),
     Exists P (l1++l2) <-> Exists P l1 \/ Exists P l2.
Proof.
intros.
induction l1; simpl; auto.
split; intros. right; auto. destruct H; auto. inv H.
split; intro.
inv H. left. left. auto.
rewrite IHl1 in H1.
destruct H1; auto. 
destruct H.
inv H. left; auto.
right. rewrite IHl1; auto.
right. rewrite IHl1; auto.
Qed.

Inductive sorted: list val -> Prop := 
| sorted_nil:
    sorted nil
| sorted_1: forall x,
    sorted (x::nil)
| sorted_cons: forall x y l,
    f_cmp Cle x y -> sorted (y::l) -> sorted (x::y::l).

Lemma sorted_app:
  forall pivot al bl,
    sorted al -> sorted bl ->
    Forall (f_cmp Cge pivot) al ->
    Forall (f_cmp Cle pivot) bl ->
    sorted (al++bl).
Proof.
intros.
induction H.
simpl; auto.
simpl.
inv H1. inv H5.
inv H0.
constructor.
inv H2.
constructor.
apply f_cmp_le_trans with pivot; auto.
apply f_cmp_swap in H4; auto.
constructor.
inv H2.
constructor.
apply f_cmp_le_trans with pivot; auto.
apply f_cmp_swap in H4; auto.
constructor; auto.
simpl.
constructor; auto.
apply IHsorted.
inv H1; auto.
Qed.

Definition quicksort_spec :=
 DECLARE _quicksort
  WITH gv : globals, m: int, n: int, before: list val, al: list val, after: list val
  PRE  [ _m OF tint, _n OF tint] 
    PROP(if zlt (Int.signed m) (Int.signed n)
            then   (Zlength before = Int.signed m 
                     /\ Zlength after = N-(Int.signed n+1)
                     /\ Zlength al = Int.signed n+1- Int.signed m)
            else al=nil;
            Forall def_float al)
    LOCAL(temp _m (Vint m); temp _n (Vint n); gvars gv)
    SEP(data_at Ews (tarray tdouble N) 
             (before ++ al ++ after) (gv _a))
  POST [ tvoid ]
    EX bl: list val,
     PROP(Permutation al bl; sorted bl) 
     LOCAL ()
    SEP(data_at Ews (tarray tdouble N)
             (before ++ bl ++ after) (gv _a)).

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog nil gv
  POST [ tint ]  
     PROP() 
     LOCAL (temp ret_temp (Vint (Int.repr 0)))
     SEP(TT).

Definition Gprog : funspecs :=
        ltac:(with_library prog [quicksort_spec]).

Set Nested Proofs Allowed.

Lemma no_saturate_hack:
  forall sh n al p,
    data_at sh (tarray tdouble n) al p |-- !!True.
Proof.
intros. apply prop_right. auto.
Qed.
Hint Resolve no_saturate_hack: saturate_local.

Lemma body_quicksort:  semax_body Vprog Gprog f_quicksort quicksort_spec.
Proof.
start_function.
rename H0 into Hdef_al.
forward_if (EX bl:list val, 
              PROP(Permutation al bl; sorted bl) LOCAL()
    SEP(data_at Ews (tarray tdouble N)
             (before ++ bl ++ after) (gv _a))).
2:{
forward. Exists al. entailer!.
rewrite if_false in H by (apply lt_false_inv; auto).
subst al. constructor.
}
2:{
Intros bl.
forward.
Exists bl.
entailer!.
}
apply lt_inv in H0.
rewrite if_true in H by auto.
rename H0 into H2.
destruct H as [H [H0 H1]].
rename m into m'. rename n into n'.
rewrite <- (Int.repr_signed m').
rewrite <- (Int.repr_signed n').
set (m := Zlength before) in *.
rewrite <- H in *.
clear m' H.
forget (Int.signed n') as n.
pose proof I.
pose proof I.
forward.
entailer!.
entailer!.
apply is_float_middle; auto; omega.
forward.
forward.
set (pivot := Znth (n-m) al).
forward_while (EX i:Z, EX j:Z, EX bl: list val,
      PROP(m<=i<=n+1; True; m-1<=j<=n; j >= i-2;
              Forall (f_cmp Cge pivot) (sublist 0 (i-m) bl);
              Forall (f_cmp Cle pivot) (sublist (j+1-m) (n+1-m) bl);
              f_cmp Cle pivot (Znth (n - m) bl);
              Permutation al bl;
              Exists (f_cmp Ceq pivot) (sublist 0 (i-m) bl) \/ j=n /\ f_cmp Ceq pivot (Znth (n-m) bl);
              j=i-2 -> f_cmp Ceq pivot (Znth (i-1-m) bl))
      LOCAL (temp _i (Vint (Int.repr i)); temp _j (Vint (Int.repr j));
                temp _pivot pivot; temp _m (Vint (Int.repr m));
                temp _n (Vint (Int.repr n)); gvars gv)
       SEP (data_at Ews (tarray tdouble N)
               (before ++ bl ++ after) (gv _a))).
- (* precondition of main while loop *)
Exists m n al.
entailer!.
autorewrite with sublist.
split3.
constructor.
constructor. subst pivot.
split; auto.
apply f_le_refl. apply Forall_Znth; try omega. auto.
split; auto.
right; split; auto.
apply float_cmp_eq_refl.
eapply Forall_forall; try apply Hdef_al. apply Znth_In; omega.
- (* tc_expr of main while loop *)
entailer!.
- (* body of main while loop *)
assert (Hpivot: def_float pivot)
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
assert (Hdef_bl: Forall def_float bl) by (eapply Forall_perm; eauto).
rewrite H2 in *.
clear H8c H6b HRE Hdef_al H2.
pose proof I. move H2 before Hmn.
clear H5. assert (H5: m<=j) by omega.
forward_loop (EX i:Z,
      PROP(m<=i<=j+1; i<=n;
              Forall (f_cmp Cge pivot) (sublist 0 (i-m) bl);
              Exists (f_cmp Ceq pivot) (sublist 0 (i - m) bl) \/
              j = n /\ f_cmp Ceq pivot (Znth (n - m) bl))
      LOCAL (temp _i (Vint (Int.repr i)); temp _j (Vint (Int.repr j));
                temp _pivot pivot; temp _m (Vint (Int.repr m));
                temp _n (Vint (Int.repr n)); gvars gv)
       SEP (data_at Ews (tarray tdouble N)
               (before ++ bl ++ after) (gv _a)))
  break: (EX i:Z,
      PROP(m<=i<=j+1; i<=n;
              Forall (f_cmp Cge pivot) (sublist 0 (i-m) bl);
             f_cmp Cle pivot (Znth (i-m) bl);
              Exists (f_cmp Ceq pivot) (sublist 0 (i - m) bl) \/
              j = n /\ f_cmp Ceq pivot (Znth (n - m) bl))
      LOCAL (temp _i (Vint (Int.repr i)); temp _j (Vint (Int.repr j));
                temp _pivot pivot; temp _m (Vint (Int.repr m));
                temp _n (Vint (Int.repr n)); gvars gv)
       SEP (data_at Ews (tarray tdouble N)
               (before ++ bl ++ after) (gv _a))).
 + (* precondition of i loop *)
   Exists i.
   entailer!.
 + (* body of i loop *)
   clear dependent i.
   clear H.
   Intros i.
   forward.
      entailer!.
      entailer!.
      apply is_float_middle; auto; omega.
   forward_if.
   forward.
   Exists (i+1).
   entailer!.
   autorewrite with sublist in H11.  fold m in H11.
   apply both_float_cmp_true in H11; auto.
   2: eapply Forall_Znth; try eassumption; auto; omega.
   apply f_cmp_swap in H11; simpl in H11.
   assert (H16: i<>j+1). {
      intro; subst i.
      eapply float_cmp_gt_le_false; try apply H11.
      apply Forall_Znth with (i:=0) in H8; try (autorewrite with sublist; omega).
      autorewrite with sublist in H8; auto.
   }
   assert (H17: i <= j) by omega. clear H4. destruct H as [H _].
   clear P_a HP_a H12 H13.
   assert (i<>n). {
      intro; subst i.
      eapply float_cmp_gt_le_false; try apply H11; eauto.
    }
    split3; try rep_omega.
    split.
    rewrite (sublist_split _ (i-m)) by rep_omega.
    rewrite Forall_app; split; auto.
    rewrite sublist_one by omega. repeat constructor; auto.
    rewrite f_cmp_ge_gt_eq. auto.
    destruct H10; auto. left.
    rewrite (sublist_split _ (i-m)) by omega.
    apply Exists_app. auto.

   forward.
   Exists i. entailer!.
   apply both_float_cmp_false in H11; auto.
   autorewrite with sublist in H11.
   fold m in H11. 
   apply f_cmp_swap in H11; simpl in H11.
   auto.
   eapply Forall_forall; eauto.
   autorewrite with sublist. apply Znth_In. omega.
 + (* after i loop *)
 clear dependent i.
 Intros i.
 rename H10 into H13. rename H12 into H10.
 rename H11 into H14.
 forward_loop (EX j':Z,
      PROP(m<=j'<=j /\ i-1<=j';
              Forall (f_cmp Clt pivot) (sublist (j'+1-m) (j+1-m) bl))
      LOCAL (temp _i (Vint (Int.repr i)); temp _j (Vint (Int.repr j'));
                temp _pivot pivot; temp _m (Vint (Int.repr m));
                temp _n (Vint (Int.repr n)); gvars gv)
       SEP (data_at Ews (tarray tdouble N)
               (before ++ bl ++ after) (gv _a)))
  break: (EX j':Z,
      PROP(m<=j'<=j /\ i-1<=j';
              Forall (f_cmp Clt pivot) (sublist (j'+1-m) (j+1-m) bl);
             f_cmp Cle (Znth (j'-m) bl) pivot)
      LOCAL (temp _i (Vint (Int.repr i)); temp _j (Vint (Int.repr j'));
                temp _pivot pivot; temp _m (Vint (Int.repr m));
                temp _n (Vint (Int.repr n)); gvars gv)
       SEP (data_at Ews (tarray tdouble N)
               (before ++ bl ++ after) (gv _a))).
  * 
    Exists j; entailer!.
    autorewrite with sublist. constructor.
  * clear H.
    Intros j'. rename H11 into H'. destruct H6 as [_ H6']. rename H12 into H6.
    forward.
      entailer!.
      entailer!.
      apply is_float_middle; auto; rep_omega.
   forward_if.
   forward.
   Exists (j'-1).
   entailer!.
   autorewrite with sublist in H11.
   apply both_float_cmp_true in H11; auto.
   2: eapply Forall_Znth; try eassumption; auto; omega.
   apply f_cmp_swap in H11; simpl in H11.
   fold m in H11.
   rewrite Z.sub_add.
   split. split; try omega.
   destruct (zeq j' m); [elimtype False | omega]. {
      subst j'.
      autorewrite with sublist in *.
      clear P_a HP_a H15 H12.
      destruct (zeq i m). 
      2:{ rewrite (sublist_split _ 1) in H13 by omega.
           rewrite Forall_app in H13. destruct H13 as [H13 _].
           rewrite sublist_one in H13 by omega. inv H13.
           eapply f_cmp_lt_ge_false; eauto.
      } 
      subst i.
      autorewrite with sublist in *.
      destruct H10. inv H10. destruct H10. subst j.
      apply Forall_Znth with (i:=n-m-1) in H6;
        try (autorewrite with sublist; rep_omega).
      autorewrite with sublist in H6.
      eapply f_cmp_lt_ge_false; try apply H6.
      apply f_cmp_ge_gt_eq; auto.
   }
   split. destruct (zeq j' (i-1)); [ | omega]. subst j'.
   elimtype False. clear P_a HP_a H'.
   rewrite Z.sub_add in H6. 
   assert (f_cmp Cge pivot (Znth (i-1-m) bl)). {
      replace (Znth (i-1-m) bl) with (Znth (i-1-m) (sublist 0 (i-m) bl)).
      2:{ rewrite Znth_sublist by rep_omega. f_equal. omega. }
   eapply Forall_Znth; try apply H13. 
   autorewrite with sublist; rep_omega.
   }
  eapply f_cmp_lt_ge_false; eauto.
   rewrite (sublist_split _ (j'+1-m)) by omega.
   rewrite Forall_app. split; auto. rewrite sublist_one by omega.
   repeat constructor; auto.
   autorewrite with sublist in H11.
   apply both_float_cmp_false in H11; auto.
   2: eapply Forall_Znth; try eassumption; auto; omega.
   fold m in H11. 
   apply f_cmp_swap in H11; simpl in H11.

   forward. (* break *)
   Exists j'.
   entailer!.
   apply f_cmp_swap in H11; auto.
 * (* after the j loop *)
   clear H.
  Intros j'.
  rename H11 into H'. clear H5. assert (H5: m<=j<=n) by omega.
  clear H6. rename H12 into H6.
  assert (H10': Exists (f_cmp Ceq pivot) (sublist 0 (i - m) bl) \/
      j' = n /\ f_cmp Ceq pivot (Znth (n - m) bl)). {
   destruct H10; auto. destruct H10; subst j.
   destruct (zeq j' n); auto.
   left.
   apply Forall_Znth with (i0:=n-j'-1) in H6; 
     try (autorewrite with sublist; omega). 
   autorewrite with sublist in H6.
   replace (n - j' - 1 + (j' + 1 - m)) with (n-m) in H6 by omega.
   elimtype False.
   eapply f_cmp_lt_ge_false; try apply H6.
   apply f_cmp_ge_gt_eq; auto.
  }
  assert (Forall (f_cmp Cle pivot) (sublist (j' + 1 - m) (n + 1 - m) bl)).
  rewrite (sublist_split _ (j+1-m)) by omega.
  rewrite Forall_app. split; auto.
  eapply Forall_impl; try apply H6.
  clear; intros; rewrite f_cmp_le_lt_eq; auto.
  clear H6.
  assert (j'<=n) by omega.
  destruct H as [H _].
  destruct H4 as [H4 _]. clear H5 H8.
  assert (H8c': j'=i-2 -> Znth (i-1-m) bl = pivot). {
    intros. subst j'. omega.
  }
  clear j H10. rename H8c' into H8c.
  pose proof (conj H H6). clear H H6.
  rename j' into j. rename H10' into H10.
  forward_if
    (EX i:Z, EX j:Z, EX bl: list val, 
   PROP (Permutation al bl; m<=i<=n+1; m-1<=j<=n; j >= i-2;
             Forall (f_cmp Cge pivot) (sublist 0 (i - m) bl);
             Forall (f_cmp Cle pivot) (sublist (j + 1 - m) (n + 1 - m) bl);
             f_cmp Cle pivot (Znth (n - m) bl);
             Exists (f_cmp Ceq pivot) (sublist 0 (i - m) bl) \/
             j = n /\ f_cmp Ceq pivot (Znth (n - m) bl);
             j = i - 2 -> f_cmp Ceq pivot (Znth (i - 1 - m) bl))
   LOCAL (temp _i (Vint (Int.repr i)); temp _j (Vint (Int.repr j));
   temp _pivot pivot; temp _m (Vint (Int.repr m));
   temp _n (Vint (Int.repr n)); gvars gv)
   SEP (data_at Ews (tarray tdouble N)
          (before ++ bl ++ after) 
          (gv _a))).
   -- 
     forward. entailer!. entailer!.
     apply is_float_middle; auto; omega.
     forward. entailer!. entailer!.
     apply is_float_middle; auto; omega.
     forward. entailer!.
     forward. entailer!.
     forward.
     forward.
     autorewrite with sublist.
     fold m.
     rewrite !def_float_f2f
       by (eapply Forall_Znth; try eassumption; omega).
     destruct (zeq i j).
     ++ subst j.
           replace (upd_Znth (i - m) (upd_Znth (i - m) bl (Znth (i - m) bl))
             (Znth (i - m) bl)) with bl.
          2:{ apply Znth_eq_ext. list_solve. intros j ? .
               destruct (zeq j (i-m)); try subst j; autorewrite with sublist.
               rewrite !(upd_Znth_same); autorewrite with sublist; auto.
               rewrite !(upd_Znth_diff) by (autorewrite with sublist; omega).
               auto.
             }
          Exists (i+1) (i-1) bl. entailer!.
          rewrite Z.sub_add.
          assert (f_cmp Ceq pivot (Znth (i-m) bl)). {
             clear - H14 H15.
           apply f_cmp_swap in H15. simpl in H15.
           eapply f_cmp_le_ge; eauto.
          } clear H14 H15.
          clear H8 H6 P_a HP_a. clear H. rename H12 into H18.
          split3.
          rewrite (sublist_split _ (i-m)) by omega.
          rewrite Forall_app. split; auto.
          rewrite sublist_one by rep_omega. repeat constructor.
          rewrite f_cmp_ge_gt_eq; auto.
          rewrite (sublist_split _ (i+1-m)) by omega. rewrite Forall_app.
          split; auto.
          rewrite sublist_one by omega. repeat constructor.
          rewrite f_cmp_le_lt_eq; auto.
          split.
          left. apply Exists_exists. exists (Znth (i-m) bl); split; auto.
          replace (Znth (i-m) bl) with (Znth (i-m) (sublist 0 (i+1-m) bl)).
          apply Znth_In. autorewrite with sublist; omega.
          autorewrite with sublist. auto.
          intros. rewrite Z.add_simpl_r.  auto.
     ++
      Exists (i+1) (j-1)   (upd_Znth (j - m) (upd_Znth (i - m) bl (Znth (j - m) bl)) (Znth (i - m) bl)).
      entailer!.
     assert (i<j) by omega.
     clear n0 H8 H12 H6 P_a HP_a.
     replace (upd_Znth (j - m) (upd_Znth (i - m) bl (Znth (j - m) bl)) (Znth (i - m) bl))
      with (sublist 0 (i-m) bl ++ sublist (j-m) (j+1-m) bl
               ++ sublist (i+1-m) (j-m) bl 
               ++ sublist (i-m) (i+1-m) bl ++ sublist (j+1-m) (Zlength bl) bl).
     2:{ rewrite  !upd_Znth_unfold.
          autorewrite with sublist.
          rewrite (sublist_one (j-m) (j+1-m)) by omega.
          rewrite (sublist_one (i-m) (i+1-m)) by omega.
          rewrite !sublist0_app2 by (autorewrite with sublist; omega).
          autorewrite with sublist.
          replace (j-m - (i-m)) with (j-i) by omega.
          replace (i - m + (Z.succ 0 + (Zlength bl - (i - m + 1))))
                   with (Zlength bl) by omega.
          replace (j-m+1-(i-m)-Z.succ 0 +(i-m+1)) with (j+1-m) by omega.
          replace (j-i- Z.succ 0 +(i-m+1)) with (j-m) by omega.
          replace (i-m+1) with (i+1-m) by omega.
          rewrite <- (app_ass (sublist 0 (i-m) _)).
          rewrite !app_ass. reflexivity.
        }
       split3.
       apply perm_trans
         with (sublist 0 (i-m) bl ++ sublist (i-m) (i+1-m) bl ++
                 sublist (i + 1 - m) (j - m) bl ++
                 sublist (j - m) (j + 1 - m) bl ++
                 sublist (j + 1 - m) (Zlength bl) bl).
       rewrite <- !sublist_split by omega.
       autorewrite with sublist; auto.
       apply Permutation_app_head; auto.
       rewrite <- !app_ass.
       apply Permutation_app_tail; auto.
       apply Permutation_app_comm_trans.
       rewrite !app_ass.
       apply Permutation_app_head; auto.
       apply Permutation_app_comm.
       rewrite sublist0_app2 by (autorewrite with sublist; rep_omega).
       autorewrite with sublist.
       rewrite Forall_app. split. auto.
       rewrite sublist_one by rep_omega. repeat constructor.
       apply f_cmp_swap in H15; auto.
       rewrite !sublist_app2 by (autorewrite with sublist; rep_omega).
       autorewrite with sublist.
       split.
       rewrite Forall_app. split.
       rewrite sublist_one by rep_omega. repeat constructor.
       auto.
       rewrite H1. auto.
       replace (n-m-(i-m)-(j+1-m-(j-m))-(j-m-(i+1-m)))
                  with (n -j) by omega.
       rewrite (sublist0_app2 (i+1-m)) by list_solve.
       autorewrite with sublist.
       replace (i+1-m-(i-m)+(j-m)) with (j+1-m) by omega.
       split.
       destruct (zeq n j).
       rewrite app_Znth1 by list_solve. rewrite sublist_one by list_solve.
       replace (n-j) with 0 by omega. autorewrite with sublist.
       auto.
       autorewrite with sublist.
       replace (n - j - (i + 1 - m - (i - m)) + (j + 1 - m))
           with (n-m) by omega. auto.
       left.
       destruct H10 as [? | [? ?]].
       apply Exists_app. left. rewrite (sublist_split _ (i-m)) by rep_omega.
       apply Exists_app; left. auto.
       subst j. clear H H5 H16 H8b. apply Exists_app. right.
       rewrite sublist_one by omega. constructor. auto.
   --
       forward.
       Exists i j bl.
       entailer!.
   --
       Intros i2 j2 bl2.
       Exists (i2,j2,bl2). entailer!.
-
    assert (Zlength al = Zlength bl). {
     rewrite !Zlength_correct. f_equal. apply Permutation_length; auto.
    }
   assert (Hdef_bl: Forall def_float bl).
     eapply Forall_perm; try apply Hdef_al; auto.
   rewrite <- (sublist_same 0 (n+1-m) bl) by omega.
   rewrite (sublist_split 0 (j+1-m) _ bl) by omega.
   rewrite <- app_assoc.
   rewrite (app_assoc before).
   apply semax_seq' with 
 (EX cl:list val,
   PROP (Permutation (sublist 0 (j + 1 - m) bl) cl;
             sorted cl)
   LOCAL (temp _i (Vint (Int.repr i)); temp _j (Vint (Int.repr j));
   temp _pivot pivot; temp _m (Vint (Int.repr m));
   temp _n (Vint (Int.repr n)); gvars gv)
   SEP (data_at Ews (tarray tdouble N)
          ((before ++ cl) ++
           (sublist (j + 1 - m) (n + 1 - m) bl) ++ after)
          (gv _a))).
  +
   destruct (zlt m j).
   * rewrite !app_ass.
     forward_call (gv,Int.repr m, Int.repr j,before,sublist 0 (j+1-m) bl, (sublist (j+1-m) (n+1-m) bl)++after).
     rewrite !Int.signed_repr by rep_omega.
     rewrite if_true by auto.
     split. split3; auto.
     autorewrite with sublist; omega.
     autorewrite with sublist; auto.
     apply Forall_sublist; auto.
     Intros cl. Exists cl.
     rewrite !app_ass.
     entailer!.
   * rewrite !app_ass.
      rewrite <- (app_ass (sublist _ _ _)).
      rewrite <- sublist_split by omega.
      rewrite sublist_same by omega.
      assert (j=m \/ j=m-1) by omega.
      forward_call (gv, Int.repr m, Int.repr j, before, @nil val, bl ++ after).
      rewrite !Int.signed_repr by rep_omega.
      rewrite if_false by omega. split; auto.
      Intros vret.
      Exists (sublist 0 (j + 1 - m) bl).
      entailer!. clear H. 
      assert (Zlength bl > 0) by omega.
      clear - H H15. destruct H15; subst j.
      rewrite sublist_one by rep_omega.
      constructor. replace (m-1+1-m) with 0 by omega.
      autorewrite with sublist. constructor.
      apply Permutation_nil in H16. subst vret. simpl.
      rewrite !app_ass. rewrite <- (app_ass (sublist _ _ _)).
      rewrite <- sublist_split by omega.
      rewrite sublist_same by omega. auto.
  +
   Intros cl.
   assert (Zlength (sublist 0 (j+1-m) bl) = Zlength cl).
     rewrite !Zlength_correct. f_equal. apply Permutation_length; auto.
   destruct (zlt i n).
   *
     subst MORE_COMMANDS; unfold abbreviate.
     assert (j=i-2 \/ j=i-1) by omega. destruct H18.
     --
     subst j. autorewrite with sublist in *.
     replace (i-2+1) with (i-1) in * by omega.
     specialize (H13 (eq_refl _)).
     clear H5 H7 HRE H2. destruct H12 as [H12 |[? ?]]; [ | omega].
     rewrite (sublist_split (i-1-m) (i-m)) by  rep_omega.
     rewrite (sublist_one (i-1-m) (i-m)) by rep_omega.
     rewrite  (app_ass [_]).
     rewrite <-  (app_ass (_ ++ _)).
     rewrite (app_ass before).
     forward_call (gv,Int.repr i, Int.repr n,
                         before++(cl++[Znth(i-1-m) bl]),
                         sublist (i-m)(n+1-m) bl, after).
     rewrite !Int.signed_repr by rep_omega.
     rewrite if_true by auto.
     split. split3; auto.
     autorewrite with sublist.
     rewrite <- H17. omega.
     autorewrite with sublist. omega.
     apply Forall_sublist; auto.
     Intros dl. Exists (cl ++ [Znth (i - 1 - m) bl] ++ dl).
     rewrite !app_ass.
     entailer!.
     clear P_a HP_a.
     split.
     eapply perm_trans; try apply H11.
     rewrite <- (sublist_same 0 (n+1-m) bl) by omega.
     rewrite (sublist_split 0 (i-1-m) (n+1-m)) by omega.
     rewrite (sublist_split (i-1-m) (i-m)(n+1-m)) by omega.
     apply Permutation_app; auto.
     rewrite (sublist_one (i-1-m) (i-m)) by omega.
     autorewrite with sublist.
     apply Permutation_app_head; auto.
apply (sorted_app pivot); auto.
apply (sorted_app pivot); auto.
constructor.
constructor.
apply f_cmp_ge_gt_eq; auto.
constructor.
eapply Forall_perm; try apply H2; auto.
rewrite (sublist_split _ (i-m)) in H9 by omega.
rewrite Forall_app in H9.
destruct H9; auto.
eapply Forall_perm; try apply H15; auto.
rewrite (sublist_split _ (i-1-m)) in H8 by omega.
rewrite Forall_app in H8.
destruct H8; auto.
constructor.
apply f_cmp_le_lt_eq; auto.
eapply Forall_perm; try apply H2; auto.
rewrite (sublist_split _ (i-m)) in H9 by omega.
rewrite Forall_app in H9.
destruct H9; auto.
    --
     subst j. autorewrite with sublist in *.
     clear H13 H5 H7 HRE H2. destruct H12 as [H12 |[? ?]]; [ | omega].
     forward_call (gv,Int.repr i, Int.repr n,
                         before++cl,
                         sublist (i-m)(n+1-m) bl, after).
     rewrite !Int.signed_repr by rep_omega.
     rewrite if_true by auto.
     split. split3; auto.
     autorewrite with sublist. omega.
     autorewrite with sublist. omega.
     apply Forall_sublist; auto.
     Intros dl. Exists (cl ++ dl).
     rewrite !app_ass.
     entailer!.
     clear  P_a HP_a.
     split.
     eapply perm_trans; try apply H11.
     rewrite <- (sublist_same 0 (n+1-m) bl) by omega.
     rewrite (sublist_split 0 (i-m) (n+1-m)) by omega.
     apply Permutation_app; auto.
     apply (sorted_app pivot); auto.
     eapply Forall_perm; try apply H15. auto.
     eapply Forall_perm; try apply H2. auto.     
   * subst MORE_COMMANDS; unfold abbreviate.
      rewrite !app_ass.
      rewrite <- (app_ass cl).
      forward_call (gv, Int.repr i, Int.repr n, before, @nil val,
                         (cl ++ sublist (j + 1 - m) (n + 1 - m) bl) ++ after).
      rewrite !Int.signed_repr by rep_omega.
      rewrite if_false by omega. split; auto.
      Intros vret.
      apply Permutation_nil in H18. subst vret.
      Exists (cl ++ sublist (j + 1 - m) (n + 1 - m) bl).
      entailer!.
     clear H.
     split.
     eapply perm_trans; try apply H11.
     rewrite <- (sublist_same 0 (n+1-m) bl) by omega.
     rewrite (sublist_split 0 (j+1-m) (n+1-m)) by omega.
     apply Permutation_app; auto.
     autorewrite with sublist.
     apply Permutation_refl.
     apply (sorted_app pivot); auto.
     clear P_a HP_a H18 H19. clear dependent cl. 
     assert (j=i-2 \/ j = i-1) by omega.
     assert (i=n \/ i=n+1) by omega.
     destruct H,H15; subst.
     2: rewrite sublist_one by omega; constructor.
     2: rewrite sublist_one by omega; constructor.
     2: rewrite Z.sub_add; autorewrite with sublist; constructor.
     specialize (H13 (eq_refl _)).
     replace (n-2+1) with (n-1) by omega.
     rewrite (sublist_split _ (n-m)) by omega.
     rewrite !sublist_one by omega.
     repeat constructor.
     apply f_cmp_le_trans with pivot.
     change Cle with (swap_comparison Cge).
     apply f_cmp_swap.
     apply f_cmp_ge_gt_eq; auto.
     eapply Forall_forall. apply H9.
     replace (Znth (n-m) bl) with (Znth 1 (sublist (n - 2 + 1 - m) (n + 1 - m) bl))
         by (autorewrite with sublist; f_equal; omega).
     apply Znth_In. 
     autorewrite with sublist. omega.
     eapply Forall_perm; try apply H15.
     rewrite (sublist_split _ (j+1-m)) in H8 by omega.
     rewrite Forall_app in H8. destruct H8; auto.
Qed.











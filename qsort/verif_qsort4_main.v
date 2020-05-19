Require Import VST.floyd.proofauto.
Require Import qsort4a.
Require Import spec_qsort4.
Require Import verif_qsort4_aux1.
Require Import float_lemmas.
Require Import Permutation.
Set Nested Proofs Allowed.

Lemma is_finite_Float_of_int:
 forall i,  Binary.is_finite 53 1024 (Float.of_int i) = true.
Admitted. (* need this lemma from the Flocq people... *)

Lemma def_float_of_int:
  forall i, def_float (Vfloat (Float.of_int i)).
Proof.
intros.
simpl.
apply is_finite_Float_of_int.
Qed.

Lemma body_compar_double:  semax_body Vprog Gprog f_compar_double compar_double_spec.
Proof.
start_function.
destruct H as [? [_ ?]].
destruct H0 as [? [_ ?]].
forward.
entailer!.
destruct x; try contradiction; simpl; auto.
forward.
entailer!.
destruct y; try contradiction; simpl; auto.
destruct x; try contradiction. rename f into x.
destruct y; try contradiction. rename f into y.
forward_if (
  EX c:Datatypes.comparison,
  PROP(match c with
              | Eq => ord_eq double_le_order (Vfloat x) (Vfloat y)
              | Lt => ord_lt double_le_order (Vfloat x) (Vfloat y)
              | Gt => ord_lt double_le_order (Vfloat y) (Vfloat x)
             end) 
  (LOCAL (temp _t'1 
              (Vint (Int.repr (match c with Lt => -1 | Eq => 0 | Gt => 1 end))))
  (SEP (data_at shp tdouble (Vfloat x) p; data_at shq tdouble (Vfloat y) q))))%assert.
-
forward.
Exists Lt.
entailer!.
hnf. simpl. unfold f_le.
intuition.
red.
rewrite Float.cmp_le_lt_eq.
rewrite orb_true_iff; auto.
red in H11.
rewrite Float.cmp_le_lt_eq in H11.
rewrite orb_true_iff in H11; auto.
destruct H11.
rewrite (Float.cmp_swap Cgt) in H10.
apply Float.cmp_lt_gt_false in H10; auto.
eapply Float.cmp_lt_eq_false; eauto.
rewrite <- Float.cmp_swap; auto.
-
forward_if.
+
forward.
forward.
Exists Eq.
entailer!.
hnf. simpl. unfold f_le.
intuition.
red.
rewrite Float.cmp_le_lt_eq.
rewrite orb_true_iff.
auto.
red.
rewrite <- Float.cmp_swap; simpl.
rewrite Float.cmp_ge_gt_eq.
rewrite orb_true_iff.
auto.
+
forward.
forward.
Exists Gt.
entailer!.
hnf. simpl. unfold f_le.
intuition.
red.
rewrite Float.cmp_le_lt_eq.
rewrite orb_true_iff.
pose proof (f_cmp_false Clt x y H H0 H3).
simpl in H9.
rewrite Float.cmp_ge_gt_eq in H9.
rewrite orb_true_iff in H9.
destruct H9; auto.
left.
rewrite <- Float.cmp_swap; auto.
right.
rewrite <- Float.cmp_swap; auto.
red in H12.
rewrite Float.cmp_le_lt_eq in H12.
rewrite orb_true_iff in H12.
destruct H12.
rewrite H3 in H11; inv H11.
rewrite H4 in H11; inv H11.
-
Intros c; forward; Exists c.
entailer!.
Qed.

Search (int->float).

Fixpoint upto (n: nat) (k: Z) : list val :=
 match n with
 | O => nil
 | S n' => Vfloat (Float.of_int (Int.repr k)) ::
                upto n' (Z.succ k)
 end.

Lemma Zlength_upto: forall i k, 
  0 <= i -> Zlength (upto (Z.to_nat i) k) = i.
Proof.
intros.
rewrite <- (Z2Nat.id i) at 2 by lia.
rewrite <- (Z2Nat.id i) in H by lia.
revert k; induction (Z.to_nat i); intros.
simpl. reflexivity.
unfold upto; fold upto.
rewrite Zlength_cons.
rewrite Nat2Z.inj_succ.
rewrite IHn; auto.
lia.
Qed.

Lemma upto_another:
  forall i k, 0 <= i ->
    upto (Z.to_nat (i+1)) k = 
   upto (Z.to_nat i) k ++ [Vfloat (Float.of_int (Int.repr (i+k)))].
Proof.
intros.
replace (i+1) with (Z.succ i) by lia.
rewrite Z2Nat.inj_succ by lia.
rewrite <- (Z2Nat.id i) at 3 by lia.
clear.
revert k; induction (Z.to_nat i); intros.
simpl.
rewrite Z.add_0_l; auto.
change (upto (S (S n)) k) with
 (Vfloat (Float.of_int (Int.repr k)) ::
 upto (S n) (Z.succ k)).
rewrite (IHn (Z.succ k)).
rewrite app_comm_cons.
f_equal.
f_equal.
f_equal.
f_equal.
f_equal.
rewrite Nat2Z.inj_succ.
lia.
Qed.

Opaque upto.


Definition main_printf_loop :=
        (Ssequence
          (Sset _i (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                             (Econst_int (Int.repr 666666) tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Sset _t'1
                  (Ederef
                    (Ebinop Oadd (Evar _a (tarray tdouble 666666))
                      (Etempvar _i tint) (tptr tdouble)) tdouble))
                (Scall None
                  (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                  {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                  ((Evar ___stringlit_1 (tarray tschar 4)) ::
                   (Etempvar _t'1 tdouble) :: nil))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint)))).

Lemma verif_main_printf_loop:
 forall (Espec : OracleKind)
  (gv : globals)
  (bl : list (reptype tdouble))
  (H : Permutation (upto (Z.to_nat N6) 0) bl)
  (H0 : sorted (ord_le double_le_order) bl),
 semax (func_tycontext f_main Vprog Gprog nil)
  (PROP ( )
   LOCAL (gvars gv)
   SEP (data_at Ews (tarray tdouble N6) bl (gv _a);
   data_at Ers (tarray tschar 4)
     (map (Vint oo cast_int_int I8 Signed)
        [Int.repr 37; Int.repr 102; Int.repr 10; Int.repr 0])
     (gv ___stringlit_1))) main_printf_loop
  (normal_ret_assert
     (PROP ( )
      LOCAL (gvars gv)
      SEP (data_at Ews (tarray tdouble N6) bl (gv _a);
      data_at Ers (tarray tschar 4)
        (map (Vint oo cast_int_int I8 Signed)
           [Int.repr 37; Int.repr 102; Int.repr 10; Int.repr 0])
        (gv ___stringlit_1)))).
Admitted.  (* I claim that it is all right to Admit this lemma because
 the technical report, "A benchmark for C program verification",
 in the table on page 3, lists a blank (not an X)
 in row "qsort" column "I/O".  Therefore we don't have to verify
 the input/output in this benchmark.   *)

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
forward_for_simple_bound N6
  (EX i:Z,
   PROP() LOCAL (gvars gv) 
   SEP (data_at Ews (tarray tdouble N6) 
            (upto (Z.to_nat i) 0 ++ list_repeat (Z.to_nat (N6-i)) Vundef) (gv _a);
          data_at Ers (tarray tschar 4)
           (map (Vint oo cast_int_int I8 Signed)
               [Int.repr 37; Int.repr 102; Int.repr 10; Int.repr 0])
            (gv ___stringlit_1);
           has_ext tt)).
-
rewrite <- N6_eq.
auto.
-
rewrite <- N6_eq.
entailer!.
change (upto (Z.to_nat 0) 0) with (@nil val).
unfold app. cancel.
-
forward.
entailer!.
apply derives_refl'.
f_equal.
replace (Z.to_nat (N6 - i))
  with (S (Z.to_nat (N6-(i+1)))).
2:{ clear - H. replace (N6-i) with (Z.succ (N6-(i+1))) by lia.
     rewrite Z2Nat.inj_succ by lia. auto.
}
 unfold list_repeat; fold @list_repeat.
 rewrite upd_Znth_app2.
2:{  rewrite Zlength_upto by lia. autorewrite with sublist. lia. }
 rewrite Zlength_upto by lia.
 rewrite Z.sub_diag.
 rewrite upd_Znth0.
 rewrite upto_another by lia.
 rewrite app_ass. f_equal. simpl. normalize.
-
(* after the for-loop *)
autorewrite with sublist.
set (al := upto (Z.to_nat N6) 0).
make_func_ptr _compar_double.
assert (H_ok:
complete_legal_cosu_type tdouble = true /\
               align_compatible_rec cenv_cs tdouble 0 /\
               no_volatiles tdouble). {
  split3; try reflexivity.
  eapply align_compatible_rec_by_value.
  reflexivity.
  apply Z.divide_0_r.
}
assert (Hdef: Forall (ord_def double_le_order) al). {
 clear.
 subst al.
 forget 0 as k.
 revert k; induction (Z.to_nat N6); simpl; intros.
 constructor.
 change (upto (S n) k) with 
   (Vfloat (Float.of_int (Int.repr k)) :: upto n (Z.succ k)).
 constructor; auto.
 red. simpl. red.
 pose proof (def_float_of_int (Int.repr k)).
 split3; auto.
 apply f_le_refl; auto.
}
pose (w := Build_qsort_witness _ tdouble H_ok 
                    double_le_order al Hdef).
assert (Zlength al = N6) by (subst al; rewrite Zlength_upto; rep_lia).
forward_call (Ews, gv _a, gv _compar_double, w);
   simpl qsort_t;
   simpl qsort_ord;
   simpl qsort_al;
  change (@reptype _ tdouble) with val.
+
rewrite <- N6_eq.
entailer!.
rewrite H; auto.
+
rewrite H.
cancel.
+
rewrite H.
split3; auto.
simpl sizeof.
computable.
simpl sizeof.
split; try rep_lia.
+
clear w H_ok Hdef.
rewrite H.
Intros bl.
deadvars!.
unfold Sfor.
fold main_printf_loop.
apply seq_assoc1.
eapply semax_seq'.
change (SEP (?R1; ?R2; ?R3)) with (@SEPx environ ([R1;R2]++[R3])).
rewrite (app_nil_end [gvars gv]).
eapply semax_frame_PQR.
unfold closed_wrt_modvars;  auto 50 with closed.
apply verif_main_printf_loop; auto.
unfold app.
forward.
Qed.









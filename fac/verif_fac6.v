Require Import VST.floyd.proofauto.
Require Import fac6.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Require Import VST.floyd.library.
Require Import fac_facts.

Definition M: Z := 1000000000.
Definition D: Z := 9.

Lemma M_eq: M = 1000000000.
Proof. reflexivity. Qed.
Hint Rewrite M_eq : rep_omega.

Lemma relate_M_D: Z.pow 10 D = M.
Proof. reflexivity. Qed.

Fixpoint digits_eval (al: list Z) (i: Z) : Z :=
  match al with
  | nil => 0
  | a::al' => a*i + digits_eval al' (M*i)
  end.

Definition bignum_rep (sh: share) (L L': Z) (n: Z) (p: val) : mpred :=
  EX al: list Z,
   !! (L <= L' /\ 
       Forall (fun x => 0 <= x < M) al /\
       Zlength al = L /\
       digits_eval al 1 = n) &&
   data_at sh (tarray tuint L') (map Vint (map Int.repr al) ++ list_repeat (Z.to_nat (L'-L)) Vundef) p.

Lemma bignum_rep_local_facts:
  forall sh L L' n p,
   bignum_rep sh L L' n p |--
   !! (is_pointer_or_null p /\ 0 <= L <= L' /\ 0 <= n < Z.pow M L).
Proof.
intros.
unfold bignum_rep.
Intros al.
subst n L.
entailer!.
clear - H0.
autorewrite with sublist in *.
assert
  (forall i, 0 < i -> 
    (i | digits_eval al i) /\ 
    0 <= digits_eval al i < i*(M^Zlength al)).
2: specialize (H 1); rewrite Z.mul_1_l in H; apply H; omega.
induction al; intros;
simpl.
split.
apply Z.divide_0_r.
omega.
inv H0.
specialize (IHal H4 (M*i)%Z).
spec IHal.
apply Z.mul_pos_pos; omega.
assert (0 <= a*i < M*i). {
  split.
  apply Z.mul_nonneg_nonneg; omega.
  apply Z.mul_lt_mono_pos_r; omega.
}
rewrite Zlength_cons.
rewrite Z.pow_succ_r by rep_omega.
rewrite Z.mul_assoc.
rewrite (Z.mul_comm i M).
destruct IHal.
split.
apply Z.divide_add_r.
apply Z.divide_mul_r.
apply Z.divide_refl.
destruct H1 as [x ?].
exists (x*M)%Z.
rewrite H1.
rewrite Z.mul_assoc.
auto.
split. omega.
forget (digits_eval al (M*i)) as b.
forget (M * i)%Z as m.
assert (0 < M ^ Zlength al).
apply Z.pow_pos_nonneg; rep_omega.
forget (M ^ Zlength al) as c.
forget (a * i)%Z as d.
clear - H1 H2 H0 H5.
destruct H1 as [e ?].
subst b.
destruct H2.
rewrite (Z.mul_comm m c) in *.
apply Zmult_lt_reg_r in H1; try omega.
assert (e + 1 <= c) by omega.
apply Zmult_le_0_reg_r in H; try omega.
assert ((e + 1) * m <= c * m).
apply Z.mul_le_mono_nonneg; try omega.
rewrite Z.mul_add_distr_r, Z.mul_1_l in H3.
omega.
Qed.

Hint Resolve bignum_rep_local_facts : saturate_local.

Lemma bignum_rep_valid_pointer:
  forall sh L L' n p,
   sepalg.nonidentity sh ->
   L' > 0 ->
   bignum_rep sh L L' n p |-- valid_pointer p.
Proof.
 unfold bignum_rep.
 intros; normalize.
 apply data_at_valid_ptr; auto.
 simpl. rewrite Z.max_r by omega.
 omega.
Qed.

Hint Resolve bignum_rep_valid_pointer : valid_pointer.

Definition calc_fac_spec :=
 DECLARE _calc_fac
  WITH sh: share, a: val, L': Z, n: Z
  PRE  [ _a OF (tptr tuint), _L OF tint, _n OF tulong ] 
     PROP(writable_share sh; 0 < L' <= Int.max_signed;
              0 <= n < M;
              fac n < M^L')
     LOCAL(temp _a a; temp _L (Vint (Int.repr L')); temp _n (Vlong (Int64.repr n)))
     SEP (bignum_rep sh 0 L' 0 a)
  POST [ tint ]  
    EX L:Z,
     PROP(0 <= L <= L' /\ fac n < M ^ L) 
     LOCAL (temp ret_temp (Vint (Int.repr L)))
     SEP(bignum_rep sh L L' (fac n) a).

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog nil gv
  POST [ tint ]  
     PROP() 
     LOCAL (temp ret_temp (Vint (Int.repr 0)))
     SEP(TT).

Definition Gprog := [calc_fac_spec].

Lemma digits_eval_nonneg:
  forall al c, 0 < c -> Forall (fun x : Z => 0 <= x < M) al -> 0 <= digits_eval al c.
Proof.
induction al; simpl; intros. omega.
inv H0.
specialize (IHal (M*c)%Z).
spec IHal.
apply Z.mul_pos_pos; omega.
specialize (IHal H4).
assert (0 <= a*c).
apply Z.mul_nonneg_nonneg; omega.
omega.
Qed.

Lemma divu64_repr: forall i j,
   0 <= i <= Int64.max_unsigned ->
   0 <= j <= Int64.max_unsigned ->
   Int64.divu (Int64.repr i) (Int64.repr j) = Int64.repr (i / j).
Proof.
intros.
unfold Int64.divu.
normalize.
Qed.
Hint Rewrite divu64_repr using rep_omega : norm.

Lemma typed_false_tulong_e:
  forall v, typed_false tulong v -> v = Vlong Int64.zero.
Proof.
clear; intros.
destruct v; inv H.
pose proof (Int64.eq_spec i Int64.zero).
destruct (Int64.eq i Int64.zero); inv H1; auto.
Qed.

Lemma repr64_inj_signed:
  forall i j,
    Int64.min_signed <= i <= Int64.max_signed ->
    Int64.min_signed <= j <= Int64.max_signed ->
    Int64.repr i = Int64.repr j -> i=j.
Proof.
intros.
rewrite <- (Int64.signed_repr i) by rep_omega.
rewrite <- (Int64.signed_repr j) by rep_omega.
congruence.
Qed.

Lemma repr64_inj_unsigned:
  forall i j,
    0 <= i <= Int64.max_unsigned ->
    0 <= j <= Int64.max_unsigned ->
    Int64.repr i = Int64.repr j -> i=j.
Proof.
intros.
rewrite <- (Int64.unsigned_repr i) by rep_omega.
rewrite <- (Int64.unsigned_repr j) by rep_omega.
congruence.
Qed.

Lemma digits_eval_mult:
 forall al b c, (digits_eval al (b*c) = b * digits_eval al c)%Z.
Proof.
induction al; intros.
simpl. omega.
simpl.
rewrite !IHal.
rewrite Z.mul_add_distr_l.
f_equal.
rewrite Z.mul_comm. rewrite <- Z.mul_assoc. rewrite (Z.mul_comm c); auto.
rewrite !Z.mul_assoc.
rewrite (Z.mul_comm b). auto.
Qed.

Lemma digits_eval_bound:
 forall al, 
   Forall (fun x => 0 <= x < M) al ->
   digits_eval al 1 < M ^ Zlength al.
Proof.
intros al Hal.
induction Hal as [ | a al ].
simpl. omega.
unfold digits_eval; fold digits_eval.
rewrite digits_eval_mult.
rewrite Zlength_cons.
rewrite Z.pow_succ_r by rep_omega.
rewrite Z.mul_1_r.
pose proof (digits_eval_nonneg al 1).
spec H0; [omega|].
specialize (H0 Hal).
clear Hal.
forget (digits_eval al 1) as e.
forget (M ^ Zlength al) as N.
assert (0 <= e < N) by auto.
clear - H H1.
replace N with (1 + (N-1)) by omega.
rewrite Z.mul_add_distr_l.
apply Z.add_lt_le_mono.
omega.
apply Z.mul_le_mono_nonneg_l.
omega.
omega.
Qed.

Lemma digits_eval_app:
   forall al bl b,
   digits_eval (al++bl) b = digits_eval al b + digits_eval bl ((M ^ Zlength al)*b).
Proof.
 induction al; simpl; intros.
  rewrite Z.mul_1_l, Z.add_0_l; auto.
  rewrite IHal.
  rewrite Zlength_cons. rewrite Z.pow_succ_r by rep_omega.
  rewrite Z.add_assoc. f_equal. f_equal.
  rewrite Z.mul_comm. rewrite <- !Z.mul_assoc.
  f_equal. apply Z.mul_comm. 
Qed.

Lemma body_calc_fac: semax_body Vprog Gprog f_calc_fac calc_fac_spec.
Proof.
start_function.
rename H1 into HL'.
unfold bignum_rep.
Intros al.
forward.
forward_for_simple_bound L'
   (EX i:Z,
      PROP ()
      LOCAL (temp _a a; temp _L (Vint (Int.repr L')); temp _n (Vlong (Int64.repr n)))
      SEP (data_at sh (tarray tuint L') 
               (map Vint (map Int.repr (1 :: list_repeat (Z.to_nat (i-1)) 0)) ++ 
                list_repeat (Z.to_nat (L'-i)) Vundef) a)).
  {entailer!.
   destruct al.
   2: elimtype False; clear - H3; rewrite Zlength_cons in H3; rep_omega.
   simpl.
   replace L' with (1 + (L'-1)) at 2 by omega.
   rewrite <- list_repeat_app' by omega.
   simpl list_repeat.
   autorewrite with sublist.
   rewrite upd_Znth0.
   autorewrite with sublist.
   simpl.  cancel.
  }
  forward. {
   entailer!.
   replace (L'-i) with (1 + (L'-i-1)) by omega.
   rewrite <- list_repeat_app' by omega.
   autorewrite with sublist.
   simpl list_repeat.
   replace (i - Z.succ (i-1)) with 0 by omega.
   rewrite upd_Znth0.
   autorewrite with sublist.
   rewrite <- app_comm_cons.
   rewrite <- app_ass.
   change ([Vint (Int.repr 0)]) with (list_repeat (Z.to_nat 1) (Vint (Int.repr 0))).
   rewrite list_repeat_app' by omega.
   replace (L' - (i+1)) with (L' - i - 1) by omega.
   replace (i - 1 + 1) with i by omega.
   cancel.
   }
  forward.
  autorewrite with sublist.
  rename n into n0.
  clear al H3 H4 H2.
  forward_while 
    (EX al:list Z, EX n:Z, 
   PROP (0 <= n <= n0; (digits_eval al 1 * fac n = fac n0)%Z;
            Forall (fun x => 0 <= x < M) al;
            Zlength al <= L')
   LOCAL (temp _l (Vint (Int.repr (Zlength al)));
   temp _a a; temp _L (Vint (Int.repr L')); temp _n (Vlong (Int64.repr n)))
   SEP (data_at sh (tarray tuint L')
          (map Vint (map Int.repr (al ++ list_repeat (Z.to_nat (L'-Zlength al)) 0))) a)).
-
  Exists [1] n0.
  entailer!. split. repeat constructor; computable. change (Zlength [1]) with 1. omega.
-
   entailer!.
-
  rename H4 into Hal. rename H5 into Hal'.
  forward.
  forward.
  assert (0 < n <= n0). { clear - H2 HRE. destruct (zeq n 0); try omega. subst. inv HRE. }
  clear HRE H2 H1.
  set (alx := al ++  list_repeat (Z.to_nat (L' - Zlength al)) 0).
  assert (digits_eval al 1 = digits_eval alx 1). {
     subst alx.
     clear.
     forget 1 as c.
     forget (Z.to_nat (L' - Zlength al)) as n.
     revert c; induction al; simpl; intros.
     revert c; induction n; simpl; intros; auto.  rewrite <- IHn. omega.
     f_equal. auto.
  }
  rewrite H1 in H3.
  assert_PROP (Zlength alx = L') 
    by (entailer!;   autorewrite with sublist in H5; auto).
  assert (Forall (eq 0) (sublist (Zlength al) (Zlength alx) alx)). {
   subst alx.
   clear.
   induction al. simpl. autorewrite with sublist. apply Forall_list_repeat. auto.
   simpl.
   rewrite !Zlength_cons.
   unfold Z.succ. rewrite <- !(Z.add_comm 1).
   rewrite app_comm_cons. change (a::al) with ([a]++al).
   rewrite app_ass.
   autorewrite with sublist.
   apply Forall_list_repeat. auto.
  }
  assert (0 <= Zlength al <= L'). split. rep_omega.
  clear- H2.
  subst alx.
  destruct (zlt L' (Zlength al)); [ | omega].
  rewrite Z_to_nat_neg in H2 by omega. autorewrite with sublist in H2. omega.
  forget (Zlength al) as L.
  assert (Halx: Forall (fun x : Z => 0 <= x < M) alx). {
    subst alx. apply Forall_app. split. auto. apply Forall_list_repeat. rep_omega.
 }
 clearbody alx; clear al H1 Hal. rename alx into al. rename Halx into Hal. subst L'.
  forward_loop (EX al': list Z, EX c:Z, EX L:Z,
   PROP (((digits_eval al' 1 + c * (M ^ Zlength al') +
             n * digits_eval (sublist (Zlength al') (Zlength al) al) (M ^ Zlength al')) =
             n * digits_eval al 1)%Z;
            (digits_eval al 1 * fac n)%Z = fac n0;
            Zlength al' <= Zlength al;
            0 <= L <= Zlength al;
            Forall (eq 0) (sublist L (Zlength al) al);
            0 <= c < M;
            Forall (fun x : Z => 0 <= x < M) al')
   LOCAL (temp _i (Vint (Int.repr (Zlength al')));
   temp _c (Vlong (Int64.repr c));
   temp _l (Vint (Int.repr L)); temp _a a;
   temp _L (Vint (Int.repr (Zlength al))); temp _n (Vlong (Int64.repr n)))
   SEP (data_at sh (tarray tuint (Zlength al))
          (map Vint (
             (map Int.repr (al' ++ sublist (Zlength al') (Zlength al) al)))) a))
  break: (EX al': list Z, EX c:Z, EX L:Z,
   PROP (((digits_eval al' 1 + c * (M ^ Zlength al') +
             n * digits_eval (sublist (Zlength al') (Zlength al) al) (M ^ Zlength al')) =
             n * digits_eval al 1)%Z;
            (digits_eval al 1 * fac n)%Z = fac n0;
            Zlength al' <= Zlength al;
            0 <= L <= Zlength al;
            Zlength al' >= L;
            Forall (fun x : Z => 0 <= x < M) al';
            c = 0;
            Forall (eq 0) (sublist L (Zlength al) al))
   LOCAL (temp _i (Vint (Int.repr (Zlength al')));
   temp _c (Vlong (Int64.repr c));
   temp _l (Vint (Int.repr L)); temp _a a;
   temp _L (Vint (Int.repr (Zlength al))); temp _n (Vlong (Int64.repr n)))
   SEP (data_at sh (tarray tuint (Zlength al))
          (map Vint (
             (map Int.repr (al' ++ sublist (Zlength al') (Zlength al) al)))) a)).
 +
   Exists (@nil Z) 0 L.
   entailer!.
   split.
   autorewrite with sublist. rewrite Z.pow_0_r. auto.
   list_solve.
   autorewrite with sublist. auto.
 +
   clear L H6 H5 Hal'.
   Intros al' c L. rename H8 into Hal'.
   forward_if (temp _t'1 (Vint (Int.repr 
                               (if zlt (Zlength al') L then 1
                                    else if (zeq c 0) then 0 else 1)))).
   forward. entailer!. rewrite if_true; auto.
   forward. entailer!. rewrite if_false by auto. if_tac. subst. reflexivity.
   rewrite Int64.eq_false; auto.
   clear - H12 H7. contradict H12.
   rewrite <- (Int64.unsigned_repr c) by rep_omega. rewrite H12; reflexivity.
   forward_if (Zlength al' < L \/ 0<c).
    forward. entailer!. if_tac in H8'; auto. if_tac in H8; subst; auto. contradiction. right; omega.
    forward.
    Exists al' c L. entailer!.
    if_tac in H8. inv H8. if_tac in H8; [ | inv H8]. split; auto.
    drop_LOCALs [_t'1].
    Intros.
    assert (Zlength al' < Zlength al). {
       destruct H8. omega.
       destruct (zeq (Zlength al') (Zlength al)); [ | omega].
       rewrite e in H1. autorewrite with sublist in H1.
       simpl in H1. 
       elimtype False.
       rewrite Z.mul_0_r, Z.add_0_r in H1.
       rewrite <- H3 in HL'.
       assert (0 < c < M) by omega.
       clear - HL' H4 H1 H5 H6 e H9 Hal'.
       rewrite fac_equation in HL'. rewrite if_true in HL' by omega.
       rewrite Z.mul_assoc in HL'. rewrite (Z.mul_comm n) in H1; rewrite <- H1 in HL'.
       clear - HL' H4 Hal' H9.
 pose proof (digits_eval_nonneg al' 1).
 spec H; [omega|].
  specialize (H Hal').
 pose proof (fac_mono 0 (n-1)). spec H0;[omega|].
 change (fac 0) with 1 in H0.
 forget (digits_eval al' 1) as e. forget (fac (n-1)) as f.
 assert (0 < M ^ Zlength al).
 apply Z.pow_pos_nonneg; rep_omega.
 forget (M ^ Zlength al) as d.
 destruct H9 as [? _].
 clear - HL' H2 H H0 H1.
 rewrite Z.mul_add_distr_r in HL'.
 assert (0 <= e*f).
 apply Z.mul_nonneg_nonneg; omega.
 assert (c * d * f < d); try omega.
 clear dependent e.
 rewrite Z.mul_comm in H4.
 rewrite Z.mul_assoc in H4.
 assert (1 <= f*c). change 1 with (1*1)%Z.
 apply Z.mul_le_mono_nonneg; omega.
 revert H4.
 assert (f*c*d >= 1*d); [|rewrite Z.mul_1_l in *; auto].
 apply Zmult_ge_compat_r; omega.
 }
 forward.
 entailer!.
 forward.
 drop_LOCALs [_t'2].
 forward.
 forward.
 entailer!.
 forward.
 normalize.
 rewrite Int.unsigned_repr.
2:{ autorewrite with sublist. 
    clear - H6 Hal H9.
    pattern (Znth (Zlength al') al).
    apply Forall_Znth. rep_omega.
    eapply Forall_impl; try eassumption.
    intros. simpl in H. rep_omega.
}
 rewrite app_Znth2 by omega. rewrite Z.sub_diag.
 autorewrite with sublist.
 rewrite !map_app.
 rewrite upd_Znth_app2 by (autorewrite with sublist; omega).
 assert (0 <= Znth (Zlength al') al < M). {
   pattern ( Znth (Zlength al') al). apply Forall_Znth. rep_omega. auto.
 }
 assert (0 <= n * Znth (Zlength al') al + c < M*M). {
  clear - H10 H7 H4 H0.
  assert (0 <= n * Znth (Zlength al') al).
  apply Z.mul_nonneg_nonneg; omega.
  split. omega.
  change (M*M)%Z with ((M-1)*M + M)%Z.
  assert (n * Znth (Zlength al') al <= (M-1)*M); [ | omega].
  apply Z.mul_le_mono_nonneg; rep_omega.
 }
 autorewrite with sublist norm.
 rewrite <- Zmod_eq by omega.
 rewrite Int64.unsigned_repr.
2:{ pose proof (Z.mod_pos_bound(n * Znth (Zlength al') al + c) 1000000000).
    spec H12; [computable|]. rep_omega.
 }
 rewrite !upd_Znth_map.
 Exists (al' ++ [(n * Znth (Zlength al') al + c) mod 1000000000]).
 Exists ((n * Znth (Zlength al') al + c) / 1000000000).
 Exists L.
 entailer!.
 split3; [ | | split3]; autorewrite with sublist; auto; try omega.
 *
  change (Z.succ 0) with 1.
  clear - H11 H10 H9 H8 Hal' H7 H6 H5 H2 H1 Hal H4 H3 H0 H.
  fold M.
  rewrite <- H1; clear H1.
  rewrite (sublist_split (Zlength al') (Zlength al' + 1) (Zlength al)) by rep_omega.
  rewrite (sublist_len_1 (Zlength al')) by rep_omega.
  simpl.
  rewrite Z.mul_add_distr_l.
  rewrite !Z.add_assoc.
  rewrite <- Z.pow_succ_r by rep_omega. unfold Z.succ.
  f_equal.
  rewrite digits_eval_app.
  rewrite <- !Z.add_assoc. f_equal.
  simpl. rewrite Z.add_0_r. rewrite Z.mul_1_r.
  set (d := Znth (Zlength al') al).
  rewrite Zmod_eq by rep_omega.
  rewrite Z.mul_sub_distr_r.
  fold (Z.succ (Zlength al')).
  rewrite Z.pow_succ_r by rep_omega.
  rewrite Z.mul_assoc.
  rewrite Z.sub_add.
  rewrite Z.mul_add_distr_r.
  rewrite Z.mul_assoc. omega.
 *
  clear - H11.
  change 1000000000 with M.
  split. apply Z.div_pos; rep_omega.
  forget (n * Znth (Zlength al') al + c) as d.
  apply Z.div_lt_upper_bound; try rep_omega.
 *
  apply Forall_app; split; auto. constructor; [ | constructor].
  pose proof (Z.mod_pos_bound(n * Znth (Zlength al') al + c) 1000000000).
  spec H15; [computable|]. rep_omega.
 *
  rewrite <- !map_app. apply derives_refl'. f_equal. f_equal. f_equal.
  rewrite app_ass. f_equal.
  autorewrite with sublist.
  rewrite (sublist_split (Zlength al') (Zlength al' + 1) (Zlength al)) by rep_omega.
  autorewrite with sublist. f_equal.
  rewrite sublist_len_1 by rep_omega.   rewrite upd_Znth0.
   autorewrite with sublist. auto.
+
 Intros al' c L0.
 forward_if (temp _l (Vint (Int.repr (Z.max  (Zlength al') L0)))).
 forward.
 entailer!. rewrite Z.max_l by omega. auto.
 forward.
 entailer!. rewrite Z.max_r by omega. auto.
 forward.
 subst c.
 autorewrite with norm.
 rewrite Z.mul_0_l, Z.add_0_r in H1.
 Exists (al' ++ sublist (Zlength al') (Z.max (Zlength al') L0) al, n-1).
 simpl fst. simpl snd. autorewrite with sublist.
 entailer!.
 *
 rewrite (fac_equation n) in H3.
 rewrite if_true in H3 by omega.
 rewrite Z.mul_assoc in H3.
 rewrite <- (Z.mul_comm n) in H3.
 rewrite <- H3. clear H3.
 f_equal.
 rewrite <- H1. clear H1.
 rewrite (sublist_split L0 (Zlength al')) in H11 by rep_omega.
 apply Forall_app in H11. destruct H11 as [_ H11].
 clear - H11 H2.
 forget (sublist (Zlength al') (Zlength al) al) as dl.
 forget (M ^ Zlength al') as N.
 replace (digits_eval dl N) with 0. omega.
 clear - H11. revert N; induction H11; intros; simpl. auto.
 rewrite <- IHForall. subst. omega.
 *
 replace (list_repeat (Z.to_nat (Zlength al - Zlength al')) 0)
   with (sublist (Zlength al') (Zlength al) al); auto.
 clear - H8 H11 H7 H2.
 forget (Zlength al') as i.
 rewrite (sublist_split L0 i) in H11 by rep_omega.
 apply Forall_app in H11. destruct H11 as [_ ?].
 assert (0 <= i <= Zlength al) by omega.
 clear - H H0.
 assert (Zlength (sublist i (Zlength al) al) = Zlength al - i).
  autorewrite with sublist. auto.
 rewrite <- H1.
 clear - H.
 forget (sublist i (Zlength al) al) as bl.
 induction H; intros. simpl; auto. rewrite Zlength_cons.
 unfold Z.succ. rewrite Z.add_comm.
 rewrite <- list_repeat_app' by rep_omega.
 simpl. f_equal; auto.
-
 assert (n=0). {clear - H2 HRE H0.
apply typed_false_tulong_e in HRE.
assert (Int64.repr n = Int64.zero) by congruence.
apply repr64_inj_unsigned in H; rep_omega.
}
  subst n.
  change (fac 0) with 1 in H3. rewrite Z.mul_1_r in H3.
  clear HRE H1.
  forward.
  Exists (Zlength al).
  unfold bignum_rep. Exists al.
  autorewrite with sublist in H5.
  entailer!.
  rewrite <- H3.
 apply digits_eval_bound; auto.
 rewrite !map_app.
 autorewrite with sublist.
 rewrite !(split2_data_at_Tarray_app (Zlength al) L') by list_solve.
 cancel.
Qed.

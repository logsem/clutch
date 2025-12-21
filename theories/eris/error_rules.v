(** * Union bound rules  *)
From stdpp Require Import namespaces finite.
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext.
From clutch.prob_lang Require Import notation tactics metatheory.
From clutch.prob_lang Require Export lang.
From clutch.eris Require Export lifting proofmode ectx_lifting primitive_laws seq_amplification.
From clutch.eris Require Export total_lifting total_ectx_lifting total_primitive_laws.

(** TODO: this file needs to get properly updated to take into account that the error credits [↯ ε]
    now works for [ε : R] rather than [ε : nonnegreal]. Ideally, no `nonnegreal` should appear at
    the level of the lemma statements! *)

Section metatheory.

Local Open Scope R.

(** * rand(N) no error *)
Lemma pgl_rand_trivial N z σ1 :
  N = Z.to_nat z →
  pgl
    (prim_step (rand #z) σ1)
    (λ ρ2, ∃ (n : fin (S N)),
        ρ2 = (Val #n, σ1)) 0.
Proof.
  simpl in *.
  intros Hz.
  rewrite head_prim_step_eq /=.
  rewrite /dmap -Hz.
  rewrite -(Rplus_0_r 0).
  eapply (pgl_dbind _ _ _ _ _ 0);
    [done|done| |by apply pgl_trivial].
  intros n ?.
  apply pgl_dret.
  by exists n.
Qed.

(** * rand(N) error *)
Lemma pgl_rand_err N z σ1 (m : fin (S N)):
  N = Z.to_nat z →
  pgl
    (prim_step (rand #z) σ1)
    (λ ρ2, ∃ (n : fin (S N)),
        (n ≠ m)%fin /\ ρ2 = (Val #n, σ1)) (1/(N+1)).
Proof.
  simpl in *.
  intros Hz.
  rewrite head_prim_step_eq /=.
  rewrite /dmap -Hz.
  rewrite -(Rplus_0_r (1 / (N + 1))).
  eapply (pgl_dbind _ _ _ _ _ 0); last first.
  { by apply ub_unif_err. }
  - intros n ?.
    apply pgl_dret.
    exists n; split; [apply H | auto].
  - lra.
  - rewrite /Rdiv.
    apply Rle_mult_inv_pos; [lra |].
    apply (Rle_lt_trans _ N).
    + apply pos_INR.
    + rewrite <- (Rplus_0_r) at 1.
      apply Rplus_lt_compat_l.
      lra.
Qed.

(* Same lemma holds for m an arbitrary natural *)
Lemma pgl_rand_err_nat N z σ1 (m : nat):
  N = Z.to_nat z →
  pgl
    (prim_step (rand #z) σ1)
    (λ ρ2, ∃ (n : fin (S N)),
        (fin_to_nat n ≠ m)%fin /\ ρ2 = (Val #n, σ1)) (1/(N+1)).
Proof.
  simpl in *.
  intros Hz.
  rewrite head_prim_step_eq /=.
  rewrite /dmap -Hz.
  rewrite -(Rplus_0_r (1 / (N + 1))).
  eapply (pgl_dbind _ _ _ _ _ 0); last first.
  { by apply ub_unif_err_nat. }
  - intros n ?.
    apply pgl_dret.
    exists n; split; [apply H | auto].
  - lra.
  - rewrite /Rdiv.
    apply Rle_mult_inv_pos; [lra |].
    apply (Rle_lt_trans _ N).
    + apply pos_INR.
    + rewrite <- (Rplus_0_r) at 1.
      apply Rplus_lt_compat_l.
      lra.
Qed.

(* Generalization to lists *)
Lemma pgl_rand_err_list_nat N z σ1 (ms : list nat):
  N = Z.to_nat z →
  pgl
    (prim_step (rand #z) σ1)
    (λ ρ2, ∃ (n : fin (S N)),
        Forall (λ m, (fin_to_nat n ≠ m)%fin) ms /\ ρ2 = (Val #n, σ1)) ((length ms)/(N+1)).
Proof.
  simpl in *.
  intros Hz.
  rewrite head_prim_step_eq /=.
  rewrite /dmap -Hz.
  rewrite -(Rplus_0_r ((length ms) / (N + 1))).
  eapply (pgl_dbind _ _ _ _ _ 0); last first.
  { by apply ub_unif_err_list_nat. }
  - intros n ?.
    apply pgl_dret.
    exists n; split; [apply H | auto].
  - lra.
  - rewrite /Rdiv.
    apply Rle_mult_inv_pos; [apply pos_INR | ].
    apply (Rle_lt_trans _ N).
    + apply pos_INR.
    + rewrite <- (Rplus_0_r) at 1.
      apply Rplus_lt_compat_l.
      lra.
Qed.

Lemma pgl_rand_err_list_int N z σ1 (ms : list Z):
  N = Z.to_nat z →
  pgl
    (prim_step (rand #z) σ1)
    (λ ρ2, ∃ (n : fin (S N)),
        Forall (λ m, (Z.of_nat (fin_to_nat n) ≠ m)%fin) ms /\ ρ2 = (Val #n, σ1)) ((length ms)/(N+1)).
Proof.
  simpl in *.
  intros Hz.
  rewrite head_prim_step_eq /=.
  rewrite /dmap -Hz.
  rewrite -(Rplus_0_r ((length ms) / (N + 1))).
  eapply (pgl_dbind _ _ _ _ _ 0); last first.
  { by apply ub_unif_err_list_int. }
  - intros n ?.
    apply pgl_dret.
    exists n; split; [apply H | auto].
  - lra.
  - rewrite /Rdiv.
    apply Rle_mult_inv_pos; [apply pos_INR | ].
    apply (Rle_lt_trans _ N).
    + apply pos_INR.
    + rewrite <- (Rplus_0_r) at 1.
      apply Rplus_lt_compat_l.
      lra.
Qed.

End metatheory.

Section rules.
  Context `{!erisGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types v : val.
  Implicit Types l : loc.




(* General expectation preserving rule, returning a nat *)

Lemma twp_rand_exp_nat (N : nat) z (ε1 : R) (ε2 : nat -> R) E Φ s :
  TCEq N (Z.to_nat z) →
  (∀ n, (0 <= ε2 n <= 1)%R) →
  (SeriesC (λ n : nat, if bool_decide (n <= N)%nat then (1 / (S N)) * ε2 n else 0)%R <= ε1 )%R →
  ↯ ε1 -∗ (∀ (n : nat), ⌜ n <= N ⌝ ∗ ↯ (ε2 n) -∗ Φ #n) -∗
  WP rand #z @ s; E [{ Φ }].
Proof.
  iIntros (-> Hleq Hε1) "Herr HΦ".
  assert (forall n, 0 <= ε2 n)%R as Hleq1.
  {
    intros; apply Hleq.
  }
  assert (forall n, ε2 n <= 1)%R as Hleq2.
  {
    intros; apply Hleq.
  }
  iApply twp_lift_step_fupd_glm; [done|].
  iIntros (σ1 ε_now) "[Hσ Hε]".
  iApply fupd_mask_intro; [set_solver|].
  iIntros "Hclose'".
  iApply glm_adv_comp; simpl.
  (* iDestruct (ec_supply_bound with "Hε Herr") as %?. *)
  iDestruct (ec_supply_ec_inv with "Hε Herr") as %(ε1' & ε3 & Hε_now & Hε1').
  set (ecfn := (λ (ρ : expr * state),
                ε3 +
                  match ρ with
                  | (Val (LitV (LitInt n)), σ) =>
                      if bool_decide(σ = σ1)
                      then if bool_decide (0 ≤ n)%Z
                           then if bool_decide (Z.to_nat n <= Z.to_nat z)
                                then mknonnegreal _ (Hleq1 (Z.to_nat n))
                                else nnreal_zero
                           else nnreal_zero
                      else nnreal_zero
                  | _ => nnreal_zero
                  end)%NNR).
  iExists
    (λ (ρ : expr * state),
      ∃ (n : Z), (0 <= n)%Z /\ (Z.to_nat n <= Z.to_nat z) /\ ρ = (Val #n, σ1)), nnreal_zero, ecfn.
  iSplit.
  { iPureIntro. eapply head_prim_reducible; eauto with head_step. }
  iSplit.
  {
    iPureIntro. exists (ε3 + 1)%R.
    intros (e & σ); simpl.
    apply Rplus_le_compat; [lra |].
    do 6 (case_match; simpl; try lra).
    apply Hleq2.
  }
  iSplit.
  {
    iPureIntro.
    rewrite /ecfn /= Rplus_0_l.
    setoid_rewrite Rmult_plus_distr_l.
    rewrite SeriesC_plus.
    - rewrite Rplus_comm.
      subst.
      apply Rplus_le_compat.
      + etrans; eauto.
        etrans; last first.
        * apply (SeriesC_le_inj _
                   (λ ρ : expr * state,
                       let (e, σ) := ρ in
                       if bool_decide (σ = σ1) then
                         match e with
                         | Val #(LitInt n) =>
                             if bool_decide (0 ≤ n)%Z
                             then if bool_decide (Z.to_nat n <= Z.to_nat z)
                                  then Some (Z.to_nat n)
                                  else None
                             else None
                         | _ => None
                         end
                       else None)).
          ** intros.
             real_solver.
          ** intros ρ1 ρ2 m Hc1 Hc2.
             do 14 ((case_bool_decide || case_match); simplify_eq).
             f_equal.
             do 3 f_equal.
             apply Z2Nat.inj; auto.
          ** apply ex_seriesC_nat_bounded.
        * apply SeriesC_le.
          ** intros []; split.
             *** apply Rmult_le_pos; auto.
             *** case_bool_decide; simplify_eq.
                 **** do 5 (case_match; simpl; (try (rewrite Rmult_0_r; lra))); last first.
                      apply bool_decide_eq_true_1 in H2.
                      apply bool_decide_eq_true_1 in H3.
                      rewrite bool_decide_eq_true_2; last by lia.
                      apply Rmult_le_compat_r; [ auto |].
                      rewrite head_prim_step_eq /=.
                      rewrite /dmap /pmf/=/dbind_pmf/dunifP.
                      setoid_rewrite dunif_pmf.
                      rewrite SeriesC_scal_l /= /Rdiv Rmult_1_l.
                      rewrite <- Rmult_1_r.
                      apply Rmult_le_compat_l; auto.
                      ***** left. eapply Rlt_le_trans; [apply (RinvN_pos' (Z.to_nat z)) |].
                      done.
                      ***** rewrite /pmf/=/dret_pmf.
                      assert (Z.to_nat n < S (Z.to_nat z)) as H4 by lia.
                      erewrite <- (SeriesC_singleton (nat_to_fin H4)).
                      apply SeriesC_le; [ | apply ex_seriesC_singleton ].
                      intro; split; [ real_solver |].
                      case_bool_decide; try real_solver.
                      rewrite bool_decide_eq_true_2; [lra|].
                      simplify_eq.
                      apply fin_to_nat_inj.
                      rewrite fin_to_nat_to_fin.
                      rewrite Nat2Z.id //.
                 **** simpl. etrans; [ | right; eapply Rmult_0_l ].
                      apply Rmult_le_compat_r; [ auto | ].
                      right.
                      rewrite head_prim_step_eq /=.
                      rewrite /dmap /pmf/=/dbind_pmf/dunifP.
                      setoid_rewrite dunif_pmf.
                      rewrite SeriesC_scal_l /= /Rdiv.
                      erewrite (SeriesC_ext _ (λ _, 0));
                        [rewrite SeriesC_0; auto; by rewrite Rmult_0_r|].
                      intro; rewrite dret_0; auto.
                      intro; simplify_eq.
          ** eapply ex_seriesC_finite_from_option.
             instantiate (1 := (λ n:nat, ( Val #(LitInt n), σ1)) <$> (seq 0%nat (S (Z.to_nat z)))).
             intros [e σ].
             split.
             --- case_bool_decide; last first.
                 { inversion 1. done. }
                 case_match; try (by inversion 1).
                 case_match; try (by inversion 1).
                 case_match; try (by inversion 1).
                 case_bool_decide; try (by inversion 1).
                 case_match; try (by inversion 1).
                 intros. subst. eapply elem_of_list_fmap_1_alt; last first.
                 { repeat f_equal. instantiate (1 := Z.to_nat n). lia. }
                 apply bool_decide_eq_true_1 in H4.
                 rewrite elem_of_seq. lia.
             --- intros H1. apply elem_of_list_fmap_2 in H1.
                 destruct H1 as [n[H1 H2]].
                 inversion H1.
                 replace (bool_decide (_=_)) with true.
                 2: { case_bool_decide; done. }
                 replace (bool_decide _) with true.
                 2: { case_bool_decide; lia. }
                 case_match; first done.
                 apply bool_decide_eq_false_1 in H.
                 rewrite elem_of_seq in H2.
                 exfalso.
                 apply H.
                 lia.
      + rewrite SeriesC_scal_r.
        rewrite <- Rmult_1_l.
        apply Rmult_le_compat; auto; try lra; apply cond_nonneg.
    - by apply ex_seriesC_scal_r.
    - eapply ex_seriesC_ext; last eapply ex_seriesC_list.
      intros [e σ].
      instantiate (2 := (λ n:nat, ( Val #(LitInt n), σ1)) <$> (seq 0%nat (S (Z.to_nat z)))).
      case_bool_decide; last first.
      + repeat (case_match; try (simpl; lra)).
        exfalso. apply H. subst.
        eapply elem_of_list_fmap_1_alt; last first.
        { apply bool_decide_eq_true_1 in H3, H4. repeat f_equal.
          - instantiate (1 := Z.to_nat n). lia.
          - done.
        }
        rewrite elem_of_seq.
        apply bool_decide_eq_true_1 in H5.
        lia.
      + instantiate (1 :=
                       (λ '(e, s), (prim_step (rand #z) σ1 (e, s) *
                                      match e with
                                      | Val #(LitInt n) =>
                                          if bool_decide (s = σ1)
                                          then
                                            if bool_decide (0 ≤ n)%Z
                                            then if bool_decide (Z.to_nat n <= Z.to_nat z)
                                                 then ε2 (Z.to_nat n)
                                                 else nnreal_zero
                                            else nnreal_zero
                                          else nnreal_zero
                                      | _ => nnreal_zero
                                      end)%R)).
        simpl. repeat f_equal.
        repeat (case_match; try (simpl; lra)).
        * apply bool_decide_eq_true_1 in H5.
          apply bool_decide_eq_false_1 in H6.
          apply INR_le in H5.
          lia.
        * apply bool_decide_eq_false_1 in H5.
          apply Rnot_le_lt in H5.
          apply bool_decide_eq_true_1 in H6.
          apply INR_lt in H5.
          lia.
  }
  iSplit.
  {
    iPureIntro.
    eapply pgl_mon_pred; last first.
    - apply (pgl_rand_trivial (Z.to_nat z) z σ1); auto.
    - intros (e2, σ2) [n H].
      pose proof (fin_to_nat_lt n).
      exists (fin_to_nat n).
      split; [lia|].
      split; [lia|].
      auto.
  }
  iIntros (e2 σ2) "%H".
  destruct H as (n & Hn1 & Hn2 & Hn3); simplify_eq.
  rewrite /ecfn.
  rewrite bool_decide_eq_true_2; last done.
  rewrite bool_decide_eq_true_2; last first.
  { zify. lia.  }
  rewrite bool_decide_eq_true_2; last done.
  iMod (ec_supply_decrease with "Hε Herr") as (????) "Hε2".
  iModIntro.
  destruct (Rlt_decision (nonneg ε3 + (ε2 (Z.to_nat n)))%R 1%R) as [Hdec | Hdec]; last first.
  { apply Rnot_lt_ge, Rge_le in Hdec.
    iApply exec_stutter_spend.
    iPureIntro.
    simpl.
    lra.
  }
  (* replace (nonneg ε3 + (ε2 (nat_to_fin l)))%R with (nonneg (ε3 + (ε2 (nat_to_fin l)))%NNR); [|by simpl]. *)
  iApply exec_stutter_free.
  iMod (ec_supply_increase ε3 (mknonnegreal _ (Hleq1 (Z.to_nat n) )) with "[Hε2]") as "[Hε2 Hcr]".
  { simpl. lra. }
  { iApply ec_supply_eq; [|done]. simplify_eq. lra. }
  iMod "Hclose'".
  iApply fupd_mask_intro; [eauto|]; iIntros "_".
  iFrame.
  iApply tgl_wp_value.
  replace (#n) with (#(Z.to_nat n)); last first.
  {
    f_equal.
    by rewrite Z2Nat.id //.
  }
  iApply "HΦ".
  iFrame.
  iPureIntro.
  lia.
Qed.


Lemma wp_rand_exp_nat (N : nat) z (ε1 : R) (ε2 : nat -> R) E Φ :
  TCEq N (Z.to_nat z) →
  (∀ n, (0 <= ε2 n <= 1)%R) →
  (SeriesC (λ n : nat, if bool_decide (n <= N)%nat then (1 / (S N)) * ε2 n else 0)%R <= ε1 )%R →
  ↯ ε1 -∗ (∀ (n : nat), ⌜ n <= N ⌝ ∗ ↯ (ε2 n) -∗ Φ #n) -∗
  WP rand #z @ E {{ Φ }}.
Proof.
  iIntros.
  iApply tgl_wp_pgl_wp'.
  wp_apply (twp_rand_exp_nat with "[$]"); try done.
Qed.


(* General expectation preserving rule, returning a fin *)

Lemma twp_rand_exp_fin (N : nat) z E (ε1 : R) (ε2 : fin (S N) -> R) :
  TCEq N (Z.to_nat z) →
  (∀ n, (0 <= ε2 n)%R) →
  SeriesC (λ n, (1 / (S N)) * ε2 n)%R = ε1 →
  [[{ ↯ ε1 }]] rand #z @ E [[{ n, RET #n; ↯ (ε2 n) }]].
Proof.
  iIntros (-> Hleq Hε1 Ψ) "Herr HΨ".
  destruct (fin_function_bounded _ ε2) as [r Hε2].
  iApply twp_lift_step_fupd_glm; [done|].
  iIntros (σ1 ε_now) "[Hσ Hε]".
  iApply fupd_mask_intro; [set_solver|].
  iIntros "Hclose'".
  iApply glm_adv_comp; simpl.
  (* iDestruct (ec_supply_bound with "Hε Herr") as %?. *)
  iDestruct (ec_supply_ec_inv with "Hε Herr") as %(ε1' & ε3 & Hε_now & Hε1').
  set (foo := (λ (ρ : expr * state),
                ε3 +
                  match ρ with
                  | (Val (LitV (LitInt n)), σ) =>
                      if bool_decide(σ = σ1)
                      then if bool_decide (0 ≤ n)%Z
                           then match (lt_dec (Z.to_nat n) (S (Z.to_nat z))) with
                                | left H => mknonnegreal _ (Hleq (@Fin.of_nat_lt (Z.to_nat n) (S (Z.to_nat z)) H))
                                | _ => nnreal_zero
                                end
                           else nnreal_zero
                      else nnreal_zero
                  | _ => nnreal_zero
                  end)%NNR).
  iExists
    (λ (ρ : expr * state),
      ∃ (n : fin (S (Z.to_nat z))), ρ = (Val #n, σ1)), nnreal_zero, foo.
  iSplit.
  { iPureIntro. eapply head_prim_reducible; eauto with head_step. }
  iSplit.
  {
    iPureIntro. exists (ε3 + r)%R.
    intros (e & σ); simpl.
    apply Rplus_le_compat; [lra |].
    assert (0 <= r)%R.
    { transitivity (ε2 0%fin); auto.
    }
    do 6 (case_match; auto).
    apply Hε2.
  }
  iSplit.
  {
    iPureIntro.
    rewrite /foo /= Rplus_0_l.
    setoid_rewrite Rmult_plus_distr_l.
    rewrite SeriesC_plus.
    - rewrite Rplus_comm.
      subst.
      apply Rplus_le_compat.
      + rewrite Hε1'.
        etrans; last first.
        * apply (SeriesC_le_inj _
                   (λ ρ : expr * state,
                       let (e, σ) := ρ in
                       if bool_decide (σ = σ1) then
                         match e with
                         | Val #(LitInt n) =>
                             if bool_decide (0 ≤ n)%Z
                             then match lt_dec (Z.to_nat n) (S (Z.to_nat z)) with
                                  | left H => Some (nat_to_fin H)
                                  | right _ => None
                                  end
                             else None
                         | _ => None
                         end
                       else None)).
          ** intros.
             (* TODO: Add this to real solver *)
             apply Rmult_le_pos; [ | auto ].
             apply Rmult_le_pos; [lra |].
             left. apply RinvN_pos'.
          ** intros ρ1 ρ2 m Hc1 Hc2.
             do 14 ((case_bool_decide || case_match); simplify_eq).
             f_equal.
             do 3 f_equal.
             assert (fin_to_nat (nat_to_fin l0) = fin_to_nat (nat_to_fin l)) as He.
             { by rewrite Hc1. }
             rewrite !fin_to_nat_to_fin in He.
             by apply Z2Nat.inj.
          ** apply ex_seriesC_finite.
        * apply SeriesC_le.
          ** intros []; split.
             *** apply Rmult_le_pos; auto.
             *** case_bool_decide; simplify_eq.
                 **** do 5 (case_match; simpl; (try (rewrite Rmult_0_r; lra))).
                      apply Rmult_le_compat_r; [ auto |].
                      rewrite head_prim_step_eq /=.
                      rewrite /dmap /pmf/=/dbind_pmf/dunifP.
                      setoid_rewrite dunif_pmf.
                      rewrite SeriesC_scal_l /= /Rdiv Rmult_1_l.
                      rewrite <- Rmult_1_r.
                      apply Rmult_le_compat_l; auto.
                      ***** left. eapply Rlt_le_trans; [apply (RinvN_pos' (Z.to_nat z)) |].
                      done.
                      ***** rewrite /pmf/=/dret_pmf.
                      erewrite <- (SeriesC_singleton (nat_to_fin l0)).
                      apply SeriesC_le; [ | apply ex_seriesC_singleton ].
                      intro; split; [ real_solver |].
                      case_bool_decide; simplify_eq.
                      case_bool_decide; try real_solver.
                      rewrite bool_decide_eq_true_2; [lra|].
                      simplify_eq.
                      apply fin_to_nat_inj.
                      rewrite fin_to_nat_to_fin.
                      rewrite Nat2Z.id //.
                 **** simpl. etrans; [ | right; eapply Rmult_0_l ].
                      apply Rmult_le_compat_r; [ auto | ].
                      right.
                      rewrite head_prim_step_eq /=.
                      rewrite /dmap /pmf/=/dbind_pmf/dunifP.
                      setoid_rewrite dunif_pmf.
                      rewrite SeriesC_scal_l /= /Rdiv.
                      erewrite (SeriesC_ext _ (λ _, 0));
                        [rewrite SeriesC_0; auto; by rewrite Rmult_0_r|].
                      intro; rewrite dret_0; auto.
                      intro; simplify_eq.
          ** eapply ex_seriesC_finite_from_option.
             instantiate (1 := (λ n:nat, ( Val #(LitInt n), σ1)) <$> (seq 0%nat (S (Z.to_nat z)))).
             intros [e s].
             split.
             --- case_bool_decide; last first.
                 { inversion 1. done. }
                 case_match; try (by inversion 1).
                 case_match; try (by inversion 1).
                 case_match; try (by inversion 1).
                 case_bool_decide; try (by inversion 1).
                 case_match; try (by inversion 1).
                 intros. subst. eapply elem_of_list_fmap_1_alt; last first.
                 { repeat f_equal. instantiate (1 := Z.to_nat n). lia. }
                 rewrite elem_of_seq. lia.
             --- intros H1. apply elem_of_list_fmap_2 in H1.
                 destruct H1 as [n[H1 H2]].
                 inversion H1.
                 replace (bool_decide (_=_)) with true.
                 2: { case_bool_decide; done. }
                 replace (bool_decide _) with true.
                 2: { case_bool_decide; lia. }
                 case_match; first done.
                 rewrite elem_of_seq in H2. lia.
      + rewrite SeriesC_scal_r.
        rewrite <- Rmult_1_l.
        apply Rmult_le_compat; auto; try lra; apply cond_nonneg.
    - by apply ex_seriesC_scal_r.
    - eapply ex_seriesC_ext; last eapply ex_seriesC_list.
      intros [e s].
      instantiate (2 := (λ n:nat, ( Val #(LitInt n), σ1)) <$> (seq 0%nat (S (Z.to_nat z)))).
      case_bool_decide; last first.
      + repeat (case_match; try (simpl; lra)).
        exfalso. apply H. subst.
        eapply elem_of_list_fmap_1_alt; last first.
        { apply bool_decide_eq_true_1 in H3, H4. repeat f_equal.
          - instantiate (1 := Z.to_nat n). lia.
          - done.
        }
        rewrite elem_of_seq. lia.
      + instantiate (1 :=
                       (λ '(e, s), (prim_step (rand #z) σ1 (e, s) *
                                      match e with
                                      | Val #(LitInt n) =>
                                          if bool_decide (s = σ1)
                                          then
                                            if bool_decide (0 ≤ n)%Z
                                            then
                                              match lt_dec (Z.to_nat n) (S (Z.to_nat z)) with
                                              | left H0 => ε2 (nat_to_fin H0)
                                              | right _ => nnreal_zero
                                              end
                                            else nnreal_zero
                                          else nnreal_zero
                                      | _ => nnreal_zero
                                      end)%R)).
        simpl. repeat f_equal.
        repeat (case_match; try (simpl; lra)).
  }
  iSplit.
  {
    iPureIntro.
    eapply pgl_mon_pred; last first.
    - apply (pgl_rand_trivial (Z.to_nat z) z σ1); auto.
    - done.
  }
  iIntros (e2 σ2) "%H".
  destruct H as (n & Hn1); simplify_eq.
  rewrite /foo.
  rewrite bool_decide_eq_true_2; last done.
  rewrite bool_decide_eq_true_2; last first.
  { by zify. }


  case_match.
  2:{
    destruct n0.
    rewrite Nat2Z.id.
    apply fin_to_nat_lt.
  }
  iMod (ec_supply_decrease with "Hε Herr") as (????) "Hε2".
  iModIntro.
  destruct (Rlt_decision (nonneg ε3 + (ε2 (nat_to_fin l)))%R 1%R) as [Hdec|Hdec]; last first.
  { apply Rnot_lt_ge, Rge_le in Hdec.
    iApply exec_stutter_spend.
    iPureIntro.
    simpl.
    lra.
  }
  (* replace (nonneg ε3 + (ε2 (nat_to_fin l)))%R with (nonneg (ε3 + (ε2 (nat_to_fin l)))%NNR); [|by simpl]. *)
  iApply exec_stutter_free.
  iMod (ec_supply_increase ε3 (mknonnegreal _ (Hleq (nat_to_fin l))) with "[Hε2]") as "[Hε2 Hcr]".
  { simpl. lra. }
  { iApply ec_supply_eq; [|done]. simplify_eq. lra. }
  iMod "Hclose'".
  iApply fupd_mask_intro; [eauto|]; iIntros "_".
  iFrame.
  iApply tgl_wp_value.
  iApply "HΨ".
  assert (nat_to_fin l = n) as ->; [|done].
  apply fin_to_nat_inj.
  rewrite fin_to_nat_to_fin.
  rewrite Nat2Z.id.
  reflexivity.
Qed.


Lemma wp_rand_exp_fin (N : nat) z E (ε1 : R) (ε2 : fin (S N) -> R) :
  TCEq N (Z.to_nat z) →
  (∀ n, (0 <= ε2 n)%R) →
  SeriesC (λ n, (1 / (S N)) * ε2 n)%R = ε1 →
  {{{ ↯ ε1 }}} rand #z @ E {{{ n, RET #n; ↯ (ε2 n) }}}.
Proof.
  iIntros.
  iApply (tgl_wp_pgl_wp_step' with "[$]").
  wp_apply (twp_rand_exp_fin with "[$]"); try done.
  iIntros (?) "H1 H2". iModIntro.
  iApply ("H2" with "[$]").
Qed.

Lemma twp_rand_exp_fin1 (N : nat) z E (ε1 : R) (ε2 : fin (S N) -> R) :
  TCEq N (Z.to_nat z) →
  (∀ n, (0 <= ε2 n)%R) →
  SeriesC (λ n, (1 / (S N)) * ε2 n)%R = ε1 →
  [[{ ↯ ε1 }]] rand #z @ E [[{ n, RET #n; ↯ (ε2 n) }]].
Proof.
  iIntros (H1 H2).
  eapply (twp_rand_exp_fin _ _ _ ε1 ε2); auto.
Qed.


Lemma wp_rand_exp_fin1 (N : nat) z E (ε1 : R) (ε2 : fin (S N) -> R) :
  TCEq N (Z.to_nat z) →
  (∀ n, (0 <= ε2 n)%R) →
  SeriesC (λ n, (1 / (S N)) * ε2 n)%R = ε1 →
  {{{ ↯ ε1 }}} rand #z @ E {{{ n, RET #n; ↯ (ε2 n) }}}.
Proof.
  iIntros (H1 H2).
  eapply (wp_rand_exp_fin _ _ _ ε1 ε2); auto.
Qed.


(* Rule to avoid one outcome, returning an integer *)

Lemma twp_rand_err_int (N : nat) (z : Z) (m : Z) E Φ s :
  TCEq N (Z.to_nat z) →
  ↯ (/ (N + 1)) ∗ (∀ (x : Z), ⌜(0 <= x <= N)%Z /\ x ≠ m⌝ -∗ Φ #x)
    ⊢ WP rand #z @ s; E [{ Φ }].
Proof.
  iIntros (->) "[Herr Hwp]".
  destruct (Zle_or_lt 0 m).
  - iApply (twp_rand_exp_nat _ _ _ (λ (n : nat), if bool_decide (Z.of_nat n = m) then 1%R else 0%R) with "Herr").
    {
      intros.
      case_bool_decide; lra.
    }
    {
      erewrite <- (SeriesC_singleton_inj m Z.of_nat).
      - apply SeriesC_le.
        + intros n.
          case_bool_decide.
          * case_bool_decide.
            ** split; [real_solver |].
               rewrite S_INR.
               real_solver.
             ** rewrite Rmult_0_r.
                real_solver.
          * real_solver.
        + apply ex_seriesC_singleton_inj; [apply Nat2Z.inj'|].
          exists (Z.to_nat m).
          by apply Z2Nat.id.
      - apply Nat2Z.inj'.
      - exists (Z.to_nat m).
        by apply Z2Nat.id.
    }
    iIntros (n) "[%Hleq Herr]".
    case_bool_decide.
    + iExFalso.
      iApply (ec_contradict with "Herr"); lra.
    + iApply "Hwp".
      iPureIntro; lia.
  - iApply twp_rand_nat; auto.
    iIntros (n) "%Hn".
    iApply "Hwp".
    iPureIntro.
    lia.
Qed.


(* Rule to avoid one outcome, returning a fin *)

Lemma twp_rand_err_fin (N : nat) (z : Z) (m : fin (S N)) E Φ s :
  TCEq N (Z.to_nat z) →
  ↯ (/ (N + 1)) ∗ (∀ x, ⌜x ≠ m⌝ -∗ Φ #x)
    ⊢ WP rand #z @ s; E [{ Φ }].
Proof.
  iIntros (->) "[Herr Hwp]".
  iApply twp_lift_step_fupd_glm; [done|].
  iIntros (σ1 ε) "[Hσ Hε]".
  iApply fupd_mask_intro; [set_solver|].
  iIntros "Hclose'".
  iDestruct (ec_supply_ec_inv with "Hε Herr") as %(?&?& -> & He).
  iApply glm_prim_step.
  iExists
      (λ (ρ : expr * state),
        ∃ (n : fin (S (Z.to_nat z))), n ≠ m /\ ρ = (Val #n, σ1)), _, _.
  iSplit.
  { iPureIntro. eapply head_prim_reducible; eauto with head_step. }
  iSplit.
  {
    iPureIntro.
    apply Rle_refl.
  }
  iSplit.
  {
    iPureIntro.
    eapply pgl_mon_pred; last first.
    - rewrite He.
      assert (/ (Z.to_nat z + 1) = Rdiv 1 (Z.to_nat z + 1)) as ->.
      { simpl.
        rewrite /Rdiv/= Rmult_1_l //.
       }
      apply (pgl_rand_err (Z.to_nat z) z σ1); auto.
    - intros [] (n & Hn1 & [=]). simplify_eq.
      eauto.
  }
  iIntros (e2 σ2) "%H".
  destruct H as (n & Hn1 & [=]); simplify_eq.
  iMod (ec_supply_decrease with "Hε Herr") as (????) "Hdec".
  iModIntro.
  iMod "Hclose'".
  iFrame.
  iModIntro.
  rewrite -tgl_wp_value.
  iDestruct ("Hwp" with "[//]") as "$".
  iApply ec_supply_eq; [|done].
  simplify_eq.
  lra.
Qed.


Lemma wp_rand_err_int (N : nat) (z : Z) (m : Z) E Φ :
  TCEq N (Z.to_nat z) →
  ↯ (/ (N + 1)) ∗
    (∀ x, ⌜(0 <= x <= N)%Z /\ x ≠ m⌝ -∗ Φ #x)
    ⊢ WP rand #z @ E {{ Φ }}.
Proof.
  iIntros. iApply tgl_wp_pgl_wp'.
  iApply (twp_rand_err_int with "[$]").
Qed.

Lemma wp_rand_err_fin (N : nat) (z : Z) (m : fin (S N)) E Φ :
  TCEq N (Z.to_nat z) →
  ↯ (/ (N + 1)) ∗
    (∀ x, ⌜x ≠ m⌝ -∗ Φ #x)
    ⊢ WP rand #z @ E {{ Φ }}.
Proof.
  iIntros. iApply tgl_wp_pgl_wp'.
  iApply (twp_rand_err_fin with "[$]").
Qed.

Lemma twp_rand_err_nat (N : nat) (z : Z) (m : nat) E Φ s :
  TCEq N (Z.to_nat z) →
  ↯ (/ (N+1)) ∗
  (∀ x : nat, ⌜ (x ≤ N) /\  x ≠ m⌝ -∗ Φ #x)
  ⊢ WP rand #z @ s; E [{ Φ }].
Proof.
  iIntros (Heq) "[Herr Hwp]".
  rewrite Heq.
  iApply twp_lift_step_fupd_glm; [done|].
  iIntros (σ1 ε) "[Hσ Hε]".
  iApply fupd_mask_intro; [set_solver|].
  iIntros "Hclose'".
  iDestruct (ec_supply_ec_inv with "Hε Herr ") as %(?&?&->&He).
  iApply glm_prim_step.
  iExists
      (λ (ρ : expr * state),
        ∃ (n : nat), (n ≤ N) /\ n ≠ m /\ ρ = (Val #n, σ1)),_,_.
  iSplit.
  { iPureIntro. eapply head_prim_reducible; eauto with head_step. }
  iSplit.
  { iPureIntro; apply Rle_refl. }
  iSplit.
  {
    iPureIntro.
    eapply pgl_mon_pred; last first.
    - rewrite He.
      assert (/ (Z.to_nat z + 1) = Rdiv 1 (Z.to_nat z + 1)) as ->.
      { simpl.
        rewrite /Rdiv/= Rmult_1_l //. }
      apply (pgl_rand_err_nat (Z.to_nat z) z σ1); auto.
    - intros [] (n & Hn1 & [=]). simplify_eq.
      exists (fin_to_nat n).
      split; eauto.
      pose proof (fin_to_nat_lt n).
      rewrite Heq.
      lia.
  }
  iIntros (e2 σ2) "%Hn".
  destruct Hn as (n & Hn1 & Hn2 & [=]); simplify_eq.
  iMod (ec_supply_decrease with "Hε Herr") as (????) "Hdec".
  iModIntro.
  iMod "Hclose'".
  iFrame.
  iModIntro.
  rewrite -tgl_wp_value.
  iDestruct ("Hwp" with "[]") as "$".
  {
    iPureIntro.
    split; auto.
    rewrite -Heq //.
  }
  iApply ec_supply_eq; [|done].
  simplify_eq.
  lra.
Qed.


Lemma wp_rand_err_nat (N : nat) (z : Z) (m : nat) E Φ :
  TCEq N (Z.to_nat z) →
  ↯ (/ (N+1)) ∗
  (∀ x : nat, ⌜(x ≤ N) /\ x ≠ m⌝ -∗ Φ #x)
  ⊢ WP rand #z @ E {{ Φ }}.
Proof.
  iIntros. iApply tgl_wp_pgl_wp'.
  iApply (twp_rand_err_nat with "[$]").
Qed.


(* Error induction rule, by increasing *)

Lemma twp_err_incr e ε s E Φ :
  to_val e = None ->
  ↯ ε ∗
  (∀ ε', ⌜ (ε < ε')%R ⌝ -∗ ↯ (ε') -∗ WP e @ s; E [{ Φ }] )
  ⊢ WP e @ s; E [{ Φ }].
  Proof.
    iIntros (?) "[Herr Hwp]".
    iApply twp_lift_step_fupd_glm; [done|].
    iIntros (σ1 ε2) "[Hσ1 Hε2]".
    iApply fupd_mask_intro; [set_solver|].
    iIntros "Hclose'".
    iApply glm_err_incr_step.
    iIntros (ε') "%Hε'".
    apply Rlt_le in Hε' as Hε''.
    pose (diff :=((ε' - ε2) Hε'')%NNR).
    destruct (decide (ε' < 1)%R); last first.
    {
      iApply exec_stutter_spend.
      iPureIntro.
      simpl in *.
      simpl.
      lra.
    }
    replace (ε') with (ε2 + diff)%NNR; last (apply nnreal_ext; rewrite /diff; simpl; lra).
    iMod (ec_supply_increase _ diff with "[$]") as "[??]".
    { rewrite /diff. simpl. simpl in *.
      lra. }
    iPoseProof (ec_combine with "[$]") as "Herr".
    iSpecialize ("Hwp" with "[] Herr").
    {
      iPureIntro.
      simpl in *. simpl.
      lra.
    }
    rewrite !tgl_wp_unfold /tgl_wp_pre /=.
    rewrite H.
    iMod ("Hclose'").
    iMod ("Hwp" with "[$]").
    by iApply exec_stutter_free.
  Qed.


  Lemma wp_err_incr e ε E Φ :
    to_val e = None ->
    ↯ ε ∗
      (∀ ε', ⌜ (ε < ε')%R ⌝ -∗ ↯ (ε') -∗ WP e @ E {{ Φ }} )
      ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (?) "[Herr Hwp]".
    iApply wp_lift_step_fupd_glm; [done|].
    iIntros (σ1 ε2) "[Hσ1 Hε2]".
    iApply fupd_mask_intro; [set_solver|].
    iIntros "Hclose'".
    iApply glm_err_incr_step.
    iIntros (ε') "%Hε'".
    apply Rlt_le in Hε' as Hε''.
    pose (diff :=((ε' - ε2) Hε'')%NNR).
    destruct (decide (ε' < 1)%R); last first.
    {
      iApply exec_stutter_spend.
      iPureIntro.
      simpl in *.
      simpl.
      lra.
    }
    replace (ε') with (ε2 + diff)%NNR; last (apply nnreal_ext; rewrite /diff; simpl; lra).
    iMod (ec_supply_increase _ diff with "[$]") as "[??]".
    { rewrite /diff. simpl. simpl in *.
      lra. }
    iPoseProof (ec_combine with "[$]") as "Herr".
    iSpecialize ("Hwp" with "[] Herr").
    {
      iPureIntro.
      simpl in *. simpl.
      lra.
    }
    rewrite !pgl_wp_unfold /pgl_wp_pre /=.
    rewrite H.
    iMod ("Hclose'").
    iMod ("Hwp" with "[$]").
    by iApply exec_stutter_free.
Qed.


(* Error from thin air *)

Lemma twp_err_pos e s E Φ :
  to_val e = None ->
  (∀ ε, ⌜ (0 < ε)%R ⌝ -∗ ↯ (ε) -∗ WP e @ s; E [{ Φ }] )
    ⊢ WP e @ s; E [{ Φ }].
  Proof.
    iIntros (?) "?".
    iMod (ec_zero) as "Herr".
    iApply (twp_err_incr with "[$]"); auto.
  Qed.


Lemma wp_err_pos e E Φ :
  to_val e = None ->
  (∀ ε, ⌜ (0 < ε)%R ⌝ -∗ ↯ (ε) -∗ WP e @ E {{ Φ }} )
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (?) "?".
    iMod (ec_zero) as "Herr".
    iApply (wp_err_incr with "[$]"); auto.
  Qed.

(* Rule for avoiding elements of a list of ints, returning an int *)

Lemma twp_rand_err_list_int (N : nat) (z : Z) (zs : list Z) E Φ :
  TCEq N (Z.to_nat z) →
  ↯ (length zs / (N+1)) ∗
  (∀ x : Z, ⌜(0 <= x <= N)%Z /\ Forall (λ m, (x ≠ m)) zs⌝ -∗ Φ #x)
  ⊢ WP rand #z @ E [{ Φ }].
Proof.
  iIntros (H) "[Herr Hwp]".
  rewrite H.
  iApply twp_lift_step_fupd_glm; [done|].
  iIntros (σ1 ε) "[Hσ Hε]".
  iApply fupd_mask_intro; [set_solver|].
  iIntros "Hclose'".
  iDestruct (ec_supply_ec_inv with "Hε Herr ") as %(?&?&->&He).
  iApply glm_prim_step.
  iExists
    (λ (ρ : expr * state),
      ∃ (n : Z), (0 <= n <= N)%Z /\ Forall (λ m, n ≠ m) zs /\ ρ = (Val #n, σ1)),_,_.
  iSplit.
  { iPureIntro. eapply head_prim_reducible; eauto with head_step. }
  iSplit.
  { iPureIntro; apply Rle_refl. }
  iSplit.
  {
    iPureIntro.
    eapply pgl_mon_pred; last first.
    - rewrite He. apply (pgl_rand_err_list_int (Z.to_nat z) z σ1); auto.
    - intros [] (n & Hn1 & [=]).
      exists (Z.of_nat $ fin_to_nat n); split.
      + split; first by lia.
        rewrite H.
        pose proof (fin_to_nat_lt n) as Hlt.
        zify; lia.
      + simplify_eq; done.
  }
  iIntros (e2 σ2) "%Hn".
  destruct Hn as (n & Hn1 & Hn2 & [=]); simplify_eq.
  iMod (ec_supply_decrease with "Hε Herr") as (????) "Hdec".
  iModIntro.
  iMod "Hclose'".
  iFrame.
  iModIntro.
  rewrite -tgl_wp_value.
  iDestruct ("Hwp" with "[]") as "$".
  {
    iPureIntro; split; auto.
    rewrite -H //.
  }
  iApply ec_supply_eq; [|done].
  simplify_eq.
  lra.
Qed.


Lemma wp_rand_err_list_int (N : nat) (z : Z) (zs : list Z) E Φ :
  TCEq N (Z.to_nat z) →
  ↯ (length zs / (N+1)) ∗
  (∀ x : Z, ⌜(0 <= x <= N)%Z /\ Forall (λ m, (x ≠ m)) zs⌝ -∗ Φ #x)
  ⊢ WP rand #z @ E {{ Φ }}.
Proof.
  iIntros. iApply tgl_wp_pgl_wp'.
  by iApply twp_rand_err_list_int.
Qed.


(* Rule for avoiding elements of a list of ints, returning a fin *)

Lemma twp_rand_err_list_int_fin (N : nat) (z : Z) (zs : list Z) E Φ :
  TCEq N (Z.to_nat z) →
  ↯ (length zs / (N+1)) ∗
  (∀ x : fin (S N), ⌜Forall (λ m, (Z.of_nat $ fin_to_nat x) ≠ m) zs⌝ -∗ Φ #x)
  ⊢ WP rand #z @ E [{ Φ }].
Proof.
  iIntros (->) "[Herr Hwp]".
  iApply twp_lift_step_fupd_glm; [done|].
  iIntros (σ1 ε) "[Hσ Hε]".
  iApply fupd_mask_intro; [set_solver|].
  iIntros "Hclose'".
  iDestruct (ec_supply_ec_inv with "Hε Herr ") as %(?&?&->&He).
  iApply glm_prim_step.
  iExists
    (λ (ρ : expr * state),
      ∃ (n : fin (S (Z.to_nat z))), Forall (λ m, Z.of_nat (fin_to_nat n) ≠ m) zs /\ ρ = (Val #n, σ1)),_,_.
  iSplit.
  { iPureIntro. eapply head_prim_reducible; eauto with head_step. }
  iSplit.
  { iPureIntro; apply Rle_refl. }
  iSplit.
  {
    iPureIntro.
    eapply pgl_mon_pred; last first.
    - rewrite He. apply (pgl_rand_err_list_int (Z.to_nat z) z σ1); auto.
    - intros [] (n & Hn1 & [=]). simplify_eq. eauto.
  }
  iIntros (e2 σ2) "%H".
  destruct H as (n & Hn1 & [=]); simplify_eq.
  iMod (ec_supply_decrease with "Hε Herr") as (????) "Hdec".
  iModIntro.
  iMod "Hclose'".
  iFrame.
  iModIntro.
  rewrite -tgl_wp_value.
  iDestruct ("Hwp" with "[//]") as "$".
  iApply ec_supply_eq; [|done].
  simplify_eq.
  lra.
Qed.

Lemma wp_rand_err_list_int_fin (N : nat) (z : Z) (zs : list Z) E Φ :
  TCEq N (Z.to_nat z) →
  ↯ (length zs / (N + 1)) ∗
  (∀ x : fin (S N), ⌜Forall (λ m, (Z.of_nat $ fin_to_nat x) ≠ m) zs⌝ -∗ Φ #x)
  ⊢ WP rand #z @ E {{ Φ }}.
Proof.
  iIntros. iApply tgl_wp_pgl_wp'.
  by iApply twp_rand_err_list_int_fin.
Qed.


(* Rule for avoiding elements of a list of nats, returning a nat *)

Lemma twp_rand_err_list_nat (N : nat) (z : Z) (ns : list nat) E Φ :
  TCEq N (Z.to_nat z) →
  ↯ (length ns / (N+1)) ∗
  (∀ x : nat, ⌜ (x ≤ N) /\ Forall (λ m, x ≠ m) ns⌝ -∗ Φ #x)
  ⊢ WP rand #z @ E [{ Φ }].
Proof.
  iIntros (Heq) "[Herr Hwp]".
  rewrite Heq.
  iApply twp_lift_step_fupd_glm; [done|].
  iIntros (σ1 ε) "[Hσ Hε]".
  iApply fupd_mask_intro; [set_solver|].
  iIntros "Hclose'".
  iDestruct (ec_supply_ec_inv with "Hε Herr") as %(?&?&->&He).
  iApply glm_prim_step.
  iExists
    (λ (ρ : expr * state),
      ∃ (n : nat), (n ≤ N) /\ Forall (λ m, n ≠ m) ns /\ ρ = (Val #n, σ1)),_,_.
  iSplit.
  { iPureIntro. eapply head_prim_reducible; eauto with head_step. }
  iSplit.
  { iPureIntro; apply Rle_refl. }
  iSplit.
  {
    iPureIntro.
    eapply pgl_mon_pred; last first.
    - rewrite He.
      apply (pgl_rand_err_list_nat (Z.to_nat z) z σ1); auto.
    - intros [] (n & Hn1 & [=]). simplify_eq.
      exists (fin_to_nat n).
      split; auto.
      pose proof (fin_to_nat_lt n).
      rewrite Heq.
      lia.
  }
  iIntros (e2 σ2) "%Hn".
  destruct Hn as (n & Hn1 & Hn2 & [=]); simplify_eq.
  iMod (ec_supply_decrease with "Hε Herr") as (????) "Hdec".
  iModIntro.
  iMod "Hclose'".
  iFrame.
  iModIntro.
  rewrite -tgl_wp_value.
  iDestruct ("Hwp" with "[]") as "$".
  {
    iPureIntro; split; auto.
    rewrite -Heq; lia.
  }
  iApply ec_supply_eq; [|done].
  simplify_eq.
  lra.
Qed.

Lemma wp_rand_err_list_nat (N : nat) (z : Z) (ns : list nat) E Φ :
  TCEq N (Z.to_nat z) →
  ↯ (length ns / (N+1)) ∗
  (∀ x : nat, ⌜ (x ≤ N) /\ Forall (λ m, x ≠ m) ns⌝ -∗ Φ #x)
  ⊢ WP rand #z @ E {{ Φ }}.
Proof.
  iIntros. iApply tgl_wp_pgl_wp'.
  by iApply (twp_rand_err_list_nat).
Qed.

(* Rule for avoiding elements of a list of nats, returning a fin *)

Lemma twp_rand_err_list_nat_fin (N : nat) (z : Z) (ns : list nat) E Φ :
  TCEq N (Z.to_nat z) →
  ↯ (length ns / (N+1)) ∗
  (∀ x : fin (S N), ⌜Forall (λ m, fin_to_nat x ≠ m) ns⌝ -∗ Φ #x)
  ⊢ WP rand #z @ E [{ Φ }].
Proof.
  iIntros (->) "[Herr Hwp]".
  iApply twp_lift_step_fupd_glm; [done|].
  iIntros (σ1 ε) "[Hσ Hε]".
  iApply fupd_mask_intro; [set_solver|].
  iIntros "Hclose'".
  iDestruct (ec_supply_ec_inv with "Hε Herr") as %(?&?&->&He).
  iApply glm_prim_step.
  iExists
    (λ (ρ : expr * state),
      ∃ (n : fin (S (Z.to_nat z))), Forall (λ m, fin_to_nat n ≠ m) ns /\ ρ = (Val #n, σ1)),_,_.
  iSplit.
  { iPureIntro. eapply head_prim_reducible; eauto with head_step. }
  iSplit.
  { iPureIntro; apply Rle_refl. }
  iSplit.
  {
    iPureIntro.
    eapply pgl_mon_pred; last first.
    - rewrite He.
      apply (pgl_rand_err_list_nat (Z.to_nat z) z σ1); auto.
    - intros [] (n & Hn1 & [=]). simplify_eq.
      eauto.
  }
  iIntros (e2 σ2) "%H".
  destruct H as (n & Hn1 & [=]); simplify_eq.
  iMod (ec_supply_decrease with "Hε Herr") as (????) "Hdec".
  iModIntro.
  iMod "Hclose'".
  iFrame.
  iModIntro.
  rewrite -tgl_wp_value.
  iDestruct ("Hwp" with "[//]") as "$".
  iApply ec_supply_eq; [|done].
  simplify_eq.
  lra.
Qed.

Lemma wp_rand_err_list_nat_fin (N : nat) (z : Z) (ns : list nat) E Φ :
  TCEq N (Z.to_nat z) →
  ↯ (length ns / (N+1)) ∗
    (∀ x : fin (S N), ⌜Forall (λ m, (fin_to_nat x) ≠ m) ns⌝ -∗ Φ #x)
    ⊢ WP rand #z @ E {{ Φ }}.
Proof.
  iIntros. iApply tgl_wp_pgl_wp'.
  by iApply (twp_rand_err_list_nat_fin).
Qed.




(* Rule for avoiding elements in a list of nats satisfying
   a predicate P, returning a fin *)

Lemma wp_rand_err_filter (N : nat) (z : Z) (P : nat -> bool) E Φ :
  TCEq N (Z.to_nat z) →
  ↯ (length (List.filter P (seq 0 (S N))) / (N + 1)) ∗
    (∀ x : fin (S N), ⌜ P x = false ⌝ -∗ Φ #x)
    ⊢ WP rand #z @ E {{ Φ }}.
Proof.
  iIntros (?) "[H1 H2]".
  iApply tgl_wp_pgl_wp'.
  iApply (twp_rand_err_list_nat_fin _ _ (List.filter P (seq 0 (S N)))).
  iFrame.
  iIntros (x) "%H0".
  iApply "H2".
  iPureIntro.
  edestruct (List.Forall_forall) as (H1 & H2).
  specialize (H1 H0).
  destruct (P x) eqn:HPx ; auto.
  exfalso.
  apply (H1 x); auto.
  apply filter_In; split; auto.
  apply in_seq.
  simpl.
  split; auto with arith.
  apply fin_to_nat_lt.
Qed.


(* FIXME: where should this go (if anywhere?) *)
Lemma match_nonneg_coercions (n : nonnegreal) : NNRbar_to_real (NNRbar.Finite n) = nonneg n.
Proof. by simpl. Qed.

Lemma mean_constraint_ub (N : nat) ε1 (ε2 : fin (S N) → nonnegreal) :
  SeriesC (λ n, (1 / (S N)) * ε2 n)%R = (nonneg ε1) →
  (∃ r, (0 <= r)%R ∧ ∀ n,(ε2 n <= r)%R).
Proof.
  intros Hsum.
  exists (nnreal_nat (S N) * ε1)%NNR.
  split. { apply Rmult_le_pos; apply cond_nonneg. }
  intros n.
  Opaque nnreal_nat.
  rewrite /= -Hsum.
  rewrite SeriesC_scal_l -Rmult_assoc -(Rmult_1_l (nonneg (ε2 _))).
  apply Rmult_le_compat; try lra.
  - by apply cond_nonneg.
  - rewrite /Rdiv Rmult_1_l.
    rewrite /= Rinv_r; try lra.
    Transparent nnreal_nat.
    rewrite /nnreal_nat.
    replace (nonneg {| nonneg := INR (S N); cond_nonneg := _ |}) with (INR (S N)); [| by simpl ].
    by apply not_0_INR.
  - rewrite -match_nonneg_coercions.
    rewrite -(SeriesC_singleton_dependent _ ε2).
    apply SeriesC_le.
    + intros n'.
      assert (H : (0 <= (nonneg (ε2 n')))%R) by apply cond_nonneg.
      rewrite /nnreal_zero /=.
      case_bool_decide; try lra.
    + apply ex_seriesC_finite.
Qed.




(* Error amplification for sampling a fin *)

Lemma twp_rand_err_amp_fin (N : nat) (z : Z) (m : nat) (ε0 : R) E Φ :
  TCEq N (Z.to_nat z) →
  ↯ ε0 ∗
  (∀ x : fin (S N), (⌜fin_to_nat x ≠ m⌝ ∨ ↯ (ε0 * (N + 1))) -∗ Φ #x)
  ⊢ WP rand #z @ E [{ Φ }].
Proof.
  iIntros (?) "(Herr&Hwp)".
  iPoseProof (ec_valid with "Herr") as "(%Hε00 & %Hε01)".
  destruct (le_lt_dec (S N) m) as [H1 | H2].
  - wp_apply (twp_rand); auto.
    iIntros (n) "?".
    iApply "Hwp".
    iLeft.
    iPureIntro.
    intros ?.
    pose proof (fin_to_nat_lt n).
    lia.
  -
  set (ε2 := (λ x : fin (S N), if bool_decide ((fin_to_nat x) =  (Fin.of_nat_lt H2))
                               then (ε0 * (N + 1))%R
                               else 0%R)).
  wp_apply (twp_rand_exp_fin1 _ _ _ ε0 ε2 with "Herr").
  {
    intros n.
    rewrite /ε2.
    case_bool_decide; [ |lra].
    apply Rmult_le_pos; [lra|].
    pose proof (pos_INR N).
    lra.
  }
  {
    rewrite -(SeriesC_singleton (Fin.of_nat_lt H2) ε0) /ε2.
    apply SeriesC_ext.
    intro n.
    case_bool_decide; case_bool_decide; simplify_eq; [| simpl; lra].
    rewrite S_INR /=.
    rewrite /Rdiv Rmult_1_l Rmult_comm Rmult_assoc Rmult_inv_r; [lra | ].
    intros Heq.
    pose proof (pos_INR N).
    lra.
  }
  iIntros (n) "Herr".
  iApply "Hwp".
  rewrite /ε2.
  case_bool_decide as Hdec.
  + by iRight.
  + iLeft.
    iPureIntro.
    intros H3.
    simplify_eq.
    apply Hdec.
    f_equal.
    rewrite nat_to_fin_to_nat //.
Qed.


Lemma wp_rand_err_amp_fin (N : nat) (z : Z) (m : nat) (ε0 : R) E Φ :
  TCEq N (Z.to_nat z) →
  ↯ ε0 ∗
  (∀ x : fin (S N), (⌜fin_to_nat x ≠ m⌝ ∨ ↯ (ε0 * (N + 1))) -∗ Φ #x)
  ⊢ WP rand #z @ E {{ Φ }}.
Proof.
  iIntros (?) "[Herr Hwp]".
  iApply tgl_wp_pgl_wp'.
  iApply (twp_rand_err_amp_fin with "[$Herr Hwp]"); done.
Qed.


(* Error amplification for sampling a nat *)


Lemma twp_rand_err_amp_nat (N : nat) (z : Z) (m : nat) (ε0 : R) E Φ :
  TCEq N (Z.to_nat z) →
  ↯ ε0 ∗
    (∀ n : nat, ⌜ n ≤ N ⌝ ∗ (⌜n ≠ m⌝ ∨ ↯ (ε0 * (N + 1))) -∗ Φ #n)
    ⊢ WP rand #z @ E [{ Φ }].
Proof.
  iIntros (?) "[Herr Hwp]".
  iApply (twp_rand_err_amp_fin N z m with "[$Herr Hwp]").
  iIntros (x) "Hx".
  iApply "Hwp".
  iSplit.
  - iPureIntro.
    pose proof (fin_to_nat_lt x); lia.
  - done.
Qed.

Lemma wp_rand_err_amp_nat (N : nat) (z : Z) (m : nat) (ε0 : R) E Φ :
  TCEq N (Z.to_nat z) →
  ↯ ε0 ∗
    (∀ n : nat, ⌜ n ≤ N ⌝ ∗ (⌜n ≠ m⌝ ∨ ↯ (ε0 * (N + 1))) -∗ Φ #n)
    ⊢ WP rand #z @ E {{ Φ }}.
Proof.
  iIntros (?) "[Herr Hwp]".
  iApply tgl_wp_pgl_wp'.
  iApply (twp_rand_err_amp_nat with "[$]").
Qed.


(* Error amplification for avoiding elements in a list of nats *)

Lemma twp_rand_err_list_adv (N : nat) (z : Z) (ns : list nat) (ε0 ε1 : R) E Φ :
  TCEq N (Z.to_nat z) →
  (0 <= ε1)%R ->
  (ε1 * (length ns) <= ε0 * (N + 1))%R ->
  ↯ ε0 ∗
    (∀ x : fin (S N),
        (⌜Forall (λ m, (fin_to_nat x) ≠ m) ns⌝ ∨ ↯ ε1) -∗ Φ #x)
    ⊢ WP rand #z @ E [{ Φ }].
Proof.
  iIntros (HN Hε1pos Hleq) "[Herr Hwp]".
  set (ε2 := (λ x : fin (S N), if bool_decide (Exists (λ m : nat, (fin_to_nat x) =  m) ns) then ε1 else 0%R)).
  wp_apply (twp_rand_exp_fin1 _ _ _ (SeriesC (λ n : fin (S N), (1 / (N + 1) * ε2 n)%R)) ε2 with "[Herr]").
  - intros n.
    rewrite /ε2.
    case_bool_decide; auto.
    lra.
  - rewrite S_INR //.
  - iApply ec_weaken; auto.
    simpl.
    rewrite SeriesC_scal_l /ε2.
    rewrite (SeriesC_ext _ (λ x : fin (S N),
                   ε1 * (if bool_decide (Exists (λ m : nat, fin_to_nat x = m) ns) then 1 else 0))%R); last first.
    {
      intro n.
      case_bool_decide; simpl; lra.
    }
    rewrite SeriesC_scal_l.
    rewrite /Rdiv Rmult_1_l.
    rewrite Rmult_comm.
    rewrite -Rdiv_def.
    pose proof (pos_INR N).
    split.
    { apply Rmult_le_pos; [|real_solver].
      apply Rmult_le_pos; [auto|].
      apply SeriesC_ge_0; [|apply ex_seriesC_finite].
      intros ?. case_bool_decide; lra. }

    apply Rcomplements.Rle_div_l; [lra |].
    assert (SeriesC (λ x : fin (S N), if bool_decide (Exists (λ m : nat, fin_to_nat x = m) ns) then 1 else 0) <= length ns)%R as Haux.
    {
      induction ns as [|?].
      - erewrite SeriesC_ext; last first.
        + intros.
          erewrite bool_decide_ext; [ | apply Exists_nil ].
          done.
        + simpl.
          setoid_rewrite bool_decide_False.
          rewrite SeriesC_0 ; auto.
          lra.
      - erewrite SeriesC_ext; last first.
        + intros.
          erewrite bool_decide_ext; [ | apply Exists_cons ].
          done.
        + etrans.
          * right. symmetry.
            eapply is_seriesC_filter_union.
            2: { apply SeriesC_correct, ex_seriesC_finite. }
            intro; simpl; lra.
          * rewrite length_cons S_INR /=.
            assert (SeriesC (λ n : fin (S N), if bool_decide (fin_to_nat n = a) then 1 else 0) <= 1)%R as Haux2.
            {
              destruct (decide (a < S N)).
              - rewrite SeriesC_singleton_inj; [lra |].
                exists (nat_to_fin l).
                rewrite fin_to_nat_to_fin //.
              - transitivity 0%R; [ | lra].
                right.
                apply SeriesC_0.
                intro.
                case_bool_decide; auto.
                simplify_eq.
                exfalso. apply n.
                apply fin_to_nat_lt.
            }
            rewrite (Rplus_comm _ 1).
            rewrite -Rplus_minus_assoc.
            apply Rplus_le_compat; [apply Haux2 |].
            etrans; last first.
            ** apply IHns.
               etrans; eauto.
               apply Rmult_le_compat_l; [auto |].
               rewrite length_cons S_INR; lra.
            **
              apply Rcomplements.Rle_minus_l.
              rewrite <- (Rplus_0_r) at 1.
              apply Rplus_le_compat; [ apply Rle_refl |].
              apply SeriesC_ge_0; [ | apply ex_seriesC_finite ].
              intros; real_solver.
    }
    etrans; eauto.
    apply Rmult_le_compat_l; auto.
  - iIntros (n) "Herrn".
    rewrite /ε2.
    case_bool_decide.
    + iApply "Hwp".
      iRight.
      iFrame.
    + iApply "Hwp".
      iLeft.
      iPureIntro.
      apply not_Exists_Forall; auto.
      apply _.
Qed.

Lemma wp_rand_err_list_adv (N : nat) (z : Z) (ns : list nat) (ε0 ε1 : R) E Φ :
  TCEq N (Z.to_nat z) →
  (0 <= ε1)%R ->
  (ε1 * (length ns) <= ε0 * (N + 1))%R ->
  ↯ ε0 ∗
    (∀ x : fin (S N),
        (⌜Forall (λ m, (fin_to_nat x) ≠ m) ns⌝ ∨  ↯ ε1 ) -∗ Φ #x)
    ⊢ WP rand #z @ E {{ Φ }}.
Proof.
  iIntros (HN Hε1 HK) "[Herr Hwp]".
  iApply tgl_wp_pgl_wp'.
  wp_apply twp_rand_err_list_adv; eauto.
  iFrame.
Qed.



(* Error amplification for avoiding elements satisfying a predicate P *)

Lemma twp_rand_err_filter_adv (N : nat) (z : Z) (P : nat -> bool) (ε0 ε1 : R) E Φ :
  TCEq N (Z.to_nat z) →
  (0 <= ε1)%R ->
  (ε1 * (length (List.filter P (seq 0 (S N)))) <= ε0 * (N + 1))%R ->
  ↯ ε0 ∗
    (∀ x : fin (S N), ((⌜ P x = false⌝) ∨ ↯ ε1 ) -∗ Φ #x)
    ⊢ WP rand #z @ E [{ Φ }].
Proof.
  iIntros (? ? HK) "[H1 Hwp]".
  iApply (twp_rand_err_list_adv _ _ (List.filter P (seq 0 (S N))) ε0 ε1); auto.
  iFrame.
  iIntros (x) "[%Hfor|Herr]".
  - iApply "Hwp".
    iLeft.
    iPureIntro.
    edestruct (List.Forall_forall) as (H1 & H2).
    specialize (H1 Hfor).
    destruct (P x) eqn:HPx ; auto.
    exfalso.
    apply (H1 x); auto.
    apply filter_In; split; auto.
    apply in_seq.
    simpl.
    split; auto with arith.
    apply fin_to_nat_lt.
  - iApply "Hwp".
    iRight. iFrame.
Qed.


(* Two lemmas about lists. Could be moved, but not sure where to *)
Lemma length_filter_seq_below (N M : nat):
  (M <= N) ->
  length (List.filter (λ x : nat, bool_decide (x ≤ M)) (seq 0 (S N))) = (M + 1).
Proof.
  intro HMN.
  induction HMN.
  - rewrite forallb_filter_id.
    + rewrite length_seq. lia.
    + apply Is_true_eq_true.
      apply forallb_True.
      apply Forall_seq.
      intros.
      rewrite bool_decide_eq_true_2; auto.
      lia.
  - rewrite seq_S List.filter_app.
    rewrite length_app IHHMN.
    simpl.
    rewrite bool_decide_eq_false_2 /=; first by lia.
    intro H.
    lia.
Qed.


Lemma length_filter_seq_above (N M : nat):
  (M <= N) ->
  length (List.filter (λ x : nat, bool_decide (M < x)) (seq 0 (S N))) = (N - M).
Proof.
  intro HMN.
  induction HMN.
  - replace (length (List.filter (λ x : nat, bool_decide (M < x)) (seq 0 (S M))))
      with
      ((S M) - length (List.filter (λ x : nat, bool_decide (x <= M)) (seq 0 (S M)))).
    + rewrite forallb_filter_id.
      * rewrite length_seq. lia.
      * apply Is_true_eq_true.
        apply forallb_True.
        apply Forall_seq.
        intros.
        rewrite bool_decide_eq_true_2; auto.
        lia.
    + replace (S M) with (length (seq 0 (S M))) at 1;
        last by rewrite length_seq; auto.
      rewrite -(List.filter_length (λ x, bool_decide (x <= M))).
      rewrite Nat.add_sub'.
      f_equal.
      apply filter_ext.
      intro a.
      case_bool_decide; case_bool_decide; auto; lia.
  - rewrite seq_S List.filter_app.
    rewrite length_app IHHMN.
    simpl.
    rewrite bool_decide_eq_true_2 /=; first by lia.
    lia.
Qed.


(* Error amplification for sampling below a bound *)

Lemma twp_rand_err_filter_below (N : nat) (M : nat) (z : Z) (ε0 ε1 : R) E Φ :
  TCEq N (Z.to_nat z) →
  (M <= N) ->
  (0 <= ε1)%R ->
  (ε1 * (M + 1) <= ε0 * (N + 1))%R ->
  ↯ ε0 ∗
    (∀ x : fin (S N), ((⌜ M < x ⌝) ∨ ↯ ε1 ) -∗ Φ #x)
    ⊢ WP rand #z @ E [{ Φ }].
Proof.
  iIntros (? HMN ? HK) "[H1 Hwp]".
  iApply (twp_rand_err_filter_adv _ _ (λ x, bool_decide (x <= M))); eauto.
  - rewrite length_filter_seq_below; auto.
    rewrite plus_INR /=.
    done.
  - iFrame.
    iIntros (x) "[%H1 | H2]".
    + iApply "Hwp".
      iLeft.
      iPureIntro.
      apply bool_decide_eq_false_1 in H1.
      lia.
    + iApply "Hwp".
      iRight. done.
Qed.


Lemma twp_rand_err_filter_above (N : nat) (M : nat) (z : Z) (ε0 ε1 : R) E Φ :
  TCEq N (Z.to_nat z) →
  (M <= N) ->
  (0 <= ε1)%R ->
  (ε1 * (N - M) <= ε0 * (N + 1))%R ->
  ↯ ε0 ∗
    (∀ x : fin (S N), ((⌜ x <= M ⌝) ∨ ↯ ε1 ) -∗ Φ #x)
    ⊢ WP rand #z @ E [{ Φ }].
Proof.
  iIntros (? HMN ? HK) "[H1 Hwp]".
  iApply (twp_rand_err_filter_adv _ _ (λ x, bool_decide (M < x))); eauto.
  - rewrite length_filter_seq_above; auto.
    rewrite minus_INR /= //.
  - iFrame.
    iIntros (x) "[%H1 | H2]".
    + iApply "Hwp".
      iLeft.
      iPureIntro.
      apply bool_decide_eq_false_1 in H1.
      lia.
    + iApply "Hwp".
      iRight. done.
Qed.


Lemma wp_rand_err_filter_adv (N : nat) (z : Z) (P : nat -> bool) (ε0 ε1 : R) E Φ :
  TCEq N (Z.to_nat z) →
  (0 <= ε1)%R ->
  (ε1 * (length (List.filter P (seq 0 (S N)))) <= ε0 * (N + 1))%R ->
  ↯ ε0 ∗
    (∀ x : fin (S N), (⌜ P x = false⌝ ∨ ↯ ε1) -∗ Φ #x)
    ⊢ WP rand #z @ E {{ Φ }}.
Proof.
  iIntros (? ? HK) "[H1 Hwp]".
  iApply tgl_wp_pgl_wp'.
  wp_apply twp_rand_err_filter_adv; eauto.
  iFrame.
Qed.



Lemma wp_bind_err_simpl e `{Hctx:!LanguageCtx K} s E (ε1 ε2 : R) P (Q : val -> iProp Σ) Φ:
  (0 <= ε1)%R →
  (0 <= ε2)%R →
  (↯ ε1 -∗ P -∗ WP e @ s; E {{ Q }}) -∗
  (∀ x, Q x -∗ ↯ ε2 -∗ WP K (Val x) @ s ; E {{ Φ }}) -∗
  P -∗ ↯ (ε1+ε2)%NNR -∗ WP K e @ s; E {{ Φ }}.
  Proof.
    iIntros (??) "H1 H2 HP Hε".
    iApply pgl_wp_bind.
    rewrite ec_split //.
    iDestruct ("Hε") as "[He1 He2]".
    iApply (pgl_wp_wand with "[H1 He1 HP]").
    { by iApply ("H1" with "[$]"). }
    iIntros (v) "HQ".
    iApply ("H2" with "[$]"). done.
  Qed.

  Lemma wp_bind_err_exp e `{Hctx:!LanguageCtx K} s E ε1 ε2 P (Q : val -> iProp Σ) Φ:
    (↯ ε1 -∗ P -∗ WP e @ s; E {{ v, ↯ (ε2 v) ∗ (Q v)}}) -∗
    (∀ x, Q x -∗ ↯ (ε2 x) -∗ WP K (Val x) @ s ; E {{ Φ }}) -∗
    P -∗ ↯ ε1 -∗ WP K e @ s; E {{ Φ }}.
  Proof.
    iIntros "H1 H2 HP Hε".
    iApply pgl_wp_bind.
    iApply (pgl_wp_wand with "[H1 Hε HP]").
    { instantiate (1 := (λ v, ↯ (ε2 v) ∗ Q v)%I). by iApply ("H1" with "[$]"). }
    iIntros (v) "[Hε HQ]".
    iApply ("H2" with "[$]"). done.
  Qed.


  Lemma twp_rec_total E (ε k : R) e Φ Ψ :
    to_val e = None →
    (0 < ε)%R →
    (1 < k)%R →
    □ (∀ (ε' : R), ⌜(0<ε')%R⌝ -∗ □ (Ψ -∗ ↯ (k * ε')%NNR -∗ WP e @ E [{ Φ }]) -∗
    Ψ -∗ ↯ ε' -∗ WP e @ E [{ Φ }]) -∗
    Ψ -∗ ↯ ε -∗ WP e @ E [{ Φ }].
  Proof.
    iIntros (Hnval Hpos Hgt1) "#Hrec HΨ Herr".
    iRevert "HΨ".
    iApply (ec_ind_amp _ k with "[] Herr");  [done|done|].
    iIntros "!#" (ε') "%Hε' #HWP Herr HΨ".
    iApply ("Hrec" $! ε' with "[//] [HWP] HΨ Herr").
    iModIntro.
    iIntros "HΨ Herr".
    iApply ("HWP" with "Herr HΨ").
  Qed.


End rules.

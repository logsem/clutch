(** * Union bound rules  *)
From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext.
From clutch.prob_lang Require Import notation tactics metatheory.
From clutch.prob_lang Require Export lang.
From clutch.ub_logic Require Export lifting ectx_lifting primitive_laws proofmode.


Section metatheory.

  Local Open Scope R.


(** * rand(N) no error *)
Lemma ub_lift_rand_trivial N z σ1 :
  N = Z.to_nat z →
  ub_lift
    (prim_step (rand #z from #()) σ1)
    (λ ρ2, ∃ (n : fin (S N)),
        ρ2 = (Val #n, σ1)) 0.
Proof.
  simpl in *.
  intros Hz.
  rewrite head_prim_step_eq /=.
  rewrite /dmap -Hz.
  rewrite -(Rplus_0_r 0).
  eapply (ub_lift_dbind _ _ _ _ _ 0); last first.
  { by apply ub_lift_trivial. }
  2,3: done.
  intros n ?.
  apply ub_lift_dret.
  by exists n.
Qed.

(** * rand(N) error *)
Lemma ub_lift_rand_err N z σ1 (m : fin (S N)):
  N = Z.to_nat z →
  ub_lift
    (prim_step (rand #z from #()) σ1)
    (λ ρ2, ∃ (n : fin (S N)),
        (n ≠ m)%fin /\ ρ2 = (Val #n, σ1)) (1/(N+1)).
Proof.
  simpl in *.
  intros Hz.
  rewrite head_prim_step_eq /=.
  rewrite /dmap -Hz.
  rewrite -(Rplus_0_r (1 / (N + 1))).
  eapply (ub_lift_dbind _ _ _ _ _ 0); last first.
  { by apply ub_unif_err. }
  - intros n ?.
    apply ub_lift_dret.
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
Lemma ub_lift_rand_err_nat N z σ1 (m : nat):
  N = Z.to_nat z →
  ub_lift
    (prim_step (rand #z from #()) σ1)
    (λ ρ2, ∃ (n : fin (S N)),
        (fin_to_nat n ≠ m)%fin /\ ρ2 = (Val #n, σ1)) (1/(N+1)).
Proof.
  simpl in *.
  intros Hz.
  rewrite head_prim_step_eq /=.
  rewrite /dmap -Hz.
  rewrite -(Rplus_0_r (1 / (N + 1))).
  eapply (ub_lift_dbind _ _ _ _ _ 0); last first.
  { by apply ub_unif_err_nat. }
  - intros n ?.
    apply ub_lift_dret.
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
Lemma ub_lift_rand_err_list_nat N z σ1 (ms : list nat):
  N = Z.to_nat z →
  ub_lift
    (prim_step (rand #z from #()) σ1)
    (λ ρ2, ∃ (n : fin (S N)),
        Forall (λ m, (fin_to_nat n ≠ m)%fin) ms /\ ρ2 = (Val #n, σ1)) ((length ms)/(N+1)).
Proof.
  simpl in *.
  intros Hz.
  rewrite head_prim_step_eq /=.
  rewrite /dmap -Hz.
  rewrite -(Rplus_0_r ((length ms) / (N + 1))).
  eapply (ub_lift_dbind _ _ _ _ _ 0); last first.
  { by apply ub_unif_err_list_nat. }
  - intros n ?.
    apply ub_lift_dret.
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


Lemma ub_lift_rand_err_list_int N z σ1 (ms : list Z):
  N = Z.to_nat z →
  ub_lift
    (prim_step (rand #z from #()) σ1)
    (λ ρ2, ∃ (n : fin (S N)),
        Forall (λ m, (Z.of_nat (fin_to_nat n) ≠ m)%fin) ms /\ ρ2 = (Val #n, σ1)) ((length ms)/(N+1)).
Proof.
  simpl in *.
  intros Hz.
  rewrite head_prim_step_eq /=.
  rewrite /dmap -Hz.
  rewrite -(Rplus_0_r ((length ms) / (N + 1))).
  eapply (ub_lift_dbind _ _ _ _ _ 0); last first.
  { by apply ub_unif_err_list_int. }
  - intros n ?.
    apply ub_lift_dret.
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
  Context `{!ub_clutchGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types v : val.
  Implicit Types l : loc.

Lemma wp_rand_err (N : nat) (z : Z) (m : fin (S N)) E Φ :
  TCEq N (Z.to_nat z) →
  € (nnreal_inv(nnreal_nat(N+1))) ∗
  (∀ x, ⌜x ≠ m⌝ -∗ Φ #x)
  ⊢ WP rand #z from #() @ E {{ Φ }}.
Proof.
  iIntros (->) "[Herr Hwp]".
  iApply wp_lift_step_fupd_exec_ub; [done|].
  iIntros (σ1 ε) "[Hσ Hε]".
  iApply fupd_mask_intro; [set_solver|].
  iIntros "Hclose'".
  solve_red.
  iDestruct (ec_supply_bound with "Hε Herr ") as %Hle.
  set (ε' := nnreal_minus ε (nnreal_inv (nnreal_nat (Z.to_nat z + 1))) Hle ).
  replace ε with (nnreal_plus (nnreal_inv (nnreal_nat (Z.to_nat z + 1))) ε'); last first.
  { apply nnreal_ext; simpl; lra. }
  iApply exec_ub_prim_step.
  iExists
      (λ (ρ : expr * state),
        ∃ (n : fin (S (Z.to_nat z))), n ≠ m /\ ρ = (Val #n, σ1)), _, _.
  iSplit.
  {
    iPureIntro.
    apply Rle_refl.
  }
  iSplit.
  {
    iPureIntro.
    eapply UB_mon_pred; last first.
    - assert (nonneg ( nnreal_inv (nnreal_nat (Z.to_nat z + 1)))
             = Rdiv 1 (Z.to_nat z + 1)) as ->.
      { simpl.
        rewrite /Rdiv/= Rmult_1_l.
        do 2 f_equal.
        rewrite plus_INR.
        f_equal.
       }
      apply (ub_lift_rand_err (Z.to_nat z) z σ1); auto.
    - intros [] (n & Hn1 & [=]). simplify_eq.
      eauto.
  }
  iIntros ((e2 & σ2)) "%H".
  destruct H as (n & Hn1 & [=]); simplify_eq.
  iPoseProof (ec_decrease_supply) as "Hdec".
  iSpecialize ("Hdec" with "Hε Herr"); eauto.
  do 2 iModIntro.
  iMod "Hclose'".
  iMod "Hdec".
  iFrame.
  iModIntro.
  iApply ub_wp_value.
  iApply "Hwp".
  done.
Qed.


Lemma wp_rand_err_nat (N : nat) (z : Z) (m : nat) E Φ :
  TCEq N (Z.to_nat z) →
  € (nnreal_inv(nnreal_nat(N+1))) ∗
  (∀ x, ⌜x ≠ m⌝ -∗ Φ #x)
  ⊢ WP rand #z from #() @ E {{ Φ }}.
Proof.
  iIntros (->) "[Herr Hwp]".
  iApply wp_lift_step_fupd_exec_ub; [done|].
  iIntros (σ1 ε) "[Hσ Hε]".
  iApply fupd_mask_intro; [set_solver|].
  iIntros "Hclose'".
  solve_red.
  iDestruct (ec_supply_bound with "Hε Herr ") as %Hle.
  set (ε' := nnreal_minus ε (nnreal_inv (nnreal_nat (Z.to_nat z + 1))) Hle ).
  replace ε with (nnreal_plus (nnreal_inv (nnreal_nat (Z.to_nat z + 1))) ε'); last first.
  { apply nnreal_ext; simpl; lra. }
  iApply exec_ub_prim_step.
  iExists
      (λ (ρ : expr * state),
        ∃ (n : fin (S (Z.to_nat z))), fin_to_nat n ≠ m /\ ρ = (Val #n, σ1)),_,_.
  iSplit.
  {
    iPureIntro; apply Rle_refl.
  }
  iSplit.
  {
    iPureIntro.
    eapply UB_mon_pred; last first.
    - assert (nonneg (nnreal_inv (nnreal_nat (Z.to_nat z + 1)))
             = Rdiv 1 (Z.to_nat z + 1)) as ->.
      { simpl.
        rewrite /Rdiv/= Rmult_1_l.
        do 2 f_equal.
        rewrite plus_INR.
        f_equal.
       }
      apply (ub_lift_rand_err_nat (Z.to_nat z) z σ1); auto.
    - intros [] (n & Hn1 & [=]). simplify_eq.
      eauto.
  }
  iIntros ((e2 & σ2)) "%H".
  destruct H as (n & Hn1 & [=]); simplify_eq.
  iPoseProof (ec_decrease_supply) as "Hdec".
  iSpecialize ("Hdec" with "Hε Herr"); eauto.
  do 2 iModIntro.
  iMod "Hclose'".
  iMod "Hdec".
  iFrame.
  iModIntro.
  iApply ub_wp_value.
  iApply "Hwp".
  done.
Qed.


Lemma wp_rand_err_list_nat (N : nat) (z : Z) (ns : list nat) E Φ :
  TCEq N (Z.to_nat z) →
  € (nnreal_div (nnreal_nat (length ns)) (nnreal_nat(N+1))) ∗
  (∀ x, ⌜Forall (λ m, x ≠ m) ns⌝ -∗ Φ #x)
  ⊢ WP rand #z from #() @ E {{ Φ }}.
Proof.
  iIntros (->) "[Herr Hwp]".
  iApply wp_lift_step_fupd_exec_ub; [done|].
  iIntros (σ1 ε) "[Hσ Hε]".
  iApply fupd_mask_intro; [set_solver|].
  iIntros "Hclose'".
  solve_red.
  iDestruct (ec_supply_bound with "Hε Herr ") as %Hle.
  set (ε' := nnreal_minus ε (nnreal_div (nnreal_nat (length ns)) (nnreal_nat (Z.to_nat z + 1))) Hle ).
  replace ε with (nnreal_plus (nnreal_div (nnreal_nat (length ns)) (nnreal_nat (Z.to_nat z + 1))) ε'); last first.
  { apply nnreal_ext; simpl; lra. }
  iApply exec_ub_prim_step.
  iExists
      (λ (ρ : expr * state),
        ∃ (n : fin (S (Z.to_nat z))), Forall (λ m, fin_to_nat n ≠ m) ns /\ ρ = (Val #n, σ1)),_,_.
  iSplit.
  {
    iPureIntro; apply Rle_refl.
  }
  iSplit.
  {
    iPureIntro.
    eapply UB_mon_pred; last first.
    - assert (nonneg (nnreal_div (nnreal_nat (length ns)) (nnreal_nat (Z.to_nat z + 1)))
             = Rdiv (length ns) (Z.to_nat z + 1)) as ->.
      { simpl.
        rewrite /Rdiv/=.
        do 2 f_equal.
        rewrite plus_INR.
        f_equal.
       }
      apply (ub_lift_rand_err_list_nat (Z.to_nat z) z σ1); auto.
    - intros [] (n & Hn1 & [=]). simplify_eq.
      eauto.
  }
  iIntros ((e2 & σ2)) "%H".
  destruct H as (n & Hn1 & [=]); simplify_eq.
  iPoseProof (ec_decrease_supply) as "Hdec".
  iSpecialize ("Hdec" with "Hε Herr"); eauto.
  do 2 iModIntro.
  iMod "Hclose'".
  iMod "Hdec".
  iFrame.
  iModIntro.
  iApply ub_wp_value.
  iApply "Hwp".
  done.
Qed.


Lemma wp_rand_err_list_int (N : nat) (z : Z) (zs : list Z) E Φ :
  TCEq N (Z.to_nat z) →
  € (nnreal_div (nnreal_nat (length zs)) (nnreal_nat(N+1))) ∗
  (∀ x : Z , ⌜Forall (λ m, x ≠ m) zs⌝ -∗ Φ #x)
  ⊢ WP rand #z from #() @ E {{ Φ }}.
Proof.
  iIntros (->) "[Herr Hwp]".
  iApply wp_lift_step_fupd_exec_ub; [done|].
  iIntros (σ1 ε) "[Hσ Hε]".
  iApply fupd_mask_intro; [set_solver|].
  iIntros "Hclose'".
  solve_red.
  iDestruct (ec_supply_bound with "Hε Herr ") as %Hle.
  set (ε' := nnreal_minus ε (nnreal_div (nnreal_nat (length zs)) (nnreal_nat (Z.to_nat z + 1))) Hle ).
  replace ε with (nnreal_plus (nnreal_div (nnreal_nat (length zs)) (nnreal_nat (Z.to_nat z + 1))) ε'); last first.
  { apply nnreal_ext; simpl; lra. }
  iApply exec_ub_prim_step.
  iExists
      (λ (ρ : expr * state),
        ∃ (n : fin (S (Z.to_nat z))), Forall (λ m, Z.of_nat (fin_to_nat n) ≠ m) zs /\ ρ = (Val #n, σ1)),_,_.
  iSplit.
  {
    iPureIntro; apply Rle_refl.
  }
  iSplit.
  {
    iPureIntro.
    eapply UB_mon_pred; last first.
    - assert (nonneg (nnreal_div (nnreal_nat (length zs)) (nnreal_nat (Z.to_nat z + 1)))
             = Rdiv (length zs) (Z.to_nat z + 1)) as ->.
      { simpl.
        rewrite /Rdiv/=.
        do 2 f_equal.
        rewrite plus_INR.
        f_equal.
       }
      apply (ub_lift_rand_err_list_int (Z.to_nat z) z σ1); auto.
    - intros [] (n & Hn1 & [=]). simplify_eq.
      eauto.
  }
  iIntros ((e2 & σ2)) "%H".
  destruct H as (n & Hn1 & [=]); simplify_eq.
  iPoseProof (ec_decrease_supply) as "Hdec".
  iSpecialize ("Hdec" with "Hε Herr"); eauto.
  do 2 iModIntro.
  iMod "Hclose'".
  iMod "Hdec".
  iFrame.
  iModIntro.
  iApply ub_wp_value.
  iApply "Hwp".
  done.
Qed.


Lemma wp_couple_rand_adv_comp (N : nat) z E Φ (ε1 : nonnegreal) (ε2 : fin (S N) -> nonnegreal) :
  TCEq N (Z.to_nat z) →
  (exists r, ∀ n, (ε2 n <= r)%R) →
  SeriesC (λ n, (1 / (S N)) * ε2 n)%R = (nonneg ε1) →
  {{{ € ε1 }}} rand #z from #() @ E {{{ n, RET #n; € (ε2 n) }}}.
Proof.
  iIntros (-> (r & Hε2) Hε1 Ψ) "Herr HΨ".
  iApply wp_lift_step_fupd_exec_ub; [done|].
  iIntros (σ1 ε_now) "[Hσ Hε]".
  iApply fupd_mask_intro; [set_solver|].
  iIntros "Hclose'".
  solve_red.
  iApply exec_ub_adv_comp; simpl.
  iDestruct (ec_split_supply with "Hε Herr") as (ε3) "%Hε3".
  rewrite Hε3.
  set (foo := (λ (ρ : expr * state),
                ε3 +
          match ρ with
            | (Val (LitV (LitInt n)), σ1) =>
                if bool_decide (0 ≤ n)%Z
                then match (lt_dec (Z.to_nat n) (S (Z.to_nat z))) with
                       | left H => ε2 (@Fin.of_nat_lt (Z.to_nat n) (S (Z.to_nat z)) H)
                       | _ => nnreal_zero
                     end
                  else nnreal_zero
            | _ => nnreal_zero
          end)%NNR).
  iExists
      (λ (ρ : expr * state),
        ∃ (n : fin (S (Z.to_nat z))), ρ = (Val #n, σ1)), nnreal_zero, foo.
  iSplit.
  {
    iPureIntro. exists (ε3 + r)%R.
    intros (e & σ); simpl.
    apply Rplus_le_compat; [lra |].
    assert (nnreal_zero <= r)%R.
    { transitivity (ε2 0%fin); auto.
      apply cond_nonneg.
    }
    do 5 (case_match; auto).
    apply Hε2.
  }
  iSplit.
  {
    iPureIntro.
    rewrite /foo /= Rplus_0_l.
    setoid_rewrite Rmult_plus_distr_l.
    rewrite SeriesC_plus.
    - rewrite Rplus_comm.
      apply Rplus_le_compat.
      + rewrite <- Hε1.
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
             apply Rmult_le_pos; [ | apply cond_nonneg ].
             apply Rmult_le_pos; [lra |].
             left. apply RinvN_pos'.
          ** intros ρ1 ρ2 m Hc1 Hc2.
             do 14 (case_match; simplify_eq).
             f_equal.
             *** do 3 f_equal.
                 admit.
             *** apply bool_decide_eq_true_1 in H2.
                 apply bool_decide_eq_true_1 in H.
                 simplify_eq. done.
          ** apply ex_seriesC_finite.
        * apply SeriesC_le.
          ** intros []; split.
             *** apply Rmult_le_pos; auto.
                 case_match; (try apply cond_nonneg).
             *** case_bool_decide; simplify_eq.
                 **** do 5 (case_match; simpl; (try (rewrite Rmult_0_r; lra))).
                      apply Rmult_le_compat_r; [ apply cond_nonneg |].
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
                      apply Rmult_le_compat_r; [apply cond_nonneg | ].
                      right.
                      rewrite head_prim_step_eq /=.
                      rewrite /dmap /pmf/=/dbind_pmf/dunifP.
                      setoid_rewrite dunif_pmf.
                      rewrite SeriesC_scal_l /= /Rdiv.
                      erewrite (SeriesC_ext _ (λ _, 0));
                        [rewrite SeriesC_0; auto; by rewrite Rmult_0_r|].
                      intro; rewrite dret_0; auto.
                      intro; simplify_eq.
          ** admit.
      + rewrite SeriesC_scal_r.
        rewrite <- Rmult_1_l.
        apply Rmult_le_compat; auto; try lra.
        apply cond_nonneg.
    - by apply ex_seriesC_scal_r.
    - admit.
  }
  iSplit.
  {
    iPureIntro.
    eapply UB_mon_pred; last first.
    - apply (ub_lift_rand_trivial (Z.to_nat z) z σ1); auto.
    - done.
  }
  iIntros ((e2 & σ2)) "%H".
  destruct H as (n & Hn1); simplify_eq.
  rewrite /foo /=.
  rewrite bool_decide_eq_true_2; last first.
  {
    by zify.
  }
  case_match.
  2:{
    destruct n0.
    rewrite Nat2Z.id.
    apply fin_to_nat_lt.
  }
  iMod (ec_decrease_supply with "Hε Herr") as "Hε2".
  do 2 iModIntro.
  iMod "Hclose'".
  iFrame.
  iMod (ec_increase_supply _ (ε2 (nat_to_fin l)) with "Hε2") as "[Hε2 Hfoo]".
  iFrame. iModIntro. wp_pures.
  iModIntro. iApply "HΨ".
  assert (nat_to_fin l = n) as ->; [|done].
  apply fin_to_nat_inj.
  rewrite fin_to_nat_to_fin.
  rewrite Nat2Z.id.
  reflexivity.
Admitted.

End rules.

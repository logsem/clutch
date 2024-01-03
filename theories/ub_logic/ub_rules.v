(** * Union bound rules  *)
From stdpp Require Import namespaces finite.
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
    (prim_step (rand #z) σ1)
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
    (prim_step (rand #z) σ1)
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
    (prim_step (rand #z) σ1)
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
    (prim_step (rand #z) σ1)
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
    (prim_step (rand #z) σ1)
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
  ⊢ WP rand #z @ E {{ Φ }}.
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
  ⊢ WP rand #z @ E {{ Φ }}.
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
  ⊢ WP rand #z @ E {{ Φ }}.
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
  ⊢ WP rand #z @ E {{ Φ }}.
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

(* FIXME: where should this go (if anywhere?) *)
Lemma match_nonneg_coercions (n : nonnegreal) : NNRbar_to_real (NNRbar.Finite n) = nonneg n.
Proof. by simpl. Qed.

Lemma mean_constraint_ub (N : nat) ε1 (ε2 : fin (S N) -> nonnegreal) :
  SeriesC (λ n, (1 / (S N)) * ε2 n)%R = (nonneg ε1) ->
  (exists r, (0 <= r)%R /\ ∀ n,(ε2 n <= r)%R).
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
    (* simpl does too much here and I can't figure out how to stop it *)
    replace (nonneg {| nonneg := INR (S N); cond_nonneg := _ |}) with (INR (S N)); [| by simpl ].
    apply not_0_INR.
    auto.
  - rewrite -match_nonneg_coercions.
    rewrite -(SeriesC_singleton_dependent _ ε2).
    apply SeriesC_le.
    + intros n'.
      assert (H : (0 <= (nonneg (ε2 n')))%R) by apply cond_nonneg.
      rewrite /nnreal_zero /=.
      case_bool_decide; try lra.
    + apply ex_seriesC_finite.
Qed.




Lemma wp_couple_rand_adv_comp (N : nat) z E Φ (ε1 : nonnegreal) (ε2 : fin (S N) -> nonnegreal) :
  TCEq N (Z.to_nat z) →
  (exists r, ∀ n, (ε2 n <= r)%R) →
  SeriesC (λ n, (1 / (S N)) * ε2 n)%R = (nonneg ε1) →
  {{{ € ε1 }}} rand #z @ E {{{ n, RET #n; € (ε2 n) }}}.
Proof.
  iIntros (-> (r & Hε2) Hε1 Ψ) "Herr HΨ".
  iApply wp_lift_step_fupd_exec_ub; [done|].
  iIntros (σ1 ε_now) "[Hσ Hε]".
  iApply fupd_mask_intro; [set_solver|].
  iIntros "Hclose'".
  solve_red.
  iApply exec_ub_adv_comp; simpl.
  iDestruct (ec_split_supply with "Hε Herr") as (ε3) "%Hε3".
  (* ε3 is the amount of credit supply left outside of ε1 (?) *)
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



(** * Approximate Lifting *)
(* FIXME: clean up *)
Lemma ub_lift_state (N : nat) 𝜎 𝛼 ns :
  𝜎.(tapes) !! 𝛼 = Some (N; ns) →
  ub_lift
    (state_step 𝜎 𝛼)
    (fun 𝜎' => exists (n : fin (S N)), 𝜎' = state_upd_tapes <[𝛼 := (N; ns ++ [n])]> 𝜎)
    nnreal_zero.
Proof.
  rewrite /ub_lift.
  intros Htapes P Hp.
  apply Req_le_sym; simpl.
  rewrite /prob SeriesC_0; auto.
  intros 𝜎'.
  remember (negb (P 𝜎')) as K; destruct K; auto.
  rewrite /state_step.
  case_bool_decide.
  2: { exfalso. apply H. by apply elem_of_dom. }
  intros.
  replace (lookup_total 𝛼 (tapes 𝜎)) with (N; ns).
  2: { rewrite (lookup_total_correct _ _ (existT N ns)); auto.  }
  apply dmap_unif_zero.
  intros n Hcont.
  apply diff_true_false.
  specialize Hp with 𝜎'.
  rewrite -Hp; [| by exists n].
  replace false with (negb true) by auto.
  by rewrite HeqK negb_involutive.
Qed.

(** adapted from wp_couple_tapes in the relational logic *)
Lemma wp_presample (N : nat) E e 𝛼 ns Φ :
  to_val e = None →
  (∀ σ', reducible e σ') →
  ▷ 𝛼 ↪ (N; ns) ∗
  (∀ (n : fin (S N)), 𝛼 ↪ (N; ns ++ [n]) -∗ WP e @ E {{ Φ }})
  ⊢ WP e @ E {{ Φ }}.
Proof.
    iIntros (He Hred) "(>H𝛼&Hwp)".
    iApply wp_lift_step_fupd_exec_ub; [done|].
    iIntros (𝜎 ε) "((Hheap&Htapes)&Hε)".
    iDestruct (ghost_map_lookup with "Htapes H𝛼") as %Hlookup.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iSplitR; [done|].
    (* now we need to prove an exec_ub, we should be able to do this with a state step. *)
    replace ε with (nnreal_zero + ε)%NNR by (apply nnreal_ext; simpl; lra).
    iApply exec_ub_state_step.
    { rewrite /= /get_active.
      by apply elem_of_list_In, elem_of_list_In, elem_of_elements, elem_of_dom. }
    iExists _.
    iSplit.
    { iPureIntro. apply ub_lift_state, Hlookup. }
    iIntros (𝜎') "[%n %H𝜎']".
    (* now we have to prove the exec_ub about 𝜎', we should be able to do this with the wp *)
    (* first: udpate the resources *)
    iDestruct (ghost_map_lookup with "Htapes H𝛼") as %?%lookup_total_correct.
    iMod (ghost_map_update ((N; ns ++ [n]) : tape) with "Htapes H𝛼") as "[Htapes H𝛼]".
    iMod "Hclose'" as "_". (* ?? *)
    iSpecialize ("Hwp" $! n with "H𝛼").
    rewrite !ub_wp_unfold /ub_wp_pre /= He.
    iSpecialize ("Hwp" $! 𝜎' ε).
    iMod ("Hwp" with "[Hheap Htapes Hε]") as "(?&Hwp)".
    { replace (nnreal_zero + ε)%NNR with ε by (apply nnreal_ext; simpl; lra).
      rewrite H𝜎'.
      iFrame.
    }
    iModIntro. iApply "Hwp".
Qed.



(* old (broken?) version *)
Definition compute_ε2_in_state (ρ : expr * state) N z (ε2 : fin (S N) -> nonnegreal) (_ : TCEq N (Z.to_nat z)) : nonnegreal.
refine(
  match ρ with
  | (Val (LitV (LitInt n)), σ) =>
      if bool_decide (0 <= n)%Z
      then match (lt_dec (Z.to_nat n) (S (Z.to_nat z))) with
             | left H => ε2 (@Fin.of_nat_lt (Z.to_nat n) _ _)
             | _ => nnreal_zero
            end
      else nnreal_zero
  | _ => nnreal_zero
  end).
  eapply Nat.le_trans.
  - apply Nat.le_succ_l, H.
  - apply Nat.eq_le_incl, eq_S. symmetry. by apply TCEq_eq.
Defined.


Lemma compute_ε2_in_state_expr e σ N z ε2 H :
  to_val e = None ->
  compute_ε2_in_state (e, σ) N z ε2 H = nnreal_zero.
Proof.
  intros; rewrite /compute_ε2_in_state; simpl.
  case_match; auto.
  simplify_eq.
Qed.


Check (fun (s : state) => s.(tapes)).
Check (fun α z ns sample=> (state_upd_tapes <[α:=(Z.to_nat z; ns ++ [sample]) : tape]> )).
Check (fun σ σ' α z ns N => (exists s : fin _, σ' = (state_upd_tapes <[α:=(Z.to_nat z; ns ++ [s]) : tape]> σ))).
Check (fun σ σ' α z ns N =>
            match exists_dec (fun s : fin _ => σ' = (state_upd_tapes <[α:=(Z.to_nat z; ns ++ [s]) : tape]> σ)) with
                | left H => _ H
                | right H => nnreal_zero
              end).

(* I'll admit this for now to see if the rest of the proof works  *)

(* really this should not depend on the expr at all :/*)


Definition compute_ε2 (σ : state) (ρ : cfg) α N ns (ε2 : fin (S N) -> nonnegreal) : nonnegreal :=
  match finite.find (fun s => state_upd_tapes <[α:=(N; ns ++ [s]) : tape]> σ = snd ρ) with
    | Some s => ε2 s
    | None => nnreal_zero
  end.


Lemma wp_presample_adv_comp (N : nat) α (ns : list (fin (S N))) z e E Φ (ε1 : nonnegreal) (ε2 : fin (S N) -> nonnegreal) :
  E = ∅ -> (* can this really only be proven when E = ∅ or can we improve this? *)
  TCEq N (Z.to_nat z) →
  to_val e = None →
  (∀ σ', reducible e σ') →
  SeriesC (λ n, (1 / (S N)) * ε2 n)%R = (nonneg ε1) →
  α ↪ (N; ns) ∗
  € ε1 ∗
  (∀ (n : fin (S N)), € (ε2 n) ∗ α ↪ (N; ns ++ [n]) -∗ WP e @ E {{ Φ }})
  ⊢ WP e @ E {{ Φ }}.
Proof.
  iIntros (? -> Hred Hσ_red Hsum) "(Hα & Hε & Hwp)".
  iApply wp_lift_step_fupd_exec_ub; [done|].
  iIntros (σ1 ε_now) "[(Hheap&Htapes) Hε_supply]".
  iDestruct (ghost_map_lookup with "Htapes Hα") as %Hlookup.
  iDestruct (ec_supply_bound with "Hε_supply Hε") as %Hε1_ub.
  iApply fupd_mask_intro; [set_solver|].
  iIntros "Hclose".
  iSplitR; [auto|].
  iApply (exec_ub_state_adv_comp' α); simpl.
  { rewrite /get_active.
    apply elem_of_list_In, elem_of_list_In, elem_of_elements, elem_of_dom.
    done. }
  iDestruct (ec_split_supply with "Hε_supply Hε") as (ε_rem) "%Hε_supply".
  rewrite Hε_supply.

  (* R: predicate should hold iff tapes σ' at α is ns ++ [n] *)
  iExists
    (fun σ' : state => exists n : fin _, σ' = (state_upd_tapes <[α:=(_; ns ++ [n]) : tape]> σ1)),
    (fun ρ => (ε_rem + compute_ε2 σ1 ρ α _ ns ε2)%NNR).

  (* upper bound *)
  iSplit.
  { iPureIntro.
    destruct (mean_constraint_ub _ _ _ Hsum) as [r [Hr_nonneg Hr_ub]].
    assert (Hr_nnonneg : (0 <= r)%R).
    { eapply Rle_trans; [|apply (Hr_ub 0%fin)].
      rewrite match_nonneg_coercions.
      apply cond_nonneg. }
    exists (ε_rem + r)%R.
    intros [e' σ'].
    apply Rplus_le_compat_l.
    rewrite /compute_ε2.
    destruct (finite.find _); auto; apply Hr_ub.
  }

  iSplit.
  { iPureIntro. simpl.
    rewrite -Hsum.

    (* first: deal with the ε_rem term *)
    setoid_rewrite Rmult_plus_distr_l.
    rewrite SeriesC_plus.

    2: { apply ex_seriesC_scal_r, pmf_ex_seriesC. }
    2: { apply pmf_ex_seriesC_mult_fn.
         destruct (mean_constraint_ub _ _ _ Hsum) as [r [Hr_nonneg Hr_ub]].
         exists r; intros; split.
          - apply cond_nonneg.
          - rewrite /compute_ε2.
            destruct (finite.find _).
            + apply Hr_ub.
            + simpl; apply Hr_nonneg.
    }

    rewrite -Rplus_comm; apply Rplus_le_compat; last first.
    { (* true because state_step is a pmf so is lt 1 *)
      rewrite SeriesC_scal_r -{2}(Rmult_1_l (nonneg ε_rem)).
      apply Rmult_le_compat; try auto; [apply cond_nonneg | lra]. }

    (* now we make an injection: we rewrite the lhs series to use a from_option *)
    pose f := (fun n : fin _ => 1 / S (Z.to_nat z) * ε2 n)%R.
    rewrite (SeriesC_ext
               (λ x : state, state_step σ1 α x * compute_ε2 σ1 (e, x) α (Z.to_nat z) ns ε2)%R
               (fun x : state => from_option f 0
                                (finite.find (fun n => state_upd_tapes <[α:=(_; ns ++ [n]) : tape]> σ1 = x ))%R));
      last first.
    { intros n.
      rewrite /compute_ε2.
      remember (finite.find _) as F.
      destruct F as [sf|].
      - Opaque INR.
        symmetry in HeqF.
        apply find_Some in HeqF.
        simpl in HeqF; rewrite -HeqF.
        rewrite /from_option /f.
        apply Rmult_eq_compat_r.
        rewrite /state_upd_tapes /=.
        rewrite /pmf.
        rewrite /state_step.
        rewrite bool_decide_true; last first.
        { rewrite elem_of_dom Hlookup /= /is_Some.
          by exists (Z.to_nat z; ns). }
        rewrite (lookup_total_correct _ _ (Z.to_nat z; ns)); auto.
        rewrite /dmap /dbind /dbind_pmf /pmf.
        rewrite /= SeriesC_scal_l -{1}(Rmult_1_r (1 / _))%R.
        rewrite /Rdiv Rmult_1_l; apply Rmult_eq_compat_l.
        (* then show that this series is 0 unless a = sf *)
        rewrite /dret /dret_pmf.
        rewrite -{2}(SeriesC_singleton sf 1%R).
        apply SeriesC_ext; intros.
        symmetry.
        case_bool_decide; simplify_eq.
        + rewrite bool_decide_true; auto.
        + rewrite bool_decide_false; auto.
          rewrite /not; intros K.
          rewrite /not in H0; apply H0.
          rewrite /state_upd_tapes in K.

          assert (R1 : ((Z.to_nat z; ns ++ [sf]) : tape) = (Z.to_nat z; ns ++ [n0])).
          { apply (insert_inv (tapes σ1) α).
            by inversion K.
          }

          (* FIXME: same problem as below: is classical logic really necessary here? *)
          apply classic_proof_irrel.PIT.EqdepTheory.inj_pair2, app_inv_head in R1.
          by inversion R1.
          Transparent INR.
      - rewrite /from_option /INR /=. lra.
    }

    apply SeriesC_le_inj.
    - (* f is nonnegative *)
      intros.
      apply Rmult_le_pos.
      + rewrite /Rdiv.
        apply Rmult_le_pos; try lra.
        apply Rlt_le, Rinv_0_lt_compat, pos_INR_S.
      + apply cond_nonneg.
    - (* injection *)
      intros ? ? ? HF1 HF2.
      apply find_Some in HF1.
      apply find_Some in HF2.
      by rewrite -HF1 -HF2.
    - (* existence *)
      apply ex_seriesC_finite.
  }

  (* lifted lookup on tapes *)
  iSplit.
  {
    iPureIntro.
    eapply UB_mon_pred; last first.
    - apply ub_lift_state. apply Hlookup.
    - done.
  }

  iIntros ((heap2 & tapes2)) "[%sample %Hsample]".
  iMod (ec_decrease_supply with "Hε_supply Hε") as "Hε_supply".
  iMod (ec_increase_supply _ (ε2 sample) with "Hε_supply") as "[Hε_supply Hε]".
  iMod (ghost_map_update ((Z.to_nat z; ns ++ [sample]) : tape) with "Htapes Hα") as "[Htapes Hα]".
  iSpecialize ("Hwp" $! sample).

  (* open the WP and specialize it to get the goal *)
  rewrite ub_wp_unfold /ub_wp_pre.
  iAssert (⌜ (common.language.to_val e) = None ⌝)%I as "%X". { auto. }
  rewrite X; clear X.
  (* then we should be able to specialize using the updated ghost state.. *)

  iAssert (⌜reducible e {| heap := heap2; tapes := tapes2 |}⌝ ={∅,E}=∗ emp)%I with "[Hclose]" as "HcloseW".
  { iIntros; iFrame. }

  iPoseProof (fupd_trans_frame E ∅ E _ (⌜reducible e {| heap := heap2; tapes := tapes2 |}⌝))%I as "HR".
  iSpecialize ("HR" with "[Hwp Hheap Hε_supply Hε Htapes Hα HcloseW]").
  { iFrame.
    iApply ("Hwp" with "[Hε Hα]"). { iFrame. }
    rewrite /state_interp /=.
    rewrite /state_upd_tapes in Hsample.
    inversion Hsample.
    iFrame. }

  rewrite Hsample /compute_ε2 /=.
  destruct (@find_is_Some _ _ _
               (λ s : fin (S (Z.to_nat z)), state_upd_tapes <[α:=(Z.to_nat z; ns ++ [s])]> σ1 = state_upd_tapes <[α:=(Z.to_nat z; ns ++ [sample])]> σ1)
               _ sample eq_refl)
            as [r [Hfind Hr]].
  rewrite Hfind.
  replace r with sample; last first.
  { rewrite /state_upd_tapes in Hr.
    (* again: I want to destruct this equality *)
    inversion Hr as [Heqt].
    apply (insert_inv (tapes σ1) α) in Heqt.
    (* FIXME is there a way around using clasical theorem here?
       Search ((_; ?X) = (_; ?Y)) (?X = ?Y).
       apply eq_sigT_eq_dep in Heqt.
       apply eq_dep_non_dep in Heqt. *)
    apply classic_proof_irrel.PIT.EqdepTheory.inj_pair2 in Heqt.
    apply app_inv_head in Heqt.
    by inversion Heqt. }

  iApply fupd_mask_mono; last done.

  (* FIXME I can't see where this could be improved in the proof, but I also see no reason why it could't.
      (related to the prophecy counterexample? idk. )*)
  set_solver.
Qed.


(*
Lemma ec_spend_irrel ε1 ε2 : (ε1.(nonneg) = ε2.(nonneg)) → € ε1 -∗ € ε2.
Proof.
  iIntros (?) "?".
  replace ε1 with ε2; first by iFrame.
  by apply nnreal_ext.
Qed.

Lemma ec_spend_1 ε1 : (1 <= ε1.(nonneg))%R → € ε1 -∗ False.
Proof. Admitted.

(** advanced composition on one tape *)
(* not really sure what this lemma will look like in the real version? *)
Lemma presample_adv_comp (N : nat) α ns (ε : nonnegreal) (ε2 : fin (S N) -> nonnegreal) :
  SeriesC (λ n, (1 / (S N)) * ε2 n)%R = (nonneg ε) →
  (α ↪ (N; ns) ∗ € ε) -∗ (∃ s, (α ↪ (N; ns ++ [s])) ∗ €(ε2 s)).
Proof. Admitted.

Lemma amplification_depth N L (ε : posreal) (kwf : kwf N L) : exists n : nat, (1 <= ε * (k N L kwf) ^ n)%R.
Proof.
  (* shouldn't be too hard, it's the log *)
Admitted.


Lemma lookup_ex {A} (n : nat) (L : list A) : (n < length L)%nat -> exists x, (L !! n) = Some x.
Proof.
  (* can't figure out how to do this with existing lemmas! *)
  intros HL.
  destruct L as [|h H]; [simpl in HL; lia|].
  generalize dependent H. generalize dependent h.
  induction n as [|n' IH].
  - intros h ? ?. exists h; by simpl.
  - intros h H HL.
    rewrite cons_length in HL; apply Arith_prebase.lt_S_n in HL.
    destruct H as [|h' H']; [simpl in HL; lia|].
    replace ((h :: h' :: H') !! S n') with ((h' :: H') !! n'); last by simpl.
    by apply IH.
Qed.


(* whenever i is strictly less than l (ie, (S i) <= l) we can amplify *)
(* we'll need another rule for spending?, but that should be simple *)
Lemma presample_amplify' N L kwf prefix (suffix_total suffix_remaining : list (fin (S N))) 𝛼 (ε : posreal) :
  ⊢ ⌜ L = length suffix_total ⌝ →
    ⌜ (0 < L)%nat ⌝ →
    𝛼 ↪ (N; prefix) -∗
    (€ (pos_to_nn ε)) -∗
    ∀ (i : nat),
      (∀ (HL : (i <= L)%nat),
          (∃ junk, 𝛼 ↪ (N; prefix ++ junk) ∗ €(εAmp N L ε kwf)) ∨
          ((𝛼 ↪ (N; prefix ++ (take i suffix_total))) ∗
            € (εR N L i ε (mk_fRwf N L i kwf HL)))).
Proof.
  iIntros (Htotal HLpos) "Htape Hcr_initial"; iIntros (i).
  iInduction i as [|i'] "IH" forall (suffix_remaining).
  - iIntros (HL).
    iRight. iSplitL "Htape".
    + rewrite take_0 -app_nil_end. iFrame.
    + iApply ec_spend_irrel; last iFrame.
      rewrite /εR /fR /pos_to_nn /=; lra.
  - iIntros "%HL".
    assert (HL' : (i' <= L)%nat) by lia.
    iSpecialize ("IH" $! _ with "Htape Hcr_initial").
    iSpecialize ("IH" $! HL').
    iDestruct "IH" as "[[%junk(Htape&Hcr)]|(Htape&Hcr)]".
    + iLeft; iExists junk; iFrame.
    +
      (* we need to do something different dependning on if (S i') is L? No. in that case we still need 1 amp*)
      assert (Hi' : (i' < length suffix_total)%nat) by lia.
      destruct (lookup_ex i' suffix_total Hi') as [target Htarget].
      rewrite (take_S_r _ _ target); [|apply Htarget].
      pose M := (εDistr_mean N L i' ε target (mk_fRwf N L (S i') kwf HL)).
      iPoseProof (presample_adv_comp N 𝛼
                   (prefix ++ take i' suffix_total)
                   (εR N L i' ε (fRwf_dec_i N L i' _)) (εDistr N L i' ε target _) M) as "PS".
      replace {| k_wf := kwf; i_ub := HL' |} with(fRwf_dec_i N L i' {| k_wf := kwf; i_ub := HL |});
        last by apply fRwf_ext.
      iSpecialize ("PS" with "[Htape Hcr]"); first iFrame.
      iDestruct "PS" as "[%s (Htape&Hcr)]".
      (* NOW we can destruct and decide if we're left or right *)
      rewrite /εDistr.
      case_bool_decide.
      * iRight. rewrite H app_assoc. iFrame.
      * iLeft. iExists (take i' suffix_total ++ [s]).
        replace (k_wf N L (S i') {| k_wf := kwf; i_ub := HL |}) with kwf; last by apply kwf_ext.
        rewrite -app_assoc; iFrame.
    Unshelve. auto.
Qed.

(* do one step in the amplification sequence *)
Lemma presample_amplify N L prefix suffix 𝛼 (ε : posreal) (kwf: kwf N L) :
  L = (length suffix) ->
  € (pos_to_nn ε) -∗
  (𝛼 ↪ (N; prefix)) -∗
  (𝛼 ↪ (N; prefix ++ suffix) ∨ (∃ junk, 𝛼 ↪ (N; prefix ++ junk) ∗ €(εAmp N L ε kwf))).
Proof.
  iIntros (Hl) "Hcr Htape".

  destruct suffix as [|s0 sr].
  - iLeft. rewrite -app_nil_end. iFrame.
  - remember (s0 :: sr) as suffix.
    assert (Hl_pos : (0 < L)%nat).
    { rewrite Hl Heqsuffix cons_length. lia. }
    iPoseProof (presample_amplify' N L _ prefix suffix suffix 𝛼 ε $! Hl Hl_pos) as "X".
    iSpecialize ("X" with "Htape Hcr").
    iSpecialize ("X" $! L (le_n L)).
    iDestruct "X" as "[H|(H&_)]".
    + iRight. iApply "H".
    + iLeft. rewrite Hl firstn_all. iFrame.
Qed.


Lemma seq_amplify N L d prefix suffix 𝛼 (ε : posreal) (kwf: kwf N L) :
  L = (length suffix) ->
  € (pos_to_nn ε) -∗
  (𝛼 ↪ (N; prefix)) -∗
  (∃ junk,
      𝛼 ↪ (N; prefix ++ junk ++ suffix) ∨ 𝛼 ↪ (N; prefix ++ junk) ∗ €(pos_to_nn (εAmp_iter N L d ε kwf))).
Proof.
  iIntros (HL) "Hcr Htape".
  iInduction (d) as [|d'] "IH".
  - iExists []; rewrite app_nil_r. iRight. iFrame.
    iApply ec_spend_irrel; last auto.
    by rewrite /εAmp_iter /pos_to_nn /= Rmult_1_r.
  - iDestruct ("IH" with "Hcr Htape") as "[%junk [Hlucky|(Htape&Hcr)]]".
    + iExists junk; iLeft; iFrame.
    + rewrite -εAmp_iter_cmp.
      iPoseProof (presample_amplify N L (prefix ++ junk) suffix 𝛼 (εAmp_iter N L d' ε kwf)) as "X"; try auto.
      iDestruct ("X" with "Hcr Htape") as "[Hlucky|[%junk' (Htape&Hcr)]]".
      * iExists junk; iLeft. rewrite -app_assoc; iFrame.
      * iExists (junk ++ junk'); iRight.
        rewrite app_assoc; iFrame.
Qed.


Lemma presample_planner_pos N prefix suffix 𝛼 ε (HN : (0 < N)%nat) (HL : (0 < (length suffix))%nat) (Hε : (0 < ε)%R) :
  € ε -∗
  (𝛼 ↪ (N; prefix)) -∗
  (∃ junk, 𝛼 ↪ (N; prefix ++ junk ++ suffix)).
Proof.
  iIntros "Hcr Htape".
  (* make the interface match the other coupling rules *)
  remember (length suffix) as L.
  assert (kwf : kwf N L). { apply mk_kwf; lia. }
  pose ε' := mkposreal ε.(nonneg) Hε.
  replace ε with (pos_to_nn ε'); last first.
  { rewrite /ε' /pos_to_nn. by apply nnreal_ext. }

  destruct (amplification_depth N L ε' kwf) as [d Hdepth].
  iDestruct ((seq_amplify N L d prefix suffix 𝛼 ε' kwf) with "Hcr Htape") as "[%junk [?|(_&Hcr)]]"; auto.
  iExFalso; iApply ec_spend_1; last iFrame.
  Set Printing Coercions.
  rewrite /pos_to_nn /εAmp_iter /=.
  replace (nonneg ε) with (pos ε') by auto.
  done.
Qed.

Lemma presample_planner N prefix suffix 𝛼 ε (Hε : (0 < ε)%R) :
  € ε -∗
  (𝛼 ↪ (S N; prefix)) -∗
  (∃ junk, 𝛼 ↪ (S N; prefix ++ junk ++ suffix)).
Proof.
  destruct suffix as [|h R].
  - iIntros "_ Htape". iExists []. do 2 (rewrite -app_nil_end); iFrame.
  - remember (h :: R) as suffix.
    iApply presample_planner_pos; auto; try lia.
    rewrite Heqsuffix cons_length.
    lia.
Qed.
*)

End rules.

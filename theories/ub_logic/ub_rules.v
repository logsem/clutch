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

(* FIXME: merge me from other branch *)
Lemma SeriesC_singleton_dependent `{Countable A} (a : A) (v : A -> nonnegreal) :
  SeriesC (λ n, if bool_decide (n = a) then v n else nnreal_zero) = nonneg (v a).
Proof.  Admitted.

Lemma mean_constraint_ub (N : nat) ε1 (ε2 : fin (S N) -> nonnegreal) :
  SeriesC (λ n, (1 / (S N)) * ε2 n)%R = (nonneg ε1) ->
  (exists r, ∀ n, (ε2 n <= r)%R).
Proof.
  intros Hsum.
  exists (nnreal_nat (S N) * ε1)%NNR.
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
  - rewrite -(SeriesC_singleton_dependent _ ε2).
    apply SeriesC_le.
    + intros n'.
      assert (H : (0 <= (nonneg (ε2 n')))%R) by apply cond_nonneg.
      rewrite /nnreal_zero /=.
      case_bool_decide; try lra.
    + apply ex_seriesC_finite.
Qed.


Lemma match_nonneg_coercions (n : nonnegreal) : NNRbar_to_real (NNRbar.Finite n) = nonneg n.
Proof. by simpl. Qed.


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



Lemma wp_presample_adv_comp (N : nat) α (ns : list (fin (S N))) z e E Φ (ε1 : nonnegreal) (ε2 : fin (S N) -> nonnegreal) :
  TCEq N (Z.to_nat z) →
  to_val e = None →
  (∀ σ', reducible e σ') →
  SeriesC (λ n, (1 / (S N)) * ε2 n)%R = (nonneg ε1) →
  ▷ α ↪ (N; ns) ∗
  € ε1 ∗
  (∀ (n : fin (S N)), € (ε2 n) ∗ α ↪ (N; ns ++ [n]) -∗ WP e @ E {{ Φ }})
  ⊢ WP e @ E {{ Φ }}.
Proof.
  iIntros (-> Hred Hσ_red Hsum) "(Hα & Hε & Hwp)".
  iApply wp_lift_step_fupd_exec_ub; [done|].
  iIntros (σ1 ε_now) "[Hσ_interp Hε_interp]".
  iApply fupd_mask_intro; [set_solver|].
  iIntros "Hclose'".
  iSplitR; [auto|].
  iApply (exec_ub_state_adv_comp' α); simpl.
  { (* should be able to prove α is active since we have α ↪ _ right? *) admit. }
  (* split supply by ε1*)
  iDestruct (ec_split_supply with "Hε_interp Hε") as (ε3) "%Hε3".
  rewrite Hε3.

  (* R: predicate should hold iff tapes σ' at α is ns ++ [n] *)
  iExists (fun σ' : state => exists n : fin _, σ' = (state_upd_tapes <[α:=(_; ns ++ [n]) : tape]> σ1)).
  (* ε2: lifted version of ε2 to states *)
  iExists (fun ρ => (ε3 + compute_ε2_in_state ρ _ z ε2 _)%NNR).

  (* upper bound *)
  iSplit.
  { iPureIntro.
    destruct (mean_constraint_ub _ _ _ Hsum) as [r Hr].
    assert (Hr_nnonneg : (0 <= r)%R).
    { eapply Rle_trans; [|apply (Hr 0%fin)].
      rewrite match_nonneg_coercions.
      apply cond_nonneg. }
    eexists (ε3 + r)%R.
    intros [e' σ'].
    apply Rplus_le_compat_l.
    rewrite /compute_ε2_in_state.
    destruct e'; try (simpl; lra).
    destruct v; try (simpl; lra).
    destruct l; try (simpl; lra).
    case_bool_decide; try (simpl; lra).
    destruct (lt_dec _ _); try (simpl; lra).
    remember (nat_to_fin _) as n'.
    rewrite -match_nonneg_coercions.
    apply (Hr n').
  }

  iSplit.
  { iPureIntro.
    rewrite /compute_ε2_in_state /=.
    setoid_rewrite Rmult_plus_distr_l.
    admit. (* what am I even using ε3 for again??? *)
  }

  assert (Htape_state: tapes σ1 !! α = Some (N; ns)) by admit.

  (* lifted lookup on tapes *)
  iSplit.
  {
    iPureIntro.
    eapply UB_mon_pred; last first.
    - apply ub_lift_state. apply Htape_state.
    - done.
  }

  (* finally update the wp *)
  iIntros ((e2 & σ2)) "[%n Hn1]"; simplify_eq.
  (* I should be able to use Hwp here, since we've now chosen a sample *)
  (* I need to get rid of that exec modality somehow, anyways. *)
  iSpecialize ("Hwp" $! n).
  rewrite /compute_ε2_in_state /=.
  admit.
Admitted.

(*

  iSplit.
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
*)

End rules.

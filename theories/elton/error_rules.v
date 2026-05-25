(** * Elton error bound rules rules  *)
From stdpp Require Import namespaces finite fin_sets.
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext.
From clutch.delay_prob_lang Require Import notation tactics metatheory.
From clutch.delay_prob_lang Require Export lang.
From clutch.elton Require Export lifting proofmode ectx_lifting primitive_laws. 

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
  case_match; last first.
  { exfalso.
    rename select (¬ _) into Hcontra.
    apply Hcontra.
    eexists _.
    by apply urn_subst_equal_obv.
  }
  erewrite urn_subst_equal_epsilon_unique; last done.
  rewrite /dmap -Hz.
  rewrite -(Rplus_0_r 0).
  eapply (pgl_dbind _ _ _ _ _ 0);
    [done|done| |by apply pgl_trivial].
  intros n ?.
  apply pgl_dret.
  by exists n.
Qed.

End metatheory.

Section rules.
  Context `{!eltonGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types v : val.
  Implicit Types l : loc.

  Local Opaque INR.
Lemma wp_couple_rand_adv_comp (N : nat) z E (ε1 : R) (ε2 : fin (S N) -> R) :
  TCEq N (Z.to_nat z) →
  (∀ n, (0 <= ε2 n)%R) ->
  (SeriesC (λ n, (1 / (S N)) * ε2 n)%R = ε1)%R →
  {{{ ↯ ε1 }}} rand #z @ E {{{ n, RET #n; ↯ (ε2 n) }}}.
Proof.
  iIntros (-> Hε2leq Hε1 Ψ) "Herr HΨ".
  destruct (fin_function_bounded _ ε2) as [r Hε2].
  iApply wp_lift_step_fupd_glm.
  iIntros (σ1 ε_now) "[Hσ Hε]".
  iApply fupd_mask_intro; [set_solver|].
  iIntros "Hclose'".
  iApply state_step_coupl_ret.
  iApply prog_coupl_adv_comp; simpl; first (iModIntro; iIntros; by iApply state_step_coupl_ret_err_ge_1).
  (* iDestruct (ec_supply_bound with "Hε Herr") as %?. *)
  iDestruct (ec_supply_ec_inv with "Hε Herr") as %(ε1' & ε3 & Hε_now & Hε1').
  unshelve eset (foo := (λ (ρ : expr * state),
                ε3 +
                  match ρ with
                  | (Val (LitV (LitInt n)), σ) =>
                      if bool_decide(σ = σ1)
                      then if bool_decide (0 ≤ n)%Z
                           then match (lt_dec (Z.to_nat n) (S (Z.to_nat z))) with
                                | left H => mknonnegreal (ε2 (@Fin.of_nat_lt (Z.to_nat n) (S (Z.to_nat z)) H)) _
                                | _ => nnreal_zero
                                end
                           else nnreal_zero
                      else nnreal_zero
                  | _ => nnreal_zero
                  end)%NNR); first naive_solver.
  iExists
    (λ ρ,
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
    do 6 (case_match; auto);
    apply Hε2.
  }
  iSplit.
  {
    iPureIntro.
    rewrite /Expval.
    rewrite /foo Rplus_0_l.
    setoid_rewrite Rmult_plus_distr_l.
    rewrite SeriesC_plus.
    - rewrite Rplus_comm.
      subst.
      apply Rplus_le_compat.
      + erewrite Hε1'.
        etrans; last first.
        * apply (SeriesC_le_inj _
                   (λ ρ : expr * state,
                       let '(e, σ) := ρ in
                       if bool_decide (σ = σ1) then
                         match (e) with
                         | (Val #(LitInt n)) =>
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
             apply Rmult_le_pos; [ | done ].
             apply Rmult_le_pos; [lra |].
             left. apply RinvN_pos'.
          ** intros ρ1 ρ2 m Hc1 Hc2.
             do 14 ((case_bool_decide || case_match); simplify_eq).
             f_equal.
             do 4 f_equal.
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
                      apply Rmult_le_compat_r; [ done |].
                      rewrite head_prim_step_eq /=.
                      case_match; last first.
                      { exfalso. rename select (¬ _) into Hcontra.
                        apply Hcontra.
                        eexists _.
                        by apply urn_subst_equal_obv.
                      }
                      rewrite /dmap /pmf/=/dbind_pmf/dunifP.
                      setoid_rewrite dunif_pmf.
                      rewrite SeriesC_scal_l /= /Rdiv Rmult_1_l.
                      rewrite <- Rmult_1_r.
                      erewrite urn_subst_equal_epsilon_unique; last done.
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
                      case_match; last done.
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
                 case_match; try (by inversion 1).
                 case_bool_decide; try (by inversion 1).
                 case_match; try (by inversion 1).
                 intros. subst. eapply list_elem_of_fmap_2'; last first.
                 { repeat f_equal. instantiate (1 := Z.to_nat n). lia. }
                 rewrite elem_of_seq. lia.
             --- intros H1. apply list_elem_of_fmap_1 in H1.
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
      + do 6 (case_match; try (simpl; rewrite INR_0; lra)).
        exfalso. apply H. subst.
        eapply list_elem_of_fmap_2'; last first.
        { apply bool_decide_eq_true_1 in H3, H4. repeat f_equal.
          - instantiate (1 := Z.to_nat n). lia.
          - done.
        }
        rewrite elem_of_seq. lia. 
      + instantiate (1 :=
                       (λ '(e, s), (prim_step (rand #z) σ1 (e, s) *
                                      match (e) with
                                      | (Val #(LitInt n)) =>
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
    iApply state_step_coupl_ret_err_ge_1.
    simpl.
    lra.
  }
  iApply state_step_coupl_ret.
  iModIntro.
  unshelve iMod (ec_supply_increase ε3 (mknonnegreal (ε2 (nat_to_fin l)) _) with "[Hε2]") as "[Hε2 Hcr]"; first done.
  { simpl. lra. }
  { iApply ec_supply_eq; [|done]. simplify_eq. lra. }
  iMod "Hclose'".
  iApply fupd_mask_intro; [eauto|]; iIntros "_".
  simpl. iFrame.
  iApply pgl_wp_value.
  iApply "HΨ".
  assert (nat_to_fin l = n) as ->; [|done].
  apply fin_to_nat_inj.
  rewrite fin_to_nat_to_fin.
  rewrite Nat2Z.id.
  reflexivity.
Qed.

Lemma wp_couple_rand_adv_comp' (N : nat) z E (ε1 : R) (ε2 : fin (S N) -> R) :
  TCEq N (Z.to_nat z) →
  (∀ n, (0<=ε2 n)%R) ->
  (SeriesC (λ n, (1 / (S N)) * ε2 n)%R <= ε1)%R →
  {{{ ↯ ε1 }}} rand #z @ E {{{ n, RET #n; ↯ (ε2 n) }}}.
Proof.
  iIntros (H1 Hineq H2).
  epose (difference :=  ((ε1)-SeriesC (λ n, (1 / (S N)) * (ε2 n)))%R ). 
  epose (ε2' n:= (ε2 n + difference)%R).
  iIntros (Φ) "Herr HΦ". 
  wp_apply (wp_couple_rand_adv_comp _ _ _ ε1 ε2' with "[$]").
  - rewrite /ε2'/difference. intros. apply Rplus_le_le_0_compat; first done.
    lra.
  - rewrite /ε2'. rewrite /difference; simpl. rewrite -/(INR (S N)).
    setoid_rewrite Rmult_plus_distr_l.
    rewrite SeriesC_plus; [|apply ex_seriesC_finite..].
    setoid_rewrite Rmult_plus_distr_l.
    rewrite SeriesC_plus; [|apply ex_seriesC_finite..].
    rewrite SeriesC_finite_mass fin_card. 
    replace (INR (S N) * (1 / INR (S N) * ε1))%R with (ε1); last first.
    { rewrite -Rmult_assoc Rdiv_1_l Rinv_r; first lra. pose proof pos_INR_S N. lra.  }
    assert ((SeriesC (λ x : fin (S N), 1 / S N * (ε2 x))
             + SeriesC (λ _ : fin (S N), 1 / S N * - SeriesC (λ n : fin (S N), 1 / S N * (ε2 n))))%R = 0)%R; last lra.
    rewrite SeriesC_finite_mass fin_card.
    rewrite -Rmult_assoc Rdiv_1_l Rinv_r; first lra. pose proof pos_INR_S N. lra.
  - iIntros. iApply "HΦ". iApply ec_weaken; last done.
    simpl; split; first done.
    rewrite -/(INR (S N)).
    apply Rplus_le_0_compat. rewrite /difference; lra. 
Qed.



Lemma wp_rand_avoid (N : nat) z E (x:Z):
  TCEq N (Z.to_nat z) →
  {{{ ↯ (1/(N+1)%nat) }}} rand #z @ E {{{ n, RET #n; ⌜x≠n⌝ }}}.
Proof.
  iIntros (-> Φ) "Herr HΦ".
  wp_apply (wp_couple_rand_adv_comp' _ _ _ _ (λ x', if bool_decide (fin_to_nat x' = Z.to_nat x) then 1 else 0)%R with "[$]").
  - intros. case_bool_decide; simpl; lra.
  - rewrite SeriesC_scal_l.
    destruct (decide (Z.to_nat x<S $ Z.to_nat z)) as [H1|H1].
    + erewrite (SeriesC_ext _ (λ x, if bool_decide (x = nat_to_fin H1) then 1 else 0)).
      * rewrite SeriesC_singleton. rewrite S_INR.
        rewrite plus_INR. 
        replace (INR 1) with 1%R by done. lra.
      * intros.
        case_bool_decide as H; [rewrite bool_decide_eq_true_2|rewrite bool_decide_eq_false_2]; try done.
        -- apply fin_to_nat_inj. by rewrite fin_to_nat_to_fin.
        -- intros ->. apply H.
           by rewrite fin_to_nat_to_fin.
    + rewrite SeriesC_0.
      * rewrite Rmult_0_r.
        apply Rdiv_INR_ge_0.
      * intros x'.
        rewrite bool_decide_eq_false_2; first done.
        intros Hcontra.
        pose proof fin_to_nat_lt x'.
        lia.
  - iIntros (?) "Herr".
    case_bool_decide; first (by iDestruct (ec_contradict with "[$]") as "[]").
    iApply "HΦ".
    iPureIntro. intros ?. subst.
    lia.
Qed. 
End rules.

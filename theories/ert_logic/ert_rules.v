(** * ERT rules  *)
From stdpp Require Import namespaces finite.
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext.
From clutch.prob_lang Require Import notation tactics metatheory.
From clutch.prob_lang Require Export lang.
From clutch.ert_logic Require Export lifting ectx_lifting primitive_laws.

Section metatheory.
  Context `{!ert_clutchGS Σ}.
  Local Open Scope R.

  Lemma wp_couple_rand_adv_comp (N : nat) z E (x1 : nonnegreal) (x2 : fin (S N) -> nonnegreal) :
    TCEq N (Z.to_nat z) →
    (exists r:nonnegreal, ∀ n, (x2 n <= r)%R) →
    1 + SeriesC (λ n, (1 / (S N)) * x2 n)%R = (nonneg x1) →
    {{{ ⧖ x1 }}} rand #z @ E {{{ n, RET #n; ⧖ (x2 n) }}}.
  Proof.
    iIntros (-> [r Hr] Hbound Φ) "Hx HΦ".
    iApply wp_lift_step_fupd_ERM; first done.
    iIntros (σ1 x) "[Hσ Hetc]".
    iApply fupd_mask_intro; [set_solver|].
    iIntros "Hclose'".
    iApply ERM_adv_comp; simpl.
    iDestruct (etc_split_supply with "[$][$]") as (x3) "%Hx3". subst.
    set (foo := (λ (ρ : expr * state),
                   x3+
          match ρ with
          | (Val (LitV (LitInt n)), σ) =>
              if bool_decide(σ = σ1)
              then if bool_decide (0 ≤ n)%Z
                then match (lt_dec (Z.to_nat n) (S (Z.to_nat z))) with
                       | left H => x2 (@Fin.of_nat_lt (Z.to_nat n) (S (Z.to_nat z)) H)
                       | _ => nnreal_zero
                     end
                else nnreal_zero
                       else nnreal_zero
            | _ => nnreal_zero
          end)%NNR).
    iExists foo.
    repeat iSplit.
    - iPureIntro. apply head_prim_reducible. eauto with head_step.
    - iPureIntro. eexists (x3+r).
      intros (e&σ); simpl. apply Rplus_le_compat_l.
      repeat case_match; simpl; try apply cond_nonneg. naive_solver.
    - (** use SeriesC_filter_finite_1 *)
      admit. (* iPureIntro. rewrite /foo /=. trans (nonneg x1); last first. *)
      (* + destruct x1, x3; simpl. lra. *)
      (* + rewrite <-Hbound. apply Rplus_le_compat_l. *)
      (*   set (bar := (λ y:fin (S(Z.to_nat z)), ((rand #(fin_to_nat y))%E, σ1))). *)
      (*   destruct (Rtotal_order r 0) as [|[|]]. *)
      (*   { pose proof cond_nonneg r as K. exfalso. eapply Rlt_not_le; done. } *)
      (*   { destruct r as [r K]. simpl in *. subst.  *)
      (*     assert (∀ n, x2 n = nnreal_zero). *)
      (*     { intros. apply nnreal_ext. simpl. *)
      (*       specialize (Hr n). pose proof cond_nonneg (x2 n). *)
      (*       apply Rle_antisym; try done. *)
      (*     } *)
      (*     (** Both equal*) *)
      (*     admit. *)
      (*     (* erewrite SeriesC_ext. *) *)
      (*     (* - erewrite dzero_mass. apply SeriesC_ge_0'. intros. repeat case_match; rewrite H; simpl. *) *)
      (*     (*   + lra. *) *)
      (*     (*   + lra. *) *)
      (*     (* - intros. repeat case_match; simpl; try rewrite dzero_0; try lra. *) *)
      (*     (*   all: rewrite H; simpl; lra. *) *)
      (*   } *)
      (*   apply (Rmult_le_reg_r (/ r)). *)
      (*   { apply Rinv_0_lt_compat. lra. } *)
      (*   rewrite -!SeriesC_scal_r. *)
      (*   set (foo' := (λ (ρ : expr * state), *)
      (*     x3+match ρ with *)
      (*     | (Val (LitV (LitInt n)), σ) => *)
      (*         if bool_decide(σ = σ1) *)
      (*         then if bool_decide (0 ≤ n)%Z *)
      (*           then match (lt_dec (Z.to_nat n) (S (Z.to_nat z))) with *)
      (*                  | left H => x2 (@Fin.of_nat_lt (Z.to_nat n) (S (Z.to_nat z)) H) *)
      (*                  | _ => nnreal_zero *)
      (*                end *)
      (*           else nnreal_zero *)
      (*                  else nnreal_zero *)
      (*       | _ => nnreal_zero *)
      (*     end  * nnreal_inv r)%NNR). *)
      (*   etrans; last eapply (SeriesC_filter_finite_1 (S (Z.to_nat z)) foo'  _ bar). *)
      (*   * apply SeriesC_le. *)
      (*     -- admit. *)
      (*     -- admit. *)
      (*   * rewrite /bar. intros ???. inversion H0. apply Nat2Z.inj in H2. *)
      (*     apply fin_to_nat_inj. done. *)
      (*   * lia. *)
      (*   * admit. (* intros [??]. rewrite /foo'. repeat case_match; simpl; try split; try lra. *) *)
      (*     (* -- apply Rmult_le_pos; [apply cond_nonneg|rewrite -Rdiv_1_l]. *) *)
      (*     (*    apply Rcomplements.Rdiv_le_0_compat; try lra. *) *)
      (*     (*    by apply Rgt_lt. *) *)
      (*     (* -- rewrite -Rdiv_def. rewrite Rcomplements.Rle_div_l; last by apply Rgt_lt. *) *)
      (*     (*    etrans; first apply Hr. by rewrite Rmult_1_l. *) *)
      (*   * admit. *)
      (*   * intros. subst. rewrite /foo'/bar. simpl. replace (0*_) with 0; last lra. *)
      (*     admit. *)
    - iIntros (e2 σ2) "%H".
      iModIntro.
      iModIntro.
      iMod "Hclose'".
      epose proof (head_reducible_prim_step).
      assert (head_reducible (rand #z) σ1) as K.
      { solve_red. }
      eapply H0 in K; last done.
      rewrite head_step_support_equiv_rel in K.
      inversion K; subst. iFrame.
      iMod (etc_decrease_supply with "[$][$]") as "Hetc".
      iMod (etc_increase_supply _ (x2 n) with "[$]") as "[Hetc Hx]".
      iModIntro. iSplitL "Hetc".
      + admit.
      + iApply ert_wp_value. by iApply "HΦ".
  Admitted.


End metatheory.

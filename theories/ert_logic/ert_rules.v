(** * ERT rules  *)
From stdpp Require Import namespaces finite.
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext.
From clutch.prob_lang Require Import notation tactics metatheory.
From clutch.prob_lang Require Export lang.
From clutch.ert_logic Require Export lifting ectx_lifting primitive_laws.

Section metatheory.
  Context `{!ertwpG prob_lang Σ}.
  Local Open Scope R.

  Lemma wp_couple_rand_adv_comp x (N : nat) (z : Z) E (r1 : R) (x2 : fin (S N) → R) :
    TCEq x (cost (rand #z)%E) ->
    TCEq N (Z.to_nat z) →
    (∀ n, 0 <= x2 n) →
    (∃ r, ∀ n, x2 n <= r) →
    x + SeriesC (λ n, 1 / S N * x2 n) = r1 →
    {{{ ⧖ r1 }}} rand #z @ E {{{ n, RET #n; ⧖ (x2 n) }}}.
  Proof.
    iIntros (-> -> Hnneg [r Hr] Hbound Φ) "Hx HΦ".
    iApply wp_lift_step_fupd_ERM; first done.
    iIntros (σ1 x) "[Hσ Hetc]".
    iApply fupd_mask_intro; [set_solver|].
    iIntros "Hclose'".
    iApply ERM_adv_comp; simpl.
    assert (0 <= r).
    { etrans; [eapply (Hnneg 0%fin)|]. apply Hr. }
    iDestruct (etc_supply_bound' with "[$][$]") as %(? & x3 & -> & ?).
    set (foo := (λ (ρ : expr * state),
                   x3 +
          match ρ with
          | (Val (LitV (LitInt n)), σ) =>
              if bool_decide(σ = σ1)
              then if bool_decide (0 ≤ n)%Z
                then match (lt_dec (Z.to_nat n) (S (Z.to_nat z))) with
                     | left H =>
                         let n := (@Fin.of_nat_lt (Z.to_nat n) (S (Z.to_nat z)) H) in
                         mknonnegreal (x2 n) (Hnneg n)
                       | _ => 0
                     end
                else 0
                       else 0
            | _ => 0
          end)%NNR).
    iExists foo.
    repeat iSplit.
    - iPureIntro. apply head_prim_reducible. eauto with head_step.
    - iPureIntro. intros. apply cond_nonneg.
    - iPureIntro. eexists (x3+r).
      intros (e&σ); simpl. apply Rplus_le_compat_l.
      repeat case_match; eauto.
    - iPureIntro.
      trans ((cost (rand #z)) + x3 +
           SeriesC
             (λ n : fin (S (Z.to_nat z)),
                1 / match Z.to_nat z with
                    | 0%nat => 1
                    | S _ => Z.to_nat z + 1
                  end * x2 n)); last first.
      { simpl in *. rewrite H0 -Hbound. apply Req_le_sym.
        rewrite Rplus_assoc (Rplus_comm (SeriesC _) x3) -Rplus_assoc. done. }
      rewrite Rplus_assoc. apply Rplus_le_compat_l.
      erewrite SeriesC_ext; last first.
      { intros. rewrite Rmult_plus_distr_l. done. }
      rewrite SeriesC_plus; last first.
      { apply pmf_ex_seriesC_mult_fn. exists r. intros. repeat case_match.
        all: simpl; split; try lra; try apply Hnneg; apply Hr. }
      { apply ex_seriesC_scal_r. apply pmf_ex_seriesC. }
      rewrite SeriesC_scal_r. apply Rplus_le_compat.
      + rewrite <-Rmult_1_l. apply Rmult_le_compat_r; first apply cond_nonneg.
        apply pmf_SeriesC.
      + pose proof Rlt_or_le 0 r as [|]; last first.
        { assert (r=nnreal_zero) as ->.
          - simpl. apply Rle_antisym; try done.
          - assert (∀ n, x2 n = 0) as K.
            { intros. simpl in *. apply Rle_antisym; try done. }
            rewrite SeriesC_0.
            + apply SeriesC_ge_0'. intros. rewrite K. simpl. lra.
            + intros. repeat case_match; rewrite ?K; simpl; try lra.
              rewrite K. lra. }
        set (h:= (λ b:fin(S(Z.to_nat z)), ((#(fin_to_nat b)):expr, σ1))).
        set (foo' := (λ x : expr * state,
                        prim_step (rand #z) σ1 x *
                          (let (e, σ) := x in
                           match e with
                           | Val #(LitInt n) =>
                               if bool_decide (σ = σ1)
                               then
                                 if bool_decide (0 ≤ n)%Z
                                 then
                                   match lt_dec (Z.to_nat n) (S (Z.to_nat z)) with
                                   | left H => x2 (nat_to_fin H)
                                   | right _ => nnreal_zero
                                   end
                                 else nnreal_zero
            else nnreal_zero
        | _ => nnreal_zero
        end))).
        etrans; last eapply (SeriesC_filter_finite_1_bounds _ foo' _ h r).
        * apply SeriesC_le; last first.
          -- apply ex_seriesC_filter_pos.
             ++ rewrite /foo'. intros; repeat case_match; simpl; try lra.
                all: apply Rmult_le_pos.
                all: try apply cond_nonneg.
                all: auto.
             ++ apply pmf_ex_seriesC_mult_fn.
                exists r. intros. repeat case_match; simpl; try lra.
                eauto.
          -- intros [e σ]. split.
             { repeat case_match; try real_solver. }
             destruct (bool_decide (∃ y, (e, σ) = h y)) eqn :H'.
             ++ rewrite bool_decide_eq_true in H'. destruct H' as [y H'].
                rewrite /h in H'. inversion H'. subst. rewrite /foo'.
                apply Req_le_sym. repeat f_equal.
                case_bool_decide; last done.
                case_bool_decide; last lia.
                repeat case_match; done.
             ++ rewrite bool_decide_eq_false in H'.
                repeat case_match; simpl; try real_solver.
                exfalso. apply H'.
                subst.
                exists (nat_to_fin l0).
                rewrite /h. repeat f_equal.
                ** rewrite fin_to_nat_to_fin. rewrite Z2Nat.id; first done.
                   by rewrite bool_decide_eq_true in H6.
                ** by rewrite bool_decide_eq_true in H5.
        * rewrite /h. intros ???K. inversion K. apply Nat2Z.inj' in H3.
          by apply fin_to_nat_inj.
        * lia.
        * done.
        * intros.
          rewrite /foo'.
          repeat case_match; simpl; split; try lra.
          all: try apply Rmult_le_pos.
          all: try apply cond_nonneg.
          all: auto.
          simpl in *. rewrite <-Rmult_1_l. apply Rmult_le_compat; auto.

        * simpl. intros. case_match.
          -- replace (1/1) with 1 by lra.
             rewrite Rmult_1_l. split; [apply Hnneg|apply Hr].
          -- split; first apply Rmult_le_pos.
             ++ apply Rcomplements.Rdiv_le_0_compat; first lra.
                pose proof pos_INR_S n. lra.
             ++ apply Hnneg.
             ++ rewrite <-Rmult_1_l. apply Rmult_le_compat.
                ** apply Rcomplements.Rdiv_le_0_compat; first lra.
                   pose proof pos_INR_S n. lra.
                ** apply Hnneg.
                ** rewrite Rcomplements.Rle_div_l.
                   --- assert (0<= INR (S n)); try lra. pose proof (pos_INR_S n). lra.
                   --- pose proof (pos_INR_S n). lra.
                ** apply Hr.
        * simpl. intros ?? ->.
          rewrite /h. rewrite /foo'.
          case_bool_decide; last done.
          case_bool_decide; last lia.
          destruct (lt_dec _ _); simpl; last first.
          { exfalso. apply n. rewrite Nat2Z.id. apply fin_to_nat_lt. }
          apply Rmult_le_compat; auto.
          -- rewrite head_prim_step_eq. simpl.
             erewrite dmap_unif_nonzero; last done.
             ** simpl. real_solver.
             ** intros ???. simplify_eq.  done.
          -- replace (nat_to_fin l) with b; first done.
             apply fin_to_nat_inj. rewrite fin_to_nat_to_fin.
             rewrite Nat2Z.id. done.
    - iIntros (e2 σ2) "%Hs".
      iModIntro.
      iModIntro.
      iMod "Hclose'".
      epose proof (head_reducible_prim_step).
      assert (head_reducible (rand #z) σ1) as K.
      { solve_red. }
      eapply H1 in K; last done.
      rewrite head_step_support_equiv_rel in K.
      inversion K; subst. iFrame.
      iMod (etc_supply_decrease with "[$][$]") as (????) "Hetc".
      iMod (etc_supply_increase _ (x2 n) with "[$]") as "(% & Hetc & % & Hx2)"; [done|].
      iModIntro. iSplitL "Hetc".
      + iApply etc_supply_irrel; last done. simpl.
        rewrite bool_decide_eq_true_2 //.
        rewrite bool_decide_eq_true_2; last lia.
        case_match; last first.
        { pose proof fin_to_nat_lt n. lia. }
        assert (nat_to_fin l = n) as ->.
        { apply fin_to_nat_inj. rewrite fin_to_nat_to_fin. lia. }
        rewrite H4. simplify_eq. apply Rplus_eq_compat_r. lra.
      + iApply ert_wp_value. by iApply "HΦ".
  Qed.

  Lemma wp_couple_rand_adv_comp' x (N : nat) (z : Z) E (x1 : R) (x2 : fin (S N) → R) :
    TCEq x (cost (rand #z)) →
    TCEq N (Z.to_nat z) →
    (∀ n, 0 <= x2 n) →
    x + SeriesC (λ n, (1 / (S N)) * x2 n)%R = x1 →
    {{{ ⧖ x1 }}} rand #z @ E {{{ n, RET #n; ⧖ (x2 n) }}}.
  Proof.
    intros -> ? Hnneg. eapply wp_couple_rand_adv_comp; try done.
    exists (SeriesC x2).
    intros ?. eapply SeriesC_ge_elem; [done|].
    eapply ex_seriesC_finite.
  Qed.

  Lemma wp_couple_rand_constant r1 r2 (N : nat) (z : Z) E :
    TCEq r1 (cost (rand #z)) →
    TCEq N (Z.to_nat z) →
    0 <= r2 →
    {{{ ⧖ (r1 + r2) }}} rand #z @ E {{{ n, RET #n; ⧖ r2 }}}.
  Proof.
    iIntros (-> -> ? Φ) "H HΦ".
    iApply (wp_couple_rand_adv_comp' with "H"); last first.
    - iModIntro. iIntros (n) "H". iApply "HΦ". done.
    - simpl.
      rewrite {1}Rplus_comm.
      rewrite (Rplus_comm _ r2).
      apply Rplus_eq_compat_r.
      rewrite SeriesC_finite_mass fin_card.
      rewrite Rdiv_1_l -Rmult_assoc -Rdiv_def.
      replace (_/_) with 1; first real_solver.
      rewrite Rdiv_diag; first real_solver.
      intros ?. assert (S (Z.to_nat z)= 0%nat); last done.
      apply INR_eq. done.
    - intros. done.
  Qed.

End metatheory.

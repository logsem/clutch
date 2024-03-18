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
    - iPureIntro. destruct x1 as [x1 x1cond]. 
      trans (1 + x3 +
           SeriesC
             (λ n : fin (S (Z.to_nat z)),
                1 / match Z.to_nat z with
                    | 0%nat => 1
                    | S _ => Z.to_nat z + 1
                  end * x2 n)); last first.
      { simpl in *. rewrite -Hbound. apply Req_le_sym. rewrite Rplus_assoc (Rplus_comm (SeriesC _) x3) -Rplus_assoc. done. }
      rewrite Rplus_assoc. apply Rplus_le_compat_l.
      erewrite SeriesC_ext; last first.
      { intros. rewrite Rmult_plus_distr_l. done. }
      rewrite SeriesC_plus; last first.
      { apply pmf_ex_seriesC_mult_fn. exists r. intros. repeat case_match.
        all: simpl; split; try lra; try apply cond_nonneg; apply Hr. }
      { apply ex_seriesC_scal_r. apply pmf_ex_seriesC. }
      rewrite SeriesC_scal_r. apply Rplus_le_compat.
      + rewrite <-Rmult_1_l. apply Rmult_le_compat_r; first apply cond_nonneg.
        apply pmf_SeriesC.
      + pose proof Rlt_or_le 0 r as [|]; last first.
        { assert (r=nnreal_zero) as ->.
          - apply nnreal_ext. simpl. apply Rle_antisym; try done. apply cond_nonneg.
          - assert (∀ n, x2 n = nnreal_zero) as K.
            { intros. apply nnreal_ext. simpl in *. apply Rle_antisym; try done. apply cond_nonneg. }
            rewrite SeriesC_0.
            + apply SeriesC_ge_0'. intros. rewrite K. simpl. lra.
            + intros. repeat case_match; try rewrite K; simpl; lra.
        }
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
                exists r. pose proof cond_nonneg r. intros. repeat case_match; simpl; try lra.
                all: split; try apply Hr.
                all: apply cond_nonneg.
          -- intros [e σ]. split.
             { repeat case_match; try real_solver.
               all: pose proof cond_nonneg; real_solver.
             }
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
                   by rewrite bool_decide_eq_true in H4.
                ** by rewrite bool_decide_eq_true in H3.
        * rewrite /h. intros ???K. inversion K. apply Nat2Z.inj' in H1.
          by apply fin_to_nat_inj.
        * lia.
        * done.
        * intros. pose proof cond_nonneg r.
          rewrite /foo'. repeat case_match; simpl; split; try lra.
          all: try apply Rmult_le_pos.
          all: try apply cond_nonneg.
          all: auto.
          simpl in *. rewrite <-Rmult_1_l. apply Rmult_le_compat; auto.
          apply cond_nonneg.
        * simpl. intros. case_match.
          -- replace (1/1) with 1 by lra.
             rewrite Rmult_1_l. split; [apply cond_nonneg|apply Hr].
          -- split; first apply Rmult_le_pos.
             ++ apply Rcomplements.Rdiv_le_0_compat; first lra.
                pose proof pos_INR_S n. lra.
             ++ apply cond_nonneg.
             ++ rewrite <-Rmult_1_l. apply Rmult_le_compat.
                ** apply Rcomplements.Rdiv_le_0_compat; first lra.
                   pose proof pos_INR_S n. lra.
                ** apply cond_nonneg.
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
          -- apply cond_nonneg.
          -- rewrite head_prim_step_eq. simpl.
             erewrite dmap_unif_nonzero; last done.
             ** simpl. real_solver.
             ** intros ???. inversion H2. apply Nat2Z.inj in H4.
                apply fin_to_nat_inj. done.
          -- replace (nat_to_fin l) with b; first done.
             apply fin_to_nat_inj. rewrite fin_to_nat_to_fin.
             rewrite Nat2Z.id. done. 
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
      + iApply etc_supply_irrel; last done. simpl.
        apply Rplus_eq_compat_l. rewrite bool_decide_eq_true_2; last done.
        rewrite bool_decide_eq_true_2; last lia.
        case_match; last first.
        { pose proof fin_to_nat_lt n. lia. }
        assert (nat_to_fin l = n) as ->; last done.
        apply fin_to_nat_inj. rewrite fin_to_nat_to_fin. lia.
      + iApply ert_wp_value. by iApply "HΦ".
  Qed.


  (** Can be strengthed, but it works for now*)
  Local Lemma mean_constraint (N : nat) ε1 (ε2 : fin (S N) -> nonnegreal) :
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
      replace (nonneg {| nonneg := INR (S N); cond_nonneg := _ |}) with (INR (S N)); [| by simpl ].
      by apply not_0_INR.
    - replace (nonneg (ε2 _)) with (NNRbar_to_real (NNRbar.Finite (ε2 n))); last first.
      { simpl. done. }
      simpl.
      rewrite -(SeriesC_singleton_dependent _ ε2).
      apply SeriesC_le.
      + intros n'.
        assert (H : (0 <= (nonneg (ε2 n')))%R) by apply cond_nonneg.
        rewrite /nnreal_zero /=.
        case_bool_decide; try lra.
      + apply ex_seriesC_finite.
  Qed.
  
  Lemma wp_couple_rand_adv_comp' (N : nat) z E (x1 : nonnegreal) (x2 : fin (S N) -> nonnegreal) :
    TCEq N (Z.to_nat z) →
    1 + SeriesC (λ n, (1 / (S N)) * x2 n)%R = (nonneg x1) →
    {{{ ⧖ x1 }}} rand #z @ E {{{ n, RET #n; ⧖ (x2 n) }}}.
  Proof.
    intros. eapply wp_couple_rand_adv_comp; try done.
    epose proof (mean_constraint _ _ _ _) as [x[H1 H2]].
    exists (mknonnegreal x H1). done.
    Unshelve.
    2: { eapply Rplus_eq_reg_l. erewrite H0.
         instantiate (1:=mknonnegreal (nonneg x1 - 1) _).
         simpl. lra. }
    Unshelve.
    rewrite <- H0. assert (0<=SeriesC (λ n, 1/S N * x2 n)); last lra.
    apply SeriesC_ge_0'. intros. apply Rmult_le_pos; last apply cond_nonneg.
    apply Rcomplements.Rdiv_le_0_compat; first lra.
    apply pos_INR_S.
  Qed.

  Lemma wp_couple_rand_constant (N : nat) z E (x : nonnegreal) :
    TCEq N (Z.to_nat z) →
    {{{ ⧖ (x+nnreal_one)%NNR }}} rand #z @ E {{{ n, RET #n; ⧖ (x) }}}.
  Proof.
    intros ->.
    iIntros(Φ) "H HΦ".
    iApply (wp_couple_rand_adv_comp' with "H"); last first.
    - iModIntro. iIntros (n) "H". iApply "HΦ". done.
    - simpl. rewrite Rplus_comm. apply Rplus_eq_compat_r.
      rewrite SeriesC_finite_mass fin_card.
      rewrite Rdiv_1_l -Rmult_assoc -Rdiv_def.
      replace (_/_) with 1; first real_solver.
      rewrite Rdiv_diag; first real_solver.
      intro H. assert (S (Z.to_nat z)= 0%nat); last done.
      apply INR_eq. done.
  Qed.
     

End metatheory.

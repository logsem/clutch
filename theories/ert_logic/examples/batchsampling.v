(** * Batch Sampling *)
From clutch.ert_logic Require Export expected_time_credits ert_weakestpre problang_wp proofmode
  derived_laws cost_models ert_rules.
From clutch.prob_lang Require Import notation tactics metatheory lang.
From iris.proofmode Require Export proofmode.
From Coq Require Export Reals Psatz.
From Coquelicot Require Export Hierarchy.
Require Import Lra.

Set Default Proof Using "Type*".

Definition sample
  := (rec: "g" "_" :=
        let: "result" := (rand #1) + #2 * (rand #1) in
        if: ("result" < #3)%E
          then "result"
        else ("g" #()))%V.

Section proof1.
  Context `{!ert_clutchGS Σ CostRand}.
  Lemma wp_geo E:
    {{{ ⧖ (8/3) }}}
      sample #()@E
      {{{(n:Z), RET #n; ⌜(0<=n<3)%Z⌝ }}}.
  Proof.
    iIntros (Φ) "Hx HΦ".
    iLöb as "IH" forall (Φ) "Hx HΦ".
    rewrite /sample.
    (* iAssert (⧖ (2/3) ∗ ⧖ 2)%I with "[Hx]"as "[Hx1 Hx2]". *)
    (* { iApply etc_split; try lra. iApply etc_irrel; last done. lra. } *)
    wp_pures. simpl.
    wp_apply (wp_couple_rand_adv_comp _ _ _ _ _ (λ x, if (fin_to_nat x =? 0)%nat then 1 else 7/3) with "[$]").
    - intros. case_match; lra.
    - exists (7/3). intros. case_match; lra.
    - simpl. rewrite SeriesC_finite_foldr. simpl. lra.
    - iIntros (n1) "Hx". case_match eqn: H1.
      + (* zero for first flip *)
        wp_pures.
        wp_apply (wp_couple_rand_constant with "[$]").
        { simpl. lra. }
        iIntros (n2) "Hx".
        wp_pures.
        case_bool_decide as H2; last first.
        { exfalso. apply H2. pose proof fin_to_nat_lt n2.
          rewrite Nat.eqb_eq in H1. lia. }
        wp_pures.
        iModIntro. iApply "HΦ".
        iPureIntro. lia.
      + wp_pures.
        wp_apply (wp_couple_rand_adv_comp _ _ _ _ _ (λ x, if (fin_to_nat x =? 0)%nat then 0 else 8/3) with "[$]").
        * intros. case_match; simpl; lra.
        * exists (8/3). intros; case_match; simpl; lra.
        * simpl. rewrite SeriesC_finite_foldr. simpl. lra.
        * iIntros (n2) "Hx". case_match eqn:K.
          { wp_pures. case_bool_decide as K'.
            - wp_pures. iModIntro. iApply "HΦ".
              iPureIntro; lia.
            - exfalso. pose proof fin_to_nat_lt n1. apply K'.
              rewrite Nat.eqb_eq in K. lia.
          }
          wp_pures. case_bool_decide as K'.
          { exfalso. rewrite Nat.eqb_neq in H1. rewrite Nat.eqb_neq in K. lia. }
          wp_pure. iApply ("IH" with "[Hx]").
          -- iApply etc_irrel; last done. simpl. lra.
          -- done.        
  Qed.  
End proof1.

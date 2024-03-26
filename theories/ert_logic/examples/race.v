From clutch.prob_lang Require Import lang notation tactics metatheory.
From clutch.ert_logic Require Export expected_time_credits ert_weakestpre problang_wp proofmode
  derived_laws cost_models ert_rules.
From iris.proofmode Require Export proofmode.
Set Default Proof Using "Type*".

(** Race example in Ngo et al. 2017*)
Local Open Scope R_scope.
Section race.
  Context `{!ert_clutchGS Σ CostTick}.
  Variable (h t:loc).
  
  Definition race :=
    (rec: "race" "_":=
       if: (!#h ≤ !#t) then
         #t <- !#t + #1 ;;
         (if: rand #1 = #0 
         then #h <- !#h + rand #9 
          else #());;
         tick #1;;
         "race" #()
       else #())%V.

  Lemma wp_race_end E (hn tn:nat):
    (tn < hn)%nat -> 
    {{{ h ↦ #hn ∗ t ↦ #tn }}}
      race #()@E
      {{{ RET #(); True }}}.
  Proof.
    iIntros (H Φ) "[Hh Ht] HΦ".
    rewrite /race.
    wp_pures.
    wp_load; iIntros "Ht".
    wp_apply (wp_load with "[$Hh]"); first simpl.
    { by case_bool_decide. }
    iIntros "Hh".
    wp_pures.
    case_bool_decide; first lia.
    wp_pures. iModIntro. iApply "HΦ". done.
  Qed.

  Lemma wp_race E (hn tn:nat):
    (hn <= tn)%nat -> 
    {{{ ⧖ (2/3*(tn+9-hn)%nat) ∗ h ↦ #hn ∗ t ↦ #tn }}}
      race #()@E
      {{{ RET #(); True }}}.
  Proof.
    iIntros (H Φ) "[Hx [Hh Ht]] HΦ".
    iLöb as "IH" forall (hn tn H Φ) "Hx Hh Ht HΦ".
    rewrite /race.
    wp_pures.
    wp_load; iIntros "Ht".
    wp_apply (wp_load with "[$Hh]").
    { by case_bool_decide. }
    iIntros "Hh".
    wp_pures. case_bool_decide; last lia.
    wp_pures.
    wp_apply (wp_load with "[$Ht]").
    { by case_bool_decide. }
    iIntros "Ht". wp_pures.
    wp_apply (wp_store with "[Ht]").
    { case_bool_decide; last done. by iFrame. }
    iIntros "Ht".
    wp_pures.
    assert (9<=INR (tn+9-hn)) as K.
    { replace 9 with (INR 9); last (simpl; lra). 
      apply le_INR. lia. }
    wp_apply (wp_couple_rand_adv_comp' _ _ _ _ _ (λ x, if bool_decide(fin_to_nat x = 0%nat) then (2 / 3 * (tn + 9 - hn - 1)%nat)-1 else (2 / 3 * (tn+1 + 9 - hn)%nat)+1)with "[$Hx]").
    { assert (9<=INR (tn + 1 + 9 - hn)%nat) as K'.
        { replace 9 with (INR 9); last (simpl; lra). 
          apply le_INR. lia. }
        assert (8<=INR (tn + 9 - hn - 1)%nat) as K''.
        { replace 8 with (INR 8); last (simpl; lra). 
          apply le_INR. lia. }
        intros; case_bool_decide; try lra.
    }
    { simpl. rewrite SeriesC_finite_foldr. simpl. 
      replace (tn + 1 + 9 - hn)%nat with (tn + 9 - hn + 1)%nat by lia.
      rewrite minus_INR; last lia.
      rewrite plus_INR. lra. }
    iIntros (n) "Hx". case_bool_decide as H1.
    - wp_pures. case_bool_decide as H2; last first.
      { exfalso. rewrite H1 in H2. naive_solver. }
      wp_pures. rewrite -/race.
      wp_apply (wp_couple_rand_adv_comp' _ _ _ _ _ (λ x, (2 / 3 * (tn + 10 - (hn + fin_to_nat x))%nat+1)) with "[$Hx]").
      { intros n'. pose proof fin_to_nat_lt n'.
        pose proof pos_INR (tn + 10 - (hn + fin_to_nat n')). lra.
      }
      { admit. }
      iIntros (x) "Hx".
      wp_apply (wp_load with "[$Hh]").
      { simpl. case_bool_decide; done. }
      iIntros "Hh". wp_pures.
      wp_apply (wp_store with "[$Hh]").
      { simpl. case_bool_decide; done. }
      iIntros "Hh". wp_pures. wp_pure.
      { pose proof fin_to_nat_lt x.
        pose proof pos_INR (tn + 10 - (hn + fin_to_nat x)). lra. }
      wp_pures.
      replace (Z.of_nat hn + Z.of_nat (fin_to_nat x))%Z with (Z.of_nat (hn + fin_to_nat x)); last lia.
      replace (_+_)%Z with (Z.of_nat (tn + 1)%nat); last lia.
      destruct (decide (tn+1 < hn+x)%nat).
      + wp_apply (wp_race_end with "[Hh Ht]"); last first.
        * done.
        * iFrame.
        * lia.
      + wp_apply ("IH" with "[][Hx][$][$][$]").
        * iPureIntro. lia.
        * iApply etc_irrel; last done.
          cut ((INR tn + 10 - (INR hn + INR (fin_to_nat x))) =
               INR (tn + 1 + 9 - (hn + fin_to_nat x))); first lra.
          replace 10 with (INR 10); last (simpl; lra).
          rewrite -!plus_INR. rewrite-minus_INR; last lia.
          f_equal. lia.
    - wp_pures. case_bool_decide as H2.
      { exfalso. inversion H2 as [H4]. lia. }
      rewrite -/race.
      wp_pures. wp_pure.
      { assert (9<=INR (tn + 1 + 9 - hn)%nat) as K'.
        { replace 9 with (INR 9); last (simpl; lra). 
          apply le_INR. lia. }
        lra. }
      wp_pures.
      replace (Z.of_nat tn + 1)%Z with (Z.of_nat (tn + 1)); last lia.
      wp_apply ("IH" with "[][Hx][$Hh][$Ht]").
      + iPureIntro; lia.
      + iApply etc_irrel; last done. lra.
      + done.
  Admitted.
    
  
End race.

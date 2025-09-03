Require Import Arith.
From clutch.foxtrot Require Import foxtrot.

Definition mixer_prog : expr :=
  let: "y" := ref #0 in
  Fork ("y" <- #1) ;;
  let: "x1" := !"y" in
  let: "x2" := rand #1 in
  ("x1" + "x2") `rem` #2.

Lemma mixer_refines_rand :
  ∅ ⊨ mixer_prog ≤ctx≤ rand #1 : TNat.
Proof.
  apply (refines_sound foxtrotRΣ).
  iIntros (??).
  unfold_rel.
  iIntros (K j) "Hspec".
  rewrite /mixer_prog.
  wp_alloc l as "Hl".
  wp_pures.
  iMod (inv_alloc nroot _ (l↦#0 ∨ l↦#1)%I with "[$Hl]") as "#Hinv".
  wp_apply wp_fork.
  { iInv "Hinv" as ">[?|?]" "Hclose".
    all: wp_store; by iMod ("Hclose" with "[$]").
  }
  wp_pures.
  wp_bind (! _)%E.
  iInv "Hinv" as ">[?|?]" "Hclose".
  - wp_load.
    iMod ("Hclose" with "[$]") as "_".
    iModIntro.
    wp_pures.
    wp_apply (wp_couple_rand_rand with "[$]"); first done.
    iIntros (?) "[% Hspec]".
    wp_pures.
    iFrame. iPureIntro.
    simpl.
    eexists _; split; last done.
    rewrite Z.rem_small; last lia.
    f_equal.
  - wp_load.
    iMod ("Hclose" with "[$]") as "_".
    iModIntro.
    wp_pures.
    wp_apply (wp_couple_rand_rand _ (λ x, if bool_decide (x<=1)%nat then 1-x else x) with "[$]").
    { intros. rewrite bool_decide_eq_true_2; last lia.
      lia. 
    }
    iIntros (?) "[% Hspec]".
    wp_pures.
    iFrame. iPureIntro.
    simpl.
    eexists _; split; last done.
    rewrite bool_decide_eq_true_2; last lia.
    destruct n as [|[|]]; try lia; repeat f_equal.
    Unshelve.
    + apply le_dec.
    + split.
      * intros ??.
        case_bool_decide as H1; case_bool_decide as H2; intros; lia.
      * intros x.
        destruct x as [|[| n]].
        -- exists 1. rewrite bool_decide_eq_true_2; lia.
        -- exists 0. rewrite bool_decide_eq_true_2; lia.
        -- exists (S $ S n). rewrite bool_decide_eq_false_2; lia.
Qed. 

Lemma rand_refines_mixer :
  ∅ ⊨ rand #1 ≤ctx≤ mixer_prog : TNat.
Proof.
  apply (refines_sound foxtrotRΣ).
  iIntros (??).
  unfold_rel.
  iIntros (K j) "Hspec".
  rewrite /mixer_prog.
  tp_alloc j as l "Hl".
  tp_pures j.
  tp_fork j.
  iIntros (?) "_".
  tp_pures j.
  tp_load j.
  tp_pures j.
  tp_bind j (rand _)%E.
  iApply wp_pupd.
  wp_apply (wp_couple_rand_rand with "[$]"); first done.
  iIntros (?) "[% Hspec]".
  simpl. 
  tp_pures j.
  iFrame. iPureIntro.
  simpl.
  eexists _; split; first done.
  rewrite Z.rem_small; last lia.
  f_equal.
Qed. 

Lemma mixer_eq_rand :
  ∅ ⊨ mixer_prog =ctx= rand #1 : TNat.
Proof.
  split; [apply mixer_refines_rand|apply rand_refines_mixer].
Qed. 

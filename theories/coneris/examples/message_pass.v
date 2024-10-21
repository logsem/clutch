From iris.algebra Require Import excl_auth.
From iris.base_logic.lib Require Export invariants cancelable_invariants.
From clutch.coneris Require Import coneris par spawn lib.flip.

Local Open Scope Z.

Set Default Proof Using "Type*".

Definition prog (l:loc) : expr:=
  #l <- #(-1);;
  ((if: flip then #l <- #0 else #l <- #1) ||| 
                                     ((rec: "f" "y":=
                                        if: "y"=#(-1)
                                        then "f" !(#l)
                                        else "y"
                                     )%V !(#l))
                                     
  ).

Section proof.
  Context `{!conerisGS Σ, !spawnG Σ, inG Σ (excl_authR boolO), cinvG Σ}.
  Lemma prog_spec l:
    {{{ ↯(/2)%R ∗ ∃ v, l↦v }}}
      prog l
      {{{
            v, RET v; l↦#0
      }}}.
  Proof.
    iIntros (Φ) "[Herr [%v Hl]] HΦ".
    rewrite /prog.
    wp_store.
    iMod (own_alloc (●E false ⋅ ◯E false)) as (γ) "[Hauth Hfrag]".
    { by apply excl_auth_valid. }
    iMod (cinv_alloc _ nroot (l↦#0 ∗ own γ (●E true) ∨ l↦ #(-1) ∗ own γ (●E false))%I with "[Hl Hauth]") as "[%γ1 [#I Hc]]"; first (iRight; iFrame).
    wp_pures.
    iDestruct "Hc" as "[Hc Hc']".
    iApply pgl_wp_fupd.
    wp_apply (wp_par (λ _, own γ (◯E true) ∗ cinv_own γ1 (1/2)%Qp)%I (λ _, cinv_own γ1 (1/2)%Qp)%I with "[Herr Hfrag Hc][Hc']").
    - wp_apply (wp_flip_adv _ _ (λ x, if x then 0 else 1)%R with "[$]").
      + intros []; lra.
      + lra.
      + iIntros ([]) "Herr"; last by iDestruct (ec_contradict with "[$]") as "%".
        wp_pures.
        iMod (cinv_acc_strong with "[I] [$]") as "K"; [done|done|..].
        iDestruct "K" as "[>[[H Hauth]|[H Hauth]] [Hc Hclose]]".
        * iCombine "Hauth Hfrag" gives "%K". by apply excl_auth_agree_L in K.
        * wp_store.
          iMod (own_update_2 _ _ _ (●E true ⋅ ◯E true) with "Hauth Hfrag") as "[Hauth Hfrag]".
          { by apply excl_auth_update. }
          iMod ("Hclose" with "[H Hauth]"); first (iLeft; iLeft; iFrame).
          iFrame.
          by rewrite -union_difference_L.
    - iLöb as "IH".
      wp_bind (!_)%E.
      iMod (cinv_acc_strong with "[I] [$]") as "K"; [done|done|..].
      iDestruct "K" as "[>[[H Hauth]|[H Hauth]] [Hc Hclose]]".
      + wp_load.
        iMod ("Hclose" with "[-Hc]"); first (iLeft; iLeft; iFrame).
        rewrite -union_difference_L; last done.
        iModIntro.
        by wp_pures.
      + wp_load.
        iMod ("Hclose" with "[-Hc]"); first (iLeft; iRight; iFrame).
        rewrite -union_difference_L; last done.
        iModIntro. wp_pures. by iApply "IH".
    - iIntros (??) "[[Hfrag Hc] Hc']".
      iCombine "Hc Hc'" as "Hc".
      iNext.
      iMod (cinv_cancel with "[][$]") as "H"; [done|done|].
      iDestruct "H" as ">[[H Hauth]|[H Hauth]]".
      + iModIntro. by iApply "HΦ".
      + iCombine "Hauth Hfrag" gives "%K". by apply excl_auth_agree_L in K.
  Qed.
    
End proof.

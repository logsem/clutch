From iris.algebra Require Import excl_auth.
From iris.base_logic.lib Require Export invariants.
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
                                     
  );; !#l.

Section proof.
  Context `{!conerisGS Σ, !spawnG Σ, inG Σ (excl_authR boolO)}.
  Lemma prog_spec l:
    {{{ ↯(/2)%R ∗ ∃ v, l↦v }}}
      prog l
      {{{
            RET #0; True
      }}}.
  Proof.
    iIntros (Φ) "[Herr [%v Hl]] HΦ".
    rewrite /prog.
    wp_store.
    iMod (own_alloc (●E false ⋅ ◯E false)) as (γ) "[Hauth Hfrag]".
    { by apply excl_auth_valid. }
    iMod (inv_alloc nroot _ (l↦#0 ∗ own γ (●E true) ∨ l↦ #(-1) ∗ own γ (●E false))%I with "[Hl Hauth]") as "#I"; first (iRight; iFrame).
    wp_pures.
    wp_apply (wp_par (λ _, own γ (◯E true))%I (λ _, True)%I with "[Herr Hfrag][]").
    - wp_apply (wp_flip_adv _ _ (λ x, if x then 0 else 1)%R with "[$]").
      + intros []; lra.
      + lra.
      + iIntros ([]) "Herr"; last by iDestruct (ec_contradict with "[$]") as "%".
        wp_pures.
        iInv "I" as ">[[H Hauth]|[H Hauth]]" "Hclose".
        * iCombine "Hauth Hfrag" gives "%K". by apply excl_auth_agree_L in K.
        * wp_store.
          iMod (own_update_2 _ _ _ (●E true ⋅ ◯E true) with "Hauth Hfrag") as "[Hauth Hfrag]".
          { by apply excl_auth_update. }
          iMod ("Hclose" with "[H Hauth]"); first (iLeft; iFrame). iModIntro. iFrame. 
    - iLöb as "IH".
      wp_bind (!_)%E.
      iInv "I" as ">[[??]|[??]]" "Hclose".
      + wp_load.
        iMod ("Hclose" with "[-]"); first (iLeft; iFrame).
        iModIntro.
        by wp_pures.
      + wp_load.
        iMod ("Hclose" with "[-]"); first (iRight; iFrame).
        iModIntro. wp_pures. iApply "IH".
    - iIntros (??) "[Hfrag _]".
      iNext. wp_pures.
      iInv "I" as ">[[H Hauth]|[H Hauth]]" "Hclose".
      + wp_load.
        iMod ("Hclose" with "[H Hauth]"); first (iLeft; iFrame). iModIntro.
        by iApply "HΦ".
      + iCombine "Hauth Hfrag" gives "%K". by apply excl_auth_agree_L in K.
  Qed.
    
End proof.

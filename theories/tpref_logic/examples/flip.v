From clutch.prob Require Import distribution markov.
From clutch.prob_lang Require Import lang notation.
From clutch.tpref_logic Require Import weakestpre spec primitive_laws proofmode.

Section coupl.
  Context `{!tprG δ Σ}.

  Definition int_to_bool : val :=
    λ: "z", ~ ("z" = #0).
  Definition flip : expr := (int_to_bool (rand #1))%E.

  Lemma rwp_couple_flip E R a1 :
    Rcoupl fair_coin (step a1) R →
    {{{ specF a1 }}} flip @ E {{{ (b : bool) a2, RET #b; specF a2 ∗ ⌜R b a2⌝  }}}.
  Proof.
    iIntros (? Φ) "Ha HΦ". rewrite /flip.
    wp_pures.
    wp_apply (rwp_couple with "Ha"); [by eapply Rcoupl_fair_coin_dunifP|].
    iIntros (n a2) "[Ha %HR]". rewrite /int_to_bool.
    wp_pures.
    case_bool_decide.
    - iApply "HΦ". iFrame. inv_fin n; eauto.
    - iApply ("HΦ"). iFrame. inv_fin n; eauto.
  Qed.

  Lemma rwp_flip E :
    ⟨⟨⟨ True ⟩⟩⟩ flip @ E ⟨⟨⟨ (b : bool), RET #(LitBool b); True ⟩⟩⟩.
  Proof.
    iIntros (Φ) "_ HΦ". rewrite /flip.
    wp_bind (rand(_) _)%E.
    wp_apply (rwp_rand 1 with "[//]").
    iIntros (?) "_ /=". rewrite /int_to_bool.
    wp_pures.
    case_bool_decide.
    - iApply "HΦ". iFrame. inv_fin n; eauto.
    - iApply ("HΦ"). iFrame. inv_fin n; eauto.
  Qed.

End coupl.

From iris.proofmode       Require Import base tactics classes proofmode.
From clutch.approxis      Require Import app_weakestpre adequacy primitive_laws.
From clutch.prob_eff_lang Require Import weakestpre protocol_agreement iEff lang.



Notation "'EWP' e @ E  <| Ψ '|' '>' {{ v , Φ } }" :=
  (ewp_def E e%E Ψ%ieff (λ v, Φ)%I)
  (at level 20, e, E, Ψ, Φ at level 200,
     format "'[' 'EWP'  e  '/' '[' @ E <|  Ψ  '|' '>'  {{  v ,  Φ  } } ']' ']'") : bi_scope.

Notation "'EWP' e @ E  <| Ψ '|' '>' {{ Φ } }" :=
  (ewp_def E e%E Ψ%ieff Φ)
  (at level 20, e, E, Ψ, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[' @ E <|  Ψ  '|' '>'  {{ Φ } } ']' ']'") : bi_scope.


Lemma ewp_imp_wp `{!spec_updateGS (lang_markov eff_prob_lang) Σ,
                     !app_weakestpre.approxisWpGS eff_prob_lang Σ}
  (e : expr) (Φ : val → iProp Σ) :
  EWP e @ ⊤ <| iEff_bottom |> {{ v, Φ v }} ⊢
  WP e @ ⊤ {{v, Φ v }}.
Proof.
  iLöb as "IH" forall (e).
  destruct (to_val e) as [ v    |] eqn:?; [|
  destruct (to_eff e) as [(v, k)|] eqn:?  ].
  - rewrite ewp_unfold /ewp_pre wp_unfold /wp_pre /= Heqo.  iIntros "$".
  - rewrite -(of_to_eff _ _ _ Heqo0).
    iIntros "Hewp".
    rewrite ewp_unfold /ewp_pre wp_unfold /wp_pre /=.
    iIntros (σ1 e1' σ1' ε1) "(Hstate&Hspec&Herr)".
    iMod ("Hewp" with "[Hstate Hspec Herr]") as "Hewp"; [iFrame|].
    iModIntro.
    iApply spec_coupl_bind; [done | | iFrame "Hewp"].
    iIntros (????) "Hewp".
    iApply fupd_spec_coupl.
    iMod "Hewp" as "(?&?&?&Hpa)".
    by rewrite protocol_agreement_bottom.
  - rewrite ewp_unfold /ewp_pre wp_unfold /wp_pre /= Heqo Heqo0.
    iIntros "H" (σ1 e1' σ1' ε1) "(Hstate & Hspec & Herr)".
    iMod ("H" with "[$Hstate $Hspec $Herr]") as "H".
    iModIntro.
    iApply spec_coupl_mono; [done | | done].
    iIntros (σ2 e2' σ2' ε2) "H".
    iApply prog_coupl_mono; [|done].
    iIntros (e3 σ3 e3' σ3' ε3) "H". iNext.
    iApply spec_coupl_mono; [done | | done].
    iIntros (σ5 e4' σ4 ε4) "H".
    iMod "H" as "(?&?&?&?)". iModIntro. iFrame.
    by iApply "IH".
Qed.

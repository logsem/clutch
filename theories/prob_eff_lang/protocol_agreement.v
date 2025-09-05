From iris.proofmode      Require Import base tactics classes.
From iris.base_logic.lib Require Import iprop.
From iris.program_logic  Require Import weakestpre language.
From clutch.prob_eff_lang Require Import lang iEff.


(** * Protocol Agreement. *)

Section protocol_agreement.
Context `{!irisGS eff_lang Σ}.

Definition protocol_agreement v Ψ (Φ : val -d> iPropO Σ) :=
  let: P := iEff_car Ψ in
  (∃ Q, P v Q ∗ □ (∀ w, Q w -∗ Φ w))%I.
Arguments protocol_agreement _%_V _%_ieff _%_I.

Global Instance protocol_agreement_ne v n :
  Proper ((dist n) ==> (dist n) ==> (dist n)) (protocol_agreement v).
Proof.
  intros ??? ???. rewrite /protocol_agreement.
  by repeat (apply H || apply H0 || f_equiv).
Qed.
Global Instance protocol_agreement_proper v :
  Proper ((≡) ==> (≡) ==> (≡)) (protocol_agreement v).
Proof.
  intros ??? ???. apply equiv_dist=>n.
  apply protocol_agreement_ne; by apply equiv_dist.
Qed.

Lemma protocol_agreement_bottom v Φ :
  protocol_agreement v ⊥ Φ ≡ False%I.
Proof.
  rewrite /protocol_agreement.
  iSplit; iIntros "H"; [|done]. by iDestruct "H" as (Q) "[H _]".
Qed.

Lemma protocol_agreement_mono v (Ψ : iEff Σ) Φ1 Φ2 :
  (protocol_agreement v Ψ Φ1 -∗ □ (∀ w, Φ1 w -∗ Φ2 w) -∗
   protocol_agreement v Ψ Φ2)%ieff.
Proof.
  iIntros "Hprot_agr #HΦ2". iDestruct "Hprot_agr" as (Φ0) "[HP #HΦ1]".
  iExists Φ0. iFrame.
  iModIntro. iIntros (w) "HΦ0". iApply "HΦ2". by iApply "HΦ1".
Qed.

End protocol_agreement.


Program Definition iEff_le {Σ} : iEffO -n> iEffO -n> iPropO Σ :=
  λne Ψ1 Ψ2,
    (□ (∀ v Φ, protocol_agreement v Ψ1 Φ -∗ protocol_agreement v Ψ2 Φ))%I.
Next Obligation. intros ??????. repeat (apply iEff_car_ne || f_equiv); done. Defined.
Next Obligation. intros ??????. simpl. repeat (apply iEff_car_ne || f_equiv); done. Defined.
(*Arguments iEff_le {_} _%_ieff _%_ieff.*)
Instance: Params (@iEff_le) 3 := {}.

Infix "⊑" := (iEff_le) (at level 70, only parsing) : ieff_scope.




Section protocol_agreement_monotonicity.
Context `{!irisGS eff_lang Σ}.

Lemma protocol_agreement_strong_mono v (Ψ1 Ψ2 : iEff Σ) Φ1 Φ2 :
  (protocol_agreement v Ψ1 Φ1 -∗ Ψ1 ⊑ Ψ2 -∗ □ (∀ v, Φ1 v -∗ Φ2 v) -∗
   protocol_agreement v Ψ2 Φ2)%ieff.
Proof.
  iIntros "Hprot_agr #HΨ HΦ". iApply "HΨ".
  by iApply (protocol_agreement_mono with "Hprot_agr HΦ").
Qed.

End protocol_agreement_monotonicity.


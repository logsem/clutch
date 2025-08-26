From iris.proofmode      Require Import base tactics classes.
From iris.base_logic.lib Require Import iprop.
From iris.program_logic  Require Import weakestpre.
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



End protocol_agreement.

From clutch.prob_eff_lang.probblaze Require Import primitive_laws.
From iris.proofmode Require Import base proofmode.
From clutch.prob_eff_lang.probblaze Require Import syntax semantics notation class_instances logic.

(* Consider generalizing the PureExec construction *)
Definition prel `{Σ : gFunctors} (e1 e2 : expr) (Φ : val → val → iProp Σ) : iProp Σ := 
  match (to_val e1), (to_val e2) with
  | Some v1, Some v2 => Φ v1 v2
  | Some v1, None => ∃ (v2 : val) n2 Ψ2, ⌜Ψ2 ∧ PureExec Ψ2 n2 e2 v2⌝ ∗ Φ v1 v2
  | None, Some v2 =>  ∃ (v1 : val) n1 Ψ1, ⌜Ψ1 ∧ PureExec Ψ1 n1 e1 v1⌝ ∗ Φ v1 v2
  | None, None => ∃ (v1 v2 : val) n1 n2 Ψ1 Ψ2,  ⌜Ψ1 ∧ PureExec Ψ1 n1 e1 v1 ∧ Ψ2 ∧ PureExec Ψ2 n2 e2 v2⌝ ∗ Φ v1 v2
  end. 

Lemma prel_intuitionistically `{Σ : gFunctors} e1 e2 Φ : 
  (□ prel e1 e2 Φ) -∗ @prel Σ e1 e2 (λ v1 v2, □ (Φ v1 v2)).
Proof.
  iIntros "#Hrel". unfold prel.
  destruct (to_val e1) eqn:Heq1, (to_val e2) eqn:Heq2; first done.
  1, 2: iDestruct "Hrel" as (???) "H"; iExists _,_; iDestruct "H" as "($ & H2)"; by iModIntro. 
  iDestruct "Hrel" as (??????) "H". iExists _,_,_,_. iDestruct "H" as "($ & H2)". by iModIntro. 
Qed. 

Notation "'PREL' e1 ≤ e2 '[{' Φ '}]'" := (prel e1%E e2%E Φ)
                                           (at level 20, e1, e2, Φ at next level, only parsing) : bi_scope.
Lemma prel_brel `{!probblazeRGS Σ} e1 e2 Φ :                         
  prel e1 e2 Φ -∗ brel ⊤ e1 e2 ⊥ Φ.
Proof. 
  iIntros "He". 
  destruct (to_val e1) eqn:Heq1, (to_val e2) eqn:Heq2; rewrite /prel Heq1 Heq2/=.
  - rewrite -(of_to_val _ _ Heq1). rewrite -(of_to_val _ _ Heq2). iApply brel_value. by iIntros "$ !>".
  - rewrite -(of_to_val _ _ Heq1). iDestruct "He" as (???(?&?)) "HΦ".
    iApply brel_pure_step_r; first done. iApply brel_value. by iIntros "$ !>".
  - rewrite -(of_to_val _ _ Heq2). iDestruct "He" as (???(?&?)) "HΦ".
    iApply brel_pure_step_later; first done. iApply brel_value. by iIntros "!> $ !>".
  - iDestruct "He" as (??????(?&?&?&?)) "H". iApply brel_pure_step_r; first done.
    iApply brel_pure_step_later; first done. iApply brel_value.
    by iIntros "!> $ !>".
Qed. 

Lemma prel_mono `{Σ : gFunctors} e1 e2 Φ Ψ : 
  (∀ v1 v2, Φ v1 v2 -∗ Ψ v1 v2) -∗
  PREL e1 ≤ e2 [{ Φ }] -∗ @prel Σ e1 e2 Ψ.
Proof.
  iIntros "Hvv Hprel". rewrite /prel.
  destruct (to_val e1) eqn:Heq1, (to_val e2) eqn:Heq2; [by iApply "Hvv" | | |].
  1,2: iDestruct "Hprel" as (???) "($ & H)"; by iApply "Hvv".
  iDestruct "Hprel" as (??????) "($ & H)"; by iApply "Hvv".
Qed.

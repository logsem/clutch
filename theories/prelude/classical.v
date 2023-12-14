From Coq.Logic Require Import ClassicalEpsilon.
From Coq.Logic Require Export FunctionalExtensionality PropExtensionality.
From stdpp Require Import prelude.

Lemma ExcludedMiddle (P : Prop) : P ∨ ¬ P.
Proof. destruct (excluded_middle_informative P); auto. Qed. 

Lemma make_proof_irrel (P : Prop) : ProofIrrel P.
Proof. intros ??; apply proof_irrelevance. Qed.

Lemma make_decision P : Decision P.
Proof.
  assert (∃ x : Decision P, True) as Hdecex.
  { destruct (ExcludedMiddle P) as [HP|HnP].
    - exists (left HP); done.
    - exists (right HnP); done. }
  apply constructive_indefinite_description in Hdecex.
  exact (proj1_sig Hdecex).
Qed.

Lemma make_decision_fun {A : Type} (P : A -> Prop) : (∀ a, Decision (P a)).
Proof.
  intros.
  apply make_decision.
Qed.

Lemma make_decision_rel {A B : Type} (R : A -> B -> Prop) : (∀ a b, Decision (R a b)).
Proof.
  intros.
  apply make_decision.
Qed.

Lemma NNP_P : ∀ P : Prop, ¬ ¬ P → P.
Proof.
  intros P NNP.
  destruct (ExcludedMiddle P); [trivial; fail|].
  exfalso; apply NNP; trivial.
Qed.

Lemma P_NNP : ∀ P : Prop, P → ¬ ¬ P.
Proof.
  intros P HP HnP; apply HnP; trivial.
Qed.

Lemma contrapositive : ∀ P Q : Prop, (¬ Q → ¬ P) → P → Q.
Proof.
  intros P Q Hcontra HP.
  destruct (ExcludedMiddle Q); [trivial; fail|].
  exfalso; apply Hcontra; trivial.
Qed.

Lemma not_exists_forall_not :
  ∀ (A : Type) (P : A → Prop), ¬ (∃ x, P x) → ∀ x, ¬ P x.
Proof. intros A P Hnex x HP; apply Hnex; eauto. Qed.

Lemma not_forall_exists_not :
  ∀ (A : Type) (P : A → Prop), ¬ (∀ x, P x) → ∃ x, ¬ P x.
Proof.
  intros A P.
  apply contrapositive.
  intros Hnex; apply P_NNP.
  intros x; apply NNP_P; revert x.
  apply not_exists_forall_not; trivial.
Qed.

Lemma not_and_or_not P Q :
  ¬ (P ∧ Q) →  ¬ P ∨ ¬ Q.
Proof.
  intros Hand.
  destruct (ExcludedMiddle P) as [HP|HnP]; [|auto].
  destruct (ExcludedMiddle Q) as [HQ|HnQ]; [|auto].
  tauto.
Qed.

Lemma partial_inv_fun {A B : Type} (f : A -> B) :
  {f_inv : B -> option A | (forall b a, (f_inv b = Some a -> f a = b) /\ (f_inv b = None -> f a ≠ b)) }.
Proof.
  epose proof (Choice B (option A) (λ b o, forall a, (o = Some a -> f a = b) /\ (o = None -> f a ≠ b))  _) as (g & Hg).
  by exists g.
  Unshelve.
  intros b.
  destruct (ExcludedMiddle (exists a, f a = b)) as [ (a &Ha) | Hb].
  - exists (Some a).
    intros a'; split; intros HS; try done.
    inversion HS.
    rewrite <- Ha.
    f_equal; auto.
  - exists None.
    intros a'; split; intros HS; try done.
    intro. apply Hb. by exists a'.
Qed.

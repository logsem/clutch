From Coq.Logic Require Export FunctionalExtensionality PropExtensionality.
From stdpp Require Import prelude.

Axiom Choice :
  ∀ A B (R : A → B → Prop), (∀ x, ∃ y, R x y) → {f : A → B | ∀ x, R x (f x)}.

Definition epsilon {A : Type} {P : A → Prop} (Hex : ∃ x, P x) : A :=
  proj1_sig (Choice unit A (λ _ x, P x) (λ _, Hex)) tt.

Lemma epsilon_correct {A : Type} (P : A → Prop) (Hex : ∃ x, P x) :
  P (epsilon Hex).
Proof.
  exact (proj2_sig (Choice unit A (λ _ x, P x) (λ _, Hex)) tt).
Qed.

Lemma ExcludedMiddle (P : Prop) : P ∨ ¬ P.
Proof.
  set (PA b := b = true ∨ P).
  set (PB b := b = false ∨ P).
  set (U := sig (λ s, s = PA ∨ s = PB)).
  set (R := (λ u b, proj1_sig u b) : U → bool → Prop).
  assert (∀ u, ∃ b, R u b) as HR.
  { intros u.
    unfold R.
    destruct (proj2_sig u) as [->| ->]; unfold PA, PB; eauto. }
  apply Choice in HR as [f Hf].
  set (A := exist _ _ (or_introl eq_refl) : U); simpl in *.
  set (B := exist _ _ (or_intror eq_refl) : U); simpl in *.
  assert (P ↔ A = B) as HPAB.
  { split.
    - intros HP.
      unfold A, B.
      assert (PA = PB) as ->.
      { unfold PA, PB.
        extensionality x; apply propositional_extensionality; tauto. }
      rewrite (proof_irrelevance _ (or_introl eq_refl) (or_intror eq_refl));
        trivial.
    - intros HAB.
      assert (proj1_sig A = proj1_sig B) as HPAB; [rewrite HAB; trivial|].
      simpl in *.
      assert (PA false) as HPAf; [rewrite HPAB; unfold PB; auto; fail|].
      destruct HPAf; [congruence| trivial]. }
  pose proof (Hf A) as HfA.
  pose proof (Hf B) as HfB.
  simpl in *.
  destruct (f A) eqn:Aeq.
  - destruct (f B) eqn:Beq.
    + destruct HfB; [congruence| auto].
    + right. intros HP; apply HPAB in HP. congruence.
  - destruct HfA; [congruence| auto].
Qed.

Lemma make_proof_irrel (P : Prop) : ProofIrrel P.
Proof. intros ??; apply proof_irrelevance. Qed.

Lemma make_decision P : Decision P.
Proof.
  assert (∃ x : Decision P, True) as Hdecex.
  { destruct (ExcludedMiddle P) as [HP|HnP].
    - exists (left HP); done.
    - exists (right HnP); done. }
  apply epsilon in Hdecex; done.
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

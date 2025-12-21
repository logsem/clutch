From Stdlib Require Import Logic.Classical_Pred_Type.
From Stdlib Require Import Reals Psatz.
From Coquelicot Require Import Series Lim_seq Rbar Rcomplements.
From stdpp Require Export countable sets.
From clutch.prelude Require Import base Coquelicot_ext stdpp_ext classical.
From discprob.prob Require Import double.
Set Default Proof Using "Type*".
Import Hierarchy.

Local Open Scope R.

Section FiberSup.
  Context {A B : Type}
          (F : A → B)
          (f : A → R)
          (Hf : ∀ a, f a <= 1).

  Definition fiber_E (b : B) : R → Prop :=
    fun x => x = 0 \/ ∃ a, F a = b /\ x = f a.

  Lemma fiber_bound b : bound (fiber_E b).
  Proof.
    unfold bound, is_upper_bound, fiber_E.
    exists 1. intros.
    destruct H; subst; try lra.
    destruct H. destruct H. subst.
    apply Hf.
  Qed.

  Lemma fiber_nonempty b : ∃ x, fiber_E b x.
  Proof. exists 0; left; reflexivity. Qed.

  Definition sup_fiber (b : B) : R :=
    proj1_sig
      (completeness
         (fiber_E b)
         (fiber_bound b)
         (fiber_nonempty b)).

  Lemma sup_fiber_is_lub b :
    is_lub (fiber_E b) (sup_fiber b).
  Proof.
    unfold sup_fiber.
    destruct (completeness _ (fiber_bound b) (fiber_nonempty b)) as [m Hm].
    simpl; exact Hm.
  Qed.

  Lemma sup_fiber_range b : 
    0 <= sup_fiber b <= 1.
  Proof.
    pose proof (sup_fiber_is_lub b).
    rewrite /is_lub /is_upper_bound in H.
    destruct H.
    split.
    - apply H. by econstructor.
    - apply H0. intros. 
      destruct H1; subst; try lra.
      destruct H1; destruct H1; subst.
      by apply Hf.
  Qed.

  Lemma sup_fiber_empty b :
    (∀ a, F a ≠ b) -> 
      sup_fiber b = 0.
  Proof.
    intros.
    pose proof (sup_fiber_range b).
    apply Rle_antisym.
    2 : lra.
    apply sup_fiber_is_lub.
    move => x Hx.
    inversion Hx; try by subst.
    destruct H1 as [a [Ha0 Ha1]].
    exfalso.
    by apply (H a).
  Qed.
    

End FiberSup.

Section FiberInf.

  Context {A B : Type}
          (F : A → B)
          (f : A → R)
          (Hf : ∀ a, 0 <= f a).

  Definition fiber_I (b : B) : R → Prop :=
    fun x => x = 1 \/ ∃ a, F a = b /\ x = f a.
  
  Definition fiber_I_neg (b : B) : R → Prop :=
    fun x => x = -1 \/ ∃ a, F a = b /\ x = - f a.

  Lemma fiber_I_neg_nonempty b : ∃ x, fiber_I_neg b x.
  Proof.
    exists (-1); left; reflexivity.
  Qed.

  Lemma fiber_I_neg_bound b : bound (fiber_I_neg b).
  Proof.
    unfold bound, is_upper_bound, fiber_I_neg.
    exists 0. intros x [ -> | [a [HFa Hx]] ].
    - by subst; lra.
    - subst. specialize (Hf a). lra.
  Qed.

  Definition sup_I_neg (b : B) : R :=
    proj1_sig
      (completeness
         (fiber_I_neg b)
         (fiber_I_neg_bound b)
         (fiber_I_neg_nonempty b)).
  
  Definition inf_fiber (b : B) : R := - sup_I_neg b.

  Definition is_lower_bound (E : R → Prop) (m : R) : Prop :=
    ∀ x, E x → m <= x.

  Definition is_glb (E : R → Prop) (m : R) : Prop :=
    is_lower_bound E m
    ∧ ∀ b, is_lower_bound E b → b <= m.

  Lemma inf_fiber_is_glb b : is_glb (fiber_I b) (inf_fiber b).
  Proof.
    rewrite /inf_fiber.  
    unfold sup_I_neg. 
    destruct (completeness _ (fiber_I_neg_bound b) (fiber_I_neg_nonempty b))
      as [M HM].  
    simpl. 
    destruct HM. 
    split.
    - move => x Hx.
      apply Ropp_le_cancel.
      ring_simplify.
      apply H. 
      destruct Hx as [ -> | [a [HFa Hx]] ].
      + econstructor. lra.
      + right. econstructor. split; eauto; lra.
    - intros. 
      apply Ropp_le_cancel.
      ring_simplify.
      apply H0.
      move => x Hx.
      apply Ropp_le_cancel.
      ring_simplify. 
      apply H1.
      destruct Hx as [ -> | [a [HFa Hx]] ].
      + econstructor. lra.
      + right. econstructor. split; eauto; lra.
  Qed.

  Lemma inf_fiber_range b : 
    0 <= inf_fiber b <= 1.
  Proof.
    pose proof (inf_fiber_is_glb b).
    rewrite /is_glb /is_lower_bound in H.
    destruct H. 
    split.
    - apply H0. intros. 
      destruct H1; subst; try lra.
      destruct H1; destruct H1; subst.
      by apply Hf.
    - apply H. by econstructor.
  Qed.

  Lemma inf_fiber_empty b : 
    (∀ a, F a ≠ b) -> 
      inf_fiber b = 1.
  Proof.
    intros.
    pose proof (inf_fiber_range b).
    apply Rle_antisym.
    { lra. }
    apply inf_fiber_is_glb.
    move => x Hx.
    inversion Hx; try by subst.
    destruct H1 as [a [Ha0 Ha1]].
    exfalso.
    by apply (H a).
  Qed.

End FiberInf.

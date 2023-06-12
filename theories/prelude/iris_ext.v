From iris.bi Require Export bi fixpoint.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export fancy_updates.
Import uPred.

(* TODO: upstream? *)
Section fupd_plainly_derived.
  Context {PROP : bi}.
  Context `{!BiFUpd PROP, !BiPlainly PROP, !BiFUpdPlainly PROP}.

  Lemma step_fupd_mono Eo Ei (P Q : PROP) :
    (P ⊢ Q) → (|={Eo}[Ei]▷=> P) ⊢ (|={Eo}[Ei]▷=> Q).
  Proof. intros HPQ. by apply fupd_mono, later_mono, fupd_mono. Qed.

  Lemma step_fupd_except_0 E1 E2 (P : PROP) : (|={E1}[E2]▷=> ◇ P) ={E1}[E2]▷=∗ P.
  Proof. rewrite fupd_except_0 //. Qed.

  Lemma step_fupdN_except_0 E1 E2 (P : PROP) n : (|={E1}[E2]▷=>^(S n) ◇ P) ={E1}[E2]▷=∗^(S n) P.
  Proof.
    induction n as [|n IH]; [apply step_fupd_except_0|].
    replace (S (S n)) with (1 + S n)%nat by lia.
    rewrite 2!step_fupdN_add. by apply step_fupd_mono.
  Qed.

  Lemma step_fupdN_plain_forall E {A} (Φ : A → PROP) `{!∀ x, Plain (Φ x)} n :
    (|={E}▷=>^n ∀ x, Φ x) ⊣⊢ (∀ x, |={E}▷=>^n Φ x).
  Proof .
    intros. apply (anti_symm _).
    { apply forall_intro=> x. apply step_fupdN_mono. eauto. }
    destruct n; [done|].
    trans (∀ x, |={E}=> ▷^(S n) ◇ Φ x)%I.
    { apply forall_mono=> x. by rewrite step_fupdN_plain. }
    rewrite -fupd_plain_forall'.
    rewrite -step_fupdN_except_0 /= -step_fupdN_intro //.
    apply fupd_elim.
    rewrite -later_forall -laterN_forall -except_0_forall.
    apply step_fupd_intro. done.
  Qed.

End fupd_plainly_derived.

Section class_instance_updates.
  Context {PROP : bi}.

  Global Instance from_forall_step_fupdN
    `{!BiFUpd PROP, !BiPlainly PROP, !BiFUpdPlainly PROP} E {A} P (Φ : A → PROP) name n :
    FromForall P Φ name → (∀ x, Plain (Φ x)) →
    FromForall (|={E}▷=>^n P) (λ a, |={E}▷=>^n (Φ a))%I name.
  Proof.
    rewrite /FromForall=>? ?.
    rewrite -step_fupdN_plain_forall. by apply step_fupdN_mono.
  Qed.
End class_instance_updates.


Section bi_least_fixpoint.

  Lemma least_fixpoint_ne_outer {PROP : bi} {A : ofe}
    (F1 : (A → PROP) → (A → PROP)) (F2 : (A → PROP) → (A → PROP)) n :
    (∀ Φ x, F1 Φ x ≡{n}≡ F2 Φ x) → ∀ x1 x2,
        x1 ≡{n}≡ x2 → bi_least_fixpoint F1 x1 ≡{n}≡ bi_least_fixpoint F2 x2.
  Proof.
    intros HF x1 x2 Hx. rewrite /bi_least_fixpoint /=.
    do 3 f_equiv; last solve_proper. repeat f_equiv. apply HF.
  Qed.

End bi_least_fixpoint.

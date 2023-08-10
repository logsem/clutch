From iris.bi Require Export bi fixpoint.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export fancy_updates.
Import uPred.

(* TODO: upstream? *)
Section fupd_plainly_derived.
  Context {PROP : bi}.
  Context `{!BiFUpd PROP, !BiPlainly PROP, !BiFUpdPlainly PROP}.

  Lemma step_fupdN_fupd_swap {E : coPset} (P: PROP) (n: nat):
    (|={E}▷=>^n |={E}=> P) ⊢ |={E}=> |={E}▷=>^n P.
  Proof.
    induction n => //=.
    iIntros "H". iMod "H". iModIntro. iModIntro. iNext. iMod "H".
    by iApply IHn.
  Qed.

  Lemma step_fupdN_Sn (P : PROP) E n :
    (|={E}▷=>^(S n) P) ⊣⊢ |={E}▷=> |={E}▷=>^n P.
  Proof. done. Qed.

  Lemma step_fupdN_Sn_r (P : PROP) n E :
    (|={E}▷=>^(S n) P) ⊣⊢ |={E}▷=>^n |={E}▷=> P.
  Proof.
    replace (S n) with (n + 1) by lia.
    rewrite step_fupdN_add //.
  Qed.

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

  Global Instance step_fupdN_ne k E1 E2:
    NonExpansive (λ P : PROP, |={E2}[E1]▷=>^k P)%I.
  Proof.
    induction k; simpl; solve_proper.
  Qed.

  Lemma step_fupd_and (P Q : PROP) E :
    (|={E}▷=> P ∧ Q) ⊢ (|={E}▷=> P) ∧ (|={E}▷=> Q).
  Proof.
    rewrite fupd_and.
    iIntros "H".
    iSplit; iMod "H".
    - do 2 iModIntro. iDestruct "H" as "[$ _]".
    - do 2 iModIntro. iDestruct "H" as "[_ $]".
  Qed.

  Lemma step_fupdN_and (P Q : PROP) E n :
    (|={E}▷=>^n P ∧ Q) ⊢ (|={E}▷=>^n P) ∧ (|={E}▷=>^n Q).
  Proof.
    induction n; [done|].
    (* rewrite step_fupdN_Sn_r. *)
    iIntros "H".
    rewrite 2!step_fupdN_Sn.
    iSplit; iMod "H".
    - do 2 iModIntro. iMod "H". iModIntro.
      iApply and_elim_l. by iApply IHn.
    - do 2 iModIntro. iMod "H". iModIntro.
      iApply and_elim_r. by iApply IHn.
  Qed.

End fupd_plainly_derived.

Section step_fupdN.
  Context {PROP : bi} `{FU: BiFUpd PROP}.

  Lemma step_fupdN_mask_comm n E1 E2 E3 E4 (P: PROP):
    E1 ⊆ E2 → E4 ⊆ E3 →
    ((|={E1, E2}=>|={E2}[E3]▷=>^n P) ⊢ |={E1}[E4]▷=>^n |={E1, E2}=> P)%I.
  Proof.
    iIntros (Hsub1 Hsub2) "H". iInduction n as [|n] "IH"; auto; simpl.
    iMod "H". iMod "H". iMod (fupd_mask_subseteq E4) as "Hclose"; auto.
    iModIntro. iNext. iMod "Hclose". iMod "H".
    iMod (fupd_mask_subseteq E1) as "Hclose'"; auto.
    iModIntro. iApply "IH". iMod "Hclose'". by iModIntro.
  Qed.

  Lemma step_fupdN_mask_comm' n E1 E2 (P: PROP):
    E2 ⊆ E1 →
    ((|={E1}[E1]▷=>^n |={E1, E2}=> P) ⊢ |={E1, E2}=> |={E2}[E2]▷=>^n P)%I.
  Proof.
    iIntros (Hsub) "H". iInduction n as [|n] "IH"; auto; simpl.
    iMod "H". iMod (fupd_mask_subseteq E2) as "Hclose"; auto.
    do 2 iModIntro. iNext. iMod "Hclose". iMod "H". by iApply "IH".
  Qed.

End step_fupdN.

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

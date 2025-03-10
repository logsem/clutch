From Coq Require Import Reals Psatz.
From iris.base_logic.lib Require Export fancy_updates.
From iris.proofmode Require Import base tactics classes.
From clutch.prelude Require Import classical.
From clutch.con_prob_lang Require Import lang spec_transition.
From clutch.common Require Export con_language.
From clutch.prob Require Export distribution.

Set Default Proof Using "Type*".

Class spec_updateGS (Σ : gFunctors) := Spec_updateGS {
  spec_interp : cfg con_prob_lang → iProp Σ;
}.
Global Arguments Spec_updateGS {_ _}.

(* a update modality for stepping spec steps without having to couple with implementation *)
Section spec_update.
  Context `{!spec_updateGS Σ, !invGS_gen hl Σ}.
  Definition spec_update_def (E : coPset) (P : iProp Σ) : iProp Σ :=
    (∀ ρ, spec_interp ρ -∗ |={E}=> ∃ μ, ⌜spec_transition ρ μ ⌝ ∗
                                       (∀ ρ', ⌜(μ ρ'>0)%R⌝ -∗ (spec_interp ρ' ∗ P)))%I.
  Local Definition spec_update_aux : seal (@spec_update_def). Proof. by eexists. Qed.
  Definition spec_update := spec_update_aux.(unseal).
  Lemma spec_update_unseal : spec_update = spec_update_def.
  Proof. rewrite -spec_update_aux.(seal_eq) //. Qed.

  Lemma spec_update_ret E P :
    P ⊢ spec_update E P.
  Proof.
    rewrite spec_update_unseal.
    iIntros "HP" (a) "Ha !#".
    iExists _.
    iFrame.
    iSplit.
    - iPureIntro. apply spec_transition_dret.
    - iIntros (??). by rewrite (dret_pos a x).
  Qed.

  Lemma spec_update_bind E1 E2 P Q :
    E1 ⊆ E2 →
    spec_update E1 P ∗ (P -∗ spec_update E2 Q) ⊢ spec_update E2 Q.
  Proof.
    rewrite !spec_update_unseal. iIntros (HE) "[P PQ] %a Ha".
    iMod (fupd_mask_subseteq E1) as "Hclose"; [done|].
    iMod ("P" $! a with "Ha") as (μ Hμ) "H".
    iMod "Hclose" as "_".
    iAssert (∀ ρ', ⌜μ ρ' > 0⌝ ={E2}=∗
            ∃ μ0, ⌜spec_transition ρ' μ0⌝ ∗
              ∀ ρ'0, ⌜μ0 ρ'0 > 0⌝ -∗ spec_interp ρ'0 ∗ Q)%I with "[-]" as "H".
    { iIntros. iDestruct ("H" with "[//]") as "[H1 H2]".
      iDestruct ("PQ" with "[$]") as "H".
      by iDestruct ("H" with "H1") as "H".
    }
    iAssert (∀ ρ', |={E2}=> ∃ μ0,  ⌜μ ρ' > 0⌝ -∗
                          ⌜spec_transition ρ' μ0⌝ ∗
                          ∀ ρ'0, ⌜μ0 ρ'0 > 0⌝ -∗ spec_interp ρ'0 ∗ Q)%I with "[-]" as "H".
    { iIntros (ρ').
      iDestruct ("H"$! ρ') as "H".
      destruct (pmf_pos μ ρ') as [|<-]; last first.
      - iExists dzero. iModIntro. iIntros (?). lra.
      - iDestruct ("H" with "[]") as ">(%&%&H)"; first (iPureIntro; lra).
        iModIntro.
        iExists _. iIntros. by iSplit. 
    }
    
    
  Admitted.

  (* Lemma spec_update_mono_fupd E P Q : *)
  (*   spec_update E P ∗ (P ={E}=∗ Q) ⊢ spec_update E Q. *)
  (* Proof. *)
  (*   rewrite spec_update_unseal. *)
  (*   iIntros "[HP PQ] %a Hsrc". *)
  (*   iMod ("HP" with "Hsrc") as (b n Hstep) "[Hsrc P]". *)
  (*   iMod ("PQ" with "P"). iFrame. eauto.  *)
  (* Qed. *)

  (* Lemma spec_update_mono E P Q : *)
  (*   spec_update E P ∗ (P -∗ Q) ⊢ spec_update E Q. *)
  (* Proof. *)
  (*   iIntros "[Hupd HPQ]". *)
  (*   iApply (spec_update_mono_fupd with "[$Hupd HPQ]"). *)
  (*   iIntros "P". iModIntro. by iApply "HPQ". *)
  (* Qed. *)

  (* Lemma fupd_spec_update E P : *)
  (*   (|={E}=> spec_update E P) ⊢ spec_update E P. *)
  (* Proof. *)
  (*   rewrite spec_update_unseal. *)
  (*   iIntros "H %e Hsrc". *)
  (*   iMod "H". by iApply "H". *)
  (* Qed. *)

  (* Lemma spec_update_frame_l R E P : *)
  (*   R ∗ spec_update E P ⊢ spec_update E (P ∗ R). *)
  (* Proof. *)
  (*   iIntros "[HR H]". *)
  (*   iApply spec_update_mono. *)
  (*   iFrame; eauto. *)
  (* Qed. *)

  (* Global Instance from_modal_spec_update_spec_update P E : *)
  (*   FromModal True modality_id (spec_update E P) (spec_update E P) P. *)
  (* Proof. iIntros (_) "HP /=". by iApply spec_update_ret. Qed. *)

  (* Global Instance elim_modal_spec_update_spec_update P Q E : *)
  (*   ElimModal True false false (spec_update E P) P (spec_update E Q) (spec_update E Q). *)
  (* Proof. iIntros (?) "[HP Hcnt]". by iApply (spec_update_bind with "[$]"). Qed. *)

  (* Global Instance frame_spec_update p E R P Q: *)
  (*   Frame p R P Q → Frame p R (spec_update E P) (spec_update E Q). *)
  (* Proof. *)
  (*   rewrite /Frame=> HR. *)
  (*   rewrite spec_update_frame_l. *)
  (*   iIntros "H". *)
  (*   iApply spec_update_mono; iFrame. *)
  (*   iIntros "[? ?]". *)
  (*   iApply HR; iFrame. *)
  (* Qed. *)

  (* Global Instance from_pure_bupd b E P φ : *)
  (*   FromPure b P φ → FromPure b (spec_update E P) φ. *)
  (* Proof. *)
  (*   rewrite /FromPure=> HP. *)
  (*   iIntros "H !>". *)
  (*   by iApply HP. *)
  (* Qed. *)

  (* Global Instance into_wand_spec_update p q E R P Q : *)
  (*   IntoWand false false R P Q → IntoWand p q (spec_update E R) (spec_update E P) (spec_update E Q). *)
  (* Proof. *)
  (*   rewrite /IntoWand /= => HR. *)
  (*   rewrite !bi.intuitionistically_if_elim. *)
  (*   iIntros ">HR >HP !>". iApply (HR with "HR HP"). *)
  (* Qed. *)

  (* Global Instance into_wand_bupd_persistent p q E R P Q : *)
  (*   IntoWand false q R P Q → IntoWand p q (spec_update E R) P (spec_update E Q). *)
  (* Proof. *)
  (*   rewrite /IntoWand /= => HR. rewrite bi.intuitionistically_if_elim. *)
  (*   iIntros ">HR HP !>". *)
  (*   iApply (HR with "HR HP"). *)
  (* Qed. *)

  (* Global Instance into_wand_bupd_args p q E R P Q : *)
  (*   IntoWand p false R P Q → IntoWand' p q R (spec_update E P) (spec_update E Q). *)
  (* Proof. *)
  (*   rewrite /IntoWand' /IntoWand /= => ->. *)
  (*   rewrite bi.intuitionistically_if_elim. *)
  (*   iIntros "Hw HP". *)
  (*   iApply spec_update_mono; iFrame. *)
  (* Qed. *)

  (* Global Instance from_sep_bupd E P Q1 Q2 : *)
  (*   FromSep P Q1 Q2 → FromSep (spec_update E P) (spec_update E Q1) (spec_update E Q2). *)
  (* Proof. *)
  (*   rewrite /FromSep=> HP. *)
  (*   iIntros "[>HQ1 >HQ2] !>". *)
  (*   iApply HP. iFrame. *)
  (* Qed. *)

  (* Global Instance elim_modal_fupd_wp p E P Q : *)
  (*   ElimModal True p false (|={E}=> P) P (spec_update E Q) (spec_update E Q). *)
  (* Proof. *)
  (*   rewrite /ElimModal bi.intuitionistically_if_elim => _. *)
  (*   iIntros "[Hu Hw]". *)
  (*   iApply fupd_spec_update. *)
  (*   iMod "Hu". *)
  (*   iApply ("Hw" with "Hu"). *)
  (* Qed. *)

  (* Global Instance from_exist_spec_update {B} P E (Φ : B → iProp Σ) : *)
  (*   FromExist P Φ → FromExist (spec_update E P) (λ b, spec_update E (Φ b))%I. *)
  (* Proof. *)
  (*   rewrite /FromExist => HP. *)
  (*   iIntros "[%x >Hx] !>". *)
  (*   iApply HP. eauto. *)
  (* Qed. *)

  (* Global Instance into_forall_spec_update {B} P E (Φ : B → iProp Σ) : *)
  (*   IntoForall P Φ → IntoForall (spec_update E P) (λ b, spec_update E (Φ b))%I. *)
  (* Proof. *)
  (*   rewrite /IntoForall=>HP. *)
  (*   iIntros "> H" (b) "!>". *)
  (*   iApply (HP with "H"). *)
  (* Qed. *)

  (* Global Instance from_assumption_spec_update p E P Q : *)
  (*   FromAssumption p P Q → KnownRFromAssumption p P (spec_update E Q). *)
  (* Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply spec_update_ret. Qed. *)

End spec_update.

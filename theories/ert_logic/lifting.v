(** The "lifting lemmas" in this file serve to lift the rules of the operational
semantics to the program logic. *)
From iris.proofmode Require Import tactics.
From iris.prelude Require Import options.
From clutch.prelude Require Import NNRbar.
From clutch.ert_logic Require Import ert_weakestpre.


Section lifting.
Context `{!ertwpG Λ Σ}.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.

#[local] Open Scope R.

Lemma wp_lift_step_fupd_ERM E Φ e1 s :
  to_val e1 = None →
  (∀ σ1 x1,
    state_interp σ1 ∗ etc_supply x1
    ={E,∅}=∗
    ERM e1 σ1 x1 (λ '(e2, σ2) x2,
      ▷ |={∅,E}=> state_interp σ2 ∗ etc_supply x2 ∗ WP e2 @ s; E {{ Φ }}))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof. by rewrite ert_wp_unfold /ert_wp_pre =>->. Qed.

Lemma wp_lift_step_fupd E Φ e1 s :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E,∅}=∗
     ⌜reducible (e1, σ1)⌝ ∗
     ⧖ (nnreal_nat 1) ∗
     ∀ e2 σ2,
       ⌜prim_step e1 σ1 (e2, σ2) > 0 ⌝ ={∅}=∗ ▷ |={∅,E}=>
       state_interp σ2 ∗ WP e2 @ s; E {{ Φ }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply wp_lift_step_fupd_ERM; [done|].
  iIntros (σ1 x1) "[Hσ Hx]".
  iMod ("H" with "[$]") as "(%Hs & Hc & H)".
  iDestruct (etc_split_supply with "Hx Hc") as %[x2 ->].
  iModIntro.
  iApply (ERM_prim_step e1 σ1).
  iExists x2.
  iSplit; [done|].
  iSplit; [done|].
  iIntros (e2 σ2 ?).
  iMod (etc_decrease_supply with "Hx Hc") as "$".
  iMod ("H" with "[//]") as "H".
  by iIntros "!> !>".
Qed.

(** Derived lifting lemmas. *)
Lemma wp_lift_step E Φ e1 s :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E,∅}=∗
    ⌜reducible (e1, σ1)⌝ ∗
    ⧖ (nnreal_nat 1) ∗
    ▷ ∀ e2 σ2,
      ⌜prim_step e1 σ1 (e2, σ2) > 0⌝ ={∅,E}=∗
      state_interp σ2 ∗
      WP e2 @ s; E {{ Φ }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step_fupd; [done|]. iIntros (?) "Hσ".
  iMod ("H" with "[$]") as "($ & $ & H)". iIntros "!>" (???) "!>!>" . by iApply "H".
Qed.

Lemma wp_lift_pure_step `{!Inhabited (state Λ)} E E' Φ e1 s :
  (∀ σ1, reducible (e1, σ1)) →
  (∀ σ1 e2 σ2, prim_step e1 σ1 (e2, σ2) > 0 → σ2 = σ1) →
  ⧖ (nnreal_nat 1) ∗
  (|={E}[E']▷=> ∀ e2 σ, ⌜prim_step e1 σ (e2, σ) > 0⌝ → WP e2 @ s; E {{ Φ }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (Hsafe Hstep) "[Hc H]". iApply wp_lift_step.
  { by eapply (to_final_None_1 (e1, inhabitant)), reducible_not_final. }
  iIntros (σ1) "Hσ". iMod "H" as "H".
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
  iSplit; [done|].
  iFrame "Hc".
  iIntros "!>" (e2 σ2 Hprim).
  destruct (Hstep _ _ _ Hprim).
  iMod "Hclose" as "_". iMod "H".
  iDestruct ("H" with "[//]") as "H". by iFrame.
Qed.

(* Atomic steps don't need any mask-changing business here, one can *)
(* use the generic lemmas here. *)
Lemma wp_lift_atomic_step_fupd {E1 E2 Φ} e1 s :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E1}=∗
    ⌜reducible (e1, σ1)⌝ ∗
    ⧖ (nnreal_nat 1) ∗
    ∀ e2 σ2, ⌜prim_step e1 σ1 (e2, σ2) > 0⌝ ={E1}[E2]▷=∗
             state_interp σ2 ∗ from_option Φ False (to_val e2))
  ⊢ WP e1 @ s; E1 {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply (wp_lift_step_fupd E1 _ e1)=>//; iIntros (σ1) "Hσ1".
  iMod ("H" $! σ1 with "[$]") as "($ & $ & H)".
  iApply fupd_mask_intro; [set_solver|].
  iIntros "Hclose" (e2 σ2 Hs). iMod "Hclose" as "_".
  iMod ("H" $! e2 σ2 with "[#]") as "H"; [done|].
  iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose !>".
  iMod "Hclose" as "_". iMod "H" as "($ & ?)".
  destruct (to_val e2) eqn:?; last by iExFalso.
  iApply ert_wp_value; last done. by apply of_to_val.
Qed.

Lemma wp_lift_atomic_step {E Φ} e1 s :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E}=∗
    ⌜reducible (e1, σ1)⌝ ∗
    ⧖ (nnreal_nat 1) ∗
    ▷ ∀ e2 σ2, ⌜prim_step e1 σ1 (e2, σ2) > 0⌝ ={E}=∗
               state_interp σ2 ∗ from_option Φ False (to_val e2))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step_fupd; [done|].
  iIntros (?) "?". iMod ("H" with "[$]") as "($ & $ & H)".
  iIntros "!> *". iIntros (Hstep) "!> !>".
  by iApply "H".
Qed.

Lemma wp_lift_pure_det_step `{!Inhabited (state Λ)} {E E' Φ} e1 e2 s :
  (∀ σ1, reducible (e1, σ1)) →
  (∀ σ1 e2' σ2, prim_step e1 σ1 (e2', σ2) > 0 → σ2 = σ1 ∧ e2' = e2) →
  ⧖ (nnreal_nat 1) ∗ (|={E}[E']▷=> WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (? Hpuredet) "[Hc H]". iApply (wp_lift_pure_step E E'); try done.
  { naive_solver. }
  iFrame "Hc".
  iApply (step_fupd_wand with "H"); iIntros "H".
  iIntros (e' σ (?&->)%Hpuredet); auto.
Qed.

Lemma wp_pure_step_fupd `{!Inhabited (state Λ)} E E' e1 e2 φ n Φ s :
  PureExec φ n e1 e2 →
  φ →
  ⧖ (nnreal_nat n) ∗
  (|={E}[E']▷=>^n WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (Hexec Hφ) "[Hc Hwp]". specialize (Hexec Hφ).
  iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?]] "IH"; simpl; [done|].
  iApply wp_lift_pure_det_step.
  - done.
  - intros σ1 e2' σ2 Hpstep.
    by injection (pmf_1_supp_eq _ _ _ (pure_step_det σ1) Hpstep).
  - assert (nnreal_nat (S n) = (nnreal_nat n + (nnreal_nat 1))%NNR) as ->.
    { apply nnreal_ext =>/=. destruct n; [|done].
      rewrite INR_0 //. lra. }
    iDestruct (etc_split with "Hc") as "[Hc $]".
    iApply (step_fupd_wand with "Hwp").
    by iApply "IH".
Qed.

Lemma wp_pure_step_later `{!Inhabited (state Λ)} E e1 e2 φ n Φ s :
  PureExec φ n e1 e2 →
  φ →
  ⧖ (nnreal_nat n) ∗
  ▷^n WP e2 @ s; E {{ Φ }} ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (??) "[Hc Hwp]".
  iApply (wp_pure_step_fupd with "[$Hc Hwp]"); [done|].
  by iApply step_fupdN_intro.
Qed.

End lifting.

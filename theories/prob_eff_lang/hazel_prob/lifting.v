(** The "lifting lemmas" in this file serve to lift the rules of the operational
    semantics to the program logic. *)

From iris.proofmode Require Import tactics.
From iris.prelude Require Import options.
From clutch.prelude Require Import NNRbar.
From clutch.approxis Require Import primitive_laws.
From clutch.prob_eff_lang.hazel_prob Require Import weakestpre lang protocol_agreement.


Section lifting.
Context `{!spec_updateGS (lang_markov eff_prob_lang) Σ, !approxisWpGS eff_prob_lang Σ}.
Implicit Types v : val.
Implicit Types e : expr.
Implicit Types σ : state.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.

#[local] Open Scope R.

Lemma ewp_lift_step_couple E Φ Ψ e1 :
  (∀ σ1 e1' σ1' ε1,
      state_interp σ1 ∗ spec_interp (e1', σ1') ∗ err_interp ε1 ={E, ∅}=∗
      spec_coupl ∅ σ1 e1' σ1' ε1 (λ σ2 e2' σ2' ε2 ,
        match to_val e1 with
        | Some v => |={∅, E}=> state_interp σ2 ∗ spec_interp (e2', σ2') ∗
                               err_interp ε2 ∗ Φ v
        | None =>
            match to_eff e1 with
               | Some (v, K) =>
                   |={∅,E}=> state_interp σ2 ∗ spec_interp (e2', σ2') ∗ err_interp ε2 ∗
                             protocol_agreement v Ψ (λ w : val, ▷ EWP fill K (Val w) @ E <| Ψ |> {{ v, Φ v }})
               | None =>
                   prog_coupl e1 σ2 e2' σ2' ε2 (λ e3 σ3 e3' σ3' ε3,
                                                  ▷ spec_coupl ∅ σ3 e3' σ3' ε3 (λ σ4 e4' σ4' ε4,
                                                                                  |={∅, E}=> state_interp σ4 ∗ spec_interp (e4', σ4') ∗
                                                                                             err_interp ε4 ∗ EWP e3 @ E <| Ψ |> {{ Φ }}))
            end
        end))
  ⊢ EWP e1 @ E <| Ψ |> {{ Φ }}.
Proof. rewrite ewp_unfold /ewp_pre //. Qed.

Lemma ewp_lift_step_spec_couple E Φ Ψ e1 :
  (∀ σ1 e1' σ1' ε1,
      state_interp σ1 ∗ spec_interp (e1', σ1') ∗ err_interp ε1 ={E, ∅}=∗
      spec_coupl ∅ σ1 e1' σ1' ε1 (λ σ2 e2' σ2' ε2,
        |={∅, E}=> state_interp σ2 ∗ spec_interp (e2', σ2') ∗
                   err_interp ε2 ∗ EWP e1 @ E <| Ψ |> {{ Φ }}))
  ⊢ EWP e1 @ E <| Ψ |> {{ Φ }}.
Proof.
  iIntros "H".
  iApply ewp_lift_step_couple.
  iIntros (????) "Hs".
  iMod ("H" with "[$]") as "H".
  iModIntro.
  iApply (spec_coupl_bind with "[] H"); [done|].
  iIntros (????) "H".
  iApply fupd_spec_coupl.
  iMod "H" as "(?&?&?&H)".
  rewrite ewp_unfold /ewp_pre.
  iApply ("H" with "[$]").
Qed.

Lemma ewp_lift_step_prog_couple E Φ Ψ e1 :
  to_eff e1 = None →
  to_val e1 = None →
  (∀ σ1 e1' σ1' ε1,
      state_interp σ1 ∗ spec_interp (e1', σ1') ∗ err_interp ε1 ={E, ∅}=∗
      prog_coupl e1 σ1 e1' σ1' ε1 (λ e2 σ2 e2' σ2' ε2,
        ▷ |={∅, E}=> state_interp σ2 ∗ spec_interp (e2', σ2') ∗
                     err_interp ε2 ∗ EWP e2 @ E <| Ψ |> {{ Φ }}))
  ⊢ EWP e1 @ E <| Ψ |> {{ Φ }}.
Proof.
  iIntros (Heff Hv) "H".
  iApply ewp_lift_step_couple.
  iIntros (????) "Hs".
  iMod ("H" with "[$]") as "H".
  iApply spec_coupl_ret.
  iModIntro. rewrite Hv Heff.
  iApply (prog_coupl_mono with "[] H").
  iIntros (?????) "H !>".
  by iApply spec_coupl_ret.
Qed.

Lemma ewp_lift_step_later E Ψ Φ e1 :
  to_eff e1 = None → 
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E,∅}=∗
     ⌜reducible (e1, σ1)⌝ ∗
     ∀ e2 σ2,
      ⌜prim_step e1 σ1 (e2, σ2) > 0⌝ ={∅}=∗ ▷ |={∅,E}=>
      state_interp σ2 ∗ EWP e2 @ E <| Ψ |> {{ Φ }})
  ⊢ EWP e1 @ E <| Ψ |> {{ Φ }}.
Proof.
  iIntros (??) "H".
  iApply ewp_lift_step_prog_couple; [done|done|].
  iIntros (σ1 e1' σ1' ε1) "(Hσ & Hρ & Hε)".
  iMod ("H" with "Hσ") as "[%Hs H]". iModIntro.
  iApply prog_coupl_step_l; [done|].
  iIntros (???).
  iMod ("H" with "[//]") as "H".
  iIntros "!> !>".
  iMod "H" as "($ & $)".
  by iFrame.
Qed.

(** Derived lifting lemmas. *)
Lemma ewp_lift_step E Φ Ψ e1 :
  to_eff e1 = None → 
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E,∅}=∗
    ⌜reducible (e1, σ1)⌝ ∗
    ▷ ∀ e2 σ2,
     ⌜prim_step e1 σ1 (e2, σ2) > 0⌝ ={∅,E}=∗
      state_interp σ2 ∗
      EWP e2 @ E <| Ψ |> {{ Φ }})
  ⊢ EWP e1 @ E <| Ψ |> {{ Φ }}.
Proof.
  iIntros (??) "H". iApply ewp_lift_step_later; [done|done|]. iIntros (?) "Hσ".
  iMod ("H" with "Hσ") as "[$ H]". iIntros "!>" (???) "!>" . by iApply "H".
Qed.

Lemma ewp_lift_pure_step `{!Inhabited state} E E' Φ Ψ e1 :
  (∀ σ1, reducible (e1, σ1)) →
  (∀ σ1 e2 σ2, prim_step e1 σ1 (e2, σ2) > 0 → σ2 = σ1) →
  (|={E}[E']▷=> ∀ e2 σ, ⌜prim_step e1 σ (e2, σ) > 0⌝ → EWP e2 @ E <| Ψ |> {{ Φ }})
  ⊢ EWP e1 @ E <| Ψ |> {{ Φ }}.
Proof.
  iIntros (Hsafe Hstep) "H". iApply ewp_lift_step.
  { specialize (Hsafe inhabitant). by eapply reducible_not_eff. }
  { specialize (Hsafe inhabitant). by eapply (to_final_None_1 (e1, _)), reducible_not_final. }
  iIntros (σ1) "Hσ". iMod "H".
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
  iSplit; [done|].
  iNext. iIntros (e2 σ2 Hprim).
  destruct (Hstep _ _ _ Hprim).
  iMod "Hclose" as "_". iMod "H".
  iDestruct ("H" with "[//]") as "H". simpl. by iFrame.
Qed.

(* Atomic steps don't need any mask-changing business here, one can *)
(* use the generic lemmas here. *)
Lemma ewp_lift_atomic_step_fupd {E1 E2 Φ Ψ} e1  :
  to_eff e1 = None → 
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E1}=∗
    ⌜reducible (e1, σ1)⌝ ∗
    ∀ e2 σ2, ⌜prim_step e1 σ1 (e2, σ2) > 0⌝ ={E1}[E2]▷=∗
      state_interp σ2 ∗
      from_option Φ False (to_val e2))
  ⊢ EWP e1 @ E1 <| Ψ |> {{ Φ }}.
Proof.
  iIntros (??) "H".
  iApply (ewp_lift_step_later E1 _ _ e1)=>//; iIntros (σ1) "Hσ1".
  iMod ("H" $! σ1 with "Hσ1") as "[$ H]".
  iApply fupd_mask_intro; first set_solver.
  iIntros "Hclose" (e2 σ2 Hs). iMod "Hclose" as "_".
  iMod ("H" $! e2 σ2 with "[#]") as "H"; [done|].
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose !>".
  iMod "Hclose" as "_". iMod "H" as "($ & HQ)".
  destruct (to_val e2) eqn:?; last by iExFalso.
  iApply ewp_value; last done. by apply of_to_val.
Qed.

Lemma ewp_lift_atomic_step {E Φ Ψ} e1 :
  to_eff e1 = None →
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E}=∗
    ⌜reducible (e1, σ1)⌝ ∗
    ▷ ∀ e2 σ2, ⌜prim_step e1 σ1 (e2, σ2) > 0⌝ ={E}=∗
      state_interp σ2 ∗
      from_option Φ False (to_val e2))
  ⊢ EWP e1 @ E <| Ψ |> {{ Φ }}.
Proof.
  iIntros (??) "H". iApply ewp_lift_atomic_step_fupd; [done|done|].
  iIntros (?) "?". iMod ("H" with "[$]") as "[$ H]".
  iIntros "!> *". iIntros (Hstep) "!> !>".
  by iApply "H".
Qed.

Lemma ewp_lift_pure_det_step `{!Inhabited state} {E E' Φ Ψ} e1 e2 :
  (∀ σ1, reducible (e1, σ1)) →
  (∀ σ1 e2' σ2, prim_step e1 σ1 (e2', σ2) > 0 → σ2 = σ1 ∧ e2' = e2) →
  (|={E}[E']▷=> EWP e2 @ E <| Ψ |> {{ Φ }}) ⊢ EWP e1 @ E <| Ψ |> {{ Φ }}.
Proof.
  iIntros (? Hpuredet) "H". iApply (ewp_lift_pure_step E E'); try done.
  { naive_solver. }
  iApply (step_fupd_wand with "H"); iIntros "H".
  iIntros (e' σ (?&->)%Hpuredet); auto.
Qed.

Lemma ewp_pure_step_fupd `{!Inhabited state} E E' e1 e2 φ n Φ Ψ :
  PureExec φ n e1 e2 →
  φ →
  (|={E}[E']▷=>^n EWP e2 @ E <| Ψ |> {{ Φ }}) ⊢ EWP e1 @ E <| Ψ |> {{ Φ }}.
Proof.
  iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
  iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?]] "IH"; simpl; first done.
  iApply ewp_lift_pure_det_step.
  - eauto.
  - intros σ1 e2' σ2 Hpstep.
    by injection (pmf_1_supp_eq _ _ _ (pure_step_det σ1) Hpstep).
  - by iApply (step_fupd_wand with "Hwp").
Qed.

Lemma ewp_pure_step_later `{!Inhabited state} E e1 e2 φ n Φ Ψ :
  PureExec φ n e1 e2 →
  φ →
  ▷^n EWP e2 @ E <| Ψ |> {{ Φ }} ⊢ EWP e1 @ E <| Ψ |> {{ Φ }}.
Proof.
  intros Hexec ?. rewrite -ewp_pure_step_fupd //. clear Hexec.
  induction n as [|n IH]; by rewrite //= -step_fupd_intro // IH.
Qed.
End lifting.

Local Open Scope R.

Section ectx_lifting.
Context
  {Hinh : Inhabited state}
 `{!spec_updateGS (lang_markov eff_prob_lang) Σ, !approxisWpGS eff_prob_lang Σ}.

Implicit Types P : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types v : val.
Implicit Types e : expr.
Local Hint Resolve head_prim_reducible head_reducible_prim_step : core.
Local Hint Resolve head_stuck_stuck : core.

Lemma ewp_lift_head_step_prog_couple {E Φ Ψ} e1 :
  to_eff e1 = None → 
  to_val e1 = None →
  (∀ σ1 e1' σ1' ε1,
    state_interp σ1 ∗ spec_interp (e1', σ1') ∗ err_interp ε1 ={E,∅}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    prog_coupl e1 σ1 e1' σ1' ε1 (λ e2 σ2 e2' σ2' ε2,
      ▷ |={∅,E}=> state_interp σ2 ∗ spec_interp (e2', σ2') ∗
                  err_interp ε2 ∗ EWP e2 @ E <| Ψ |> {{ Φ }}))
  ⊢ EWP e1 @ E <| Ψ |> {{ Φ }}.
Proof.
  iIntros (??) "H". iApply ewp_lift_step_prog_couple; [done|done|].
  iIntros (σ1 e1' σ1' ε1) "Hσ".
  by iMod ("H" with "Hσ") as "[% H]".
Qed.

Lemma ewp_lift_head_step {E Φ Ψ} e1 :
  to_eff e1 = None → 
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E,∅}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ▷ ∀ e2 σ2, ⌜head_step e1 σ1 (e2, σ2) > 0⌝ ={∅,E}=∗
      state_interp σ2 ∗ EWP e2 @ E <| Ψ |> {{ Φ }})
  ⊢ EWP e1 @ E <| Ψ |> {{ Φ }}.
Proof.
  iIntros (??) "H". iApply ewp_lift_step_later; [done|done|]. iIntros (?) "Hσ".
  iMod ("H" with "Hσ") as "[% H]"; iModIntro.
  iSplit.
  { iPureIntro. assert (∃ ρ,  head_step e1 σ1 ρ > 0) as ((e2, σ2) & Hstep). { apply head_reducible_step. }
    eexists. by apply head_step_prim_step. }
  iIntros (???) "!> !>". iApply "H"; auto.
  iPureIntro.
  rewrite -head_prim_step_eq. done.
Qed.

Lemma ewp_lift_atomic_head_step_fupd {E1 E2 Φ Ψ} e1 :
  to_eff e1 = None →
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E1}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ∀ e2 σ2, ⌜head_step e1 σ1 (e2, σ2) > 0⌝ ={E1}[E2]▷=∗
      state_interp σ2 ∗
      from_option Φ False (to_val e2))
  ⊢ EWP e1 @ E1 <| Ψ |> {{ Φ }}.
Proof.
  iIntros (??) "H". iApply ewp_lift_atomic_step_fupd; [done|done|].
  iIntros (σ1) "Hσ1". iMod ("H" with "Hσ1") as "[% H]"; iModIntro.
  iSplit.
  { iPureIntro. assert (∃ ρ,  head_step e1 σ1 ρ > 0) as ((e2, σ2) & Hstep). { apply head_reducible_step. }
    eexists. by apply head_step_prim_step. } 
  iIntros (e2 σ2 Hstep).
  iApply "H".
  iPureIntro.
  rewrite -head_prim_step_eq. done.
Qed.

Lemma ewp_lift_atomic_head_step {E Φ Ψ} e1 :
  to_eff e1 = None →
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ▷ ∀ e2 σ2, ⌜head_step e1 σ1 (e2, σ2) > 0⌝ ={E}=∗
      state_interp σ2 ∗
      from_option Φ False (to_val e2))
  ⊢ EWP e1 @ E <| Ψ |>{{ Φ }}.
Proof.
  iIntros (??) "H". iApply ewp_lift_atomic_step; eauto.
  iIntros (σ1) "Hσ1". iMod ("H" with "Hσ1") as "[% H]"; iModIntro.
  iSplit.
  { iPureIntro.  assert (∃ ρ,  head_step e1 σ1 ρ > 0) as ((e2, σ2) & Hstep). { apply head_reducible_step. }
    eexists. by apply head_step_prim_step. }  
  iNext. iIntros (e2 σ2 Hstep).
  iApply "H".
  iPureIntro.
  rewrite -head_prim_step_eq. done.
Qed.

Lemma ewp_lift_pure_det_head_step {E E' Φ Ψ} e1 e2 :
  to_eff e1 = None →
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2' σ2,
    head_step e1 σ1 (e2', σ2) > 0 → σ2 = σ1 ∧ e2' = e2) →
  (|={E}[E']▷=> EWP e2 @ E <| Ψ |> {{ Φ }}) ⊢ EWP e1 @ E <| Ψ |> {{ Φ }}.
Proof using Hinh.
  intros. erewrite !(ewp_lift_pure_det_step e1 e2); [done| |].
  { intros σ1. specialize H1 with (σ1 := σ1). assert (∃ ρ,  head_step e1 σ1 ρ > 0) as ((e1', σ1') & Hstep). { apply head_reducible_step. }
    eexists. by apply head_step_prim_step. }
  { intros σ1 e2' σ2 Hprim. apply H2. rewrite -head_prim_step_eq. done. }
Qed.

Lemma ewp_lift_pure_det_head_step' {E Φ Ψ} e1 e2 :
  to_eff e1 = None →
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2' σ2,
    head_step e1 σ1 (e2', σ2) > 0 → σ2 = σ1 ∧ e2' = e2) →
  ▷ EWP e2 @ E <| Ψ |> {{ Φ }} ⊢ EWP e1 @ E <| Ψ |> {{ Φ }}.
Proof using Hinh.
  intros. rewrite -[(EWP e1 @ _ <| _ |> {{ _ }})%I]ewp_lift_pure_det_head_step //.
  rewrite -step_fupd_intro //.
Qed.

End ectx_lifting.

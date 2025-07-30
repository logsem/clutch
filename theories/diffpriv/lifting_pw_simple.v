(** The "lifting lemmas" in this file serve to lift the rules of the operational
    semantics to the program logic. *)
From iris.proofmode Require Import tactics.
From iris.prelude Require Import options.
From clutch.prelude Require Import NNRbar.
From clutch.diffpriv Require Import wp_pw_simple.

Section lifting.
Context `{!spec_updateGS (lang_markov Λ) Σ, !diffprivWpGS Λ Σ}.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.

#[local] Open Scope R.

Lemma wp_lift_step_couple_full E Φ e1 s :
  (match to_val e1 with
   | Some v => |={E}=> Φ v
   | None =>
       ∀ σ1 e1' σ1' ε δ,
         state_interp σ1 ∗ spec_interp (e1', σ1') ∗ err_interp ε δ ={E,∅}=∗
         ⌜reducible (e1, σ1)⌝ ∗
         ((∃ (R : cfg Λ → cfg Λ → Prop) (ε1 ε2 δ1 δ2 : nonnegreal) (n : nat),
           ⌜DPcoupl (prim_step e1 σ1) (pexec n (e1', σ1')) R ε1 δ1⌝ ∗
            ⌜ε1 + ε2 <= ε⌝ ∗ ⌜δ1 + δ2 <= δ⌝ ∗
            (∀ e2 σ2 e2' σ2',
                (⌜R (e2, σ2) (e2', σ2')⌝ ={∅}=∗
                 ▷ |={∅,E}=>  (state_interp σ2 ∗ spec_interp (e2', σ2') ∗ err_interp ε2 δ2 ∗ WP e2 @ s; E {{ Φ }}))))
           ∨
             ▷ |={∅,E}=> ((□ (∀ v, Φ v ∗-∗ ∃ (v' : val Λ) (σ' : state Λ), spec_interp ((of_val v'), σ') ∗ ⌜v = v'⌝))
              ∗
                ∀ RES : val Λ,
                  WP e1 @ s; E {{ (λ v1, ∃ (v1' : val Λ) (σv' : state Λ),
                        spec_interp (of_val v1', σv') ∗ ⌜v1 = RES → v1' = RES⌝) }}
             )
         )
      end)
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof. rewrite wp_unfold /wp_pre //. Qed.

Lemma wp_lift_step_couple E Φ e1 s :
  (match to_val e1 with
   | Some v => |={E}=> Φ v
   | None =>
       ∀ σ1 e1' σ1' ε δ,
         state_interp σ1 ∗ spec_interp (e1', σ1') ∗ err_interp ε δ ={E,∅}=∗
         ⌜reducible (e1, σ1)⌝ ∗
         ∃ (R : cfg Λ → cfg Λ → Prop) (ε1 ε2 δ1 δ2 : nonnegreal) (n : nat),
           ⌜DPcoupl (prim_step e1 σ1) (pexec n (e1', σ1')) R ε1 δ1⌝ ∗
            ⌜ε1 + ε2 <= ε⌝ ∗ ⌜δ1 + δ2 <= δ⌝ ∗
            (∀ e2 σ2 e2' σ2',
                (⌜R (e2, σ2) (e2', σ2')⌝ ={∅}=∗
                 ▷ |={∅,E}=>  (state_interp σ2 ∗ spec_interp (e2', σ2') ∗ err_interp ε2 δ2 ∗ WP e2 @ s; E {{ Φ }} )))
      end)
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof. rewrite wp_unfold /wp_pre //. iIntros "H". destruct (to_val e1) => //.
       iIntros "* R". iSpecialize ("H" with "R"). iMod "H" as "(% & H)". iModIntro. iFrame. done.
Qed.

Lemma wp_lift_step_later E Φ e1 s :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E,∅}=∗
     ⌜reducible (e1, σ1)⌝ ∗
     ∀ e2 σ2,
      ⌜prim_step e1 σ1 (e2, σ2) > 0⌝ ={∅}=∗ ▷ |={∅,E}=>
      state_interp σ2 ∗ WP e2 @ s; E {{ Φ }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (h) "H".
  iApply wp_lift_step_couple. rewrite h.
  iIntros (σ1 e1' σ1' ε1 δ1) "(Hσ & Hρ & Hε)".
  iMod ("H" with "Hσ") as "[%Hs H]". iModIntro.
  iSplit => //.
  iExists _,0%NNR,ε1,0%NNR,δ1,0%nat.
  iSplit; [iPureIntro|].
  { setoid_rewrite pexec_O.
    eapply DPcoupl_pos_R, DPcoupl_trivial.
    - apply prim_step_mass. eauto.
    - apply dret_mass. }
  repeat (iSplit; [iPureIntro|]) ; [real_solver|real_solver|].
  iIntros (e2 σ2 e2' σ2' (_ & ? & [= -> ->]%dret_pos)). iFrame.
  iMod ("H" with "[//]") as "H".
  iIntros "!> !>".
  by iMod "H" as "[$ $]".
Qed.

(** Derived lifting lemmas. *)
Lemma wp_lift_step E Φ e1 s :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E,∅}=∗
    ⌜reducible (e1, σ1)⌝ ∗
    ▷ ∀ e2 σ2,
     ⌜prim_step e1 σ1 (e2, σ2) > 0⌝ ={∅,E}=∗
      state_interp σ2 ∗
      WP e2 @ s; E {{ Φ }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step_later. iIntros (?) "Hσ".
  iMod ("H" with "Hσ") as "[$ H]". iIntros "!>" (???) "!>" . by iApply "H".
Qed.

Lemma wp_lift_pure_step `{!Inhabited (state Λ)} E E' Φ e1 s :
  (∀ σ1, reducible (e1, σ1)) →
  (∀ σ1 e2 σ2, prim_step e1 σ1 (e2, σ2) > 0 → σ2 = σ1) →
  (|={E}[E']▷=> ∀ e2 σ, ⌜prim_step e1 σ (e2, σ) > 0⌝ → WP e2 @ s; E {{ Φ }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (Hsafe Hstep) "H". iApply wp_lift_step.
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
Lemma wp_lift_atomic_step_fupd {E1 E2 Φ} e1 s :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E1}=∗
    ⌜reducible (e1, σ1)⌝ ∗
    ∀ e2 σ2, ⌜prim_step e1 σ1 (e2, σ2) > 0⌝ ={E1}[E2]▷=∗
      state_interp σ2 ∗
      from_option Φ False (to_val e2))
  ⊢ WP e1 @ s; E1 {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply (wp_lift_step_later E1 _ e1)=>//; iIntros (σ1) "Hσ1".
  iMod ("H" $! σ1 with "Hσ1") as "[$ H]".
  iApply fupd_mask_intro; first set_solver.
  iIntros "Hclose" (e2 σ2 Hs). iMod "Hclose" as "_".
  iMod ("H" $! e2 σ2 with "[#]") as "H"; [done|].
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose !>".
  iMod "Hclose" as "_". iMod "H" as "($ & HQ)".
  destruct (to_val e2) eqn:?; last by iExFalso.
  iApply wp_value; last done. by apply of_to_val.
Qed.

Lemma wp_lift_atomic_step {E Φ} e1 s :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E}=∗
    ⌜reducible (e1, σ1)⌝ ∗
    ▷ ∀ e2 σ2, ⌜prim_step e1 σ1 (e2, σ2) > 0⌝ ={E}=∗
      state_interp σ2 ∗
      from_option Φ False (to_val e2))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step_fupd.
  iIntros (?) "?". iMod ("H" with "[$]") as "[$ H]".
  iIntros "!> *". iIntros (Hstep) "!> !>".
  by iApply "H".
Qed.

Lemma wp_lift_pure_det_step `{!Inhabited (state Λ)} {E E' Φ} e1 e2 s :
  (∀ σ1, reducible (e1, σ1)) →
  (∀ σ1 e2' σ2, prim_step e1 σ1 (e2', σ2) > 0 → σ2 = σ1 ∧ e2' = e2) →
  (|={E}[E']▷=> WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (? Hpuredet) "H". iApply (wp_lift_pure_step E E'); try done.
  { naive_solver. }
  iApply (step_fupd_wand with "H"); iIntros "H".
  iIntros (e' σ (?&->)%Hpuredet); auto.
Qed.

Lemma wp_pure_step_fupd `{!Inhabited (state Λ)} E E' e1 e2 φ n Φ s :
  PureExec φ n e1 e2 →
  φ →
  (|={E}[E']▷=>^n WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
  iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?]] "IH"; simpl; first done.
  iApply wp_lift_pure_det_step.
  - eauto.
  - intros σ1 e2' σ2 Hpstep.
    by injection (pmf_1_supp_eq _ _ _ (pure_step_det σ1) Hpstep).
  - by iApply (step_fupd_wand with "Hwp").
Qed.

Lemma wp_pure_step_later `{!Inhabited (state Λ)} E e1 e2 φ n Φ s :
  PureExec φ n e1 e2 →
  φ →
  ▷^n WP e2 @ s; E {{ Φ }} ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  intros Hexec ?. rewrite -wp_pure_step_fupd //. clear Hexec.
  induction n as [|n IH]; by rewrite //= -step_fupd_intro // IH.
Qed.

End lifting.

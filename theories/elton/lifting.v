From iris.proofmode Require Import tactics.
From iris.prelude Require Import options.
From clutch.prelude Require Import NNRbar.
From clutch.delay_prob_lang Require Import lang.
From clutch.elton Require Import weakestpre.


Section lifting.
  Context `{!eltonWpGS d_prob_lang Σ}.
  Implicit Types v : val d_prob_lang.
  Implicit Types e : expr d_prob_lang.
  Implicit Types σ : state d_prob_lang.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val d_prob_lang → iProp Σ.

  #[local] Open Scope R.

  Lemma wp_lift_step_fupd_glm E Φ e1 s :
    (∀ σ1 ε1,
     state_interp σ1 ∗ err_interp ε1 ={E, ∅}=∗
     state_step_coupl e1 σ1 ε1
       (λ e2 σ2 ε2,
          match to_val e2 with
          | Some v => |={∅, E}=> state_interp σ2 ∗ err_interp ε2 ∗ Φ v
          | None => prog_coupl e2 σ2 ε2
                     (λ e3 σ3 ε3,
                        ▷ state_step_coupl e3 σ3 ε3
                          (λ e4 σ4 ε4, |={∅, E}=> state_interp σ4 ∗ err_interp ε4 ∗ WP e4 @ s ; E {{Φ}}
                          )
                     )
          end
       ))
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    by rewrite pgl_wp_unfold /pgl_wp_pre. 
  Qed.



  Lemma wp_lift_step_fupd E Φ e1 s :
    to_val e1 = None ->
    (∀ σ1, state_interp σ1
           ={E,∅}=∗
           ⌜reducible (e1, σ1)⌝ ∗
           ∀ e2 σ2,
       ⌜prim_step e1 σ1 (e2, σ2) > 0 ⌝ ={∅}=∗ ▷ |={∅,E}=>
       state_interp σ2 ∗ WP e2 @ s; E {{ Φ }} )
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (H) "H".
    iApply wp_lift_step_fupd_glm.
    iIntros (σ1 ε) "[Hσ Hε]".
    iMod ("H" with "Hσ") as "[%Hs H]". iModIntro.
    iApply state_step_coupl_ret.
    rewrite H.
    iApply prog_coupl_prim_step.
    { iModIntro. iIntros. by iApply state_step_coupl_ret_err_ge_1. }
    iExists _.
    iExists nnreal_zero.
    iExists ε.
    iSplit; first done.
    iSplit.
    { iPureIntro. simpl. lra. }
    iSplit.
    { iPureIntro.
      eapply pgl_pos_R, pgl_trivial.
      simpl; lra.
    }
    simpl.
    iIntros (e2 σ2  (?&?)).
    iMod ("H" with "[//]")as "H".
    iIntros "!> !>".
    iApply state_step_coupl_ret.
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
       WP e2 @ s; E {{ Φ }}
    )
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (?) "H". iApply wp_lift_step_fupd; [done|]. iIntros (?) "Hσ".
    iMod ("H" with "Hσ") as "[$ H]". iIntros "!>" (???) "!>!>" . by iApply "H".
  Qed.

  Lemma wp_lift_pure_step `{!Inhabited (state d_prob_lang)} E E' Φ e1 s :
    (∀ σ1, reducible (e1, σ1)) →
    (∀ σ1 e2 σ2, prim_step e1 σ1 (e2, σ2) > 0 → σ2 = σ1) →
    (|={E}[E']▷=> ∀ e2 σ, ⌜prim_step e1 σ (e2, σ) > 0⌝ → WP e2 @ s; E {{ Φ }})
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (Hsafe Hstep) "H". iApply wp_lift_step.
    { specialize (Hsafe inhabitant) as Hsafe'.
      rewrite /reducible in Hsafe'. destruct Hsafe' as [].
      eapply val_stuck.
      by simpl in *. }
    iIntros (σ1) "Hσ". iMod "H".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit; [done|].
    iNext. iIntros (e2 σ2 Hprim).
    destruct (Hstep _ _ _ Hprim).
    iMod "Hclose" as "_". iMod "H". subst.
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
                    from_option Φ False (to_val e2) 
    )
    ⊢ WP e1 @ s; E1 {{ Φ }}.
  Proof.
    iIntros (?) "H".
    iApply (wp_lift_step_fupd E1 _ e1)=>//; iIntros (σ1) "Hσ1".
    iMod ("H" $! σ1 with "Hσ1") as "[$ H]".
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose" (e2 σ2 Hs). iMod "Hclose" as "_".
    iMod ("H" $! e2 σ2 with "[#]") as "H"; [done|].
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose !>".
    iMod "Hclose" as "_". iMod "H" as "($ & HQ )".
    destruct (to_val e2) eqn:?; last by iExFalso. iFrame.
    iApply pgl_wp_value; last done. by apply of_to_val.
  Qed.

  Lemma wp_lift_atomic_step {E Φ} e1 s :
    to_val e1 = None →
    (∀ σ1, state_interp σ1 ={E}=∗
           ⌜reducible (e1, σ1)⌝ ∗
           ▷ ∀ e2 σ2, ⌜prim_step e1 σ1 (e2, σ2) > 0⌝ ={E}=∗
                      state_interp σ2 ∗
                      from_option Φ False (to_val e2) 
    )
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (?) "H". iApply wp_lift_atomic_step_fupd; [done|].
    iIntros (?) "?". iMod ("H" with "[$]") as "[$ H]".
    iIntros "!> *". iIntros (Hstep) "!> !>".
    by iApply "H".
  Qed.

  Lemma wp_lift_pure_det_step `{!Inhabited (state d_prob_lang)} {E E' Φ} e1 e2 s :
    (∀ σ1, reducible (e1, σ1)) →
    (∀ σ1 e2' σ2, prim_step e1 σ1 (e2', σ2) > 0 → σ2 = σ1 ∧ e2' = e2) →
    (|={E}[E']▷=> WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (? Hpuredet) "H". iApply (wp_lift_pure_step E E'); try done.
    { naive_solver. }
    iApply (step_fupd_wand with "H"); iIntros "H".
    iIntros (e' σ (?&->)%Hpuredet); auto.
  Qed.

  Lemma wp_pure_step_fupd `{!Inhabited (state d_prob_lang)} E E' e1 e2 φ n Φ s :
    PureExec φ n e1 e2 →
    φ →
    (|={E}[E']▷=>^n WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
    iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?]] "IH"; simpl; first done.
    iApply wp_lift_pure_det_step.
    - done. 
    - intros σ1 e2' σ2 Hpstep.
      by injection (pmf_1_supp_eq _ _ _ (pure_step_det σ1) Hpstep).
    - by iApply (step_fupd_wand with "Hwp").
  Qed.

  Lemma wp_pure_step_later `{!Inhabited (state d_prob_lang)} E e1 e2 φ n Φ s :
    PureExec φ n e1 e2 →
    φ →
    ▷^n WP e2 @ s; E {{ Φ }} ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    intros Hexec ?. rewrite -wp_pure_step_fupd //. clear Hexec.
    induction n as [|n IH]; by rewrite //= -step_fupd_intro // IH.
  Qed.

End lifting.

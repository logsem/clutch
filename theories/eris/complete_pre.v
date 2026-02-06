(** Adaptation of pure_complete/complete_pre.v for the eris probabilistic framework.

    Key differences from the original:
    - prim_step is probabilistic: expr → state → distr (expr * state)
    - cfg = expr * state (no thread pools, no forking)
    - No observations (κ)
    - Uses erisWpGS instead of irisGS_gen
*)

From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import base proofmode classes.
From iris.base_logic Require Export invariants lib.ghost_map lib.cancelable_invariants.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.

From clutch.common Require Export language.
From clutch.eris Require Export weakestpre total_weakestpre.
From clutch.prob Require Import distribution.

Section prelims.
  Context {Λ : language}.

  (** Multi-step relation for probabilistic semantics.
      prim_steps e1 σ1 e2 σ2 holds if there is a path of positive probability
      from (e1, σ1) to (e2, σ2). *)
  Inductive prim_steps : Λ.(expr) → Λ.(state) → Λ.(expr) → Λ.(state) → Prop :=
  | prim_steps_refl e σ :
      prim_steps e σ e σ
  | prim_steps_step e1 σ1 e2 σ2 e3 σ3 :
      prim_step e1 σ1 (e2, σ2) > 0 →
      prim_steps e2 σ2 e3 σ3 →
      prim_steps e1 σ1 e3 σ3.

  Lemma prim_steps_trans e1 σ1 e2 σ2 e3 σ3 :
    prim_steps e1 σ1 e2 σ2 →
    prim_steps e2 σ2 e3 σ3 →
    prim_steps e1 σ1 e3 σ3.
  Proof.
    intros Hsteps1. revert e3 σ3.
    induction Hsteps1 as [|e1 σ1 e2 σ2 e2' σ2' Hstep Hsteps IH];
      intros e3 σ3 Hsteps2.
    - done.
    - econstructor 2; [exact Hstep|]. by apply IH.
  Qed.

  Lemma prim_steps_fill K e1 σ1 e2 σ2 :
    LanguageCtx K →
    prim_steps e1 σ1 e2 σ2 →
    prim_steps (K e1) σ1 (K e2) σ2.
  Proof.
    intros HK.
    induction 1 as [|e1 σ1 e2 σ2 e3 σ3 Hstep Hsteps IH].
    - constructor.
    - econstructor 2; [|exact IH].
      by apply fill_step.
  Qed.

  (** Configuration safety for single-expression execution *)
  Definition cfg_not_stuck (ρ : cfg Λ) : Prop :=
    not_stuck ρ.

  Definition cfg_safe (ρ : cfg Λ) : Prop :=
    ∀ e' σ', prim_steps ρ.1 ρ.2 e' σ' → not_stuck (e', σ').

  Lemma cfg_safe_step e1 σ1 e2 σ2 :
    cfg_safe (e1, σ1) →
    prim_step e1 σ1 (e2, σ2) > 0 →
    cfg_safe (e2, σ2).
  Proof.
    intros Hsafe Hstep e' σ' Hsteps.
    apply Hsafe. simpl.
    econstructor 2; [exact Hstep|exact Hsteps].
  Qed.

  Lemma cfg_safe_steps e1 σ1 e2 σ2 :
    cfg_safe (e1, σ1) →
    prim_steps e1 σ1 e2 σ2 →
    cfg_safe (e2, σ2).
  Proof.
    intros Hsafe Hsteps e' σ' Hsteps'.
    apply Hsafe. simpl.
    eapply prim_steps_trans; [exact Hsteps|exact Hsteps'].
  Qed.

  Lemma prim_val_stuck v σ (ρ : cfg Λ) :
    prim_step (of_val v) σ ρ > 0 → False.
  Proof.
    intros HH%val_stuck. by rewrite to_of_val in HH.
  Qed.

  Local Instance val_atomic_eris a (v : val Λ) : Atomic a (of_val v).
  Proof.
    intros σ e' σ' Hstep.
    exfalso. eapply (prim_val_stuck v σ (e', σ')). exact Hstep.
  Qed.

End prelims.

Section fractional.
  Context `{Σ : gFunctors}.

  Lemma fractional_divide_n (Q : Qp → iProp Σ) (Hf : Fractional Q) (p : positive) q :
    Q q -∗
    [∗ list] _ ∈ seq 0 (Pos.to_nat p), Q (q / pos_to_Qp p)%Qp.
  Proof.
    revert q. induction p as [|p IHp] using Pos.peano_ind; intros q.
    - rewrite /= Qp.div_1. by iIntros "$".
    - iIntros "Hq".
      assert ((q / pos_to_Qp (Pos.succ p))%Qp + ((q * pos_to_Qp p) / pos_to_Qp (Pos.succ p))%Qp = q)%Qp as Heq.
      { rewrite -Qp.div_add_distr -{1}(Qp.mul_1_r q) -Qp.mul_add_distr_l pos_to_Qp_add Pos.add_1_l.
        rewrite -{2}(Qp.mul_1_l (pos_to_Qp (Pos.succ p))) Qp.div_mul_cancel_r Qp.div_1 //. }
      rewrite -{1}Heq Hf Pos2Nat.inj_succ seq_S /= big_sepL_snoc.
      iDestruct "Hq" as "[$ Hq]". iPoseProof (IHp with "Hq") as "Hres".
      iApply (big_sepL_wand with "Hres").
      iApply big_sepL_intro. iIntros "!>" (???) "H".
      iStopProof. f_equiv.
      rewrite Qp.div_div Qp.div_mul_cancel_r //.
  Qed.

End fractional.

Section magic_rule.
  Context `{!erisWpGS Λ Σ}.

  (** Magic rule for opening invariants around atomic subexpressions.
      This allows opening an invariant when executing an atomic subexpression
      within a larger expression.

      Note: This is adapted from the Iris version but uses eris's probabilistic WP. *)
  Lemma wp_inv_open_maybe (e : expr Λ) s E1 E2 Φ :
    (|={E1,E2}=>
      (∃ K e', ⌜LanguageCtx K⌝ ∗ ⌜e = K e'⌝ ∗ ⌜(Atomic StronglyAtomic e')⌝
        ∗ WP e' @ s; E2 {{ v, |={E2,E1}=> WP K (of_val v) @ s; E1 {{ Φ }} }})
      ∨ |={E2,E1}=> WP e @ s; E1 {{ Φ }})
    -∗ WP e @ s; E1 {{ Φ }}.
  Proof.
    iIntros "H".
    destruct (to_val e) as [v|] eqn:Hev.
    - (* e is already a value *)
      eapply of_to_val in Hev. subst e.
      iApply pgl_wp_atomic.
      1: eapply val_atomic_eris.
      iMod "H" as "[H|H]"; last first.
      { iModIntro. rewrite !pgl_wp_value_fupd'.
        iModIntro. iMod "H". done. }
      iDestruct "H" as "(%K & %e' & %HK & %Hvke & %Hato & Hwp)".
      destruct (to_val e') as [v'|] eqn:Hev'.
      { eapply of_to_val in Hev'. subst e'. rewrite !pgl_wp_value_fupd'.
        iMod "Hwp". do 2 iModIntro. rewrite -Hvke pgl_wp_value_fupd'. by iMod "Hwp". }
      eapply of_to_val_flip in Hvke.
      eapply fill_not_val in Hev'. congruence.
    - (* e is not a value - use the glm bind rule *)
      rewrite pgl_wp_unfold /pgl_wp_pre Hev.
      iIntros (σ1 ε1) "[Hσ Hε]".
      iMod "H" as "[H|>H]"; last first.
      { by iMod ("H" with "[$Hσ $Hε]") as "H". }
      iDestruct "H" as "(%K & %e' & %HK & -> & %Hato & Hwp)".
      rewrite pgl_wp_unfold /pgl_wp_pre.
      destruct (to_val e') as [v|] eqn:Heq.
      { (* e' is a value, so K e' = K (of_val v) *)
        eapply of_to_val in Heq. subst e'.
        iMod "Hwp" as "Hwp".
        iMod "Hwp" as "Hwp".
        (* K (of_val v) is not a value by Hev *)
        rewrite pgl_wp_unfold /pgl_wp_pre Hev.
        by iMod ("Hwp" with "[$Hσ $Hε]") as "Hwp". }
      (* e' is not a value, proceed with glm_bind *)
      iMod ("Hwp" with "[$Hσ $Hε]") as "Hglm".
      iModIntro.
      iApply (glm_bind K); first done.
      (* Use glm_strengthen to get step witness for atomicity *)
      iPoseProof (glm_strengthen with "Hglm") as "Hglm".
      iApply (glm_mono_pred with "[] Hglm").
      iIntros ([e2 σ2] ε2) "[[%σ' %Hpstep] H]".
      destruct (Hato σ' e2 σ2 Hpstep) as [v2 Hval2].
      assert (e2 = of_val v2) as -> by by symmetry; apply of_to_val.
      iNext.
      iMod "H" as "(Hσ & Hε & Hwp)".
      rewrite pgl_wp_unfold /pgl_wp_pre Hval2.
      iMod "Hwp" as "Hwp".
      iMod "Hwp" as "Hwp".
      iModIntro. iFrame.
  Qed.

  (** Total WP version of the magic rule *)
  Lemma twp_inv_open_maybe (e : expr Λ) s E1 E2 Φ :
    (|={E1,E2}=>
      (∃ K e', ⌜LanguageCtx K⌝ ∗ ⌜e = K e'⌝ ∗ ⌜(Atomic StronglyAtomic e')⌝
        ∗ WP e' @ s; E2 [{ v, |={E2,E1}=> WP K (of_val v) @ s; E1 [{ Φ }] }])
      ∨ |={E2,E1}=> WP e @ s; E1 [{ Φ }])
    -∗ WP e @ s; E1 [{ Φ }].
  Proof.
    iIntros "H".
    destruct (to_val e) as [v|] eqn:Hev.
    - eapply of_to_val in Hev. subst e.
      iApply tgl_wp_atomic.
      1: eapply val_atomic_eris.
      iMod "H" as "[H|H]"; last first.
      { iModIntro. rewrite !tgl_wp_value_fupd'.
        iModIntro. iMod "H". done. }
      iDestruct "H" as "(%K & %e' & %HK & %Hvke & %Hato & Hwp)".
      destruct (to_val e') as [v'|] eqn:Hev'.
      { eapply of_to_val in Hev'. subst e'. rewrite !tgl_wp_value_fupd'.
        iMod "Hwp". do 2 iModIntro. rewrite -Hvke tgl_wp_value_fupd'. by iMod "Hwp". }
      eapply of_to_val_flip in Hvke.
      eapply fill_not_val in Hev'. congruence.
    - rewrite tgl_wp_unfold /tgl_wp_pre Hev.
      iIntros (σ1 ε1) "[Hσ Hε]".
      iMod "H" as "[H|>H]"; last first.
      { by iMod ("H" with "[$Hσ $Hε]") as "H". }
      iDestruct "H" as "(%K & %e' & %HK & -> & %Hato & Hwp)".
      rewrite tgl_wp_unfold /tgl_wp_pre.
      destruct (to_val e') as [v|] eqn:Heq.
      { 
        eapply of_to_val in Heq. subst e'.
        iMod "Hwp" as "Hwp".
        iMod "Hwp" as "Hwp".
        rewrite tgl_wp_unfold /tgl_wp_pre Hev.
        by iMod ("Hwp" with "[$Hσ $Hε]") as "Hwp". 
      }
      iMod ("Hwp" with "[$Hσ $Hε]") as "Hglm".
      iModIntro.
      iApply (glm_bind K); first done.
      iPoseProof (glm_strengthen with "Hglm") as "Hglm".
      iApply (glm_mono_pred with "[] Hglm").
      iIntros ([e2 σ2] ε2) "[[%σ' %Hpstep] H]".
      destruct (Hato σ' e2 σ2 Hpstep) as [v2 Hval2].
      assert (e2 = of_val v2) as -> by by symmetry; apply of_to_val.
      iMod "H" as "(Hσ & Hε & Hwp)".
      rewrite tgl_wp_unfold /tgl_wp_pre Hval2.
      iMod "Hwp" as "Hwp".
      iMod "Hwp" as "Hwp".
      iModIntro. iFrame.
  Qed.

End magic_rule.

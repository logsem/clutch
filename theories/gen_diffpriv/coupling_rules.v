(** Coupling rules for the generic DP weakest precondition.

    The centerpiece is [wp_couple_tapes_gen]: the GENERIC state-step tape
    coupling, parametric in an ABSTRACT [DPcoupl μ μ' R'] of the two family
    draws.  This is the reuse seam — the per-distribution DP content (Laplace
    shift, Gaussian, RR_coin, …) enters only through that hypothesis; the tape
    plumbing (presampling erasure + spec-side state step) is shared.  Concrete
    per-family coupling rules instantiate the bridge. *)
From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext fin.
From clutch.prob Require Import differential_privacy distribution couplings_dp.
From clutch.diffpriv Require Import lifting ectx_lifting.
From clutch.base_logic Require Export error_credits_mult error_credits.
From clutch.gen_diffpriv Require Export primitive_laws.
From clutch.gen_prob_lang Require Import notation tactics metatheory erasure.
From clutch.gen_prob_lang.spec Require Export spec_ra.
(* import gen_prob_lang.lang LAST so concrete expr/val/state shadow the
   [language] record projections re-exported transitively *)
From clutch.gen_prob_lang Require Import lang.

Local Open Scope R.

Section rules.
  Context (Sg : Sig).
  Canonical Structure gen_ectxi_lang_cpl := gen_ectxi_lang Sg.
  Canonical Structure gen_ectx_lang_cpl := gen_ectx_lang Sg.
  Canonical Structure gen_lang_cpl := gen_lang Sg.
  Canonical Structure gen_markov_cpl := lang_markov (gen_lang Sg).
  Context `{!diffprivGS Sg Σ}.
  #[local] Existing Instance spec_rules_spec_updateGS.
  #[local] Instance spec_updateGS_cpl : spec_updateGS gen_markov_cpl Σ :=
    spec_rules_spec_updateGS Sg.

  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.

  (** Generic state-step tape coupling: from an abstract DP coupling of the two
      family draws [μ = sig_sample Sg i pv] and [μ' = sig_sample Sg i pv'], get
      the WP rule that advances two tapes [α]/[α'] by coupled draws. *)
  Lemma wp_couple_tapes_gen (i : nat) (pv pv' : val) (μ μ' : distr val)
    α α' xs xs' (R' : val → val → Prop) e Φ (ε' : R) E :
    sig_sample Sg i pv = Some μ →
    sig_sample Sg i pv' = Some μ' →
    DPcoupl μ μ' R' ε' 0 →
    ▷ α ↪ (i, pv, xs) ∗ ▷ α' ↪ₛ (i, pv', xs') ∗ ↯m ε' -∗
    (∀ v v', ⌜R' v v'⌝ -∗
        α ↪ (i, pv, xs ++ [v]) ∗ α' ↪ₛ (i, pv', xs' ++ [v']) -∗ WP e @ E {{ Φ }}) -∗
    WP e @ E {{ Φ }}.
  Proof.
    iIntros (Hμ Hμ' Hcpl) "(>Hα & >Hα' & Hε) HΦ".
    iApply wp_lift_step_spec_couple.
    iIntros (σ1 e1' σ1' ε_now δ_now) "((Hh1 & Ht1) & Hauth2 & Hε2 & Hδ2)".
    iDestruct "Hauth2" as "(HK & Hh2 & Ht2)".
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iDestruct (ecm_supply_ecm_inv with "Hε2 Hε") as %(ε'' & ε_now_rest & foo & Hε'').
    iDestruct (ghost_map_lookup with "Ht2 Hα'") as %Hαs'.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %Hαs.
    iApply (spec_coupl_erasables_weak
      (λ σ2 σ2', ∃ v v', R' v v' ∧
         σ2 = state_upd_stapes <[α:=(i,pv,xs++[v])]> σ1 ∧
         σ2' = state_upd_stapes <[α':=(i,pv',xs'++[v'])]> σ1')
      (state_step Sg σ1 α) (state_step Sg σ1' α')
      ε'' ε_now_rest ε_now 0%NNR δ_now δ_now);
      [done | apply nnreal_ext; simpl; lra | | by eapply state_step_erasable
       | (eapply state_step_erasable; apply Hαs') | ].
    1:{ erewrite (state_step_unfold Sg σ1 α i pv xs Hαs).
        erewrite (state_step_unfold Sg σ1' α' i pv' xs' Hαs').
        rewrite Hμ Hμ'.
        apply DPcoupl_map; [apply cond_nonneg | apply cond_nonneg | ].
        rewrite Hε''.
        eapply (DPcoupl_mono μ μ μ' μ' R' _ ε' ε' 0 0); [done|done| |lra|lra|exact Hcpl].
        intros x y HR. exists x, y. done. }
    iIntros (σ2 σ2' (v & v' & HR & -> & ->)).
    iApply spec_coupl_ret.
    iMod (ghost_map_update (i, pv, xs ++ [v]) with "Ht1 Hα") as "[$ Hα]".
    iMod (ghost_map_update (i, pv', xs' ++ [v']) with "Ht2 Hα'") as "[$ Hα']".
    iMod (ecm_supply_decrease with "Hε2 Hε") as (ε1 ε2 Hε1 Heq2) "H".
    iModIntro. iMod "Hclose'" as "_".
    iDestruct ("HΦ" $! v v' HR with "[$Hα $Hα']") as "Hwp".
    iFrame "Hh1 HK Hh2 Hwp Hδ2".
    assert (ε2 = ε_now_rest) as ->.
    { apply nnreal_ext. apply (f_equal nonneg) in Hε1, foo. simpl in Hε1, foo. lra. }
    iModIntro. rewrite /mult_ec_supply. iFrame "H".
  Qed.

End rules.

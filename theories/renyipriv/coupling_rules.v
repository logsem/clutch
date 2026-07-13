(** * Coupling rules  *)
From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext fin.
From clutch.prob Require Import differential_privacy.
From clutch.diffpriv Require Import lifting ectx_lifting.
From clutch.prob_lang Require Import lang notation tactics metatheory erasure.
From clutch.prob_lang.spec Require Import spec_rules.
From clutch.renyipriv Require Export primitive_laws.

Section rules.
  Context `{!renyiprivGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types v : val.
  Implicit Types l : loc.

  #[local] Open Scope R.

  (** helper lemma  *)
  Lemma RDPcoupl_steps_ctx_bind_r `{Countable A} (μ : distr A)
    e1' σ1' R (α ρ: nonnegreal) K :
    to_val e1' = None →
    (1 <= α) ->
    RDPcoupl μ (prim_step e1' σ1') R α ρ →
    RDPcoupl μ (prim_step (fill K e1') σ1')
      (λ a '(e2', σ2'), ∃ e2'', (e2', σ2') = (fill K e2'', σ2') ∧ R a (e2'', σ2')) α ρ.
  Proof.
    intros Hcpl Hα Hv.
    rewrite fill_dmap //= -(dret_id_right μ ) /=.
    replace (ρ) with (ρ+0)%NNR; [|apply nnreal_ext; simpl; lra].
    eapply (RDPcoupl_dbind); [ done | done | done | | done ].
    intros ? [] ?.
    apply RDPcoupl_dret=>/=; [done|done|]. eauto.
  Qed.

  Lemma hoare_couple_gauss_exact (loc : Z)
    (num den : Z) K E :
    (0 < IZR num / IZR den)%R →
    {{{ ⤇ fill K (Gauss #loc #num #den) }}}
      Gauss #loc #num #den @ E
      {{{ (z : Z), RET #z; ⤇ fill K #z }}}.
  Proof.
    iIntros (Hpos ?) "Hr Hcnt".
    iApply wp_lift_prim_steps_coupl; [done|].
    iIntros (σ1 e1' σ1' α_now ρ_now) "((Hh1 & Ht1) & Hauth2 & Herr) /=".
    iDestruct (spec_auth_prog_agree with "Hauth2 Hr") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iExists _, 0%NNR, ρ_now.
    repeat iSplit.
    - iPureIntro. apply nnreal_ext; simpl; lra.
    - iPureIntro. solve_red.
    - iPureIntro. solve_red.
    - iPoseProof (rc_supply_valid with "Herr") as "%Hα".
      iPureIntro.
      apply RDPcoupl_steps_ctx_bind_r => //.
      eapply RDPcoupl_gauss_exact; [done|reflexivity|exact Hpos].
    - iIntros (???? (?& [=->] & (z & [=-> ->] & [=-> ->]))).
      iMod (spec_update_prog (fill K #z) with "Hauth2 Hr") as "[$ Hspec0]".
      do 2 iModIntro.
      iMod "Hclose'" as "_".
      iModIntro. iFrame.
      rewrite -wp_value.
      iDestruct ("Hcnt" with "[$Hspec0]") as "$".
  Qed.

  Lemma hoare_couple_gauss (loc loc' k : Z)
    (Hdist : (Z.abs (loc - loc') <= k)%Z)
    (num den : Z) (s α ρ: R) K E :
    (1 <= α) ->
    (IZR num / IZR den)%R = s →
    0 < IZR num / IZR den →
    ρ = (((IZR k)^2)/(2 * (s^2)))%R →
    {{{ ⤇ fill K (Gauss #loc' #num #den) ∗ ↯R (α, ρ) }}}
      Gauss #loc #num #den @ E
      {{{ (z : Z), RET #z; ⤇ fill K #(z) }}}.
  Proof.
    iIntros (Hα1 Hs Hspos Hρ Φ) "(HK & Herr) Hcnt".
    assert (Hs0 : (0 < s)%R) by (rewrite -Hs; lra).
    assert (Hρ0 : (0 <= ρ)%R).
    { rewrite Hρ. apply Rcomplements.Rdiv_le_0_compat; nra. }
    iApply wp_lift_prim_steps_coupl; [done|].
    iIntros (σ1 e1' σ1' α_now ρ_now) "((Hh1 & Ht1) & Hauth2 & Hsply) /=".
    iDestruct (spec_auth_prog_agree with "Hauth2 HK") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iPoseProof (rc_supply_valid with "Hsply") as "%Hαnow".
    iDestruct (rc_supply_bound with "Hsply Herr") as %[Hαle Hρle].
    set (ρ1 := mknonnegreal ρ Hρ0).
    set (ρ2 := nnreal_minus ρ_now ρ1 Hρle).
    iExists _, ρ1, ρ2.
    repeat iSplit.
    - iPureIntro. apply nnreal_ext; simpl; lra.
    - iPureIntro. solve_red.
    - iPureIntro. solve_red.
    - iPureIntro.
      apply RDPcoupl_steps_ctx_bind_r => //.
      eapply (RDPcoupl_gauss_primstep loc loc' k Hdist num den s) => //.
    - iIntros (???? (?& [=->] & (z & [=-> ->] & [=-> ->]))).
      iMod (spec_update_prog (fill K #z) with "Hauth2 HK") as "[$ Hspec0]".
      iMod (rc_supply_decrease with "Hsply Herr") as (ρs' Hρeq) "Hsply'".
      do 2 iModIntro.
      iMod "Hclose'" as "_".
      iModIntro.
      assert (ρs' = ρ2) as -> by (apply nnreal_ext; simpl; lra).
      iFrame.
      rewrite -wp_value.
      iDestruct ("Hcnt" with "[$Hspec0]") as "$".
  Qed.

End rules.
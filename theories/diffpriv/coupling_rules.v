(** * Coupling rules  *)
From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext fin.
From clutch.prob Require Import differential_privacy.
From clutch.diffpriv Require Import lifting ectx_lifting.
From clutch.prob_lang Require Import lang notation tactics metatheory erasure.
From clutch.prob_lang.spec Require Import spec_rules.
From clutch.diffpriv Require Export primitive_laws.

Section rules.
  Context `{!diffprivGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types v : val.
  Implicit Types l : loc.

  #[local] Open Scope R.

  (** helper lemma  *)
  Lemma DPcoupl_steps_ctx_bind_r `{Countable A} (μ : distr A)
    e1' σ1' R (ε δ: nonnegreal) K :
    to_val e1' = None →
    DPcoupl μ (prim_step e1' σ1') R ε δ →
    DPcoupl μ (prim_step (fill K e1') σ1')
      (λ a '(e2', σ2'), ∃ e2'', (e2', σ2') = (fill K e2'', σ2') ∧ R a (e2'', σ2')) ε δ.
  Proof.
    intros Hcpl Hv.
    rewrite fill_dmap //= -(dret_id_right μ ) /=.
    eapply (DPcoupl_dbind' ε 0 _ δ 0); [lra|done|done|lra| |done].
    intros ? [] ?.
    apply DPcoupl_dret=>/=; [done|done|]. eauto.
  Qed.

  Lemma DPcoupl_laplace_step
    (loc loc' k k' : Z)
    (Hdist : (Z.abs (k + loc - loc') <= k')%Z)
    (num den : Z) ε ε' σ1 σ1' :
    (IZR num / IZR den) = ε →
    0 < IZR num / IZR den →
    ε' = (IZR k' * ε) →
    DPcoupl (language.prim_step (Laplace #num #den #loc) σ1)
      (prim_step (Laplace #num #den #loc') σ1')
      (λ ρ2 ρ2', ∃ (z : Z),
          ρ2 = (Val #z, σ1) ∧ ρ2' = (Val #(z+k), σ1'))
      ε' 0.
  Proof.
    intros ?Hε??Hε'. simpl. fold cfg.
    rewrite ?head_prim_step_eq /= ; try by exact 0%Z.
    rewrite /dmap.
    replace 0 with (0 + 0) by lra.
    replace ε' with (ε' + 0) by lra.
    eapply DPcoupl_dbind => //.
    2:{ case_decide ; [|done].
        rewrite /laplace_rat.
        rewrite Hε' -Hε.
        apply Mcoupl_to_DPcoupl.
        eapply (Mcoupl_laplace).
        done.
    }
    simpl.
    intros z1 z2 Hres.
    apply DPcoupl_dret; [done|done|]. subst.
    exists z1. done.
  Qed.


  Lemma wp_couple_laplace (loc loc' k k' : Z)
    (Hdist : (Z.abs (k + loc - loc') <= k')%Z)
    (num den : Z) (ε ε' : R) K E :
    IZR num / IZR den = ε →
    0 < IZR num / IZR den →
    ε' = (IZR k' * ε) →
    {{{ ⤇ fill K (Laplace #num #den #loc') ∗ ↯m ε' }}}
      Laplace #num #den #loc @ E
      {{{ (z : Z), RET #z; ⤇ fill K #(z+k) }}}.
  Proof.
    iIntros (Hε εpos Hε').
    iIntros (?) "(Hr & Hε) Hcnt".
    iApply wp_lift_step_prog_couple; [done|].
    iIntros (σ1 e1' σ1' ε_now δ_now) "((Hh1 & Ht1) & Hauth2 & (Hε2 & Hδ))".
    iDestruct (spec_auth_prog_agree with "Hauth2 Hr") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iDestruct (ecm_supply_ecm_inv with "Hε2 Hε") as %(? &?& -> & Hε'').
    iApply (prog_coupl_steps _ _ _ δ_now 0%NNR) ;
      [done| apply nnreal_ext; simpl; lra |solve_red|solve_red|..].
    { apply DPcoupl_steps_ctx_bind_r => //. rewrite Hε''.
      eapply DPcoupl_laplace_step => //. }
    iIntros (???? (?& [=->] & (z & [=-> ->] & [=-> ->]))).
    iMod (spec_update_prog (fill K #(_)) with "Hauth2 Hr") as "[$ Hspec0]".
    iMod (ecm_supply_decrease with "Hε2 Hε") as (???Herr Hε''') "H".
    do 2 iModIntro.
    iMod "Hclose'" as "_".
    iModIntro. iFrame.
    rewrite -wp_value.
    iDestruct ("Hcnt" with "[$Hspec0]") as "$".
    simplify_eq. rewrite Hε'' Hε''' in Herr.
    rewrite Rplus_comm in Herr. apply Rplus_eq_reg_r in Herr. clear -Herr.
    apply nnreal_ext in Herr. subst. done.
    Unshelve. all: exact 0%Z.
  Qed.

End rules.

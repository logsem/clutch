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

  Lemma hoare_couple_laplace (loc loc' k k' : Z)
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
    iIntros (σ1 e1' σ1' ε_now δ_now) "((Hh1 & Ht1) & Hauth2 & (Hε2 & Hδ)) /=".
    iDestruct (spec_auth_prog_agree with "Hauth2 Hr") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iDestruct (ecm_supply_ecm_inv with "Hε2 Hε") as %(? &?& -> & Hε'').
    iApply (prog_coupl_steps_simple _ _ _ δ_now 0%NNR);
      [done| apply nnreal_ext; simpl; lra |solve_red|solve_red|..].
    { apply DPcoupl_steps_ctx_bind_r => //. rewrite Hε''.
      eapply DPcoupl_laplace_step => //. } simpl.
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

  Lemma wp_couple_laplace (loc loc' k k' : Z)
    (Hdist : (Z.abs (k + loc - loc') <= k')%Z)
    (num den : Z) (ε ε' : R) K E :
    IZR num / IZR den = ε →
    0 < IZR num / IZR den →
    ε' = (IZR k' * ε) →
    ⤇ fill K (Laplace #num #den #loc') -∗ ↯m ε' -∗
    WP (Laplace #num #den #loc) @ E
      {{ v, ∃ z : Z, ⌜v = #z⌝ ∗ ⤇ fill K #(z+k) }}.
  Proof.
    iIntros (Hε εpos Hε').
    iIntros "Hr Hε".
    iApply wp_lift_step_prog_couple; [done|].
    iIntros (σ1 e1' σ1' ε_now δ_now) "((Hh1 & Ht1) & Hauth2 & Hε2 & Hδ2)".
    iDestruct (spec_auth_prog_agree with "Hauth2 Hr") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iDestruct (ecm_supply_ecm_inv with "Hε2 Hε") as %(? &?& -> & Hε'').
    iApply (prog_coupl_steps_simple _ _ _ δ_now 0%NNR) ;
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
    simplify_eq. rewrite Hε'' Hε''' in Herr.
    rewrite Rplus_comm in Herr. apply Rplus_eq_reg_r in Herr. clear -Herr.
    apply nnreal_ext in Herr. subst. iSplitL. 2: done. done.
    Unshelve. all: exact 0%Z.
  Qed.

  Lemma hoare_couple_laplace_choice (loc loc' T : Z)
    (dist_loc : (Z.abs (loc - loc') <= 1)%Z)
    (num den : Z) (ε ε' : R) K E :
    IZR num / IZR den = ε →
    0 < IZR num / IZR den →
    ε' = (2*ε) →
    {{{ ⤇ fill K (Laplace #num #den #loc') ∗ ↯m ε' }}}
      Laplace #num #den #loc @ E
      {{{ (z : Z), RET #z;
          ∃ z' : Z, ⤇ fill K #z'
                 ∗
                   ( ⌜(T <= z ∧ T + 1 <= z')⌝
                     ∨
                       (⌜z < T ∧ z' < T + 1⌝ ∗ ↯m ε'))%Z
           }}}.
  Proof.
    iIntros (Hε εpos Hε').
    iIntros (?) "(Hr & Hε) Hcnt".
    iApply wp_lift_step_prog_couple; [done|]. simpl.
    iIntros (σ1 e1' σ1' ε_now δ_now) "((Hh1 & Ht1) & Hauth2 & (Hε2 & Hδ))".
    iDestruct (spec_auth_prog_agree with "Hauth2 Hr") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iDestruct (ecm_supply_ecm_inv with "Hε2 Hε") as %(? & ε_now_minus_ε' & H_ε_now & Hε'').
    set (P := (λ '(ez, _) , ∃ z : Z, ez = Val (LitV (LitInt z)) ∧ T <= z)%Z : cfg → Prop).
    set (R := (λ ρ ρ' : expr * state ,
                  ρ.2 = σ1 ∧ ρ'.2 = σ1' ∧
                  (P ρ →
                  let (ez, ez') := (ρ.1, ρ'.1) in
                  ∃ z z' : Z, ez = Val (LitV (LitInt z)) ∧
                                ez' = Val (LitV (LitInt z')) ∧
                                T <= z ∧ T + 1 <= z')%Z)).
    set (RR := (λ a '(e2', σ2'), ∃ e2'', (e2', σ2') = (fill K e2'', σ2') ∧ R a (e2'', σ2'))).
    set (R' := (λ ρ ρ' : expr * state ,
                   ρ.2 = σ1 ∧ ρ'.2 = σ1' ∧
                   (¬ P ρ →
                   let (ez, ez') := (ρ.1, ρ'.1) in
                   ∃ z z' : Z, ez = Val (LitV (LitInt z)) ∧
                                 ez' = Val (LitV (LitInt z')) ∧
                                 z < T ∧ z' < T + 1)%Z)).
    set (RR' := (λ a '(e2', σ2'), ∃ e2'', (e2', σ2') = (fill K e2'', σ2') ∧ R' a (e2'', σ2'))).
    opose proof (prog_coupl_steps ε_now_minus_ε' x ε_now 0 ε_now
                   δ_now 0 0 δ_now
                   P RR RR')%NNR as pcs ; simpl in pcs.
    iApply pcs => // ; clear pcs.
    1,2: apply nnreal_ext ; simpl ; lra.
    1,2: solve_red.

    (* Disjointness of R and R' under P is fine *)
    - intros [] [] []. intros P_ρ nP_ρ'. subst R R' P ; simpl in *. intros [h h'].
      destruct h as (e1'' & eq'' & R_ρρ').
      destruct h' as (? & eq''' & R'_ρρ').
      apply R_ρρ' in P_ρ. apply R'_ρρ' in nP_ρ'.
      destruct P_ρ as [?[?[?[?[]]]]]. destruct nP_ρ' as [?[?[?[?[]]]]].
      subst. simplify_eq. lia.

    (* If we're above (P holds) the coupling should be the shift Laplace translation. *)
    (* Shouldn't we get to know that P holds here? *)
    - intros. replace 0%R with (nonneg 0%NNR) => //.
      apply DPcoupl_steps_ctx_bind_r => //.
      subst. simpl in *.
      eapply DPcoupl_mono ; last first.
      1: eapply DPcoupl_laplace_step.
      all: try by intuition eauto.
      { instantiate (1 := 1%Z).
        rewrite Hε''. real_solver_partial. 1: lra.
        replace 2 with (IZR 2) => //. apply IZR_le.
        revert dist_loc. repeat apply Zabs_ind ; lia. }
      + simpl. intros [e σ] [e' σ'] (z & eq_ez & eq_ez'). repeat split. 1,2: simpl ; by simplify_eq.
        intros Pe. destruct Pe as (ey & eq_ey & above). simpl.
        exists z, (z + 1)%Z.
        repeat split ; simplify_eq => //.
        lia.

    (* if P is false we use the trivial coupling *)
    - intros. replace 0%R with (nonneg 0%NNR) => //. apply DPcoupl_steps_ctx_bind_r => //.
      subst. simpl in *.
      eapply DPcoupl_mono ; last first.
      1: eapply DPcoupl_laplace_step.
      all: try by intuition eauto.
      { instantiate (1 := (loc' - loc)%Z).
        replace (loc' - loc + loc - loc')%Z with 0%Z by lia.
        assert (Z.abs 0 = 0)%Z as ->. 2: lra. apply Zabs_ind ; lia. }
      + simpl. intros [e σ] [e' σ'] (z & eq_ez & eq_ez').
        repeat split. 1,2: simpl ; by simplify_eq.
        intros nPe. exists z, (z + (loc' - loc))%Z.
        repeat split ; simplify_eq => //.
        * subst P R R' ; simpl in *.
          destruct (decide (z < T)%Z) => //.
          exfalso. apply nPe. exists z. split => //. lia.
        * subst P R R' ; simpl in *.
          destruct (decide (z < T)%Z). 1: lia. exfalso ; apply nPe ; exists z ; split => // ; lia.

    - iIntros (e2 σ2 e2' σ2').
      destruct (decide (P (e2, σ2))) as [p | n].
      + iSplitL ; last first.
        { iIntros ([nP_ρ2 R'_ρ2]). exfalso. done. }
        iIntros (((ze2 & eqe2 & Pe2) & (e2'' & [eq_e2'' R_ρ2ρ2']))).
        unfold R in R_ρ2ρ2'.
        simpl in R_ρ2ρ2'. destruct R_ρ2ρ2' as (<- & <- & R_ρ2ρ2'). specialize (R_ρ2ρ2' p).
        destruct R_ρ2ρ2' as (z & z' & eq_e2_z & eq_e2''_z' & z_above & z'_above).
        inversion eq_e2''. simplify_eq.
        iMod (spec_update_prog (fill K #(_)) with "Hauth2 Hr") as "[$ Hspec0]".
        iMod (ecm_supply_decrease with "Hε2 Hε") as (???Herr Hε''') "H".
        do 2 iModIntro.
        iMod "Hclose'" as "_".
        iModIntro. iFrame.
        rewrite -wp_value.
        iDestruct ("Hcnt" with "[$Hspec0]") as "$".
        { iLeft. done. }
        simplify_eq. rewrite Hε'' Hε''' in Herr.
        rewrite Rplus_comm in Herr. apply Rplus_eq_reg_r in Herr. clear -Herr.
        apply nnreal_ext in Herr. subst. iFrame.

      + iSplitR.
        { iIntros ([P_ρ2 R_ρ2]). exfalso. done. }
        iIntros ((nP_ρ2 & (e2'' & [eq_e2'' R'_ρ2ρ2']))).
        unfold R' in R'_ρ2ρ2'.
        simpl in R'_ρ2ρ2'. destruct R'_ρ2ρ2' as (<- & <- & R'_ρ2ρ2'). specialize (R'_ρ2ρ2' nP_ρ2).
        destruct R'_ρ2ρ2' as (z & z' & eq_e2_z & eq_e2''_z' & z_below & z'_below).
        inversion eq_e2''. simplify_eq.
        iMod (spec_update_prog (fill K #(_)) with "Hauth2 Hr") as "[$ Hspec0]".
        do 2 iModIntro.
        iMod "Hclose'" as "_".
        iModIntro. iFrame.
        rewrite -wp_value.
        iDestruct ("Hcnt" with "[$Hspec0 Hε]") as "$".
        { iRight. iFrame. done. }
        Unshelve. all: exact 0%Z.
  Qed.

End rules.

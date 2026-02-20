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

  Lemma hoare_couple_laplace_exact (loc : Z)
    (num den : Z) K E :
    {{{ ⤇ fill K (Laplace #num #den #loc #()) }}}
      Laplace #num #den #loc #() @ E
      {{{ (z : Z), RET #z; ⤇ fill K #z }}}.
  Proof.
    iIntros (?) "Hr Hcnt".
    iApply wp_lift_step_prog_couple; [done|].
    iIntros (σ1 e1' σ1' ε_now δ_now) "((Hh1 & Ht1) & Hauth2 & (Hε2 & Hδ)) /=".
    iDestruct (spec_auth_prog_agree with "Hauth2 Hr") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iApply (prog_coupl_steps_simple ε_now 0%NNR _ δ_now 0%NNR);
      [apply nnreal_ext ; real_solver| apply nnreal_ext; simpl; lra |try solve_red|try solve_red|..].
    { apply DPcoupl_steps_ctx_bind_r => //.
      eapply DPcoupl_laplace_primstep_exact => //. }
    iIntros (???? (?& [=->] & (z & [=-> ->] & [=-> ->]))).
    iMod (spec_update_prog (fill K #(_)) with "Hauth2 Hr") as "[$ Hspec0]".
    (* iMod (ecm_supply_decrease with "Hε2 Hε") as (???Herr Hε''') "H". *)
    do 2 iModIntro.
    iMod "Hclose'" as "_".
    iModIntro. iFrame.
    rewrite -wp_value.
    iDestruct ("Hcnt" with "[$Hspec0]") as "$".
  Qed.

  Lemma hoare_couple_laplace (loc loc' k k' : Z)
    (Hdist : (Z.abs (k + loc - loc') <= k')%Z)
    (num den : Z) (ε ε' : R) K E :
    IZR num / IZR den = ε →
    0 < IZR num / IZR den →
    ε' = (IZR k' * ε) →
    {{{ ⤇ fill K (Laplace #num #den #loc' #()) ∗ ↯m ε' }}}
      Laplace #num #den #loc #() @ E
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
      eapply DPcoupl_laplace_primstep => //. } simpl.
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
    Unshelve. all: constructor.
  Qed.

  Lemma wp_couple_tapes_laplace (mean mean' k k' : Z) α α' zs zs' e Φ
    (Hdist : (Z.abs (k + mean - mean') <= k')%Z)
    (num den : Z) (ε ε' : R) E :
    IZR num / IZR den = ε →
    0 < IZR num / IZR den →
    ε' = (IZR k' * ε) →
    ▷ α ↪L (num, den, mean; zs) ∗ ▷ α' ↪Lₛ (num, den, mean'; zs') ∗ ↯m ε' -∗
    (∀ z, α ↪L (num, den, mean; zs ++ [z]) ∗ α' ↪Lₛ (num, den, mean'; zs' ++ [z + k]%Z) -∗
          WP e @ E {{ Φ }}) -∗
    WP e @ E {{ Φ }}.
  Proof.
    iIntros (Hε εpos Hε').
    iIntros "(>α & >α' & Hε) HΦ".
    iApply wp_lift_step_spec_couple.
    iIntros (σ1 e1' σ1' ε_now δ_now) "((Hh1 & Ht1 & Htl1) & Hauth2 & Hε2 & Hδ2)".
    iDestruct "Hauth2" as "(HK&Hh2&Ht2&Htl2)/=".
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iDestruct (ecm_supply_ecm_inv with "Hε2 Hε") as %(ε'' & ε_now_rest & foo & Hε'').
    rewrite -Hε''. rewrite -Hε'' in Hε'. clear Hε''. clear ε'. rename ε'' into ε'.
    iDestruct (ghost_map_lookup with "Htl2 α'") as %?.
    iDestruct (ghost_map_lookup with "Htl1 α") as %?.

    iApply (spec_coupl_erasables_weak _ _ _ ε' ε_now_rest _ 0%NNR δ_now) => //.
    1: apply nnreal_ext ; simpl ; lra.
    1: eapply DPcoupl_laplace_statestep => //.
    { by eapply state_step_laplace_erasable. }
    { by eapply state_step_laplace_erasable. }
    simpl.
    iIntros (σ2 σ2' (z & -> & ->)).
    iApply spec_coupl_ret.

    iDestruct (ghost_map_lookup with "Htl1 α") as %?%lookup_total_correct.
    iDestruct (ghost_map_lookup with "Htl2 α'") as %?%lookup_total_correct.
    iMod (ghost_map_update ((Tape_Laplace num den mean (zs ++ [z]))) with "Htl1 α") as "[$ α]".
    iMod (ghost_map_update ((Tape_Laplace num den mean' (zs' ++ [z+k]%Z))) with "Htl2 α'") as "[$ α']".
    iMod (ecm_supply_decrease with "Hε2 Hε") as (????) "H".
    iModIntro. iMod "Hclose'" as "_". iFrame.
    simplify_eq.
    iDestruct ("HΦ" $! z with "[$α $α']") as "Hwp".
    iSplitL "H".
    2: done.
    iApply ecm_supply_eq; [|done].
      simplify_eq/=; lra.
  Qed.

  Lemma hoare_couple_laplace_choice (loc loc' T : Z)
    (dist_loc : (Z.abs (loc - loc') <= 1)%Z)
    (num den : Z) (ε ε' : R) K E :
    IZR num / IZR den = ε →
    0 < IZR num / IZR den →
    ε' = (2*ε) →
    {{{ ⤇ fill K (Laplace #num #den #loc' #()) ∗ ↯m ε' }}}
      Laplace #num #den #loc #() @ E
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
      (* for 2num/den we get a coupling that shifts the rhs by 1 *)
      1: eapply (DPcoupl_laplace_primstep loc loc' 1 (Z.abs (1 + loc - loc'))).
      all: try by intuition eauto.
      {
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
      1: eapply (DPcoupl_laplace_primstep loc loc'
                   (loc' - loc) (Z.abs ((loc' - loc) + loc - loc'))).
      all: try by intuition eauto.
      {
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


  (** TODO: This should be generalizable to injective functions [N] -> [M]
      Then we can get the exact couplings with bijections as a corollary *)
  Lemma wp_couple_tapes (N M : nat) E e α αₛ ns nsₛ Φ (δ : R) :
    (N <= M)%nat →
    (S M - S N) / S M = δ →
    ▷ α ↪N (N; ns) ∗ ▷ αₛ ↪ₛN (M; nsₛ) ∗
    ↯ δ ∗
    (∀ (n : nat),
        ⌜ n ≤ N ⌝ -∗
        α ↪N (N; ns ++ [n]) ∗ αₛ ↪ₛN (M; nsₛ ++ [n]) -∗
        WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (NMpos NMδ) "(>Hα & >Hαₛ & Hδ & Hwp)".
    iMod ecm_zero as "Hε".
    iApply wp_lift_step_spec_couple.
    iIntros (σ1 e1' σ1' ε_now δ_now) "((Hh1 & Ht1 & Htl1) & Hauth2 & Hε2 & Hδ2)".
    iDestruct "Hauth2" as "(HK&Hh2&Ht2&Htl2)/=".
    iDestruct "Hα" as (fs) "(%&Hα)".
    iDestruct "Hαₛ" as (fsₛ) "(%&Hαₛ)".
    iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iDestruct (ec_supply_ec_inv with "Hδ2 Hδ") as %(?&?&->&<-).
    iDestruct (ecm_supply_ecm_inv with "Hε2 Hε") as %(?&?&->&hh).
    iApply spec_coupl_erasables_weak ; [done|done|..].
    { rewrite hh. simpl.
      apply ARcoupl_to_DPcoupl.
      apply (ARcoupl_state_state N M σ1 σ1' α αₛ fs fsₛ x NMpos NMδ H2 H1). }
    { by eapply state_step_erasable. }
    { by eapply state_step_erasable. }
    iIntros (σ2 σ2' (n & m & nm & -> & ->)).
    iApply spec_coupl_ret.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?%lookup_total_correct.
    iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?%lookup_total_correct.
    iMod (ghost_map_update ((N; fs ++ [n]) : tape) with "Ht1 Hα") as "[$ Hα]".
    iMod (ghost_map_update ((M; fsₛ ++ [m]) : tape) with "Ht2 Hαₛ") as "[$ Hαₛ]".
    iMod (ec_supply_decrease with "Hδ2 Hδ") as (????) "H".
    iMod (ecm_supply_decrease with "Hε2 Hε") as (????) "Hm".
    iModIntro. iMod "Hclose'" as "_". iFrame.
    pose proof (fin_to_nat_lt n).
    iDestruct ("Hwp" $! n with "[]") as "Hwp".
    { iPureIntro; lia. }
    rewrite -/add_ec_supply.
    iSplitL "H Hm".
    { iSplitL "Hm".
      - iApply ecm_supply_eq; [|done]. simplify_eq/=; lra.
      - iApply ec_supply_eq; [|done]. simplify_eq/=; lra.
    }
    iModIntro.
    iApply "Hwp".
    iSplitL "Hα".
    - iExists _. iFrame.
      rewrite fmap_app.
      simplify_eq. done.
    - iExists _. iFrame.
      rewrite nm.
      rewrite fmap_app.
      simplify_eq. done.
  Qed.


  Lemma wp_couple_tapes_bij N f `{Bij nat nat f} E e α αₛ ns nsₛ Φ :
    (forall n, n < S N -> f n < S N)%nat ->
    ▷ α ↪N (N; ns) ∗ ▷ αₛ ↪ₛN (N; nsₛ) ∗
      (∀ n : nat, α ↪N (N; ns ++ [n]) ∗ αₛ ↪ₛN (N; nsₛ ++ [f n]) ∗ ⌜ n ≤ N ⌝  -∗
                    WP e @ E {{ Φ }})
      ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (Hdom) "(>Hα & >Hαₛ & Hwp)".
    iApply wp_lift_step_spec_couple.
    iIntros (σ1 e1' σ1' ε_now δ_now) "((Hh1 & Ht1 & Htl1) & Hauth2 & Hε2 & Hδ2)".
    iDestruct "Hauth2" as "(HK&Hh2&Ht2&Htl2)/=".
    iDestruct "Hα" as (fs) "(<-&Hα)".
    iDestruct "Hαₛ" as (fsₛ) "(<-&Hαₛ)".
    destruct (restr_bij_fin (S N) f) as [g [HBij Hfg]].
    { intros n Hn.
      by apply Hdom.
    }
    iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    replace ε_now with (0 + ε_now)%NNR; last first.
    { apply nnreal_ext; simpl; lra. }
    replace δ_now with (0 + δ_now)%NNR; last first.
    { apply nnreal_ext; simpl; lra. }
    iApply spec_coupl_erasables_weak; [done|done|..].
    { eapply ARcoupl_to_DPcoupl, ARcoupl_exact.
      (* eauto unifies the wrong premise? *)
      apply Rcoupl_state_state; [apply HBij | apply H1 | apply H0 ]. }
    { by eapply state_step_erasable. }
    { by eapply state_step_erasable. }
    iIntros (σ2 σ2' (n & ? & ?)).
    iApply spec_coupl_ret.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?%lookup_total_correct.
    iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?%lookup_total_correct.
    simplify_map_eq.
    iMod (ghost_map_update ((N; fs ++ [n]) : tape) with "Ht1 Hα") as "[$ Hα]".
    iMod (ghost_map_update ((N; fsₛ ++ [g n]) : tape) with "Ht2 Hαₛ") as "[$ Hαₛ]".
    iModIntro. iMod "Hclose'" as "_".
    replace (0 + ε_now)%NNR with ε_now; last first.
    { apply nnreal_ext; simpl; lra. }
    replace (0 + δ_now)%NNR with δ_now; last first.
    { apply nnreal_ext; simpl; lra. }
    iFrame.
    iApply ("Hwp" $! (fin_to_nat n) with "[-]").
    iSplitL "Hα".
    { iExists _. iFrame.
      iPureIntro.
      rewrite fmap_app //. }
    iSplitL "Hαₛ".
    { iExists _. iFrame.
      iPureIntro.
      rewrite fmap_app -Hfg //. }
    iPureIntro.
    apply (fin.fin_to_nat_le n).
  Qed.

  Lemma wp_couple_tapes_rev (N M : nat) E e α αₛ ns nsₛ Φ (δ : R) :
    (M <= N)%nat →
    (S N - S M) / S N = δ →
    ▷ α ↪N (N; ns) ∗ ▷ αₛ ↪ₛN (M; nsₛ) ∗
    ↯ δ ∗
    (∀ (n m : nat),
        ⌜n = m⌝ -∗
        α ↪N (N; ns ++ [n]) ∗ αₛ ↪ₛN (M; nsₛ ++ [m]) -∗
        ⌜m ≤ M⌝ -∗
        WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (NMpos NMδ) "( >Hα & >Hαₛ & Hδ & Hwp)".
    iApply wp_lift_step_spec_couple.
    iIntros (σ1 e1' σ1' ε_now δ_now) "((Hh1 & Ht1 & Htl1) & Hauth2 & Hε2 & Hδ2)".
    iDestruct "Hauth2" as "(HK&Hh2&Ht2&Htl2)".
    iDestruct "Hα" as (fs) "(<-&Hα)".
    iDestruct "Hαₛ" as (fsₛ) "(<-&Hαₛ)".
    iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    replace ε_now with (0 + ε_now)%NNR; last first.
    { apply nnreal_ext; simpl; lra. }
    replace δ_now with (0 + δ_now)%NNR; last first.
    { apply nnreal_ext; simpl; lra. }
    iDestruct (ec_supply_ec_inv with "Hδ2 Hδ") as %(?&?&->&<-).
    iApply spec_coupl_erasables_weak ; [done|done|..].
    { by apply ARcoupl_to_DPcoupl, ARcoupl_state_state_rev. }
    { by eapply state_step_erasable. }
    { by eapply state_step_erasable. }
    iIntros (σ2 σ2' (n & m & nm & ? & ?)).
    iApply spec_coupl_ret.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?%lookup_total_correct.
    iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?%lookup_total_correct.
    simplify_map_eq.
    iMod (ghost_map_update ((N; fs ++ [n]) : tape) with "Ht1 Hα") as "[$ Hα]".
    iMod (ghost_map_update ((M; fsₛ ++ [m]) : tape) with "Ht2 Hαₛ") as "[$ Hαₛ]".
    iMod (ec_supply_decrease with "Hδ2 Hδ") as (????) "H".
    iModIntro. iMod "Hclose'" as "_".
    iFrame.
    iDestruct ("Hwp" with "[//] [-H Hε2] []") as "$".
    - iSplitL "Hα".
      { iExists _. iFrame.
        iPureIntro.
        rewrite fmap_app //. }
      iExists _. iFrame.
      iPureIntro.
      rewrite fmap_app //.
    - iPureIntro.
      apply (fin_to_nat_le m).
    - replace (0 + ε_now)%NNR with ε_now; last first.
      { apply nnreal_ext; simpl; lra. }
      iSplitR "H" ; iFrame ; try done.
      iApply ec_supply_eq; [|done].
      simplify_eq/=; lra.
  Qed.

  Lemma wp_rand_avoid_l {N} (m : nat) (z : Z) E (δ : R) :
    TCEq N (Z.to_nat z) →
    δ = 1 / (S N) →
    {{{ ↯ δ }}}
      rand #z @ E
    {{{ (n : nat), RET #n; ⌜n ≠ m⌝ ∗ ⌜ n ≤ N ⌝ }}}.
  Proof.
    iIntros (-> -> Φ) "Hδ Hwp".
    iApply wp_lift_step_prog_couple; [done|].
    iIntros (σ1 e1' σ1' ε_now δ_now) "((Hh1 & Ht1 & Htl1) & Hauth2 & Hε2 & Hδ2)".
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iDestruct (ec_supply_ec_inv with "Hδ2 Hδ") as %(δ &?& -> & ?).
    replace ε_now with (0 + ε_now)%NNR; last first.
    { apply nnreal_ext; simpl; lra. }
    iApply prog_coupl_step_l_dret ; [done|done|solve_red|..].
    { by apply ARcoupl_to_DPcoupl, (ARcoupl_rand_no_coll_l _ (fin_force (Z.to_nat z) m)). }
    iIntros (?? (n & [= -> ->] & ? & [=])).
    iMod (ec_supply_decrease with "Hδ2 Hδ") as (????) "Hs".
    simplify_eq.
    do 2 iModIntro.
    iMod "Hclose'" as "_".
    iFrame.
    rewrite -wp_value.
    iDestruct ("Hwp" with "[]") as "$".
    - iPureIntro.
      split; eauto.
      + destruct (le_gt_dec m (Z.to_nat z)).
        * intro H3. apply H1. apply fin_to_nat_inj.
          rewrite fin_force_to_nat_le; auto.
        * pose proof (fin_to_nat_le n). lia.
      + apply (fin_to_nat_le).
   - iSplitL "Hε2" => //.
     + iApply ecm_supply_eq; [|done]. simpl. lra.
     + iApply ec_supply_eq; [|done]. lra.
  Qed.

  Lemma wp_rand_avoid_r {N} (m : nat) (z : Z) K e E Φ (δ : R) :
    TCEq N (Z.to_nat z) →
    δ = 1 / (S N) →
    ⤇ fill K (rand #z) ∗
    ↯ δ ∗
    (∀ (n : nat),
       ⤇ fill K #n -∗ ⌜n ≠ m⌝ -∗ ⌜ n ≤ N ⌝ -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (-> ->) "(HK & Hδ & Hwp)".
    iApply wp_lift_step_spec_couple.
    iIntros (σ1 e1' σ1' ε_now δ_now) "((Hh1 & Ht1 & Htl1) & Hauth2 & Hε2 & Hδ2)".
    iDestruct (spec_auth_prog_agree with "Hauth2 HK") as "->".
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iDestruct (ec_supply_ec_inv with "Hδ2 Hδ") as %(δ &?& -> & ?).
    replace ε_now with (0 + ε_now)%NNR; last first.
    { apply nnreal_ext; simpl; lra. }
    iApply (spec_coupl_erasable_steps 1 _ (dret σ1)); [done|done|..].
    { rewrite pexec_1 step_or_final_no_final //; last first.
      { apply reducible_not_final. solve_red. }
      eapply DPcoupl_steps_ctx_bind_r; [done|].
      by apply ARcoupl_to_DPcoupl, (ARcoupl_rand_no_coll_r _ (fin_force (Z.to_nat z) m)). }
    { apply dret_erasable. }
    iIntros (??? (n & [=-> ] & (y&->&[=-> ->]&?))) "!>".
    iApply spec_coupl_ret.
    iMod (spec_update_prog (fill K #_) with "Hauth2 HK") as "[$ HK]".
    iMod (ec_supply_decrease with "Hδ2 Hδ") as (????) "H".
    simplify_eq.
    iMod "Hclose'" as "_".
    iFrame.
    iDestruct ("Hwp" with "[$] []") as "Hwp".
    {
      iPureIntro.
      destruct (le_gt_dec m (Z.to_nat z)).
      - intro H3. apply H2. apply fin_to_nat_inj.
        rewrite fin_force_to_nat_le; auto.
      - pose proof (fin_to_nat_le y). lia.
    }
    iSplitL "Hε2 H".
    { iSplitL "Hε2".
      - iApply ecm_supply_eq; [|done]. simpl. lra.
      - iApply ec_supply_eq; [|done]. lra.
    }
    iApply "Hwp".
    iPureIntro.
    apply (fin_to_nat_le y).
  Qed.

  (** rand(unit, N) ~ rand(unit, M) coupling, N <= M, under inj *)
  Lemma wp_couple_rand_rand_inj (N M : nat) (f: nat → nat) z w K E (δ : R) :
    (∀ n, n < S N → f n < S M)%nat →
    (∀ n1 n2, n1 < S N → n2 < S N → f n1 = f n2 → n1 = n2)%nat →
    TCEq N (Z.to_nat z) →
    TCEq M (Z.to_nat w) →
    (N <= M)%nat →
    (S M - S N) / S M = δ →
    {{{ ⤇ fill K (rand #w) ∗ ↯ δ }}}
      rand #z @ E
    {{{ (n : nat), RET #n; ⤇ fill K #(f n) ∗ ⌜ n ≤ N ⌝ }}}.
  Proof.
    iIntros (Hdom Hinj).

    set g := (λ m : fin (S N), Fin.of_nat_lt (Hdom m (fin_to_nat_lt m))).
    assert (Inj eq eq g).
    { intros m1 m2 Heq.
      assert (fin_to_nat (g m1) = f (fin_to_nat m1)) as H1.
      { rewrite /g fin_to_nat_to_fin //. }
      assert (fin_to_nat (g m2) = f (fin_to_nat m2)) as H2.
      { rewrite /g fin_to_nat_to_fin //. }
      apply fin_to_nat_inj.
      apply Hinj; [apply fin_to_nat_lt..|].
      rewrite -H1 -H2 //. by f_equal. }

    iIntros (-> -> HNM Hδ ?) "(Hr & Hδ) Hcnt".
    iApply wp_lift_step_prog_couple; [done|].
    iIntros (σ1 e1' σ1' ε_now δ_now) "((Hh1 & Ht1 & Htl1) & Hauth2 & Hε2 & Hδ2)".
    iDestruct (spec_auth_prog_agree with "Hauth2 Hr") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iDestruct (ec_supply_ec_inv with "Hδ2 Hδ") as %(? &?& -> & ?).
    replace ε_now with (0 + ε_now)%NNR at 2 ; [|apply nnreal_ext; simpl; lra].
    iApply prog_coupl_steps_simple; [done|done|solve_red|solve_red|..].
    { apply DPcoupl_steps_ctx_bind_r, ARcoupl_to_DPcoupl, (ARcoupl_rand_rand_inj _ _ g); done || lra. }
    iIntros (???? (?& [=->] & (n & [=-> ->] & [=-> ->]))).
    iMod (spec_update_prog (fill K #(g _)) with "Hauth2 Hr") as "[$ Hspec0]".
    iMod (ec_supply_decrease with "Hδ2 Hδ") as (????) "H".
    do 2 iModIntro.
    iMod "Hclose'" as "_".
    iModIntro. iFrame.
    rewrite -wp_value.
    rewrite /g fin_to_nat_to_fin.
    iDestruct ("Hcnt" with "[$Hspec0]") as "$".
    {
      iPureIntro.
      apply fin_to_nat_le.
    }
    iApply ec_supply_eq; [|done].
    simplify_eq. lra.
  Qed.

  (** rand(unit, N) ~ rand(unit, M) coupling, N <= M, under equality *)
  Lemma wp_couple_rand_rand_leq (N M : nat) z w K E (δ : R) :
    TCEq N (Z.to_nat z) →
    TCEq M (Z.to_nat w) →
    (N <= M)%nat →
    (S M - S N) / S M = δ →
    {{{ ⤇ fill K (rand #w) ∗ ↯ δ }}}
      rand #z @ E
    {{{ (n : nat), RET #n;
        ⌜ n ≤ N ⌝ ∗ ⤇ fill K #n }}}.
  Proof.
    iIntros (-> -> HNM <- ?) "(Hr & Hδ) Hwp".
    iApply (wp_couple_rand_rand_inj _ _ (λ x, x) with "[$]"); [lia|lia|done|done|].
    iModIntro. iIntros (?) "[? %]". iApply ("Hwp" $! n).
    iFrame.
    iPureIntro. lia.
  Qed.

  (** rand(unit, N) ~ rand(unit, M) coupling, M <= N, along an injection *)
  Lemma wp_couple_rand_rand_rev_inj (N M : nat) (f : nat -> nat) z w K E (δ : R) :
    (∀ n, n < S M -> f n < S N)%nat →
    (∀ n1 n2, n1 < S M → n2 < S M → f n1 = f n2 → n1 = n2)%nat →
    TCEq N (Z.to_nat z) →
    TCEq M (Z.to_nat w) →
    (M <= N)%nat →
    (S N - S M) / S N = δ →
    {{{ ⤇ fill K (rand #w) ∗ ↯ δ }}}
      rand #z @ E
    {{{ (m : nat), RET #(f m); ⤇ fill K #m ∗ ⌜ m ≤ M ⌝ }}}.
  Proof.
    iIntros (Hdom Hinj).

    set g := (λ m : fin (S M), Fin.of_nat_lt (Hdom m (fin_to_nat_lt m))).
    assert (Inj eq eq g).
    { intros m1 m2 Heq.
      assert (fin_to_nat (g m1) = f (fin_to_nat m1)) as H1.
      { rewrite /g fin_to_nat_to_fin //. }
      assert (fin_to_nat (g m2) = f (fin_to_nat m2)) as H2.
      { rewrite /g fin_to_nat_to_fin //. }
      apply fin_to_nat_inj.
      apply Hinj; [apply fin_to_nat_lt..|].
      rewrite -H1 -H2 //. by f_equal. }

    iIntros (-> -> HNM <- ?) "(Hr & Hδ) Hwp".
    iApply wp_lift_step_prog_couple; [done|].
    iIntros (σ1 e1' σ1' ε_now δ_now) "((Hh1 & Ht1 & Htl1) & Hauth2 & Hε2 & Hδ2)".
    iDestruct (spec_auth_prog_agree with "Hauth2 Hr") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    replace ε_now with (0 + ε_now)%NNR at 2 ; [|apply nnreal_ext; simpl; lra].
    iDestruct (ec_supply_ec_inv with "Hδ2 Hδ") as %(? & ? & -> & ?).
    iApply prog_coupl_steps_simple; [done|done|solve_red|solve_red|..].
    { eapply DPcoupl_steps_ctx_bind_r; [done|].
      by eapply ARcoupl_to_DPcoupl, (ARcoupl_rand_rand_rev_inj _ _ g). }
    iIntros (???? (?& [=->] & (n & [=-> ->] & [=-> ->]))).
    iMod (spec_update_prog (fill K #_) with "Hauth2 Hr") as "[$ Hspec0]".
    iMod (ec_supply_decrease with "Hδ2 Hδ") as (????) "H".
    do 2 iModIntro.
    iMod "Hclose'" as "_".
    iModIntro. iFrame.
    rewrite /g fin_to_nat_to_fin //.
    rewrite -wp_value.
    iDestruct ("Hwp" with "[$Hspec0]") as "$".
    { iPureIntro.
      apply fin_to_nat_le. }
    iApply ec_supply_eq; [|done].
    simplify_eq. lra.
  Qed.

  (** rand(unit, N) ~ rand(unit, M) coupling, N <= M, under equality *)
  Lemma wp_couple_rand_rand_rev_leq (N M : nat) z w K E (ε : R) :
    TCEq N (Z.to_nat z) →
    TCEq M (Z.to_nat w) →
    (M <= N)%nat →
    (S N - S M) / S N = ε →
    {{{ ⤇ fill K (rand #w) ∗ ↯ ε }}}
      rand #z @ E
    {{{ (n : nat ), RET #n;
        ⌜ n ≤ N ⌝ ∗ ⤇ fill K #n }}}.
  Proof.
    iIntros (-> -> HNM <- ?) "(Hr & Hε) Hwp".
    iApply (wp_couple_rand_rand_rev_inj _ _ (λ x, x) with "[$]"); [lia|lia|done|done|..].
    iIntros "!>" (m) "[? %]".
    iSpecialize ("Hwp" $! m).
    iApply ("Hwp" with "[-]").
    iFrame.
    iPureIntro. lia.
  Qed.



  (** * rand(N) ~ rand(N) coupling *)
  (*
    There should be an easier proof of this using wp_couple_rand_rand_inj,
    but that uses an injective function nat -> nat as opposed to fin (S N) -> fin (S N)
  *)
  Lemma wp_couple_rand_rand N f `{Bij nat nat f} z K E :
    TCEq N (Z.to_nat z) →
    (forall n:nat, (n < S N)%nat -> (f n < S N)%nat) ->
    {{{ ⤇ fill K (rand #z) }}}
      rand #z @ E
    {{{ (n : nat), RET #n; ⌜ n ≤ N ⌝ ∗ ⤇ fill K #(f n) }}}.
  Proof.
    iIntros (H0 Hdom Ψ) "Hr HΨ".
    destruct (restr_bij_fin (S N) f Hdom) as [ff [Hbij Hff]].
    iApply wp_lift_step_prog_couple; [done|].
    iIntros (σ1 e1' σ1' ε δ) "[Hσ [Hs Hε]]".
    iDestruct (spec_auth_prog_agree with "Hs Hr") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".

    replace ε with (0 + ε)%NNR; last first.
    { apply nnreal_ext; simpl; lra. }
    iApply (prog_coupl_steps_simple _ _ _ δ 0%NNR δ
              (λ ρ2 ρ2',
                ∃ (n : fin _), ρ2 = (Val #n, σ1) ∧ ρ2' = (fill K #(f n), σ1')))
    ; [done|simpl ; apply nnreal_ext ; real_solver|solve_red|solve_red|..].
    { rewrite /= fill_dmap //.
      rewrite /= -(dret_id_right (prim_step _ _)) /=.
      apply ARcoupl_to_DPcoupl, ARcoupl_exact.
      eapply Rcoupl_dmap.
      eapply Rcoupl_mono.
      - apply (Rcoupl_rand_rand _ ff).
        by rewrite H0.
      - intros [] [] (b & [=] & [=])=>/=.
        simplify_eq.
        rewrite Hff. eauto. }
    iIntros (e2 σ2 e2' σ2' (b & [= -> ->] & [= -> ->])) "!> !>".
    iMod (spec_update_prog with "Hs Hr") as "[$ Hr]".
    iMod "Hclose" as "_".
    replace (0 + ε)%NNR with ε; last first.
    { apply nnreal_ext; simpl; lra. }
    iFrame.
    iApply wp_value.
    iApply "HΨ".
    iFrame.
    iPureIntro.
    apply fin_to_nat_le.
  Qed.

  (** coupling rand and rand but avoid certain values*)
  Lemma wp_couple_rand_rand_avoid N (l:list _) z K E :
    TCEq N (Z.to_nat z) →
    NoDup l ->
    {{{ ↯ (length l/(N+1)) ∗
          ⤇ fill K (rand #z) }}}
      rand #z @ E
      {{{ (n : fin (S N)), RET #n; ⌜n∉l⌝ ∗ ⤇ fill K #n }}}.
  Proof.
    iIntros (H0 Hl Ψ) "[Hδ Hr] HΨ".
    iApply wp_lift_step_prog_couple; [done|].
    iIntros (σ1 e1' σ1' ε δ) "[Hσ [Hs [Hε2 Hδ2]]]".
    iDestruct (spec_auth_prog_agree with "Hs Hr") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".
    replace ε with (0 + ε)%NNR at 2 ; [|apply nnreal_ext; simpl; lra].
    iDestruct (ec_supply_ec_inv with "Hδ2 Hδ") as %(x & x1 & -> & H).
    iApply (prog_coupl_steps_simple _ _ _
              (* (λ ρ2 ρ2', *)
              (*   ∃ (n : fin _), n∉l /\ρ2 = (Val #n, σ1) ∧ ρ2' = (fill K #(n), σ1')) *))
    ; [done|done|solve_red|solve_red|..].
    { eapply DPcoupl_steps_ctx_bind_r; first done.
      apply ARcoupl_to_DPcoupl, ARcoupl_rand_rand_avoid_list; first done.
      - by rewrite S_INR.
      - by apply TCEq_eq.
    }
    iIntros (e2 σ2 e2' σ2' (b & [= ->] & (?&?&[= -> ->] & [= -> ->]))) "!> !>".
    iMod (spec_update_prog with "Hs Hr") as "[$ Hr]".
    iMod (ec_supply_decrease with "Hδ2 Hδ") as (x2 x3 H1 ?) "H".
    replace (x3) with (x1); last first.
    { apply nnreal_ext. inversion H1.
      lra.
    }
    iMod "Hclose" as "_".
    iFrame.
    iApply wp_value.
    iApply "HΨ".
    iFrame.
    by iPureIntro.
  Qed.

  Local Lemma length_remove_dups `{EqDecision A} (l:list A):
    length (remove_dups l) <= length l.
  Proof.
    induction l; first done.
    simpl.
    case_match; simpl.
    all: rewrite -!/(INR (S _)); rewrite !S_INR; lra.
  Qed.

  Lemma wp_couple_rand_rand_avoid' N (l:list _) z K E :
    TCEq N (Z.to_nat z) →
    {{{ ↯ (length l/(N+1)) ∗
          ⤇ fill K (rand #z) }}}
      rand #z @ E
      {{{ (n : fin (S N)), RET #n; ⌜n∉l⌝ ∗ ⤇ fill K #n }}}.
  Proof.
    set (l':=remove_dups l).
    iIntros (H0 Ψ) "[Hε Hr] HΨ".
    iApply (wp_couple_rand_rand_avoid with "[-HΨ]").
    - apply NoDup_remove_dups.
    - iFrame.
      iApply (ec_weaken with "[$]").
      split.
      + apply Rcomplements.Rdiv_le_0_compat.
        * apply pos_INR.
        * pose proof pos_INR N. lra.
      + rewrite !Rdiv_def.
        apply Rmult_le_compat_r.
        * apply Rlt_le. apply Rinv_0_lt_compat. pose proof pos_INR N. lra.
        * apply length_remove_dups.
    - iModIntro. iIntros (?) "[%?]".
      iApply "HΨ". iFrame.
      iPureIntro.
      by rewrite -elem_of_remove_dups.
  Qed.


  (** fragmented state rand N ~ state rand M, N>=M, under injective function from M to N*)
  Lemma wp_couple_fragmented_rand_rand_inj {M N} (f: nat → nat) {_ : Inj (=) (=) f}
    ns nsₛ α αₛ e E Φ:
    (M <= N)%nat →
    (forall n : nat, (n < S M)%nat -> (f n < S N)%nat) ->
    ▷ α ↪N (N; ns) ∗ ▷ αₛ ↪ₛN (M; nsₛ) ∗
    (∀ (n : nat),
       ⌜ n ≤ N ⌝ -∗
       if bool_decide (∃ m:nat, m ≤ M /\ f m = n) then
         ∀ m : nat, α ↪N (N; ns ++ [f m]) ∗ αₛ ↪ₛN (M; nsₛ ++ [m]) ∗ ⌜ f m ≤ N ⌝ ∗ ⌜ m ≤ M ⌝ -∗
              WP e @ E {{ Φ }}
       else
         α ↪N (N; ns ++ [n]) ∗ αₛ ↪ₛN (M; nsₛ) ∗ ⌜ n ≤ N ⌝ -∗
         WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (Hineq Hdom) "(>Hα & >Hαₛ & Hwp)".
    edestruct (restr_inj_fin (S M) (S N) f (le_n_S M N Hineq) Hdom) as [g [HgInj HgEq]].
    iDestruct "Hα" as (fs) "(<-&Hα)".
    iDestruct "Hαₛ" as (fsₛ) "(<-&Hαₛ)".
    iApply wp_lift_step_spec_couple.
    iIntros (σ1 e1' σ1' ε_now δ_now) "((Hh1 & Ht1 & Htl1) & Hauth2 & Hε2 & Hδ2)".
    iDestruct "Hauth2" as "(HK&Hh2&Ht2&Htl2)/=".
    iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?.
    simplify_map_eq.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    replace (ε_now) with (0 + ε_now)%NNR; last (apply nnreal_ext; simpl; lra).
    replace (δ_now) with (0 + δ_now)%NNR; last (apply nnreal_ext; simpl; lra).
    iApply spec_coupl_erasables_weak; [done|done|..].
    { by apply ARcoupl_to_DPcoupl, ARcoupl_exact, Rcoupl_fragmented_rand_rand_inj. }
    { by eapply state_step_erasable. }
    { eapply erasable_dbind_predicate.
      - solve_distr_mass.
      - by eapply state_step_erasable.
      - apply dret_erasable. }
    iIntros (?? [n H']).
    case_bool_decide in H'.
    - destruct Hf as [m' <-].
      destruct H' as (m & ? & ? & Hfm).
      simplify_eq.
      iMod (ghost_map_update ((N; fs ++ [g _]) : tape) with "Ht1 Hα") as "[Ht1 Hα]".
      iMod (ghost_map_update ((M; fsₛ ++ [_]) : tape) with "Ht2 Hαₛ") as "[Ht2 Hαₛ]".
      iModIntro.
      iApply spec_coupl_ret.
      iMod "Hclose'" as "_".
      iSpecialize ("Hwp" $! (f m')).
      rewrite bool_decide_eq_true_2.
      2: { exists m'.
           split; auto.
           apply fin_to_nat_le. }
      iSpecialize ("Hwp" $! _ m').
      iDestruct ("Hwp" with "[$Hα $Hαₛ]") as "Hwp".
      { iPureIntro.
        split; [rewrite fmap_app /= HgEq // |].
        split; [rewrite fmap_app /=  // |].
        split; auto.
        - apply Nat.lt_succ_r, Hdom, fin_to_nat_lt.
        - apply fin_to_nat_le.
      }
      assert (0 + ε_now = ε_now)%NNR as ->.
      { apply nnreal_ext; simpl; lra. }
      assert (0 + δ_now = δ_now)%NNR as ->.
      { apply nnreal_ext; simpl; lra. }
      by iFrame.
    - destruct H' as [??]. simplify_eq.
      iMod (ghost_map_update ((N; fs ++ [n]) : tape) with "Ht1 Hα") as "[Ht1 Hα]".
      iModIntro.
      iApply spec_coupl_ret.
      iMod "Hclose'" as "_".
      iSpecialize ("Hwp" $! (fin_to_nat n)).
      rewrite bool_decide_eq_false_2 //.
      2: {
        intros [m [Hm1 Hm2]].
        apply Hf.
        assert (m < S M)%nat as Hm3.
        { lia. }
        exists (nat_to_fin Hm3).
        apply fin_to_nat_inj.
        rewrite HgEq -Hm2.
        rewrite fin_to_nat_to_fin //.
      }
      iDestruct ("Hwp" with "[]") as "Hwp".
      { iPureIntro. apply fin_to_nat_le. }
      assert (0 + ε_now = ε_now)%NNR as ->.
      { apply nnreal_ext; simpl; lra. }
      assert (0 + δ_now = δ_now)%NNR as ->.
      { apply nnreal_ext; simpl; lra. }
      iFrame.
      iApply "Hwp".
      iModIntro.
      iSplitL "Hα".
      { iFrame. rewrite fmap_app //. }
      iSplitL "Hαₛ".
      { iFrame. auto. }
      iPureIntro. apply fin_to_nat_le.
      Unshelve.
      apply Nat.lt_succ_r, Hdom, fin_to_nat_lt.
  Qed.

  (** fragmented state rand N ~ state rand M, N>=M, under equality*)
  Lemma wp_couple_fragmented_rand_rand_leq (M N : nat) ns nsₛ α αₛ e E Φ:
    (M <= N)%nat →
    ▷ α ↪N (N; ns) ∗ ▷ αₛ ↪ₛN (M; nsₛ) ∗
    (∀ (n : nat),
       ⌜ n ≤ N ⌝ -∗
       if (bool_decide (n < S M)%nat)
         then
           α ↪N (N; ns ++ [n]) ∗ αₛ ↪ₛN (M; nsₛ ++ [n]) ∗ ⌜ n ≤ M ⌝ -∗
           WP e @ E {{ Φ }}
         else
           α ↪N (N; ns ++ [n]) ∗ αₛ ↪ₛN (M; nsₛ) ∗ ⌜ n ≤ N ⌝ -∗
           WP e @ E {{ Φ }}
    )
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (Hineq) "(>Hα & >Hαₛ & Hwp)".

    (*
    assert (∀ x : fin (S M), fin_to_nat x < S N)%nat as H.
    { intros. pose proof (fin_to_nat_lt x). lia. }
    set f := (λ x, nat_to_fin (H x)).
    assert (Inj (eq) (eq) f) as Hinj.
    { rewrite /f. intros ?? H0.
      apply (f_equal fin_to_nat) in H0. rewrite !fin_to_nat_to_fin in H0.
      by apply fin_to_nat_inj. } *)

    iApply (wp_couple_fragmented_rand_rand_inj (λ x, x) with "[$Hα $Hαₛ Hwp]"); [done| intros; lia |].
    iIntros (n) "%Hn".
    case_bool_decide as H1.
    - destruct H1 as [n' [Hn' <-]].
      iIntros (?) "(?&?&%&%)".
      iSpecialize ("Hwp" $! m).
      rewrite bool_decide_eq_true_2; last by lia.
      iApply "Hwp"; auto.
      by iFrame.
    - iSpecialize ("Hwp" $! n).
      case_match.
      2: { iIntros "(?&?&%)".
           iApply "Hwp"; auto.
           by iFrame. }
      exfalso. apply H1.
      exists n. split; auto.
      apply bool_decide_eq_true_1 in H.
      lia.
  Qed.

  (** * fragmented state rand N ~ state rand M, M>=N, under injective function from N to M*)
  Lemma wp_couple_fragmented_rand_rand_inj_rev {M N} (f: nat -> nat) {_: Inj (=) (=) f}
    ns nsₛ α αₛ e E Φ:
    (N <= M)%nat →
    (forall n, n < S N -> f n < S M)%nat ->
    ▷ α ↪N (N; ns) ∗ ▷ αₛ ↪ₛN (M; nsₛ) ∗
    (∀ (m : nat),
        ⌜ m ≤ M ⌝ -∗
        if bool_decide (∃ n:nat, n ≤ N /\ f n = m) then
          ∀ n, α ↪N (N; ns ++ [n]) ∗ αₛ ↪ₛN (M; nsₛ ++ [f n]) ∗ ⌜n ≤ N⌝ ∗ ⌜f n ≤ M⌝ -∗
               WP e @ E {{ Φ }}
        else
          α ↪N (N; ns) ∗ αₛ ↪ₛN (M; nsₛ++[m]) ∗ ⌜m ≤ M⌝ -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (Hineq Hdom) "(>Hα & >Hαₛ & Hwp)".
    edestruct (restr_inj_fin (S N) (S M) f (le_n_S N M Hineq) Hdom) as [g [HgInj HgEq]].
    iDestruct "Hα" as (fs) "(<-&Hα)".
    iDestruct "Hαₛ" as (fsₛ) "(<-&Hαₛ)".
    iApply wp_lift_step_spec_couple.
    iIntros (σ1 e1' σ1' ε_now δ_now) "((Hh1 & Ht1 & Htl1) & Hauth2 & Hε2 & Hδ2)".
    iDestruct "Hauth2" as "(HK&Hh2&Ht2&Htl2)/=".
    iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    replace (ε_now) with (0+ε_now)%NNR; last (apply nnreal_ext; simpl; lra).
    replace (δ_now) with (0+δ_now)%NNR; last (apply nnreal_ext; simpl; lra).
    iApply spec_coupl_erasables_weak; [done|done|..].
    { by apply ARcoupl_to_DPcoupl, ARcoupl_exact, Rcoupl_swap, Rcoupl_fragmented_rand_rand_inj. }
    { eapply erasable_dbind_predicate.
      - solve_distr_mass.
      - by eapply state_step_erasable.
      - apply dret_erasable. }
    { by eapply state_step_erasable. }
    iIntros (?? [m H']).
    case_bool_decide in H'.
    - destruct Hf as [m' <-].
      destruct H' as (n & ? & ? & Hfn).
      simplify_eq.
      iMod (ghost_map_update ((N; fs ++ [_]) : tape) with "Ht1 Hα") as "[Ht1 Hα]".
      iMod (ghost_map_update ((M; fsₛ ++ [_]) : tape) with "Ht2 Hαₛ") as "[Ht2 Hαₛ]".
      iModIntro. iApply spec_coupl_ret. iMod "Hclose'" as "_".
      iSpecialize ("Hwp" $! (f m')).
      rewrite bool_decide_eq_true_2.
      2: { exists m'.
           split; auto.
           apply fin_to_nat_le. }
      iSpecialize ("Hwp" $! _ m').
      iDestruct ("Hwp" with "[$Hα $Hαₛ]") as "Hwp".
      { iPureIntro.
        split; [rewrite fmap_app /=  // |].
        split; [rewrite fmap_app /= -HgEq // |].
        split; auto.
        - apply fin_to_nat_le.
        - apply Nat.lt_succ_r, Hdom, fin_to_nat_lt.
      }
      assert (0 + ε_now = ε_now)%NNR as ->.
      { apply nnreal_ext; simpl; lra. }
      assert (0 + δ_now = δ_now)%NNR as ->.
      { apply nnreal_ext; simpl; lra. }
      by iFrame.
    - destruct H' as [??]. simplify_eq.
      iMod (ghost_map_update ((M; fsₛ ++ [m]) : tape) with "Ht2 Hαₛ") as "[Ht2 Hαₛ]".
      iModIntro. iApply spec_coupl_ret. iMod "Hclose'" as "_".
      iSpecialize ("Hwp" $! m).
      rewrite bool_decide_eq_false_2 //.
      2: {
        intros [n [Hn1 Hn2]].
        apply Hf.
        assert (n < S N)%nat as Hn3 by lia.
        exists (nat_to_fin Hn3).
        apply fin_to_nat_inj.
        rewrite HgEq -Hn2.
        rewrite fin_to_nat_to_fin //.
      }
      iDestruct ("Hwp" with "[]") as "Hwp"; [iPureIntro; apply fin_to_nat_le | ].
      assert (0 + ε_now = ε_now)%NNR as ->.
      { apply nnreal_ext; simpl; lra. }
      assert (0 + δ_now = δ_now)%NNR as ->.
      { apply nnreal_ext; simpl; lra. }
      iFrame.
      iApply "Hwp".
      iSplitL "Hα"; [by iFrame |].
      iSplitL; [|iPureIntro; apply fin_to_nat_le ].
      iFrame.
      rewrite fmap_app /= //.
      Unshelve.
      apply Nat.lt_succ_r, Hdom, fin_to_nat_lt.
  Qed.

  (** fragmented state rand N ~ state rand M, M>=N, under injective function from N to M,
      but with errors for rejection sampling! *)
  Lemma wp_couple_fragmented_rand_rand_inj_rev' {M N} (f : nat -> nat) {_: Inj (=) (=) f}
    ns nsₛ α αₛ e E Φ (δ : R) :
    0 <= δ →
    (N < M)%nat →
    (forall n, n < S N -> f n < S M)%nat ->
    ▷ α ↪N (N; ns) ∗ ▷ αₛ ↪ₛN (M; nsₛ) ∗ ↯ δ ∗
    (∀ (m : nat),
       ⌜ m ≤ M ⌝ -∗
       if bool_decide (∃ n:nat, n ≤ N /\ f n = m) then
         ∀ n, α ↪N (N; ns ++ [n]) ∗ αₛ ↪ₛN (M; nsₛ ++ [f n]) ∗ ⌜ n ≤ N ⌝ ∗ ⌜ f n ≤ M ⌝ -∗
              WP e @ E {{ Φ }}
     else
       ∀ (δ' : R),
         ⌜δ' = (S M / (S M - S N) * δ)%R⌝ ∗
         α ↪N (N; ns) ∗ αₛ ↪ₛN (M; nsₛ++[m]) ∗ ↯ δ' ∗ ⌜ m ≤ M ⌝ -∗
         WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (Hδ Hineq Hdom) "(>Hα & >Hαₛ & Hδ & Hwp)".
    edestruct (restr_inj_fin (S N) (S M) f (le_n_S N M (Nat.lt_le_incl _ _ Hineq)) Hdom) as [g [HgInj HgEq]].
    iDestruct "Hα" as (fs) "(<-&Hα)".
    iDestruct "Hαₛ" as (fsₛ) "(<-&Hαₛ)".
    iApply wp_lift_step_spec_couple.
    iIntros (σ1 e1' σ1' ε_now δ_now) "((Hh1 & Ht1 & Htl1) & Hauth2 & Hε2 & Hδ2)".
    iDestruct "Hauth2" as "(HK&Hh2&Ht2&Htl2)".
    iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iDestruct (ec_supply_bound with "[$][$]") as %Hle.

    set δ' := mknonnegreal _ Hδ.

    set δ_now1 := nnreal_minus δ_now δ' Hle.
    set δ_now2 := (δ_now + δ' * nnreal_nat (S N) / nnreal_nat (S M - S N))%NNR.
    set (E2 σ := if bool_decide (∃ x, σ = state_upd_tapes <[αₛ:=(M; fsₛ ++ [g x])]> σ1')
                 then δ_now1 else δ_now2).
    assert (∀ σ, E2 σ <= Rmax δ_now1 δ_now2)%R.
    { intros ?. rewrite /E2. apply Rmax_Rle. case_bool_decide; by [left| right]. }

    iApply (spec_coupl_erasables_exp E2 (Rmax δ_now1 δ_now2) 0%NNR ε_now δ_now).
    { eapply ARcoupl_exact, Rcoupl_swap, Rcoupl_fragmented_rand_rand_inj; done || lia. }
    { apply erasable_dbind_predicate.
      - solve_distr_mass.
      - by eapply state_step_erasable.
      - apply dret_erasable. }
    { by eapply state_step_erasable. }
    { done. }
    { simpl. erewrite state_step_unfold; [|done].
      (* TODO: cleanup *)
      rewrite /Expval.
      erewrite (SeriesC_ext _
                  (λ b : state,
                      if bool_decide (b ∈ (λ x, state_upd_tapes <[αₛ:=(M; fsₛ ++ [x])]> σ1')
                                        <$> (fin_enum (S M)))
                     then /(S M) * E2 b else 0)%R); last first.
      { intros n.
        case_bool_decide as Hin; last first.
        { apply Rmult_eq_0_compat_r. rewrite /dmap/dbind/dbind_pmf/pmf/=.
          apply SeriesC_0. intros. apply Rmult_eq_0_compat_l.
          rewrite /dret_pmf. case_bool_decide; last lra.
          subst. exfalso. apply Hin. erewrite elem_of_list_fmap.
          exists x; split; first done. replace (fin_enum (S M)) with (enum (fin (S M))) by done.
          apply elem_of_enum. }
        rewrite elem_of_list_fmap in Hin. destruct Hin as [y [-> ?]].
        apply Rmult_eq_compat_r. rewrite /dmap/dbind/dbind_pmf/pmf/=.
        rewrite SeriesC_scal_l.
        replace (SeriesC _) with 1%R; first lra.
        symmetry.
        rewrite /dret_pmf.
        erewrite (SeriesC_ext _ (λ x, if bool_decide (x = y) then 1 else 0))%R;
          first apply SeriesC_singleton.
        intros.
        case_bool_decide as H2i.
        - apply state_upd_tapes_same in H2i. simplify_eq.
          case_bool_decide; done.
        - case_bool_decide; last done.
          subst. done. }
      { trans (SeriesC (λ x, if bool_decide (∃ y, g y = x) then / S M * δ_now1 else / S M * δ_now2))%R.
        - rewrite Rplus_0_l.
          set (h σ := match decide (∃ x, σ = state_upd_tapes <[αₛ:=(M; fsₛ ++ [x])]> σ1') with
                    | left Hproof => Some (epsilon Hproof)
                    | _ => None
                    end).
          etrans; last eapply (SeriesC_le_inj _ h).
          + apply Req_le_sym. apply SeriesC_ext. (** should be ok *)
            intros s. rewrite /h. case_match eqn:Heqn; last first.
            { rewrite bool_decide_eq_false_2; first (simpl;lra).
              erewrite elem_of_list_fmap.
              intros [? [->?]]. apply n.
              naive_solver. }
            pose proof epsilon_correct _ e0 as H'.
            rewrite bool_decide_eq_true_2; last first.
            { destruct e0 as [x ?]. subst. rewrite elem_of_list_fmap.
              eexists _. split; first done.
              replace (fin_enum _) with (enum (fin (S M))) by done.
              apply elem_of_enum. }
            rewrite !S_INR.
            rewrite /E2.
            simpl in *. subst.
            case_bool_decide as H1'.
            * rewrite bool_decide_eq_true_2.
              { rewrite /δ_now1. simpl; lra. }
              destruct H1' as [y ?]. exists y. rewrite H3. done.
            * rewrite bool_decide_eq_false_2.
              { rewrite /δ_now2; simpl; lra. }
              intros [x H2'].
              apply H1'. rewrite H' in H2'. apply state_upd_tapes_same in H2'. simplify_eq.
              naive_solver.
          + intros. case_bool_decide; apply Rmult_le_pos; try done.
            all: rewrite <-Rdiv_1_l; apply Rcomplements.Rdiv_le_0_compat; try lra.
            all: apply pos_INR_S.
          + intros n1 n2 m. rewrite /h. do 2 case_match; try done.
            intros.
            pose proof epsilon_correct _ e0.
            pose proof epsilon_correct _ e1. simpl in *. simplify_eq.
            rewrite H7 H8. by repeat f_equal.
          + apply ex_seriesC_finite.
        - eset (diff:=elements (((list_to_set (enum (fin(S M)))):gset _ )∖ ((list_to_set(g<$>enum (fin(S N)))):gset _))).
          erewrite (SeriesC_ext _
                      (λ x : fin (S M), (if bool_decide (x ∈ g<$> enum (fin(S N))) then / S M * δ_now1 else 0%R) +
                                         if bool_decide (x ∈ diff ) then / S M * δ_now2 else 0%R
                   ))%R; last first.
          { (** annoying lemma again *)
            intros n. rewrite /diff.
            case_bool_decide as H1'.
            - destruct H1' as [? H1']. rewrite bool_decide_eq_true_2; last first.
              + subst. apply elem_of_list_fmap_1. apply elem_of_enum.
              + subst. rewrite bool_decide_eq_false_2; first lra.
                rewrite elem_of_elements.
                rewrite not_elem_of_difference; right.
                rewrite elem_of_list_to_set. apply elem_of_list_fmap_1; apply elem_of_enum.
            - rewrite bool_decide_eq_false_2; last first.
              { rewrite elem_of_list_fmap. intros [?[??]].
                subst. apply H1'. naive_solver. }
              rewrite bool_decide_eq_true_2; first lra.
              rewrite elem_of_elements. rewrite elem_of_difference.
              split; rewrite elem_of_list_to_set; first apply elem_of_enum.
              rewrite elem_of_list_fmap. intros [?[??]].
              subst. apply H1'. naive_solver.
          }
        rewrite SeriesC_plus; try apply ex_seriesC_finite.
        rewrite !SeriesC_list_2; last first.
        { apply NoDup_fmap_2; [done|apply NoDup_enum]. }
        { rewrite /diff. eapply NoDup_elements. }
        rewrite length_fmap. rewrite fin.length_enum_fin.
        rewrite /diff.
        replace (length _) with (S M - S N)%nat; last first.
        { erewrite <-size_list_to_set; last apply NoDup_elements.
          erewrite list_to_set_elements.
          rewrite size_difference.
          - rewrite !size_list_to_set; [|apply NoDup_fmap; [auto|apply NoDup_enum]|apply NoDup_enum]; auto.
            rewrite length_fmap.
            rewrite !fin.length_enum_fin. done.
          - intros ??. apply elem_of_list_to_set. apply elem_of_enum.
        }
        rewrite /δ_now1 /δ_now2. simpl. rewrite -/(INR (S N)) -/(INR (S M)). rewrite !S_INR.
        rewrite !Rmult_assoc.
        rewrite minus_INR; last lia.
        cut ((N+1)/ (M + 1) * δ_now - (N+1)/(M+1) *δ+
               (M-N)/ (M + 1) * δ_now + ((N + 1)/(M+1) * ((M-N)/ (M - N))) * δ <= δ_now)%R; first lra.
        rewrite Rdiv_diag; last first.
        { assert (N < M)%R; real_solver. }
        cut ((N + 1) / (M + 1) * δ_now+ (M - N) / (M + 1) * δ_now <= δ_now)%R; first lra.
        cut ((M + 1) / (M + 1) * δ_now <= δ_now)%R; first lra.
        rewrite Rdiv_diag; first lra.
        pose proof pos_INR M. lra. }
      Unshelve. all : eapply gset_fin_set. }

    iIntros (?? [m H']).
    case_bool_decide in H' as H1'.
    - destruct H' as (n&?&?&?).
      destruct H1' as [n' <-].
      assert (n' = n) as -> by (by apply (inj _)).
      simplify_eq.
      iApply spec_coupl_ret.
      iMod (ghost_map_update ((N; fs ++ [n]) : tape) with "Ht1 Hα") as "[$ Hα]".
      iMod (ghost_map_update ((M; fsₛ ++ [g n]) : tape) with "Ht2 Hαₛ") as "[$ Hαₛ]".
      iModIntro. iMod "Hclose'" as "_".
      iSpecialize ("Hwp" $! (f n)).
      rewrite bool_decide_eq_true_2.
      2: { exists n.
           split; auto.
           apply fin_to_nat_le. }

      iSpecialize ("Hwp" $! _ (n)). iFrame.
      iDestruct ("Hwp" with "[$Hα $Hαₛ]") as "Hwp".
      { iPureIntro.
        split; [rewrite fmap_app /=  // |].
        split; [rewrite fmap_app /= HgEq // |].
        split; [apply fin_to_nat_le | ].
        apply Nat.lt_succ_r, Hdom, fin_to_nat_lt.
      }
      replace (δ_now) with (δ' + δ_now1)%NNR; last first.
      { apply nnreal_ext. simpl. lra. }
      iMod (ec_supply_decrease with "[$] [$]") as (????) "H".
      iFrame.
      rewrite /E2 bool_decide_eq_true_2; [|eauto].
      iApply ec_supply_eq; [|done].
      simplify_eq /=. lra.

    - destruct H' as [??]. simplify_eq.
      replace (E2 _) with (δ_now2); last first.
      { rewrite /E2. rewrite bool_decide_eq_false_2 //.
        intros [? H2']. apply state_upd_tapes_same in H2'. simplify_eq. naive_solver. }
      destruct (Rle_or_lt 1 δ_now2).
      { iModIntro. by iApply spec_coupl_ret_err_ge_1. }
      iModIntro.
      iApply spec_coupl_ret.
      iMod (ghost_map_update ((M; fsₛ ++ [m]) : tape) with "Ht2 Hαₛ") as "[? Hαₛ]".
      iMod "Hclose'" as "_".
      iSpecialize ("Hwp" $! m).
      rewrite bool_decide_eq_false_2 //.
      2: {
        intros [n [Hn1 Hn2]].
        apply H1'.
        assert (n < S N)%nat as Hn3 by lia.
        exists (nat_to_fin Hn3).
        apply fin_to_nat_inj.
        rewrite HgEq -Hn2.
        rewrite fin_to_nat_to_fin //.
      }
      rewrite !S_INR /=.
      iFrame.
      iMod (ec_supply_increase with "[$Hδ2]") as "[$ Hδ']".
      { by eapply Rle_lt_trans. }
      iCombine "Hδ Hδ'" as "Hδ".
      iApply ("Hwp" $! _ with "[$Hα $Hαₛ $Hδ]").
      iPureIntro.
      split.
      1:{
        simpl. rewrite -/(INR (S N)). rewrite S_INR.
        replace (INR M + 1 - (INR N + 1))%R with (INR M - INR N)%R by lra.
        rewrite -{1}(Rmult_1_l δ).
        rewrite Rmult_assoc (Rmult_comm δ).
        rewrite -Rmult_plus_distr_r. apply Rmult_eq_compat_r.
        rewrite Rdiv_def.
        replace (1)%R with ((INR M - INR N)*/(INR M - INR N))%R at 1; last first.
        { apply Rinv_r. apply lt_INR in Hineq. lra. }
        rewrite minus_INR; [|real_solver].
        rewrite -Rmult_plus_distr_r. lra. }
      split; auto.
      split; [ | apply fin_to_nat_le ].
      rewrite fmap_app //.
      Unshelve.
      + apply Nat.lt_succ_r, Hdom, fin_to_nat_lt.
      + apply fin_to_nat_le.
  Qed.

 Lemma wp_couple_fragmented_rand_rand_leq_rev' {M N : nat} ns nsₛ α αₛ e E Φ (ε : R) :
       0 <= ε →
       (N < M)%nat →
       ▷ α ↪N (N; ns) ∗ ▷ αₛ ↪ₛN (M; nsₛ) ∗ ↯ ε ∗
       (∀ (m : nat),
          ⌜ m ≤ M ⌝ -∗
          if bool_decide (m < S N)%nat
            then
              α ↪N (N; ns ++ [m]) ∗ αₛ ↪ₛN (M; nsₛ ++ [m]) ∗ ⌜ m ≤ N ⌝ -∗
              WP e @ E {{ Φ }}
            else
              ∀ (ε' : R),
                ⌜ε' = (S M / (S M - S N) * ε)%R⌝ ∗
                α ↪N (N; ns) ∗ αₛ ↪ₛN (M; nsₛ++[m]) ∗ ↯ ε' ∗ ⌜ m ≤ M ⌝ -∗
                WP e @ E {{ Φ }}
         )
       ⊢ WP e @ E {{ Φ }}.
     Proof.
       iIntros (Hε Hineq) "(>Hα & >Hαₛ & Hε & Hwp)".
       iApply (wp_couple_fragmented_rand_rand_inj_rev' (λ x, x) with "[$Hα $Hαₛ $Hε Hwp]"); [done|done| .. ].
       { intros; lia. }
       iIntros (n) "%Hn".
       case_bool_decide as H1.
       - destruct H1 as [n' [Hn' <-]].
         iIntros (?) "(?&?&%&%)".
         iSpecialize ("Hwp" $! n with "[//]").
         rewrite bool_decide_eq_true_2; last by lia.
         iSpecialize ("Hwp" with "[-]"); iFrame.
         done.
       - iSpecialize ("Hwp" $! n with "[//]").
         rewrite bool_decide_eq_false_2; [iFrame |].
         intro. apply H1.
         exists n. lia.
     Qed.

  (** wp_couple_exp *)
  Lemma wp_couple_exp (M N p:nat)
    (f : list nat → nat)
    (Hdom: forall (l : list nat), Forall (λ x, (x < S N)%nat) l -> (f l < S M)%nat)
    (Hinj: forall (l1 l2:list nat),
        Forall (λ x, (x < S N)%nat) l1 ->
        Forall (λ x, (x < S N)%nat) l2 ->
        length l1 = p -> length l2 = p -> f l1 = f l2 -> l1 = l2) ns nsₛ α αₛ e E Φ:
    (S N ^ p = S M)%nat->
    ▷ α ↪N (N; ns) ∗ ▷ αₛ ↪ₛN (M; nsₛ) ∗
    (∀ (l : list nat) (m: nat),
       ⌜Forall (λ x, (x < S N)%nat) l⌝ -∗
       ⌜(m < S M)%nat ⌝ -∗
       ⌜length l = p /\ f l = m⌝ -∗
       α ↪N (N; ns ++ l) -∗ αₛ ↪ₛN (M; nsₛ ++ [m]) -∗
       WP e @ E {{ Φ }}
    )
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (Heq) "(>Hα & >Hαₛ & Hwp)".
    iDestruct "Hα" as (fs) "(<-&Hα)".
    iDestruct "Hαₛ" as (fsₛ) "(<-&Hαₛ)".
    destruct (restr_list_inj_fixed_length (S N) (S M) p f) as [g [Hg1 Hg2]]; auto.
    iApply wp_lift_step_spec_couple.
    iIntros (σ1 e1' σ1' ε_now δ_now) "((Hh1 & Ht1 & Htl1) & Hauth2 & Hε2 & Hδ2)".
    iDestruct "Hauth2" as "(HK&Hh2&Ht2&Htl2)/=".
    iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?.
    simplify_map_eq.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    replace (ε_now) with (0+ε_now)%NNR; last (apply nnreal_ext; simpl; lra).
    replace (δ_now) with (0+δ_now)%NNR; last (apply nnreal_ext; simpl; lra).
    iApply spec_coupl_erasables_weak; [done|done|..].
    - apply ARcoupl_to_DPcoupl, ARcoupl_exact. apply Rcoupl_state_state_exp.
      all: exact.
    - eapply iterM_state_step_erasable; done.
    - by eapply state_step_erasable.
    - iIntros (σ2 σ2') "%K".
      destruct K as (xs' & z & Hlen & -> & -> & <-).
      iMod (ghost_map_update ((N; fs ++ xs') : tape) with "Ht1 Hα") as "[Ht1 Hα]".
      iMod (ghost_map_update ((M; fsₛ ++ [g xs']) : tape) with "Ht2 Hαₛ") as "[Ht2 Hαₛ]".
      iModIntro.
      iApply spec_coupl_ret.
      iMod "Hclose'".
      iSpecialize ("Hwp" $! (fin_to_nat <$> xs') (g xs') with "[][][]").
      + iPureIntro.
        apply fin_forall_leq.
      + iPureIntro. apply fin_to_nat_lt.
      + iPureIntro; split; auto.
        rewrite length_fmap //.
      + iFrame.
        replace (0+_)%NNR with (ε_now).
        2:{ apply nnreal_ext. simpl; lra. }
        replace (0+_)%NNR with (δ_now).
        2:{ apply nnreal_ext. simpl; lra. }
        iFrame.
        iApply ("Hwp" with "[Hα][-]").
        * rewrite -fmap_app. iFrame. done.
        * iFrame. rewrite fmap_app. done.
  Qed.


  Lemma wp_couple_exp_decoder (M N p : nat ) ns nsₛ α αₛ e E Φ:
    (S N ^ p = S M)%nat ->
    ▷ α ↪N (N; ns) ∗ ▷ αₛ ↪ₛN (M; nsₛ) ∗
    (∀ (l : list nat) (m: nat),
       ⌜Forall (λ x, (x < S N)%nat) l⌝ -∗
       ⌜(m < S M)%nat ⌝ -∗
       ⌜length l = p⌝ -∗
       α ↪N (N; ns ++ l) -∗ αₛ ↪ₛN (M; nsₛ ++ [@decoder_nat N l]) -∗
       WP e @ E {{ Φ }}
    )
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (Heq) "(>Hα & >Hαₛ & Hwp)".
    set (f := (λ l : list nat, if bool_decide (length l = p) then @decoder_nat N l else 0%nat )).
    iApply (wp_couple_exp M N p f); auto.
    {
      rewrite -Heq /f.
      intros l Hl.
      case_bool_decide; simplify_eq.
      - by apply fin.decoder_aux_ineq.
      - lia.
    }
    {
      rewrite /f.
      intros ?????<-.
      case_bool_decide; [|done].
      rewrite bool_decide_eq_true_2; auto.
      intro.
      by apply (@fin.decoder_aux_inj N).
    }
    iFrame.
    rewrite /f.
    iIntros (??) "% % (%&%) Hα Hαs".
    case_bool_decide; [|done].
    iApply ("Hwp" with "[//] [//] [//] Hα [Hαs]").
    simplify_eq.
    iFrame.
  Qed.


  Lemma wp_couple_exp_decoder_lr (M N p : nat ) ns nsₛ α αₛ e E Φ:
    (S N ^ p = S M)%nat ->
    ▷ α ↪N (N; ns) ∗ ▷ αₛ ↪ₛN (M; nsₛ) ∗
    (∀ (l : list nat) (m: nat),
       ⌜Forall (λ x, (x < S N)%nat) l⌝ -∗
       ⌜(m < S M)%nat ⌝ -∗
       ⌜length l = p⌝ -∗
       α ↪N (N; ns ++ l) -∗ αₛ ↪ₛN (M; nsₛ ++ [@decoder_nat_lr N l]) -∗
       WP e @ E {{ Φ }}
    )
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (Heq) "(>Hα & >Hαₛ & Hwp)".
    set (f := (λ l : list nat, if bool_decide (length l = p) then @decoder_nat_lr N l else 0%nat )).
    iApply (wp_couple_exp M N p f); auto.
    {
      rewrite -Heq /f.
      intros l Hl.
      case_bool_decide; simplify_eq.
      - by apply fin.decoder_lr_aux_ineq.
      - lia.
    }
    {
      rewrite /f.
      intros ?????<-.
      case_bool_decide; [|done].
      rewrite bool_decide_eq_true_2; auto.
      intro.
      by apply (@fin.decoder_lr_aux_inj N).
    }
    iFrame.
    rewrite /f.
    iIntros (??) "% % (%&%) Hα Hαs".
    case_bool_decide; [|done].
    iApply ("Hwp" with "[//] [//] [//] Hα [Hαs]").
    simplify_eq.
    iFrame.
  Qed.


  Lemma wp_couple_exp_rev (M N p:nat)
    (f:(list nat) -> nat)
    (Hdom: forall (l : list nat), Forall (λ x, (x < S N)%nat) l -> (f l < S M)%nat)
    (Hinj: forall (l1 l2:list nat),
        Forall (λ x, (x < S N)%nat) l1 ->
        Forall (λ x, (x < S N)%nat) l2 ->
        length l1 = p -> length l2 = p -> f l1 = f l2 -> l1 = l2) ns nsₛ α αₛ e E Φ:
    (S N ^ p = S M)%nat->
    ▷ α ↪N (M; ns) ∗ ▷ αₛ ↪ₛN (N; nsₛ) ∗
    (∀ (l : list nat) (m: nat),
       ⌜Forall (λ x, (x < S N)%nat) l⌝ -∗
       ⌜(m < S M)%nat ⌝ -∗
       ⌜length l = p /\ f l = m⌝ -∗
       α ↪N (M; ns ++ [m]) -∗ αₛ ↪ₛN (N; nsₛ ++ l) -∗
       WP e @ E {{ Φ }}
    )
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (Heq) "(>Hα & >Hαₛ & Hwp)".
    iApply wp_lift_step_spec_couple.
    iDestruct "Hα" as (fs) "(<-&Hα)".
    iDestruct "Hαₛ" as (fsₛ) "(<-&Hαₛ)".
    destruct (restr_list_inj_fixed_length (S N) (S M) p f) as [g [Hg1 Hg2]]; auto.
    iIntros (σ1 e1' σ1' ε_now δ_now) "((Hh1 & Ht1 & Htl1) & Hauth2 & Hε2 & Hδ2)".
    iDestruct "Hauth2" as "(HK&Hh2&Ht2&Htl2)/=".
    iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?.
    simplify_map_eq.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    replace (ε_now) with (0+ε_now)%NNR; last (apply nnreal_ext; simpl; lra).
    replace δ_now with (0 + δ_now)%NNR at 2 ; [|apply nnreal_ext; simpl; lra].
    iApply spec_coupl_erasables_weak; [done|done|..].
    - apply ARcoupl_to_DPcoupl, ARcoupl_exact. apply Rcoupl_swap. apply Rcoupl_state_state_exp.
      all: exact.
    - by eapply state_step_erasable.
    - eapply iterM_state_step_erasable; done.
    - iIntros (σ2 σ2') "%K".
      destruct K as (xs' & z & Hlen & -> & -> & <-).
      iMod (ghost_map_update ((M; fs ++ [g xs']) : tape) with "Ht1 Hα") as "[Ht1 Hα]".
      iMod (ghost_map_update ((N; fsₛ ++ xs') : tape) with "Ht2 Hαₛ") as "[Ht2 Hαₛ]".
      iModIntro.
      iApply spec_coupl_ret.
      iSpecialize ("Hwp" $! (fin_to_nat <$> xs') (g xs') with "[][][]").
      + iPureIntro.
        apply fin_forall_leq.
      + iPureIntro. apply fin_to_nat_lt.
      + iPureIntro; split; auto.
        rewrite length_fmap //.
      + iFrame.
        replace (0+_)%NNR with (ε_now).
        2:{ apply nnreal_ext. simpl; lra. }
        iFrame.
        iMod "Hclose'".
        iApply ("Hwp" with "[Hα][-]").
        * iFrame. rewrite fmap_app //.
        * iFrame. rewrite -fmap_app //.
  Qed.



  Lemma wp_couple_exp_decoder_rev (M N p:nat) ns nsₛ α αₛ e E Φ:
    (S N ^ p = S M)%nat->
    ▷ α ↪N (M; ns) ∗ ▷ αₛ ↪ₛN (N; nsₛ) ∗
    (∀ (l : list nat) (m: nat),
       ⌜Forall (λ x, (x < S N)%nat) l⌝ -∗
       ⌜(m < S M)%nat ⌝ -∗
       ⌜length l = p⌝ -∗
       α ↪N (M; ns ++ [@decoder_nat N l]) -∗ αₛ ↪ₛN (N; nsₛ ++ l) -∗
       WP e @ E {{ Φ }}
    )
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (Heq) "(>Hα & >Hαₛ & Hwp)".
    set (f := (λ l : list nat, if bool_decide (length l = p) then @decoder_nat N l else 0%nat )).
    iApply (wp_couple_exp_rev M N p f); auto.
    {
      rewrite -Heq /f.
      intros l Hl.
      case_bool_decide; simplify_eq.
      - by apply fin.decoder_aux_ineq.
      - lia.
    }
    {
      rewrite /f.
      intros ?????<-.
      case_bool_decide; [|done].
      rewrite bool_decide_eq_true_2; auto.
      intro.
      by apply (@fin.decoder_aux_inj N).
    }
    iFrame.
    rewrite /f.
    iIntros (??) "% % (%&%) Hα Hαs".
    case_bool_decide; [|done].
    simplify_eq.
    iApply ("Hwp" with "[//] [//] [//] Hα [Hαs]").
    iFrame.
  Qed.


  Lemma wp_couple_exp_decoder_lr_rev (M N p:nat) ns nsₛ α αₛ e E Φ:
    (S N ^ p = S M)%nat->
    ▷ α ↪N (M; ns) ∗ ▷ αₛ ↪ₛN (N; nsₛ) ∗
    (∀ (l : list nat) (m: nat),
       ⌜Forall (λ x, (x < S N)%nat) l⌝ -∗
       ⌜(m < S M)%nat ⌝ -∗
       ⌜length l = p⌝ -∗
       α ↪N (M; ns ++ [@decoder_nat_lr N l]) -∗ αₛ ↪ₛN (N; nsₛ ++ l) -∗
       WP e @ E {{ Φ }}
    )
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (Heq) "(>Hα & >Hαₛ & Hwp)".
    set (f := (λ l : list nat, if bool_decide (length l = p) then @decoder_nat_lr N l else 0%nat )).
    iApply (wp_couple_exp_rev M N p f); auto.
    {
      rewrite -Heq /f.
      intros l Hl.
      case_bool_decide; simplify_eq.
      - by apply fin.decoder_lr_aux_ineq.
      - lia.
    }
    {
      rewrite /f.
      intros ?????<-.
      case_bool_decide; [|done].
      rewrite bool_decide_eq_true_2; auto.
      intro.
      by apply (@fin.decoder_lr_aux_inj N).
    }
    iFrame.
    rewrite /f.
    iIntros (??) "% % (%&%) Hα Hαs".
    case_bool_decide; [|done].
    simplify_eq.
    iApply ("Hwp" with "[//] [//] [//] Hα [Hαs]").
    iFrame.
  Qed.

  (** * Exact couplings  *)
  Lemma wp_couple_tape_rand N f `{Bij nat nat f} K E α z ns Φ e :
    TCEq N (Z.to_nat z) →
    (∀ n, n < S N -> f n < S N)%nat →
    ▷ α ↪N (N; ns) ∗ ⤇ fill K (rand #z) ∗
    (∀ n : nat, α ↪N (N; ns ++ [n]) ∗ ⤇ fill K #(f n) ∗ ⌜ n ≤ N ⌝ -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (H0 Hdom) "(>Hα & Hj & Hwp)".
    iDestruct "Hα" as (fs) "(<-&Hα)".
    destruct (restr_bij_fin (S N) f Hdom) as [ff [Hbij Hff]].
    iApply wp_lift_step_spec_couple.
    iIntros (σ1 e1' σ1' ε δ) "[[Hh1 [Ht1 Htl1]] [Hauth2 Herr]]".
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?.
    iDestruct (spec_auth_prog_agree with "Hauth2 Hj") as %-> .
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    replace ε with (0 + ε)%NNR at 2 ; [|apply nnreal_ext; simpl; lra].
    replace δ with (0 + δ)%NNR at 2 ; [|apply nnreal_ext; simpl; lra].
    iApply (spec_coupl_erasable_steps 1 _ (state_step σ1 α)); [done|done|..].
    { rewrite pexec_1 step_or_final_no_final; last first.
      { apply reducible_not_final. solve_red. }
      apply DPcoupl_steps_ctx_bind_r => /=; [done|].
      apply ARcoupl_to_DPcoupl, ARcoupl_exact, Rcoupl_pos_R, (Rcoupl_state_rand N ff); eauto.
      rewrite -H0 //.
    }
    { by eapply state_step_erasable. }
    iIntros(σ2 e2' σ2' (? & [= ->] & (? & -> & [= -> ->]) & ? & ?)).
    iApply spec_coupl_ret.
    iMod (spec_update_prog (fill K #(ff _)) with "Hauth2 Hj") as "[$ Hspec0]".
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?%lookup_total_correct.
    iMod (ghost_map_update ((_; fs ++ [_]) : tape) with "Ht1 Hα") as "[$ Hα]".
    iModIntro. iMod "Hclose'" as "_".
    iSpecialize ("Hwp" with "[Hα Hspec0]").
    {
      iFrame.
      iSplitR.
      - iPureIntro.
        rewrite fmap_app //.
      - rewrite Hff. iFrame.
        iPureIntro. apply fin_to_nat_le.
    }
    iFrame.
    done.
  Qed.

  (** * rand(unit, N) ~ state_step(α', N) coupling *)
  Lemma wp_couple_rand_tape N f `{Bij nat nat f} z E α ns :
    TCEq N (Z.to_nat z) →
    (∀ n, n < S N -> f n < S N)%nat →
    {{{ ▷ α ↪ₛN (N; ns) }}}
      rand #z @ E
    {{{ (n : nat), RET #n; α ↪ₛN (N; ns ++ [f n]) ∗ ⌜ n ≤ N ⌝ }}}.
  Proof.
    iIntros (H0 Hdom ?) ">Hαs Hwp".
    iDestruct "Hαs" as (fs) "(<-&Hαs)".
    destruct (restr_bij_fin (S N) f Hdom) as [ff [Hbij Hff]].
    iApply wp_lift_step_prog_couple; [done|].
    iIntros (σ1 e1' σ1' ε δ) "[[Hh1 Ht1] [Hauth2 Herr]]".
    iDestruct (spec_auth_lookup_tape with "Hauth2 Hαs") as %?.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    replace (ε) with (0+ε)%NNR at 2 by (apply nnreal_ext; simpl; lra).
    replace δ with (0 + δ)%NNR at 2 ; [|apply nnreal_ext; simpl; lra].
    iApply prog_coupl_step_l_erasable; [done|done|solve_red|..].
    { apply ARcoupl_to_DPcoupl, ARcoupl_exact.
      eapply (Rcoupl_rand_state _ ff); eauto.
      rewrite -H0//. }
    { by eapply state_step_erasable. }
    iIntros (??? (n & [= -> ->] & ->)).
    iMod (spec_auth_update_tape (_; fs ++ [ff _]) with "Hauth2 Hαs") as "[Htapes Hαs]".
    do 2 iModIntro.
    iMod "Hclose'" as "_".
    iFrame.
    iApply wp_value.
    iApply ("Hwp" $! _ with "[$Hαs]").
    iPureIntro.
    rewrite fmap_app -Hff.
    split; auto.
    apply fin_to_nat_le.
  Qed.

  Lemma wp_couple_rand_rand_lbl N f `{Bij nat nat f} z K E α :
    TCEq N (Z.to_nat z) →
    (∀ n, n < S N -> f n < S N)%nat →
    {{{ α ↪ₛN (N; []) ∗ ⤇ fill K (rand(#lbl:α) #z) }}}
      rand #z @ E
      {{{ (n : nat), RET #n; α ↪ₛN (N; []) ∗ ⤇ fill K #(f n) ∗ ⌜ n ≤ N ⌝ }}}.
  Proof.
    iIntros (-> Hdom ?) "(Hα & Hspec) Hwp".
    iApply wp_spec_update.
    iApply (wp_couple_rand_tape with "[$Hα]"); auto.
    iIntros "!>" (n) "[Hα %Hn]".
    simpl.
    iDestruct (read_spec_tape_head with "Hα") as (x xs) "[Hα [%Hrw Hret]]" .
    iMod (step_rand with "[$]") as "[? ?]".
    iModIntro.
    iApply ("Hwp" with "[-]").
    iSpecialize ("Hret" with "[$]").
    rewrite Hrw.
    by iFrame.
  Qed.

  Lemma wp_couple_rand_lbl_rand_lbl N f `{Bij nat nat f} z K E α α' :
    TCEq N (Z.to_nat z) →
    (∀ n, n < S N -> f n < S N)%nat →
    {{{ ▷ α ↪N (N; []) ∗ ▷ α' ↪ₛN (N; []) ∗ ⤇ fill K (rand(#lbl:α') #z) }}}
      rand(#lbl:α) #z @ E
    {{{ (n : nat), RET #n; α ↪N (N; []) ∗ α' ↪ₛN (N; []) ∗ ⤇ fill K #(f n) ∗ ⌜ n ≤ N ⌝ }}}.
  Proof.
    iIntros (???) "(>Hα & >Hαs & Hr) HΨ".
    iMod ec_zero.
    iApply (wp_couple_tapes_bij N f); auto.
    iFrame.
    iIntros (n) "(Hα & Hαs & %) /=".
    iDestruct (read_spec_tape_head with "Hαs") as (x xs) "[Hαs [%Hrw Hret]]" .
    iMod (step_rand with "[$Hr $Hαs]") as "[? ?]".
    iApply (wp_rand_tape with "Hα").
    iIntros "!> (Hα & %)".
    iApply ("HΨ").
    iSpecialize ("Hret" with "[$]").
    rewrite Hrw.
    by iFrame.
  Qed.


  (** * rand(α, N) ~ rand(α, N) wrong bound coupling *)
  Lemma wp_couple_rand_lbl_rand_lbl_wrong N M f `{Bij nat nat f} z K E α α' xs ys :
    TCEq N (Z.to_nat z) →
    N ≠ M →
    (∀ n, n < S N -> f n < S N)%nat →
    {{{ ▷ α ↪N (M; xs) ∗ ▷ α' ↪ₛN (M; ys) ∗ ⤇ fill K (rand(#lbl:α') #z) }}}
      rand(#lbl:α) #z @ E
    {{{ (n : nat), RET #n; α ↪N (M; xs) ∗ α' ↪ₛN (M; ys) ∗ ⤇ fill K #(f n) ∗ ⌜ n ≤ N ⌝ }}}.
  Proof.
    iIntros (-> ? Hdom Ψ) "(>Hα & >Hαs & Hr) Hwp".
    iApply wp_lift_step_prog_couple; [done|].
    iIntros (σ1 e1' σ1' ε δ) "[[Hh [Ht Htl]] [Hs Herr]]".
    iDestruct "Hα" as (fs) "(<-&Hα)".
    iDestruct "Hαs" as (fsₛ) "(<-&Hαs)".
    destruct (restr_bij_fin _ f Hdom) as [g [HBij Hfg]]; auto.
    iDestruct (ghost_map_lookup with "Ht Hα") as %?.
    iDestruct (spec_auth_lookup_tape with "Hs Hαs") as %?.
    iDestruct (spec_auth_prog_agree with "Hs Hr") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".
    replace ε with (0 + ε)%NNR at 2 ; [|apply nnreal_ext; simpl; lra].
    replace δ with (0 + δ)%NNR at 2 ; [|apply nnreal_ext; simpl; lra].
    iApply (prog_coupl_steps_simple _ _ _ _ _ _
              (λ ρ2 ρ2',
                ∃ (n : fin _), ρ2 = (Val #n, σ1) ∧ ρ2' = (fill K #(f n), σ1')))
    ; [done|done|solve_red|solve_red|..].
    { rewrite /= fill_dmap //.
      rewrite -(dret_id_right (prim_step _ _)) /=.
      apply ARcoupl_to_DPcoupl, ARcoupl_exact.
      apply Rcoupl_dmap.
      eapply Rcoupl_mono; [by eapply (Rcoupl_rand_lbl_rand_lbl_wrong _ _ g)|].
      intros [] [] (b & [=] & [=])=>/=.
      simplify_eq. rewrite Hfg. eauto. }
    iIntros (e2 σ2 e2' σ2' (b & [= -> ->] & [= -> ->])) "!>".
    iModIntro.
    iMod (spec_update_prog with "Hs Hr") as "[$ Hr]".
    replace (0 + ε)%NNR with ε; last first.
    { apply nnreal_ext; simpl; lra. }
    iFrame.
    iMod "Hclose" as "_".
    iApply wp_value.
    iApply ("Hwp" with "[-]").
    iFrame.
    iPureIntro.
    split; auto.
    split; auto.
    apply fin_to_nat_le.
  Qed.


End rules.

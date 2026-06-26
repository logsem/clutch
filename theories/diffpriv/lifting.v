(** The "lifting lemmas" in this file serve to lift the rules of the operational
    semantics to the program logic. *)
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From clutch.prelude Require Import NNRbar.
From clutch.diffpriv Require Import weakestpre.

Section lifting.
Context `{!spec_updateGS (lang_markov Λ) Σ, !diffprivWpGS Λ Σ}.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.

#[local] Open Scope R.

Lemma wp_lift_step_couple E Φ e1 s :
  (∀ σ1 e1' σ1' ε1 δ1,
      state_interp σ1 ∗ spec_interp (e1', σ1') ∗ err_interp ε1 δ1 ={E, ∅}=∗
      spec_coupl ∅ σ1 e1' σ1' ε1 δ1 (λ σ2 e2' σ2' ε2 δ2,
        match to_val e1 with
        | Some v => |={∅, E}=> state_interp σ2 ∗ spec_interp (e2', σ2') ∗
                               err_interp ε2 δ2 ∗ Φ v
        | None =>
            prog_coupl e1 σ2 e2' σ2' ε2 δ2 (λ e3 σ3 e3' σ3' ε3 δ3,
                ▷ spec_coupl ∅ σ3 e3' σ3' ε3 δ3 (λ σ4 e4' σ4' ε4 δ4,
                    |={∅, E}=> state_interp σ4 ∗ spec_interp (e4', σ4') ∗
                               err_interp ε4 δ4 ∗ WP e3 @ s; E {{ Φ }}))
        end))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof. rewrite wp_unfold /wp_pre //. Qed.

Lemma wp_lift_step_spec_couple E Φ e1 s :
  (∀ σ1 e1' σ1' ε1 δ1,
      state_interp σ1 ∗ spec_interp (e1', σ1') ∗ err_interp ε1 δ1 ={E, ∅}=∗
      spec_coupl ∅ σ1 e1' σ1' ε1 δ1 (λ σ2 e2' σ2' ε2 δ2,
        |={∅, E}=> state_interp σ2 ∗ spec_interp (e2', σ2') ∗
                   err_interp ε2 δ2 ∗ WP e1 @ s; E {{ Φ }}))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros "H".
  iApply wp_lift_step_couple.
  iIntros (?????) "Hs".
  iMod ("H" with "[$]") as "H".
  iModIntro.
  iApply (spec_coupl_bind with "[] H"); [done|].
  iIntros (?????) "H".
  iApply fupd_spec_coupl.
  iMod "H" as "(?&?&?&H)".
  rewrite wp_unfold /wp_pre.
  iApply ("H" with "[$]").
Qed.

Lemma wp_lift_step_prog_couple E Φ e1 s :
  to_val e1 = None →
  (∀ σ1 e1' σ1' ε1 δ1,
      state_interp σ1 ∗ spec_interp (e1', σ1') ∗ err_interp ε1 δ1 ={E, ∅}=∗
      prog_coupl e1 σ1 e1' σ1' ε1 δ1 (λ e2 σ2 e2' σ2' ε2 δ2,
        ▷ |={∅, E}=> state_interp σ2 ∗ spec_interp (e2', σ2') ∗
                     err_interp ε2 δ2 ∗ WP e2 @ s; E {{ Φ }}))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (Hv) "H".
  iApply wp_lift_step_couple.
  iIntros (?????) "Hs".
  iMod ("H" with "[$]") as "H".
  iApply spec_coupl_ret.
  iModIntro. rewrite Hv.
  iApply (prog_coupl_mono with "[] H").
  iIntros (??????) "H !>".
  by iApply spec_coupl_ret.
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
  iIntros (Hv) "H".
  iApply wp_lift_step_couple.
  iIntros (σ1 e1' σ1' ε1 δ1) "(Hσ & Hρ & Hε)".
  iMod ("H" with "Hσ") as "[%Hs H]". iModIntro.
  iApply spec_coupl_ret.
  rewrite Hv.
  iApply prog_coupl_step_l; [done|].
  iSplitR.
  { iModIntro. iIntros (?????) .
    iModIntro. iApply spec_coupl_ret_err_ge_1. simpl. lra. }
  iIntros (??) "Hpr".
  iMod ("H" with "[$]") as "H".
  iModIntro. iModIntro.
  iApply spec_coupl_ret.
  iMod "H" as "($ & $)".
  iFrame. done.
Qed.

Lemma wp_lift_prim_steps_coupl E Φ e1 s :
  to_val e1 = None →
  (∀ σ1 e1' σ1' ε δ,
      state_interp σ1 ∗ spec_interp (e1', σ1') ∗ err_interp ε δ ={E, ∅}=∗
      ∃ (S : cfg Λ → cfg Λ → Prop) (ε1 ε2 δ1 δ2 : nonnegreal),
        ⌜ε = (ε1 + ε2)%NNR⌝ ∗
        ⌜δ = (δ1 + δ2)%NNR⌝ ∗
        ⌜reducible (e1, σ1)⌝ ∗
        ⌜reducible (e1', σ1')⌝ ∗
        ⌜DPcoupl (prim_step e1 σ1) (prim_step e1' σ1') S ε1 δ1⌝ ∗
        ∀ e2 σ2 e2' σ2', ⌜S (e2, σ2) (e2', σ2')⌝ ={∅}=∗ ▷ |={∅,E}=>
          state_interp σ2 ∗ spec_interp (e2', σ2') ∗
          err_interp ε2 δ2 ∗ WP e2 @ s; E {{ Φ }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (He1) "H".
  iApply wp_lift_step_couple.
  iIntros (σ1 e1' σ1' ε δ) "(Hst & Hsp & Herr)".
  iMod ("H" with "[$Hst $Hsp $Herr]") as
    "[%S [%ε1 [%ε2 [%δ1 [%δ2 (%Hε & %Hδ & %Hred & %Hred' & %Hcpl & H)]]]]]".
  iModIntro.
  iApply spec_coupl_ret.
  rewrite He1.
  iApply (prog_coupl_steps_simple ε2 ε1 _ δ2 δ1 _ S); [done | done | done | done | done |].
  iSplitR.
  { iModIntro. iIntros (?????) .
    iModIntro. iApply spec_coupl_ret_err_ge_1. simpl. lra. }
  iIntros (????) "HR".
  iMod ("H" with "HR") as "H".
  iModIntro.
  by iApply spec_coupl_ret.
Qed.

Lemma wp_lift_prim_step_l_dret E Φ e1 s :
  to_val e1 = None →
  (∀ σ1 e1' σ1' ε δ,
      state_interp σ1 ∗ spec_interp (e1', σ1') ∗ err_interp ε δ ={E, ∅}=∗
      ∃ R (ε1 ε2 δ1 δ2 : nonnegreal),
        ⌜ε = (ε1 + ε2)%NNR⌝ ∗
        ⌜δ = (δ1 + δ2)%NNR⌝ ∗
        ⌜reducible (e1, σ1)⌝ ∗
        ⌜DPcoupl (prim_step e1 σ1) (dret σ1') R ε1 δ1⌝ ∗
        ∀ e2 σ2, ⌜R (e2, σ2) σ1'⌝ ={∅}=∗ ▷ |={∅,E}=>
             state_interp σ2 ∗ spec_interp (e1', σ1') ∗
             err_interp ε2 δ2 ∗ WP e2 @ s; E {{ Φ }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (He1) "H".
  iApply wp_lift_step_couple.
  iIntros (σ1 e1' σ1' ε δ) "(Hst & Hsp & Herr)".
  iMod ("H" with "[$Hst $Hsp $Herr]") as
    "[%R [%ε1 [%ε2 [%δ1 [%δ2 (%Hε & %Hδ & %Hred & %Hcpl & H)]]]]]".
  iModIntro.
  iApply spec_coupl_ret.
  rewrite He1.
  iApply (prog_coupl_step_l_dret ε2 ε1 _ δ2 δ1); [done|done|done|done|].
  iSplitR.
  { iModIntro. iIntros (?????) .
    iModIntro. iApply spec_coupl_ret_err_ge_1. simpl. lra. }
  iIntros (??) "HR".
  iMod ("H" with "HR") as "H".
  iModIntro.
  by iApply spec_coupl_ret.
Qed.

Lemma wp_lift_prim_step_l_erasable E Φ e1 s :
  to_val e1 = None →
  (∀ σ1 e1' σ1' ε δ,
      state_interp σ1 ∗ spec_interp (e1', σ1') ∗ err_interp ε δ ={E, ∅}=∗
      ∃ R μ1' (ε1 ε2 δ1 δ2 : nonnegreal),
        ⌜ε = (ε1 + ε2)%NNR⌝ ∗
        ⌜δ = (δ1 + δ2)%NNR⌝ ∗
        ⌜reducible (e1, σ1)⌝ ∗
        ⌜DPcoupl (prim_step e1 σ1) μ1' R ε1 δ1⌝ ∗
        ⌜erasable μ1' σ1'⌝ ∗
        ∀ e2 σ2 σ2', ⌜R (e2, σ2) σ2'⌝ ={∅}=∗ ▷ |={∅,E}=>
             state_interp σ2 ∗ spec_interp (e1', σ2') ∗
             err_interp ε2 δ2 ∗ WP e2 @ s; E {{ Φ }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (He1) "H".
  iApply wp_lift_step_couple.
  iIntros (σ1 e1' σ1' ε δ) "(Hst & Hsp & Herr)".
  iMod ("H" with "[$Hst $Hsp $Herr]") as
    "[%R [%μ1' [%ε1 [%ε2 [%δ1 [%δ2 (%Hε & %Hδ & %Hred & %Hcpl & %Hera & H)]]]]]]".
  iModIntro.
  iApply spec_coupl_ret.
  rewrite He1.
  iApply (prog_coupl_step_l_erasable ε2 ε1 δ2 δ1 μ1'); [done|done|done|done|done|].
  iSplitR.
  { iModIntro. iIntros (?????) .
    iModIntro. iApply spec_coupl_ret_err_ge_1. simpl. lra. }
  iIntros (???) "HR".
  iMod ("H" with "HR") as "H".
  iModIntro.
  by iApply spec_coupl_ret.
Qed.

Lemma wp_lift_prim_steps_choice E Φ e1 s :
  to_val e1 = None →
  (∀ σ1 e1' σ1' ε δ,
      state_interp σ1 ∗ spec_interp (e1', σ1') ∗ err_interp ε δ ={E, ∅}=∗
      ∃ (P : cfg Λ → Prop) (R R' : cfg Λ → cfg Λ → Prop)
        (ε1 ε2 ε1' ε2' δ1 δ2 δ1' : nonnegreal),
        ⌜ε = (ε1 + ε2)%NNR⌝ ∗
        ⌜ε = (ε1' + ε2')%NNR⌝ ∗
        ⌜δ = (δ1 + δ2 + δ1')%NNR⌝ ∗
        ⌜reducible (e1, σ1)⌝ ∗
        ⌜reducible (e1', σ1')⌝ ∗
        ⌜∀ a a' b, P a → ¬P a' → ¬(R a b ∧ R' a' b)⌝ ∗
        ⌜DPcoupl (prim_step e1 σ1) (prim_step e1' σ1') R ε1 δ1⌝ ∗
        ⌜DPcoupl (prim_step e1 σ1) (prim_step e1' σ1') R' ε1' δ1'⌝ ∗
        ∀ e2 σ2 e2' σ2',
          (⌜P (e2, σ2) ∧ R (e2, σ2) (e2', σ2')⌝ ={∅}=∗ ▷ |={∅,E}=>
             state_interp σ2 ∗ spec_interp (e2', σ2') ∗
             err_interp ε2 δ2 ∗ WP e2 @ s; E {{ Φ }}) ∗
          (⌜¬P (e2, σ2) ∧ R' (e2, σ2) (e2', σ2')⌝ ={∅}=∗ ▷ |={∅,E}=>
             state_interp σ2 ∗ spec_interp (e2', σ2') ∗
             err_interp ε2' δ2 ∗ WP e2 @ s; E {{ Φ }}))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (He1) "H".
  iApply wp_lift_step_couple.
  iIntros (σ1 e1' σ1' ε δ) "(Hst & Hsp & Herr)".
  iMod ("H" with "[$Hst $Hsp $Herr]") as
    "[%P [%R [%R' [%ε1 [%ε2 [%ε1' [%ε2' [%δ1 [%δ2 [%δ1'
      (%Hε & %Hε' & %Hδ & %Hred & %Hred' & %Hindep & %Hcpl & %Hcpl' & H)
    ]]]]]]]]]]".
  iModIntro.
  iApply spec_coupl_ret.
  rewrite He1.
  iApply (prog_coupl_steps_choice ε2 ε1 ε2' ε1' _ δ2 δ1 δ1' _);
    [done | done | done | done | done | done | done | done |].
  iSplitR.
  { iModIntro. iIntros (?????) .
    iModIntro. iApply spec_coupl_ret_err_ge_1. simpl. lra. }
  iIntros (e2 σ2 e2' σ2').
  iDestruct ("H" $! e2 σ2 e2' σ2') as "[H1 H2]".
  iSplitL "H1".
  - iIntros "HR".
    iMod ("H1" with "HR") as "H1".
    iModIntro.
    by iApply spec_coupl_ret.
  - iIntros "HR".
    iMod ("H2" with "HR") as "H2".
    iModIntro.
    by iApply spec_coupl_ret.
Qed.

Lemma wp_lift_prim_steps_coupl_adv E Φ e1 s :
  to_val e1 = None →
  (∀ σ1 e1' σ1' ε δ,
      state_interp σ1 ∗ spec_interp (e1', σ1') ∗ err_interp ε δ ={E, ∅}=∗
      ∃ (S : cfg Λ → cfg Λ → Prop) (E2 D2 : cfg Λ → cfg Λ → nonnegreal) (ε1 ε2 δ1 δ2 : nonnegreal),
        ⌜ε = (ε1 + ε2)%NNR⌝ ∗
        ⌜δ = (δ1 + δ2)%NNR⌝ ∗
        ⌜reducible (e1, σ1)⌝ ∗
        ⌜reducible (e1', σ1')⌝ ∗
        ⌜DPcoupl (prim_step e1 σ1) (prim_step e1' σ1') S ε1 δ1⌝ ∗
        ⌜forall ρ1 ρ2, D2 ρ1 ρ2 <= 1⌝ ∗
        ⌜forall (h1 h2 : cfg Λ → R),
            (forall a, 0 <= h1 a <= 1) ->
            (forall b, 0 <= h2 b <= 1) ->
            (forall a b, S a b -> h1 a <= exp (E2 a b) * h2 b + D2 a b) ->
            Expval (prim_step e1 σ1) h1 <=
              exp ε2 * Expval (prim_step e1' σ1') h2 + δ2⌝ ∗
        ∀ e2 σ2 e2' σ2',  ⌜S (e2, σ2) (e2',σ2')⌝ ={∅}=∗ ▷|={∅,E}=>
          state_interp σ2 ∗ spec_interp (e2', σ2') ∗
          err_interp (E2 (e2, σ2) (e2', σ2'))%NNR
                     (D2 (e2, σ2) (e2', σ2'))%NNR ∗
          WP e2 @ s; E {{ Φ }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (He1) "H".
  iApply wp_lift_step_couple.
  iIntros (σ1 e1' σ1' ε δ) "(Hst & Hsp & Herr)".
  iMod ("H" with "[$Hst $Hsp $Herr]") as
    "[%S [%E2 [%D2 [%ε1 [%ε2 [%δ1 [%δ2 (%Hε & %Hδ & %Hred & %Hred' & %Hcpl & %HD2 & %Hkanto & H)]]]]]]]".
  iModIntro.
  iApply spec_coupl_ret.
  rewrite He1.
  subst.
  iApply (prog_coupl_steps_adv (ε1+ε2)%NNR (δ1+δ2)%NNR S _ _ _ _ E2 D2);
    [done | done | done | |].
  - intros h1 h2 Hh1 Hh2 Hpair.
    apply (Rle_trans _ (exp ε2 * Expval (prim_step e1' σ1') h2 + δ2)).
    + apply Hkanto; done.
    + apply Rplus_le_compat.
      * apply Rmult_le_compat_r.
        -- apply Expval_ge_0'. intro b. apply Hh2.
        -- apply exp_mono. simpl. have := cond_nonneg ε1. lra.
      * simpl. have := cond_nonneg δ1. lra.
  - iSplitR.
    + iModIntro. iIntros (e2 σ2 e2' σ2' ε') .
      iModIntro. iApply spec_coupl_ret_err_ge_1. simpl. lra.
    + iIntros (e2 σ2 e2' σ2') "HS".
      iMod ("H" with "HS") as "H".
      iModIntro.
      iApply spec_coupl_ret.
      iExact "H".
Qed.

Lemma wp_lift_prim_steps_coupl_adv' E Φ e1 s :
  to_val e1 = None →
  (∀ σ1 e1' σ1' ε δ,
      state_interp σ1 ∗ spec_interp (e1', σ1') ∗ err_interp ε δ ={E, ∅}=∗
      ∃ (E2 D2 : cfg Λ → cfg Λ → nonnegreal),
        ⌜reducible (e1, σ1)⌝ ∗
        ⌜reducible (e1', σ1')⌝ ∗
        ⌜∀ ρ1 ρ2, D2 ρ1 ρ2 <= 1⌝ ∗
        ⌜forall (h1 h2 : cfg Λ → R),
            (forall a, 0 <= h1 a <= 1) ->
            (forall b, 0 <= h2 b <= 1) ->
            (forall a b, h1 a <= exp (E2 a b) * h2 b + D2 a b) ->
            Expval (prim_step e1 σ1) h1 <=
              exp ε * Expval (prim_step e1' σ1') h2 + δ⌝ ∗
        ∀ e2 σ2 e2' σ2', ▷ |={∅,E}=>
          state_interp σ2 ∗ spec_interp (e2', σ2') ∗
          err_interp (E2 (e2, σ2) (e2', σ2'))%NNR
                     (D2 (e2, σ2) (e2', σ2'))%NNR ∗
          WP e2 @ s; E {{ Φ }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (He1) "H".
  iApply wp_lift_step_couple.
  iIntros (σ1 e1' σ1' ε δ) "(Hst & Hsp & Herr)".
  iMod ("H" with "[$Hst $Hsp $Herr]") as
    "[%E2 [%D2 (%Hred & %Hred' & %HD2 & %Hkanto & H)]]".
  iModIntro.
  iApply spec_coupl_ret.
  rewrite He1.
  iApply (prog_coupl_steps_adv_alt _ _ _ _ _ _ E2 D2);
    [done | done | done | done |].
  iIntros (????).
  iModIntro.
  by iApply spec_coupl_ret.
Qed.

Lemma wp_lift_prim_steps_coupl_adv_err_le_1 E Φ e1 s :
  to_val e1 = None →
  (∀ σ1 e1' σ1' ε δ,
      state_interp σ1 ∗ spec_interp (e1', σ1') ∗ err_interp ε δ ={E, ∅}=∗
      ∃ (S : cfg Λ → cfg Λ → Prop) (E2 D2 : cfg Λ → cfg Λ → nonnegreal) (ε1 ε2 δ1 δ2 : nonnegreal),
        ⌜ε = (ε1 + ε2)%NNR⌝ ∗
        ⌜δ = (δ1 + δ2)%NNR⌝ ∗
        ⌜reducible (e1, σ1)⌝ ∗
        ⌜reducible (e1', σ1')⌝ ∗
        ⌜DPcoupl (prim_step e1 σ1) (prim_step e1' σ1') S ε1 δ1⌝ ∗
        ⌜∀ ρ1 ρ2, D2 ρ1 ρ2 <= 1⌝ ∗
        ⌜forall (h1 h2 : cfg Λ → R),
            (forall a, 0 <= h1 a <= 1) ->
            (forall b, 0 <= h2 b <= 1) ->
            (forall a b, S a b -> h1 a <= exp (E2 a b) * h2 b + D2 a b) ->
            Expval (prim_step e1 σ1) h1 <=
              exp ε2 * Expval (prim_step e1' σ1') h2 + δ2⌝ ∗
        ∀ e2 σ2 e2' σ2', ⌜S (e2, σ2) (e2',σ2')⌝ ={∅}=∗ ▷|={∅,E}=>
          ⌜1 <= (D2 (e2, σ2) (e2', σ2') : R)⌝ ∨ (
            state_interp σ2 ∗ spec_interp (e2', σ2') ∗
            err_interp (E2 (e2, σ2) (e2', σ2'))%NNR
                       (D2 (e2, σ2) (e2', σ2'))%NNR ∗
            WP e2 @ s; E {{ Φ }}))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (He1) "H".
  iApply wp_lift_step_couple.
  iIntros (σ1 e1' σ1' ε δ) "(Hst & Hsp & Herr)".
  iMod ("H" with "[$Hst $Hsp $Herr]") as
    "[%S [%E2 [%D2 [%ε1 [%ε2 [%δ1 [%δ2 (%Hε & %Hδ & %Hred & %Hred' & %Hcpl & %HD2 & %Hkanto & H)]]]]]]]".
  iModIntro.
  iApply spec_coupl_ret.
  rewrite He1.
  subst.
  iApply (prog_coupl_steps_adv (ε1+ε2)%NNR (δ1+δ2)%NNR S _ _ _ _ E2 D2);
    [done | done | done | |].
  - intros h1 h2 Hh1 Hh2 Hpair.
    apply (Rle_trans _ (exp ε2 * Expval (prim_step e1' σ1') h2 + δ2)).
    + apply Hkanto; done.
    + apply Rplus_le_compat.
      * apply Rmult_le_compat_r.
        -- apply Expval_ge_0'. intro b. apply Hh2.
        -- apply exp_mono. simpl. have := cond_nonneg ε1. lra.
      * simpl. have := cond_nonneg δ1. lra.
  - iSplitR.
    + iModIntro. iIntros (e2 σ2 e2' σ2' ε') .
      iModIntro. iApply spec_coupl_ret_err_ge_1. simpl. lra.
    + iIntros (e2 σ2 e2' σ2') "HS".
      iMod ("H" with "HS") as "H".
      iModIntro.
      destruct (Rlt_or_le ((D2 (e2, σ2) (e2', σ2') : R)) 1) as [HD2lt | HD2ge].
      * iApply spec_coupl_ret.
        iModIntro.
        iMod "H" as "[%Hle | (?&?&?&?)]".
        -- lra.
        -- by iFrame.
      * iApply spec_coupl_ret_err_ge_1.
        simpl in *. lra.
Qed.


Lemma wp_lift_prim_steps_coupl_adv_frame_err_le_1 E Φ e1 s :
  to_val e1 = None →
  (∀ σ1 e1' σ1' ε δ,
      state_interp σ1 ∗ spec_interp (e1', σ1') ∗ err_interp ε δ ={E, ∅}=∗
      ∃ (S : cfg Λ → cfg Λ → Prop) (E2 D2 : cfg Λ → cfg Λ → nonnegreal) (ε1 ε2 δ1 δ2 : nonnegreal),
        ⌜ε = (ε1 + ε2)%NNR⌝ ∗
        ⌜δ = (δ1 + δ2)%NNR⌝ ∗
        ⌜reducible (e1, σ1)⌝ ∗
        ⌜reducible (e1', σ1')⌝ ∗
        ⌜∀ ρ1 ρ2, D2 ρ1 ρ2 <= 1⌝ ∗
        ⌜forall (h1 h2 : cfg Λ → R),
            (forall a, 0 <= h1 a <= 1) ->
            (forall b, 0 <= h2 b <= 1) ->
            (forall a b, S a b -> h1 a <= exp (E2 a b) * h2 b + D2 a b) ->
            Expval (prim_step e1 σ1) h1 <=
              exp ε1 * Expval (prim_step e1' σ1') h2 + δ1⌝ ∗
        ∀ e2 σ2 e2' σ2', ⌜S (e2, σ2) (e2',σ2')⌝ ={∅}=∗ ▷|={∅,E}=>
          ⌜1 <= (D2 (e2, σ2) (e2', σ2') + δ2 : R)⌝ ∨ (
            state_interp σ2 ∗ spec_interp (e2', σ2') ∗
            err_interp (E2 (e2, σ2) (e2', σ2') + ε2)%NNR
                       (D2 (e2, σ2) (e2', σ2') + δ2)%NNR ∗
            WP e2 @ s; E {{ Φ }}))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (He1) "H".
  iApply wp_lift_step_couple.
  iIntros (σ1 e1' σ1' ε δ) "(Hst & Hsp & Herr)".
  iMod ("H" with "[$Hst $Hsp $Herr]") as
    "[%S [%E2 [%D2 [%ε1 [%ε2 [%δ1 [%δ2 (%Hε & %Hδ & %Hred & %Hred' & %HD2 & %Hkanto & H)]]]]]]]".
  iModIntro.
  iApply spec_coupl_ret.
  rewrite He1.
  iApply (prog_coupl_steps_adv_frame ε1 ε2 _ δ1 δ2 _ S _ _ _ _ E2 D2);
    [done | done | done | done | done | done |].
  iSplitR.
  { iModIntro. iIntros (?????) .
    iModIntro. iApply spec_coupl_ret_err_ge_1. simpl. lra. }
  iIntros (e2 σ2 e2' σ2') "HS".
  iMod ("H" with "HS") as "H".
  iModIntro.
  destruct (Rlt_or_le ((D2 (e2, σ2) (e2', σ2') + δ2: R)) 1) as [HD2lt | HD2ge].
  - iApply spec_coupl_ret.
    iModIntro.
    iMod "H" as "[%Hle | (?&?&?&?)]".
    + lra.
    + by iFrame.
  - iApply spec_coupl_ret_err_ge_1.
    simpl in *. have := cond_nonneg δ2. lra.
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
  iIntros (?) "H". iApply wp_lift_step_later; [done|]. iIntros (?) "Hσ".
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
  iIntros (?) "H". iApply wp_lift_atomic_step_fupd; [done|].
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

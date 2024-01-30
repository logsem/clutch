From Coq Require Export Reals Psatz.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Import fancy_updates ghost_map.
From iris.bi Require Export fixpoint big_op.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.prob_lang Require Import lang erasure.
From clutch.tpref_logic Require Import weakestpre spec primitive_laws.
From clutch.prob Require Import couplings distribution markov.

Section adequacy.
  Context `{!tprG δ Σ}.
  Implicit Type e : expr.
  Implicit Type σ : state.
  Implicit Type a : mstate δ.
  Implicit Type b : mstate_ret δ.

  #[local]
  Lemma rwp_coupl_final e σ a b R n :
    to_final a = Some b →
    to_val e = None →
    rwp_coupl e σ a (λ '(e2, σ2) a2,
        ∀ n, |={∅}=> |={∅}▷=>^n ⌜exec n a2 ≾ lim_exec (e2, σ2) : R⌝)
      ⊢ |={∅}=> |={∅}▷=>^n ⌜exec n a ≾ lim_exec (e, σ) : R⌝.
  Proof.
    iIntros (Hf Hv) "Hcpl".
    erewrite exec_is_final; [|done].
    rewrite rwp_coupl_unfold.
    iDestruct "Hcpl" as "[(%S & % & % & HR) | [(%S & %Hcpl & HR) | [(%S & % & %Hcpl & HR) | (% & % & %Hαs & %Hcpl & HR)]]]".
    - iEval (rewrite -(dret_id_left (λ a, dret b) a)).
      rewrite lim_exec_step step_or_final_no_final; [|auto].
      iApply (step_fupdN_mono _ _ _ (⌜∀ ρ', S ρ' a → dret b ≾ lim_exec ρ' : R⌝)%I).
      { iIntros (Hcnt). iPureIntro.
        eapply refRcoupl_dbind; [|by apply Rcoupl_refRcoupl', Rcoupl_pos_R].
        intros a1 [e' σ'] (HR & Hs & <-%dret_pos). eauto. }
      destruct n.
      + iIntros ([e2 σ2] HR).
        iMod ("HR" with "[//]") as "H".
        iMod ("H" $! O). by erewrite exec_is_final.
      + iIntros "!>" ([e2 σ2] HR).
        rewrite step_fupdN_Sn.
        iMod ("HR" with "[//]") as "H".
        iMod ("H" $! n). by erewrite exec_is_final.
    - rewrite is_final_dzero in Hcpl; [|eauto].
      apply Rcoupl_mass_eq in Hcpl.
      rewrite dret_mass dzero_mass in Hcpl.
      lra.
    - rewrite is_final_dzero in Hcpl; [|eauto].
      apply Rcoupl_mass_eq in Hcpl.
      rewrite prim_step_mass ?dzero_mass in Hcpl; [|done].
      lra.
    - rewrite is_final_dzero in Hcpl; [|eauto].
      apply Rcoupl_mass_eq in Hcpl.
      rewrite dzero_mass in Hcpl.
      rewrite state_steps_mass // in Hcpl. lra.
  Qed.

  Theorem wp_refRcoupl_step_fupdN (e : expr) (σ : state) (a : mstate δ) (n : nat) :
    state_interp σ ∗ specA a ∗ WP e {{ _, True }} ⊢
    |={⊤,∅}=> |={∅}▷=>^n ⌜lim_exec (e, σ) ≿ exec n a : λ _ _, True⌝.
  Proof.
    iIntros "(Hσ & Ha & Hrwp)".
    iRevert (σ a n) "Hσ Ha".
    iApply (rwp_ind' (λ e, _) with "[] Hrwp"); clear.
    iIntros "!#" (e) "Hrwp"; iIntros (σ a n) "Hσ Ha".
    rewrite /rwp_pre.
    iSpecialize ("Hrwp" with "[$]").
    case_match eqn:Hv.
    - iMod "Hrwp" as "(Hσ & Hauth & _)".
      erewrite lim_exec_final; [|done].
      iApply fupd_mask_intro; [set_solver|]; iIntros "_".
      iApply step_fupdN_intro; [done|].
      iModIntro.
      iPureIntro.
      eapply refRcoupl_trivial.
      rewrite dret_mass //.
    - iMod "Hrwp" as "Hcpl".
      iDestruct (rwp_coupl_strong_mono _ _ _ _
                   ((λ '(e2, σ2) a2, ∀ n, |={∅}=> |={∅}▷=>^n
                        ⌜exec n a2 ≾ lim_exec (e2, σ2) : _⌝))%I
                 with "[] Hcpl") as "Hcpl".
      { iIntros ([e' σ'] a') "(% & H) %".
        iMod "H" as "(? & ? & H)".
        by iMod ("H" with "[$] [$]"). }
      iInduction n as [|n] "IH" forall (e σ a Hv).
      + destruct (to_final a) eqn:Hf.
        { by iApply rwp_coupl_final. }
        rewrite exec_O_not_final; [|by apply to_final_None_2].
        iModIntro. iPureIntro.
        apply refRcoupl_dzero.
      + destruct (to_final a) eqn:Hf.
        { by iApply rwp_coupl_final. }
        rewrite rwp_coupl_unfold.
        iDestruct "Hcpl" as "[(%R & % & % & HR) | [(%R & %Hcpl & HR) | [(%R & % & %Hcpl & HR) | (% & % & %Hαs & %Hcpl & HR)]]]".
        * iEval (rewrite -(dret_id_left (exec _))).
          rewrite lim_exec_step step_or_final_no_final; [|eauto].
          iApply (step_fupdN_mono _ _ _
                    (⌜∀ ρ', R ρ' a → exec _ a ≾ lim_exec ρ' : _⌝)%I).
          { iIntros (Hcnt). iPureIntro.
            eapply refRcoupl_dbind; [|by apply Rcoupl_refRcoupl', Rcoupl_pos_R].
            intros a1 [e' σ'] (HR & Hs & <-%dret_pos). eauto. }
          iModIntro.
          iIntros ([e2 σ2] HR).
          rewrite step_fupdN_Sn.
          iMod ("HR" with "[//]") as "H".
          iMod ("H" $! (S n)) as "HR".
          rewrite -step_fupdN_Sn.
          iApply "HR".
        * rewrite exec_Sn_not_final; [|eauto].
          iEval (rewrite -(dret_id_left (lim_exec))).
          iApply (step_fupdN_mono _ _ _
                    (⌜∀ a, R (e, σ) a → exec n a ≾ lim_exec (e, σ) :_⌝)%I).
          { iIntros (HR). iPureIntro.
            eapply refRcoupl_dbind; [|by apply Rcoupl_refRcoupl', Rcoupl_pos_R].
            intros a1 [? ?] (? & [= -> ->]%dret_pos & Hs). eauto. }
          iIntros "!>" (a'' HR).
          rewrite step_fupdN_Sn.
          iMod ("HR" with "[//]") as "HR".
          do 2 iModIntro. iMod "HR".
          iApply ("IH" with "[//] HR").
        * rewrite exec_Sn_not_final; [|eauto].
          rewrite lim_exec_step step_or_final_no_final; [|eauto].
          iApply (step_fupdN_mono _ _ _
                    (⌜∀ ρ' a', R ρ' a' → exec n a' ≾ lim_exec ρ' : _⌝)%I).
          { iIntros (HR). iPureIntro.
            eapply refRcoupl_dbind; [|by apply Rcoupl_refRcoupl'].
            intros ???. by apply HR. }
          iModIntro.
          iIntros ([e' σ'] a0 HR).
          rewrite step_fupdN_Sn.
          iMod ("HR" with "[//]") as "HR".
          do 2 iModIntro.
          by iMod "HR".
        * rewrite exec_Sn_not_final; [|eauto].
          erewrite (lim_exec_eq_erasure αs); [|done].
          iModIntro.
          iApply (step_fupdN_mono _ _ _
                    (⌜∀ σ' a', R2 σ' a' → exec n a' ≾ lim_exec (e, σ') : λ _ _, True⌝)%I).
          { iIntros (Hcnt). iPureIntro.
            eapply refRcoupl_dbind; [|by eapply Rcoupl_refRcoupl'].
            intros ???. by eapply Hcnt. }
          iIntros (σ' a' ?).
          rewrite step_fupdN_Sn.
          iMod ("HR" with "[//]") as "H".
          iIntros "!> !>".
          iMod "H".
          iApply ("IH" with "[//] H").
  Qed.

  Theorem wp_refRcoupl_step_fupdN_res (e : expr) (σ : state) (a : mstate δ) (n : nat) (φ : val → mstate_ret δ → Prop) :
    state_interp σ ∗ specA a ∗ WP e {{ v, ∃ a' b, specF a' ∗ ⌜to_final a' = Some b⌝ ∗ ⌜φ v b⌝ }} ⊢
    |={⊤,∅}=> |={∅}▷=>^n ⌜lim_exec (e, σ) ≿ exec n a : φ⌝.
  Proof.
    iIntros "(Hσ & Ha & Hrwp)".
    iRevert (σ a n) "Hσ Ha".
    iApply (rwp_ind' (λ e, _) with "[] Hrwp"); clear.
    iIntros "!#" (e) "Hrwp"; iIntros (σ a n) "Hσ Ha".
    rewrite /rwp_pre.
    iSpecialize ("Hrwp" with "[$]").
    case_match eqn:Hv.
    - iMod "Hrwp" as "(Hσ & Hauth & (% & % & Hspec & % & %))".
      iDestruct (spec_auth_agree with "Hauth Hspec") as %<-.
      erewrite lim_exec_final; [|done].
      iApply fupd_mask_intro; [set_solver|]; iIntros "_".
      iApply step_fupdN_intro; [done|].
      iModIntro.
      iPureIntro.
      erewrite exec_is_final; [|done].
      by apply Rcoupl_refRcoupl, Rcoupl_dret.
    - iMod "Hrwp" as "Hcpl".
      iDestruct (rwp_coupl_strong_mono _ _ _ _
                   ((λ '(e2, σ2) a2, ∀ n, |={∅}=> |={∅}▷=>^n
                        ⌜exec n a2 ≾ lim_exec (e2, σ2) : _⌝))%I
                 with "[] Hcpl") as "Hcpl".
      { iIntros ([e' σ'] a') "(% & H) %".
        iMod "H" as "(? & ? & H)".
        by iMod ("H" with "[$] [$]"). }
      iInduction n as [|n] "IH" forall (e σ a Hv).
      + destruct (to_final a) eqn:Hf.
        { by iApply rwp_coupl_final. }
        rewrite exec_O_not_final; [|by apply to_final_None_2].
        iModIntro. iPureIntro.
        apply refRcoupl_dzero.
      + destruct (to_final a) eqn:Hf.
        { by iApply rwp_coupl_final. }
        rewrite rwp_coupl_unfold.
        iDestruct "Hcpl" as "[(%R & % & % & HR) | [(%R & %Hcpl & HR) | [(%R & % & %Hcpl & HR) | (% & % & %Hαs & %Hcpl & HR)]]]".
        * iEval (rewrite -(dret_id_left (exec _))).
          rewrite lim_exec_step step_or_final_no_final; [|eauto].
          iApply (step_fupdN_mono _ _ _
                    (⌜∀ ρ', R ρ' a → exec _ a ≾ lim_exec ρ' : _⌝)%I).
          { iIntros (Hcnt). iPureIntro.
            eapply refRcoupl_dbind; [|by apply Rcoupl_refRcoupl', Rcoupl_pos_R].
            intros a1 [e' σ'] (HR & Hs & <-%dret_pos). eauto. }
          iModIntro.
          iIntros ([e2 σ2] HR).
          rewrite step_fupdN_Sn.
          iMod ("HR" with "[//]") as "H".
          iMod ("H" $! (S n)) as "HR".
          rewrite -step_fupdN_Sn.
          iApply "HR".
        * rewrite exec_Sn_not_final; [|eauto].
          iEval (rewrite -(dret_id_left (lim_exec))).
          iApply (step_fupdN_mono _ _ _
                    (⌜∀ a, R (e, σ) a → exec n a ≾ lim_exec (e, σ) :_⌝)%I).
          { iIntros (HR). iPureIntro.
            eapply refRcoupl_dbind; [|by apply Rcoupl_refRcoupl', Rcoupl_pos_R].
            intros a1 [? ?] (? & [= -> ->]%dret_pos & Hs). eauto. }
          iIntros "!>" (a'' HR).
          rewrite step_fupdN_Sn.
          iMod ("HR" with "[//]") as "HR".
          do 2 iModIntro. iMod "HR".
          iApply ("IH" with "[//] HR").
        * rewrite exec_Sn_not_final; [|eauto].
          rewrite lim_exec_step step_or_final_no_final; [|eauto].
          iApply (step_fupdN_mono _ _ _
                    (⌜∀ ρ' a', R ρ' a' → exec n a' ≾ lim_exec ρ' : _⌝)%I).
          { iIntros (HR). iPureIntro.
            eapply refRcoupl_dbind; [|by apply Rcoupl_refRcoupl'].
            intros ???. by apply HR. }
          iModIntro.
          iIntros ([e' σ'] a0 HR).
          rewrite step_fupdN_Sn.
          iMod ("HR" with "[//]") as "HR".
          do 2 iModIntro.
          by iMod "HR".
        * rewrite exec_Sn_not_final; [|eauto].
          erewrite (lim_exec_eq_erasure αs); [|done].
          iModIntro.
          iApply (step_fupdN_mono _ _ _
                    (⌜∀ σ' a', R2 σ' a' → exec n a' ≾ lim_exec (e, σ') : _⌝)%I).
          { iIntros (Hcnt). iPureIntro.
            eapply refRcoupl_dbind; [|by eapply Rcoupl_refRcoupl'].
            intros ???. by eapply Hcnt. }
          iIntros (σ' a' ?).
          rewrite step_fupdN_Sn.
          iMod ("HR" with "[//]") as "H".
          iIntros "!> !>".
          iMod "H".
          iApply ("IH" with "[//] H").
  Qed.

End adequacy.

Theorem wp_refRcoupl `{!tprGpreS δ Σ} e σ a n :
  (∀ `{!tprG δ Σ}, ⊢ specF a -∗ WP e {{ _, True }}) →
  lim_exec (e, σ) ≿ exec n a : (λ _ _, True).
Proof.
  intros Hwp.
  eapply (step_fupdN_soundness_no_lc _ n 0).
  iIntros (Hinv) "_".
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh _]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht _]]".
  iMod (spec_auth_alloc a) as (HspecG) "[Hauth Hfrag]".
  set (HclutchG := TprG _ Σ _ _ _ γH γT HspecG).
  iApply wp_refRcoupl_step_fupdN.
  iFrame.
  by iApply (Hwp with "[Hfrag]").
Qed.

Theorem wp_refRcoupl_res `{!tprGpreS δ Σ} e σ a n φ :
  (∀ `{!tprG δ Σ},
    ⊢ specF a -∗  WP e {{ v, ∃ a' b, specF a' ∗ ⌜to_final a' = Some b⌝ ∗ ⌜φ v b⌝ }}) →
  lim_exec (e, σ) ≿ exec n a : φ.
Proof.
  intros Hwp.
  eapply (step_fupdN_soundness_no_lc _ n 0).
  iIntros (Hinv) "_".
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh _]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht _]]".
  iMod (spec_auth_alloc a) as (HspecG) "[Hauth Hfrag]".
  set (HclutchG := TprG _ Σ _ _ _ γH γT HspecG).
  iApply wp_refRcoupl_step_fupdN_res.
  iFrame.
  by iApply (Hwp with "[Hfrag]").
Qed.

Corollary wp_refRcoupl_mass Σ `{!tprGpreS δ Σ} e σ a :
  (∀ `{!tprG δ Σ}, ⊢ specF a -∗ WP e {{ _, True }}) →
  SeriesC (lim_exec a) <= SeriesC (lim_exec (e, σ)).
Proof.
  intros Hrwp.
  apply lim_exec_leq_mass.
  intros.
  eapply (refRcoupl_mass_eq _ _ (λ _ _, True)).
  eapply wp_refRcoupl.
  iIntros (?) "Hfrag".
  iApply rwp_mono; [|iApply (Hrwp with "Hfrag")].
  iIntros (?) "H". eauto.
Qed.

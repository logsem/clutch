From Coq Require Export Reals Psatz.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Import fancy_updates ghost_map.
From iris.bi Require Export fixpoint big_op.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.prob_lang Require Import lang.
From clutch.tpref_logic Require Import weakestpre spec primitive_laws.
From clutch.prob Require Import couplings distribution markov.

(* TODO: generalize to any language? *)
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
        ∀ n, |={∅}=> |={∅}▷=>^n ⌜exec n a2 ≾ lim_exec_val (e2, σ2) : R⌝)
      ⊢ |={∅}=> |={∅}▷=>^n ⌜exec n a ≾ lim_exec_val (e, σ) : R⌝.
  Proof.
    iIntros (Hf Hv) "Hcpl".
    erewrite exec_is_final; [|done].
    rewrite rwp_coupl_unfold.
    iDestruct "Hcpl" as (R') "[(% & %Hcpl & HR) | [[%Hcpl HR] | (% & %Hcpl & HR)]]".
    - iEval (rewrite -(dret_id_left (λ a, dret b) a)).
      rewrite lim_exec_val_prim_step prim_step_or_val_no_val; [|done].
      iApply (step_fupdN_mono _ _ _
                (⌜∀ ρ', R' ρ' a → dret b ≾ lim_exec_val ρ' : R⌝)%I).
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
    - rewrite is_final_dzero in Hcpl; [|eauto with markov].
      apply Rcoupl_mass_eq in Hcpl.
      rewrite dret_mass dzero_mass in Hcpl.
      lra.
    - rewrite is_final_dzero in Hcpl; [|eauto with markov].
      apply Rcoupl_mass_eq in Hcpl.
      rewrite prim_step_mass ?dzero_mass in Hcpl; [|done].
      lra.
  Qed.

  Theorem wp_refRcoupl_step_fupdN (e : expr) (σ : state) (a : mstate δ) (n : nat) (φ : val → mstate_ret δ → Prop)  :
    state_interp σ ∗ specA a ∗ WP e {{ v, ∃ a' b, specF a' ∗ ⌜to_final a' = Some b⌝ ∗ ⌜φ v b⌝ }} ⊢
    |={⊤,∅}=> |={∅}▷=>^n ⌜lim_exec_val (e, σ) ≿ exec n a : φ⌝.
  Proof.
    iIntros "(Hσ & Ha & Hrwp)".
    iRevert (σ a n) "Hσ Ha".
    iApply (rwp_ind' (λ e, _) with "[] Hrwp"); clear.
    iIntros "!#" (e) "Hrwp"; iIntros (σ a n) "Hσ Ha".
    rewrite /rwp_pre.
    iSpecialize ("Hrwp" with "[$]").
    case_match eqn:Hv.
    - iMod "Hrwp" as "(Hσ & Hauth & [% [% (Hfrag & % & %)]])".
      iDestruct (spec_auth_agree with "Hauth Hfrag") as %<-.
      erewrite exec_is_final; [|done].
      erewrite lim_exec_val_val; [|done].
      iApply fupd_mask_intro; [set_solver|]; iIntros "_".
      iApply step_fupdN_intro; [done|].
      iModIntro.
      iPureIntro.
      by eapply Rcoupl_refRcoupl, Rcoupl_dret.
    - iMod "Hrwp" as "Hcpl".
      iDestruct (rwp_coupl_strong_mono _ _ _ _
                    ((λ '(e2, σ2) a2, ∀ n, |={∅}=> |={∅}▷=>^n
                        ⌜exec n a2 ≾ lim_exec_val (e2, σ2) : flip φ⌝))%I
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
        iDestruct "Hcpl" as (R) "[(%Hred & %Hcpl & HR) | [[%Hcpl HR] | (%Hred & %Hcpl & HR)]]".
        * iEval (rewrite -(dret_id_left (exec _))).
          rewrite lim_exec_val_prim_step prim_step_or_val_no_val; [|done].
          iApply (step_fupdN_mono _ _ _
                    (⌜∀ ρ', R ρ' a → exec _ a ≾ lim_exec_val ρ' : flip φ⌝)%I).
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
        * rewrite exec_Sn_not_final; [|eauto with markov].
          iEval (rewrite -(dret_id_left (lim_exec_val))).
          iApply (step_fupdN_mono _ _ _
                    (⌜∀ a, R (e, σ) a → exec n a ≾ lim_exec_val (e, σ) : flip φ⌝)%I).
          { iIntros (HR). iPureIntro.
            eapply refRcoupl_dbind; [|by apply Rcoupl_refRcoupl', Rcoupl_pos_R].
            intros a1 [? ?] (? & [= -> ->]%dret_pos & Hs). eauto. }
          iIntros "!>" (a'' HR).
          rewrite step_fupdN_Sn.
          iMod ("HR" with "[//]") as "HR".
          do 2 iModIntro. iMod "HR".
          iApply ("IH" with "[//] HR").
        * rewrite exec_Sn_not_final; [|eauto with markov].
          rewrite lim_exec_val_prim_step prim_step_or_val_no_val; [|done].
          iApply (step_fupdN_mono _ _ _
                    (⌜∀ ρ' a', R ρ' a' → exec n a' ≾ lim_exec_val ρ' : flip φ⌝)%I).
          { iIntros (HR). iPureIntro.
            eapply refRcoupl_dbind; [|by apply Rcoupl_refRcoupl'].
            intros ???. by apply HR. }
          iModIntro.
          iIntros ([e' σ'] a0 HR).
          rewrite step_fupdN_Sn.
          iMod ("HR" with "[//]") as "HR".
          do 2 iModIntro.
          by iMod "HR".
  Qed.

End adequacy.

Theorem wp_refRcoupl `{!tprGpreS δ Σ} e σ a n φ :
  (∀ `{!tprG δ Σ},
    ⊢ specF a -∗ WP e {{ v, ∃ a' b, specF a' ∗ ⌜to_final a' = Some b⌝ ∗ ⌜φ v b⌝ }}) →
  lim_exec_val (e, σ) ≿ exec n a : φ.
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

Corollary wp_refRcoupl_mass Σ `{!tprGpreS δ Σ} e σ a :
  (∀ `{!tprG δ Σ}, ⊢ specF a -∗ WP e {{ v, ∃ a', specF a' ∗ ⌜is_final a'⌝ }}) →
  SeriesC (lim_exec a) <= SeriesC (lim_exec_val (e, σ)).
Proof.
  intros Hrwp.
  apply lim_exec_leq_mass.
  intros.
  eapply (refRcoupl_mass_eq _ _ (λ _ _, True)).
  eapply wp_refRcoupl.
  iIntros (?) "Hfrag".
  iApply rwp_mono; [|iApply (Hrwp with "Hfrag")].
  iIntros (?) "(% & ? & [% %])". eauto.
Qed.

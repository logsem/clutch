From iris.proofmode Require Import base proofmode.
From Coquelicot Require Export Lim_seq Rbar.
From clutch.common Require Export language.
From clutch.ub_logic Require Import ub_total_weakestpre adequacy primitive_laws.
From clutch.prob Require Import distribution union_bounds.

Import uPred.

Section adequacy.
  Context `{!ub_clutchGS Σ}.

  Theorem twp_step_fupd (e : expr) (σ : state) (ε : nonnegreal) φ  :
    state_interp σ ∗ err_interp (ε) ∗ WP e [{ v, ⌜φ v⌝ }] ⊢
    |={⊤,∅}=> ⌜(1 - ε <= SeriesC (lim_exec (e, σ)))%R⌝.
  Proof.
    iIntros "(Hstate & Herr & Htwp)".
    iRevert (σ ε) "Hstate Herr".
    pose proof (ub_twp_ind' ⊤ ()  (λ e _, ∀ (a : state) (a0 : nonnegreal),
                                  state_interp a -∗ err_interp a0 ={⊤,∅}=∗ ⌜1 - a0 <= SeriesC (lim_exec (e, a))⌝)%I) as H. iApply H.
    2: { destruct twp_default. done. }
    clear H e.
    iModIntro.
    iIntros (e Φ) "H".
    iIntros (σ ε) "Hs Hec".
    rewrite /ub_twp_pre.
    case_match.
    - iApply fupd_mask_intro; first done. iIntros "_".
      admit.
    - iSpecialize ("H" $! σ ε with "[$]").
      iMod "H".
      iRevert (H).
      iApply (exec_ub_strong_ind (λ ε e σ, ⌜language.to_val e = None⌝ ={∅}=∗ ⌜1 - ε <= SeriesC (lim_exec (e, σ))⌝)%I with "[][$H]").
      iModIntro. clear e σ ε. iIntros (e σ ε) "H %Hval".
      iDestruct "H" as "[H|[H|[H|H]]]".
      + iDestruct "H" as "(%R & %ε1 & %ε2 & %Hred & %Hineq & %Hub & H)".
        rewrite lim_exec_step step_or_final_no_final.
        2: { rewrite /is_final. rewrite -eq_None_not_Some. simpl. by eapply reducible_not_val. }
        rewrite dbind_mass.
        iAssert (∀ ρ2 : language.expr prob_lang * language.state prob_lang,
          ⌜R ρ2⌝ ={∅}=∗
          let
          '(e2, σ2) := ρ2 in
          |={∅}=> ⌜1 - ε2 <= SeriesC (lim_exec (e2, σ2))⌝)%I with "[H]" as "H".
        { iIntros (ρ2) "%Hρ2". iMod ("H" $! ρ2 Hρ2) as "H".
          destruct ρ2. iMod "H" as "(?&?&H)".
          iMod ("H" with "[$][$]"). iModIntro. iModIntro. done.
        } 
        admit.
      + iDestruct "H" as "(%R & %ε1 & %ε2 & %Hred & %Hbound & %Hineq & %Hub & H)".
        rewrite lim_exec_step step_or_final_no_final.
        2: { rewrite /is_final. rewrite -eq_None_not_Some. simpl. by eapply reducible_not_val. }
        rewrite dbind_mass.
        iAssert (∀ ρ2 : language.expr prob_lang * language.state prob_lang,
          ⌜R ρ2⌝ ={∅}=∗
          let
          '(e2, σ2) := ρ2 in
          |={∅}=> ⌜1 - (ε2 ρ2) <= SeriesC (lim_exec (e2, σ2))⌝)%I with "[H]" as "H".
        { iIntros (ρ2) "%Hρ2". iMod ("H" $! ρ2 Hρ2) as "H".
          destruct ρ2. iMod "H" as "(?&?&H)".
          iMod ("H" with "[$][$]"). iModIntro. iModIntro. done.
        }
        admit.
      + iInduction (language.get_active σ) as [| l] "IH".
        { rewrite big_orL_nil //. }
        rewrite !big_orL_cons.
        iDestruct "H" as "[H|H]".
        2:{ by iApply "IH". }
        iDestruct "H" as "(%R & %ε1 & %ε2 & %Hineq & %Hub & H)".
        iAssert (∀ σ2 : language.state prob_lang,
                   ⌜R σ2⌝ ={∅}=∗ ⌜1 - ε2 <= SeriesC (lim_exec (e, σ2))⌝)%I with "[H]" as "H".
        { iIntros. iMod ("H" $! σ2 (H)) as "H". iDestruct "H" as "[H _]". iApply "H". done. }
        admit.
      + iInduction (language.get_active σ) as [| l] "IH".
        { rewrite big_orL_nil //. }
        rewrite !big_orL_cons.
        iDestruct "H" as "[H|H]".
        2:{ by iApply "IH". }
        iDestruct "H" as "(%R & %ε1 & %ε2  & %Hbound & %Hineq & %Hub & H)".
        iAssert (∀ σ2 : language.state prob_lang,
                   ⌜R σ2⌝ ={∅}=∗ ⌜1 - (ε2 (e, σ2)) <= SeriesC (lim_exec (e, σ2))⌝)%I with "[H]" as "H".
        { iIntros. iMod ("H" $! σ2 (H)) as "H". iDestruct "H" as "[H _]". iApply "H". done. }
        admit. 
  Admitted.
  
End adequacy.


Theorem twp_mass_lim_exec Σ `{ub_clutchGpreS Σ} (e : expr) (σ : state) (ε : nonnegreal) φ :
  (∀ `{ub_clutchGS Σ}, ⊢ € ε -∗ WP e [{ v, ⌜φ v⌝ }]) →
  (1 - ε <= SeriesC (lim_exec (e, σ)))%R.
Proof.
  intros Hwp.
  eapply (step_fupdN_soundness_no_lc _ 0 0) => Hinv.
  iIntros "_".
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh _]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht _]]".
  iMod ec_alloc as (?) "[? ?]".
  set (HclutchGS := HeapG Σ _ _ _ γH γT _).
  epose proof (twp_step_fupd e σ ε φ).
  iApply fupd_wand_r. iSplitL.
  - iApply H1. iFrame. by iApply Hwp.
  -  iIntros "%". iApply step_fupdN_intro; first done. done. 
Qed. 

Theorem twp_union_bound_lim Σ `{ub_clutchGpreS Σ} (e : expr) (σ : state) (ε : nonnegreal) φ :
  (∀ `{ub_clutchGS Σ}, ⊢ € ε -∗ WP e [{ v, ⌜φ v⌝ }]) →
  ub_lift (lim_exec (e, σ)) φ ε.
Proof.
  intros.
  eapply wp_union_bound_lim; first done.
  intros H1.
  iIntros "Hε".
  iApply ub_twp_ub_wp.
  iAssert (WP e [{ v, ⌜φ v⌝ }])%I with "[Hε]" as "H".
  2:{ destruct twp_default. destruct wp_default. iExact "H". }
  by iApply H0.
Qed.

(** limit rules *)
Theorem twp_mass_lim_exec_limit Σ `{ub_clutchGpreS Σ} (e : expr) (σ : state) (ε : nonnegreal) φ :
  (∀ `{ub_clutchGS Σ}, (∀ ε' : nonnegreal, ε' > ε -> ⊢ € ε' -∗ WP e [{ v, ⌜φ v⌝ }])) →
  (1 - ε <= SeriesC (lim_exec (e, σ)))%R.
Proof.
  intros H'.
  apply real_le_limit.
  intros ε0 H1.
  replace (1-_-_) with (1- (ε+ε0)) by lra.
  assert (0<=ε+ ε0) as Hε0.
  { trans ε; try lra. by destruct ε. }
  pose (mknonnegreal (ε+ε0) Hε0) as NNRε0.
  assert (ε+ε0 = (NNRbar_to_real (NNRbar.Finite (NNRε0)))) as Heq.
  { by simpl. }
  rewrite Heq.
  eapply twp_mass_lim_exec; first done.
  intros. iIntros "He".
  iApply H'; try iFrame.
  simpl. destruct ε; simpl in H1; simpl; lra.
Qed.

Theorem twp_union_bound_lim_limit Σ `{ub_clutchGpreS Σ} (e : expr) (σ : state) (ε : nonnegreal) φ :
  (∀ `{ub_clutchGS Σ}, (∀ ε':nonnegreal, ε'>ε -> ⊢ € ε' -∗ WP e [{ v, ⌜φ v⌝ }])) →
  ub_lift (lim_exec (e, σ)) φ ε.
Proof.
  (* This lemma can be proven with the continuity of ub_lift lemma in the pull request *)
Admitted.

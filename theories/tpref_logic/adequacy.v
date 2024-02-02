From Coq Require Export Reals Psatz.
From iris.proofmode Require Import base proofmode.
From iris.bi Require Import bi derived_laws_later.
From iris.bi.lib Require Export fixpoint.
From iris.base_logic Require Import derived.
From iris.base_logic.lib Require Import fancy_updates ghost_map.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.prob_lang Require Import lang metatheory erasure.
From clutch.tpref_logic Require Import weakestpre spec primitive_laws.
From clutch.prob Require Import couplings distribution markov.

Section refines.
  Context {Σ : gFunctors} {δ : markov}.

  Implicit Type e : expr.
  Implicit Type σ : state.
  Implicit Type ρ : cfg.
  Implicit Type a : mstate δ.
  Implicit Type b : mstate_ret δ.

  (** * A Step-indexed left-partial coupling *)
  (** A stratified plain coupling relation where steps of the model are tied to
      the step index. This is the "simulation relation" that the relational
      logic constructs.

      Everything looks like you'd expect, *except* the [except_0] modality [◇]
      in the front. This is technically needed because [fupd] does not interact
      well with [▷], i.e.,

            (▷ |={E}=> P) ⊢ |={E}=> ▷ ◇ P

      Philosophically, I guess this is the price we pay, for working "up to"
      timelessness in the logic. *)
  Definition refines_pre (refines : mstate δ * cfg -d> iProp Σ) : mstate δ * cfg -d> iProp Σ :=
    λ '(a, (e, σ)),
      (◇ (⌜is_final (e, σ)⌝ ∨
         (⌜reducible e σ⌝ ∧ ∃ R, ⌜Rcoupl (prim_step e σ) (dret a) R⌝ ∧
                                 ∀ ρ', ⌜R ρ' a⌝ → refines (a, ρ')) ∨
         (⌜reducible e σ⌝ ∧ ∃ R, ⌜Rcoupl (prim_step e σ) (step a) R⌝ ∧
                              ∀ ρ' a', ⌜R ρ' a'⌝ → ▷ refines (a', ρ')) ∨
         (∃ R, ⌜Rcoupl (dret (e, σ)) (step a) R⌝ ∧ ∀ a', ⌜R (e, σ) a'⌝ → ▷ refines (a', (e, σ))) ∨
         (∃ R αs, ⌜αs ⊆ get_active σ⌝ ∗ ⌜Rcoupl (foldlM state_step σ αs) (step a) R⌝ ∗
                  ∀ σ' a', ⌜R σ' a'⌝ → ▷ refines (a', (e, σ')))))%I.

  #[local] Instance refine_pre_ne Φ :
    NonExpansive (refines_pre Φ).
  Proof.
    rewrite /refines_pre.
    intros ? [? []] [? []] [[=] [[=] [=]]].
    by simplify_eq.
  Qed.

  #[local] Instance refines_pre_mono : BiMonoPred refines_pre.
  Proof.
    split; [|apply _].
    iIntros (Φ Ψ HNEΦ HNEΨ) "#Hw".
    iIntros ([a (e1 & σ1)]) ">[[%v %Hv] | [(% & % & % & H) | [(% & % & % & H) |
                                          [(% & % & H)| (% & % & % & % & H)]]]] !>".
    - iLeft. eauto.
    - iRight; iLeft. iFrame "%". iExists _. iFrame "%".
      iIntros (??). iApply "Hw". by iApply "H".
    - iRight; iRight; iLeft. iFrame "%". iExists _. iFrame "%".
      iIntros (???). iApply "Hw". by iApply "H".
    - iRight; iRight; iRight; iLeft. iFrame "%". iExists _. iFrame "%".
      iIntros (??). iApply "Hw". by iApply "H".
    - iRight; iRight; iRight; iRight. iFrame "%". iExists _, _. iFrame "%".
      iIntros (???). iApply "Hw". by iApply "H".
  Qed.

  Definition refines' := bi_least_fixpoint refines_pre.
  Definition refines a ρ := refines' (a, ρ).

  Lemma refines_unfold a ρ :
    refines a ρ ≡ refines_pre refines' (a, ρ).
  Proof. apply least_fixpoint_unfold. apply _. Qed.

  Lemma refines_ind (Ψ : mstate δ → cfg → iProp Σ):
    (∀ n a ρ, Proper (dist n) (Ψ a ρ)) →
    ⊢ (□ (∀ a ρ, refines_pre (λ '(a, ρ), Ψ a ρ ∧ refines a ρ) (a, ρ) -∗ Ψ a ρ) →
       ∀ a ρ , refines a ρ -∗ Ψ a ρ)%I.
  Proof.
    iIntros (HΨ). iIntros "#IH" (a [e σ]) "H".
    set (Ψ' := uncurry Ψ : prodO (mstateO δ) (prodO (exprO) (stateO)) → iProp Σ).
    assert (NonExpansive Ψ').
    { intros ? [? []] [? []] [[=] [[=] [=]]]. simplify_eq/=. by apply HΨ. }
    iApply (least_fixpoint_ind _ Ψ' with "[] H").
    iIntros "!#" ([? []]) "H". by iApply "IH".
  Qed.

  #[global] Instance refines_plain a ρ : Plain (refines a ρ).
  Proof.
    rewrite /Plain.
    iRevert (a ρ); iApply refines_ind.
    iIntros "!#" (a [e σ]).
    rewrite refines_unfold /refines_pre.
    rewrite -except_0_plainly.
    iIntros ">[[%v %Hv] | [(% & % & % & H) | [(% & % & % & H) |
                          [(% & % & H)| (% & % & % & % & H)]]]] !>".
    - eauto.
    - iRight; iLeft. iSplit; [done|].
      iExists _. iSplit; [done|].
      iIntros (? HR). by iDestruct ("H" $! _ HR) as "[H _]".
    - iRight; iRight; iLeft. iSplit; [done|].
      iExists _. iSplit; [done|].
      iIntros (?? HR). iDestruct ("H" $! _ _ HR) as "[H _]".
      by iApply later_plainly_1.
    - iRight; iRight; iRight; iLeft.
      iExists _. iSplit; [done|].
      iIntros (? HR).
      iDestruct ("H" $! _ HR) as "[H _]".
      by iApply later_plainly_1.
    - iRight; iRight; iRight; iRight.
      iExists _, _. iSplit; [done|]. iSplit; [done|].
      iIntros (?? HR).
      iApply later_plainly_1.
      by iDestruct ("H" $! _ _ HR) as "[H _]".
  Qed.

  #[global] Instance isexcept0_refines a ρ : IsExcept0 (refines a ρ).
  Proof.
    rewrite /IsExcept0. destruct ρ as [e σ].
    iIntros "H".
    rewrite refines_unfold.
    by iMod "H".
  Qed.

  Lemma refines_soundness_laterN n a ρ :
    refines a ρ ⊢ ◇ ▷^(S n) ⌜exec n a ≾ lim_exec ρ : λ _ _, True⌝.
  Proof.
    iIntros "H". iRevert (n); iRevert (a ρ) "H".
    iApply refines_ind.
    iIntros "!#" (a [e σ]).
    iIntros ">[[%v %Hv] | [(% & %R & % & H) | [(% & %R & %Hcpl & H) |
                          [(%R & %Hcpl & H)| (%R & % & % & %Hcpl & H)]]]] %n !>".
    - iPureIntro. erewrite lim_exec_final; [|done]. apply refRcoupl_dret_trivial.
    - rewrite lim_exec_not_final /=; [|by eapply reducible_not_final].
      rewrite -(dret_id_left (exec n)).
      iApply (bi.laterN_mono _ (∀ ρ', ⌜R ρ' a → exec n a ≾ lim_exec ρ' : (λ _ _, True)⌝)).
      { iIntros (?). iPureIntro.
        eapply refRcoupl_dbind; [|by apply Rcoupl_refRcoupl', Rcoupl_pos_R].
        intros ?? (? & ? & ->%dret_pos); eauto. }
      iIntros (? HR).
      iDestruct ("H" $! _ HR) as "[H _]".
      by iDestruct ("H" $! n) as ">H".
    - rewrite lim_exec_not_final /=; [|by eapply reducible_not_final].
      destruct n.
      + destruct (decide (is_final a)); last first.
        { iPureIntro. rewrite exec_O_not_final //. apply refRcoupl_dzero. }
        exfalso. move: Hcpl => /Rcoupl_mass_eq.
        rewrite is_final_dzero ?dzero_mass ?prim_step_mass; eauto. lra.
      + destruct (to_final a) eqn:Ha.
        { exfalso. move: Hcpl => /Rcoupl_mass_eq.
          rewrite is_final_dzero ?dzero_mass ?prim_step_mass; eauto. lra. }
        rewrite /= Ha.
        iApply (bi.laterN_mono _ (∀ ρ' a', ⌜R ρ' a' → exec n a' ≾ lim_exec ρ' : (λ _ _, True)⌝)).
        { iIntros (?). iPureIntro.
          eapply refRcoupl_dbind; [|by apply Rcoupl_refRcoupl'].
          intros ???. eauto. }
        iIntros (?? HR).
        iDestruct ("H" $! _ _ HR) as "[HR _]". iModIntro.
        by iDestruct ("HR" $! n) as ">H".
    - rewrite -{2}(dret_id_left lim_exec).
      destruct n.
      + destruct (decide (is_final a)); last first.
        { iPureIntro. rewrite exec_O_not_final //. apply refRcoupl_dzero. }
        exfalso. move: Hcpl => /Rcoupl_mass_eq.
        rewrite is_final_dzero ?dzero_mass ?dret_mass; eauto. lra.
      + destruct (to_final a) eqn:Ha.
        { exfalso. move: Hcpl => /Rcoupl_mass_eq.
          rewrite is_final_dzero ?dzero_mass ?dret_mass; eauto. lra. }
        rewrite /= Ha.
        iApply (bi.laterN_mono _ (∀ a', ⌜R (e, σ) a' → exec n a' ≾ lim_exec (e, σ) : (λ _ _, True)⌝)).
        { iIntros (?). iPureIntro.
          eapply refRcoupl_dbind; [|by apply Rcoupl_refRcoupl', Rcoupl_pos_R].
          intros ?? (?&->%dret_pos&?). eauto. }
        iIntros (a' HR).
        iDestruct ("H" $! _ HR) as "[HR _]". iModIntro.
        by iDestruct ("HR" $! n) as ">H".
    - (* Erasure *)
      erewrite (lim_exec_eq_erasure αs); [|done].
      destruct n.
      + destruct (decide (is_final a)); last first.
        { iPureIntro. rewrite exec_O_not_final //. apply refRcoupl_dzero. }
        exfalso. move: Hcpl => /Rcoupl_mass_eq.
        rewrite is_final_dzero ?dzero_mass ?state_steps_mass; eauto. lra.
      + destruct (to_final a) eqn:Ha.
        { exfalso. move: Hcpl => /Rcoupl_mass_eq.
          rewrite is_final_dzero ?dzero_mass ?state_steps_mass; eauto. lra. }
        rewrite exec_Sn_not_final; [|eauto].
        iApply (bi.laterN_mono _ (∀ σ' a', ⌜R σ' a' → exec n a' ≾ lim_exec (e, σ') : (λ _ _, True)⌝)).
        { iIntros (?). iPureIntro.
          eapply refRcoupl_dbind; [|by apply Rcoupl_refRcoupl'].
          intros ???. eauto. }
        iIntros (σ' a' HR).
        iDestruct ("H" $! _ _ HR) as "[HR _]". iModIntro.
        by iDestruct ("HR" $! n) as ">H".
  Qed.

  (** [refines] is sound ... *)
  Lemma refines_soundness n a ρ :
    (⊢ refines a ρ) → exec n a ≾ lim_exec ρ : λ _ _, True.
  Proof.
    rewrite refines_soundness_laterN.
    rewrite bi.except_0_into_later.
    eapply (uPred.soundness _ (S (S n))).
  Qed.

End refines.

(** ... and our relational logic implies [refines].  *)
Lemma rwp_refines `{!tprGpreS δ Σ} e σ a :
  (∀ `{!tprG δ Σ}, ⊢ specF a -∗ WP e {{ _, True }}) →
  (⊢@{iProp Σ} refines a (e, σ)).
Proof.
  intros Hwp.
  (* Here we are breaking the [fupd] abstraction *)
  iMod (fupd_soundness_no_lc_unfold 0) as (??) "(_ & Hω & #Hfupd)".
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh _]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht _]]".
  iMod (spec_auth_alloc a) as (HspecG) "[Ha Hfrag]".
  iCombine "Hh Ht" as "Hσ".
  set (HtprG := TprG _ Σ _ _ _ γH γT HspecG).
  iDestruct (Hwp HtprG with "Hfrag") as "Hwp"; clear Hwp.
  iRevert (σ a) "Hσ Ha Hω".
  iApply (rwp_ind' (λ e, _) with "[] Hwp"); clear e.
  iIntros "!#" (e); iIntros "H"; iIntros (σ a) "Hσ Ha Hω".
  iSpecialize ("H" with "[$Hσ $Ha]").
  case_match eqn:Hv; [|clear Hv].
  { rewrite refines_unfold. iLeft. eauto. }
  iDestruct ("Hfupd" with "H Hω") as ">>[Hω H]".
  iDestruct (rwp_coupl_strong_mono _ _ _ _
               ((λ '(e2, σ2) a2, |={∅, ⊤}=> ω ⊤ -∗ refines a2 (e2, σ2)))%I with "[] H") as "H".
  { iIntros ([e' σ'] a') "[% H]".
    iMod "H" as "(Hσ & Ha & H)".
    iModIntro. iApply ("H" with "Hσ Ha"). }
  iRevert (e σ a) "H Hω".
  iApply rwp_coupl_strong_ind.
  iIntros "!#" (e σ a) "H Hω".
  rewrite refines_unfold.
  iDestruct "H" as "[(%R & % & % & H) | [(%R & %H & H) |
                    [(%R & % & % & H) | (% & % & %Hαs & %H & H)]]]".
  - iRight; iLeft. iFrame "%".
    iExists _. iFrame "%".
    iIntros ([? ?] HR).
    iDestruct ("H" $! _ HR) as "H".
    iDestruct ("Hfupd" with "H Hω") as ">>[Hω H]".
    iDestruct ("Hfupd" with "H Hω") as ">>[Hω H]".
    iModIntro. by iApply ("H" with "Hω").
  - iRight; iRight; iRight; iLeft.
    iExists _. iFrame "%".
    iIntros (? HR).
    iSpecialize ("H" $! _ HR).
    iDestruct ("Hfupd" with "H Hω") as ">>[Hω H]".
    do 2 iModIntro.
    iDestruct ("Hfupd" with "H Hω") as ">>[Hω [H _]]".
    by iApply "H".
  - iRight; iRight; iLeft. iFrame "%".
    iExists _. iFrame "%".
    iIntros ([? ?] ? HR).
    iDestruct ("H" $! _ _ HR) as "H".
    iDestruct ("Hfupd" with "H Hω") as ">>[Hω H]".
    do 2 iModIntro.
    iDestruct ("Hfupd" with "H Hω") as ">>[Hω H]".
    iDestruct ("Hfupd" with "H Hω") as ">>[Hω H]".
    by iApply "H".
  - iRight; iRight; iRight; iRight.
    iExists _, _. iFrame "%".
    iIntros (?? HR).
    iDestruct ("H" $! _ _ HR) as "H".
    iDestruct ("Hfupd" with "H Hω") as ">>[Hω H]".
    do 2 iModIntro.
    iDestruct ("Hfupd" with "H Hω") as ">>[Hω [H _]]".
    by iApply "H".
Qed.

(** * Soundness  *)
Lemma rwp_soundness `{!tprGpreS δ Σ} e σ a n :
  (∀ `{!tprG δ Σ}, ⊢ specF a -∗ WP e {{ _, True }}) →
  exec n a ≾ lim_exec (e, σ) : (λ _ _, True).
Proof. intros. by eapply refines_soundness, rwp_refines. Qed.

Lemma rwp_soundness_mass Σ `{!tprGpreS δ Σ} e σ a :
  (∀ `{!tprG δ Σ}, ⊢ specF a -∗ WP e {{ _, True }}) →
  (SeriesC (lim_exec a) <= SeriesC (lim_exec (e, σ)))%R.
Proof.
  intros. apply lim_exec_leq_mass => n.
  eapply (refRcoupl_mass_eq _ _ (λ _ _, True)).
  by apply rwp_soundness.
Qed.

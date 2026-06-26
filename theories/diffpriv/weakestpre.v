From Stdlib Require Export Reals Psatz.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export lib.fixpoint_mono big_op.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext NNRbar.
From clutch.common Require Export language erasable.
From clutch.base_logic Require Export spec_update.
From clutch.prob Require Export couplings_dp distribution.

Import uPred.

Local Open Scope R.

Class diffprivWpGS (Λ : language) (Σ : gFunctors) `{!spec_updateGS (lang_markov Λ) Σ} := DiffprivWpGS {
  #[global] diffprivWpGS_invGS :: invGS_gen HasNoLc Σ;

  state_interp : state Λ → iProp Σ;
  err_interp : nonnegreal → nonnegreal -> iProp Σ;
}.
Global Opaque diffprivWpGS_invGS.
Global Arguments DiffprivWpGS {Λ Σ _}.

Canonical Structure NNRO := leibnizO nonnegreal.
(* TODO: move *)
#[global] Hint Resolve cond_nonneg : core.

(** * Coupling modalities  *)
Section coupl_modalities.
  Context `{!spec_updateGS (lang_markov Λ) Σ, !diffprivWpGS Λ Σ}.

  (** ** [spec_coupl]  *)

  (** The [spec_coupl] modality allows us to (optionally) prepend spec execution steps and erasable
      distributions, e.g. [state_step]s on both sides. *)
  Definition spec_coupl_pre E Z (Φ : state Λ * cfg Λ * nonnegreal * nonnegreal → iProp Σ) :
    state Λ * cfg Λ * nonnegreal * nonnegreal → iProp Σ :=
    (λ (x : state Λ * cfg Λ * nonnegreal * nonnegreal),
      let '(σ1, (e1', σ1'), ε, δ) := x in
      ⌜1 <= δ⌝ ∨
      (Z σ1 e1' σ1' ε δ) ∨
      (∃ (S : state Λ → cfg Λ → Prop) (μ1 : distr (state Λ)) (μ1' : distr (cfg Λ))
         (ε1 : nonnegreal) (δ1 : nonnegreal)
         (ε2 : nonnegreal) (δ2 : nonnegreal),
         ⌜DPcoupl μ1 μ1' S ε1 δ1⌝ ∗
         ⌜(ε1 + ε2) <= ε⌝ ∗ ⌜(δ1 + δ2) <= δ⌝ ∗
         ⌜erasable μ1 σ1⌝ ∗ ⌜ rewritable (e1', σ1') μ1' ⌝ ∗
         ∀ σ2 e2' σ2', ⌜S σ2 (e2', σ2')⌝ ={E}=∗ Φ (σ2, (e2', σ2'), ε2, δ2)) ∨
        (* Approxis *)
      (∃ (S : state Λ → cfg Λ → Prop) (n : nat) (μ1 : distr (state Λ)) (μ1' : distr (state Λ))
         (δ1 : nonnegreal) (X2 : cfg Λ → nonnegreal) (r : R),
         ⌜ARcoupl μ1 (σ2' ← μ1'; pexec n (e1', σ2')) S δ1⌝ ∗
         ⌜∀ ρ, X2 ρ <= r⌝ ∗
         ⌜δ1 + Expval (σ2' ← μ1'; pexec n (e1', σ2')) X2 <= δ⌝ ∗
         ⌜erasable μ1 σ1⌝ ∗ ⌜erasable μ1' σ1'⌝ ∗
         ∀ σ2 e2' σ2', ⌜S σ2 (e2', σ2')⌝ ={E}=∗ Φ (σ2, (e2', σ2'), ε, X2 (e2', σ2'))))%I.

  #[local] Instance spec_coupl_pre_ne Z E Φ :
    NonExpansive (spec_coupl_pre E Z Φ).
  Proof.
    rewrite /spec_coupl_pre.
    intros ? (((?&?&?)&?)&?) (((?&?&?)&?)&?) ([[[=] [[=] [=]]] [=]] & [=]).
    by simplify_eq/=.
  Qed.

  #[local] Instance spec_coupl_pre_mono Z E : BiMonoPred (spec_coupl_pre Z E).
  Proof.
    split; [|apply _].
    iIntros (Φ Ψ HNEΦ HNEΨ) "#Hwand".
    iIntros ((((σ1 & e1' & σ1')& ε) & δ))
      "[% | [? | [(% & % & % & % & % & % & % & % & % & % & % & % & H)
          | (% & % & % & % & % & % & % & % & % & % & % & % & H)]]]".
    - iLeft. done.
    - iRight ; iLeft. done.
    - do 2 iRight ; iLeft.
      repeat iExists _.
      repeat (iSplit; [done|]).
      iIntros (????). iApply "Hwand". by iApply "H".
    - do 2 iRight ; iRight.
      repeat iExists _.
      repeat (iSplit; [done|]).
      iIntros (????). iApply "Hwand". by iApply "H".
  Qed.

  Implicit Type ε δ: nonnegreal.

  Definition spec_coupl' E Z := bi_least_fixpoint (spec_coupl_pre E Z).
  Definition spec_coupl E σ e' σ' ε δ Z := spec_coupl' E Z (σ, (e', σ'), ε, δ).

  Lemma spec_coupl_unfold E σ1 e1' σ1' ε δ Z :
    spec_coupl E σ1 e1' σ1' ε δ Z ≡
      (⌜1 <= δ⌝ ∨
         (Z σ1 e1' σ1' ε δ) ∨
      (∃ (S : state Λ → cfg Λ → Prop) (μ1 : distr (state Λ)) (μ1' : distr (cfg Λ))
         ε1 δ1 ε2 δ2,
         ⌜DPcoupl μ1 μ1' S ε1 δ1⌝ ∗
         ⌜ε1 + ε2 <= ε⌝ ∗ ⌜(δ1 + δ2) <= δ⌝ ∗
         ⌜erasable μ1 σ1⌝ ∗ ⌜rewritable (e1', σ1') μ1' ⌝ ∗
         ∀ σ2 e2' σ2', ⌜S σ2 (e2', σ2')⌝ ={E}=∗ spec_coupl E σ2 e2' σ2' ε2 δ2 Z) ∨
      (∃ (S : state Λ → cfg Λ → Prop) (n : nat) (μ1 : distr (state Λ)) (μ1' : distr (state Λ))
         (δ1 : nonnegreal) (X2 : cfg Λ → nonnegreal) (r : R),
         ⌜ARcoupl μ1 (σ2' ← μ1'; pexec n (e1', σ2')) S δ1⌝ ∗
         ⌜∀ ρ, X2 ρ <= r⌝ ∗
         ⌜δ1 + Expval (σ2' ← μ1'; pexec n (e1', σ2')) X2 <= δ⌝ ∗
         ⌜erasable μ1 σ1⌝ ∗ ⌜erasable μ1' σ1'⌝ ∗
         ∀ σ2 e2' σ2', ⌜S σ2 (e2', σ2')⌝ ={E}=∗ spec_coupl E σ2 e2' σ2' ε (X2 (e2', σ2')) Z))%I.
  Proof. rewrite /spec_coupl /spec_coupl' least_fixpoint_unfold //. Qed.

  Lemma spec_coupl_ret_err_ge_1 E σ1 e1' σ1' Z (ε δ : nonnegreal) :
    1 <= δ → ⊢ spec_coupl E σ1 e1' σ1' ε δ Z.
  Proof. iIntros. rewrite spec_coupl_unfold. by iLeft. Qed.

  Lemma spec_coupl_ret E σ1 e1' σ1' Z ε δ:
    Z σ1 e1' σ1' ε δ -∗ spec_coupl E σ1 e1' σ1' ε δ Z.
  Proof. iIntros. rewrite spec_coupl_unfold. by (iRight ; iLeft). Qed.

  Lemma spec_coupl_rec σ1 e1' σ1' E ε δ Z :
    (∃ (S : state Λ → cfg Λ → Prop) (μ1 : distr (state Λ)) (μ1' : distr (cfg Λ))
       ε1 δ1 ε2 δ2,
       ⌜DPcoupl μ1 μ1' S ε1 δ1⌝ ∗
       ⌜ε1 + ε2 <= ε⌝ ∗ ⌜(δ1 + δ2) <= δ⌝ ∗
       ⌜erasable μ1 σ1⌝ ∗ ⌜rewritable (e1', σ1') μ1'⌝ ∗
       ∀ σ2 e2' σ2', ⌜S σ2 (e2', σ2')⌝ ={E}=∗ spec_coupl E σ2 e2' σ2' ε2 δ2 Z)%I
    ⊢ spec_coupl E σ1 e1' σ1' ε δ Z.
  Proof. iIntros "H". rewrite spec_coupl_unfold. do 2 iRight. iLeft. done. Qed.

  Lemma spec_coupl_rec_app σ1 e1' σ1' E (ε δ : nonnegreal) Z :
    (∃ (S : state Λ → cfg Λ → Prop) (n : nat) (μ1 : distr (state Λ)) (μ1' : distr (state Λ))
       (δ1 : nonnegreal) (X2 : cfg Λ → nonnegreal) (r : R),
       ⌜ARcoupl μ1 (σ2' ← μ1'; pexec n (e1', σ2')) S δ1⌝ ∗
       ⌜∀ ρ, X2 ρ <= r⌝ ∗
       ⌜δ1 + Expval (σ2 ← μ1'; pexec n (e1', σ2)) X2 <= δ⌝ ∗
       ⌜erasable μ1 σ1⌝ ∗ ⌜erasable μ1' σ1'⌝ ∗
       ∀ σ2 e2' σ2', ⌜S σ2 (e2', σ2')⌝ ={E}=∗ spec_coupl E σ2 e2' σ2' ε (X2 (e2', σ2')) Z)%I
    ⊢ spec_coupl E σ1 e1' σ1' ε δ Z.
  Proof. iIntros "H". rewrite spec_coupl_unfold. do 2 iRight; iRight. done. Qed.

  Lemma spec_coupl_ind E (Ψ Z : state Λ → expr Λ → state Λ → nonnegreal → nonnegreal -> iProp Σ) :
    ⊢ (□ (∀ σ e' σ' ε δ,
             spec_coupl_pre E Z (λ '(σ, (e', σ'), ε', δ'),
                 Ψ σ e' σ' ε' δ' ∧ spec_coupl E σ e' σ' ε' δ' Z)%I (σ, (e', σ'), ε, δ) -∗ Ψ σ e' σ' ε δ) →
       ∀ σ e' σ' ε δ, spec_coupl E σ e' σ' ε δ Z -∗ Ψ σ e' σ' ε δ)%I.
  Proof.
    iIntros "#IH" (σ e' σ' ε δ) "H".
    set (Ψ' := (λ '(σ, (e', σ'), ε, δ), Ψ σ e' σ' ε δ) :
           (prodO (prodO (prodO (stateO Λ) (prodO (exprO Λ) (stateO Λ))) NNRO) NNRO) → iProp Σ).
    assert (NonExpansive Ψ').
    { intros n [[[σ1 [e1' σ1']] ε1] δ1] [[[σ2 [e2' σ2']] ε2] δ2].
      intros (([[=] ([=] & [=])] & [=]) & [=]).
      by simplify_eq/=. }
    iApply (least_fixpoint_ind _ Ψ' with "[] H").
    iIntros "!#" ([[[? [??]] ?] ?]) "H". by iApply "IH".
  Qed.

  Lemma fupd_spec_coupl E σ1 e1' σ1' Z ε δ :
    (|={E}=> spec_coupl E σ1 e1' σ1' ε δ Z) ⊢ spec_coupl E σ1 e1' σ1' ε δ Z.
  Proof.
    iIntros "H".
    iApply spec_coupl_rec.
    iExists _, (dret σ1), (dret (e1', σ1')), 0%NNR, 0%NNR , ε, δ.
    iSplit; [iPureIntro|].
    { by apply DPcoupl_pos_R, (DPcoupl_dret _ _ (λ _ _, True)). }
    iSplit.
    { iPureIntro. destruct ε => /= ; lra. }
    iSplit.
    { iPureIntro. destruct δ => /= ; lra. }
    iSplit; [iPureIntro; apply dret_erasable|].
    iSplit; [iPureIntro; apply dret_rewritable|].
    by iIntros (??? (_ & ->%dret_pos & [=-> ->]%dret_pos)).
  Qed.

  Lemma spec_coupl_mono E1 E2 σ1 e1' σ1' Z1 Z2 ε δ :
    E1 ⊆ E2 →
    (∀ σ2 e2' σ2' ε' δ', Z1 σ2 e2' σ2' ε' δ' -∗ Z2 σ2 e2' σ2' ε' δ') -∗
    spec_coupl E1 σ1 e1' σ1' ε δ Z1 -∗ spec_coupl E2 σ1 e1' σ1' ε δ Z2.
  Proof.
    iIntros (HE) "HZ Hs".
    iRevert "HZ".
    iRevert (σ1 e1' σ1' ε δ) "Hs".
    iApply spec_coupl_ind.
    iIntros "!#" (σ e' σ' ε δ)
      "[% | [? | [(% & % & % & % & % & % & % & % & % & % & % & % & H)
            | (% & % & % & % & % & % & % & % & % & % & % & % & H)]]] Hw".
    - iApply spec_coupl_ret_err_ge_1. done.
    - iApply spec_coupl_ret. by iApply "Hw".
    - iApply spec_coupl_rec.
      repeat iExists _.
      iSplit; [done|].
      iSplit; [iPureIntro; by etrans|].
      do 3 (iSplit; [done|]).
      iIntros (????).
      iApply fupd_mask_mono; [done|].
      iMod ("H" with "[//]") as "[IH _]".
      by iApply "IH".
    - iApply spec_coupl_rec_app.
      repeat iExists _.
      iSplit; [done|].
      iSplit; [iPureIntro; by etrans|].
      do 3 (iSplit; [done|]).
      iIntros (????).
      iApply fupd_mask_mono; [done|].
      iMod ("H" with "[//]") as "[IH _]".
      by iApply "IH".
  Qed.

  Lemma spec_coupl_mono_err_1 ε1 ε2 δ E σ1 e1' σ1' Z :
    ε1 <= ε2 → spec_coupl E σ1 e1' σ1' ε1 δ Z -∗ spec_coupl E σ1 e1' σ1' ε2 δ Z.
  Proof.
    iIntros (Heps) "Hs".
    iApply spec_coupl_rec.
    set (ε' := nnreal_minus ε2 ε1 Heps).
    iExists _, (dret σ1), (dret (e1', σ1')), ε', 0%NNR , ε1 , δ.
    iSplit; [iPureIntro|].
    { eapply DPcoupl_pos_R,
        (DPcoupl_mon_grading _ _ _ ε' _ 0%NNR),
        (DPcoupl_dret _ _ (λ _ _, True)) => /=; [lra| done| lra| done |lra]. }
    iSplit; [iPureIntro|].
    { rewrite /ε' => /=. lra. }
    iSplit; [iPureIntro|].
    { simpl. lra. }
    iSplit; [iPureIntro; apply dret_erasable|].
    iSplit; [iPureIntro; apply dret_rewritable|].
    by iIntros (??? (_ & ->%dret_pos & [=-> ->]%dret_pos)).
  Qed.


  Lemma spec_coupl_mono_err_2 ε δ1 δ2 E σ1 e1' σ1' Z :
    δ1 <= δ2 → spec_coupl E σ1 e1' σ1' ε δ1 Z -∗ spec_coupl E σ1 e1' σ1' ε δ2 Z.
  Proof.
    iIntros (Heps) "Hs".
    iApply spec_coupl_rec.
    set (δ' := nnreal_minus δ2 δ1 Heps).
    iExists _, (dret σ1), (dret (e1', σ1')), 0%NNR, δ' , ε , δ1.
    iSplit; [iPureIntro|].
    { eapply DPcoupl_pos_R,
        (DPcoupl_mon_grading _ _ _ 0%NNR _ δ'),
        (DPcoupl_dret _ _ (λ _ _, True)) => /=; [ done | done | done | lra | done ]. }
    iSplit; [iPureIntro|].
    { simpl. lra. }
    iSplit; [iPureIntro|].
    { rewrite /δ' => /=. lra. }
    iSplit; [iPureIntro; apply dret_erasable|].
    iSplit; [iPureIntro; apply dret_rewritable|].
    by iIntros (??? (_ & ->%dret_pos & [=-> ->]%dret_pos)).
  Qed.

  Lemma spec_coupl_bind E1 E2 σ1 e1' σ1' Z1 Z2 ε δ :
    E1 ⊆ E2 →
    (∀ σ2 e2' σ2' ε' δ', Z1 σ2 e2' σ2' ε' δ' -∗ spec_coupl E2 σ2 e2' σ2' ε' δ' Z2) -∗
    spec_coupl E1 σ1 e1' σ1' ε δ Z1 -∗
    spec_coupl E2 σ1 e1' σ1' ε δ Z2.
  Proof.
    iIntros (HE) "HZ Hs".
    iRevert "HZ".
    iRevert (σ1 e1' σ1' ε δ) "Hs".
    iApply spec_coupl_ind.
    iIntros "!#" (σ e' σ' ε δ)
      "[% | [H | [(%R & %μ1 & %μ1' & %ε1' & %δ1' & %ε2 & %δ2 & %r & % & % & % & % & H)
            |(%R & %n & %μ1 & %μ1' & %ε1' & %X2 & %r & % & % & % & % & % & H) ]]] HZ".
    - iApply spec_coupl_ret_err_ge_1 => //.
    - iApply ("HZ" with "H").
    - iApply spec_coupl_rec.
      iExists R, μ1, μ1', ε1', δ1', ε2, δ2.
      iSplit; [done|].
      iSplit; [iPureIntro|].
      { by etrans. }
      iSplit; [iPureIntro|].
      { by etrans. }
      do 2 (iSplit; [done|]).
      iIntros (????).
      iMod (fupd_mask_subseteq E1) as "Hclose"; [done|].
      iMod ("H" with "[//]") as "[H _]".
      iMod "Hclose".
      by iApply "H".
    - iApply spec_coupl_rec_app.
      iExists R, n, μ1, μ1', ε1', X2, r.
      iSplit; [done|].
      iSplit; [iPureIntro|].
      { by etrans. }
      do 3 (iSplit; [done|]).
      iIntros (????).
      iMod (fupd_mask_subseteq E1) as "Hclose"; [done|].
      iMod ("H" with "[//]") as "[H _]".
      iMod "Hclose".
      by iApply "H".
  Qed.

  Lemma spec_coupl_erasables R μ1 μ1' ε1 ε2 ε δ1 δ2 δ E σ1 e1' σ1' Z :
    ε = (ε1 + ε2)%NNR →
    δ = (δ1 + δ2)%NNR →
    DPcoupl μ1 μ1' R ε1 δ1 →
    erasable μ1 σ1 →
    rewritable (e1', σ1') μ1' →
    (∀ σ2 ρ2', ⌜R σ2 ρ2'⌝ ={E}=∗ spec_coupl E σ2 ρ2'.1 ρ2'.2 ε2 δ2 Z)
    ⊢ spec_coupl E σ1 e1' σ1' ε δ Z.
  Proof.
    iIntros (-> -> ???) "H".
    iApply spec_coupl_rec.
    iExists R, μ1, μ1', ε1, δ1, ε2, δ2.
    iSplit; [iPureIntro|].
    { rewrite -(dret_id_right μ1).
      rewrite -(dret_id_right μ1').
      eapply (DPcoupl_dbind' ε1 0 _ δ1 0 _) ; [lra|done|lra|lra | |done].
      intros ???.
      eapply DPcoupl_dret; [lra | lra | done]. }
    iSplit; [by iPureIntro|].
    do 3 (iSplit; [done|]).
    iIntros (????).
    by iApply ("H" $! σ2 (e2', σ2')).
  Qed.

  Lemma spec_coupl_erasables_exp (X2 : _ → nonnegreal) (r : R) δ1 ε δ R μ1 μ1' E σ1 e1' σ1' Z :
    ARcoupl μ1 μ1' R δ1 →
    erasable μ1 σ1 →
    erasable μ1' σ1' →
    (∀ ρ, X2 ρ <= r) →
    δ1 + Expval μ1' X2 <= δ →
    (∀ σ2 σ2', ⌜R σ2 σ2'⌝ ={E}=∗ spec_coupl E σ2 e1' σ2' ε (X2 σ2') Z)
    ⊢ spec_coupl E σ1 e1' σ1' ε δ Z.
  Proof.
    iIntros (???? Hδ) "H".
    iApply spec_coupl_rec_app.
    set X2' := (λ (ρ : cfg Λ), X2 ρ.2).
    iExists (λ σ2 '(e2', σ2'), R σ2 σ2' ∧ e2' = e1'), 0%nat, μ1, μ1', δ1, X2', r.
    iSplit; [iPureIntro|].
    { rewrite -(dret_id_right μ1).
      eapply (ARcoupl_dbind' δ1 0%NNR); [done|done|simpl; lra|..|done].
      intros ???.
      rewrite pexec_O.
      by apply ARcoupl_dret. }
    iSplit; [iPureIntro|].
    { intros []. rewrite /X2' //. }
    iSplit; [iPureIntro|].
    { rewrite /X2'. setoid_rewrite pexec_O. rewrite Expval_dmap //=.
      by eapply ex_expval_bounded=>/=. }
    do 2 (iSplit; [done|]).
    iIntros (??? [? ->]). rewrite /X2' /=.
    by iApply "H".
  Qed.

  Lemma DPcoupl_rewritable_of_erasable (e1' : expr Λ) (μ1 μ1' : distr $ state Λ) R (ε1 δ1 : nonnegreal) (H : DPcoupl μ1 μ1' R ε1 δ1) :
    DPcoupl μ1 (rewritable_of_erasable μ1' e1') (fun x y => R x y.2 ∧ y.1 = e1') ε1 δ1.
  Proof.
    rewrite -(dret_id_right μ1).
    eapply (DPcoupl_dbind' ε1 0 ε1 δ1 0 δ1) => //. 1,2: lra.
    intros. apply DPcoupl_dret ; try lra.
    done.
  Qed.

  Lemma spec_coupl_erasables_weak R μ1 μ1' ε1 ε2 ε δ1 δ2 δ E σ1 e1' σ1' Z :
    ε = (ε1 + ε2)%NNR →
    δ = (δ1 + δ2)%NNR →
    DPcoupl μ1 μ1' R ε1 δ1 →
    erasable μ1 σ1 →
    erasable μ1' σ1' →
    (∀ σ2 σ2', ⌜R σ2 σ2'⌝ ={E}=∗ spec_coupl E σ2 e1' σ2' ε2 δ2 Z)
    ⊢ spec_coupl E σ1 e1' σ1' ε δ Z.
  Proof.
    iIntros (-> -> ???) "H".
    iApply spec_coupl_erasables => //. 2: by apply rewritable_erasable.
    1: apply DPcoupl_rewritable_of_erasable => //.
    simpl.
    iIntros "%%[% %h]".
    simplify_eq.
    iApply "H". done.
  Qed.

  Lemma spec_coupl_erasable_steps n R μ1 ε1 ε2 ε δ1 δ2 δ E σ1 e1' σ1' Z :
    ε = (ε1 + ε2)%NNR →
    δ = (δ1 + δ2)%NNR →
    DPcoupl μ1 (pexec n (e1', σ1')) R ε1 δ1 →
    erasable μ1 σ1 →
    (∀ σ2 e2' σ2', ⌜R σ2 (e2', σ2')⌝ ={E}=∗ spec_coupl E σ2 e2' σ2' ε2 δ2 Z)
      ⊢ spec_coupl E σ1 e1' σ1' ε δ Z.
  Proof.
    iIntros (-> -> ??) "H".
    iApply spec_coupl_rec.
    iExists R, μ1, (pexec n (e1', σ1')), ε1, δ1, ε2, δ2.
    do 4 (iSplit; [done|]).
    iSplit; [iPureIntro; apply rewritable_pexec|].
    done.
  Qed.

  Lemma spec_coupl_steps n ε2 ε1 ε δ2 δ1 δ R E σ1 e1' σ1' Z :
    ε = (ε1 + ε2)%NNR →
    δ = (δ1 + δ2)%NNR →
    DPcoupl (dret σ1) (pexec n (e1', σ1')) R ε1 δ1 →
    (∀ σ2 e2' σ2', ⌜R σ2 (e2', σ2')⌝ ={E}=∗ spec_coupl E σ2 e2' σ2' ε2 δ2 Z)
      ⊢ spec_coupl E σ1 e1' σ1' ε δ Z.
  Proof.
    iIntros (-> -> ?) "H".
    iApply (spec_coupl_erasable_steps n _ _ ε1 ε2 _ δ1 δ2); [done| done | |apply dret_erasable|].
    { by apply DPcoupl_pos_R. }
    iIntros (??? (? & ->%dret_pos & ?)).
    by iApply "H".
  Qed.

  Lemma spec_coupl_steps_det n ε δ σ1 e1' σ1' e2' σ2' Z E :
    pexec n (e1', σ1') (e2', σ2') = 1 →
    spec_coupl E σ1 e2' σ2' ε δ Z ⊢
      spec_coupl E σ1 e1' σ1' ε δ Z.
  Proof.
    iIntros (Hexec%pmf_1_eq_dret) "H".
    iApply (spec_coupl_steps n ε 0%NNR _ δ 0%NNR).
    { apply nnreal_ext => /=. lra. }
    { apply nnreal_ext => /=. lra. }
    { apply DPcoupl_pos_R, DPcoupl_trivial; [solve_distr_mass|].
      rewrite Hexec. solve_distr_mass. }
    rewrite Hexec.
    iIntros (??? (_ & ->%dret_pos & [=-> ->]%dret_pos)).
    done.
  Qed.

  Lemma spec_coupl_step ε δ E σ1 e1' σ1' Z :
    reducible (e1', σ1') →
    (∀ e2' σ2', ⌜prim_step e1' σ1' (e2', σ2') > 0%R⌝ ={E}=∗ spec_coupl E σ1 e2' σ2' ε δ Z)
      ⊢ spec_coupl E σ1 e1' σ1' ε δ Z.
  Proof.
    iIntros (?) "H".
    iApply (spec_coupl_steps 1 ε 0%NNR _ δ 0%NNR).
    { apply nnreal_ext => /=. lra. }
    { apply nnreal_ext => /=. lra. }
    { rewrite pexec_1 step_or_final_no_final; [|by apply reducible_not_final].
      apply DPcoupl_pos_R, DPcoupl_trivial; [solve_distr_mass|].
      by apply prim_step_mass. }
    iIntros (??? (?&->%dret_pos&?)).
    by iApply "H".
  Qed.

  (** * [prog_coupl] *)

  (** The [prog_coupl] modality allows us to coupl *exactly* one program step with any number of
      spec execution steps and an erasable distribution *)
  Definition prog_coupl (e1 : expr Λ) (σ1 : state Λ) (e1' : expr Λ) (σ1' : state Λ)
      (ε δ : nonnegreal)
      (Z : expr Λ → state Λ → expr Λ → state Λ → nonnegreal → nonnegreal → iProp Σ)
      : iProp Σ :=
    ∃ (n : nat) (μ1' : distr (state Λ))
      (E2 : cfg Λ → cfg Λ → nonnegreal)
      (D2 : cfg Λ → cfg Λ → nonnegreal)
      (S : cfg Λ → cfg Λ → Prop),
      ⌜reducible (e1, σ1)⌝ ∗
      ⌜∃ r, ∀ ρ1 ρ2, (D2 ρ1 ρ2 : R) <= r⌝ ∗
      ⌜∀ h1 h2 : cfg Λ → R,
         (∀ ρ, 0 <= h1 ρ <= 1) →
         (∀ ρ, 0 <= h2 ρ <= 1) →
         (∀ ρ1 ρ2, S ρ1 ρ2 -> h1 ρ1 <= exp (E2 ρ1 ρ2) * h2 ρ2 + D2 ρ1 ρ2) →
         SeriesC (λ ρ, (prim_step e1 σ1 ρ * h1 ρ)%R) <=
           exp ε * SeriesC (λ ρ, ((σ2' ← μ1'; pexec n (e1', σ2')) ρ * h2 ρ)%R) + δ⌝ ∗
      ⌜erasable μ1' σ1'⌝ ∗
      ∀ e2 σ2 e2' σ2', ⌜S (e2, σ2) (e2', σ2')⌝ ={∅}=∗
          Z e2 σ2 e2' σ2' (E2 (e2,σ2) (e2',σ2')) (D2 (e2,σ2) (e2',σ2')).

  Lemma prog_coupl_strong_mono e1 σ1 e1' σ1' Z1 Z2 ε δ :
    □(∀ e2 σ2 e2' σ2' ε', Z2 e2 σ2 e2' σ2' ε' 1%NNR) -∗
    (∀ e2 σ2 e2' σ2' ε' δ', ⌜∃ σ, prim_step e1 σ (e2, σ2) > 0⌝ ∗ Z1 e2 σ2 e2' σ2' ε' δ' -∗ Z2 e2 σ2 e2' σ2' ε' δ') -∗
    prog_coupl e1 σ1 e1' σ1' ε δ Z1 -∗ prog_coupl e1 σ1 e1' σ1' ε δ Z2.
  Proof.
    iIntros "#H1F Hm (%n & %μ1' & %E2 & %D2 & %S &
             %Hred & [%r %HD2r] & %Hkanto & %Heras & Hcnt) /=".
    rewrite /prog_coupl.
    set (S' := λ (ρ1 ρ2 : cfg Λ), S ρ1 ρ2 ∧ ∃ σ, prim_step e1 σ ρ1 > 0).
    iExists n, μ1', E2, D2, S'.
    iSplit; [done|].
    iSplit; [iPureIntro; exists r; exact HD2r|].
    iSplit.
    { iPureIntro.
      intros h1 h2 Hh1 Hh2 Hh1h2.
      set (h x := if bool_decide (∃ σ, prim_step e1 σ x > 0)%R then h1 x else 0).
      assert (SeriesC (λ ρ, prim_step e1 σ1 ρ * h1 ρ) =
                SeriesC (λ ρ, prim_step e1 σ1 ρ * h ρ)) as ->.
      { apply SeriesC_ext. intros ρ. rewrite /h. case_bool_decide; auto.
        assert (prim_step e1 σ1 ρ = 0) as ->; [|real_solver].
        destruct (pmf_pos (prim_step e1 σ1) ρ); auto. exfalso. real_solver. }
      apply Hkanto; auto.
      - rewrite /h. real_solver.
      - intros ρ1 ρ2 HS. rewrite /h. case_bool_decide as Hacc.
        + apply Hh1h2. split; [exact HS | exact Hacc].
        + apply Rplus_le_le_0_compat.
          * apply Rmult_le_pos; [left; apply exp_pos|]. apply Hh2.
          * apply cond_nonneg. }
    iSplit; [done|].
    iIntros (e2 σ2 e2' σ2') "[%HS %Hacc]".
    iMod ("Hcnt" with "[%]") as "HZ1"; [exact HS|].
    iModIntro.
    iApply "Hm".
    iSplitR; [iPureIntro; exact Hacc|].
    iExact "HZ1".
  Qed.

  Lemma prog_coupl_mono e1 σ1 e1' σ1' Z1 Z2 ε δ:
    (∀ e2 σ2 e2' σ2' ε' δ', Z1 e2 σ2 e2' σ2' ε' δ' -∗ Z2 e2 σ2 e2' σ2' ε' δ') -∗
    prog_coupl e1 σ1 e1' σ1' ε δ Z1 -∗ prog_coupl e1 σ1 e1' σ1' ε δ Z2.
  Proof.
    iIntros "Hm (%n & %μ1' & %E2 & %D2 & %S &
             %Hred & [%r %HD2r] & %Hkanto & %Heras & Hcnt) /=".
    rewrite /prog_coupl.
    iExists n, μ1', E2, D2, S.
    iSplit; [done|].
    iSplit; [iPureIntro; exists r; exact HD2r|].
    iSplit; [done|].
    iSplit; [done|].
    iIntros (e2 σ2 e2' σ2') "HS".
    iMod ("Hcnt" with "HS") as "HZ1".
    iModIntro.
    iApply "Hm". iExact "HZ1".
  Qed.

  Lemma prog_coupl_strengthen e1 σ1 e1' σ1' Z ε δ:
    □(∀ e2 σ2 e2' σ2' ε', Z e2 σ2 e2' σ2' ε' 1%NNR) -∗
    prog_coupl e1 σ1 e1' σ1' ε δ Z -∗
    prog_coupl e1 σ1 e1' σ1' ε δ (λ e2 σ2 e2' σ2' ε' δ',
      ⌜(∃ σ, prim_step e1 σ (e2, σ2) > 0) ∨ 1 <= δ'⌝ ∧ Z e2 σ2 e2' σ2' ε' δ').
  Proof.
    iIntros "#H1F".
    iApply prog_coupl_strong_mono.
    - iModIntro.
      iIntros (?????).
      iSplit; auto.
      iPureIntro.
      right; real_solver.
    - iIntros (??????) "[% ?]".
      iSplit; [|iFrame]; auto.
  Qed.

  Lemma prog_coupl_ctx_bind K `{!LanguageCtx K} e1 σ1 e1' σ1' Z ε δ:
    to_val e1 = None →
    □(∀ e2 σ2 e2' σ2' ε', Z e2 σ2 e2' σ2' ε' 1%NNR) -∗
    prog_coupl e1 σ1 e1' σ1' ε δ (λ e2, Z (K e2)) -∗ prog_coupl (K e1) σ1 e1' σ1' ε δ Z.
  Proof.
    iIntros (Hv) "#H1F (%n & %μ1' & %E2 & %D2 & %S & [%r %] & %Hexp & % & Hcnt) /=".

    (** (classical) inverse of context [K] *)
    destruct (partial_inv_fun K) as (Kinv & HKinv).
    assert (∀ b a : expr Λ, Kinv b = Some a → K a = b) as HKinvS; [intros; by apply HKinv|].
    assert (∀ b a : expr Λ, Kinv b = None → K a ≠ b) as HKinvN; [intros; by apply HKinv|].
    assert (∀ e, Kinv (K e) = Some e) as HKinv3.
    { intro e.
      destruct (Kinv (K e)) eqn:Heq;
        eapply HKinv in Heq; by simplify_eq. }
    set (S' := λ '(e, σ) ρ2, ∃ e3, Kinv e = Some e3 ∧ S (e3, σ) ρ2).
    set (E2' := (λ '(e, σ) ρ2, from_option (λ e', E2 (e', σ) ρ2) 0%NNR (Kinv e))).
    set (D2' := λ (x : cfg Λ) (y : cfg Λ),
                   from_option (λ e', D2 (e', x.2) y) 1%NNR (Kinv x.1)).
    iExists n, μ1', E2', D2', S'.
    repeat iSplit.
    - iPureIntro; apply reducible_fill; exists r; exact H.
    - iPureIntro.
      destruct Hexp as [r0 Hr0].
      exists (Rmax 1 r0).
      intros ρ1 ρ2.
      rewrite /D2'.
      destruct (Kinv ρ1.1); simpl.
      + etransitivity; [apply Hr0 | apply Rmax_r].
      + apply Rmax_l.
    - iPureIntro.
      intros h1 h2 Hh1 Hh2 Hh1h2.

      set (h x := h1 (K x.1, x.2)).
      assert (SeriesC (λ ρ, prim_step (K e1) σ1 ρ * h1 ρ) =
                SeriesC (λ ρ, prim_step e1 σ1 ρ * h ρ)) as ->.
      {
        rewrite /h.
        apply Rle_antisym.
        - etrans; last first.
          + eapply (SeriesC_le_inj _ (λ ρ, match Kinv ρ.1 with Some e' => Some (e', ρ.2) | None => None end)).
            * real_solver.
            * intros [] []; simpl.
              intros z Hx Hy.
              case_match eqn:Hm1; case_match eqn:Hm2; simpl; try done.
              simplify_eq.
              rewrite pair_equal_spec; split; auto.
              apply HKinvS in Hm1 as <-.
              apply HKinvS in Hm2 as <-.
              done.
            * apply (ex_seriesC_le _ (prim_step e1 σ1)); auto.
              real_solver.
          + right.
            apply SeriesC_ext.
            intros (e&σ); simpl.
            case_match eqn:HKe; simpl.
            * apply HKinvS in HKe.
              rewrite -HKe.
              f_equal.
              symmetry.
              by apply fill_step_prob.
            * destruct (pmf_pos (prim_step (K e1) σ1) (e,σ)) as [Hprm | Hprm]; [|real_solver].
              exfalso.
              destruct (fill_step_inv e1 σ1 e σ Hv ) as [e2' [? ?]]; auto.
              by apply (HKinvN _ e2') in HKe.

        - etrans; last first.
          + eapply (SeriesC_le_inj _ (λ ρ, Some (K ρ.1, ρ.2))).
            * real_solver.
            * intros [][]; simpl.
              intros z Hx Hy.
              apply Some_inj in Hx.
              apply Some_inj in Hy.
              by simplify_eq.
            * apply (ex_seriesC_le _ (prim_step (K e1) σ1)); auto.
              real_solver.
          + right.
            apply SeriesC_ext.
            intros (e&σ); simpl.
            f_equal.
            by apply fill_step_prob.
      }
      apply H0; rewrite /h //.
      intros (e3, σ3) ρ2 HS_inner; simpl.
      assert (S' (K e3, σ3) ρ2) by (rewrite /S'; eauto).
      specialize (Hh1h2 (K e3, σ3) ρ2 ltac:(auto)).
      apply (Rle_trans _ _ _ Hh1h2).
      simpl. rewrite /D2'. simpl. rewrite HKinv3. simpl. lra.
    - iDestruct "Hcnt" as "[% _]"; done.
    - iDestruct "Hcnt" as "[_ Hcnt]".
      iIntros (e2 σ2 e2' σ2') "(%e3 & %He3 & %HS_inner)".
      rewrite -(HKinvS _ _ He3).
      rewrite /E2' /D2'. simpl. rewrite HKinv3. simpl.
      iApply "Hcnt". iPureIntro. exact HS_inner.
  Qed.


  (* Witness that [exp ε * δ] is non-negative, used to package it as a
     [nonnegreal] in the δ-budget of [prog_coupl_steps_adv] below. *)
  Lemma nonneg_exp_mul (ε δ : nonnegreal) : (0 <= exp ε * δ)%R.
  Proof. apply Rmult_le_pos; [left; apply exp_pos | apply cond_nonneg]. Qed.

  Lemma prog_coupl_steps_adv_alt (ε δ : nonnegreal) e1 σ1 e1' σ1'
      (E2 D2 : cfg Λ → cfg Λ → nonnegreal) Z :
    reducible (e1, σ1) →
    reducible (e1', σ1') →
    (∀ ρ1 ρ2, D2 ρ1 ρ2 <= 1) ->
    (forall h1 h2,
        (forall a, 0 <= h1 a <= 1) ->
        (forall b, 0 <= h2 b <= 1) ->
        (forall a b, h1 a <= exp (E2 a b) * h2 b + D2 a b) ->
        (Expval (prim_step e1 σ1) h1 <=
           (exp ε) * Expval (prim_step e1' σ1') h2 + δ) ) ->
    (∀ e2 σ2 e2' σ2',
       |={∅}=> Z e2 σ2 e2' σ2' (E2 (e2,σ2) (e2',σ2'))%NNR
                                (D2 (e2,σ2) (e2',σ2'))%NNR)
      ⊢ prog_coupl e1 σ1 e1' σ1' ε δ Z.
  Proof.
    iIntros (Hred Hred' HD2 Hkanto) "Hcnt".
    iExists 1%nat, (dret σ1'), E2, D2, (λ _ _, True).
    iSplit; [done|].
    iSplit; [iPureIntro; by exists 1|].
    iSplit.
    { iPureIntro.
      rewrite dret_id_left pexec_1.
      rewrite step_or_final_no_final; [|by apply reducible_not_final].
      intros h1 h2 Hh1 Hh2 Hh1h2.
      apply Hkanto; [done|done|].
      intros a b. exact (Hh1h2 a b I). }
    iSplit; [iPureIntro; apply dret_erasable|].
    iIntros (e2 σ2 e2' σ2') "_". iApply "Hcnt".
  Qed.


  Lemma prog_coupl_steps_adv (ε δ : nonnegreal) S e1 σ1 e1' σ1'
      (E2 D2 : cfg Λ → cfg Λ → nonnegreal) Z :
    reducible (e1, σ1) →
    reducible (e1', σ1') →
    (∀ ρ1 ρ2, D2 ρ1 ρ2 <= 1) →
    (forall h1 h2,
        (forall a, 0 <= h1 a <= 1) ->
        (forall b, 0 <= h2 b <= 1) ->
        (forall a b, S a b -> h1 a <= exp (E2 a b) * h2 b + D2 a b) ->
        (Expval (prim_step e1 σ1) h1 <=
           (exp ε) * Expval (prim_step e1' σ1') h2 + δ)) →
    □(∀ e2 σ2 e2' σ2' ε', Z e2 σ2 e2' σ2' ε' 1%NNR) ∗
    (∀ e2 σ2 e2' σ2',
       ⌜S (e2, σ2) (e2', σ2')⌝ ={∅}=∗
       Z e2 σ2 e2' σ2' (E2 (e2,σ2) (e2',σ2')) (D2 (e2,σ2) (e2',σ2')))
      ⊢ prog_coupl e1 σ1 e1' σ1' ε δ Z.
  Proof.
    iIntros (Hred Hred' HD2 Hkanto) "[#Hbox Hcnt]".
    iExists 1%nat, (dret σ1'), E2, D2, S.
    iSplit; [done|].
    iSplit; [iPureIntro; by exists 1|].
    iSplit.
    { iPureIntro.
      rewrite dret_id_left pexec_1.
      rewrite step_or_final_no_final; [|by apply reducible_not_final].
      intros h1 h2 Hh1 Hh2 Hh1h2.
      apply Hkanto; [done|done|done]. }
    iSplit; [iPureIntro; apply dret_erasable|].
    iIntros (e2 σ2 e2' σ2') "%HS".
    iApply "Hcnt". done.
  Qed.

  Lemma prog_coupl_steps_adv_frame (ε1 ε2 ε δ1 δ2 δ: nonnegreal) S e1 σ1 e1' σ1'
      (E2 D2 : cfg Λ → cfg Λ → nonnegreal) Z :
    ε = (ε1 + ε2)%NNR →
    δ = (δ1 + δ2)%NNR →
    reducible (e1, σ1) →
    reducible (e1', σ1') →
    (∀ ρ1 ρ2, D2 ρ1 ρ2 <= 1) →
    (forall h1 h2,
        (forall a, 0 <= h1 a <= 1) ->
        (forall b, 0 <= h2 b <= 1) ->
        (forall a b, S a b -> h1 a <= exp (E2 a b) * h2 b + D2 a b) ->
        (Expval (prim_step e1 σ1) h1 <=
           (exp ε1) * Expval (prim_step e1' σ1') h2 + δ1)) →
    □(∀ e2 σ2 e2' σ2' ε', Z e2 σ2 e2' σ2' ε' 1%NNR) ∗
    (∀ e2 σ2 e2' σ2',
       ⌜S (e2, σ2) (e2', σ2')⌝ ={∅}=∗
       Z e2 σ2 e2' σ2' (E2 (e2,σ2) (e2',σ2') + ε2)%NNR (D2 (e2,σ2) (e2',σ2') + δ2)%NNR)
      ⊢ prog_coupl e1 σ1 e1' σ1' ε δ Z.
  Proof.
    iIntros (-> -> Hred Hred' HD2 Hkanto) "[#Hbox Hcnt]".
    set (E2_pc := λ (ρ1 ρ2 : cfg Λ), (E2 ρ1 ρ2 + ε2)%NNR).
    set (D2_pc := λ (ρ1 ρ2 : cfg Λ),
                    if bool_decide (S ρ1 ρ2) then (D2 ρ1 ρ2 + δ2)%NNR else 1%NNR).
    iExists 1%nat, (dret σ1'), E2_pc, D2_pc, S.
    iSplit; [done|].
    iSplit.
    { iPureIntro. exists (1 + δ2). intros ρ1 ρ2. rewrite /D2_pc.
      case_bool_decide; simpl.
      - have := HD2 ρ1 ρ2. have := cond_nonneg δ2. lra.
      - have := cond_nonneg δ2. lra. }
    iSplit.
    { iPureIntro.
      rewrite dret_id_left pexec_1.
      rewrite step_or_final_no_final; [|by apply reducible_not_final].
      intros h1 h2 Hh1 Hh2 Hh1h2.
      set (h1' := λ ρ, Rmax 0 (h1 ρ - δ2)).
      set (h2' := λ ρ, Rmin 1 (exp ε2 * h2 ρ)).
      have Hh1'bnd : ∀ ρ, 0 <= h1' ρ <= 1.
      { intro ρ. rewrite /h1'; split; [apply Rmax_l|].
        apply Rmax_lub; [lra|].
        apply Rcomplements.Rle_minus_l. transitivity 1; [apply Hh1|].
        have := cond_nonneg δ2. lra. }
      have Hh2'bnd : ∀ ρ, 0 <= h2' ρ <= 1.
      { intro ρ. rewrite /h2'; split.
        - apply Rmin_glb; [lra|].
          apply Rmult_le_pos; [left; apply exp_pos|apply Hh2].
        - apply Rmin_l. }
      have Hpair : ∀ a b, S a b → h1' a <= exp (E2 a b) * h2' b + D2 a b.
      { intros a b HSab.
        rewrite /h1' /h2'.
        apply Rmax_lub.
        - apply Rplus_le_le_0_compat.
          + apply Rmult_le_pos; [left; apply exp_pos|].
            apply Rmin_glb; [lra|apply Rmult_le_pos; [left; apply exp_pos|apply Hh2]].
          + apply cond_nonneg.
        - have Hc := Hh1h2 a b HSab.
          rewrite /E2_pc /D2_pc bool_decide_eq_true_2 in Hc; [|done]. simpl in Hc.
          destruct (Rle_or_lt (exp ε2 * h2 b) 1) as [Hle | Hgt].
          + rewrite Rmin_right; [|exact Hle].
            have Hkey : exp (E2 a b + ε2) * h2 b = exp (E2 a b) * (exp ε2 * h2 b).
            { rewrite exp_plus. ring. }
            rewrite Hkey in Hc. lra.
          + rewrite Rmin_left; [|lra]. rewrite Rmult_1_r.
            have HexpE2 : 1 <= exp (E2 a b).
            { apply exp_pos_ge_1. apply cond_nonneg. }
            have := Hh1 a. have := cond_nonneg δ2. have := cond_nonneg (D2 a b). lra. }
      have HK := Hkanto h1' h2' Hh1'bnd Hh2'bnd Hpair.
      rewrite /Expval in HK.
      have HA : SeriesC (λ ρ, prim_step e1 σ1 ρ * h1 ρ) <=
                SeriesC (λ ρ, prim_step e1 σ1 ρ * h1' ρ) + δ2.
      { transitivity (SeriesC (λ ρ, prim_step e1 σ1 ρ * h1' ρ + prim_step e1 σ1 ρ * δ2)).
        - apply SeriesC_le.
          + intros ρ; split.
            * apply Rmult_le_pos; auto. apply Hh1.
            * rewrite /h1'. rewrite -Rmult_plus_distr_l.
              apply Rmult_le_compat_l; auto.
              apply (Rle_trans _ (Rmax 0 (h1 ρ - δ2) + δ2)).
              ** assert (h1 ρ <= Rmax 0 (h1 ρ - δ2) + δ2); [|lra].
                 apply (Rle_trans _ ((h1 ρ - δ2) + δ2)); [lra|].
                 apply Rplus_le_compat_r. apply Rmax_r.
              ** apply Rplus_le_compat_l. real_solver.
          + apply ex_seriesC_plus.
            * apply (ex_seriesC_le _ (prim_step e1 σ1)); auto.
              intros ρ; split.
              ** apply Rmult_le_pos; auto. apply Rmax_l.
              ** rewrite -{2}(Rmult_1_r (prim_step e1 σ1 ρ)).
                 apply Rmult_le_compat_l; auto.
                 rewrite /h1'. apply Rmax_lub; [lra|].
                 apply Rcomplements.Rle_minus_l. transitivity 1; [apply Hh1|].
                 have := cond_nonneg δ2. lra.
            * apply ex_seriesC_scal_r; auto.
        - rewrite SeriesC_plus.
          + apply Rplus_le_compat_l.
            rewrite SeriesC_scal_r.
            rewrite -{2}(Rmult_1_l (nonneg δ2)).
            apply Rmult_le_compat_r; [apply cond_nonneg|apply pmf_SeriesC].
          + apply (ex_seriesC_le _ (prim_step e1 σ1)); auto.
            intros ρ; rewrite /h1'; split.
            * apply Rmult_le_pos; auto. apply Rmax_l.
            * rewrite -{2}(Rmult_1_r (prim_step e1 σ1 ρ)).
              apply Rmult_le_compat_l; auto.
              apply Rmax_lub; [lra|].
              apply Rcomplements.Rle_minus_l. transitivity 1; [apply Hh1|].
              have := cond_nonneg δ2. lra.
          + apply ex_seriesC_scal_r; auto. }
      have HYineq : SeriesC (λ ρ, prim_step e1' σ1' ρ * h2' ρ) <=
                    exp ε2 * SeriesC (λ ρ, prim_step e1' σ1' ρ * h2 ρ).
      { rewrite -SeriesC_scal_l.
        apply SeriesC_le.
        - intros b; split.
          + apply Rmult_le_pos; auto. rewrite /h2'.
            apply Rmin_glb; [lra|].
            apply Rmult_le_pos; [left; apply exp_pos|apply Hh2].
          + rewrite /h2'.
            rewrite (Rmult_comm (exp ε2) (_ * _)) Rmult_assoc.
            apply Rmult_le_compat_l; auto.
            rewrite -(Rmult_comm (exp ε2)). apply Rmin_r.
        - apply ex_seriesC_scal_l.
          apply (ex_seriesC_le _ (prim_step e1' σ1')); auto.
          intros b; split.
          + apply Rmult_le_pos; [auto|apply Hh2].
          + rewrite -{2}(Rmult_1_r (prim_step _ _ _)).
            apply Rmult_le_compat_l; [auto|apply Hh2]. }
      apply (Rle_trans _ _ _ HA).
      apply (Rle_trans _
               (exp ε1 * SeriesC (λ ρ, prim_step e1' σ1' ρ * h2' ρ) + δ1 + δ2)).
      { apply Rplus_le_compat_r. exact HK. }
      apply (Rle_trans _
               (exp ε1 * (exp ε2 * SeriesC (λ ρ, prim_step e1' σ1' ρ * h2 ρ)) + δ1 + δ2)).
      { do 2 apply Rplus_le_compat_r.
        apply Rmult_le_compat_l; [left; apply exp_pos|exact HYineq]. }
      simpl. rewrite exp_plus. lra. }
    iSplit; [iPureIntro; apply dret_erasable|].
    iIntros (e2 σ2 e2' σ2') "%HS".
    rewrite /E2_pc /D2_pc bool_decide_eq_true_2; [|done].
    iMod ("Hcnt" $! e2 σ2 e2' σ2' with "[%]") as "$"; done.
  Qed.

  Lemma prog_coupl_steps_simple ε2 ε1 ε δ2 δ1 δ R e1 σ1 e1' σ1' Z :
    ε = (ε1 + ε2)%NNR →
    δ = (δ1 + δ2)%NNR →
    reducible (e1, σ1) →
    reducible (e1', σ1') →
    DPcoupl (prim_step e1 σ1) (prim_step e1' σ1') R ε1 δ1 →
    □(∀ e2 σ2 e2' σ2' ε, Z e2 σ2 e2' σ2' ε 1%NNR) ∗
    (∀ e2 σ2 e2' σ2', ⌜R (e2, σ2) (e2', σ2')⌝ ={∅}=∗ Z e2 σ2 e2' σ2' ε2 δ2)
      ⊢ prog_coupl e1 σ1 e1' σ1' ε δ Z.
  Proof.
    iIntros (-> -> Hred Hred' Hcpl) "[#Hbox Hcnt]".
    set (S := R).
    set (D2 := λ (ρ1 ρ2 : cfg Λ), if bool_decide (R ρ1 ρ2) then δ2 else 1%NNR).
    iExists 1%nat, (dret σ1'), (λ _ _, ε2), D2, S.
    iSplit; [done|].
    iSplit.
    { iPureIntro. exists (Rmax 1 δ2). intros ρ1 ρ2.
      rewrite /D2. case_bool_decide; simpl; [apply Rmax_r | apply Rmax_l]. }
    iSplit.
    { iPureIntro.
      rewrite dret_id_left pexec_1.
      rewrite step_or_final_no_final; [|by apply reducible_not_final].
      intros h1 h2 Hh1 Hh2 Hh1h2.
      (* Intermediate functions:
           h1' a = Rmax 0 (h1 a - δ2)   (drop the δ2 contribution on the lhs)
           h2' b = Rmin 1 (exp ε2 * h2 b)  (absorb ε2 on the rhs)
         Both land in [0,1] and satisfy R a b → h1' a <= h2' b. *)
      set (h1' := λ ρ, Rmax 0 (h1 ρ - δ2)).
      set (h2' := λ ρ, Rmin 1 (exp ε2 * h2 ρ)).
      (* Step 2: SeriesC(μ1·h1) <= SeriesC(μ1·h1') + δ2. *)
      assert (SeriesC (λ ρ, prim_step e1 σ1 ρ * h1 ρ) <=
                SeriesC (λ ρ, prim_step e1 σ1 ρ * h1' ρ) + δ2) as Hstep2.
      { transitivity (SeriesC (λ ρ, prim_step e1 σ1 ρ * h1' ρ + prim_step e1 σ1 ρ * δ2)).
        - apply SeriesC_le.
          + intros ρ; split.
            * apply Rmult_le_pos; auto. apply Hh1.
            * rewrite /h1'. rewrite -Rmult_plus_distr_l.
              apply Rmult_le_compat_l; auto.
              apply (Rle_trans _ (Rmax 0 (h1 ρ - δ2) + δ2)).
              ** assert (h1 ρ <= Rmax 0 (h1 ρ - δ2) + δ2); [|lra].
                 apply (Rle_trans _ ((h1 ρ - δ2) + δ2)); [lra|].
                 apply Rplus_le_compat_r. apply Rmax_r.
              ** apply Rplus_le_compat_l. real_solver.
          + apply ex_seriesC_plus.
            * apply (ex_seriesC_le _ (prim_step e1 σ1)); auto.
              intros ρ; split.
              ** apply Rmult_le_pos; auto. apply Rmax_l.
              ** rewrite -{2}(Rmult_1_r (prim_step e1 σ1 ρ)).
                 apply Rmult_le_compat_l; auto.
                 rewrite /h1'. apply Rmax_lub; [lra|].
                 apply Rcomplements.Rle_minus_l. transitivity 1; [apply Hh1|].
                 have := cond_nonneg δ2. lra.
            * apply ex_seriesC_scal_r; auto.
        - rewrite SeriesC_plus.
          + apply Rplus_le_compat_l.
            rewrite SeriesC_scal_r.
            rewrite -{2}(Rmult_1_l (nonneg δ2)).
            apply Rmult_le_compat_r; [apply cond_nonneg|apply pmf_SeriesC].
          + apply (ex_seriesC_le _ (prim_step e1 σ1)); auto.
            intros ρ; rewrite /h1'; split.
            * apply Rmult_le_pos; auto. apply Rmax_l.
            * rewrite -{2}(Rmult_1_r (prim_step e1 σ1 ρ)).
              apply Rmult_le_compat_l; auto.
              apply Rmax_lub; [lra|].
              apply Rcomplements.Rle_minus_l. transitivity 1; [apply Hh1|].
              have := cond_nonneg δ2. lra.
          + apply ex_seriesC_scal_r; auto. }
      (* Step 3: DPcoupl on h1', h2'. *)
      assert (SeriesC (λ ρ, prim_step e1 σ1 ρ * h1' ρ) <=
                exp ε1 * SeriesC (λ ρ, prim_step e1' σ1' ρ * h2' ρ) + δ1) as Hstep3.
      { apply (Hcpl h1' h2').
        - intros a; rewrite /h1'; split; [apply Rmax_l|].
          apply Rmax_lub; [lra|].
          apply Rcomplements.Rle_minus_l. transitivity 1; [apply Hh1|].
          have := cond_nonneg δ2. lra.
        - intros b; rewrite /h2'; split.
          + apply Rmin_glb; [lra|].
            apply Rmult_le_pos; [left; apply exp_pos|apply Hh2].
          + apply Rmin_l.
        - intros a b HRab.
          rewrite /h1' /h2'.
          apply Rmax_lub.
          + apply Rmin_glb; [lra|].
            apply Rmult_le_pos; [left; apply exp_pos|apply Hh2].
          + (* h1 a - δ2 <= Rmin 1 (exp ε2 * h2 b) *)
            apply Rmin_glb.
            * have := Hh1 a. have := cond_nonneg δ2. lra.
            * (* from Hh1h2 with D2 a b = δ2 (R holds) *)
              specialize (Hh1h2 a b HRab). rewrite /D2 in Hh1h2.
              rewrite bool_decide_eq_true_2 in Hh1h2; [|done].
              simpl in Hh1h2.
              apply (Rle_trans _ (exp ε2 * h2 b + δ2 - δ2)); [|lra].
              apply Rplus_le_compat_r. exact Hh1h2. }
      (* Step 4: SeriesC(μ2·h2') <= exp ε2 * SeriesC(μ2·h2). *)
      assert (SeriesC (λ ρ, prim_step e1' σ1' ρ * h2' ρ) <=
                exp ε2 * SeriesC (λ ρ, prim_step e1' σ1' ρ * h2 ρ)) as Hstep4.
      { rewrite -SeriesC_scal_l.
        apply SeriesC_le.
        - intros b; split.
          + apply Rmult_le_pos; auto. rewrite /h2'.
            apply Rmin_glb; [lra|].
            apply Rmult_le_pos; [left; apply exp_pos|apply Hh2].
          + rewrite /h2'.
            rewrite (Rmult_comm (exp ε2) ( _ * _)) Rmult_assoc.
            apply Rmult_le_compat_l; auto.
            rewrite -(Rmult_comm (exp ε2)). apply Rmin_r.
        - apply ex_seriesC_scal_l.
          apply (ex_seriesC_le _ (prim_step e1' σ1')); auto.
          intros b; split.
          + apply Rmult_le_pos; [auto|apply Hh2].
          + rewrite -{2}(Rmult_1_r (prim_step _ _ _)).
            apply Rmult_le_compat_l; [auto|apply Hh2]. }
      (* Combine: chain Hstep2, Hstep3, Hstep4. *)
      apply (Rle_trans _ _ _ Hstep2).
      apply (Rle_trans _ (exp ε1 * SeriesC (λ ρ, prim_step e1' σ1' ρ * h2' ρ) + δ1 + δ2)).
      { apply Rplus_le_compat_r. exact Hstep3. }
      apply (Rle_trans _
               (exp ε1 * (exp ε2 * SeriesC (λ ρ, prim_step e1' σ1' ρ * h2 ρ)) + δ1 + δ2)).
      { do 2 apply Rplus_le_compat_r.
        apply Rmult_le_compat_l; [left; apply exp_pos|exact Hstep4]. }
      simpl. rewrite exp_plus. lra. }
    iSplit; [iPureIntro; apply dret_erasable|].
    iIntros (e2 σ2 e2' σ2') "%HR".
    rewrite /D2 bool_decide_eq_true_2; [|done].
    iMod ("Hcnt" $! e2 σ2 e2' σ2' with "[%]") as "$"; done.
  Qed.

  Lemma prog_coupl_steps_choice ε2 ε1 ε2' ε1' ε δ2 δ1 δ1' δ P R R' e1 σ1 e1' σ1' Z :
    ε = (ε1 + ε2)%NNR →
    ε = (ε1' + ε2')%NNR →
    δ = (δ1 + δ2 + δ1')%NNR →
    reducible (e1, σ1) →
    reducible (e1', σ1') →
    (forall a a' b, P a -> ¬ P a' -> ¬(R a b /\ R' a' b)) ->
    DPcoupl (prim_step e1 σ1) (prim_step e1' σ1') R ε1 δ1 →
    DPcoupl (prim_step e1 σ1) (prim_step e1' σ1') R' ε1' δ1' →
    □(∀ e2 σ2 e2' σ2' ε'', Z e2 σ2 e2' σ2' ε'' 1%NNR) ∗
    (∀ e2 σ2 e2' σ2',
        (⌜P (e2, σ2) /\ R (e2, σ2) (e2', σ2')⌝ ={∅}=∗ Z e2 σ2 e2' σ2' ε2 δ2) ∗
        (⌜ ¬P (e2, σ2) /\ R' (e2, σ2) (e2', σ2')⌝ ={∅}=∗ Z e2 σ2 e2' σ2' ε2' δ2))
      ⊢ prog_coupl e1 σ1 e1' σ1' ε δ Z.
  Proof.
    iIntros (Hε Hε' Hδ Hred Hred' Hindep Hcpl1 Hcpl2) "[#Hbox Hcnt]".
    set (E2 := λ (ρ1 ρ2 : cfg Λ), if bool_decide (P ρ1) then ε2 else ε2').
    set (S_pc := λ (ρ1 ρ2 : cfg Λ), (P ρ1 ∧ R ρ1 ρ2) ∨ (¬ P ρ1 ∧ R' ρ1 ρ2)).
    set (D2 := λ (ρ1 ρ2 : cfg Λ),
                 if bool_decide ((P ρ1 ∧ R ρ1 ρ2) ∨ (¬ P ρ1 ∧ R' ρ1 ρ2))
                 then δ2 else 1%NNR).
    iExists 1%nat, (dret σ1'), E2, D2, S_pc.
    iSplit; [done|].
    iSplit.
    { iPureIntro. exists (Rmax 1 δ2). intros ρ1 ρ2. rewrite /D2.
      case_bool_decide; simpl; [apply Rmax_r | apply Rmax_l]. }
    iSplit.
    { iPureIntro.
      rewrite dret_id_left pexec_1.
      rewrite step_or_final_no_final; [|by apply reducible_not_final].
      intros h1 h2 Hh1 Hh2 Hh1h2.
      eapply (DPcoupl_choice_adv_kanto (prim_step e1 σ1) (prim_step e1' σ1')
                P R R' ε1 ε2 δ1 δ2 ε1' ε2' δ1' ε δ);
        [apply cond_nonneg | apply cond_nonneg | apply cond_nonneg
        | rewrite Hε; simpl; lra | rewrite Hε'; simpl; lra
        | rewrite Hδ; simpl; lra | done | done | done | done | done | ..].
      - intros ρ1 ρ2 HP HR.
        specialize (Hh1h2 ρ1 ρ2 (or_introl (conj HP HR))).
        rewrite /E2 /D2 in Hh1h2.
        rewrite bool_decide_eq_true_2 // in Hh1h2.
        rewrite bool_decide_eq_true_2 in Hh1h2; [done|]. by left.
      - intros ρ1 ρ2 HP HR.
        specialize (Hh1h2 ρ1 ρ2 (or_intror (conj HP HR))).
        rewrite /E2 /D2 in Hh1h2.
        rewrite bool_decide_eq_false_2 // in Hh1h2.
        rewrite bool_decide_eq_true_2 in Hh1h2; [done|]. by right. }
    iSplit; [iPureIntro; apply dret_erasable|].
    iIntros (e2 σ2 e2' σ2') "%HS".
    rewrite /D2 bool_decide_eq_true_2; [|exact HS].
    iDestruct ("Hcnt" $! e2 σ2 e2' σ2') as "[Hcnt1 Hcnt2]".
    rewrite /E2. destruct HS as [[HP HR] | [HnP HR']].
    - rewrite bool_decide_eq_true_2; [|done].
      iMod ("Hcnt1" with "[%]") as "$"; done.
    - rewrite bool_decide_eq_false_2; [|done].
      iMod ("Hcnt2" with "[%]") as "$"; done.
  Qed.


  Lemma prog_coupl_step_l_erasable ε2 ε1 δ2 δ1 μ1' ε δ R e1 σ1 e1' σ1' Z :
    ε = (ε1 + ε2)%NNR →
    δ = (δ1 + δ2)%NNR →
    reducible (e1, σ1) →
    DPcoupl (prim_step e1 σ1) μ1' R ε1 δ1  →
    erasable μ1' σ1' →
    □(∀ e2 σ2 e2' σ2' ε'', Z e2 σ2 e2' σ2' ε'' 1%NNR) ∗
    (∀ e2 σ2 σ2', ⌜R (e2, σ2) σ2'⌝ ={∅}=∗ Z e2 σ2 e1' σ2' ε2 δ2)
      ⊢ prog_coupl e1 σ1 e1' σ1' ε δ Z.
  Proof.
    iIntros (Hε Hδ Hred Hcpl Hera) "[#Hbox Hcnt]".
    set (S_le := λ (ρ1 : cfg Λ) (ρ2 : cfg Λ), R ρ1 ρ2.2 ∧ ρ2.1 = e1').
    set (D2 := λ (ρ1 : cfg Λ) (ρ2 : cfg Λ),
                 if bool_decide (S_le ρ1 ρ2) then δ2 else 1%NNR).
    iExists 0%nat, μ1', (λ _ _, ε2), D2, S_le.
    iSplit; [done|].
    iSplit.
    { iPureIntro. exists (Rmax 1 δ2). intros ρ1 ρ2. rewrite /D2.
      case_bool_decide; simpl; [apply Rmax_r | apply Rmax_l]. }
    iSplit.
    { iPureIntro.
      unfold pexec; simpl.
      intros h1 h2 Hh1 Hh2 Hh1h2.
      assert (SeriesC (λ ρ : cfg Λ, (μ1' ≫= λ σ2', dret (e1', σ2')) ρ * h2 ρ) =
              SeriesC (λ σ2', μ1' σ2' * h2 (e1', σ2'))) as Heq.
      {
        assert (Hfold :
          SeriesC (λ ρ : cfg Λ, (μ1' ≫= λ σ2', dret (e1', σ2')) ρ * h2 ρ) =
          Expval (μ1' ≫= λ σ2' : state Λ, dret (e1', σ2')) h2).
        { rewrite /Expval. done. }
        rewrite Hfold.
        rewrite Expval_dbind;
          [| intros b; apply (proj1 (Hh2 b))
           | apply ex_expval_unit; apply Hh2].
        rewrite /Expval.
        apply SeriesC_ext. intros σ2'. f_equal.
        fold (Expval (dret (e1', σ2')) h2).
        apply Expval_dret.
      }
      rewrite Heq.
      eapply (DPcoupl_adv_kanto (prim_step e1 σ1) μ1' R ε1 ε2 δ1 δ2 ε δ);
        [apply cond_nonneg | apply cond_nonneg
        | rewrite Hε; simpl; lra | rewrite Hδ; simpl; lra | done | done
        | intros σ2'; apply Hh2 | ].
      intros a σ2' HR.
      specialize (Hh1h2 a (e1', σ2') (conj HR eq_refl)).
      rewrite /D2 /S_le in Hh1h2.
      rewrite bool_decide_eq_true_2 in Hh1h2; [done|]. done. }
    iSplit; [done|].
    iIntros (e2 σ2 e2' σ2') "%HS".
    rewrite /D2 bool_decide_eq_true_2; [|exact HS].
    destruct HS as [HR He]. simpl in HR, He. rewrite He.
    iMod ("Hcnt" $! e2 σ2 σ2' with "[%]") as "$"; [exact HR | done].
  Qed.

  Lemma prog_coupl_step_l_dret ε2 ε1 ε δ2 δ1 δ R e1 σ1 e1' σ1' Z :
    ε = (ε1 + ε2)%NNR →
    δ = (δ1 + δ2)%NNR →
    reducible (e1, σ1) →
    DPcoupl (prim_step e1 σ1) (dret σ1') R ε1 δ1 →
    □(∀ e2 σ2 e2' σ2' ε'', Z e2 σ2 e2' σ2' ε'' 1%NNR) ∗
    (∀ e2 σ2, ⌜R (e2, σ2) σ1'⌝ ={∅}=∗ Z e2 σ2 e1' σ1' ε2 δ2)
    ⊢ prog_coupl e1 σ1 e1' σ1' ε δ Z.
  Proof.
    iIntros (-> -> ? ?) "[#Hbox H]".
    iApply (prog_coupl_step_l_erasable _ _ _ _ (dret (σ1'))); [done|done|done|..].
    { by apply DPcoupl_pos_R. }
    { apply dret_erasable. }
    iSplit; [iApply "Hbox"|].
    iIntros (??? (?&?&->%dret_pos)).
    by iApply "H".
  Qed.

  Lemma prog_coupl_step_l e1 σ1 e1' σ1' ε δ Z :
    reducible (e1, σ1) →
    □(∀ e2 σ2 e2' σ2' ε'', Z e2 σ2 e2' σ2' ε'' 1%NNR) ∗
    (∀ e2 σ2, ⌜prim_step e1 σ1 (e2, σ2) > 0⌝ ={∅}=∗ Z e2 σ2 e1' σ1' ε δ)
    ⊢ prog_coupl e1 σ1 e1' σ1' ε δ Z.
  Proof.
    iIntros (?) "[#Hbox H]".
    iApply (prog_coupl_step_l_dret ε 0%NNR _ δ 0%NNR);
      [apply nnreal_ext => /= ; lra| apply nnreal_ext => /= ; lra | done|..].
    { eapply DPcoupl_pos_R, DPcoupl_trivial.
      - by apply prim_step_mass.
      - apply dret_mass. }
    iSplit; [iApply "Hbox"|].
    iIntros (?? (_ & ? & [=]%dret_pos)).
    by iApply "H".
  Qed.

  Lemma prog_coupl_reducible e e' σ σ' Z ε δ :
    prog_coupl e σ e' σ' ε δ Z -∗ ⌜reducible (e, σ)⌝.
  Proof. by iIntros "(%&%&%&%&%&?&?)". Qed.

End coupl_modalities.


(** * The weakest precondition  *)
Definition wp_pre `{!spec_updateGS (lang_markov Λ) Σ, !diffprivWpGS Λ Σ}
    (wp : coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
     coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
  (∀ σ1 e1' σ1' ε1 δ1,
      state_interp σ1 ∗ spec_interp (e1', σ1') ∗ err_interp ε1 δ1 ={E, ∅}=∗
      spec_coupl ∅ σ1 e1' σ1' ε1 δ1 (λ σ2 e2' σ2' ε2 δ2,
        match to_val e1 with
        | Some v => |={∅, E}=> state_interp σ2 ∗ spec_interp (e2', σ2') ∗ err_interp ε2 δ2 ∗ Φ v
        | None =>
            prog_coupl e1 σ2 e2' σ2' ε2 δ2 (λ e3 σ3 e3' σ3' ε3 δ3,
                ▷ spec_coupl ∅ σ3 e3' σ3' ε3 δ3 (λ σ4 e4' σ4' ε4 δ4,
                    |={∅, E}=> state_interp σ4 ∗ spec_interp (e4', σ4') ∗ err_interp ε4 δ4 ∗ wp E e3 Φ))
      end))%I.

Local Instance wp_pre_contractive `{!spec_updateGS (lang_markov Λ) Σ, !diffprivWpGS Λ Σ} :
  Contractive wp_pre.
Proof.
  rewrite /wp_pre /= => n wp wp' Hwp E e1 Φ.
  do 12 f_equiv.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [? ?]. rewrite /spec_coupl_pre.
  do 4 f_equiv.
  rewrite /prog_coupl.
  do 26 f_equiv;
  f_contractive.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [? ?]. rewrite /spec_coupl_pre.
  do 9 f_equiv.
  apply Hwp.
Qed.

Local Definition wp_def `{!spec_updateGS (lang_markov Λ) Σ, !diffprivWpGS Λ Σ} :
  Wp (iProp Σ) (expr Λ) (val Λ) () :=
  {| wp := λ _ : (), fixpoint (wp_pre); wp_default := () |}.
Local Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp' := wp_aux.(unseal).
Global Arguments wp' {Λ Σ _}.
Global Existing Instance wp'.
Local Lemma wp_unseal `{!spec_updateGS (lang_markov Λ) Σ, !diffprivWpGS Λ Σ} : wp =
  (@wp_def Λ Σ _ _).(wp).
Proof. rewrite -wp_aux.(seal_eq) //. Qed.

Section wp.
Context `{!spec_updateGS (lang_markov Λ) Σ, !diffprivWpGS Λ Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types ρ : cfg Λ.

(* Weakest pre *)
Lemma wp_unfold E e Φ s :
  WP e @ s; E {{ Φ }} ⊣⊢ wp_pre (wp (PROP:=iProp Σ) s) E e Φ.
Proof. rewrite wp_unseal. apply (fixpoint_unfold wp_pre). Qed.

Global Instance wp_ne E e n s :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp (PROP:=iProp Σ) s E e).
Proof.
  revert e. induction (lt_wf n) as [n _ IH]=> e Φ Ψ HΦ.
  rewrite !wp_unfold /wp_pre /=.
  do 12 f_equiv.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [? ?]. rewrite /spec_coupl_pre /prog_coupl.
  do 30 f_equiv;
  f_contractive_fin.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [? ?]. rewrite /spec_coupl_pre.
  do 8 f_equiv.
  rewrite IH; [done|lia|].
  intros ?. apply dist_S, HΦ.
Qed.
Global Instance wp_proper E e s :
  Proper (pointwise_relation _ (≡) ==> (≡)) (wp (PROP:=iProp Σ) s E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne=>v; apply equiv_dist.
Qed.
Global Instance wp_contractive E e n s :
  TCEq (to_val e) None →
  Proper (pointwise_relation _ (dist_later n) ==> dist n) (wp (PROP:=iProp Σ) s E e).
Proof.
  intros He Φ Ψ HΦ. rewrite !wp_unfold /wp_pre He /=.
  do 12 f_equiv.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [? ?]. rewrite /spec_coupl_pre.
  rewrite /prog_coupl.
  do 29 f_equiv;
  f_contractive.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [? ?]. rewrite /spec_coupl_pre.
  do 22 f_equiv.
Qed.

Lemma wp_value_fupd' E Φ v s : (|={E}=> Φ v) ⊢ WP of_val v @ s; E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre to_of_val.
  iIntros "H" (?????) "(?&?&?)".
  iApply spec_coupl_ret.
  iMod "H". iFrame.
  iApply fupd_mask_subseteq.
  set_solver.
Qed.

Lemma wp_strong_mono E1 E2 e Φ Ψ s :
  E1 ⊆ E2 →
  WP e @ s; E1 {{ Φ }} -∗
 (∀ σ1 e1' σ1' ε1 δ1 v,
     state_interp σ1 ∗ spec_interp (e1', σ1') ∗ err_interp ε1 δ1 ∗ Φ v -∗
     spec_coupl ∅ σ1 e1' σ1' ε1 δ1 (λ σ2 e2' σ2' ε2 δ2,
          |={E2}=> state_interp σ2 ∗ spec_interp (e2', σ2') ∗ err_interp ε2 δ2 ∗ Ψ v)) -∗
  WP e @ s; E2 {{ Ψ }}.
Proof.
  iIntros (HE) "H HΦ". iLöb as "IH" forall (e E1 E2 HE Φ Ψ s).
  rewrite !wp_unfold /wp_pre /=.
  iIntros (σ1 e1' σ1' ε1 δ1) "(Hσ & Hs & Hε)".
  iSpecialize ("H" with "[$]").
  iMod (fupd_mask_subseteq E1) as "Hclose"; [done|].
  iMod "H"; iModIntro.
  iApply (spec_coupl_bind with "[-H] H"); [done|].
  iIntros (?????) "H".
  destruct (to_val e) as [v|] eqn:?.
  { iApply fupd_spec_coupl.
    iMod "H" as "(?&?&?)".
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iSpecialize ("HΦ" with "[$]").
    iApply (spec_coupl_bind with "[-HΦ] HΦ"); [done|].
    iIntros (?????) "Hσ".
    iApply spec_coupl_ret.
    iMod "Hclose'". iMod "Hclose".
    by iMod "Hσ". }
  iApply spec_coupl_ret.
  iApply (prog_coupl_mono with "[HΦ Hclose] H").
  iIntros (e2 σ3 e3' σ3' ε3 δ3) "H !>".
  iApply (spec_coupl_mono with "[HΦ Hclose] H"); [done|].
  iIntros (σ4 e4' σ4' ε4 δ4) "> ($ & $ & $ & H)".
  iMod "Hclose" as "_".
  iModIntro.
  by iApply ("IH" with "[] H").
Qed.

Lemma wp_strong_mono' E1 E2 e Φ Ψ s :
  E1 ⊆ E2 →
  WP e @ s; E1 {{ Φ }} -∗
  (∀ σ ρ v ε δ,
      state_interp σ ∗ spec_interp ρ ∗ err_interp ε δ ∗ Φ v ={E2}=∗
      state_interp σ ∗ spec_interp ρ ∗ err_interp ε δ ∗ Ψ v) -∗
  WP e @ s; E2 {{ Ψ }}.
Proof.
  iIntros (?) "Hwp Hw".
  iApply (wp_strong_mono with "Hwp"); [done|].
  iIntros (??????) "(?&?&?&?)".
  iApply spec_coupl_ret.
  by iMod ("Hw" with "[$]").
Qed.

Lemma wp_strong_mono'' e Φ Ψ :
  WP e {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e {{ Ψ }}.
Proof.
  iIntros "Hwp Hw".
  iApply (wp_strong_mono with "Hwp"); [done|].
  iIntros (??????) "(?&?&?&?)".
  iApply spec_coupl_ret.
  iFrame. iApply "Hw". done.
Qed.

Lemma fupd_wp E e Φ s: (|={E}=> WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre.
  iIntros "H" (?????) "(?&?&?)".
  destruct (to_val e) as [v|] eqn:?.
  { by iMod ("H" with "[$]"). }
  by iMod ("H" with "[$]").
Qed.

Lemma wp_fupd E e Φ s : WP e @ s; E {{ v, |={E}=> Φ v }} ⊢ WP e @ s; E {{ Φ }}.
Proof.
  iIntros "H".
  iApply (wp_strong_mono E with "H"); [done|].
  iIntros (??????) "(? & ? & ? & ?)".
  iApply spec_coupl_ret.
  by iFrame.
Qed.

Lemma wp_atomic E1 E2 e Φ `{!Atomic StronglyAtomic e} s :
  (|={E1,E2}=> WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros "H". rewrite !wp_unfold /wp_pre.
  iIntros (σ1 e1' σ1' ε1 δ1) "(Hσ & Hs & Hε)".
  iDestruct ("H" with "[$]") as ">> H".
  iModIntro.
  iApply (spec_coupl_mono with "[] H"); [done|].
  iIntros (σ2 e2' σ2' ε2 δ2) "H".
  destruct (to_val e) as [v|] eqn:?.
  { iDestruct "H" as "> ($ & $ & $ & $)". }
  iDestruct (prog_coupl_strengthen with "[] H") as "H".
  { iModIntro. iIntros (?????). iApply spec_coupl_ret_err_ge_1. simpl. lra. }
  iApply (prog_coupl_mono with "[] H").
  iIntros (e3 σ3 e3' σ3' ε3 δ3) "[[(% & %Hstep)|%] H] !>"; last first.
  { iApply spec_coupl_ret_err_ge_1. simpl. lra. }
  iApply (spec_coupl_bind with "[] H"); [done|].
  iIntros (?????) "H".
  iApply fupd_spec_coupl.
  iMod "H" as "(Hσ & Hρ & Hε & H)".
  rewrite !wp_unfold /wp_pre.
  destruct (to_val e3) as [v2|] eqn:He2.
  + iMod ("H" with "[$]") as "H". iModIntro.
    iApply (spec_coupl_mono with "[] H"); [done|].
    iIntros (?????) "> ($ & $ & $ & >H)".
    rewrite -(of_to_val e3 v2) //.
    iApply wp_value_fupd'.
    iApply fupd_mask_intro_subseteq; [|done].
    set_solver.
  + iMod ("H" with "[$]") as "H". iModIntro.
    iApply (spec_coupl_mono with "[] H"); [done|].
    iIntros (?????) "H".
    iDestruct (prog_coupl_reducible with "H") as %[ρ Hr].
    pose proof (atomic _ _ _ Hstep) as [? Hval].
    apply val_stuck in Hr. simplify_eq.
Qed.

Lemma wp_step_fupd E1 E2 e P Φ s :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> P) -∗ WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ s; E1 {{ Φ }}.
Proof.
  rewrite !wp_unfold /wp_pre. iIntros (-> ?) "HR H".
  iIntros (σ1 e1' σ1' ε1 δ1) "Hs". iMod "HR".
  iMod ("H" with "Hs") as "H".
  iModIntro.
  iApply (spec_coupl_mono with "[HR] H"); [done|].
  iIntros (σ2 e2' σ2' ε2 δ2) "H".
  iApply (prog_coupl_mono with "[HR] H").
  iIntros (e3 σ3 e3' σ3' ε3 δ3) "H !>".
  iApply (spec_coupl_mono with "[HR] H"); [done|].
  iIntros (σ4 e4' σ4' ε4 δ4) "H".
  iMod "H" as "($ & $ & $ & H)".
  iMod "HR".
  iApply (wp_strong_mono E2 with "H"); [done..|].
  iIntros "!>" (??????) "(? & ? & ? & H)".
  iApply spec_coupl_ret.
  iMod ("H" with "[$]").
  by iFrame.
Qed.

Lemma wp_bind K `{!LanguageCtx K} E e Φ s :
  WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }} ⊢ WP K e @ s; E {{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ s). rewrite !wp_unfold /wp_pre.
  iIntros (σ1 e1' σ1' ε1 δ1) "Hs".
  iMod ("H" with "[$]") as "H".
  iApply (spec_coupl_bind with "[] H"); [done|].
  iIntros (σ2 e2' σ2' ε2 δ2) "H".
  destruct (to_val e) as [v|] eqn:He.
  { iApply fupd_spec_coupl.
    iMod "H" as "(Hσ & Hs & Hε & H)".
    apply of_to_val in He as <-.
    rewrite wp_unfold /wp_pre.
    by iMod ("H" with "[$]"). }
  rewrite fill_not_val /=; [|done].
  iApply spec_coupl_ret.
  iApply prog_coupl_ctx_bind; [done| |].
  { iModIntro. iIntros (?????). iApply spec_coupl_ret_err_ge_1. simpl. lra. }
  iApply (prog_coupl_mono with "[] H").
  iIntros (e3 σ3 e3' σ3' ε3 δ3) "H !>".
  iApply (spec_coupl_mono with "[] H"); [done|].
  iIntros (σ4 e4' σ4' ε4 δ4) "H".
  iMod "H" as "($ & $ & $ & H)".
  iModIntro.
  by iApply "IH".
Qed.

Lemma spec_update_wp E e Φ a :
  spec_update E (WP e @ a; E {{ Φ }}) ⊢ WP e @ a; E {{ Φ }}.
Proof.
  iIntros "Hspec".
  iEval (rewrite !wp_unfold /wp_pre).
  iIntros (σ1 e1' σ1' ε1 δ1) "(Hσ & Hs & Hε)".
  rewrite spec_update_unseal.
  iMod ("Hspec" with "Hs")
    as ([e2' σ2'] n Hstep%stepN_pexec_det) "(Hs & Hwp)".
  iEval (rewrite !wp_unfold /wp_pre) in "Hwp".
  iMod ("Hwp" with "[$]") as "Hwp".
  iModIntro.
  by iApply spec_coupl_steps_det.
Qed.

Lemma wp_spec_update E e Φ s :
  WP e @ s; E {{ v, spec_update E (Φ v) }} ⊢ WP e @ s; E {{ Φ }}.
Proof.
  iIntros "Hwp".
  iLöb as "IH" forall (e E Φ s).
  rewrite !wp_unfold /wp_pre.
  iIntros (σ1 e1' σ1' ε1 δ1) "(Hσ & Hs & Hε)".
  iMod ("Hwp" with "[$]") as "Hwp".
  iModIntro.
  iApply (spec_coupl_bind with "[] Hwp"); [done|].
  iIntros (?????) "H".
  destruct (to_val e).
  { iApply fupd_spec_coupl.
    iMod "H" as "(?&?&?& Hupd)".
    rewrite spec_update_unseal.
    iMod ("Hupd" with "[$]")
      as ([e3' σ3'] n Hstep%stepN_pexec_det) "(Hs & Hwp)".
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".
    iApply spec_coupl_steps_det; [done|].
    iApply spec_coupl_ret.
    iMod "Hclose".
    by iFrame. }
  iApply spec_coupl_ret.
  iApply (prog_coupl_mono with "[] H").
  iIntros (e2 σ3 e3' σ3' ε3 δ3) "H !>".
  iApply (spec_coupl_mono with "[] H"); [done|].
  iIntros (σ4 e4' σ4' ε4 δ4) "> ($ & $ & $ & H)".
  iApply ("IH" with "H").
Qed.

(** * Derived rules *)
Lemma wp_mono E e Φ Ψ s : (∀ v, Φ v ⊢ Ψ v) → WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (wp_strong_mono' with "H"); auto.
  iIntros (?????) "($ & $ & $ & ?)". by iApply HΦ.
Qed.
Lemma wp_mask_mono E1 E2 e Φ s : E1 ⊆ E2 → WP e @ s; E1 {{ Φ }} ⊢ WP e @ s; E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (wp_strong_mono' with "H"); auto. Qed.
Global Instance wp_mono' E e s :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.
Global Instance wp_flip_mono' E e s :
  Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (wp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.

Lemma wp_value_fupd E Φ e v s : IntoVal e v → (|={E}=> Φ v) ⊢ WP e @ s; E {{ Φ }}.
Proof. intros <-. by apply wp_value_fupd'. Qed.
Lemma wp_value' E Φ v s : Φ v ⊢ WP (of_val v) @ s; E {{ Φ }}.
Proof. iIntros. by iApply wp_value_fupd. Qed.
Lemma wp_value E Φ e v s : IntoVal e v → Φ v ⊢ WP e @ s; E {{ Φ }}.
Proof. intros <-. apply wp_value'. Qed.

Lemma wp_frame_l E e Φ R s : R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof.
  iIntros "[? H]".
  iApply (wp_strong_mono with "H"); [done|].
  iIntros (??????) "(? & ? & ? & ?)".
  iApply spec_coupl_ret. by iFrame.
Qed.
Lemma wp_frame_r E e Φ R s : WP e @ s; E {{ Φ }} ∗ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros "[H ?]". iApply (wp_strong_mono' with "H"); auto with iFrame. Qed.

Lemma wp_frame_step_l E1 E2 e Φ R s :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> R) ∗ WP e @ s; E2 {{ Φ }} ⊢ WP e @ s; E1 {{ v, R ∗ Φ v }}.
Proof.
  iIntros (??) "[Hu Hwp]". iApply (wp_step_fupd with "Hu"); try done.
  iApply (wp_mono with "Hwp"). by iIntros (?) "$$".
Qed.
Lemma wp_frame_step_r E1 E2 e Φ R s :
  TCEq (to_val e) None → E2 ⊆ E1 →
  WP e @ s; E2 {{ Φ }} ∗ (|={E1}[E2]▷=> R) ⊢ WP e @ s; E1 {{ v, Φ v ∗ R }}.
Proof.
  rewrite [(WP _ @ _; _ {{ _ }} ∗ _)%I]comm.
  setoid_rewrite (comm _ _ R).
  apply wp_frame_step_l.
Qed.
Lemma wp_frame_step_l' E e Φ R s :
  TCEq (to_val e) None → ▷ R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_l E E); try iFrame; eauto. Qed.
Lemma wp_frame_step_r' E e Φ R s :
  TCEq (to_val e) None → WP e @ s; E {{ Φ }} ∗ ▷ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_r E E); try iFrame; eauto. Qed.

Lemma wp_wand E e Φ Ψ s :
  WP e @ s; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (wp_strong_mono' with "Hwp"); auto.
  iIntros (?????) "($ & $ & $ & ?)". by iApply "H".
Qed.
Lemma wp_wand_l E e Φ Ψ s :
  (∀ v, Φ v -∗ Ψ v) ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_wand_r E e Φ Ψ s :
  WP e @ s; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_frame_wand E e Φ R s :
  R -∗ WP e @ s; E {{ v, R -∗ Φ v }} -∗ WP e @ s; E {{ Φ }}.
Proof.
  iIntros "HR HWP". iApply (wp_wand with "HWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.

End wp.

(** * Proofmode class instances *)
Section proofmode_classes.
  Context `{!spec_updateGS (lang_markov Λ) Σ, !diffprivWpGS Λ Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  Global Instance frame_wp p E e R Φ Ψ s :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Ψ }}) | 2.
  Proof. rewrite /Frame=> HR. rewrite wp_frame_l. apply wp_mono, HR. Qed.

  Global Instance is_except_0_wp E e Φ s : IsExcept0 (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_wp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_wp p E e P Φ s :
    ElimModal True p false (|==> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r wand_elim_r fupd_wp.
  Qed.

  Global Instance elim_modal_fupd_wp p E e P Φ s :
    ElimModal True p false (|={E}=> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_wp.
  Qed.

  Global Instance elim_modal_fupd_wp_atomic p E1 E2 e P Φ s :
    ElimModal (Atomic StronglyAtomic e) p false
            (|={E1,E2}=> P) P
            (WP e @ s; E1 {{ Φ }}) (WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }})%I | 100.
  Proof.
    intros ?. rewrite intuitionistically_if_elim fupd_frame_r wand_elim_r wp_atomic //.
  Qed.

  Global Instance add_modal_fupd_wp E e P Φ s :
    AddModal (|={E}=> P) P (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_wp. Qed.

  Global Instance elim_acc_wp_atomic {X} E1 E2 α β γ e Φ s :
    ElimAcc (X:=X) (Atomic StronglyAtomic e)
            (fupd E1 E2) (fupd E2 E1)
            α β γ (WP e @ s; E1 {{ Φ }})
            (λ x, WP e @ s; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I | 100.
  Proof.
    iIntros (?) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_wp_nonatomic {X} E α β γ e Φ s :
    ElimAcc (X:=X) True (fupd E E) (fupd E E)
            α β γ (WP e @ s; E {{ Φ }})
            (λ x, WP e @ s; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply wp_fupd.
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  #[global] Instance elim_modal_spec_update_wp P E e Ψ :
    ElimModal True false false (spec_update E P) P (WP e @ E {{ Ψ }}) (WP e @ E {{ Ψ }}).
  Proof.
    iIntros (?) "[HP Hcnt]".
    iApply spec_update_wp.
    iMod "HP". iModIntro. by iApply "Hcnt".
  Qed.

  #[global] Instance elim_modal_spec_updateN_wp P E n e Ψ :
    ElimModal True false false (spec_updateN n E P) P (WP e @ E {{ Ψ }}) (WP e @ E {{ Ψ }}).
  Proof.
    iIntros (?) "[HP Hcnt]".
    iDestruct (spec_updateN_implies_spec_update with "HP") as "> HP".
    by iApply "Hcnt".
  Qed.

End proofmode_classes.

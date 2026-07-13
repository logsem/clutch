From Stdlib Require Export Reals Psatz.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export lib.fixpoint_mono big_op.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext NNRbar.
From clutch.common Require Export language erasable.
From clutch.base_logic Require Export spec_update.
From clutch.prob Require Export couplings_rdp distribution.

Import uPred.

Local Open Scope R.

Class renyiprivWpGS (Λ : language) (Σ : gFunctors) `{!spec_updateGS (lang_markov Λ) Σ} := RenyiprivWpGS {
  #[global] renyiprivWpGS_invGS :: invGS_gen HasNoLc Σ;

  state_interp : state Λ → iProp Σ;
  err_interp : nonnegreal → nonnegreal -> iProp Σ;
}.
Global Opaque renyiprivWpGS_invGS.
Global Arguments RenyiprivWpGS {Λ Σ _}.

Canonical Structure NNRO := leibnizO nonnegreal.
(* TODO: move *)
#[global] Hint Resolve cond_nonneg : core.

(** * Coupling modalities  *)
Section coupl_modalities.
  Context `{!spec_updateGS (lang_markov Λ) Σ, !renyiprivWpGS Λ Σ}.

  (** ** [spec_coupl]  *)

  (** The [spec_coupl] modality allows us to (optionally) prepend spec execution steps and erasable
      distributions, e.g. [state_step]s on both sides. *)
  Definition spec_coupl_pre E Z (Φ : state Λ * cfg Λ * nonnegreal * nonnegreal → iProp Σ) :
    state Λ * cfg Λ * nonnegreal * nonnegreal → iProp Σ :=
    (λ (x : state Λ * cfg Λ * nonnegreal * nonnegreal),
      let '(σ1, (e1', σ1'), α , ρ) := x in
      (Z σ1 e1' σ1' α ρ) ∨
      (∃ (S : state Λ → cfg Λ → Prop) (n : nat) (μ1 : distr (state Λ)) (μ1' : distr (state Λ))
         (ρ1 : nonnegreal) (ρ2 : nonnegreal),
         ⌜RDPcoupl μ1 (σ2' ← μ1'; pexec n (e1', σ2')) S α ρ1⌝ ∗
         ⌜(ρ1 + ρ2) <= ρ⌝ ∗
         ⌜erasable μ1 σ1⌝ ∗
         (* TODO: Consider rewritable *)
         ⌜erasable μ1' σ1'⌝ ∗
         ∀ σ2 e2' σ2', ⌜S σ2 (e2', σ2')⌝ ={E}=∗ Φ (σ2, (e2', σ2'), α, ρ2)))%I.

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
    iIntros ((((σ1 & e1' & σ1') & α) & ρ))
      "[? | (% & % & % & % & % & % & % & % & % & % & H)]".
    - iLeft. done.
    - iRight.
      repeat iExists _.
      repeat (iSplit; [done|]).
      iIntros (????). iApply "Hwand". by iApply "H".
  Qed.

  Implicit Type α ρ: nonnegreal.

  Definition spec_coupl' E Z := bi_least_fixpoint (spec_coupl_pre E Z).
  Definition spec_coupl E σ e' σ' α ρ Z := spec_coupl' E Z (σ, (e', σ'), α, ρ).

  Lemma spec_coupl_unfold E σ1 e1' σ1' α ρ Z :
    spec_coupl E σ1 e1' σ1' α ρ Z ≡
      ((Z σ1 e1' σ1' α ρ) ∨
      (∃ (S : state Λ → cfg Λ → Prop) (n : nat) (μ1 : distr (state Λ)) (μ1' : distr (state Λ))
         ρ1 ρ2,
         ⌜RDPcoupl μ1 (σ2' ← μ1'; pexec n (e1', σ2')) S α ρ1⌝ ∗
         ⌜ρ1 + ρ2 <= ρ⌝ ∗
         ⌜erasable μ1 σ1⌝ ∗ ⌜erasable μ1' σ1'⌝ ∗
         ∀ σ2 e2' σ2', ⌜S σ2 (e2', σ2')⌝ ={E}=∗ spec_coupl E σ2 e2' σ2' α ρ2 Z))%I.
  Proof. rewrite /spec_coupl /spec_coupl' least_fixpoint_unfold //. Qed.

  Lemma spec_coupl_ret E σ1 e1' σ1' Z α ρ:
    Z σ1 e1' σ1' α ρ -∗ spec_coupl E σ1 e1' σ1' α ρ Z.
  Proof. iIntros. rewrite spec_coupl_unfold. by iLeft. Qed.

  Lemma spec_coupl_rec σ1 e1' σ1' E α ρ Z :
    (∃ (S : state Λ → cfg Λ → Prop) (n : nat) (μ1 : distr (state Λ)) (μ1' : distr (state Λ))
       ρ1 ρ2,
       ⌜RDPcoupl μ1 (σ2' ← μ1'; pexec n (e1', σ2')) S α ρ1⌝ ∗
        ⌜ρ1 + ρ2 <= ρ⌝ ∗
       ⌜erasable μ1 σ1⌝ ∗ ⌜erasable μ1' σ1'⌝ ∗
       ∀ σ2 e2' σ2', ⌜S σ2 (e2', σ2')⌝ ={E}=∗ spec_coupl E σ2 e2' σ2' α ρ2 Z)%I
    ⊢ spec_coupl E σ1 e1' σ1' α ρ Z.
  Proof. iIntros "H". rewrite spec_coupl_unfold. iRight. done. Qed.

  Lemma spec_coupl_ind E (Ψ Z : state Λ → expr Λ → state Λ → nonnegreal → nonnegreal -> iProp Σ) :
    ⊢ (□ (∀ σ e' σ' α ρ,
             spec_coupl_pre E Z (λ '(σ, (e', σ'), α', ρ'),
                 Ψ σ e' σ' α' ρ' ∧ spec_coupl E σ e' σ' α' ρ' Z)%I (σ, (e', σ'), α,  ρ) -∗ Ψ σ e' σ' α ρ) →
       ∀ σ e' σ' α ρ, spec_coupl E σ e' σ' α ρ Z -∗ Ψ σ e' σ' α ρ)%I.
  Proof.
    iIntros "#IH" (σ e' σ' α ρ) "H".
    set (Ψ' := (λ '(σ, (e', σ'), α, ρ), Ψ σ e' σ' α ρ) :
           (prodO (prodO (prodO (stateO Λ) (prodO (exprO Λ) (stateO Λ))) NNRO) NNRO) → iProp Σ).
    assert (NonExpansive Ψ').
    { intros n [[[σ1 [e1' σ1']] α1] ρ1] [[[σ2 [e2' σ2']] α2] ρ2].
      intros (([[=] ([=] & [=])] & [=]) & [=]).
      by simplify_eq/=. }
    iApply (least_fixpoint_ind _ Ψ' with "[] H").
    iIntros "!#" ([[[? [??]] ?] ?]) "H". by iApply "IH".
  Qed.

  Lemma fupd_spec_coupl E σ1 e1' σ1' Z α ρ :
    (|={E}=> spec_coupl E σ1 e1' σ1' α ρ Z) ⊢ spec_coupl E σ1 e1' σ1' α ρ Z.
  Proof.
    iIntros "H".
    iApply spec_coupl_rec.
    iExists (λ σ2 c, σ2 = σ1 ∧ c = (e1', σ1')), 0%nat,
      (dret σ1), (dret σ1'), 0%NNR, ρ.
    rewrite dret_id_left pexec_O.
    iSplit; [iPureIntro|].
    { apply RDPcoupl_dret'; [simpl; lra|done]. }
    iSplit; [iPureIntro; simpl; lra|].
    do 2 (iSplit; [iPureIntro; apply dret_erasable|]).
    by iIntros (??? (-> & [= -> ->])).
  Qed.

  Lemma spec_coupl_mono E1 E2 σ1 e1' σ1' Z1 Z2 α ρ :
    E1 ⊆ E2 →
    (∀ σ2 e2' σ2' α' ρ', Z1 σ2 e2' σ2' α' ρ' -∗ Z2 σ2 e2' σ2' α' ρ') -∗
    spec_coupl E1 σ1 e1' σ1' α ρ Z1 -∗ spec_coupl E2 σ1 e1' σ1' α ρ Z2.
  Proof.
    iIntros (HE) "HZ Hs".
    iRevert "HZ".
    iRevert (σ1 e1' σ1' α ρ) "Hs".
    iApply spec_coupl_ind.
    iIntros "!#" (σ e' σ' α ρ)
      "[? | (% & % & % & % & % & % & % & % & % & % & H)] Hw".
    - iApply spec_coupl_ret. by iApply "Hw".
    - iApply spec_coupl_rec.
      repeat iExists _.
      do 4 (iSplit; [done|]).
      iIntros (????).
      iApply fupd_mask_mono; [done|].
      iMod ("H" with "[//]") as "[IH _]".
      by iApply "IH".
  Qed.

  Lemma spec_coupl_mono_err_1 α ρ1 ρ2 E σ1 e1' σ1' Z :
    ρ1 <= ρ2 → spec_coupl E σ1 e1' σ1' α ρ1 Z -∗ spec_coupl E σ1 e1' σ1' α ρ2 Z.
  Proof.
    iIntros (Hle) "Hs".
    iApply spec_coupl_rec.
    iExists (λ σ2 c, σ2 = σ1 ∧ c = (e1', σ1')), 0%nat,
      (dret σ1), (dret σ1'), 0%NNR, ρ1.
    rewrite dret_id_left pexec_O.
    iSplit; [iPureIntro|].
    { apply RDPcoupl_dret'; [simpl; lra|done]. }
    iSplit; [iPureIntro; simpl; lra|].
    do 2 (iSplit; [iPureIntro; apply dret_erasable|]).
    iIntros (??? (-> & [= -> ->])) "!>".
    done.
  Qed.


  Lemma spec_coupl_bind E1 E2 σ1 e1' σ1' Z1 Z2 α ρ :
    E1 ⊆ E2 →
    (∀ σ2 e2' σ2' α' ρ', Z1 σ2 e2' σ2' α' ρ' -∗ spec_coupl E2 σ2 e2' σ2' α' ρ' Z2) -∗
    spec_coupl E1 σ1 e1' σ1' α ρ Z1 -∗
    spec_coupl E2 σ1 e1' σ1' α ρ Z2.
  Proof.
    iIntros (HE) "HZ Hs".
    iRevert "HZ".
    iRevert (σ1 e1' σ1' α ρ) "Hs".
    iApply spec_coupl_ind.
    iIntros "!#" (σ e' σ' α ρ)
      "[H | (%R & %n & %μ1 & %μ1' & %ρ1' & %ρ2' & % & % & % & % & H)] HZ".
    - iApply ("HZ" with "H").
    - iApply spec_coupl_rec.
      iExists R, n, μ1, μ1', ρ1', ρ2'.
      do 4 (iSplit; [done|]).
      iIntros (????).
      iMod (fupd_mask_subseteq E1) as "Hclose"; [done|].
      iMod ("H" with "[//]") as "[H _]".
      iMod "Hclose".
      by iApply "H".
  Qed.

  Lemma spec_coupl_erasables R μ1 μ1' α ρ1 ρ2 ρ E σ1 e1' σ1' Z :
    ρ = (ρ1 + ρ2)%NNR →
    RDPcoupl μ1 μ1' R α ρ1 →
    erasable μ1 σ1 →
    erasable μ1' σ1' →
    (∀ σ2 σ2', ⌜R σ2 σ2'⌝ ={E}=∗ spec_coupl E σ2 e1' σ2' α ρ2 Z)
    ⊢ spec_coupl E σ1 e1' σ1' α ρ Z.
  Proof.
    iIntros (-> Hcpl Hμ1 Hμ1') "H".
    iApply spec_coupl_rec.
    iExists (λ σ2 c, ∃ σ2', R σ2 σ2' ∧ c = (e1', σ2')), 0%nat,
      μ1, μ1', ρ1, ρ2.
    iSplit; [iPureIntro|].
    { setoid_rewrite pexec_O.
      by apply RDPcoupl_dmap_r. }
    iSplit; [iPureIntro; simpl; lra|].
    do 2 (iSplit; [done|]).
    iIntros (σ2 e2' σ2' (σ & HR & [= -> ->])).
    by iApply "H".
  Qed.

  Lemma spec_coupl_erasable_steps n R μ1 α ρ1 ρ2 ρ E σ1 e1' σ1' Z :
    ρ = (ρ1 + ρ2)%NNR →
    RDPcoupl μ1 (pexec n (e1', σ1')) R α ρ1 →
    erasable μ1 σ1 →
    (∀ σ2 e2' σ2', ⌜R σ2 (e2', σ2')⌝ ={E}=∗ spec_coupl E σ2 e2' σ2' α ρ2 Z)
      ⊢ spec_coupl E σ1 e1' σ1' α ρ Z.
  Proof.
    iIntros (-> Hcpl Hμ1) "H".
    iApply spec_coupl_rec.
    iExists R, n, μ1, (dret σ1'), ρ1, ρ2.
    rewrite dret_id_left.
    iSplit; [done|].
    iSplit; [iPureIntro; simpl; lra|].
    iSplit; [done|].
    iSplit; [iPureIntro; apply dret_erasable|].
    done.
  Qed.

  Lemma spec_coupl_steps n α ρ1 ρ2 ρ R E σ1 e1' σ1' Z :
    ρ = (ρ1 + ρ2)%NNR →
    RDPcoupl (dret σ1) (pexec n (e1', σ1')) R α ρ1 →
    (∀ σ2 e2' σ2', ⌜R σ2 (e2', σ2')⌝ ={E}=∗ spec_coupl E σ2 e2' σ2' α ρ2 Z)
      ⊢ spec_coupl E σ1 e1' σ1' α ρ Z.
  Proof.
    iIntros (-> Hcpl) "H".
    iApply (spec_coupl_erasable_steps n R (dret σ1) α ρ1 ρ2);
      [done|done|apply dret_erasable|].
    done.
  Qed.

  Lemma spec_coupl_steps_det n α ρ σ1 e1' σ1' e2' σ2' Z E :
    pexec n (e1', σ1') (e2', σ2') = 1 →
    spec_coupl E σ1 e2' σ2' α ρ Z ⊢
      spec_coupl E σ1 e1' σ1' α ρ Z.
  Proof.
    iIntros (Hexec%pmf_1_eq_dret) "H".
    iApply (spec_coupl_steps n α 0%NNR ρ ρ
              (λ σ2 c, σ2 = σ1 ∧ c = (e2', σ2'))).
    { apply nnreal_ext => /=. lra. }
    { rewrite Hexec.
      apply RDPcoupl_dret'; [simpl; lra|done]. }
    iIntros (??? (-> & [= -> ->])) "!>".
    done.
  Qed.

  Lemma spec_coupl_step α ρ E σ1 e1' σ1' Z :
    1 <= α →
    reducible (e1', σ1') →
    (∀ e2' σ2', ⌜prim_step e1' σ1' (e2', σ2') > 0%R⌝ ={E}=∗ spec_coupl E σ1 e2' σ2' α ρ Z)
      ⊢ spec_coupl E σ1 e1' σ1' α ρ Z.
  Proof.
    iIntros (Hα Hred) "H".
    iApply (spec_coupl_steps 1 α 0%NNR ρ ρ
              (λ σ2 c, σ2 = σ1 ∧ 0 < prim_step e1' σ1' c)).
    { apply nnreal_ext => /=. lra. }
    { rewrite pexec_1 step_or_final_no_final; [|by apply reducible_not_final].
      apply RDPcoupl_dret_trivial; [done|apply cond_nonneg|].
      by apply prim_step_mass. }
    iIntros (??? (-> & ?)).
    by iApply "H".
  Qed.



  Definition prog_coupl e1 σ1 e1' σ1' α ρ Z : iProp Σ :=
    ∃ (R : cfg Λ → cfg Λ → Prop) (n : nat) (μ1' : distr (state Λ))
      ρ1 ρ2,
      ⌜reducible (e1, σ1)⌝ ∗
      ⌜RDPcoupl (prim_step e1 σ1) (σ2' ← μ1'; pexec n (e1', σ2')) R α ρ1⌝ ∗
      ⌜ρ1 + ρ2 <= ρ⌝ ∗
      ⌜erasable μ1' σ1'⌝ ∗
      ∀ e2 σ2 e2' σ2', ⌜R (e2, σ2) (e2', σ2')⌝ ={∅}=∗ Z e2 σ2 e2' σ2' α ρ2.

  Lemma prog_coupl_strong_mono e1 σ1 e1' σ1' Z1 Z2 α ρ :
    (∀ e2 σ2 e2' σ2' α' ρ', ⌜∃ σ, prim_step e1 σ (e2, σ2) > 0⌝ ∗ Z1 e2 σ2 e2' σ2' α' ρ' -∗ Z2 e2 σ2 e2' σ2' α' ρ') -∗
    prog_coupl e1 σ1 e1' σ1' α ρ Z1 -∗ prog_coupl e1 σ1 e1' σ1' α ρ Z2.
  Proof.
    iIntros "Hm (%R & %n & %μ1' & %ρ1 & %ρ2 & %Hred & %Hcpl & %Hle & %Hμ1' & Hcnt) /=".
    iExists _, n, μ1', ρ1, ρ2.
    iSplit; [done|].
    iSplit.
    { iPureIntro. apply RDPcoupl_pos_R; [apply cond_nonneg|done]. }
    do 2 (iSplit; [done|]).
    iIntros (e2 σ2 e2' σ2' (HR & Hprim & ?)).
    iMod ("Hcnt" with "[//]") as "HZ1".
    iModIntro.
    iApply "Hm".
    iSplitR; [by iExists _|done].
  Qed.

  Lemma prog_coupl_mono e1 σ1 e1' σ1' Z1 Z2 α ρ:
    (∀ e2 σ2 e2' σ2' α' ρ', Z1 e2 σ2 e2' σ2' α' ρ' -∗ Z2 e2 σ2 e2' σ2' α' ρ') -∗
    prog_coupl e1 σ1 e1' σ1' α ρ Z1 -∗ prog_coupl e1 σ1 e1' σ1' α ρ Z2.
  Proof.
    iIntros "Hm".
    iApply prog_coupl_strong_mono.
    iIntros (??????) "[_ H]". by iApply "Hm".
  Qed.

  Lemma prog_coupl_strengthen e1 σ1 e1' σ1' Z α ρ:
    prog_coupl e1 σ1 e1' σ1' α ρ Z -∗
    prog_coupl e1 σ1 e1' σ1' α ρ (λ e2 σ2 e2' σ2' α' ρ', ⌜∃ σ, prim_step e1 σ (e2, σ2) > 0⌝ ∧ Z e2 σ2 e2' σ2' α' ρ').
  Proof.
    iApply prog_coupl_strong_mono. iIntros (??????) "[$ $]".
  Qed.

  Lemma prog_coupl_ctx_bind K `{!LanguageCtx K} e1 σ1 e1' σ1' Z α ρ:
    to_val e1 = None →
    prog_coupl e1 σ1 e1' σ1' α ρ (λ e2, Z (K e2)) -∗ prog_coupl (K e1) σ1 e1' σ1' α ρ Z.
  Proof.
    iIntros (Hv) "(%R & %n & %μ1' & %ρ1 & %ρ2 & %Hred & %Hcpl & %Hle & %Hμ1' & Hcnt) /=".
    rewrite /prog_coupl.
    iExists (λ ρa c, ∃ ρa', R ρa' c ∧ ρa = fill_lift K ρa'), n, μ1', ρ1, ρ2.
    iSplit; [eauto using reducible_fill|].
    iSplit.
    { iPureIntro.
      rewrite fill_dmap //.
      by apply RDPcoupl_dmap_l. }
    do 2 (iSplit; [done|]).
    iIntros (e2 σ2 e2' σ2' ([e3 σ3] & HR & [= -> ->])).
    by iApply "Hcnt".
  Qed.

  Lemma prog_coupl_steps α ρ1 ρ2 ρ R e1 σ1 e1' σ1' Z :
    ρ = (ρ1 + ρ2)%NNR →
    reducible (e1, σ1) →
    reducible (e1', σ1') →
    RDPcoupl (prim_step e1 σ1) (prim_step e1' σ1') R α ρ1 →
    (∀ e2 σ2 e2' σ2', ⌜R (e2, σ2) (e2', σ2')⌝ ={∅}=∗ Z e2 σ2 e2' σ2' α ρ2)
      ⊢ prog_coupl e1 σ1 e1' σ1' α ρ Z.
  Proof.
    iIntros (-> Hred Hred' Hcpl) "Hcnt".
    iExists R, 1%nat, (dret σ1'), ρ1, ρ2.
    rewrite dret_id_left pexec_1.
    rewrite step_or_final_no_final; [|by apply reducible_not_final].
    do 2 (iSplit; [done|]).
    iSplit; [iPureIntro; simpl; lra|].
    iSplit; [iPureIntro; apply dret_erasable|].
    done.
  Qed.

  Lemma prog_coupl_step_l_erasable ρ2 ρ1 μ1' α ρ R e1 σ1 e1' σ1' Z :
    ρ = (ρ1 + ρ2)%NNR →
    reducible (e1, σ1) →
    RDPcoupl (prim_step e1 σ1) μ1' R α ρ1  →
    erasable μ1' σ1' →
    (∀ e2 σ2 σ2', ⌜R (e2, σ2) σ2'⌝ ={∅}=∗ Z e2 σ2 e1' σ2' α ρ2)
    ⊢ prog_coupl e1 σ1 e1' σ1' α ρ Z.
  Proof.
    iIntros (-> Hred Hcpl Hμ1') "Hcnt".
    iExists (λ ρa c, ∃ σ2', R ρa σ2' ∧ c = (e1', σ2')), 0%nat, μ1', ρ1, ρ2.
    iSplit; [done|].
    iSplit.
    { iPureIntro.
      setoid_rewrite pexec_O.
      by apply RDPcoupl_dmap_r. }
    iSplit; [iPureIntro; simpl; lra|].
    iSplit; [done|].
    iIntros (e2 σ2 e2' σ2' (σ & HR & [= -> ->])).
    by iApply "Hcnt".
  Qed.

  Lemma prog_coupl_step_l_dret ρ2 ρ1 ρ α R e1 σ1 e1' σ1' Z :
    ρ = (ρ1 + ρ2)%NNR →
    reducible (e1, σ1) →
    RDPcoupl (prim_step e1 σ1) (dret σ1') R α ρ1 →
    (∀ e2 σ2, ⌜R (e2, σ2) σ1'⌝ ={∅}=∗ Z e2 σ2 e1' σ1' α ρ2)
    ⊢ prog_coupl e1 σ1 e1' σ1' α ρ Z.
  Proof.
    iIntros (-> Hred Hcpl) "Hcnt".
    iApply (prog_coupl_step_l_erasable _ _ (dret σ1'));
      [done|done| |apply dret_erasable|].
    { apply RDPcoupl_pos_R; [apply cond_nonneg|done]. }
    iIntros (e2 σ2 σ2' (HR & ? & ->%dret_pos)).
    by iApply "Hcnt".
  Qed.

  Lemma prog_coupl_step_l e1 σ1 e1' σ1' α ρ Z :
    reducible (e1, σ1) →
    (∀ e2 σ2, ⌜prim_step e1 σ1 (e2, σ2) > 0⌝ ={∅}=∗ Z e2 σ2 e1' σ1' α ρ)
    ⊢ prog_coupl e1 σ1 e1' σ1' α ρ Z.
  Proof.
    iIntros (Hred) "Hcnt".
    iApply (prog_coupl_step_l_dret ρ 0%NNR).
    { apply nnreal_ext => /=. lra. }
    { done. }
    { apply RDPcoupl_trivial_dret_r; [apply cond_nonneg|].
      by apply prim_step_mass. }
    iIntros (e2 σ2 (Hpos & _)).
    by iApply "Hcnt".
  Qed.

  Lemma prog_coupl_reducible e e' σ σ' Z α ρ :
    prog_coupl e σ e' σ' α ρ Z -∗ ⌜reducible (e, σ)⌝.
  Proof. by iIntros "(% & % & % & % & % & $ & ?)". Qed.

End coupl_modalities.

(** * The weakest precondition  *)
Definition wp_pre `{!spec_updateGS (lang_markov Λ) Σ, !renyiprivWpGS Λ Σ}
    (wp : coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
     coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
  (∀ σ1 e1' σ1' α1 ρ1,
      state_interp σ1 ∗ spec_interp (e1', σ1') ∗ err_interp α1 ρ1 ={E, ∅}=∗
      spec_coupl ∅ σ1 e1' σ1' α1 ρ1 (λ σ2 e2' σ2' α2 ρ2,
        match to_val e1 with
        | Some v => |={∅, E}=> state_interp σ2 ∗ spec_interp (e2', σ2') ∗ err_interp α2 ρ2 ∗ Φ v
        | None =>
            prog_coupl e1 σ2 e2' σ2' α2 ρ2 (λ e3 σ3 e3' σ3' α3 ρ3,
                ▷ spec_coupl ∅ σ3 e3' σ3' α3 ρ3 (λ σ4 e4' σ4' α4 ρ4,
                    |={∅, E}=> state_interp σ4 ∗ spec_interp (e4', σ4') ∗ err_interp α4 ρ4 ∗ wp E e3 Φ))
      end))%I.

Local Instance wp_pre_contractive `{!spec_updateGS (lang_markov Λ) Σ, !renyiprivWpGS Λ Σ} :
  Contractive wp_pre.
Proof.
  rewrite /wp_pre /= => n wp wp' Hwp E e1 Φ.
  do 12 f_equiv.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [? ?]. rewrite /spec_coupl_pre.
  do 4 f_equiv.
  rewrite /prog_coupl.
  do 25 f_equiv.
  f_contractive.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [[[? [? ?]] ?] ?]. rewrite /spec_coupl_pre.
  do 5 f_equiv.
  apply Hwp.
Qed.

Local Definition wp_def `{!spec_updateGS (lang_markov Λ) Σ, !renyiprivWpGS Λ Σ} :
  Wp (iProp Σ) (expr Λ) (val Λ) () :=
  {| wp := λ _ : (), fixpoint (wp_pre); wp_default := () |}.
Local Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp' := wp_aux.(unseal).
Global Arguments wp' {Λ Σ _}.
Global Existing Instance wp'.
Local Lemma wp_unseal `{!spec_updateGS (lang_markov Λ) Σ, !renyiprivWpGS Λ Σ} : wp =
  (@wp_def Λ Σ _ _).(wp).
Proof. rewrite -wp_aux.(seal_eq) //. Qed.

Section wp.
Context `{!spec_updateGS (lang_markov Λ) Σ, !renyiprivWpGS Λ Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.

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
  do 29 f_equiv.
  f_contractive_fin.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [[[? [? ?]] ?] ?]. rewrite /spec_coupl_pre.
  do 5 f_equiv.
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
  do 28 f_equiv.
  f_contractive.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [[[? [? ?]] ?] ?]. rewrite /spec_coupl_pre.
  do 5 f_equiv.
  apply wp_ne.
  intros v. apply HΦ.
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
 (∀ σ1 e1' σ1' α1 ρ1 v,
     state_interp σ1 ∗ spec_interp (e1', σ1') ∗ err_interp α1 ρ1 ∗ Φ v -∗
     spec_coupl ∅ σ1 e1' σ1' α1 ρ1 (λ σ2 e2' σ2' α2 ρ2,
          |={E2}=> state_interp σ2 ∗ spec_interp (e2', σ2') ∗ err_interp α2 ρ2 ∗ Ψ v)) -∗
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
  (∀ σ ρ v α ρ',
      state_interp σ ∗ spec_interp ρ ∗ err_interp α ρ' ∗ Φ v ={E2}=∗
      state_interp σ ∗ spec_interp ρ ∗ err_interp α ρ' ∗ Ψ v) -∗
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
  iDestruct (prog_coupl_strengthen with "H") as "H".
  iApply (prog_coupl_mono with "[] H").
  iIntros (??????) "[[% %Hstep] H] !>".
  iApply (spec_coupl_bind with "[] H"); [done|].
  iIntros (?????) "H".
  iApply fupd_spec_coupl.
  iMod "H" as "(Hσ & Hρ & Hε & H)".
  rewrite !wp_unfold /wp_pre.
  destruct (to_val e2) as [v2|] eqn:He2.
  + iMod ("H" with "[$]") as "H". iModIntro.
    iApply (spec_coupl_mono with "[] H"); [done|].
    iIntros (?????) "> ($ & $ & $ & >H)".
    rewrite -(of_to_val e2 v2) //.
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
  iApply prog_coupl_ctx_bind; [done|].
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
  Context `{!spec_updateGS (lang_markov Λ) Σ, !renyiprivWpGS Λ Σ}.
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
From Coq Require Export Reals Psatz.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export fixpoint big_op.
From iris.prelude Require Import options.
From iris.algebra Require Import ofe.

From mathcomp.analysis Require Import measure.

From clutch.prelude Require Import stdpp_ext iris_ext NNRbar.
From clutch.meas_lang Require Export language erasable.
From clutch.meas_lang Require Export meas_spec_update.
From clutch.prob.monad Require Export couplings_app.
From clutch.bi Require Export weakestpre.
(*  From clutch.prob Require Export couplings_app distribution. *)
From Coq Require Import ssrfun.


From mathcomp.analysis Require Import reals measure lebesgue_measure lebesgue_integral sequences function_spaces Rstruct.
From clutch.prob.monad Require Import prelude giry.
From stdpp Require Import base.
From Coq Require Import Reals.

From mathcomp.analysis Require Import constructive_ereal.


Import uPred.

Local Open Scope R.

Class micrometerWpGS (Λ : meas_language) (Σ : gFunctors) `{!meas_spec_updateGS (meas_lang_markov Λ) Σ} := MicrometerWpGS {
  #[global] micrometerWpGS_invGS :: invGS_gen HasNoLc Σ;

  state_interp : state Λ → iProp Σ;
  err_interp : nonnegreal → iProp Σ;
}.
Global Opaque micrometerWpGS_invGS.
Global Arguments MicrometerWpGS {Λ Σ _}.

Canonical Structure NNRO := leibnizO nonnegreal.

(** * Coupling modalities  *)
Section coupl_modalities.
  Context `{!meas_spec_updateGS (meas_lang_markov Λ) Σ, !micrometerWpGS Λ Σ}.

  (** ** [meas_spec_coupl]  *)

  (** The [meas_spec_coupl] modality allows us to (optionally) prepend spec execution steps and erasable
      distributions, e.g. [state_step]s on both sides. *)

  (*
 HB.lock Definition expectation {d} {T : measurableType d} {R : realType}
  (P : probability T R) (X : T -> R) := (\int[P]_w (X w)%:E)%E.
*)

  Definition coe_nonnegreal_bar_R : nonnegreal -> \bar R := EFin \o nonneg.

  (* NOTE: le_ereal due to Scope clash with expressions. Move expval to its own file where this isn't the case. *)


  Definition meas_spec_coupl_pre (E : coPset)
      (Z : stateO Λ -> exprO Λ -> stateO Λ -> NNRO -> iProp Σ) (Φ : stateO Λ * (exprO Λ * stateO Λ) * NNRO → iProp Σ) :
      (stateO Λ) * (exprO Λ * stateO Λ) * NNRO → iProp Σ :=
    (λ (x : stateO Λ * (exprO Λ * stateO Λ) * NNRO),
       let '(σ1, (e1', σ1'), ε) := x in
       ⌜1 <= ε⌝ ∨
       (Z σ1 e1' σ1' ε) ∨
      (∃ (S : state Λ → cfg Λ → Prop) (n : nat) (μ1 : giryM (state Λ)) (μ1' : giryM (state Λ))
         (ε1 : nonnegreal) (X2 : cfg Λ → nonnegreal) (r : R),
           ⌜ ARcoupl_meas μ1 (gBind' (pexec n \o pair e1') μ1') S (0)%R  (coe_nonnegreal_bar_R ε1) ⌝ ∗
           ⌜∀ ρ, X2 ρ <= r⌝ ∗
           ⌜ (le_ereal (EFin (nonneg ε1)) (\int[gBind' (pexec n \o pair e1') μ1']_ρ (EFin (nonneg (X2 ρ))))) ⌝ ∗
           ⌜erasable μ1 σ1⌝ ∗
           ⌜erasable μ1' σ1'⌝ ∗
           ∀ σ2 e2' σ2', ⌜S σ2 (e2', σ2')⌝ ={E}=∗ Φ (σ2, (e2', σ2'), X2 (e2', σ2'))))%I.

  #[local] Instance meas_spec_coupl_pre_ne Z E Φ :
    NonExpansive (meas_spec_coupl_pre E Z Φ).
  Proof.
    rewrite /meas_spec_coupl_pre.
    intros ? ((?&?&?) & ?) ((?&?&?) & ?) ([[=] ([=] & [=])] & [=]).
    by simplify_eq/=.
  Qed.

  #[local] Instance meas_spec_coupl_pre_mono Z E : BiMonoPred (meas_spec_coupl_pre Z E).
  Proof.
    split; [|apply _].
    iIntros (Φ Ψ HNEΦ HNEΨ) "#Hwand".
    iIntros (((σ1 & e1' & σ1') & ε))
      "[H | [? | (% & % & % & % & % & % & % & % & % & % & % & % & H)]]".
    - iLeft. done.
    - iRight. iLeft. done.
    - iRight. iRight.
      repeat iExists _.
      repeat (iSplit; [done|]).
      iIntros (????). iApply "Hwand". by iApply "H".
  Qed.

  Implicit Type ε : NNRO.

  Definition meas_spec_coupl' (E : coPset) (Z : stateO Λ -> exprO Λ -> stateO Λ -> NNRO -> iProp Σ) :
      stateO Λ * (exprO Λ * stateO Λ) * NNRO → iProp Σ :=
    bi_least_fixpoint (meas_spec_coupl_pre E Z).

  Definition meas_spec_coupl E σ e' σ' ε Z := meas_spec_coupl' E Z (σ, (e', σ'), ε).

  Lemma meas_spec_coupl_unfold E σ1 e1' σ1' ε Z :
    meas_spec_coupl E σ1 e1' σ1' ε Z ≡
      (⌜1 <= ε⌝ ∨
      (Z σ1 e1' σ1' ε) ∨
      (∃ (S : state Λ → cfg Λ → Prop) (n : nat) (μ1 : giryM (state Λ)) (μ1' : giryM  (state Λ))
         (ε1 : nonnegreal) (X2 : cfg Λ → nonnegreal) (r : R),
         ⌜ARcoupl_meas μ1 (gBind' (pexec n \o pair e1') μ1') S (0)%R  (coe_nonnegreal_bar_R ε1) ⌝ ∗
         ⌜∀ ρ, X2 ρ <= r⌝ ∗
         ⌜ (le_ereal (EFin (nonneg ε1)) (\int[gBind' (pexec n \o pair e1') μ1']_ρ (EFin (nonneg (X2 ρ))))) ⌝ ∗
         ⌜erasable μ1 σ1⌝ ∗ ⌜erasable μ1' σ1'⌝ ∗
         ∀ σ2 e2' σ2', ⌜S σ2 (e2', σ2')⌝ ={E}=∗ meas_spec_coupl E σ2 e2' σ2' (X2 (e2', σ2')) Z))%I.
  Proof. rewrite /meas_spec_coupl /meas_spec_coupl' least_fixpoint_unfold //. Qed.

  Lemma meas_spec_coupl_ret_err_ge_1 E σ1 e1' σ1' Z (ε : nonnegreal) :
    1 <= ε → ⊢ meas_spec_coupl E σ1 e1' σ1' ε Z.
  Proof. iIntros. rewrite meas_spec_coupl_unfold. by iLeft. Qed.

  Lemma meas_spec_coupl_ret E σ1 e1' σ1' Z ε :
    Z σ1 e1' σ1' ε -∗ meas_spec_coupl E σ1 e1' σ1' ε Z.
  Proof. iIntros. rewrite meas_spec_coupl_unfold. by iRight; iLeft. Qed.

  Lemma meas_spec_coupl_rec σ1 e1' σ1' E (ε : nonnegreal) Z :
    (∃ (S : state Λ → cfg Λ → Prop) (n : nat) (μ1 : giryM (state Λ)) (μ1' : giryM (state Λ))
       (ε1 : nonnegreal) (X2 : cfg Λ → nonnegreal) (r : R),
       ⌜ARcoupl_meas μ1 (gBind' (pexec n \o pair e1') μ1') S (0)%R  (coe_nonnegreal_bar_R ε1) ⌝ ∗
       ⌜∀ ρ, X2 ρ <= r⌝ ∗
       ⌜ (le_ereal (EFin (nonneg ε1)) (\int[gBind' (pexec n \o pair e1') μ1']_ρ (EFin (nonneg (X2 ρ))))) ⌝ ∗
       ⌜erasable μ1 σ1⌝ ∗ ⌜erasable μ1' σ1'⌝ ∗
       ∀ σ2 e2' σ2', ⌜S σ2 (e2', σ2')⌝ ={E}=∗ meas_spec_coupl E σ2 e2' σ2' (X2 (e2', σ2')) Z)%I
    ⊢ meas_spec_coupl E σ1 e1' σ1' ε Z.
  Proof. iIntros "H". rewrite meas_spec_coupl_unfold. iRight; iRight. done. Qed.

  Lemma meas_spec_coupl_ind E (Ψ Z : state Λ → expr Λ → state Λ → nonnegreal → iProp Σ) :
    ⊢ (□ (∀ σ e' σ' ε,
             meas_spec_coupl_pre E Z (λ '(σ, (e', σ'), ε'),
                 Ψ σ e' σ' ε' ∧ meas_spec_coupl E σ e' σ' ε' Z)%I (σ, (e', σ'), ε) -∗ Ψ σ e' σ' ε) →
       ∀ σ e' σ' ε, meas_spec_coupl E σ e' σ' ε Z -∗ Ψ σ e' σ' ε)%I.
  Proof.
    iIntros "#IH" (σ e' σ' ε) "H".
    set (Ψ' := (λ '(σ, (e', σ'), ε), Ψ σ e' σ' ε) :
           (prodO (prodO (stateO Λ) (prodO (exprO Λ) (stateO Λ))) NNRO) → iProp Σ).
    assert (NonExpansive Ψ').
    { intros n [[σ1 [e1' σ1']] ε1] [[σ2 [e2' σ2']] ε2].
      intros ([[=] ([=] & [=])] & [=]).
      by simplify_eq/=. }
    iApply (least_fixpoint_ind _ Ψ' with "[] H").
    iIntros "!#" ([[? [??]] ?]) "H". by iApply "IH".
  Qed.

  Lemma fupd_meas_spec_coupl E σ1 e1' σ1' Z (ε : nonnegreal) :
    (|={E}=> meas_spec_coupl E σ1 e1' σ1' ε Z) ⊢ meas_spec_coupl E σ1 e1' σ1' ε Z.
  Proof.
    iIntros "H".
    iApply meas_spec_coupl_rec.
    iExists _, 0%nat, (gRet σ1), (gRet σ1'), 0%NNR, (λ _, ε), ε.
  Admitted.
  (*
    rewrite dret_id_left pexec_O.
    iSplit; [iPureIntro|].
    { by apply ARcoupl_pos_R, (ARcoupl_dret _ _ (λ _ _, True)). }
    iSplit; [done|].
    iSplit; [iPureIntro|].
    { rewrite Rplus_0_l Expval_dret //. }
    do 2 (iSplit; [iPureIntro; apply dret_erasable|]).
    by iIntros (??? (_ & ->%dret_pos & [=-> ->]%dret_pos)).
  Qed. *)

  Lemma meas_spec_coupl_mono E1 E2 σ1 e1' σ1' Z1 Z2 ε :
    E1 ⊆ E2 →
    (∀ σ2 e2' σ2' ε', Z1 σ2 e2' σ2' ε' -∗ Z2 σ2 e2' σ2' ε') -∗
    meas_spec_coupl E1 σ1 e1' σ1' ε Z1 -∗ meas_spec_coupl E2 σ1 e1' σ1' ε Z2.
  Proof.
    iIntros (HE) "HZ Hs".
    iRevert "HZ".
    iRevert (σ1 e1' σ1' ε) "Hs".
    iApply meas_spec_coupl_ind.
    iIntros "!#" (σ e' σ' ε)
      "[% | [? | (% & % & % & % & % & % & % & % & % & % & % & % & H)]] Hw".
    - iApply meas_spec_coupl_ret_err_ge_1. lra.
    - iApply meas_spec_coupl_ret. by iApply "Hw".
    - iApply meas_spec_coupl_rec.
      repeat iExists _.
      iSplit; [done|].
      iSplit; [iPureIntro; by etrans|].
      do 3 (iSplit; [done|]).
      iIntros (????).
      iApply fupd_mask_mono; [done|].
      iMod ("H" with "[//]") as "[IH _]".
      by iApply "IH".
  Qed.

  Lemma meas_spec_coupl_mono_err ε1 ε2 E σ1 e1' σ1' Z :
    ε1 <= ε2 → meas_spec_coupl E σ1 e1' σ1' ε1 Z -∗ meas_spec_coupl E σ1 e1' σ1' ε2 Z.
  Proof.
    iIntros (Heps) "Hs".
    iApply meas_spec_coupl_rec.
    set (ε' := nnreal_minus ε2 ε1 Heps).
  Admitted.
  (*
    iExists _, 0%nat, (dret σ1), (dret σ1'), ε', (λ _, ε1), ε1.
    rewrite dret_id_left pexec_O.
    iSplit; [iPureIntro|].
    { eapply ARcoupl_pos_R, ARcoupl_mon_grading,
        (ARcoupl_dret _ _ (λ _ _, True)) => /=; [|done|done]. lra. }
    iSplit; [done|].
    iSplit; [iPureIntro|].
    { rewrite Expval_dret /=. lra. }
    do 2 (iSplit; [iPureIntro; apply dret_erasable|]).
    by iIntros (??? (_ & ->%dret_pos & [=-> ->]%dret_pos)).
  Qed. *)

  Lemma meas_spec_coupl_bind E1 E2 σ1 e1' σ1' Z1 Z2 ε :
    E1 ⊆ E2 →
    (∀ σ2 e2' σ2' ε', Z1 σ2 e2' σ2' ε' -∗ meas_spec_coupl E2 σ2 e2' σ2' ε' Z2) -∗
    meas_spec_coupl E1 σ1 e1' σ1' ε Z1 -∗
    meas_spec_coupl E2 σ1 e1' σ1' ε Z2.
  Proof.
    iIntros (HE) "HZ Hs".
    iRevert "HZ".
    iRevert (σ1 e1' σ1' ε) "Hs".
    iApply meas_spec_coupl_ind.
    iIntros "!#" (σ e' σ' ε)
      "[% | [H | (%R & %n & %μ1 & %μ1' & %ε1' & %X2 & %r & % & % & % & % & % & H)]] HZ".
    - by iApply meas_spec_coupl_ret_err_ge_1.
    - iApply ("HZ" with "H").
    - iApply meas_spec_coupl_rec.
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

  Lemma meas_spec_coupl_erasables_exp (X2 : _ → nonnegreal) (r : R) ε1 ε R μ1 μ1' E σ1 e1' σ1' Z :
    ARcoupl_meas μ1 μ1' R (0)%R (EFin (nonneg ε1))  →
    erasable μ1 σ1 →
    erasable μ1' σ1' →
    (∀ ρ, X2 ρ <= r) →
    (le_ereal (EFin (nonneg ε1) + \int[μ1']_x (EFin \o nonneg \o X2 $ x)) (EFin (nonneg ε))) ->
    (∀ σ2 σ2', ⌜R σ2 σ2'⌝ ={E}=∗ meas_spec_coupl E σ2 e1' σ2' (X2 σ2') Z)
    ⊢ meas_spec_coupl E σ1 e1' σ1' ε Z.
  Proof.
    iIntros (???? Hε) "H".
    iApply meas_spec_coupl_rec.
    set X2' := (λ (ρ : cfg Λ), X2 ρ.2).
    iExists (λ σ2 '(e2', σ2'), R σ2 σ2' ∧ e2' = e1'), 0%nat, μ1, μ1', ε1, X2', r.
    iSplit; [iPureIntro|].
  Admitted.
  (*
    { rewrite -(dret_id_right μ1).
      eapply (ARcoupl_dbind' ε1 0%NNR); [done|done|simpl; lra|..|done].
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
  Qed. *)

  Lemma meas_spec_coupl_erasables R μ1 μ1' ε1 ε2 ε E σ1 e1' σ1' Z :
    ε = (ε1 + ε2)%NNR →
    ARcoupl_meas μ1 μ1' R (0)%R (EFin (nonneg ε1)) →
    erasable μ1 σ1 →
    erasable μ1' σ1' →
    (∀ σ2 σ2', ⌜R σ2 σ2'⌝ ={E}=∗ meas_spec_coupl E σ2 e1' σ2' ε2 Z)
    ⊢ meas_spec_coupl E σ1 e1' σ1' ε Z.
  Proof.
    iIntros (-> ???) "H".
    iApply (meas_spec_coupl_erasables_exp (λ _, ε2) ε2); [done|done|done|done| |done].
  Admitted.
  (*
    rewrite Expval_const //=.
    apply Rle_plus_plus; [done|]. real_solver. 
  Qed. *)

  Lemma meas_spec_coupl_erasable_steps n R μ1 ε1 ε2 ε E σ1 e1' σ1' Z :
    ε = (ε1 + ε2)%NNR →
    ARcoupl_meas μ1 (pexec n (e1', σ1')) R (0)%R (EFin (nonneg ε1)) →
    erasable μ1 σ1 →
    (∀ σ2 e2' σ2', ⌜R σ2 (e2', σ2')⌝ ={E}=∗ meas_spec_coupl E σ2 e2' σ2' ε2 Z)
    ⊢ meas_spec_coupl E σ1 e1' σ1' ε Z.
  Proof.
    iIntros (-> ??) "H".
    iApply meas_spec_coupl_rec.
  Admitted.
  (*
    iExists R, n, μ1, (dret σ1'), ε1, (λ _, ε2), ε2.
    rewrite dret_id_left.
    do 2 (iSplit; [done|]).
    iSplit; [iPureIntro|].
    { rewrite Expval_const //.
      apply Rle_plus_plus; [done|].
      real_solver. }
    iSplit; [done|].
    iSplit; [iPureIntro; apply dret_erasable|].
    done.
  Qed. *)

  Lemma meas_spec_coupl_steps n ε2 ε1 ε R E σ1 e1' σ1' Z :
    ε = (ε1 + ε2)%NNR →
    ARcoupl_meas (gRet σ1) (pexec n (e1', σ1')) R (0)%R (EFin (nonneg ε1)) →
    (∀ σ2 e2' σ2', ⌜R σ2 (e2', σ2')⌝ ={E}=∗ meas_spec_coupl E σ2 e2' σ2' ε2 Z)
    ⊢ meas_spec_coupl E σ1 e1' σ1' ε Z.
  Proof.
  Admitted.
  (*
    iIntros (-> ?) "H".
    iApply (meas_spec_coupl_erasable_steps n _ _ ε1 ε2), [done| |apply dret_erasable|].
    { by apply ARcoupl_pos_R. }
    iIntros (??? (? & ->%dret_pos & ?)).
    by iApply "H".
  Qed. *)

  Lemma meas_spec_coupl_steps_det n ε σ1 e1' σ1' e2' σ2' Z E :
    is_det (e2', σ2') (pexec n (e1', σ1')) →
    meas_spec_coupl E σ1 e2' σ2' ε Z ⊢
    meas_spec_coupl E σ1 e1' σ1' ε Z.
  Proof.
  Admitted.
  (*
    iIntros (Hexec%pmf_1_eq_dret) "H".
    iApply (meas_spec_coupl_steps n ε 0%NNR).
    { apply nnreal_ext => /=. lra. }
    { apply ARcoupl_pos_R, ARcoupl_trivial; [solve_distr_mass|].
      rewrite Hexec. solve_distr_mass. }
    rewrite Hexec.
    iIntros (??? (_ & ->%dret_pos & [=-> ->]%dret_pos)).
    done.
  Qed. *)

  (*
      Still not sure about this one

  Lemma meas_spec_coupl_step ε E σ1 e1' σ1' Z :
    reducible (e1', σ1') →
    (∀ e2' σ2', ⌜prim_step e1' σ1' (e2', σ2') > 0%R⌝ ={E}=∗ meas_spec_coupl E σ1 e2' σ2' ε Z)
    ⊢ meas_spec_coupl E σ1 e1' σ1' ε Z.
  Proof.
    iIntros (?) "H".
    iApply (meas_spec_coupl_steps 1 ε 0%NNR).
    { apply nnreal_ext => /=. lra. }
    { rewrite pexec_1 step_or_final_no_final; [|by apply reducible_not_final].
      apply ARcoupl_pos_R, ARcoupl_trivial; [solve_distr_mass|].
      by apply prim_step_mass. }
    iIntros (??? (?&->%dret_pos&?)).
    by iApply "H".
  Qed.

  *)

  (** * [meas_prog_coupl] *)

  (** The [meas_prog_coupl] modality allows us to coupl *exactly* one program step with any number of
      spec execution steps and an erasable distribution *)
  Definition meas_prog_coupl (e1 : exprO Λ) (σ1 : stateO Λ) (e1' : exprO Λ) σ1' (ε : NNRO) Z : iProp Σ :=
    ∃ (R : cfg Λ → cfg Λ → Prop) (n : nat) (μ1' : giryM (state Λ))
      (ε1 : nonnegreal) (X2 : cfg Λ → nonnegreal) (r : nonnegreal),
      ⌜reducible (e1, σ1)⌝ ∗
      ⌜ARcoupl_meas (prim_step (e1, σ1)) (gBind' (pexec n \o pair e1') μ1') R (0)%R  (coe_nonnegreal_bar_R ε1) ⌝ ∗
      ⌜∀ ρ, X2 ρ <= r⌝ ∗
      ⌜ (le_ereal (EFin (nonneg ε1)) (\int[gBind' (pexec n \o pair e1') μ1']_ρ (EFin (nonneg (X2 ρ))))) ⌝ ∗
      ⌜erasable μ1' σ1'⌝ ∗
      ∀ e2 σ2 e2' σ2', ⌜R (e2, σ2) (e2', σ2')⌝ ={∅}=∗ Z e2 σ2 e2' σ2' (X2 (e2, σ2)).

  (*
    Not sure about this one either
  Lemma meas_prog_coupl_strong_mono e1 σ1 e1' σ1' Z1 Z2 ε :
    (∀ e2 σ2 e2' σ2' ε', ⌜∃ σ, prim_step e1 σ (e2, σ2) > 0⌝ ∗ Z1 e2 σ2 e2' σ2' ε' -∗ Z2 e2 σ2 e2' σ2' ε') -∗
    meas_prog_coupl e1 σ1 e1' σ1' ε Z1 -∗ meas_prog_coupl e1 σ1 e1' σ1' ε Z2.
  Proof.
    iIntros "Hm (%R & %n & %μ1' & %ε1 & %X2 & %r & % & % & % & % & % & Hcnt) /=".
    iExists _, _, _, _, _, _.
    iSplit; [done|].
    iSplit.
    { iPureIntro. by apply ARcoupl_pos_R. }
    iFrame "%".
    iIntros (e2 σ2 e2' σ2' (HR & Hprim & ?)).
    iApply "Hm".
    iSplitR; [by iExists _|].
    by iApply "Hcnt".
  Qed.
*)

  Lemma meas_prog_coupl_mono e1 σ1 e1' σ1' Z1 Z2 ε :
    (∀ e2 σ2 e2' σ2' ε', Z1 e2 σ2 e2' σ2' ε' -∗ Z2 e2 σ2 e2' σ2' ε') -∗
    meas_prog_coupl e1 σ1 e1' σ1' ε Z1 -∗ meas_prog_coupl e1 σ1 e1' σ1' ε Z2.
  Proof. Admitted.
  (*
    iIntros "Hm".
    iApply meas_prog_coupl_strong_mono.
    iIntros (?????) "[_ H]". by iApply "Hm".
  Qed.

  Lemma meas_prog_coupl_strengthen e1 σ1 e1' σ1' Z ε :
    meas_prog_coupl e1 σ1 e1' σ1' ε Z -∗
    meas_prog_coupl e1 σ1 e1' σ1' ε (λ e2 σ2 e2' σ2' ε', ⌜∃ σ, prim_step e1 σ (e2, σ2) > 0⌝ ∧ Z e2 σ2 e2' σ2' ε').
  Proof.
    iApply meas_prog_coupl_strong_mono. iIntros (?????) "[$ $]".
  Qed. *)

  Lemma meas_prog_coupl_ctx_bind K `{!LanguageCtx K} e1 σ1 e1' σ1' Z ε:
    to_val e1 = None →
    meas_prog_coupl e1 σ1 e1' σ1' ε (λ e2, Z (K e2)) -∗ meas_prog_coupl (K e1) σ1 e1' σ1' ε Z.
  Proof.
    iIntros (Hv) "(%R & %n & %μ1' & %ε1 & %X2 & %r & % & % & % & % & % & Hcnt) /=".

    (** (classical) inverse of context [K] *)
    destruct (partial_inv_fun K) as (Kinv & HKinv).
    assert (∀ e, Kinv (K e) = Some e) as HKinv3.
    { intro e.
      destruct (Kinv (K e)) eqn:Heq;
        eapply HKinv in Heq; try by simplify_eq. admit.  (* Needs LanguageCtx to be injective *) }
    set (X2' := (λ '(e, σ), from_option (λ e', X2 (e', σ)) 0%NNR (Kinv e))).
    assert (∀ e2 σ2, X2' (K e2, σ2) = X2 (e2, σ2)) as HX2'.
    { intros. rewrite /X2' HKinv3 //. }

    iExists (λ '(e2, σ2) ρ', ∃ e2', e2 = K e2' ∧ R (e2', σ2) ρ'), n, μ1', ε1, X2', r.
    iSplit; [eauto using reducible_fill|].
    1: { admit. }
    iSplit.
    { iPureIntro.
      admit.
      (*
      rewrite fill_dmap //.
      rewrite -(dret_id_right (μ1' ≫= _ )) //.
      rewrite /dmap.
      eapply (ARcoupl_dbind' _ nnreal_zero); [..|done]; [done|done|simpl; lra|..].
      intros [] ?? => /=. apply ARcoupl_dret; [done|]. eauto. *) }
    iSplit; [iPureIntro|].
    { intros [e σ]. simpl. destruct (Kinv e) => //=. admit. }
    iSplit; [iPureIntro|].
    { admit.
      (*
      rewrite fill_dmap // Expval_dmap //=; last first.
      - eapply ex_expval_bounded. intros [] => /=. rewrite HKinv3 //=.
      - etrans; [|done].
        apply Rle_plus_plus; [done|].
        right; apply SeriesC_ext.
        intros [e σ]. rewrite -HX2' //. *) }
    iSplit; [done|].
    iIntros (e2 σ2 e2' σ2' (e3 & -> & HR)).
    rewrite HX2'.
    by iApply "Hcnt".
  Admitted.

  Lemma meas_prog_coupl_steps ε2 ε1 ε R e1 σ1 e1' σ1' Z :
    ε = (ε1 + ε2)%NNR →
    reducible (e1, σ1) →
    reducible (e1', σ1') →
    ARcoupl_meas (prim_step (e1, σ1)) (prim_step (e1', σ1')) R (0)%R (EFin (nonneg ε1)) →
    (∀ e2 σ2 e2' σ2', ⌜R (e2, σ2) (e2', σ2')⌝ ={∅}=∗ Z e2 σ2 e2' σ2' ε2)
    ⊢ meas_prog_coupl e1 σ1 e1' σ1' ε Z.
  Proof.
    iIntros (-> Hred Hred' Hcpl) "Hcnt".
    iExists _, 1%nat, (gRet σ1'), ε1, (λ _, ε2), ε2.
    iSplit; [done|].
  Admitted.
  (*
    rewrite dret_id_left pexec_1.
    rewrite step_or_final_no_final; [|by apply reducible_not_final].
    do 2 (iSplit; [done|]).
    iSplit; [iPureIntro|].
    { rewrite Expval_const //. rewrite prim_step_mass //=. lra. }
    iSplit; [iPureIntro; apply dret_erasable|].
    done.
  Qed. *)

  Lemma meas_prog_coupl_step_l_erasable ε2 ε1 μ1' ε R e1 σ1 e1' σ1' Z :
    ε = (ε1 + ε2)%NNR →
    reducible (e1, σ1) →
    ARcoupl_meas (prim_step (e1, σ1)) μ1' R (0)%R (EFin (nonneg ε1)) →
    erasable μ1' σ1' →
    (∀ e2 σ2 σ2', ⌜R (e2, σ2) σ2'⌝ ={∅}=∗ Z e2 σ2 e1' σ2' ε2)
    ⊢ meas_prog_coupl e1 σ1 e1' σ1' ε Z.
  Proof.
    iIntros (-> ? ? ?) "H".
    iExists (λ ρ2 '(e2', σ2'), R ρ2 σ2' ∧ e2' = e1'), 0%nat, μ1', ε1, (λ _, ε2), ε2.
    iSplit; [done|].
    iSplit; [iPureIntro|].
  Admitted.
  (*
    { setoid_rewrite pexec_O.
      rewrite -(dret_id_right (prim_step _ _)).
      replace ε1 with (ε1 + 0)%NNR; [|apply nnreal_ext; simpl; lra].
      eapply ARcoupl_dbind; [done|done|..|done].
      intros ???. by apply ARcoupl_dret. }        
    iSplit; [done|].
    iSplit; [iPureIntro|].
    { rewrite Expval_const //. rewrite prim_step_mass //=. lra. }
    iSplit; [done|].
    iIntros (e2 σ2 e2' σ2' [? ->]).
    by iApply "H".
  Qed.   *)

  Lemma meas_prog_coupl_step_l_dret ε2 ε1 ε R e1 σ1 e1' σ1' Z :
    ε = (ε1 + ε2)%NNR →
    reducible (e1, σ1) →
    ARcoupl_meas (prim_step (e1, σ1)) (gRet σ1') R (0)%R (EFin (nonneg ε1)) →
    (∀ e2 σ2, ⌜R (e2, σ2) σ1'⌝ ={∅}=∗ Z e2 σ2 e1' σ1' ε2)
    ⊢ meas_prog_coupl e1 σ1 e1' σ1' ε Z.
  Proof.
    iIntros (-> ? ?) "H".
    iApply (meas_prog_coupl_step_l_erasable _ _ (gRet (σ1'))); [done|done|..].
  Admitted.
  (*
    { by apply ARcoupl_pos_R. }
    { apply dret_erasable. }
    iIntros (??? (?&?&->%dret_pos)).
    by iApply "H".
  Qed. *)

  (* Unsure
  Lemma meas_prog_coupl_step_l e1 σ1 e1' σ1' ε Z :
    reducible (e1, σ1) →
    (∀ e2 σ2, ⌜prim_step (e1 σ1 (e2, σ2) > 0⌝ ={∅}=∗ Z e2 σ2 e1' σ1' ε)
    ⊢ meas_prog_coupl e1 σ1 e1' σ1' ε Z.
  Proof.
    iIntros (?) "H".
    iApply (meas_prog_coupl_step_l_dret ε 0%NNR); [|done|..].
    { apply nnreal_ext => /=. lra. }
    { eapply ARcoupl_pos_R, ARcoupl_trivial.
      - by apply prim_step_mass.
      - apply dret_mass. }
    iIntros (?? (_ & ? & [=]%dret_pos)).
    by iApply "H".
  Qed.

  Lemma meas_prog_coupl_reducible e e' σ σ' Z ε :
    meas_prog_coupl e σ e' σ' ε Z -∗ ⌜reducible (e, σ)⌝.
  Proof. by iIntros "(%&%&%&%&%&%&%&%& _)". Qed.

  *)

End coupl_modalities.

(** * The weakest precondition  *)
Definition wp_pre `{!meas_spec_updateGS (meas_lang_markov Λ) Σ, !micrometerWpGS Λ Σ}
    (wp : coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
     coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
  (∀ σ1 e1' σ1' ε1,
      state_interp σ1 ∗ spec_interp (e1', σ1') ∗ err_interp ε1 ={E, ∅}=∗
      meas_spec_coupl ∅ σ1 e1' σ1' ε1 (λ σ2 e2' σ2' ε2,
        match to_val e1 with
        | Some v => |={∅, E}=> state_interp σ2 ∗ spec_interp (e2', σ2') ∗ err_interp ε2 ∗ Φ v
        | None =>
            meas_prog_coupl e1 σ2 e2' σ2' ε2 (λ e3 σ3 e3' σ3' ε3,
                ▷ meas_spec_coupl ∅ σ3 e3' σ3' ε3 (λ σ4 e4' σ4' ε4,
                    |={∅, E}=> state_interp σ4 ∗ spec_interp (e4', σ4') ∗ err_interp ε4 ∗ wp E e3 Φ))
      end))%I.

Local Instance wp_pre_contractive `{!meas_spec_updateGS (meas_lang_markov Λ) Σ, !micrometerWpGS Λ Σ} :
  Contractive wp_pre.
Proof.
  rewrite /wp_pre /= => n wp wp' Hwp E e1 Φ.
Admitted.
(*
  do 10 f_equiv.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [? [? ?]]. rewrite /meas_spec_coupl_pre.
  do 5 f_equiv.
  rewrite /meas_prog_coupl.
  do 27 f_equiv.
  f_contractive.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [? [? ?]]. rewrite /meas_spec_coupl_pre.
  do 8 f_equiv.
  apply Hwp.
Qed. *)

Local Definition wp_def `{!meas_spec_updateGS (meas_lang_markov Λ) Σ, !micrometerWpGS Λ Σ} :
  Wp (iProp Σ) (expr Λ) (val Λ) () :=
  {| wp := λ _ : (), fixpoint (wp_pre); wp_default := () |}.

Local Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp' := wp_aux.(unseal).
Global Arguments wp' {Λ Σ _}.
Global Existing Instance wp'.

Local Lemma wp_unseal `{!meas_spec_updateGS (meas_lang_markov Λ) Σ, !micrometerWpGS Λ Σ} :
  wp = (@wp_def Λ Σ _ _).(wp).
Proof. rewrite -wp_aux.(seal_eq) //. Qed.

Section wp.
Context `{!meas_spec_updateGS (meas_lang_markov Λ) Σ, !micrometerWpGS Λ Σ}.
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

(*
Global Instance wp_ne E e n s :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp (PROP:=iProp Σ) s E e).
Proof. Admitted. (*
  revert e. induction (lt_wf n) as [n _ IH]=> e Φ Ψ HΦ.
  rewrite !wp_unfold /wp_pre /=.
  do 10 f_equiv.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [? [? ?]]. rewrite /meas_spec_coupl_pre /meas_prog_coupl.
  do 32 f_equiv.
  f_contractive_fin.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [? [? ?]]. rewrite /meas_spec_coupl_pre.
  do 8 f_equiv.
  rewrite IH; [done|lia|].
  intros ?. apply dist_S, HΦ.
Qed. *) *)


Global Instance wp_proper E e s :
  Proper (pointwise_relation _ (≡) ==> (≡)) (wp (PROP:=iProp Σ) s E e).
Proof. Admitted.
(*
  by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne=>v; apply equiv_dist.
Qed.  *)
(*
Global Instance wp_contractive E e n s :
  TCEq (to_val e) None →
  Proper (pointwise_relation _ (dist_later n) ==> dist n) (wp (PROP:=iProp Σ) s E e).
Proof. Admitted. (*
  intros He Φ Ψ HΦ. rewrite !wp_unfold /wp_pre He /=.
  do 10 f_equiv.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [? [? ?]]. rewrite /meas_spec_coupl_pre.
  rewrite /meas_prog_coupl.
  do 31 f_equiv.
  f_contractive.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [? [? ?]]. rewrite /meas_spec_coupl_pre.
  do 22 f_equiv.
Qed.  *)  *)

Lemma wp_value_fupd' E Φ v s : (|={E}=> Φ v) ⊢ WP of_val v @ s; E {{ Φ }}.
Proof. Admitted. (*
  rewrite wp_unfold /wp_pre to_of_val.
  iIntros "H" (????) "(?&?&?)".
  iApply meas_spec_coupl_ret.
  iMod "H". iFrame.
  iApply fupd_mask_subseteq.
  set_solver.
Qed. *)

Lemma wp_strong_mono E1 E2 e Φ Ψ s :
  E1 ⊆ E2 →
  WP e @ s; E1 {{ Φ }} -∗
 (∀ σ1 e1' σ1' ε1 v,
     state_interp σ1 ∗ spec_interp (e1', σ1') ∗ err_interp ε1 ∗ Φ v -∗
     meas_spec_coupl ∅ σ1 e1' σ1' ε1 (λ σ2 e2' σ2' ε2,
          |={E2}=> state_interp σ2 ∗ spec_interp (e2', σ2') ∗ err_interp ε2 ∗ Ψ v)) -∗
  WP e @ s; E2 {{ Ψ }}.
Proof. Admitted. (*
  iIntros (HE) "H HΦ". iLöb as "IH" forall (e E1 E2 HE Φ Ψ s).
  rewrite !wp_unfold /wp_pre /=.
  iIntros (σ1 e1' σ1' ε1) "(Hσ & Hs & Hε)".
  iSpecialize ("H" with "[$]").
  iMod (fupd_mask_subseteq E1) as "Hclose"; [done|].
  iMod "H"; iModIntro.
  iApply (meas_spec_coupl_bind with "[-H] H"); [done|].
  iIntros (????) "H".
  destruct (to_val e) as [v|] eqn:?.
  { iApply fupd_meas_spec_coupl.
    iMod "H" as "(?&?&?)".
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iSpecialize ("HΦ" with "[$]").
    iApply (meas_spec_coupl_bind with "[-HΦ] HΦ"); [done|].
    iIntros (????) "Hσ".
    iApply meas_spec_coupl_ret.
    iMod "Hclose'". iMod "Hclose".
    by iMod "Hσ". }
  iApply meas_spec_coupl_ret.
  iApply (meas_prog_coupl_mono with "[HΦ Hclose] H").
  iIntros (e2 σ3 e3' σ3' ε3) "H !>".
  iApply (meas_spec_coupl_mono with "[HΦ Hclose] H"); [done|].
  iIntros (σ4 e4' σ4' ε4) "> ($ & $ & $ & H)".
  iMod "Hclose" as "_".
  iModIntro.
  by iApply ("IH" with "[] H").
Qed. *)

Lemma wp_strong_mono' E1 E2 e Φ Ψ s :
  E1 ⊆ E2 →
  WP e @ s; E1 {{ Φ }} -∗
  (∀ σ ρ v ε,
      state_interp σ ∗ spec_interp ρ ∗ err_interp ε ∗ Φ v ={E2}=∗
      state_interp σ ∗ spec_interp ρ ∗ err_interp ε ∗ Ψ v) -∗
  WP e @ s; E2 {{ Ψ }}.
Proof. Admitted. (*
  iIntros (?) "Hwp Hw".
  iApply (wp_strong_mono with "Hwp"); [done|].
  iIntros (?????) "(?&?&?&?)".
  iApply meas_spec_coupl_ret.
  by iMod ("Hw" with "[$]").
Qed. *)

Lemma fupd_wp E e Φ s: (|={E}=> WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre.
  iIntros "H" (????) "(?&?&?)".
  destruct (to_val e) as [v|] eqn:?.
  { by iMod ("H" with "[$]"). }
  by iMod ("H" with "[$]").
Qed.

Lemma wp_fupd E e Φ s : WP e @ s; E {{ v, |={E}=> Φ v }} ⊢ WP e @ s; E {{ Φ }}.
Proof. Admitted. (*
  iIntros "H".
  iApply (wp_strong_mono E with "H"); [done|].
  iIntros (?????) "(? & ? & ? & ?)".
  iApply meas_spec_coupl_ret.
  by iFrame.
Qed. *)

Lemma wp_atomic E1 E2 e Φ `{!Atomic StronglyAtomic e} s :
  (|={E1,E2}=> WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ s; E1 {{ Φ }}.
Proof. Admitted. (*
  iIntros "H". rewrite !wp_unfold /wp_pre.
  iIntros (σ1 e1' σ1' ε1) "(Hσ & Hs & Hε)".
  iDestruct ("H" with "[$]") as ">> H".
  iModIntro.
  iApply (meas_spec_coupl_mono with "[] H"); [done|].
  iIntros (σ2 e2' σ2' ε2) "H".
  destruct (to_val e) as [v|] eqn:?.
  { iDestruct "H" as "> ($ & $ & $ & $)". }
  iDestruct (meas_prog_coupl_strengthen with "H") as "H".
  iApply (meas_prog_coupl_mono with "[] H").
  iIntros (?????) "[[% %Hstep] H] !>".
  iApply (meas_spec_coupl_bind with "[] H"); [done|].
  iIntros (????) "H".
  iApply fupd_meas_spec_coupl.
  iMod "H" as "(Hσ & Hρ & Hε & H)".
  rewrite !wp_unfold /wp_pre.
  destruct (to_val e2) as [v2|] eqn:He2.
  + iMod ("H" with "[$]") as "H". iModIntro.
    iApply (meas_spec_coupl_mono with "[] H"); [done|].
    iIntros (????) "> ($ & $ & $ & >H)".
    rewrite -(of_to_val e2 v2) //.
    iApply wp_value_fupd'.
    iApply fupd_mask_intro_subseteq; [|done].
    set_solver.
  + iMod ("H" with "[$]") as "H". iModIntro.
    iApply (meas_spec_coupl_mono with "[] H"); [done|].
    iIntros (????) "H".
    iDestruct (meas_prog_coupl_reducible with "H") as %[ρ Hr].
    pose proof (atomic _ _ _ Hstep) as [? Hval].
    apply val_stuck in Hr. simplify_eq.
Qed. *)

Lemma wp_step_fupd E1 E2 e P Φ s :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> P) -∗ WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ s; E1 {{ Φ }}.
Proof. Admitted. (*
  rewrite !wp_unfold /wp_pre. iIntros (-> ?) "HR H".
  iIntros (σ1 e1' σ1' ε1) "Hs". iMod "HR".
  iMod ("H" with "Hs") as "H".
  iModIntro.
  iApply (meas_spec_coupl_mono with "[HR] H"); [done|].
  iIntros (σ2 e2' σ2' ε2) "H".
  iApply (meas_prog_coupl_mono with "[HR] H").
  iIntros (e3 σ3 e3' σ3' ε3) "H !>".
  iApply (meas_spec_coupl_mono with "[HR] H"); [done|].
  iIntros (σ4 e4' σ4' ε4) "H".
  iMod "H" as "($ & $ & $ & H)".
  iMod "HR".
  iApply (wp_strong_mono E2 with "H"); [done..|].
  iIntros "!>" (?????) "(? & ? & ? & H)".
  iApply meas_spec_coupl_ret.
  iMod ("H" with "[$]").
  by iFrame.
Qed. *)

Lemma wp_bind K `{!LanguageCtx K} E e Φ s :
  WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }} ⊢ WP K e @ s; E {{ Φ }}.
Proof. Admitted. (*
  iIntros "H". iLöb as "IH" forall (E e Φ s). rewrite !wp_unfold /wp_pre.
  iIntros (σ1 e1' σ1' ε1) "Hs".
  iMod ("H" with "[$]") as "H".
  iApply (meas_spec_coupl_bind with "[] H"); [done|].
  iIntros (σ2 e2' σ2' ε2) "H".
  destruct (to_val e) as [v|] eqn:He.
  { iApply fupd_meas_spec_coupl.
    iMod "H" as "(Hσ & Hs & Hε & H)".
    apply of_to_val in He as <-.
    rewrite wp_unfold /wp_pre.
    by iMod ("H" with "[$]"). }
  rewrite fill_not_val /=; [|done].
  iApply meas_spec_coupl_ret.
  iApply meas_prog_coupl_ctx_bind; [done|].
  iApply (meas_prog_coupl_mono with "[] H").
  iIntros (e3 σ3 e3' σ3' ε3) "H !>".
  iApply (meas_spec_coupl_mono with "[] H"); [done|].
  iIntros (σ4 e4' σ4' ε4) "H".
  iMod "H" as "($ & $ & $ & H)".
  iModIntro.
  by iApply "IH".
Qed. *)

(*
Lemma spec_update_wp E e Φ a :
  spec_update E (WP e @ a; E {{ Φ }}) ⊢ WP e @ a; E {{ Φ }}.
Proof.
  iIntros "Hspec".
  iEval (rewrite !wp_unfold /wp_pre).
  iIntros (σ1 e1' σ1' ε1) "(Hσ & Hs & Hε)".
  rewrite spec_update_unseal.
  iMod ("Hspec" with "Hs")
    as ([e2' σ2'] n Hstep%stepN_pexec_det) "(Hs & Hwp)".
  iEval (rewrite !wp_unfold /wp_pre) in "Hwp".
  iMod ("Hwp" with "[$]") as "Hwp".
  iModIntro.
  by iApply meas_spec_coupl_steps_det.
Qed.

Lemma wp_spec_update E e Φ s :
  WP e @ s; E {{ v, spec_update E (Φ v) }} ⊢ WP e @ s; E {{ Φ }}.
Proof.
  iIntros "Hwp".
  iLöb as "IH" forall (e E Φ s).
  rewrite !wp_unfold /wp_pre.
  iIntros (σ1 e1' σ1' ε1) "(Hσ & Hs & Hε)".
  iMod ("Hwp" with "[$]") as "Hwp".
  iModIntro.
  iApply (meas_spec_coupl_bind with "[] Hwp"); [done|].
  iIntros (????) "H".
  destruct (to_val e).
  { iApply fupd_meas_spec_coupl.
    iMod "H" as "(?&?&?& Hupd)".
    rewrite spec_update_unseal.
    iMod ("Hupd" with "[$]")
      as ([e3' σ3'] n Hstep%stepN_pexec_det) "(Hs & Hwp)".
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".
    iApply meas_spec_coupl_steps_det; [done|].
    iApply meas_spec_coupl_ret.
    iMod "Hclose".
    by iFrame. }
  iApply meas_spec_coupl_ret.
  iApply (meas_prog_coupl_mono with "[] H").
  iIntros (e2 σ3 e3' σ3' ε3) "H !>".
  iApply (meas_spec_coupl_mono with "[] H"); [done|].
  iIntros (σ4 e4' σ4' ε4) "> ($ & $ & $ & H)".
  iApply ("IH" with "H").
Qed.
*)

(** * Derived rules *)
Lemma wp_mono E e Φ Ψ s : (∀ v, Φ v ⊢ Ψ v) → WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (wp_strong_mono' with "H"); auto.
  iIntros (????) "($ & $ & $ & ?)". by iApply HΦ.
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
Proof. Admitted. (*
  iIntros "[? H]".
  iApply (wp_strong_mono with "H"); [done|].
  iIntros (?????) "(? & ? & ? & ?)".
  iApply meas_spec_coupl_ret. by iFrame.
Qed. *)
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
  iIntros (????) "($ & $ & $ & ?)". by iApply "H".
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
  Context `{!meas_spec_updateGS (meas_lang_markov Λ) Σ, !micrometerWpGS Λ Σ}.
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

  (*
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
  Qed. *)
End proofmode_classes.

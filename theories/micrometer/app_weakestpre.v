From Coq Require Export Reals Psatz.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export fixpoint big_op.
From iris.prelude Require Import options.
From iris.algebra Require Import ofe.

From mathcomp.analysis Require Import measure.
From mathcomp.classical Require Import classical_sets.

From clutch.prelude Require Import stdpp_ext iris_ext NNRbar.
From clutch.meas_lang Require Export language erasable.
From clutch.meas_lang Require Export meas_spec_update.
From clutch.prob.monad Require Export couplings_app tactics.
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

Definition coe_nonnegreal_bar_R : nonnegreal -> \bar R := EFin \o nonneg.

(** * Coupling modalities  *)
Section coupl_modalities.
  Context `{!meas_spec_updateGS (meas_lang_markov Λ) Σ, !micrometerWpGS Λ Σ}.

  (** [exists-support modality] There exists a measurable set with mass 1 on which the proposition holds *)
  Definition EXSM {d} {T : measurableType d} (Φ : T → iProp Σ) (ρ : giryM T) : iProp Σ :=
    ∃ S : set T, ⌜measurable S ⌝ ∗ ⌜ρ S = EFin (1)%R⌝ ∗ ∀ ρ' : T , ⌜S ρ'⌝ → Φ ρ'.

  Lemma EXSM_ret_idemp {d} {T : measurableType d} (Φ : T → iProp Σ) (ρ : giryM T) :
    EXSM (fun ρ' => EXSM Φ (gRet ρ')) ρ ⊣⊢ (EXSM Φ ρ).
  Proof.
    iSplit.
    { iIntros "[%S [%HS [%HS1 X]]]".
      unfold EXSM.
      iExists S.
      iSplitR; [done|].
      iSplitR; [done|].
      iIntros (ρ' Hρ').
      iSpecialize ("X" $! ρ' Hρ').
      iDestruct "X" as "[%S' [%HS' [%HS'' Y]]]".
      iApply "Y".
      iPureIntro.
      apply gRetMass1Inv; done.
    }
    { iIntros "[%S [%HS1 [%HS2 X]]]".
      iExists S.
      iSplitR; [done|].
      iSplitR; [done|].
      iIntros (ρ' Hρ').
      iExists S.
      iSplitR; [done|].
      iSplitR.
      { by iPureIntro; apply gRetMass1Inv. }
      iApply "X".
    }
  Qed.

  Local Open Scope classical_set_scope.
  Lemma EXSM_ret {d} {T : measurableType d} (Φ : T → iProp Σ) (t : T) (H : d.-measurable [set t]) :
    Φ t -∗ EXSM Φ (gRet t).
  Proof.
    iIntros "H".
    iExists [set t].
    iSplitR; [done|].
    iSplitR; [by iPureIntro; apply gRetMass1Inv|].
    simpl.
    by iIntros (ρ) "->".
  Qed.




  (** ** [meas_spec_coupl]  *)

  (** The [meas_spec_coupl] modality allows us to (optionally) prepend spec execution steps and erasable
      distributions, e.g. [state_step]s on both sides. *)

  Definition meas_spec_coupl_pre (E : coPset)
      (Z : stateO Λ -> exprO Λ -> stateO Λ -> NNRO -> iProp Σ) (Φ : stateO Λ * (exprO Λ * stateO Λ) * NNRO → iProp Σ) :
      (stateO Λ) * (exprO Λ * stateO Λ) * NNRO → iProp Σ :=
    (λ (x : stateO Λ * (exprO Λ * stateO Λ) * NNRO),
       let '(σ1, (e1', σ1'), ε) := x in
       ⌜1 <= ε⌝ ∨
       (Z σ1 e1' σ1' ε) ∨
       (∃ (S : state Λ → (expr Λ * state Λ)%type → Prop) (n : nat) (μ1 : giryM (state Λ)) (μ1' : giryM (state Λ))
          (ε1 : nonnegreal) (X2 : (expr Λ * state Λ)%type → nonnegreal) (r : R),
            ⌜ ARcoupl_meas μ1 (gBind' (pexec n \o pair (toPacked e1')) μ1') S (0)%R  (coe_nonnegreal_bar_R ε1) ⌝ ∗
            ⌜∀ ρ, X2 ρ <= r⌝ ∗
            ⌜ (le_ereal (EFin (nonneg ε1) + \int[gBind' (pexec n \o pair (toPacked e1')) μ1']_ρ (EFin (nonneg (X2 ρ))))) (EFin (nonneg ε)) ⌝ ∗
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
         ⌜ARcoupl_meas μ1 (gBind' (pexec n \o pair (toPacked e1')) μ1') S (0)%R  (coe_nonnegreal_bar_R ε1) ⌝ ∗
         ⌜∀ ρ, X2 ρ <= r⌝ ∗
          ⌜ (le_ereal (EFin (nonneg ε1) + \int[gBind' (pexec n \o pair (toPacked e1')) μ1']_ρ (EFin (nonneg (X2 ρ))))) (EFin (nonneg ε)) ⌝ ∗
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
       ⌜ (le_ereal (EFin (nonneg ε1) + \int[gBind' (pexec n \o pair e1') μ1']_ρ (EFin (nonneg (X2 ρ))))) (EFin (nonneg ε)) ⌝ ∗
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
           (prodO (prodO (state Λ) (prodO (exprO Λ) (stateO Λ))) NNRO) → iProp Σ).
    assert (NonExpansive Ψ').
    { intros n [[σ1 [e1' σ1']] ε1] [[σ2 [e2' σ2']] ε2].
      intros ([[=] ([=] & [=])] & [=]).
      by simplify_eq/=. }
    iApply (least_fixpoint_ind _ Ψ' with "[] H").
    iIntros "!#" ([[? [??]] ?]) "H". by iApply "IH".
  Qed.


  (** ********************* Lemma code (being worked on elsewhere *)

  Theorem gBind_id_left : ∀ {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2} (f : T1 -> giryM T2)
    (a : T1) (HMF : measurable_fun setT f),
    gBind' f (gRet a) = f a.
  Proof. Admitted.

  Lemma gRet_id_right {d1} {T : measurableType d1} (μ : giryM T)  :
    gBind' gRet μ = μ.
  Admitted.

  Lemma pexec_0' :  (pexec 0 :  mstate (meas_lang_markov Λ) -> _) = gRet.
  Proof. apply functional_extensionality; intro a; eapply pexec_O. Qed.

  (* This might not be true of is_det as written because it's a subdistribution, but we can
     change the definition *)
  Lemma is_det_dret {d1} {T1 : measurableType d1} {μ1 : giryM T1} {t : T1} (H : is_det t μ1) :
    μ1 = gRet t.
  Admitted.

  (** ********************* *)


  Local Open Scope classical_set_scope.

  Lemma fupd_meas_spec_coupl E σ1 e1' σ1' Z (ε : nonnegreal) :
    (|={E}=> meas_spec_coupl E σ1 e1' σ1' ε Z) ⊢ meas_spec_coupl E σ1 e1' σ1' ε Z.
  Proof.
    iIntros "H".
    iApply meas_spec_coupl_rec.
    iExists _, 0%nat, (gRet (toPacked σ1)), (gRet (toPacked σ1')), 0%NNR, (λ _, ε), ε.
    setoid_rewrite gBind_id_left; first last.
    { apply @measurable_compT.
      { done. }
      { by apply pexec_meas. }
      { by apply measurable_pair1. }
    }
    { apply @measurable_compT.
      { done. }
      { by apply pexec_meas. }
      { by apply measurable_pair1. }
    }
    rewrite pexec_0'.
    iSplit; [iPureIntro|].
    { eapply (@ARcoupl_meas_pos_R _ _ _ _ _ _ _ _ _ [set (toPacked σ1)] ([set (toPacked e1')] `*` [set (toPacked σ1')])).
      { by apply state_meas_points. }
      { by apply measurableX; [apply expr_meas_points | apply state_meas_points]. }
      { apply gRetMass1Inv; [|done]. by apply state_meas_points. }
      { apply gRetMass1Inv; [|done].
        by apply measurableX; [apply expr_meas_points | apply state_meas_points]. }
      eapply (ARcoupl_meas_dret); try done.
      Unshelve.
      2: { intros _ _. apply True. (* idk why I get typ2 errors when I do this the other way around *) }
      done.
    }
    iSplit; [done|].
    iSplit; [iPureIntro|].
    { rewrite integral_cst.
      { rewrite //=/numfun.indic//=.
        rewrite mem_set;[|done].
        repeat destroy_mathcomp; lra.
      }
      { by eapply @measurableT. }
    }
    iSplit. { iPureIntro. by apply erasable_gRet. }
    iSplit. { iPureIntro. by apply erasable_gRet. }
    iIntros (??? (_ & S1 & S2)); simpl. simpl in S1, S2; inversion S2; subst.
    by iApply "H".
  Qed.

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
    iExists (fun A B => A = σ1 ∧ B.1 = e1' ∧ B.2 = σ1'), 0%nat, (gRet (toPacked σ1)), (gRet (toPacked σ1')), ε', (fun _ => ε1), ε1.
    setoid_rewrite gBind_id_left.
    2: { admit. (* prove gBind_id_left to see if necessary *) }
    2: { admit. (* prove gBind_id_left to see if necessary *) }
    rewrite pexec_0'.
    iSplit. {
      iPureIntro.
      apply (@ARcoupl_meas_mon_grading _ _ _ _ _ _ _ 0 _ (EFin 0) _).
      { done. }
      { repeat destroy_mathcomp. lra. }
      apply ARcoupl_meas_dret; done.
    }
    iSplit; [iPureIntro; done|].
    iSplit. {
      (* integral of cst function wrt. ret  *) admit. } (* { rewrite Expval_dret /=. lra. } *)
    iSplit. { iPureIntro. by apply erasable_gRet. }
    iSplit. { iPureIntro. by apply erasable_gRet. }
    iIntros (???); simpl; iIntros ([-> [-> ->]]). by iFrame.
  Admitted. (** OK *)

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
    { rewrite -(gRet_id_right μ1).
      have -> : (gBind' gRet μ1) = gBind gRet_meas_fun μ1 by admit.
      have XM : measurable_fun setT (pexec 0 \o pair (toPacked e1')) by admit.
      have -> : (gBind' (pexec 0 \o pair (toPacked e1')) μ1') = (gBind XM μ1') by admit.
      simpl.
      have -> : (0 = 0 + 0)%R by admit.
      have -> : (coe_nonnegreal_bar_R ε1) = (adde (coe_nonnegreal_bar_R ε1) (EFin 0)) by admit.
      eapply ARcoupl_meas_dbind.
      { admit. }
      { done. }
      { (* 0 is finite ?? *) admit. }
      2: { by eapply H. }
      setoid_rewrite pexec_0'.
      (* This is a ret-ret coupling with error 0
      eapply (ARcoupl_dbind' ε1 0%NNR); [done|done|simpl; lra|..|done].
      intros ???.
      rewrite pexec_O.
      by apply ARcoupl_dret. *)
    admit. }
    iSplit; [iPureIntro|].
    { intros []. rewrite /X2' //. }
    iSplit; [iPureIntro|].
    { rewrite /X2'. setoid_rewrite pexec_0'.
      (* rewrite Expval_dmap //=.
      by eapply ex_expval_bounded=>/=. *)
      admit. }
    do 2 (iSplit; [done|]).
    iIntros (??? [? ->]). rewrite /X2' /=.
    by iApply "H".
  Admitted. (** UNSURE *)

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
    (* UB the intergral by ε2 * μ1' setT *)
  Admitted. (** OK *)
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
    iExists R, n, μ1, (gRet σ1'), ε1, (λ _, ε2), ε2.
    setoid_rewrite gBind_id_left.
    2: { admit. (* prove gBind_id_left to see if necessary *) }
    2: { admit. (* prove gBind_id_left to see if necessary *) }
    iSplit. { done. }
    iSplit. { done. }
    iSplit. {
      (*
      unfold ARcoupl_meas in H.
      simpl in H.
      pose f : (state Λ) -> _ := (fun _ => EFin (nonneg ε1)).
      have Hf : measurable_fun setT f by admit.
      pose g : expr Λ * state Λ → _ := fun _ => EFin (nonneg ε2).
      have Hg : measurable_fun setT g by admit.
      Check H f Hf _ _ g Hg _ _. (* Needs f ≤ g on R ... *)
      iPureIntro.*)
      admit. }
    (* { rewrite Expval_const //. apply Rle_plus_plus; [done|]. real_solver. }  *)
    iSplit. { done. }
    iSplit. { iPureIntro. by apply erasable_gRet. }
    done.
  Admitted. (** UNSURE *)

  Lemma meas_spec_coupl_steps n ε2 ε1 ε R E σ1 e1' σ1' Z :
    ε = (ε1 + ε2)%NNR →
    ARcoupl_meas (gRet σ1) (pexec n (e1', σ1')) R (0)%R (EFin (nonneg ε1)) →
    (∀ (σ2 : stateO Λ) (e2' : exprO Λ) (σ2' : stateO Λ), ⌜R (toPacked σ2) (e2', σ2')⌝ ={E}=∗ meas_spec_coupl E σ2 e2' σ2' ε2 Z)
    ⊢ meas_spec_coupl E σ1 e1' σ1' ε Z.
  Proof.
    iIntros (-> ?) "H".
    iApply (meas_spec_coupl_erasable_steps n R (gRet σ1) ε1 ε2); [done | done | |].
    { by apply erasable_gRet. }
    iFrame.
  Qed.

  Lemma meas_spec_coupl_steps_det n ε σ1 e1' σ1' e2' σ2' Z E :
    is_det (e2', σ2') (pexec n (e1', σ1')) →
    meas_spec_coupl E σ1 e2' σ2' ε Z ⊢
    meas_spec_coupl E σ1 e1' σ1' ε Z.
  Proof.
    iIntros (Hexec%is_det_dret) "H".
    iApply (meas_spec_coupl_steps n ε 0%NNR).
    { apply nnreal_ext => /=. lra. }
    { eapply (@ARcoupl_meas_pos_R _ _ _ _ _ _ _ _ _ [set (toPacked σ1)] ([set e2'] `*` [set σ2'])), ARcoupl_meas_trivial.
      { by apply state_meas_points. }
      { by apply measurableX; [apply expr_meas_points | apply state_meas_points ]. }
      { apply gRetMass1Inv; [by apply state_meas_points|done]. }
      { rewrite Hexec. apply gRetMass1Inv; [|done].
        by apply measurableX; [apply expr_meas_points | apply state_meas_points ]. }
      { apply gRetMass1Inv; [|done]. by eapply @measurableT. }
      { rewrite Hexec. apply gRetMass1Inv; [|done]. by eapply @measurableT. }
    }
    iIntros (??? (_ & H1 & H2)).
    simpl in H1, H2.
    destruct H2 as [->->].
    rewrite /toPacked in H1; subst.
    done.
  Qed.

  Lemma meas_spec_coupl_step ε E σ1 e1' σ1' Z :
    reducible (e1', σ1') ->
    (EXSM (fun ρ' : (cfg Λ) => |={E}=> meas_spec_coupl E σ1 ρ'.1 ρ'.2 ε Z) (prim_step (e1', σ1')))
    ⊢ meas_spec_coupl E σ1 e1' σ1' ε Z.
  Proof.
    iIntros (?) "[%S [%H1 [%H2 H3]]]".
    iStartProof.
    iApply (meas_spec_coupl_steps 1 ε 0%NNR).
    { apply nnreal_ext => /=. lra. }
    (*
    { rewrite pexec_1 step_or_final_no_final; [|by apply reducible_not_final].
      eapply (@ARcoupl_meas_pos_R _ _ _ _ _ _ _ _ _ [set σ1] S), ARcoupl_meas_trivial.
      { admit. (* Singletons are measurable *) }
      { done. }
      { admit. (* gRet mass *) }
      { (** IDK but use H2 probably *) admit. }
      { admit. (* gRet is PMF *) }
      { apply prim_step_mass.
        rewrite /is_zero.
        intro HK.
        pose HK' := HK S.
        by rewrite //= in HK'. }
    }
    iIntros (??? (_ & H4 & H5)).
    rewrite //= in H4; subst.
    iSpecialize ("H3" $! (e2', σ2')); simpl.
    by iApply "H3". *)
  Admitted. (** UNSURE *)


  (** * [meas_prog_coupl] *)

  (** The [meas_prog_coupl] modality allows us to coupl *exactly* one program step with any number of
      spec execution steps and an erasable distribution *)
  Definition meas_prog_coupl (e1 : exprO Λ) (σ1 : stateO Λ) (e1' : exprO Λ) σ1' (ε : NNRO) Z : iProp Σ :=
    ∃ (R : cfg Λ → cfg Λ → Prop) (n : nat) (μ1' : giryM (state Λ))
      (ε1 : nonnegreal) (X2 : cfg Λ → nonnegreal) (r : nonnegreal),
      ⌜reducible (toPacked e1, toPacked σ1)⌝ ∗
      ⌜ARcoupl_meas (prim_step (e1, σ1)) (gBind' (pexec n \o pair (toPacked e1')) μ1') R (0)%R  (coe_nonnegreal_bar_R ε1) ⌝ ∗
      ⌜∀ ρ, X2 ρ <= r⌝ ∗
      ⌜ (le_ereal (EFin (nonneg ε1) + \int[gBind' (pexec n \o pair (toPacked e1')) μ1']_ρ (EFin (nonneg (X2 ρ))))) (EFin (nonneg ε))⌝ ∗
      ⌜erasable μ1' σ1'⌝ ∗
      ∀ e2 σ2 e2' σ2', ⌜R (e2, σ2) (e2', σ2')⌝ ={∅}=∗ Z e2 σ2 e2' σ2' (X2 (e2, σ2)).

(* This one is actually never used outside of the weaker case (wich can be proven
   independently) and prog_coupl_strengthen.

  Can I prove prog_coupl_strengthen independently? This lemma is also only used once, can I get
  rid of it's usage?

  Lemma meas_prog_coupl_strong_mono e1 σ1 e1' σ1' Z1 Z2 ε :
    (∀ (e2' : expr Λ) (σ2' σ : state Λ) ε',
       EXSM (fun '(e2, σ2) => Z1 e2 σ2 e2' σ2' ε' -∗ Z2 e2 σ2 e2' σ2' ε') (prim_step (e1, σ)))
      ⊢ meas_prog_coupl e1 σ1 e1' σ1' ε Z1 -∗ meas_prog_coupl e1 σ1 e1' σ1' ε Z2.
  Proof.
    iIntros "Hm (%R & %n & %μ1' & %ε1 & %X2 & %r & % & %Hcpl & % & % & % & Hcnt) /=".
    iExists _, _, _, _, _, _.
    iSplit; [done|].
    (* I want to use Hm here to get S, but I'll eventually need e2', σ2' σ from the application of Hcnt.
      Does switching the order quantification make it possile? *)

    iSplit.
    { iPureIntro.
      eapply (@ARcoupl_meas_pos_R _ _ _ _ _ _ _ _ _ _ _); last by apply Hcpl.
      (* Need sets with with mass 1
          in (prim_step (e1, σ1)), and
          in (gBind' (pexec n \o pair e1') μ1') *)

      (* by apply ARcoupl_pos_R. *)  all: admit. }
    iFrame "%".
    iIntros (e2 σ2 e2' σ2') "[%HR0 [%HR1 %HR2]]".
    iSpecialize ("Hm" $! e2' σ2' σ2 (X2 (e2, σ2))).
    unfold EXSM.
    iDestruct "Hm" as (S) "[%X [%X' Y]]".
    iSpecialize ("Y" $! (e2, σ2)).
    iApply fupd_idemp.
    iApply "Y".
    { iPureIntro. (* S is not in scope... *) admit. }
    iSpecialize ("Hcnt" $! e2 σ2 e2' σ2' HR0).
    iApply "Hcnt".
  Admitted. (** UNSURE *)
*)

  Lemma meas_prog_coupl_mono e1 σ1 e1' σ1' Z1 Z2 ε :
    (∀ e2 σ2 e2' σ2' ε', Z1 e2 σ2 e2' σ2' ε' -∗ Z2 e2 σ2 e2' σ2' ε') -∗
    meas_prog_coupl e1 σ1 e1' σ1' ε Z1 -∗ meas_prog_coupl e1 σ1 e1' σ1' ε Z2.
  Proof.
    iIntros "Hm".
    unfold meas_prog_coupl.
    iIntros "(%R & %n & %μ1' & %ε1 & %X2 & %r & %Hred & %Hcpl & %HX2 & %Hε & %Herasable & H)".
    iExists _, _, _, _, _, _.
    iSplitR; first done.
    iSplitR; first by iPureIntro; apply Hcpl.
    iSplitR; first by iPureIntro; eapply HX2.
    iSplitR; first by iPureIntro; eapply Hε.
    iSplitR; first by iPureIntro; eapply Herasable.
    iIntros (???? HR).
    iApply "Hm".
    iApply "H".
    done.
  Qed.

  (*
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
  Admitted. (** UNSURE *)

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
  (*
    rewrite dret_id_left pexec_1.
    rewrite step_or_final_no_final; [|by apply reducible_not_final].
    do 2 (iSplit; [done|]).
    iSplit; [iPureIntro|].
    { rewrite Expval_const //. rewrite prim_step_mass //=. lra. }
    iSplit; [iPureIntro; apply dret_erasable|].
    done.
  Qed. *)
  Admitted.

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
    { setoid_rewrite pexec_0'.
      (*
      rewrite -(dret_id_right (prim_step _ _)).
      replace ε1 with (ε1 + 0)%NNR; [|apply nnreal_ext; simpl; lra].
      eapply ARcoupl_dbind; [done|done|..|done].
      intros ???. by apply ARcoupl_dret. }         *)
      admit.
    }
    iSplit; [done|].
    iSplit; [iPureIntro|].
    { admit. (* Huh? Only if ε_1 ≤ ε_2 right? *) }  (*  { rewrite Expval_const //. rewrite prim_step_mass //=. lra. } *)
    iSplit; [done|].
    iIntros (e2 σ2 e2' σ2' [? ->]).
    by iApply "H".
  Admitted. (** UNSURE *)

  Lemma meas_prog_coupl_step_l_dret ε2 ε1 ε R e1 σ1 e1' σ1' Z :
    ε = (ε1 + ε2)%NNR →
    reducible (e1, σ1) →
    ARcoupl_meas (prim_step (e1, σ1)) (gRet σ1') R (0)%R (EFin (nonneg ε1)) →
    (∀ e2 σ2, ⌜R (e2, σ2) σ1'⌝ ={∅}=∗ Z e2 σ2 e1' σ1' ε2)
    ⊢ meas_prog_coupl e1 σ1 e1' σ1' ε Z.
  Proof.
    iIntros (-> ? ?) "H".
    iApply (meas_prog_coupl_step_l_erasable _ _ (gRet (σ1')) _ _); [done|done| |..].
    { eapply (@ARcoupl_meas_pos_R _ _ _ _ _ _ _ _ _ setT [set σ1']).
      { by eapply @measurableT. }
      { (* measurable singleton *) admit. }
      { (* prim step PMF *) admit. }
      { (* return PMF *) admit. }
      by apply H0.
    }
    { admit. (* gRet erasable *) }
    iIntros (??? (?&?&H3)).
    simpl in H3; subst.
    by iApply "H".
  Admitted. (** OK *)


  Lemma meas_prog_coupl_step_l e1 σ1 e1' σ1' ε Z :
    reducible (e1, σ1) →
    EXSM (λ ρ, |={∅}=> Z ρ.1 ρ.2 e1' σ1' ε) (prim_step (e1, σ1))
    ⊢ meas_prog_coupl e1 σ1 e1' σ1' ε Z.
  Proof.
    iIntros (?) "[%S [%H1 [%H2 H3]]]".
    iApply (meas_prog_coupl_step_l_dret ε 0%NNR); [|done|..].
    { apply nnreal_ext => /=. lra. }
    { eapply (@ARcoupl_meas_pos_R _ _ _ _ _ _ _ _ _ S [set σ1']); try done.
      { (* measurable singletons *) admit. }
      { (* gRet property *) admit. }
      apply ARcoupl_meas_trivial; try done.
      { (* Follows from H2 + prim_step is subdistribution *) admit. }
      { (* gRet is PMF *) admit. }
    }
    iIntros (?? (_ & ? & [=])).
    iSpecialize ("H3" $! (e2, σ2)); simpl.
    by iApply "H3".
  Admitted. (** OK *)

  Lemma meas_prog_coupl_reducible e e' σ σ' Z ε :
    meas_prog_coupl e σ e' σ' ε Z -∗ ⌜reducible (toPacked e, toPacked σ)⌝.
  Proof. by iIntros "(%&%&%&%&%&%&%&%& _)". Qed.

End coupl_modalities.

(** * The weakest precondition  *)
Definition wp_pre `{!meas_spec_updateGS (meas_lang_markov Λ) Σ, !micrometerWpGS Λ Σ}
    (wp : coPset -d> exprO Λ -d> (valO Λ -d> iPropO Σ) -d> iPropO Σ) :
     coPset -d> exprO Λ -d> (valO Λ -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
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
  do 4 (apply forall_ne; move=>?).
  apply wand_ne; [f_equiv|].
  apply fupd_ne.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [[?[??]]?].
  rewrite /meas_spec_coupl_pre.
  apply or_ne; [done|].
  case (to_val e1); [done|].
  apply or_ne; [|done].
  unfold meas_prog_coupl.
  do 6 (apply exist_ne; move=>?).
  do 5 (apply sep_ne; [done|]).
  do 4 (apply forall_ne; move=>?).
  apply wand_ne; [f_equiv|].
  apply fupd_ne.
  f_contractive.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [[?[??]]?].
  rewrite /meas_spec_coupl_pre.
  do 2 f_equiv.
  apply fupd_ne.
  do 3 f_equiv.
  apply Hwp.
Qed.

Local Definition wp_def `{!meas_spec_updateGS (meas_lang_markov Λ) Σ, !micrometerWpGS Λ Σ} :
  Wp (iProp Σ) (Measurable.sort (expr Λ)) (Measurable.sort (val Λ)) () :=
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
Implicit Types v : Measurable.sort (val Λ).
Implicit Types e : Measurable.sort (expr Λ).
Implicit Types σ : Measurable.sort (state Λ).
Implicit Types ρ : Measurable.sort (cfg Λ).

(* Weakest pre *)
Lemma wp_unfold E e Φ s :
  WP e @ s; E {{ Φ }} ⊣⊢ wp_pre (wp (PROP:=iProp Σ) s) E e Φ.
Proof. rewrite wp_unseal. apply (fixpoint_unfold wp_pre). Qed.

Global Instance wp_ne E e n s :
  Proper (pointwise_relation _ (ofe.dist n) ==> ofe.dist n) (wp (PROP:=iProp Σ) s E e).
Proof.
  revert e. induction (lt_wf n) as [n _ IH]=> e Φ Ψ HΦ.
  rewrite !wp_unfold /wp_pre /=.
  do 4 (apply forall_ne; move=>?).
  apply wand_ne; [f_equiv|].
  apply fupd_ne.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [[?[??]]?].
  rewrite /meas_spec_coupl_pre.
  apply or_ne; [done|].
  case (to_val e).
  { move=>?.
    f_equiv.
    apply fupd_ne; f_equiv.
    apply sep_ne; f_equiv.
    done.
  }
  apply or_ne; [|done].
  unfold meas_prog_coupl.
  do 6 (apply exist_ne; move=>?).
  do 5 (apply sep_ne; [done|]).
  do 4 (apply forall_ne; move=>?).
  apply wand_ne; [f_equiv|].
  apply fupd_ne.
  f_contractive.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [[?[??]]?].
  rewrite /meas_spec_coupl_pre.
  do 2 f_equiv.
  apply fupd_ne.
  do 3 f_equiv.
  apply IH; [done|].
  move=>?.
  eapply ofe.dist_le; [by apply HΦ|].
  lia.
Qed.

Global Instance wp_proper E e s :
  Proper (pointwise_relation _ (≡) ==> (≡)) (wp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne=>v; apply equiv_dist. Qed.

Global Instance wp_contractive E e n s :
  TCEq (to_val e) None →
  Proper (pointwise_relation _ (dist_later n) ==> ofe.dist n) (wp (PROP:=iProp Σ) s E e).
Proof.
  intros He Φ Ψ HΦ. rewrite !wp_unfold /wp_pre He /=.
  do 4 (apply forall_ne; move=>?).
  apply wand_ne; [f_equiv|].
  apply fupd_ne.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [[?[??]]?].
  rewrite /meas_spec_coupl_pre.
  apply or_ne; [done|].
  apply or_ne; [|done].
  rewrite /meas_prog_coupl.
  do 6 (apply exist_ne; move=>?).
  do 5 (apply sep_ne; [done|]).
  do 4 (apply forall_ne; move=>?).
  apply wand_ne; [f_equiv|].
  apply fupd_ne.
  f_contractive.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [[?[??]]?].
  rewrite /meas_spec_coupl_pre.
  do 2 f_equiv.
  apply fupd_ne.
  do 3 f_equiv.
  apply wp_ne.
  apply HΦ.
Qed.

Lemma wp_value_fupd' E Φ v s : (|={E}=> Φ v) ⊢ WP of_val v @ s; E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre to_of_val.
  iIntros "H" (????) "(?&?&?)".
  iApply meas_spec_coupl_ret.
  iMod "H". iFrame.
  iApply fupd_mask_subseteq.
  set_solver.
Qed.

Lemma wp_strong_mono E1 E2 e Φ Ψ s :
  E1 ⊆ E2 →
  WP e @ s; E1 {{ Φ }} -∗
 (∀ σ1 e1' σ1' ε1 v,
     state_interp σ1 ∗ spec_interp (e1', σ1') ∗ err_interp ε1 ∗ Φ v -∗
     meas_spec_coupl ∅ σ1 e1' σ1' ε1 (λ σ2 e2' σ2' ε2,
          |={E2}=> state_interp σ2 ∗ spec_interp (e2', σ2') ∗ err_interp ε2 ∗ Ψ v)) -∗
  WP e @ s; E2 {{ Ψ }}.
Proof.
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
Qed.

Lemma wp_strong_mono' E1 E2 e Φ Ψ s :
  E1 ⊆ E2 →
  WP e @ s; E1 {{ Φ }} -∗
  (∀ σ ρ v ε,
      state_interp σ ∗ spec_interp ρ ∗ err_interp ε ∗ Φ v ={E2}=∗
      state_interp σ ∗ spec_interp ρ ∗ err_interp ε ∗ Ψ v) -∗
  WP e @ s; E2 {{ Ψ }}.
Proof.
  iIntros (?) "Hwp Hw".
  iApply (wp_strong_mono with "Hwp"); [done|].
  iIntros (?????) "(?&?&?&?)".
  iApply meas_spec_coupl_ret.
  by iMod ("Hw" with "[$]").
Qed.

Lemma fupd_wp E e Φ s: (|={E}=> WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre.
  iIntros "H" (????) "(?&?&?)".
  destruct (to_val e) as [v|] eqn:?.
  { by iMod ("H" with "[$]"). }
  by iMod ("H" with "[$]").
Qed.

Lemma wp_fupd E e Φ s : WP e @ s; E {{ v, |={E}=> Φ v }} ⊢ WP e @ s; E {{ Φ }}.
Proof.
  iIntros "H".
  iApply (wp_strong_mono E with "H"); [done|].
  iIntros (?????) "(? & ? & ? & ?)".
  iApply meas_spec_coupl_ret.
  by iFrame.
Qed.

Lemma wp_atomic E1 E2 e Φ `{!Atomic StronglyAtomic e} s :
  (|={E1,E2}=> WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros "H". rewrite !wp_unfold /wp_pre.
  iIntros (σ1 e1' σ1' ε1) "(Hσ & Hs & Hε)".
  iDestruct ("H" with "[$]") as ">> H".
  iModIntro.
  iApply (meas_spec_coupl_mono with "[] H"); [done|].
  iIntros (σ2 e2' σ2' ε2) "H".
  destruct (to_val e) as [v|] eqn:?.
  { iDestruct "H" as "> ($ & $ & $ & $)". }
  (* iDestruct (meas_prog_coupl_strengthen with "H") as "H". *)
  iApply (meas_prog_coupl_mono with "[] H").
  iIntros (?????) "H !>".
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
    (* Check atomic. My version of atomic is different than theirs so that's the difference *)
    admit.
Admitted. (** VERY UNSURE *) (* I don't know if there's some way to prove this without proving prog_coupl_strengthen *)
    (*
    iDestruct (meas_prog_coupl_reducible with "H") as %[ρ Hr].
    pose proof (atomic _ _ _ Hstep) as [? Hval].
    apply val_stuck in Hr. simplify_eq.
Qed.
*)

Lemma wp_step_fupd E1 E2 e P Φ s :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> P) -∗ WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ s; E1 {{ Φ }}.
Proof.
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
Qed.

Lemma wp_bind K `{!MeasLanguageCtx K} E e Φ s :
  WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }} ⊢ WP K e @ s; E {{ Φ }}.
Proof.
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
  iApply meas_prog_coupl_ctx_bind; [done|done|].
  iApply (meas_prog_coupl_mono with "[] H").
  iIntros (e3 σ3 e3' σ3' ε3) "H !>".
  iApply (meas_spec_coupl_mono with "[] H"); [done|].
  iIntros (σ4 e4' σ4' ε4) "H".
  iMod "H" as "($ & $ & $ & H)".
  iModIntro.
  by iApply "IH".
Qed.

Lemma spec_update_wp E e Φ a :
  spec_update E (WP e @ a; E {{ Φ }}) ⊢ WP e @ a; E {{ Φ }}.
Proof.
  iIntros "Hspec".
  iEval (rewrite !wp_unfold /wp_pre).
  iIntros (σ1 e1' σ1' ε1) "(Hσ & Hs & Hε)".
  rewrite spec_update_unseal.
  iMod ("Hspec" with "Hs")
    as ([e2' σ2'] n Hstep) "(Hs & Hwp)". (* Hstep%stepN_pexec_det *)
  iEval (rewrite !wp_unfold /wp_pre) in "Hwp".
  iMod ("Hwp" with "[$]") as "Hwp".
  iModIntro.
  iApply meas_spec_coupl_steps_det; [|done].
  (* stepN_pexec_det *)  admit.
Admitted.

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
      as ([e3' σ3'] n Hstep) "(Hs & Hwp)". (* Hstep%stepN_pexec_det *)
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".
    iApply meas_spec_coupl_steps_det.
    { (* stepN_pexec_det *)  admit. }
    iApply meas_spec_coupl_ret.
    iMod "Hclose".
    by iFrame. }
  iApply meas_spec_coupl_ret.
  iApply (meas_prog_coupl_mono with "[] H").
  iIntros (e2 σ3 e3' σ3' ε3) "H !>".
  iApply (meas_spec_coupl_mono with "[] H"); [done|].
  iIntros (σ4 e4' σ4' ε4) "> ($ & $ & $ & H)".
  iApply ("IH" with "H").
Admitted.

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
Proof.
  iIntros "[? H]".
  iApply (wp_strong_mono with "H"); [done|].
  iIntros (?????) "(? & ? & ? & ?)".
  iApply meas_spec_coupl_ret. by iFrame.
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

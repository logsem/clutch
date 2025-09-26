From Coq Require Export Reals Psatz.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre fixpoint big_op.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext NNRbar.
From clutch.common Require Export language erasable.
From clutch.base_logic Require Export spec_update.
From clutch.prob Require Export couplings_app distribution.
From clutch.approxis Require Import app_weakestpre.


From clutch.prob_eff_lang Require Import iEff.
From clutch.prob_eff_lang Require Import lang protocol_agreement.



Import uPred.

Local Open Scope R.

(* Class approxisWpGS (Λ : language) (Σ : gFunctors) `{!spec_updateGS (lang_markov Λ) Σ} := ApproxisWpGS {
     #[global] approxisWpGS_invGS :: invGS_gen HasNoLc Σ;
   
     state_interp : state → iProp Σ;
     err_interp : nonnegreal → iProp Σ;
   }.
   Global Opaque approxisWpGS_invGS.
   Global Arguments ApproxisWpGS {Λ Σ _}. *)

Canonical Structure NNRO := leibnizO nonnegreal.
(* TODO: move *)
#[global] Hint Resolve cond_nonneg : core.

(* (** * Coupling modalities  *)
   Section coupl_modalities.
     Context `{!spec_updateGS (lang_markov eff_prob_lang) Σ, !approxisWpGS eff_prob_lang Σ}.
   
     (** ** [spec_coupl]  *)
     (** The [spec_coupl] modality allows us to (optionally) prepend spec execution steps and erasable
         distributions, e.g. [state_step]s on both sides. *)
   Definition spec_coupl_pre E Z (Φ : state * cfg * nonnegreal → iProp Σ) : state * cfg * nonnegreal → iProp Σ :=
       (λ (x : state * cfg * nonnegreal),
         let '(σ1, (e1', σ1'), ε) := x in
         ⌜1 <= ε⌝ ∨
         (Z σ1 e1' σ1' ε) ∨
         (∃ (S : state → cfg → Prop) (n : nat) (μ1 : distr (state)) (μ1' : distr (state))
            (ε1 : nonnegreal) (X2 : cfg → nonnegreal) (r : R),
            ⌜ARcoupl μ1 (σ2' ← μ1'; pexec n (e1', σ2')) S ε1⌝ ∗
            ⌜∀ ρ, X2 ρ <= r⌝ ∗
            ⌜ε1 + Expval (σ2' ← μ1'; pexec n (e1', σ2')) X2 <= ε⌝ ∗
            ⌜erasable μ1 σ1⌝ ∗ ⌜erasable μ1' σ1'⌝ ∗
            ∀ σ2 e2' σ2', ⌜S σ2 (e2', σ2')⌝ ={E}=∗ Φ (σ2, (e2', σ2'), X2 (e2', σ2'))))%I.
   
     #[local] Instance spec_coupl_pre_ne Z E Φ :
       NonExpansive (spec_coupl_pre E Z Φ).
     Proof.
       rewrite /spec_coupl_pre.
       intros ? ((?&?&?) & ?) ((?&?&?) & ?) ([[=] ([=] & [=])] & [=]).
       by simplify_eq/=.
     Qed.
   
     #[local] Instance spec_coupl_pre_mono Z E : BiMonoPred (spec_coupl_pre Z E).
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
   
     Implicit Type ε : nonnegreal.
   
     Definition spec_coupl' E Z := bi_least_fixpoint (spec_coupl_pre E Z).
     Definition spec_coupl E σ e' σ' ε Z := spec_coupl' E Z (σ, (e', σ'), ε).
   
     Lemma spec_coupl_unfold E σ1 e1' σ1' ε Z :
       spec_coupl E σ1 e1' σ1' ε Z ≡
         (⌜1 <= ε⌝ ∨
         (Z σ1 e1' σ1' ε) ∨
         (∃ (S : state → cfg → Prop) (n : nat) (μ1 : distr (state)) (μ1' : distr (state))
            (ε1 : nonnegreal) (X2 : cfg → nonnegreal) (r : R),
            ⌜ARcoupl μ1 (σ2' ← μ1'; pexec n (e1', σ2')) S ε1⌝ ∗
            ⌜∀ ρ, X2 ρ <= r⌝ ∗
            ⌜ε1 + Expval (σ2 ← μ1'; pexec n (e1', σ2)) X2 <= ε⌝ ∗
            ⌜erasable μ1 σ1⌝ ∗ ⌜erasable μ1' σ1'⌝ ∗
            ∀ σ2 e2' σ2', ⌜S σ2 (e2', σ2')⌝ ={E}=∗ spec_coupl E σ2 e2' σ2' (X2 (e2', σ2')) Z))%I.
     Proof. rewrite /spec_coupl /spec_coupl' least_fixpoint_unfold //. Qed.
   
     Lemma spec_coupl_ret_err_ge_1 E σ1 e1' σ1' Z (ε : nonnegreal) :
       1 <= ε → ⊢ spec_coupl E σ1 e1' σ1' ε Z.
     Proof. iIntros. rewrite spec_coupl_unfold. by iLeft. Qed.
   
     Lemma spec_coupl_ret E σ1 e1' σ1' Z ε :
       Z σ1 e1' σ1' ε -∗ spec_coupl E σ1 e1' σ1' ε Z.
     Proof. iIntros. rewrite spec_coupl_unfold. by iRight; iLeft. Qed.
   
     Lemma spec_coupl_rec σ1 e1' σ1' E (ε : nonnegreal) Z :
       (∃ (S : state → cfg → Prop) (n : nat) (μ1 : distr (state)) (μ1' : distr (state))
          (ε1 : nonnegreal) (X2 : cfg → nonnegreal) (r : R),
          ⌜ARcoupl μ1 (σ2' ← μ1'; pexec n (e1', σ2')) S ε1⌝ ∗
          ⌜∀ ρ, X2 ρ <= r⌝ ∗
          ⌜ε1 + Expval (σ2 ← μ1'; pexec n (e1', σ2)) X2 <= ε⌝ ∗
          ⌜erasable μ1 σ1⌝ ∗ ⌜erasable μ1' σ1'⌝ ∗
          ∀ σ2 e2' σ2', ⌜S σ2 (e2', σ2')⌝ ={E}=∗ spec_coupl E σ2 e2' σ2' (X2 (e2', σ2')) Z)%I
       ⊢ spec_coupl E σ1 e1' σ1' ε Z.
     Proof. iIntros "H". rewrite spec_coupl_unfold. iRight; iRight. done. Qed.
   
     Lemma spec_coupl_ind E (Ψ Z : state → expr  → state → nonnegreal → iProp Σ) :
       ⊢ (□ (∀ σ e' σ' ε,
                spec_coupl_pre E Z (λ '(σ, (e', σ'), ε'),
                    Ψ σ e' σ' ε' ∧ spec_coupl E σ e' σ' ε' Z)%I (σ, (e', σ'), ε) -∗ Ψ σ e' σ' ε) →
          ∀ σ e' σ' ε, spec_coupl E σ e' σ' ε Z -∗ Ψ σ e' σ' ε)%I.
     Proof.
       iIntros "#IH" (σ e' σ' ε) "H".
       set (Ψ' := (λ '(σ, (e', σ'), ε), Ψ σ e' σ' ε) :
              (prodO (prodO (stateO ) (prodO (exprO ) (stateO))) NNRO) → iProp Σ).
       assert (NonExpansive Ψ').
       { intros n [[σ1 [e1' σ1']] ε1] [[σ2 [e2' σ2']] ε2].
         intros ([[=] ([=] & [=])] & [=]).
         by simplify_eq/=. }
       iApply (least_fixpoint_ind _ Ψ' with "[] H").
       iIntros "!#" ([[? [??]] ?]) "H". by iApply "IH".
     Qed.
   
     Lemma fupd_spec_coupl E σ1 e1' σ1' Z (ε : nonnegreal) :
       (|={E}=> spec_coupl E σ1 e1' σ1' ε Z) ⊢ spec_coupl E σ1 e1' σ1' ε Z.
     Proof.
       iIntros "H".
       iApply spec_coupl_rec.
       iExists _, 0%nat, (dret σ1), (dret σ1'), 0%NNR, (λ _, ε), ε.
       rewrite dret_id_left pexec_O.
       iSplit; [iPureIntro|].
       { by apply ARcoupl_pos_R, (ARcoupl_dret _ _ (λ _ _, True)). }
       iSplit; [done|].
       iSplit; [iPureIntro|].
       { rewrite Rplus_0_l Expval_dret //. }
       do 2 (iSplit; [iPureIntro; apply dret_erasable|]).
       by iIntros (??? (_ & ->%dret_pos & [=-> ->]%dret_pos)).
     Qed.
   
     Lemma spec_coupl_mono E1 E2 σ1 e1' σ1' Z1 Z2 ε :
       E1 ⊆ E2 →
       (∀ σ2 e2' σ2' ε', Z1 σ2 e2' σ2' ε' -∗ Z2 σ2 e2' σ2' ε') -∗
       spec_coupl E1 σ1 e1' σ1' ε Z1 -∗ spec_coupl E2 σ1 e1' σ1' ε Z2.
     Proof.
       iIntros (HE) "HZ Hs".
       iRevert "HZ".
       iRevert (σ1 e1' σ1' ε) "Hs".
       iApply spec_coupl_ind.
       iIntros "!#" (σ e' σ' ε)
         "[% | [? | (% & % & % & % & % & % & % & % & % & % & % & % & H)]] Hw".
       - iApply spec_coupl_ret_err_ge_1. lra.
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
     Qed.
   
     Lemma spec_coupl_mono_err ε1 ε2 E σ1 e1' σ1' Z :
       ε1 <= ε2 → spec_coupl E σ1 e1' σ1' ε1 Z -∗ spec_coupl E σ1 e1' σ1' ε2 Z.
     Proof.
       iIntros (Heps) "Hs".
       iApply spec_coupl_rec.
       set (ε' := nnreal_minus ε2 ε1 Heps).
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
     Qed.
   
     Lemma spec_coupl_bind E1 E2 σ1 e1' σ1' Z1 Z2 ε :
       E1 ⊆ E2 →
       (∀ σ2 e2' σ2' ε', Z1 σ2 e2' σ2' ε' -∗ spec_coupl E2 σ2 e2' σ2' ε' Z2) -∗
       spec_coupl E1 σ1 e1' σ1' ε Z1 -∗
       spec_coupl E2 σ1 e1' σ1' ε Z2.
     Proof.
       iIntros (HE) "HZ Hs".
       iRevert "HZ".
       iRevert (σ1 e1' σ1' ε) "Hs".
       iApply spec_coupl_ind.
       iIntros "!#" (σ e' σ' ε)
         "[% | [H | (%R & %n & %μ1 & %μ1' & %ε1' & %X2 & %r & % & % & % & % & % & H)]] HZ".
       - by iApply spec_coupl_ret_err_ge_1.
       - iApply ("HZ" with "H").
       - iApply spec_coupl_rec.
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
   
     Lemma spec_coupl_erasables_exp (X2 : _ → nonnegreal) (r : R) ε1 ε R μ1 μ1' E σ1 e1' σ1' Z :
       ARcoupl μ1 μ1' R ε1 →
       erasable μ1 σ1 →
       erasable μ1' σ1' →
       (∀ ρ, X2 ρ <= r) →
       ε1 + Expval μ1' X2 <= ε →
       (∀ σ2 σ2', ⌜R σ2 σ2'⌝ ={E}=∗ spec_coupl E σ2 e1' σ2' (X2 σ2') Z)
       ⊢ spec_coupl E σ1 e1' σ1' ε Z.
     Proof.
       iIntros (???? Hε) "H".
       iApply spec_coupl_rec.    
       set X2' := (λ (ρ : cfg), X2 ρ.2).
       iExists (λ σ2 '(e2', σ2'), R σ2 σ2' ∧ e2' = e1'), 0%nat, μ1, μ1', ε1, X2', r.
       iSplit; [iPureIntro|].
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
     Qed. 
   
     Lemma spec_coupl_erasables R μ1 μ1' ε1 ε2 ε E σ1 e1' σ1' Z :
       ε = (ε1 + ε2)%NNR →
       ARcoupl μ1 μ1' R ε1 →
       erasable μ1 σ1 →
       erasable μ1' σ1' →
       (∀ σ2 σ2', ⌜R σ2 σ2'⌝ ={E}=∗ spec_coupl E σ2 e1' σ2' ε2 Z)
       ⊢ spec_coupl E σ1 e1' σ1' ε Z.
     Proof.
       iIntros (-> ???) "H".
       iApply (spec_coupl_erasables_exp (λ _, ε2) ε2); [done|done|done|done| |done].
       rewrite Expval_const //=.
       apply Rle_plus_plus; [done|]. real_solver. 
     Qed.
   
     Lemma spec_coupl_erasable_steps n R μ1 ε1 ε2 ε E σ1 e1' σ1' Z :
       ε = (ε1 + ε2)%NNR →
       ARcoupl μ1 (pexec n (e1', σ1')) R ε1 →
       erasable μ1 σ1 →
       (∀ σ2 e2' σ2', ⌜R σ2 (e2', σ2')⌝ ={E}=∗ spec_coupl E σ2 e2' σ2' ε2 Z)
       ⊢ spec_coupl E σ1 e1' σ1' ε Z.
     Proof.
       iIntros (-> ??) "H".
       iApply spec_coupl_rec.
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
     Qed.
   
     Lemma spec_coupl_steps n ε2 ε1 ε R E σ1 e1' σ1' Z :
       ε = (ε1 + ε2)%NNR →
       ARcoupl (dret σ1) (pexec n (e1', σ1')) R ε1 →
       (∀ σ2 e2' σ2', ⌜R σ2 (e2', σ2')⌝ ={E}=∗ spec_coupl E σ2 e2' σ2' ε2 Z)
       ⊢ spec_coupl E σ1 e1' σ1' ε Z.
     Proof.
       iIntros (-> ?) "H".
       iApply (spec_coupl_erasable_steps n _ _ ε1 ε2); [done| |apply dret_erasable|].
       { by apply ARcoupl_pos_R. }
       iIntros (??? (? & ->%dret_pos & ?)).
       by iApply "H".
     Qed.
   
     Lemma spec_coupl_steps_det n ε σ1 e1' σ1' e2' σ2' Z E :
       pexec n (e1', σ1') (e2', σ2') = 1 →
       spec_coupl E σ1 e2' σ2' ε Z ⊢
       spec_coupl E σ1 e1' σ1' ε Z.
     Proof.
       iIntros (Hexec%pmf_1_eq_dret) "H".
       iApply (spec_coupl_steps n ε 0%NNR).
       { apply nnreal_ext => /=. lra. }
       { apply ARcoupl_pos_R, ARcoupl_trivial; [solve_distr_mass|].
         rewrite Hexec. solve_distr_mass. }
       rewrite Hexec.
       iIntros (??? (_ & ->%dret_pos & [=-> ->]%dret_pos)).
       done.
     Qed.
   
     Lemma spec_coupl_step ε E σ1 e1' σ1' Z :
       reducible (e1', σ1') →
       (∀ e2' σ2', ⌜prim_step e1' σ1' (e2', σ2') > 0%R⌝ ={E}=∗ spec_coupl E σ1 e2' σ2' ε Z)
       ⊢ spec_coupl E σ1 e1' σ1' ε Z.
     Proof.
       iIntros (?) "H".
       iApply (spec_coupl_steps 1 ε 0%NNR).
       { apply nnreal_ext => /=. lra. }
       { rewrite pexec_1 step_or_final_no_final; [|by apply reducible_not_final].
         apply ARcoupl_pos_R, ARcoupl_trivial; [solve_distr_mass|].
         by apply prim_step_mass. }
       iIntros (??? (?&->%dret_pos&?)).
       by iApply "H".
     Qed.
   
     (** * [prog_coupl] *)
   
     (** The [prog_coupl] modality allows us to coupl *exactly* one program step with any number of
         spec execution steps and an erasable distribution *)
     Definition prog_coupl e1 σ1 e1' σ1' ε Z : iProp Σ :=
       ∃ (R : cfg → cfg → Prop) (n : nat) (μ1' : distr (state))
         (ε1 : nonnegreal) (X2 : cfg → nonnegreal) (r : nonnegreal),
         ⌜reducible (e1, σ1)⌝ ∗
         ⌜ARcoupl (prim_step e1 σ1) (σ2' ← μ1'; pexec n (e1', σ2')) R ε1⌝ ∗
         ⌜∀ ρ, X2 ρ <= r⌝ ∗
         ⌜ε1 + Expval (prim_step e1 σ1) X2 <= ε⌝ ∗
         ⌜erasable μ1' σ1'⌝ ∗
         ∀ e2 σ2 e2' σ2', ⌜R (e2, σ2) (e2', σ2')⌝ ={∅}=∗ Z e2 σ2 e2' σ2' (X2 (e2, σ2)).
   
     Lemma prog_coupl_strong_mono e1 σ1 e1' σ1' Z1 Z2 ε :
       (∀ e2 σ2 e2' σ2' ε', ⌜∃ σ, prim_step e1 σ (e2, σ2) > 0⌝ ∗ Z1 e2 σ2 e2' σ2' ε' -∗ Z2 e2 σ2 e2' σ2' ε') -∗
       prog_coupl e1 σ1 e1' σ1' ε Z1 -∗ prog_coupl e1 σ1 e1' σ1' ε Z2.
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
   
     Lemma prog_coupl_mono e1 σ1 e1' σ1' Z1 Z2 ε :
       (∀ e2 σ2 e2' σ2' ε', Z1 e2 σ2 e2' σ2' ε' -∗ Z2 e2 σ2 e2' σ2' ε') -∗
       prog_coupl e1 σ1 e1' σ1' ε Z1 -∗ prog_coupl e1 σ1 e1' σ1' ε Z2.
     Proof.
       iIntros "Hm".
       iApply prog_coupl_strong_mono.
       iIntros (?????) "[_ H]". by iApply "Hm".
     Qed.
   
     Lemma prog_coupl_strengthen e1 σ1 e1' σ1' Z ε :
       prog_coupl e1 σ1 e1' σ1' ε Z -∗
       prog_coupl e1 σ1 e1' σ1' ε (λ e2 σ2 e2' σ2' ε', ⌜∃ σ, prim_step e1 σ (e2, σ2) > 0⌝ ∧ Z e2 σ2 e2' σ2' ε').
     Proof.
       iApply prog_coupl_strong_mono. iIntros (?????) "[$ $]".
     Qed.
   
   
   
     Lemma prog_coupl_steps ε2 ε1 ε R e1 σ1 e1' σ1' Z :
       ε = (ε1 + ε2)%NNR →
       reducible (e1, σ1) →
       reducible (e1', σ1') →
       ARcoupl (prim_step e1 σ1) (prim_step e1' σ1') R ε1 →
       (∀ e2 σ2 e2' σ2', ⌜R (e2, σ2) (e2', σ2')⌝ ={∅}=∗ Z e2 σ2 e2' σ2' ε2)
       ⊢ prog_coupl e1 σ1 e1' σ1' ε Z.
     Proof.
       iIntros (-> Hred Hred' Hcpl) "Hcnt".
       iExists _, 1%nat, (dret σ1'), ε1, (λ _, ε2), ε2.
       iSplit; [done|].
       rewrite dret_id_left pexec_1.
       rewrite step_or_final_no_final; [|by apply reducible_not_final].
       do 2 (iSplit; [done|]).
       iSplit; [iPureIntro|].
       { rewrite Expval_const //. rewrite prim_step_mass //=. lra. }
       iSplit; [iPureIntro; apply dret_erasable|].
       done.
     Qed.
   
     Lemma prog_coupl_step_l_erasable ε2 ε1 μ1' ε R e1 σ1 e1' σ1' Z :
       ε = (ε1 + ε2)%NNR →
       reducible (e1, σ1) →
       ARcoupl (prim_step e1 σ1) μ1' R ε1 →
       erasable μ1' σ1' →
       (∀ e2 σ2 σ2', ⌜R (e2, σ2) σ2'⌝ ={∅}=∗ Z e2 σ2 e1' σ2' ε2)
       ⊢ prog_coupl e1 σ1 e1' σ1' ε Z.
     Proof.
       iIntros (-> ? ? ?) "H".
       iExists (λ ρ2 '(e2', σ2'), R ρ2 σ2' ∧ e2' = e1'), 0%nat, μ1', ε1, (λ _, ε2), ε2.
       iSplit; [done|].
       iSplit; [iPureIntro|].
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
     Qed.     
   
     Lemma prog_coupl_step_l_dret ε2 ε1 ε R e1 σ1 e1' σ1' Z :
       ε = (ε1 + ε2)%NNR →
       reducible (e1, σ1) →
       ARcoupl (prim_step e1 σ1) (dret σ1') R ε1 →
       (∀ e2 σ2, ⌜R (e2, σ2) σ1'⌝ ={∅}=∗ Z e2 σ2 e1' σ1' ε2)
       ⊢ prog_coupl e1 σ1 e1' σ1' ε Z.
     Proof.
       iIntros (-> ? ?) "H".
       iApply (prog_coupl_step_l_erasable _ _ (dret (σ1'))); [done|done|..].
       { by apply ARcoupl_pos_R. }
       { apply dret_erasable. }
       iIntros (??? (?&?&->%dret_pos)).
       by iApply "H".
     Qed.
   
     Lemma prog_coupl_step_l e1 σ1 e1' σ1' ε Z :
       reducible (e1, σ1) →
       (∀ e2 σ2, ⌜prim_step e1 σ1 (e2, σ2) > 0⌝ ={∅}=∗ Z e2 σ2 e1' σ1' ε)
       ⊢ prog_coupl e1 σ1 e1' σ1' ε Z.
     Proof.
       iIntros (?) "H".
       iApply (prog_coupl_step_l_dret ε 0%NNR); [|done|..].
       { apply nnreal_ext => /=. lra. }
       { eapply ARcoupl_pos_R, ARcoupl_trivial.
         - by apply prim_step_mass.
         - apply dret_mass. }
       iIntros (?? (_ & ? & [=]%dret_pos)).
       by iApply "H".
     Qed.
   
     Lemma prog_coupl_reducible e e' σ σ' Z ε :
       prog_coupl e σ e' σ' ε Z -∗ ⌜reducible (e, σ)⌝.  Proof. by iIntros "(%&%&%&%&%&%&%&%& _)". Qed.
   
   End coupl_modalities. *)


(** * The weakest precondition  *)
Definition ewp_pre `{!spec_updateGS (lang_markov eff_prob_lang) Σ, !approxisWpGS eff_prob_lang Σ}
    (ewp : coPset -d> expr -d> iEff Σ -d> (val -d> iPropO Σ) -d> iPropO Σ) :
  coPset -d> expr -d> iEff Σ -d> (val -d> iPropO Σ) -d> iPropO Σ := λ E e1 Ψ Φ,
  (∀ σ1 e1' σ1' ε1,
      state_interp σ1 ∗ spec_interp (e1', σ1') ∗ err_interp ε1 ={E, ∅}=∗
      spec_coupl ∅ σ1 e1' σ1' ε1 (λ σ2 e2' σ2' ε2,
        match to_val e1 with
        | Some v => |={∅, E}=> state_interp σ2 ∗ spec_interp (e2', σ2') ∗ err_interp ε2 ∗ Φ v
        | None =>
            match to_eff e1 with
            | Some (v, K) =>
                |={∅, E}=> state_interp σ2 ∗ spec_interp (e2', σ2') ∗ err_interp ε2
                           ∗ protocol_agreement v Ψ (λ w, ▷ ewp E (fill K (Val w)) Ψ Φ)
            | None => 
                prog_coupl e1 σ2 e2' σ2' ε2 (λ e3 σ3 e3' σ3' ε3,
                                               ▷ spec_coupl ∅ σ3 e3' σ3' ε3 (λ σ4 e4' σ4' ε4,
                                                                               |={∅, E}=> state_interp σ4 ∗ spec_interp (e4', σ4') ∗ err_interp ε4 ∗ ewp E e3 Ψ Φ))
            end
      end))%I.

Local Instance ewp_pre_contractive `{!spec_updateGS (lang_markov eff_prob_lang) Σ, !approxisWpGS eff_prob_lang Σ} :
  Contractive ewp_pre.
Proof.
  rewrite /ewp_pre /= /protocol_agreement => n ewp ewp' Hewp E e1 Ψ Φ.
  do 10 f_equiv.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [? [? ?]]. rewrite /spec_coupl_pre.
  do 6 f_equiv.
  { do 12 f_equiv. f_contractive. apply Hewp. }
  rewrite /prog_coupl.
  do 27 f_equiv.
  f_contractive.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [? [? ?]]. rewrite /spec_coupl_pre.
  do 8 f_equiv.
  apply Hewp.
Qed.

(* Local Definition wp_def `{!spec_updateGS (lang_markov eff_prob_lang) Σ, !approxisWpGS Σ} :
     Wp (iProp Σ) (expr) (val) () :=
     {| wp := λ _ : (), fixpoint (wp_pre); wp_default := () |}. *)
Definition ewp_def `{!spec_updateGS (lang_markov eff_prob_lang) Σ, !approxisWpGS eff_prob_lang Σ} :
  coPset -d> expr -d> iEff Σ -d> (val -d> iPropO Σ) -d> iPropO Σ :=
  fixpoint ewp_pre.

Local Definition ewp_aux : seal (@ewp_def). Proof. by eexists. Qed.
Definition ewp' := ewp_aux.(unseal).
Global Arguments ewp' {Σ _}.
(* Global Existing Instance wp'.     I don't know what this is for  *)
(* Local Lemma wp_unseal `{!spec_updateGS (lang_markov eff_prob_lang) Σ, !approxisWpGS Σ} : wp =
     (@wp_def Σ _ _).(wp).
   Proof. rewrite -wp_aux.(seal_eq) //. Qed. *)


Notation "'EWP' e @ E  <| Ψ '|' '>' {{ v , Φ } }" :=
  (ewp_def E e%E Ψ%ieff (λ v, Φ)%I)
  (at level 20, e, E, Ψ, Φ at level 200,
     format "'[' 'EWP'  e  '/' '[' @ E <|  Ψ  '|' '>'  {{  v ,  Φ  } } ']' ']'") : bi_scope.

Notation "'EWP' e @ E  <| Ψ '|' '>' {{ Φ } }" :=
  (ewp_def E e%E Ψ%ieff Φ)
  (at level 20, e, E, Ψ, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[' @ E <|  Ψ  '|' '>'  {{ Φ } } ']' ']'") : bi_scope.

Section ewp.
Context `{!spec_updateGS (lang_markov eff_prob_lang) Σ, !approxisWpGS eff_prob_lang Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types v : val.
Implicit Types e : expr.
Implicit Types σ : state.
Implicit Types ρ : cfg.

(* Weakest pre *)
Lemma ewp_unfold E e Ψ Φ :
  EWP e @ E <| Ψ |> {{ Φ }} ⊣⊢ ewp_pre ewp_def E e Ψ Φ.
Proof. apply (fixpoint_unfold ewp_pre). Qed.

Global Instance ewp_ne E e n :
  Proper ((dist n) ==> (pointwise_relation _ (dist n)) ==> dist n) (ewp_def E e).
Proof.
  revert e. induction (lt_wf n) as [n _ IH]=> e Ψ Ψ' HΨ Φ Φ' HΦ.
  rewrite !ewp_unfold /ewp_pre /= /protocol_agreement.
  do 10 f_equiv.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [? [? ?]]. rewrite /spec_coupl_pre /prog_coupl.
  do 15 f_equiv.
  - apply HΨ.
  - do 3 f_equiv. f_contractive_fin.
    apply IH; eauto using dist_S. f_equiv. apply dist_S. apply HΦ. 
  - do 18 f_equiv.
  f_contractive_fin.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [? [? ?]]. rewrite /spec_coupl_pre.
  do 8 f_equiv.
  rewrite IH; [done|lia| |]; intros ?; apply dist_S;
    [apply HΨ | apply HΦ].
Qed.
Global Instance ewp_proper E e :
  Proper ((≡) ==> pointwise_relation _ (≡) ==> (≡)) (ewp_def E e).
Proof.
  intros Ψ Ψ' ? Φ Φ' ?; apply equiv_dist=>n; apply ewp_ne=>v; apply equiv_dist; eauto.
Qed.
(* Global Instance wp_contractive E e n :
     TCEq (to_val e) None →
     Proper (dist_later n ==> pointwise_relation _ (dist_later n) ==> dist n) (wp_def E e).
   Proof.
     intros He Ψ Ψ' HΨ Φ Φ' HΦ. rewrite !wp_unfold /wp_pre He /= /protocol_agreement.
     do 10 f_equiv.
     apply least_fixpoint_ne_outer; [|done].
     intros ? [? [? ?]]. rewrite /spec_coupl_pre.
     rewrite /prog_coupl.
     do 12 f_equiv.
     - f_equiv. eauto.
     - do 5 f_equiv.
       + eauto.
              
     f_contractive.
     apply least_fixpoint_ne_outer; [|done].
     intros ? [? [? ?]]. rewrite /spec_coupl_pre.
     do 22 f_equiv.
   Qed. *)

Lemma ewp_eff E Ψ Φ v k :
  protocol_agreement v Ψ (λ w, ▷ EWP fill k (Val w) @ E <| Ψ |> {{ Φ }}) ⊢
  EWP Eff v k @ E <| Ψ |> {{ Φ }}.
Proof.
  rewrite ewp_unfold /ewp_pre /=. iIntros "HP" (σ1 e1' σ1' ε1) "(Hstate & Hspec & Herr)".
  iApply spec_coupl_ret. iFrame. iApply fupd_mask_subseteq. set_solver.
Qed.


Lemma ewp_value_fupd' E Ψ Φ v : (|={E}=> Φ v) ⊢ EWP of_val v @ E <| Ψ |> {{ Φ }}.
Proof.
  rewrite ewp_unfold /ewp_pre to_of_val.
  iIntros "H" (????) "(?&?&?)".
  iApply spec_coupl_ret.
  iMod "H". iFrame.
  iApply fupd_mask_subseteq.
  set_solver.
Qed.

Lemma ewp_strong_mono E1 E2 e Φ1 Φ2 Ψ1 Ψ2 :
  E1 ⊆ E2 →
  EWP e @ E1 <| Ψ1 |> {{ Φ1 }} -∗
  □(∀ (u : val) Φ, protocol_agreement u Ψ1 Φ -∗ protocol_agreement u Ψ2 Φ) -∗ (* Is this the right notion for Ψ1 ⊑ Ψ2? *)
  □(∀ σ1 e1' σ1' ε1 v,        (* Can I add a box here? *)
        state_interp σ1 ∗ spec_interp (e1', σ1') ∗ err_interp ε1 ∗ Φ1 v -∗
        spec_coupl ∅ σ1 e1' σ1' ε1 (λ σ2 e2' σ2' ε2,
                                      |={E2}=> state_interp σ2 ∗ spec_interp (e2', σ2') ∗ err_interp ε2 ∗ Φ2 v)) -∗
  EWP e @ E2 <| Ψ2 |> {{ Φ2 }}.
Proof.
  iIntros (HE) "H HΨ HΦ". iLöb as "IH" forall (e E1 E2 HE Φ1 Φ2 Ψ1 Ψ2).
  rewrite !ewp_unfold /ewp_pre /=.
  iIntros (σ1 e1' σ1' ε1) "(Hσ & Hs & Hε)".
  iSpecialize ("H" with "[$]").
  iMod (fupd_mask_subseteq E1) as "Hclose"; [done|].
  iMod "H"; iModIntro.
  iApply (spec_coupl_bind with "[-H] H"); [done|].
  iIntros (????) "H".
  destruct (to_val e) as [v|] eqn:?.
  { iApply fupd_spec_coupl.
    iMod "H" as "(?&?&?)".
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iSpecialize ("HΦ" with "[$]").
    iApply (spec_coupl_bind with "[-HΦ] HΦ"); [done|].
    iIntros (????) "Hσ".
    iApply spec_coupl_ret.
    iMod "Hclose'". iMod "Hclose".
    by iMod "Hσ". }
  destruct (to_eff e) as [(v, K)|] eqn:?.
  { iApply spec_coupl_ret.
    iMod "H" as "(?&?&?&%Q&?&H)".
    iFrame.
    iDestruct "HΨ" as "#HΨ".
    iDestruct "HΦ" as "#HΦ".
    iDestruct "H" as "#H".
    iApply "HΨ".
    rewrite /protocol_agreement.
    iExists Q. iFrame.
    iApply fupd_wand_r. iFrame.
    iIntros "_".
    iModIntro.
    iIntros (w) "HQ".
    iApply ("IH" with "[] [HQ]"); try done.
    iApply "H". done. }
  iApply spec_coupl_ret.
  iDestruct "HΨ" as "#HΨ".
  iApply (prog_coupl_mono with "[HΦ Hclose] H").
  iIntros (e2 σ3 e3' σ3' ε3) "H !>".
  iApply (spec_coupl_mono with "[HΦ Hclose] H"); [done|].
  iIntros (σ4 e4' σ4' ε4) "> ($ & $ & $ & H)".
  iMod "Hclose" as "_".
  iModIntro.
  by iApply ("IH" with "[] H").
Qed.

Lemma ewp_mono E Ψ Φ Φ' e :
  (∀ v, Φ v ⊢ |={E}=> Φ' v) →
    EWP e @ E <| Ψ |> {{ Φ }} ⊢ EWP e @ E <| Ψ |> {{ Φ' }}.
Proof.
  iIntros (HΦ) "H"; iApply (ewp_strong_mono with "H"); first done.
  { iModIntro. iIntros (??) "$". }
  iModIntro.
  iIntros (?????) "(?&?&?&?)".
  iApply spec_coupl_ret. iFrame.
  by iApply HΦ. 
Qed.




(* Lemma wp_strong_mono' E1 E2 e Φ Ψ s :
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
     iApply spec_coupl_ret.
     by iMod ("Hw" with "[$]").
   Qed. *)

Lemma fupd_ewp E e Φ Ψ : (|={E}=> EWP e @ E <| Ψ |> {{ Φ }}) ⊢ EWP e @ E <| Ψ |> {{ Φ }}.
Proof.
  rewrite ewp_unfold /ewp_pre.
  iIntros "H" (????) "(?&?&?)".
  destruct (to_val e) as [v|] eqn:?.
  { by iMod ("H" with "[$]"). }
  by iMod ("H" with "[$]").
Qed.

Lemma ewp_fupd E e Φ Ψ : EWP e @ E <| Ψ |> {{ v, |={E}=> Φ v }} ⊢ EWP e @ E <| Ψ |> {{ Φ }}.
Proof.
  iIntros "H". 
  iApply (ewp_strong_mono E with "H"); [done| |].
  { iModIntro. iIntros (??) "$". }
  iModIntro.
  iIntros (?????) "(? & ? & ? & ?)".
  iApply spec_coupl_ret.
  by iFrame. 
Qed.

Lemma ewp_atomic E1 E2 e Φ Ψ `{!Atomic StronglyAtomic e} :
  TCEq (to_eff e) None →
  (|={E1,E2}=>
     EWP e @ E2 <| Ψ |> {{ v, |={E2,E1}=> Φ v }}) ⊢
     EWP e @ E1 <| Ψ |> {{ Φ }}.
Proof.
  intro Heff.
  iIntros "H". rewrite !ewp_unfold /ewp_pre.
  iIntros (σ1 e1' σ1' ε1) "(Hσ & Hs & Hε)".
  iDestruct ("H" with "[$]") as ">> H".
  iModIntro.
  iApply (spec_coupl_mono with "[] H"); [done|].
  iIntros (σ2 e2' σ2' ε2) "H".
  destruct (to_val e) as [v|] eqn:?.
  { iDestruct "H" as "> ($ & $ & $ & $)". }
  rewrite Heff.
  iDestruct (prog_coupl_strengthen with "H") as "H".
  iApply (prog_coupl_mono with "[] H").
  iIntros (?????) "[[% %Hstep] H] !>".
  iApply (spec_coupl_bind with "[] H"); [done|].
  iIntros (????) "H".
  iApply fupd_spec_coupl.
  iMod "H" as "(Hσ & Hρ & Hε & H)".
  rewrite !ewp_unfold /ewp_pre.
  destruct (to_val e2) as [v2|] eqn:He2.
  + iMod ("H" with "[$]") as "H". iModIntro.
    iApply (spec_coupl_mono with "[] H"); [done|].
    iIntros (????) "> ($ & $ & $ & >H)".
    rewrite -(of_to_val e2 v2) //.
    iApply ewp_value_fupd'.
    iApply fupd_mask_intro_subseteq; [|done].
    set_solver.
  + destruct (to_eff e2) as [(v2, k2)|] eqn:He2'.
  - iMod ("H" with "[$]") as "H".
    iModIntro.
    iApply (spec_coupl_mono with "[] H"); [done|].
    iIntros (????) "H".
    pose proof (atomic _ _ _ Hstep) as [? Hval].
    naive_solver.
  - iMod ("H" with "[$]") as "H". iModIntro.
    iApply (spec_coupl_mono with "[] H"); [done|].
    iIntros (????) "H". 
    iDestruct (prog_coupl_reducible with "H") as %[ρ Hr].
    pose proof (atomic _ _ _ Hstep) as [? Hval].
    apply val_stuck in Hr. naive_solver.
Qed.

(* Lemma wp_step_fupd E1 E2 e P Φ Ψ :
     TCEq (to_eff e) None →
     TCEq (to_val e) None → E2 ⊆ E1 →
     (|={E1}[E2]▷=> P) -∗ WP e @ E2 <| Ψ |> {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ E1 <| Ψ |> {{ Φ }}.
   Proof.
     rewrite !wp_unfold /wp_pre. iIntros (-> -> ?) "HR H".
     iIntros (σ1 e1' σ1' ε1) "Hs". iMod "HR".
     iMod ("H" with "Hs") as "H".
     iModIntro.
     iApply (spec_coupl_mono with "[HR] H"); [done|].
     iIntros (σ2 e2' σ2' ε2) "H".
     iApply (prog_coupl_mono with "[HR] H").
     iIntros (e3 σ3 e3' σ3' ε3) "H !>".
     iApply (spec_coupl_mono with "[HR] H"); [done|].
     iIntros (σ4 e4' σ4' ε4) "H".
     iMod "H" as "($ & $ & $ & H)".
     iMod "HR".
     iApply (wp_strong_mono E2 with "H"); [done..| iModIntro; naive_solver |].
     iModIntro.                    (* Strong mono is not strong enough. Cannot have the box *)
     iIntros "!>" (?????) "(? & ? & ? & H)".
     iApply spec_coupl_ret. 
   (*   iMod ("H" with "[$]").
        by iFrame.
      Qed. *)
   Admitted. *)


  (* ------------------------------------------------------------------------ *)
  (** Reasoning about Pure Steps. *)

  Lemma ewp_pure_step' E e e' Ψ Φ :
    pure_prim_step e e' → 
      ▷ EWP e' @ E <| Ψ |> {{ Φ }} -∗
      EWP e @ E <| Ψ |> {{ Φ }}.
  Proof.
    intros Hstep.
      destruct (to_val e) as [ v         |] eqn:He;
    [|destruct (to_eff e) as [(v, k)|] eqn:He'].
    - rewrite <- (of_to_val _ _ He) in Hstep. destruct Hstep. pose proof (val_irreducible v inhabitant). rewrite -not_reducible in H.
      by apply H in pure_prim_step_safe.
    - rewrite <- (of_to_eff _ _ _ He') in Hstep. destruct Hstep. pose proof (eff_irreducible v k inhabitant). rewrite -not_reducible in H.
      by apply H in pure_prim_step_safe.
    - rewrite !(ewp_unfold E e) /ewp_pre He He'.
      iIntros "Hwp" (σ1 e1' σ1' ϵ') "(Hs & Hspec & Herr)".
      iMod (fupd_mask_subseteq ∅) as "Hclose"; [by apply empty_subseteq|].
      iModIntro.
      iApply spec_coupl_ret.
      iApply prog_coupl_step_l.  { exists (e', σ1). simpl. pose proof (pure_prim_step_det _ _ Hstep σ1) as H. rewrite H. real_solver. }
      iIntros (e2 σ2 Hprim).
      iModIntro. iNext.
      iApply spec_coupl_ret.
      iMod ("Hclose") as "_". iModIntro.
      iFrame.
      pose proof (pure_prim_step_det _ _  Hstep σ1).
      apply (pure_prim_step_imp_det e e') in Hprim as (-> & ->); eauto.
      iFrame.
  Qed.

  Lemma ewp_pure_step E e e' Ψ Φ :
    pure_prim_step e e' → 
      EWP e' @ E <| Ψ |> {{ Φ }} -∗
        EWP e @ E <| Ψ |> {{ Φ }}.
  Proof. iIntros "% Hwp". by iApply (ewp_pure_step' with "Hwp"). Qed.

  Lemma ewp_pure_steps' E e e' Ψ Φ :
    tc pure_prim_step e e' → 
      ▷ EWP e' @ E <| Ψ |>  {{ Φ }} -∗
          EWP e @ E <| Ψ |> {{ Φ }}.
  Proof.
    intros Hstep; iInduction Hstep as [|] "IH".
    - by iApply ewp_pure_step'.
    - iIntros "Hewp". iApply ewp_pure_step'. { apply H. } iNext. by iApply "IH".
  Qed.

  Lemma ewp_pure_steps E e e' Ψ Φ :
    rtc pure_prim_step e e' → 
      EWP e' @ E <| Ψ |> {{ Φ }} -∗
        EWP e @ E <| Ψ |> {{ Φ }}.
  Proof.
    intros Hstep; iInduction Hstep as [|] "IH".
    - by iIntros "?".  
    - iIntros "Hewp". iApply ewp_pure_step. {apply H. } by iApply "IH".
  Qed.

  (* ------------------------------------------------------------------------ *)
  (** Bind Rule. *)
  
  Lemma ewp_eff_steps k `{NeutralEctx k} E Ψ Φ v k' :
    EWP Eff v (k' ++ k) @ E <| Ψ |> {{ Φ }} -∗
     EWP fill k (Eff v k') @ E <| Ψ |> {{ Φ }}.
  Proof. apply ewp_pure_steps, rtc_pure_prim_step_eff. Qed.

  Lemma fill_app_ctx K K' e : fill K (fill K' e) = fill (K' ++ K) e.
  Proof. unfold fill. by rewrite foldl_app. Qed.

  Lemma prog_coupl_ctx_bind (K : ectx) e1 σ1 e1' σ1' Z ε:
    to_eff e1 = None → 
    to_val e1 = None →
    prog_coupl e1 σ1 e1' σ1' ε (λ e2, Z (fill K e2)) -∗ prog_coupl (fill K e1) σ1 e1' σ1' ε Z.
  Proof.
    iIntros (Heff Hv) "(%R & %n & %μ1' & %ε1 & %X2 & %r & % & % & % & % & % & Hcnt) /=".

    (** (classical) inverse of context [K] *)
    destruct (partial_inv_fun (fill K)) as (Kinv & HKinv).
    assert (∀ e, Kinv (fill K e) = Some e) as HKinv3.
    { intro e.
      destruct (Kinv (fill K e)) eqn:Heq; eapply HKinv in Heq;
        try apply fill_inj in Heq; by simplify_eq. }
    set (X2' := (λ '(e, σ), from_option (λ e', X2 (e', σ)) 0%NNR (Kinv e))).
    assert (∀ e2 σ2, X2' (fill K e2, σ2) = X2 (e2, σ2)) as HX2'.
    { intros. rewrite /X2' HKinv3 //. }
    iExists (λ '(e2, σ2) ρ', ∃ e2', e2 = fill K e2' ∧ R (e2', σ2) ρ'), n, μ1', ε1, X2', r.
    iSplit; [eauto using reducible_fill|].
    iSplit.
    { iPureIntro. simpl.
      rewrite fill_dmap //.
      rewrite -(dret_id_right (μ1' ≫= _ )) //.
      rewrite /dmap.
      eapply (ARcoupl_dbind' _ nnreal_zero); [..|done]; [done|done|simpl; lra|..].
      intros [] ?? => /=. apply ARcoupl_dret; [done|]. eauto. }
    iSplit; [iPureIntro|].
    { intros [e σ]. simpl. destruct (Kinv e) => //=. }
    iSplit; [iPureIntro|].
    { simpl. rewrite fill_dmap // Expval_dmap //=; last first.
      - eapply ex_expval_bounded. intros [] => /=. rewrite HKinv3 //=.
      - etrans; [|done].
        apply Rle_plus_plus; [done|].
        right; apply SeriesC_ext.
        intros [e σ]. rewrite -HX2' //. }
    iSplit; [done|].
    iIntros (e2 σ2 e2' σ2' (e3 & -> & HR)).
    rewrite HX2'.
    by iApply "Hcnt".
  Qed.

  Lemma ewp_bind K `{NeutralEctx K} E e Φ Ψ :
    EWP e @ E <| Ψ |> {{ v, EWP fill K (of_val v) @ E <| Ψ |> {{ Φ }} }} ⊢ EWP fill K e @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "H". iLöb as "IH" forall (E e Φ Ψ).
    destruct (to_val e) as [v|] eqn:He.
    { 
      rewrite !ewp_unfold /ewp_pre.
      iIntros (σ1 e1' σ1' ε1) "Hs".
      iMod ("H" with "[$]") as "H".
      iApply (spec_coupl_bind with "[] H"); [done|].
      iIntros (σ2 e2' σ2' ε2) "H".
      iApply fupd_spec_coupl.
      apply of_to_val in He as <-.
      iMod "H" as "(Hσ & Hs & Hε & H)".
      rewrite ewp_unfold /ewp_pre.
      iApply ("H" with "[$]"). } 
    destruct (to_eff e) as [(v, k) |] eqn:Heff.
    { destruct e=>//=.
      iApply ewp_eff_steps.
      rewrite !ewp_unfold /ewp_pre; simpl.
      iIntros (????) "(Hstate & Hspec & Herr)".
      iMod ("H" with "[$]") as "H". iModIntro.
      iApply spec_coupl_mono; [done| |done].
      iIntros (????) "H". iMod "H". iModIntro.
      iDestruct "H" as "($&$&$&Hwp)".
      unfold protocol_agreement.
      iDestruct "Hwp" as (Q) "(HΨ & #Hr)".
      iExists Q. iFrame. iModIntro.
      iIntros (w) "HQ".
      iDestruct ("Hr" with "HQ") as "Hwp".
      iNext. 
      iDestruct ("IH" with "Hwp") as "Hwp".
      rewrite fill_app_ctx.
      done. }
    rewrite !ewp_unfold /ewp_pre.
    iIntros (σ1 e1' σ1' ε1) "(Hstate & Hspec & Herr)".
    iSpecialize ("H" with "[$]").
    iApply (spec_coupl_bind with "[] H"); [done|].
    iIntros (????) "Hwp". rewrite He. rewrite Heff.
    iApply spec_coupl_ret.
    rewrite fill_not_val; [|done].
    rewrite fill_not_eff; [|done].
    iApply prog_coupl_ctx_bind; [done|done|].
    iApply prog_coupl_mono; try done.
    iIntros (e3 σ3 e3' σ3' ε3') "Hspec". iNext.
    iApply spec_coupl_mono; [done| | iApply "Hspec"].
    iIntros (σ4 e4' σ4' ε4) "H".
    iDestruct (fupd_frame_r with "[IH H]") as "H".
    { iSplitL "H". { iApply "H". } {iApply "IH". } }
    iApply fupd_mono; [ | done].
    iIntros "(($&$&$&Hwp)&IH)". by iApply "IH". 
  Qed.

  Lemma Ectxi_ewp_bind Ki `{NeutralEctxi Ki} E Ψ Φ e e' :
  e' = fill_item Ki e  →
  EWP e  @ E <| Ψ |> {{ v, EWP fill_item Ki (of_val v) @ E <| Ψ |> {{ Φ }} }} ⊢
  EWP e' @ E <| Ψ |> {{ Φ }}.
  Proof. intros ->. by iApply (ewp_bind [Ki]). Qed.

  Lemma ewp_pure_bind K E Ψ Φ e e' :
    e' = fill K e  →
    EWP                 e @ E <| ⊥ |> {{ v,
                                           EWP fill K (of_val v) @ E <| Ψ |> {{ Φ }} }} ⊢
    EWP                e' @ E <| Ψ |> {{ Φ }}.
  Proof.
    intros ->. iLöb as "IH" forall (e).
    destruct (to_val e) as [ v    |] eqn:He;
  [|destruct (to_eff e) as [(v, k)|] eqn:He'].
    - rewrite <- (of_to_val _ _ He).
      iIntros "H".
      rewrite !ewp_unfold /ewp_pre.
      iIntros (????) "(Hstate & Hspec & Herr)".
      iSpecialize ("H" with "[$]"). simpl. 
      iApply (spec_coupl_bind with "[]"); [done| |done].
      iIntros (????) "H".
      iApply fupd_spec_coupl.
      iMod "H" as "(Hσ & Hs & Hε & H)".
      rewrite !ewp_unfold /ewp_pre.
      iSpecialize ("H" $! _ _ _ _ with "[$Hσ $Hs $Hε]").
      done.
    - iIntros "Hprot_agr".
      destruct e=>//=.
      rewrite !ewp_unfold /ewp_pre; simpl.
      iIntros (????) "(Hstate & Hspec & Herr)".
      iMod ("Hprot_agr" with "[$]") as "H". iModIntro.
      iApply spec_coupl_bind; [done| |done].
      iIntros (????) "H".
      iApply fupd_spec_coupl.
      rewrite protocol_agreement_bottom.
      by iMod "H" as "(?&?&?&?)".
    - rewrite !ewp_unfold /ewp_pre.
      iIntros "Hewp" (σ1 e1' σ1' ε1) "(Hstate & Hspec & Herr)".
      iSpecialize ("Hewp" with "[$]").
      iApply (spec_coupl_bind with "[] Hewp"); [done|].
      iIntros (????) "Hwp". rewrite He. rewrite He'.
      iApply spec_coupl_ret.
      rewrite fill_not_val; [|done].
      rewrite fill_not_eff; [|done].
      iApply prog_coupl_ctx_bind; [done|done|].
      iApply prog_coupl_mono; try done.
      iIntros (e3 σ3 e3' σ3' ε3') "Hspec". iNext.
      iApply spec_coupl_mono; [done| | iApply "Hspec"].
      iIntros (σ4 e4' σ4' ε4) "H".
      iDestruct (fupd_frame_r with "[IH H]") as "H".
      { iSplitL "H". { iApply "H". } {iApply "IH". } }
      iApply fupd_mono; [ | done].
      iIntros "(($&$&$&Hwp)&IH)". by iApply "IH". 
  Qed.
  
  
  Lemma spec_update_ewp E e Φ Ψ :
    spec_update E (EWP e @ E <| Ψ |> {{ Φ }}) ⊢ EWP e @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "Hspec".
    iEval (rewrite !ewp_unfold /ewp_pre).
    iIntros (σ1 e1' σ1' ε1) "(Hσ & Hs & Hε)".
    rewrite spec_update_unseal.
    iMod ("Hspec" with "Hs")
      as ([e2' σ2'] n Hstep%stepN_pexec_det) "(Hs & Hwp)".
    iEval (rewrite !ewp_unfold /ewp_pre) in "Hwp".
    iMod ("Hwp" with "[$]") as "Hwp".
    iModIntro.
    by iApply spec_coupl_steps_det.
  Qed.

  Lemma ewp_spec_update E e Φ Ψ :
    EWP e @ E <| Ψ |>{{ v, spec_update E (Φ v) }} ⊢ EWP e @ E <| Ψ |> {{ Φ }}.
  Proof.
  iIntros "Hwp".
  iLöb as "IH" forall (e E Φ Ψ).
  rewrite !ewp_unfold /ewp_pre.
  iIntros (σ1 e1' σ1' ε1) "(Hσ & Hs & Hε)".
  iMod ("Hwp" with "[$]") as "Hwp".
  iModIntro.
  iApply (spec_coupl_bind with "[] Hwp"); [done|].
  iIntros (????) "H".
  destruct (to_val e) as [ v    |] eqn:He;
  [|destruct (to_eff e) as [(v, k)|] eqn:He'].
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
  { iApply fupd_spec_coupl.
    iMod "H" as "(?&?&?& Hupd)".
    rewrite spec_update_unseal.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".
    iApply spec_coupl_ret.
    iFrame.
    iMod "Hclose" as "_". iModIntro.
    iApply (protocol_agreement_mono with "[$]").
    iModIntro. iIntros (w) "Hewp !>". by iApply "IH". }
  iApply spec_coupl_ret.
  iApply (prog_coupl_mono with "[] H").
  iIntros (e2 σ3 e3' σ3' ε3) "H !>".
  iApply (spec_coupl_mono with "[] H"); [done|].
  iIntros (σ4 e4' σ4' ε4) "> ($ & $ & $ & H)".
  iApply ("IH" with "H").
  Qed.
 (*

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
*)
Lemma ewp_value_fupd E Φ Ψ e v : IntoVal e v → (|={E}=> Φ v) ⊢ EWP e @ E <| Ψ |> {{ Φ }}.
Proof. intros <-. by apply ewp_value_fupd'. Qed.
Lemma ewp_value' E Φ Ψ v : Φ v ⊢ EWP (of_val v) @ E <| Ψ |> {{ Φ }}.
Proof. iIntros. by iApply ewp_value_fupd. Qed.
Lemma ewp_value E Φ Ψ e v : IntoVal e v → Φ v ⊢ EWP e @ E <| Ψ |> {{ Φ }}.
Proof. intros <-. apply ewp_value'. Qed.


(* Lemma wp_frame_l E e Φ R s : R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
   Proof.
     iIntros "[? H]".
     iApply (wp_strong_mono with "H"); [done|].
     iIntros (?????) "(? & ? & ? & ?)".
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
Qed. *)

End ewp.


(** * Proofmode class instances *)
Section proofmode_classes.
  Context `{!spec_updateGS (lang_markov eff_prob_lang) Σ, !approxisWpGS eff_prob_lang Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types v : val.
  Implicit Types e : expr.

  (* Global Instance frame_wp p E e R Φ Φ' Ψ :
       (∀ v, Frame p R (Φ v) (Φ' v)) →
       Frame p R (EWP e @ E <| Ψ |> {{ Φ }}) (EWP e @ E <| Ψ |> {{ Φ' }}) | 2.
     Proof. rewrite /Frame=> HR. rewrite ewp_frame_l. apply wp_mono, HR. Qed. *)

  Global Instance is_except_0_ewp E e Φ Ψ : IsExcept0 (EWP e @ E <| Ψ |> {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_ewp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_ewp p E e P Φ Ψ :
    ElimModal True p false (|==> P) P (EWP e @ E <| Ψ |> {{ Φ }}) (EWP e @ E <| Ψ |> {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r wand_elim_r fupd_ewp.
  Qed.

  Global Instance elim_modal_fupd_ewp p E e P Φ Ψ :
    ElimModal True p false (|={E}=> P) P (EWP e @ E <| Ψ |> {{ Φ }}) (EWP e @ E <| Ψ |> {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_ewp.
  Qed.

  (* Global Instance elim_modal_fupd_wp_atomic p E1 E2 e P Φ Ψ :
       ElimModal (Atomic StronglyAtomic e) p false
               (|={E1,E2}=> P) P
               (EWP e @ E1 <| Ψ |> {{ Φ }}) (EWP e @ E2 <| Ψ |> {{ v, |={E2,E1}=> Φ v }})%I | 100.
     Proof.
       intros ??. rewrite intuitionistically_if_elim fupd_frame_r wand_elim_r ewp_atomic //. 
     Qed.
     
     Global Instance add_modal_fupd_wp E e P Φ Ψ :
       AddModal (|={E}=> P) P (EWP e @ E <| Ψ |> {{ Φ }}).
     Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_ewp. Qed.
     
     Global Instance elim_acc_wp_atomic {X} E1 E2 α β γ e Φ Ψ :
       ElimAcc (X:=X) (Atomic StronglyAtomic e)
               (fupd E1 E2) (fupd E2 E1)
               α β γ (EWP e @ E1 <| Ψ |> {{ Φ }})
               (λ x, EWP e @ E2 <| Ψ |> {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I | 100.
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
     Qed. *)

  #[global] Instance elim_modal_spec_update_wp P E e Φ Ψ :
    ElimModal True false false (spec_update E P) P (EWP e @ E <| Ψ |> {{ Φ }}) (EWP e @ E <| Ψ |> {{ Φ }}).
  Proof.
    iIntros (?) "[HP Hcnt]".
    iApply spec_update_ewp.
    iMod "HP". iModIntro. by iApply "Hcnt".
  Qed.

  #[global] Instance elim_modal_spec_updateN_wp P E n e Φ Ψ :
    ElimModal True false false (spec_updateN n E P) P (EWP e @ E <| Ψ |>{{ Φ }}) (EWP e @ E <| Ψ |> {{ Φ }}).
  Proof.
    iIntros (?) "[HP Hcnt]".
    iDestruct (spec_updateN_implies_spec_update with "HP") as "> HP".
    by iApply "Hcnt".
  Qed.

End proofmode_classes.


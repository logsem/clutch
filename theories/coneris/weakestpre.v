From Coq Require Export Reals Psatz.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export fixpoint big_op.
From iris.prelude Require Import options.

From clutch.bi Require Export weakestpre.
From clutch.prelude Require Import stdpp_ext iris_ext NNRbar.
From clutch.prob Require Export couplings distribution graded_predicate_lifting.
From clutch.con_prob_lang Require Import lang erasure.
From clutch.common Require Export sch_erasable con_language.

Import uPred.

Local Open Scope NNR_scope.
#[global] Hint Resolve cond_nonneg : core.

(** We for now specialize the wp to con_prob_lang, since we allow 
    big state steps which are sch_erasable to tape oblivious schedulers,
    a kind of schedulers specific to the language
*)

Class conerisWpGS (Λ : conLanguage) (Σ : gFunctors) := ConerisWpGS {
  conerisWpGS_invGS :: invGS_gen HasNoLc Σ;
  state_interp : state Λ → iProp Σ;
  fork_post: val Λ -> iProp Σ;
  err_interp : nonnegreal → iProp Σ;
}.
Global Opaque conerisWpGS_invGS.
Global Arguments ConerisWpGS {Λ Σ}.
Canonical Structure NNRO := leibnizO nonnegreal.

Section modalities.
  Context `{conerisWpGS con_prob_lang Σ}.
  Implicit Types ε : nonnegreal.

  Definition state_step_coupl_pre E Z Φ : (state con_prob_lang * nonnegreal -> iProp Σ) :=
    (λ x,
      let '(σ1, ε) := x in
      ⌜(1<=ε)%R⌝ ∨
        Z σ1 ε ∨
      (∃ R μ (ε1 : nonnegreal) (ε2 : state con_prob_lang -> nonnegreal),
          ⌜ sch_erasable (λ t _ _ sch, TapeOblivious t sch) μ σ1 ⌝ ∗
          ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗
          ⌜ (ε1 + Expval μ ε2 <= ε)%R ⌝ ∗
          ⌜pgl μ R ε1⌝ ∗
          ∀ σ2, ⌜ R σ2 ⌝ ={E}=∗ Φ (σ2, ε2 σ2)))%I.

    
  #[local] Instance state_step_coupl_pre_ne E Z Φ :
    NonExpansive (state_step_coupl_pre E Z Φ).
  Proof.
    rewrite /state_step_coupl_pre.
    intros ?[??][??][[=][=]]. by simplify_eq.
  Qed.

  #[local] Instance state_step_coupl_pre_mono E Z : BiMonoPred (state_step_coupl_pre E Z).
  Proof.
    split; [|apply _].
    iIntros (Φ Ψ HNEΦ HNEΨ) "#Hwand".
    iIntros ([??]) "[H|[?|(%&%&%&%&%&%&%&%&H)]]".
    - by iLeft.
    - iRight; by iLeft.
    - do 2 iRight.
      repeat iExists _; repeat (iSplit; [done|]).
      iIntros (??).
      iApply "Hwand".
      by iApply "H".
  Qed.

  Definition state_step_coupl' E Z := bi_least_fixpoint (state_step_coupl_pre E Z).
  Definition state_step_coupl E σ ε Z:= state_step_coupl' E Z (σ, ε).

  Lemma state_step_coupl_unfold E σ1 ε Z :
    state_step_coupl E σ1 ε Z ≡
      (⌜(1 <= ε)%R⌝ ∨
      (Z σ1 ε) ∨
      (∃ R μ (ε1 : nonnegreal) (ε2 : state con_prob_lang -> nonnegreal),
          ⌜ sch_erasable (λ t _ _ sch, TapeOblivious t sch) μ σ1 ⌝ ∗
          ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗
          ⌜ (ε1 + SeriesC (λ ρ, (μ ρ) * ε2 ρ) <= ε)%R ⌝ ∗
          ⌜pgl μ R ε1⌝ ∗
          ∀ σ2, ⌜ R σ2 ⌝ ={E}=∗ state_step_coupl E σ2 (ε2 σ2) Z))%I.
  Proof. rewrite /state_step_coupl /state_step_coupl' least_fixpoint_unfold //. Qed.

  Lemma state_step_coupl_ret_err_ge_1 E σ1 Z (ε : nonnegreal) :
    (1 <= ε)%R → ⊢ state_step_coupl E σ1 ε Z.
  Proof. iIntros. rewrite state_step_coupl_unfold. by iLeft. Qed.

  Lemma state_step_coupl_ret E σ1 Z ε :
    Z σ1 ε -∗ state_step_coupl E σ1 ε Z.
  Proof. iIntros. rewrite state_step_coupl_unfold. by iRight; iLeft. Qed.

  Lemma state_step_coupl_rec σ1 E (ε : nonnegreal) Z :
    (∃ R μ (ε1 : nonnegreal) (ε2 : state con_prob_lang -> nonnegreal),
          ⌜ sch_erasable (λ t _ _ sch, TapeOblivious t sch) μ σ1 ⌝ ∗
          ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗
          ⌜ (ε1 + Expval μ ε2 <= ε)%R ⌝ ∗
          ⌜pgl μ R ε1⌝ ∗
          ∀ σ2, ⌜ R σ2 ⌝ ={E}=∗ state_step_coupl E σ2 (ε2 σ2) Z)%I
    ⊢ state_step_coupl E σ1 ε Z.
  Proof. iIntros "H". rewrite state_step_coupl_unfold. iRight; iRight. done. Qed.

  Lemma state_step_coupl_ind E (Ψ Z : state con_prob_lang → nonnegreal → iProp Σ) :
    ⊢ (□ (∀ σ ε,
             state_step_coupl_pre E Z (λ '(σ, ε'),
                 Ψ σ ε' ∧ state_step_coupl E σ ε' Z)%I (σ, ε) -∗ Ψ σ ε) →
       ∀ σ ε, state_step_coupl E σ ε Z -∗ Ψ σ ε)%I.
  Proof.
    iIntros "#IH" (σ ε) "H".
    set (Ψ' := (λ '(σ, ε), Ψ σ ε) :
           (prodO (stateO con_prob_lang) NNRO) → iProp Σ).
    assert (NonExpansive Ψ').
    { intros n [σ1 ε1] [σ2 ε2].
      intros [[=][=]].
      by simplify_eq/=. }
    iApply (least_fixpoint_ind _ Ψ' with "[] H").
    iIntros "!#" ([? ?]) "H". by iApply "IH".
  Qed.

  Lemma fupd_state_step_coupl E σ1 Z (ε : nonnegreal) :
    (|={E}=> state_step_coupl E σ1 ε Z) ⊢ state_step_coupl E σ1 ε Z.
  Proof.
    iIntros "H".
    iApply state_step_coupl_rec.
    iExists (λ x, x= σ1), (dret σ1), nnreal_zero, (λ _, ε).
    repeat iSplit.
    - iPureIntro. apply dret_sch_erasable.
    - iPureIntro. naive_solver.
    - simpl. iPureIntro. rewrite Expval_const; last done.
      rewrite dret_mass. lra.
    - iPureIntro.
      by apply pgl_dret.
    - by iIntros (? ->).
  Qed.
  
  Lemma state_step_coupl_mono E1 E2 σ1 Z1 Z2 ε :
    E1 ⊆ E2 →
    (∀ σ2 ε', Z1 σ2 ε' -∗ Z2 σ2 ε') -∗
    state_step_coupl E1 σ1 ε Z1 -∗ state_step_coupl E2 σ1 ε Z2.
  Proof.
    iIntros (HE) "HZ Hs".
    iRevert "HZ".
    iRevert (σ1 ε) "Hs".
    iApply state_step_coupl_ind.
    iIntros "!#" (σ ε)
      "[% | [? | (% & % & % & % & % & % & % & % & H)]] Hw".
    - iApply state_step_coupl_ret_err_ge_1. lra.
    - iApply state_step_coupl_ret. by iApply "Hw".
    - iApply state_step_coupl_rec.
      repeat iExists _.
      repeat iSplit; try done.
      iIntros (??).
      iApply fupd_mask_mono; [done|].
      iMod ("H" with "[//]") as "[IH _]".
      by iApply "IH".
  Qed.

  Lemma state_step_coupl_mono_err ε1 ε2 E σ1 Z :
    (ε1 <= ε2)%R → state_step_coupl E σ1 ε1 Z -∗ state_step_coupl E σ1 ε2 Z.
  Proof.
    iIntros (Heps) "Hs".
    iApply state_step_coupl_rec.
    set (ε' := nnreal_minus ε2 ε1 Heps).
    iExists (λ x, x=σ1), (dret σ1), nnreal_zero, (λ _, ε1).
    repeat iSplit.
    - iPureIntro. apply dret_sch_erasable.
    - iPureIntro; naive_solver.
    - iPureIntro. simpl. rewrite Expval_const; last done. rewrite dret_mass; lra.
    - iPureIntro. by apply pgl_dret.
    - by iIntros (?->).
  Qed.
  
  Lemma state_step_coupl_bind E1 E2 σ1 Z1 Z2 ε :
    E1 ⊆ E2 →
    (∀ σ2 ε', Z1 σ2 ε' -∗ state_step_coupl E2 σ2 ε' Z2) -∗
    state_step_coupl E1 σ1 ε Z1 -∗
    state_step_coupl E2 σ1 ε Z2.
  Proof.
    iIntros (HE) "HZ Hs".
    iRevert "HZ".
    iRevert (σ1 ε) "Hs".
    iApply state_step_coupl_ind.
    iIntros "!#" (σ ε)
      "[% | [H | (% & % & % & % & % & % & % & % & H)]] HZ".
    - by iApply state_step_coupl_ret_err_ge_1.
    - iApply ("HZ" with "H").
    - iApply state_step_coupl_rec.
      repeat iExists _.
      repeat iSplit; try done.
      iIntros (??).
      iMod (fupd_mask_subseteq E1) as "Hclose"; [done|].
      iMod ("H" with "[//]") as "[H _]".
      iMod "Hclose".
      by iApply "H".
  Qed.
  
  Lemma state_step_coupl_state_step E α σ1 Z (ε ε' : nonnegreal) :
    α ∈ get_active σ1 →
    (∃ R, ⌜pgl (state_step σ1 α) R ε⌝ ∗
          ∀ σ2 , ⌜R σ2 ⌝ ={E}=∗ state_step_coupl E σ2 ε' Z)
    ⊢ state_step_coupl E σ1 (ε + ε') Z.
  Proof.
    iIntros (Hin) "(%R&%&H)".
    iApply state_step_coupl_rec.
    iExists R, (state_step σ1 α), ε, (λ _, ε').
    repeat iSplit; try done.
    - iPureIntro.
      simpl in *.
      rewrite elem_of_elements elem_of_dom in Hin.
      destruct Hin.
      by eapply state_step_sch_erasable.
    - iPureIntro; eexists _; done.
    - iPureIntro. rewrite Expval_const; last done. rewrite state_step_mass; [simpl;lra|done]. 
  Qed.

  Lemma state_step_coupl_iterM_state_adv_comp E N α σ1 Z (ε : nonnegreal) :
    (α ∈ get_active σ1 ->
     (∃ R ε1 (ε2 : _ -> nonnegreal),
        ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗
        ⌜ (ε1 + Expval (iterM N (λ σ, state_step σ α) σ1) ε2 <= ε)%R ⌝ ∗
        ⌜pgl (iterM N (λ σ, state_step σ α) σ1) R ε1⌝ ∗
        ∀ σ2, ⌜ R σ2 ⌝ ={E}=∗ state_step_coupl E σ2 (ε2 σ2) Z)
      ⊢ state_step_coupl E σ1 ε Z)%I.
  Proof.
    iIntros (Hin) "(%R & %ε1 & %ε2 & % & %Hε & % & H)".
    iApply state_step_coupl_rec.
    iExists R, _, ε1, ε2.
    repeat iSplit; try done.
    - iPureIntro.
      simpl in *.
      rewrite elem_of_elements elem_of_dom in Hin.
      destruct Hin.
      by eapply iterM_state_step_sch_erasable.
  Qed. 
  
  Lemma state_step_coupl_state_adv_comp E α σ1 Z (ε : nonnegreal) :
    (α ∈ get_active σ1 ->
     (∃ R ε1 (ε2 : _ -> nonnegreal),
        ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗
        ⌜ (ε1 + Expval (state_step σ1 α) ε2 <= ε)%R ⌝ ∗
        ⌜pgl (state_step σ1 α) R ε1⌝ ∗
        ∀ σ2, ⌜ R σ2 ⌝ ={E}=∗ state_step_coupl E σ2 (ε2 σ2) Z)
      ⊢ state_step_coupl E σ1 ε Z)%I.
  Proof.
    iIntros (Hin) "(%R & %ε1 & %ε2 & % & %Hε & % & H)".
    iApply (state_step_coupl_iterM_state_adv_comp _ 1%nat); first done.
    repeat iExists _. simpl. rewrite dret_id_right.
    by repeat iSplit.
  Qed.
  

  (** * One step prog coupl *)

  Definition prog_coupl e1 σ1 ε Z : iProp Σ :=
    (∃ R (ε1 : nonnegreal) (ε2 : (expr con_prob_lang * state con_prob_lang * list (expr con_prob_lang)) -> nonnegreal),
           ⌜reducible e1 σ1⌝ ∗
           ⌜∃ (r:nonnegreal), ∀ ρ, (ε2 ρ <= r)%R ⌝ ∗
           ⌜(ε1 + Expval (prim_step e1 σ1) ε2 <= ε)%R⌝ ∗
           ⌜pgl (prim_step e1 σ1) R ε1⌝ ∗
           (∀ e2 σ2 efs, ⌜R (e2, σ2, efs)⌝ ={∅}=∗
                         Z (e2, σ2, efs) (ε2 (e2, σ2, efs)))
       )%I.
  
  (* Definition glm_pre *)
  (*   (Z : (expr con_prob_lang * state con_prob_lang * list (expr con_prob_lang)) -> nonnegreal -> iProp Σ) (Φ : partial_cfg con_prob_lang * nonnegreal -> iProp Σ) := *)
  (*   (λ (x : partial_cfg con_prob_lang * nonnegreal), *)
  (*      let '((e1, σ1), ε) := x in *)
  (*      (∃ R (ε1 : nonnegreal) (ε2 : (expr con_prob_lang * state con_prob_lang * list (expr con_prob_lang)) -> nonnegreal), *)
  (*          ⌜reducible e1 σ1⌝ ∗ *)
  (*          ⌜∃ r, ∀ ρ, (ε2 ρ <= r)%R ⌝ ∗ *)
  (*          ⌜(ε1 + SeriesC (λ ρ, (prim_step e1 σ1 ρ) * ε2 ρ) <= ε)%R⌝ ∗ *)
  (*          ⌜pgl (prim_step e1 σ1) R ε1⌝ ∗ *)
  (*          (∀ e2 σ2 efs, ⌜R (e2, σ2, efs)⌝ ={∅}=∗ *)
  (*                       stutter (λ ε', Z (e2, σ2, efs) ε') (ε2 (e2, σ2, efs))) *)
  (*      ) ∨ *)
  (*        (∃ R μ (ε1 : nonnegreal) (ε2 : state con_prob_lang -> nonnegreal), *)
  (*         ⌜ sch_erasable (λ t _ _ sch, TapeOblivious t sch) μ σ1 ⌝ ∗ *)
  (*         ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗ *)
  (*         ⌜ (ε1 + SeriesC (λ ρ, (μ ρ) * ε2 ρ) <= ε)%R ⌝ ∗ *)
  (*         ⌜pgl μ R ε1⌝ ∗ *)
  (*             ∀ σ2, ⌜ R σ2 ⌝ ={∅}=∗ stutter (λ ε', Φ ((e1, σ2), ε')) (ε2 σ2)) *)
  (*   )%I. *)

  (* Canonical Structure NNRO := leibnizO nonnegreal. *)

  (* Local Instance exec_state_ub_pre_NonExpansive Z Φ : *)
  (*   NonExpansive (glm_pre Z Φ). *)
  (* Proof. *)
  (*   rewrite /glm_pre. *)
  (*   intros n ((?&?)&?) ((?&?)&?) [ [[=] [=]] [=]]. *)
  (*   by simplify_eq. *)
  (* Qed. *)
  
  (* Local Instance exec_coupl_pre_mono Z : BiMonoPred (glm_pre Z). *)
  (* Proof. *)
  (*   split; [|apply _]. *)
  (*   iIntros (Φ Ψ HNEΦ HNEΨ) "#Hwand". *)
  (*   rewrite /glm_pre. *)
  (*   iIntros (((e1 & σ1) & ε)) "Hexec". *)
  (*   iDestruct "Hexec" as "[H|H]". *)
  (*   - by iLeft. *)
  (*   - iRight. *)
  (*     iDestruct "H" as "(% & % & % & % & % & %Herasable & %Hsum & %Hlift & HΦ)". *)
  (*     iExists _, _, _, _. *)
  (*     repeat iSplit; try done. *)
  (*     iIntros. *)
  (*     iApply (stutter_mono with "[]"); first done; last first. *)
  (*       * by iMod ("HΦ" with "[//]"). *)
  (*       * iIntros. *)
  (*         by iApply "Hwand". *)
  (* Qed. *)

  
  (* Definition glm' Z := bi_least_fixpoint (glm_pre Z). *)
  (* Definition glm e σ ε Z := glm' Z ((e, σ), ε). *)

  (* Lemma glm_unfold (e1 : exprO con_prob_lang) (σ1 : stateO con_prob_lang) Z (ε : NNRO) : *)
  (*   glm e1 σ1 ε Z ≡ *)
  (*     ((∃ R (ε1 : nonnegreal) (ε2 : (expr con_prob_lang * state con_prob_lang * list (expr con_prob_lang)) -> nonnegreal), *)
  (*          ⌜reducible e1 σ1⌝ ∗ *)
  (*          ⌜∃ r, ∀ ρ, (ε2 ρ <= r)%R ⌝ ∗ *)
  (*          ⌜(ε1 + SeriesC (λ ρ, (prim_step e1 σ1 ρ) * ε2 ρ) <= ε)%R⌝ ∗ *)
  (*          ⌜pgl (prim_step e1 σ1) R ε1⌝ ∗ *)
  (*          (∀ e2 σ2 efs, ⌜R (e2, σ2, efs)⌝ ={∅}=∗ *)
  (*                       stutter (λ ε', Z (e2, σ2, efs) ε') (ε2 (e2, σ2, efs))) *)
  (*      ) ∨ *)
  (*        (∃ R μ (ε1 : nonnegreal) (ε2 : state con_prob_lang -> nonnegreal), *)
  (*         ⌜ sch_erasable (λ t _ _ sch, TapeOblivious t sch) μ σ1 ⌝ ∗ *)
  (*         ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗ *)
  (*         ⌜ (ε1 + SeriesC (λ ρ, (μ ρ) * ε2 ρ) <= ε)%R ⌝ ∗ *)
  (*         ⌜pgl μ R ε1⌝ ∗ *)
  (*         ∀ σ2, ⌜ R σ2 ⌝ ={∅}=∗ stutter (λ ε', glm e1 σ2 ε' Z) (ε2 σ2)) *)
  (*     )%I. *)
  (* Proof. *)
  (*   rewrite /glm/glm' least_fixpoint_unfold//. *)
  (* Qed. *)

  (* Local Definition partial_cfgO := (prodO (exprO con_prob_lang) (stateO con_prob_lang)). *)

  Lemma prog_coupl_mono_err e σ Z ε ε':
    (ε<=ε')%R -> prog_coupl e σ ε Z -∗ prog_coupl e σ ε' Z.
  Proof.
    iIntros (?) "(%&%&%&%&%&%&%&H)".
    repeat iExists _.
    repeat iSplit; try done.
    iPureIntro.
    etrans; exact.
  Qed.

  Lemma prog_coupl_strong_mono e1 σ1 Z1 Z2 ε :
    (∀ e2 σ2 ε' efs, ⌜∃ σ, (prim_step e1 σ (e2, σ2, efs) > 0)%R⌝ ∗ Z1 (e2, σ2, efs) ε' -∗ Z2 (e2, σ2, efs) ε') -∗
    prog_coupl e1 σ1 ε Z1 -∗ prog_coupl e1 σ1 ε Z2.
  Proof.
    iIntros "Hm (%&%&%&%&%&%&% & Hcnt) /=".
    repeat iExists _. repeat iSplit.
    - done.
    - done.
    - done.
    - iPureIntro; by apply pgl_pos_R.
    - simpl. iIntros (???[??]).
      iApply "Hm".
      iSplitR; [by iExists _|].
      by iApply "Hcnt".
  Qed.

  Lemma prog_coupl_mono e1 σ1 Z1 Z2 ε :
    (∀ e2 σ2 efs ε', Z1 (e2, σ2, efs) ε' -∗ Z2 (e2, σ2, efs) ε') -∗
    prog_coupl e1 σ1 ε Z1 -∗ prog_coupl e1 σ1 ε Z2.
  Proof.
    iIntros "Hm".
    iApply prog_coupl_strong_mono.
    iIntros (????) "[_ H]". by iApply "Hm".
  Qed.
  
  (* Lemma glm_mono_grading e σ Z ε ε' : *)
  (*   ⌜(ε <= ε')%R⌝ -∗ *)
  (*   glm e σ ε Z -∗ glm e σ ε' Z. *)
  (* Proof. *)
  (*   iIntros "Hleq H_ub". iRevert "Hleq". *)
  (*   rewrite /glm /glm'. *)
  (*   set (Φ := (λ x, ∀ (ε'' : nonnegreal), ((⌜(x.2 <= ε'' )%R⌝ -∗ (bi_least_fixpoint (glm_pre Z) (x.1, ε'')))))%I : prodO partial_cfgO NNRO → iPropI Σ). *)
  (*   assert (NonExpansive Φ). *)
  (*   { intros n ((?&?)&?) ((?&?)&?) [ [[=] [=]] [=]]. by simplify_eq. } *)
  (*   iPoseProof (least_fixpoint_ind (glm_pre Z) Φ with "[]") as "H"; last first. *)
  (*   { iApply ("H" with "H_ub"). } *)
  (*   iIntros "!#" ([[? σ'] ε'']). rewrite /glm_pre. *)
  (*   iIntros "[(% & % & % & % & % & % & % & H)|H] %ε3 %Hleq' /="; simpl in Hleq'. *)
  (*   - rewrite least_fixpoint_unfold. *)
  (*     iLeft. *)
  (*     iExists _,_,_. *)
  (*     repeat iSplit; try done. *)
  (*     iPureIntro; etrans; done. *)
  (*   - rewrite least_fixpoint_unfold. *)
  (*     iRight. *)
  (*     simpl. *)
  (*     iDestruct "H" as "(%R2 & %μ & %ε1 & %ε2 & (%Herasable & %Hleq2 & %Hub & %Hlift & H ))". *)
  (*     iExists R2, μ. iExists ε1. iExists ε2. *)
  (*     iSplit; [auto|]. *)
  (*     iSplit; [auto|]. *)
  (*     iSplit; [ iPureIntro; lra | ]. *)
  (*     iSplit; [ done | ]. *)
  (*     iIntros. *)
  (*     rewrite /glm_pre. *)
  (*     iMod ("H" with "[//]"). *)
  (*     iModIntro. *)
  (*     iApply stutter_mono; [done| |done]. *)
  (*     simpl. *)
  (*     iIntros "K". *)
  (*     by iApply "K". *)
  (* Qed. *)
  
  (* Lemma glm_strong_mono e1 σ1 Z1 Z2 ε ε' : *)
  (*   ⌜(ε <= ε')%R⌝ -∗ *)
  (*   (∀ e2 σ2 ε'', (⌜∃ σ, (prim_step e1 σ (e2, σ2) > 0)%R⌝ ∗ Z1 (e2, σ2) ε'' -∗ Z2 (e2, σ2) ε'')) -∗ *)
  (*   glm e1 σ1 ε Z1 -∗ glm e1 σ1 ε' Z2. *)
  (* Proof. *)
  (*   iIntros "%Hleq HZ H_ub". *)
  (*   iApply glm_mono_grading; auto. *)
  (*   iRevert "HZ". *)
  (*   rewrite /glm /glm'. *)
  (*   set (Φ := (λ x,(∀ e2 σ2 ε'', ⌜∃ σ, (prim_step x.1.1 σ (e2, σ2) > 0)%R⌝ ∗ Z1 (e2, σ2) ε'' -∗ Z2 (e2, σ2) ε'') -∗ *)
  (*                 (bi_least_fixpoint (glm_pre Z2) x ))%I : prodO partial_cfgO NNRO → iPropI Σ). *)
  (*   assert (NonExpansive Φ). *)
  (*   { intros n ((?&?)&?) ((?&?)&?) [[[=] [=]] [=]]. by simplify_eq. } *)
  (*   iPoseProof (least_fixpoint_iter (glm_pre Z1) Φ with "[]") as "H"; last first. *)
  (*   { by iApply ("H" with "H_ub"). } *)
  (*   iIntros "!#" ([[? σ'] ε'']). rewrite /glm_pre. *)
  (*   iIntros "[(% & % & % & % & % & % & % & H)|H] HZ /=". *)
  (*   - rewrite least_fixpoint_unfold. *)
  (*     iLeft. *)
  (*     iExists _,_,_. *)
  (*     do 3 (iSplit; first done). *)
  (*     iSplit; first (iPureIntro; by apply pgl_pos_R). *)
  (*     iIntros (???[??]). *)
  (*     iMod ("H" with "[//]"). *)
  (*     iModIntro. *)
  (*     iApply (stutter_mono with "[][HZ][$]"); first done. *)
  (*     iIntros "H". *)
  (*     iApply "HZ". iFrame. *)
  (*     iPureIntro. naive_solver. *)
  (*  - rewrite least_fixpoint_unfold. *)
  (*    iRight. *)
  (*    iDestruct "H" as "(%R2 & %μ & %ε1 & %ε2 & (% & % & % & % & H))". *)
  (*     iExists R2. iExists μ. iExists ε1. iExists ε2. *)
  (*     iSplit; [auto | ]. *)
  (*     iSplit; [auto | ]. *)
  (*     iSplit; [by iPureIntro| ]. *)
  (*     iSplit; [done | ]. *)
  (*     iIntros. *)
  (*     iMod ("H" with "[//]") as "H". *)
  (*     iModIntro. *)
  (*     iApply (stutter_mono with "[][HZ]"); [done| |done]. *)
  (*     simpl. *)
  (*     rewrite /Φ. *)
  (*     iIntros "H".  *)
  (*     iApply "H". *)
  (*     iFrame. *)
  (* Qed. *)

  (* Lemma glm_mono Z1 Z2 e1 σ1 ε1 ε2 : *)
  (*   ⌜(ε1 <= ε2)%R⌝ -∗ (∀ ρ ε, Z1 ρ ε -∗ Z2 ρ ε) -∗ glm e1 σ1 ε1 Z1 -∗ glm e1 σ1 ε2 Z2. *)
  (* Proof. *)
  (*   iIntros "%Hleq HZ". iApply glm_strong_mono; auto. *)
  (*   iIntros (???) "[_ ?]". by iApply "HZ". *)
  (* Qed. *)

  (* Lemma glm_mono_pred Z1 Z2 e1 σ1 ε : *)
  (*   (∀ ρ ε, Z1 ρ ε -∗ Z2 ρ ε) -∗ glm e1 σ1 ε Z1 -∗ glm e1 σ1 ε Z2. *)
  (* Proof. *)
  (*   iIntros "HZ". iApply glm_strong_mono; auto. *)
  (*   iIntros (???) "[_ ?]". by iApply "HZ". *)
  (* Qed. *)

  Lemma prog_coupl_strengthen e1 σ1 Z ε :
    prog_coupl e1 σ1 ε Z -∗
    prog_coupl e1 σ1 ε (λ '(e2, σ2, efs) ε', ⌜∃ σ, (prim_step e1 σ (e2, σ2, efs) > 0)%R⌝ ∧ Z (e2, σ2, efs) ε').
  Proof.
    iApply prog_coupl_strong_mono. iIntros (????) "[$ $]".
  Qed.
  
  (* Lemma glm_strengthen e1 σ1 Z ε : *)
  (*   glm e1 σ1 ε Z -∗ *)
  (*   glm e1 σ1 ε (λ '(e2, σ2) ε', ⌜∃ σ, (prim_step e1 σ (e2, σ2) > 0)%R⌝ ∧ Z (e2, σ2) ε'). *)
  (* Proof. *)
  (*   iApply glm_strong_mono; [iPureIntro; lra | ]. *)
  (*   iIntros (???) "[[% ?] ?]". iSplit; [|done]. by iExists _. *)
  (* Qed. *)

  Lemma prog_coupl_ctx_bind K `{!ConLanguageCtx K} e1 σ1 Z ε:
    to_val e1 = None ->
    prog_coupl e1 σ1 ε (λ '(e2, σ2, efs) ε', Z (K e2, σ2, efs) ε') -∗ prog_coupl (K e1) σ1 ε Z.
  Proof.
    iIntros (Hv) "(%R&%ε1&%ε2&%&[%%]&%&%&H)".
    
    (** (classical) inverse of context [K] *)
    destruct (partial_inv_fun K) as (Kinv & HKinv).
    assert (∀ e, Kinv (K e) = Some e) as HKinv3.
    { intro e.
      destruct (Kinv (K e)) eqn:Heq;
        eapply HKinv in Heq; by simplify_eq. }
    set (ε2' := (λ '(e, σ, efs), from_option (λ e', ε2 (e', σ, efs)) 0%NNR (Kinv e))).
    assert (∀ e2 σ2 efs, ε2' (K e2, σ2, efs) = ε2 (e2, σ2, efs)) as Hε2'.
    { intros. rewrite /ε2' HKinv3 //. }
    iExists (λ '(e2, σ2, efs), ∃ e2', e2 = K e2' /\ R (e2', σ2, efs)), ε1, ε2'.
    repeat iSplit; try iPureIntro.
    - by apply reducible_fill.
    - rewrite /ε2'. eexists _.
      intros [[??]?].
      destruct (Kinv _); simpl; naive_solver.
    - rewrite fill_dmap// Expval_dmap//=; last first.
      + eapply ex_expval_bounded. simpl. intros [[??]?] => /=. by rewrite HKinv3/=.
      + etrans; last done.
        apply Rle_plus_plus; first done.
        right.
        apply SeriesC_ext.
        intros [[??]?]. simpl. by rewrite HKinv3/=.
    - rewrite fill_dmap//.
      replace (ε1) with (ε1+0)%NNR; last (apply nnreal_ext; simpl; lra).
      eapply pgl_dbind; try done.
      intros a ?. apply pgl_dret.
      destruct a as [[??]?] => /=.
      naive_solver.
    - iIntros (???(?&->&?)).
      rewrite /ε2'. rewrite HKinv3/=.
      by iApply "H".
  Qed.
  
  (* Lemma glm_bind K `{!ConLanguageCtx K} e1 σ1 Z ε : *)
  (*   to_val e1 = None → *)
  (*   glm e1 σ1 ε (λ '(e2, σ2, efs) ε', Z (K e2, σ2, efs) ε') -∗ glm (K e1) σ1 ε Z. *)
  (* Proof. *)
  (*   iIntros (Hv) "Hub". *)
  (*   iAssert (⌜to_val e1 = None⌝)%I as "-#H"; [done|]. *)
  (*   iRevert "H". *)
  (*   rewrite /glm /glm'. *)
  (*   set (Φ := (λ x, ⌜to_val x.1.1 = None⌝ -∗ *)
  (*                    bi_least_fixpoint (glm_pre Z) ((K x.1.1, x.1.2), x.2))%I *)
  (*          : prodO partial_cfgO NNRO → iPropI Σ). *)
  (*   assert (NonExpansive Φ). *)
  (*   { intros n ((?&?)&?) ((?&?)&?) [[[=] [=]] [=]]. by simplify_eq. } *)
  (*   iPoseProof (least_fixpoint_iter *)
  (*                 (glm_pre (λ '(e2, σ2, efs) ε', Z (K e2, σ2, efs) ε')) Φ *)
  (*                with "[]") as "H"; last first. *)
  (*   { iIntros (?). iApply ("H" $! ((_, _), _) with "Hub [//]"). } *)
  (*   iIntros "!#" ([[? σ'] ε']). rewrite /glm_pre. *)
  (*   iIntros " [(% & % & % & % & [%r %Hr] & % & % & H)|H] %Hv'". *)
  (*   - rewrite least_fixpoint_unfold. *)
  (*     iLeft. *)
  (*     destruct (partial_inv_fun K) as (Kinv & HKinv). *)
  (*     assert (forall e e', Kinv e' = Some e -> K e = e') as HKinv1; [intros; by apply HKinv |]. *)
  (*     assert (forall e e', Kinv e = None -> K e' ≠ e) as HKinv2; [intros; by apply HKinv |]. *)
  (*     assert (forall e, Kinv (K e) = Some e) as HKinv3. *)
  (*     { intro e. *)
  (*       destruct (Kinv (K e)) eqn:H5. *)
  (*       - apply HKinv1 in H5. f_equal. by apply fill_inj. *)
  (*       - eapply (HKinv2 _ e) in H5. done. } *)
  (*     set (ε3 := (λ '(e,σ,efs), from_option (λ e', ε2 (e',σ, efs)) nnreal_zero (Kinv e))). *)
  (*     assert (forall e2 σ2 efs, ε3 (K e2, σ2, efs) = ε2 (e2, σ2, efs)) as Haux. *)
  (*     { *)
  (*       intros e2 σ2 efs. *)
  (*       rewrite /ε3 HKinv3 //. *)
  (*     } *)
  (*     iExists (λ '(e2, σ2, efs), ∃ e2', e2 = K e2' ∧ R2 (e2', σ2, efs)),_,ε3. *)
  (*     iSplit; [iPureIntro; by apply reducible_fill|]. *)
  (*     iSplit. *)
  (*     { iPureIntro. exists r. intros ([e σ]&efs). rewrite /ε3. *)
  (*       destruct (Kinv e); simpl; try real_solver. *)
  (*       etrans; [ | eapply (Hr (e, σ, efs)); eauto]. apply cond_nonneg. *)
  (*     } *)
  (*     iSplit; [|iSplit]. *)
  (*     2: { iPureIntro. *)
  (*          rewrite <- Rplus_0_r. *)
  (*          rewrite fill_dmap //=. *)
  (*          eapply (pgl_dbind _ _ R2). *)
  (*          - eapply pgl_nonneg_grad; eauto. *)
  (*          - lra. *)
  (*          - intros [[]] ? =>/=. *)
  (*            apply pgl_dret. *)
  (*            eauto. *)
  (*          - auto. *)
  (*     } *)
  (*     + iPureIntro; simpl. *)
  (*       etrans; [ | exact]. *)
  (*       apply Rplus_le_compat_l. *)
  (*       transitivity (SeriesC (λ '(e,σ,efs), (prim_step (K o) σ' (K e, σ, efs) * ε3 (K e, σ, efs))%R)). *)
  (*       * etrans; [ | eapply (SeriesC_le_inj _ (λ '(e,σ, efs), (Kinv e ≫= (λ e', Some (e',σ, efs)))))]. *)
  (*         ** apply SeriesC_le. *)
  (*            *** intros ([e σ] & efs); simpl; split. *)
  (*                **** apply Rmult_le_pos; auto. *)
  (*                     apply cond_nonneg. *)
  (*                **** destruct (Kinv e) eqn:He; simpl. *)
  (*                     ***** rewrite (HKinv1 _ _ He). *)
  (*                     rewrite He /from_option //. *)
  (*                     ***** destruct (decide (prim_step (K o) σ' (e, σ, efs) > 0)%R) as [Hgt | Hngt]. *)
  (*         -- epose proof (fill_step_inv _ _ _ _ _ _ Hgt) as (e2' & (?&?)). *)
  (*            by destruct (HKinv2 e e2' He). *)
  (*         --  apply Rnot_gt_le in Hngt. *)
  (*             assert (prim_step (K o) σ' (e, σ, efs) = 0%R); [by apply Rle_antisym | ]. *)
  (*             lra. *)
  (*             *** apply (ex_seriesC_le _ (λ '(e, σ, efs), (prim_step (K o) σ' (e, σ, efs) * ε3 (e, σ, efs))%R)). *)
  (*                 **** intros ([e σ] & efs); simpl; split. *)
  (*                      ***** destruct (Kinv e); simpl; try lra. *)
  (*                      apply Rmult_le_pos; auto. *)
  (*                      destruct (Kinv _); simpl; try lra. *)
  (*                      apply cond_nonneg. *)
  (*                      ***** destruct (Kinv e) eqn:He; simpl; try real_solver. *)
  (*                      rewrite HKinv3 /= (HKinv1 _ _ He) //. *)
  (*                 **** apply (ex_seriesC_le _ (λ ρ, ((prim_step (K o) σ' ρ ) * r)%R)); [ | apply ex_seriesC_scal_r; auto]. *)
  (*                      intros ([e σ]&efs); split. *)
  (*                      ***** apply Rmult_le_pos; auto. *)
  (*                      apply cond_nonneg. *)
  (*                      ***** rewrite /ε3. destruct (Kinv e); simpl; try real_solver. *)
  (*                      apply Rmult_le_compat_l; auto. *)
  (*                      etrans; [ | eapply (Hr (e, σ, efs)); eauto]. apply cond_nonneg. *)
  (*             ** intros [[]]. *)
  (*                apply Rmult_le_pos; auto. *)
  (*                apply cond_nonneg. *)
  (*             ** intros [[e3 ]] [[e4]] [[e5]]? ?. *)
  (*                destruct (Kinv e3) eqn:He3; destruct (Kinv e4) eqn:He4; simpl in *; simplify_eq. *)
  (*                f_equal; auto. *)
  (*                rewrite -(HKinv1 _ _ He3). *)
  (*                by rewrite -(HKinv1 _ _ He4). *)
  (*             ** apply (ex_seriesC_le _ (λ '(e, σ, efs), ((prim_step (K o) σ' (K e, σ, efs)) * r)%R)). *)
  (*                *** intros ([]&?); split. *)
  (*                    **** apply Rmult_le_pos; auto. *)
  (*                         apply cond_nonneg. *)
  (*                    **** rewrite /ε3 HKinv3 /=. real_solver. *)
  (*                *** apply (ex_seriesC_ext (λ ρ, ((prim_step o σ' ρ) * r)%R)); auto. *)
  (*                    **** intros [[]]. apply Rmult_eq_compat_r. by apply fill_step_prob. *)
  (*                    **** by apply ex_seriesC_scal_r. *)
  (*       * right. apply SeriesC_ext. *)
  (*         intros ([]&?). *)
  (*         rewrite Haux. *)
  (*         f_equal; auto. *)
  (*         symmetry; by apply fill_step_prob. *)
  (*     + iIntros (???[?[->?]]). *)
  (*       iMod ("H" with "[//]"). *)
  (*       by rewrite Haux. *)
  (*       Unshelve. auto. *)
  (*   - rewrite least_fixpoint_unfold; simpl. *)
  (*     iRight. *)
  (*     (* from above (combine?)*) *)
  (*     destruct (partial_inv_fun K) as (Kinv & HKinv). *)
  (*     assert (forall e e', Kinv e' = Some e -> K e = e') as HKinv1; [intros; by apply HKinv |]. *)
  (*     assert (forall e e', Kinv e = None -> K e' ≠ e) as HKinv2; [intros; by apply HKinv |]. *)
  (*     assert (forall e, Kinv (K e) = Some e) as HKinv3. *)
  (*     { intro e. *)
  (*       destruct (Kinv (K e)) eqn:H3. *)
  (*       - apply HKinv1 in H3. f_equal. by apply fill_inj. *)
  (*       - eapply (HKinv2 _ e) in H3. done. } *)
  (*     simpl. *)
  (*     iDestruct "H" as "(%R2 & %μ & %ε1 & %ε2 & (%Herasable & %Hub & %Hleq & %Hlift & H))". *)
  (*     iExists _, _, _, _. *)
  (*     repeat iSplit; try done. *)
  (*     iIntros. *)
  (*     iMod ("H" with "[//]") as "H". *)
  (*     rewrite /Φ. *)
  (*     iApply stutter_mono; [done| |done]. *)
  (*     simpl. iIntros "H". by iApply "H". *)
  (* Qed. *)


  Lemma prog_coupl_prim_step e1 σ1 Z ε :
    (∃ R ε1 ε2, ⌜reducible e1 σ1⌝ ∗ ⌜ (ε1 + ε2 <= ε)%R ⌝ ∗ ⌜pgl (prim_step e1 σ1) R ε1⌝ ∗
          ∀ e2 σ2 efs, ⌜R (e2, σ2, efs)⌝ ={∅}=∗ Z (e2, σ2, efs) ε2)
    ⊢ prog_coupl e1 σ1 ε Z.
  Proof.
    iIntros "(%R&%ε1&%ε2&%&%&%&H)".
    iExists R, ε1, (λ _, ε2).
    repeat iSplit; try done.
    - iPureIntro. naive_solver.
    - iPureIntro. rewrite Expval_const; last done.
      rewrite prim_step_mass; [lra|done].
  Qed. 

  Lemma prog_coupl_adv_comp e1 σ1 Z (ε : nonnegreal) :
      (∃ R (ε1 : nonnegreal) (ε2 : _ -> nonnegreal),
          ⌜reducible e1 σ1⌝ ∗
          ⌜ exists (r:nonnegreal), forall ρ, (ε2 ρ <= r)%R ⌝ ∗
          ⌜ (ε1 + Expval (prim_step e1 σ1) ε2 <= ε)%R ⌝ ∗ ⌜pgl (prim_step e1 σ1) R ε1⌝ ∗
            ∀ e2 σ2 efs, ⌜ R (e2, σ2, efs) ⌝ ={∅}=∗ Z (e2, σ2, efs) (ε2 (e2, σ2, efs)))
    ⊢ prog_coupl e1 σ1 ε Z.
  Proof.
    iIntros "(% & % & % & % & % & % & % & H)".
    iExists _,_,_.
    by repeat iSplit.
  Qed.


  (* Lemma glm_strong_ind (Ψ : expr con_prob_lang → state con_prob_lang → nonnegreal → iProp Σ) Z : *)
  (*   (∀ n e σ ε, Proper (dist n) (Ψ e σ ε)) → *)
  (*   ⊢ (□ (∀ e σ ε, glm_pre Z (λ '((e, σ), ε), Ψ e σ ε ∧ glm e σ ε Z)%I ((e, σ), ε) -∗ Ψ e σ ε) → *)
  (*      ∀ e σ ε, glm e σ ε Z -∗ Ψ e σ ε)%I. *)
  (* Proof. *)
  (*   iIntros (HΨ). iIntros "#IH" (e σ ε) "H". *)
  (*   set (Ψ' := (λ '((e, σ), ε), Ψ e σ ε): *)
  (*          (prodO (prodO (exprO con_prob_lang) (stateO con_prob_lang)) NNRO) → iProp Σ). *)
  (*   assert (NonExpansive Ψ'). *)
  (*   { intros n [[e1 σ1]?] [[e2 σ2]?] *)
  (*       [[?%leibniz_equiv ?%leibniz_equiv]?%leibniz_equiv]. *)
  (*     simplify_eq/=. f_equiv. } *)
  (*   rewrite /glm/glm'. *)
  (*   iApply (least_fixpoint_ind _ Ψ' with "[] H"). *)
  (*   iModIntro. iIntros ([[??]?]) "H". by iApply "IH". *)
  (* Qed.  *)
End modalities.

(** * The weakest precondition *)

Definition pgl_wp_pre `{!conerisWpGS con_prob_lang Σ}
    (wp : coPset -d> expr con_prob_lang -d> (val con_prob_lang -d> iPropO Σ) -d> iPropO Σ) :
  coPset -d> expr con_prob_lang -d> (val con_prob_lang -d> iPropO Σ) -d> iPropO Σ :=
  (λ E e1 Φ,
     match to_val e1 with
     | Some v => |={E}=>Φ v
     | None => ∀ σ1 ε1,
     state_interp σ1 ∗ err_interp ε1 ={E, ∅}=∗
     glm e1 σ1 ε1
       (λ '(e2, σ2, efs) (ε2: nonnegreal),  ▷|={∅,E}=> 
          state_interp σ2 ∗  err_interp ε2 ∗ wp E e2 Φ ∗
          [∗ list] ef ∈efs, wp ⊤ ef fork_post
       )
     end
  )%I.


Local Instance wp_pre_contractive `{!conerisWpGS con_prob_lang Σ} : Contractive (pgl_wp_pre).
Proof.
  rewrite /pgl_wp_pre /= => n wp wp' Hwp E e1 Φ /=.
  do 7 (f_equiv).
  apply least_fixpoint_ne_outer; [|done].
  intros Ψ [[e' σ'] ε']. rewrite /glm_pre.
  rewrite /stutter.
  do 20 f_equiv.
  f_contractive.
  repeat f_equiv; apply Hwp.
Qed.

(* TODO: get rid of stuckness in notation [iris/bi/weakestpre.v] so that we don't have to do this *)
Local Definition pgl_wp_def `{!conerisWpGS con_prob_lang Σ} : Wp (iProp Σ) (expr con_prob_lang) (val con_prob_lang) () :=
  {| wp := λ _ : (), fixpoint (pgl_wp_pre); wp_default := () |}.
Local Definition pgl_wp_aux : seal (@pgl_wp_def). Proof. by eexists. Qed.
Definition pgl_wp' := pgl_wp_aux.(unseal).
Global Arguments pgl_wp' {Σ _}.
Global Existing Instance pgl_wp'.
Local Lemma pgl_wp_unseal `{!conerisWpGS con_prob_lang Σ} : wp = (@pgl_wp_def Σ _).(wp).
Proof. rewrite -pgl_wp_aux.(seal_eq) //. Qed.

Section pgl_wp.
Context `{!conerisWpGS con_prob_lang Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val con_prob_lang → iProp Σ.
Implicit Types v : val con_prob_lang.
Implicit Types e : expr con_prob_lang.
Implicit Types σ : state con_prob_lang.
Implicit Types ρ : partial_cfg con_prob_lang.
Implicit Types ε : R.

(* Weakest pre *)
Lemma pgl_wp_unfold s E e Φ :
  WP e @ s; E {{ Φ }} ⊣⊢ pgl_wp_pre (wp (PROP:=iProp Σ) s) E e Φ.
Proof. rewrite pgl_wp_unseal. apply (fixpoint_unfold (pgl_wp_pre)). Qed.

Global Instance pgl_wp_ne s E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp (PROP:=iProp Σ) s E e).
Proof.
  revert e. induction (lt_wf n) as [n _ IH]=> e Φ Ψ HΦ.
  rewrite !pgl_wp_unfold /pgl_wp_pre /=.
  do 7 f_equiv.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [[]?]. rewrite /glm_pre.
  rewrite /stutter.
  do 20 f_equiv.
  f_contractive.
  do 4 f_equiv. 
  rewrite IH; [done|lia|].
  intros ?. eapply dist_le; first apply HΦ. lia. 
Qed.

Global Instance pgl_wp_proper s E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (wp (PROP:=iProp Σ) s E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply pgl_wp_ne=>v; apply equiv_dist.
Qed.
Global Instance pgl_wp_contractive s E e n :
  TCEq (to_val e) None →
  Proper (pointwise_relation _ (dist_later n) ==> dist n) (wp (PROP:=iProp Σ) s E e).
Proof.
  intros He Φ Ψ HΦ. rewrite !pgl_wp_unfold /pgl_wp_pre He /=.
  do 6 f_equiv. 
  apply least_fixpoint_ne_outer; [|done].
  intros ? [[]?]. rewrite /glm_pre.
  rewrite /stutter.
  do 20 f_equiv.
  f_contractive. do 6 f_equiv. done.
Qed.

Lemma pgl_wp_value_fupd' s E Φ v : WP of_val v @ s; E {{ Φ }} ⊣⊢ |={E}=> Φ v.
Proof. rewrite pgl_wp_unfold /pgl_wp_pre to_of_val. auto. Qed.

Lemma pgl_wp_strong_mono E1 E2 e Φ Ψ s :
  E1 ⊆ E2 →
  WP e @ s ; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ WP e @ s ; E2 {{ Ψ }}.
Proof.
  iIntros (HE) "H HΦ". iLöb as "IH" forall (e E1 E2 HE Φ Ψ).
  rewrite !pgl_wp_unfold /pgl_wp_pre /=.
  destruct (con_prob_lang.to_val e) as [v|] eqn:?.
  { iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _). }
  iIntros (σ1 ε) "[Hσ Hε]".
  iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  iMod ("H" with "[$]") as "H".
  iApply (glm_mono_pred with "[Hclose HΦ] H").
  iIntros ([[e2 σ2] efs]?) "H".
  iModIntro.
  iMod "H" as "(?&?& Hwp&?)". iFrame.
  iMod "Hclose" as "_". iModIntro.
  iApply ("IH" with "[] Hwp"); auto.
Qed.

Lemma fupd_pgl_wp s E e Φ : (|={E}=> WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }}.
Proof.
  rewrite pgl_wp_unfold /pgl_wp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?.
  { by iMod "H". }
   iIntros (σ1 ε) "Hi". iMod "H". by iApply "H".
Qed.
Lemma pgl_wp_fupd s E e Φ : WP e @ s; E {{ v, |={E}=> Φ v }} ⊢ WP e @ s; E {{ Φ }}.
Proof. iIntros "H". iApply (pgl_wp_strong_mono E with "H"); auto. Qed.

Lemma pgl_wp_atomic E1 E2 e Φ `{!Atomic StronglyAtomic e} a :
  (|={E1,E2}=> WP e @ a; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ a; E1 {{ Φ }}.
Proof.
  iIntros "H".
  rewrite !pgl_wp_unfold /pgl_wp_pre.
  destruct (to_val e) as [v|] eqn:He; [by do 2 iMod "H"|].
  iIntros (σ1 ε1) "(Hσ&Hε)".
  iSpecialize ("H" $! σ1 ε1).
  iMod ("H" with "[Hσ Hε]") as "H"; [iFrame|].
  iMod "H"; iModIntro.
  iApply (glm_strong_mono with "[] [] H"); [done|].
  iIntros ([e2 σ2] efs ε2) "([%σ' %Hstep]&H)".
  iNext.
  iMod "H" as "(Hσ&Hε&Hwp&?)".
  rewrite !pgl_wp_unfold /pgl_wp_pre.
  destruct (to_val e2) as [?|] eqn:He2.
  + iFrame. do 2 (iMod "Hwp"). by do 2 iModIntro.
  + specialize (atomic _ _ _ _ Hstep) as Hatomic. (* key step *)
    destruct Hatomic.
    congruence. (* how do we do this "by hand"? Not obvious to me *)
Qed.

Lemma pgl_wp_step_fupd s E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> P) -∗ WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ s; E1 {{ Φ }}.
Proof.
  rewrite !pgl_wp_unfold /pgl_wp_pre. iIntros (-> ?) "HR H".
  iIntros (σ1 ε) "[Hσ Hε]". iMod "HR".
  iMod ("H" with "[$Hσ $Hε]") as "H".
  iModIntro.
  iApply (glm_mono_pred with "[HR] H").
  iIntros ([[e2 σ2]efs] ?) "H".
  iModIntro.
  iMod "H" as "(Hσ & Hρ & H & Hf)".
  iMod "HR".
  iFrame "Hσ Hρ Hf".
  iApply (pgl_wp_strong_mono E2 with "H"); [done..|].
  iIntros "!>" (v) "H". by iApply "H".
Qed.

Lemma pgl_wp_bind K `{!ConLanguageCtx K} s E e Φ :
  WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }} ⊢ WP K e @ s; E {{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite pgl_wp_unfold /pgl_wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by iApply fupd_pgl_wp. }
  rewrite pgl_wp_unfold /pgl_wp_pre fill_not_val /=; [|done].
  iIntros (σ1 ε) "[Hσ Hε]".
  iMod ("H" with "[$Hσ $Hε]") as "H".
  iModIntro.
  iApply glm_bind; [done |].
  iApply (glm_mono with "[] [] H").
  - iPureIntro; lra.
  - iIntros ([[e2 σ2] efs] ?) "H".
    iModIntro.
    iMod "H" as "(Hσ & Hρ & H & Hf)".
    iModIntro.
    iFrame "Hσ Hρ Hf". by iApply "IH".
Qed.

(** * Derived rules *)
Lemma pgl_wp_mono s E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (pgl_wp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma pgl_wp_mask_mono s E1 E2 e Φ : E1 ⊆ E2 → WP e @ s; E1 {{ Φ }} ⊢ WP e @ s; E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (pgl_wp_strong_mono with "H"); auto. Qed.
Global Instance pgl_wp_mono' s E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply pgl_wp_mono. Qed.
Global Instance pgl_wp_flip_mono' s E e :
  Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (wp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply pgl_wp_mono. Qed.

Lemma pgl_wp_value_fupd s E Φ e v : IntoVal e v → WP e @ s; E {{ Φ }} ⊣⊢ |={E}=> Φ v.
Proof. intros <-. by apply pgl_wp_value_fupd'. Qed.
Lemma pgl_wp_value' s E Φ v : Φ v ⊢ WP (of_val v) @ s; E {{ Φ }}.
Proof. rewrite pgl_wp_value_fupd'. auto. Qed.
Lemma pgl_wp_value s E Φ e v : IntoVal e v → Φ v ⊢ WP e @ s; E {{ Φ }}.
Proof. intros <-. apply pgl_wp_value'. Qed.

Lemma pgl_wp_frame_l s E e Φ R : R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros "[? H]". iApply (pgl_wp_strong_mono with "H"); auto with iFrame. Qed.
Lemma pgl_wp_frame_r s E e Φ R : WP e @ s; E {{ Φ }} ∗ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros "[H ?]". iApply (pgl_wp_strong_mono with "H"); auto with iFrame. Qed.

Lemma pgl_wp_frame_step_l s E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> R) ∗ WP e @ s; E2 {{ Φ }} ⊢ WP e @ s; E1 {{ v, R ∗ Φ v }}.
Proof.
  iIntros (??) "[Hu Hwp]". iApply (pgl_wp_step_fupd with "Hu"); try done.
  iApply (pgl_wp_mono with "Hwp"). by iIntros (?) "$$".
Qed.
Lemma pgl_wp_frame_step_r s E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  WP e @ s; E2 {{ Φ }} ∗ (|={E1}[E2]▷=> R) ⊢ WP e @ s; E1 {{ v, Φ v ∗ R }}.
Proof.
  rewrite [(WP _ @ _; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply pgl_wp_frame_step_l.
Qed.
Lemma pgl_wp_frame_step_l' s E e Φ R :
  TCEq (to_val e) None → ▷ R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros (?) "[??]". iApply (pgl_wp_frame_step_l s E E); try iFrame; eauto. Qed.
Lemma pgl_wp_frame_step_r' s E e Φ R :
  TCEq (to_val e) None → WP e @ s; E {{ Φ }} ∗ ▷ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros (?) "[??]". iApply (pgl_wp_frame_step_r s E E); try iFrame; eauto. Qed.

Lemma pgl_wp_wand s E e Φ Ψ :
  WP e @ s; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (pgl_wp_strong_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma pgl_wp_wand_l s E e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (pgl_wp_wand with "Hwp H"). Qed.
Lemma wp_wand_r s E e Φ Ψ :
  WP e @ s; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (pgl_wp_wand with "Hwp H"). Qed.
Lemma pgl_wp_frame_wand s E e Φ R :
  R -∗ WP e @ s; E {{ v, R -∗ Φ v }} -∗ WP e @ s; E {{ Φ }}.
Proof.
  iIntros "HR HWP". iApply (pgl_wp_wand with "HWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.

End pgl_wp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{!conerisWpGS con_prob_lang Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val con_prob_lang → iProp Σ.
  Implicit Types v : val con_prob_lang.
  Implicit Types e : expr con_prob_lang.

  Global Instance frame_pgl_wp p s E e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Ψ }}) | 2.
  Proof. rewrite /Frame=> HR. rewrite pgl_wp_frame_l. apply pgl_wp_mono, HR. Qed.

  Global Instance is_except_0_pgl_wp s E e Φ : IsExcept0 (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_pgl_wp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_pgl_wp p s E e P Φ :
    ElimModal True p false (|==> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r wand_elim_r fupd_pgl_wp.
  Qed.

  Global Instance elim_modal_fupd_pgl_wp p s E e P Φ :
    ElimModal True p false (|={E}=> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_pgl_wp.
  Qed.

  Global Instance elim_modal_fupd_pgl_wp_atomic p s E1 E2 e P Φ :
    ElimModal (Atomic StronglyAtomic e) p false
            (|={E1,E2}=> P) P
            (WP e @ s; E1 {{ Φ }}) (WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }})%I | 100.
  Proof.
    intros ?.
    by rewrite intuitionistically_if_elim
      fupd_frame_r wand_elim_r pgl_wp_atomic.
  Qed.

  Global Instance add_modal_fupd_pgl_wp s E e P Φ :
    AddModal (|={E}=> P) P (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_pgl_wp. Qed.

  Global Instance elim_acc_pgl_wp_atomic {X} E1 E2 α β γ e s Φ :
    ElimAcc (X:=X) (Atomic StronglyAtomic e)
            (fupd E1 E2) (fupd E2 E1)
            α β γ (WP e @ s; E1 {{ Φ }})
            (λ x, WP e @ s; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I | 100.
  Proof.
    iIntros (?) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (pgl_wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_pgl_wp_nonatomic {X} E α β γ e s Φ :
    ElimAcc (X:=X) True (fupd E E) (fupd E E)
            α β γ (WP e @ s; E {{ Φ }})
            (λ x, WP e @ s; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply pgl_wp_fupd.
    iApply (pgl_wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.
End proofmode_classes.

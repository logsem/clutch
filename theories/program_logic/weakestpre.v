From Coq Require Export Reals Psatz.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre fixpoint big_op.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.prob Require Export couplings distribution.
From clutch.program_logic Require Export exec language.

Import uPred.

Local Open Scope R.

(** [irisGS] specifies the interface for the resource algebras implementing the
    [state] and [cfg] of a [language] [Λ]. For the purposes of defining the
    weakest precondition, we only need [irisGS] to give meaning to invariants,
    and provide predicates describing valid states via [state_interp] and valid
    specification configurations via [spec_interp]. *)
Class irisGS (Λ : language) (Σ : gFunctors) := IrisG {
  iris_invGS :> invGS_gen HasNoLc Σ;
  state_interp : state Λ → iProp Σ;
  spec_interp : cfg Λ → iProp Σ;
}.
Global Opaque iris_invGS.
Global Arguments IrisG {Λ Σ}.

(** * The coupling modality [exec_coupl]  *)
Section exec_coupl.
  Context `{!irisGS Λ Σ}.

  Definition exec_coupl_pre (Z : cfg Λ → cfg Λ → iProp Σ) (Φ : cfg Λ * cfg Λ → iProp Σ) :=
    (λ (x : cfg Λ * cfg Λ),
      let '((e1, σ1), (e1', σ1')) := x in
      (* [prim_step] on both sides *)
      (∃ R, ⌜reducible e1 σ1⌝ ∗
            ⌜Rcoupl (prim_step e1 σ1) (prim_step e1' σ1') R⌝ ∗
            ∀ ρ2 ρ2', ⌜R ρ2 ρ2'⌝ ={∅}=∗ Z ρ2 ρ2') ∨
      (* [prim_step] only on the left *)
      (∃ R, ⌜reducible e1 σ1⌝ ∗
            ⌜Rcoupl (prim_step e1 σ1) (dret (e1', σ1')) R⌝ ∗
            ∀ ρ2, ⌜R ρ2 (e1', σ1')⌝ ={∅}=∗ Z ρ2 (e1', σ1')) ∨
      (* an arbitrary amount of [prim_step]s on the right *)
      (∃ R n, ⌜Rcoupl (dret (e1, σ1)) (exec n (e1', σ1')) R⌝ ∗
            ∀ e2' σ2', ⌜R (e1, σ1) (e2', σ2')⌝ ={∅}=∗ Φ ((e1, σ1), (e2', σ2'))) ∨
      (* [prim_step] on the left, [state_step] on the right *)
      ([∨ list] α' ∈ get_active σ1',
        (∃ R, ⌜reducible e1 σ1⌝ ∗
              ⌜Rcoupl (prim_step e1 σ1) (state_step σ1' α')  R⌝ ∗
              ∀ e2 σ2 σ2', ⌜R (e2, σ2) σ2'⌝ ={∅}=∗ Z (e2, σ2) (e1', σ2'))) ∨
      (* [state_step] on the left, a [prim_step] on the right *)
      ([∨ list] α ∈ get_active σ1,
        (∃ R, ⌜Rcoupl (state_step σ1 α) (prim_step e1' σ1') R⌝ ∗
              ∀ σ2 e2' σ2', ⌜R σ2 (e2', σ2')⌝ ={∅}=∗ Φ ((e1, σ2), (e2', σ2')))) ∨
      (* [state_step] on both sides - a case for all combinations of 'active' indicies on both sides *)
      ([∨ list] αs ∈ list_prod (get_active σ1) (get_active σ1'),
        (∃ R, ⌜Rcoupl (state_step σ1 αs.1) (state_step σ1' αs.2) R⌝ ∗
              (∀ σ2 σ2', ⌜R σ2 σ2'⌝ ={∅}=∗ Φ ((e1, σ2), (e1', σ2')))))
    )%I.

  Local Instance exec_state_coupl_pre_NonExpansive Z Φ :
    NonExpansive (exec_coupl_pre Z Φ).
  Proof.
    rewrite /exec_coupl_pre.
    intros n ((?&?)&(?&?)) ((?&?)&(?&?)) [[[=] [=]] [[=] [=]]].
    by simplify_eq.
  Qed.

  Local Instance exec_coupl_pre_mono Z : BiMonoPred (exec_coupl_pre Z).
  Proof.
    split; [|apply _].
    iIntros (Φ Ψ HNEΦ HNEΨ) "#Hwand".
    rewrite /exec_coupl_pre.
    iIntros (((e1 & σ1) & (e1' & σ1'))) "Hexec".
    iDestruct "Hexec" as "[H | [H | [(% & % & % & HZ) | [Hl | [Hl | Hl]]]]]".
    - by iLeft.
    - by iRight; iLeft.
    - iRight; iRight; iLeft.
      iExists _, _. iSplit; [done|].
      iIntros. iApply "Hwand". by iApply "HZ".
    - iRight; iRight; iRight; iLeft.
      iInduction (get_active σ1') as [| l] "IH" forall "Hl".
      { rewrite big_orL_nil //. }
      rewrite !big_orL_cons.
      iDestruct "Hl" as "[(% & % & % & HZ) | H]".
      + iLeft. iExists _. do 2 (iSplit; [done|]).
        iIntros. by iApply "HZ".
      + iRight. by iApply "IH".
    - iRight; iRight; iRight; iRight; iLeft.
      iInduction (get_active σ1) as [| l] "IH" forall "Hl".
      { rewrite big_orL_nil //. }
      rewrite !big_orL_cons.
      iDestruct "Hl" as "[(% & % & HZ) | H]".
      + iLeft. iExists _. iSplit; [done|].
        iIntros. iApply "Hwand". by iApply "HZ".
      + iRight. by iApply "IH".
    - iRight; iRight; iRight; iRight; iRight.
      iInduction (list_prod (get_active σ1) (get_active σ1')) as [| l] "IH" forall "Hl".
      { rewrite big_orL_nil //. }
      rewrite !big_orL_cons.
      iDestruct "Hl" as "[(% & % & HZ) | H]".
      + iLeft. iExists _. iSplit; [done|].
        iIntros. iApply "Hwand". by iApply "HZ".
      + iRight. by iApply "IH".
  Qed.

  Definition exec_coupl' Z := bi_least_fixpoint (exec_coupl_pre Z).
  Definition exec_coupl e σ e' σ' Z := exec_coupl' Z ((e, σ), (e', σ')).

  Lemma exec_coupl_unfold e1 σ1 e1' σ1' Z :
    exec_coupl e1 σ1 e1' σ1' Z ≡
      ((∃ R, ⌜reducible e1 σ1⌝ ∗
            ⌜Rcoupl (prim_step e1 σ1) (prim_step e1' σ1') R⌝ ∗
            ∀ ρ2 ρ2', ⌜R ρ2 ρ2'⌝ ={∅}=∗ Z ρ2 ρ2') ∨
      (∃ R, ⌜reducible e1 σ1⌝ ∗
            ⌜Rcoupl (prim_step e1 σ1) (dret (e1', σ1')) R⌝ ∗
            ∀ ρ2, ⌜R ρ2 (e1', σ1')⌝ ={∅}=∗ Z ρ2 (e1', σ1')) ∨
      (∃ R n, ⌜Rcoupl (dret (e1, σ1)) (exec n (e1', σ1')) R⌝ ∗
              ∀ e2' σ2', ⌜R (e1, σ1) (e2', σ2')⌝ ={∅}=∗ exec_coupl e1 σ1 e2' σ2' Z) ∨
      ([∨ list] α' ∈ get_active σ1',
        (∃ R, ⌜reducible e1 σ1⌝ ∗
              ⌜Rcoupl (prim_step e1 σ1) (state_step σ1' α')  R⌝ ∗
              ∀ e2 σ2 σ2', ⌜R (e2, σ2) σ2'⌝ ={∅}=∗ Z (e2, σ2) (e1', σ2'))) ∨
      ([∨ list] α ∈ get_active σ1,
        (∃ R, ⌜Rcoupl (state_step σ1 α) (prim_step e1' σ1') R⌝ ∗
              ∀ σ2 e2' σ2', ⌜R σ2 (e2', σ2')⌝ ={∅}=∗ exec_coupl e1 σ2 e2' σ2' Z)) ∨
      ([∨ list] αs ∈ list_prod (get_active σ1) (get_active σ1'),
        (∃ R, ⌜Rcoupl (state_step σ1 αs.1) (state_step σ1' αs.2) R⌝ ∗
              (∀ σ2 σ2', ⌜R σ2 σ2'⌝ ={∅}=∗ exec_coupl e1 σ2 e1' σ2' Z))))%I.
  Proof. rewrite /exec_coupl/exec_coupl' least_fixpoint_unfold //. Qed.

  Local Definition cfgO := (prodO (exprO Λ) (stateO Λ)).

  Lemma exec_coupl_strong_mono e1 σ1 e1' σ1' (Z1 Z2 : cfg Λ → cfg Λ → iProp Σ) :
    (∀ e2 σ2 ρ', (⌜∃ σ, prim_step e1 σ (e2, σ2) > 0⌝ ∗ Z1 (e2, σ2) ρ' -∗ Z2 (e2, σ2) ρ')) -∗
    exec_coupl e1 σ1 e1' σ1' Z1 -∗ exec_coupl e1 σ1 e1' σ1' Z2.
  Proof.
    iIntros "HZ Hcpl". iRevert "HZ".
    rewrite /exec_coupl /exec_coupl'.
    set (Φ := (λ x,
      (∀ e2 σ2 ρ', ⌜∃ σ, prim_step x.1.1 σ (e2, σ2) > 0⌝ ∗ Z1 (e2, σ2) ρ' -∗ Z2 (e2, σ2) ρ') -∗
                  (bi_least_fixpoint (exec_coupl_pre Z2) x ))%I : prodO cfgO cfgO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros n ((?&?)&(?&?)) ((?&?)&(?&?)) [[[=] [=]] [[=] [=]]]. by simplify_eq. }
    iPoseProof (least_fixpoint_iter (exec_coupl_pre Z1) Φ with "[]") as "H"; last first.
    { iIntros "HZ". by iApply ("H" with "Hcpl"). }
    iIntros "!#" ([[? σ] [? σ']]). rewrite /exec_coupl_pre.
    iIntros "[(% & % & % & H) | [(% & % & % & H) | [(% & % & % & H) | [H | [H | H]]]]] HZ".
    - rewrite least_fixpoint_unfold.
      iLeft. iExists _.
      iSplit; [done|].
      iSplit.
      { iPureIntro. by apply Rcoupl_pos_R. }
      iIntros ([] [] (?&?&?)). iMod ("H" with "[//]").
      iModIntro. iApply "HZ". eauto.
    - rewrite least_fixpoint_unfold.
      iRight. iLeft. iExists _.
      iSplit; [done|].
      iSplit.
      { iPureIntro. by apply Rcoupl_pos_R. }
      iIntros ([] (?&?&?)). iMod ("H" with "[//]").
      iModIntro. iApply "HZ". eauto.
    - rewrite least_fixpoint_unfold.
      iRight. iRight. iLeft. iExists _, _.
      iSplit; [done|]. iIntros.
      by iApply ("H" with "[//]").
    - rewrite least_fixpoint_unfold.
      iRight; iRight; iRight; iLeft.
      iInduction (get_active σ') as [| l] "IH".
      { rewrite big_orL_nil //. }
      rewrite 2!big_orL_cons.
      iDestruct "H" as "[(% & % & % & H) | Ht]".
      + iLeft. iExists _. iSplit; [done|].
        iSplit.
        { iPureIntro. by apply Rcoupl_pos_R. }
        iIntros (??? (?&?&?)). iMod ("H" with "[//]").
        iModIntro. iApply "HZ". eauto.
      + iRight. by iApply ("IH" with "Ht").
    - rewrite least_fixpoint_unfold.
      iRight; iRight; iRight; iRight; iLeft.
      iInduction (get_active σ) as [| l] "IH".
      { rewrite big_orL_nil //. }
      rewrite 2!big_orL_cons.
      iDestruct "H" as "[(% & % & H) | Ht]".
      + iLeft. iExists _. iSplit; [done|].
        iIntros. by iApply ("H" with "[//]").
      + iRight. by iApply ("IH" with "Ht").
    - rewrite least_fixpoint_unfold.
      do 5 iRight.
      iInduction (list_prod (get_active σ) (get_active σ')) as [| l] "IH".
      { rewrite big_orL_nil //. }
      rewrite 2!big_orL_cons.
      iDestruct "H" as "[(% & ? & H) | Ht]".
      + iLeft. iExists _. iSplit; [done|].
        iIntros. by iApply ("H" with "[//]").
      + iRight. by iApply ("IH" with "Ht").
  Qed.

  Lemma exec_coupl_mono (Z1 Z2 : cfg Λ → cfg Λ → iProp Σ) e1 σ1 e1' σ1' :
    (∀ ρ ρ', Z1 ρ ρ' -∗ Z2 ρ ρ') -∗ exec_coupl e1 σ1 e1' σ1' Z1 -∗ exec_coupl e1 σ1 e1' σ1' Z2.
  Proof.
    iIntros "HZ". iApply exec_coupl_strong_mono.
    iIntros (???) "[_ ?]". by iApply "HZ".
  Qed.

  Lemma exec_coupl_strengthen e1 σ1 e1' σ1' (Z : cfg Λ → cfg Λ → iProp Σ) :
    exec_coupl e1 σ1 e1' σ1' Z -∗
    exec_coupl e1 σ1 e1' σ1' (λ '(e2, σ2) ρ', ⌜∃ σ, prim_step e1 σ (e2, σ2) > 0⌝ ∧ Z (e2, σ2) ρ').
  Proof.
    iApply exec_coupl_strong_mono.
    iIntros (???) "[[% ?] ?]". iSplit; [|done]. by iExists _.
  Qed.

  Lemma exec_coupl_bind K `{!LanguageCtx K} e1 σ1 e1' σ1' (Z : cfg Λ → cfg Λ → iProp Σ) :
    to_val e1 = None →
    exec_coupl e1 σ1 e1' σ1' (λ '(e2, σ2) ρ2', Z (K e2, σ2) ρ2') -∗ exec_coupl (K e1) σ1 e1' σ1' Z.
  Proof.
    iIntros (Hv) "Hcpl".
    iAssert (⌜to_val e1 = None⌝)%I as "-#H"; [done|].
    iRevert "H".
    rewrite /exec_coupl /exec_coupl'.
    set (Φ := (λ x, ⌜to_val x.1.1 = None⌝ -∗
                     bi_least_fixpoint (exec_coupl_pre Z) ((K x.1.1, x.1.2), (x.2.1, x.2.2)))%I
           : prodO cfgO cfgO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros n ((?&?)&(?&?)) ((?&?)&(?&?)) [[[=] [=]] [[=] [=]]]. by simplify_eq. }
    iPoseProof (least_fixpoint_iter
                  (exec_coupl_pre (λ '(e2, σ2) ρ2', Z (K e2, σ2) ρ2')) Φ
                 with "[]") as "H"; last first.
    { iIntros (?). iApply ("H" $! ((_, _), (_, _)) with "Hcpl [//]"). }
    iIntros "!#" ([[? σ] [? σ']]). rewrite {1}/exec_coupl_pre.
    iIntros "[(% & % & % & H) | [(% & % & % & H) | [(% & %n & % & H) | [H | [H | H]]]]] %Hv'".
    - rewrite least_fixpoint_unfold.
      iLeft. iExists (λ '(e2, σ2) ρ', ∃ e2', e2 = K e2' ∧ R2 (e2', σ2) ρ').
      rewrite fill_dmap //=.
      iSplit; [eauto using reducible_fill|].
      iSplit.
      { iPureIntro. rewrite -(dret_id_right (prim_step _ σ')).
        eapply Rcoupl_dbind; [|done].
        intros [] ?? =>/=. apply Rcoupl_dret. eauto. }
      iIntros ([] [] (? & -> & ?)).
      by iMod ("H" with "[//]").
    - rewrite least_fixpoint_unfold /=.
      iRight. iLeft. iExists (λ '(e2, σ2) ρ', ∃ e2', e2 = K e2' ∧ R2 (e2', σ2) ρ').
      iSplit; [eauto using reducible_fill|].
      iSplit.
      { iPureIntro.
        rewrite fill_dmap //=.
        rewrite -(dret_id_right (dret _)).
        eapply Rcoupl_dbind; [|done].
        intros [] ?? =>/=. apply Rcoupl_dret. eauto. }
      iIntros ([] (? & -> & ?)).
      by iMod ("H" with "[//]").
    - rewrite least_fixpoint_unfold.
      iRight. iRight. iLeft.
      iExists (λ '(e2, σ2) ρ', ∃ e2', e2 = K e2' ∧ R2 (e2', σ2) ρ'), n. simpl.
      iSplit.
      { iPureIntro.
        rewrite -(dret_id_right (exec _ _)).
        rewrite -(dret_id_left (λ ρ, dret (K ρ.1, ρ.2)) (_, σ)).
        eapply Rcoupl_dbind; [|done].
        intros [] [] ?. apply Rcoupl_dret. eauto. }
      iIntros (?? (? & <-%(inj _) & ?)).
      iMod ("H" with "[//] [//]") as "H".
      iModIntro. iApply "H".
    - rewrite least_fixpoint_unfold.
      iRight; iRight; iRight; iLeft. simpl.
      iInduction (get_active σ') as [| l] "IH".
      { rewrite big_orL_nil //. }
      rewrite 2!big_orL_cons.
      iDestruct "H" as "[(% & % & % & H) | Ht]".
      + iLeft. iExists (λ '(e2, σ2) σ2', ∃ e2', e2 = K e2' ∧ R2 (e2', σ2) σ2').
        iSplit; [eauto using reducible_fill|].
        iSplit.
        { iPureIntro.
          rewrite fill_dmap //.
          rewrite -(dret_id_right (state_step _ _)).
          eapply Rcoupl_dbind; [|done].
          intros [] ?? =>/=.
          apply Rcoupl_dret. eauto. }
        iIntros (??? (?& -> & ?)).
        iApply ("H" with "[//]").
      + iRight. by iApply ("IH" with "Ht").
    - rewrite least_fixpoint_unfold /=.
      iRight; iRight; iRight; iRight; iLeft.
      iInduction (get_active σ) as [| l] "IH".
      { rewrite big_orL_nil //. }
      rewrite 2!big_orL_cons.
      iDestruct "H" as "[(% & % & H) | Ht]".
      + iLeft. iExists _. iSplit; [done|].
        iIntros. by iApply ("H" with "[//]").
      + iRight. by iApply ("IH" with "Ht").
    - rewrite least_fixpoint_unfold /=.
      do 5 iRight.
      iInduction (list_prod (get_active σ) (get_active σ')) as [| l] "IH".
      { rewrite big_orL_nil //. }
      rewrite 2!big_orL_cons.
      iDestruct "H" as "[(% & ? & H) | Ht]".
      + iLeft. iExists _. iSplit; [done|].
        iIntros. iMod ("H" with "[//]") as "H".
        iModIntro. by iApply "H".
      + iRight. by iApply ("IH" with "Ht").
  Qed.

  Lemma exec_coupl_prim_steps e1 σ1 e1' σ1' Z :
    (∃ R, ⌜reducible e1 σ1⌝ ∗
          ⌜Rcoupl (prim_step e1 σ1) (prim_step e1' σ1') R⌝ ∗
          ∀ ρ2 ρ2', ⌜R ρ2 ρ2'⌝ ={∅}=∗ Z ρ2 ρ2')
    ⊢ exec_coupl e1 σ1 e1' σ1' Z.
  Proof.
    iIntros "H".
    rewrite {1}exec_coupl_unfold.
    by iLeft.
  Qed.

  Lemma exec_coupl_prim_step_l e1 σ1 e1' σ1' Z :
    (∃ R, ⌜reducible e1 σ1⌝ ∗
          ⌜Rcoupl (prim_step e1 σ1) (dret (e1', σ1')) R⌝ ∗
          ∀ ρ2, ⌜R ρ2 (e1', σ1')⌝ ={∅}=∗ Z ρ2 (e1', σ1'))
    ⊢ exec_coupl e1 σ1 e1' σ1' Z.
  Proof.
    iIntros "H".
    rewrite {1}exec_coupl_unfold.
    iRight; iLeft.
    done.
  Qed.

  Lemma exec_coupl_exec_r e1 σ1 e1' σ1' Z :
    (∃ R n, ⌜Rcoupl (dret (e1, σ1)) (exec n (e1', σ1')) R⌝ ∗
            ∀ e2' σ2', ⌜R (e1, σ1) (e2', σ2')⌝ ={∅}=∗ exec_coupl e1 σ1 e2' σ2' Z)
    ⊢ exec_coupl e1 σ1 e1' σ1' Z.
  Proof.
    iIntros "H".
    rewrite {1}exec_coupl_unfold.
    iRight; iRight; iLeft.
    done.
  Qed.

  Lemma exec_coupl_prim_state α' e1 σ1 e1' σ1' Z :
    α' ∈ get_active σ1' →
    (∃ R, ⌜reducible e1 σ1⌝ ∗
          ⌜Rcoupl (prim_step e1 σ1) (state_step σ1' α')  R⌝ ∗
          ∀ e2 σ2 σ2', ⌜R (e2, σ2) σ2'⌝ ={∅}=∗ Z (e2, σ2) (e1', σ2'))
    ⊢ exec_coupl e1 σ1 e1' σ1' Z.
  Proof.
    iIntros (?) "H".
    rewrite {1}exec_coupl_unfold.
    iRight; iRight; iRight; iLeft.
    by iApply big_orL_elem_of.
  Qed.

  Lemma exec_coupl_state_prim α e1 σ1 e1' σ1' Z :
    α ∈ get_active σ1 →
    (∃ R, ⌜Rcoupl (state_step σ1 α) (prim_step e1' σ1') R⌝ ∗
          ∀ σ2 e2' σ2', ⌜R σ2 (e2', σ2')⌝ ={∅}=∗ exec_coupl e1 σ2 e2' σ2' Z)
    ⊢ exec_coupl e1 σ1 e1' σ1' Z.
  Proof.
    iIntros (?) "H".
    rewrite {1}exec_coupl_unfold.
    iRight; iRight; iRight; iRight; iLeft.
    by iApply big_orL_elem_of.
  Qed.

  Lemma exec_coupl_state_steps α α' e1 σ1 e1' σ1' Z :
    (α, α') ∈ list_prod (get_active σ1) (get_active σ1') →
    (∃ R, ⌜Rcoupl (state_step σ1 α) (state_step σ1' α') R⌝ ∗
          (∀ σ2 σ2', ⌜R σ2 σ2'⌝ ={∅}=∗ exec_coupl e1 σ2 e1' σ2' Z))
    ⊢ exec_coupl e1 σ1 e1' σ1' Z.
  Proof.
    iIntros (?) "H".
    rewrite {1}exec_coupl_unfold.
    do 5 iRight.
    by iApply big_orL_elem_of.
  Qed.

  Lemma exec_coupl_reducible e e' σ σ' Z :
    exec_coupl e σ e' σ' Z ={∅}=∗ ⌜reducible e σ⌝.
  Proof.
    rewrite /exec_coupl /exec_coupl'.
    set (Φ := (λ x, |={∅}=> ⌜reducible x.1.1 x.1.2⌝)%I : prodO cfgO cfgO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros n ((?&?)&(?&?)) ((?&?)&(?&?)) [[[=] [=]] [[=] [=]]]. by simplify_eq. }
    iPoseProof (least_fixpoint_iter (exec_coupl_pre Z) Φ
                 with "[]") as "H"; last first.
    { done. }
    iIntros "!>" (([e1 σ1] & [e1' σ1'])). rewrite /exec_coupl_pre.
    iIntros "[(% & % & % & H) | [(% & % & % & H) | [(% & % & %Hcpl & H) | [H | [H | H]]]]] /=";
      [done|done| | | |].
    - eapply Rcoupl_pos_R in Hcpl.
      eapply Rcoupl_inhabited_l in Hcpl as ([] & [] & ? & [= -> ->]%dret_pos & ?); last first.
      { rewrite dret_mass; lra. }
      by iMod ("H" with "[//]").
    - iDestruct (big_orL_mono _ (λ n αs, |={∅}=> ⌜reducible e1 σ1⌝)%I  with "H") as "H".
      { iIntros (? α' ?%elem_of_list_lookup_2) "(% & % & _)". eauto. }
      iInduction (get_active σ1') as [| α'] "IH"; [done|].
      rewrite big_orL_cons.
      iDestruct "H" as "[? | H]"; [done|].
      by iApply "IH".
    - iDestruct (big_orL_mono _ (λ n αs, |={∅}=> ⌜reducible e1 σ1⌝)%I  with "H") as "H".
      { iIntros (? α' ?%elem_of_list_lookup_2) "(% & %Hcpl & H)".
        eapply Rcoupl_pos_R in Hcpl.
        eapply Rcoupl_inhabited_l in Hcpl as (σ2 & [] & ? & ? & ?); last first.
        { rewrite state_step_mass //. lra. }
        iApply (pure_impl_1 (reducible e1 σ2)).
        { iPureIntro. by eapply state_step_reducible. }
        by iMod ("H" with "[//]"). }
      iInduction (get_active σ1) as [| α] "IH"; [done|].
      rewrite big_orL_cons.
      iDestruct "H" as "[? | H]"; [done|].
      by iApply "IH".
    - iDestruct (big_orL_mono _ (λ n αs, |={∅}=> ⌜reducible e1 σ1⌝)%I  with "H") as "H".
      { iIntros (? [α1 α2] [? ?]%elem_of_list_lookup_2%elem_of_list_prod_1) "(% & %Hcpl & H)".
        eapply Rcoupl_pos_R in Hcpl.
        eapply Rcoupl_inhabited_l in Hcpl as (σ2 &?&?& Hs &?); last first.
        { rewrite state_step_mass //. lra. }
        iApply (pure_impl_1 (reducible e1 σ2)).
        { iPureIntro. by eapply state_step_reducible. }
        by iMod ("H" with "[//]"). }
      iInduction (list_prod (get_active σ1) (get_active σ1')) as [| [α α']] "IH"; [done|].
      rewrite big_orL_cons.
      iDestruct "H" as "[? | H]"; [done|].
      by iApply "IH".
  Qed.

  Lemma exec_coupl_det_r n e1 σ1 e1' σ1' e2' σ2' Z :
    exec n (e1', σ1') (e2', σ2') = 1 →
    exec_coupl e1 σ1 e2' σ2' Z -∗
    exec_coupl e1 σ1 e1' σ1' Z.
  Proof.
    iIntros (Hexec%pmf_1_eq_dret) "Hcpl".
    iApply exec_coupl_exec_r.
    iExists _, n. iSplit.
    { iPureIntro. apply Rcoupl_pos_R, Rcoupl_trivial.
      - apply dret_mass.
      - rewrite Hexec; apply dret_mass. }
    iIntros (e2'' σ2'' (_ & _ & H)).
    rewrite Hexec in H. by apply dret_pos in H as [= -> ->].
  Qed.

End exec_coupl.

(** * The weakest precondition  *)
Definition wp_pre `{!irisGS Λ Σ}
    (wp : coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
    coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
  match to_val e1 with
  | Some v => |={E}=> Φ v
  | None => ∀ σ1 e1' σ1',
      state_interp σ1 ∗ spec_interp (e1', σ1') ={E,∅}=∗
      exec_coupl e1 σ1 e1' σ1' (λ '(e2, σ2) '(e2', σ2'),
        ▷ |={∅,E}=> state_interp σ2 ∗ spec_interp (e2', σ2') ∗ wp E e2 Φ)
end%I.

Local Instance wp_pre_contractive `{!irisGS Λ Σ} : Contractive wp_pre.
Proof.
  rewrite /wp_pre /= => n wp wp' Hwp E e1 Φ.
  do 9 f_equiv.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [[] []]. rewrite /exec_coupl_pre.
  do 10 f_equiv.
  { f_equiv. do 2 case_match. f_contractive. do 3 f_equiv. apply Hwp. }
  { case_match. f_contractive. do 3 f_equiv. apply Hwp. }
  { do 9 f_equiv. f_contractive. do 3 f_equiv. apply Hwp. }
Qed.

(* TODO: get rid of stuckness in notation [iris/bi/weakestpre.v] so that we don't have to do this *)
Local Definition wp_def `{!irisGS Λ Σ} : Wp (iProp Σ) (expr Λ) (val Λ) stuckness :=
  λ (s : stuckness), fixpoint (wp_pre).
Local Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp' := wp_aux.(unseal).
Global Arguments wp' {Λ Σ _}.
Global Existing Instance wp'.
Local Lemma wp_unseal `{!irisGS Λ Σ} : wp = @wp_def Λ Σ _.
Proof. rewrite -wp_aux.(seal_eq) //. Qed.

Section wp.
Context `{!irisGS Λ Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types ρ : cfg Λ.

(* Weakest pre *)
Lemma wp_unfold s E e Φ :
  WP e @ s; E {{ Φ }} ⊣⊢ wp_pre (wp (PROP:=iProp Σ) s) E e Φ.
Proof. rewrite wp_unseal. apply (fixpoint_unfold wp_pre). Qed.

Global Instance wp_ne s E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp (PROP:=iProp Σ) s E e).
Proof.
  revert e. induction (lt_wf n) as [n _ IH]=> e Φ Ψ HΦ.
  rewrite !wp_unfold /wp_pre /=.
  do 9 f_equiv.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [[] []]. rewrite /exec_coupl_pre.
  do 10 f_equiv.
  (* If this proof breaks with iris > 4.0.0, check the changelog for
  dist_later. Using f_contractive_fin instead of f_contractive might work. *)
  { f_equiv. do 2 case_match. f_contractive. do 3 f_equiv.
    rewrite IH; [done|lia|]. intros ?. eapply dist_S, HΦ. }
  { case_match. f_contractive. do 3 f_equiv.
    rewrite IH; [done|lia|]. intros ?. eapply dist_S, HΦ. }
  { do 9 f_equiv. f_contractive. do 3 f_equiv. rewrite IH; [done|lia|].
    intros ?. eapply dist_S, HΦ. }
Qed.
Global Instance wp_proper s E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (wp (PROP:=iProp Σ) s E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne=>v; apply equiv_dist.
Qed.
Global Instance wp_contractive s E e n :
  TCEq (to_val e) None →
  Proper (pointwise_relation _ (dist_later n) ==> dist n) (wp (PROP:=iProp Σ) s E e).
Proof.
  intros He Φ Ψ HΦ. rewrite !wp_unfold /wp_pre He /=.
  do 8 f_equiv.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [[] []]. rewrite /exec_coupl_pre.
  do 10 f_equiv.
  { f_equiv. do 2 case_match. f_contractive. do 6 f_equiv.  }
  { case_match. f_contractive. do 6 f_equiv. }
  { do 9 f_equiv. f_contractive. do 6 f_equiv. }
Qed.

Lemma wp_value_fupd' s E Φ v : WP of_val v @ s; E {{ Φ }} ⊣⊢ |={E}=> Φ v.
Proof. rewrite wp_unfold /wp_pre to_of_val. auto. Qed.

Lemma wp_strong_mono s1 s2 E1 E2 e Φ Ψ :
  s1 ⊑ s2 → E1 ⊆ E2 →
  WP e @ s1; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ WP e @ s2; E2 {{ Ψ }}.
Proof.
  iIntros (? HE) "H HΦ". iLöb as "IH" forall (e E1 E2 HE Φ Ψ).
  rewrite !wp_unfold /wp_pre /=.
  destruct (to_val e) as [v|] eqn:?.
  { iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _). }
  iIntros (σ1 e1' σ1') "[Hσ Hs]".
  iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  iMod ("H" with "[$]") as "H".
  iModIntro.
  iApply (exec_coupl_mono with "[Hclose HΦ] H").
  iIntros ([e2 σ2] [e2' σ2']) "H".
  iModIntro.
  iMod "H" as "(?&?& Hwp)". iFrame.
  iMod "Hclose" as "_". iModIntro.
  iApply ("IH" with "[] Hwp"); auto.
Qed.

Lemma fupd_wp s E e Φ : (|={E}=> WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?.
  { by iMod "H". }
  iIntros (σ1 e1' σ1') "Hi". iMod "H". by iApply "H".
Qed.
Lemma wp_fupd s E e Φ : WP e @ s; E {{ v, |={E}=> Φ v }} ⊢ WP e @ s; E {{ Φ }}.
Proof. iIntros "H". iApply (wp_strong_mono s s E with "H"); auto. Qed.

Lemma wp_atomic s E1 E2 e Φ `{!Atomic WeaklyAtomic e} :
  (|={E1,E2}=> WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros "H". rewrite !wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { by iDestruct "H" as ">>> $". }
  iIntros (σ1 e1' σ1') "[Hσ Hs]". iMod "H".
  iMod ("H" with "[$]") as "H".
  iModIntro.
  iDestruct (exec_coupl_strengthen with "H") as "H".
  iApply (exec_coupl_mono with "[] H").
  iIntros ([e2 σ2] [e2' σ2']) "[[% %Hstep] H]".
  iModIntro.
  iMod "H" as "(Hσ & Hρ & H)".
  (* destruct s *)
  rewrite !wp_unfold /wp_pre.
  destruct (to_val e2) as [v2|] eqn:He2.
  + iDestruct "H" as ">> $". by iFrame.
  + iMod ("H" with "[$]") as "H".
    iMod (exec_coupl_reducible with "H") as %[ρ ?].
    pose proof (atomic _ _ _ Hstep ρ). lra.
  (* destruct (atomic _ _ _ Hstep) as [v <-%of_to_val]. *)
  (* rewrite wp_value_fupd'. iMod "H" as ">H". *)
  (* iModIntro. iFrame. by iApply wp_value_fupd'. *)
Qed.

Lemma wp_step_fupd s E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> P) -∗ WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ s; E1 {{ Φ }}.
Proof.
  rewrite !wp_unfold /wp_pre. iIntros (-> ?) "HR H".
  iIntros (σ1 e1' σ1') "[Hσ Hs]". iMod "HR".
  iMod ("H" with "[$Hσ $Hs]") as "H".
  iModIntro.
  iApply (exec_coupl_mono with "[HR] H").
  iIntros ([e2 σ2] [e2' σ2']) "H".
  iModIntro.
  iMod "H" as "(Hσ & Hρ & H)".
  iMod "HR".
  iFrame "Hσ Hρ".
  iApply (wp_strong_mono s s E2 with "H"); [done..|].
  iIntros "!>" (v) "H". by iApply "H".
Qed.

Lemma wp_bind K `{!LanguageCtx K} s E e Φ :
  WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }} ⊢ WP K e @ s; E {{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by iApply fupd_wp. }
  rewrite wp_unfold /wp_pre fill_not_val /=; [|done].
  iIntros (σ1 e1' σ1') "[Hσ Hs]".
  iMod ("H" with "[$Hσ $Hs]") as "H".
  iModIntro.
  iApply exec_coupl_bind; [done|].
  iApply (exec_coupl_mono with "[] H").
  iIntros ([e2 σ2] [e2' σ2']) "H".
  iModIntro.
  iMod "H" as "(Hσ & Hρ & H)".
  iModIntro. iFrame "Hσ Hρ". by iApply "IH".
Qed.

(* Lemma wp_bind_inv K `{!LanguageCtx K} s E e Φ : *)
(*   WP K e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }}. *)
(* Proof. *)
(*   iIntros "H". iLöb as "IH" forall (E e Φ). rewrite !wp_unfold /wp_pre /=. *)
(*   destruct (to_val e) as [v|] eqn:He. *)
(*   { apply of_to_val in He as <-. by rewrite !wp_unfold /wp_pre. } *)
(*   rewrite fill_not_val //. *)
(*   iIntros (σ1 ns κ κs nt) "Hσ". iMod ("H" with "[$]") as "[% H]". *)
(*   iModIntro; iSplit. *)
(*   { destruct s; eauto using reducible_fill_inv. } *)
(*   iIntros (e2 σ2 efs Hstep) "Hcred". *)
(*   iMod ("H" $! _ _ _ with "[] Hcred") as "H"; first eauto using fill_step. *)
(*   iIntros "!> !>". iMod "H". iModIntro. iApply (step_fupdN_wand with "H"). *)
(*   iIntros "H". iMod "H" as "($ & H & $)". iModIntro. by iApply "IH". *)
(* Qed. *)

(** * Derived rules *)
Lemma wp_mono s E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (wp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma wp_stuck_mono s1 s2 E e Φ :
  s1 ⊑ s2 → WP e @ s1; E {{ Φ }} ⊢ WP e @ s2; E {{ Φ }}.
Proof. iIntros (?) "H". iApply (wp_strong_mono with "H"); auto. Qed.
Lemma wp_stuck_weaken s E e Φ :
  WP e @ s; E {{ Φ }} ⊢ WP e @ E ?{{ Φ }}.
Proof. apply wp_stuck_mono. by destruct s. Qed.
Lemma wp_mask_mono s E1 E2 e Φ : E1 ⊆ E2 → WP e @ s; E1 {{ Φ }} ⊢ WP e @ s; E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (wp_strong_mono with "H"); auto. Qed.
Global Instance wp_mono' s E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.
Global Instance wp_flip_mono' s E e :
  Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (wp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.

Lemma wp_value_fupd s E Φ e v : IntoVal e v → WP e @ s; E {{ Φ }} ⊣⊢ |={E}=> Φ v.
Proof. intros <-. by apply wp_value_fupd'. Qed.
Lemma wp_value' s E Φ v : Φ v ⊢ WP (of_val v) @ s; E {{ Φ }}.
Proof. rewrite wp_value_fupd'. auto. Qed.
Lemma wp_value s E Φ e v : IntoVal e v → Φ v ⊢ WP e @ s; E {{ Φ }}.
Proof. intros <-. apply wp_value'. Qed.

Lemma wp_frame_l s E e Φ R : R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros "[? H]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.
Lemma wp_frame_r s E e Φ R : WP e @ s; E {{ Φ }} ∗ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros "[H ?]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.

Lemma wp_frame_step_l s E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> R) ∗ WP e @ s; E2 {{ Φ }} ⊢ WP e @ s; E1 {{ v, R ∗ Φ v }}.
Proof.
  iIntros (??) "[Hu Hwp]". iApply (wp_step_fupd with "Hu"); try done.
  iApply (wp_mono with "Hwp"). by iIntros (?) "$$".
Qed.
Lemma wp_frame_step_r s E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  WP e @ s; E2 {{ Φ }} ∗ (|={E1}[E2]▷=> R) ⊢ WP e @ s; E1 {{ v, Φ v ∗ R }}.
Proof.
  rewrite [(WP _ @ _; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply wp_frame_step_l.
Qed.
Lemma wp_frame_step_l' s E e Φ R :
  TCEq (to_val e) None → ▷ R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_l s E E); try iFrame; eauto. Qed.
Lemma wp_frame_step_r' s E e Φ R :
  TCEq (to_val e) None → WP e @ s; E {{ Φ }} ∗ ▷ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_r s E E); try iFrame; eauto. Qed.

Lemma wp_wand s E e Φ Ψ :
  WP e @ s; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (wp_strong_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma wp_wand_l s E e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_wand_r s E e Φ Ψ :
  WP e @ s; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_frame_wand s E e Φ R :
  R -∗ WP e @ s; E {{ v, R -∗ Φ v }} -∗ WP e @ s; E {{ Φ }}.
Proof.
  iIntros "HR HWP". iApply (wp_wand with "HWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.

End wp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{!irisGS Λ Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  Global Instance frame_wp p s E e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Ψ }}) | 2.
  Proof. rewrite /Frame=> HR. rewrite wp_frame_l. apply wp_mono, HR. Qed.

  Global Instance is_except_0_wp s E e Φ : IsExcept0 (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_wp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_wp p s E e P Φ :
    ElimModal True p false (|==> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r wand_elim_r fupd_wp.
  Qed.

  Global Instance elim_modal_fupd_wp p s E e P Φ :
    ElimModal True p false (|={E}=> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_wp.
  Qed.

  Global Instance elim_modal_fupd_wp_atomic p s E1 E2 e P Φ :
    ElimModal (Atomic WeaklyAtomic e) p false
            (|={E1,E2}=> P) P
            (WP e @ s; E1 {{ Φ }}) (WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }})%I | 100.
  Proof.
    intros ?. by rewrite intuitionistically_if_elim
      fupd_frame_r wand_elim_r wp_atomic.
  Qed.

  Global Instance add_modal_fupd_wp s E e P Φ :
    AddModal (|={E}=> P) P (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_wp. Qed.

  Global Instance elim_acc_wp_atomic {X} E1 E2 α β γ e s Φ :
    ElimAcc (X:=X) (Atomic WeaklyAtomic e)
            (fupd E1 E2) (fupd E2 E1)
            α β γ (WP e @ s; E1 {{ Φ }})
            (λ x, WP e @ s; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I | 100.
  Proof.
    iIntros (?) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_wp_nonatomic {X} E α β γ e s Φ :
    ElimAcc (X:=X) True (fupd E E) (fupd E E)
            α β γ (WP e @ s; E {{ Φ }})
            (λ x, WP e @ s; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply wp_fupd.
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.
End proofmode_classes.

From Coq Require Export Reals Psatz.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre fixpoint big_op.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext NNRbar.
From clutch.prob Require Export couplings_app distribution.
From clutch.common Require Export language erasable.
From clutch.base_logic Require Export spec_update.

Import uPred.

(*Local Open Scope NNR_scope.*)
Local Open Scope R.

(** [parisWpGS] specifies the interface for the resource algebras implementing the
    [state] and [cfg] of a [language] [Λ]. For the purposes of defining the
    weakest precondition, we only need [parisWpGS] to give meaning to invariants,
    and provide predicates describing valid states via [state_interp] and valid
    specification configurations via [spec_interp]. *)
Class parisWpGS (Λ : language) (Σ : gFunctors) `{!spec_updateGS (lang_markov Λ) Σ} := ParisWpGS {
  #[global] parisWpGS_invGS :: invGS_gen HasNoLc Σ;

  state_interp : state Λ → iProp Σ;
  err_interp : nonnegreal → iProp Σ;
}.
Global Opaque parisWpGS_invGS.
Global Arguments ParisWpGS {Λ Σ _}.

Section exec_stutter.
  Context `{!spec_updateGS (lang_markov Λ) Σ, !parisWpGS Λ Σ}.

  Definition exec_stutter (Z : nonnegreal -> iProp Σ) (ε:nonnegreal) : iProp Σ :=
    (⌜(1<=ε)%R⌝ ∨ Z ε)%I.

  Lemma exec_stutter_spend Z (ε:nonnegreal):
    ⌜(1<=ε)%R⌝ -∗ exec_stutter Z ε.
  Proof.
    iIntros. iLeft. done.
  Qed.

  Lemma exec_stutter_free Z (ε:nonnegreal):
    Z ε -∗ exec_stutter Z  ε.
  Proof.
    iIntros. iRight. done.
  Qed.

  Lemma exec_stutter_monotone Z1 Z2 ε:
    (Z1 ε -∗ Z2 ε) -∗ exec_stutter Z1 ε -∗ exec_stutter Z2 ε.
  Proof.
    iIntros "H1 [%H2|H2]".
    - iApply exec_stutter_spend. done.
    - iApply exec_stutter_free. iApply "H1". done.
  Qed.
End exec_stutter.

(** * The coupling modality [exec_coupl]  *)
Section exec_coupl.
  Context `{!spec_updateGS (lang_markov Λ) Σ, !parisWpGS Λ Σ}.

  Definition exec_coupl_pre (Z : cfg Λ → cfg Λ → nonnegreal -> iProp Σ) (Φ : (cfg Λ * cfg Λ) * nonnegreal  → iProp Σ) :=
    (λ (x : (cfg Λ * cfg Λ) * nonnegreal),
      let '(((e1, σ1), (e1', σ1')), ε) := x in
      (* [prim_step] on both sides *)
      (∃ R (ε1 ε2 : nonnegreal), ⌜ (ε1 + ε2 <= ε)%R ⌝ ∗ ⌜reducible (e1, σ1)⌝ ∗
            ⌜ARcoupl (prim_step e1 σ1) (prim_step e1' σ1') R ε1 ⌝ ∗
            ∀ ρ2 ρ2', ⌜R ρ2 ρ2'⌝ ={∅}=∗ Z ρ2 ρ2' ε2) ∨
      (* [prim_step] only on the left *)
      (∃ R (ε1 ε2 : nonnegreal), ⌜ (ε1 + ε2 <= ε)%R ⌝ ∗ ⌜reducible (e1, σ1)⌝ ∗
            ⌜ARcoupl (prim_step e1 σ1) (dret (e1', σ1')) R ε1⌝ ∗
            ∀ ρ2, ⌜R ρ2 (e1', σ1')⌝ ={∅}=∗ Z ρ2 (e1', σ1') ε2) ∨
      (* an arbitrary amount of [prim_step]s on the right *)
      (∃ R n (ε1 ε2 : nonnegreal), ⌜ (ε1 + ε2 <= ε)%R ⌝ ∗
          ⌜ARcoupl (dret (e1, σ1)) (pexec n (e1', σ1')) R ε1⌝ ∗
            ∀ e2' σ2', ⌜R (e1, σ1) (e2', σ2')⌝ ={∅}=∗ Φ (((e1, σ1), (e2', σ2')), ε2)) ∨
      (* [prim_step] on the left, [state_step] on the right *)
      ([∨ list] α' ∈ get_active σ1',
        (∃ R (ε1 ε2 : nonnegreal), ⌜ (ε1 + ε2 <= ε)%R ⌝ ∗ ⌜reducible (e1, σ1)⌝ ∗
              ⌜ARcoupl (prim_step e1 σ1) (state_step σ1' α')  R ε1⌝ ∗
              ∀ e2 σ2 σ2', ⌜R (e2, σ2) σ2'⌝ ={∅}=∗ Z (e2, σ2) (e1', σ2') ε2)) ∨
      (* [state_step] on the left, a [prim_step] on the right *)
      ([∨ list] α ∈ get_active σ1,
        (∃ R (ε1 ε2 : nonnegreal), ⌜ (ε1 + ε2 <= ε)%R ⌝ ∗
           ⌜ARcoupl (state_step σ1 α) (prim_step e1' σ1') R ε1⌝ ∗
              ∀ σ2 e2' σ2', ⌜R σ2 (e2', σ2')⌝ ={∅}=∗ Φ (((e1, σ2), (e2', σ2')), ε2))) ∨
        (* big state step on both sides *)
        (∃ R μ1 μ2 (ε1 ε2 : nonnegreal) (E2: state Λ -> nonnegreal), (* ⌜reducible (e1, σ1)⌝ ∗ *)
                    ⌜ (ε1 + ε2 <= ε)%R ⌝ ∗
                    ⌜ARcoupl (μ1) (μ2) R ε1⌝ ∗
                    ⌜ ∃ n, ∀ b, (0 <= E2 b <= n)%R ⌝ ∗
                    ⌜ (SeriesC (λ b, μ2 b * E2 b) <= ε2)%R ⌝ ∗
                    ⌜erasable μ1 σ1⌝ ∗
                    ⌜erasable μ2 σ1'⌝ ∗
              (∀ σ2 σ2', ⌜R σ2 σ2'⌝ ={∅}=∗ exec_stutter (λ ε', Φ (((e1, σ2), (e1', σ2')), ε')) (E2 σ2')))
    )%I.

  (* TODO: Define this globally, it appears in error credits too *)
  Canonical Structure NNRO := leibnizO nonnegreal.

  Local Instance exec_state_coupl_pre_NonExpansive Z Φ :
    NonExpansive (exec_coupl_pre Z Φ).
  Proof.
    rewrite /exec_coupl_pre.
    intros n (((?&?)&(?&?))&?) (((?&?)&(?&?))&?) [ [[[=][=]] [[=][=]]] [=] ].
    by simplify_eq.
  Qed.

  Local Instance exec_coupl_pre_mono Z : BiMonoPred (exec_coupl_pre Z).
  Proof.
    split; [|apply _].
    iIntros (Φ Ψ HNEΦ HNEΨ) "#Hwand".
    rewrite /exec_coupl_pre.
    iIntros ((((e1 & σ1)&(e1' & σ1'))&ε)) "Hexec".
    iDestruct "Hexec" as "[H | [H | [(% & % & % & % & % & % & HZ) | [Hl | [Hl | Hl]]]]]".
    - by iLeft.
    - by iRight; iLeft.
    - iRight; iRight; iLeft.
      iExists _, _, ε1, _. iSplit; [done|].
      iIntros. iSplit; [try done |].
      iIntros. iApply "Hwand". by iApply "HZ".
    - iRight; iRight; iRight; iLeft.
      iInduction (get_active σ1') as [| l] "IH" forall "Hl".
      { rewrite big_orL_nil //. }
      rewrite !big_orL_cons.
      iDestruct "Hl" as "[(% & % & % & % & % & % & HZ) | H]".
      + iLeft. iExists _,_,_ .
        do 3 (iSplit; [done|]).
        iIntros. by iApply "HZ".
      + iRight. by iApply "IH".
    - iRight; iRight; iRight; iRight; iLeft.
      iInduction (get_active σ1) as [| l] "IH" forall "Hl".
      { rewrite big_orL_nil //. }
      rewrite !big_orL_cons.
      iDestruct "Hl" as "[(% & % & % & % & % & HZ) | H]".
      + iLeft. iExists _,_,_. iSplit; [done|].
        iIntros. iSplit; [done|].
        iIntros. iApply "Hwand". by iApply "HZ".
      + iRight. by iApply "IH".
    - iRight; iRight; iRight; iRight; iRight.
      iDestruct "Hl" as "(%&%&%&%&%&%&%&%&%&%&%&%&H)".
      iExists _, _, _, _, _, _. repeat iSplit; try done.
      iIntros. iApply exec_stutter_monotone; last iApply ("H" with "[//]").
      simpl. iApply "Hwand".
  Qed.

  Definition exec_coupl' Z := bi_least_fixpoint (exec_coupl_pre Z).
  Definition exec_coupl e σ e' σ' Z ε := exec_coupl' Z (((e, σ), (e', σ')),ε).

  Lemma exec_coupl_unfold e1 σ1 e1' σ1' Z ε :
    exec_coupl e1 σ1 e1' σ1' Z ε ≡
      ((∃ R (ε1 ε2 : nonnegreal), ⌜ (ε1 + ε2 <= ε)%R ⌝ ∗ ⌜reducible (e1, σ1)⌝ ∗
            ⌜ARcoupl (prim_step e1 σ1) (prim_step e1' σ1') R ε1 ⌝ ∗
            ∀ ρ2 ρ2', ⌜R ρ2 ρ2'⌝ ={∅}=∗ Z ρ2 ρ2' ε2) ∨
      (∃ R (ε1 ε2 : nonnegreal), ⌜ (ε1 + ε2 <= ε)%R ⌝ ∗ ⌜reducible (e1, σ1)⌝ ∗
            ⌜ARcoupl (prim_step e1 σ1) (dret (e1', σ1')) R ε1⌝ ∗
            ∀ ρ2, ⌜R ρ2 (e1', σ1')⌝ ={∅}=∗ Z ρ2 (e1', σ1') ε2) ∨
      (∃ R n (ε1 ε2 : nonnegreal), ⌜ (ε1 + ε2 <= ε)%R ⌝ ∗
          ⌜ARcoupl (dret (e1, σ1)) (pexec n (e1', σ1')) R ε1⌝ ∗
            ∀ e2' σ2', ⌜R (e1, σ1) (e2', σ2')⌝ ={∅}=∗ exec_coupl e1 σ1 e2' σ2' Z ε2) ∨
      (* [prim_step] on the left, [state_step] on the right *)
      ([∨ list] α' ∈ get_active σ1',
        (∃ R (ε1 ε2 : nonnegreal), ⌜ (ε1 + ε2 <= ε)%R ⌝ ∗ ⌜reducible (e1, σ1)⌝ ∗
              ⌜ARcoupl (prim_step e1 σ1) (state_step σ1' α')  R ε1⌝ ∗
              ∀ e2 σ2 σ2', ⌜R (e2, σ2) σ2'⌝ ={∅}=∗ Z (e2, σ2) (e1', σ2') ε2)) ∨
      (* [state_step] on the left, a [prim_step] on the right *)
      ([∨ list] α ∈ get_active σ1,
        (∃ R (ε1 ε2 : nonnegreal), ⌜ (ε1 + ε2 <= ε)%R ⌝ ∗
           ⌜ARcoupl (state_step σ1 α) (prim_step e1' σ1') R ε1⌝ ∗
              ∀ σ2 e2' σ2', ⌜R σ2 (e2', σ2')⌝ ={∅}=∗ exec_coupl e1 σ2 e2' σ2' Z ε2)) ∨
      (* big state step *)
        (∃ R μ1 μ2 (ε1 ε2 : nonnegreal) (E2 : state Λ -> nonnegreal), (* ⌜reducible (e1, σ1)⌝ ∗ *)
                    ⌜ (ε1 + ε2 <= ε)%R ⌝ ∗
                    ⌜ARcoupl (μ1) (μ2) R ε1⌝ ∗
                    ⌜∃ n, ∀ b, (0 <= E2 b <= n)%R ⌝ ∗
                    ⌜ (SeriesC (λ b, μ2 b * E2 b) <= ε2)%R ⌝ ∗
                    ⌜erasable μ1 σ1⌝ ∗
                    ⌜erasable μ2 σ1'⌝ ∗
              (∀ σ2 σ2', ⌜R σ2 σ2'⌝ ={∅}=∗ exec_stutter (λ ε', exec_coupl e1 σ2 e1' σ2' Z ε') (E2 σ2')))
    )%I.
  Proof. rewrite /exec_coupl/exec_coupl' least_fixpoint_unfold //. Qed.

  Local Definition cfgO := (prodO (exprO Λ) (stateO Λ)).

  Lemma exec_coupl_strong_mono e1 σ1 e1' σ1'
    (Z1 Z2 : cfg Λ → cfg Λ → nonnegreal -> iProp Σ) (ε : nonnegreal):
    (∀ e2 σ2 ρ' ε',
       (⌜∃ σ, prim_step e1 σ (e2, σ2) > 0⌝ ∗ Z1 (e2, σ2) ρ' ε' -∗ Z2 (e2, σ2) ρ' ε')) -∗
    exec_coupl e1 σ1 e1' σ1' Z1 ε -∗ exec_coupl e1 σ1 e1' σ1' Z2 ε.
  Proof.
    iIntros "HZ Hcpl". iRevert "HZ".
    rewrite /exec_coupl /exec_coupl'.
    set (Φ := (λ x,
      (∀ e2 σ2 ρ' ε', ⌜∃ σ, prim_step x.1.1.1 σ (e2, σ2) > 0⌝ ∗ Z1 (e2, σ2) ρ' ε' -∗ Z2 (e2, σ2) ρ' ε') -∗
                  (bi_least_fixpoint (exec_coupl_pre Z2) x ))%I : prodO (prodO cfgO cfgO) NNRO  → iPropI Σ).
    assert (NonExpansive Φ).
    { intros n (((?&?)&(?&?))&?) (((?&?)&(?&?))&?) [[[[=][=]][[=][=]]][=]]. by simplify_eq. }
    iPoseProof (least_fixpoint_iter (exec_coupl_pre Z1) Φ with "[]") as "H"; last first.
    { iIntros "HZ". by iApply ("H" with "Hcpl"). }
    iIntros "!#" ([[[? σ] [? σ']] ε' ]). rewrite /exec_coupl_pre.
    iIntros "[(% & % & % & % & % & % & H) | [(% & % & % & % & % & % & H) | [(% & % & % & % & % & % & H) | [H | [H | H]]]]] HZ".
    - rewrite least_fixpoint_unfold.
      iLeft. iExists _,_,_.
      iSplit; [done|].
      iSplit; [done|].
      iSplit.
      { iPureIntro. by apply ARcoupl_pos_R. }
      iIntros ([] [] (?&?&?)). iMod ("H" with "[//]").
      iModIntro. iApply "HZ". eauto.
    - rewrite least_fixpoint_unfold.
      iRight. iLeft. iExists _, _, _.
      iSplit; [done|].
      iSplit; [done|].
      iSplit.
      { iPureIntro. by apply ARcoupl_pos_R. }
      iIntros ([] (?&?&?)). iMod ("H" with "[//]").
      iModIntro. iApply "HZ". eauto.
    - rewrite least_fixpoint_unfold.
      iRight. iRight. iLeft. iExists _, _, _, _.
      iSplit; [done|].
      iSplit; [done|].
      iIntros.
      by iApply ("H" with "[//]").
    - rewrite least_fixpoint_unfold.
      iRight; iRight; iRight; iLeft.
      iInduction (get_active σ') as [| l] "IH".
      { rewrite big_orL_nil //. }
      rewrite 2!big_orL_cons.
      iDestruct "H" as "[(% & % & % & % & % & % & H) | Ht]".
      + iLeft. iExists _,_,_. iSplit; [done|].
        iSplit; [done|].
        iSplit.
        { iPureIntro. by apply ARcoupl_pos_R. }
        iIntros (??? (?&?&?)). iMod ("H" with "[//]").
        iModIntro. iApply "HZ". eauto.
      + iRight. by iApply ("IH" with "Ht").
    - rewrite least_fixpoint_unfold.
      iRight; iRight; iRight; iRight; iLeft.
      iInduction (get_active σ) as [| l] "IH".
      { rewrite big_orL_nil //. }
      rewrite 2!big_orL_cons.
      iDestruct "H" as "[(% & % & % & % & % & H) | Ht]".
      + iLeft. iExists _, _ , _.
        iSplit; [done|].
        iSplit; [done|].
        iIntros. by iApply ("H" with "[//]").
      + iRight. by iApply ("IH" with "Ht").
    - rewrite least_fixpoint_unfold.
      do 5 iRight.
      simpl.
      iDestruct "H" as "(%&%&%&%&%&%&%&%&%&%&%&%&H)".
      iExists _, _, _, _, _, _.
      repeat iSplit; try done.
      iIntros. iApply (exec_stutter_monotone with "[HZ]"); last by iApply ("H" with "[//]").
      simpl.
      iIntros "IH". by iApply "IH".
  Qed.

  Lemma exec_coupl_mono (Z1 Z2 : cfg Λ → cfg Λ → nonnegreal -> iProp Σ) e1 σ1 e1' σ1' ε :
    (∀ ρ ρ' ε', Z1 ρ ρ' ε' -∗ Z2 ρ ρ' ε') -∗ exec_coupl e1 σ1 e1' σ1' Z1 ε -∗ exec_coupl e1 σ1 e1' σ1' Z2 ε.
  Proof.
    iIntros "HZ". iApply exec_coupl_strong_mono.
    iIntros (????) "[_ ?]". by iApply "HZ".
  Qed.

  Lemma exec_coupl_strengthen e1 σ1 e1' σ1' (Z : cfg Λ → cfg Λ → nonnegreal -> iProp Σ) ε:
    exec_coupl e1 σ1 e1' σ1' Z ε -∗
    exec_coupl e1 σ1 e1' σ1'
    (λ '(e2, σ2) ρ' ε', ⌜∃ σ, prim_step e1 σ (e2, σ2) > 0⌝ ∧ Z (e2, σ2) ρ' ε') ε.
  Proof.
    iApply exec_coupl_strong_mono.
    iIntros (????) "[[% ?] ?]". iSplit; [|done]. by iExists _.
  Qed.

  Lemma exec_coupl_bind K `{!LanguageCtx K} e1 σ1 e1' σ1' (Z : cfg Λ → cfg Λ → nonnegreal -> iProp Σ) ε :
    to_val e1 = None →
    exec_coupl e1 σ1 e1' σ1' (λ '(e2, σ2) ρ2' ε', Z (K e2, σ2) ρ2' ε') ε -∗ exec_coupl (K e1) σ1 e1' σ1' Z ε.
  Proof.
    iIntros (Hv) "Hcpl".
    iAssert (⌜to_val e1 = None⌝)%I as "-#H"; [done|].
    iRevert "H".
    rewrite /exec_coupl /exec_coupl'.
    set (Φ := (λ x, ⌜to_val x.1.1.1 = None⌝ -∗
                     bi_least_fixpoint (exec_coupl_pre Z) (((K x.1.1.1, x.1.1.2), (x.1.2.1, x.1.2.2)), x.2))%I
           : prodO (prodO cfgO cfgO) NNRO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros n (((?&?)&(?&?))&?) (((?&?)&(?&?))&?) [[[[=] [=]] [[=] [=]]][=]] . by simplify_eq. }
    iPoseProof (least_fixpoint_iter
                  (exec_coupl_pre (λ '(e2, σ2) ρ2' ε', Z (K e2, σ2) ρ2' ε')) Φ
                 with "[]") as "H"; last first.
    { iIntros (?). iApply ("H" $! (((_, _), (_, _)),_) with "Hcpl [//]"). }
    iIntros "!#" ([[[? σ] [? σ']]ε' ]). rewrite {1}/exec_coupl_pre.
    iIntros "[(% & % & % & % & % & % & H) | [(% & % & % & % & % & % & H) | [(% & %n & % & % & % & % & H) | [H | [H | H]]]]] %Hv'".
    - rewrite least_fixpoint_unfold.
      iLeft. iExists (λ '(e2, σ2) ρ', ∃ e2', e2 = K e2' ∧ R2 (e2', σ2) ρ').
      rewrite fill_dmap //=.
      iExists _, _.
      iSplit;[done|].
      iSplit; [eauto using reducible_fill|].
      iSplit.
      { iPureIntro. rewrite -(dret_id_right (prim_step _ σ')).
        rewrite <- Rplus_0_r.
        rewrite /dmap.
        eapply (ARcoupl_dbind _ _ _ _ R2); auto.
        - apply cond_nonneg.
        - lra.
        - intros [] ?? =>/=. apply ARcoupl_dret. eauto.
      }
      iIntros ([] [] (? & -> & ?)).
      by iMod ("H" with "[//]").
    - rewrite least_fixpoint_unfold /=.
      iRight. iLeft. iExists (λ '(e2, σ2) ρ', ∃ e2', e2 = K e2' ∧ R2 (e2', σ2) ρ').
      iExists _, _.
      iSplit; [done|].
      iSplit; [eauto using reducible_fill|].
      iSplit.
      { iPureIntro.
        rewrite fill_dmap //=.
        rewrite -(dret_id_right (dret _)).
        rewrite <- Rplus_0_r.
        eapply ARcoupl_dbind; eauto.
        - apply cond_nonneg.
        - lra.
        - intros [] ?? =>/=. apply ARcoupl_dret. eauto. }
      iIntros ([] (? & -> & ?)).
      by iMod ("H" with "[//]").
    - rewrite least_fixpoint_unfold.
      iRight. iRight. iLeft.
      iExists (λ '(e2, σ2) ρ', ∃ e2', e2 = K e2' ∧ R2 (e2', σ2) ρ'), n, _, _. simpl.
      iSplit; [done | ].
      iSplit.
      { iPureIntro.
        rewrite -(dret_id_right (pexec _ _)).
        rewrite -(dret_id_left (λ ρ, dret (K ρ.1, ρ.2)) (_, σ)).
        rewrite <- Rplus_0_r.
        eapply ARcoupl_dbind; eauto.
        - apply cond_nonneg.
        - lra.
        - intros [] [] ?. apply ARcoupl_dret. eauto. }
      iIntros (?? (? & <-%(inj _) & ?)).
      iMod ("H" with "[//] [//]") as "H".
      iModIntro. iApply "H".
    - rewrite least_fixpoint_unfold.
      iRight; iRight; iRight; iLeft. simpl.
      iInduction (get_active σ') as [| l] "IH".
      { rewrite big_orL_nil //. }
      rewrite 2!big_orL_cons.
      iDestruct "H" as "[(% & % & % & % & % & % & H) | Ht]".
      + iLeft. iExists (λ '(e2, σ2) σ2', ∃ e2', e2 = K e2' ∧ R2 (e2', σ2) σ2'),_,_.
        iSplit;[done|].
        iSplit; [eauto using reducible_fill|].
        iSplit.
        { iPureIntro.
          rewrite fill_dmap //.
          rewrite -(dret_id_right (state_step _ _)).
          rewrite <- Rplus_0_r.
          eapply ARcoupl_dbind; eauto.
          - apply cond_nonneg.
          - lra.
          - intros [] ?? =>/=.
            apply ARcoupl_dret. eauto. }
        iIntros (??? (?& -> & ?)).
        iApply ("H" with "[//]").
      + iRight. by iApply ("IH" with "Ht").
    - rewrite least_fixpoint_unfold /=.
      iRight; iRight; iRight; iRight; iLeft.
      iInduction (get_active σ) as [| l] "IH".
      { rewrite big_orL_nil //. }
      rewrite 2!big_orL_cons.
      iDestruct "H" as "[(% & % & % & % & % & H) | Ht]".
      + iLeft. iExists _,_,_.
        iSplit; [done|].
        iSplit; [done|].
        iIntros. by iApply ("H" with "[//]").
      + iRight. by iApply ("IH" with "Ht").
    - rewrite least_fixpoint_unfold /=.
      do 5 iRight.
      iDestruct "H" as "(%&%&%&%&%&%&%&%&%&%&%&%&H)".
      iExists _, _, _, _, _, _.
      repeat (iSplit; [done|]).
      iIntros. iMod ("H" with "[//]") as "H". iModIntro.
      iApply (exec_stutter_monotone with "[][$]").
      iIntros "H".
      by iApply "H".
  Qed.

  Lemma exec_coupl_prim_steps e1 σ1 e1' σ1' Z (ε ε' : nonnegreal) :
    (∃ R, ⌜reducible (e1, σ1)⌝ ∗
          ⌜ARcoupl (prim_step e1 σ1) (prim_step e1' σ1') R ε⌝ ∗
          ∀ ρ2 ρ2', ⌜R ρ2 ρ2'⌝ ={∅}=∗ Z ρ2 ρ2' ε')
    ⊢ exec_coupl e1 σ1 e1' σ1' Z (nnreal_plus ε ε').
  Proof.
    iIntros "(%&?&?&H)".
    rewrite {1}exec_coupl_unfold.
    iLeft.
    iExists _,ε,ε'.
    iFrame.
    done.
  Qed.

  Lemma exec_coupl_prim_step_l e1 σ1 e1' σ1' Z (ε ε' : nonnegreal) :
    (∃ R, ⌜reducible (e1, σ1)⌝ ∗
          ⌜ARcoupl (prim_step e1 σ1) (dret (e1', σ1')) R ε⌝ ∗
          ∀ ρ2, ⌜R ρ2 (e1', σ1')⌝ ={∅}=∗ Z ρ2 (e1', σ1') ε')
    ⊢ exec_coupl e1 σ1 e1' σ1' Z (nnreal_plus ε ε').
  Proof.
    iIntros "(%&?&?&H)".
    rewrite {1}exec_coupl_unfold.
    iRight; iLeft.
    iExists _,ε,ε'.
    iFrame.
    done.
  Qed.

  Lemma exec_coupl_exec_r e1 σ1 e1' σ1' Z (ε ε' : nonnegreal) :
    (∃ R n, ⌜ARcoupl (dret (e1, σ1)) (pexec n (e1', σ1')) R ε⌝ ∗
            ∀ e2' σ2', ⌜R (e1, σ1) (e2', σ2')⌝ ={∅}=∗ exec_coupl e1 σ1 e2' σ2' Z ε')
    ⊢ exec_coupl e1 σ1 e1' σ1' Z (nnreal_plus ε ε').
  Proof.
    iIntros "(%&%&?&H)".
    rewrite {1}exec_coupl_unfold.
    iRight; iRight; iLeft.
    iExists _, _, ε, ε'.
    iFrame.
    done.
  Qed.

  Lemma exec_coupl_prim_state α' e1 σ1 e1' σ1' Z (ε ε' : nonnegreal):
    α' ∈ get_active σ1' →
    (∃ R, ⌜reducible (e1, σ1)⌝ ∗
          ⌜ARcoupl (prim_step e1 σ1) (state_step σ1' α') R ε⌝ ∗
          ∀ e2 σ2 σ2', ⌜R (e2, σ2) σ2'⌝ ={∅}=∗ Z (e2, σ2) (e1', σ2') ε')
    ⊢ exec_coupl e1 σ1 e1' σ1' Z (nnreal_plus ε ε').
  Proof.
    iIntros (?) "(%&?&?&H)".
    rewrite {1}exec_coupl_unfold.
    iRight; iRight; iRight; iLeft.
    iApply big_orL_elem_of; [done |].
    iExists _,_,_.
    iFrame.
    done.
  Qed.

  Lemma exec_coupl_state_prim α e1 σ1 e1' σ1' Z (ε ε' : nonnegreal) :
    α ∈ get_active σ1 →
    (∃ R, ⌜ARcoupl (state_step σ1 α) (prim_step e1' σ1') R ε⌝ ∗
          ∀ σ2 e2' σ2', ⌜R σ2 (e2', σ2')⌝ ={∅}=∗ exec_coupl e1 σ2 e2' σ2' Z ε')
    ⊢ exec_coupl e1 σ1 e1' σ1' Z (nnreal_plus ε ε').
  Proof.
    iIntros (?) "(%&?&H)".
    rewrite {1}exec_coupl_unfold.
    iRight; iRight; iRight; iRight; iLeft.
    iApply big_orL_elem_of; eauto.
    iExists _, ε, ε'.
    iFrame.
    done.
  Qed.


  Lemma exec_coupl_big_state_steps_adv_RHS e1 σ1 e1' σ1' Z (ε1 ε2 : nonnegreal):
    (∃ R μ1 μ2 (E2 : state Λ -> nonnegreal), (* ⌜reducible (e1, σ1)⌝ ∗ *)
                ⌜ARcoupl (μ1) (μ2) R ε1⌝ ∗
                ⌜∃ n, ∀ b, (0 <= E2 b <= n)%R ⌝ ∗
                ⌜(SeriesC (λ b, μ2 b * (E2 b)) <= ε2)%R⌝ ∗
                ⌜erasable μ1 σ1⌝ ∗
                ⌜erasable μ2 σ1'⌝ ∗
          (∀ σ2 σ2', ⌜R σ2 σ2'⌝ ={∅}=∗ exec_stutter (λ ε', exec_coupl e1 σ2 e1' σ2' Z ε') (E2 σ2')))
    ⊢ exec_coupl e1 σ1 e1' σ1' Z (nnreal_plus ε1 ε2).
  Proof.
    iIntros "H".
    rewrite {1}exec_coupl_unfold.
    do 5 iRight.
    iDestruct "H" as "(%&%&%&%&%&%&%&%&%&H)".
    iExists _, _, _, _, _, _.
    repeat iSplit; simpl; try done.
  Qed.

  Lemma exec_coupl_big_state_steps e1 σ1 e1' σ1' Z (ε1 ε2 : nonnegreal):
    (∃ R μ1 μ2, (* ⌜reducible (e1, σ1)⌝ ∗ *)
                ⌜ARcoupl (μ1) (μ2) R ε1⌝ ∗
                ⌜erasable μ1 σ1⌝ ∗
                ⌜erasable μ2 σ1'⌝ ∗
          (∀ σ2 σ2', ⌜R σ2 σ2'⌝ ={∅}=∗ exec_coupl e1 σ2 e1' σ2' Z ε2))
    ⊢ exec_coupl e1 σ1 e1' σ1' Z (nnreal_plus ε1 ε2).
  Proof.
    iIntros "H".
    iDestruct "H" as "(%&%&%&%&%&%&H)".
    iApply exec_coupl_big_state_steps_adv_RHS.
    iExists _, _, _, _.
    repeat iSplit; try done; last first.
    { iIntros. iMod ("H" with "[//]"). iModIntro. iApply exec_stutter_free. done. }
    - simpl.
      iPureIntro. rewrite SeriesC_scal_r.
      assert (SeriesC μ2 <= 1) by done.
      replace (nonneg ε2)%R with (1*nonneg ε2)%R at 2 by lra.
      apply Rmult_le_compat_r; auto. apply cond_nonneg.
    - iPureIntro. eexists; intros _. split; [apply cond_nonneg|naive_solver].
  Qed.

  Lemma exec_coupl_det_r n e1 σ1 e1' σ1' e2' σ2' Z (ε : nonnegreal) :
    pexec n (e1', σ1') (e2', σ2') = 1 →
    exec_coupl e1 σ1 e2' σ2' Z ε -∗
    exec_coupl e1 σ1 e1' σ1' Z ε.
  Proof.
    iIntros (Hexec%pmf_1_eq_dret) "Hcpl".
    replace ε with (nnreal_plus nnreal_zero ε) at 2
      by by apply nnreal_ext => /= ; lra.
    iApply exec_coupl_exec_r.
    iExists _, n. iSplit.
    { iPureIntro. apply ARcoupl_pos_R, ARcoupl_trivial.
      - apply dret_mass.
      - rewrite Hexec; apply dret_mass. }
    iIntros (e2'' σ2'' (_ & _ & H)).
    rewrite Hexec in H. by apply dret_pos in H as [= -> ->].
  Qed.


End exec_coupl.

(** * The weakest precondition  *)
Definition wp_pre`{!spec_updateGS (lang_markov Λ) Σ, !parisWpGS Λ Σ}
    (wp : coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
    coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
  match to_val e1 with
  | Some v => |={E}=> Φ v
  | None => ∀ σ1 e1' σ1' ε,
      state_interp σ1 ∗ spec_interp (e1', σ1') ∗ err_interp ε ={E,∅}=∗
      exec_coupl e1 σ1 e1' σ1' (λ '(e2, σ2) '(e2', σ2') ε2,
        ▷ |={∅,E}=> state_interp σ2 ∗ spec_interp (e2', σ2') ∗ err_interp ε2 ∗ wp E e2 Φ) ε
end%I.

Local Instance wp_pre_contractive `{!spec_updateGS (lang_markov Λ) Σ, !parisWpGS Λ Σ} : Contractive wp_pre.
Proof.
  rewrite /wp_pre /= => n wp wp' Hwp E e1 Φ.
  do 11 f_equiv.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [[[] []] ?]. rewrite /exec_coupl_pre.
  do 15 f_equiv.
  { f_equiv. do 2 case_match. f_contractive. do 4 f_equiv. apply Hwp. }
  { case_match. f_contractive. do 4 f_equiv. apply Hwp. }
  { do 9 f_equiv. f_contractive. do 4 f_equiv. apply Hwp. }
Qed.

(* TODO: get rid of stuckness in notation [iris/bi/weakestpre.v] so that we don't have to do this *)
Local Definition wp_def `{!spec_updateGS (lang_markov Λ) Σ, !parisWpGS Λ Σ} : Wp (iProp Σ) (expr Λ) (val Λ) () :=
  {| wp := λ _ : (), fixpoint (wp_pre); wp_default := () |}.
Local Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp' := wp_aux.(unseal).
Global Arguments wp' {Λ Σ _}.
Global Existing Instance wp'.
Local Lemma wp_unseal `{!spec_updateGS (lang_markov Λ) Σ, !parisWpGS Λ Σ} : wp = (@wp_def Λ Σ _ _).(wp).
Proof. rewrite -wp_aux.(seal_eq) //. Qed.

Section wp.
Context `{!spec_updateGS (lang_markov Λ) Σ, !parisWpGS Λ Σ}.
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
  do 11 f_equiv.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [[[] []] ?]. rewrite /exec_coupl_pre.
  do 15 f_equiv.
  { f_equiv. do 2 case_match. f_contractive_fin. do 4 f_equiv.
    rewrite IH; [done|lia|]. intros ?. eapply dist_S, HΦ. }
  { case_match. f_contractive_fin. do 4 f_equiv.
    rewrite IH; [done|lia|]. intros ?. eapply dist_S, HΦ. }
  { do 9 f_equiv. f_contractive_fin. do 4 f_equiv. rewrite IH; [done|lia|].
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
  do 10 f_equiv.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [[[] []] ?]. rewrite /exec_coupl_pre.
  do 15 f_equiv.
  { f_equiv. do 2 case_match. f_contractive. do 7 f_equiv.  }
  { case_match. f_contractive. do 7 f_equiv. }
  { do 9 f_equiv. f_contractive. do 7 f_equiv. }
Qed.

Lemma wp_value_fupd' s E Φ v : WP of_val v @ s; E {{ Φ }} ⊣⊢ |={E}=> Φ v.
Proof. rewrite wp_unfold /wp_pre to_of_val. auto. Qed.

Lemma wp_strong_mono E1 E2 e Φ Ψ s :
  E1 ⊆ E2 →
  WP e @ s ; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ WP e @ s ; E2 {{ Ψ }}.
Proof.
  iIntros (HE) "H HΦ". iLöb as "IH" forall (e E1 E2 HE Φ Ψ).
  rewrite !wp_unfold /wp_pre /=.
  destruct (to_val e) as [v|] eqn:?.
  { iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _). }
  iIntros (σ1 e1' σ1' ε) "[Hσ [Hs Herr]]".
  iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  iMod ("H" with "[$]") as "H".
  iModIntro.
  iFrame.
  iApply (exec_coupl_mono with "[Hclose HΦ] H").
  iIntros ([e2 σ2] [e2' σ2'] ε') "H".
  iModIntro.
  iMod "H" as "(?&?&?&Hwp)". iFrame.
  iMod "Hclose" as "_". iModIntro.
  iApply ("IH" with "[] Hwp"); auto.
Qed.

Lemma fupd_wp s E e Φ : (|={E}=> WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?.
  { by iMod "H". }
  iIntros (σ1 e1' σ1' ε) "Hi". iMod "H". by iApply "H".
Qed.
Lemma wp_fupd s E e Φ : WP e @ s; E {{ v, |={E}=> Φ v }} ⊢ WP e @ s; E {{ Φ }}.
Proof. iIntros "H". iApply (wp_strong_mono E with "H"); auto. Qed.

Lemma wp_spec_steps P E e Φ s :
  TCEq (to_val e) None →
  spec_update E P -∗ (P -∗ WP e @ s; E {{ Φ }}) -∗ WP e @ s; E {{ Φ }}.
Proof.
  rewrite wp_unfold/wp_pre.
  iIntros (->) "Hupd Hwp". iIntros (σ1 e1' σ1' ε) "(Hσ1 & Hspec & Hε)".
  rewrite spec_update_unseal. 
  iMod ("Hupd" with "Hspec") as "/= (%ρ' & %n & %H &Hspec & HP)".
  destruct ρ'.
  iSpecialize ("Hwp" with "HP [$]").
  iMod "Hwp". iModIntro.
  iApply (exec_coupl_det_r n with "[$]").
  by apply stepN_pexec_det.
Qed.

Lemma wp_atomic s E1 E2 e Φ `{!Atomic StronglyAtomic e} :
  (|={E1,E2}=> WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros "H". rewrite !wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { by iDestruct "H" as ">>> $". }
  iIntros (σ1 e1' σ1' ε) "[Hσ [Hs Herr]]". iMod "H".
  iMod ("H" with "[$]") as "H".
  iModIntro.
  iFrame.
  iDestruct (exec_coupl_strengthen with "H") as "H".
  iApply (exec_coupl_mono with "[] H").
  iIntros ([e2 σ2] [e2' σ2'] ε') "[[% %Hstep] H]".
  iModIntro.
  iMod "H" as "(Hσ & Hρ & Hε & H)".
  (* destruct s *)
  rewrite !wp_unfold /wp_pre.
  destruct (to_val e2) as [v2|] eqn:He2.
  - iDestruct "H" as ">> $". by iFrame.
  - iMod ("H" with "[$]") as "H".
    pose proof (atomic σ e2 σ2 Hstep) as H3. simpl in H3.
    rewrite /is_Some in H3.
    destruct H3.
    simplify_eq.
Qed.

Lemma wp_step_fupd s E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> P) -∗ WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ s; E1 {{ Φ }}.
Proof.
  rewrite !wp_unfold /wp_pre. iIntros (-> ?) "HR H".
  iIntros (σ1 e1' σ1' ε) "[Hσ [Hs Hε]]". iMod "HR".
  iMod ("H" with "[$Hσ $Hs $Hε]") as "H".
  iModIntro.
  iFrame.
  iApply (exec_coupl_mono with "[HR] H").
  iIntros ([e2 σ2] [e2' σ2'] ε') "H".
  iModIntro.
  iMod "H" as "(Hσ & Hρ & Hε & H)".
  iMod "HR".
  iFrame "Hσ Hρ Hε".
  iApply (wp_strong_mono E2 with "H"); [done..|].
  iIntros "!>" (v) "H". by iApply "H".
Qed.

Lemma wp_bind K `{!LanguageCtx K} s E e Φ :
  WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }} ⊢ WP K e @ s; E {{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by iApply fupd_wp. }
  rewrite wp_unfold /wp_pre fill_not_val /=; [|done].
  iIntros (σ1 e1' σ1' ε) "[Hσ [Hs Herr]]".
  iMod ("H" with "[$Hσ $Hs $Herr]") as "H".
  iModIntro.
  - iApply exec_coupl_bind; [done|].
  iApply (exec_coupl_mono with "[] H").
  iIntros ([e2 σ2] [e2' σ2'] ε') "H".
  iModIntro.
  iMod "H" as "(Hσ & Hρ & Hε & H)".
  iModIntro. iFrame "Hσ Hρ Hε". by iApply "IH".
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
  Context `{!spec_updateGS (lang_markov Λ) Σ, !parisWpGS Λ Σ}.
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
    ElimModal (Atomic StronglyAtomic e) p false
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
    ElimAcc (X:=X) (Atomic StronglyAtomic e)
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

  Global Instance elim_modal_spec_update_wp P E e Ψ :
    TCEq (to_val e) None →
    ElimModal True false false (spec_update E P) P (WP e @ E {{ Ψ }}) (WP e @ E {{ Ψ }}).
  Proof.
    iIntros (??) "[HP Hcnt]".
    iApply (wp_spec_steps with "[$] [$]").
  Qed.

  Global Instance elim_modal_spec_updateN_wp P E n e Ψ :
    TCEq (to_val e) None →
    ElimModal True false false (spec_updateN n E P) P (WP e @ E {{ Ψ }}) (WP e @ E {{ Ψ }}).
  Proof.
    iIntros (??) "[HP Hcnt]".
    iDestruct (spec_updateN_implies_spec_update with "HP") as "HP".
    iApply (wp_spec_steps with "[$] [$]").
  Qed.

End proofmode_classes.

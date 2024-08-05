From Coq Require Export Reals Psatz.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export fixpoint big_op.
From iris.prelude Require Import options.

From clutch.bi Require Export weakestpre.
From clutch.prelude Require Import stdpp_ext iris_ext NNRbar.
From clutch.prob Require Export couplings distribution graded_predicate_lifting.
From clutch.common Require Export con_language.

Import uPred.

Local Open Scope NNR_scope.

Class conerisWpGS (Λ : conLanguage) (Σ : gFunctors) := ConerisWpGS {
  conerisWpGS_invGS :: invGS_gen HasNoLc Σ;
  state_interp : state Λ → iProp Σ;
  fork_post: val Λ -> iProp Σ;
  err_interp : nonnegreal → iProp Σ;
}.
Global Opaque conerisWpGS_invGS.
Global Arguments ConerisWpGS {Λ Σ}.


Section glm.
  Context `{conerisWpGS Λ Σ}.
  Implicit Types ε : nonnegreal.

  Definition stutter
    (Z : nonnegreal -> iProp Σ)
    (ε : nonnegreal) : iProp Σ :=
    (⌜(ε>=1)%R⌝ ∨ Z ε)%I.

  Lemma stutter_mono Z1 Z2 ε ε':
    ⌜ (ε<=ε')%R ⌝ -∗
    (Z1 ε -∗ Z2 ε') -∗
    stutter Z1 ε -∗ stutter Z2 ε'.
  Proof.
    iIntros (?) "H [% | H']".
    - iLeft. iPureIntro. lra.
    - iRight. by iApply "H".
  Qed. 

  (* Simple one without adv comp or state steps*)
  Definition glm_pre
    (Z : (expr Λ * state Λ * list (expr Λ)) -> nonnegreal -> iProp Σ) (Φ : partial_cfg Λ * nonnegreal -> iProp Σ) :=
    (λ (x : partial_cfg Λ * nonnegreal),
       let '((e1, σ1), ε) := x in
       (∃ R (ε1 : nonnegreal) (ε2 : (expr Λ * state Λ * list (expr Λ)) -> nonnegreal),
           ⌜reducible e1 σ1⌝ ∗
           ⌜∃ r, ∀ ρ, (ε2 ρ <= r)%R ⌝ ∗
           ⌜(ε1 + SeriesC (λ ρ, (prim_step e1 σ1 ρ) * ε2 ρ) <= ε)%R⌝ ∗
           ⌜pgl (prim_step e1 σ1) R ε1⌝ ∗
           (∀ e2 σ2 efs, ⌜R (e2, σ2, efs)⌝ ={∅}=∗
                        stutter (λ ε', Z (e2, σ2, efs) ε') (ε2 (e2, σ2, efs)))
       ) ∨
     ([∨ list] α ∈ get_active σ1,
        (∃ R (ε1 : nonnegreal) (ε2 : state Λ -> nonnegreal),
          ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗
          ⌜ (ε1 + SeriesC (λ ρ, (state_step σ1 α ρ) * ε2 ρ) <= ε)%R ⌝ ∗
          ⌜pgl (state_step σ1 α) R ε1⌝ ∗
              ∀ σ2, ⌜ R σ2 ⌝ ={∅}=∗ stutter (λ ε', Φ ((e1, σ2), ε')) (ε2 σ2)))
    )%I.

  Canonical Structure NNRO := leibnizO nonnegreal.

  Local Instance exec_state_ub_pre_NonExpansive Z Φ :
    NonExpansive (glm_pre Z Φ).
  Proof.
    rewrite /glm_pre.
    intros n ((?&?)&?) ((?&?)&?) [ [[=] [=]] [=]].
    by simplify_eq.
  Qed.
  
  Local Instance exec_coupl_pre_mono Z : BiMonoPred (glm_pre Z).
  Proof.
    split; [|apply _].
    iIntros (Φ Ψ HNEΦ HNEΨ) "#Hwand".
    rewrite /glm_pre.
    iIntros (((e1 & σ1) & ε)) "Hexec".
    iDestruct "Hexec" as "[H|H]".
    - by iLeft.
    - iRight.
      iInduction (get_active σ1) as [| l] "IH" forall "H".
      { rewrite big_orL_nil //. }
      rewrite !big_orL_cons.
      iDestruct "H" as "[(% & % & % & % & %Hsum & %Hlift & HΦ) | H]".
      + iLeft. iExists R2.
        iExists ε1. iExists _.
        iSplit; [try done|].
        iSplit; [try done|].
        iSplit; [try done|].
        iIntros.
        iApply (stutter_mono with "[]"); first done; last first.
        * by iMod ("HΦ" with "[//]").
        * iIntros.
          by iApply "Hwand".
      + iRight. by iApply "IH".
  Qed.

  
  Definition glm' Z := bi_least_fixpoint (glm_pre Z).
  Definition glm e σ ε Z := glm' Z ((e, σ), ε).

  Lemma glm_unfold (e1 : exprO Λ) (σ1 : stateO Λ) Z (ε : NNRO) :
    glm e1 σ1 ε Z ≡
      ((∃ R (ε1 : nonnegreal) (ε2 : (expr Λ * state Λ * list (expr Λ)) -> nonnegreal),
           ⌜reducible e1 σ1⌝ ∗
           ⌜∃ r, ∀ ρ, (ε2 ρ <= r)%R ⌝ ∗
           ⌜(ε1 + SeriesC (λ ρ, (prim_step e1 σ1 ρ) * ε2 ρ) <= ε)%R⌝ ∗
           ⌜pgl (prim_step e1 σ1) R ε1⌝ ∗
           (∀ e2 σ2 efs, ⌜R (e2, σ2, efs)⌝ ={∅}=∗
                        stutter (λ ε', Z (e2, σ2, efs) ε') (ε2 (e2, σ2, efs)))
       ) ∨
         ([∨ list] α ∈ get_active σ1,
        (∃ R (ε1 : nonnegreal) (ε2 : state Λ -> nonnegreal),
          ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗
          ⌜ (ε1 + SeriesC (λ ρ, (state_step σ1 α ρ) * ε2 ρ) <= ε)%R ⌝ ∗
          ⌜pgl (state_step σ1 α) R ε1⌝ ∗
          ∀ σ2, ⌜ R σ2 ⌝ ={∅}=∗ stutter (λ ε', glm e1 σ2 ε' Z) (ε2 σ2)))
           )
      %I.
  Proof.
    rewrite /glm/glm' least_fixpoint_unfold//.
  Qed.

  Local Definition partial_cfgO := (prodO (exprO Λ) (stateO Λ)).
  
  Lemma glm_mono_grading e σ Z ε ε' :
    ⌜(ε <= ε')%R⌝ -∗
    glm e σ ε Z -∗ glm e σ ε' Z.
  Proof.
    iIntros "Hleq H_ub". iRevert "Hleq".
    rewrite /glm /glm'.
    set (Φ := (λ x, ∀ (ε'' : nonnegreal), ((⌜(x.2 <= ε'' )%R⌝ -∗ (bi_least_fixpoint (glm_pre Z) (x.1, ε'')))))%I : prodO partial_cfgO NNRO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros n ((?&?)&?) ((?&?)&?) [ [[=] [=]] [=]]. by simplify_eq. }
    iPoseProof (least_fixpoint_ind (glm_pre Z) Φ with "[]") as "H"; last first.
    { iApply ("H" with "H_ub"). }
    iIntros "!#" ([[? σ'] ε'']). rewrite /glm_pre.
    iIntros "[(% & % & % & % & % & % & % & H)|H] %ε3 %Hleq' /="; simpl in Hleq'.
    - rewrite least_fixpoint_unfold.
      iLeft.
      iExists _,_,_.
      repeat iSplit; try done.
      iPureIntro; etrans; done.
    - rewrite least_fixpoint_unfold.
      iRight.
      iInduction (get_active σ') as [| l] "IH".
      { rewrite big_orL_nil //. }
      rewrite 2!big_orL_cons.
      iDestruct "H" as "[(%R2 & %ε1 & %ε2 & (%Hleq2 & %Hub & %Hlift & H )) | Ht]".
      + iLeft.
        iExists R2. iExists ε1. iExists ε2.
        iSplit; [auto|].
        iSplit; [ iPureIntro; lra | ].
        iSplit; [ done | ].
        iIntros.
        rewrite /glm_pre.
        iClear "IH".
        iMod ("H" with "[//]").
        iModIntro.
        iApply stutter_mono; [done| |done].
        simpl.
        iIntros "K".
        by iApply "K".
      + iRight. by iApply ("IH" with "Ht"). 
  Qed.
  
  Lemma glm_strong_mono e1 σ1 Z1 Z2 ε ε' :
    ⌜(ε <= ε')%R⌝ -∗
    (∀ e2 σ2 ε'', (⌜∃ σ, (prim_step e1 σ (e2, σ2) > 0)%R⌝ ∗ Z1 (e2, σ2) ε'' -∗ Z2 (e2, σ2) ε'')) -∗
    glm e1 σ1 ε Z1 -∗ glm e1 σ1 ε' Z2.
  Proof.
    iIntros "%Hleq HZ H_ub".
    iApply glm_mono_grading; auto.
    iRevert "HZ".
    rewrite /glm /glm'.
    set (Φ := (λ x,(∀ e2 σ2 ε'', ⌜∃ σ, (prim_step x.1.1 σ (e2, σ2) > 0)%R⌝ ∗ Z1 (e2, σ2) ε'' -∗ Z2 (e2, σ2) ε'') -∗
                  (bi_least_fixpoint (glm_pre Z2) x ))%I : prodO partial_cfgO NNRO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros n ((?&?)&?) ((?&?)&?) [[[=] [=]] [=]]. by simplify_eq. }
    iPoseProof (least_fixpoint_iter (glm_pre Z1) Φ with "[]") as "H"; last first.
    { by iApply ("H" with "H_ub"). }
    iIntros "!#" ([[? σ'] ε'']). rewrite /glm_pre.
    iIntros "[(% & % & % & % & % & % & % & H)|H] HZ /=".
    - rewrite least_fixpoint_unfold.
      iLeft.
      iExists _,_,_.
      do 3 (iSplit; first done).
      iSplit; first (iPureIntro; by apply pgl_pos_R).
      iIntros (???[??]).
      iMod ("H" with "[//]").
      iModIntro.
      iApply (stutter_mono with "[][HZ][$]"); first done.
      iIntros "H".
      iApply "HZ". iFrame.
      iPureIntro. naive_solver.
   - rewrite least_fixpoint_unfold.
      iRight.
      iInduction (get_active σ') as [| l] "IH".
      { rewrite big_orL_nil //. }
      rewrite 2!big_orL_cons.
      iDestruct "H" as "[(%R2 & %ε1 & %ε2 & (% & % & % & H)) | Ht]".
      + iLeft. iExists R2. iExists ε1. iExists ε2.
        iSplit; [auto | ].
        iSplit; [iPureIntro; lra | ].
        iSplit; [done | ].
        iIntros.
        iMod ("H" with "[//]") as "H".
        iModIntro.
        iApply (stutter_mono with "[][HZ]"); [done| |done].
        simpl.
        rewrite /Φ.
        iIntros "H". 
        iApply "H".
        iFrame.
      + iRight. by iApply ("IH" with "Ht").
  Qed.

  Lemma glm_mono Z1 Z2 e1 σ1 ε1 ε2 :
    ⌜(ε1 <= ε2)%R⌝ -∗ (∀ ρ ε, Z1 ρ ε -∗ Z2 ρ ε) -∗ glm e1 σ1 ε1 Z1 -∗ glm e1 σ1 ε2 Z2.
  Proof.
    iIntros "%Hleq HZ". iApply glm_strong_mono; auto.
    iIntros (???) "[_ ?]". by iApply "HZ".
  Qed.

  Lemma glm_mono_pred Z1 Z2 e1 σ1 ε :
    (∀ ρ ε, Z1 ρ ε -∗ Z2 ρ ε) -∗ glm e1 σ1 ε Z1 -∗ glm e1 σ1 ε Z2.
  Proof.
    iIntros "HZ". iApply glm_strong_mono; auto.
    iIntros (???) "[_ ?]". by iApply "HZ".
  Qed.

  Lemma glm_strengthen e1 σ1 Z ε :
    glm e1 σ1 ε Z -∗
    glm e1 σ1 ε (λ '(e2, σ2) ε', ⌜∃ σ, (prim_step e1 σ (e2, σ2) > 0)%R⌝ ∧ Z (e2, σ2) ε').
  Proof.
    iApply glm_strong_mono; [iPureIntro; lra | ].
    iIntros (???) "[[% ?] ?]". iSplit; [|done]. by iExists _.
  Qed.


  Lemma glm_bind K `{!ConLanguageCtx K} e1 σ1 Z ε :
    to_val e1 = None →
    glm e1 σ1 ε (λ '(e2, σ2, efs) ε', Z (K e2, σ2, efs) ε') -∗ glm (K e1) σ1 ε Z.
  Proof.
    iIntros (Hv) "Hub".
    iAssert (⌜to_val e1 = None⌝)%I as "-#H"; [done|].
    iRevert "H".
    rewrite /glm /glm'.
    set (Φ := (λ x, ⌜to_val x.1.1 = None⌝ -∗
                     bi_least_fixpoint (glm_pre Z) ((K x.1.1, x.1.2), x.2))%I
           : prodO partial_cfgO NNRO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros n ((?&?)&?) ((?&?)&?) [[[=] [=]] [=]]. by simplify_eq. }
    iPoseProof (least_fixpoint_iter
                  (glm_pre (λ '(e2, σ2, efs) ε', Z (K e2, σ2, efs) ε')) Φ
                 with "[]") as "H"; last first.
    { iIntros (?). iApply ("H" $! ((_, _), _) with "Hub [//]"). }
    iIntros "!#" ([[? σ'] ε']). rewrite /glm_pre.
    iIntros " [(% & % & % & % & [%r %Hr] & % & % & H)|H] %Hv'".
    - rewrite least_fixpoint_unfold.
      iLeft.
      destruct (partial_inv_fun K) as (Kinv & HKinv).
      assert (forall e e', Kinv e' = Some e -> K e = e') as HKinv1; [intros; by apply HKinv |].
      assert (forall e e', Kinv e = None -> K e' ≠ e) as HKinv2; [intros; by apply HKinv |].
      assert (forall e, Kinv (K e) = Some e) as HKinv3.
      { intro e.
        destruct (Kinv (K e)) eqn:H5.
        - apply HKinv1 in H5. f_equal. by apply fill_inj.
        - eapply (HKinv2 _ e) in H5. done. }
      set (ε3 := (λ '(e,σ,efs), from_option (λ e', ε2 (e',σ, efs)) nnreal_zero (Kinv e))).
      assert (forall e2 σ2 efs, ε3 (K e2, σ2, efs) = ε2 (e2, σ2, efs)) as Haux.
      {
        intros e2 σ2 efs.
        rewrite /ε3 HKinv3 //.
      }
      iExists (λ '(e2, σ2, efs), ∃ e2', e2 = K e2' ∧ R2 (e2', σ2, efs)),_,ε3.
      iSplit; [iPureIntro; by apply reducible_fill|].
      iSplit.
      { iPureIntro. exists r. intros ([e σ]&efs). rewrite /ε3.
        destruct (Kinv e); simpl; try real_solver.
        etrans; [ | eapply (Hr (e, σ, efs)); eauto]. apply cond_nonneg.
      }
      iSplit; [|iSplit].
      2: { iPureIntro.
           rewrite <- Rplus_0_r.
           rewrite fill_dmap //=.
           eapply (pgl_dbind _ _ R2).
           - eapply pgl_nonneg_grad; eauto.
           - lra.
           - intros [[]] ? =>/=.
             apply pgl_dret.
             eauto.
           - auto.
      }
      + iPureIntro; simpl.
        etrans; [ | exact].
        apply Rplus_le_compat_l.
        transitivity (SeriesC (λ '(e,σ,efs), (prim_step (K o) σ' (K e, σ, efs) * ε3 (K e, σ, efs))%R)).
        * etrans; [ | eapply (SeriesC_le_inj _ (λ '(e,σ, efs), (Kinv e ≫= (λ e', Some (e',σ, efs)))))].
          ** apply SeriesC_le.
             *** intros ([e σ] & efs); simpl; split.
                 **** apply Rmult_le_pos; auto.
                      apply cond_nonneg.
                 **** destruct (Kinv e) eqn:He; simpl.
                      ***** rewrite (HKinv1 _ _ He).
                      rewrite He /from_option //.
                      ***** destruct (decide (prim_step (K o) σ' (e, σ, efs) > 0)%R) as [Hgt | Hngt].
          -- epose proof (fill_step_inv _ _ _ _ _ _ Hgt) as (e2' & (?&?)).
             by destruct (HKinv2 e e2' He).
          --  apply Rnot_gt_le in Hngt.
              assert (prim_step (K o) σ' (e, σ, efs) = 0%R); [by apply Rle_antisym | ].
              lra.
              *** apply (ex_seriesC_le _ (λ '(e, σ, efs), (prim_step (K o) σ' (e, σ, efs) * ε3 (e, σ, efs))%R)).
                  **** intros ([e σ] & efs); simpl; split.
                       ***** destruct (Kinv e); simpl; try lra.
                       apply Rmult_le_pos; auto.
                       destruct (Kinv _); simpl; try lra.
                       apply cond_nonneg.
                       ***** destruct (Kinv e) eqn:He; simpl; try real_solver.
                       rewrite HKinv3 /= (HKinv1 _ _ He) //.
                  **** apply (ex_seriesC_le _ (λ ρ, ((prim_step (K o) σ' ρ ) * r)%R)); [ | apply ex_seriesC_scal_r; auto].
                       intros ([e σ]&efs); split.
                       ***** apply Rmult_le_pos; auto.
                       apply cond_nonneg.
                       ***** rewrite /ε3. destruct (Kinv e); simpl; try real_solver.
                       apply Rmult_le_compat_l; auto.
                       etrans; [ | eapply (Hr (e, σ, efs)); eauto]. apply cond_nonneg.
              ** intros [[]].
                 apply Rmult_le_pos; auto.
                 apply cond_nonneg.
              ** intros [[e3 ]] [[e4]] [[e5]]? ?.
                 destruct (Kinv e3) eqn:He3; destruct (Kinv e4) eqn:He4; simpl in *; simplify_eq.
                 f_equal; auto.
                 rewrite -(HKinv1 _ _ He3).
                 by rewrite -(HKinv1 _ _ He4).
              ** apply (ex_seriesC_le _ (λ '(e, σ, efs), ((prim_step (K o) σ' (K e, σ, efs)) * r)%R)).
                 *** intros ([]&?); split.
                     **** apply Rmult_le_pos; auto.
                          apply cond_nonneg.
                     **** rewrite /ε3 HKinv3 /=. real_solver.
                 *** apply (ex_seriesC_ext (λ ρ, ((prim_step o σ' ρ) * r)%R)); auto.
                     **** intros [[]]. apply Rmult_eq_compat_r. by apply fill_step_prob.
                     **** by apply ex_seriesC_scal_r.
        * right. apply SeriesC_ext.
          intros ([]&?).
          rewrite Haux.
          f_equal; auto.
          symmetry; by apply fill_step_prob.
      + iIntros (???[?[->?]]).
        iMod ("H" with "[//]").
        by rewrite Haux.
        Unshelve. auto.
    - rewrite least_fixpoint_unfold; simpl.
      iRight.
      (* from above (combine?)*)
      destruct (partial_inv_fun K) as (Kinv & HKinv).
      assert (forall e e', Kinv e' = Some e -> K e = e') as HKinv1; [intros; by apply HKinv |].
      assert (forall e e', Kinv e = None -> K e' ≠ e) as HKinv2; [intros; by apply HKinv |].
      assert (forall e, Kinv (K e) = Some e) as HKinv3.
      { intro e.
        destruct (Kinv (K e)) eqn:H3.
        - apply HKinv1 in H3. f_equal. by apply fill_inj.
        - eapply (HKinv2 _ e) in H3. done. }
      iInduction (get_active σ') as [| l ls] "IH".
      { rewrite big_orL_nil //. }
      rewrite 2!big_orL_cons.
      iDestruct "H" as "[(%R2 & %ε1 & %ε2 & (%Hub & %Hleq & %Hlift & H)) | Ht]".
      + iLeft.
        iExists _, _, _.
        repeat iSplit; try done.
        iIntros.
        iMod ("H" with "[//]") as "H".
        rewrite /Φ.
        iApply stutter_mono; [done| |done].
        simpl. iIntros "H". by iApply "H".
      + iRight. by iApply ("IH" with "Ht").
  Qed.

  Lemma glm_prim_step e1 σ1 Z ε :
    (∃ R ε1 ε2, ⌜reducible e1 σ1⌝ ∗ ⌜ (ε1 + ε2 <= ε)%R ⌝ ∗ ⌜pgl (prim_step e1 σ1) R ε1⌝ ∗
          ∀ e2 σ2 efs, ⌜R (e2, σ2, efs)⌝ ={∅}=∗ Z (e2, σ2, efs) ε2)
    ⊢ glm e1 σ1 ε Z.
  Proof.
    iIntros "(%R&%ε1&%ε2&%&%&%&H)".
    rewrite glm_unfold.
    iLeft.
    iExists R, ε1, (λ _, ε2).
    repeat iSplit; try done.
    - iPureIntro. naive_solver.
    - iPureIntro. rewrite SeriesC_scal_r. rewrite prim_step_mass; [lra|done].
    - iIntros (????). iRight.
      iApply "H". done.
  Qed.
  

  Lemma glm_adv_comp e1 σ1 Z (ε : nonnegreal) :
      (∃ R (ε1 : nonnegreal) (ε2 : _ -> nonnegreal),
          ⌜reducible e1 σ1⌝ ∗
          ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗
          ⌜ (ε1 + SeriesC (λ ρ, (prim_step e1 σ1 ρ) * ε2(ρ)) <= ε)%R ⌝ ∗ ⌜pgl (prim_step e1 σ1) R ε1⌝ ∗
            ∀ e2 σ2 efs, ⌜ R (e2, σ2, efs) ⌝ ={∅}=∗ stutter (λ ε', Z (e2, σ2, efs) ε') (ε2 (e2, σ2, efs)))
    ⊢ glm e1 σ1 ε Z.
  Proof.
    iIntros "(% & % & % & % & % & % & % & H)".
    rewrite {1}glm_unfold.
    iLeft.
    iExists _,_,_.
    by repeat iSplit.
  Qed.

  Lemma glm_state_step α e1 σ1 Z (ε ε' : nonnegreal) :
    α ∈ get_active σ1 →
    (∃ R, ⌜pgl (state_step σ1 α) R ε⌝ ∗
          ∀ σ2 , ⌜R σ2 ⌝ ={∅}=∗ glm e1 σ2 ε' Z)
    ⊢ glm e1 σ1 (ε + ε') Z.
  Proof.
    iIntros (?) "(%&%&H)".
    rewrite glm_unfold. iRight.
    iApply big_orL_elem_of; first done.
    iExists R2, ε, (λ _, ε').
    repeat iSplit; try done.
    - iPureIntro; eexists _; done.
    - iPureIntro. rewrite SeriesC_scal_r. rewrite state_step_mass; [simpl;lra|done]. 
    - iIntros. iRight. by iApply "H".
  Qed.



  (* for state steps that consume zero error *)
  Lemma glm_state_adv_comp' α e1 σ1 Z (ε : nonnegreal) :
    (α ∈ get_active σ1 ->
     (∃ R (ε2 : _ -> nonnegreal),
        ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗
        ⌜ (SeriesC (λ ρ, (state_step σ1 α ρ) * ε2 ρ) <= ε)%R ⌝ ∗
        ⌜pgl (state_step σ1 α) R nnreal_zero⌝ ∗
        ∀ σ2, ⌜ R σ2 ⌝ ={∅}=∗ stutter (fun ε' => glm e1 σ2 ε' Z) (ε2 σ2))
      ⊢ glm e1 σ1 ε Z)%I.
  Proof.
    iIntros (?) "(% & % & % & %Hε & % & H)".
    rewrite {1}glm_unfold.
    iRight.
    iApply big_orL_elem_of; eauto.
    iExists _,nnreal_zero,_.
    iSplit; [auto|].
    iSplit.
    { iPureIntro. by rewrite /= Rplus_0_l. }
    iSplit; [done|done].
  Qed.
  

  Lemma glm_strong_ind (Ψ : expr Λ → state Λ → nonnegreal → iProp Σ) Z :
    (∀ n e σ ε, Proper (dist n) (Ψ e σ ε)) →
    ⊢ (□ (∀ e σ ε, glm_pre Z (λ '((e, σ), ε), Ψ e σ ε ∧ glm e σ ε Z)%I ((e, σ), ε) -∗ Ψ e σ ε) →
       ∀ e σ ε, glm e σ ε Z -∗ Ψ e σ ε)%I.
  Proof.
    iIntros (HΨ). iIntros "#IH" (e σ ε) "H".
    set (Ψ' := (λ '((e, σ), ε), Ψ e σ ε):
           (prodO (prodO (exprO Λ) (stateO Λ)) NNRO) → iProp Σ).
    assert (NonExpansive Ψ').
    { intros n [[e1 σ1]?] [[e2 σ2]?]
        [[?%leibniz_equiv ?%leibniz_equiv]?%leibniz_equiv].
      simplify_eq/=. f_equiv. }
    rewrite /glm/glm'.
    iApply (least_fixpoint_ind _ Ψ' with "[] H").
    iModIntro. iIntros ([[??]?]) "H". by iApply "IH".
  Qed. 
    
End glm.

(** * The weakest precondition *)

Definition pgl_wp_pre `{!conerisWpGS Λ Σ}
    (wp : coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
  coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ :=
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


Local Instance wp_pre_contractive `{!conerisWpGS Λ Σ} : Contractive (pgl_wp_pre).
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
Local Definition pgl_wp_def `{!conerisWpGS Λ Σ} : Wp (iProp Σ) (expr Λ) (val Λ) () :=
  {| wp := λ _ : (), fixpoint (pgl_wp_pre); wp_default := () |}.
Local Definition pgl_wp_aux : seal (@pgl_wp_def). Proof. by eexists. Qed.
Definition pgl_wp' := pgl_wp_aux.(unseal).
Global Arguments pgl_wp' {Λ Σ _}.
Global Existing Instance pgl_wp'.
Local Lemma pgl_wp_unseal `{!conerisWpGS Λ Σ} : wp = (@pgl_wp_def Λ Σ _).(wp).
Proof. rewrite -pgl_wp_aux.(seal_eq) //. Qed.

Section pgl_wp.
Context `{!conerisWpGS Λ Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types ρ : partial_cfg Λ.
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
  destruct (to_val e) as [v|] eqn:?.
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
  + iMod ("Hwp" $! _ _ with "[Hσ Hε]") as "Hwp"; [iFrame|].
    specialize (atomic _ _ _ _ Hstep) as Hatomic. (* key step *)
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
  Context `{!conerisWpGS Λ Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

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

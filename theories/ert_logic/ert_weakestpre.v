From Coq Require Export Reals Psatz.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export fixpoint big_op.
From iris.prelude Require Import options.

From clutch.bi Require Export weakestpre.
From clutch.prelude Require Import stdpp_ext NNRbar.
From clutch.prob Require Export couplings distribution union_bounds.
From clutch.common Require Export language.

Import uPred.

Local Open Scope NNR_scope.

(** [irisGS] specifies the interface for the resource algebras implementing the
    [state] and [cfg] of a [language] [Λ]. For the purposes of defining the
    weakest precondition, we only need [irisGS] to give meaning to invariants,
    and provide predicates describing valid states via [state_interp].
    Here [err_interp] is a resource tracking an upper bound on the probability of
    error (i.e. terminating in a state that does not satisfy the postcondition)
 *)
Class irisGS (Λ : language) (Σ : gFunctors) := IrisG {
  iris_invGS :: invGS_gen HasNoLc Σ;
  state_interp : state Λ → iProp Σ;
  err_interp : nonnegreal → iProp Σ;
}.
Global Opaque iris_invGS.
Global Arguments IrisG {Λ Σ}.

(* TODO: upstream? *)
Lemma least_fixpoint_ne_outer {PROP : bi} {A : ofe}
    (F1 : (A → PROP) → (A → PROP)) (F2 : (A → PROP) → (A → PROP)) n :
  (∀ Φ x, F1 Φ x ≡{n}≡ F2 Φ x) → ∀ x1 x2,
  x1 ≡{n}≡ x2 → bi_least_fixpoint F1 x1 ≡{n}≡ bi_least_fixpoint F2 x2.
Proof.
  intros HF x1 x2 Hx. rewrite /bi_least_fixpoint /=.
  do 3 f_equiv; last solve_proper. repeat f_equiv. apply HF.
Qed.



(** * The union bound modality [exec_ub]  *)
Section exec_ub.
  Context `{!irisGS Λ Σ}.

  Implicit Types ε : nonnegreal.
  Implicit Types Z : cfg Λ → nonnegreal → iProp Σ.



  Definition exec_stutter (P : nonnegreal -> iProp Σ) ε : iProp Σ :=
    (∃ R (ε1 ε2 : nonnegreal),
                  ⌜(ε1 + ε2 <= ε)%R ⌝ ∗
                  ⌜total_ub_lift (dret tt) R ε1 ⌝ ∗
                  (⌜ R tt ⌝ -∗ P ε2))%I.


  (* Stutter can pretty much only be used in one of two ways becasue of the (dret tt) *)
  (* The first allows us to obtain an exec_stutter for free if we can prove Φ *)
  Lemma exec_stutter_free P ε : P ε -∗ exec_stutter P ε.
  Proof.
    iIntros "?".
    iExists (fun _ => True), nnreal_zero, ε.
    iSplitR; [iPureIntro; simpl; lra| ].
    iSplitR.
    { iPureIntro.
      rewrite /total_ub_lift /=.
      rewrite prob_dret_true; [lra|case_bool_decide;done].
    }
    iFrame; eauto.
  Qed.

  (* The second allows us to exclude cases with too much credit *)
  Lemma exec_stutter_spend P ε : ⌜(1 <= ε)%R⌝ -∗ exec_stutter P ε.
  Proof.
    iIntros "%".
    assert (Hdiff : (0 <= ε - 1)%R); [lra|].
    iExists (fun _ => False), nnreal_one, (mknonnegreal (ε - 1) Hdiff).
    iSplitR; [iPureIntro; simpl; lra|].
    iSplitR.
    { iPureIntro.
      rewrite /total_ub_lift /=.
      intros.
      eapply Rle_trans; [|eapply prob_ge_0].
      lra.
    }
    iIntros "?"; eauto.
  Qed.


  Definition exec_stutter_1 (P : nonnegreal -> iProp Σ) ε : iProp Σ := (⌜(1 <= ε)%R ⌝ ∨ (P ε))%I.
  Lemma exec_stutter_compat P ε : ⊢ (exec_stutter_1 P ε → exec_stutter P ε).
  Proof.
    rewrite /exec_stutter_1.
    iIntros "[%H|H]".
    - iApply exec_stutter_spend; done.
    - iApply exec_stutter_free; done.
  Qed.

  Lemma exec_stutter_compat_1 P ε :
    ⊢ (∀ ε ε' : nonnegreal, ⌜(ε <= ε')%R⌝ -∗ (P ε -∗ P ε'))
        -∗ (exec_stutter P ε -∗ exec_stutter_1 P ε).
  Proof.
    rewrite /exec_stutter /exec_stutter_1.
    iIntros "Hmono [% [% [% (% & % & H)]]]".
    destruct (Rle_decision 1%R (nonneg ε)%R) as [Hdec|Hdec].
    { iLeft; iPureIntro. lra. }
    iRight.
    rewrite /total_ub_lift in H0.
    remember (λ a : (), @bool_decide (R2 a) (make_decision (R2 a))) as X.
    destruct (X ()) as [|] eqn:HX; simpl in *.
    - iApply ("Hmono" $!  ε2).
      { iPureIntro; simpl.
        eapply Rle_trans; [|eapply H].
        destruct ε2; destruct ε1; simpl; lra. }
      iApply "H".
      iPureIntro.
      rewrite HeqX in HX.
      apply bool_decide_eq_true_1 in HX.
      done.
    - exfalso.
      rewrite /not in Hdec; apply Hdec.
      rewrite /prob /dret SeriesC_finite_foldr /enum /= in H0.
      rewrite Rplus_0_r /pmf /dret_pmf HX /= in H0.
      assert (H' : (1 <= nonneg ε1)%R); first lra.
      eapply Rle_trans; last eapply H.
      eapply Rle_trans; first eapply H'.
      destruct ε1; destruct ε2; simpl; lra.
  Qed.
  
  Lemma exec_stutter_mono_grading P ε ε' :
    ⌜(ε <= ε')%R⌝ -∗
    exec_stutter P ε -∗ exec_stutter P ε'.
  Proof.
    iIntros "% [%R [%ε1 [%ε2 (%Hsum & %Hlift & HΦ)]]]".
    iExists R, ε1, ε2.
    iSplitR; [ iPureIntro; lra |].
    iSplitR; [ done |].
    iIntros; iApply "HΦ"; done.
  Qed.

  Lemma exec_stutter_mono_pred P Q ε :
    (∀ ε', P ε' -∗ Q ε') -∗
    exec_stutter P ε -∗ exec_stutter Q ε.
  Proof.
    iIntros "Hwand [%R [%ε1 [%ε2 (%Hsum & %Hlift & HΨ)]]]".
    iExists R, ε1, ε2.
    iSplitR; [iPureIntro; simpl; lra|].
    iSplitR; [eauto|].
    iIntros.
    iApply "Hwand".
    iApply "HΨ".
    iPureIntro.
    done.
  Qed.


  Definition exec_ub_pre (Z : cfg Λ → nonnegreal → iProp Σ) (Φ : cfg Λ * nonnegreal → iProp Σ) :=
    (λ (x : cfg Λ * nonnegreal),
      let '((e1, σ1), ε) := x in
      (* [prim_step] with adv composition *)
      (∃ R (ε1 : nonnegreal) (ε2 : cfg Λ -> nonnegreal),
          ⌜reducible (e1, σ1)⌝ ∗
          ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗
          ⌜ (ε1 + SeriesC (λ ρ, (prim_step e1 σ1 ρ) * ε2(ρ)) <= ε)%R ⌝ ∗
          ⌜ub_lift (prim_step e1 σ1) R ε1⌝ ∗
            ∀ e2 σ2, ⌜ R (e2, σ2) ⌝ ={∅}=∗ exec_stutter (fun ε' => Z (e2, σ2) ε') (ε2 (e2, σ2))) ∨
      (* [state_step] with adv composition*)
      ([∨ list] α ∈ get_active σ1,
        (∃ R (ε1 : nonnegreal) (ε2 : cfg Λ -> nonnegreal),
          ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗
          ⌜ (ε1 + SeriesC (λ σ2, (state_step σ1 α σ2) * ε2 (e1, σ2)) <= ε)%R ⌝ ∗
          ⌜ub_lift (state_step σ1 α) R ε1⌝ ∗
              ∀ σ2, ⌜ R σ2 ⌝ ={∅}=∗ exec_stutter (fun ε' => Φ ((e1, σ2), ε')) (ε2 (e1, σ2)))))%I.


  (* TODO: Define this globally, it appears in error credits too *)
  Canonical Structure NNRO := leibnizO nonnegreal.

  Local Instance exec_state_ub_pre_NonExpansive Z Φ :
    NonExpansive (exec_ub_pre Z Φ).
  Proof.
    rewrite /exec_ub_pre.
    intros n ((?&?)&?) ((?&?)&?) [ [[=] [=]] [=]].
    by simplify_eq.
  Qed.

  Local Instance exec_coupl_pre_mono Z : BiMonoPred (exec_ub_pre Z).
  Proof.
    split; [|apply _].
    iIntros (Φ Ψ HNEΦ HNEΨ) "#Hwand".
    rewrite /exec_ub_pre.
    iIntros (((e1 & σ1) & ε)) "Hexec".
    iDestruct "Hexec" as "[H | H]".
    - by iLeft.
    - iRight.
      iInduction (get_active σ1) as [| l] "IH" forall "H".
      { rewrite big_orL_nil //. }
      rewrite !big_orL_cons.
      iDestruct "H" as "[(% & % & % & % & %Hsum & Hlift & HΦ) | H]".
      + iLeft. iExists R2.
        iExists ε1. iExists _.
        iSplit; [try done|].
        iSplit; [try done|].
        iSplit; [try done|].
        iIntros.
        iApply (exec_stutter_mono_pred with "[]").
        { iIntros (?) "H".  iApply "Hwand". iApply "H". }
        by iApply "HΦ".
      + iRight. by iApply "IH".
    Qed.

  Definition exec_ub' Z := bi_least_fixpoint (exec_ub_pre Z).
  Definition exec_ub e σ ε Z := exec_ub' Z ((e, σ), ε).

  Lemma exec_ub_unfold (e1 : exprO Λ) (σ1 : stateO Λ) Z (ε : NNRO) :
    exec_ub e1 σ1 ε Z ≡
      ((∃ R (ε1 : nonnegreal) (ε2 : cfg Λ -> nonnegreal),
          ⌜reducible (e1, σ1)⌝ ∗
          ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗
          ⌜ (ε1 + SeriesC (λ ρ, (prim_step e1 σ1 ρ) * ε2(ρ)) <= ε)%R ⌝ ∗
          ⌜ub_lift (prim_step e1 σ1) R ε1⌝ ∗
            ∀ e2 σ2, ⌜ R (e2, σ2) ⌝ ={∅}=∗ exec_stutter (fun ε' => Z (e2, σ2) ε') (ε2 (e2, σ2))) ∨
      ([∨ list] α ∈ get_active σ1,
        (∃ R (ε1 : nonnegreal) (ε2 : cfg Λ -> nonnegreal),
          ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗
          ⌜ (ε1 + SeriesC (λ ρ, (state_step σ1 α ρ) * ε2 (e1, ρ)) <= ε)%R ⌝ ∗
          ⌜ub_lift (state_step σ1 α) R ε1⌝ ∗
              ∀ σ2, ⌜ R σ2 ⌝ ={∅}=∗ exec_stutter (fun ε' => exec_ub e1 σ2 ε' Z) (ε2 (e1, σ2)))))%I.
  Proof. rewrite /exec_ub/exec_ub' least_fixpoint_unfold //. Qed.

  Local Definition cfgO := (prodO (exprO Λ) (stateO Λ)).
  
  Lemma exec_ub_mono_grading e σ Z ε ε' :
    ⌜(ε <= ε')%R⌝ -∗
    exec_ub e σ ε Z -∗ exec_ub e σ ε' Z.
  Proof.
    iIntros "Hleq H_ub". iRevert "Hleq".
    rewrite /exec_ub /exec_ub'.
    set (Φ := (λ x, ∀ (ε'' : nonnegreal), ((⌜(x.2 <= ε'' )%R⌝ -∗ (bi_least_fixpoint (exec_ub_pre Z) (x.1, ε'')))))%I : prodO cfgO NNRO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros n ((?&?)&?) ((?&?)&?) [ [[=] [=]] [=]]. by simplify_eq. }
    iPoseProof (least_fixpoint_ind (exec_ub_pre Z) Φ with "[]") as "H"; last first.
    { iApply ("H" with "H_ub"). }
    iIntros "!#" ([[? σ'] ε'']). rewrite /exec_ub_pre.
    iIntros "[ (% & % & % & % & % & % & % & H) | H] %ε3 %Hleq' /="; simpl in Hleq'.
    - rewrite least_fixpoint_unfold.
      iLeft. iExists _,_,_.
      iSplit; [|iSplit; [| iSplit; [| iSplit]]]; try done.
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
        rewrite /exec_ub_pre.
        iClear "IH".
        iMod ("H" with "[//]").
        iModIntro.
        iApply (exec_stutter_mono_pred); [|eauto].
        iIntros (?) "[_ ?]".
        iFrame.
      + iRight. by iApply ("IH" with "Ht").
  Qed.

  Lemma exec_ub_strong_mono e1 σ1 Z1 Z2 ε ε' :
    ⌜(ε <= ε')%R⌝ -∗
    (∀ e2 σ2 ε'', (⌜∃ σ, (prim_step e1 σ (e2, σ2) > 0)%R⌝ ∗ Z1 (e2, σ2) ε'' -∗ Z2 (e2, σ2) ε'')) -∗
    exec_ub e1 σ1 ε Z1 -∗ exec_ub e1 σ1 ε' Z2.
  Proof.
    iIntros "%Hleq HZ H_ub".
    iApply exec_ub_mono_grading; auto.
    iRevert "HZ".
    rewrite /exec_ub /exec_ub'.
    set (Φ := (λ x,(∀ e2 σ2 ε'', ⌜∃ σ, (prim_step x.1.1 σ (e2, σ2) > 0)%R⌝ ∗ Z1 (e2, σ2) ε'' -∗ Z2 (e2, σ2) ε'') -∗
                  (bi_least_fixpoint (exec_ub_pre Z2) x ))%I : prodO cfgO NNRO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros n ((?&?)&?) ((?&?)&?) [[[=] [=]] [=]]. by simplify_eq. }
    iPoseProof (least_fixpoint_iter (exec_ub_pre Z1) Φ with "[]") as "H"; last first.
    { by iApply ("H" with "H_ub"). }
    iIntros "!#" ([[? σ'] ε'']). rewrite /exec_ub_pre.
    iIntros "[ (% & % & % & % & % & % & % & H) | H] HZ /=".
    - rewrite least_fixpoint_unfold.
      iLeft.
      iExists _,_,_.
      iSplit; [done|].
      iSplit; [done|].
      iSplit; [done|].
      iSplit.
      { iPureIntro.
        by apply ub_lift_pos_R. }
      iIntros (? ? (?&?)). iMod ("H" with "[//]").
      iModIntro.
      iApply (exec_stutter_mono_pred with "[HZ]"); [|eauto].
      simpl.
      iIntros (?) "?".
      iApply "HZ". eauto.
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
        iApply (exec_stutter_mono_pred with "[HZ]"); [|eauto].
        iIntros (?) "H".
        rewrite /Φ.
        iApply "H".
        iFrame.
      + iRight. by iApply ("IH" with "Ht").
  Qed.

  Lemma exec_ub_mono Z1 Z2 e1 σ1 ε1 ε2 :
    ⌜(ε1 <= ε2)%R⌝ -∗ (∀ ρ ε, Z1 ρ ε -∗ Z2 ρ ε) -∗ exec_ub e1 σ1 ε1 Z1 -∗ exec_ub e1 σ1 ε2 Z2.
  Proof.
    iIntros "%Hleq HZ". iApply exec_ub_strong_mono; auto.
    iIntros (???) "[_ ?]". by iApply "HZ".
  Qed.

  Lemma exec_ub_mono_pred Z1 Z2 e1 σ1 ε :
    (∀ ρ ε, Z1 ρ ε -∗ Z2 ρ ε) -∗ exec_ub e1 σ1 ε Z1 -∗ exec_ub e1 σ1 ε Z2.
  Proof.
    iIntros "HZ". iApply exec_ub_strong_mono; auto.
    iIntros (???) "[_ ?]". by iApply "HZ".
  Qed.

  Lemma exec_ub_strengthen e1 σ1 Z ε :
    exec_ub e1 σ1 ε Z -∗
    exec_ub e1 σ1 ε (λ '(e2, σ2) ε', ⌜∃ σ, (prim_step e1 σ (e2, σ2) > 0)%R⌝ ∧ Z (e2, σ2) ε').
  Proof.
    iApply exec_ub_strong_mono; [iPureIntro; lra | ].
    iIntros (???) "[[% ?] ?]". iSplit; [|done]. by iExists _.
  Qed.



  Lemma exec_ub_bind K `{!LanguageCtx K} e1 σ1 Z ε :
    to_val e1 = None →
    exec_ub e1 σ1 ε (λ '(e2, σ2) ε', Z (K e2, σ2) ε') -∗ exec_ub (K e1) σ1 ε Z.
  Proof.
    iIntros (Hv) "Hub".
    iAssert (⌜to_val e1 = None⌝)%I as "-#H"; [done|].
    iRevert "H".
    rewrite /exec_ub /exec_ub'.
    set (Φ := (λ x, ⌜to_val x.1.1 = None⌝ -∗
                     bi_least_fixpoint (exec_ub_pre Z) ((K x.1.1, x.1.2), x.2))%I
           : prodO cfgO NNRO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros n ((?&?)&?) ((?&?)&?) [[[=] [=]] [=]]. by simplify_eq. }
    iPoseProof (least_fixpoint_iter
                  (exec_ub_pre (λ '(e2, σ2) ε', Z (K e2, σ2) ε')) Φ
                 with "[]") as "H"; last first.
    { iIntros (?). iApply ("H" $! ((_, _), _) with "Hub [//]"). }
    iIntros "!#" ([[? σ'] ε']). rewrite /exec_ub_pre.
    iIntros " [ (% & % & % & % & (%r & %Hr) & % & % & H) | H ] %Hv'".
    - rewrite least_fixpoint_unfold.
      iLeft. simpl.
      destruct (partial_inv_fun K) as (Kinv & HKinv).
      assert (forall e e', Kinv e' = Some e -> K e = e') as HKinv1; [intros; by apply HKinv |].
      assert (forall e e', Kinv e = None -> K e' ≠ e) as HKinv2; [intros; by apply HKinv |].
      assert (forall e, Kinv (K e) = Some e) as HKinv3.
      { intro e.
        destruct (Kinv (K e)) eqn:H3.
        - apply HKinv1 in H3. f_equal. by apply fill_inj.
        - eapply (HKinv2 _ e) in H3. done. }
      set (ε3 := (λ '(e,σ), from_option (λ e', ε2 (e',σ)) nnreal_zero (Kinv e))).
      assert (forall e2 σ2, ε3 (K e2, σ2) = ε2 (e2, σ2)) as Haux.
      {
        intros e2 σ2.
        rewrite /ε3 HKinv3 //.
      }
      iExists (λ '(e2, σ2), ∃ e2', e2 = K e2' ∧ R2 (e2', σ2)),_,ε3.
      iSplit; [iPureIntro; by apply reducible_fill|].
      iSplit.
      {
        iPureIntro. exists r. intros (e&σ). rewrite /ε3.
        destruct (Kinv e); simpl; try real_solver.
        etrans; [ | eapply (Hr (e, σ)); eauto]. apply cond_nonneg.
      }
      iSplit; [ | iSplit].
      2:{ iPureIntro.
        rewrite <- Rplus_0_r.
        rewrite fill_dmap //=.
        eapply (ub_lift_dbind _ _ R2).
        - eapply ub_nonneg_grad; eauto.
        - lra.
        - intros [] ? =>/=.
          apply ub_lift_dret.
          eauto.
        - auto.
       }
      + iPureIntro.
        etrans; [ | apply H1].
        apply Rplus_le_compat_l.
        transitivity (SeriesC (λ '(e,σ), (prim_step (K o) σ' (K e, σ) * ε3 (K e, σ))%R)).
        * etrans; [ | eapply (SeriesC_le_inj _ (λ '(e,σ), (Kinv e ≫= (λ e', Some (e',σ)))))].
          ** apply SeriesC_le.
             *** intros (e & σ); simpl; split.
                 **** apply Rmult_le_pos; auto.
                      apply cond_nonneg.
                 **** destruct (Kinv e) eqn:He; simpl.
                      ***** rewrite (HKinv1 _ _ He).
                            rewrite He /from_option //.
                      ***** destruct (decide (prim_step (K o) σ' (e, σ) > 0)%R) as [Hgt | Hngt].
                            -- epose proof (fill_step_inv _ _ _ _ _ Hgt) as (e2' & (H3&?)).
                               by destruct (HKinv2 e e2' He).
                            --  apply Rnot_gt_le in Hngt.
                                assert (prim_step (K o) σ' (e, σ) = 0); [by apply Rle_antisym | ].
                                lra.
            *** apply (ex_seriesC_le _ (λ '(e, σ), (prim_step (K o) σ' (e, σ) * ε3 (e, σ))%R)).
                **** intros (e & σ); simpl; split.
                     ***** destruct (Kinv e); simpl; try lra.
                           apply Rmult_le_pos; auto.
                           destruct (Kinv _); simpl; try lra.
                           apply cond_nonneg.
                     ***** destruct (Kinv e) eqn:He; simpl; try real_solver.
                           rewrite HKinv3 /= (HKinv1 _ _ He) //.
                **** apply (ex_seriesC_le _ (λ ρ, ((prim_step (K o) σ' ρ ) * r)%R)); [ | apply ex_seriesC_scal_r; auto].
                     intros (e&σ); split.
                     ***** apply Rmult_le_pos; auto.
                           apply cond_nonneg.
                     ***** rewrite /ε3. destruct (Kinv e); simpl; try real_solver.
                           apply Rmult_le_compat_l; auto.
                           etrans; [ | eapply (Hr (e, σ)); eauto]. apply cond_nonneg.
         ** intros [].
            apply Rmult_le_pos; auto.
            apply cond_nonneg.
         ** intros (e3&σ3) (e4&σ4) (e5&σ5) ? ?.
            destruct (Kinv e3) eqn:He3; destruct (Kinv e4) eqn:He4; simpl in *; simplify_eq.
            f_equal; auto.
            rewrite -(HKinv1 _ _ He3).
            by rewrite -(HKinv1 _ _ He4).
         ** apply (ex_seriesC_le _ (λ '(e, σ), ((prim_step (K o) σ' (K e, σ)) * r)%R)).
            *** intros (e&σ); split.
                **** apply Rmult_le_pos; auto.
                     apply cond_nonneg.
                **** rewrite /ε3 HKinv3 /=. real_solver.
            *** apply (ex_seriesC_ext (λ ρ, ((prim_step o σ' ρ) * r)%R)); auto.
                **** intros []. apply Rmult_eq_compat_r. by apply fill_step_prob.
                **** by apply ex_seriesC_scal_r.
        * right. apply SeriesC_ext.
          intros (e&σ).
          rewrite Haux.
          f_equal; auto.
          symmetry; by apply fill_step_prob.
      + iIntros (? ? (? & -> & ?)).
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
      + set (ε3 := (λ '(e,σ), from_option (λ e', ε2 (e',σ)) nnreal_zero (Kinv e))).
        assert (forall e2 σ2, ε3 (K e2, σ2) = ε2 (e2, σ2)) as Haux.
        { intros e2 σ2. rewrite /ε3 HKinv3 //. }
        iLeft.
        iExists R2,_,ε3.
        iSplit.
        { iPureIntro.
          destruct Hub as [r Hr]; exists r.
          intros (e&σ). rewrite /ε3.
          destruct (Kinv e); simpl; try real_solver.
          etrans; [ | eapply (Hr (e, σ)); eauto]. apply cond_nonneg.
        }
        iSplit; [| iSplit].
        2: { iPureIntro; done. }
        * iPureIntro.
          etrans; [ | apply Hleq].
          apply Rplus_le_compat_l.
          apply SeriesC_le; last first.
          { destruct Hub as [r Hr].
            apply (ex_seriesC_le _ (λ ρ, (state_step σ' l ρ * r)%R)).
            - intros; split.
              + apply Rmult_le_pos; [apply pmf_pos | by destruct (ε2 _ )].
              + apply Rmult_le_compat_l; auto; apply pmf_pos.
            - apply ex_seriesC_scal_r.
              apply pmf_ex_seriesC.
          }
          intros 𝜎; simpl.
          split.
          ** apply Rmult_le_pos; auto; apply cond_nonneg.
          ** rewrite HKinv3 /=. lra.
        * rewrite /Φ.
          iIntros (σ).
          iSpecialize ("H" $! σ).
          iIntros "Hr"; iSpecialize ("H" with "Hr").
          iMod "H"; iModIntro.
          rewrite /ε3 HKinv3 /=.
          simpl.
          iClear "IH".
          iApply (exec_stutter_mono_pred with "[]"); [|eauto].
          iIntros (?) "H".
          iApply "H".
          by simpl in Hv'.
      + iRight. by iApply ("IH" with "Ht").
  Qed.


  Lemma exec_ub_prim_step e1 σ1 Z ε :
    (∃ R ε1 ε2, ⌜reducible (e1, σ1)⌝ ∗ ⌜ (ε1 + ε2 <= ε)%R ⌝ ∗ ⌜ub_lift (prim_step e1 σ1) R ε1⌝ ∗
          ∀ e2 σ2 , ⌜R (e2, σ2)⌝ ={∅}=∗ Z (e2, σ2) ε2)
    ⊢ exec_ub e1 σ1 ε Z.
  Proof.
    iIntros "(%R&%ε1&%ε2&%&%&%&H)".
    rewrite exec_ub_unfold.
    iLeft.
    iExists R, ε1, (λ _, ε2).
    repeat iSplit; try done.
    - iExists ε2. done.
    - iPureIntro. rewrite SeriesC_scal_r. rewrite prim_step_mass; last done. lra.
    - iIntros. iApply exec_stutter_free. iApply "H". done.
  Qed. 


  Lemma exec_ub_adv_comp e1 σ1 Z (ε : nonnegreal) :
      (∃ R (ε1 : nonnegreal) (ε2 : cfg Λ -> nonnegreal),
          ⌜reducible (e1, σ1)⌝ ∗
          ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗
          ⌜ (ε1 + SeriesC (λ ρ, (prim_step e1 σ1 ρ) * ε2(ρ)) <= ε)%R ⌝ ∗ ⌜ub_lift (prim_step e1 σ1) R ε1⌝ ∗
            ∀ e2 σ2, ⌜ R (e2, σ2) ⌝ ={∅}=∗ exec_stutter (fun ε' => Z (e2, σ2) ε') (ε2 (e2, σ2)))
    ⊢ exec_ub e1 σ1 ε Z.
  Proof.
    iIntros "(% & % & % & % & % & % & % & H)".
    rewrite {1}exec_ub_unfold.
    iLeft.
    iExists _,_,_.
    iSplit; [done|].
    iSplit; [done|].
    iSplit; [done|].
    iSplit; done.
  Qed.


  Lemma exec_ub_adv_comp' e1 σ1 Z (ε : nonnegreal) :
      (∃ R (ε2 : cfg Λ -> nonnegreal),
          ⌜reducible (e1, σ1)⌝ ∗
          ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗
          ⌜ (SeriesC (λ ρ, (prim_step e1 σ1 ρ) * ε2(ρ)) = ε)%R ⌝ ∗ ⌜ub_lift (prim_step e1 σ1) R nnreal_zero⌝ ∗
            ∀ e2 σ2, ⌜ R (e2, σ2)⌝ ={∅}=∗ exec_stutter (fun ε' => Z (e2, σ2) ε') (ε2 (e2, σ2)))
    ⊢ exec_ub e1 σ1 ε Z.
  Proof.
    iIntros "(% & % & % & % & %Hε & % & H)".
    rewrite {1}exec_ub_unfold.
    iLeft.
    iExists _,nnreal_zero,_.
    iSplit; [done|].
    iSplit; [done|].
    iSplit.
    { iPureIntro.
      simpl. rewrite Hε. lra.
    }
    iSplit; done.
  Qed.

  (* TODO: Maybe allow weakening of the grading *)
  Lemma exec_ub_state_step α e1 σ1 Z (ε ε' : nonnegreal) :
    α ∈ get_active σ1 →
    (∃ R, ⌜ub_lift (state_step σ1 α) R ε⌝ ∗
          ∀ σ2 , ⌜R σ2 ⌝ ={∅}=∗ exec_ub e1 σ2 ε' Z)
    ⊢ exec_ub e1 σ1 (ε + ε') Z.
  Proof.
    iIntros (?) "(%&%&H)".
    rewrite exec_ub_unfold. iRight.
    iApply big_orL_elem_of; first done.
    iExists R2, ε, (λ _, ε').
    repeat iSplit; try done.
    - iPureIntro; eexists _; done.
    - iPureIntro. rewrite SeriesC_scal_r. rewrite state_step_mass; [simpl;lra|done]. 
    - iIntros. iApply exec_stutter_free. by iApply "H".
  Qed.



  (* for state steps that consume zero error *)
  Lemma exec_ub_state_adv_comp' α e1 σ1 Z (ε : nonnegreal) :
    (α ∈ get_active σ1 ->
     (∃ R (ε2 : cfg Λ -> nonnegreal),
        ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗
        ⌜ (SeriesC (λ ρ, (state_step σ1 α ρ) * ε2 (e1, ρ)) <= ε)%R ⌝ ∗
        ⌜ub_lift (state_step σ1 α) R nnreal_zero⌝ ∗
        ∀ σ2, ⌜ R σ2 ⌝ ={∅}=∗ exec_stutter (fun ε' => exec_ub e1 σ2 ε' Z) (ε2 (e1, σ2)))
      ⊢ exec_ub e1 σ1 ε Z)%I.
  Proof.
    iIntros (?) "(% & % & % & %Hε & % & H)".
    rewrite {1}exec_ub_unfold.
    iRight.
    iApply big_orL_elem_of; eauto.
    iExists _,nnreal_zero,_.
    iSplit; [auto|].
    iSplit.
    { iPureIntro. by rewrite /= Rplus_0_l. }
    iSplit; [done|done].
  Qed.

  Lemma exec_ub_strong_ind (Ψ : expr Λ → state Λ → nonnegreal → iProp Σ) Z :
    (∀ n e σ ε, Proper (dist n) (Ψ e σ ε)) →
    ⊢ (□ (∀ e σ ε, exec_ub_pre Z (λ '((e, σ), ε), Ψ e σ ε ∧ exec_ub e σ ε Z)%I ((e, σ), ε) -∗ Ψ e σ ε) →
       ∀ e σ ε, exec_ub e σ ε Z -∗ Ψ e σ ε)%I.
  Proof.
    iIntros (HΨ). iIntros "#IH" (e σ ε) "H".
    set (Ψ' := (λ '((e, σ), ε), Ψ e σ ε):
           (prodO (prodO (exprO Λ) (stateO Λ)) NNRO) → iProp Σ).
    assert (NonExpansive Ψ').
    { intros n [[e1 σ1]?] [[e2 σ2]?]
        [[?%leibniz_equiv ?%leibniz_equiv]?%leibniz_equiv].
      simplify_eq/=. f_equiv. }
    rewrite /exec_ub/exec_ub'.
    iApply (least_fixpoint_ind _ Ψ' with "[] H").
    iModIntro. iIntros ([[??]?]) "H". by iApply "IH".
  Qed. 


(*
  Lemma exec_ub_reducible e σ Z1 Z2 ε1 ε2 :
    (exec_ub e σ ε1 Z1)  ={∅}=∗ ⌜irreducible e σ⌝ -∗ (exec_ub e σ ε2 Z2).
  Proof.
    rewrite /exec_ub /exec_ub'.
    set (Φ := (λ x, |={∅}=> ⌜irreducible x.2.1 x.2.2⌝ -∗ (exec_ub x.2.1 x.2.2 ε2 Z2))%I : prodO NNRO cfgO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros n (?&(?&?)) (?&(?&?)) [[=] [[=] [=]]]. by simplify_eq. }
    iPoseProof (least_fixpoint_iter (exec_ub_pre Z1) Φ
                 with "[]") as "H"; last first.
    { done. }
    iIntros "!>" ((ε' & [e1 σ1])). rewrite /exec_ub_pre.
    iIntros "[(% & % & % & H) | H] /="; auto;
    rewrite /Φ/=.
    - iModIntro.
      iIntros.
      exfalso.
      pose proof (not_reducible (e1, σ1)) as (H3 & H4).
      by apply H4.
    - iDestruct (big_orL_mono _ (λ n αs, |={∅}=> ⌜irreducible (e1, σ1)⌝ -∗ exec_ub e1 σ1 ε2 Z2)%I  with "H") as "H".
      { intros.
        iIntros.
        iModIntro.
        iIntros.
        rewrite exec_ub_unfold.
        iRight.
        iApply (big_orL_elem_of _ _ y).
        - eapply elem_of_list_lookup_2; eauto.
        -
*)

(*
  Lemma exec_ub_irreducible e σ Z ε :
    ⌜irreducible e σ⌝ ⊢ exec_ub e σ ε Z.
  Proof.
    iIntros "H".
    rewrite {1}exec_ub_unfold.
    iRight.
    iInduction (get_active σ) as [| l] "IH".
    { rewrite big_orL_nil //. }
      rewrite 2!big_orL_cons.
      iDestruct "H" as "[(%R2 & %ε1 & %ε2 & (%Hleq & %Hub & H)) | Ht]".
*)

  (* This lemma might not be true anymore *)
  (*
  Lemma exec_ub_reducible e σ Z ε :
    exec_ub e σ ε Z ={∅}=∗ ⌜reducible e σ⌝.
  Proof.
    rewrite /exec_ub /exec_ub'.
    set (Φ := (λ x, |={∅}=> ⌜reducible x.2.1 x.2.2⌝)%I : prodO RO cfgO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros n (?&(?&?)) (?&(?&?)) [[=] [[=] [=]]]. by simplify_eq. }
    iPoseProof (least_fixpoint_iter (exec_ub_pre Z) Φ
                 with "[]") as "H"; last first.
    { done. }
    iIntros "!>" ((ε' & [e1 σ1])). rewrite /exec_ub_pre.
    iIntros "[(% & % & % & H) | H] /="; auto.
    rewrite /Φ/=.
    Search "big_orL".
    iDestruct (big_orL_mono _ (λ n αs, |={∅}=> ⌜reducible (e1, σ1)⌝)%I  with "H") as "H".
      { iIntros (? α' ?%elem_of_list_lookup_2) "(%R2 & %ε1 & %ε2 & %Hleq & %Hub & H)".
        eapply ub_lift_pos_R in Hub.
        eapply Rcoupl_inhabited_l in Hcpl as (σ2 & [] & ? & ? & ?); last first.
        { rewrite state_step_mass //. lra. }
        iApply (pure_impl_1 (reducible e1 σ2)).
        { iPureIntro. by eapply state_step_reducible. }
        by iMod ("H" with "[//]"). }
      iInduction (get_active σ1) as [| α] "IH"; [done|].
      rewrite big_orL_cons.
      iDestruct "H" as "[? | H]"; [done|].
      by iApply "IH".
    - iDestruct (big_orL_mono _ (λ n αs, |={∅}=> ⌜reducible (e1, σ1)⌝)%I  with "H") as "H".
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
  *)

  (*
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
  *)

End exec_ub.

(** * The weakest precondition  *)
Definition ub_wp_pre `{!irisGS Λ Σ}
    (wp : coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
    coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
  match to_val e1 with
  | Some v => |={E}=> Φ v
  | None => ∀ σ1 ε1,
      state_interp σ1 ∗ err_interp ε1 ={E,∅}=∗
      exec_ub e1 σ1 ε1 (λ '(e2, σ2) ε2,
        ▷ |={∅,E}=> state_interp σ2 ∗ err_interp ε2 ∗ wp E e2 Φ)
end%I.

Local Instance wp_pre_contractive `{!irisGS Λ Σ} : Contractive (ub_wp_pre).
Proof.
  rewrite /ub_wp_pre /= => n wp wp' Hwp E e1 Φ /=.
  do 7 (f_equiv).
  apply least_fixpoint_ne_outer; [|done].
  intros Ψ [[e' σ'] ε']. rewrite /exec_ub_pre.
  do 17 f_equiv.
  { rewrite /exec_stutter. do 9 f_equiv. f_contractive. do 3 f_equiv. apply Hwp. }
Qed.


(* TODO: get rid of stuckness in notation [iris/bi/weakestpre.v] so that we don't have to do this *)
Local Definition ub_wp_def `{!irisGS Λ Σ} : Wp (iProp Σ) (expr Λ) (val Λ) () :=
  {| wp := λ _ : (), fixpoint (ub_wp_pre); wp_default := () |}.
Local Definition ub_wp_aux : seal (@ub_wp_def). Proof. by eexists. Qed.
Definition ub_wp' := ub_wp_aux.(unseal).
Global Arguments ub_wp' {Λ Σ _}.
Global Existing Instance ub_wp'.
Local Lemma ub_wp_unseal `{!irisGS Λ Σ} : wp = (@ub_wp_def Λ Σ _).(wp).
Proof. rewrite -ub_wp_aux.(seal_eq) //. Qed.

Section ub_wp.
Context `{!irisGS Λ Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types ρ : cfg Λ.
Implicit Types ε : R.

(* Weakest pre *)
Lemma ub_wp_unfold s E e Φ :
  WP e @ s; E {{ Φ }} ⊣⊢ ub_wp_pre (wp (PROP:=iProp Σ) s) E e Φ.
Proof. rewrite ub_wp_unseal. apply (fixpoint_unfold (ub_wp_pre)). Qed.

Global Instance ub_wp_ne s E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp (PROP:=iProp Σ) s E e).
Proof.
  revert e. induction (lt_wf n) as [n _ IH]=> e Φ Ψ HΦ.
  rewrite !ub_wp_unfold /ub_wp_pre /=.
  do 7 f_equiv.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [[]?]. rewrite /exec_ub_pre.
  do 16 f_equiv.
  rewrite /exec_stutter.
  do 10 f_equiv. f_contractive_fin.
  rewrite IH; [done|lia|].
  intros ?. eapply dist_S, HΦ. 
Qed.

Global Instance ub_wp_proper s E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (wp (PROP:=iProp Σ) s E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply ub_wp_ne=>v; apply equiv_dist.
Qed.
Global Instance ub_wp_contractive s E e n :
  TCEq (to_val e) None →
  Proper (pointwise_relation _ (dist_later n) ==> dist n) (wp (PROP:=iProp Σ) s E e).
Proof.
  intros He Φ Ψ HΦ. rewrite !ub_wp_unfold /ub_wp_pre He /=.
  do 6 f_equiv.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [[]?]. rewrite /exec_ub_pre.
  do 16 f_equiv.
  rewrite /exec_stutter. do 10 f_equiv. f_contractive. do 6 f_equiv.
Qed.

Lemma ub_wp_value_fupd' s E Φ v : WP of_val v @ s; E {{ Φ }} ⊣⊢ |={E}=> Φ v.
Proof. rewrite ub_wp_unfold /ub_wp_pre to_of_val. auto. Qed.

Lemma ub_wp_strong_mono E1 E2 e Φ Ψ s :
  E1 ⊆ E2 →
  WP e @ s ; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ WP e @ s ; E2 {{ Ψ }}.
Proof.
  iIntros (HE) "H HΦ". iLöb as "IH" forall (e E1 E2 HE Φ Ψ).
  rewrite !ub_wp_unfold /ub_wp_pre /=.
  destruct (to_val e) as [v|] eqn:?.
  { iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _). }
  iIntros (σ1 ε) "[Hσ Hε]".
  iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  iMod ("H" with "[$]") as "H".
  iApply (exec_ub_mono_pred with "[Hclose HΦ] H").
  iIntros ([e2 σ2]?) "H".
  iModIntro.
  iMod "H" as "(?&?& Hwp)". iFrame.
  iMod "Hclose" as "_". iModIntro.
  iApply ("IH" with "[] Hwp"); auto.
Qed.

Lemma fupd_ub_wp s E e Φ : (|={E}=> WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }}.
Proof.
  rewrite ub_wp_unfold /ub_wp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?.
  { by iMod "H". }
   iIntros (σ1 ε) "Hi". iMod "H". by iApply "H".
Qed.
Lemma ub_wp_fupd s E e Φ : WP e @ s; E {{ v, |={E}=> Φ v }} ⊢ WP e @ s; E {{ Φ }}.
Proof. iIntros "H". iApply (ub_wp_strong_mono E with "H"); auto. Qed.

Lemma ub_wp_atomic E1 E2 e Φ `{!Atomic StronglyAtomic e} a :
  (|={E1,E2}=> WP e @ a; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ a; E1 {{ Φ }}.
Proof.
  iIntros "H".
  rewrite !ub_wp_unfold /ub_wp_pre.
  destruct (to_val e) as [v|] eqn:He; [by do 2 iMod "H"|].
  iIntros (σ1 ε1) "(Hσ&Hε)".
  iSpecialize ("H" $! σ1 ε1).
  iMod ("H" with "[Hσ Hε]") as "H"; [iFrame|].
  iMod "H"; iModIntro.
  iApply (exec_ub_strong_mono with "[] [] H"); [done|].
  iIntros (e2 σ2 ε2) "([%σ' %Hstep]&H)".
  iNext.
  iMod "H" as "(Hσ&Hε&Hwp)".
  rewrite !ub_wp_unfold /ub_wp_pre.
  destruct (to_val e2) as [?|] eqn:He2.
  + iFrame. do 2 (iMod "Hwp"). by do 2 iModIntro.
  + iMod ("Hwp" $! _ _ with "[Hσ Hε]") as "Hwp"; [iFrame|].
    specialize (atomic _ _ _ Hstep) as Hatomic. (* key step *)
    destruct Hatomic.
    congruence. (* how do we do this "by hand"? Not obvious to me *)
Qed.


(* Fixable?
Lemma ub_wp_atomic s E1 E2 e Φ `{!Atomic (stuckness_to_atomicity s) e} :
  (|={E1,E2}=> WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros "H". rewrite !ub_wp_unfold /ub_wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { by iDestruct "H" as ">>> $". }
  iIntros (σ1 ε) "[Hσ Hε]". iMod "H".
  iMod ("H" with "[$]") as "H".
  iModIntro.
  iDestruct (exec_ub_strengthen with "H") as "H".
  iApply (exec_ub_mono_pred with "[] H").
  iIntros (? [e2 σ2]) "[[% %Hstep] H]".
  iModIntro.
  iMod "H" as "(Hσ & Hρ & H)".
  rewrite !ub_wp_unfold /ub_wp_pre.
  destruct (to_val e2) as [v2|] eqn:He2.
  - iDestruct "H" as ">> $". by iFrame.
  - iMod ("H" with "[$]") as "H".
    pose proof (atomic σ e2 σ2 Hstep) as H3.
    case_match.
    + rewrite /is_Some in H3.
      destruct H3.
      simplify_eq.
    + apply not_reducible in H3.
      (* so... we could get this back if we did a case match on
         the exec_ub in H. We would need to exclude the two state step cases somehow. *)
      rewrite {1}exec_ub_unfold.
      iDestruct "H" as "[[% [% [% (%Hred&_)]]]|[[% [% [% (%Hred&_)]]]|[H|H]]]".
      1,2: by destruct H3.
      (* ??? *)
Admitted.
*)

Lemma ub_wp_step_fupd s E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> P) -∗ WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ s; E1 {{ Φ }}.
Proof.
  rewrite !ub_wp_unfold /ub_wp_pre. iIntros (-> ?) "HR H".
  iIntros (σ1 ε) "[Hσ Hε]". iMod "HR".
  iMod ("H" with "[$Hσ $Hε]") as "H".
  iModIntro.
  iApply (exec_ub_mono_pred with "[HR] H").
  iIntros ([e2 σ2] ?) "H".
  iModIntro.
  iMod "H" as "(Hσ & Hρ & H)".
  iMod "HR".
  iFrame "Hσ Hρ".
  iApply (ub_wp_strong_mono E2 with "H"); [done..|].
  iIntros "!>" (v) "H". by iApply "H".
Qed.

Lemma ub_wp_bind K `{!LanguageCtx K} s E e Φ :
  WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }} ⊢ WP K e @ s; E {{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite ub_wp_unfold /ub_wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by iApply fupd_ub_wp. }
  rewrite ub_wp_unfold /ub_wp_pre fill_not_val /=; [|done].
  iIntros (σ1 ε) "[Hσ Hε]".
  iMod ("H" with "[$Hσ $Hε]") as "H".
  iModIntro.
  iApply exec_ub_bind; [done |].
  iApply (exec_ub_mono with "[] [] H").
  - iPureIntro; lra.
  - iIntros ([e2 σ2] ?) "H".
    iModIntro.
    iMod "H" as "(Hσ & Hρ & H)".
    iModIntro.
    iFrame "Hσ Hρ". by iApply "IH".
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
Lemma ub_wp_mono s E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (ub_wp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma ub_wp_mask_mono s E1 E2 e Φ : E1 ⊆ E2 → WP e @ s; E1 {{ Φ }} ⊢ WP e @ s; E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (ub_wp_strong_mono with "H"); auto. Qed.
Global Instance ub_wp_mono' s E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply ub_wp_mono. Qed.
Global Instance ub_wp_flip_mono' s E e :
  Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (wp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply ub_wp_mono. Qed.

Lemma ub_wp_value_fupd s E Φ e v : IntoVal e v → WP e @ s; E {{ Φ }} ⊣⊢ |={E}=> Φ v.
Proof. intros <-. by apply ub_wp_value_fupd'. Qed.
Lemma ub_wp_value' s E Φ v : Φ v ⊢ WP (of_val v) @ s; E {{ Φ }}.
Proof. rewrite ub_wp_value_fupd'. auto. Qed.
Lemma ub_wp_value s E Φ e v : IntoVal e v → Φ v ⊢ WP e @ s; E {{ Φ }}.
Proof. intros <-. apply ub_wp_value'. Qed.

Lemma ub_wp_frame_l s E e Φ R : R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros "[? H]". iApply (ub_wp_strong_mono with "H"); auto with iFrame. Qed.
Lemma ub_wp_frame_r s E e Φ R : WP e @ s; E {{ Φ }} ∗ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros "[H ?]". iApply (ub_wp_strong_mono with "H"); auto with iFrame. Qed.

Lemma ub_wp_frame_step_l s E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> R) ∗ WP e @ s; E2 {{ Φ }} ⊢ WP e @ s; E1 {{ v, R ∗ Φ v }}.
Proof.
  iIntros (??) "[Hu Hwp]". iApply (ub_wp_step_fupd with "Hu"); try done.
  iApply (ub_wp_mono with "Hwp"). by iIntros (?) "$$".
Qed.
Lemma ub_wp_frame_step_r s E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  WP e @ s; E2 {{ Φ }} ∗ (|={E1}[E2]▷=> R) ⊢ WP e @ s; E1 {{ v, Φ v ∗ R }}.
Proof.
  rewrite [(WP _ @ _; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply ub_wp_frame_step_l.
Qed.
Lemma ub_wp_frame_step_l' s E e Φ R :
  TCEq (to_val e) None → ▷ R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros (?) "[??]". iApply (ub_wp_frame_step_l s E E); try iFrame; eauto. Qed.
Lemma ub_wp_frame_step_r' s E e Φ R :
  TCEq (to_val e) None → WP e @ s; E {{ Φ }} ∗ ▷ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros (?) "[??]". iApply (ub_wp_frame_step_r s E E); try iFrame; eauto. Qed.

Lemma ub_wp_wand s E e Φ Ψ :
  WP e @ s; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (ub_wp_strong_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma ub_wp_wand_l s E e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (ub_wp_wand with "Hwp H"). Qed.
Lemma wp_wand_r s E e Φ Ψ :
  WP e @ s; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (ub_wp_wand with "Hwp H"). Qed.
Lemma ub_wp_frame_wand s E e Φ R :
  R -∗ WP e @ s; E {{ v, R -∗ Φ v }} -∗ WP e @ s; E {{ Φ }}.
Proof.
  iIntros "HR HWP". iApply (ub_wp_wand with "HWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.

End ub_wp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{!irisGS Λ Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  Global Instance frame_ub_wp p s E e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Ψ }}) | 2.
  Proof. rewrite /Frame=> HR. rewrite ub_wp_frame_l. apply ub_wp_mono, HR. Qed.

  Global Instance is_except_0_ub_wp s E e Φ : IsExcept0 (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_ub_wp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_ub_wp p s E e P Φ :
    ElimModal True p false (|==> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r wand_elim_r fupd_ub_wp.
  Qed.

  Global Instance elim_modal_fupd_ub_wp p s E e P Φ :
    ElimModal True p false (|={E}=> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_ub_wp.
  Qed.

  Global Instance elim_modal_fupd_ub_wp_atomic p s E1 E2 e P Φ :
    ElimModal (Atomic StronglyAtomic e) p false
            (|={E1,E2}=> P) P
            (WP e @ s; E1 {{ Φ }}) (WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }})%I | 100.
  Proof.
    intros ?.
    by rewrite intuitionistically_if_elim
      fupd_frame_r wand_elim_r ub_wp_atomic.
  Qed.

  Global Instance add_modal_fupd_ub_wp s E e P Φ :
    AddModal (|={E}=> P) P (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_ub_wp. Qed.

  Global Instance elim_acc_ub_wp_atomic {X} E1 E2 α β γ e s Φ :
    ElimAcc (X:=X) (Atomic StronglyAtomic e)
            (fupd E1 E2) (fupd E2 E1)
            α β γ (WP e @ s; E1 {{ Φ }})
            (λ x, WP e @ s; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I | 100.
  Proof.
    iIntros (?) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (ub_wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_ub_wp_nonatomic {X} E α β γ e s Φ :
    ElimAcc (X:=X) True (fupd E E) (fupd E E)
            α β γ (WP e @ s; E {{ Φ }})
            (λ x, WP e @ s; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply ub_wp_fupd.
    iApply (ub_wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.
End proofmode_classes.

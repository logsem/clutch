From Stdlib Require Export Reals Psatz.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export fixpoint big_op.
From iris.prelude Require Import options.

From clutch.bi Require Export weakestpre.
From clutch.prelude Require Import stdpp_ext iris_ext NNRbar tactics.
From clutch.con_prob_lang Require Import lang erasure.
From clutch.common Require Export sch_erasable con_language.
From clutch.prob Require Export couplings_app distribution.
From clutch.foxtrot Require Import oscheduler full_info.

Import uPred.

Set Default Proof Using "Type*".


Local Open Scope NNR_scope.
#[global] Hint Resolve cond_nonneg : core.

Class foxtrotWpGS (Λ : conLanguage) (Σ : gFunctors) := FoxtrotWpGS {
  foxtrotWpGS_invGS :: invGS_gen HasNoLc Σ;
  state_interp : state Λ → iProp Σ;
  spec_interp : cfg Λ -> iProp Σ;                                                         
  fork_post: val Λ -> iProp Σ;
  err_interp : nonnegreal → iProp Σ;
}.
Global Opaque foxtrotWpGS_invGS.
Global Arguments FoxtrotWpGS {Λ Σ}.
Canonical Structure NNRO := leibnizO nonnegreal.
#[global] Hint Resolve cond_nonneg : core.


Section modalities.
  Context `{H:!foxtrotWpGS con_prob_lang Σ}.
  Implicit Types ε : nonnegreal.

  (** spec_coupl *)
  Definition spec_coupl_pre Z
    (Φ : state con_prob_lang * cfg con_prob_lang * nonnegreal -> iProp Σ) :
    (state con_prob_lang * cfg con_prob_lang * nonnegreal -> iProp Σ) :=
    (λ x,
      let '(σ1, ρ, ε) := x in
      ⌜(1<=ε)%R⌝ ∨
        Z σ1 ρ ε ∨
        (∀ (ε': nonnegreal), ⌜(ε < ε')%R⌝ -∗ Φ (σ1, ρ, ε')) ∨
        ∃ (S: state con_prob_lang -> (full_info_state * cfg con_prob_lang) -> Prop)
          (μ : distr (state con_prob_lang))
          (osch : full_info_oscheduler)
          (ε1 : nonnegreal) (X2 : full_info_state * cfg con_prob_lang -> nonnegreal) (r : R),
          ⌜ sch_erasable (λ t _ _ sch, TapeOblivious t sch) μ σ1 ⌝ ∗
          ⌜ ∀ x, (X2 x <= r)%R ⌝ ∗
          ⌜ (ε1 + Expval (osch_lim_exec osch ([], ρ)) X2 <= ε)%R ⌝ ∗
          ⌜ ARcoupl μ (osch_lim_exec osch ([], ρ)) S ε1 ⌝ ∗
          ⌜ ∀ σx σy ρx ρy l , S σx (l, ρx) -> S σy (l, ρy) -> σx=σy /\ ρx = ρy ⌝ ∗
          ∀ σ2 l ρ', ⌜S σ2 (l, ρ')⌝ ={∅}=∗ Φ (σ2, ρ', X2 (l, ρ'))
    )%I.
    
  #[local] Instance spec_coupl_pre_ne Z Φ :
    NonExpansive (spec_coupl_pre Z Φ).
  Proof.
    rewrite /spec_coupl_pre.
    intros ?[[?[??]]?][[?[??]]?] ([[=][=]]&[=]).
    by simplify_eq.
  Qed.

  #[local] Instance spec_coupl_pre_mono Z : BiMonoPred (spec_coupl_pre Z).
  Proof.
    split; [|apply _].
    iIntros (Φ Ψ HNEΦ HNEΨ) "#Hwand".
    iIntros ([[??]?]) "[H|[H|[H|(%&%&%&%&%&%&%&%&%&%&%&H)]]]".
    - by iLeft.
    - iRight; by iLeft.
    - do 2 iRight; iLeft.
      iIntros. iApply "Hwand".
      by iApply "H".
    - do 3 iRight.
      repeat iExists _; repeat (iSplit; [done|]).
      iIntros.
      iApply "Hwand".
      iApply ("H" with "[//]").
  Qed.

  Definition spec_coupl' Z := bi_least_fixpoint (spec_coupl_pre Z).
  Definition spec_coupl σ ρ ε Z:= spec_coupl' Z ((σ, ρ), ε).

  Lemma spec_coupl_unfold σ1 ρ ε Z :
    spec_coupl σ1 ρ ε Z ≡
      (⌜(1<=ε)%R⌝ ∨
        Z σ1 ρ ε ∨
        (∀ (ε': nonnegreal), ⌜(ε < ε')%R⌝ -∗ spec_coupl σ1 ρ ε' Z) ∨
        ∃ (S: state con_prob_lang -> (full_info_state * cfg con_prob_lang) -> Prop)
          (μ : distr (state con_prob_lang))
          (osch : full_info_oscheduler)
          (ε1 : nonnegreal) (X2 : full_info_state * cfg con_prob_lang -> nonnegreal) (r : R),
          ⌜ sch_erasable (λ t _ _ sch, TapeOblivious t sch) μ σ1 ⌝ ∗
          ⌜ ∀ x, (X2 x <= r)%R ⌝ ∗
          ⌜ (ε1 + Expval (osch_lim_exec osch ([], ρ)) X2 <= ε)%R ⌝ ∗
          ⌜ ARcoupl μ (osch_lim_exec osch ([], ρ)) S ε1 ⌝ ∗
          ⌜ ∀ σx σy ρx ρy l , S σx (l, ρx) -> S σy (l, ρy) -> σx=σy /\ ρx = ρy  ⌝ ∗
          ∀ σ2 l ρ', ⌜S σ2 (l, ρ')⌝ ={∅}=∗ spec_coupl σ2 ρ' (X2 (l, ρ')) Z)%I.
  Proof. rewrite /spec_coupl /spec_coupl' least_fixpoint_unfold //. Qed.

  Lemma spec_coupl_ret_err_ge_1 σ1 ρ1 Z (ε : nonnegreal) :
    (1 <= ε)%R → ⊢ spec_coupl σ1 ρ1 ε Z.
  Proof. iIntros. rewrite spec_coupl_unfold. by iLeft. Qed.

  Lemma spec_coupl_ret σ1 ρ1 Z ε :
    Z σ1 ρ1 ε -∗ spec_coupl σ1 ρ1 ε Z.
  Proof. iIntros. rewrite spec_coupl_unfold. by iRight; iLeft. Qed.

  Lemma spec_coupl_amplify σ1 ρ1 Z ε :
    (∀ (ε':nonnegreal), ⌜(ε<ε')%R⌝ -∗ spec_coupl σ1 ρ1 ε' Z) -∗ spec_coupl σ1 ρ1 ε Z.
  Proof.
    iIntros.  rewrite spec_coupl_unfold. naive_solver. Qed.

  Lemma spec_coupl_rec σ1 ρ1 (ε : nonnegreal) Z :
     (∃ (S: state con_prob_lang -> (full_info_state * cfg con_prob_lang) -> Prop)
          (μ : distr (state con_prob_lang))
          (osch : full_info_oscheduler)
          (ε1 : nonnegreal) (X2 : full_info_state * cfg con_prob_lang -> nonnegreal) (r : R),
          ⌜ sch_erasable (λ t _ _ sch, TapeOblivious t sch) μ σ1 ⌝ ∗
          ⌜ ∀ x, (X2 x <= r)%R ⌝ ∗
          ⌜ (ε1 + Expval (osch_lim_exec osch ([], ρ1)) X2 <= ε)%R ⌝ ∗
          ⌜ ARcoupl μ (osch_lim_exec osch ([], ρ1)) S ε1 ⌝ ∗
          ⌜ ∀ σx σy ρx ρy l , S σx (l, ρx) -> S σy (l, ρy) -> σx=σy /\ ρx = ρy  ⌝ ∗
          ∀ σ2 l ρ', ⌜S σ2 (l, ρ')⌝ ={∅}=∗ spec_coupl σ2 ρ' (X2 (l, ρ')) Z)%I
    ⊢ spec_coupl σ1 ρ1 ε Z.
  Proof. iIntros "H". rewrite spec_coupl_unfold. repeat iRight. done. Qed.

  Lemma spec_coupl_ind (Ψ Z : state con_prob_lang → cfg con_prob_lang -> nonnegreal → iProp Σ) :
    ⊢ (□ (∀ σ ρ ε,
             spec_coupl_pre Z (λ '(σ', ρ', ε'),
                 Ψ σ' ρ' ε' ∧ spec_coupl σ' ρ' ε' Z)%I ((σ, ρ), ε) -∗ Ψ σ ρ ε) →
       ∀ σ ρ ε, spec_coupl σ ρ ε Z -∗ Ψ σ ρ ε)%I.
  Proof.
    iIntros "#IH" (σ ρ ε) "H".
    set (Ψ' := (λ '(σ, ρ, ε), Ψ σ ρ ε) :
           (prodO (prodO (stateO con_prob_lang) (cfgO con_prob_lang)) NNRO) → iProp Σ).
    assert (NonExpansive Ψ').
    { intros n [[σ1 ρ1] ε1] [[σ2 ρ2] ε2].
      intros [[[=][=]][=]].
      by simplify_eq/=. }
    iApply (least_fixpoint_ind _ Ψ' with "[] H").
    iIntros "!#" ([[??] ?]) "H". by iApply "IH".
  Qed.

  Lemma fupd_spec_coupl σ1 ρ1 Z (ε : nonnegreal) :
    (|={∅}=> spec_coupl σ1 ρ1 ε Z) ⊢ spec_coupl σ1 ρ1 ε Z.
  Proof.
    iIntros "H".
    iApply spec_coupl_rec.
    iExists (λ x y, x= σ1 /\ y= ([], ρ1)), (dret _), full_info_inhabitant, nnreal_zero, (λ _, ε), ε.
    repeat iSplit.
    - iPureIntro. apply dret_sch_erasable.
    - iPureIntro. naive_solver.
    - iPureIntro. rewrite full_info_inhabitant_lim_exec.
      rewrite Expval_dret/=; lra.
    - iPureIntro.
      rewrite full_info_inhabitant_lim_exec.
      by apply ARcoupl_dret.
    - iIntros (?????[??][??]). by simplify_eq.
    - iIntros (???[??]). by simplify_eq.
  Qed.
  
  Lemma spec_coupl_mono σ1 ρ1 Z1 Z2 ε :
    (∀ σ2 ρ2 ε', Z1 σ2 ρ2 ε' -∗ Z2 σ2 ρ2 ε') -∗
    spec_coupl σ1 ρ1 ε Z1 -∗ spec_coupl σ1 ρ1 ε Z2.
  Proof.
    iIntros "HZ Hs".
    iRevert "HZ".
    iRevert (σ1 ρ1 ε) "Hs".
    iApply spec_coupl_ind.
    iIntros "!#" (σ ρ ε)
      "[% | [? | [H|(%&%&%&%&%&%&%&%&%&%&%&H)]]] Hw".
    - iApply spec_coupl_ret_err_ge_1. lra.
    - iApply spec_coupl_ret. by iApply "Hw".
    - iApply spec_coupl_amplify. iIntros. by iApply "H".
    - iApply spec_coupl_rec.
      repeat iExists _.
      repeat iSplit; try done.
      iIntros (????).
      iMod ("H" $! _ with "[//]") as "[IH _]".
      by iApply "IH".
  Qed.

  Lemma spec_coupl_mono_err ε1 ε2 σ1 ρ1 Z :
    (ε1 <= ε2)%R → spec_coupl σ1 ρ1 ε1 Z -∗ spec_coupl σ1 ρ1 ε2 Z.
  Proof.
    iIntros (Heps) "Hs".
    iApply spec_coupl_rec.
    set (ε' := nnreal_minus ε2 ε1 Heps).
    iExists (λ x y, x=σ1/\y=([], ρ1)), (dret _), full_info_inhabitant, nnreal_zero, (λ _, ε1), ε1.
    repeat iSplit.
    - iPureIntro. apply dret_sch_erasable.
    - iPureIntro; intros. simpl. lra.
    - iPureIntro. rewrite full_info_inhabitant_lim_exec.
      rewrite Expval_dret/=; lra.
    - iPureIntro.
      rewrite full_info_inhabitant_lim_exec.
      by apply ARcoupl_dret.
    - iIntros (?????[??][??]). by simplify_eq.
    - iIntros (???[??]); by simplify_eq.
  Qed.
  
  Lemma spec_coupl_bind σ1 ρ1 Z1 Z2 ε :
    (∀ σ2 ρ2 ε', Z1 σ2 ρ2 ε' -∗ spec_coupl σ2 ρ2 ε' Z2) -∗
    spec_coupl σ1 ρ1 ε Z1 -∗
    spec_coupl σ1 ρ1 ε Z2.
  Proof.
    iIntros "HZ Hs".
    iRevert "HZ".
    iRevert (σ1 ρ1 ε) "Hs".
    iApply spec_coupl_ind.
    iIntros "!#" (σ ρ ε)
      "[% | [H |[H| (%&%&%&%&%&%&%&%&%&%&%&H)]]] HZ".
    - by iApply spec_coupl_ret_err_ge_1.
    - iApply ("HZ" with "H").
    - iApply spec_coupl_amplify.
      iIntros. by iApply "H". 
    - iApply spec_coupl_rec.
      repeat iExists _.
      repeat iSplit; try done.
      iIntros (????).
      iMod ("H" $! _ with "[//]") as "[H _]".
      by iApply "H".
  Qed.

  Lemma spec_coupl_step_l_dret_adv R μ (ε1 : nonnegreal) (ε2 : state con_prob_lang -> nonnegreal) ρ1 σ1 Z ε :
    sch_erasable (λ t _ _ sch, TapeOblivious t sch) μ σ1  ->
    (exists r, forall ρ, (ε2 ρ <= r)%R) ->
    (ε1 + Expval μ ε2 <= ε)%R ->
    pgl μ R ε1->
    (∀ σ2, ⌜ R σ2 ⌝ ={∅}=∗ spec_coupl σ2 ρ1 (ε2 σ2) Z)%I
    ⊢ spec_coupl σ1 ρ1 ε Z.
  Proof.
    iIntros (Herasable [r Hound] Hineq Hpgl) "H".
    iApply spec_coupl_rec.
    pose (n:=length ρ1.1).
    iExists (λ σ' '(l, ρ'),
               R σ' /\ ρ' = ρ1 /\ l=[(cfg_to_cfg' ρ1, n+ encode_nat σ')%nat; (cfg_to_cfg' ρ1, n)]
            ).
    iExists μ.
    iExists (full_info_cons_osch (λ _, dmap (λ x, n+encode_nat x)%nat μ)
                                 (λ _, full_info_stutter_osch full_info_inhabitant)
            ).
    iExists ε1, (λ '(l, ρ'),
                   match l!!0%nat with
                   | Some p =>
                       match decode_nat (p.2-n)%nat with
                       | Some x => ε2 x
                       | None => nnreal_zero
                       end
                   | None => nnreal_zero
                   end
                ).
    iExists r.
    assert (0<=r).
    { trans (ε2 inhabitant); naive_solver. }
    repeat iSplit.
    - done.
    - iPureIntro. intros [??]. by repeat case_match.
    - iPureIntro.
      etrans; last exact.
      apply Rplus_le_compat_l.
      rewrite full_info_cons_osch_lim_exec.
      rewrite Expval_dbind; last first.
      { eapply ex_expval_bounded with r.
        intros [??]. by repeat case_match.
      }
      { intros [??]. by repeat case_match. }
      rewrite Expval_dmap; last first.
      { apply ex_expval_bounded with r.
        intros ?. split.
        - apply Expval_ge_0'.
          intros [??]. by repeat case_match.
        - Local Opaque full_info_lift_osch.
          simpl.
          rewrite out_of_bounds_step'; last first.
          { rewrite /n. lia. }
          rewrite dret_id_left.
          rewrite full_info_lift_osch_lim_exec full_info_stutter_osch_lim_exec full_info_inhabitant_lim_exec.
          rewrite Expval_dmap; last first.
          + simpl. 
            apply ex_expval_bounded with r.
            intros [??]. simpl; by repeat case_match.
          + intros [??]. by repeat case_match.
          + rewrite dmap_dret. rewrite Expval_dret. simpl.
            by case_match.
      }
      { intros. apply Expval_ge_0'. intros [??]. by case_match.
      }
      apply Expval_le; last first.
      { apply ex_expval_bounded with r. naive_solver. }
      intros σ.
      simpl.
      rewrite out_of_bounds_step'; last (rewrite /n; lia).
      rewrite dret_id_left.
      rewrite full_info_lift_osch_lim_exec full_info_stutter_osch_lim_exec full_info_inhabitant_lim_exec.
      rewrite !dmap_dret Expval_dret.
      simpl. replace (_+_-_)%nat with (encode_nat (σ)); last first.
      { simpl. lia. }
      rewrite decode_encode_nat. done.
    - rewrite full_info_cons_osch_lim_exec.
      rewrite /dmap -!dbind_assoc.
      rewrite -{1}(dret_id_right (μ)).
      iPureIntro.
      replace (ε1) with (ε1+0)%NNR; last (apply nnreal_ext; simpl; lra).
      eapply (ARcoupl_dbind _ _ _ _ (λ x y, x=y /\ R x)); [try done..|]; last first.
      { replace (ε1) with (0+ε1)%NNR; last (apply nnreal_ext; simpl; lra).
        eapply up_to_bad_lhs; last done.
        eapply ARcoupl_mono; [done|done| |done|apply ARcoupl_eq].
        intros. naive_solver.
      }
      intros σ ?[??].
      simplify_eq.
      rewrite dret_id_left out_of_bounds_step'; last (rewrite /n; lia).
      rewrite dret_id_left full_info_lift_osch_lim_exec full_info_stutter_osch_lim_exec full_info_inhabitant_lim_exec.
      rewrite !dmap_dret.
      by apply ARcoupl_dret.
    - iPureIntro. intros x1 x2 ???(?&?&?)(?&?&?).
      subst. simplify_eq.
      assert (encode_nat x1 = encode_nat x2) as H' by lia.
      apply encode_nat_inj in H'. subst. naive_solver.
    - iIntros (σ l ?(?&->&->)).
      simpl.
      replace (_+_-_)%nat with (encode_nat σ); last first.
      { simpl. lia. }
      rewrite decode_encode_nat. by iApply "H".
      Local Transparent full_info_lift_osch.
  Qed.

  Lemma spec_coupl_step_r_adv R (ε1 : nonnegreal) m (ε2 : _ -> nonnegreal) ρ1 σ1 Z ε j e:
    reducible e ρ1.2 ->
    ρ1.1 !! j = Some e ->
    (exists r, forall ρ, (ε2 ρ <= r)%R) ->
    (ε1 + Expval (prim_step e ρ1.2) ε2 <= ε)%R ->
    pgl (prim_step e ρ1.2) (λ '(e', σ', efs), R(e', σ', efs)/\ tapes σ' = m) ε1->
    (∀ e' σ' efs, ⌜ R (e', σ', efs) /\ tapes σ' = m⌝ ={∅}=∗ spec_coupl σ1 (<[j:=e']>ρ1.1++efs, σ') (ε2 (e', σ', efs)) Z)%I
    ⊢ spec_coupl σ1 ρ1 ε Z.
  Proof.
    iIntros (Hreducible Hsome [r Hound] Hineq Hpgl) "H".
    assert (to_val e = None) as Hval.
    { destruct Hreducible. by eapply val_stuck. }
    iApply spec_coupl_rec.
    iExists (λ σ' '(l, ρ'),
               σ' = σ1 /\
               ∃ e' σ' efs,
                 R (e', σ', efs) /\
                 tapes σ' = m /\
                 ρ' = (<[j:=e']>ρ1.1++efs, σ') /\
                 l = [(cfg_to_cfg' ρ1, j)%nat; (cfg_to_cfg' (<[j:=e']>ρ1.1++efs, σ'), length (<[j:=e']>ρ1.1++efs))] 
            ).
    iExists (dret _).
    iExists (full_info_cons_osch (λ _, dret j)
                                 (λ _, full_info_stutter_osch full_info_inhabitant)
            ).
    iExists ε1, (λ '(l, ρ'),
                   match (decide (∃ '(e', σ', efs), ρ'=(<[j:=e']>ρ1.1++efs, σ'))) with
                   | left pro => ε2 (epsilon pro)
                   | _ => 0%NNR
                   end     
                ).
    iExists r.
    assert (0<=r).
    { trans (ε2 inhabitant); naive_solver. }
    repeat iSplit.
    - iPureIntro. apply dret_sch_erasable.
    - iPureIntro. intros [??]. by repeat case_match.
    - iPureIntro.
      etrans; last exact.
      apply Rplus_le_compat_l.
      rewrite full_info_cons_osch_lim_exec.
      rewrite Expval_dbind; last first.
      { eapply ex_expval_bounded with r.
        intros [??]. by repeat case_match.
      }
      { intros [??]. by repeat case_match. }
      rewrite Expval_dret.
      rewrite /step'.
      destruct ρ1.
      rewrite Hsome Hval.
      rewrite /dmap. rewrite -dbind_assoc'.
      rewrite Expval_dbind; last first.
      { apply ex_expval_bounded with r.
        intros [].
        case_match; simpl; try lra.
        naive_solver.
      }
      { intros []. by case_match. }
      apply Expval_le; last first.
      { apply ex_expval_bounded with r. naive_solver. }
      intros [[]].
      split; first apply SeriesC_ge_0'.
      { intros []. apply Rmult_le_pos; real_solver. }
      rewrite dret_id_left'.
      rewrite full_info_lift_osch_lim_exec.
      rewrite Expval_dmap; last first.
      { apply ex_expval_bounded with r.
        intros []. simpl. case_match; naive_solver. }
      { intros []. by case_match. }
      rewrite full_info_stutter_osch_lim_exec.
      rewrite Expval_dmap; last first.
      { apply ex_expval_bounded with r. intros []. simpl. case_match; naive_solver. }
      { intros []. simpl. by case_match. }
      rewrite full_info_inhabitant_lim_exec.
      rewrite Expval_dret.
      simpl.
      case_match eqn:H'; last done.
      pose proof epsilon_correct _ e1. simpl in *.
      destruct (epsilon e1) as [[]].
      simplify_eq.
      apply app_inj_1 in H1 as [K ->]; last by rewrite !insert_length.
      right.
      repeat f_equal.
      assert (<[j:=e0]> l !!j = <[j:=e2]> l!!j) as K'.
      { by f_equal. }
      rewrite !list_lookup_insert in K'; first by simplify_eq.
      all: by eapply lookup_lt_Some.
    - iPureIntro.
      replace (ε1) with (ε1+0 )%NNR; last first.
      { apply nnreal_ext. simpl; lra. }
      rewrite full_info_cons_osch_lim_exec.
      rewrite dret_id_left.
      rewrite /step'.
      destruct ρ1. rewrite Hsome Hval.
      rewrite /dmap. rewrite -dbind_assoc.
      assert (dret σ1 = dret ()≫= λ _, dret σ1) as Hrewrite; last rewrite Hrewrite.
      { by rewrite dret_id_left. }
      eapply ARcoupl_dbind; [done|done| |]; last first.
      + replace (ε1) with (0+ε1 )%NNR; last first.
        { apply nnreal_ext. simpl; lra. }
        eapply up_to_bad_rhs; last done.
        instantiate (1:= λ a b, (λ '(e', σ', efs), R (e', σ', efs) ∧ tapes σ' = m) b ). simpl.
        eapply ARcoupl_mono;[done|done| |done|apply ARcoupl_trivial]; first done.
        * apply dret_mass.
        * by apply: prim_step_mass.
      + intros ?[[]]?.
        rewrite dret_id_left.
        rewrite full_info_lift_osch_lim_exec.
        setoid_rewrite full_info_stutter_osch_lim_exec.
        rewrite dmap_comp.
        setoid_rewrite full_info_inhabitant_lim_exec.
        rewrite dmap_dret.
        apply ARcoupl_dret; try done.
        simpl; split; first done.
        naive_solver.
    - iPureIntro.
      intros.
      destruct!/=.
      split; first done.
      rewrite pair_eq.
      split.
      + apply app_inj_1 in H2 as [K ->]; last by rewrite !insert_length.
        rewrite app_inv_tail_iff.
        assert (<[j:=e'0]> ρ1.1 !!j = <[j:=e']> ρ1.1!!j) as K'.
        { by f_equal. }
        rewrite !list_lookup_insert in K'; first by simplify_eq.
        all: by eapply lookup_lt_Some.
      + destruct σ'0, σ'. simpl in *; naive_solver.
    - iIntros (????).
      destruct!/=.
      case_match eqn :Heqn; last first.
      { exfalso. apply n. eexists (_,_,_). naive_solver. }
      pose proof epsilon_correct _ e0 as H2.
      destruct (epsilon e0) as [[]].
      simpl in *.
      iMod ("H" with "[]") as "H"; first (iPureIntro; naive_solver).
      iModIntro.
      simplify_eq.
      apply app_inj_1 in H2 as [K ->]; last by rewrite !insert_length.
      assert (<[j:=e']> ρ1.1 !!j = <[j:=e1]> ρ1.1!!j) as K'.
      { by f_equal. }
      rewrite !list_lookup_insert in K'; first by simplify_eq.
      all: by eapply lookup_lt_Some.
  Qed.

  Lemma spec_coupl_step_r R (ε1 : nonnegreal) m (ε2 : nonnegreal) ρ1 σ1 Z ε j e:
    reducible e ρ1.2 ->
    ρ1.1 !! j = Some e ->
    (ε1 + ε2 <= ε)%R ->
    pgl (prim_step e ρ1.2) (λ '(e', σ', efs), R(e', σ', efs)/\ tapes σ' = m) ε1->
    (∀ e' σ' efs, ⌜ R (e', σ', efs) /\ tapes σ' = m⌝ ={∅}=∗ spec_coupl σ1 (<[j:=e']>ρ1.1++efs, σ') ε2 Z)%I
    ⊢ spec_coupl σ1 ρ1 ε Z.
  Proof.
    intros.
    iApply spec_coupl_step_r_adv; try done; first naive_solver.
    rewrite Expval_const; last done.
    rewrite prim_step_mass; first lra.
    naive_solver.
  Qed.
  
  (** TODO: state step for LHS *)
(*   Lemma spec_coupl_state_step α σ1 Z (ε ε' : nonnegreal) : *)
(*     α ∈ get_active σ1 → *)
(*     (∃ R, ⌜pgl (state_step σ1 α) R ε⌝ ∗ *)
(*           ∀ σ2 , ⌜R σ2 ⌝ ={∅}=∗ spec_coupl σ2 ε' Z) *)
(*     ⊢ spec_coupl σ1 (ε + ε') Z. *)
(*   Proof. *)
(*     iIntros (Hin) "(%R&%&H)". *)
(*     iApply spec_coupl_rec'. *)
(*     iExists R, (state_step σ1 α), ε, (λ _, ε'). *)
(*     repeat iSplit; try done. *)
(*     - iPureIntro. *)
(*       simpl in *. *)
(*       rewrite elem_of_elements elem_of_dom in Hin. *)
(*       destruct Hin. *)
(*       by eapply state_step_sch_erasable. *)
(*     - iPureIntro; eexists _; done. *)
(*     - iPureIntro. rewrite Expval_const; last done. rewrite state_step_mass; [simpl;lra|done].  *)
(*   Qed. *)

(*   Lemma spec_coupl_iterM_state_adv_comp N α σ1 Z (ε : nonnegreal) : *)
(*     (α ∈ get_active σ1 -> *)
(*      (∃ R ε1 (ε2 : _ -> nonnegreal), *)
(*         ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗ *)
(*         ⌜ (ε1 + Expval (iterM N (λ σ, state_step σ α) σ1) ε2 <= ε)%R ⌝ ∗ *)
(*         ⌜pgl (iterM N (λ σ, state_step σ α) σ1) R ε1⌝ ∗ *)
(*         ∀ σ2, ⌜ R σ2 ⌝ ={∅}=∗ spec_coupl σ2 (ε2 σ2) Z) *)
(*       ⊢ spec_coupl σ1 ε Z)%I. *)
(*   Proof. *)
(*     iIntros (Hin) "(%R & %ε1 & %ε2 & % & %Hε & % & H)". *)
(*     iApply spec_coupl_rec'. *)
(*     iExists R, _, ε1, ε2. *)
(*     repeat iSplit; try done. *)
(*     - iPureIntro. *)
(*       simpl in *. *)
(*       rewrite elem_of_elements elem_of_dom in Hin. *)
(*       destruct Hin. *)
(*       by eapply iterM_state_step_sch_erasable. *)
(*   Qed.  *)
  
(*   Lemma spec_coupl_state_adv_comp α σ1 Z (ε : nonnegreal) : *)
(*     (α ∈ get_active σ1 -> *)
(*      (∃ R ε1 (ε2 : _ -> nonnegreal), *)
(*         ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗ *)
(*         ⌜ (ε1 + Expval (state_step σ1 α) ε2 <= ε)%R ⌝ ∗ *)
(*         ⌜pgl (state_step σ1 α) R ε1⌝ ∗ *)
(*         ∀ σ2, ⌜ R σ2 ⌝ ={∅}=∗ spec_coupl σ2 (ε2 σ2) Z) *)
(*       ⊢ spec_coupl σ1 ε Z)%I. *)
(*   Proof. *)
(*     iIntros (Hin) "(%R & %ε1 & %ε2 & % & %Hε & % & H)". *)
(*     iApply (spec_coupl_iterM_state_adv_comp 1%nat); first done. *)
(*     repeat iExists _. simpl. rewrite dret_id_right. *)
(*     by repeat iSplit. *)
(*   Qed. *)
  

  (** * One step prog coupl *)

  Definition prog_coupl e1 σ1 ρ1 ε Z : iProp Σ :=
    (∃ (S : (expr con_prob_lang * state con_prob_lang * list (expr con_prob_lang)) -> (full_info_state * cfg con_prob_lang) -> Prop)
       (osch : full_info_oscheduler)
       (ε1:nonnegreal) (X2 : full_info_state * cfg con_prob_lang -> nonnegreal) (r:R),
           ⌜reducible e1 σ1⌝ ∗
           ⌜ ∀ x, (X2 x <= r)%R ⌝ ∗
           ⌜ (ε1 + Expval (osch_lim_exec osch ([], ρ1)) X2 <= ε)%R⌝ ∗
           ⌜ ARcoupl (prim_step e1 σ1) (osch_lim_exec osch ([], ρ1)) S ε1 ⌝ ∗
           ⌜ ∀ x1 x2 l y1 y2, S x1 (l, y1) -> S x2 (l, y2) -> x1 = x2 /\ y1 =y2 ⌝ ∗
           (∀ e2 σ2 efs l ρ2, ⌜S (e2, σ2, efs) (l, ρ2)⌝ ={∅}=∗
                         Z e2 σ2 efs ρ2 (X2 (l, ρ2)) )
       )%I.

  Lemma prog_coupl_mono_err e σ ρ Z ε ε':
    (ε<=ε')%R -> prog_coupl e σ ρ ε Z -∗ prog_coupl e σ ρ ε' Z.
  Proof.
    iIntros (?) "(%&%&%&%&%&%&%&%&%&%&H)".
    repeat iExists _.
    repeat iSplit; last first; try done.
    iPureIntro.
    etrans; exact.
  Qed.

  Lemma prog_coupl_strong_mono e1 σ1 ρ1 Z1 Z2 ε :
    (∀ e2 σ2 ρ2 ε' efs, ⌜∃ σ, (prim_step e1 σ (e2, σ2, efs) > 0)%R⌝ ∗ Z1 e2 σ2 efs ρ2 ε' -∗ Z2 e2 σ2 efs ρ2 ε') -∗
    prog_coupl e1 σ1 ρ1 ε Z1 -∗ prog_coupl e1 σ1 ρ1 ε Z2.
  Proof.
    iIntros "Hm (%&%&%&%&%&%&%&%&%Hcoupl&%&H) /=".
    rewrite /prog_coupl.
    apply ARcoupl_pos_R in Hcoupl.
    iExists _, _, _, _, _.
    repeat iSplit; try done.
    - iPureIntro. intros [[??]?] [[??]?]???.
      intros [?[??]][?[??]].
      naive_solver.
    - simpl.
      iIntros (?????(?&?&?)).
      iApply "Hm". iMod ("H" with "[//]").
      iFrame. iPureIntro. naive_solver.
  Qed.
  
  Lemma prog_coupl_mono e1 σ1 ρ1 Z1 Z2 ε :
    (∀ e2 σ2 efs ρ2 ε', Z1 e2 σ2 efs ρ2 ε' -∗ Z2 e2 σ2 efs ρ2 ε') -∗
    prog_coupl e1 σ1 ρ1 ε Z1 -∗ prog_coupl e1 σ1 ρ1 ε Z2.
  Proof.
    iIntros "Hm".
    rewrite /prog_coupl.
    iIntros "(%&%&%&%&%&%&%&%&%&%&H)".
    repeat iExists _; repeat iSplit; try done.
    iIntros. iApply "Hm". by iApply "H".
  Qed.
  
  Lemma prog_coupl_strengthen e1 σ1 ρ1 Z ε :
    prog_coupl e1 σ1 ρ1 ε Z -∗
    prog_coupl e1 σ1 ρ1 ε (λ e2 σ2 efs ρ2 ε',
                             ⌜(∃ σ, (prim_step e1 σ (e2, σ2, efs) > 0)%R)⌝ ∧ Z e2 σ2 efs ρ2 ε').
  Proof.
    iIntros "(%&%&%&%&%&%&%&%&%Hcoupl&%&H) /=".
    rewrite /prog_coupl.
    apply ARcoupl_pos_R in Hcoupl.
    iExists _, _, _, _, _.
    repeat iSplit; try done.
    - iPureIntro. intros [[??]?] [[??]?]???.
      intros [?[??]][?[??]].
      naive_solver.
    - simpl.
      iIntros (?????(?&?&?)).
      iMod ("H" with "[//]") as "$".
      iPureIntro. naive_solver.
  Qed.

  Lemma prog_coupl_ctx_bind K `{!ConLanguageCtx K} e1 σ1 ρ1 Z ε:
    to_val e1 = None ->
    prog_coupl e1 σ1 ρ1 ε (λ e2 σ2 efs ρ2 ε', Z (K e2) σ2 efs ρ2 ε') -∗ prog_coupl (K e1) σ1 ρ1 ε Z.
  Proof.
    iIntros (Hv) "H".
    (* iDestruct (prog_coupl_strengthen with "[][$]") as "H". *)
    (* { iModIntro. by iIntros. } *)
    iDestruct "H" as "(%R&%osch&%ε1&%X2&%r&%&%&%&%&%Hinj&H)".
    (** (classical) inverse of context [K] *)
    destruct (partial_inv_fun K) as (Kinv & HKinv).
    assert (∀ e, Kinv (K e) = Some e) as HKinv3.
    { intro e.
      destruct (Kinv (K e)) eqn:Heq;
        eapply HKinv in Heq; by simplify_eq. }
    (* set (ε2' := (λ '(e, σ, efs), from_option (λ e', ε2 (e', σ, efs)) 1%NNR (Kinv e))). *)
    (* assert (∀ e2 σ2 efs, ε2' (K e2, σ2, efs) = ε2 (e2, σ2, efs)) as Hε2'. *)
    (* { intros. rewrite /ε2' HKinv3 //. } *)
    rewrite /prog_coupl.
    iExists (λ '(e2, σ2, efs) ρ2, ∃ e2', e2 = K e2' /\ R (e2', σ2, efs) ρ2), osch, ε1, X2, r.
    repeat iSplit; try iPureIntro.
    - by apply reducible_fill.
    - done.
    - done.
    - rewrite fill_dmap //.
      rewrite /dmap.
      rewrite -(dret_id_right (osch_lim_exec _ _)) //.
      eapply (ARcoupl_dbind' _ nnreal_zero); last done; [done|done|simpl; lra|].
      iIntros ([[??]?]??).
      apply ARcoupl_dret; naive_solver.
    - simpl. intros [[??]?][[??]?]???[?[? R1]][?[? R2]]. simplify_eq.
      pose proof Hinj _ _ _ _ _ R1 R2 as [??]. by simplify_eq.
    - iIntros (?????(?&->&?)).
      by iApply "H".
  Qed.
  
  Lemma prog_coupl_reducible e σ ρ Z ε :
    prog_coupl e σ ρ ε Z -∗ ⌜reducible e σ⌝.
  Proof. by iIntros "(%&%&%&%&%&%&?)". Qed.

  
  Lemma prog_coupl_step_l_dret_adv (ε ε1:nonnegreal) (X2: _ -> nonnegreal) R e1 σ1 ρ1 Z :
    (ε1 + Expval (prim_step e1 σ1 ) X2 <= ε)%NNR →
    reducible e1 σ1 →
    (exists r, ∀ ρ, (X2 ρ <= r)%R) ->
    pgl (prim_step e1 σ1) R ε1 →
    (∀ e2 σ2 efs, ⌜R (e2, σ2, efs)⌝ ={∅}=∗ Z e2 σ2 efs ρ1 (X2 (e2, σ2, efs)))
    ⊢ prog_coupl e1 σ1 ρ1 ε Z.
  Proof.
    iIntros (Hineq Hred [r Hbound] Hpgl) "H".
    rewrite /prog_coupl.
    pose (n:=length ρ1.1).
    iExists (λ ρ '(l, ρ'),
               R ρ /\ ρ' = ρ1 /\ l=[(cfg_to_cfg' ρ1, n+ encode_nat ρ)%nat; (cfg_to_cfg' ρ1, n)]
            ).
    iExists (full_info_cons_osch (λ _, dmap (λ x, n+encode_nat x)%nat (prim_step e1 σ1))
                                 (λ _, full_info_stutter_osch full_info_inhabitant)
            ).
    iExists ε1, (λ '(l, ρ'),
                   match l!!0%nat with
                   | Some p =>
                       match decode_nat (p.2-n)%nat with
                       | Some x => X2 x
                       | None => nnreal_zero
                       end
                   | None => nnreal_zero
                   end
                ).
    iExists r.
    assert (0<=r).
    { trans (X2 inhabitant); naive_solver. }
    repeat iSplit.
    - done.
    - iPureIntro. intros [??]. by repeat case_match.
    - iPureIntro.
      etrans; last exact.
      apply Rplus_le_compat_l.
      rewrite full_info_cons_osch_lim_exec.
      rewrite Expval_dbind; last first.
      { eapply ex_expval_bounded with r.
        intros [??]. by repeat case_match.
      }
      { intros [??]. by repeat case_match. }
      rewrite Expval_dmap; last first.
      { apply ex_expval_bounded with r.
        intros [[??]?]. split.
        - apply Expval_ge_0'.
          intros [??]. by repeat case_match.
        - Local Opaque full_info_lift_osch.
          simpl.
          rewrite out_of_bounds_step'; last first.
          { rewrite /n. lia. }
          rewrite dret_id_left.
          rewrite full_info_lift_osch_lim_exec full_info_stutter_osch_lim_exec full_info_inhabitant_lim_exec.
          rewrite Expval_dmap; last first.
          + simpl. 
            apply ex_expval_bounded with r.
            intros [??]. simpl; by repeat case_match.
          + intros [??]. by repeat case_match.
          + rewrite dmap_dret. rewrite Expval_dret. simpl.
            by case_match.
      }
      { intros. apply Expval_ge_0'. intros [??]. by case_match.
      }
      apply Expval_le; last first.
      { apply ex_expval_bounded with r. naive_solver. }
      intros [[e s]l].
      simpl.
      rewrite out_of_bounds_step'; last (rewrite /n; lia).
      rewrite dret_id_left.
      rewrite full_info_lift_osch_lim_exec full_info_stutter_osch_lim_exec full_info_inhabitant_lim_exec.
      rewrite !dmap_dret Expval_dret.
      simpl. replace (_+_-_)%nat with (encode_nat (e, s, l)); last first.
      { simpl. lia. }
      rewrite decode_encode_nat. done.
    - rewrite full_info_cons_osch_lim_exec.
      rewrite /dmap -!dbind_assoc.
      rewrite -{1}(dret_id_right (prim_step _ _)).
      iPureIntro.
      replace (ε1) with (ε1+0)%NNR; last (apply nnreal_ext; simpl; lra).
      eapply (ARcoupl_dbind _ _ _ _ (λ x y, x=y /\ R x)); [try done..|]; last first.
      { replace (ε1) with (0+ε1)%NNR; last (apply nnreal_ext; simpl; lra).
        eapply up_to_bad_lhs; last done.
        eapply ARcoupl_mono; [done|done| |done|apply ARcoupl_eq].
        intros. naive_solver.
      }
      intros [[e s]l][[??]?][??].
      simplify_eq.
      rewrite dret_id_left out_of_bounds_step'; last (rewrite /n; lia).
      rewrite dret_id_left full_info_lift_osch_lim_exec full_info_stutter_osch_lim_exec full_info_inhabitant_lim_exec.
      rewrite !dmap_dret.
      by apply ARcoupl_dret.
    - iPureIntro. intros x1 x2 ???(?&?&?)(?&?&?).
      subst. simplify_eq.
      assert (encode_nat x1 = encode_nat x2) as H' by lia.
      apply encode_nat_inj in H'. subst. naive_solver.
    - iIntros (e s l ??(?&->&->)).
      simpl.
      replace (_+_-_)%nat with (encode_nat (e, s, l)); last first.
      { simpl. lia. }
      rewrite decode_encode_nat. by iApply "H".
      Local Transparent full_info_lift_osch.
  Qed.
  
  Lemma prog_coupl_step_l_dret ε1 ε2 ε R e1 σ1 ρ1 Z :
    ε = (ε1 + ε2)%NNR →
    reducible e1 σ1 →
    pgl (prim_step e1 σ1) R ε1 →
    (∀ e2 σ2 efs, ⌜R (e2, σ2, efs)⌝ ={∅}=∗ Z e2 σ2 efs ρ1 ε2)
    ⊢ prog_coupl e1 σ1 ρ1 ε Z.
  Proof.
    iIntros (Heq Hred ?) "?". iApply (prog_coupl_step_l_dret_adv _ ε1 (λ _, ε2)); try done; last naive_solver.
    rewrite Expval_const; try done.
    rewrite prim_step_mass.
    { rewrite Rmult_1_r. rewrite Heq. simpl. lra. }
    apply Hred.
  Qed.
 
  Lemma prog_coupl_step_l e1 σ1 ρ1 ε Z :
    reducible e1 σ1 →
    (∀ e2 σ2 efs, ⌜prim_step e1 σ1 (e2, σ2, efs) > 0⌝ ={∅}=∗ Z e2 σ2 efs ρ1 ε)
    ⊢ prog_coupl e1 σ1 ρ1 ε Z.
  Proof.
    iIntros (?) "H".
    iApply (prog_coupl_step_l_dret 0%NNR ε); [|done|..].
    { apply nnreal_ext => /=. lra. }
    { by apply pgl_pos_R, pgl_trivial. }
    simpl.
    iIntros (??? (_ & ?)).
    by iApply "H".
  Qed.

End modalities.

(** * The weakest precondition  *)
Definition wp_pre `{!foxtrotWpGS con_prob_lang Σ}
    (wp : coPset -d> expr con_prob_lang -d> (val con_prob_lang -d> iPropO Σ) -d> iPropO Σ) :
     coPset -d> expr con_prob_lang -d> (val con_prob_lang -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
  (∀ σ1 ρ1 ε1,
      state_interp σ1 ∗ spec_interp ρ1 ∗ err_interp ε1 ={E, ∅}=∗
      spec_coupl σ1 ρ1 ε1 (λ σ2 ρ2 ε2,
        match to_val e1 with
        | Some v => |={∅, E}=> state_interp σ2 ∗ spec_interp ρ2 ∗ err_interp ε2 ∗ Φ v
        | None =>
            prog_coupl e1 σ2 ρ2 ε2 (λ e3 σ3 efs ρ3 ε3,
                ▷ spec_coupl σ3 ρ3 ε3 (λ σ4 ρ4 ε4,
                   |={∅, E}=> state_interp σ4 ∗ spec_interp ρ4 ∗ err_interp ε4 ∗
                             wp E e3 Φ ∗[∗ list] ef ∈efs, wp ⊤ ef fork_post))
      end))%I.


Local Instance wp_pre_contractive `{!foxtrotWpGS con_prob_lang Σ} : Contractive (wp_pre).
Proof.
  rewrite /wp_pre /= => n wp wp' Hwp E e1 Φ /=.
  do 8 f_equiv.
  apply least_fixpoint_ne_outer; [|done].
  intros Ψ [[e' σ'] ε'].
  rewrite /spec_coupl_pre.
  do 3 f_equiv.
  rewrite /prog_coupl.
  do 27 f_equiv.
  f_contractive.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [[??]?].
  rewrite /spec_coupl_pre.
  repeat f_equiv; apply Hwp.
Qed.


Local Definition wp_def `{!foxtrotWpGS con_prob_lang Σ} :
  Wp (iProp Σ) (expr con_prob_lang) (val con_prob_lang) () :=
  {| wp := λ _ : (), fixpoint (wp_pre); wp_default := () |}.
Local Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp' := wp_aux.(unseal).
Global Arguments wp' {Σ _}.
Global Existing Instance wp'.
Local Lemma wp_unseal `{!foxtrotWpGS con_prob_lang Σ} : wp =
  (@wp_def Σ _).(wp).
Proof. rewrite -wp_aux.(seal_eq) //. Qed.



Section wp.
Context `{!foxtrotWpGS con_prob_lang Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val con_prob_lang → iProp Σ.
Implicit Types v : val con_prob_lang.
Implicit Types e : expr con_prob_lang.
Implicit Types σ : state con_prob_lang.
Implicit Types ρ : cfg con_prob_lang.

(* Weakest pre *)
Lemma wp_unfold E e Φ s :
  WP e @ s; E {{ Φ }} ⊣⊢ wp_pre (wp (PROP:=iProp Σ) s) E e Φ.
Proof. rewrite wp_unseal. apply (fixpoint_unfold wp_pre). Qed.

Global Instance wp_ne E e n s :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp (PROP:=iProp Σ) s E e).
Proof.
  revert e. induction (lt_wf n) as [n _ IH]=> e Φ Ψ HΦ.
  rewrite !wp_unfold /wp_pre /=.
  do 8 f_equiv.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [? [? ?]]. rewrite /spec_coupl_pre /prog_coupl.
  do 31 f_equiv.
  f_contractive_fin.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [? [? ?]]. rewrite /spec_coupl_pre.
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
  do 8 f_equiv.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [? [? ?]]. rewrite /spec_coupl_pre.
  rewrite /prog_coupl.
  do 30 f_equiv.
  f_contractive.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [? [? ?]]. rewrite /spec_coupl_pre.
  repeat f_equiv.
Qed.

Lemma wp_value_fupd' E Φ v s : (|={E}=> Φ v) ⊢ WP of_val v @ s; E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre to_of_val.
  iIntros "H" (???) "(?&?&?)".
  iApply spec_coupl_ret.
  iMod "H". iFrame.
  iApply fupd_mask_subseteq.
  set_solver.
Qed.

Lemma wp_strong_mono E1 E2 e Φ Ψ s :
  E1 ⊆ E2 →
  WP e @ s; E1 {{ Φ }} -∗
 (∀ σ1 ρ1 ε1 v,
     state_interp σ1 ∗ spec_interp ρ1 ∗ err_interp ε1 ∗ Φ v ={E2, ∅}=∗
     spec_coupl σ1 ρ1 ε1 (λ σ2 ρ2 ε2,
          |={∅, E2}=> state_interp σ2 ∗ spec_interp ρ2 ∗ err_interp ε2 ∗ Ψ v)) -∗
  WP e @ s; E2 {{ Ψ }}.
Proof.
  iIntros (HE) "H HΦ". iLöb as "IH" forall (e E1 E2 HE Φ Ψ s).
  rewrite !wp_unfold /wp_pre /=.
  iIntros (σ1 ρ1 ε1) "(Hσ & Hs & Hε)".
  iSpecialize ("H" with "[$]").
  iMod (fupd_mask_subseteq E1) as "Hclose"; [done|].
  iMod "H"; iModIntro.
  iApply (spec_coupl_bind with "[-H] H").
  iIntros (???) "H". simpl.
  case_match eqn:Hv.
  { iApply fupd_spec_coupl.
    iMod "H" as "(?&?&?)".
    iMod "Hclose" as "_".
    iMod ("HΦ" with "[$]").
    iModIntro.
    iApply (spec_coupl_bind with "[][$]").
    iIntros (???) "Hσ".
    by iApply spec_coupl_ret. }
  iApply spec_coupl_ret.
  iApply (prog_coupl_mono with "[HΦ Hclose] H").
  iIntros (e2 σ3 efs ρ3 ε3) "H !>".
  iApply (spec_coupl_mono with "[HΦ Hclose] H").
  iIntros (σ4 ρ4  ε4) "> ($ & $ & $ & H & Hefs)".
  iMod "Hclose" as "_".
  iModIntro. iFrame.
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
  iIntros (????) "(?&?&?&?)".
  iApply spec_coupl_ret.
  iApply fupd_mask_intro; first set_solver.
  iIntros ">?".
  iApply "Hw". iFrame.
Qed.

Lemma spec_coupl_wp E e Φ s :
  (∀ σ1 ρ1 ε1, state_interp σ1 ∗ spec_interp ρ1 ∗ err_interp ε1 ={E, ∅}=∗
            spec_coupl σ1 ρ1 ε1
              (λ σ2 ρ2 ε2, |={∅, E}=> state_interp σ2 ∗ spec_interp ρ2 ∗ err_interp ε2 ∗ WP e @ s ; E {{Φ}})) -∗
  WP e @ s ; E {{ Φ }}.
Proof.
  iIntros "H".
  erewrite wp_unfold. rewrite /wp_pre.
  iIntros (???) "(?&?&?)". 
  iSpecialize ("H" with "[$]").
  iMod "H". iModIntro.
  iApply (spec_coupl_bind with "[][$]").
  iIntros (???) "H".
  iApply fupd_spec_coupl.
  iMod "H" as "(?&?&?&H)".
  rewrite wp_unfold/wp_pre.
  iApply "H". iFrame.
Qed. 

Lemma fupd_wp E e Φ s: (|={E}=> WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre.
  iIntros "H" (???) "(?&?&?)".
  destruct (to_val e) as [v|] eqn:?.
  { by iMod ("H" with "[$]"). }
  by iMod ("H" with "[$]").
Qed.

Lemma wp_fupd E e Φ s : WP e @ s; E {{ v, |={E}=> Φ v }} ⊢ WP e @ s; E {{ Φ }}.
Proof.
  iIntros "H".
  iApply (wp_strong_mono E with "H"); [done|].
  iIntros (????) "(? & ? & ? & >?)".
  iApply spec_coupl_ret. iFrame.
  iApply fupd_mask_intro_subseteq; set_solver.
Qed.

Lemma wp_atomic E1 E2 e Φ `{!Atomic StronglyAtomic e} s :
  (|={E1,E2}=> WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros "H". rewrite !wp_unfold /wp_pre.
  iIntros (σ1 ρ1 ε1) "(Hσ & Hs & Hε)".
  iDestruct ("H" with "[$]") as ">> H".
  iModIntro.
  iApply (spec_coupl_mono with "[] H").
  iIntros (σ2 ρ2 ε2) "H".
  destruct (to_val e) as [v|] eqn:?.
  { iDestruct "H" as "> ($ & $ & $ & $)". }
  iDestruct (prog_coupl_strengthen with "H") as "H".
  iApply (prog_coupl_mono with "[] H").
  iIntros (?????) "[[% %Hstep] H] !>".
  iApply (spec_coupl_bind with "[] H").
  iIntros (???) "H".
  iApply fupd_spec_coupl.
  iMod "H" as "(Hσ & Hρ & Hε & H & Hefs)".
  rewrite !wp_unfold /wp_pre.
  destruct (to_val e2) as [v2|] eqn:He2.
  + iMod ("H" with "[$]") as "H". iModIntro.
    iApply (spec_coupl_mono with "[Hefs] H").
    iIntros (???) "> ($ & $ & $ & >H)".
    rewrite -(of_to_val e2 v2) //. iFrame.
    iApply wp_value_fupd'.
    iApply fupd_mask_intro_subseteq; [|done].
    set_solver.
  + iMod ("H" with "[$]") as "H". iModIntro.
    iApply (spec_coupl_mono with "[Hefs] H").
    iIntros (???) "H".
    iDestruct (prog_coupl_reducible with "H") as %[ρ Hr].
    pose proof (atomic _ _ _ _ Hstep) as [? Hval].
    apply val_stuck in Hr. simplify_eq.
Qed.

Lemma wp_step_fupd E1 E2 e P Φ s :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> P) -∗ WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ s; E1 {{ Φ }}.
Proof.
  rewrite !wp_unfold /wp_pre. iIntros (-> ?) "HR H".
  iIntros (σ1 ρ1 ε1) "Hs". iMod "HR".
  iMod ("H" with "Hs") as "H".
  iModIntro.
  iApply (spec_coupl_mono with "[HR] H").
  iIntros (σ2 ρ2 ε2) "H".
  iApply (prog_coupl_mono with "[HR] H").
  iIntros (e3 σ3 efs ρ3 ε3) "H !>".
  iApply (spec_coupl_mono with "[HR] H").
  iIntros (σ4 ρ4 ε4) "H".
  iMod "H" as "($ & $ & $ & H & Hefs)".
  iMod "HR". iFrame.
  iApply (wp_strong_mono E2 with "H"); first done.
  iIntros "!>" (????) "(? & ? & ? & H)".
  iApply spec_coupl_ret.
  iMod ("H" with "[$]").
  iFrame.
  iApply fupd_mask_intro_subseteq; set_solver.
Qed.

Lemma wp_bind K `{!ConLanguageCtx K} E e Φ s :
  WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }} ⊢ WP K e @ s; E {{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ s). rewrite !wp_unfold /wp_pre.
  iIntros (σ1 ρ1 ε1) "Hs".
  iMod ("H" with "[$]") as "H".
  iApply (spec_coupl_bind with "[] H").
  iIntros (σ2 ρ2 ε2) "H".
  destruct (to_val e) as [v|] eqn:He.
  { iApply fupd_spec_coupl.
    iMod "H" as "(Hσ & Hs & Hε & H)".
    apply of_to_val in He as <-.
    rewrite wp_unfold /wp_pre.
    by iMod ("H" with "[$]"). }
  rewrite fill_not_val/=; last done. 
  iApply spec_coupl_ret.
  iApply prog_coupl_ctx_bind; first done.
  iApply (prog_coupl_mono with "[] H").
  iIntros (e3 σ3 efs ρ3 ε3) "H !>".
  iApply (spec_coupl_mono with "[] H").
  iIntros (σ4 ρ4 ε4) "H".
  iMod "H" as "($ & $ & $ & H & $)".
  iModIntro.
  by iApply "IH".
Qed.

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
  iIntros (????) "(? & ? & ? & ?)".
  iApply spec_coupl_ret.
  iFrame.
  iApply fupd_mask_intro_subseteq; set_solver.
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
  Context `{!foxtrotWpGS con_prob_lang Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val con_prob_lang → iProp Σ.
  Implicit Types v : val con_prob_lang.
  Implicit Types e : expr con_prob_lang.

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

End proofmode_classes.

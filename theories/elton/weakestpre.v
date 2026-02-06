From Stdlib Require Export Reals Psatz.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export lib.fixpoint_mono big_op.
From iris.prelude Require Import options.

From clutch.bi Require Export weakestpre.
From clutch.prelude Require Import stdpp_ext iris_ext NNRbar.
From clutch.prob Require Export couplings distribution graded_predicate_lifting.
From clutch.delay_prob_lang Require Import lang urn_subst metatheory urn_erasable preserve_atomicity.
From clutch.common Require Export language.

(** This file contains the definition of the weakest precondition of elton *)
Import uPred.

Local Open Scope NNR_scope.
#[global] Hint Resolve cond_nonneg : core.

(** We for now specialize the wp to delay_prob_lang, since we allow 
    big state steps which are sch_erasable to tape oblivious schedulers,
    a kind of schedulers specific to the language
*)

Class eltonWpGS (Λ : language) (Σ : gFunctors) := EltonWpGS {
  eltonWpGS_invGS :: invGS_gen HasNoLc Σ;
  state_interp : state Λ → iProp Σ;
  err_interp : nonnegreal → iProp Σ;
}.
Global Opaque eltonWpGS_invGS.
Global Arguments EltonWpGS {Λ Σ}.
Canonical Structure NNRO := leibnizO nonnegreal.



Section rupd.
  Context `{H:!eltonWpGS d_prob_lang Σ}.
  (* Do we need to open invariants? *)
  Definition rupd_def (P: val d_prob_lang -> Prop) Q v : iProp Σ:=
    (∀ σ1, state_interp σ1 -∗ 
           ⌜∀ f, (urns_f_distr (urns σ1) f > 0)%R -> ∃ v', urn_subst_val f v = Some v' /\ P v'⌝ ∗ (Q ∗ state_interp σ1)).
  
  Local Definition rupd_aux : seal (@rupd_def). Proof. by eexists. Qed.
  Definition rupd := rupd_aux.(unseal).
  Lemma rupd_unseal : rupd = rupd_def.
  Proof. rewrite -rupd_aux.(seal_eq) //. Qed.
  
End rupd. 


(* Definition total_weight (lis:list(gset nat)) := *)
(*   list_sum (size <$> lis). *)

(* Definition list_weighted_distr' (lis:list (gset nat)) i:=  *)
(*   if (bool_decide (total_weight lis=0)%nat) then 0%R *)
(*   else match lis!!i with *)
(*        | Some s => ((size s)/(total_weight lis))%R *)
(*        | None => 0%R *)
(*        end. *)
  
Section modalities.
  Context `{eltonWpGS d_prob_lang Σ}.
  Implicit Types ε : nonnegreal.

  (** This prolly need to be changed to allow value promotion for easier computation? *)
  Definition state_step_coupl_pre Z Φ : (expr d_prob_lang * state d_prob_lang * nonnegreal -> iProp Σ) :=
    (λ x,
      let '(e, σ1, ε) := x in
      ⌜(1<=ε)%R⌝ ∨
        Z e σ1 ε ∨
        (∀ (ε':nonnegreal), ⌜(ε<ε')%R⌝ -∗ Φ (e, σ1, ε')) ∨
        (∃ μ (ε2 :_ -> nonnegreal),
            ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗
            ⌜ (Expval (μ) ε2 <= ε)%R ⌝ ∗
            ⌜urn_erasable μ σ1.(urns)⌝ ∗
            ∀ m', |={∅}=> Φ (e, state_upd_urns (λ _, m') σ1, ε2 m')
        ) ∨
        (∃ (K:ectx (d_prob_ectx_lang)) (v: val d_prob_lang) v',
            ⌜e = fill K (Val v)⌝ ∗
            ⌜∀ f, (urns_f_distr (urns σ1) f > 0)%R -> urn_subst_val f v = Some v' ⌝ ∗
            (|={∅}=> Φ (fill K (Val v'), σ1, ε))
        )
    )%I.

    
  #[local] Instance state_step_coupl_pre_ne Z Φ :
    NonExpansive (state_step_coupl_pre Z Φ).
  Proof.
    rewrite /state_step_coupl_pre.
    intros ?[[]?][[]?][[[=][=]][=]]. by simplify_eq.
  Qed.

  #[local] Instance state_step_coupl_pre_mono Z : BiMonoPred (state_step_coupl_pre Z).
  Proof.
    split; [|apply _].
    iIntros (Φ Ψ HNEΦ HNEΨ) "#Hwand".
    iIntros ([[]?]) "[H|[?|[H|[(%&%&%&%&%&H)|(%&%&%&%&%&H)]]]]".
    - by iLeft.
    - iRight; by iLeft.
    - iRight; iRight; iLeft.
      iIntros (??).
      iApply "Hwand".
      by iApply "H".
    - do 3 iRight. iLeft.
      repeat iExists _; repeat (iSplit; [done|]).
      iIntros (x).
      iDestruct ("H" $! x) as "H".
      iApply "Hwand".
      by iApply "H".
    - repeat iRight.
      iExists _, _, _. repeat iSplit; try done.
      iFrame.
      by iApply "Hwand".
  Qed.

  Definition state_step_coupl' Z := bi_least_fixpoint (state_step_coupl_pre Z).
  Definition state_step_coupl e σ ε Z:= state_step_coupl' Z (e, σ, ε).

  Lemma state_step_coupl_unfold e σ1 ε Z :
    state_step_coupl e σ1 ε Z ≡
      (⌜(1 <= ε)%R⌝ ∨
         (Z e σ1 ε) ∨
         (∀ ε', ⌜(ε<ε')%R⌝ -∗ state_step_coupl e σ1 ε' Z) ∨
         (∃ μ (ε2 :_ -> nonnegreal),
            ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗
            ⌜ (Expval (μ) ε2 <= ε)%R ⌝ ∗
            ⌜urn_erasable μ σ1.(urns)⌝ ∗
            ∀ m', |={∅}=> state_step_coupl e (state_upd_urns (λ _, m') σ1) (ε2 m') Z
         ) ∨
         (∃ (K:ectx (d_prob_ectx_lang)) (v: val d_prob_lang) v',
            ⌜e = fill K (Val v)⌝ ∗
            ⌜∀ f, (urns_f_distr (urns σ1) f > 0)%R -> urn_subst_val f v = Some v' ⌝ ∗
            (|={∅}=> state_step_coupl (fill K (Val v'))  σ1 ε Z)
        )
      )%I.
  Proof. rewrite /state_step_coupl /state_step_coupl' least_fixpoint_unfold //. Qed.

  Lemma state_step_coupl_ret_err_ge_1 e σ1 Z (ε : nonnegreal) :
    (1 <= ε)%R → ⊢ state_step_coupl e σ1 ε Z.
  Proof. iIntros. rewrite state_step_coupl_unfold. by iLeft. Qed.

  Lemma state_step_coupl_ret e σ1 Z ε :
    Z e σ1 ε -∗ state_step_coupl e σ1 ε Z.
  Proof. iIntros. rewrite state_step_coupl_unfold. by iRight; iLeft. Qed.

  Lemma state_step_coupl_ampl e σ1 Z ε:
    (∀ ε', ⌜(ε<ε')%R⌝ -∗ state_step_coupl e σ1 ε' Z) -∗ state_step_coupl e σ1 ε Z.
  Proof. iIntros. rewrite state_step_coupl_unfold.
         do 2 iRight; by iLeft.
  Qed. 

  Lemma state_step_coupl_ampl' e σ1 Z ε:
    (∀ ε', ⌜(ε<ε'<1)%R⌝ -∗ state_step_coupl e σ1 ε' Z) -∗ state_step_coupl e σ1 ε Z.
  Proof.
    iIntros "H".
    iApply state_step_coupl_ampl.
    iIntros (ε' ?).
    destruct (Rlt_or_le ε' 1)%R.
    - iApply "H". iPureIntro. lra.
    - by iApply state_step_coupl_ret_err_ge_1. 
  Qed.

  Lemma state_step_coupl_rec e σ1 (ε : nonnegreal) Z :
    (∃ μ (ε2 :_ -> nonnegreal),
            ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗
            ⌜ (Expval (μ) ε2 <= ε)%R ⌝ ∗
            ⌜urn_erasable μ σ1.(urns)⌝ ∗
            ∀ m', |={∅}=> state_step_coupl e (state_upd_urns (λ _, m') σ1) (ε2 m') Z
        )
    ⊢ state_step_coupl e σ1 ε Z.
  Proof. iIntros "H". rewrite state_step_coupl_unfold. do 3 iRight. iLeft. done. Qed.

  Lemma state_step_coupl_value_promote e σ1 (ε : nonnegreal) Z:
     (∃ (K:ectx (d_prob_ectx_lang)) (v: val d_prob_lang) v',
            ⌜e = fill K (Val v)⌝ ∗
            ⌜∀ f, (urns_f_distr (urns σ1) f > 0)%R -> urn_subst_val f v = Some v' ⌝ ∗
            (|={∅}=> state_step_coupl (fill K (Val v')) σ1 ε Z)
     ) ⊢
     state_step_coupl e σ1 ε Z.
  Proof.
    iIntros "H". rewrite state_step_coupl_unfold. repeat iRight. done.
  Qed. 

  Lemma state_step_coupl_rec_complete_split e σ1 (ε : nonnegreal) Z :
    (∃ u s (ε2 :_ -> nonnegreal),
        ⌜s≠∅⌝ ∗ 
        ⌜σ1.(urns) !! u = Some (urn_unif s) ⌝ ∗
        ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗
                    ⌜ (SeriesC (λ x, if bool_decide (x ∈ elements s) then ε2 x else 0%NNR)/ size s <= ε)%R ⌝ ∗
                    (∀ x, ⌜x∈s⌝ ={∅}=∗ state_step_coupl e (state_upd_urns <[u:=urn_unif {[x]}]> σ1) (ε2 x) Z )
    )%I
    ⊢ state_step_coupl e σ1 ε Z.
  Proof.
    iIntros "(%u&%s&%ε2&%Hs&%Hlookup&[%r %]&%Hineq&H)".
    iApply state_step_coupl_rec.
    destruct σ1 as [? us]; simpl; simpl in *.
    iExists _, (λ m, match ClassicalEpsilon.excluded_middle_informative
                             (∃ x, m=<[u:=urn_unif {[x]}]> us /\ x ∈ s) with
                     | left P =>ε2 (epsilon P)%NNR
                     | right _ => 1%NNR
                     end
               ).
    repeat iSplit.
    3:{ iPureIntro. by eapply complete_split_urn_erasable. }
    - iPureIntro.
      exists (Rmax 1 r).
      intros. case_match.
      + etrans; last apply Rmax_r. naive_solver.
      + apply Rmax_l.
    - iPureIntro.
      etrans; last exact.
      rewrite /Expval.
      rewrite /dbind/dbind_pmf{1}/pmf.
      setoid_rewrite <-SeriesC_scal_r.
      rewrite fubini_pos_seriesC'; last first.
      + setoid_rewrite Rmult_assoc.
        setoid_rewrite SeriesC_scal_l.
        apply (ex_seriesC_le _ (λ x, unif_set s x *Rmax 1 r))%R; last by apply ex_seriesC_scal_r.
        intros. split.
        * apply Rmult_le_pos; first done.
          apply SeriesC_ge_0'.
          real_solver.
        * apply Rmult_le_compat_l; first done.
          trans (SeriesC (λ x, if bool_decide (x=(<[u:=urn_unif {[n]}]> us) ) then Rmax 1 r else 0%R)); last (by rewrite SeriesC_singleton).
          apply SeriesC_le; last apply ex_seriesC_singleton.
          intros n'.
          split; first real_solver.
          case_bool_decide; subst.
          -- rewrite dret_1_1; last done. rewrite Rmult_1_l.
             rewrite Rmax_Rle.
             case_match; naive_solver.
          -- rewrite dret_0; first lra. done.
      + intros.
        setoid_rewrite Rmult_assoc.
        apply ex_seriesC_scal_l.
        apply (ex_seriesC_le _ (λ x, if bool_decide (x=(<[u:=urn_unif {[a]}]> us)) then Rmax 1 r else 0)); last apply ex_seriesC_singleton.
        intros. split; first real_solver.
        case_bool_decide.
        * rewrite dret_1_1; last done.
          subst.
          rewrite Rmult_1_l.
          case_match;
            rewrite Rmax_Rle; naive_solver.
        * rewrite dret_0; simpl; try lra. done.
      + intros. real_solver. 
      + right.
        apply SeriesC_ext.
        intros a.
        setoid_rewrite Rmult_assoc.
        rewrite SeriesC_scal_l.
        case_bool_decide as H'.
        * rewrite unif_set_compute; last set_solver.
          rewrite Rmult_comm. f_equal.
          erewrite (SeriesC_ext _ (λ x, if bool_decide (x=(<[u:=urn_unif {[a]}]> us) ) then nonneg (ε2 a) else 0%R)); first by rewrite SeriesC_singleton.
          intros.
          case_bool_decide; subst.
          -- rewrite dret_1_1; last done.
             rewrite Rmult_1_l.
             case_match.
             ++ do 2 f_equal.
                rename select (∃ _, _) into He.
                pose proof epsilon_correct _ He as [He'].
                apply insert_inv in He'.
                assert (∀ x y, urn_unif x = urn_unif y -> x=y) as Hcut.
                { clear. intros. by simplify_eq. }
                apply Hcut in He'.
                set_solver.
             ++ exfalso. 
                apply elem_of_elements in H'. naive_solver.
          -- rewrite dret_0; last done.
             lra.
        * rewrite unif_set_compute'; last set_solver. simpl; lra.
    - iIntros (m').
      case_match.
      + rename select (∃ _, _) into He.
        pose proof epsilon_correct _ He as [H2 ].
        simpl in *.
        iMod ("H" with "[//]").
        by rewrite -H2.
      + by iApply state_step_coupl_ret_err_ge_1.
  Qed. 
        
  (* Lemma state_step_coupl_rec_equiv σ1 (ε : nonnegreal) Z : *)
  (*   (∃ μ (ε2 : state con_prob_lang -> nonnegreal), *)
  (*       ⌜ sch_erasable (λ t _ _ sch, TapeOblivious t sch) μ σ1 ⌝ ∗ *)
  (*       ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗ *)
  (*                   ⌜ (Expval μ ε2 <= ε)%R ⌝ ∗ *)
  (*                   ∀ σ2, |={∅}=> state_step_coupl σ2 (ε2 σ2) Z)%I ⊣⊢ *)
  (*   (∃ R μ (ε1 : nonnegreal) (ε2 : state con_prob_lang -> nonnegreal), *)
  (*       ⌜ sch_erasable (λ t _ _ sch, TapeOblivious t sch) μ σ1 ⌝ ∗ *)
  (*       ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗ *)
  (*                   ⌜ (ε1 + Expval μ ε2 <= ε)%R ⌝ ∗ *)
  (*                   ⌜pgl μ R ε1⌝ ∗ *)
  (*                   ∀ σ2, ⌜ R σ2 ⌝ ={∅}=∗ state_step_coupl σ2 (ε2 σ2) Z)%I. *)
  (* Proof. *)
  (*   iSplit. *)
  (*   - iIntros "H". *)
  (*     iDestruct "H" as "(%μ & %ε2 & % & [%r %] & %Hineq  &H)". *)
  (*     iExists (λ _, True), μ, 0, (λ σ, if bool_decide (μ σ > 0)%R then ε2 σ else 1). *)
  (*     repeat iSplit; first done. *)
  (*     + iPureIntro. exists (Rmax r 1). *)
  (*       intros; case_bool_decide. *)
  (*       * etrans; last apply Rmax_l. done. *)
  (*       * simpl. apply Rmax_r. *)
  (*     + simpl. iPureIntro. rewrite Rplus_0_l. etrans; last exact. *)
  (*       rewrite /Expval. apply Req_le. *)
  (*       apply SeriesC_ext. *)
  (*       intros n. case_bool_decide; first done. *)
  (*       destruct (pmf_pos μ n) as [K|K]. *)
  (*       * exfalso. apply Rlt_gt in K. naive_solver. *)
  (*       * simpl. rewrite -K. lra. *)
  (*     + iPureIntro. by apply pgl_trivial. *)
  (*     + iIntros. case_bool_decide; first done. *)
  (*       by iApply state_step_coupl_ret_err_ge_1. *)
  (*   - iIntros "H". *)
  (*     iDestruct "H" as "(%R & %μ & %ε1 & %ε2 & % & [%r %] & %Hineq & %Hpgl &H)". *)
  (*     iExists μ, (λ σ, if bool_decide(R σ) then ε2 σ else 1). *)
  (*     repeat iSplit; try done. *)
  (*     + iPureIntro. exists (Rmax r 1). *)
  (*       intros; case_bool_decide. *)
  (*       * etrans; last apply Rmax_l. done. *)
  (*       * simpl. apply Rmax_r. *)
  (*     + rewrite /Expval in Hineq. rewrite /Expval. iPureIntro. *)
  (*       rewrite /pgl/prob in Hpgl. etrans; last exact. *)
  (*       etrans; last (apply Rplus_le_compat_r; exact). *)
  (*       rewrite -SeriesC_plus. *)
  (*       * apply SeriesC_le. *)
  (*         -- intros. split; first (case_bool_decide; real_solver). *)
  (*            case_bool_decide; simpl; try lra. *)
  (*            rewrite Rmult_1_r. apply Rplus_le_0_compat. *)
  (*            real_solver. *)
  (*         -- apply ex_seriesC_plus. *)
  (*            ++ apply (ex_seriesC_le _ μ); last done. *)
  (*               intros. case_bool_decide; by simpl. *)
  (*            ++ apply pmf_ex_seriesC_mult_fn. naive_solver. *)
  (*       * apply (ex_seriesC_le _ μ); last done. *)
  (*         intros. case_bool_decide; by simpl. *)
  (*       * apply pmf_ex_seriesC_mult_fn. naive_solver. *)
  (*     + iIntros. case_bool_decide. *)
  (*       * iApply ("H" with "[//]"). *)
  (*       * by iApply state_step_coupl_ret_err_ge_1. *)
  (* Qed. *)

  (* Lemma state_step_coupl_rec' σ1 (ε : nonnegreal) Z : *)
  (*   (∃ R μ (ε1 : nonnegreal) (ε2 : state con_prob_lang -> nonnegreal), *)
  (*         ⌜ sch_erasable (λ t _ _ sch, TapeOblivious t sch) μ σ1 ⌝ ∗ *)
  (*         ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗ *)
  (*         ⌜ (ε1 + Expval μ ε2 <= ε)%R ⌝ ∗ *)
  (*         ⌜pgl μ R ε1⌝ ∗ *)
  (*         ∀ σ2, ⌜ R σ2 ⌝ ={∅}=∗ state_step_coupl σ2 (ε2 σ2) Z)%I *)
  (*   ⊢ state_step_coupl σ1 ε Z. *)
  (* Proof. *)
  (*   iIntros. iApply state_step_coupl_rec. by rewrite state_step_coupl_rec_equiv. *)
  (* Qed. *)
      

  Lemma state_step_coupl_ind (Ψ Z : _ -> state d_prob_lang → nonnegreal → iProp Σ) :
    ⊢ (□ (∀ e σ ε,
             state_step_coupl_pre Z (λ '(e, σ, ε'),
                 Ψ e σ ε' ∧ state_step_coupl e σ ε' Z)%I (e, σ, ε) -∗ Ψ e σ ε) →
       ∀ e σ ε, state_step_coupl e σ ε Z -∗ Ψ e σ ε)%I.
  Proof.
    iIntros "#IH" (e σ ε) "H".
    set (Ψ' := (λ '(e, σ, ε), Ψ e σ ε) :
           (prodO (prodO (exprO d_prob_lang )(stateO d_prob_lang)) NNRO) → iProp Σ).
    assert (NonExpansive Ψ').
    { intros n [[e1 σ1] ε1] [[e2 σ2] ε2].
      intros [[[=][=]][=]].
      by simplify_eq/=. }
    iApply (least_fixpoint_ind _ Ψ' with "[] H").
    iIntros "!#" ([[] ?]) "H". by iApply "IH".
  Qed.

  Lemma fupd_state_step_coupl e σ1 Z (ε : nonnegreal) :
    (|={∅}=> state_step_coupl e σ1 ε Z) ⊢ state_step_coupl e σ1 ε Z.
  Proof.
    iIntros "H".
    iApply state_step_coupl_rec.
    iExists (dret σ1.(urns)), (λ x, if bool_decide (x = σ1.(urns)) then ε else 1%NNR).
    repeat iSplit.
    - iExists (Rmax ε 1).
      iPureIntro. intros. case_bool_decide; [apply Rmax_l|apply Rmax_r].
    - iPureIntro. rewrite Expval_dret.
      by case_bool_decide.
    - iPureIntro. apply dret_urn_erasable. 
    - iIntros (?).
      iMod "H".
      case_bool_decide.
      + subst; by destruct σ1.
      + by iApply state_step_coupl_ret_err_ge_1.
  Qed.
  
  Lemma state_step_coupl_mono e σ1 Z1 Z2 ε :
    (∀ e σ2 ε', Z1 e σ2 ε' -∗ Z2 e σ2 ε') -∗
    state_step_coupl e σ1 ε Z1 -∗ state_step_coupl e σ1 ε Z2.
  Proof.
    iIntros "HZ Hs".
    iRevert "HZ".
    iRevert (e σ1 ε) "Hs".
    iApply state_step_coupl_ind.
    iIntros "!#" (e σ ε)
      "[% | [? | [H|[(% & % & % & % & % &  H)|H]]]] Hw".
    - iApply state_step_coupl_ret_err_ge_1. lra.
    - iApply state_step_coupl_ret. by iApply "Hw".
    - iApply state_step_coupl_ampl.
      iIntros (??).
      by iApply "H".
    - iApply state_step_coupl_rec.
      repeat iExists _.
      repeat iSplit; try done.
      iIntros (x).
      iDestruct ("H" $! x) as "H".
      iMod "H" as "[IH _]".
      by iApply "IH".
    - iApply state_step_coupl_value_promote.
      iDestruct "H" as "(%&%&%&%&%&H2)".
      iExists _, _, _. repeat iSplit; try done.
      iMod ("H2") as "[H2 _]".
      by iApply "H2".
  Qed.

  (* Prove this when generalize splitting condition *)
  Lemma state_step_coupl_mono_err e1 ε1 ε2 σ1 Z :
    (ε1 <= ε2)%R → state_step_coupl e1 σ1 ε1 Z -∗ state_step_coupl e1 σ1 ε2 Z.
  Proof.
    iIntros (Heps) "Hs".
    iApply state_step_coupl_rec.
    destruct σ1 as [? us].
    iExists (dret us), (λ x, if bool_decide (x=us) then ε1 else 1%NNR).
    repeat iSplit.
    - iPureIntro.
      exists (Rmax ε1 1).
      intros.
      case_bool_decide.
      + apply Rmax_l.
      + apply Rmax_r.
    - rewrite Expval_dret. by rewrite bool_decide_eq_true_2.
    - iPureIntro. apply dret_urn_erasable.
    - iIntros (?).
      iModIntro. case_bool_decide; subst; first done.
      by iApply state_step_coupl_ret_err_ge_1.
  Qed.
  
  Lemma state_step_coupl_bind e1 σ1 Z1 Z2 ε :
    (∀ e2 σ2 ε', Z1 e2 σ2 ε' -∗ state_step_coupl e2 σ2 ε' Z2) -∗
    state_step_coupl e1 σ1 ε Z1 -∗
    state_step_coupl e1 σ1 ε Z2.
  Proof.
    iIntros "HZ Hs".
    iRevert "HZ".
    iRevert (e1 σ1 ε) "Hs".
    iApply state_step_coupl_ind.
    iIntros "!#" (e σ ε)
      "[% | [H | [H|[(% & % & % & % & % &  H)|H]]]] HZ".
    - by iApply state_step_coupl_ret_err_ge_1.
    - iApply ("HZ" with "H").
    - iApply state_step_coupl_ampl.
      iIntros (??).
      iDestruct ("H" with "[//]") as "[H _]".
      by iApply "H".
    - iApply state_step_coupl_rec.
      repeat iExists _.
      repeat iSplit; try done.
      iIntros (x).
      iDestruct ("H" $! x) as "H".
      iMod ("H") as "[H _]".
      by iApply "H".
    - iDestruct "H" as "(%&%&%&%&%&H2)".
      iApply state_step_coupl_value_promote.
      iExists _, _, _.
      repeat iSplit; try done.
      iMod ("H2") as "[H2 _]".
      by iApply "H2".
  Qed.

  (** Lemma needed for adequacy *)
  Lemma state_step_coupl_preserve e σ ε Z:
    is_well_constructed_expr e = true -> 
    expr_support_set e ⊆ urns_support_set (urns σ) ->
    map_Forall (λ (_ : loc) v , is_well_constructed_val v = true) (heap σ) ->
    map_Forall (λ (_ : loc) v , val_support_set v ⊆ urns_support_set (urns σ))
               (heap σ) ->
    state_step_coupl e σ ε Z -∗
    state_step_coupl e σ ε
      (λ e' σ' ε',
         ⌜is_well_constructed_expr e'= true⌝ ∗
         ⌜expr_support_set e' ⊆ urns_support_set (urns σ')⌝ ∗
                ⌜map_Forall (λ (_ : loc) v, is_well_constructed_val v = true) (heap σ')⌝ ∗
                ⌜map_Forall (λ (_ : loc) v, val_support_set v ⊆ urns_support_set (urns σ')) (heap σ')⌝ ∗
                Z e' σ' ε').
  Proof.
    intros H1 H2 H3 H4.
    iIntros "H".
    iRevert (H1 H2 H3 H4).
    iRevert "H".
    iRevert (e σ ε).
    iApply state_step_coupl_ind.
    iModIntro.
    iIntros (e σ ε) "H".
    iIntros (He Hsubset Hforall1 Hforall2).
    iDestruct "H" as "[%|[H|[H|[H|H]]]]".
    - by iApply state_step_coupl_ret_err_ge_1.
    - iApply state_step_coupl_ret. iFrame. iPureIntro. naive_solver.
    - iApply state_step_coupl_ampl.
      iIntros.
      iDestruct ("H" with "[//]") as "[H _]".
      by iApply "H".
    - iDestruct "H" as "(%μ&%ε2&[%r %]&%H2&%&H)".
      iApply state_step_coupl_rec.
      iExists μ, (λ m, if bool_decide (μ m > 0) then ε2 m else 1%NNR)%R.
      repeat iSplit.
      + iPureIntro. exists (Rmax r 1).
        intros. case_bool_decide; [|apply Rmax_r].
        etrans; last apply Rmax_l. naive_solver.
      + iPureIntro. erewrite Expval_support in H2.
        etrans; last exact.
        rewrite /Expval.
        right.
        apply SeriesC_ext.
        intros. repeat f_equal.
        by case_bool_decide.
      + done.
      +  iIntros (x).
         iDestruct ("H" $! x) as "H".
         iMod "H" as "[H _]". iModIntro.
         case_bool_decide; last by iApply state_step_coupl_ret_err_ge_1.
         iApply "H"; iPureIntro.
         * done.
         * etrans; first exact.
           by erewrite <-urn_erasable_same_support_set.
         * done.
         * eapply map_Forall_impl; first done.
           simpl.
           intros. etrans; first exact.
           by erewrite <-urn_erasable_same_support_set.
    - iDestruct "H" as "(%&%&%&%&%H1&H2)".
      iApply state_step_coupl_value_promote.
      subst.
      repeat iExists _, _, _.
      iFrame.
      repeat iSplit; try done.
      iMod ("H2") as "[H2 _]".
      iApply ("H2"); iPureIntro; try done.
      + rewrite !is_well_constructed_fill in He *.
        rewrite !andb_true_iff in He *.
        split; last naive_solver.
        apply is_simple_val_well_constructed.
        destruct!/=.
        epose proof urns_f_distr_witness _ as [? H'].
        apply H1 in H'.
        by eapply urn_subst_val_is_simple.
      + subst.
        rewrite support_set_fill.
        rewrite support_set_fill in Hsubset.
        etrans; last exact.
        simpl.
        rewrite is_simple_val_support_set; first set_solver.
        epose proof urns_f_distr_witness _ as [? H'].
        apply H1 in H'.
        by eapply urn_subst_val_is_simple.
  Qed. 

  Lemma state_step_coupl_ctx_bind K e1 σ1 Z ε:
    state_step_coupl e1 σ1 ε
      (λ e2 σ2 ε',
         state_step_coupl (fill K e2) σ2 ε' Z) -∗ state_step_coupl (fill K e1) σ1 ε Z.
  Proof.
    iRevert (e1 σ1 ε).
    iApply state_step_coupl_ind.
    iModIntro.
    iIntros (e σ ε) "H".
    iDestruct "H" as "[%|[H|[H|[H|H]]]]".
    - iApply state_step_coupl_ret_err_ge_1. lra.
    - done. 
    - iApply state_step_coupl_ampl.
      iIntros.
      by iDestruct ("H" with "[//]") as "[H _]".
    - iDestruct ("H") as "(%&%&%&%&%&H)".
      iApply state_step_coupl_rec.
      repeat iExists _; repeat iSplit; try done.
      iIntros. by iMod ("H" $! _) as "[H _]".
    - iDestruct "H" as "(%&%&%&%&%&H2)".
      subst.
      iApply state_step_coupl_value_promote.
      iExists (comp_ectx K _), _, _.
      repeat iSplit; try done; try iFrame.
      + by rewrite fill_app.
      + rewrite fill_app.
        by iMod ("H2") as "[$ _]".
  Qed.

  Lemma state_step_coupl_preserve_to_val e1 σ1 ε Z:
    state_step_coupl e1 σ1 ε Z ⊣⊢ state_step_coupl e1 σ1 ε (λ e2 σ2 ε2, Z e2 σ2 ε2 ∗ ⌜ssrbool.isSome(to_val e1) = ssrbool.isSome(to_val e2)⌝).
  Proof.
    iSplit.
    - iRevert (e1 σ1 ε).
      iApply state_step_coupl_ind.
      iModIntro.
      iIntros (e σ ε) "H".
      iDestruct "H" as "[%|[H|[H|[H|H]]]]".
      + iApply state_step_coupl_ret_err_ge_1. lra.
      + iApply state_step_coupl_ret. by iFrame.
      + iApply state_step_coupl_ampl.
        iIntros.
        by iDestruct ("H" with "[//]") as "[H _]".
      + iDestruct ("H") as "(%&%&%&%&%&H)".
        iApply state_step_coupl_rec.
        repeat iExists _; repeat iSplit; try done.
        iIntros. by iMod ("H" $! _) as "[H _]".
      + iDestruct "H" as "(%&%v&%v'&%&%&H2)".
        subst.
        iApply state_step_coupl_value_promote.
        iExists _, _, _. 
        repeat iSplit; try done; try iFrame.
        iMod ("H2") as "[H2 _]".
        assert (ssrbool.isSome$ to_val (fill K (Val v')) = ssrbool.isSome $ to_val (fill K (Val (v)))) as Hrewrite; last by rewrite Hrewrite.
        simpl.
        destruct K as [|e]; simpl; first done.
        rewrite fill_not_val; first rewrite fill_not_val; try done; by destruct e.
    - iApply state_step_coupl_mono.
      iIntros (???) "[$?]".
  Qed.

  Lemma state_step_coupl_preserve_atomic `{Hatomic: !Atomic StronglyAtomic e1} σ1 ε Z :
    state_step_coupl e1 σ1 ε Z ⊣⊢ state_step_coupl e1 σ1 ε (λ e2 σ2 ε2, Z e2 σ2 ε2 ∗ ⌜Atomic StronglyAtomic e2⌝).
  Proof.
    iSplit; last first.
    { iApply state_step_coupl_mono.
      iIntros (???) "[$?]". }
    iIntros "H".
    iRevert (Hatomic).
    iRevert (e1 σ1 ε) "H".
    iApply state_step_coupl_ind.
    iModIntro.
    iIntros (e σ ε) "H".
    iDestruct "H" as "[%|[H|[H|[H|H]]]]"; iIntros (Hatomic).
    - iApply state_step_coupl_ret_err_ge_1. lra.
    - iApply state_step_coupl_ret. by iFrame.
    - iApply state_step_coupl_ampl.
      iIntros.
      iDestruct ("H" with "[//]") as "[H _]".
      by iApply "H".
    - iDestruct ("H") as "(%&%&%&%&%&H)".
      iApply state_step_coupl_rec.
      repeat iExists _; repeat iSplit; try done.
      iIntros. iMod ("H" $! _) as "[H _]".
      by iApply "H".
    - iDestruct "H" as "(%&%v&%v'&%&%H1&H2)".
      subst.
      iApply state_step_coupl_value_promote.
      iExists _, _, _.
      repeat iSplit; try done; try iFrame.
      iMod ("H2") as "[H _]".
      iApply "H".
      iPureIntro.
      epose proof urns_f_distr_witness _ as [? H'].
      apply H1 in H'.
      by eapply value_promote_preserves_atomicity.
  Qed.
  
  (* Lemma state_step_coupl_state_step α σ1 Z (ε ε' : nonnegreal) : *)
  (*   α ∈ get_active σ1 → *)
  (*   (∃ R, ⌜pgl (state_step σ1 α) R ε⌝ ∗ *)
  (*         ∀ σ2 , ⌜R σ2 ⌝ ={∅}=∗ state_step_coupl σ2 ε' Z) *)
  (*   ⊢ state_step_coupl σ1 (ε + ε') Z. *)
  (* Proof. *)
  (*   iIntros (Hin) "(%R&%&H)". *)
  (*   iApply state_step_coupl_rec'. *)
  (*   iExists R, (state_step σ1 α), ε, (λ _, ε'). *)
  (*   repeat iSplit; try done. *)
  (*   - iPureIntro. *)
  (*     simpl in *. *)
  (*     rewrite elem_of_elements elem_of_dom in Hin. *)
  (*     destruct Hin. *)
  (*     by eapply state_step_sch_erasable. *)
  (*   - iPureIntro; eexists _; done. *)
  (*   - iPureIntro. rewrite Expval_const; last done. rewrite state_step_mass; [simpl;lra|done].  *)
  (* Qed. *)

  (* Lemma state_step_coupl_iterM_state_adv_comp N α σ1 Z (ε : nonnegreal) : *)
  (*   (α ∈ get_active σ1 -> *)
  (*    (∃ R ε1 (ε2 : _ -> nonnegreal), *)
  (*       ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗ *)
  (*       ⌜ (ε1 + Expval (iterM N (λ σ, state_step σ α) σ1) ε2 <= ε)%R ⌝ ∗ *)
  (*       ⌜pgl (iterM N (λ σ, state_step σ α) σ1) R ε1⌝ ∗ *)
  (*       ∀ σ2, ⌜ R σ2 ⌝ ={∅}=∗ state_step_coupl σ2 (ε2 σ2) Z) *)
  (*     ⊢ state_step_coupl σ1 ε Z)%I. *)
  (* Proof. *)
  (*   iIntros (Hin) "(%R & %ε1 & %ε2 & % & %Hε & % & H)". *)
  (*   iApply state_step_coupl_rec'. *)
  (*   iExists R, _, ε1, ε2. *)
  (*   repeat iSplit; try done. *)
  (*   - iPureIntro. *)
  (*     simpl in *. *)
  (*     rewrite elem_of_elements elem_of_dom in Hin. *)
  (*     destruct Hin. *)
  (*     by eapply iterM_state_step_sch_erasable. *)
  (* Qed.  *)
  
  (* Lemma state_step_coupl_state_adv_comp α σ1 Z (ε : nonnegreal) : *)
  (*   (α ∈ get_active σ1 -> *)
  (*    (∃ R ε1 (ε2 : _ -> nonnegreal), *)
  (*       ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗ *)
  (*       ⌜ (ε1 + Expval (state_step σ1 α) ε2 <= ε)%R ⌝ ∗ *)
  (*       ⌜pgl (state_step σ1 α) R ε1⌝ ∗ *)
  (*       ∀ σ2, ⌜ R σ2 ⌝ ={∅}=∗ state_step_coupl σ2 (ε2 σ2) Z) *)
  (*     ⊢ state_step_coupl σ1 ε Z)%I. *)
  (* Proof. *)
  (*   iIntros (Hin) "(%R & %ε1 & %ε2 & % & %Hε & % & H)". *)
  (*   iApply (state_step_coupl_iterM_state_adv_comp 1%nat); first done. *)
  (*   repeat iExists _. simpl. rewrite dret_id_right. *)
  (*   by repeat iSplit. *)
  (* Qed. *)
  

  (** * One step prog coupl *)

  Definition prog_coupl e1 σ1 ε Z : iProp Σ :=
    (∃ (ε2 : (expr d_prob_lang * state d_prob_lang) -> nonnegreal),
           ⌜reducible (e1, σ1)⌝ ∗
           ⌜∃ r, ∀ ρ, (ε2 ρ <= r)%R ⌝ ∗
           ⌜(Expval (prim_step e1 σ1) ε2 <= ε)%R⌝ ∗
           (∀ e2 σ2, |={∅}=>
                         Z e2 σ2 (ε2 (e2, σ2)))
       )%I.
  
  Definition prog_coupl_equiv1 e1 σ1 ε Z:
    (∀ e2 σ2, Z e2 σ2 1) -∗
    prog_coupl e1 σ1 ε Z -∗
    (∃ R (ε1 : nonnegreal) (ε2 : (expr d_prob_lang * state d_prob_lang) -> nonnegreal),
           ⌜reducible (e1, σ1)⌝ ∗
           ⌜∃ r, ∀ ρ, (ε2 ρ <= r)%R ⌝ ∗
           ⌜(ε1 + Expval (prim_step e1 σ1) ε2 <= ε)%R⌝ ∗
           ⌜pgl (prim_step e1 σ1) R ε1⌝ ∗
           (∀ e2 σ2, ⌜R (e2, σ2)⌝ ={∅}=∗
                         Z e2 σ2 (ε2 (e2, σ2)))
    )%I.
  Proof.
    rewrite /prog_coupl.
    iIntros "H1 H".
    iDestruct "H" as "(%ε2 & % & [%r %] & %Hineq  &H)".
    iExists (λ _, True), 0, (λ x, if bool_decide (prim_step e1 σ1 x > 0)%R then ε2 x else 1).
    repeat iSplit; first done.
    - iPureIntro. exists (Rmax r 1).
      intros; case_bool_decide.
      + etrans; last apply Rmax_l. done.
      + simpl. apply Rmax_r.
    - simpl. iPureIntro. rewrite Rplus_0_l. etrans; last exact.
      rewrite /Expval. apply Req_le.
      apply SeriesC_ext.
      intros n. case_bool_decide; first done.
      destruct (pmf_pos (prim_step e1 σ1) n) as [K|K].
      + exfalso. apply Rlt_gt in K. naive_solver.
      + simpl. rewrite -K. lra.
    - iPureIntro. by apply pgl_trivial.
    - iIntros. case_bool_decide; done.
  Qed.

  Definition prog_coupl_equiv2 e1 σ1 ε Z:
    (∀ e2 σ2, Z e2 σ2 1) -∗
    (∃ R (ε1 : nonnegreal) (ε2 : (expr d_prob_lang * state d_prob_lang) -> nonnegreal),
        ⌜reducible (e1, σ1)⌝ ∗
        ⌜∃ r, ∀ ρ, (ε2 ρ <= r)%R ⌝ ∗
                   ⌜(ε1 + Expval (prim_step e1 σ1) ε2 <= ε)%R⌝ ∗
                   ⌜pgl (prim_step e1 σ1) R ε1⌝ ∗
                   (∀ e2 σ2, ⌜R (e2, σ2)⌝ ={∅}=∗
                                 Z e2 σ2 (ε2 (e2, σ2)))
    )%I-∗
    prog_coupl e1 σ1 ε Z.
  Proof. 
    iIntros "H1 H".
    iDestruct "H" as "(%R & %ε1 & %ε2 & % & [%r %] & %Hineq & %Hpgl &H)".
    iExists (λ σ, if bool_decide(R σ) then ε2 σ else 1).
    repeat iSplit; try done.
    - iPureIntro. exists (Rmax r 1).
      intros; case_bool_decide.
      + etrans; last apply Rmax_l. done.
      + simpl. apply Rmax_r.
    - rewrite /Expval in Hineq. rewrite /Expval. iPureIntro.
      rewrite /pgl/prob in Hpgl. etrans; last exact.
      etrans; last (apply Rplus_le_compat_r; exact).
      rewrite -SeriesC_plus.
      + apply SeriesC_le.
        * intros. split; first (case_bool_decide; real_solver).
          case_bool_decide; simpl; try lra.
          rewrite Rmult_1_r. apply Rplus_le_0_compat.
          real_solver.
        * apply ex_seriesC_plus.
          -- apply (ex_seriesC_le _ (prim_step e1 σ1)); last done.
             intros. case_bool_decide; by simpl.
          -- apply pmf_ex_seriesC_mult_fn. naive_solver.
      + apply (ex_seriesC_le _ (prim_step e1 σ1)); last done.
        intros. case_bool_decide; by simpl.
      + apply pmf_ex_seriesC_mult_fn. naive_solver.
    - iIntros. case_bool_decide; last done.
      iApply ("H" with "[//]").
  Qed. 

  Lemma prog_coupl_mono_err e σ Z ε ε':
    (ε<=ε')%R -> prog_coupl e σ ε Z -∗ prog_coupl e σ ε' Z.
  Proof.
    iIntros (?) "(%&%&%&%&H)".
    repeat iExists _.
    repeat iSplit; try done.
    iPureIntro.
    etrans; exact.
  Qed.

  Lemma prog_coupl_strong_mono e1 σ1 Z1 Z2 ε :
    □(∀ e2 σ2, Z2 e2 σ2 1) -∗
    (∀ e2 σ2 ε', ⌜∃ σ, (prim_step e1 σ (e2, σ2) > 0)%R⌝ ∗ Z1 e2 σ2 ε' -∗ Z2 e2 σ2 ε') -∗
    prog_coupl e1 σ1 ε Z1 -∗ prog_coupl e1 σ1 ε Z2.
  Proof.
    iIntros "#H1 Hm (%&%&[%r %]&%Hineq & Hcnt) /=".
    rewrite /prog_coupl.
    iExists (λ x, if bool_decide (∃ σ, prim_step e1 σ x >0)%R then ε2 x else 1).
    repeat iSplit.
    - done.
    - iPureIntro. exists (Rmax r 1).
      intros; case_bool_decide.
      + etrans; last apply Rmax_l. done.
      + simpl. apply Rmax_r.
    - rewrite /Expval in Hineq. rewrite /Expval. iPureIntro.
      rewrite /Expval. etrans; last exact. apply Req_le.
      apply SeriesC_ext.
      intros n. case_bool_decide; first done.
      destruct (pmf_pos (prim_step e1 σ1) n) as [K|K].
      + exfalso. apply Rlt_gt in K. naive_solver.
      + simpl. rewrite -K. lra.
    - simpl. iIntros (??).
      case_bool_decide; last done.
      iApply "Hm". iMod ("Hcnt" $! _ _).
      by iFrame.
  Qed.

  Lemma prog_coupl_mono e1 σ1 Z1 Z2 ε :
    (∀ e2 σ2 ε', Z1 e2 σ2 ε' -∗ Z2 e2 σ2 ε') -∗
    prog_coupl e1 σ1 ε Z1 -∗ prog_coupl e1 σ1 ε Z2.
  Proof.
    iIntros "Hm".
    rewrite /prog_coupl.
    iIntros "(%&%&%&%&?)".
    repeat iExists _; repeat iSplit; try done.
    iIntros. by iApply "Hm".
  Qed.
    Lemma prog_coupl_strengthen e1 σ1 Z ε :
    □(∀ e2 σ2, Z e2 σ2 1) -∗
    prog_coupl e1 σ1 ε Z -∗
    prog_coupl e1 σ1 ε (λ e2 σ2 ε', ⌜(∃ σ, (prim_step e1 σ (e2, σ2) > 0)%R)\/ (1<=ε')%R⌝ ∧ Z e2 σ2 ε').
  Proof.
    iIntros "#Hmono (%&%&[%r %]&%Hineq & Hcnt) /=".
    rewrite /prog_coupl.
    iExists (λ x, if bool_decide (∃ σ, prim_step e1 σ x >0)%R then ε2 x else 1).
    repeat iSplit.
    - done.
    - iPureIntro. exists (Rmax r 1).
      intros; case_bool_decide.
      + etrans; last apply Rmax_l. done.
      + simpl. apply Rmax_r.
    - rewrite /Expval in Hineq. rewrite /Expval. iPureIntro.
      rewrite /Expval. etrans; last exact. apply Req_le.
      apply SeriesC_ext.
      intros n. case_bool_decide; first done.
      destruct (pmf_pos (prim_step e1 σ1) n) as [K|K].
      + exfalso. apply Rlt_gt in K. naive_solver.
      + simpl. rewrite -K. lra.
    - simpl. iIntros (??).
      case_bool_decide.
      + iMod ("Hcnt" $! _ _).
        iFrame. iPureIntro. naive_solver.
      + iMod ("Hcnt" $! e2 σ2  ).
        iModIntro. iSplit; last iApply "Hmono".
        iPureIntro. naive_solver.
  Qed.

  Lemma prog_coupl_ctx_bind K e1 σ1 Z ε:
    to_val e1 = None ->
    □(∀ e2 σ2, Z e2 σ2 1) -∗
    prog_coupl e1 σ1 ε (λ e2 σ2 ε', Z (fill K e2) σ2 ε') -∗ prog_coupl (fill K e1) σ1 ε Z.
  Proof.
    iIntros (Hv) "#H' H".
    (* iDestruct (prog_coupl_strengthen with "[][$]") as "H". *)
    (* { iModIntro. by iIntros. } *)
    iDestruct "H" as "(%ε2&%&[%r %]&%&H)".
    (** (classical) inverse of context [K] *)
    destruct (partial_inv_fun (fill K)) as (Kinv & HKinv).
    assert (∀ e, Kinv (fill K e) = Some e) as HKinv3.
    { intro e.
      destruct (Kinv (fill K e)) eqn:Heq;
        eapply HKinv in Heq; by simplify_eq. }
    set (ε2' := (λ '(e, σ), from_option (λ e', ε2 (e', σ)) 1%NNR (Kinv e))).
    assert (∀ e2 σ2, ε2' (fill K e2, σ2) = ε2 (e2, σ2)) as Hε2'.
    { intros. rewrite /ε2' HKinv3 //. }
    (* iExists (λ '(e2, σ2, efs), ∃ e2', e2 = K e2' /\ R (e2', σ2, efs)), ε1, ε2'. *)
    iExists ε2'.
    repeat iSplit; try iPureIntro.
    - by apply reducible_fill.
    - rewrite /ε2'. eexists (Rmax 1%R r).
      intros [??].
      destruct (Kinv _); simpl.
      + etrans; last apply Rmax_r. done.
      + apply Rmax_l.
    - rewrite fill_dmap// Expval_dmap//=; last first.
      + eapply ex_expval_bounded. simpl. intros [??] => /=. by rewrite HKinv3/=.
      + etrans; last done.
        rewrite /Expval. apply Req_le.
        apply SeriesC_ext.
        intros [??]. simpl. by rewrite HKinv3/=.
    (* - rewrite fill_dmap//. *)
    (*   replace (ε1) with (ε1+0)%NNR; last (apply nnreal_ext; simpl; lra). *)
    (*   eapply pgl_dbind; try done. *)
    (*   intros a ?. apply pgl_dret. *)
    (*   destruct a as [[??]?] => /=. *)
    (*   naive_solver. *)
    - iIntros (??).
      rewrite /ε2'.
      destruct (Kinv e2) eqn:H'; simpl; last done.
      apply HKinv in H'. by subst.
  Qed.

  
  Lemma prog_coupl_reducible e σ Z ε :
    prog_coupl e σ ε Z -∗ ⌜reducible (e, σ)⌝.
  Proof. by iIntros "(%&%&%&%& _)". Qed.
 

  Lemma prog_coupl_adv_comp e1 σ1 Z (ε : nonnegreal) :
    □(∀ e2 σ2, Z e2 σ2 1) -∗
      (∃ R (ε1 : nonnegreal) (ε2 : _ -> nonnegreal),
          ⌜reducible (e1, σ1)⌝ ∗
          ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗
          ⌜ (ε1 + Expval (prim_step e1 σ1) ε2 <= ε)%R ⌝ ∗ ⌜pgl (prim_step e1 σ1) R ε1⌝ ∗
          ∀ e2 σ2, ⌜ R (e2, σ2) ⌝ ={∅}=∗ Z e2 σ2 (ε2 (e2, σ2))) -∗
        prog_coupl e1 σ1 ε Z.
  Proof.
    iIntros "#H' H".
    by iApply prog_coupl_equiv2.
  Qed.

  Lemma prog_coupl_prim_step e1 σ1 Z ε :
    □(∀ e2 σ2, Z e2 σ2 1) -∗
    (∃ R ε1 ε2, ⌜reducible (e1, σ1)⌝ ∗ ⌜ (ε1 + ε2 <= ε)%R ⌝ ∗ ⌜pgl (prim_step e1 σ1) R ε1⌝ ∗
          ∀ e2 σ2, ⌜R (e2, σ2)⌝ ={∅}=∗ Z e2 σ2 ε2) -∗
     prog_coupl e1 σ1 ε Z.
  Proof.
    iIntros "#H' H".
    iApply prog_coupl_adv_comp; first done.
    iDestruct "H" as "(%R&%ε1 & %ε2 & % & %& % & H)".
    iExists R, ε1, (λ _, ε2).
    repeat iSplit; try done.
    - iPureIntro. naive_solver.
    - iPureIntro. rewrite Expval_const; last done.
      rewrite prim_step_mass; [lra|done].
  Qed.

  (** Lemma needed for adequacy *)
  Lemma prog_coupl_preserve e σ ε Z:
    is_well_constructed_expr e = true ->
    expr_support_set e ⊆ urns_support_set (urns σ) ->
    map_Forall (λ (_ : loc) v , is_well_constructed_val v = true) (heap σ) ->
    map_Forall (λ (_ : loc) v , val_support_set v ⊆ urns_support_set (urns σ))
               (heap σ) ->
    □(∀ e2 σ2, Z e2 σ2 1) -∗
    prog_coupl e σ ε Z -∗
    prog_coupl e σ ε
      (λ e' σ' ε', ((⌜is_well_constructed_expr e' = true ⌝ ∗
                     ⌜expr_support_set e' ⊆ urns_support_set (urns σ')⌝ ∗
                   ⌜map_Forall (λ (_ : loc) v, is_well_constructed_val v = true) (heap σ')⌝ ∗
                   ⌜map_Forall (λ (_ : loc) v, val_support_set v ⊆ urns_support_set (urns σ')) (heap σ')⌝) ∨ ⌜(1<=ε')%R⌝) ∗
                Z e' σ' ε').
  Proof.
    iIntros (He Hsubset Hforall1 Hforall2) "#H1 H".
    rewrite /prog_coupl.
    iDestruct "H" as "(%&%&[%r %]&%&H)".
    iExists (λ x, if bool_decide (prim_step e σ x>0)%R then ε2 x else 1).
    repeat iSplit; try done.
    - iPureIntro.
      exists (Rmax r 1). intros. case_bool_decide.
      + etrans; last apply Rmax_l. done.
      + etrans; last apply Rmax_r. done. 
    - iPureIntro. etrans; last exact.
      right.
      rewrite /Expval.
      apply SeriesC_ext.
      intros x.
      case_bool_decide; first done.
      pose proof (pmf_pos (prim_step e σ) x).
      assert (prim_step e σ x=0) as ->; simpl; simpl in *; lra.
    - iIntros (e2 σ2).
      iMod ("H" $! e2 σ2). iFrame. 
      case_bool_decide; last first. 
      { iModIntro. iSplit; last done.
        iPureIntro. by right. }
      iFrame.
      iPureIntro.
      left.
      by eapply prim_step_preserve.
  Qed. 

End modalities.

(** * The weakest precondition *)

Definition pgl_wp_pre `{!eltonWpGS d_prob_lang Σ}
    (wp : coPset -d> expr d_prob_lang -d> (val d_prob_lang -d> iPropO Σ) -d> iPropO Σ) :
  coPset -d> expr d_prob_lang -d> (val d_prob_lang -d> iPropO Σ) -d> iPropO Σ :=
  (λ E e1 Φ,
     ∀ σ1 ε1,
     state_interp σ1 ∗ err_interp ε1 ={E, ∅}=∗
     state_step_coupl e1 σ1 ε1
       (λ e2 σ2 ε2,
          match to_val e2 with
          | Some v => |={∅, E}=> state_interp σ2 ∗ err_interp ε2 ∗ Φ v
          | None => prog_coupl e2 σ2 ε2
                     (λ e3 σ3 ε3,
                        ▷ state_step_coupl e3 σ3 ε3
                          (λ e4 σ4 ε4, |={∅, E}=> state_interp σ4 ∗ err_interp ε4 ∗ wp E e4 Φ 
                          )
                     )
          end
       )
  )%I.

Local Instance wp_pre_contractive `{!eltonWpGS d_prob_lang Σ} : Contractive (pgl_wp_pre).
Proof.
  rewrite /pgl_wp_pre /= => n wp wp' Hwp E e1 Φ /=.
  do 6 f_equiv.
  apply least_fixpoint_ne_outer; [|done].
  intros Ψ [[e' σ'] ε'].
  rewrite /state_step_coupl_pre.
  do 3 f_equiv.
  rewrite /prog_coupl.
  do 10 f_equiv.
  f_contractive.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [[??]?].
  rewrite /state_step_coupl_pre.
  repeat f_equiv; apply Hwp.
Qed.

(* TODO: get rid of stuckness in notation [iris/bi/weakestpre.v] so that we don't have to do this *)
Local Definition pgl_wp_def `{!eltonWpGS d_prob_lang Σ} : Wp (iProp Σ) (expr d_prob_lang) (val d_prob_lang) () :=
  {| wp := λ _ : (), fixpoint (pgl_wp_pre); wp_default := () |}.
Local Definition pgl_wp_aux : seal (@pgl_wp_def). Proof. by eexists. Qed.
Definition pgl_wp' := pgl_wp_aux.(unseal).
Global Arguments pgl_wp' {Σ _}.
Global Existing Instance pgl_wp'.
Local Lemma pgl_wp_unseal `{!eltonWpGS d_prob_lang Σ} : wp = (@pgl_wp_def Σ _).(wp).
Proof. rewrite -pgl_wp_aux.(seal_eq) //. Qed.

Section pgl_wp.
Context `{!eltonWpGS d_prob_lang Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val d_prob_lang → iProp Σ.
Implicit Types v : val d_prob_lang.
Implicit Types e : expr d_prob_lang.
Implicit Types σ : state d_prob_lang.
Implicit Types ρ : cfg d_prob_lang.
Implicit Types ε : nonnegreal.

(* Weakest pre *)
Lemma pgl_wp_unfold s E e Φ :
  WP e @ s; E {{ Φ }} ⊣⊢ pgl_wp_pre (wp (PROP:=iProp Σ) s) E e Φ.
Proof. rewrite pgl_wp_unseal. apply (fixpoint_unfold (pgl_wp_pre)). Qed.

Global Instance pgl_wp_ne s E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp (PROP:=iProp Σ) s E e).
Proof.
  revert e. induction (lt_wf n) as [n _ IH]=> e Φ Ψ HΦ.
  rewrite !pgl_wp_unfold /pgl_wp_pre /=.
  do 6 f_equiv.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [[]?]. rewrite /state_step_coupl_pre.
  rewrite /prog_coupl.
  do 13 f_equiv.
  f_contractive.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [[]?]. rewrite /state_step_coupl_pre.
  do 5 f_equiv. 
  rewrite IH; [done|done|].
  intros ?. eapply dist_le; first apply HΦ. simpl in *. lia. 
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
  intros He Φ Ψ HΦ.
  rewrite !pgl_wp_unfold /pgl_wp_pre.
  do 6 f_equiv.
  assert (
      ∀ σ1 ε K1 K2, state_step_coupl e σ1 ε
                   (λ e2 σ2 ε2,
                      match to_val e2 with
                      | Some v => K1 e2 σ2 ε2 v
                      | None => K2 e2 σ2 ε2
                   end) ⊣⊢
    state_step_coupl e σ1 ε
      (λ e2 σ2 ε2, K2 e2 σ2 ε2 )) as Hrewrite.
  { iIntros.
    iSplit.
    - rewrite state_step_coupl_preserve_to_val.
      iIntros. iApply (state_step_coupl_mono with "[][$]").
      rewrite He.
      iIntros (???) "[? %]".
      by case_match.
    - rewrite state_step_coupl_preserve_to_val.
      iIntros. iApply (state_step_coupl_mono with "[][$]").
      rewrite He.
      iIntros (???) "[? %]".
      by case_match.
  }
  rewrite !Hrewrite.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [[]?]. rewrite /state_step_coupl_pre.
  rewrite /prog_coupl.
  do 12 f_equiv.
  f_contractive. 
  apply least_fixpoint_ne_outer; [|done].
  intros ? [[]?]. rewrite /state_step_coupl_pre.
  repeat f_equiv.
Qed.

Lemma pgl_wp_value_fupd' s E Φ v : ⊢ (|={E}=> Φ v) -∗ WP of_val v @ s; E {{ Φ }} .
Proof. rewrite pgl_wp_unfold /pgl_wp_pre.
       iIntros "H" (??) "[??]".
       iApply state_step_coupl_ret.
       iMod "H".
       iFrame.
       iApply fupd_mask_subseteq. set_solver.
Qed.

Lemma pgl_wp_strong_mono E1 E2 e Φ Ψ s :
  E1 ⊆ E2 →
  WP e @ s ; E1 {{ Φ }} -∗
             (∀ σ1 ε1 v, state_interp σ1 ∗ err_interp ε1 ∗ Φ v ={E2, ∅}=∗
                         state_step_coupl (Val v) σ1 ε1
                           (λ e2 σ2 ε2, |={∅, E2}=> state_interp σ2 ∗ err_interp ε2 ∗
                                                   ∃ v', ⌜ e2 = Val v' ⌝ ∗ Ψ v')) -∗
             WP e @ s ; E2 {{ Ψ }}.
Proof.
  iIntros (HE) "H HΦ". iLöb as "IH" forall (e E1 E2 HE Φ Ψ).
  rewrite !pgl_wp_unfold /pgl_wp_pre /=.
  iIntros (σ1 ε) "[Hσ Hε]".
  iSpecialize ("H" with "[$]").
  iMod (fupd_mask_subseteq E1) as "Hclose"; [done|].
  iMod "H"; iModIntro.
  (* rewrite state_step_coupl_preserve_to_val. *)
  iApply (state_step_coupl_bind with "[-H]H").
  iIntros (e2 ??) "H".
  destruct (d_prob_lang.to_val e2) as [v|] eqn:Heq.
  { iApply fupd_state_step_coupl.
    iMod "H" as "(?&?&?)".
    iMod "Hclose" as "_".
    iSpecialize ("HΦ" with "[$]").
    iMod "HΦ".
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose".
    apply d_prob_lang.of_to_val in Heq as ?. subst.
    rewrite state_step_coupl_preserve_to_val.
    iApply (state_step_coupl_bind with "[-HΦ] [$]").
    iIntros (???) "[H %]".
    iApply state_step_coupl_ret.
    simpl in *. case_match eqn:Heq'; last done.
    apply d_prob_lang.of_to_val in Heq' as ?. subst.
    iMod "H" as "($&$&(%&%&H))".
    by simplify_eq.
  }
  iApply state_step_coupl_ret.
  rewrite Heq.
  iApply (prog_coupl_mono with "[-H] H").
  iIntros (???) "H !>".
  iApply (state_step_coupl_mono with "[-H] H").
  iIntros (???) ">(?&?&H)".
  iMod "Hclose" as "_".
  iFrame.
  iModIntro.
  by iApply ("IH" with "[//]H").
Qed.

Lemma pgl_wp_strong_mono' E1 E2 e Φ Ψ s :
  E1 ⊆ E2 →
  WP e @ s ; E1 {{ Φ }} -∗
             (∀ σ1 ε1 v, state_interp σ1 ∗ err_interp ε1 ∗ Φ v 
              ={E2}=∗ state_interp σ1 ∗ err_interp ε1 ∗ Ψ v) -∗
             WP e @ s ; E2 {{ Ψ }}.
Proof.
  iIntros (?) "Hwp Hw".
  iApply (pgl_wp_strong_mono with "[$]"); first done.
  iIntros (???) "H".
  iApply state_step_coupl_ret.
  iApply fupd_mask_intro; first set_solver.
  iIntros ">Hclose".
  iMod ("Hw" with "[$]") as "($&$&?)".
  by iFrame. 
Qed.

Lemma state_step_coupl_wp E e Φ s :
  (∀ σ1 ε1, state_interp σ1 ∗ err_interp ε1 ={E, ∅}=∗
            state_step_coupl e σ1 ε1
              (λ e2 σ2 ε2, |={∅, E}=> state_interp σ2 ∗ err_interp ε2 ∗ WP e2 @ s ; E {{Φ}})) -∗
  WP e @ s ; E {{ Φ }}.
Proof.
  iIntros "H".
  erewrite pgl_wp_unfold. rewrite /pgl_wp_pre.
  iIntros (??) "[??]". 
  iSpecialize ("H" with "[$]").
  iApply fupd_mono; last done.
  iIntros "H".
  iApply (state_step_coupl_bind with "[][$]").
  iIntros (???) "H".
  iApply fupd_state_step_coupl.
  iMod "H" as "(?&?&H)".
  rewrite pgl_wp_unfold/pgl_wp_pre.
  iApply "H". iFrame.
Qed. 

Lemma fupd_pgl_wp s E e Φ : (|={E}=> WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }}.
Proof.
  rewrite pgl_wp_unfold /pgl_wp_pre. iIntros "H" (??) "[??]".
  iMod "H".
  by iSpecialize ("H" with "[$]").
Qed.
Lemma pgl_wp_fupd s E e Φ : WP e @ s; E {{ v, |={E}=> Φ v }} ⊢ WP e @ s; E {{ Φ }}.
Proof. iIntros "H". iApply (pgl_wp_strong_mono E with "H"); auto.
       iIntros (???) "(?&?&>?)".
       iApply state_step_coupl_ret.
       iApply fupd_mask_intro; first set_solver.
       iIntros ">_".
       by iFrame.
Qed.

(** * Value promotion makes this rule hard to prove *)
Lemma pgl_wp_atomic E1 E2 e Φ `{!Atomic StronglyAtomic e} a :
  (|={E1,E2}=> WP e @ a; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ a; E1 {{ Φ }}.
Proof.
  iIntros "H".
  rewrite !pgl_wp_unfold /pgl_wp_pre.
  iIntros (??) "[??]".
  iDestruct ("H" with "[$]") as ">>H".
  iModIntro.
  rewrite state_step_coupl_preserve_atomic.
  iApply (state_step_coupl_mono with "[] H").
  iIntros (e2 σ2 ε2).
  destruct (to_val e2) as [v|] eqn:He.
  - iIntros "[>(?&?&>?) %]". by iFrame.
  - iIntros "[H %]".
    iDestruct (prog_coupl_strengthen with "[]H") as "H".
    { iModIntro. iIntros. by iApply state_step_coupl_ret_err_ge_1. }
    iApply (prog_coupl_mono with "[] [$]").
    iIntros (???) "[[[%%]|%H0]?]!>"; last first.
    { by iApply state_step_coupl_ret_err_ge_1. }
    rewrite state_step_coupl_preserve_to_val.
    iApply (state_step_coupl_bind with "[][$]").
    iIntros (???) "[H %H1]".
    iApply fupd_state_step_coupl.
    iMod "H" as "(?&?&H)".
    rewrite !pgl_wp_unfold {1}/pgl_wp_pre.
    iSpecialize ("H" with "[$]").
    iMod "H". iModIntro.
    rewrite state_step_coupl_preserve_to_val.
    iApply (state_step_coupl_mono with "[-H]H").
    iIntros (???).
    case_match eqn:H'.
    + iIntros "[>(?&?&>?) _]".
      iFrame. iModIntro.
      rewrite -(of_to_val _ _ H').
      by iApply pgl_wp_value_fupd'.
    + iIntros "[_ %H2]".
      simpl in *.
      epose proof (atomic _ _ _ H0) as [? H3].
      simpl in *.
      exfalso.
      rewrite H2 in H1.
      by rewrite H3 in H1.
Qed. 

Lemma pgl_wp_step_fupd s E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> P) -∗ WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ s; E1 {{ Φ }}.
Proof.
  rewrite !pgl_wp_unfold /pgl_wp_pre.
  iIntros (H ?) "HR H".
  iIntros (σ1 ε) "[Hσ Hε]". iMod "HR".
  iMod ("H" with "[$Hσ $Hε]") as "H".
  iModIntro.
  rewrite state_step_coupl_preserve_to_val.
  iApply (state_step_coupl_mono with "[-H]H").
  iIntros (???) "[H %Heq]".
  rewrite H in Heq.
  case_match; first done.
  iApply (prog_coupl_mono with "[-H]H").
  iIntros (???) "H!>".
  iApply (state_step_coupl_mono with "[-H]H").
  iIntros (???) ">(?&?&?)".
  iMod "HR".
  iFrame. iModIntro.
  iApply (pgl_wp_strong_mono with "[$]"); first done.
  iIntros (???) "(?&?&K)".
  iApply state_step_coupl_ret.
  iFrame.
  iApply fupd_mask_intro; first set_solver.
  iIntros ">_".
  iMod ("K" with "[$]").
  by iFrame. 
Qed.

Lemma pgl_wp_bind K s E e Φ :
  WP e @ s; E {{ v, WP (fill K (of_val v)) @ s; E {{ Φ }} }} ⊢ WP fill K e @ s; E {{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite !pgl_wp_unfold /pgl_wp_pre.
  iIntros (??) "[??]".
  iMod ("H" with "[$]") as "H".
  iModIntro.
  iApply (state_step_coupl_ctx_bind).
  iApply (state_step_coupl_bind with "[][$]").
  iIntros (e2 ??) "H".
  destruct (to_val e2) as [v|] eqn:He.
  { apply of_to_val in He as <-.
    iApply fupd_state_step_coupl.
    iMod "H" as "(?&?&H)".
    rewrite pgl_wp_unfold /pgl_wp_pre.
    iMod ("H" with "[$]").
    by iApply state_step_coupl_ret.
  }
  iApply state_step_coupl_ret.
  iApply state_step_coupl_ret. 
  rewrite fill_not_val; last done.
  iApply prog_coupl_ctx_bind; [done|..].
  { iModIntro; iIntros. by iApply state_step_coupl_ret_err_ge_1. }
  iApply (prog_coupl_mono with "[] [$]").
  iIntros (???) "H!>".
  iApply (state_step_coupl_ctx_bind).
  iApply (state_step_coupl_mono with "[][$]").
  iIntros (???) "H".
  iApply state_step_coupl_ret.
  iMod ("H") as "($&$&?)".
  by iApply "IH".
Qed. 

(** * Derived rules *)
Lemma pgl_wp_mono s E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (pgl_wp_strong_mono' with "H"); auto.
  iIntros (???) "($&$&?)".
  by iApply HΦ.
Qed.
Lemma pgl_wp_mask_mono s E1 E2 e Φ : E1 ⊆ E2 → WP e @ s; E1 {{ Φ }} ⊢ WP e @ s; E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (pgl_wp_strong_mono' with "H"); auto. Qed.
Global Instance pgl_wp_mono' s E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply pgl_wp_mono. Qed.
Global Instance pgl_wp_flip_mono' s E e :
  Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (wp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply pgl_wp_mono. Qed.

Lemma pgl_wp_value_fupd s E Φ e v : IntoVal e v → (|={E}=> Φ v) ⊢ WP e @ s; E {{ Φ }} .
Proof. intros <-. iApply pgl_wp_value_fupd'. Qed.
Lemma pgl_wp_value' s E Φ v : Φ v ⊢ WP (of_val v) @ s; E {{ Φ }}.
Proof. iIntros "?". iApply pgl_wp_value_fupd'. auto. Qed.
Lemma pgl_wp_value s E Φ e v : IntoVal e v → Φ v ⊢ WP e @ s; E {{ Φ }}.
Proof. intros <-. apply pgl_wp_value'. Qed.

Lemma pgl_wp_frame_l s E e Φ R : R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros "[? H]". iApply (pgl_wp_strong_mono with "H"); auto.
       iIntros (???) "(?&?&?)".
       iApply state_step_coupl_ret.
       iApply fupd_mask_intro; first set_solver.
       iIntros ">_".
       by iFrame.
Qed.
Lemma pgl_wp_frame_r s E e Φ R : WP e @ s; E {{ Φ }} ∗ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros "[H ?]". iApply (pgl_wp_strong_mono with "H"); auto.
       iIntros (???) "(?&?&?)".
       iApply state_step_coupl_ret.
       iApply fupd_mask_intro; first set_solver.
       iIntros ">_".
       by iFrame.
Qed.

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
  iIntros (???) "(?&?&?)".
  iApply state_step_coupl_ret. iFrame.
  iApply fupd_mask_intro; first set_solver.
  iIntros ">_".
  iExists _.
  iModIntro. iSplit; first done.
  by iApply "H".
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
  Context `{!eltonWpGS d_prob_lang Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val d_prob_lang → iProp Σ.
  Implicit Types v : val d_prob_lang.
  Implicit Types e : expr d_prob_lang.

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


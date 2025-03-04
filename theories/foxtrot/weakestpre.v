From Coq Require Export Reals Psatz.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export fixpoint big_op.
From iris.prelude Require Import options.

From clutch.bi Require Export weakestpre.
From clutch.prelude Require Import stdpp_ext iris_ext NNRbar.
From clutch.con_prob_lang Require Import lang erasure.
From clutch.common Require Export sch_erasable con_language.
From clutch.prob Require Export couplings_app distribution graded_predicate_lifting.


Set Default Proof Using "Type*".

Import uPred.

Local Open Scope NNR_scope.
#[global] Hint Resolve cond_nonneg : core.

Section spec_transition.
  Definition spec_transition_compress (ρ: cfg con_prob_lang) (μ : distr (option nat))
    (f: nat -> cfg con_prob_lang -> distr (cfg con_prob_lang)) (μ' : distr (cfg con_prob_lang))
    : distr (cfg con_prob_lang) :=
    (μ ≫= (λ (o:option nat),
             match o with
             | Some tid => (dbind (λ ρ', f tid ρ') (step tid ρ))
             | None => μ'
             end
    )).

  Inductive spec_transition (ρ:cfg con_prob_lang) : distr (cfg con_prob_lang) ->  Prop :=
  | spec_transition_dret : spec_transition ρ (dret ρ)
  | spec_transition_bind (μ : distr (option nat))
      (f: nat -> cfg con_prob_lang -> distr (cfg con_prob_lang)) (μ' : distr (cfg con_prob_lang)):
    (∀ (tid:nat), (μ (Some tid) > 0)%R -> 
                (forall ρ', step tid ρ ρ' > 0 -> spec_transition ρ' (f tid ρ'))) ->
    ((μ None > 0)%R -> spec_transition ρ μ') ->
    spec_transition ρ (spec_transition_compress ρ μ f μ')
  .

  Lemma spec_transition_bind' ρ μ μ1 f μ2 :
    μ=spec_transition_compress ρ μ1 f μ2 ->
    (∀ (tid:nat), (μ1 (Some tid) > 0)%R -> 
                (forall ρ', step tid ρ ρ' > 0 -> spec_transition ρ' (f tid ρ'))) ->
    ((μ1 None > 0)%R -> spec_transition ρ μ2) ->
    spec_transition ρ μ.
  Proof.
    intros -> ??.
    by apply spec_transition_bind.
  Qed.
End spec_transition.

Class foxtrotWpGS (Λ : conLanguage) (Σ : gFunctors) := FoxtrotWpGS {
  foxtrotWpGS_invGS :: invGS_gen HasNoLc Σ;
  state_interp : state Λ → iProp Σ;
  fork_post: val Λ -> iProp Σ;
  err_interp : nonnegreal → iProp Σ;
}.
Global Opaque foxtrotWpGS_invGS.
Global Arguments FoxtrotWpGS {Λ Σ}.
Canonical Structure NNRO := leibnizO nonnegreal.


Section modalities.
  Context `{foxtrotWpGS con_prob_lang Σ}.
  Implicit Types ε : nonnegreal.

  (** state_step_coupl *)
  Definition state_step_coupl_pre Z Φ : (state con_prob_lang * cfg con_prob_lang * nonnegreal -> iProp Σ) :=
    (λ x,
      let '(σ1, ρ, ε) := x in
      ⌜(1<=ε)%R⌝ ∨
        Z σ1 ρ ε ∨
        ∃ (S: state con_prob_lang -> cfg con_prob_lang -> Prop) μ
          (ε1 ε2: nonnegreal),
          ⌜spec_transition ρ μ ⌝ ∗
          ⌜ ε1 + ε2 <= ε ⌝ ∗
          ⌜ ARcoupl (dret σ1) μ S ε1 ⌝ ∗
          ∀ ρ', ⌜S σ1 ρ'⌝ ={∅}=∗ Φ (σ1, ρ', ε2)
    )%I.
      (* ( ∃ μ (ε2 : state con_prob_lang -> nonnegreal), *)
          (* ⌜ sch_erasable (λ t _ _ sch, TapeOblivious t sch) μ σ1 ⌝ ∗ *)
          (* ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗ *)
          (* ⌜ (Expval μ ε2 <= ε)%R ⌝ ∗ *)
          (* ∀ σ2, |={∅}=> Φ (σ2, ε2 σ2)))%I. *)

    
(*   #[local] Instance state_step_coupl_pre_ne Z Φ : *)
(*     NonExpansive (state_step_coupl_pre Z Φ). *)
(*   Proof. *)
(*     rewrite /state_step_coupl_pre. *)
(*     intros ?[??][??][[=][=]]. by simplify_eq. *)
(*   Qed. *)

(*   #[local] Instance state_step_coupl_pre_mono Z : BiMonoPred (state_step_coupl_pre Z). *)
(*   Proof. *)
(*     split; [|apply _]. *)
(*     iIntros (Φ Ψ HNEΦ HNEΨ) "#Hwand". *)
(*     iIntros ([??]) "[H|[?|[H|(%&%&%&%&%&H)]]]". *)
(*     - by iLeft. *)
(*     - iRight; by iLeft. *)
(*     - iRight; iRight; iLeft. *)
(*       iIntros (??). *)
(*       iApply "Hwand". *)
(*       by iApply "H". *)
(*     - do 3 iRight. *)
(*       repeat iExists _; repeat (iSplit; [done|]). *)
(*       iIntros (?). *)
(*       iApply "Hwand". *)
(*       by iApply "H". *)
(*   Qed. *)

(*   Definition state_step_coupl' Z := bi_least_fixpoint (state_step_coupl_pre Z). *)
(*   Definition state_step_coupl σ ε Z:= state_step_coupl' Z (σ, ε). *)

(*   Lemma state_step_coupl_unfold σ1 ε Z : *)
(*     state_step_coupl σ1 ε Z ≡ *)
(*       (⌜(1 <= ε)%R⌝ ∨ *)
(*          (Z σ1 ε) ∨ *)
(*          (∀ ε', ⌜(ε<ε')%R⌝ -∗ state_step_coupl σ1 ε' Z) ∨ *)
(*       (∃ μ (ε2 : state con_prob_lang -> nonnegreal), *)
(*           ⌜ sch_erasable (λ t _ _ sch, TapeOblivious t sch) μ σ1 ⌝ ∗ *)
(*           ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗ *)
(*           ⌜ (SeriesC (λ ρ, (μ ρ) * ε2 ρ) <= ε)%R ⌝ ∗ *)
(*           ∀ σ2, |={∅}=> state_step_coupl σ2 (ε2 σ2) Z))%I. *)
(*   Proof. rewrite /state_step_coupl /state_step_coupl' least_fixpoint_unfold //. Qed. *)

(*   Lemma state_step_coupl_ret_err_ge_1 σ1 Z (ε : nonnegreal) : *)
(*     (1 <= ε)%R → ⊢ state_step_coupl σ1 ε Z. *)
(*   Proof. iIntros. rewrite state_step_coupl_unfold. by iLeft. Qed. *)

(*   Lemma state_step_coupl_ret σ1 Z ε : *)
(*     Z σ1 ε -∗ state_step_coupl σ1 ε Z. *)
(*   Proof. iIntros. rewrite state_step_coupl_unfold. by iRight; iLeft. Qed. *)

(*   Lemma state_step_coupl_ampl σ1 Z ε: *)
(*     (∀ ε', ⌜(ε<ε')%R⌝ -∗ state_step_coupl σ1 ε' Z) -∗ state_step_coupl σ1 ε Z. *)
(*   Proof. iIntros. rewrite state_step_coupl_unfold. *)
(*          do 2 iRight; by iLeft. *)
(*   Qed.  *)

(*   Lemma state_step_coupl_ampl' σ1 Z ε: *)
(*     (∀ ε', ⌜(ε<ε'<1)%R⌝ -∗ state_step_coupl σ1 ε' Z) -∗ state_step_coupl σ1 ε Z. *)
(*   Proof. *)
(*     iIntros "H". *)
(*     iApply state_step_coupl_ampl. *)
(*     iIntros (ε' ?). *)
(*     destruct (Rlt_or_le ε' 1)%R. *)
(*     - iApply "H". iPureIntro. lra. *)
(*     - by iApply state_step_coupl_ret_err_ge_1.  *)
(*   Qed.  *)

(*   Lemma state_step_coupl_rec σ1 (ε : nonnegreal) Z : *)
(*     (∃ μ (ε2 : state con_prob_lang -> nonnegreal), *)
(*           ⌜ sch_erasable (λ t _ _ sch, TapeOblivious t sch) μ σ1 ⌝ ∗ *)
(*           ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗ *)
(*           ⌜ (Expval μ ε2 <= ε)%R ⌝ ∗ *)
(*           ∀ σ2, |={∅}=> state_step_coupl σ2 (ε2 σ2) Z)%I *)
(*     ⊢ state_step_coupl σ1 ε Z. *)
(*   Proof. iIntros "H". rewrite state_step_coupl_unfold. repeat iRight. done. Qed. *)

(*   Lemma state_step_coupl_rec_equiv σ1 (ε : nonnegreal) Z : *)
(*     (∃ μ (ε2 : state con_prob_lang -> nonnegreal), *)
(*         ⌜ sch_erasable (λ t _ _ sch, TapeOblivious t sch) μ σ1 ⌝ ∗ *)
(*         ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗ *)
(*                     ⌜ (Expval μ ε2 <= ε)%R ⌝ ∗ *)
(*                     ∀ σ2, |={∅}=> state_step_coupl σ2 (ε2 σ2) Z)%I ⊣⊢ *)
(*     (∃ R μ (ε1 : nonnegreal) (ε2 : state con_prob_lang -> nonnegreal), *)
(*         ⌜ sch_erasable (λ t _ _ sch, TapeOblivious t sch) μ σ1 ⌝ ∗ *)
(*         ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗ *)
(*                     ⌜ (ε1 + Expval μ ε2 <= ε)%R ⌝ ∗ *)
(*                     ⌜pgl μ R ε1⌝ ∗ *)
(*                     ∀ σ2, ⌜ R σ2 ⌝ ={∅}=∗ state_step_coupl σ2 (ε2 σ2) Z)%I. *)
(*   Proof. *)
(*     iSplit. *)
(*     - iIntros "H". *)
(*       iDestruct "H" as "(%μ & %ε2 & % & [%r %] & %Hineq  &H)". *)
(*       iExists (λ _, True), μ, 0, (λ σ, if bool_decide (μ σ > 0)%R then ε2 σ else 1). *)
(*       repeat iSplit; first done. *)
(*       + iPureIntro. exists (Rmax r 1). *)
(*         intros; case_bool_decide. *)
(*         * etrans; last apply Rmax_l. done. *)
(*         * simpl. apply Rmax_r. *)
(*       + simpl. iPureIntro. rewrite Rplus_0_l. etrans; last exact. *)
(*         rewrite /Expval. apply Req_le. *)
(*         apply SeriesC_ext. *)
(*         intros n. case_bool_decide; first done. *)
(*         destruct (pmf_pos μ n) as [K|K]. *)
(*         * exfalso. apply Rlt_gt in K. naive_solver. *)
(*         * simpl. rewrite -K. lra. *)
(*       + iPureIntro. by apply pgl_trivial. *)
(*       + iIntros. case_bool_decide; first done. *)
(*         by iApply state_step_coupl_ret_err_ge_1. *)
(*     - iIntros "H". *)
(*       iDestruct "H" as "(%R & %μ & %ε1 & %ε2 & % & [%r %] & %Hineq & %Hpgl &H)". *)
(*       iExists μ, (λ σ, if bool_decide(R σ) then ε2 σ else 1). *)
(*       repeat iSplit; try done. *)
(*       + iPureIntro. exists (Rmax r 1). *)
(*         intros; case_bool_decide. *)
(*         * etrans; last apply Rmax_l. done. *)
(*         * simpl. apply Rmax_r. *)
(*       + rewrite /Expval in Hineq. rewrite /Expval. iPureIntro. *)
(*         rewrite /pgl/prob in Hpgl. etrans; last exact. *)
(*         etrans; last (apply Rplus_le_compat_r; exact). *)
(*         rewrite -SeriesC_plus. *)
(*         * apply SeriesC_le. *)
(*           -- intros. split; first (case_bool_decide; real_solver). *)
(*              case_bool_decide; simpl; try lra. *)
(*              rewrite Rmult_1_r. apply Rplus_le_0_compat. *)
(*              real_solver. *)
(*           -- apply ex_seriesC_plus. *)
(*              ++ apply (ex_seriesC_le _ μ); last done. *)
(*                 intros. case_bool_decide; by simpl. *)
(*              ++ apply pmf_ex_seriesC_mult_fn. naive_solver. *)
(*         * apply (ex_seriesC_le _ μ); last done. *)
(*           intros. case_bool_decide; by simpl. *)
(*         * apply pmf_ex_seriesC_mult_fn. naive_solver. *)
(*       + iIntros. case_bool_decide. *)
(*         * iApply ("H" with "[//]"). *)
(*         * by iApply state_step_coupl_ret_err_ge_1. *)
(*   Qed. *)

(*   Lemma state_step_coupl_rec' σ1 (ε : nonnegreal) Z : *)
(*     (∃ R μ (ε1 : nonnegreal) (ε2 : state con_prob_lang -> nonnegreal), *)
(*           ⌜ sch_erasable (λ t _ _ sch, TapeOblivious t sch) μ σ1 ⌝ ∗ *)
(*           ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗ *)
(*           ⌜ (ε1 + Expval μ ε2 <= ε)%R ⌝ ∗ *)
(*           ⌜pgl μ R ε1⌝ ∗ *)
(*           ∀ σ2, ⌜ R σ2 ⌝ ={∅}=∗ state_step_coupl σ2 (ε2 σ2) Z)%I *)
(*     ⊢ state_step_coupl σ1 ε Z. *)
(*   Proof. *)
(*     iIntros. iApply state_step_coupl_rec. by rewrite state_step_coupl_rec_equiv. *)
(*   Qed. *)
      

(*   Lemma state_step_coupl_ind (Ψ Z : state con_prob_lang → nonnegreal → iProp Σ) : *)
(*     ⊢ (□ (∀ σ ε, *)
(*              state_step_coupl_pre Z (λ '(σ, ε'), *)
(*                  Ψ σ ε' ∧ state_step_coupl σ ε' Z)%I (σ, ε) -∗ Ψ σ ε) → *)
(*        ∀ σ ε, state_step_coupl σ ε Z -∗ Ψ σ ε)%I. *)
(*   Proof. *)
(*     iIntros "#IH" (σ ε) "H". *)
(*     set (Ψ' := (λ '(σ, ε), Ψ σ ε) : *)
(*            (prodO (stateO con_prob_lang) NNRO) → iProp Σ). *)
(*     assert (NonExpansive Ψ'). *)
(*     { intros n [σ1 ε1] [σ2 ε2]. *)
(*       intros [[=][=]]. *)
(*       by simplify_eq/=. } *)
(*     iApply (least_fixpoint_ind _ Ψ' with "[] H"). *)
(*     iIntros "!#" ([? ?]) "H". by iApply "IH". *)
(*   Qed. *)

(*   Lemma fupd_state_step_coupl σ1 Z (ε : nonnegreal) : *)
(*     (|={∅}=> state_step_coupl σ1 ε Z) ⊢ state_step_coupl σ1 ε Z. *)
(*   Proof. *)
(*     iIntros "H". *)
(*     iApply state_step_coupl_rec'. *)
(*     iExists (λ x, x= σ1), (dret σ1), nnreal_zero, (λ _, ε). *)
(*     repeat iSplit. *)
(*     - iPureIntro. apply dret_sch_erasable. *)
(*     - iPureIntro. naive_solver. *)
(*     - simpl. iPureIntro. rewrite Expval_const; last done. *)
(*       rewrite dret_mass. lra. *)
(*     - iPureIntro. *)
(*       by apply pgl_dret. *)
(*     - by iIntros (? ->). *)
(*   Qed. *)
  
(*   Lemma state_step_coupl_mono σ1 Z1 Z2 ε : *)
(*     (∀ σ2 ε', Z1 σ2 ε' -∗ Z2 σ2 ε') -∗ *)
(*     state_step_coupl σ1 ε Z1 -∗ state_step_coupl σ1 ε Z2. *)
(*   Proof. *)
(*     iIntros "HZ Hs". *)
(*     iRevert "HZ". *)
(*     iRevert (σ1 ε) "Hs". *)
(*     iApply state_step_coupl_ind. *)
(*     iIntros "!#" (σ ε) *)
(*       "[% | [? | [H|(% & % & % & % & % & H)]]] Hw". *)
(*     - iApply state_step_coupl_ret_err_ge_1. lra. *)
(*     - iApply state_step_coupl_ret. by iApply "Hw". *)
(*     - iApply state_step_coupl_ampl. *)
(*       iIntros (??). *)
(*       by iApply "H". *)
(*     - iApply state_step_coupl_rec. *)
(*       repeat iExists _. *)
(*       repeat iSplit; try done. *)
(*       iIntros (?). *)
(*       iMod ("H" $! σ2) as "[IH _]". *)
(*       by iApply "IH". *)
(*   Qed. *)

(*   Lemma state_step_coupl_mono_err ε1 ε2 σ1 Z : *)
(*     (ε1 <= ε2)%R → state_step_coupl σ1 ε1 Z -∗ state_step_coupl σ1 ε2 Z. *)
(*   Proof. *)
(*     iIntros (Heps) "Hs". *)
(*     iApply state_step_coupl_rec'. *)
(*     set (ε' := nnreal_minus ε2 ε1 Heps). *)
(*     iExists (λ x, x=σ1), (dret σ1), nnreal_zero, (λ _, ε1). *)
(*     repeat iSplit. *)
(*     - iPureIntro. apply dret_sch_erasable. *)
(*     - iPureIntro; naive_solver. *)
(*     - iPureIntro. simpl. rewrite Expval_const; last done. rewrite dret_mass; lra. *)
(*     - iPureIntro. by apply pgl_dret. *)
(*     - by iIntros (?->). *)
(*   Qed. *)
  
(*   Lemma state_step_coupl_bind σ1 Z1 Z2 ε : *)
(*     (∀ σ2 ε', Z1 σ2 ε' -∗ state_step_coupl σ2 ε' Z2) -∗ *)
(*     state_step_coupl σ1 ε Z1 -∗ *)
(*     state_step_coupl σ1 ε Z2. *)
(*   Proof. *)
(*     iIntros "HZ Hs". *)
(*     iRevert "HZ". *)
(*     iRevert (σ1 ε) "Hs". *)
(*     iApply state_step_coupl_ind. *)
(*     iIntros "!#" (σ ε) *)
(*       "[% | [H | [H|(% & % & % & % & % & H)]]] HZ". *)
(*     - by iApply state_step_coupl_ret_err_ge_1. *)
(*     - iApply ("HZ" with "H"). *)
(*     - iApply state_step_coupl_ampl. *)
(*       iIntros (??). *)
(*       iDestruct ("H" with "[//]") as "[H _]". *)
(*       by iApply "H". *)
(*     - iApply state_step_coupl_rec. *)
(*       repeat iExists _. *)
(*       repeat iSplit; try done. *)
(*       iIntros (?). *)
(*       iMod ("H" $! _) as "[H _]". *)
(*       by iApply "H". *)
(*   Qed. *)
  
(*   Lemma state_step_coupl_state_step α σ1 Z (ε ε' : nonnegreal) : *)
(*     α ∈ get_active σ1 → *)
(*     (∃ R, ⌜pgl (state_step σ1 α) R ε⌝ ∗ *)
(*           ∀ σ2 , ⌜R σ2 ⌝ ={∅}=∗ state_step_coupl σ2 ε' Z) *)
(*     ⊢ state_step_coupl σ1 (ε + ε') Z. *)
(*   Proof. *)
(*     iIntros (Hin) "(%R&%&H)". *)
(*     iApply state_step_coupl_rec'. *)
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

(*   Lemma state_step_coupl_iterM_state_adv_comp N α σ1 Z (ε : nonnegreal) : *)
(*     (α ∈ get_active σ1 -> *)
(*      (∃ R ε1 (ε2 : _ -> nonnegreal), *)
(*         ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗ *)
(*         ⌜ (ε1 + Expval (iterM N (λ σ, state_step σ α) σ1) ε2 <= ε)%R ⌝ ∗ *)
(*         ⌜pgl (iterM N (λ σ, state_step σ α) σ1) R ε1⌝ ∗ *)
(*         ∀ σ2, ⌜ R σ2 ⌝ ={∅}=∗ state_step_coupl σ2 (ε2 σ2) Z) *)
(*       ⊢ state_step_coupl σ1 ε Z)%I. *)
(*   Proof. *)
(*     iIntros (Hin) "(%R & %ε1 & %ε2 & % & %Hε & % & H)". *)
(*     iApply state_step_coupl_rec'. *)
(*     iExists R, _, ε1, ε2. *)
(*     repeat iSplit; try done. *)
(*     - iPureIntro. *)
(*       simpl in *. *)
(*       rewrite elem_of_elements elem_of_dom in Hin. *)
(*       destruct Hin. *)
(*       by eapply iterM_state_step_sch_erasable. *)
(*   Qed.  *)
  
(*   Lemma state_step_coupl_state_adv_comp α σ1 Z (ε : nonnegreal) : *)
(*     (α ∈ get_active σ1 -> *)
(*      (∃ R ε1 (ε2 : _ -> nonnegreal), *)
(*         ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗ *)
(*         ⌜ (ε1 + Expval (state_step σ1 α) ε2 <= ε)%R ⌝ ∗ *)
(*         ⌜pgl (state_step σ1 α) R ε1⌝ ∗ *)
(*         ∀ σ2, ⌜ R σ2 ⌝ ={∅}=∗ state_step_coupl σ2 (ε2 σ2) Z) *)
(*       ⊢ state_step_coupl σ1 ε Z)%I. *)
(*   Proof. *)
(*     iIntros (Hin) "(%R & %ε1 & %ε2 & % & %Hε & % & H)". *)
(*     iApply (state_step_coupl_iterM_state_adv_comp 1%nat); first done. *)
(*     repeat iExists _. simpl. rewrite dret_id_right. *)
(*     by repeat iSplit. *)
(*   Qed. *)
  

(*   (** * One step prog coupl *) *)

(*   Definition prog_coupl e1 σ1 ε Z : iProp Σ := *)
(*     (∃ (ε2 : (expr con_prob_lang * state con_prob_lang * list (expr con_prob_lang)) -> nonnegreal), *)
(*            ⌜reducible e1 σ1⌝ ∗ *)
(*            ⌜∃ r, ∀ ρ, (ε2 ρ <= r)%R ⌝ ∗ *)
(*            ⌜(Expval (prim_step e1 σ1) ε2 <= ε)%R⌝ ∗ *)
(*            (∀ e2 σ2 efs, |={∅}=> *)
(*                          Z e2 σ2 efs (ε2 (e2, σ2, efs))) *)
(*        )%I. *)
  
(*   Definition prog_coupl_equiv1 e1 σ1 ε Z: *)
(*     (∀ e2 σ2 efs, Z e2 σ2 efs 1) -∗ *)
(*     prog_coupl e1 σ1 ε Z -∗ *)
(*     (∃ R (ε1 : nonnegreal) (ε2 : (expr con_prob_lang * state con_prob_lang * list (expr con_prob_lang)) -> nonnegreal), *)
(*            ⌜reducible e1 σ1⌝ ∗ *)
(*            ⌜∃ r, ∀ ρ, (ε2 ρ <= r)%R ⌝ ∗ *)
(*            ⌜(ε1 + Expval (prim_step e1 σ1) ε2 <= ε)%R⌝ ∗ *)
(*            ⌜pgl (prim_step e1 σ1) R ε1⌝ ∗ *)
(*            (∀ e2 σ2 efs, ⌜R (e2, σ2, efs)⌝ ={∅}=∗ *)
(*                          Z e2 σ2 efs (ε2 (e2, σ2, efs))) *)
(*     )%I. *)
(*   Proof. *)
(*     rewrite /prog_coupl. *)
(*     iIntros "H1 H". *)
(*     iDestruct "H" as "(%ε2 & % & [%r %] & %Hineq  &H)". *)
(*     iExists (λ _, True), 0, (λ x, if bool_decide (prim_step e1 σ1 x > 0)%R then ε2 x else 1). *)
(*     repeat iSplit; first done. *)
(*     - iPureIntro. exists (Rmax r 1). *)
(*       intros; case_bool_decide. *)
(*       + etrans; last apply Rmax_l. done. *)
(*       + simpl. apply Rmax_r. *)
(*     - simpl. iPureIntro. rewrite Rplus_0_l. etrans; last exact. *)
(*       rewrite /Expval. apply Req_le. *)
(*       apply SeriesC_ext. *)
(*       intros n. case_bool_decide; first done. *)
(*       destruct (pmf_pos (prim_step e1 σ1) n) as [K|K]. *)
(*       + exfalso. apply Rlt_gt in K. naive_solver. *)
(*       + simpl. rewrite -K. lra. *)
(*     - iPureIntro. by apply pgl_trivial. *)
(*     - iIntros. case_bool_decide; done. *)
(*   Qed. *)

(*   Definition prog_coupl_equiv2 e1 σ1 ε Z: *)
(*     (∀ e2 σ2 efs, Z e2 σ2 efs 1) -∗ *)
(*     (∃ R (ε1 : nonnegreal) (ε2 : (expr con_prob_lang * state con_prob_lang * list (expr con_prob_lang)) -> nonnegreal), *)
(*         ⌜reducible e1 σ1⌝ ∗ *)
(*         ⌜∃ r, ∀ ρ, (ε2 ρ <= r)%R ⌝ ∗ *)
(*                    ⌜(ε1 + Expval (prim_step e1 σ1) ε2 <= ε)%R⌝ ∗ *)
(*                    ⌜pgl (prim_step e1 σ1) R ε1⌝ ∗ *)
(*                    (∀ e2 σ2 efs, ⌜R (e2, σ2, efs)⌝ ={∅}=∗ *)
(*                                  Z e2 σ2 efs (ε2 (e2, σ2, efs))) *)
(*     )%I-∗ *)
(*     prog_coupl e1 σ1 ε Z. *)
(*   Proof.  *)
(*     iIntros "H1 H". *)
(*     iDestruct "H" as "(%R & %ε1 & %ε2 & % & [%r %] & %Hineq & %Hpgl &H)". *)
(*     iExists (λ σ, if bool_decide(R σ) then ε2 σ else 1). *)
(*     repeat iSplit; try done. *)
(*     - iPureIntro. exists (Rmax r 1). *)
(*       intros; case_bool_decide. *)
(*       + etrans; last apply Rmax_l. done. *)
(*       + simpl. apply Rmax_r. *)
(*     - rewrite /Expval in Hineq. rewrite /Expval. iPureIntro. *)
(*       rewrite /pgl/prob in Hpgl. etrans; last exact. *)
(*       etrans; last (apply Rplus_le_compat_r; exact). *)
(*       rewrite -SeriesC_plus. *)
(*       + apply SeriesC_le. *)
(*         * intros. split; first (case_bool_decide; real_solver). *)
(*           case_bool_decide; simpl; try lra. *)
(*           rewrite Rmult_1_r. apply Rplus_le_0_compat. *)
(*           real_solver. *)
(*         * apply ex_seriesC_plus. *)
(*           -- apply (ex_seriesC_le _ (prim_step e1 σ1)); last done. *)
(*              intros. case_bool_decide; by simpl. *)
(*           -- apply pmf_ex_seriesC_mult_fn. naive_solver. *)
(*       + apply (ex_seriesC_le _ (prim_step e1 σ1)); last done. *)
(*         intros. case_bool_decide; by simpl. *)
(*       + apply pmf_ex_seriesC_mult_fn. naive_solver. *)
(*     - iIntros. case_bool_decide; last done. *)
(*       iApply ("H" with "[//]"). *)
(*   Qed.  *)

(*   Lemma prog_coupl_mono_err e σ Z ε ε': *)
(*     (ε<=ε')%R -> prog_coupl e σ ε Z -∗ prog_coupl e σ ε' Z. *)
(*   Proof. *)
(*     iIntros (?) "(%&%&%&%&H)". *)
(*     repeat iExists _. *)
(*     repeat iSplit; try done. *)
(*     iPureIntro. *)
(*     etrans; exact. *)
(*   Qed. *)

(*   Lemma prog_coupl_strong_mono e1 σ1 Z1 Z2 ε : *)
(*     □(∀ e2 σ2 efs, Z2 e2 σ2 efs 1) -∗ *)
(*     (∀ e2 σ2 ε' efs, ⌜∃ σ, (prim_step e1 σ (e2, σ2, efs) > 0)%R⌝ ∗ Z1 e2 σ2 efs ε' -∗ Z2 e2 σ2 efs ε') -∗ *)
(*     prog_coupl e1 σ1 ε Z1 -∗ prog_coupl e1 σ1 ε Z2. *)
(*   Proof. *)
(*     iIntros "#H1 Hm (%&%&[%r %]&%Hineq & Hcnt) /=". *)
(*     rewrite /prog_coupl. *)
(*     iExists (λ x, if bool_decide (∃ σ, prim_step e1 σ x >0)%R then ε2 x else 1). *)
(*     repeat iSplit. *)
(*     - done. *)
(*     - iPureIntro. exists (Rmax r 1). *)
(*       intros; case_bool_decide. *)
(*       + etrans; last apply Rmax_l. done. *)
(*       + simpl. apply Rmax_r. *)
(*     - rewrite /Expval in Hineq. rewrite /Expval. iPureIntro. *)
(*       rewrite /Expval. etrans; last exact. apply Req_le. *)
(*       apply SeriesC_ext. *)
(*       intros n. case_bool_decide; first done. *)
(*       destruct (pmf_pos (prim_step e1 σ1) n) as [K|K]. *)
(*       + exfalso. apply Rlt_gt in K. naive_solver. *)
(*       + simpl. rewrite -K. lra. *)
(*     - simpl. iIntros (???). *)
(*       case_bool_decide; last done. *)
(*       iApply "Hm". iMod ("Hcnt" $! _ _ _). *)
(*       by iFrame. *)
(*   Qed. *)

(*   Lemma prog_coupl_mono e1 σ1 Z1 Z2 ε : *)
(*     (∀ e2 σ2 efs ε', Z1 e2 σ2 efs ε' -∗ Z2 e2 σ2 efs ε') -∗ *)
(*     prog_coupl e1 σ1 ε Z1 -∗ prog_coupl e1 σ1 ε Z2. *)
(*   Proof. *)
(*     iIntros "Hm". *)
(*     rewrite /prog_coupl. *)
(*     iIntros "(%&%&%&%&?)". *)
(*     repeat iExists _; repeat iSplit; try done. *)
(*     iIntros. by iApply "Hm". *)
(*   Qed. *)
(*     Lemma prog_coupl_strengthen e1 σ1 Z ε : *)
(*     □(∀ e2 σ2 efs, Z e2 σ2 efs 1) -∗ *)
(*     prog_coupl e1 σ1 ε Z -∗ *)
(*     prog_coupl e1 σ1 ε (λ e2 σ2 efs ε', ⌜(∃ σ, (prim_step e1 σ (e2, σ2, efs) > 0)%R)\/ (1<=ε')%R⌝ ∧ Z e2 σ2 efs ε'). *)
(*   Proof. *)
(*     iIntros "#Hmono (%&%&[%r %]&%Hineq & Hcnt) /=". *)
(*     rewrite /prog_coupl. *)
(*     iExists (λ x, if bool_decide (∃ σ, prim_step e1 σ x >0)%R then ε2 x else 1). *)
(*     repeat iSplit. *)
(*     - done. *)
(*     - iPureIntro. exists (Rmax r 1). *)
(*       intros; case_bool_decide. *)
(*       + etrans; last apply Rmax_l. done. *)
(*       + simpl. apply Rmax_r. *)
(*     - rewrite /Expval in Hineq. rewrite /Expval. iPureIntro. *)
(*       rewrite /Expval. etrans; last exact. apply Req_le. *)
(*       apply SeriesC_ext. *)
(*       intros n. case_bool_decide; first done. *)
(*       destruct (pmf_pos (prim_step e1 σ1) n) as [K|K]. *)
(*       + exfalso. apply Rlt_gt in K. naive_solver. *)
(*       + simpl. rewrite -K. lra. *)
(*     - simpl. iIntros (???). *)
(*       case_bool_decide. *)
(*       + iMod ("Hcnt" $! _ _ _). *)
(*         iFrame. iPureIntro. naive_solver. *)
(*       + iMod ("Hcnt" $! e2 σ2 efs ). *)
(*         iModIntro. iSplit; last iApply "Hmono". *)
(*         iPureIntro. naive_solver. *)
(*   Qed. *)

(*   Lemma prog_coupl_ctx_bind K `{!ConLanguageCtx K} e1 σ1 Z ε: *)
(*     to_val e1 = None -> *)
(*     □(∀ e2 σ2 efs, Z e2 σ2 efs 1) -∗ *)
(*     prog_coupl e1 σ1 ε (λ e2 σ2 efs ε', Z (K e2) σ2 efs ε') -∗ prog_coupl (K e1) σ1 ε Z. *)
(*   Proof. *)
(*     iIntros (Hv) "#H' H". *)
(*     (* iDestruct (prog_coupl_strengthen with "[][$]") as "H". *) *)
(*     (* { iModIntro. by iIntros. } *) *)
(*     iDestruct "H" as "(%ε2&%&[%r %]&%&H)". *)
(*     (** (classical) inverse of context [K] *) *)
(*     destruct (partial_inv_fun K) as (Kinv & HKinv). *)
(*     assert (∀ e, Kinv (K e) = Some e) as HKinv3. *)
(*     { intro e. *)
(*       destruct (Kinv (K e)) eqn:Heq; *)
(*         eapply HKinv in Heq; by simplify_eq. } *)
(*     set (ε2' := (λ '(e, σ, efs), from_option (λ e', ε2 (e', σ, efs)) 1%NNR (Kinv e))). *)
(*     assert (∀ e2 σ2 efs, ε2' (K e2, σ2, efs) = ε2 (e2, σ2, efs)) as Hε2'. *)
(*     { intros. rewrite /ε2' HKinv3 //. } *)
(*     (* iExists (λ '(e2, σ2, efs), ∃ e2', e2 = K e2' /\ R (e2', σ2, efs)), ε1, ε2'. *) *)
(*     iExists ε2'. *)
(*     repeat iSplit; try iPureIntro. *)
(*     - by apply reducible_fill. *)
(*     - rewrite /ε2'. eexists (Rmax 1%R r). *)
(*       intros [[??]?]. *)
(*       destruct (Kinv _); simpl. *)
(*       + etrans; last apply Rmax_r. done. *)
(*       + apply Rmax_l. *)
(*     - rewrite fill_dmap// Expval_dmap//=; last first. *)
(*       + eapply ex_expval_bounded. simpl. intros [[??]?] => /=. by rewrite HKinv3/=. *)
(*       + etrans; last done. *)
(*         rewrite /Expval. apply Req_le. *)
(*         apply SeriesC_ext. *)
(*         intros [[??]?]. simpl. by rewrite HKinv3/=. *)
(*     (* - rewrite fill_dmap//. *) *)
(*     (*   replace (ε1) with (ε1+0)%NNR; last (apply nnreal_ext; simpl; lra). *) *)
(*     (*   eapply pgl_dbind; try done. *) *)
(*     (*   intros a ?. apply pgl_dret. *) *)
(*     (*   destruct a as [[??]?] => /=. *) *)
(*     (*   naive_solver. *) *)
(*     - iIntros (???). *)
(*       rewrite /ε2'. *)
(*       destruct (Kinv e2) eqn:H'; simpl; last done. *)
(*       apply HKinv in H'. by subst. *)
(*   Qed. *)

  
(*   Lemma prog_coupl_reducible e σ Z ε : *)
(*     prog_coupl e σ ε Z -∗ ⌜reducible e σ⌝. *)
(*   Proof. by iIntros "(%&%&%&%& _)". Qed. *)
 

(*   Lemma prog_coupl_adv_comp e1 σ1 Z (ε : nonnegreal) : *)
(*     □(∀ e2 σ2 efs, Z e2 σ2 efs 1) -∗ *)
(*       (∃ R (ε1 : nonnegreal) (ε2 : _ -> nonnegreal), *)
(*           ⌜reducible e1 σ1⌝ ∗ *)
(*           ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗ *)
(*           ⌜ (ε1 + Expval (prim_step e1 σ1) ε2 <= ε)%R ⌝ ∗ ⌜pgl (prim_step e1 σ1) R ε1⌝ ∗ *)
(*           ∀ e2 σ2 efs, ⌜ R (e2, σ2, efs) ⌝ ={∅}=∗ Z e2 σ2 efs (ε2 (e2, σ2, efs))) -∗ *)
(*         prog_coupl e1 σ1 ε Z. *)
(*   Proof. *)
(*     iIntros "#H' H". *)
(*     by iApply prog_coupl_equiv2. *)
(*   Qed. *)

(*   Lemma prog_coupl_prim_step e1 σ1 Z ε : *)
(*     □(∀ e2 σ2 efs, Z e2 σ2 efs 1) -∗ *)
(*     (∃ R ε1 ε2, ⌜reducible e1 σ1⌝ ∗ ⌜ (ε1 + ε2 <= ε)%R ⌝ ∗ ⌜pgl (prim_step e1 σ1) R ε1⌝ ∗ *)
(*           ∀ e2 σ2 efs, ⌜R (e2, σ2, efs)⌝ ={∅}=∗ Z e2 σ2 efs ε2) -∗ *)
(*      prog_coupl e1 σ1 ε Z. *)
(*   Proof. *)
(*     iIntros "#H' H". *)
(*     iApply prog_coupl_adv_comp; first done. *)
(*     iDestruct "H" as "(%R&%ε1 & %ε2 & % & %& % & H)". *)
(*     iExists R, ε1, (λ _, ε2). *)
(*     repeat iSplit; try done. *)
(*     - iPureIntro. naive_solver. *)
(*     - iPureIntro. rewrite Expval_const; last done. *)
(*       rewrite prim_step_mass; [lra|done]. *)
(*   Qed.  *)

End modalities.

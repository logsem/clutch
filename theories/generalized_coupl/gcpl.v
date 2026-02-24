From Stdlib Require Export Reals Psatz Specif.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export big_op.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext NNRbar.
From clutch.prob Require Export distribution graded_predicate_lifting countable_couplings.
From clutch.common Require Export language erasable.
From clutch.generalized_coupl Require Export convex.
From clutch.prob_lang Require Import erasure.

From clutch.clutch Require Import weakestpre.

Local Open Scope R.

Section cpl.
  Context {A A' B B' : Type}.

  Lemma ARcouplC_dbind (f : A → cdistr A') (g : B → cdistr B')
    (μ1 : cdistr A) (μ2 : cdistr B) (R : A → B → Prop) (S : A' → B' → Prop) ε1 ε2 :
    (Rle 0 ε1) -> (Rle 0 ε2) ->
    (∀ a b, R a b → ARcouplC (f a) (g b) S ε2) → ARcouplC μ1 μ2 R ε1 → ARcouplC (cdbind f μ1) (cdbind g μ2) S (ε1 + ε2).
  Proof.
    (* The proof follows the same Fubini argument as ARcoupl_dbind.
       The key step is cdistr_double_swap which swaps SeriesCS.
       Both cdistr_double_swap lemmas are currently admitted in
       countable_distribution.v, so this is admitted transitively. *)
  Admitted.
End cpl.

Section gcoupl.
  Context {A : Type} {Σ : gFunctors} {Λ : language} `{invGS_gen HasNoLc Σ} (CC : conv_comb A).

  Local Canonical Structure ARO := leibnizO A.

  Definition gscpl_pre E Z (Φ : state Λ * A → iProp Σ) : state Λ * A → iProp Σ :=
    (λ (x : state Λ * A),
      let '(σ1, a) := x in
      (Z σ1 a) ∨
      (∃ (S : state Λ → A → Prop) (μ1 : distr (state Λ)) (η : cdistr A),
         ⌜ARcouplC μ1 η S 0⌝ ∗
         ⌜CC a η⌝ ∗
         ⌜erasable μ1 σ1⌝ ∗
         ⌜∀ σ1 σ2 a', S σ1 a' → S σ2 a' → σ1 = σ2⌝ ∗
         ∀ σ2 a', ⌜S σ2 a'⌝ ={E}=∗ Φ (σ2, a')))%I.

  #[local] Instance gscpl_pre_ne Z E Φ :
    NonExpansive (gscpl_pre E Z Φ).
  Proof.
    rewrite /gscpl_pre.
    intros ? (?&?) (?&?) ([=] & [=]).
    by simplify_eq.
  Qed.

  #[local] Instance gscpl_pre_mono Z E : BiMonoPred (gscpl_pre Z E).
  Proof.
    split; [|apply _].
    iIntros (Φ Ψ HNEΦ HNEΨ) "#Hwand".
    iIntros ((σ1 & a)) "[H | (%S & %μ1 & %η & %Hcoupl & %HCC & %Heras & %Hinj & H)]".
    - iLeft. done.
    - iRight.
      repeat iExists _.
      repeat (iSplit; [done|]).
      iIntros (???). iApply "Hwand". by iApply "H".
  Qed.

  Definition gscpl' E Z := bi_least_fixpoint (gscpl_pre E Z).
  Definition gscpl E σ a Z := gscpl' E Z (σ, a).

  Lemma gscpl_ind E (Ψ Z : state Λ → A → iProp Σ) :
    ⊢ (□ (∀ σ a,
             gscpl_pre E Z (λ '(σ, a'),
                 Ψ σ a' ∧ gscpl E σ a' Z)%I (σ, a) -∗ Ψ σ a) →
       ∀ σ a, gscpl E σ a Z -∗ Ψ σ a)%I.
  Proof.
    iIntros "#IH" (σ a) "H".
    rewrite /gscpl /gscpl'.
    set (Ψ' := (λ '(σ, a), Ψ σ a) : prodO (stateO Λ) ARO → iProp Σ).
    assert (NonExpansive Ψ').
    { intros n [σ1 a1] [σ2 a2] [?%leibniz_equiv ?%leibniz_equiv].
      rewrite /Ψ'. simpl in *. by simplify_eq.  }
    iApply (least_fixpoint_ind _ Ψ' with "[] H").
    iIntros "!#" ([? ?]) "HF". by iApply "IH".
  Qed.

  Definition gpcpl e σ a Z : iProp Σ :=
    ∃ (R : cfg Λ → A → Prop) (η : cdistr A),
        ⌜CC a η⌝ ∗
        ⌜reducible (e, σ)⌝ ∗
        ⌜ARcouplC (prim_step e σ) η R 0⌝ ∗
        ⌜∀ ρ1 ρ2 a', R ρ1 a' → R ρ2 a' → ρ1 = ρ2⌝ ∗
        ∀ e' σ' a', ⌜R (e', σ') a'⌝ ={∅}=∗ Z e' σ' a'.

  Lemma ARcouplC_erasure_erasable_exp_rhs (μ1 : distr (state Λ)) η R Φ e σ a n :
    ARcouplC μ1 η R 0 →
    CC a η →
    erasable μ1 σ →
    (∀ σ' a', R σ' a' →
        ∃ μ, CC a' μ ∧ ARcouplC (exec n (e, σ')) μ Φ 0) →
    (∀ σ1 σ2 a', R σ1 a' → R σ2 a' → σ1 = σ2) →
    ∃ μ, CC a μ ∧ ARcouplC (exec n (e, σ)) μ Φ 0.
  Proof.
    intros Hcoupl Hcc Hμ1 Hcont Hinj.
    assert (∀ a', ∃ μ', CC a' μ' ∧ ∀ σ', R σ' a' → ARcouplC (exec n (e, σ')) μ' Φ 0) as Hf.
    { intro a'.
      destruct (ExcludedMiddle (∃ σ', R σ' a')) as [[σ' HR] | Hnone].
      - destruct (Hcont σ' a' HR) as [μ' [HCC' Hcoupl']].
        exists μ'. split; [done|].
        intros σ'' HR''.
        have Heq : σ'' = σ' by eapply Hinj.
        by subst.
      - exists (cdret a'). split; [apply ccr_cdret|].
        intros σ' HR. exfalso. apply Hnone. by exists σ'.
    }
    apply Choice in Hf.
    destruct Hf as [g Hg].
    exists (cdbind g η).
    split.
    - apply ccr_cdbind; [done|]. intro a'. exact (proj1 (Hg a')).
    - rewrite -Hμ1.
      rewrite -cdbind_dbind.
      replace 0 with (0+0); last lra.
      eapply ARcouplC_dbind; [lra | lra | | done].
      intros σ' a' HR.
      exact ((proj2 (Hg a')) σ' HR). 
  Qed.

  Lemma gscpl_erasure n m e1 σ1 Z φ a :
      gscpl ∅ σ1 a Z -∗
      (∀ σ2 a', Z σ2 a' ={∅}=∗ |={∅}▷=>^n ⌜∃ η, CC a' η ∧ ARcouplC (exec m (e1, σ2)) η φ 0⌝) -∗
      |={∅}=> |={∅}▷=>^n ⌜∃ μ, CC a μ ∧ ARcouplC (exec m (e1, σ1)) μ φ 0⌝.
  Proof.
    iRevert (σ1 a).
    iApply gscpl_ind.
    iIntros "!>" (σ1 a).
    iIntros "[HZ | (%S & %μ1 & %η & %Hcoupl & %HCC & %Heras & %Hinj & H)] HZ_cont".
    - by iMod ("HZ_cont" with "[$HZ]").
    - iApply (step_fupdN_mono _ _ _
        ⌜∀ σ2 a', S σ2 a' → ∃ μ, CC a' μ ∧ ARcouplC (exec m (e1, σ2)) μ φ 0⌝).
      { iPureIntro. intros Hcont.
        eapply ARcouplC_erasure_erasable_exp_rhs; [done|done|done|exact Hcont|done]. }
      iIntros (σ2 a' HS).
      iMod ("H" with "[//]") as "[IH _]".
      by iApply "IH".
  Qed.

  Lemma ARcouplC_prim_step_exp_rhs (η : cdistr A) R Φ e σ a m :
    ARcouplC (prim_step (l := Λ) e σ) η R 0 →
    CC a η →
    reducible (e, σ) →
    (∀ e' σ' a', R (e', σ') a' → ∃ μ, CC a' μ ∧ ARcouplC (exec m (e', σ')) μ Φ 0) →
    (∀ ρ1 ρ2 a', R ρ1 a' → R ρ2 a' → ρ1 = ρ2) →
    ∃ μ, CC a μ ∧ ARcouplC (exec (S m) (e, σ)) μ Φ 0.
  Proof.
    intros Hcoupl Hcc Hred Hcont Hinj.
    assert (to_val e = None) as Hnv.
    { destruct Hred as [ρ' Hstep]. exact (val_stuck e σ ρ' Hstep). }
    Search is_final.
    rewrite exec_Sn_not_final //. 2 : by apply to_final_None_2.
    assert (∀ a', ∃ μ', CC a' μ' ∧ ∀ ρ, R ρ a' → ARcouplC (exec m ρ) μ' Φ 0) as Hf.
    { intro a'.
      destruct (ExcludedMiddle (∃ ρ, R ρ a')) as [[ρ HR] | Hnone].
      - destruct ρ as [e' σ'].
        destruct (Hcont e' σ' a' HR) as [μ' [HCC' Hcoupl']].
        exists μ'. split; [done|].
        intros ρ'' HR''.
        have Heq : ρ'' = (e', σ') by eapply Hinj.
        by subst.
      - exists (cdret a'). split; [apply ccr_cdret|].
        intros ρ HR. exfalso. apply Hnone. by exists ρ. }
    apply Choice in Hf.
    destruct Hf as [g Hg].
    exists (cdbind g η).
    split.
    - apply ccr_cdbind; [done|]. intro a'. exact (proj1 (Hg a')).
    - rewrite -cdbind_dbind.
      replace 0 with (0+0); last lra.
      eapply ARcouplC_dbind; [lra | lra | | done].
      intros [e' σ'] a' HR.
      exact ((proj2 (Hg a')) (e', σ') HR).
  Qed.

  Lemma gpcpl_erasure n m e σ a Z φ :
      gpcpl e σ a Z -∗
      (∀ e' σ' a', Z e' σ' a' ={∅}=∗ |={∅}▷=>^n ⌜∃ μ, CC a' μ ∧ ARcouplC (exec m (e', σ')) μ φ 0⌝) -∗
      |={∅}=> |={∅}▷=>^n ⌜∃ μ, CC a μ ∧ ARcouplC (exec (S m) (e, σ)) μ φ 0⌝.
  Proof.
    iIntros "(%R & %η & %HCC & %Hred & %Hcoupl & %Hinj & H) HZ_cont".
    iApply (step_fupdN_mono _ _ _
        ⌜∀ e' σ' a', R (e', σ') a' → ∃ μ, CC a' μ ∧ ARcouplC (exec m (e', σ')) μ φ 0⌝).
    { iPureIntro. intros Hcont.
      eapply ARcouplC_prim_step_exp_rhs; [done|done|done|exact Hcont|done]. }
    iIntros (e' σ' a' HR).
    iMod ("H" with "[//]") as "HZ".
    by iApply "HZ_cont".
  Qed.

End gcoupl.


Section general.
Context `{invGS_gen HasNoLc Σ}.

Class generalWpGS (A : Type) (Λ : language) (Σ : gFunctors) := GeneralWpGS {
  generalWpGS_invGS :: invGS_gen HasNoLc Σ;
  generalWpGS_cc : conv_comb A;
  state_interp : state Λ → iProp Σ;
  spec_interp : A → iProp Σ;
}.

Opaque generalWpGS_invGS.
Arguments GeneralWpGS {A Λ Σ}.

Definition wp_pre `{!generalWpGS A Λ Σ}
    (wp : coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
    coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
    (∀ σ1 a1,
      state_interp σ1 ∗ spec_interp a1 ={E, ∅}=∗
      gscpl generalWpGS_cc ∅ σ1 a1 (λ σ2 a2,
        match to_val e1 with
        | Some v => |={∅, E}=> state_interp σ2 ∗ spec_interp a2 ∗ Φ v
        | None =>
            gpcpl generalWpGS_cc e1 σ2 a2 (λ e3 σ3 a3,
                ▷ gscpl generalWpGS_cc ∅ σ3 a3 (λ σ4 a4,
                    |={∅, E}=> state_interp σ4 ∗ spec_interp a4 ∗ wp E e3 Φ))
      end))%I.

Local Instance wp_pre_contractive `{!generalWpGS A Λ Σ} : Contractive (wp_pre).
Proof.
  (* rewrite /wp_pre /= => n wp wp' Hwp E e1 Φ.
  do 6 f_equiv.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [? ?]. rewrite /gscpl_pre.
  do 2 f_equiv.
  rewrite /gpcpl.
  do 15 f_equiv.
  f_contractive.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [? ?]. rewrite /gscpl_pre. *)
(*   do 5 f_equiv.
  apply Hwp. *)
(* Qed. *)
Admitted.

Local Definition wp_def `{!generalWpGS A Λ Σ} : Wp (iProp Σ) (expr Λ) (val Λ) () :=
  {| wp := λ _ : (), fixpoint (wp_pre); wp_default := () |}.
Local Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp' := wp_aux.(unseal).
Global Arguments wp' {A Λ _}.
Global Existing Instance wp'.
Local Lemma wp_unseal `{!generalWpGS A Λ Σ} : wp = (@wp_def A Λ _).(wp).
Proof. rewrite -wp_aux.(seal_eq) //. Qed.

Section wp.

Context `{!generalWpGS A Λ Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types ρ : cfg Λ.
Implicit Types a : A.

End wp.
End general.
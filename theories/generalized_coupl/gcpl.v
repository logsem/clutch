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

  Lemma gscpl_unfold E σ a Z :
    gscpl E σ a Z ≡
      (Z σ a ∨
       ∃ (S : state Λ → A → Prop) (μ1 : distr (state Λ)) (η : cdistr A),
          ⌜ARcouplC μ1 η S 0⌝ ∗
          ⌜CC a η⌝ ∗
          ⌜erasable μ1 σ⌝ ∗
          ⌜∀ σ1 σ2 a', S σ1 a' → S σ2 a' → σ1 = σ2⌝ ∗
          ∀ σ2 a', ⌜S σ2 a'⌝ ={E}=∗ gscpl E σ2 a' Z)%I.
  Proof. rewrite /gscpl /gscpl' least_fixpoint_unfold //. Qed.

  Lemma gscpl_ret E σ a Z : Z σ a -∗ gscpl E σ a Z.
  Proof. iIntros "H". rewrite gscpl_unfold. iLeft. done. Qed.

  Lemma gscpl_rec E σ a Z :
    (∃ (S : state Λ → A → Prop) (μ1 : distr (state Λ)) (η : cdistr A),
       ⌜ARcouplC μ1 η S 0⌝ ∗
       ⌜CC a η⌝ ∗
       ⌜erasable μ1 σ⌝ ∗
       ⌜∀ σ1 σ2 a', S σ1 a' → S σ2 a' → σ1 = σ2⌝ ∗
       ∀ σ2 a', ⌜S σ2 a'⌝ ={E}=∗ gscpl E σ2 a' Z)%I
    ⊢ gscpl E σ a Z.
  Proof. iIntros "H". rewrite gscpl_unfold. iRight. done. Qed.

  Lemma fupd_gscpl E σ a Z :
    (|={E}=> gscpl E σ a Z) ⊢ gscpl E σ a Z.
  Proof.
    iIntros "H".
    iApply gscpl_rec.
    iExists (λ σ2 a2, σ2 = σ ∧ a2 = a), (dret σ), (cdret a).
    iSplit.
    { iPureIntro.
      intros f g Hf Hg HS.
      have HLσ : SeriesCS (λ σ', distr_cdistr (dret σ) σ' * f σ') = f σ.
      { erewrite (SeriesCS_ext _ (λ σ', if bool_decide (σ' = σ) then f σ else 0)).
        - apply SeriesCS_singleton.
        - intros σ'. rewrite distr_cdistr_eq dret_pmf_unfold. real_solver. }
      have HLa : SeriesCS (λ a', cdret a a' * g a') = g a.
      { erewrite (SeriesCS_ext _ (λ a', if bool_decide (a' = a) then g a else 0)).
        - apply SeriesCS_singleton.
        - intros a'. rewrite cdret_pmf_unfold. real_solver. }
      rewrite HLσ HLa.
      have := HS σ a (conj eq_refl eq_refl). lra. }
    iSplit; [iPureIntro; apply ccr_cdret|].
    iSplit; [iPureIntro; apply dret_erasable|].
    iSplit; [iPureIntro; intros ??? [-> _] [-> _] => //|].
    iIntros (σ2 a2 [->->]). iExact "H".
  Qed.

  Lemma gscpl_mono E1 E2 σ a Z1 Z2 :
    E1 ⊆ E2 →
    (∀ σ' a', Z1 σ' a' -∗ Z2 σ' a') -∗
    gscpl E1 σ a Z1 -∗ gscpl E2 σ a Z2.
  Proof.
    iIntros (HE) "HZ Hs".
    iRevert "HZ".
    iRevert (σ a) "Hs".
    iApply gscpl_ind.
    iIntros "!#" (σ a) "[HZ | (%S & %μ1 & %η & %Hcoupl & %HCC & %Heras & %Hinj & H)] Hw".
    - iApply gscpl_ret. by iApply "Hw".
    - rewrite gscpl_unfold. iRight.
      iExists S, μ1, η.
      repeat (iSplit; [done|]).
      iIntros (σ2 a' HS).
      iApply fupd_mask_mono; [done|].
      iMod ("H" with "[//]") as "[IH _]".
      by iApply "IH".
  Qed.

  Lemma gscpl_bind E1 E2 σ a Z1 Z2 :
    E1 ⊆ E2 →
    (∀ σ' a', Z1 σ' a' -∗ gscpl E2 σ' a' Z2) -∗
    gscpl E1 σ a Z1 -∗ gscpl E2 σ a Z2.
  Proof.
    iIntros (HE) "HZ Hs".
    iRevert "HZ".
    iRevert (σ a) "Hs".
    iApply gscpl_ind.
    iIntros "!#" (σ a) "[HZ | (%S & %μ1 & %η & %Hcoupl & %HCC & %Heras & %Hinj & H)] Hw".
    - iApply ("Hw" with "HZ").
    - rewrite gscpl_unfold. iRight.
      iExists S, μ1, η.
      repeat (iSplit; [done|]).
      iIntros (σ2 a' HS).
      iApply fupd_mask_mono; [done|].
      iMod ("H" with "[//]") as "[H _]".
      by iApply "H".
  Qed.

  Lemma gpcpl_mono e σ a Z1 Z2 :
    (∀ e' σ' a', Z1 e' σ' a' -∗ Z2 e' σ' a') -∗
    gpcpl e σ a Z1 -∗ gpcpl e σ a Z2.
  Proof.
    iIntros "HZ (%R & %η & %HCC & %Hred & %Hcoupl & %Hinj & H)".
    iExists R, η.
    iSplit; [done|]. iSplit; [done|]. iSplit; [done|]. iSplit; [done|].
    iIntros (e' σ' a' HR).
    iMod ("H" with "[//]") as "HZ1".
    by iApply "HZ".
  Qed.

  Lemma ARcouplC_pos_R_cfg (μ1 : distr (cfg Λ)) (η : cdistr A) (R : cfg Λ → A → Prop) ε :
    ARcouplC μ1 η R ε → ARcouplC μ1 η (λ ρ a, R ρ a ∧ μ1 ρ > 0) ε.
  Proof.
  Admitted.
  (*   intros Hcoupl f g Hf Hg HS.
    set (f' := λ ρ, if Rlt_dec 0 (μ1 ρ) then f ρ else 0).
    have Hf'f : SeriesCS (λ ρ, distr_cdistr μ1 ρ * f' ρ) =
                  SeriesCS (λ ρ, distr_cdistr μ1 ρ * f ρ).
    { apply SeriesCS_ext => ρ. rewrite /f'.
      destruct (Rlt_dec 0 (μ1 ρ)) as [H | H]; [done|].
      rewrite /distr_cdistr /=. have Hzρ : μ1 ρ = 0 by lra. rewrite Hzρ. lra. }
    have Hf'bound : ∀ ρ, 0 ≤ f' ρ ≤ 1.
    { intros ρ. rewrite /f'. destruct (Rlt_dec 0 (μ1 ρ)); [apply Hf|lra]. }
    have Hf'R : ∀ ρ a, R ρ a → f' ρ ≤ g a.
    { intros ρ a HR. rewrite /f'. destruct (Rlt_dec 0 (μ1 ρ)) as [Hpos|Hnpos].
      - apply HS. exact (conj HR Hpos).
      - have : 0 ≤ g a := (Hg a).1. lra. }
    rewrite -Hf'f.
    exact (Hcoupl f' g Hf'bound Hg Hf'R).
  Qed. *)

  Lemma gpcpl_strengthen e σ a Z :
    gpcpl e σ a Z -∗
    gpcpl e σ a (λ e' σ' a', ⌜prim_step e σ (e', σ') > 0⌝ ∧ Z e' σ' a').
  Proof.
    iIntros "(%R & %η & %HCC & %Hred & %Hcoupl & %Hinj & H)".
    iExists (λ ρ a', R ρ a' ∧ prim_step e σ ρ > 0), η.
    iSplit; [done|]. iSplit; [done|].
    iSplit; [iPureIntro; by apply ARcouplC_pos_R_cfg|].
    iSplit; [iPureIntro; intros ρ1 ρ2 a' [HR1 _] [HR2 _]; by eapply Hinj|].
    iIntros (e' σ' a' [HR Hprim]).
    iSpecialize ("H" $! _ _ _ HR).
    iMod "H". iModIntro.
    iSplit; [done|].
    by iApply "H".
  Qed.

  Lemma gpcpl_reducible e σ a Z : gpcpl e σ a Z -∗ ⌜reducible (e, σ)⌝.
  Proof. by iIntros "(%&%&%&%& _)". Qed.

  Lemma ARcouplC_dmap_l (f : cfg Λ → cfg Λ) `{!Inj (=) (=) f}
      (μ1 : distr (cfg Λ)) (μ2 : cdistr A) (R : cfg Λ → A → Prop) ε :
    ARcouplC μ1 μ2 R ε →
    ARcouplC (dmap f μ1) μ2 (λ ρ a, ∃ ρ', ρ = f ρ' ∧ R ρ' a) ε.
  Proof.
    (* Key step: SeriesC (λ ρ, dmap f μ1 ρ * h ρ) = SeriesC (λ ρ', μ1 ρ' * h (f ρ')).
       This is Fubini for distr and requires distr_double_swap, currently admitted. *)
  Admitted.

  Lemma gpcpl_ctx_bind K `{!LanguageCtx K} e σ a Z :
    to_val e = None →
    gpcpl e σ a (λ e' σ' a', Z (K e') σ' a') -∗
    gpcpl (K e) σ a Z.
  Proof.
    iIntros (Hv) "(%R & %η & %HCC & %Hred & %Hcoupl & %Hinj & H)".
    iExists (λ '(e2, σ2) a', ∃ e2', e2 = K e2' ∧ R (e2', σ2) a'), η.
    iSplit; [done|].
    iSplit; [iPureIntro; exact (reducible_fill (K:=K) _ _ Hred)|].
    iSplit.
  Admitted.
  (*   { iPureIntro. rewrite fill_dmap //.
      apply (ARcouplC_dmap_l (fill_lift K)).
      eapply (ARcouplC_mono_R R); [|done].
      intros ρ a' HR. exact ⟨ρ, eq_refl, HR⟩. }
    iSplit.
    { iPureIntro. intros [e1 σ1] [e2 σ2] a' [e1' [-> HR1]] [e2' [-> HR2]].
      have := Hinj (e1', σ1) (e2', σ2) a' HR1 HR2.
      intros [=He Hσ]. f_equal; [by apply fill_inj|done]. }
    iIntros (e2 σ2 a' [e2' [-> HR]]).
    by iApply "H".
  Qed. *)

End gcoupl.


Section generic.
Context `{invGS_gen HasNoLc Σ}.

Class genericWpGS (A : Type) (Λ : language) (Σ : gFunctors) := GenericWpGS {
  genericWpGS_invGS :: invGS_gen HasNoLc Σ;
  state_interp : state Λ → iProp Σ;
  spec_interp : A → iProp Σ;
  spec_cc : conv_comb A;
}.

Opaque genericWpGS_invGS.
Arguments GenericWpGS {A Λ Σ}.

Definition wp_pre `{!genericWpGS A Λ Σ}
    (wp : coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
    coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
    (∀ σ1 a1,
      state_interp σ1 ∗ spec_interp a1 ={E, ∅}=∗
      gscpl spec_cc ∅ σ1 a1 (λ σ2 a2,
        match to_val e1 with
        | Some v => |={∅, E}=> state_interp σ2 ∗ spec_interp a2 ∗ Φ v
        | None =>
            gpcpl spec_cc e1 σ2 a2 (λ e3 σ3 a3,
                ▷ gscpl spec_cc ∅ σ3 a3 (λ σ4 a4,
                    |={∅, E}=> state_interp σ4 ∗ spec_interp a4 ∗ wp E e3 Φ))
      end))%I.

Local Instance wp_pre_contractive `{!genericWpGS A Λ Σ} : Contractive (wp_pre).
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

Local Definition wp_def `{!genericWpGS A Λ Σ} : Wp (iProp Σ) (expr Λ) (val Λ) () :=
  {| wp := λ _ : (), fixpoint (wp_pre); wp_default := () |}.
Local Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp' := wp_aux.(unseal).
Global Arguments wp' {A Λ _}.
Global Existing Instance wp'.
Local Lemma wp_unseal `{!genericWpGS A Λ Σ} : wp = (@wp_def A Λ _).(wp).
Proof. rewrite -wp_aux.(seal_eq) //. Qed.

End generic.

Section wp.

Context `{!genericWpGS A Λ Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types ρ : cfg Λ.
Implicit Types a : A.

Local Notation CC := spec_cc.

Lemma wp_unfold E e Φ s :
  WP e @ s; E {{ Φ }} ⊣⊢ wp_pre (wp (PROP:=iProp Σ) s) E e Φ.
Proof. rewrite wp_unseal. apply (fixpoint_unfold wp_pre). Qed.

Global Instance wp_ne E e n s :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp (PROP:=iProp Σ) s E e).
Proof. Admitted.

Global Instance wp_proper E e s :
  Proper (pointwise_relation _ (≡) ==> (≡)) (wp (PROP:=iProp Σ) s E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne=>v; apply equiv_dist.
Qed.

Global Instance wp_contractive E e n s :
  TCEq (to_val e) None →
  Proper (pointwise_relation _ (dist_later n) ==> dist n) (wp (PROP:=iProp Σ) s E e).
Proof. Admitted.

Lemma wp_value_fupd' E Φ v s : (|={E}=> Φ v) ⊢ WP of_val v @ s; E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre to_of_val.
  iIntros "H" (σ1 a1) "(?&?)".
  iApply gscpl_ret.
  iMod "H". iFrame.
  iApply fupd_mask_subseteq.
  set_solver.
Qed.

Lemma wp_strong_mono E1 E2 e Φ Ψ s :
  E1 ⊆ E2 →
  WP e @ s; E1 {{ Φ }} -∗
  (∀ σ1 a1 v,
      state_interp σ1 ∗ spec_interp a1 ∗ Φ v -∗
      gscpl CC ∅ σ1 a1 (λ σ2 a2,
           |={E2}=> state_interp σ2 ∗ spec_interp a2 ∗ Ψ v)) -∗
  WP e @ s; E2 {{ Ψ }}.
Proof.
  iIntros (HE) "H HΦ". iLöb as "IH" forall (e E1 E2 HE Φ Ψ s).
  rewrite !wp_unfold /wp_pre /=.
  iIntros (σ1 a1) "(Hσ & Hs)".
  iSpecialize ("H" with "[$]").
  iMod (fupd_mask_subseteq E1) as "Hclose"; [done|].
  iMod "H"; iModIntro.
  iApply (gscpl_bind with "[-H] H"); [done|].
  iIntros (σ2 a2) "H".
  destruct (to_val e) as [v|] eqn:?.
  { iApply fupd_gscpl.
    iMod "H" as "(?&?)".
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iSpecialize ("HΦ" with "[$]").
    iApply (gscpl_bind with "[-HΦ] HΦ"); [done|].
    iIntros (σ3 a3) "Hσ".
    iApply gscpl_ret.
    iMod "Hclose'". iMod "Hclose".
    by iMod "Hσ". }
  iApply gscpl_ret.
  iApply (gpcpl_mono with "[HΦ Hclose] H").
  iIntros (e2 σ3 a3) "H !>".
  iApply (gscpl_mono with "[HΦ Hclose] H"); [done|].
  iIntros (σ4 a4) "> ($ & $ & H)".
  iMod "Hclose" as "_".
  iModIntro.
  by iApply ("IH" with "[] H").
Qed.

Lemma wp_strong_mono' E1 E2 e Φ Ψ s :
  E1 ⊆ E2 →
  WP e @ s; E1 {{ Φ }} -∗
  (∀ σ a v,
      state_interp σ ∗ spec_interp a ∗ Φ v ={E2}=∗
      state_interp σ ∗ spec_interp a ∗ Ψ v) -∗
  WP e @ s; E2 {{ Ψ }}.
Proof.
  iIntros (?) "Hwp Hw".
  iApply (wp_strong_mono with "Hwp"); [done|].
  iIntros (σ1 a1 v) "(?&?&?)".
  iApply gscpl_ret.
  by iMod ("Hw" with "[$]").
Qed.

Lemma fupd_wp E e Φ s : (|={E}=> WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre.
  iIntros "H" (σ1 a1) "(Hσ & Hs)".
  destruct (to_val e) as [v|] eqn:?.
  { by iMod ("H" with "[$]"). }
  by iMod ("H" with "[$]").
Qed.

Lemma wp_fupd E e Φ s : WP e @ s; E {{ v, |={E}=> Φ v }} ⊢ WP e @ s; E {{ Φ }}.
Proof.
  iIntros "H".
  iApply (wp_strong_mono E with "H"); [done|].
  iIntros (σ1 a1 v) "(? & ? & ?)".
  iApply gscpl_ret.
  by iFrame.
Qed.

Lemma wp_atomic E1 E2 e Φ `{!Atomic StronglyAtomic e} s :
  (|={E1,E2}=> WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros "H". rewrite !wp_unfold /wp_pre.
  iIntros (σ1 a1) "(Hσ & Hs)".
  iDestruct ("H" with "[$]") as ">> H".
  iModIntro.
  iApply (gscpl_mono with "[] H"); [done|].
  iIntros (σ2 a2) "H".
  destruct (to_val e) as [v|] eqn:?.
  { iDestruct "H" as "> ($ & $ & $)". }
  iDestruct (gpcpl_strengthen with "H") as "H".
  iApply (gpcpl_mono with "[] H").
  iIntros (e2 σ3 a3) "[%Hstep H] !>".
  iApply (gscpl_bind with "[] H"); [done|].
  iIntros (σ4 a4) "H".
  iApply fupd_gscpl.
  iMod "H" as "(Hσ & Hs & H)".
  rewrite !wp_unfold /wp_pre.
  destruct (to_val e2) as [v2|] eqn:He2.
  + iMod ("H" with "[$]") as "H". iModIntro.
    iApply (gscpl_mono with "[] H"); [done|].
    iIntros (σ5 a5) "> ($ & $ & >H)".
    rewrite -(of_to_val e2 v2) //.
    iApply wp_value_fupd'.
    iApply fupd_mask_intro_subseteq; [|done].
    set_solver.
  + iMod ("H" with "[$]") as "H". iModIntro.
    iApply (gscpl_mono with "[] H"); [done|].
    iIntros (σ5 a5) "H".
    iDestruct (gpcpl_reducible with "H") as %[ρ Hr].
    pose proof (atomic _ _ _ Hstep) as [? Hval].
    apply val_stuck in Hr. simplify_eq.
Qed.

Lemma wp_step_fupd E1 E2 e P Φ s :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> P) -∗ WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ s; E1 {{ Φ }}.
Proof.
  rewrite !wp_unfold /wp_pre. iIntros (-> ?) "HR H".
  iIntros (σ1 a1) "Hs". iMod "HR".
  iMod ("H" with "Hs") as "H".
  iModIntro.
  iApply (gscpl_mono with "[HR] H"); [done|].
  iIntros (σ2 a2) "H".
  iApply (gpcpl_mono with "[HR] H").
  iIntros (e3 σ3 a3) "H !>".
  iApply (gscpl_mono with "[HR] H"); [done|].
  iIntros (σ4 a4) "H".
  iMod "H" as "($ & $ & H)".
  iMod "HR".
  iApply (wp_strong_mono E2 with "H"); [done..|].
  iIntros "!>" (σ5 a5 v) "(? & ? & H)".
  iApply gscpl_ret.
  iMod ("H" with "[$]").
  by iFrame.
Qed.

Lemma wp_bind K `{!LanguageCtx K} E e Φ s :
  WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }} ⊢ WP K e @ s; E {{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ s). rewrite !wp_unfold /wp_pre.
  iIntros (σ1 a1) "Hs".
  iMod ("H" with "[$]") as "H".
  iApply (gscpl_bind with "[] H"); [done|].
  iIntros (σ2 a2) "H".
  destruct (to_val e) as [v|] eqn:He.
  { iApply fupd_gscpl.
    iMod "H" as "(Hσ & Hs & H)".
    apply of_to_val in He as <-.
    rewrite wp_unfold /wp_pre.
    by iMod ("H" with "[$]"). }
  rewrite fill_not_val /=; [|done].
  iApply gscpl_ret.
  iApply gpcpl_ctx_bind; [done|].
  iApply (gpcpl_mono with "[] H").
  iIntros (e3 σ3 a3) "H !>".
  iApply (gscpl_mono with "[] H"); [done|].
  iIntros (σ4 a4) "H".
  iMod "H" as "($ & $ & H)".
  iModIntro.
  by iApply "IH".
Qed.

(** * Derived rules *)
Lemma wp_mono E e Φ Ψ s : (∀ v, Φ v ⊢ Ψ v) → WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (wp_strong_mono' with "H"); auto.
  iIntros (???) "($ & $ & ?)". by iApply HΦ.
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
  iIntros (σ1 a1 v) "(? & ? & ?)".
  iApply gscpl_ret. by iFrame.
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
  iIntros (???) "($ & $ & ?)". by iApply "H".
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
  Context `{!genericWpGS A Λ Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  Global Instance frame_wp p E e R Φ Ψ s :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Ψ }}) | 2.
  Proof. rewrite /Frame=> HR. rewrite wp_frame_l. apply wp_mono, HR. Qed.

  Global Instance is_except_0_wp E e Φ s : IsExcept0 (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_wp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_wp p E e P Φ s :
    ElimModal True p false (|==> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r bi.wand_elim_r fupd_wp.
  Qed.

  Global Instance elim_modal_fupd_wp p E e P Φ s :
    ElimModal True p false (|={E}=> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r fupd_wp.
  Qed.

  Global Instance elim_modal_fupd_wp_atomic p E1 E2 e P Φ s :
    ElimModal (Atomic StronglyAtomic e) p false
            (|={E1,E2}=> P) P
            (WP e @ s; E1 {{ Φ }}) (WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }})%I | 100.
  Proof.
    intros ?. rewrite bi.intuitionistically_if_elim fupd_frame_r bi.wand_elim_r wp_atomic //.
  Qed.

  Global Instance add_modal_fupd_wp E e P Φ s :
    AddModal (|={E}=> P) P (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r bi.wand_elim_r fupd_wp. Qed.

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

Section adequacy.
Context `{!genericWpGS A Λ Σ}.
Local Notation CC := spec_cc.

  Lemma wp_adequacy_val_fupd (e : expr Λ) (σ : state Λ) a n φ v:
    to_val e = Some v →
    state_interp σ ∗ spec_interp a ∗
    WP e {{ v, ∀ a', spec_interp a' -∗ ⌜φ v a'⌝ }} ⊢
    |={⊤, ∅}=> ⌜∃ μ, CC a μ ∧ ARcouplC (exec n (e, σ)) μ φ 0⌝.
  Proof.
    iIntros (He) "(Hσ & Hs & Hwp)".
    rewrite wp_unfold /wp_pre /= He.
    iMod ("Hwp" with "[$]") as "Hwp".
    iApply (gscpl_erasure _ 0 with "Hwp").
    iIntros (σ1 a') "> (Hh & Hs & Hp) /=".
    iPoseProof ("Hp" with "Hs") as "%". 
    iApply fupd_mask_intro; [set_solver|]; iIntros "_". 
    iPureIntro. exists (cdret a'). split; first by apply ccr_cdret.
    erewrite exec_is_final; [|done].
    rewrite -cdret_dret.
  Admitted.

End adequacy.

(* Section p.
  Context `(CC : conv_comb A).
  Context {Σ : gFunctors}.
  Context {Λ : language}.

  Axiom spec_frag : A → iProp Σ.
  (* Axiom spec_alloc : ∀ a : A, ⊢ |==> ∃ H : genericWpGS _ Λ Σ, spec_frag . *)
End p. *)
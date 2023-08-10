From Coq Require Export Reals Psatz.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export fixpoint big_op.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.bi Require Export weakestpre.
From clutch.prob Require Export couplings distribution.
From clutch.program_logic Require Export exec language.
From clutch.tpr Require Export spec.

Import uPred.

Local Open Scope R.

Class tprwpG (Λ : language) (Σ : gFunctors) := IrisG {
  iris_invGS :> invGS_gen HasNoLc Σ;
  state_interp : state Λ → iProp Σ;
}.
Global Opaque iris_invGS.
Global Arguments IrisG {Λ Σ}.

(** * A coupling fixpoint for [rwp] *)
Section rwp_coupl.
  Context `{spec A B Σ} `{!tprwpG Λ Σ}.

  Canonical Structure AO := leibnizO A.

  Definition rwp_coupl_pre (Z : cfg Λ → A → iProp Σ) (Φ : cfg Λ * A → iProp Σ) : cfg Λ * A → iProp Σ :=
    (λ (x : cfg Λ * A),
      let '((e1, σ1), a1) := x in
      ∃ R,
        (⌜reducible e1 σ1⌝ ∗
         ⌜Rcoupl (prim_step e1 σ1) (dret a1) R⌝ ∗
         ∀ ρ2, ⌜R ρ2 a1⌝ ={∅}=∗ Z ρ2 a1) ∨
        (⌜Rcoupl (dret (e1, σ1)) (step a1) R⌝ ∗
         ∀ a2, ⌜R (e1, σ1) a2⌝ ={∅}▷=∗ Φ ((e1, σ1), a2)) ∨
        (⌜reducible e1 σ1⌝ ∗
         ⌜Rcoupl (prim_step e1 σ1) (step a1) R⌝ ∗
         ∀ ρ2 a2, ⌜R ρ2 a2⌝ ={∅}▷=∗ Z ρ2 a2)
    )%I.

  #[local] Instance rwp_coupl_pre_ne Z Φ :
    NonExpansive (rwp_coupl_pre Z Φ).
  Proof.
    rewrite /rwp_coupl_pre.
    intros n ((?&?) & ?) ((?&?) & ?) [[[=] [=]] [=]].
    by simplify_eq.
  Qed.

  Local Instance rwp_coupl_pre_mono Z : BiMonoPred (rwp_coupl_pre Z).
  Proof.
    split; [|apply _].
    iIntros (Φ Ψ HNEΦ HNEΨ) "#Hwand".
    iIntros ([(e & σ1) a]) "[%R [[% ?] | [[% HR] | [% ?]]]]".
    - iExists _. iLeft. eauto.
    - iExists _. iRight; iLeft. iSplit; [done|].
      iIntros (??). iApply "Hwand". by iApply "HR".
    - iExists _. iRight; iRight. eauto.
  Qed.

  Definition rwp_coupl' Z := bi_least_fixpoint (rwp_coupl_pre Z).
  Definition rwp_coupl e σ a Z := rwp_coupl' Z ((e, σ), a).

  Lemma rwp_coupl_unfold e1 σ1 a1 Z :
    rwp_coupl e1 σ1 a1 Z ≡
      (∃ R,
        (⌜reducible e1 σ1⌝ ∗
         ⌜Rcoupl (prim_step e1 σ1) (dret a1) R⌝ ∗
         ∀ ρ2, ⌜R ρ2 a1⌝ ={∅}=∗ Z ρ2 a1) ∨
        (⌜Rcoupl (dret (e1, σ1)) (step a1) R⌝ ∗
         ∀ a2, ⌜R (e1, σ1) a2⌝ ={∅}▷=∗ rwp_coupl e1 σ1 a2 Z) ∨
        (⌜reducible e1 σ1⌝ ∗
         ⌜Rcoupl (prim_step e1 σ1) (step a1) R⌝ ∗
         ∀ ρ2 a2, ⌜R ρ2 a2⌝ ={∅}▷=∗ Z ρ2 a2))%I.
  Proof. rewrite /rwp_coupl /rwp_coupl' least_fixpoint_unfold //. Qed.

  #[local] Definition cfgO := (prodO (exprO Λ) (stateO Λ)).

  Lemma rwp_coupl_strong_mono e1 σ1 a1 (Z1 Z2 : cfg Λ → A → iProp Σ) :
    (∀ ρ2 a2, (⌜prim_step e1 σ1 ρ2 > 0⌝ ∗ Z1 ρ2 a2 -∗ Z2 ρ2 a2)) -∗
    rwp_coupl e1 σ1 a1 Z1 -∗ rwp_coupl e1 σ1 a1 Z2.
  Proof.
    iIntros "HZ Hrwp". iRevert "HZ".
    set (Φ := (λ x,
      (∀ ρ2 a2, ⌜prim_step x.1.1 x.1.2 ρ2 > 0⌝ ∗ Z1 ρ2 a2 -∗ Z2 ρ2 a2) -∗
                rwp_coupl x.1.1 x.1.2 x.2 Z2)%I : prodO cfgO AO → iPropI Σ).
    rewrite /rwp_coupl /rwp_coupl'.
    assert (NonExpansive Φ).
    { intros n ((?&?) & ?) ((?&?) & ?) [[[=] [=]] [=]]. by simplify_eq/=. }
    iPoseProof (least_fixpoint_iter (rwp_coupl_pre Z1) Φ with "[]") as "H"; last first.
    { iIntros "HZ". by iApply ("H" with "Hrwp"). }
    clear.
    iIntros "!#" ([[e σ] a]) "[%R [(%Hred & %Hcpl & HR) | [[%Hcpl HR] | (%Hred & %Hcpl & HR)]]] Hwand /=".
    - rewrite rwp_coupl_unfold. iExists _. iLeft.
      iSplit; [done|].
      iSplit; [iPureIntro; by eapply Rcoupl_pos_R|].
      iIntros (ρ2 (HR & Hs & _)).
      iMod ("HR" with "[//]") as "HZ1". iModIntro.
      iApply "Hwand". eauto.
    - rewrite rwp_coupl_unfold. iExists _. iRight; iLeft.
      iSplit; [done|]. iIntros (a2 HR).
      iMod ("HR" with "[//]") as "HΦ". do 2 iModIntro.
      by iApply "HΦ".
    - rewrite rwp_coupl_unfold. iExists _. iRight; iRight.
      iSplit; [done|].
      iSplit; [iPureIntro; by eapply Rcoupl_pos_R|].
      iIntros (ρ2 a2 (HR & Hs & _)).
      iMod ("HR" with "[//]") as "HZ1". iModIntro.
      iApply "Hwand". iModIntro. iMod "HZ1". eauto.
  Qed.

  Lemma rwp_coupl_strong_ind (Ψ : expr Λ → state Λ → A → iProp Σ) (Z : cfg Λ → A → iProp Σ) :
    (∀ n e σ a, Proper (dist n) (Ψ e σ a)) →
    ⊢ (□ (∀ e σ a, rwp_coupl_pre Z (λ '((e, σ), a), Ψ e σ a ∧ rwp_coupl e σ a Z)%I ((e, σ), a) -∗ Ψ e σ a) →
       ∀ e σ a, rwp_coupl e σ a Z -∗ Ψ e σ a)%I.
  Proof.
    iIntros (HΨ). iIntros "#IH" (e σ a) "H".
    set (Ψ' := uncurry3 Ψ :
           (prodO (prodO (exprO Λ) (stateO Λ)) AO) → iProp Σ).
    assert (NonExpansive Ψ').
    { intros n [[e1 σ1] a1] [[e2 σ2] a2]
        [[?%leibniz_equiv ?%leibniz_equiv] ?%leibniz_equiv].
      simplify_eq/=. solve_proper. }
    iApply (least_fixpoint_ind _ Ψ' with "[] H").
    iIntros "!#" ([[??] ?]) "H". by iApply "IH".
  Qed.

  Lemma rwp_coupl_bind K `{!LanguageCtx K} e1 σ1 a1 Z :
    to_val e1 = None →
    rwp_coupl e1 σ1 a1 (λ '(e2, σ2) a2, Z (K e2, σ2) a2) -∗ rwp_coupl (K e1) σ1 a1 Z.
  Proof.
    iIntros (Hv) "Hcpl".
    iRevert (Hv).
    set (Φ := (λ x, ⌜to_val x.1.1 = None⌝ -∗
                    rwp_coupl (K x.1.1) x.1.2 x.2 Z)%I : prodO cfgO AO → iPropI Σ).
    rewrite /rwp_coupl /rwp_coupl'.
    assert (NonExpansive Φ).
    { intros n ((?&?) & ?) ((?&?) & ?) [[[=] [=]] [=]]. by simplify_eq/=. }
    iPoseProof (least_fixpoint_iter _ Φ with "[]") as "H"; last first.
    { iIntros (?). iApply ("H" $! (e1, _, _) with "Hcpl [//]").  }
    clear e1 σ1 a1.
    iIntros "!>" ([[e1 σ1] a1]) "[%R [(%Hred & %Hcpl & HR) | [[%Hcpl HR] | (%Hred & %Hcpl & HR)]]] % /=".
    - rewrite rwp_coupl_unfold.
      iExists (λ '(e2, σ2) ρ', ∃ e2', e2 = K e2' ∧ R (e2', σ2) ρ'). iLeft.
      iSplit; [eauto using reducible_fill|].
      iSplit.
      { iPureIntro.
        rewrite fill_dmap //=.
        rewrite -(dret_id_right (dret _)).
        eapply Rcoupl_dbind; [|done].
        intros [] ?? =>/=. apply Rcoupl_dret. eauto. }
      iIntros ([? σ2] (e2' & -> & ?)).
      by iApply ("HR" $! (_, _)).
    - rewrite rwp_coupl_unfold.
      iExists (λ '(e2, σ2) a2, ∃ e2', e2 = K e2' ∧ R (e2', σ2) a2). iRight; iLeft.
      iSplit.
      { iPureIntro.
        rewrite -(dret_id_right (step _)).
        rewrite -(dret_id_left (λ ρ, dret (K ρ.1, ρ.2)) (_, _)).
        eapply Rcoupl_dbind; [|done].
        intros [] ? ?. apply Rcoupl_dret. eauto. }
      iIntros (a2 (e2' & <-%(inj _) & ?)).
      iMod ("HR" with "[//]") as "H".
      do 2 iModIntro. by iApply "H".
    - rewrite rwp_coupl_unfold.
      iExists (λ '(e2, σ2) a2, ∃ e2', e2 = K e2' ∧ R (e2', σ2) a2). iRight; iRight.
      rewrite fill_dmap //=.
      iSplit; [eauto using reducible_fill|].
      iSplit.
      { iPureIntro. rewrite -(dret_id_right (step _)).
        eapply Rcoupl_dbind; [|done].
        intros [] ?? =>/=. apply Rcoupl_dret. eauto. }
      iIntros ([] ? (? & -> & ?)).
      by iMod ("HR" with "[//]").
  Qed.

  Lemma rwp_coupl_prim_step_l e1 σ1 a1 Z :
    (∃ R, ⌜reducible e1 σ1⌝ ∗
          ⌜Rcoupl (prim_step e1 σ1) (dret a1) R⌝ ∗
          ∀ ρ2, ⌜R ρ2 a1⌝ ={∅}=∗ Z ρ2 a1)
    ⊢ rwp_coupl e1 σ1 a1 Z.
  Proof.
    rewrite {1}rwp_coupl_unfold.
    iIntros "(%R & H)".
    iExists R. iLeft. done.
  Qed.

  Lemma rwp_coupl_step_r e1 σ1 a1 Z :
    (∃ R, ⌜Rcoupl (dret (e1, σ1)) (step a1) R⌝ ∗
          ∀ a2, ⌜R (e1, σ1) a2⌝ ={∅}▷=∗ rwp_coupl e1 σ1 a2 Z)
    ⊢ rwp_coupl e1 σ1 a1 Z.
  Proof.
    rewrite {1}rwp_coupl_unfold.
    iIntros "[%R H]".
    iExists R. iRight; iLeft. done.
  Qed.

  Lemma rwp_coupl_steps e1 σ1 a1 Z :
    (∃ R, ⌜reducible e1 σ1⌝ ∗
          ⌜Rcoupl (prim_step e1 σ1) (step a1) R⌝ ∗
          ∀ ρ2 a2, ⌜R ρ2 a2⌝ ={∅}▷=∗ Z ρ2 a2)
    ⊢ rwp_coupl e1 σ1 a1 Z.
  Proof.
    rewrite {1}rwp_coupl_unfold.
    iIntros "[%R H]".
    iExists R. iRight; iRight. done.
  Qed.

  Lemma rwp_coupl_det_r n e1 σ1 a1 a2 Z :
    stepN n a1 a2 = 1 →
    (|={∅}▷=>^n rwp_coupl e1 σ1 a2 Z) ⊢ rwp_coupl e1 σ1 a1 Z.
  Proof.
    revert a1.
    iInduction n as [|k IH] "IH".
    { iIntros (?). rewrite stepN_O. by iIntros (->%dret_1_2) "H". }
    iIntros (a).
    rewrite stepN_Sn.
    iIntros (Hs) "Hcpl".
    iApply rwp_coupl_step_r.
    iExists _. iSplit.
    { iPureIntro.
      apply Rcoupl_pos_R, Rcoupl_trivial.
      - solve_distr_mass.
      - by eapply dbind_det_inv_l. }
    iIntros (a3 (_ & _ & Hs')).
    rewrite step_fupdN_Sn.
    iApply (step_fupd_wand with "Hcpl").
    iApply "IH".
    iPureIntro. by eapply dbind_det_inv_r.
  Qed.

End rwp_coupl.

(** * The refinement weakest preconditions *)
Definition rwp_pre `{spec A B Σ} `{!tprwpG Λ Σ}
    (rwp : coPset -d> expr Λ -d> (val Λ -d> iProp Σ) -d> iProp Σ) :
    coPset -d> expr Λ -d> (val Λ -d> iProp Σ) -d> iProp Σ := λ E e1 Φ,
  (∀ σ1 a1,
    state_interp σ1 ∗ spec_interp a1 -∗
    match to_val e1 with
    | Some v => |={E}=> state_interp σ1 ∗ spec_interp a1 ∗ Φ v
    | None => |={E,∅}=>
        rwp_coupl e1 σ1 a1  (λ '(e2, σ2) a2,
            |={∅,E}=> state_interp σ2 ∗ spec_interp a2 ∗ rwp E e2 Φ)
    end)%I.

(* An [rswp] takes an [rswp_step] and afterwards proves an [rwp] *)
Definition rswp_step `{spec A B Σ} `{!tprwpG Λ Σ} (k : nat) E (e1 : expr Λ) (Z : expr Λ → iProp Σ) : iProp Σ :=
  (∀ σ1 a1,
      state_interp σ1 ∗ spec_interp a1 ={E,∅}=∗ |={∅}▷=>^k
      ⌜reducible e1 σ1⌝ ∧
      (∃ R, ⌜Rcoupl (prim_step e1 σ1) (dret a1) R⌝ ∧
            ∀ e2 σ2, ⌜R (e2, σ2) a1⌝ -∗ |={∅,E}=> (state_interp σ2 ∗ spec_interp a1 ∗ Z e2))).

Lemma rwp_pre_mono `{spec A B Σ} `{!tprwpG Λ Σ} (wp1 wp2 : coPset → expr Λ → (val Λ → iProp Σ) → iProp Σ) :
  ⊢ ((□ ∀ E e Φ, wp1 E e Φ -∗ wp2 E e Φ) →
        ∀ E e Φ, rwp_pre wp1 E e Φ -∗ rwp_pre wp2 E e Φ)%I.
Proof.
  iIntros "#H"; iIntros (E e1 Φ) "Hwp". rewrite /rwp_pre.
  destruct (to_val e1) as [v|]; first done.
  iIntros (σ1 a1) "Hσ". iMod ("Hwp" with "Hσ") as "Hwp". iModIntro.
  iApply (rwp_coupl_strong_mono with "[] Hwp").
  iIntros ([e2 σ2] a2) "[% Hfupd]".
  iMod "Hfupd" as "($ & $ & Hwp)".
  iModIntro.
  iApply ("H" with "Hwp").
Qed.

(* Uncurry [rwp_pre] and equip its type with an OFE structure *)
Definition rwp_pre' {Σ A B Λ} `{spec A B Σ} `{!tprwpG Λ Σ} :
  (prodO (prodO (leibnizO coPset) (exprO Λ)) (val Λ -d> iProp Σ) → iProp Σ) →
   prodO (prodO (leibnizO coPset) (exprO Λ)) (val Λ -d> iProp Σ) → iProp Σ
  := uncurry3 ∘ rwp_pre ∘ curry3.

Local Instance exec_coupl_pre_mono {Λ A B Σ} `{spec A B Σ} `{!tprwpG Λ Σ} :
  BiMonoPred rwp_pre'.
Proof.
  constructor.
  - iIntros (wp1 wp2 ? ?) "#H"; iIntros ([[E e1] Φ]); iRevert (E e1 Φ).
    iApply rwp_pre_mono. iIntros "!#" (E e Φ). iApply ("H" $! (E,e,Φ)).
  - intros wp Hwp n [[E1 e1] Φ1] [[E2 e2] Φ2]
      [[?%leibniz_equiv ?%leibniz_equiv] ?]; simplify_eq/=.
    rewrite /curry3 /rwp_pre.
    do 7 f_equiv.
    + do 3 f_equiv.
    + rewrite /rwp_coupl /rwp_coupl' /rwp_coupl_pre.
      do 26 (f_equiv || case_match || done).
Qed.

(** * RWP *)
#[local] Definition rwp_def `{spec A B Σ} `{!tprwpG Λ Σ} (_ : ()) (E : coPset) (e : expr Λ) (Φ : val Λ → iProp Σ) : iProp Σ
  := bi_least_fixpoint rwp_pre' (E,e,Φ).
#[local] Definition rwp_def' `{spec A B Σ} `{!tprwpG Λ Σ} : Rwp (iProp Σ) (expr Λ) (val Λ) () :=
  {| rwp := rwp_def; rwp_default := () |}.
#[local] Definition rwp_aux `{spec A B Σ} `{!tprwpG Λ Σ} : seal (@rwp_def'). by eexists. Qed
                             .
Definition rwp' `{spec A B Σ} `{!tprwpG Λ Σ} := rwp_aux.(unseal).
#[global] Existing Instance rwp'.
#[local] Lemma rwp_unseal `{spec A B Σ} `{!tprwpG Λ Σ} : rwp = (@rwp_def' A B _ _ _ Σ _ Λ _).(rwp).
Proof. rewrite -rwp_aux.(seal_eq) //. Qed.

(** * RSWP  *)
Definition rswp_def `{spec A B Σ} `{!tprwpG Λ Σ} (k : nat) (_ : ()) (E : coPset) (e : expr Λ) (Φ : val Λ → iProp Σ) : iProp Σ
  := rswp_step k E e (λ e2, RWP e2 @ E ⟨⟨ Φ ⟩⟩)%I.
Definition rswp_def' `{spec A B Σ} `{!tprwpG Λ Σ} : Rswp (iProp Σ) (expr Λ) (val Λ) ()
  := {| rswp := rswp_def; rswp_default := () |}.

Definition rswp_aux `{spec A B Σ} `{!tprwpG Λ Σ} : seal (@rswp_def'). by eexists. Qed.
#[global]

Definition rswp' `{spec A B Σ} `{!tprwpG Λ Σ} := rswp_aux.(unseal).
#[global] Existing Instance rswp'.

#[local] Lemma rswp_unseal `{spec A B Σ} `{!tprwpG Λ Σ} : rswp = (@rswp_def' A B _ _ _ Σ _ Λ _).(rswp).
Proof. rewrite -rswp_aux.(seal_eq) //. Qed.

Section rwp.
Context `{spec A B Σ} `{!tprwpG Λ Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types b : bool.

Lemma rwp_unfold E e Φ :
  RWP e @ E ⟨⟨ Φ ⟩⟩ ⊣⊢ rwp_pre (rwp (PROP:=iProp Σ) rwp_default) E e Φ.
Proof. rewrite rwp_unseal /= /rwp_def least_fixpoint_unfold //. Qed.

Lemma rwp_strong_ind  Ψ :
  (∀ n E e, Proper (pointwise_relation _ (dist n) ==> dist n) (Ψ E e)) →
  ⊢ (□ (∀ e E Φ, rwp_pre (λ E e Φ, Ψ E e Φ ∧ RWP e @ E ⟨⟨ Φ ⟩⟩) E e Φ -∗ Ψ E e Φ) →
        ∀ e E Φ, RWP e @ E ⟨⟨ Φ ⟩⟩ -∗ Ψ E e Φ)%I.
Proof.
  iIntros (HΨ). iIntros "#IH" (e E Φ) "H". rewrite rwp_unseal.
  set (Ψ' := uncurry3 Ψ :
    prodO (prodO (leibnizO coPset) (exprO Λ)) (val Λ -d> iProp Σ) → iProp Σ).
  assert (NonExpansive Ψ').
  { intros n [[E1 e1] Φ1] [[E2 e2] Φ2]
      [[?%leibniz_equiv ?%leibniz_equiv] ?]; simplify_eq/=. by apply HΨ. }
  iApply (least_fixpoint_ind _ Ψ' with "[] H").
  iIntros "!#" ([[??] ?]) "H". by iApply "IH".
Qed.

Lemma rwp_ind Ψ :
  (∀ n E e, Proper (pointwise_relation _ (dist n) ==> dist n) (Ψ E e)) →
  ⊢ (□ (∀ e E Φ, rwp_pre (λ E e Φ, Ψ E e Φ) E e Φ -∗ Ψ E e Φ)
      → ∀ e E Φ, RWP e @ E ⟨⟨ Φ ⟩⟩ -∗ Ψ E e Φ)%I.
Proof.
  iIntros (HΨ) "#H". iApply rwp_strong_ind. iIntros "!>" (e E Φ) "Hrwp".
  iApply "H". iApply (rwp_pre_mono with "[] Hrwp"). clear.
  iIntros "!>" (E e Φ) "[$ _]".
Qed.

Global Instance rwp_ne E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (rwp (PROP:=iProp Σ) rwp_default E e).
Proof.
  intros Φ1 Φ2 HΦ. rewrite !rwp_unseal /= /rwp_def' /rwp_def. by apply least_fixpoint_ne.
Qed.

Global Instance rwp_proper E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (rwp (PROP:=iProp Σ) rwp_default E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply rwp_ne=>v; apply equiv_dist.
Qed.

Lemma rwp_strong_ind' Ψ Φ E e :
  (∀ n e, Proper (dist n) (Ψ e)) →
  ⊢ (□ (∀ e, rwp_pre (λ _ e _, Ψ e ∧ RWP e @ E ⟨⟨ Φ ⟩⟩) E e Φ -∗ Ψ e) →
       RWP e @ E ⟨⟨ Φ ⟩⟩ -∗ Ψ e)%I.
Proof.
  iIntros (HΨ) "#IH Hrwp".
  iRevert "IH".
  iApply (rwp_strong_ind (λ E e Φ, _) with "[] Hrwp").
  { intros ??? ???. rewrite /rwp_pre. do 12 f_equiv.
    - do 3 f_equiv.
    - apply least_fixpoint_ne; f_equiv.
      rewrite /rwp_coupl_pre.
      do 25 (f_equiv || case_match). }
  clear.
  iIntros "!#" (e E Φ) "H #IH".
  iApply "IH".
  iIntros (σ a) "[Hσ Ha]".
  iSpecialize ("H" with "[$]").
  case_match; [done|].
  iMod "H" as "H".
  iModIntro.
  iApply (rwp_coupl_strong_mono with "[] H").
  iIntros ([e2 σ2] a2) "[% >($ & $ & H)] !>".
  iSplit; [by iApply "H"|].
  by iDestruct "H" as "[_ ?]".
Qed.

Lemma rwp_ind' Ψ Φ E e:
  (∀ n e, Proper (dist n) (Ψ e)) →
  ⊢ (□ (∀ e, rwp_pre (λ _ e _, Ψ e) E e Φ -∗ Ψ e) →
    RWP e @ E ⟨⟨ Φ ⟩⟩ -∗ Ψ e)%I.
Proof.
  iIntros (?) "#H".
  iApply rwp_strong_ind'.
  iIntros (e') "!> Hrwp".
  iApply "H".
  iApply (rwp_pre_mono with "[] Hrwp").
  iIntros "!>" (_ ? _) "[$ _]".
Qed.

Lemma rwp_value' E Φ v : Φ v ⊢ RWP of_val v @ E ⟨⟨ Φ ⟩⟩.
Proof. iIntros "HΦ". rewrite rwp_unfold /rwp_pre to_of_val. by iIntros (??) "[$ $]". Qed.

Lemma rwp_strong_mono' E1 E2 e Φ Ψ :
  E1 ⊆ E2 →
  RWP e @ E1 ⟨⟨ Φ ⟩⟩ -∗
  (∀ σ a v, state_interp σ ∗ spec_interp a ∗ Φ v ={E2}=∗
            state_interp σ ∗ spec_interp a ∗ Ψ v) -∗
  RWP e @ E2 ⟨⟨ Ψ ⟩⟩.
Proof.
  iIntros (HE) "H HΦ". iRevert (E2 Ψ HE) "HΦ"; iRevert (e E1 Φ) "H".
  iApply rwp_ind; first solve_proper.
  iIntros "!#" (e E1 Φ) "IH"; iIntros (E2 Ψ HE) "HΦ".
  rewrite !rwp_unfold /rwp_pre.
  destruct (to_val e) as [v|] eqn:?.
  { iIntros (??) "H".
    iSpecialize ("IH" with "[$]").
    iMod (fupd_mask_mono with "IH") as "(?&?&?)"; [done|].
    iApply ("HΦ" with "[$]"). }
  iIntros (σ1 a1) "Hσ". iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  iMod ("IH" with "[$]") as "IH". iModIntro.
  iApply (rwp_coupl_strong_mono with "[HΦ Hclose] IH").
  iIntros ([e2 σ2] a2) "[% H]".
  iMod "H" as "($ & $ & H)".
  iMod "Hclose" as "_".
  iModIntro.
  by iApply "H".
Qed.

Lemma rwp_strong_mono E1 E2 e Φ Ψ :
  E1 ⊆ E2 →
  RWP e @ E1 ⟨⟨ Φ ⟩⟩ -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ RWP e @ E2 ⟨⟨ Ψ ⟩⟩.
Proof.
  iIntros (?) "Hrwp H". iApply (rwp_strong_mono' with "[$]"); auto.
  iIntros (???) "($&$&HΦ)". by iApply "H".
Qed.

Lemma fupd_rwp E e Φ : (|={E}=> RWP e @ E ⟨⟨ Φ ⟩⟩) ⊢ RWP e @ E ⟨⟨ Φ ⟩⟩.
Proof.
  rewrite rwp_unfold /rwp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?.
  { by iMod "H". }
  iIntros (σ1 a) "HS". iMod "H". by iApply "H".
Qed.
Lemma fupd_rwp' E e Φ :
  (∀ σ a, state_interp σ ∗ spec_interp a ={E}=∗
          state_interp σ ∗ spec_interp a ∗ RWP e @ E ⟨⟨ Φ ⟩⟩)
  ⊢ RWP e @ E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros "H".
  iEval (rewrite rwp_unfold /rwp_pre). destruct (to_val e) as [v|] eqn:Heq.
  { iIntros. iSpecialize ("H" with "[$]"). rewrite rwp_unfold /rwp_pre Heq.
    iMod "H" as "(H1&H2&Hwand)". by iMod ("Hwand" with "[$]") as "$". }
  iIntros (σ1 a1) "HS".
  iMod ("H" with "[$]") as "(? & ? & Hwand)".
  iEval (rewrite rwp_unfold /rwp_pre Heq) in "Hwand".
  by iMod ("Hwand" with "[$]") as "$".
Qed.
Lemma rwp_fupd E e Φ : RWP e @ E ⟨⟨ v, |={E}=> Φ v ⟩⟩ ⊢ RWP e @ E ⟨⟨ Φ ⟩⟩.
Proof. iIntros "H". iApply (rwp_strong_mono E with "H"); auto. Qed.

Lemma rwp_fupd' E e Φ :
  RWP e @ E ⟨⟨ v, ∀ σ a, state_interp σ ∗ spec_interp a ={E}=∗
                         state_interp σ ∗ spec_interp a ∗ Φ v⟩⟩
  ⊢ RWP e @ E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros "H". iApply (rwp_strong_mono' E with "H"); auto. iIntros (???) "(?&?&H)".
  by iMod ("H" with "[$]").
Qed.

(* TODO: not just StronglyAtomic?  *)
Lemma rwp_atomic E1 E2 e Φ `{!Atomic StronglyAtomic e} :
  (|={E1,E2}=> RWP e @ E2 ⟨⟨ v, |={E2,E1}=> Φ v ⟩⟩) ⊢ RWP e @ E1 ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros "H". rewrite !rwp_unfold /rwp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { iIntros. iMod ("H"). iMod ("H" with "[$]") as "($&$&$)". }
  iIntros (σ1 a1) "Hσ". iMod "H".
  iMod ("H" $! σ1 with "Hσ") as "H". iModIntro.
  iApply (rwp_coupl_strong_mono with "[] H").
  iIntros ([e2 σ2] a2) "[%Hstep H]".
  iMod "H" as "(Hσ & Ha & Hrwp)".
  rewrite !rwp_unfold /rwp_pre .
  destruct (to_val e2) as [v2|] eqn:He2.
  + iMod ("Hrwp" with "[$]") as "($ & $ & H)".
    iMod "H" as "$". eauto.
  + iMod ("Hrwp" with "[$]") as "H".
    specialize (atomic _ _ _ Hstep) as Hatomic.
    destruct Hatomic. congruence.
Qed.

Lemma rwp_bind K `{!LanguageCtx K} E e Φ :
  RWP e @ E ⟨⟨ v, RWP K (of_val v) @ E ⟨⟨ Φ ⟩⟩ ⟩⟩ ⊢ RWP K e @ E ⟨⟨ Φ ⟩⟩.
Proof.
  revert Φ. cut (∀ Φ', RWP e @ E ⟨⟨ Φ' ⟩⟩ -∗ ∀ Φ,
  (∀ v, Φ' v -∗ RWP K (of_val v) @ E ⟨⟨ Φ ⟩⟩) -∗ RWP K e @ E ⟨⟨ Φ ⟩⟩).
  { iIntros (help Φ) "H". iApply (help with "H"); auto. }
  iIntros (Φ') "H". iRevert (e E Φ') "H". iApply rwp_strong_ind; first solve_proper.
  iIntros "!#" (e E1 Φ') "IH". iIntros (Φ) "HΦ".
  rewrite /rwp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. iApply fupd_rwp'.
    iIntros. iMod ("IH" with "[$]") as "($&$&H)".
    by iApply "HΦ". }
  rewrite rwp_unfold /rwp_pre fill_not_val //.
  iIntros (σ1 a1) "H". iMod ("IH" with "H") as "IH". iModIntro.
  iDestruct "IH" as "H".
  iApply rwp_coupl_bind; [done|].
  iApply (rwp_coupl_strong_mono with "[HΦ] H").
  iIntros ([e2 σ2] a2) "[%Hstep H]".
  iMod "H" as "($ & $ & H)".
  iModIntro.
  by iApply "H".
Qed.

(** * Derived rules *)
Lemma rwp_mono E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → RWP e @ E ⟨⟨ Φ ⟩⟩ ⊢ RWP e @ E ⟨⟨ Ψ ⟩⟩.
Proof.
  iIntros (HΦ) "H"; iApply (rwp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma rwp_mask_mono E1 E2 e Φ : E1 ⊆ E2 → RWP e @ E1 ⟨⟨ Φ ⟩⟩ ⊢ RWP e @ E2 ⟨⟨ Φ ⟩⟩.
Proof. iIntros (?) "H"; iApply (rwp_strong_mono with "H"); auto. Qed.
Global Instance rwp_mono' E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (rwp (PROP:=iProp Σ) rwp_default E e).
Proof. by intros Φ Φ' ?; apply rwp_mono. Qed.

Lemma rwp_value E Φ e v : IntoVal e v → Φ v ⊢ RWP e @ E ⟨⟨ Φ ⟩⟩.
Proof. intros <-. by apply rwp_value'. Qed.
Lemma rwp_value_fupd' E Φ v : (|={E}=> Φ v) ⊢ RWP of_val v @ E ⟨⟨ Φ ⟩⟩.
Proof. intros. by rewrite -rwp_fupd -rwp_value'. Qed.
Lemma rwp_value_fupd E Φ e v `{!IntoVal e v} :
  (|={E}=> Φ v) ⊢ RWP e @ E ⟨⟨ Φ ⟩⟩.
Proof. intros. rewrite -rwp_fupd -rwp_value //. Qed.

Lemma rwp_frame_l E e Φ R : R ∗ RWP e @ E ⟨⟨ Φ ⟩⟩ ⊢ RWP e @ E ⟨⟨ v, R ∗ Φ v ⟩⟩.
Proof. iIntros "[? H]". iApply (rwp_strong_mono with "H"); auto with iFrame. Qed.
Lemma rwp_frame_r E e Φ R : RWP e @ E ⟨⟨ Φ ⟩⟩ ∗ R ⊢ RWP e @ E ⟨⟨ v, Φ v ∗ R ⟩⟩.
Proof. iIntros "[H ?]". iApply (rwp_strong_mono with "H"); auto with iFrame. Qed.

Lemma rwp_wand E e Φ Ψ :
  RWP e @ E ⟨⟨ Φ ⟩⟩ -∗ (∀ v, Φ v -∗ Ψ v) -∗ RWP e @ E ⟨⟨ Ψ ⟩⟩.
Proof.
  iIntros "Hwp H". iApply (rwp_strong_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma rwp_wand_l E e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ RWP e @ E ⟨⟨ Φ ⟩⟩ ⊢ RWP e @ E ⟨⟨ Ψ ⟩⟩.
Proof. iIntros "[H Hwp]". iApply (rwp_wand with "Hwp H"). Qed.
Lemma rwp_wand_r E e Φ Ψ :
  RWP e @ E ⟨⟨ Φ ⟩⟩ ∗ (∀ v, Φ v -∗ Ψ v) ⊢ RWP e @ E ⟨⟨ Ψ ⟩⟩.
Proof. iIntros "[Hwp H]". iApply (rwp_wand with "Hwp H"). Qed.
Lemma rwp_frame_wand_l E e Q Φ :
  Q ∗ RWP e @ E ⟨⟨ v, Q -∗ Φ v ⟩⟩ -∗ RWP e @ E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros "[HQ HRWP]". iApply (rwp_wand with "HRWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.

End rwp.

Section rswp.
Context `{spec A B Σ} `{!tprwpG Λ Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types b : bool.

Lemma rswp_unfold k s E e Φ :
  RSWP e at k @ s; E ⟨⟨ Φ ⟩⟩ ⊣⊢ rswp_def k s E e Φ.
Proof. by rewrite rswp_unseal. Qed.

Global Instance rswp_ne k s E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (rswp (PROP:=iProp Σ) k s E e).
Proof.
  intros Φ1 Φ2 HΦ. rewrite !rswp_unfold /rswp_def /rswp_step. do 22 f_equiv.
Qed.

Global Instance rswp_proper k s E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (rswp (PROP:=iProp Σ) k s E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply rswp_ne=>v; apply equiv_dist.
Qed.

Lemma rswp_strong_mono k E1 E2 e Φ Ψ :
  E1 ⊆ E2 →
  RSWP e at k @ E1 ⟨⟨ Φ ⟩⟩ -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ RSWP e at k @ E2 ⟨⟨ Ψ ⟩⟩.
Proof.
  iIntros (HE); rewrite !rswp_unfold /rswp_def /rswp_step.
  iIntros "H  HΦ" (σ1 a) "Hσ". iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  iMod ("H" with "[$]") as "H". iModIntro.
  iApply (step_fupdN_wand with "H").
  iIntros "(% & % & % & H)".
  iSplit; [done|].
  iExists _. iSplit; [done|]. iIntros (e2 σ2 HR).
  iMod ("H" with "[//]") as "($ & $ & H)".
  iMod "Hclose" as "_". iModIntro.
  by iApply (rwp_strong_mono with "H").
Qed.

Lemma fupd_rswp k E e Φ : (|={E}=> RSWP e at k @ E ⟨⟨ Φ ⟩⟩) ⊢ RSWP e at k @ E ⟨⟨ Φ ⟩⟩.
Proof.
  rewrite rswp_unfold /rswp_def /rswp_step. iIntros "H".
  iIntros (σ1 a) "HS". iMod "H". by iApply "H".
Qed.
Lemma rswp_fupd k E e Φ : RSWP e at k @ E ⟨⟨ v, |={E}=> Φ v ⟩⟩ ⊢ RSWP e at k @ E ⟨⟨ Φ ⟩⟩.
Proof. iIntros "H". iApply (rswp_strong_mono k E with "H"); auto. Qed.

Lemma rwp_no_step E e Φ:
  to_val e = None →
  RSWP e at 0 @ E ⟨⟨ Φ ⟩⟩ ⊢ RWP e @ E ⟨⟨ Φ ⟩⟩.
Proof.
  rewrite rswp_unfold rwp_unfold /rswp_def /rwp_pre /rswp_step.
  iIntros (->) "Hswp". iIntros (σ1 a) "[Ha Hσ]".
  iMod ("Hswp" with "[$]") as "(% & % & % & Hswp)". iModIntro.
  iApply rwp_coupl_prim_step_l.
  iExists _.
  iSplit; [done|].
  iSplit; [done|].
  iIntros ([e2 σ2] HR) "!>".
  by iMod ("Hswp" with "[//]").
Qed.

Lemma rwp_spec_steps n P E e Φ:
  to_val e = None →
  (P -∗ RSWP e at n @ E ⟨⟨ Φ ⟩⟩) ∗ spec_update n E P ⊢ RWP e @ E ⟨⟨ Φ ⟩⟩.
Proof.
  rewrite rswp_unfold rwp_unfold /rswp_def /rwp_pre /rswp_step.
  iIntros (->) "[Hswp Hspec]". iIntros (σ1 a) "[Hσ1 Ha]". rewrite /spec_update.
  iMod ("Hspec" with "Ha") as (a' Ha) "(Hsource_interp & HP)".
  iMod ("Hswp" with "HP [$]") as "Hswp".
  iModIntro.
  iApply rwp_coupl_det_r; [done|].
  iApply (step_fupdN_mono with "Hswp").
  iIntros "(% & % & % & H)".
  iApply rwp_coupl_prim_step_l.
  iExists _.
  iSplit; [done|].
  iSplit; [done|].
  iIntros ([e2 σ2] HR) "!>".
  by iMod ("H" with "[//]").
Qed.

Lemma rswp_later k E e Φ :
  ▷ RSWP e at k @ E ⟨⟨ Φ ⟩⟩ ⊢ RSWP e at (S k) @ E ⟨⟨ Φ ⟩⟩.
Proof.
  rewrite 2!rswp_unfold /rswp_def /rswp_step.
  iIntros "H" (σ1 a) "[Hσ Ha]".
  iMod (fupd_mask_subseteq ∅) as "Hclose"; [set_solver|].
  rewrite step_fupdN_Sn.
  do 3 iModIntro.
  iMod "Hclose" as "_".
  by iMod ("H" with "[$]").
Qed.

(* TODO: not just [StronglyAtomic]? *)
Lemma rswp_atomic k E1 E2 e Φ `{!Atomic StronglyAtomic e} :
  (|={E1,E2}=> RSWP e at k @ E2 ⟨⟨ v, |={E2,E1}=> Φ v ⟩⟩) ⊢ RSWP e at k @ E1 ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros "H". rewrite !rswp_unfold /rswp_def /rswp_step.
  iIntros (σ1 a) "Hσ". iMod "H".
  iMod ("H" $! σ1 with "Hσ") as "H". iModIntro.
  iApply (step_fupdN_wand with "H"); iIntros "[% (%R & % & H)]".
  iSplit; [done|].
  iExists _.
  iSplit; [iPureIntro; by eapply Rcoupl_pos_R|].
  iIntros (e2 σ2 (HR & Hstep & ?)).
  iMod ("H" with "[//]") as "(Hσ2 & Ha & H)".
  rewrite 2!rwp_unfold /rwp_pre. case_match eqn:He2.
  - iDestruct ("H" with "[$]") as ">($ & $ & >$)". eauto.
  - specialize (atomic _ _ _ Hstep) as Hatomic.
    destruct Hatomic. congruence.
Qed.

Lemma rswp_bind K `{!LanguageCtx K} k E e Φ :
  to_val e = None →
  RSWP e at k @ E ⟨⟨ v, RWP K (of_val v) @ E ⟨⟨ Φ ⟩⟩ ⟩⟩ ⊢ RSWP K e at k @ E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros (He) "H". rewrite !rswp_unfold /rswp_def /rswp_step.
  iIntros (σ1 a) "Hσ". iMod ("H" with "Hσ") as "H".
  iModIntro. iApply (step_fupdN_wand with "H").
  iIntros "[% (%R & % & H)]".
  iSplit; [eauto using reducible_fill|].
  iExists (λ '(e2, σ2) ρ', ∃ e2', e2 = K e2' ∧ R (e2', σ2) ρ').
  iSplit.
  { iPureIntro.
    rewrite fill_dmap //=.
    rewrite -(dret_id_right (dret _)).
    eapply Rcoupl_dbind; [|done].
    intros [] ?? =>/=. apply Rcoupl_dret. eauto. }
  iIntros (?? (e2 & -> &?)).
  iMod ("H" with "[//]") as "($ & $ & H)".
  iModIntro.
  by iApply rwp_bind.
Qed.

(** * Derived rules *)
Lemma rswp_mono k E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → RSWP e at k @ E ⟨⟨ Φ ⟩⟩ ⊢ RSWP e at k @ E ⟨⟨ Ψ ⟩⟩.
Proof.
  iIntros (HΦ) "H". iApply (rswp_strong_mono with "[H] []"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma rswp_mask_mono k E1 E2 e Φ : E1 ⊆ E2 → RSWP e at k @ E1 ⟨⟨ Φ ⟩⟩ ⊢ RSWP e at k @ E2 ⟨⟨ Φ ⟩⟩.
Proof. iIntros (?) "H"; iApply (rswp_strong_mono with "H"); auto. Qed.
Global Instance rswp_mono' k E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (rswp (PROP:=iProp Σ) k rswp_default E e).
Proof. by intros Φ Φ' ?; apply rswp_mono. Qed.

Lemma rswp_frame_l k E e Φ R : R ∗ RSWP e at k @ E ⟨⟨ Φ ⟩⟩ ⊢ RSWP e at k @ E ⟨⟨ v, R ∗ Φ v ⟩⟩.
Proof. iIntros "[? H]". iApply (rswp_strong_mono with "H"); auto with iFrame. Qed.
Lemma rswp_frame_r k E e Φ R : RSWP e at k @ E ⟨⟨ Φ ⟩⟩ ∗ R ⊢ RSWP e at k @ E ⟨⟨ v, Φ v ∗ R ⟩⟩.
Proof. iIntros "[H ?]". iApply (rswp_strong_mono with "H"); auto with iFrame. Qed.

Lemma rswp_wand k E e Φ Ψ :
  RSWP e at k @ E ⟨⟨ Φ ⟩⟩ -∗ (∀ v, Φ v -∗ Ψ v) -∗ RSWP e at k @ E ⟨⟨ Ψ ⟩⟩.
Proof.
  iIntros "Hwp H". iApply (rswp_strong_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma rswp_wand_l k E e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ RSWP e at k @ E ⟨⟨ Φ ⟩⟩ ⊢ RSWP e at k @ E ⟨⟨ Ψ ⟩⟩.
Proof. iIntros "[H Hwp]". iApply (rswp_wand with "Hwp H"). Qed.
Lemma rswp_wand_r k E e Φ Ψ :
  RSWP e at k @ E ⟨⟨ Φ ⟩⟩ ∗ (∀ v, Φ v -∗ Ψ v) ⊢ RSWP e at k @ E ⟨⟨ Ψ ⟩⟩.
Proof. iIntros "[Hwp H]". iApply (rswp_wand with "Hwp H"). Qed.
Lemma rswp_frame_wand_l k E e Q Φ :
  Q ∗ RSWP e at k @ E ⟨⟨ v, Q -∗ Φ v ⟩⟩ -∗ RSWP e at k @ E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros "[HQ HWP]". iApply (rswp_wand with "HWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.

End rswp.


(** Proofmode class instances *)
Section proofmode_classes.
  Context {Σ A B Λ} `{spec A B Σ} `{!tprwpG Λ Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.

  Global Instance frame_rwp p E e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (RWP e @ E ⟨⟨ Φ ⟩⟩) (RWP e @ E ⟨⟨ Ψ ⟩⟩).
  Proof. rewrite /Frame=> HR. rewrite rwp_frame_l. apply rwp_mono, HR. Qed.

  Global Instance frame_rswp k p E e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (RSWP e at k @ E ⟨⟨ Φ ⟩⟩) (RSWP e at k @ E ⟨⟨ Ψ ⟩⟩).
  Proof. rewrite /Frame=> HR. rewrite rswp_frame_l. apply rswp_mono, HR. Qed.

  Global Instance is_except_0_rwp E e Φ : IsExcept0 (RWP e @ E ⟨⟨ Φ ⟩⟩).
  Proof. by rewrite /IsExcept0 -{2}fupd_rwp -except_0_fupd -fupd_intro. Qed.

  Global Instance is_except_0_rswp k E e Φ : IsExcept0 (RSWP e at k @ E ⟨⟨ Φ ⟩⟩).
  Proof. by rewrite /IsExcept0 -{2}fupd_rswp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_rwp p E e P Φ :
    ElimModal True p false (|==> P) P (RWP e @ E ⟨⟨ Φ ⟩⟩) (RWP e @ E ⟨⟨ Φ ⟩⟩).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r bi.wand_elim_r fupd_rwp.
  Qed.

  Global Instance elim_modal_bupd_rswp k p E e P Φ :
    ElimModal True p false (|==> P) P (RSWP e at k @ E ⟨⟨ Φ ⟩⟩) (RSWP e at k @ E ⟨⟨ Φ ⟩⟩).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r bi.wand_elim_r fupd_rswp.
  Qed.

  Global Instance elim_modal_fupd_rwp p E e P Φ :
    ElimModal True p false (|={E}=> P) P (RWP e @ E ⟨⟨ Φ ⟩⟩) (RWP e @ E ⟨⟨ Φ ⟩⟩).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r fupd_rwp.
  Qed.

  Global Instance elim_modal_fupd_rswp k p E e P Φ :
    ElimModal True p false (|={E}=> P) P (RSWP e at k @ E ⟨⟨ Φ ⟩⟩) (RSWP e at k @ E ⟨⟨ Φ ⟩⟩).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r fupd_rswp.
  Qed.

  Global Instance elim_modal_fupd_rwp_atomic p E1 E2 e P Φ :
    Atomic StronglyAtomic e →
    ElimModal True p false (|={E1,E2}=> P) P
            (RWP e @ E1 ⟨⟨ Φ ⟩⟩) (RWP e @ E2 ⟨⟨ v, |={E2,E1}=> Φ v ⟩⟩)%I.
  Proof.
    intros. by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r rwp_atomic.
  Qed.

 Global Instance elim_modal_fupd_rswp_atomic k p E1 E2 e P Φ :
    Atomic StronglyAtomic e →
    ElimModal True p false (|={E1,E2}=> P) P
            (RSWP e at k @ E1 ⟨⟨ Φ ⟩⟩) (RSWP e at k @ E2 ⟨⟨ v, |={E2,E1}=> Φ v ⟩⟩)%I.
  Proof.
    intros. by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r rswp_atomic.
  Qed.

  Global Instance add_modal_fupd_rwp E e P Φ :
    AddModal (|={E}=> P) P (RWP e @ E ⟨⟨ Φ ⟩⟩).
  Proof. by rewrite /AddModal fupd_frame_r bi.wand_elim_r fupd_rwp. Qed.

  Global Instance add_modal_fupd_rswp k E e P Φ :
    AddModal (|={E}=> P) P (RSWP e at k @ E ⟨⟨ Φ ⟩⟩).
  Proof. by rewrite /AddModal fupd_frame_r bi.wand_elim_r fupd_rswp. Qed.

  Global Instance elim_acc_wp {X} E1 E2 α β γ e Φ :
    ElimAcc (X:=X) (Atomic StronglyAtomic e) (fupd E1 E2) (fupd E2 E1)
            α β γ (RWP e @ E1 ⟨⟨ Φ ⟩⟩)
            (λ x, RWP e @ E2 ⟨⟨ v, |={E2}=> β x ∗ (γ x -∗? Φ v) ⟩⟩)%I.
  Proof.
    intros ?. rewrite /ElimAcc.
    iIntros "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (rwp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_rswp {X} k E1 E2 α β γ e Φ :
    ElimAcc (X:=X) (Atomic StronglyAtomic e) (fupd E1 E2) (fupd E2 E1)
            α β γ (RSWP e at k @ E1 ⟨⟨ Φ ⟩⟩)
            (λ x, RSWP e at k @ E2 ⟨⟨ v, |={E2}=> β x ∗ (γ x -∗? Φ v) ⟩⟩)%I.
  Proof.
    intros ?. rewrite /ElimAcc.
    iIntros "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (rswp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_wp_nonatomic {X} E α β γ e Φ :
    ElimAcc (X:=X) True (fupd E E) (fupd E E)
            α β γ (RWP e @ E ⟨⟨ Φ ⟩⟩)
            (λ x, RWP e @ E ⟨⟨ v, |={E}=> β x ∗ (γ x -∗? Φ v) ⟩⟩)%I.
  Proof.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply rwp_fupd.
    iApply (rwp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_swp_nonatomic {X} k E α β γ e Φ :
    ElimAcc (X:=X) True (fupd E E) (fupd E E)
            α β γ (RSWP e at k @ E ⟨⟨ Φ ⟩⟩)
            (λ x, RSWP e at k @ E ⟨⟨ v, |={E}=> β x ∗ (γ x -∗? Φ v) ⟩⟩)%I.
  Proof.
    rewrite /ElimAcc.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply rswp_fupd.
    iApply (rswp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

End proofmode_classes.

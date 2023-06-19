From Coq Require Export Reals Psatz.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export fixpoint big_op.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.bi Require Export weakestpre.
From clutch.prob Require Export couplings distribution.
From clutch.program_logic Require Export exec language.

Import uPred.

Local Open Scope R.

Class tprwpG (Λ : language) (Σ : gFunctors) := IrisG {
  iris_invGS :> invGS_gen HasNoLc Σ;
  state_interp : state Λ → iProp Σ;
}.
Global Opaque iris_invGS.
Global Arguments IrisG {Λ Σ}.

Class spec (A : Type) `{Countable A} (Σ : gFunctors) := Spec {
  spec_step   : A → distr A;
  spec_interp : A → iProp Σ;
}.
Global Arguments Spec {_ _ _ _}.

(** * The weakest precondition  *)
Definition rwp_step {Σ Λ A} `{spec A Σ} `{!tprwpG Λ Σ} E (e1 : expr Λ) (Z : cfg Λ → A → iProp Σ) : iProp Σ :=
  ∀ σ1 a1,
    state_interp σ1 ∗ spec_interp a1 ={E,∅}=∗
    ⌜reducible e1 σ1⌝ ∗
    ((∃ R, ⌜Rcoupl (prim_step e1 σ1) (dret a1) R⌝ ∗
          ∀ ρ2, ⌜R ρ2 a1⌝ ={∅}=∗ Z ρ2 a1) ∨
    (∃ R, ⌜Rcoupl (prim_step e1 σ1) (spec_step a1) R⌝ ∗
          ∀ ρ2 a2, ⌜R ρ2 a2⌝ ={∅}=∗ ▷ Z ρ2 a2)).

Definition rwp_pre {Σ A Λ} `{spec A Σ} `{!tprwpG Λ Σ}
    (rwp : coPset -d> expr Λ -d> (val Λ -d> iProp Σ) -d> iProp Σ) :
    coPset -d> expr Λ -d> (val Λ -d> iProp Σ) -d> iProp Σ := λ E e1 Φ,
  match to_val e1 with
  | Some v => ∀ σ a, state_interp σ ∗ spec_interp a ={E}=∗ state_interp σ ∗ spec_interp a ∗ Φ v
  | None => rwp_step E e1 (λ '(e2, σ2) a2, |={∅,E}=> state_interp σ2 ∗ spec_interp a2 ∗ rwp E e2 Φ)
  end%I.

Lemma rwp_pre_mono {Σ A Λ} `{spec A Σ} `{!tprwpG Λ Σ} (wp1 wp2 : coPset → expr Λ → (val Λ → iProp Σ) → iProp Σ) :
  ⊢ ((□ ∀ E e Φ, wp1 E e Φ -∗ wp2 E e Φ) →
      ∀ E e Φ, rwp_pre wp1 E e Φ -∗ rwp_pre wp2 E e Φ)%I.
Proof.
  iIntros "#H"; iIntros (E e1 Φ) "Hwp". rewrite /rwp_pre /rwp_step.
  destruct (to_val e1) as [v|]; first done.
  iIntros (σ1 a1) "Hσ". iMod ("Hwp" with "Hσ") as "[% Hwp]". iModIntro.
  iSplit; [done|].
  iDestruct "Hwp" as "[(% & % & HR) | (% & % & HR)]".
  - iLeft. iExists _. iSplit; [done|].
    iIntros ([e2 σ2] HR). iMod ("HR" $! (e2,σ2) HR) as "HR".
    iModIntro. iMod "HR" as "($ & $ & Hwp1)".
    iModIntro. iApply ("H" with "Hwp1").
  - iRight. iExists _. iSplit; [done|].
    iIntros ([e2 σ2] a2 HR). iMod ("HR" $! (e2,σ2) a2 HR) as "HR".
    iIntros "!# !>". iMod "HR" as "($ & $ & Hwp1)".
    iModIntro. by iApply ("H" with "Hwp1").
Qed.

(* Uncurry [rwp_pre] and equip its type with an OFE structure *)
Definition rwp_pre' {Σ A Λ} `{spec A Σ} `{!tprwpG Λ Σ} :
  (prodO (prodO (leibnizO coPset) (exprO Λ)) (val Λ -d> iProp Σ) → iProp Σ) →
   prodO (prodO (leibnizO coPset) (exprO Λ)) (val Λ -d> iProp Σ) → iProp Σ
  := uncurry3 ∘ rwp_pre ∘ curry3.

Local Instance exec_coupl_pre_mono {Λ A Σ} `{spec A Σ} `{!tprwpG Λ Σ} :
  BiMonoPred rwp_pre'.
Proof.
  constructor.
  - iIntros (wp1 wp2 ? ?) "#H"; iIntros ([[E e1] Φ]); iRevert (E e1 Φ).
    iApply rwp_pre_mono. iIntros "!#" (E e Φ). iApply ("H" $! (E,e,Φ)).
  - intros wp Hwp n [[E1 e1] Φ1] [[E2 e2] Φ2]
      [[?%leibniz_equiv ?%leibniz_equiv] ?]; simplify_eq/=.
    rewrite /curry3 /rwp_pre /rwp_step.
    do 21 (f_equiv || case_match || done).
    + by apply pair_ne.
    + do 3 f_equiv. by apply pair_ne.
Qed.

Definition rwp_def {Σ A Λ} `{spec A Σ} `{!tprwpG Λ Σ} (_ : ()) (E : coPset) (e : expr Λ) (Φ : val Λ → iProp Σ) : iProp Σ
  := bi_least_fixpoint rwp_pre' (E,e,Φ).
Definition rwp_aux {Σ A Λ} `{spec A Σ} `{!tprwpG Λ Σ} : seal (@rwp_def Σ A Λ _ _ _ _). by eexists. Qed.
#[global]
Instance rwp' {Σ A Λ} `{spec A Σ} `{!tprwpG Λ Σ} : Rwp (iProp Σ) (expr Λ) (val Λ) () := rwp_aux.(unseal).

Local Lemma rwp_unseal `{spec A Σ} `{!tprwpG Λ Σ} : rwp = @rwp_def Σ A Λ _ _ _ _.
Proof. rewrite -rwp_aux.(seal_eq) //. Qed.

Section rwp.
Context {Σ A Λ} `{spec A Σ} `{!tprwpG Λ Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types b : bool.

Lemma rwp_unfold E e Φ :
  RWP e @ E ⟨⟨ Φ ⟩⟩ ⊣⊢ rwp_pre (rwp (PROP:=iProp Σ) ()) E e Φ.
Proof. by rewrite rwp_unseal /rwp_def least_fixpoint_unfold. Qed.

Lemma rwp_strong_ind Ψ :
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
  Proper (pointwise_relation _ (dist n) ==> dist n) (rwp (PROP:=iProp Σ) () E e).
Proof.
  intros Φ1 Φ2 HΦ. rewrite !rwp_unseal. by apply (least_fixpoint_ne _), pair_ne, HΦ.
Qed.

Global Instance rwp_proper E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (rwp (PROP:=iProp Σ) () E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply rwp_ne=>v; apply equiv_dist.
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
  rewrite !rwp_unfold /rwp_pre /rwp_step.
  destruct (to_val e) as [v|] eqn:?.
  { iIntros (??) "H".
    iSpecialize ("IH" with "[$]").
    iMod (fupd_mask_mono with "IH") as "(?&?&?)"; [done|].
    iApply ("HΦ" with "[$]"). }
  iIntros (σ1 a1) "Hσ". iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  iMod ("IH" with "[$]") as "IH". iModIntro. iDestruct "IH" as (b) "IH".
  iSplit; [done|].
  iDestruct "IH" as "[(% & % & HR) | (% & % & HR)]".
  - iLeft. iExists _. iSplit; [done|].
    iIntros ([e2 σ2] HR). iMod ("HR" $! (e2,σ2) HR) as "HR".
    iModIntro. iMod "HR" as "($ & $ & Hwp1)".
    iMod "Hclose". iModIntro.
    by iApply "Hwp1".
  - iRight. iExists _. iSplit; [done|].
    iIntros ([e2 σ2] a2 HR). iMod ("HR" $! (e2,σ2) a2 HR) as "HR".
    iModIntro. iModIntro. iMod "HR" as "($ & $ & Hwp1)".
    iMod "Hclose". iModIntro. by iApply "Hwp1".
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
  iSpecialize ("H" with "[$]"). rewrite rwp_unfold /rwp_pre Heq.
  iMod "H" as "(H1&H2&Hwand)". by iMod ("Hwand" with "[$]") as "$".
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

Lemma rwp_atomic E1 E2 e Φ `{!Atomic a e} :
  (|={E1,E2}=> RWP e @ E2 ⟨⟨ v, |={E2,E1}=> Φ v ⟩⟩) ⊢ RWP e @ E1 ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros "H". rewrite !rwp_unfold /rwp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { iIntros. iMod ("H"). iMod ("H" with "[$]") as "($&$&$)". }
  iIntros (σ1 a1) "Hσ". iMod "H".
  rewrite /rwp_step.
  iMod ("H" $! σ1 with "Hσ") as "[% H]". iModIntro.
  iSplit; [done|].
  iDestruct "H" as "[(% & % & HR) | (% & % & HR)]".
  - iLeft. iExists _. iSplit.
    { iPureIntro. by apply Rcoupl_pos_R. }
    iIntros ([e2 σ2] (?& Hstep &?)). iMod ("HR" with "[//]") as "HR".
    iModIntro. iMod "HR" as "(H1 & H2 & Hwp1)".
    rewrite !rwp_unfold /rwp_pre .
    destruct (to_val e2) as [v2|] eqn:He2.
    + iMod ("Hwp1" with "[$]") as "($ & $ & H)".
      iMod "H" as "$". eauto.
    + iMod ("Hwp1" with "[$]") as "(% & H)".
      specialize (atomic _ _ _ Hstep) as Hatomic.
      destruct a.
      * destruct Hatomic. simplify_eq.
      * by apply not_reducible in Hatomic.
  - iRight. iExists _. iSplit.
    { iPureIntro. by apply Rcoupl_pos_R. }
    iIntros ([e2 σ2] ? (?& Hstep &?)). iMod ("HR" with "[//]") as "HR".
    iIntros "!> !>". iMod "HR" as "(H1 & H2 & Hwp1)".
    rewrite !rwp_unfold /rwp_pre .
    destruct (to_val e2) as [v2|] eqn:He2.
    + iMod ("Hwp1" with "[$]") as "($ & $ & H)".
      iMod "H" as "$". eauto.
    + iMod ("Hwp1" with "[$]") as "(% & H)".
      specialize (atomic _ _ _ Hstep) as Hatomic.
      destruct a.
      * destruct Hatomic. simplify_eq.
      * by apply not_reducible in Hatomic.
Qed.

Lemma rwp_bind K `{!LanguageCtx K} E e Φ :
  RWP e @ E ⟨⟨ v, RWP K (of_val v) @ E ⟨⟨ Φ ⟩⟩ ⟩⟩ ⊢ RWP K e @ E ⟨⟨ Φ ⟩⟩.
Proof.
  revert Φ. cut (∀ Φ', RWP e @ E ⟨⟨ Φ' ⟩⟩ -∗ ∀ Φ,
  (∀ v, Φ' v -∗ RWP K (of_val v) @ E ⟨⟨ Φ ⟩⟩) -∗ RWP K e @ E ⟨⟨ Φ ⟩⟩).
  { iIntros (help Φ) "H". iApply (help with "H"); auto. }
  iIntros (Φ') "H". iRevert (e E Φ') "H". iApply rwp_strong_ind; first solve_proper.
  iIntros "!#" (e E1 Φ') "IH". iIntros (Φ) "HΦ".
  rewrite /rwp_pre /rwp_step.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. iApply fupd_rwp'.
    iIntros. iMod ("IH" with "[$]") as "($&$&H)".
    by iApply "HΦ". }
  rewrite rwp_unfold /rwp_pre /rwp_step fill_not_val //.
  iIntros (σ1 a1) "H". iMod ("IH" with "H") as "IH". iModIntro.
  iDestruct "IH" as (Hred) "H".
  iSplit; [eauto using reducible_fill|].
  iDestruct "H" as "[(% & % & HR) | (% & % & HR)]".
  - iLeft. iExists (λ '(e2, σ2) ρ', ∃ e2', e2 = K e2' ∧ R2 (e2', σ2) ρ').
    iSplit.
    { iPureIntro.
      rewrite fill_dmap //=.
      rewrite -(dret_id_right (dret _)).
      eapply Rcoupl_dbind; [|done].
      intros [] ?? =>/=. apply Rcoupl_dret. eauto. }
    iIntros ([] (? & -> & ?)) "!#".
    iMod ("HR" with "[//]") as "H".
    iMod "H" as "($ & $ & H )".
    iModIntro. by iApply "H".
  - iRight. iExists (λ '(e2, σ2) ρ', ∃ e2', e2 = K e2' ∧ R2 (e2', σ2) ρ').
    iSplit.
    { iPureIntro.
      rewrite fill_dmap //=.
      rewrite -(dret_id_right (spec_step _)).
      eapply Rcoupl_dbind; [|done].
      intros [] ?? =>/=. apply Rcoupl_dret. eauto. }
    iIntros ([] ? (? & -> & ?)) "".
    iMod ("HR" with "[//]") as "HR".
    iIntros "!> !>".
    iMod "HR" as "($ & $ & H)".
    by iApply "H".
Qed.

(* Lemma rwp_bind_inv K `{!LanguageCtx K} s E e Φ : *)
(*   RWP K e @ E ⟨⟨ Φ ⟩⟩ ⊢ RWP e @ E ⟨⟨ v, RWP K (of_val v) @ E ⟨⟨ Φ ⟩⟩ ⟩⟩. *)
(* Proof. *)
(*   iIntros "H". remember (K e) as e' eqn:He'. *)
(*   iRevert (e He'). iRevert (e' E Φ) "H". iApply rwp_strong_ind; first solve_proper. *)
(*   iIntros "!#" (e' E1 Φ) "IH". iIntros (e ->). *)
(*   rewrite !rwp_unfold {2}/rwp_pre. *)
(*   destruct (to_val e) as [v|] eqn:He. *)
(*   { iIntros (???) "($&$)". iModIntro. apply of_to_val in He as <-. rewrite !rwp_unfold. *)
(*     iApply (rwp_pre_mono with "[] IH"). by iIntros "!#" (E e Φ') "[_ ?]". } *)
(*   rewrite /rwp_pre fill_not_val //. *)
(*   iIntros (σ1 κs n) "Hσ". iMod ("IH" with "[$]") as (b) "IH". iModIntro. *)
(*   iExists b. iNext. iMod "IH" as "[% IH]"; iModIntro. iSplit. *)
(*   { destruct eauto using reducible_fill. } *)
(*   iIntros (e2 σ2 efs κ Hstep). *)
(*   iMod ("IH" $! (K e2) σ2 efs κ with "[]") as "(Hsrc & Hσ & IH & IHefs)"; eauto using fill_step. *)
(*   iModIntro. iFrame "Hsrc Hσ". iSplitR "IHefs". *)
(*   - iDestruct "IH" as "[IH _]". by iApply "IH". *)
(*   - by setoid_rewrite bi.and_elim_r. *)
(* Qed. *)

(** * Derived rules *)
Lemma rwp_mono E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → RWP e @ E ⟨⟨ Φ ⟩⟩ ⊢ RWP e @ E ⟨⟨ Ψ ⟩⟩.
Proof.
  iIntros (HΦ) "H"; iApply (rwp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma rwp_mask_mono E1 E2 e Φ : E1 ⊆ E2 → RWP e @ E1 ⟨⟨ Φ ⟩⟩ ⊢ RWP e @ E2 ⟨⟨ Φ ⟩⟩.
Proof. iIntros (?) "H"; iApply (rwp_strong_mono with "H"); auto. Qed.
Global Instance rwp_mono' E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (rwp (PROP:=iProp Σ) () E e).
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

(** Proofmode class instances *)
Section proofmode_classes.
  Context {Σ A Λ} `{spec A Σ} `{!tprwpG Λ Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.

  Global Instance frame_rwp p E e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (RWP e @ E ⟨⟨ Φ ⟩⟩) (RWP e @ E ⟨⟨ Ψ ⟩⟩).
  Proof. rewrite /Frame=> HR. rewrite rwp_frame_l. apply rwp_mono, HR. Qed.

  Global Instance is_except_0_rwp E e Φ : IsExcept0 (RWP e @ E ⟨⟨ Φ ⟩⟩).
  Proof. by rewrite /IsExcept0 -{2}fupd_rwp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_rwp p E e P Φ :
    ElimModal True p false (|==> P) P (RWP e @ E ⟨⟨ Φ ⟩⟩) (RWP e @ E ⟨⟨ Φ ⟩⟩).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r bi.wand_elim_r fupd_rwp.
  Qed.

  Global Instance elim_modal_fupd_rwp p E e P Φ :
    ElimModal True p false (|={E}=> P) P (RWP e @ E ⟨⟨ Φ ⟩⟩) (RWP e @ E ⟨⟨ Φ ⟩⟩).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r fupd_rwp.
  Qed.

  Global Instance elim_modal_fupd_rwp_atomic p E1 E2 e P Φ :
    Atomic StronglyAtomic e →
    ElimModal True p false (|={E1,E2}=> P) P
            (RWP e @ E1 ⟨⟨ Φ ⟩⟩) (RWP e @ E2 ⟨⟨ v, |={E2,E1}=> Φ v ⟩⟩)%I.
  Proof.
    intros. by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r rwp_atomic.
  Qed.

  Global Instance add_modal_fupd_rwp E e P Φ :
    AddModal (|={E}=> P) P (RWP e @ E ⟨⟨ Φ ⟩⟩).
  Proof. by rewrite /AddModal fupd_frame_r bi.wand_elim_r fupd_rwp. Qed.

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

End proofmode_classes.

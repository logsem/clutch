From Coq Require Export Reals Psatz.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export fixpoint big_op.
From iris.prelude Require Import options.
From clutch.prob Require Export couplings distribution markov.
From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.bi Require Import weakestpre.
From clutch.base_logic Require Export spec_update.
From clutch.common Require Export language erasable.

Import uPred.

Local Open Scope R.

Class clutchWpGS (Λ : language) (Σ : gFunctors) := ClutchWpGS {
  #[global] clutchWpGS_invGS :: invGS_gen HasNoLc Σ;
  #[global] clutchWpGS_spec_updateGS :: spec_updateGS (lang_markov Λ) Σ;

  state_interp : state Λ → iProp Σ;
}.
Global Opaque clutchWpGS_invGS.
Global Arguments ClutchWpGS {Λ Σ _}.

(** * Coupling modalities *)
Section exec_coupl.
  Context `{!clutchWpGS Λ Σ}.

  (** * [spec_coupl] *)

  (** The [spec_coupl] modality allows us to (optionally) prepend spec execution steps and erasable
      distributions, e.g. [state_step]s on both sides. *)
  Definition spec_coupl_pre Z (Φ : state Λ * cfg Λ → iProp Σ) : state Λ * cfg Λ → iProp Σ :=
    (λ (x : state Λ * cfg Λ),
      let '(σ1, (e1', σ1')) := x in
      (∃ (R : state Λ → state Λ → Prop) (μ1 : distr (state Λ)) (μ1' : distr (state Λ)),
        ⌜Rcoupl μ1 μ1' R⌝ ∗
        ⌜erasable μ1 σ1⌝ ∗ ⌜erasable μ1' σ1'⌝ ∗
        ∀ σ2 σ2', ⌜R σ2 σ2'⌝ ={∅}=∗ Z σ2 e1' σ2') ∨
     (∃ (R : state Λ → cfg Λ → Prop) (n : nat) (μ1 : distr (state Λ)) (μ1' : distr (state Λ)),
        ⌜Rcoupl μ1 (σ2 ← μ1'; pexec n (e1', σ2)) R⌝ ∗
        ⌜erasable μ1 σ1⌝ ∗ ⌜erasable μ1' σ1'⌝ ∗
        ∀ σ2 e2' σ2', ⌜R σ2 (e2', σ2')⌝ ={∅}=∗ Φ (σ2, (e2', σ2'))))%I.

  #[local] Instance spec_coupl_pre_ne Z Φ :
    NonExpansive (spec_coupl_pre Z Φ).
  Proof.
    rewrite /spec_coupl_pre.
    intros n (? & (?&?)) (? & (?&?)) ([=] & [[=] [=]]).
    by simplify_eq /=.
  Qed.

  #[local] Instance spec_coupl_pre_mono Z : BiMonoPred (spec_coupl_pre Z).
  Proof.
    split; [|apply _].
    iIntros (Φ Ψ HNEΦ HNEΨ) "#Hwand".
    iIntros ([σ (e' & σ')]) "[(% & % & % & % & % & % & H) | (% & % & % & % & % & % & % & H)]".
    - iLeft. iExists _, _, _. by iFrame "%".
    - iRight. iExists _, _, _, _. iFrame "%".
      iIntros (????). iApply "Hwand". by iApply "H".
  Qed.

  Definition spec_coupl' Z := bi_least_fixpoint (spec_coupl_pre Z).
  Definition spec_coupl σ e' σ' Z := spec_coupl' Z (σ, (e', σ')).

  Lemma spec_coupl_unfold σ1 e1' σ1' Z :
    spec_coupl σ1 e1' σ1' Z ≡
      ((∃ (R : state Λ → state Λ → Prop) (μ1 : distr (state Λ)) (μ1' : distr (state Λ)),
           ⌜Rcoupl μ1 μ1' R⌝ ∗
           ⌜erasable μ1 σ1⌝ ∗ ⌜erasable μ1' σ1'⌝ ∗
           ∀ σ2 σ2', ⌜R σ2 σ2'⌝ ={∅}=∗ Z σ2 e1' σ2') ∨
       (∃ (R : state Λ → cfg Λ → Prop) (n : nat) (μ1 : distr (state Λ)) (μ1' : distr (state Λ)),
           ⌜Rcoupl μ1 (σ2 ← μ1'; pexec n (e1', σ2)) R⌝ ∗
           ⌜erasable μ1 σ1⌝ ∗ ⌜erasable μ1' σ1'⌝ ∗
           ∀ σ2 e2' σ2', ⌜R σ2 (e2', σ2')⌝ ={∅}=∗ spec_coupl σ2 e2' σ2' Z))%I.
  Proof. rewrite /spec_coupl /spec_coupl' least_fixpoint_unfold //. Qed.

  Lemma spec_coupl_base σ1 e1' σ1' Z :
    (∃ (R : state Λ → state Λ → Prop) (μ1 : distr (state Λ)) (μ1' : distr (state Λ)),
           ⌜Rcoupl μ1 μ1' R⌝ ∗
           ⌜erasable μ1 σ1⌝ ∗ ⌜erasable μ1' σ1'⌝ ∗
           ∀ σ2 σ2', ⌜R σ2 σ2'⌝ ={∅}=∗ Z σ2 e1' σ2')
    ⊢ spec_coupl σ1 e1' σ1' Z.
  Proof. iIntros "H". rewrite spec_coupl_unfold. by iLeft. Qed.

  Lemma spec_coupl_rec σ1 e1' σ1' Z :
    (∃ (R : state Λ → cfg Λ → Prop) (n : nat) (μ1 : distr (state Λ)) (μ1' : distr (state Λ)),
           ⌜Rcoupl μ1 (σ2 ← μ1'; pexec n (e1', σ2)) R⌝ ∗
           ⌜erasable μ1 σ1⌝ ∗ ⌜erasable μ1' σ1'⌝ ∗
           ∀ σ2 e2' σ2', ⌜R σ2 (e2', σ2')⌝ ={∅}=∗ spec_coupl σ2 e2' σ2' Z)
    ⊢ spec_coupl σ1 e1' σ1' Z.
  Proof. iIntros "H". rewrite spec_coupl_unfold. by iRight. Qed.

  Lemma spec_coupl_erasable_steps σ1 e1' σ1' Z :
    (∃ (R : state Λ → cfg Λ → Prop) (n : nat) (μ1 : distr (state Λ)),
        ⌜Rcoupl μ1 (pexec n (e1', σ1')) R⌝ ∗
        ⌜erasable μ1 σ1⌝ ∗
        ∀ σ2 e2' σ2', ⌜R σ2 (e2', σ2')⌝ ={∅}=∗ Z σ2 e2' σ2')
    ⊢ spec_coupl σ1 e1' σ1' Z.
  Proof.
    iIntros "(%R & %n & %μ1 & %Hcpl & %Hμ1 & H)".
    iApply spec_coupl_rec.
    iExists R, n, μ1, (dret σ1').
    rewrite dret_id_left.
    iFrame "%".
    iSplit; [iPureIntro; apply dret_erasable|].
    iIntros (σ2 e2' σ2' HR) "!>".
    iApply spec_coupl_base.
    iExists _, (dret σ2), (dret σ2').
    iSplit; [iPureIntro|].
    { apply Rcoupl_pos_R, Rcoupl_trivial; solve_distr_mass. }
    do 2 (iSplit; [iPureIntro; apply dret_erasable|]).
    iIntros (σ3 σ3' (_ & ->%dret_pos & ->%dret_pos)).
    by iApply "H".
  Qed.

  Lemma spec_coupl_steps σ1 e1' σ1' Z :
    (∃ (R : state Λ → cfg Λ → Prop) (n : nat),
        ⌜Rcoupl (dret σ1) (pexec n (e1', σ1')) R⌝ ∗
        ∀ σ2 e2' σ2', ⌜R σ2 (e2', σ2')⌝ ={∅}=∗ Z σ2 e2' σ2')
    ⊢ spec_coupl σ1 e1' σ1' Z.
  Proof.
    iIntros "(%R & %n & %Hcpl & H)".
    iApply spec_coupl_erasable_steps.
    iExists R, n, (dret σ1).
    iFrame "%"; iFrame.
    iPureIntro; apply dret_erasable.
  Qed.

  Lemma spec_coupl_ind (Ψ : state Λ → expr Λ → state Λ → iProp Σ) (Z : state Λ → expr Λ → state Λ → iPropI Σ) :
    ⊢ (□ (∀ σ e' σ',
             spec_coupl_pre Z (λ '(σ, (e', σ')),
                 Ψ σ e' σ' ∧ spec_coupl σ e' σ' Z)%I (σ, (e', σ')) -∗ Ψ σ e' σ') →
       ∀ σ e' σ', spec_coupl σ e' σ' Z -∗ Ψ σ e' σ')%I.
  Proof.
    iIntros "#IH" (σ e' σ') "H".
    set (Ψ' := (λ '(σ, (e', σ')), Ψ σ e' σ') :
           (prodO (stateO Λ) (prodO (exprO Λ) (stateO Λ))) → iProp Σ).
    assert (NonExpansive Ψ').
    { intros n [σ1 [e1' σ1']] [σ2 [e2' σ2']]
        [?%leibniz_equiv [?%leibniz_equiv ?%leibniz_equiv]].
      by simplify_eq/=. }
    iApply (least_fixpoint_ind _ Ψ' with "[] H").
    iIntros "!#" ([? [??]]) "H". by iApply "IH".
  Qed.

  Lemma spec_coupl_mono σ1 e1' σ1' Z1 Z2 :
    (∀ σ2 e2' σ2', Z1 σ2 e2' σ2' ={∅}=∗ Z2 σ2 e2' σ2') -∗
    spec_coupl σ1 e1' σ1' Z1 -∗ spec_coupl σ1 e1' σ1' Z2.
  Proof.
    iIntros "HZ Hs".
    iRevert "HZ"; iRevert (σ1 e1' σ1') "Hs".
    iApply spec_coupl_ind.
    iIntros "!#" (σ e' σ') "[(% & % & % & % & % & % & H) |
                             (% & % & % & % & % & % & % & H)] Hw".
    - iApply spec_coupl_base.
      iExists _, _, _. iFrame "%". iIntros (???).
      iMod ("H" with "[//]"). by iApply "Hw".
    - iApply spec_coupl_rec.
      iExists _, _, _, _. iFrame "%". iIntros (????).
      iMod ("H" with "[//]") as "[IH _]". by iApply "IH".
  Qed.

  Lemma spec_coupl_bind σ1 e1' σ1' Z1 Z2 :
    (∀ σ2 e2' σ2', Z1 σ2 e2' σ2' ={∅}=∗ spec_coupl σ2 e2' σ2' Z2) -∗
    spec_coupl σ1 e1' σ1' Z1 -∗ spec_coupl σ1 e1' σ1' Z2.
  Proof.
    iIntros "HZ Hs".
    iDestruct (spec_coupl_mono with "HZ Hs") as "Hs".
    iRevert (σ1 e1' σ1') "Hs".
    iApply spec_coupl_ind.
    iIntros "!#" (σ1 e1' σ1') "[(%R & % & % & % & % & % & H) |
                                (%R & % & % & % & % & % & % & H)]".
    - iApply spec_coupl_rec.
      iExists (λ σ2 '(e2', σ2'), R σ2 σ2' ∧ e1' = e2'), 0%nat, μ1, μ1'.
      iFrame "%".
      iSplit; [iPureIntro|].
      { setoid_rewrite pexec_O.  rewrite -(dret_id_right μ1).
        eapply Rcoupl_dbind; [|done]. intros ???.
        by apply Rcoupl_dret. }
      iIntros (??? [? <-]).
      by iMod ("H" with "[//]").
    - iApply spec_coupl_rec.
      iExists _, _, _, _.
      iFrame "%". iIntros (????).
      by iMod ("H" with "[//]") as "[H _]".
  Qed.

  Lemma spec_coupl_ret σ1 e1' σ1' (Z : state Λ → expr Λ → state Λ → iProp Σ) :
    Z σ1 e1' σ1' -∗ spec_coupl σ1 e1' σ1' Z.
  Proof.
    iIntros "HZ".
    iApply spec_coupl_base.
    iExists _, (dret σ1), (dret σ1').
    iSplit.
    { iPureIntro. apply Rcoupl_pos_R, Rcoupl_trivial; solve_distr_mass. }
    do 2 (iSplit; [iPureIntro; apply dret_erasable|]).
    by iIntros (?? (_ & ->%dret_pos & ->%dret_pos)).
  Qed.

  (** * [prog_coupl] *)

  (** The [prog_coupl] modality allows us to coupl *exactly* one program step with any number of
      spec execution steps and erasable distributions *)
  Definition prog_coupl e1 σ1 e1' σ1' (Z : expr Λ → state Λ → expr Λ → state Λ → iProp Σ) :=
    (∃ (R : cfg Λ → cfg Λ → Prop) (n : nat) (μ1' : distr (state Λ)),
        ⌜reducible (e1, σ1)⌝ ∗
        ⌜Rcoupl (prim_step e1 σ1) (σ2 ← μ1'; pexec n (e1', σ2)) R⌝ ∗
        ⌜erasable μ1' σ1'⌝ ∗
        ∀ e2 σ2 e2' σ2', ⌜R (e2, σ2) (e2', σ2')⌝ ={∅}=∗ Z e2 σ2 e2' σ2')%I.

  (** TODO: we could probably inject an erasable distribution on the left as well, if we require it
      to preserve reducibility *)
  (** TODO: change to [refRcoupl] rather than [Rcoupl] *)

  Lemma prog_coupl_strong_mono e1 σ1 e1' σ1' Z1 Z2 :
    (∀ e2 σ2 e2' σ2', ⌜∃ σ, prim_step e1 σ (e2, σ2) > 0⌝ ∗ Z1 e2 σ2 e2' σ2' -∗ Z2 e2 σ2 e2' σ2') -∗
    prog_coupl e1 σ1 e1' σ1' Z1 -∗ prog_coupl e1 σ1 e1' σ1' Z2.
  Proof.
    iIntros "Hm (%R & %n & %μ1'& %Hred & %Hcpl & %Hμ1' & Hcnt) /=".
    iExists _, _, _.
    iSplit; [done|].
    iSplit.
    { iPureIntro. by apply Rcoupl_pos_R. }
    iFrame "%".
    iIntros (e2 σ2 e2' σ2' (HR & Hprim & ?)).
    iApply "Hm".
    iSplitR; [by iExists _|].
    by iApply "Hcnt".
  Qed.

  Lemma prog_coupl_mono e1 σ1 e1' σ1' Z1 Z2 :
    (∀ e2 σ2 e2' σ2', Z1 e2 σ2 e2' σ2' -∗ Z2 e2 σ2 e2' σ2') -∗
    prog_coupl e1 σ1 e1' σ1' Z1 -∗ prog_coupl e1 σ1 e1' σ1' Z2.
  Proof.
    iIntros "Hm".
    iApply prog_coupl_strong_mono.
    iIntros (????) "[_ H]". by iApply "Hm".
  Qed.

  Lemma prog_coupl_strengthen e1 σ1 e1' σ1' Z :
    prog_coupl e1 σ1 e1' σ1' Z -∗
    prog_coupl e1 σ1 e1' σ1' (λ e2 σ2 e2' σ2', ⌜∃ σ, prim_step e1 σ (e2, σ2) > 0⌝ ∧ Z e2 σ2 e2' σ2').
  Proof.
    iApply prog_coupl_strong_mono. iIntros (????) "[$ $]".
  Qed.

  Lemma prog_coupl_ctx_bind K `{!LanguageCtx K} e1 σ1 e1' σ1' Z :
    to_val e1 = None →
    prog_coupl e1 σ1 e1' σ1' (λ e2 σ2 e2' σ2', Z (K e2) σ2 e2' σ2') -∗ prog_coupl (K e1) σ1 e1' σ1' Z.
  Proof.
    iIntros (Hv) "(%R & %n & %μ1'& %Hred & %Hcpl & %Hμ1' & Hcnt) /=".
    rewrite /prog_coupl.
    iExists (λ '(e2, σ2) ρ', ∃ e2', e2 = K e2' ∧ R (e2', σ2) ρ'), n, μ1'.
    iSplit; [eauto using reducible_fill|].
    iSplit.
    { iPureIntro.
      rewrite fill_dmap //.
      rewrite -(dret_id_right (μ1' ≫= _ )) //.
      eapply Rcoupl_dbind; [|done].
      intros [] ?? =>/=. apply Rcoupl_dret. eauto. }
    iSplit; [done|].
    iIntros (e2 σ2 e2' σ2' (e3 & -> & HR)).
    by iApply "Hcnt".
  Qed.

  Lemma prog_coupl_prim_steps e1 σ1 e1' σ1' Z :
    (∃ R, ⌜reducible (e1, σ1)⌝ ∗
          ⌜Rcoupl (prim_step e1 σ1) (prim_step e1' σ1') R⌝ ∗
          ∀ e2 σ2 e2' σ2', ⌜R (e2, σ2) (e2', σ2')⌝ -∗ Z e2 σ2 e2' σ2')
    ⊢ prog_coupl e1 σ1 e1' σ1' Z.
  Proof.
    iIntros "(%R & %Hred & %Hcpl & Hcnt)".
    iExists R, 1%nat, (dret σ1').
    rewrite dret_id_left pexec_1 /=.
    assert (reducible (e1', σ1')).
    { apply Rcoupl_mass_eq in Hcpl.
      apply reducible_mass_pos in Hred.
      apply mass_pos_reducible.
      rewrite -Hcpl //. }
    rewrite step_or_final_no_final; [|by apply reducible_not_final].
    iFrame "%".
    iSplit; [iPureIntro; apply dret_erasable|].
    iIntros (e2 σ2 e2' σ2' HR).
    by iApply "Hcnt".
  Qed.

  Lemma prog_coupl_prim_step_l e1 σ1 e1' σ1' Z :
    (∃ R, ⌜reducible (e1, σ1)⌝ ∗
          ⌜Rcoupl (prim_step e1 σ1) (dret (e1', σ1')) R⌝ ∗
          ∀ e2 σ2, ⌜R (e2, σ2) (e1', σ1')⌝ -∗ Z e2 σ2 e1' σ1')
    ⊢ prog_coupl e1 σ1 e1' σ1' Z.
  Proof.
    iIntros "(%R & %Hred & %Hcpl & Hcnt)".
    iExists _, 0%nat, (dret σ1').
    rewrite dret_id_left pexec_O.
    iSplit; [done|].
    iSplit; [iPureIntro; by eapply Rcoupl_pos_R|].
    iSplit; [iPureIntro; apply dret_erasable|].
    iIntros (e2 σ2 e2' σ2' (?&?&[= -> ->]%dret_pos)).
    by iApply "Hcnt".
  Qed.

  Lemma prog_coupl_reducible e e' σ σ' Z :
    prog_coupl e σ e' σ' Z -∗ ⌜reducible (e, σ)⌝.
  Proof. by iIntros "(%R & %n & %μ1'& $ & ?)". Qed.

End exec_coupl.

(** * The weakest precondition  *)
Definition wp_pre `{!clutchWpGS Λ Σ}
    (wp : coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
     coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
  (∀ σ1 e1' σ1',
      state_interp σ1 ∗ spec_interp (e1', σ1') ={E, ∅}=∗
      spec_coupl σ1 e1' σ1' (λ σ2 e2' σ2',
        match to_val e1 with
        | Some v => |={∅, E}=> state_interp σ2 ∗ spec_interp (e2', σ2') ∗ Φ v
        | None =>
            prog_coupl e1 σ2 e2' σ2' (λ e3 σ3 e3' σ3',
                ▷ spec_coupl σ3 e3' σ3' (λ σ4 e4' σ4',
                    |={∅, E}=> state_interp σ4 ∗ spec_interp (e4', σ4') ∗ wp E e3 Φ))
      end))%I.

Local Instance wp_pre_contractive `{!clutchWpGS Λ Σ} : Contractive wp_pre.
Proof.
  rewrite /wp_pre /= => n wp wp' Hwp E e1 Φ.
  do 8 f_equiv.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [? [? ?]]. rewrite /spec_coupl_pre.
  do 17 f_equiv.
  rewrite /prog_coupl.
  do 19 f_equiv.
  f_contractive.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [? [? ?]]. rewrite /spec_coupl_pre.
  do 19 f_equiv.
  apply Hwp.
Qed.

Local Definition wp_def `{!clutchWpGS Λ Σ} : Wp (iProp Σ) (expr Λ) (val Λ) () :=
  {| wp := λ _ : (), fixpoint (wp_pre); wp_default := () |}.
Local Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp' := wp_aux.(unseal).
Global Arguments wp' {Λ Σ _}.
Global Existing Instance wp'.
Local Lemma wp_unseal `{!clutchWpGS Λ Σ} : wp = (@wp_def Λ Σ _).(wp).
Proof. rewrite -wp_aux.(seal_eq) //. Qed.

Section wp.
Context `{!clutchWpGS Λ Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types ρ : cfg Λ.

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
  do 36 f_equiv.
  f_contractive_fin.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [? [? ?]]. rewrite /spec_coupl_pre.
  do 19 f_equiv.
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
  do 16 f_equiv. rewrite /prog_coupl.
  do 19 f_equiv.
  f_contractive.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [? [? ?]]. rewrite /spec_coupl_pre.
  do 22 f_equiv.
Qed.

Lemma wp_value_fupd' E Φ v s : (|={E}=> Φ v) ⊢ WP of_val v @ s; E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre to_of_val.
  iIntros "H" (???) "(?&?)".
  iApply spec_coupl_ret.
  iMod "H". iFrame.
  iApply fupd_mask_subseteq.
  set_solver.
Qed.

Lemma wp_strong_mono E1 E2 e Φ Ψ s :
  E1 ⊆ E2 →
  WP e @ s; E1 {{ Φ }} -∗
  (∀ σ ρ v, state_interp σ ∗ spec_interp ρ ∗ Φ v ={E2}=∗
            state_interp σ ∗ spec_interp ρ ∗ Ψ v) -∗
  WP e @ s; E2 {{ Ψ }}.
Proof.
  iIntros (HE) "H HΦ". iLöb as "IH" forall (e E1 E2 HE Φ Ψ s).
  rewrite !wp_unfold /wp_pre /=.
  iIntros (σ1 e1' σ1') "[Hσ Hs]".
  iSpecialize ("H" with "[$]").
  iMod (fupd_mask_subseteq E1) as "Hclose"; [done|].
  iMod "H"; iModIntro.
  iApply (spec_coupl_mono with "[HΦ Hclose] H").
  iIntros (σ2 e2' σ2') "H".
  destruct (to_val e) as [v|] eqn:?.
  { iMod "H" as "(? & ? & H)".
    iMod "Hclose" as "_".
    iMod ("HΦ" with "[$]") as "($ & $ & $)".
    iApply fupd_mask_subseteq.
    set_solver. }
  iModIntro.
  iApply (prog_coupl_mono with "[HΦ Hclose] H").
  iIntros (e2 σ3 e3' σ3') "H !>".
  iApply (spec_coupl_mono with "[HΦ Hclose] H").
  iIntros (σ4 e4' σ4') "H !>".
  iMod "H" as "($ & $ & H)".
  iMod "Hclose" as "_".
  iModIntro.
  by iApply ("IH" with "[] H").
Qed.

Lemma fupd_wp E e Φ s: (|={E}=> WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre.
  iIntros "H" (???) "[Hσ Hs]".
  destruct (to_val e) as [v|] eqn:?.
  { by iMod ("H" with "[$]"). }
  by iMod ("H" with "[$]").
Qed.

Lemma wp_fupd E e Φ s : WP e @ s; E {{ v, |={E}=> Φ v }} ⊢ WP e @ s; E {{ Φ }}.
Proof.
  iIntros "H".
  iApply (wp_strong_mono E with "H"); [done|].
  by iIntros (???) "($ & $ & > $)".
Qed.

Lemma wp_atomic E1 E2 e Φ `{!Atomic StronglyAtomic e} s :
  (|={E1,E2}=> WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros "H". rewrite !wp_unfold /wp_pre.
  iIntros (σ1 e1' σ1') "[Hσ Hs]".
  iDestruct ("H" with "[$]") as ">> H".
  iModIntro.
  iApply (spec_coupl_mono with "[] H").
  iIntros (σ2 e2' σ2') "H !>".
  destruct (to_val e) as [v|] eqn:?.
  { iDestruct "H" as "> ($ & $ & $)". }
  iDestruct (prog_coupl_strengthen with "H") as "H".
  iApply (prog_coupl_mono with "[] H").
  iIntros (????) "[[% %Hstep] H] !>".
  iApply (spec_coupl_bind with "[] H").
  iIntros (???) "H".
  iMod "H" as "(Hσ & Hρ & H)".
  rewrite !wp_unfold /wp_pre.
  destruct (to_val e2) as [v2|] eqn:He2.
  + iMod ("H" with "[$]") as "H". iModIntro.
    iApply (spec_coupl_mono with "[] H").
    iIntros (???) "> ($ & $ & >H)".
    rewrite -(of_to_val e2 v2) //.
    iApply wp_value_fupd'.
    iApply fupd_mask_intro_subseteq; [|done].
    set_solver.
  + iMod ("H" with "[$]") as "H". iModIntro.
    iApply (spec_coupl_mono with "[] H").
    iIntros (???) "H".
    iDestruct (prog_coupl_reducible with "H") as %[ρ Hr].
    pose proof (atomic _ _ _ Hstep) as [? Hval].
    apply val_stuck in Hr. simplify_eq.
Qed.

Lemma wp_step_fupd E1 E2 e P Φ s :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> P) -∗ WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ s; E1 {{ Φ }}.
Proof.
  rewrite !wp_unfold /wp_pre. iIntros (-> ?) "HR H".
  iIntros (σ1 e1' σ1') "[Hσ Hs]". iMod "HR".
  iMod ("H" with "[$Hσ $Hs]") as "H".
  iModIntro.
  iApply (spec_coupl_mono with "[HR] H").
  iIntros (σ2 e2' σ2') "H !>".
  iApply (prog_coupl_mono with "[HR] H").
  iIntros (e3 σ3 e3' σ3') "H !>".
  iApply (spec_coupl_mono with "[HR] H").
  iIntros (σ4 e4' σ4') "H !>".
  iMod "H" as "($ & $ & H)".
  iMod "HR".
  iApply (wp_strong_mono E2 with "H"); [done..|].
  iIntros "!>" (???) "($ & $ & H)". by iApply "H".
Qed.

Lemma wp_bind K `{!LanguageCtx K} E e Φ s :
  WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }} ⊢ WP K e @ s; E {{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ s). rewrite !wp_unfold /wp_pre.
  iIntros (σ1 e1' σ1') "[Hσ Hs]".
  iMod ("H" with "[$]") as "H".
  iApply (spec_coupl_bind with "[] H").
  iIntros (σ2 e2' σ2') "H".
  destruct (to_val e) as [v|] eqn:He.
  { iMod "H" as "(Hσ & Hs & H)".
    apply of_to_val in He as <-.
    rewrite wp_unfold /wp_pre.
    by iMod ("H" with "[$]"). }
  rewrite fill_not_val /=; [|done].
  iModIntro.
  iApply spec_coupl_ret.
  iApply prog_coupl_ctx_bind; [done|].
  iApply (prog_coupl_mono with "[] H").
  iIntros (e3 σ3 e3' σ3') "H !>".
  iApply (spec_coupl_mono with "[] H").
  iIntros (σ4 e4' σ4') "H !>".
  iMod "H" as "($ & $ & H)".
  iModIntro.
  by iApply "IH".
Qed.

Lemma wp_spec_steps P E1 E2 e Φ a :
  E1 ⊆ E2 →
  spec_update E1 P -∗ (P -∗ WP e @ a; E2 {{ Φ }}) -∗ WP e @ a; E2 {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre.
  iIntros (HE) "Hspec H".
  iIntros (σ1 e1' σ1') "[Hσ Hs]". rewrite /spec_update.
  iMod (fupd_mask_subseteq E1) as "Hclose"; [done|].
    iMod ("Hspec" with "Hs")
    as ([e2' σ2'] n Hstep%stepN_pexec_det%pmf_1_eq_dret) "(Hs & HP)".
    iSpecialize ("H" with "HP").
  iMod "Hclose" as "_".
  iMod ("H" with "[$]") as "H".
  iModIntro.
  iApply spec_coupl_rec.
  iExists _, n, (dret σ1), (dret σ1').
  iSplit; [iPureIntro|].
  { rewrite dret_id_left Hstep.
    apply Rcoupl_pos_R, Rcoupl_trivial; solve_distr_mass. }
  do 2 (iSplit; [iPureIntro; apply dret_erasable|]).
  by iIntros (σ3 e3' σ3' (_ & ->%dret_pos & [= -> ->]%dret_pos)).
Qed.

(** * Derived rules *)
Lemma wp_mono E e Φ Ψ s : (∀ v, Φ v ⊢ Ψ v) → WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (wp_strong_mono with "H"); auto.
  iIntros (???) "($ & $ & ?)". by iApply HΦ.
Qed.
Lemma wp_mask_mono E1 E2 e Φ s : E1 ⊆ E2 → WP e @ s; E1 {{ Φ }} ⊢ WP e @ s; E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (wp_strong_mono with "H"); auto. Qed.
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
Proof. iIntros "[? H]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.
Lemma wp_frame_r E e Φ R s : WP e @ s; E {{ Φ }} ∗ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros "[H ?]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.

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
  iIntros "Hwp H". iApply (wp_strong_mono with "Hwp"); auto.
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

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{!clutchWpGS Λ Σ}.
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

  #[global] Instance elim_modal_spec_update_wp P E e Ψ :
    ElimModal True false false (spec_update E P) P (WP e @ E {{ Ψ }}) (WP e @ E {{ Ψ }}).
  Proof.
    iIntros (?) "[HP Hcnt]". by iApply (wp_spec_steps with "[$] [$]").
  Qed.

  #[global] Instance elim_modal_spec_updateN_wp P E n e Ψ :
    ElimModal True false false (spec_updateN n E P) P (WP e @ E {{ Ψ }}) (WP e @ E {{ Ψ }}).
  Proof.
    iIntros (?) "[HP Hcnt]".
    iDestruct (spec_updateN_implies_spec_update with "HP") as "HP".
    by iApply (wp_spec_steps with "[$] [$]").
  Qed.

End proofmode_classes.

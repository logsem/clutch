From Coq Require Export Reals Psatz.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export fixpoint big_op.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.bi Require Export weakestpre.
From clutch.prob Require Export couplings distribution markov.
From clutch.common Require Export language spec_update.
From clutch.tpref_logic Require Export spec.

Import uPred.

Local Open Scope R.

Class tprwpG (Λ : language) (Σ : gFunctors) := IrisG {
  iris_invGS :: invGS_gen HasNoLc Σ;
  state_interp : state Λ → iProp Σ;
}.
Global Opaque iris_invGS.
Global Arguments IrisG {Λ Σ}.

(** * A coupling fixpoint for [rwp] *)
Section rwp_coupl.
  Context `{spec δ Σ} `{!tprwpG Λ Σ}.

  Definition rwp_coupl_pre (Z : cfg Λ → mstate δ → iProp Σ) (Φ : cfg Λ * mstate δ → iProp Σ) : cfg Λ * mstate δ → iProp Σ :=
    (λ (x : cfg Λ * mstate δ),
      let '((e1, σ1), a1) := x in
        (* Program step *)
        (∃ R, ⌜reducible (e1, σ1)⌝ ∗
              ⌜refRcoupl (dret a1) (prim_step e1 σ1) R⌝ ∗
              ∀ ρ2, ⌜R a1 ρ2⌝ ={∅}=∗ Z ρ2 a1) ∨
        (* Model step *)
        (∃ R, ⌜reducible a1⌝ ∗
              ⌜refRcoupl (step a1) (dret (e1, σ1)) R⌝ ∗
              ∀ a2, ⌜R a2 (e1, σ1)⌝ ={∅}▷=∗ Φ ((e1, σ1), a2)) ∨
        (* Program ~ model coupling step *)
        (∃ R, ⌜reducible a1⌝ ∗
              ⌜reducible (e1, σ1)⌝ ∗
              ⌜refRcoupl (step a1) (prim_step e1 σ1) R⌝ ∗
              ∀ ρ2 a2, ⌜R a2 ρ2⌝ ={∅}▷=∗ Z ρ2 a2) ∨
        (* State-step ~ model coupling *)
        (∃ R αs, ⌜reducible a1⌝ ∗
                 ⌜αs ⊆ get_active σ1⌝ ∗
                 ⌜refRcoupl (step a1) (foldlM state_step σ1 αs) R⌝ ∗
                 ∀ σ2 a2, ⌜R a2 σ2⌝ ={∅}▷=∗ Φ ((e1, σ2), a2)))%I.

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
    iIntros ([(e & σ1) a]) "[(% & % & % & ?) | [(% & % & % & HR) | [(% & % & % & HR) | (% & % & % & % & % & HR)]]]".
    - iLeft. iExists _. eauto.
    - iRight; iLeft. iExists _. iFrame "%".
      iIntros (??). iApply "Hwand". by iApply "HR".
    - iRight; iRight; iLeft. iExists _. eauto.
    - iRight; iRight; iRight.
      iExists _, _. iFrame "%".
      iIntros (???). iApply "Hwand". by iApply "HR".
  Qed.

  Definition rwp_coupl' Z := bi_least_fixpoint (rwp_coupl_pre Z).
  Definition rwp_coupl e σ a Z := rwp_coupl' Z ((e, σ), a).

  Lemma rwp_coupl_unfold e1 σ1 a1 Z :
    rwp_coupl e1 σ1 a1 Z ≡
     ((∃ R, ⌜reducible (e1, σ1)⌝ ∗
            ⌜refRcoupl (dret a1) (prim_step e1 σ1) R⌝ ∗
            ∀ ρ2, ⌜R a1 ρ2⌝ ={∅}=∗ Z ρ2 a1) ∨
      (∃ R, ⌜reducible a1⌝ ∗
            ⌜refRcoupl (step a1) (dret (e1, σ1)) R⌝ ∗
            ∀ a2, ⌜R a2 (e1, σ1)⌝ ={∅}▷=∗ rwp_coupl e1 σ1 a2 Z) ∨
      (∃ R, ⌜reducible a1⌝ ∗
            ⌜reducible (e1, σ1)⌝ ∗
            ⌜refRcoupl (step a1) (prim_step e1 σ1) R⌝ ∗
            ∀ ρ2 a2, ⌜R a2 ρ2⌝ ={∅}▷=∗ Z ρ2 a2) ∨
      (∃ R αs, ⌜reducible a1⌝ ∗
               ⌜αs ⊆ get_active σ1⌝ ∗
               ⌜refRcoupl (step a1) (foldlM state_step σ1 αs) R⌝ ∗
               ∀ σ2 a2, ⌜R a2 σ2⌝ ={∅}▷=∗ rwp_coupl e1 σ2 a2 Z))%I.
  Proof. rewrite /rwp_coupl /rwp_coupl' least_fixpoint_unfold //. Qed.

  #[local] Definition cfgO := (prodO (exprO Λ) (stateO Λ)).

  Lemma rwp_coupl_strong_mono e1 σ1 a1 (Z1 Z2 : cfg Λ → mstate δ → iProp Σ) :
    (∀ ρ2 a2, (⌜∃ σ, prim_step e1 σ ρ2 > 0⌝ ∗ Z1 ρ2 a2 -∗ Z2 ρ2 a2)) -∗
    rwp_coupl e1 σ1 a1 Z1 -∗ rwp_coupl e1 σ1 a1 Z2.
  Proof.
    iIntros "HZ Hrwp". iRevert "HZ".
    set (Φ := (λ x,
      (∀ ρ2 a2, ⌜∃ σ, prim_step x.1.1 σ ρ2 > 0⌝ ∗ Z1 ρ2 a2 -∗ Z2 ρ2 a2) -∗
                rwp_coupl x.1.1 x.1.2 x.2 Z2)%I : prodO cfgO (mstateO δ) → iPropI Σ).
    rewrite /rwp_coupl /rwp_coupl'.
    assert (NonExpansive Φ).
    { intros n ((?&?) & ?) ((?&?) & ?) [[[=] [=]] [=]]. by simplify_eq/=. }
    iPoseProof (least_fixpoint_iter (rwp_coupl_pre Z1) Φ with "[]") as "H"; last first.
    { iIntros "HZ". by iApply ("H" with "Hrwp"). }
    clear.
    iIntros "!#" ([(e & σ1) a]) "[(% & % & % & HR) | [(% & % & % & HR) | [(% & % & % & % & HR) | (% & % & % & % & % & HR)]]] Hwand /=".
    - rewrite rwp_coupl_unfold. iLeft. iExists _.
      iSplit; [done|].
      iSplit; [iPureIntro; by eapply refRcoupl_dret_l_inv|].
      iIntros (ρ2 (HR & _ & Hs)).
      iMod ("HR" with "[//]") as "HZ1". iModIntro.
      iApply "Hwand". eauto.
    - rewrite rwp_coupl_unfold. iRight; iLeft. iExists _.
      iFrame "%". iIntros (a2 HR).
      iMod ("HR" with "[//]") as "HΦ". do 2 iModIntro.
      by iApply "HΦ".
    - rewrite rwp_coupl_unfold. iRight; iRight; iLeft. iExists _.
      iSplit; [done|]. iSplit; [done|].
      iSplit; [iPureIntro; by eapply refRcoupl_pos_R|].
      iIntros (ρ2 a2 (HR & ? & ?)).
      iMod ("HR" with "[//]") as "HZ1". iModIntro.
      iApply "Hwand". iModIntro. iMod "HZ1" as "$". eauto.
    - rewrite rwp_coupl_unfold. iRight; iRight; iRight.
      iExists _, _. iFrame "%".
      iIntros (???). by iApply ("HR" with "[//]").
  Qed.

  Lemma rwp_coupl_strong_ind (Ψ : expr Λ → state Λ → mstate δ → iProp Σ) (Z : cfg Λ → mstate δ → iProp Σ) :
    (∀ n e σ a, Proper (dist n) (Ψ e σ a)) →
    ⊢ (□ (∀ e σ a, rwp_coupl_pre Z (λ '((e, σ), a), Ψ e σ a ∧ rwp_coupl e σ a Z)%I ((e, σ), a) -∗ Ψ e σ a) →
       ∀ e σ a, rwp_coupl e σ a Z -∗ Ψ e σ a)%I.
  Proof.
    iIntros (HΨ). iIntros "#IH" (e σ a) "H".
    set (Ψ' := uncurry3 Ψ :
           (prodO (prodO (exprO Λ) (stateO Λ)) (mstateO δ)) → iProp Σ).
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
                    rwp_coupl (K x.1.1) x.1.2 x.2 Z)%I : prodO cfgO (mstateO δ) → iPropI Σ).
    rewrite /rwp_coupl /rwp_coupl'.
    assert (NonExpansive Φ).
    { intros n ((?&?) & ?) ((?&?) & ?) [[[=] [=]] [=]]. by simplify_eq/=. }
    iPoseProof (least_fixpoint_iter _ Φ with "[]") as "H"; last first.
    { iIntros (?). iApply ("H" $! (e1, _, _) with "Hcpl [//]").  }
    clear e1 σ1 a1.
    iIntros "!#" ([(e & σ1) a]) "[(%R & % & % & HR) | [(%R & % & % & HR) | [(%R & % & % & % & HR) | (% & % & % & % & % & HR)]]] % ".
    - rewrite rwp_coupl_unfold.
      iLeft.
      iExists (λ ρ' '(e2, σ2), ∃ e2', e2 = K e2' ∧ R ρ' (e2', σ2)).
      iSplit; [eauto using reducible_fill|].
      iSplit.
      { iPureIntro.
        rewrite fill_dmap //=.
        rewrite -(dret_id_right (dret _)).
        eapply refRcoupl_dbind; [|done].
        intros ? [] ? =>/=. apply refRcoupl_dret. eauto. }
      iIntros ([? σ2] (e2' & -> & ?)).
      by iApply ("HR" $! (_, _)).
    - rewrite rwp_coupl_unfold.
      iRight; iLeft.
      iExists (λ a2 '(e2, σ2), ∃ e2', e2 = K e2' ∧ R a2 (e2', σ2)).
      iSplit; [done|].
      iSplit.
      { iPureIntro.
        rewrite -(dret_id_right (step _)).
        rewrite -(dret_id_left (λ ρ, dret (K ρ.1, ρ.2)) (_, _)).
        eapply refRcoupl_dbind; [|done].
        intros ? [] ?. apply refRcoupl_dret. eauto. }
      iIntros (a2 (e2' & <-%(inj _) & ?)).
      iMod ("HR" with "[//]") as "H".
      do 2 iModIntro. by iApply "H".
    - rewrite rwp_coupl_unfold.
      iRight; iRight; iLeft.
      iExists (λ a2 '(e2, σ2), ∃ e2', e2 = K e2' ∧ R a2 (e2', σ2)).
      rewrite fill_dmap //=.
      iSplit; [done|].
      iSplit; [eauto using reducible_fill|].
      iSplit.
      { iPureIntro. rewrite -(dret_id_right (step _)).
        eapply refRcoupl_dbind; [|done].
        intros ? [] ? =>/=. apply refRcoupl_dret. eauto. }
      iIntros ([] ? (? & -> & ?)).
      by iMod ("HR" with "[//]").
    - rewrite rwp_coupl_unfold /=.
      iRight; iRight; iRight.
      iExists _, _. iFrame "%".
      iIntros (???). by iApply "HR".
  Qed.

  Lemma rwp_coupl_prim_step_l R e1 σ1 a1 Z :
    reducible (e1, σ1) →
    refRcoupl (dret a1) (prim_step e1 σ1) R →
    (∀ ρ2, ⌜R a1 ρ2⌝ ={∅}=∗ Z ρ2 a1)
     ⊢ rwp_coupl e1 σ1 a1 Z.
  Proof.
    rewrite {1}rwp_coupl_unfold.
    iIntros (??) "H".
    iLeft. iExists R. by iFrame "%".
  Qed.

  Lemma rwp_coupl_step_r R e1 σ1 a1 Z :
    reducible a1 →
    refRcoupl (step a1) (dret (e1, σ1)) R →
    (∀ a2, ⌜R a2 (e1, σ1)⌝ ={∅}▷=∗ rwp_coupl e1 σ1 a2 Z)
    ⊢ rwp_coupl e1 σ1 a1 Z.
  Proof.
    rewrite {1}rwp_coupl_unfold.
    iIntros (??) "H".
    iRight; iLeft. iExists R. by iFrame "%".
  Qed.

  Lemma rwp_coupl_steps R e1 σ1 a1 Z :
    reducible a1 →
    reducible (e1, σ1) →
    refRcoupl (step a1) (prim_step e1 σ1) R →
    (∀ ρ2 a2, ⌜R a2 ρ2⌝ ={∅}▷=∗ Z ρ2 a2)
    ⊢ rwp_coupl e1 σ1 a1 Z.
  Proof.
    rewrite {1}rwp_coupl_unfold.
    iIntros (???) "H".
    iRight; iRight; iLeft. iExists R. by iFrame "%".
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
    { eapply dbind_det_inv_l in Hs.
      eapply mass_pos_reducible. lra. }
    { apply refRcoupl_pos_R, refRcoupl_trivial.
      rewrite dret_mass. apply pmf_SeriesC. }
    iIntros (a3 (_ & ? & _)).
    rewrite step_fupdN_Sn.
    iApply (step_fupd_wand with "Hcpl").
    iApply "IH".
    iPureIntro. by eapply dbind_det_inv_r.
  Qed.

  Lemma rwp_coupl_state_steps R αs e1 σ1 a1 Z :
    reducible a1 →
    αs ⊆ get_active σ1 →
    refRcoupl (step a1) (foldlM state_step σ1 αs) R →
    (∀ σ2 a2, ⌜R a2 σ2⌝ ={∅}▷=∗ rwp_coupl e1 σ2 a2 Z)
    ⊢ rwp_coupl e1 σ1 a1 Z.
  Proof.
    rewrite {1}rwp_coupl_unfold.
    iIntros (???) "H".
    iRight; iRight; iRight.
    iExists _, _. by iFrame "%".
  Qed.

End rwp_coupl.

(** * The refinement weakest preconditions *)
Definition rwp_pre `{spec δ Σ} `{!tprwpG Λ Σ}
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

Lemma rwp_pre_mono `{spec δ Σ} `{!tprwpG Λ Σ} (wp1 wp2 : coPset → expr Λ → (val Λ → iProp Σ) → iProp Σ) :
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
Definition rwp_pre' {Σ δ Λ} `{spec δ Σ} `{!tprwpG Λ Σ} :
  (prodO (prodO (leibnizO coPset) (exprO Λ)) (val Λ -d> iProp Σ) → iProp Σ) →
   prodO (prodO (leibnizO coPset) (exprO Λ)) (val Λ -d> iProp Σ) → iProp Σ
  := uncurry3 ∘ rwp_pre ∘ curry3.

Local Instance exec_coupl_pre_mono {Λ δ Σ} `{spec δ Σ} `{!tprwpG Λ Σ} :
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
      do 19 (f_equiv || case_match || done).
      * done.
      * do 7 (f_equiv || case_match || done). done.
Qed.

(** * RWP *)
#[local] Definition rwp_def {Λ δ Σ} `{!tprwpG Λ Σ, !spec δ Σ} (_ : ()) (E : coPset) (e : expr Λ) (Φ : val Λ → iProp Σ) : iProp Σ
  := bi_least_fixpoint rwp_pre' (E,e,Φ).
#[local] Definition rwp_def' {Λ δ Σ} `{!tprwpG Λ Σ, !spec δ Σ} : Wp (iProp Σ) (expr Λ) (val Λ) () :=
  {| wp := rwp_def; wp_default := () |}.
#[local] Definition rwp_aux : seal (@rwp_def'). by eexists. Qed
                             .
Definition rwp' := rwp_aux.(unseal).
#[global] Existing Instance rwp'.
#[local] Lemma rwp_unseal {Λ δ Σ} `{!tprwpG Λ Σ, !spec δ Σ} : wp = rwp_def'.(wp).
Proof. rewrite -rwp_aux.(seal_eq) //. Qed.

(** * RSWP  *)
(** Notations for 'stronger' weakest preconditions *)
Class Rswp (PROP EXPR VAL A : Type) := {
  rswp : nat → A → coPset → EXPR → (VAL → PROP) → PROP;
  rswp_default : A
}.
Global Arguments rswp {_ _ _ _ _} _ _ _%E _%I.
Global Instance: Params (@rswp) 9 := {}.
Global Arguments rswp_default : simpl never.


(** Notations without binder -- only parsing because they overlap with the
notations with binder. *)
Notation "'RSWP' e 'at' k @ s ; E ⟨⟨ Φ ⟩ ⟩" := (rswp k%nat s E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'RSWP' e 'at' k @ E ⟨⟨ Φ ⟩ ⟩" := (rswp k%nat rswp_default E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'RSWP' e 'at' k ⟨⟨ Φ ⟩ ⟩" := (rswp k%nat rswp_default ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.

(** Notations with binder.  The indentation for the inner format block is chosen
such that *if* one has a single-character mask (e.g. [E]), the second line
should align with the binder(s) on the first line. *)
Notation "'RSWP' e 'at' k @ s ; E ⟨⟨ v , Q ⟩ ⟩" := (rswp k%nat s E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'RSWP'  e  'at'  k  '/' '[          ' @  s ;  E  ⟨⟨  v ,  Q  ⟩ ⟩ ']' ']'") : bi_scope.
Notation "'RSWP' e 'at' k @ E ⟨⟨ v , Q ⟩ ⟩" := (rswp k%nat rswp_default E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'RSWP'  e  'at'  k  '/' '[       ' @  E  ⟨⟨  v ,  Q  ⟩ ⟩ ']' ']'") : bi_scope.
Notation "'RSWP' e 'at' k ⟨⟨ v , Q ⟩ ⟩" := (rswp k%nat rswp_default ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'RSWP'  e  'at'  k  '/' '[   ' ⟨⟨  v ,  Q  ⟩ ⟩ ']' ']'") : bi_scope.

(* Texan triples *)
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k @ s ; E ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ,
      P -∗ ▷^k (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RSWP e at k @ s; E ⟨⟨ Φ ⟩⟩)%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  'at'  k  '/' @  s ;  E  ⟨⟨⟨  x  ..  y ,  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k @ E ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ,
      P -∗ ▷^k (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RSWP e at k @ E ⟨⟨ Φ ⟩⟩)%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  'at'  k  '/' @  E  ⟨⟨⟨  x  ..  y ,  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ,
      P -∗ ▷^k (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RSWP e at k ⟨⟨ Φ ⟩⟩)%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e   'at'  k  '/' ⟨⟨⟨  x  ..  y ,  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.

Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k @ s ; E ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ, P -∗ ▷^k (Q -∗ Φ pat%V) -∗ RSWP e at k @ s; E ⟨⟨ Φ ⟩⟩)%I
    (at level 20,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  'at'  k  '/' @  s ;  E  ⟨⟨⟨  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k @ E ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ, P -∗ ▷^k (Q -∗ Φ pat%V) -∗ RSWP e at k @ E ⟨⟨ Φ ⟩⟩)%I
    (at level 20,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  'at'  k  '/' @  E  ⟨⟨⟨  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ, P -∗ ▷^k(Q -∗ Φ pat%V) -∗ RSWP e at k ⟨⟨ Φ ⟩⟩)%I
    (at level 20,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  'at'  k  '/' ⟨⟨⟨  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.

(** Aliases for stdpp scope -- they inherit the levels and format from above. *)
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k @ s ; E ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ ▷^k (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RSWP e at k @ s; E ⟨⟨ Φ ⟩⟩) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k @ E ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ ▷^k (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RSWP e at k @ E ⟨⟨ Φ ⟩⟩) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ ▷^k (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RSWP e at k ⟨⟨ Φ ⟩⟩) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k @ s ; E ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ ▷^k (Q -∗ Φ pat%V) -∗ RSWP e at k @ s; E ⟨⟨ Φ ⟩⟩) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k @ E ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ ▷^k (Q -∗ Φ pat%V) -∗ RSWP e at k @ E ⟨⟨ Φ ⟩⟩) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ ▷^k (Q -∗ Φ pat%V) -∗ RSWP e at k ⟨⟨ Φ ⟩⟩) : stdpp_scope.

(** An [rswp] takes an [rswp_step] and afterwards proves an [rwp] *)
Definition rswp_step `{spec δ Σ} `{!tprwpG Λ Σ} (k : nat) E (e1 : expr Λ) (Z : expr Λ → iProp Σ) : iProp Σ :=
  (∀ σ1 a1,
      state_interp σ1 ∗ spec_interp a1 ={E,∅}=∗ |={∅}▷=>^k
      ⌜reducible (e1, σ1)⌝ ∧
      (∃ R, ⌜refRcoupl (dret a1) (prim_step e1 σ1) R⌝ ∧
            ∀ e2 σ2, ⌜R a1 (e2, σ2)⌝ -∗ |={∅,E}=> (state_interp σ2 ∗ spec_interp a1 ∗ Z e2))).

#[local] Definition rswp_def {Λ δ Σ} `{!tprwpG Λ Σ, !spec δ Σ}
  (k : nat) (a : ()) (E : coPset) (e : expr Λ) (Φ : val Λ → iProp Σ) : iProp Σ
  := rswp_step k E e (λ e2, WP e2 @ a; E {{ Φ }})%I.
#[local] Definition rswp_def' {Λ δ Σ} `{!tprwpG Λ Σ, !spec δ Σ} : Rswp (iProp Σ) (expr Λ) (val Λ) ()
  := {| rswp := rswp_def; rswp_default := () |}.

#[local] Definition rswp_aux : seal (@rswp_def'). by eexists. Qed.

Definition rswp' := rswp_aux.(unseal).
#[global] Existing Instance rswp'.

#[local] Lemma rswp_unseal `{!spec δ Σ} `{!tprwpG Λ Σ} : rswp = rswp_def'.(rswp).
Proof. rewrite -rswp_aux.(seal_eq) //. Qed.

Section rwp.
Context `{!spec δ Σ} `{!tprwpG Λ Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types b : bool.

Lemma rwp_unfold E e Φ a :
  WP e @ a; E {{ Φ }} ⊣⊢ rwp_pre (wp (PROP:=iProp Σ) a) E e Φ.
Proof. rewrite rwp_unseal /= /rwp_def least_fixpoint_unfold //. Qed.

Lemma rwp_strong_ind Ψ a :
  (∀ n E e, Proper (pointwise_relation _ (dist n) ==> dist n) (Ψ E e)) →
  ⊢ (□ (∀ e E Φ, rwp_pre (λ E e Φ, Ψ E e Φ ∧ WP e @ a; E {{ Φ }}) E e Φ -∗ Ψ E e Φ) →
        ∀ e E Φ, WP e @ a; E {{ Φ }} -∗ Ψ E e Φ)%I.
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

Lemma rwp_ind Ψ a :
  (∀ n E e, Proper (pointwise_relation _ (dist n) ==> dist n) (Ψ E e)) →
  ⊢ (□ (∀ e E Φ, rwp_pre (λ E e Φ, Ψ E e Φ) E e Φ -∗ Ψ E e Φ)
      → ∀ e E Φ, WP e @ a; E {{ Φ }} -∗ Ψ E e Φ)%I.
Proof.
  iIntros (HΨ) "#H". iApply rwp_strong_ind. iIntros "!>" (e E Φ) "Hrwp".
  iApply "H". iApply (rwp_pre_mono with "[] Hrwp"). clear.
  iIntros "!>" (E e Φ) "[$ _]".
Qed.

Global Instance rwp_ne E e n a :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp (PROP:=iProp Σ) a E e).
Proof.
  intros Φ1 Φ2 HΦ. rewrite !rwp_unseal /= /rwp_def' /rwp_def. by apply least_fixpoint_ne.
Qed.

Global Instance rwp_proper E e a :
  Proper (pointwise_relation _ (≡) ==> (≡)) (wp (PROP:=iProp Σ) a E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply rwp_ne=>v; apply equiv_dist.
Qed.

Lemma rwp_strong_ind' Ψ Φ E e a :
  (∀ n e, Proper (dist n) (Ψ e)) →
  ⊢ (□ (∀ e, rwp_pre (λ _ e _, Ψ e ∧ WP e @ a; E {{ Φ }}) E e Φ -∗ Ψ e) →
       WP e @ a; E {{ Φ }} -∗ Ψ e)%I.
Proof.
  iIntros (HΨ) "#IH Hrwp".
  iRevert "IH".
  iApply (rwp_strong_ind (λ E e Φ, _) with "[] Hrwp").
  { intros ??? ???. rewrite /rwp_pre. do 12 f_equiv.
    - do 3 f_equiv.
    - apply least_fixpoint_ne; f_equiv.
      rewrite /rwp_coupl_pre.
      do 27 (f_equiv || case_match). }
  clear.
  iIntros "!#" (e E Φ) "H #IH".
  iApply "IH".
  iIntros (σ ?) "[Hσ Ha]".
  iSpecialize ("H" with "[$]").
  case_match; [done|].
  iMod "H" as "H".
  iModIntro.
  iApply (rwp_coupl_strong_mono with "[] H").
  iIntros ([e2 σ2] a2) "[% >($ & $ & H)] !>".
  iSplit; [by iApply "H"|].
  by iDestruct "H" as "[_ ?]".
Qed.

Lemma rwp_ind' Ψ Φ E e a :
  (∀ n e, Proper (dist n) (Ψ e)) →
  ⊢ (□ (∀ e, rwp_pre (λ _ e _, Ψ e) E e Φ -∗ Ψ e) →
    WP e @ a; E {{ Φ }} -∗ Ψ e)%I.
Proof.
  iIntros (?) "#H".
  iApply rwp_strong_ind'.
  iIntros (e') "!> Hrwp".
  iApply "H".
  iApply (rwp_pre_mono with "[] Hrwp").
  iIntros "!>" (_ ? _) "[$ _]".
Qed.

Lemma rwp_value' E Φ v a : Φ v ⊢ WP of_val v @ a; E {{ Φ }}.
Proof. iIntros "HΦ". rewrite rwp_unfold /rwp_pre to_of_val. by iIntros (??) "[$ $]". Qed.

Lemma rwp_strong_mono' E1 E2 e Φ Ψ a :
  E1 ⊆ E2 →
  WP e @ a; E1 {{ Φ }} -∗
  (∀ σ a v, state_interp σ ∗ spec_interp a ∗ Φ v ={E2}=∗
            state_interp σ ∗ spec_interp a ∗ Ψ v) -∗
  WP e @ a; E2 {{ Ψ }}.
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

Lemma rwp_strong_mono E1 E2 e Φ Ψ a :
  E1 ⊆ E2 →
  WP e @ a; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ WP e @ a; E2 {{ Ψ }}.
Proof.
  iIntros (?) "Hrwp H". iApply (rwp_strong_mono' with "[$]"); auto.
  iIntros (???) "($&$&HΦ)". by iApply "H".
Qed.

Lemma fupd_rwp E e Φ a : (|={E}=> WP e @ a; E {{ Φ }}) ⊢ WP e @ a; E {{ Φ }}.
Proof.
  rewrite rwp_unfold /rwp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?.
  { by iMod "H". }
  iIntros (σ1 a') "HS". iMod "H". by iApply "H".
Qed.
Lemma fupd_rwp' E e Φ a :
  (∀ σ m, state_interp σ ∗ spec_interp m ={E}=∗
          state_interp σ ∗ spec_interp m ∗ WP e @ a; E {{ Φ }})
  ⊢ WP e @ a; E {{ Φ }}.
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
Lemma rwp_fupd E e Φ a : WP e @ a; E {{ v, |={E}=> Φ v }} ⊢ WP e @ a; E {{ Φ }}.
Proof. iIntros "H". iApply (rwp_strong_mono E with "H"); auto. Qed.

Lemma rwp_fupd' E e Φ a :
  WP e @ a; E {{ v, ∀ σ m, state_interp σ ∗ spec_interp m ={E}=∗
                            state_interp σ ∗ spec_interp m ∗ Φ v}}
  ⊢ WP e @ a; E {{ Φ }}.
Proof.
  iIntros "H". iApply (rwp_strong_mono' E with "H"); auto. iIntros (???) "(?&?&H)".
  by iMod ("H" with "[$]").
Qed.

(* TODO: not just StronglyAtomic?  *)
Lemma rwp_atomic E1 E2 e Φ `{!Atomic StronglyAtomic e} a :
  (|={E1,E2}=> WP e @ a; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ a; E1 {{ Φ }}.
Proof.
  iIntros "H". rewrite !rwp_unfold /rwp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { iIntros. iMod ("H"). iMod ("H" with "[$]") as "($&$&$)". }
  iIntros (σ1 a1) "Hσ". iMod "H".
  iMod ("H" $! σ1 with "Hσ") as "H". iModIntro.
  iApply (rwp_coupl_strong_mono with "[] H").
  iIntros ([e2 σ2] a2) "[[% %Hstep] H]".
  iMod "H" as "(Hσ & Ha & Hrwp)".
  rewrite !rwp_unfold /rwp_pre .
  destruct (to_val e2) as [v2|] eqn:He2.
  + iMod ("Hrwp" with "[$]") as "($ & $ & H)".
    iMod "H" as "$". eauto.
  + iMod ("Hrwp" with "[$]") as "H".
    specialize (atomic _ _ _ Hstep) as Hatomic.
    destruct Hatomic. congruence.
Qed.

Lemma rwp_bind K `{!LanguageCtx K} E e Φ a :
  WP e @ a; E {{ v, WP K (of_val v) @ a; E {{ Φ }} }} ⊢ WP K e @ a; E {{ Φ }}.
Proof.
  revert Φ.
  cut (∀ Φ', WP e @ a; E {{ Φ' }} -∗
       ∀ Φ, (∀ v, Φ' v -∗ WP K (of_val v) @ a; E {{ Φ }}) -∗ WP K e @ a; E {{ Φ }}).
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
Lemma rwp_mono E e Φ Ψ a : (∀ v, Φ v ⊢ Ψ v) → WP e @ a; E {{ Φ }} ⊢ WP e @ a; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (rwp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma rwp_mask_mono E1 E2 e Φ a : E1 ⊆ E2 → WP e @ a; E1 {{ Φ }} ⊢ WP e @ a; E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (rwp_strong_mono with "H"); auto. Qed.
Global Instance rwp_mono' E e a :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp (PROP:=iProp Σ) a E e).
Proof. by intros Φ Φ' ?; apply rwp_mono. Qed.

Lemma rwp_value E Φ e v a : IntoVal e v → Φ v ⊢ WP e @ a; E {{ Φ }}.
Proof. intros <-. by apply rwp_value'. Qed.
Lemma rwp_value_fupd' E Φ v a : (|={E}=> Φ v) ⊢ WP of_val v @ a; E {{ Φ }}.
Proof. intros. by rewrite -rwp_fupd -rwp_value'. Qed.
Lemma rwp_value_fupd E Φ e v `{!IntoVal e v} a :
  (|={E}=> Φ v) ⊢ WP e @ a; E {{ Φ }}.
Proof. intros. rewrite -rwp_fupd -rwp_value //. Qed.

Lemma rwp_frame_l E e Φ R a : R ∗ WP e @ a; E {{ Φ }} ⊢ WP e @ a; E {{ v, R ∗ Φ v }}.
Proof. iIntros "[? H]". iApply (rwp_strong_mono with "H"); auto with iFrame. Qed.
Lemma rwp_frame_r E e Φ R a : WP e @ a; E {{ Φ }} ∗ R ⊢ WP e @ a; E {{ v, Φ v ∗ R }}.
Proof. iIntros "[H ?]". iApply (rwp_strong_mono with "H"); auto with iFrame. Qed.

Lemma rwp_wand E e Φ Ψ a :
  WP e @ a; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ a; E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (rwp_strong_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma rwp_wand_l E e Φ Ψ a :
  (∀ v, Φ v -∗ Ψ v) ∗ WP e @ a; E {{ Φ }} ⊢ WP e @ a; E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (rwp_wand with "Hwp H"). Qed.
Lemma rwp_wand_r E e Φ Ψ a :
  WP e @ a; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ a; E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (rwp_wand with "Hwp H"). Qed.
Lemma rwp_frame_wand_l E e Q Φ a :
  Q ∗ WP e @ a; E {{ v, Q -∗ Φ v }} -∗ WP e @ a; E {{ Φ }}.
Proof.
  iIntros "[HQ HWP]". iApply (rwp_wand with "HWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.

End rwp.

Section rswp.
Context `{!spec δ Σ} `{!tprwpG Λ Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types b : bool.

Lemma rswp_unfold k a E e Φ :
  RSWP e at k @ a; E ⟨⟨ Φ ⟩⟩ ⊣⊢ rswp_step k E e (λ e2, WP e2 @ a; E {{ Φ }}).
Proof. by rewrite rswp_unseal. Qed.

Global Instance rswp_ne k a E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (rswp (PROP:=iProp Σ) k a E e).
Proof.
  intros Φ1 Φ2 HΦ. rewrite !rswp_unfold /rswp_step. do 22 f_equiv.
Qed.

Global Instance rswp_proper k a E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (rswp (PROP:=iProp Σ) k a E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply rswp_ne=>v; apply equiv_dist.
Qed.

Lemma rswp_strong_mono k E1 E2 e Φ Ψ a :
  E1 ⊆ E2 →
  RSWP e at k @ a; E1 ⟨⟨ Φ ⟩⟩ -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ RSWP e at k @ a; E2 ⟨⟨ Ψ ⟩⟩.
Proof.
  iIntros (HE); rewrite !rswp_unfold /rswp_step.
  iIntros "H  HΦ" (σ1 m) "Hσ". iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  iMod ("H" with "[$]") as "H". iModIntro.
  iApply (step_fupdN_wand with "H").
  iIntros "(% & % & % & H)".
  iSplit; [done|].
  iExists _. iSplit; [done|]. iIntros (e2 σ2 HR).
  iMod ("H" with "[//]") as "($ & $ & H)".
  iMod "Hclose" as "_". iModIntro.
  by iApply (rwp_strong_mono with "H").
Qed.

Lemma fupd_rswp k E e Φ a : (|={E}=> RSWP e at k @ a; E ⟨⟨ Φ ⟩⟩) ⊢ RSWP e at k @ a; E ⟨⟨ Φ ⟩⟩.
Proof.
  rewrite rswp_unfold /rswp_step. iIntros "H".
  iIntros (σ1 m) "HS". iMod "H". by iApply "H".
Qed.
Lemma rswp_fupd k E e Φ a : RSWP e at k @ a; E ⟨⟨ v, |={E}=> Φ v ⟩⟩ ⊢ RSWP e at k @ a; E ⟨⟨ Φ ⟩⟩.
Proof. iIntros "H". iApply (rswp_strong_mono k E with "H"); auto. Qed.

Lemma rwp_no_step E e Φ a :
  TCEq (to_val e) None →
  RSWP e at 0 @ a; E ⟨⟨ Φ ⟩⟩ ⊢ WP e @ a; E {{ Φ }}.
Proof.
  rewrite rswp_unfold rwp_unfold /rwp_pre /rswp_step.
  iIntros (->) "Hswp". iIntros (σ1 m) "[Ha Hσ]".
  iMod ("Hswp" with "[$]") as "(% & % & % & Hswp)". iModIntro.
  iApply rwp_coupl_prim_step_l; [done|done|].
  iIntros ([e2 σ2] HR) "!>".
  by iMod ("Hswp" with "[//]").
Qed.

Lemma rwp_spec_steps n P E e Φ a :
  TCEq (to_val e) None →
  (P -∗ RSWP e at n @ a; E ⟨⟨ Φ ⟩⟩) ∗ spec_update n E P ⊢ WP e @ a; E {{ Φ }}.
Proof.
  rewrite rswp_unfold rwp_unfold /rwp_pre /rswp_step.
  iIntros (->) "[Hswp Hspec]". iIntros (σ1 m) "[Hσ1 Ha]". rewrite /spec_update.
  iMod ("Hspec" with "Ha") as (a' Ha) "(Hsource_interp & HP)".
  iMod ("Hswp" with "HP [$]") as "Hswp".
  iModIntro.
  iApply rwp_coupl_det_r; [done|].
  iApply (step_fupdN_mono with "Hswp").
  iIntros "(% & % & % & H)".
  iApply rwp_coupl_prim_step_l; [done|done|].
  iIntros ([e2 σ2] HR) "!>".
  by iMod ("H" with "[//]").
Qed.

Lemma rwp_spec_steps' n P E e Φ a :
  TCEq (to_val e) None →
  (P -∗ ▷^n WP e @ a; E {{ Φ }}) ∗ spec_update n E P ⊢ WP e @ a; E {{ Φ }}.
Proof.
  rewrite rwp_unfold /rwp_pre.
  iIntros (->) "[Hrwp Hspec]". iIntros (σ1 m) "[Hσ1 Ha]". rewrite /spec_update.
  iMod ("Hspec" with "Ha") as (a' Ha) "(Hsource_interp & HP)".
  iSpecialize ("Hrwp" with "HP").
  iApply fupd_mono.
  { iIntros "H". by iApply rwp_coupl_det_r. }
  iApply step_fupdN_mask_comm'; [set_solver|].
  iApply step_fupdN_intro; [done|].
  iModIntro.
  by iMod ("Hrwp" with "[$]").
Qed.

Lemma rswp_later k E e Φ a :
  ▷ RSWP e at k @ a; E ⟨⟨ Φ ⟩⟩ ⊢ RSWP e at (S k) @ a; E ⟨⟨ Φ ⟩⟩.
Proof.
  rewrite 2!rswp_unfold /rswp_step.
  iIntros "H" (σ1 m) "[Hσ Ha]".
  iMod (fupd_mask_subseteq ∅) as "Hclose"; [set_solver|].
  rewrite step_fupdN_Sn.
  do 3 iModIntro.
  iMod "Hclose" as "_".
  by iMod ("H" with "[$]").
Qed.

(* TODO: not just [StronglyAtomic]? *)
Lemma rswp_atomic k E1 E2 e Φ `{!Atomic StronglyAtomic e} a :
  (|={E1,E2}=> RSWP e at k @ a; E2 ⟨⟨ v, |={E2,E1}=> Φ v ⟩⟩) ⊢ RSWP e at k @ a; E1 ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros "H". rewrite !rswp_unfold /rswp_step.
  iIntros (σ1 m) "Hσ". iMod "H".
  iMod ("H" $! σ1 with "Hσ") as "H". iModIntro.
  iApply (step_fupdN_wand with "H"); iIntros "[% (%R & % & H)]".
  iSplit; [done|].
  iExists _.
  iSplit; [iPureIntro; by eapply refRcoupl_pos_R|].
  iIntros (e2 σ2 (HR & ? & Hstep)).
  iMod ("H" with "[//]") as "(Hσ2 & Ha & H)".
  rewrite 2!rwp_unfold /rwp_pre. case_match eqn:He2.
  - iDestruct ("H" with "[$]") as ">($ & $ & >$)". eauto.
  - specialize (atomic _ _ _ Hstep) as Hatomic.
    destruct Hatomic. congruence.
Qed.

Lemma rswp_bind K `{!LanguageCtx K} k E e Φ a :
  to_val e = None →
  RSWP e at k @ a; E ⟨⟨ v, WP K (of_val v) @ a; E {{ Φ }} ⟩⟩ ⊢ RSWP K e at k @ a; E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros (He) "H". rewrite !rswp_unfold /rswp_step.
  iIntros (σ1 m) "Hσ". iMod ("H" with "Hσ") as "H".
  iModIntro. iApply (step_fupdN_wand with "H").
  iIntros "[% (%R & % & H)]".
  iSplit; [eauto using reducible_fill|].
  iExists (λ a' '(e2, σ2), ∃ e2', e2 = K e2' ∧ R a' (e2', σ2)).
  iSplit.
  { iPureIntro.
    rewrite fill_dmap //=.
    rewrite -(dret_id_right (dret _)).
    eapply refRcoupl_dbind; [|done].
    intros ? [] ? =>/=. apply refRcoupl_dret. eauto. }
  iIntros (?? (? & -> &?)).
  iMod ("H" with "[//]") as "($ & $ & H)".
  iModIntro.
  by iApply rwp_bind.
Qed.

(** * Derived rules *)
Lemma rswp_mono k E e Φ Ψ a : (∀ v, Φ v ⊢ Ψ v) → RSWP e at k @ a; E ⟨⟨ Φ ⟩⟩ ⊢ RSWP e at k @ a; E ⟨⟨ Ψ ⟩⟩.
Proof.
  iIntros (HΦ) "H". iApply (rswp_strong_mono with "[H] []"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma rswp_mask_mono k E1 E2 e Φ a : E1 ⊆ E2 → RSWP e at k @ a; E1 ⟨⟨ Φ ⟩⟩ ⊢ RSWP e at k @ a; E2 ⟨⟨ Φ ⟩⟩.
Proof. iIntros (?) "H"; iApply (rswp_strong_mono with "H"); auto. Qed.
Global Instance rswp_mono' k E e a :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (rswp (PROP:=iProp Σ) k a E e).
Proof. by intros Φ Φ' ?; apply rswp_mono. Qed.

Lemma rswp_frame_l k E e Φ R a : R ∗ RSWP e at k @ a; E ⟨⟨ Φ ⟩⟩ ⊢ RSWP e at k @ a; E ⟨⟨ v, R ∗ Φ v ⟩⟩.
Proof. iIntros "[? H]". iApply (rswp_strong_mono with "H"); auto with iFrame. Qed.
Lemma rswp_frame_r k E e Φ R a : RSWP e at k @ a; E ⟨⟨ Φ ⟩⟩ ∗ R ⊢ RSWP e at k @ a; E ⟨⟨ v, Φ v ∗ R ⟩⟩.
Proof. iIntros "[H ?]". iApply (rswp_strong_mono with "H"); auto with iFrame. Qed.

Lemma rswp_wand k E e Φ Ψ a :
  RSWP e at k @ a; E ⟨⟨ Φ ⟩⟩ -∗ (∀ v, Φ v -∗ Ψ v) -∗ RSWP e at k @ a; E ⟨⟨ Ψ ⟩⟩.
Proof.
  iIntros "Hwp H". iApply (rswp_strong_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma rswp_wand_l k E e Φ Ψ a :
  (∀ v, Φ v -∗ Ψ v) ∗ RSWP e at k @ a; E ⟨⟨ Φ ⟩⟩ ⊢ RSWP e at k @ a; E ⟨⟨ Ψ ⟩⟩.
Proof. iIntros "[H Hwp]". iApply (rswp_wand with "Hwp H"). Qed.
Lemma rswp_wand_r k E e Φ Ψ a :
  RSWP e at k @ a; E ⟨⟨ Φ ⟩⟩ ∗ (∀ v, Φ v -∗ Ψ v) ⊢ RSWP e at k @ a; E ⟨⟨ Ψ ⟩⟩.
Proof. iIntros "[Hwp H]". iApply (rswp_wand with "Hwp H"). Qed.
Lemma rswp_frame_wand_l k E e Q Φ a :
  Q ∗ RSWP e at k @ a; E ⟨⟨ v, Q -∗ Φ v ⟩⟩ -∗ RSWP e at k @ a; E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros "[HQ HWP]". iApply (rswp_wand with "HWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.

End rswp.


(** Proofmode class instances *)
Section proofmode_classes.
  Context {Σ δ Λ} `{!spec δ Σ} `{!tprwpG Λ Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.

  Global Instance frame_rwp p E e R Φ Ψ a :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (WP e @ a; E {{ Φ }}) (WP e @ a; E {{ Ψ }}).
  Proof. rewrite /Frame=> HR. rewrite rwp_frame_l. apply rwp_mono, HR. Qed.

  Global Instance frame_rswp k p E e R Φ Ψ a :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (RSWP e at k @ a; E ⟨⟨ Φ ⟩⟩) (RSWP e at k @ a; E ⟨⟨ Ψ ⟩⟩).
  Proof. rewrite /Frame=> HR. rewrite rswp_frame_l. apply rswp_mono, HR. Qed.

  Global Instance is_except_0_rwp E e Φ a : IsExcept0 (WP e @ a; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_rwp -except_0_fupd -fupd_intro. Qed.

  Global Instance is_except_0_rswp k E e Φ a : IsExcept0 (RSWP e at k @ a; E ⟨⟨ Φ ⟩⟩).
  Proof. by rewrite /IsExcept0 -{2}fupd_rswp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_rwp p E e P Φ a :
    ElimModal True p false (|==> P) P (WP e @ a; E {{ Φ }}) (WP e @ a; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
         (bupd_fupd E) fupd_frame_r bi.wand_elim_r fupd_rwp.
  Qed.

  Global Instance elim_modal_bupd_rswp k p E e P Φ a :
    ElimModal True p false (|==> P) P (RSWP e at k @ a; E ⟨⟨ Φ ⟩⟩) (RSWP e at k @ a; E ⟨⟨ Φ ⟩⟩).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
         (bupd_fupd E) fupd_frame_r bi.wand_elim_r fupd_rswp.
  Qed.

  Global Instance elim_modal_fupd_rwp p E e P Φ a :
    ElimModal True p false (|={E}=> P) P (WP e @ a; E {{ Φ }}) (WP e @ a; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
         fupd_frame_r bi.wand_elim_r fupd_rwp.
  Qed.

  Global Instance elim_modal_fupd_rswp k p E e P Φ a :
    ElimModal True p false (|={E}=> P) P (RSWP e at k @ a; E ⟨⟨ Φ ⟩⟩) (RSWP e at k @ a; E ⟨⟨ Φ ⟩⟩).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
         fupd_frame_r bi.wand_elim_r fupd_rswp.
  Qed.

  Global Instance elim_modal_fupd_rwp_atomic p E1 E2 e P Φ a :
    ElimModal (Atomic StronglyAtomic e) p false (|={E1,E2}=> P) P
      (WP e @ a; E1 {{ Φ }}) (WP e @ a; E2 {{ v, |={E2,E1}=> Φ v }})%I | 100.
  Proof.
    intros ?. by rewrite intuitionistically_if_elim
                   fupd_frame_r wand_elim_r rwp_atomic.
  Qed.

  Global Instance elim_modal_fupd_rswp_atomic k p E1 E2 e P Φ a :
    ElimModal (Atomic StronglyAtomic e) p false (|={E1,E2}=> P) P
      (RSWP e at k @ a; E1 ⟨⟨ Φ ⟩⟩) (RSWP e at k @ a; E2 ⟨⟨ v, |={E2,E1}=> Φ v ⟩⟩)%I | 100.
  Proof.
    intros ?. by rewrite intuitionistically_if_elim
                   fupd_frame_r wand_elim_r rswp_atomic.
  Qed.

  Global Instance add_modal_fupd_rwp E e P Φ a :
    AddModal (|={E}=> P) P (WP e @ a; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r bi.wand_elim_r fupd_rwp. Qed.

  Global Instance add_modal_fupd_rswp k E e P Φ a :
    AddModal (|={E}=> P) P (RSWP e at k @ a; E ⟨⟨ Φ ⟩⟩).
  Proof. by rewrite /AddModal fupd_frame_r bi.wand_elim_r fupd_rswp. Qed.

  Global Instance elim_acc_wp {X} E1 E2 α β γ e Φ a :
    ElimAcc (X:=X) (Atomic StronglyAtomic e) (fupd E1 E2) (fupd E2 E1)
      α β γ (WP e @ a; E1 {{ Φ }})
      (λ x, WP e @ a; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I | 100.
  Proof.
    intros ?. rewrite /ElimAcc.
    iIntros "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (rwp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_rswp {X} k E1 E2 α β γ e Φ a :
    ElimAcc (X:=X) (Atomic StronglyAtomic e) (fupd E1 E2) (fupd E2 E1)
      α β γ (RSWP e at k @ a; E1 ⟨⟨ Φ ⟩⟩)
      (λ x, RSWP e at k @ a; E2 ⟨⟨ v, |={E2}=> β x ∗ (γ x -∗? Φ v) ⟩⟩)%I | 100.
  Proof.
    intros ?. rewrite /ElimAcc.
    iIntros "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (rswp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_wp_nonatomic {X} E α β γ e Φ a :
    ElimAcc (X:=X) True (fupd E E) (fupd E E)
      α β γ (WP e @ a; E {{ Φ }})
      (λ x, WP e @ a; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply rwp_fupd.
    iApply (rwp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_swp_nonatomic {X} k E α β γ e Φ a :
    ElimAcc (X:=X) True (fupd E E) (fupd E E)
      α β γ (RSWP e at k @ a; E ⟨⟨ Φ ⟩⟩)
      (λ x, RSWP e at k @ a; E ⟨⟨ v, |={E}=> β x ∗ (γ x -∗? Φ v) ⟩⟩)%I.
  Proof.
    rewrite /ElimAcc.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply rswp_fupd.
    iApply (rswp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

End proofmode_classes.

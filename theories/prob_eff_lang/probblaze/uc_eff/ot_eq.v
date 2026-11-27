(* The values of the oblivious transfer of [ot.v] in the equivalence logic
   of [eq/]: the reference string, the receiver's message, the
   ciphertexts; and the coupling tactics the OT proofs use.  Shared by the
   proofs of all corruption cases. *)

From iris.proofmode Require Import base proofmode classes.
From iris.bi Require Import monpred.
From iris.proofmode Require Import monpred.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory semantics logic adequacy mode.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_row sem_sig sem_env sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze.eq Require Import eq_logic eq_valgroup eq_compat.
From clutch.prob_eff_lang.probblaze.uc_eff Require Import modules eq_modules ot.

Import fingroup.
Import fingroup.fingroup.
Import valgroup_notation.

#[local] Set Default Proof Using "All".

Section ot_eq.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  #[local] Open Scope bi_scope.

  (* The reference string. *)
  Lemma eq_crs (a b c d : vgG) :
    ⊢ ⟪ Crs ⟫ (vgval a, vgval b, vgval c, vgval d)%V (vgval a, vgval b, vgval c, vgval d)%V.
  Proof.
    rewrite /Crs. iEval (rewrite eq_lift_prod).
    iExists _, _, _, _. do 2 (iSplit; first done). iSplitL; last by iApply eq_group_val.
    iEval (rewrite eq_lift_prod).
    iExists _, _, _, _. do 2 (iSplit; first done). iSplitL; last by iApply eq_group_val.
    iEval (rewrite eq_lift_prod).
    iExists _, _, _, _. do 2 (iSplit; first done). iSplitL; by iApply eq_group_val.
  Qed.

  (* A pair of group elements: the receiver's message. *)
  Lemma eq_pair (a b a' b' : vgG) :
    a = a' → b = b' → ⊢ ⟪ 𝔾 × 𝔾 ⟫ (vgval a, vgval b)%V (vgval a', vgval b')%V.
  Proof.
    intros -> ->. iEval (rewrite eq_lift_prod).
    iExists _, _, _, _. do 2 (iSplit; first done). iSplitL; by iApply eq_group_val.
  Qed.

  (* Two ciphertexts, given and read. *)
  Lemma eq_ctxts (a b c d a' b' c' d' : vgG) :
    a = a' → b = b' → c = c' → d = d' →
    ⊢ ⟪ (𝔾 × 𝔾) × (𝔾 × 𝔾) ⟫ (vgval a, vgval b, (vgval c, vgval d))%V
                              (vgval a', vgval b', (vgval c', vgval d'))%V.
  Proof.
    intros -> -> -> ->. iEval (rewrite eq_lift_prod).
    iExists _, _, _, _. do 2 (iSplit; first done).
    iSplitL; iEval (rewrite eq_lift_prod); iExists _, _, _, _; do 2 (iSplit; first done);
      iSplitL; by iApply eq_group_val.
  Qed.

  Lemma eq_lift_ctxts vl vr :
    ⟪ (𝔾 × 𝔾) × (𝔾 × 𝔾) ⟫ vl vr ⊢
      ∃ c0 d0 c1 d1 : vgG,
        ⌜vl = (vgval c0, vgval d0, (vgval c1, vgval d1))%V ∧
         vr = (vgval c0, vgval d0, (vgval c1, vgval d1))%V⌝.
  Proof.
    iIntros "H". iEval (rewrite eq_lift_prod) in "H".
    iDestruct "H" as (el er fl fr) "(-> & -> & He & Hf)".
    iEval (rewrite eq_lift_prod) in "He". iDestruct "He" as (cl cr dl dr) "(-> & -> & Hc & Hd)".
    iEval (rewrite eq_lift_prod) in "Hf". iDestruct "Hf" as (cl' cr' dl' dr') "(-> & -> & Hc' & Hd')".
    iEval (rewrite eq_lift_group) in "Hc". iDestruct "Hc" as (c0) "[-> ->]".
    iEval (rewrite eq_lift_group) in "Hd". iDestruct "Hd" as (d0) "[-> ->]".
    iEval (rewrite eq_lift_group) in "Hc'". iDestruct "Hc'" as (c1) "[-> ->]".
    iEval (rewrite eq_lift_group) in "Hd'". iDestruct "Hd'" as (d1) "[-> ->]".
    by iExists c0, d0, c1, d1.
  Qed.

End ot_eq.

(* Coupling the next [rand] of both programs: along a bijection [f], and
   along [f] avoiding the value [a] for an error credit. *)
Tactic Notation "couple_along" constr(f) :=
  eq_focus_l (rand #_)%E; eq_focus_r (rand #_)%E; iApply (eq_couple_rand_rand_bij _ _ f).
Tactic Notation "couple_along" constr(f) "avoiding" constr(a) :=
  eq_focus_l (rand #_)%E; eq_focus_r (rand #_)%E; iApply (eq_couple_rand_rand_avoid _ _ a f).

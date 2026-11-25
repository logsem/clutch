(* Rules of the equivalence logic ([eq/]) used to reason about modules:
   reading values of base types, calling the operations of an interface,
   and turning a self-equivalence into a typing. *)

From iris.proofmode Require Import base proofmode classes.
From iris.bi Require Import monpred.
From iris.proofmode Require Import monpred.
From clutch.prob_eff_lang.probblaze Require Import primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory semantics logic adequacy mode.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_row sem_sig sem_env sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze Require Import valgroup.
From clutch.prob_eff_lang.probblaze.eq Require Import eq_logic eq_valgroup eq_compat.

Import fingroup.
Import fingroup.fingroup.
Import valgroup_notation.

#[local] Set Default Proof Using "All".

Section eq_modules.
  Context `{!probblazeRGS Σ}.
  #[local] Open Scope bi_scope.

  Lemma eq_lift_bool vl vr :
    eq_lift (Σ := Σ) sem_ty_bool vl vr ⊣⊢ ∃ b : bool, ⌜vl = #b ∧ vr = #b⌝.
  Proof.
    split=> d. rewrite monPred_at_exist eq_lift_at. setoid_rewrite monPred_at_pure.
    destruct d; rewrite /pick /sem_ty_bool /=; iSplit; iIntros "[%b %H]"; iExists b;
      iPureIntro; naive_solver.
  Qed.

  Lemma eq_lift_option (τ : sem_ty Σ) vl vr :
    ⟪ Option τ ⟫ vl vr ⊣⊢
      ⌜vl = NONEV ∧ vr = NONEV⌝ ∨ ∃ wl wr, ⌜vl = SOMEV wl ∧ vr = SOMEV wr⌝ ∗ ⟪ τ ⟫ wl wr.
  Proof.
    rewrite /sem_ty_option eq_lift_sum. iSplit.
    - iIntros "(%wl & %wr & [(-> & -> & H)|(-> & -> & H)])".
      + iEval (rewrite eq_lift_unit) in "H". iDestruct "H" as %[-> ->]. by iLeft.
      + iRight. iExists _, _. by iFrame.
    - iIntros "[[-> ->]|(%wl & %wr & [-> ->] & H)]".
      + iExists #()%V, #()%V. iLeft. do 2 (iSplit; first done). by iEval (rewrite eq_lift_unit).
      + iExists _, _. iRight. by iFrame.
  Qed.

  (* Related state of the two programs: a flag, and a pair of empty tapes. *)
  Definition flag_rel (s s' : loc) : iPropD Σ := ∃ b : bool, s ↦ₗ #b ∗ s' ↦ᵣ #b.
  Definition tape_rel (N : nat) (α α' : loc) : iPropD Σ := α ↪ₗN (N; []) ∗ α' ↪ᵣN (N; []).

  (* A self-equivalence is a typing. *)
  Lemma eq_val_typed (v : val) (τ : sem_ty Σ) : (⊢ ⟪ τ ⟫ v v) → ⊢ ⊨ᵥ v ≤ v : τ.
  Proof.
    intros [H]. specialize (H Fwd). rewrite monPred_at_emp eq_lift_at /pick /= in H.
    rewrite /sem_val_typed /tc_opaque. iModIntro. by iApply H.
  Qed.

  (* Calling an operation in evaluation contexts, without a frame: at the
     row of the operation itself. *)
  Lemma eq_call m (θ : sem_row Σ) (A B : sem_ty Σ) (fl fr wl wr : val) Kl Kr R :
    (∀ l1s, NeutralEctx l1s Kl) → (∀ l2s, NeutralEctx l2s Kr) →
    ⊢ ⟪ A -{ θ }-[m]-> B ⟫ fl fr -∗ ⟪ A ⟫ wl wr -∗
      □ (∀ vl vr, ⟪ B ⟫ vl vr -∗
           EQ fill Kl (Val vl) ≈ fill Kr (Val vr) <|iLblSig_to_iLblThy θ|> {{ R }}) -∗
      EQ fill Kl (fl wl) ≈ fill Kr (fr wr) <|iLblSig_to_iLblThy θ|> {{ R }}.
  Proof.
    intros ??. iStartProof (iProp _). iIntros (d) "Hf Hw #Hc".
    iEval (rewrite eq_lift_at /sem_ty_mbang) in "Hf". iEval (rewrite eq_lift_at) in "Hw".
    iDestruct (bi.intuitionistically_if_elim with "Hf") as "Hf".
    destruct d; rewrite eq_rel_at /pick /=.
    - iApply brel_bind'; first by iApply traversable_to_iThy.
      rewrite /sem_ty_arr /=. iApply (brel_wand with "[Hf Hw]"); first by iApply "Hf".
      iIntros "!>" (v1 v2) "HB". iApply (eq_rel_at_elim_const Fwd).
      iApply ("Hc" $! v1 v2 with "[HB]"). by rewrite eq_lift_at.
    - iApply brel_bind'; first by iApply traversable_to_iThy.
      rewrite /sem_ty_arr /=. iApply (brel_wand with "[Hf Hw]"); first by iApply "Hf".
      iIntros "!>" (v1 v2) "HB". iApply (eq_rel_at_elim_const Bwd).
      iApply ("Hc" $! v2 v1 with "[HB]"). by rewrite eq_lift_at.
  Qed.

  (* Calling a one-shot (affine) operation, typed at row [¡ θ'], in
     evaluation contexts, keeping a frame [P] across the call. *)
  Lemma brel_call_frame_aff (θ' ρ : sem_row Σ) (A B : sem_ty Σ) (P : iProp Σ)
      (f1 f2 w1 w2 : val) K1 K2 R :
    (∀ l1s, NeutralEctx l1s K1) → (∀ l2s, NeutralEctx l2s K2) →
    ⊢ (¡ θ')%R ≤ᵣ ρ -∗ (A -{ ¡ θ' }-∘ B)%T f1 f2 -∗ A w1 w2 -∗ P -∗
      □ (∀ v1 v2, B v1 v2 -∗ P -∗
           BREL fill K1 (Val v1) ≤ fill K2 (Val v2) <|iLblSig_to_iLblThy ρ|> {{ R }}) -∗
      BREL fill K1 (f1 w1) ≤ fill K2 (f2 w2) <|iLblSig_to_iLblThy ρ|> {{ R }}.
  Proof.
    iIntros (HK1 HK2) "#Hρ Hf Hw HP #Hc".
    iApply (brel_bind K1 K2); [by iApply traversable_to_iThy|iApply to_iThy_le_refl|].
    iApply (brel_wand _ _ _ (λ v1 v2, B v1 v2 ∗ P)%I with "[Hf Hw HP]"); last first.
    { iIntros "!# % % [HB HP]". iApply ("Hc" with "HB HP"). }
    iApply brel_introduction_mono; first iApply "Hρ".
    iApply (brel_mono_on_prop _ _ _ P with "[] HP").
    { iApply (row_type_sub (ρ := (¡ θ')%R) (τ := λ _ _, P) $! #()%V #()%V). }
    rewrite /sem_ty_arr /=. iApply ("Hf" with "Hw").
  Qed.

  Lemma eq_call_frame_aff (θ' ρ : sem_row Σ) (A B : sem_ty Σ) (P : iPropD Σ)
      (fl fr wl wr : val) Kl Kr R :
    (∀ l1s, NeutralEctx l1s Kl) → (∀ l2s, NeutralEctx l2s Kr) →
    ⊢ ⎡(¡ θ')%R ≤ᵣ ρ⎤ -∗ ⟪ A -{ ¡ θ' }-∘ B ⟫ fl fr -∗ ⟪ A ⟫ wl wr -∗ P -∗
      □ (∀ vl vr, ⟪ B ⟫ vl vr -∗ P -∗
           EQ fill Kl (Val vl) ≈ fill Kr (Val vr) <|iLblSig_to_iLblThy ρ|> {{ R }}) -∗
      EQ fill Kl (fl wl) ≈ fill Kr (fr wr) <|iLblSig_to_iLblThy ρ|> {{ R }}.
  Proof.
    intros ??. iStartProof (iProp _). iIntros (d) "#Hρ Hf Hw HP #Hc".
    iEval (rewrite eq_lift_at) in "Hf". iEval (rewrite eq_lift_at) in "Hw".
    destruct d; rewrite eq_rel_at /pick /=.
    - iApply (brel_call_frame_aff θ' ρ A B (P Fwd) with "Hρ Hf Hw HP").
      iIntros "!>" (v1 v2) "HB HP". iApply (eq_rel_at_elim_const Fwd).
      iApply ("Hc" $! v1 v2 with "[HB] HP"). by rewrite eq_lift_at.
    - iApply (brel_call_frame_aff θ' ρ A B (P Bwd) with "Hρ Hf Hw HP").
      iIntros "!>" (v1 v2) "HB HP". iApply (eq_rel_at_elim_const Bwd).
      iApply ("Hc" $! v2 v1 with "[HB] HP"). by rewrite eq_lift_at.
  Qed.

End eq_modules.

Section eq_modules_group.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  #[local] Open Scope bi_scope.

  (* A message box: empty, or holding the same group element. *)
  Definition box_rel (m m' : loc) : iPropD Σ :=
    (m ↦ₗ NONEV ∗ m' ↦ᵣ NONEV) ∨ ∃ x : vgG, m ↦ₗ SOMEV (vgval x) ∗ m' ↦ᵣ SOMEV (vgval x).

  Lemma eq_none : ⊢ ⟪ Option 𝔾 ⟫ NONEV NONEV.
  Proof. iApply eq_lift_option. by iLeft. Qed.

  Lemma eq_some (x y : vgG) : x = y → ⊢ ⟪ Option 𝔾 ⟫ (SOMEV (vgval x)) (SOMEV (vgval y)).
  Proof.
    intros ->. iApply eq_lift_option. iRight. iExists _, _. iSplit; first done.
    iApply eq_lift_group. by iExists y.
  Qed.

  Lemma eq_group_val (x y : vgG) : x = y → ⊢ ⟪ 𝔾 ⟫ (vgval x) (vgval y).
  Proof. intros ->. iApply eq_lift_group. by iExists y. Qed.

End eq_modules_group.

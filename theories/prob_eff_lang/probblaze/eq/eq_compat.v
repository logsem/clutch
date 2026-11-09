(* Rules of the logic for equivalences that come from the semantic typing
   rules ([compatibility]). *)

From iris.bi Require Import monpred.
From iris.proofmode Require Import base proofmode classes monpred.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode tactics notation.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_row sem_judgement compatibility sem_sig.
From clutch.prob_eff_lang.probblaze.eq Require Import eq_logic eq_handlers.

Section eq_compat.
  Context `{!probblazeRGS Σ}.
  #[local] Open Scope bi_scope.

  (* Calling a function of an effectful (multi-shot) arrow type in contexts
     [K1] and [K2], keeping a frame [P] across the call.  The effects [θ']
     of the call must be handled outside, as recorded by [(¡ θ') ≤ᵣ ρ]. *)
  Lemma brel_call_frame (θ' ρ : sem_row Σ) (A B : sem_ty Σ) (P : iProp Σ) (f1 f2 w1 w2 : val) K1 K2 R :
    (∀ l1s, NeutralEctx l1s K1) → (∀ l2s, NeutralEctx l2s K2) →
    ⊢ (¡ θ')%R ≤ᵣ ρ -∗ (A -{ θ' }-> B)%T f1 f2 -∗ A w1 w2 -∗ P -∗
      □ (∀ v1 v2, B v1 v2 -∗ P -∗ BREL fill K1 (Val v1) ≤ fill K2 (Val v2) <|iLblSig_to_iLblThy ρ|> {{ R }}) -∗
      BREL fill K1 (f1 w1) ≤ fill K2 (f2 w2) <|iLblSig_to_iLblThy ρ|> {{ R }}.
  Proof.
    iIntros (HK1 HK2) "#Hρ #Hf Hw HP #Hc".
    iApply (brel_bind K1 K2); [by iApply traversable_to_iThy|iApply to_iThy_le_refl|].
    iApply (brel_wand _ _ _ (λ v1 v2, B v1 v2 ∗ P)%I with "[Hw HP]"); last first.
    { iIntros "!# % % [HB HP]". iApply ("Hc" with "HB HP"). }
    iApply brel_introduction_mono; first iApply "Hρ".
    iApply (brel_mono_on_prop _ _ _ P with "[] HP").
    { iApply (row_type_sub (ρ := (¡ θ')%R) (τ := λ _ _, P) $! #()%V #()%V). }
    iDestruct (ty_le_uarr_mfbang A B θ' $! f1 f2 with "Hf") as "Hf'".
    rewrite /sem_ty_arr /=. iApply ("Hf'" with "Hw").
  Qed.

  Lemma eq_call_frame (θ' ρ : sem_row Σ) (A B : sem_ty Σ) (P : iPropD Σ) (fl fr wl wr : val) Kl Kr R :
    (∀ l1s, NeutralEctx l1s Kl) → (∀ l2s, NeutralEctx l2s Kr) →
    ⊢ ⎡(¡ θ')%R ≤ᵣ ρ⎤ -∗ ⟪ A -{ θ' }-> B ⟫ fl fr -∗ ⟪ A ⟫ wl wr -∗ P -∗
      □ (∀ vl vr, ⟪ B ⟫ vl vr -∗ P -∗
           EQ fill Kl (Val vl) ≈ fill Kr (Val vr) <|iLblSig_to_iLblThy ρ|> {{ R }}) -∗
      EQ fill Kl (fl wl) ≈ fill Kr (fr wr) <|iLblSig_to_iLblThy ρ|> {{ R }}.
  Proof.
    intros ??. iStartProof (iProp _). iIntros (d) "#Hρ Hf Hw HP #Hc".
    iEval (rewrite eq_lift_at) in "Hf". iEval (rewrite eq_lift_at) in "Hw".
    destruct d; rewrite eq_rel_at /pick /=.
    - iApply (brel_call_frame θ' ρ A B (P Fwd) with "Hρ Hf Hw HP").
      iIntros "!>" (v1 v2) "HB HP". iApply (eq_rel_at_elim_const Fwd).
      iApply ("Hc" $! v1 v2 with "[HB] HP"). by rewrite eq_lift_at.
    - iApply (brel_call_frame θ' ρ A B (P Bwd) with "Hρ Hf Hw HP").
      iIntros "!>" (v1 v2) "HB HP". iApply (eq_rel_at_elim_const Bwd).
      iApply ("Hc" $! v2 v1 with "[HB] HP"). by rewrite eq_lift_at.
  Qed.

  (* Calling an operation of the environment, typed at row [θ], from below a
     theory [X] with labels [l1s], [l2s] (e.g. inside a handler). *)
  Lemma brel_env_call l1s l2s X k1 k2 (f1 f2 v1 v2 : val) (τ κ : sem_ty Σ) (θ L : sem_row Σ) R :
    ectx_labels k1 ⊆ l1s →
    ectx_labels k2 ⊆ l2s →
    ⊢ (τ -{ θ }-> κ)%T f1 f2 -∗
    τ v1 v2 -∗
    (∀ w1 w2, κ w1 w2 -∗
       BREL fill k1 w1 ≤ fill k2 w2
         <|(l1s, l2s, X) :: iLblSig_to_iLblThy (sem_row_union (¡ θ)%R L)|> {{R}}) -∗
    BREL fill k1 (f1 v1) ≤ fill k2 (f2 v2)
      <|(l1s, l2s, X) :: iLblSig_to_iLblThy (sem_row_union (¡ θ)%R L)|> {{R}}.
  Proof.
    iIntros (Hk1 Hk2) "Hf Hv Hk".
    iApply (brel_bind'' _ _ (iLblSig_to_iLblThy (¡ θ)%R) [(l1s, l2s, X)]).
    { rewrite labels_l_cons /=. set_solver. }
    { rewrite labels_r_cons /=. set_solver. }
    { iApply to_iThy_le_intro'. unfold sem_row_union.
      repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app).
      solve_submseteq. }
    rewrite iThyIfMono_iLblSig_to_iThyIfMono.
    iApply (brel_mono OS with "[] [Hf Hv] Hk"); first iApply to_iThy_le_refl.
    rewrite /sem_ty_mbang /sem_ty_arr /=. by iApply "Hf".
  Qed.

  Lemma eq_env_call lls rls T kl kr (fl fr vl vr : val) (τ κ : sem_ty Σ) (θ L : sem_row Σ) R :
    ectx_labels kl ⊆ lls → ectx_labels kr ⊆ rls →
    ⊢ ⟪ τ -{ θ }-> κ ⟫ fl fr -∗ ⟪ τ ⟫ vl vr -∗
      (∀ wl wr, ⟪ κ ⟫ wl wr -∗
         EQ fill kl wl ≈ fill kr wr <|eq_thy_cons lls rls T (iLblSig_to_iLblThy (sem_row_union (¡ θ)%R L))|> {{ R }}) -∗
      EQ fill kl (fl vl) ≈ fill kr (fr vr) <|eq_thy_cons lls rls T (iLblSig_to_iLblThy (sem_row_union (¡ θ)%R L))|> {{ R }}.
  Proof.
    intros Hkl Hkr. iStartProof (iProp _). iIntros (d) "Hf Hv Hk".
    iEval (rewrite eq_lift_at) in "Hf". iEval (rewrite eq_lift_at) in "Hv".
    rewrite eq_rel_at. destruct d; rewrite /pick /=.
    - iApply (brel_env_call with "Hf Hv"); [done|done|]. iIntros (w1 w2) "Hw".
      iApply (eq_rel_at_elim Fwd _ _ _ (eq_thy_cons lls rls T (iLblSig_to_iLblThy (sem_row_union (¡ θ)%R L)))). iApply ("Hk" $! w1 w2 with "[Hw]").
      by rewrite eq_lift_at.
    - iApply (brel_env_call with "Hf Hv"); [done|done|]. iIntros (w1 w2) "Hw".
      iApply (eq_rel_at_elim Bwd _ _ _ (eq_thy_cons lls rls T (iLblSig_to_iLblThy (sem_row_union (¡ θ)%R L)))). iApply ("Hk" $! w2 w1 with "[Hw]").
      by rewrite eq_lift_at.
  Qed.

  (* The general form: the theory inclusion is a premise. *)
  Lemma brel_env_call_gen k1 k2 (f1 f2 v1 v2 : val) (τ κ : sem_ty Σ) (θ : sem_row Σ) (M N : iLblThy Σ) R :
    ectx_labels k1 ⊆ labels_l M → ectx_labels k2 ⊆ labels_r M →
    ⊢ to_iThy_le (iLblSig_to_iLblThy (¡ θ)%R ++ M) N -∗
      (τ -{ θ }-> κ)%T f1 f2 -∗ τ v1 v2 -∗
      (∀ w1 w2, κ w1 w2 -∗ BREL fill k1 w1 ≤ fill k2 w2 <|N|> {{R}}) -∗
      BREL fill k1 (f1 v1) ≤ fill k2 (f2 v2) <|N|> {{R}}.
  Proof.
    iIntros (Hk1 Hk2) "#Hle Hf Hv Hk".
    iApply (brel_bind'' _ _ (iLblSig_to_iLblThy (¡ θ)%R) M N); [done|done|done|].
    rewrite iThyIfMono_iLblSig_to_iThyIfMono.
    iApply (brel_mono OS with "[] [Hf Hv] Hk"); first iApply to_iThy_le_refl.
    rewrite /sem_ty_mbang /sem_ty_arr /=. by iApply "Hf".
  Qed.

  Lemma eq_env_call_gen lls rls T kl kr (fl fr vl vr : val) (τ κ : sem_ty Σ) (θ : sem_row Σ) (Y : eqThy Σ) R :
    ectx_labels kl ⊆ lls → ectx_labels kr ⊆ rls →
    (∀ d, ⊢ to_iThy_le (iLblSig_to_iLblThy (¡ θ)%R ++ [((pick d lls rls, pick d rls lls), T d)]) (eq_thy_at Y d)) →
    ⊢ ⟪ τ -{ θ }-> κ ⟫ fl fr -∗ ⟪ τ ⟫ vl vr -∗
      (∀ wl wr, ⟪ κ ⟫ wl wr -∗ EQ fill kl wl ≈ fill kr wr <|Y|> {{ R }}) -∗
      EQ fill kl (fl vl) ≈ fill kr (fr vr) <|Y|> {{ R }}.
  Proof.
    intros Hkl Hkr HY. iStartProof (iProp _). iIntros (d) "Hf Hv Hk".
    iEval (rewrite eq_lift_at) in "Hf". iEval (rewrite eq_lift_at) in "Hv".
    rewrite eq_rel_at. destruct d; rewrite /pick /=.
    - iApply (brel_env_call_gen _ _ _ _ _ _ _ _ θ [((lls, rls), T Fwd)] with "[] Hf Hv");
        [rewrite /labels_l /=; set_solver|rewrite /labels_r /=; set_solver|iApply (HY Fwd)|].
      iIntros (w1 w2) "Hw". iApply (eq_rel_at_elim Fwd). iApply ("Hk" $! w1 w2 with "[Hw]"). by rewrite eq_lift_at.
    - iApply (brel_env_call_gen _ _ _ _ _ _ _ _ θ [((rls, lls), T Bwd)] with "[] Hf Hv");
        [rewrite /labels_l /=; set_solver|rewrite /labels_r /=; set_solver|iApply (HY Bwd)|].
      iIntros (w1 w2) "Hw". iApply (eq_rel_at_elim Bwd). iApply ("Hk" $! w2 w1 with "[Hw]"). by rewrite eq_lift_at.
  Qed.

End eq_compat.

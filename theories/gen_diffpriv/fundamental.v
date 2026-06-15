(** Compatibility lemmas + fundamental theorem (generic DP, [gen_prob_lang]).

    Ported from [diffpriv/fundamental].  The generalized type system
    ([gen_prob_lang/typing/types]) has NO sampling typing rule (no [TAllocTape]
    / [TRand] / [TRandU]) and the contextual ctx items drop [CTX_AllocTape] /
    [CTX_Rand*], so the sampling compatibility lemmas
    ([bin_log_related_alloctape] / [_rand_tape] / [_rand_unit]) and their cases
    in [fundamental] / [bin_log_related_under_typed_ctx] are omitted. *)
From iris.base_logic Require Export invariants.
From iris.algebra Require Import list.
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext.
From clutch.prob Require Import distribution couplings couplings_app couplings_dp.
From clutch.gen_diffpriv Require Import primitive_laws model compatibility app_rel_rules rel_tactics.
From clutch.gen_prob_lang.typing Require Import types.
From clutch.gen_diffpriv Require Import interp coupling_rules proofmode.
From clutch.gen_prob_lang.spec Require Import spec_rules.
From clutch.gen_prob_lang Require Import metatheory notation lang.

Section fundamental.
  (* [Sg] implicit (via the [diffprivRGS Sg Σ] generalization), as in [model]:
     keeps it an implicit leading argument so the positional [bin_log_related_*]
     applications below line up. *)
  Context `{!diffprivRGS Sg Σ}.
  Canonical Structure gen_ectxi_lang_fund := gen_ectxi_lang Sg.
  Canonical Structure gen_ectx_lang_fund := gen_ectx_lang Sg.
  Canonical Structure gen_lang_fund := gen_lang Sg.
  Canonical Structure gen_markov_fund := lang_markov (gen_lang Sg).
  Implicit Types Δ : listO (lrelC Σ).
  Hint Resolve to_of_val : core.

  (* [typed]/[val_typed] take the signature [Sg] explicitly (it is a section
     variable in [typing/types]); re-bind the [⊢ₜ]/[⊢ᵥ] notations over the
     ambient [Sg] here. *)
  Local Notation "Γ ⊢ₜ e : τ" := (typed Sg Γ e τ)
    (at level 74, e, τ at next level).
  Local Notation "⊢ᵥ v : τ" := (val_typed Sg v τ)
    (at level 20, v, τ at next level).
  (* Pinned [fill] + spec-step instance, for the sampling compatibility lemmas
     ([refines_alloc_sample_tape_*] step the spec tape via [step_alloc_sample_tape]). *)
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Sg)).
  #[local] Existing Instance spec_rules_spec_updateGS.
  #[local] Instance spec_updateGS_fund : spec_updateGS gen_markov_fund Σ :=
    spec_rules_spec_updateGS Sg.

  Local Ltac intro_clause := progress (iIntros (vs) "#Hvs /=").
  Local Ltac intro_clause' := progress (iIntros (?) "? /=").
  Local Ltac value_case := try intro_clause';
    try rel_pure_l; try rel_pure_r; rel_values.

  Local Tactic Notation "rel_bind_ap" uconstr(e1) uconstr(e2) constr(IH) ident(v) ident(w) constr(Hv):=
    rel_bind_l (subst_map _ e1);
    rel_bind_r (subst_map _ e2);
    try iSpecialize (IH with "Hvs");
    iApply (refines_bind with IH);
    iIntros (v w) Hv; simpl.

  Lemma bin_log_related_var Δ Γ x τ :
    Γ !! x = Some τ →
    ⊢ 〈Δ;Γ〉 ⊨ Var x ≤log≤ Var x : τ.
  Proof.
    iIntros (Hx). iIntros (vs) "#Hvs". simpl.
    rewrite (env_ltyped2_lookup _ vs x); last first.
    { rewrite lookup_fmap Hx //. }
    rewrite !lookup_fmap.
    iDestruct "Hvs" as (v1 v2 ->) "HA". simpl.
    by iApply refines_ret.
  Qed.

  Lemma bin_log_related_pair Δ Γ e1 e2 e1' e2' (τ1 τ2 : type) :
    (〈Δ;Γ〉 ⊨ e1 ≤log≤ e1' : τ1) -∗
    (〈Δ;Γ〉 ⊨ e2 ≤log≤ e2' : τ2) -∗
    〈Δ;Γ〉 ⊨ Pair e1 e2 ≤log≤ Pair e1' e2' : TProd τ1 τ2.
  Proof.
    iIntros "IH1 IH2".
    intro_clause.
    iApply (refines_pair with "[IH1] [IH2]").
    - by iApply "IH1".
    - by iApply "IH2".
  Qed.

  Lemma bin_log_related_fst Δ Γ e e' τ1 τ2 :
    (〈Δ;Γ〉 ⊨ e ≤log≤ e' : τ1 * τ2) -∗
    〈Δ;Γ〉 ⊨ Fst e ≤log≤ Fst e' : τ1.
  Proof.
    iIntros "IH".
    intro_clause.
    rel_bind_ap e e' "IH" v w "IH".
    iDestruct "IH" as (v1 v2 w1 w2) "(% & % & IHw & IHw')". simplify_eq/=.
    value_case.
  Qed.

  Lemma bin_log_related_snd Δ Γ e e' τ1 τ2 :
    (〈Δ;Γ〉 ⊨ e ≤log≤ e' : τ1 * τ2) -∗
    〈Δ;Γ〉 ⊨ Snd e ≤log≤ Snd e' : τ2.
  Proof.
    iIntros "IH".
    intro_clause.
    rel_bind_ap e e' "IH" v w "IH".
    iDestruct "IH" as (v1 v2 w1 w2) "(% & % & IHw & IHw')". simplify_eq/=.
    value_case.
  Qed.

  Lemma bin_log_related_app Δ Γ e1 e2 e1' e2' τ1 τ2 :
    (〈Δ;Γ〉 ⊨ e1 ≤log≤ e1' : τ1 → τ2) -∗
    (〈Δ;Γ〉 ⊨ e2 ≤log≤ e2' : τ1) -∗
    〈Δ;Γ〉 ⊨ App e1 e2 ≤log≤ App e1' e2' :  τ2.
  Proof.
    iIntros "IH1 IH2".
    intro_clause.
    iApply (refines_app with "[IH1] [IH2]").
    - by iApply "IH1".
    - by iApply "IH2".
  Qed.

  Lemma bin_log_related_rec Δ (Γ : stringmap type) (f x : binder) (e e' : expr) τ1 τ2 :
    □ (〈Δ;<[f:=TArrow τ1 τ2]>(<[x:=τ1]>Γ)〉 ⊨ e ≤log≤ e' : τ2) -∗
    〈Δ;Γ〉 ⊨ Rec f x e ≤log≤ Rec f x e' : τ1 → τ2.
  Proof.
    iIntros "#Ht".
    intro_clause.
    rel_pure_l. rel_pure_r.
    iApply refines_arrow_val.
    iModIntro. iLöb as "IH". iIntros (v1 v2) "#Hτ1".
    rel_pure_l. rel_pure_r.

    set (r := (RecV f x (subst_map (binder_delete x (binder_delete f (fst <$> vs))) e), RecV f x (subst_map (binder_delete x (binder_delete f (snd <$> vs))) e'))).
    set (vvs' := binder_insert f r (binder_insert x (v1,v2) vs)).
    iSpecialize ("Ht" $! vvs' with "[#]").
    { rewrite !binder_insert_fmap.
      iApply (env_ltyped2_insert with "[IH]").
      - iApply "IH".
      - iApply (env_ltyped2_insert with "Hτ1").
        by iFrame. }

    unfold vvs'.
    destruct x as [|x], f as [|f];
      rewrite /= ?fmap_insert ?subst_map_insert //.
      try by iApply "H".
    destruct (decide (x = f)) as [->|]; iSimpl in "Ht".
    - rewrite !delete_insert_eq !subst_subst !delete_delete_eq.
      by iApply "Ht".
    - rewrite !delete_insert_ne // subst_map_insert.
      rewrite !(subst_subst_ne _ x f) // subst_map_insert.
      by iApply "Ht".
  Qed.

  Lemma bin_log_related_tlam Δ Γ (e e' : expr) τ :
    (∀ (A : lrel Σ),
      □ (〈(A::Δ);⤉Γ〉 ⊨ e ≤log≤ e' : τ)) -∗
    〈Δ;Γ〉 ⊨ (Λ: e) ≤log≤ (Λ: e') : ∀: τ.
  Proof.
    iIntros "#H".
    intro_clause. rel_pure_l. rel_pure_r.
    iApply refines_forall.
    iModIntro. iIntros (A).
    iDestruct ("H" $! A) as "#H1".
    iApply "H1".
    by rewrite (interp_ren A Δ Γ).
  Qed.

  Lemma bin_log_related_tapp' Δ Γ e e' τ τ' :
    (〈Δ;Γ〉 ⊨ e ≤log≤ e' : ∀: τ) -∗
    〈Δ;Γ〉 ⊨ (TApp e) ≤log≤ (TApp e') : τ.[τ'/].
  Proof.
    iIntros "IH".
    intro_clause.
    rel_bind_ap e e' "IH" v v' "IH".
    iSpecialize ("IH" $! (interp τ' Δ)).
    iDestruct "IH" as "#IH".
    iSpecialize ("IH" $! #() #() with "[//]").
    by rewrite -interp_subst.
  Qed.

  Lemma bin_log_related_tapp (τi : lrel Σ) Δ Γ e e' τ :
    (〈Δ;Γ〉 ⊨ e ≤log≤ e' : ∀: τ) -∗
    〈τi::Δ;⤉Γ〉 ⊨ (TApp e) ≤log≤ (TApp e') : τ.
  Proof.
    iIntros "IH". intro_clause.
    iApply (bin_log_related_app _ _ e #() e' #() () τ with "[IH] [] Hvs").
    - iClear (vs) "Hvs". intro_clause.
      rewrite interp_ren.
      iSpecialize ("IH" with "Hvs").
      iApply (refines_wand with "IH").
      eauto with iFrame.
    - value_case.
  Qed.

  Lemma bin_log_related_seq R Δ Γ e1 e2 e1' e2' τ1 τ2 :
    (〈(R::Δ);⤉Γ〉 ⊨ e1 ≤log≤ e1' : τ1) -∗
    (〈Δ;Γ〉 ⊨ e2 ≤log≤ e2' : τ2) -∗
    〈Δ;Γ〉 ⊨ (e1;; e2) ≤log≤ (e1';; e2') : τ2.
  Proof.
    iIntros "He1 He2".
    intro_clause.
    iApply (refines_seq (interp τ1 (R::Δ)) with "[He1]").
    - iApply ("He1" with "[Hvs]").
      by rewrite interp_ren.
    - by iApply "He2".
  Qed.

  Lemma bin_log_related_seq' Δ Γ e1 e2 e1' e2' τ1 τ2 :
    (〈Δ;Γ〉 ⊨ e1 ≤log≤ e1' : τ1) -∗
    (〈Δ;Γ〉 ⊨ e2 ≤log≤ e2' : τ2) -∗
    〈Δ;Γ〉 ⊨ (e1;; e2) ≤log≤ (e1';; e2') : τ2.
  Proof.
    iIntros "He1 He2".
    iApply (bin_log_related_seq lrel_true _ _ _ _ _ _ τ1.[ren (+1)] with "[He1] He2").
    intro_clause.
    rewrite interp_ren -(interp_ren_up [] Δ τ1).
    by iApply "He1".
  Qed.

  Lemma bin_log_related_injl Δ Γ e e' τ1 τ2 :
    (〈Δ;Γ〉 ⊨ e ≤log≤ e' : τ1) -∗
    〈Δ;Γ〉 ⊨ InjL e ≤log≤ InjL e' : τ1 + τ2.
  Proof.
    iIntros "IH".
    intro_clause.
    iApply refines_injl.
    by iApply "IH".
  Qed.

  Lemma bin_log_related_injr Δ Γ e e' τ1 τ2 :
    (〈Δ;Γ〉 ⊨ e ≤log≤ e' : τ2) -∗
    〈Δ;Γ〉 ⊨ InjR e ≤log≤ InjR e' : τ1 + τ2.
  Proof.
    iIntros "IH".
    intro_clause.
    iApply refines_injr. by iApply "IH".
  Qed.

  Lemma bin_log_related_case Δ Γ e0 e1 e2 e0' e1' e2' τ1 τ2 τ3 :
    (〈Δ;Γ〉 ⊨ e0 ≤log≤ e0' : τ1 + τ2) -∗
    (〈Δ;Γ〉 ⊨ e1 ≤log≤ e1' : τ1 → τ3) -∗
    (〈Δ;Γ〉 ⊨ e2 ≤log≤ e2' : τ2 → τ3) -∗
    〈Δ;Γ〉 ⊨ Case e0 e1 e2 ≤log≤ Case e0' e1' e2' : τ3.
  Proof.
    iIntros "IH1 IH2 IH3".
    intro_clause.
    rel_bind_ap e0 e0' "IH1" v0 v0' "IH1".
    iDestruct "IH1" as (w w') "[(% & % & #Hw)|(% & % & #Hw)]"; simplify_eq/=;
      rel_case_l; rel_case_r.
    - iApply (bin_log_related_app Δ Γ _ w _ w'  with "IH2 [] Hvs").
      value_case.
    - iApply (bin_log_related_app Δ Γ _ w _ w'  with "IH3 [] Hvs").
      value_case.
  Qed.

  Lemma bin_log_related_if Δ Γ e0 e1 e2 e0' e1' e2' τ :
    (〈Δ;Γ〉 ⊨ e0 ≤log≤ e0' : TBool) -∗
    (〈Δ;Γ〉 ⊨ e1 ≤log≤ e1' : τ) -∗
    (〈Δ;Γ〉 ⊨ e2 ≤log≤ e2' : τ) -∗
    〈Δ;Γ〉 ⊨ If e0 e1 e2 ≤log≤ If e0' e1' e2' : τ.
  Proof.
    iIntros "IH1 IH2 IH3".
    intro_clause.
    rel_bind_ap e0 e0' "IH1" v0 v0' "IH1".
    iDestruct "IH1" as ([]) "[% %]"; simplify_eq/=;
      rel_if_l; rel_if_r.
    - by iApply "IH2".
    - by iApply "IH3".
  Qed.

  Lemma bin_log_related_load Δ Γ e e' τ :
    (〈Δ;Γ〉 ⊨ e ≤log≤ e' : (TRef τ)) -∗
    〈Δ;Γ〉 ⊨ Deref e ≤log≤ Deref e' : τ.
  Proof.
    iIntros "IH".
    intro_clause.
    iApply refines_load.
    by iApply "IH".
  Qed.

  Lemma bin_log_related_store Δ Γ e1 e2 e1' e2' τ :
    (〈Δ;Γ〉 ⊨ e1 ≤log≤ e1' : TRef τ) -∗
    (〈Δ;Γ〉 ⊨ e2 ≤log≤ e2' : τ) -∗
    〈Δ;Γ〉 ⊨ Store e1 e2 ≤log≤ Store e1' e2' : ().
  Proof.
    iIntros "IH1 IH2".
    intro_clause.
    iApply (refines_store with "[IH1] [IH2]").
    - by iApply "IH1".
    - by iApply "IH2".
  Qed.

  Lemma bin_log_related_alloc Δ Γ e e' τ :
    (〈Δ;Γ〉 ⊨ e ≤log≤ e' : τ) -∗
    〈Δ;Γ〉 ⊨ Alloc e ≤log≤ Alloc e' : TRef τ.
  Proof.
    iIntros "IH".
    intro_clause.
    rel_bind_ap e e' "IH" v v' "IH".
    rel_alloc_l l as "Hl".
    rel_alloc_r k as "Hk".
    iMod (inv_alloc (logN .@ (l,k)) _ (∃ w1 w2,
      l ↦ w1 ∗ k ↦ₛ w2 ∗ interp τ Δ w1 w2)%I with "[Hl Hk IH]") as "HN"; eauto.
    { iNext. iExists v, v'; simpl; iFrame. }
    rel_values. iExists l, k. eauto.
  Qed.

  Lemma bin_log_related_subsume_int_nat  Δ Γ e e' :
  (〈Δ; Γ〉 ⊨ e ≤log≤ e' : TNat) -∗
  (〈Δ; Γ〉 ⊨ e ≤log≤ e' : TInt).
  Proof.
    iIntros "IH".
    intro_clause.
    rel_bind_ap e e' "IH" v v' "#IH".
    iDestruct "IH" as (N) "(->&->)".
    value_case.
  Qed.

  Lemma bin_log_related_unboxed_eq Δ Γ e1 e2 e1' e2' τ :
    UnboxedType τ →
    (〈Δ;Γ〉 ⊨ e1 ≤log≤ e1' : τ) -∗
    (〈Δ;Γ〉 ⊨ e2 ≤log≤ e2' : τ) -∗
    〈Δ;Γ〉 ⊨ BinOp EqOp e1 e2 ≤log≤ BinOp EqOp e1' e2' : TBool.
  Proof.
    iIntros (Hτ) "IH1 IH2".
    intro_clause.
    rel_bind_ap e2 e2' "IH2" v2 v2' "#IH2".
    rel_bind_ap e1 e1' "IH1" v1 v1' "#IH1".
    iAssert (⌜val_is_unboxed v1⌝)%I as "%".
    { rewrite !unboxed_type_sound //.
      iDestruct "IH1" as "[$ _]". }
    iAssert (⌜val_is_unboxed v2'⌝)%I as "%".
    { rewrite !unboxed_type_sound //.
      iDestruct "IH2" as "[_ $]". }
    iMod (unboxed_type_eq with "IH1 IH2") as "%"; first done.
    rel_op_l. rel_op_r.
    do 2 case_bool_decide; first [by rel_values | naive_solver].
  Qed.

  Lemma bin_log_related_int_binop Δ Γ op e1 e2 e1' e2' τ :
    binop_int_res_type op = Some τ →
    (〈Δ;Γ〉 ⊨ e1 ≤log≤ e1' : TInt) -∗
    (〈Δ;Γ〉 ⊨ e2 ≤log≤ e2' : TInt) -∗
    〈Δ;Γ〉 ⊨ BinOp op e1 e2 ≤log≤ BinOp op e1' e2' : τ.
  Proof.
    iIntros (Hopτ) "IH1 IH2".
    intro_clause.
    rel_bind_ap e2 e2' "IH2" v2 v2' "IH2".
    rel_bind_ap e1 e1' "IH1" v1 v1' "IH1".
    iDestruct "IH1" as (n) "[% %]"; simplify_eq/=.
    iDestruct "IH2" as (n') "[% %]"; simplify_eq/=.
    destruct (binop_int_typed_safe op n n' _ Hopτ) as [v' Hopv'].
    rel_op_l; eauto.
    rel_op_r; eauto.
    value_case.
    destruct op; inversion Hopv'; simplify_eq/=; try case_match; eauto.
  Qed.

  Lemma bin_log_related_bool_binop Δ Γ op e1 e2 e1' e2' τ :
    binop_bool_res_type op = Some τ →
    (〈Δ;Γ〉 ⊨ e1 ≤log≤ e1' : TBool) -∗
    (〈Δ;Γ〉 ⊨ e2 ≤log≤ e2' : TBool) -∗
    〈Δ;Γ〉 ⊨ BinOp op e1 e2 ≤log≤ BinOp op e1' e2' : τ.
  Proof.
    iIntros (Hopτ) "IH1 IH2".
    intro_clause.
    rel_bind_ap e2 e2' "IH2" v2 v2' "IH2".
    rel_bind_ap e1 e1' "IH1" v1 v1' "IH1".
    iDestruct "IH1" as (n) "[% %]"; simplify_eq/=.
    iDestruct "IH2" as (n') "[% %]"; simplify_eq/=.
    destruct (binop_bool_typed_safe op n n' _ Hopτ) as [v' Hopv'].
    rel_op_l; eauto.
    rel_op_r; eauto.
    value_case.
    destruct op; inversion Hopv'; simplify_eq/=; eauto.
  Qed.

  Lemma bin_log_related_int_unop Δ Γ op e e' τ :
    unop_int_res_type op = Some τ →
    (〈Δ;Γ〉 ⊨ e ≤log≤ e' : TInt) -∗
    〈Δ;Γ〉 ⊨ UnOp op e ≤log≤ UnOp op e' : τ.
  Proof.
    iIntros (Hopτ) "IH".
    intro_clause.
    rel_bind_ap e e' "IH" v v' "IH".
    iDestruct "IH" as (n) "[% %]"; simplify_eq/=.
    destruct (unop_int_typed_safe op n _ Hopτ) as [v' Hopv'].
    rel_pure_l. rel_pure_r.
    value_case.
    destruct op; inversion Hopv'; simplify_eq/=; try case_match; eauto.
  Qed.

  Lemma bin_log_related_bool_unop Δ Γ op e e' τ :
    unop_bool_res_type op = Some τ →
    (〈Δ;Γ〉 ⊨ e ≤log≤ e' : TBool) -∗
    〈Δ;Γ〉 ⊨ UnOp op e ≤log≤ UnOp op e' : τ.
  Proof.
    iIntros (Hopτ) "IH".
    intro_clause.
    rel_bind_ap e e' "IH" v v' "IH".
    iDestruct "IH" as (n) "[% %]"; simplify_eq/=.
    destruct (unop_bool_typed_safe op n _ Hopτ) as [v' Hopv'].
    rel_pure_l. rel_pure_r.
    value_case.
    destruct op; inversion Hopv'; simplify_eq/=; try case_match; eauto.
  Qed.

  Lemma bin_log_related_unfold Δ Γ e e' τ :
    (〈Δ;Γ〉 ⊨ e ≤log≤ e' : μ: τ) -∗
    〈Δ;Γ〉 ⊨ rec_unfold e ≤log≤ rec_unfold e' : τ.[(TRec τ)/].
  Proof.
    iIntros "IH".
    intro_clause.
    rel_bind_ap e e' "IH" v v' "IH".
    iEval (rewrite lrel_rec_unfold /lrel_car /=) in "IH".
    change (lrel_rec _) with (interp (TRec τ) Δ).
    rel_rec_l. rel_rec_r.
    value_case. by rewrite -interp_subst.
  Qed.

  Lemma bin_log_related_fold Δ Γ e e' τ :
    (〈Δ;Γ〉 ⊨ e ≤log≤ e' : τ.[(TRec τ)/]) -∗
    〈Δ;Γ〉 ⊨ e ≤log≤ e' : μ: τ.
  Proof.
    iIntros "IH".
    intro_clause.
    rel_bind_ap e e' "IH" v v' "IH".
    value_case.
    iModIntro.
    iEval (rewrite lrel_rec_unfold /lrel_car /=).
    change (lrel_rec _) with (interp (TRec τ) Δ).
    by rewrite -interp_subst.
  Qed.

  Lemma bin_log_related_pack' Δ Γ e e' (τ τ' : type) :
    (〈Δ;Γ〉 ⊨ e ≤log≤ e' : τ.[τ'/]) -∗
    〈Δ;Γ〉 ⊨ e ≤log≤ e' : ∃: τ.
  Proof.
    iIntros "IH".
    intro_clause.
    rel_bind_ap e e' "IH" v v' "#IH".
    value_case.
    iModIntro. iExists (interp τ' Δ).
    by rewrite interp_subst.
  Qed.

  Lemma bin_log_related_pack (τi : lrel Σ) Δ Γ e e' τ :
    (〈τi::Δ;⤉Γ〉 ⊨ e ≤log≤ e' : τ) -∗
    〈Δ;Γ〉 ⊨ e ≤log≤ e' : ∃: τ.
  Proof.
    iIntros "IH".
    intro_clause.
    iSpecialize ("IH" $! vs with "[Hvs]").
    { by rewrite interp_ren. }
    rel_bind_ap e e' "IH" v v' "#IH".
    value_case.
    iModIntro. by iExists τi.
  Qed.

  Lemma bin_log_related_unpack Δ Γ x e1 e1' e2 e2' τ τ2 :
    (〈Δ;Γ〉 ⊨ e1 ≤log≤ e1' : ∃: τ) -∗
    (∀ τi : lrel Σ,
      〈τi::Δ;<[x:=τ]>(⤉Γ)〉 ⊨
        e2 ≤log≤ e2' : (Autosubst_Classes.subst (ren (+1)) τ2)) -∗
    〈Δ;Γ〉 ⊨ (unpack: x := e1 in e2) ≤log≤ (unpack: x := e1' in e2') : τ2.
  Proof.
    iIntros "IH1 IH2".
    intro_clause.
    rel_pure_l. rel_pure_r.
    rel_bind_ap e1 e1' "IH1" v v' "#IH1".
    iDestruct "IH1" as (A) "#IH".
    rel_rec_l. rel_pure_l. rel_pure_l.
    rel_rec_r. rel_pure_r. rel_pure_r.
    rel_pure_l. rel_pure_r.
    iSpecialize ("IH2" $! A (binder_insert x (v,v') vs) with "[Hvs]").
    { rewrite -(interp_ren A).
      rewrite binder_insert_fmap.
      iApply (env_ltyped2_insert with "IH Hvs"). }
    rewrite !binder_insert_fmap !subst_map_binder_insert /=.
    iApply (refines_wand with "IH2").
    iIntros (v1 v2). rewrite (interp_ren_up [] Δ τ2 A).
    asimpl. eauto.
  Qed.

  (** ** Sampling compatibility lemmas.

      These wire the per-family syntactic [SampleTyping] interface into the
      logical relation, via the bridge lemmas [eq_type_sound] / [ground_of_eqtype]
      / [interp_of_ground] (turning the syntactic side conditions into the
      semantic ones) and the coupling rules [wp_couple_sample_gen] (direct form)
      / [wp_couple_sample_tape_gen] (tape form). *)

  (** Reflexive coupling: any distribution couples with itself along equality at
      zero multiplicative and additive cost. *)
  Lemma DPcoupl_refl `{Countable A} (μ : distr A) : DPcoupl μ μ (=) 0 0.
  Proof. apply ARcoupl_to_DPcoupl, ARcoupl_eq. Qed.

  (** [sig_sample] at index [i] (with [Sg !! i = Some D]) decodes [v] to [p] and
      samples [D p], lifted through [sf_inj]. *)
  Lemma sig_sample_decode_at (D : SampleFamily) i (v : val) (p : sf_param D) :
    Sg !! i = Some D → sf_param_of_val D v = Some p →
    sig_sample Sg i v = Some (dmap (sf_inj D) (sf_sample D p)).
  Proof. intros Hi Hp. unfold sig_sample. rewrite Hi /= Hp /=. reflexivity. Qed.

  (** Spec-side / impl-side tape allocation, relationally (analogues of the heap
      [refines_alloc_r] / [refines_alloc_l]). *)
  Lemma refines_alloc_sample_tape_r E K (i : nat) (pv : val) t A :
    (∀ l : loc, l ↪ₛ (i, pv, []) -∗ REL t << fill K (of_val (LitV (LitLbl l))) @ E : A)
      ⊢ REL t << fill K (AllocSampleTape i (Val pv)) @ E : A.
  Proof.
    iIntros "Hlog". iApply refines_step_r. iIntros (k) "Hk".
    iMod (step_alloc_sample_tape with "Hk") as (l) "[Hk Hl]".
    iModIntro. iExists _. iFrame "Hk". by iApply "Hlog".
  Qed.

  Lemma refines_alloc_sample_tape_l K E (i : nat) (pv : val) t A :
    (▷ (∀ l : loc, l ↪ (i, pv, []) -∗ REL fill K (of_val (LitV (LitLbl l))) << t @ E : A))
      ⊢ REL fill K (AllocSampleTape i (Val pv)) << t @ E : A.
  Proof.
    iIntros "Hlog". iApply refines_wp_l.
    wp_apply (wp_alloc_sample_tape i pv with "[//]").
    iIntros (l) "Hl". by iApply "Hlog".
  Qed.

  (** Direct sampling [Sample i e1 e2] with [e2 : TUnit]. *)
  Lemma bin_log_related_sample Δ Γ i e1 e1' e2 e2' D τp τo :
    Sg !! i = Some D → SampleTyping D τp τo →
    bin_log_related ⊤ Δ Γ e1 e1' τp -∗
    bin_log_related ⊤ Δ Γ e2 e2' TUnit -∗
    bin_log_related ⊤ Δ Γ (Sample i e1 e2) (Sample i e1' e2') τo.
  Proof.
    iIntros (Hi Hst) "He1 He2". destruct Hst as [Heqp Hdec Hout].
    iIntros (vs) "#Hvs /=".
    iSpecialize ("He1" with "Hvs"). iSpecialize ("He2" with "Hvs").
    rel_bind_l (subst_map _ e2); rel_bind_r (subst_map _ e2').
    iApply (refines_bind with "He2"). iIntros (w2 w2') "Hw2 /=".
    iDestruct "Hw2" as %[-> ->].
    rel_bind_l (subst_map _ e1); rel_bind_r (subst_map _ e1').
    iApply (refines_bind with "He1"). iIntros (v1 v1') "#Hv1 /=".
    iDestruct (eq_type_sound _ _ _ _ Heqp with "Hv1") as %<-.
    iDestruct (ground_of_eqtype _ _ _ _ Heqp with "Hv1") as %Hgv.
    destruct (Hdec _ Hgv) as [p Hp].
    rewrite refines_eq /refines_def.
    iIntros (K ε) "Hspec Hna Herr %Hε".
    iMod ecm_zero as "Hm".
    iApply (wp_couple_sample_gen Sg i v1 v1
              (dmap (sf_inj D) (sf_sample D p)) (dmap (sf_inj D) (sf_sample D p))
              (λ w w', ∃ o : sf_out D, w = sf_inj D o ∧ w' = sf_inj D o) K ⊤ 0
              (sig_sample_decode_at D i v1 p Hi Hp) (sig_sample_decode_at D i v1 p Hi Hp) _
              with "[$Hspec $Hm]").
    { iIntros "!>" (w w') "(Hspec & %HR)". destruct HR as (o & -> & ->).
      iExists (sf_inj D o), ε. iFrame "Hspec Hna Herr".
      iSplitR; [done|]. iApply (interp_of_ground τo Δ (sf_inj D o)). apply Hout. }
    Unshelve.
    apply (DPcoupl_map (sf_inj D) (sf_inj D) (sf_sample D p) (sf_sample D p)
             (λ w w', ∃ o : sf_out D, w = sf_inj D o ∧ w' = sf_inj D o) 0 0); [lra|lra|].
    eapply (DPcoupl_mono (sf_sample D p) (sf_sample D p) (sf_sample D p) (sf_sample D p)
              (=) (λ a a', ∃ o : sf_out D, sf_inj D a = sf_inj D o ∧ sf_inj D a' = sf_inj D o)
              0 0 0 0);
      [ intros; reflexivity | intros; reflexivity
      | intros a a' ->; by exists a' | lra | lra | apply DPcoupl_refl ].
  Qed.

  (** Tape-based sampling [Sample i e1 e2] with [e2 : TTape].  The tape is kept
      empty by [lrel_tape], so the read collapses to a fresh draw (handled by
      [wp_couple_sample_tape_gen]); the tape is returned unchanged. *)
  Lemma bin_log_related_sample_tape Δ Γ i e1 e1' e2 e2' D τp τo :
    Sg !! i = Some D → SampleTyping D τp τo →
    bin_log_related ⊤ Δ Γ e1 e1' τp -∗
    bin_log_related ⊤ Δ Γ e2 e2' TTape -∗
    bin_log_related ⊤ Δ Γ (Sample i e1 e2) (Sample i e1' e2') τo.
  Proof.
    iIntros (Hi Hst) "He1 He2". destruct Hst as [Heqp Hdec Hout].
    iIntros (vs) "#Hvs /=".
    iSpecialize ("He1" with "Hvs"). iSpecialize ("He2" with "Hvs").
    rel_bind_l (subst_map _ e2); rel_bind_r (subst_map _ e2').
    iApply (refines_bind with "He2"). iIntros (w2 w2') "Hw2 /=".
    iDestruct "Hw2" as (α α' j pv0 -> ->) "#Hinv".
    rel_bind_l (subst_map _ e1); rel_bind_r (subst_map _ e1').
    iApply (refines_bind with "He1"). iIntros (v1 v1') "#Hv1 /=".
    iDestruct (eq_type_sound _ _ _ _ Heqp with "Hv1") as %<-.
    iDestruct (ground_of_eqtype _ _ _ _ Heqp with "Hv1") as %Hgv.
    destruct (Hdec _ Hgv) as [p Hp].
    iApply (refines_atomic_l _ _ _ []); simpl.
    iIntros (K') "Hr".
    iInv (logN.@ (α, α')) as ">[Hα Hα']" "Hclose".
    iModIntro. iMod ecm_zero as "Hm".
    iApply (wp_couple_sample_tape_gen Sg i v1 v1
              (dmap (sf_inj D) (sf_sample D p)) (dmap (sf_inj D) (sf_sample D p))
              (λ w w', ∃ o : sf_out D, w = sf_inj D o ∧ w' = sf_inj D o)
              α α' j pv0 j pv0 K' _ 0
              (sig_sample_decode_at D i v1 p Hi Hp) (sig_sample_decode_at D i v1 p Hi Hp) _
              with "[$Hr $Hα $Hα' $Hm]").
    iIntros "!>" (w w') "(Hr & Hα & Hα' & %HR)". destruct HR as (o & -> & ->).
    iMod ("Hclose" with "[$Hα $Hα']") as "_". iModIntro.
    iExists (Val (sf_inj D o)). iFrame "Hr".
    rel_values. iApply (interp_of_ground τo Δ (sf_inj D o)). apply Hout.
    Unshelve.
    apply (DPcoupl_map (sf_inj D) (sf_inj D) (sf_sample D p) (sf_sample D p)
             (λ w w', ∃ o : sf_out D, w = sf_inj D o ∧ w' = sf_inj D o) 0 0); [lra|lra|].
    eapply (DPcoupl_mono (sf_sample D p) (sf_sample D p) (sf_sample D p) (sf_sample D p)
              (=) (λ a a', ∃ o : sf_out D, sf_inj D a = sf_inj D o ∧ sf_inj D a' = sf_inj D o)
              0 0 0 0);
      [ intros; reflexivity | intros; reflexivity
      | intros a a' ->; by exists a' | lra | lra | apply DPcoupl_refl ].
  Qed.

  (** Allocating a sample tape. *)
  Lemma bin_log_related_alloc_sample_tape Δ Γ i e1 e1' D τp τo :
    Sg !! i = Some D → SampleTyping D τp τo →
    bin_log_related ⊤ Δ Γ e1 e1' τp -∗
    bin_log_related ⊤ Δ Γ (AllocSampleTape i e1) (AllocSampleTape i e1') TTape.
  Proof.
    iIntros (Hi Hst) "He1". destruct Hst as [Heqp Hdec Hout].
    iIntros (vs) "#Hvs /=".
    iSpecialize ("He1" with "Hvs").
    rel_bind_l (subst_map _ e1); rel_bind_r (subst_map _ e1').
    iApply (refines_bind with "He1"). iIntros (v1 v1') "#Hv1 /=".
    iDestruct (eq_type_sound _ _ _ _ Heqp with "Hv1") as %<-.
    iApply (refines_alloc_sample_tape_r ⊤ [] i v1). iIntros (l') "Hl'".
    iApply (refines_alloc_sample_tape_l [] ⊤ i v1). iModIntro. iIntros (l) "Hl".
    iMod (inv_alloc (logN .@ (l,l')) _ (l ↪ (i, v1, []) ∗ l' ↪ₛ (i, v1, []))%I
            with "[$Hl $Hl']") as "#Hinv".
    rel_values. iExists l, l', i, v1. eauto.
  Qed.

  Theorem fundamental Δ Γ e τ :
    Γ ⊢ₜ e : τ → ⊢ 〈Δ;Γ〉 ⊨ e ≤log≤ e : τ
  with fundamental_val Δ v τ :
    ⊢ᵥ v : τ → ⊢ interp τ Δ v v.
  Proof.
    - intros Ht. destruct Ht.
      + by iApply bin_log_related_var.
      + iIntros (γ) "#H". simpl. rel_values.
        iModIntro. by iApply fundamental_val.
      + iApply bin_log_related_int_binop; first done;
          by iApply fundamental.
      + iApply bin_log_related_bool_binop; first done;
          by iApply fundamental.
      + iApply bin_log_related_int_unop; first done.
        by iApply fundamental.
      + iApply bin_log_related_bool_unop; first done.
        by iApply fundamental.
      + iApply bin_log_related_unboxed_eq; try done;
          by iApply fundamental.
      + iApply bin_log_related_pair;
          by iApply fundamental.
      + iApply bin_log_related_fst;
          by iApply fundamental.
      + iApply bin_log_related_snd;
          by iApply fundamental.
      + iApply bin_log_related_injl;
          by iApply fundamental.
      + iApply bin_log_related_injr;
          by iApply fundamental.
      + iApply bin_log_related_case;
          by iApply fundamental.
      + iApply bin_log_related_if;
          by iApply fundamental.
      + iApply bin_log_related_rec.
        iModIntro. by iApply fundamental.
      + iApply bin_log_related_app;
          by iApply fundamental.
      + iApply bin_log_related_tlam.
        iIntros (A). iModIntro. by iApply fundamental.
      + iApply bin_log_related_tapp'; by iApply fundamental.
      + iApply bin_log_related_fold; by iApply fundamental.
      + iApply bin_log_related_unfold; by iApply fundamental.
      + iApply bin_log_related_pack'; by iApply fundamental.
      + iApply bin_log_related_unpack; try by iApply fundamental.
        iIntros (A). by iApply fundamental.
      + iApply bin_log_related_alloc; by iApply fundamental.
      + iApply bin_log_related_load; by iApply fundamental.
      + iApply bin_log_related_store; by iApply fundamental.
      + iApply bin_log_related_subsume_int_nat ; by iApply fundamental.
      + iApply bin_log_related_sample;
          first [ eassumption | by iApply fundamental ].
      + iApply bin_log_related_sample_tape;
          first [ eassumption | by iApply fundamental ].
      + iApply bin_log_related_alloc_sample_tape;
          first [ eassumption | by iApply fundamental ].
    - intros Hv. destruct Hv; simpl.
      + iSplit; eauto.
      + iExists _; iSplit; eauto.
      + iExists _; iSplit; eauto.
      + iExists _; iSplit; eauto.
      + iExists _,_,_,_.
        repeat iSplit; eauto; by iApply fundamental_val.
      + iExists _,_. iLeft.
        repeat iSplit; eauto; by iApply fundamental_val.
      + iExists _,_. iRight.
        repeat iSplit; eauto; by iApply fundamental_val.
      + iLöb as "IH". iModIntro.
        iIntros (v1 v2) "#Hv".
        pose (Γ := (<[f:=(τ1 → τ2)%ty]> (<[x:=τ1]> ∅)):stringmap type).
        pose (γ := (binder_insert f ((rec: f x := e)%V,(rec: f x := e)%V)
                     (binder_insert x (v1, v2) ∅)):stringmap (val*val)).
        rel_pure_l. rel_pure_r.
        iPoseProof (fundamental Δ Γ e τ2 $! γ with "[]") as "H"; eauto.
        { rewrite /γ /Γ. rewrite !binder_insert_fmap fmap_empty.
          iApply (env_ltyped2_insert with "IH").
          iApply (env_ltyped2_insert with "Hv").
          iApply env_ltyped2_empty. }
        rewrite /γ /=. rewrite !binder_insert_fmap !fmap_empty /=.
        by rewrite !subst_map_binder_insert_2_empty.
      + iIntros (A). iModIntro. iIntros (v1 v2) "_".
        rel_pures_l. rel_pures_r.
        iPoseProof (fundamental (A::Δ) ∅ e τ $! ∅ with "[]") as "H"; eauto.
        { rewrite fmap_empty. iApply env_ltyped2_empty. }
        by rewrite !fmap_empty subst_map_empty.
  Qed.

  Theorem refines_typed τ Δ e :
    ∅ ⊢ₜ e : τ →
    ⊢ REL e << e : interp τ Δ.
  Proof.
    move=> /fundamental Hty.
    iPoseProof (Hty Δ with "[]") as "H".
    { rewrite fmap_empty. iApply env_ltyped2_empty. }
    by rewrite !fmap_empty !subst_map_empty.
  Qed.

End fundamental.


Section bin_log_related_under_typed_ctx.
  Context `{!diffprivRGS Sg Σ}.
  Canonical Structure gen_ectxi_lang_fundctx := gen_ectxi_lang Sg.
  Canonical Structure gen_ectx_lang_fundctx := gen_ectx_lang Sg.
  Canonical Structure gen_lang_fundctx := gen_lang Sg.
  Canonical Structure gen_markov_fundctx := lang_markov (gen_lang Sg).

  (* Precongruence *)
  Lemma bin_log_related_under_typed_ctx Γ e e' τ Γ' τ' K :
    (typed_ctx Sg K Γ τ Γ' τ') →
    (□ ∀ Δ, (〈Δ;Γ〉 ⊨ e ≤log≤ e' : τ)) -∗
      (∀ Δ, 〈Δ;Γ'〉 ⊨ fill_ctx K e ≤log≤ fill_ctx K e' : τ')%I.
  Proof.
    revert Γ τ Γ' τ' e e'.
    induction K as [|k K]=> Γ τ Γ' τ' e e'; simpl.
    - inversion_clear 1; trivial. iIntros "#H".
      iIntros (Δ). by iApply "H".
    - inversion_clear 1 as [|? ? ? ? ? ? ? ? Hx1 Hx2].
      specialize (IHK _ _ _ _ e e' Hx2).
      inversion Hx1; subst; simpl; iIntros "#Hrel";
        iIntros (Δ).
      + iApply (bin_log_related_rec with "[-]"); auto.
        iModIntro. iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_app with "[]").
        { iApply (IHK with "[Hrel]"); auto. }
        by iApply fundamental.
      + iApply (bin_log_related_app _ _ _ _ _ _ τ2 with "[]").
        { by iApply fundamental. }
        iApply (IHK with "[Hrel]"); auto.
      + iApply bin_log_related_int_unop; eauto.
        by iApply (IHK with "Hrel").
      + iApply bin_log_related_bool_unop; eauto.
        by iApply (IHK with "Hrel").
      + iApply bin_log_related_int_binop;
          try (by iApply fundamental); eauto.
        by iApply (IHK with "Hrel").
      + iApply bin_log_related_int_binop;
          try (by iApply fundamental); eauto.
        by iApply (IHK with "Hrel"); auto.
      + iApply bin_log_related_bool_binop;
          try (by iApply fundamental); eauto.
        by iApply (IHK with "Hrel").
      + iApply bin_log_related_bool_binop;
          try (by iApply fundamental); eauto.
        by iApply (IHK with "Hrel").
      + iApply bin_log_related_unboxed_eq; try (eassumption || by iApply fundamental).
        by iApply (IHK with "Hrel").
      + iApply bin_log_related_unboxed_eq; try (eassumption || by iApply fundamental).
        by iApply (IHK with "Hrel").
      + iApply (bin_log_related_if with "[] []");
          try by iApply fundamental.
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_if with "[] []");
          try by iApply fundamental.
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_if with "[] []");
          try by iApply fundamental.
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_pair with "[]").
        { iApply (IHK with "[Hrel]"); auto. }
        by iApply fundamental.
      + iApply (bin_log_related_pair with "[]").
        { by iApply fundamental. }
        iApply (IHK with "[Hrel]"); auto.
      + iApply bin_log_related_fst.
        iApply (IHK with "[Hrel]"); auto.
      + iApply bin_log_related_snd.
        iApply (IHK with "[Hrel]"); auto.
      + iApply bin_log_related_injl.
        iApply (IHK with "[Hrel]"); auto.
      + iApply bin_log_related_injr.
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_case with "[] []").
        { iApply (IHK with "[Hrel]"); auto. }
        { by iApply fundamental. }
        by iApply fundamental.
      + iApply (bin_log_related_case with "[] []").
        { by iApply fundamental. }
        { iApply (IHK with "[Hrel]"); auto. }
        by iApply fundamental.
      + iApply (bin_log_related_case with "[] []").
        { by iApply fundamental. }
        { by iApply fundamental. }
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_alloc with "[]").
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_load with "[]").
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_store with "[]");
          try by iApply fundamental.
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_store with "[]");
          try by iApply fundamental.
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_fold with "[]").
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_unfold with "[]").
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_tlam with "[]").
        iIntros (τi). iModIntro.
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_tapp' with "[]").
        iApply (IHK with "[Hrel]"); auto.
      + iApply bin_log_related_unpack.
        * iApply (IHK with "[Hrel]"); auto.
        * iIntros (A). by iApply fundamental.
      + iApply bin_log_related_unpack.
        * by iApply fundamental.
        * iIntros (A). iApply (IHK with "[Hrel]"); auto.
      (* Sampling: hole at parameter / tape / alloc-parameter position.  In each
         the sibling subterm is discharged by [fundamental], the hole by [IHK],
         the [Sg !! i]/[SampleTyping] side conditions by [eassumption]. *)
      + iApply bin_log_related_sample;
          first [ eassumption | by iApply fundamental | iApply (IHK with "[Hrel]"); auto ].
      + iApply bin_log_related_sample_tape;
          first [ eassumption | by iApply fundamental | iApply (IHK with "[Hrel]"); auto ].
      + iApply bin_log_related_sample;
          first [ eassumption | by iApply fundamental | iApply (IHK with "[Hrel]"); auto ].
      + iApply bin_log_related_sample_tape;
          first [ eassumption | by iApply fundamental | iApply (IHK with "[Hrel]"); auto ].
      + iApply bin_log_related_alloc_sample_tape;
          first [ eassumption | by iApply fundamental | iApply (IHK with "[Hrel]"); auto ].
  Qed.
End bin_log_related_under_typed_ctx.

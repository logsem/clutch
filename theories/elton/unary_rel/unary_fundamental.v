(** Compatibility lemmas for the logical relation *)
From iris.base_logic Require Export invariants.
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext. 
From clutch.delay_prob_lang Require Import metatheory notation lang.
From clutch.elton Require Import primitive_laws proofmode.
From clutch.delay_prob_lang.typing Require Import types.
From clutch.elton.unary_rel Require Import unary_model unary_compatibility unary_rel_tactics unary_app_rel_rules unary_interp.

Section fundamental.
  Context `{!eltonGS Σ}.
  Implicit Types Δ : listO (lrelC Σ).
  Hint Resolve to_of_val : core.

  Local Ltac intro_clause := progress (iIntros (vs) "#Hvs /=").
  Local Ltac intro_clause' := progress (iIntros (?) "? /=").
  Local Ltac value_case := try intro_clause';
    try rel_pure_l; rel_values.

  Local Tactic Notation "rel_bind_ap" uconstr(e1) (* uconstr(e2)  *)constr(IH) ident(v) constr(Hv):=
    rel_bind_l (subst_map _ e1);
    (* rel_bind_r (subst_map _ e2); *)
    try iSpecialize (IH with "Hvs");
    iApply (refines_bind with IH);
    iIntros (v) Hv; simpl.

  Lemma bin_log_related_var Δ Γ x τ :
    Γ !! x = Some τ →
    ⊢ 〈Δ;Γ〉 ⊨ Var x : τ.
  Proof.
    intros Hx. intro_clause. simpl.
    rewrite (env_ltyped2_lookup _ vs x); last first.
    { rewrite lookup_fmap Hx //. }
    iDestruct "Hvs" as (v1 ->) "HA". simpl.
    by iApply refines_ret.
  Qed.

  Lemma bin_log_related_pair Δ Γ e1 e2 (τ1 τ2 : type) :
    (〈Δ;Γ〉 ⊨ e1 : τ1) -∗
    (〈Δ;Γ〉 ⊨ e2 : τ2) -∗
    〈Δ;Γ〉 ⊨ Pair e1 e2  : TProd τ1 τ2.
  Proof.
    iIntros "IH1 IH2".
    intro_clause.
    iApply (refines_pair with "[IH1] [IH2]").
    - by iApply "IH1".
    - by iApply "IH2".
  Qed.

  Lemma bin_log_related_fst Δ Γ e τ1 τ2 :
    (〈Δ;Γ〉 ⊨ e : τ1 * τ2) -∗
    〈Δ;Γ〉 ⊨ Fst e  : τ1.
  Proof.
    iIntros "IH".
    intro_clause.
    rel_bind_ap e "IH" v "IH".
    iDestruct "IH" as (v1 v2 )  "(% & IHw & IHw')". simplify_eq/=.
    value_case.
  Qed.

  Lemma bin_log_related_snd Δ Γ e τ1 τ2 :
    (〈Δ;Γ〉 ⊨ e : τ1 * τ2) -∗
    〈Δ;Γ〉 ⊨ Snd e : τ2.
  Proof.
    iIntros "IH".
    intro_clause.
    rel_bind_ap e "IH" v "IH".
    iDestruct "IH" as (v1 w1) "(% & IHw & IHw')". simplify_eq/=.
    value_case.
  Qed.

  Lemma bin_log_related_app Δ Γ e1 e2 τ1 τ2 :
    (〈Δ;Γ〉 ⊨ e1 : τ1 → τ2) -∗
    (〈Δ;Γ〉 ⊨ e2 : τ1) -∗
    〈Δ;Γ〉 ⊨ App e1 e2 :  τ2.
  Proof.
    iIntros "IH1 IH2".
    intro_clause.
    iApply (refines_app with "[IH1] [IH2]").
    - by iApply "IH1".
    - by iApply "IH2".
  Qed.

  Lemma bin_log_related_rec Δ (Γ : stringmap type) (f x : binder) (e : expr) τ1 τ2 :
    □ (〈Δ;<[f:=TArrow τ1 τ2]>(<[x:=τ1]>Γ)〉 ⊨ e : τ2) -∗
    〈Δ;Γ〉 ⊨ Rec f x e : τ1 → τ2.
  Proof.
    iIntros "#Ht".
    intro_clause.
    rel_pure_l. 
    iApply refines_arrow_val.
    iModIntro. iLöb as "IH". iIntros (v1) "#Hτ1".
    rel_pure_l. 

    set (r := (RecV f x (subst_map (binder_delete x (binder_delete f (vs))) e))).
    set (vvs' := binder_insert f r (binder_insert x (v1) vs)).
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
    - rewrite !delete_insert_delete !subst_subst !delete_idemp.
      by iApply "Ht".
    - rewrite !delete_insert_ne // subst_map_insert.
      rewrite !(subst_subst_ne _ x f) // subst_map_insert.
  Qed.

  Lemma bin_log_related_tlam Δ Γ (e : expr) τ :
    (∀ (A : lrel Σ),
      □ (〈(A::Δ);⤉Γ〉 ⊨ e : τ)) -∗
    〈Δ;Γ〉 ⊨ (Λ: e) : ∀: τ.
  Proof.
    iIntros "#H".
    intro_clause. rel_pure_l. 
    iApply refines_forall.
    iModIntro. iIntros (A).
    iDestruct ("H" $! A) as "#H1".
    iApply "H1".
    by rewrite (interp_ren A Δ Γ).
  Qed.

  Lemma bin_log_related_tapp' Δ Γ e τ τ' :
    (〈Δ;Γ〉 ⊨ e : ∀: τ) -∗
    〈Δ;Γ〉 ⊨ (TApp e)  : τ.[τ'/].
  Proof.
    iIntros "IH".
    intro_clause.
    rel_bind_ap e "IH" v "IH".
    iSpecialize ("IH" $! (interp τ' Δ)).
    iDestruct "IH" as "#IH".
    iSpecialize ("IH" $! #() with "[//]").
    by rewrite -interp_subst.
  Qed.

  Lemma bin_log_related_tapp (τi : lrel Σ) Δ Γ e τ :
    (〈Δ;Γ〉 ⊨ e : ∀: τ) -∗
    〈τi::Δ;⤉Γ〉 ⊨ (TApp e) : τ.
  Proof.
    iIntros "IH". intro_clause.
    iApply (bin_log_related_app _ _ e #()  () τ with "[IH] [] Hvs").
    - iClear (vs) "Hvs". intro_clause.
      rewrite interp_ren.
      iSpecialize ("IH" with "Hvs").
      iApply (refines_wand with "IH").
      eauto with iFrame.
    - value_case.
  Qed.

  Lemma bin_log_related_seq R Δ Γ e1 e2 τ1 τ2 :
    (〈(R::Δ);⤉Γ〉 ⊨ e1 : τ1) -∗
    (〈Δ;Γ〉 ⊨ e2 : τ2) -∗
    〈Δ;Γ〉 ⊨ (e1;; e2) : τ2.
  Proof.
    iIntros "He1 He2".
    intro_clause.
    iApply (refines_seq (interp τ1 (R::Δ)) with "[He1]").
    - iApply ("He1" with "[Hvs]").
      by rewrite interp_ren.
    - by iApply "He2".
  Qed.

  Lemma bin_log_related_seq' Δ Γ e1 e2 τ1 τ2 :
    (〈Δ;Γ〉 ⊨ e1 : τ1) -∗
    (〈Δ;Γ〉 ⊨ e2 : τ2) -∗
    〈Δ;Γ〉 ⊨ (e1;; e2) : τ2.
  Proof.
    iIntros "He1 He2".
    iApply (bin_log_related_seq lrel_true _ _ _ _ τ1.[ren (+1)] with "[He1] He2").
    intro_clause.
    rewrite interp_ren -(interp_ren_up [] Δ τ1).
    by iApply "He1".
  Qed.

  Lemma bin_log_related_injl Δ Γ e τ1 τ2 :
    (〈Δ;Γ〉 ⊨ e : τ1) -∗
    〈Δ;Γ〉 ⊨ InjL e : τ1 + τ2.
  Proof.
    iIntros "IH".
    intro_clause.
    iApply refines_injl.
    by iApply "IH".
  Qed.

  Lemma bin_log_related_injr Δ Γ e τ1 τ2 :
    (〈Δ;Γ〉 ⊨ e : τ2) -∗
    〈Δ;Γ〉 ⊨ InjR e : τ1 + τ2.
  Proof.
    iIntros "IH".
    intro_clause.
    iApply refines_injr. by iApply "IH".
  Qed.

  Lemma bin_log_related_case Δ Γ e0 e1 e2 τ1 τ2 τ3 :
    (〈Δ;Γ〉 ⊨ e0 : τ1 + τ2) -∗
    (〈Δ;Γ〉 ⊨ e1 : τ1 → τ3) -∗
    (〈Δ;Γ〉 ⊨ e2 : τ2 → τ3) -∗
    〈Δ;Γ〉 ⊨ Case e0 e1 e2 : τ3.
  Proof.
    iIntros "IH1 IH2 IH3".
    intro_clause.
    rel_bind_ap e0 "IH1" v0 "IH1".
    iDestruct "IH1" as (w) "[(% & #Hw)|(% & #Hw)]"; simplify_eq/=;
      rel_pures_l.
    - iApply (bin_log_related_app Δ Γ _ w  with "IH2 [] Hvs").
      value_case.
    - iApply (bin_log_related_app Δ Γ _ w with "IH3 [] Hvs").
      value_case.
  Qed.

  Lemma bin_log_related_if Δ Γ e0 e1 e2 τ :
    (〈Δ;Γ〉 ⊨ e0 : TBool) -∗
    (〈Δ;Γ〉 ⊨ e1 : τ) -∗
    (〈Δ;Γ〉 ⊨ e2 : τ) -∗
    〈Δ;Γ〉 ⊨ If e0 e1 e2 : τ.
  Proof.
    iIntros "IH1 IH2 IH3".
    intro_clause.
    rel_bind_ap e0 "IH1" v0 "IH1".
    iDestruct "IH1" as ([]) "%"; simplify_eq/=;
      rel_pures_l.
    - by iApply "IH2".
    - by iApply "IH3".
  Qed.

  Lemma bin_log_related_load Δ Γ e τ :
    (〈Δ;Γ〉 ⊨ e : (TRef τ)) -∗
    〈Δ;Γ〉 ⊨ Load e : τ.
  Proof.
    iIntros "IH".
    intro_clause.
    iApply refines_load.
    by iApply "IH".
  Qed.

  Lemma bin_log_related_store Δ Γ e1 e2 τ :
    (〈Δ;Γ〉 ⊨ e1 : TRef τ) -∗
    (〈Δ;Γ〉 ⊨ e2 : τ) -∗
    〈Δ;Γ〉 ⊨ Store e1 e2 : ().
  Proof.
    iIntros "IH1 IH2".
    intro_clause.
    iApply (refines_store with "[IH1] [IH2]").
    - by iApply "IH1".
    - by iApply "IH2".
  Qed.

  Lemma bin_log_related_alloc Δ Γ e τ :
    (〈Δ;Γ〉 ⊨ e : τ) -∗
    〈Δ;Γ〉 ⊨ Alloc e : TRef τ.
  Proof.
    iIntros "IH".
    intro_clause.
    rel_bind_ap e "IH" v "IH".
    rel_alloc_l l as "Hl".
    (* rel_alloc_r k as "Hk". *)
    iMod (inv_alloc (logN .@ (l)) _ (∃ w1,
      l ↦ w1 ∗ interp τ Δ w1)%I with "[Hl IH]") as "HN"; eauto.
    (* { iNext. iExists v; simpl; iFrame. } *)
    rel_values. iExists l. eauto.
  Qed.

  (* Lemma bin_log_related_alloctape Δ Γ e : *)
  (*   (〈Δ;Γ〉 ⊨ e : TNat) -∗ *)
  (*   〈Δ;Γ〉 ⊨ alloc e : TTape. *)
  (* Proof. *)
  (*   iIntros "IH". *)
  (*   intro_clause. *)
  (*   rel_bind_ap e "IH" v "IH". *)
  (*   iDestruct "IH" as (N) "%H2". *)
  (*   subst.  *)
  (*   rel_alloctape_l α as "Hα". *)
  (*   (* rel_alloctape_r β as "Hβ". *) *)
  (*   iPoseProof (tapeN_to_empty with "Hα") as "Hα". *)
  (*   (* iPoseProof (spec_tapeN_to_empty with "Hβ") as "Hβ". *) *)
  (*   iMod (inv_alloc (logN .@ (α)) _ (α ↪ (_; []) )%I *)
  (*          with "[$Hα]") as "HN". *)
  (*   rel_values. iExists α, N. auto. *)
  (* Qed. *)

  Lemma bin_log_related_rand Δ Γ e  :
    (〈Δ; Γ〉 ⊨ e : TNat) -∗
    〈Δ; Γ〉 ⊨ rand e : TNat.
  Proof.
    iIntros "IH1".
    intro_clause.
    (* rel_bind_ap e2  "IH2" v2 "#IH2". *)
    rel_bind_ap e "IH1" v "#IH1".
    iDestruct "IH1" as (N) "%H".
    subst. 
    iApply refines_rand; value_case.
  Qed.

  (* Lemma bin_log_related_rand_unit Δ Γ e1 e2 : *)
  (*   (〈Δ; Γ〉 ⊨ e1 : TNat) -∗ *)
  (*   (〈Δ; Γ〉 ⊨ e2 : TUnit) -∗ *)
  (*   〈Δ; Γ〉 ⊨ rand(e2) e1  : TNat. *)
  (* Proof. *)
  (*   iIntros "IH1 IH2". *)
  (*   intro_clause. *)
  (*   rel_bind_ap e2 "IH2" v2 "#IH2". *)
  (*   rel_bind_ap e1 "IH1" v1 "#IH1". *)
  (*   iDestruct "IH1" as (N) "%H". *)
  (*   subst. *)
  (*   (* destruct H as [-> ->]. *) *)
  (*   iDestruct "IH2" as "%H". *)
  (*   subst.  *)
  (*   (* destruct H as [-> ->]. *) *)
  (*   iApply refines_rand_unit. *)
  (*   value_case. *)
  (* Qed. *)

  Lemma bin_log_related_subsume_int_nat  Δ Γ e :
  (〈Δ; Γ〉 ⊨ e : TNat) -∗
  (〈Δ; Γ〉 ⊨ e: TInt).
  Proof.
    iIntros "IH".
    intro_clause.
    rel_bind_ap e "IH" v "#IH".
    iDestruct "IH" as (N) "->".
    value_case.
  Qed.

  Lemma bin_log_related_unboxed_eq Δ Γ e1 e2 τ :
    UnboxedType τ →
    (〈Δ;Γ〉 ⊨ e1 : τ) -∗
    (〈Δ;Γ〉 ⊨ e2 : τ) -∗
    〈Δ;Γ〉 ⊨ BinOp EqOp e1 e2: TBool.
  Proof.
    iIntros (Hτ) "IH1 IH2".
    intro_clause.
    rel_bind_ap e2 "IH2" v2 "#IH2".
    rel_bind_ap e1 "IH1" v1 "#IH1".
    (* iAssert (⌜val_is_unboxed v1⌝)%I as "%". *)
    (* { rewrite !unboxed_type_sound //. } *)
    (*   iDestruct "IH1" as "[$ _]". } *)
    (* iAssert (⌜val_is_unboxed v2'⌝)%I as "%". *)
    (* { rewrite !unboxed_type_sound //. *)
    (*   iDestruct "IH2" as "[_ $]". } *)
    (* iMod (unboxed_type_eq with "IH1 IH2") as "%"; first done. *)
    destruct Hτ.
    - iDestruct "IH1" as "->". iDestruct "IH2" as "->". rel_pures_l.
      rel_values.
    - iDestruct "IH1" as "[% ->]". iDestruct "IH2" as "[% ->]". rel_pures_l.
      rel_values.
    - iDestruct "IH1" as "[% ->]". iDestruct "IH2" as "[% ->]". rel_pures_l.
      rel_values.
    - iDestruct "IH1" as "[% ->]". iDestruct "IH2" as "[% ->]". rel_pures_l.
      rel_values.
    - iDestruct "IH1" as "[% [-> _]]". iDestruct "IH2" as "[% [-> _]]". rel_pures_l.
      rel_values.
  Qed.

  Lemma bin_log_related_int_binop Δ Γ op e1 e2 τ :
    binop_int_res_type op = Some τ →
    (〈Δ;Γ〉 ⊨ e1 : TInt) -∗
    (〈Δ;Γ〉 ⊨ e2 : TInt) -∗
    〈Δ;Γ〉 ⊨ BinOp op e1 e2 : τ.
  Proof.
    iIntros (Hopτ) "IH1 IH2".
    intro_clause.
    rel_bind_ap e2 "IH2" v2 "IH2".
    rel_bind_ap e1 "IH1" v1 "IH1".
    iDestruct "IH1" as (n) "->"; simplify_eq/=.
    iDestruct "IH2" as (n') "->"; simplify_eq/=.
    destruct (binop_int_typed_safe op n n' _ Hopτ) as [v' Hopv'].
    rel_pures_l; eauto.
    (* rel_pures_r; eauto. *)
    value_case.
    destruct op; inversion Hopv'; simplify_eq/=; try case_match; eauto.
  Qed.

  Lemma bin_log_related_bool_binop Δ Γ op e1 e2  τ :
    binop_bool_res_type op = Some τ →
    (〈Δ;Γ〉 ⊨ e1 : TBool) -∗
    (〈Δ;Γ〉 ⊨ e2 : TBool) -∗
    〈Δ;Γ〉 ⊨ BinOp op e1 e2 : τ.
  Proof.
    iIntros (Hopτ) "IH1 IH2".
    intro_clause.
    rel_bind_ap e2 "IH2" v2 "IH2".
    rel_bind_ap e1 "IH1" v1 "IH1".
    iDestruct "IH1" as (n) "->"; simplify_eq/=.
    iDestruct "IH2" as (n') "->"; simplify_eq/=.
    destruct (binop_bool_typed_safe op n n' _ Hopτ) as [v' Hopv'].
    rel_pures_l; eauto.
    (* rel_pures_r; eauto. *)
    value_case.
    destruct op; inversion Hopv'; simplify_eq/=; eauto.
  Qed.

  Lemma bin_log_related_int_unop Δ Γ op e τ :
    unop_int_res_type op = Some τ →
    (〈Δ;Γ〉 ⊨ e : TInt) -∗
    〈Δ;Γ〉 ⊨ UnOp op e : τ.
  Proof.
    iIntros (Hopτ) "IH".
    intro_clause.
    rel_bind_ap e "IH" v "IH".
    iDestruct "IH" as (n) "->"; simplify_eq/=.
    destruct (unop_int_typed_safe op n _ Hopτ) as [v' Hopv'].
    rel_pure_l. (* rel_pure_r. *)
    value_case.
    destruct op; inversion Hopv'; simplify_eq/=; try case_match; eauto.
  Qed.

  Lemma bin_log_related_bool_unop Δ Γ op e τ :
    unop_bool_res_type op = Some τ →
    (〈Δ;Γ〉 ⊨ e : TBool) -∗
    〈Δ;Γ〉 ⊨ UnOp op e : τ.
  Proof.
    iIntros (Hopτ) "IH".
    intro_clause.
    rel_bind_ap e "IH" v "IH".
    iDestruct "IH" as (n) "->"; simplify_eq/=.
    destruct (unop_bool_typed_safe op n _ Hopτ) as [v' Hopv'].
    rel_pure_l. (* rel_pure_r. *)
    value_case.
    destruct op; inversion Hopv'; simplify_eq/=; try case_match; eauto.
  Qed.

  Lemma bin_log_related_unfold Δ Γ e τ :
    (〈Δ;Γ〉 ⊨ e : μ: τ) -∗
    〈Δ;Γ〉 ⊨ rec_unfold e : τ.[(TRec τ)/].
  Proof.
    iIntros "IH".
    intro_clause.
    rel_bind_ap e "IH" v"IH".
    iEval (rewrite lrel_rec_unfold /lrel_car /=) in "IH".
    change (lrel_rec _) with (interp (TRec τ) Δ).
    rel_rec_l. (* rel_rec_r. *)
    value_case. by rewrite -interp_subst.
  Qed.

  Lemma bin_log_related_fold Δ Γ e τ :
    (〈Δ;Γ〉 ⊨ e : τ.[(TRec τ)/]) -∗
    〈Δ;Γ〉 ⊨ e : μ: τ.
  Proof.
    iIntros "IH".
    intro_clause.
    rel_bind_ap e "IH" v "IH".
    value_case.
    iModIntro.
    iEval (rewrite lrel_rec_unfold /lrel_car /=).
    change (lrel_rec _) with (interp (TRec τ) Δ).
    by rewrite -interp_subst.
  Qed.

  Lemma bin_log_related_pack' Δ Γ e (τ τ' : type) :
    (〈Δ;Γ〉 ⊨ e : τ.[τ'/]) -∗
    〈Δ;Γ〉 ⊨ e : ∃: τ.
  Proof.
    iIntros "IH".
    intro_clause.
    rel_bind_ap e "IH" v "#IH".
    value_case.
    iModIntro. iExists (interp τ' Δ).
    by rewrite interp_subst.
  Qed.

  Lemma bin_log_related_pack (τi : lrel Σ) Δ Γ e τ :
    (〈τi::Δ;⤉Γ〉 ⊨ e : τ) -∗
    〈Δ;Γ〉 ⊨ e : ∃: τ.
  Proof.
    iIntros "IH".
    intro_clause.
    iSpecialize ("IH" $! vs with "[Hvs]").
    { by rewrite interp_ren. }
    rel_bind_ap e "IH" v "#IH".
    value_case.
    iModIntro. by iExists τi.
  Qed.

  Lemma bin_log_related_unpack Δ Γ x e1 e2 τ τ2 :
    (〈Δ;Γ〉 ⊨ e1 : ∃: τ) -∗
    (∀ τi : lrel Σ,
      〈τi::Δ;<[x:=τ]>(⤉Γ)〉 ⊨
        e2 : (Autosubst_Classes.subst (ren (+1)) τ2)) -∗
    〈Δ;Γ〉 ⊨ (unpack: x := e1 in e2) : τ2.
  Proof.
    iIntros "IH1 IH2".
    intro_clause.
    rel_pure_l. (* rel_pure_r. *)
    rel_bind_ap e1 "IH1" v "#IH1".
    iDestruct "IH1" as (A) "#IH".
    rel_rec_l. rel_pure_l. rel_pure_l.
    (* rel_rec_r. rel_pure_r. rel_pure_r. *)
    rel_pure_l. (* rel_pure_r. *)
    iSpecialize ("IH2" $! A (binder_insert x (v) vs) with "[Hvs]").
    { rewrite -(interp_ren A).
      rewrite binder_insert_fmap.
      iApply (env_ltyped2_insert with "IH Hvs"). }
    rewrite !subst_map_binder_insert /=.
    iApply (refines_wand with "IH2").
    iIntros (v1). rewrite (interp_ren_up [] Δ τ2 A).
    asimpl. eauto.
  Qed.

  (* Lemma bin_log_related_fork Δ Γ e : *)
  (*   (〈Δ;Γ〉 ⊨ e : ()) -∗ *)
  (*   〈Δ;Γ〉 ⊨ Fork e : (). *)
  (* Proof. *)
  (*   iIntros "IH". *)
  (*   intro_clause. *)
  (*   iApply refines_fork. *)
  (*   by iApply "IH". *)
  (* Qed. *)

  (* Lemma bin_log_related_CmpXchg_EqType Δ Γ e1 e2 e3 τ : *)
  (*   EqType τ -> *)
  (*   UnboxedType τ -> *)
  (*   (〈Δ;Γ〉 ⊨ e1 : TRef τ) -∗ *)
  (*   (〈Δ;Γ〉 ⊨ e2 : τ) -∗ *)
  (*   (〈Δ;Γ〉 ⊨ e3 : τ) -∗ *)
  (*   〈Δ;Γ〉 ⊨ CmpXchg e1 e2 e3 : TProd τ TBool. *)
  (* Proof. *)
  (*   intros Hτ Hτ'. *)
  (*   iIntros "IH1 IH2 IH3". *)
  (*   intro_clause. *)
  (*   rel_bind_ap e3 "IH3" v3 "#IH3". *)
  (*   rel_bind_ap e2 "IH2" v2 "#IH2". *)
  (*   rel_bind_ap e1 "IH1" v1 "#IH1". *)
  (*   iDestruct "IH1" as (l) "(% & Hinv)"; simplify_eq/=. *)
  (*   iDestruct (unboxed_type_sound with "IH2") as "%"; try fast_done. *)
  (*   (* iDestruct (eq_type_sound with "IH2") as "%"; first fast_done. *) *)
  (*   (* iDestruct (eq_type_sound with "IH3") as "%"; first fast_done. *) *)
  (*   subst. *)
  (*   rewrite -(fill_empty (CmpXchg #l _ _)). *)
  (*   iApply refines_atomic_l. *)
  (*   (* iIntros (? j) "Hspec". *) *)
  (*   iInv (logN .@ (l)) as (v1) "[>Hv1 #Hv]" "Hclose". *)
  (*   iModIntro. *)
  (*   destruct (decide (v1 = v2)) as [|Hneq]; subst. *)
  (*   - iApply wp_pupd. *)
  (*     wp_cmpxchg_suc. *)
  (*     iModIntro. *)
  (*     (* iDestruct (eq_type_sound with "Hv") as "%"; first fast_done. *) *)
  (*     (* tp_cmpxchg_suc j. *) *)
  (*     iModIntro. *)
  (*     iMod ("Hclose" with "[-]"). *)
  (*     { iNext; by iFrame. } *)
  (*     iModIntro. *)
  (*     iFrame.  *)
  (*     rel_values. subst. *)
  (*     iExists _, _. do 2 (iSplitL; first done). *)
  (*     by iExists _. *)
  (*   - iApply wp_pupd. *)
  (*     wp_cmpxchg_fail. *)
  (*     iModIntro. *)
  (*     (* iDestruct (eq_type_sound with "Hv") as "%"; first fast_done. *) *)
  (*     (* tp_cmpxchg_fail j. *) *)
  (*     iModIntro. *)
  (*     iMod ("Hclose" with "[-]"). *)
  (*     { iNext; iExists _; by iFrame. } *)
  (*     iModIntro. iFrame.  *)
  (*     rel_values. iExists _, _. do 2 (iSplitL; first done). *)
  (*     by iExists _. *)
  (* Qed. *)

  
  (* Lemma bin_log_related_CmpXchg Δ Γ e1 e2 e3 τ: *)
  (*   UnboxedType τ -> *)
  (*   (〈Δ;Γ〉 ⊨ e1 : TRef τ) -∗ *)
  (*   (〈Δ;Γ〉 ⊨ e2 : τ) -∗ *)
  (*   (〈Δ;Γ〉 ⊨ e3 : τ) -∗ *)
  (*   〈Δ;Γ〉 ⊨ CmpXchg e1 e2 e3 : TProd τ TBool. *)
  (* Proof. *)
  (*   intros.  *)
  (*   cut (EqType τ ∨ ∃ τ', τ = TRef τ'). *)
  (*   { intros [Hτ | [τ' ->]]. *)
  (*     - by iApply bin_log_related_CmpXchg_EqType. *)
  (*     - iIntros "H1 H2 H3". intro_clause. *)
  (*       iSpecialize ("H1" with "Hvs"). *)
  (*       iSpecialize ("H2" with "Hvs"). *)
  (*       iSpecialize ("H3" with "Hvs"). *)
  (*       iApply (refines_cmpxchg_ref with "H1 H2 H3"). } *)
  (*   by apply unboxed_type_ref_or_eqtype. *)
  (* Qed. *)

  (* Lemma bin_log_related_xchg Δ Γ e1 e2 τ : *)
  (*   (〈Δ;Γ〉 ⊨ e1 : TRef τ) -∗ *)
  (*   (〈Δ;Γ〉 ⊨ e2 : τ) -∗ *)
  (*   〈Δ;Γ〉 ⊨ Xchg e1 e2 : τ. *)
  (* Proof. *)
  (*   iIntros "IH1 IH2". *)
  (*   intro_clause. *)
  (*   iApply (refines_xchg with "[IH1] [IH2]"). *)
  (*   - by iApply "IH1". *)
  (*   - by iApply "IH2". *)
  (* Qed. *)

  (* Lemma bin_log_related_FAA Δ Γ e1 e2 : *)
  (*   (〈Δ;Γ〉 ⊨ e1 : TRef TNat) -∗ *)
  (*   (〈Δ;Γ〉 ⊨ e2 : TNat) -∗ *)
  (*   〈Δ;Γ〉 ⊨ FAA e1 e2 : TNat. *)
  (* Proof. *)
  (*   iIntros "IH1 IH2". *)
  (*   intro_clause. *)
  (*   rel_bind_ap e2  "IH2" v2 "#IH2". *)
  (*   rel_bind_ap e1 "IH1" v1 "#IH1". *)
  (*   iDestruct "IH1" as (l) "(% & Hinv)"; simplify_eq/=. *)
  (*   iDestruct "IH2" as (n) "->". simplify_eq. *)
  (*   rewrite -(fill_empty (FAA #l _)). *)
  (*   iApply refines_atomic_l. *)
  (*   (* iIntros (? j) "Hspec". *) *)
  (*   iInv (logN.@ (l)) as (v1) "[>Hv1 #>Hv]" "Hclose". *)
  (*   iDestruct "Hv" as (n1) "->"; simplify_eq. *)
  (*   iApply wp_pupd. *)
  (*   iModIntro. *)
  (*   wp_faa. *)
  (*   iModIntro. *)
  (*   (* tp_faa j. *) *)
  (*   iModIntro. *)
  (*   iMod ("Hclose" with "[-]") as "_". *)
  (*   { iNext. iExists _. iFrame. rewrite -Nat2Z.inj_add. by iExists _. } *)
  (*   iFrame. iModIntro. simpl. rel_values. *)
  (* Qed. *)
  
  Theorem fundamental Δ Γ e τ :
    Γ ⊢ₜ e : τ → ⊢ 〈Δ;Γ〉 ⊨ e : τ
  with fundamental_val Δ v τ :
    ⊢ᵥ v : τ → ⊢ interp τ Δ v.
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
      + iApply bin_log_related_rand; by iApply fundamental.
      + iApply bin_log_related_subsume_int_nat ; by iApply fundamental.
    - intros Hv. destruct Hv; simpl.
      + eauto. 
      + iExists _; eauto.
      + iExists _; eauto.
      + iExists _; eauto.
      + iExists _,_.
        repeat iSplit; eauto; by iApply fundamental_val.
      + iExists _. iLeft.
        repeat iSplit; eauto; by iApply fundamental_val.
      + iExists _. iRight.
        repeat iSplit; eauto; by iApply fundamental_val.
      + iLöb as "IH". iModIntro.
        iIntros (v1) "#Hv".
        pose (Γ := (<[f:=(τ1 → τ2)%ty]> (<[x:=τ1]> ∅)):stringmap type).
        pose (γ := (binder_insert f (rec: f x := e)%V
                     (binder_insert x (v1) ∅)):stringmap (val)).
        rel_pure_l. 
        iPoseProof (fundamental Δ Γ e τ2 $! γ with "[]") as "H"; eauto.
        { rewrite /γ /Γ. rewrite !binder_insert_fmap fmap_empty.
          iApply (env_ltyped2_insert with "IH").
          iApply (env_ltyped2_insert with "Hv").
          iApply env_ltyped2_empty. }
        rewrite /γ /=.
        by rewrite !subst_map_binder_insert_2_empty.
      + iIntros (A). iModIntro. iIntros (v1) "_".
        rel_pures_l. (* rel_pures_r. *)
        iPoseProof (fundamental (A::Δ) ∅ e τ $! ∅ with "[]") as "H"; eauto.
        { rewrite fmap_empty. iApply env_ltyped2_empty. }
        by rewrite subst_map_empty.
  Qed.

  Theorem refines_typed τ Δ e :
    ∅ ⊢ₜ e : τ →
    ⊢ REL e : interp τ Δ.
  Proof.
    move=> /fundamental Hty.
    iPoseProof (Hty Δ with "[]") as "H".
    { rewrite fmap_empty. iApply env_ltyped2_empty. }
    by rewrite !subst_map_empty.
  Qed.
  
  Theorem typed_safe τ Δ e :
    ∅ ⊢ₜ e : τ →
    ⊢ WP e {{ interp τ Δ }}.
  Proof.
    iIntros (H).
    iPoseProof refines_typed as "H"; first done.
    by unfold_rel.
  Qed.

End fundamental.

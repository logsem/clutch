From iris.base_logic Require Export invariants. 
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext.

From clutch.prob_eff_lang.probblaze Require Import metatheory notation syntax semantics sem_judgement sem_def sem_operators sem_row proofmode.
From clutch.prob_eff_lang.probblaze Require Import primitive_laws compatibility pure_weakestpre.
From clutch.prob_eff_lang.probblaze Require Import sem_env sem_types sem_sig.
From clutch.prob_eff_lang.probblaze Require Import types.
From clutch.prob_eff_lang.probblaze Require Import interp logic fundamental_subtyping.

Section compatibility_interp.

  Context `{!probblazeRGS Σ}.

  Ltac push_lr_one :=
  first [ rewrite lbl_resolve_rec
        | rewrite lbl_resolve_app | rewrite lbl_resolve_unop
        | rewrite lbl_resolve_binop | rewrite lbl_resolve_if
        | rewrite lbl_resolve_pair | rewrite lbl_resolve_fst
        | rewrite lbl_resolve_snd | rewrite lbl_resolve_injl
        | rewrite lbl_resolve_injr | rewrite lbl_resolve_case
        | rewrite lbl_resolve_allocn | rewrite lbl_resolve_load
        | rewrite lbl_resolve_store | rewrite lbl_resolve_alloctape
        | rewrite lbl_resolve_rand | rewrite lbl_resolve_effect
        | rewrite lbl_resolve_do_label | rewrite lbl_resolve_do_name
        | rewrite lbl_resolve_handle_label | rewrite lbl_resolve_handle_name
        | idtac ].
  Ltac push_lr := push_lr_one; push_lr_one.
  
  Lemma syn_typed_binop_typed_binop op ι κ τ η μ δ ξ:
  syn_typed_bin_op op ι κ τ → typed_bin_op op (interp._ty η μ δ ι ξ) (interp._ty η μ δ κ ξ) (interp._ty η μ δ τ ξ).
  Proof.
  intros []; constructor.
  Qed.

  Lemma syn_typed_unop_typed_unop op κ τ η μ δ ξ:
  syn_typed_un_op op κ τ → typed_un_op op (interp._ty η μ δ κ ξ) (interp._ty η μ δ τ ξ).
  Proof.
  intros []; constructor.
  Qed.


  Lemma ctx_dom_env_dom x Γ :
  ∀ η μ δ ξ, x ∉ ctx_dom Γ → x ∉ env_dom ((λ '(s, τ), (s, interp._ty η μ δ τ ξ)) <$> Γ).
  Proof.
  intros η μ δ ξ Hnin. induction Γ as [| (y, κ) Γ' IH]; simpl.
  - rewrite env_dom_nil. apply not_elem_of_nil.
  - rewrite env_dom_cons. apply not_elem_of_cons. split.
    + intros ->. apply Hnin. rewrite /ctx_dom /=. set_solver.
    + apply IH. rewrite /ctx_dom /= in Hnin. set_solver.
  Qed.


  Lemma interp_c_var Δ τ Γ x :
   ⊢ 〈Δ; (ctx_insert (BNamed x) τ Γ)〉 ⊨ₜ (Var x) ≤log≤ (Var x) :RNil:τ⫤Γ.
  Proof.
   iIntros (η μ δ ξ' Hδ).
   rewrite !lbl_resolve_var.
   iIntros (γ) "!# /= [%v (%Hrw & Hτ & HΓ₁)] /=".
   rewrite !lookup_fmap. rewrite Hrw. simpl.
   iApply brel_value. iIntros. by iFrame.
  Qed.

  Lemma interp_c_binop Δ Γ1 Γ2 Γ3 op e1 e2 ρ τ ι κ :
       syn_typed_bin_op op ι κ τ ->
       ⊢  (〈Δ; Γ2〉 ⊨ₜ e1 ≤log≤ e1 :ρ:ι⫤Γ3) -∗
       ( 〈Δ; Γ1〉 ⊨ₜ e2 ≤log≤ e2 :ρ:κ⫤Γ2) -∗
       〈Δ; Γ1〉 ⊨ₜ BinOp op e1 e2 ≤log≤ BinOp op e1 e2 :ρ:τ⫤ Γ3.                                                     
  Proof.
    intros Hsyn. iIntros "#He1 #He2".
    iIntros (η μ δ ξ Hδ). rewrite !lbl_resolve_binop.
    iIntros "!# %γ HΓ1 //=".
    About syn_typed_binop_typed_binop.
    apply (syn_typed_binop_typed_binop op ι κ τ η μ δ ξ) in Hsyn.
    destruct (bin_op_copy_types _ _ _ _ Hsyn) as [Hmulτ [Hmulκ Hmulι]].
    iApply (brel_bind [BinOpRCtx _ _] [BinOpRCtx _ _]); [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
    iApply (brel_wand with "[HΓ1]"); first by iApply "He2".
    iIntros "!# % % (#Hκ & HΓ2) /=".
    iApply (brel_bind [BinOpLCtx _ _] [BinOpLCtx _ _]); [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
    iApply (brel_wand with "[Hκ HΓ2]"); first by iApply "He1".
    iIntros "!# % % (#Hτ & HΓ3) /=".
    destruct op; inversion Hsyn;
      iDestruct "Hκ" as "(%n1 & -> & ->)";
      iDestruct "Hτ" as "(%n2 & -> & ->)";
      brel_pures_l; brel_pures_r; iFrame; eauto. 
   Qed.

  Lemma interp_c_unop Δ Γ1 Γ2 e op ρ κ τ :
    syn_typed_un_op op κ τ ->
    ⊢ (〈Δ; Γ1〉 ⊨ₜ e ≤log≤ e :ρ:κ⫤Γ2) -∗
    (〈Δ; Γ1〉 ⊨ₜ (UnOp op e) ≤log≤ (UnOp op e) :ρ:τ⫤Γ2).
  Proof.
    intros Hsyn. iIntros "#He".
    iIntros (η μ δ ξ Hδ). rewrite !lbl_resolve_unop.
     iIntros "!# %γ HΓ1 //=".
    iApply (brel_bind [UnOpCtx _] [UnOpCtx _]); [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
    iApply (brel_wand with "[HΓ1]"); first by iApply "He".
    iIntros "!# % % (Hτ & HΓ2) /=".
    destruct op; inversion Hsyn;
      iDestruct "Hτ" as "(%n2 & -> & ->)";
      brel_pures_l; brel_pures_r; iFrame; eauto.
  Qed.
  
  Lemma interp_c_val Δ Γ v τ :
    ⊢  (⊨ᵥ v ≤log≤ v : τ) -∗
      (〈Δ; Γ〉 ⊨ₜ (Val v) ≤log≤ (Val v) :RNil:τ⫤Γ).
  Proof.
    iIntros "#Hval". iIntros (η μ δ ξ Hδ).
    rewrite !lbl_resolve_val.
    iIntros "!# %vvs HΓ /=".
    iApply brel_value. iFrame.  Locate "⊨ᵥ". unfold bin_log_val_related. simpl. iIntros. iFrame. iModIntro. unfold sem_val_typed.
    iSpecialize ("Hval" $! η μ δ ξ). simpl.
    iDestruct "Hval" as "#Hval".
    iApply "Hval".
  Qed.
  
  (*Lemma interp_c_pure *)
                                
  Lemma interp_c_pair Δ Γ1 Γ2 Γ3 e1 e2 τ1 τ2 ρ :
   (∀ η μ δ ξ, (interp._row η μ δ ρ ξ) ᵣ⪯ₜ (interp._ty η μ δ τ2 ξ)) ->
   ⊢ (〈Δ; Γ2〉 ⊨ₜ e1 ≤log≤ e1 :ρ:τ1⫤Γ3) -∗
    (〈Δ; Γ1〉 ⊨ₜ e2 ≤log≤ e2 :ρ:τ2⫤Γ2) -∗
    (〈Δ; Γ1〉 ⊨ₜ (e1, e2) ≤log≤ (e1, e2) :ρ:(τ1 * τ2)⫤Γ3).
  Proof.
    intros Hrt. iIntros "#He1 #He2".
    iIntros (η μ δ ξ Hδ). rewrite !lbl_resolve_pair.
    iIntros "!# %γ HΓ1 //=".
    iApply (brel_bind [PairRCtx _] [PairRCtx _]); [iApply traversable_to_iThy| iApply to_iThy_le_refl |].
    iApply (brel_wand with "[HΓ1]"); first by iApply "He2".
    iIntros "!# % % (Hτ2 & HΓ2) /=".
    iApply (brel_bind [PairLCtx _] [PairLCtx _]); [iApply traversable_to_iThy| iApply to_iThy_le_refl|].
    iApply (brel_wand with "[Hτ2 HΓ2]").
    { iApply (brel_mono_on_prop with "[][Hτ2]"); [by iApply row_type_sub| done| by iApply "He1"]. }
    iIntros "!# % % ((Hτ & HΓ3) & Hτ2) /=".
    brel_pures_l. brel_pures_r.
    by iFrame.
  Qed.
  
  Lemma interp_c_fst Δ Γ1 Γ2 ρ τ1 τ2 e :
    ⊢ (〈Δ; Γ1〉 ⊨ₜ e ≤log≤ e :ρ:(τ1 * τ2)⫤Γ2) -∗
    (〈Δ; Γ1〉 ⊨ₜ (Fst e) ≤log≤ (Fst e) :ρ:τ1⫤Γ2).
  Proof.
    iIntros "#He". iIntros (η μ δ ξ Hδ). rewrite !lbl_resolve_fst.
    iIntros "!# %γ HΓ1 //=".
    iApply (brel_bind [_] [_]); [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
    iApply (brel_wand with "[HΓ1]"); [by iApply "He"|].
    iIntros "!# % % ((%&%&%&%&->&->&Hτ&_)&HΓ2)". 
    brel_pures_l. brel_pures_r.
    by iFrame.
  Qed.

  Lemma interp_c_snd Δ Γ1 Γ2 ρ τ1 τ2 e :
    ⊢ (〈Δ; Γ1〉 ⊨ₜ e ≤log≤ e :ρ:(τ1 * τ2)⫤Γ2) -∗
    (〈Δ; Γ1〉 ⊨ₜ (Snd e) ≤log≤ (Snd e) :ρ:τ2⫤Γ2).
  Proof.
    iIntros "#He". iIntros (η μ δ ξ Hδ). rewrite !lbl_resolve_snd.
    iIntros "!# %γ HΓ1 //=".
    iApply (brel_bind [_] [_]); [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
    iApply (brel_wand with "[HΓ1]"); [by iApply "He"|].
    iIntros "!# % % ((%&%&%&%&->&->&_&Hκ)&HΓ2)". 
    brel_pures_l. brel_pures_r.
    by iFrame.
  Qed.
  
  Lemma interp_c_left_inj Δ Γ1 Γ2 ρ τ1 τ2 e :
     ⊢ (〈Δ; Γ1〉 ⊨ₜ e ≤log≤ e :ρ:τ1⫤Γ2) -∗
     (〈Δ; Γ1〉 ⊨ₜ (InjL e) ≤log≤ (InjL e) :ρ:(τ1 + τ2)⫤Γ2).
  Proof.
    iIntros "#He". iIntros (η μ δ ξ Hδ). rewrite !lbl_resolve_injl.
    iIntros "!# %γ HΓ1 //=".
    iApply (brel_bind [InjLCtx] [InjLCtx]); [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
    iApply (brel_wand with "[HΓ1]"); first by iApply "He".
    iIntros "!# % % (Hτ & HΓ2) //=".
    brel_pures_l. brel_pures_r.
    iModIntro. iFrame. iExists _, _. iLeft.
    by iFrame.
  Qed.

  Lemma interp_c_right_inj Δ Γ1 Γ2 ρ τ1 τ2 e :
     ⊢ (〈Δ; Γ1〉 ⊨ₜ e ≤log≤ e :ρ:τ2⫤Γ2) -∗
     (〈Δ; Γ1〉 ⊨ₜ (InjR e) ≤log≤ (InjR e) :ρ:(τ1 + τ2)⫤Γ2).
  Proof.
    iIntros "#He". iIntros (η μ δ ξ Hδ). rewrite !lbl_resolve_injr.
    iIntros "!# %γ HΓ1 //=".
    iApply (brel_bind [InjRCtx] [InjRCtx]); [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
    iApply (brel_wand with "[HΓ1]"); first by iApply "He".
    iIntros "!# % % (Hκ & HΓ2) //=".
    brel_pures_l. brel_pures_r.
    iFrame. iExists _,_. iRight. by iFrame.
  Qed.
  
  Lemma interp_c_match Δ Γ1 Γ2 Γ3 e0 e1 e2 τ1 τ2 τ3 (x y : binder) ρ :
    let xΓ2 := match x with BNamed x => ((x,τ1) :: Γ2) | BAnon => Γ2 end in
    let yΓ2 := match y with BNamed y => ((y,τ2) :: Γ2) | BAnon => Γ2 end in
    x ∉ ctx_dom Γ2 -> x ∉ ctx_dom Γ3 -> y ∉ ctx_dom Γ2 -> y ∉ ctx_dom Γ3 ->
    ⊢  (〈Δ; Γ1〉 ⊨ₜ e0 ≤log≤ e0 :ρ:(τ1 + τ2)⫤Γ2) -∗
       (〈Δ; xΓ2〉 ⊨ₜ e1 ≤log≤ e1 :ρ:τ3⫤Γ3) -∗
       (〈Δ; yΓ2〉 ⊨ₜ e2 ≤log≤ e2 :ρ:τ3⫤Γ3) -∗                                                         
       (〈Δ; Γ1〉 ⊨ₜ
        match: e0 with InjL x => e1 | InjR y => e2 end
        ≤log≤
        match: e0 with InjL x => e1 | InjR y => e2 end :ρ:τ3⫤Γ3).
  Proof.
      iIntros (??????) "#He0 #He1 #He2".
      iIntros (η μ δ ξ Hδ). push_lr.
      iIntros "!# %γ HΓ1 //=".
      destruct x,y.
      - iApply (brel_bind [CaseCtx _ _] [CaseCtx _ _]); [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
        simpl.
        iApply (brel_wand with "[HΓ1]"); first by iApply "He0".
        iIntros "!# % % ((% & % & [(-> & -> & Hτ1)|(->&->&Hτ2)]) & HΓ2) //="; brel_pures_l; brel_pures_r.
      + by iApply "He1".       
      + by iApply "He2".
     - iApply (brel_bind [CaseCtx _ _] [CaseCtx _ _]); [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
       iApply (brel_wand with "[HΓ1]"); first by iApply "He0".
       iIntros "!# % % ((% & % & [(-> & -> & Hτ1)|(->&->&Hτ2)]) & HΓ2) //="; brel_pures_l; brel_pures_r.
      + by iApply "He1".       
      + rewrite -!subst_map_insert. iApply (brel_wand with "[HΓ2 Hτ2]").
        { assert (w1 = fst (w1, w2) ∧ w2 = snd (w1, w2)) as (-> & ->) by done. rewrite -!fmap_insert. simpl.
          iApply "He2".
          + iPureIntro. auto.
          + simpl. rewrite -> env_sem_typed_cons. solve_env. unfold fmap. 
            set (Γ2' := list_fmap (string * type)%type
              (string * sem_ty Σ)%type
              (λ '(s0, τ), (s0, interp._ty η μ δ τ ξ))
              Γ2). rewrite -env_sem_typed_insert; [by iApply "HΓ2" | eapply ctx_dom_env_dom; auto ]. }
        iIntros "!# % % [$ HΓ3]". rewrite -env_sem_typed_insert; [by iApply "HΓ3" | eapply ctx_dom_env_dom; auto ].
    - iApply (brel_bind [CaseCtx _ _] [CaseCtx _ _]); [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
      iApply (brel_wand with "[HΓ1]"); first by iApply "He0".
      iIntros "!# % % ((% & % & [(-> & -> & Hτ1)|(->&->&Hτ2)]) & HΓ2) //="; brel_pures_l; brel_pures_r.
      + rewrite -!subst_map_insert. iApply (brel_wand with "[HΓ2 Hτ1]").
        { assert (w1 = fst (w1, w2) ∧ w2 = snd (w1, w2)) as (-> & ->) by done. rewrite -!fmap_insert. simpl.
          iApply "He1".
          + iPureIntro. auto.
          + simpl. rewrite -> env_sem_typed_cons. solve_env. unfold fmap.
             set (Γ2' := list_fmap (string * type)%type
              (string * sem_ty Σ)%type
              (λ '(s0, τ), (s0, interp._ty η μ δ τ ξ))
              Γ2). rewrite -env_sem_typed_insert; [by iApply "HΓ2" | eapply ctx_dom_env_dom; auto ].
        }
        iIntros "!# % % [$ HΓ3]". solve_env.  rewrite -env_sem_typed_insert; [by iApply "HΓ3" | eapply ctx_dom_env_dom; auto ]. 
      + by iApply "He2".
    - iApply (brel_bind [CaseCtx _ _] [CaseCtx _ _]); [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
      iApply (brel_wand with "[HΓ1]"); first by iApply "He0".
      iIntros "!# % % ((% & % & [(-> & -> & Hτ1)|(->&->&Hτ2)]) & HΓ2) //="; brel_pures_l; brel_pures_r.
      + rewrite -!subst_map_insert. iApply (brel_wand with "[HΓ2 Hτ1]").
        { assert (w1 = fst (w1, w2) ∧ w2 = snd (w1, w2)) as (-> & ->) by done. rewrite -!fmap_insert. simpl.
          iApply "He1".
          + iPureIntro. auto.
          + simpl. rewrite -> env_sem_typed_cons. solve_env. unfold fmap. 
            set (Γ2' := list_fmap (string * type)%type
              (string * sem_ty Σ)%type
              (λ '(s0, τ), (s0, interp._ty η μ δ τ ξ))
              Γ2). rewrite -env_sem_typed_insert; [by iApply "HΓ2" | eapply ctx_dom_env_dom; auto ]. }
        iIntros "!# % % [$ HΓ3]". solve_env. rewrite -env_sem_typed_insert; [by iApply "HΓ3" | eapply ctx_dom_env_dom; auto ]. 
      + rewrite -!subst_map_insert. iApply (brel_wand with "[HΓ2 Hτ2]").
        { assert (w1 = fst (w1, w2) ∧ w2 = snd (w1, w2)) as (-> & ->) by done. rewrite -!fmap_insert. simpl.
          iApply "He2".
          + iPureIntro. auto. 
          + simpl. rewrite -> env_sem_typed_cons. solve_env. unfold fmap. 
            set (Γ2' := list_fmap (string * type)%type
              (string * sem_ty Σ)%type
              (λ '(s0, τ), (s0, interp._ty η μ δ τ ξ))
              Γ2). rewrite -env_sem_typed_insert; [by iApply "HΓ2" | eapply ctx_dom_env_dom; auto ]. }
        iIntros "!# % % [$ HΓ3]". solve_env.  rewrite -env_sem_typed_insert; [by iApply "HΓ3" | eapply ctx_dom_env_dom; auto ].
    Qed.

  Lemma interp_c_if Δ Γ1 Γ2 Γ3 ρ τ e0 e1 e2 :
    ⊢ (〈Δ; Γ1〉 ⊨ₜ e0 ≤log≤ e0 : ρ:𝔹⫤Γ2) -∗
      (〈Δ; Γ2〉 ⊨ₜ e1 ≤log≤ e1 : ρ:τ⫤Γ3) -∗
      (〈Δ; Γ2〉 ⊨ₜ e2 ≤log≤ e2 : ρ:τ⫤Γ3) -∗              
      (〈Δ; Γ1〉 ⊨ₜ (if: e0 then e1 else e2)
         ≤log≤ (if: e0 then e1 else e2) :ρ:τ⫤Γ3).
  Proof. iIntros "#He0 #He1 #He2".
         iIntros (η μ δ ξ Hδ). push_lr.
         iIntros "!# %γ HΓ1 //=".
         iApply (brel_bind [IfCtx _ _] [IfCtx _ _]); [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
         iApply (brel_wand with "[HΓ1]"); first by iApply "He0".
         iIntros "!# % % (#(% & -> & ->) & HΓ2) /=".
         destruct b; brel_pures_l; brel_pures_r; [by iApply "He1"|by iApply "He2"].
  Qed.

  Lemma bin_log_pure_typed_oval Δ Γ Γ' e1 e2 τ :
    ⊢ (⟨Δ; Γ ⟩ ⊨ₚ e1 ≤log≤ e2 : τ) -∗
    (〈Δ; ctx_append Γ Γ'〉 ⊨ₜ e1 ≤log≤ e2 : RNil:τ⫤Γ').
  Proof.
    iIntros "#He".
    iIntros (η μ δ ξ Hδ).
    iIntros "!# %γ HΓ' /=".
    iApply prel_brel.
    unfold ctx_append.
    rewrite fmap_app.
    rewrite env_sem_typed_app.
    iDestruct "HΓ'" as "(HΓ & HΓ')".
    unfold bin_log_related.
    iSpecialize ("He" $! η μ δ ξ Hδ).
    iDestruct ("He" with "HΓ") as "Hprel".
    iApply (prel_mono with "[HΓ'][$]").
    by iIntros (??) "$".
  Qed.

  Lemma bin_log_pure_typed_mbang_MS_weaken Δ Γ m e1 e2 τ :
    ⊢ (⟨Δ; Γ ⟩ ⊨ₚ e1 ≤log≤ e2 : ![MS] τ) -∗
    (⟨Δ; Γ ⟩ ⊨ₚ e1 ≤log≤ e2 : ![m] τ).
  Proof.
    iIntros "#He".
    iIntros (η μ δ ξ Hδ).
    iIntros "!# %γ HΓ /=".
    iSpecialize ("He" $! η μ δ ξ Hδ).
    iDestruct ("He" with "HΓ") as "Hprel".
    iApply (prel_mono with "[] Hprel").
    iIntros (w1 w2). rewrite /sem_ty_mbang /=.
    iIntros "#H". by iApply bi.intuitionistically_intuitionistically_if.
  Qed.


  Lemma interp_c_bin_log_pure_typed_ufun Δ Γ  ρ τ κ e1 e2 f x `{le.MultiC Γ} :
    x ∉ (ctx_dom Γ) -> f ∉ (ctx_dom Γ) ->
    match f with BNamed f => BNamed f ≠ x | BAnon => True end →
    ⊢ (〈Δ; (x, τ) ::? (f, (TBang MS (TArrow τ ρ κ))) ::? Γ〉 ⊨ₜ e1 ≤log≤ e2 :ρ:κ⫤[]) -∗
    (⟨Δ; Γ ⟩ ⊨ₚ (rec: f x := e1) ≤log≤ (rec: f x := e2) :(τ -{ ρ }-> κ)).
  Proof.
    iIntros (???) "#He".
    iIntros (η μ δ ξ Hδ). push_lr.
    iIntros "!# %γ HΓ /=".
    pose proof (multi_env_sound Γ H η μ δ ξ) as HMultiE.
    iDestruct "HΓ" as "#HΓ".
    iSpecialize ("He" $! η μ δ ξ Hδ). push_lr.
    rewrite /prel /=.
    iExists _,_,1%nat,1%nat.
    iSplit; first (iPureIntro; repeat split; by apply pure_recc).
    iLöb as "IH". rewrite /sem_ty_mbang /sem_ty_arr /=.
    iIntros "!# % % Hτ". simpl.
    iApply brel_pure_step_r; first done.
    iApply brel_pure_step_later; first done. iModIntro.
    destruct f; destruct x; simpl.
    - iApply brel_wand;
       [by iApply "He"|iIntros (??) "!# ($&_)"].
    - rewrite -!subst_map_insert.
      assert (w1 = fst (w1, w2) ∧ w2 = snd (w1, w2)) as (->&->) by done.
      rewrite -!fmap_insert. simpl. 
      iApply (brel_wand with "[Hτ]"); [iApply "He"|iIntros (??) "!# ($&_)"].
      solve_env. rewrite -env_sem_typed_insert; [iApply "HΓ" |].
      simpl. eapply ctx_dom_env_dom. auto.
    - rewrite -!subst_map_insert.
      assert ((rec: _ _ := _)%V = fst (_,(rec: s <> := subst_map (delete s (snd <$> γ)) e2)%V)) as -> by done.
       assert ((rec: s <> := subst_map _ e2)%V = snd ((rec: s <> := subst_map (delete s (fst <$> γ)) e1)%V, _)) as -> by done.
         rewrite -!fmap_insert; simpl. solve_env. admit.
         (*iApply brel_wand.
         +  iApply "He". [iApply "He"|iIntros (??) "!# ($&_)"].
         solve_env. *)
       - assert (s ≠ s0) by (intros ?; simplify_eq).
         do 2 (rewrite subst_subst_ne; last done;
               rewrite -subst_map_insert;
               rewrite -delete_insert_ne; last done;
               rewrite -subst_map_insert).
         assert (w1 = fst (w1, w2) ∧ w2 = snd (w1, w2)) as (->&->) by done.
         rewrite -!fmap_insert; simpl.
         assert ((rec: _ _ := _)%V = fst (_,(rec: s s0 := subst_map (delete s0 (delete s (snd <$> γ))) e2)%V)) as -> by done.
         assert ((rec: s s0 := subst_map _ e2)%V = snd ((rec: s s0 := subst_map (delete s0 (delete s (fst <$> γ)))  e1)%V, _)) as -> by done.
         rewrite -!fmap_insert; simpl. admit.
         (*iApply (brel_wand with "[Hτ]"); [iApply "He"|iIntros (??) "!# ($ &_)"].
         solve_env.
         by do 2 (rewrite -env_sem_typed_insert; last done). *)
  Admitted.
  
  Lemma interp_c_bin_log_pure_typed_ufun_mode Δ Γ τ κ ρ m f x e1 e2 `{le.MultiC Γ} :
    x ∉ (ctx_dom Γ) -> f ∉ (ctx_dom Γ) ->
    match f with BNamed f => BNamed f ≠ x | BAnon => True end →
    ⊢ (〈Δ; (x, τ) ::? (f, (TBang MS (TArrow τ ρ κ))) ::? Γ〉 ⊨ₜ e1 ≤log≤ e2 :ρ:κ⫤[]) -∗
    (⟨Δ; Γ ⟩ ⊨ₚ (rec: f x := e1) ≤log≤ (rec: f x := e2) :(τ -{ ρ }-[ m ]-> κ)).
  Proof.
    iIntros (???) "#He". 
    iApply bin_log_pure_typed_mbang_MS_weaken.
    by iApply (interp_c_bin_log_pure_typed_ufun with "He"). 
  Qed.
  
  Lemma interp_c_fun_rec Δ Γ Γ' ρ τ κ e f x m `{le.MultiC Γ} :
    x ∉ (ctx_dom Γ) -> f ∉ (ctx_dom Γ) ->
    match f with BNamed f => BNamed f ≠ x | BAnon => True end →
    ⊢ (〈Δ; ((x, τ) ::? (f, TBang m (TArrow τ ρ κ)) ::? Γ)〉 ⊨ₜ e ≤log≤ e :ρ:κ⫤[]) -∗
    (〈Δ; ctx_append Γ Γ'〉 ⊨ₜ (rec: f x := e) ≤log≤ (rec: f x := e) :RNil:(τ -{ ρ }-[ m ]-> κ)⫤Γ').
  Proof. iIntros (Hx Hf Hfx) "#He".
         iApply bin_log_pure_typed_oval.
         iApply (interp_c_bin_log_pure_typed_ufun_mode Δ Γ τ κ ρ m f x e e Hx Hf Hfx).
         iIntros (η μ δ ξ Hδ). push_lr.
         unfold bin_log_related.
         iSpecialize ("He" $! η μ δ ξ Hδ).
         iApply (sem_typed_sub_env with "[] He").
         destruct f as [|sf]; destruct x as [|sx]; simpl.
         - iApply env_le_refl.
         - iApply env_le_refl.
         - iApply env_le_cons;
             [iApply env_le_refl| iApply ty_le_mbang_elim_MS].
         - iApply env_le_trans; [iApply env_le_refl | iApply env_le_cons].
           { iApply env_le_cons.
             + iApply env_le_refl.
             + iApply ty_le_mbang_elim_MS.
           }
           { iApply ty_le_refl. }
           Unshelve.
           + eapply H.
  Qed.

  Lemma bin_log_swap_ctx_second Δ Γ x y τ1 τ2 κ ρ e1 e2 :
   ⊢ (〈Δ; (y, τ2) :: (x, τ1) :: Γ〉 ⊨ₜ e1 ≤log≤ e2 :ρ:κ⫤[]) -∗
   (〈Δ; (x, τ1) :: (y, τ2) :: Γ〉 ⊨ₜ e1 ≤log≤ e2 :ρ:κ⫤[]).
  Proof.
    iIntros "#H".
    iIntros (η μ δ ξ Hδ).
    push_lr.
    iSpecialize ("H" $! η μ δ ξ Hδ).
    iApply sem_typed_sub.
    { iApply env_le_swap_second. }
    { iApply env_le_refl. }
    { iApply row_le_refl. }
    { iApply ty_le_refl. }
    { iApply "H". }
  Qed.
 
  Lemma interp_c_app_gen Δ Γ1 Γ2 Γ3 ρ ρ' ρ'' τ κ e1 e1' e2 e2' :
    (∀ η μ δ ξ, (interp._row η μ δ ρ' ξ) ᵣ⪯ₜ (interp._ty η μ δ τ ξ)) ->
    (∀ η μ δ ξ, (interp._row η μ δ ρ'' ξ) ᵣ⪯ₑ
               ((λ '(s, τ), (s, interp._ty η μ δ τ ξ)) <$> Γ3)) ->
             
    ⊢ (∀ η μ δ ξ, (interp._row η μ δ ρ' ξ) ≤ᵣ (interp._row η μ δ ρ ξ)) -∗
      (∀ η μ δ ξ, (interp._row η μ δ ρ'' ξ) ≤ᵣ (interp._row η μ δ ρ ξ)) -∗ 
      (〈Δ; Γ2〉 ⊨ₜ e1 ≤log≤ e2 :ρ':(τ -{ ρ''}-∘ κ)⫤Γ3) -∗
      (〈Δ; Γ1〉 ⊨ₜ e1'≤log≤ e2':ρ:τ⫤Γ2) -∗
      (〈Δ; Γ1〉 ⊨ₜ e1 e1' ≤log≤ e2 e2' :ρ:κ⫤Γ3).
  Proof. iIntros (??) "#Hρ'ρ #Hρ''ρ #Hee1 #Hee2".
         iIntros (η μ δ ξ Hδ). push_lr.
         iIntros  "!# %γ HΓ1 /=".
         iSpecialize ("Hρ'ρ" $! η μ δ ξ).
         iSpecialize ("Hρ''ρ" $! η μ δ ξ).
         iSpecialize ("Hee1" $! η μ δ ξ).
         iSpecialize ("Hee2" $! η μ δ ξ).
         iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
         iDestruct ("Hee2" with "[%]") as "Harg"; [eapply Hδ|].
         iDestruct ("Hee1" with "[%]") as "Hlam"; [eapply Hδ|].
         iDestruct ("Harg" with "HΓ1") as "He2brel".
         iApply (brel_wand with "He2brel").
         iIntros "!# % % (Hτ & HΓ2) /=".
         iApply (brel_bind [AppLCtx _] [AppLCtx _]); [iApply traversable_to_iThy|iApply "Hρ'ρ"|].
         iApply (brel_wand with "[Hτ HΓ2]").
         { iApply (brel_mono_on_prop with "[][Hτ]"); [iApply row_type_sub| iApply "Hτ"|]. by iApply "Hlam". }
        iIntros "!# % % ((Hfun & HΓ3) & Hτ) /=".
        iDestruct ("Hfun" with "Hτ") as "Hfun".
        iApply brel_introduction_mono; [iApply "Hρ''ρ"|].
        iApply (brel_wand with "[Hfun HΓ3]").
        { iApply (brel_mono_on_prop with "[][HΓ3]"); [iApply row_env_sub|iApply "HΓ3" |done]. }
        iIntros "!# % % ($&$)".
  Qed.

  (*Lemma interp_c_type_cong Δ Γ1 Γ2 e1 e2 ρ τ τ' :
   (∀ η μ δ ξ, ((interp._ty η μ δ τ ξ) ≡ (interp._ty η μ δ τ' ξ))%stdpp) -> 
    ⊢ (〈Δ; Γ1〉 ⊨ₜ e1 ≤log≤ e2 :ρ:τ'⫤Γ2) -∗
    (*(〈Δ; Γ1〉 ⊨ₜ e1 ≤log≤ e2 :ρ:τ⫤Γ2). *)
    (〈Δ; Γ1〉 ⊨ₜ e1 ≤log≤ e2 :ρ:Autosubst_Classes.subst
             (Autosubst_Basics.scons τ' Autosubst_Classes.ids) τ⫤Γ2).
  Proof. intros Hτ.
         iIntros "Hτ'".
         iIntros (η μ δ ξ Hδ).
         iSpecialize ("Hτ'" $! η μ δ ξ).
         specialize (Hτ η μ δ ξ).
         About Autosubst_Basics.scons.
         rewrite (sem_typed_type_proper _ _ _ _ _ _ _ Hτ).
         iApply "Hτ'".
         iPureIntro. auto.
  Qed.*)
  
(*Lemma interp_c_row_elim

Lemma interp_c_mode_elim *)
  Lemma interp_c_alloc_ref Δ Γ1 Γ2 ρ τ e1 e2:
    ⊢ (〈Δ; Γ1〉 ⊨ₜ e1 ≤log≤ e2 :ρ: τ⫤Γ2) -∗
    (〈Δ; Γ1〉 ⊨ₜ ref e1 ≤log≤ ref e2 :ρ:ref τ⫤Γ2).
  Proof.
    iIntros "#He".
    iIntros (η μ δ ξ Hδ).
    iIntros "!# %γ HΓ1 //=".
    iApply (brel_bind [AllocNRCtx _] [AllocNRCtx _]); [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
    iApply (brel_wand with "[HΓ1]"); first by iApply "He".
    iIntros "!# % % (Hτ & HΓ2) //=".
    iApply brel_alloc_l. iIntros "!> % Hl1".
    iApply brel_alloc_r. iIntros "% Hl2".
    iApply brel_value. iIntros. iFrame. done.
  Qed.
  
  Lemma interp_c_load_ref Δ Γ x τ :
    ⊢ (〈Δ; (x, TRef τ) ::  Γ〉 ⊨ₜ (Load x) ≤log≤ (Load x) :RNil: τ⫤((x, TRef ⊤) ::Γ)).
  Proof.
    iIntros (η μ δ ξ Hδ).
    push_lr. simpl. rewrite !lbl_resolve_var.
    iIntros "%γ !# //= [%vv (%Hrw & (%w1 & %w2 & %Heq1 & %Heq2 & (%l1 & %l2 & Hl1 & Hl2 & Hτ)) & HΓ)]".
    destruct vv as (v1, v2). simpl in *. simplify_eq.
    rewrite !lookup_fmap. rewrite Hrw //=.
    iApply (brel_load_l with "Hl1"). iIntros "!> Hl1".
    iApply (brel_load_r with "Hl2"). iIntros "Hl2".
    iApply brel_value. iFrame. solve_env.
  Qed.
  
  Lemma interp_c_store Δ Γ1 Γ2 x e1 e2 τ κ ι ρ :
    ⊢ (〈Δ; (x, TRef τ) ::  Γ1〉 ⊨ₜ e1 ≤log≤ e2 :ρ: ι⫤((x, TRef κ) :: Γ2)) -∗
    (〈Δ; (x, TRef τ) ::  Γ1〉 ⊨ₜ (x <- e1) ≤log≤ (x <- e2) :ρ: TUnit⫤((x, TRef ι) :: Γ2)).
  Proof.
    iIntros "#He".
    iIntros (η μ δ ξ Hδ).
    push_lr. rewrite !lbl_resolve_var. simpl.
    iSpecialize ("He" $! η μ δ ξ Hδ).    
    iIntros "!# %γ //= HΓ1 //=".
    iApply (brel_bind [StoreRCtx _] [StoreRCtx _]); [iApply traversable_to_iThy|iApply to_iThy_le_refl|]. simpl.
    iApply (brel_wand with "[HΓ1]"); first by iApply "He".
    rewrite !lookup_fmap.
    iIntros "!# % % (Hι & [%ll (%Hrw & (% & % & % & % & (%&%&Hl1&Hl2&Hκ)) & HΓ2)]) //=".
    destruct ll as (l1', l2'). simpl in *. simplify_eq. rewrite Hrw.
    iApply (brel_store_l with "Hl1"). iIntros "!> Hl1".
    iApply (brel_store_r with "Hl2"). iIntros "Hl2".
    iApply brel_value.
    solve_env.
  Qed.
  
  Lemma interp_c_alloctape Δ Γ1 Γ2 ρ e1 e2 :
    ⊢ (〈Δ; Γ1〉 ⊨ₜ e1 ≤log≤ e2 :ρ:TInt⫤Γ2) -∗
    (〈Δ; Γ1〉 ⊨ₜ alloc e1 ≤log≤ alloc e2 :ρ:TTape⫤Γ2).
  Proof. iIntros "#He".
         iIntros (η μ δ ξ Hδ). simpl.
         iSpecialize ("He" $! η μ δ ξ Hδ).
         iIntros "%γ !# //= HΓ1".
         iApply (brel_bind [AllocTapeCtx] [AllocTapeCtx]);
          [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
         iApply (brel_wand with "[HΓ1]"); first by iApply "He".
         iIntros "!# % % ((%z & -> & ->) & HΓ2) //=".
         iApply (brel_alloctape_l _ (Z.to_nat z)). iIntros "!> %α1 Hα1".
         iApply (brel_alloctape_r _ (Z.to_nat z)). iIntros "%α2 Hα2".
         iDestruct (tapeN_to_empty with "Hα1") as "Hα1".
         unshelve iMod (inv_alloc (logN.@(α1,α2)) _
            (α1 ↪ (Z.to_nat z; []) ∗ α2 ↪ₛ (Z.to_nat z; []))%I with "[Hα1 Hα2]") as "#Hinv".
         { iFrame. }
         iApply brel_value. iIntros. iFrame.
        iExists α1, α2, (Z.to_nat z). by iFrame "Hinv".
  Qed.
  
  Lemma interp_c_rand Δ Γ1 Γ2 Γ3 ρ e1 e2 e1' e2' :
    ⊢ (〈Δ; Γ2〉 ⊨ₜ e1 ≤log≤ e1' :ρ:TInt⫤Γ3) -∗
      (〈Δ; Γ1〉 ⊨ₜ e2 ≤log≤ e2' :ρ:TTape⫤Γ2) -∗                             
      (〈Δ; Γ1〉 ⊨ₜ rand(e2) e1 ≤log≤ rand(e2') e1' :ρ:TNat⫤Γ3).
  Proof. iIntros "#He1 #He2".
         iIntros (η μ δ ξ Hδ). push_lr.
         iSpecialize ("He1" $! η μ δ ξ Hδ).
         iSpecialize ("He2" $! η μ δ ξ Hδ).
         iIntros "%γ !# //= HΓ1".
         iApply (brel_bind [RandRCtx _] [RandRCtx _]);
          [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
         iApply (brel_wand with "[HΓ1]"); first by iApply "He2".
         iIntros "!# % % ((%α1 & %α2 & %N & -> & -> & #Hinv) & HΓ2) //=".
         iApply (brel_bind [RandLCtx _] [RandLCtx _]);
          [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
         iApply (brel_wand with "[HΓ2]"); first by iApply "He1".
         iIntros "!# % % ((%z & -> & ->) & HΓ3) //=".
         iApply (brel_atomic_l _ []).
         iIntros (K') "Hj".
         iMod (inv_acc _ (logN.@(α1,α2)) with "Hinv") as "[(>Hα1 & >Hα2) Hclose]";
         first done.
         iModIntro.
         iApply (wp_couple_rand_lbl_rand_lbl _ (λ n : nat, n)
              with "[$Hα1 $Hα2 $Hj]"); [done|].
         iIntros (n) "!> (Hα1 & Hα2 & Hj & %Hlt)".
         iMod ("Hclose" with "[$Hα1 $Hα2]") as "_".
         iModIntro. iExists _. iFrame.
         iApply brel_value. iIntros. iFrame.
         iExists n. iModIntro. by iSplit.
  Qed.
  
  Lemma interp_c_randu Δ Γ1 Γ2 Γ3 ρ e1 e1' e2 e2' :
    ⊢ (〈Δ; Γ2〉 ⊨ₜ e1 ≤log≤ e1' :ρ:TInt⫤Γ3) -∗
      (〈Δ; Γ1〉 ⊨ₜ e2 ≤log≤ e2' :ρ:TUnit⫤Γ2) -∗ 
      (〈Δ; Γ1〉 ⊨ₜ rand(e2) e1 ≤log≤ rand(e2') e1' :ρ:TNat⫤Γ3).
  Proof. iIntros "#He1 #He2".
         iIntros (η μ δ ξ Hδ). push_lr.
         iSpecialize ("He1" $! η μ δ ξ Hδ).
         iSpecialize ("He2" $! η μ δ ξ Hδ).
         iIntros "%γ !# //= HΓ1".
         iApply (brel_bind [RandRCtx _] [RandRCtx _]);
          [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
         iApply (brel_wand with "[HΓ1]"); first by iApply "He2".
         iIntros "!# % % ((-> & ->) & HΓ2) //=".
         iApply (brel_bind [RandLCtx _] [RandLCtx _]);
          [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
         iApply (brel_wand with "[HΓ2]"); first by iApply "He1".
         iIntros "!# % % ((%z & -> & ->) & HΓ3) //=".
         iApply (brel_couple_rand_rand _ (Z.to_nat z) (λ n : nat, n) z [] []); [done|].
         iIntros (n) "%Hle". iApply brel_value. iIntros. iFrame.
         iExists n. iModIntro. by iSplit.
  Qed.

  (*Lemma interp_c_fold Δ Γ1 Γ2 e1 e2 ρ τ :
    ⊢ 〈Δ; Γ1〉 ⊨ₜ e1 ≤log≤ e2 :ρ:(TRec τ)⫤Γ2.
   
  Lemma interp_c_unfold 
  
  Lemma interp_c_pack
           ⊢ 〈Δ; Γ1〉 ⊨ₜ e ≤log≤ e :ρ:(∃: τ)⫤Γ2
Lemma interp_c_unpack *)
 
  Lemma interp_c_effect_gen Δ Γ1 Γ2 s e1 e2 ρ τ :
    vars._fresh s (Γ1 ++ Γ2) ρ τ ->
    ⊢ (〈<[s:=()]> Δ; Γ1〉 ⊨ₜ e1 ≤log≤ e2 :(RCons (SAbs s) ρ):τ⫤Γ2) -∗
     (* 〈Δ; Γ1〉 ⊨ₜ (lbl_subst s l1 e1) ≤log≤ (lbl_subst s l2 e2):(RCons (SAbs s) ρ):τ⫤Γ2) -∗ *)
    (〈Δ; Γ1〉 ⊨ₜ (effect s e1) ≤log≤ (effect s e2) :ρ:τ⫤Γ2).
  Proof. iIntros "%H #He".
         iIntros (η μ δ ξ Hδ). simpl.
         iApply sem_typed_effect_gen.
         iIntros (l1 l2).
         rewrite /bin_log_related.
         iSpecialize ("He" $! η μ (<[s:=(l1,l2)]>δ) ξ).
         iSpecialize ("He" with "[]").
         { iPureIntro. rewrite !dom_insert_L. set_solver. }
         rewrite (resolve_map_insert fst Δ δ s (l1,l2))
              (resolve_map_insert snd Δ δ s (l1,l2)).
        rewrite -!lbl_resolve_insert_subst.
        destruct H as (Hctx & Hrow & Hty).
        assert (s ∉ vars._ctx Γ1) as HΓ1
        by (intros Hin; apply Hctx;
            rewrite /vars._ctx fmap_app union_list_app_L; set_solver).
       assert (s ∉ vars._ctx Γ2) as HΓ2
        by (intros Hin; apply Hctx;
            rewrite /vars._ctx fmap_app union_list_app_L; set_solver).
      assert (interp._ty η μ (<[s:=(l1,l2)]>δ) τ ξ ≡ interp._ty η μ δ τ ξ)
        as Hτeq by (by apply (interp.ty_delta_irrel δ s (l1,l2))).
      assert (interp._row η μ (<[s:=(l1,l2)]>δ) (RCons (SAbs s) ρ) ξ
              ≡ sem_row.sem_row_cons (sem_sig.sem_sig_bottom l1 l2)
                  (interp._row η μ δ ρ ξ)) as Hρeq.
      { (*subst (RCons (SAbs s) ρ);*) simpl.
        rewrite (interp.row_delta_irrel δ s (l1,l2) ρ η μ ξ Hrow)
                lookup_total_insert_eq /=. reflexivity. }
      assert (∀ (Γ0 : list (string*type)), s ∉ vars._ctx Γ0 →
        env_equiv_pw
          ((λ '(s0, τ0), (s0, interp._ty η μ δ τ0 ξ)) <$> Γ0)
          ((λ '(s0, τ0), (s0, interp._ty η μ (<[s:=(l1,l2)]>δ) τ0 ξ))
             <$> Γ0)) as Henv.
      { intros Γ0 HΓ0. rewrite /env_equiv_pw.
        induction Γ0 as [|[x α] Γ0' IH]; simpl; [constructor|].
        constructor.
        - split; [done|]. symmetry.
          apply (interp.ctx_elem_delta_irrel δ s (l1,l2) ((x,α)::Γ0') x α);
            [done|by left].
        - apply IH. intros Hin. apply HΓ0.
          rewrite /vars._ctx /= in Hin |- *. set_solver. }
      iApply (sem_typed_row_cong _ _ _ _ _ _ _ (symmetry Hρeq)).
      iApply (sem_typed_type_cong _ _ _ _ _ _ _ (symmetry Hτeq)).
      iApply (sem_typed_env_cong _ _ _ _ _ _ _ _ (Henv Γ1 HΓ1) (Henv Γ2 HΓ2)).
      iApply "He".
   Qed.
 
(*Lemma interp_c_effect_do *)
  Lemma interp_c_deephandle_os Δ Γ1 Γ2 Γ3 τ τ' ι κ r h e (*ρ ρ'*) ρ0 x y k s σ `{le.MultiC Γ3} :
       let ρ := RCons σ ρ0 in
       let ρ' := RCons (SFlip OS (SSig s ι κ)) ρ0 in
       let Γ3' := <[ x :=c ι]> (<[ k:=c κ -{ rename_type_row (Autosubst_Basics.lift 1%nat) ρ }-[ OS]-> Autosubst_Classes.subst (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat))
                           τ']> ((λ '(x0, α0), (x0, Autosubst_Classes.subst
                                                      (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) α0)) <$> Γ3)) in
       let Γ3'' := ( (λ '(x0, α0),
            (x0, Autosubst_Classes.subst
                   (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) α0)) <$> Γ3 ) in
       (match x with BNamed s => s ∉ ctx_dom Γ2 | BAnon => True end) →
       (match x with BNamed s => s ∉ ctx_dom Γ3 | BAnon => True end) →
       (match k with BNamed s => s ∉ ctx_dom Γ3 | BAnon => True end) →
       (match x, k with BNamed a, BNamed b => a ≠ b | _, _ => True end) →
       (match y with BNamed s => s ∉ ctx_dom Γ2 | BAnon => True end) →
       (match y with BNamed s => s ∉ ctx_dom Γ3 | BAnon => True end) →
       Δ !! s = Some () ->
       le.eff_name_from_sig σ = s ->
        ⊢ (〈Δ; <[ y :=c τ ]> (ctx_append Γ2 Γ3)〉 ⊨ₜ r ≤log≤ r :ρ:τ'⫤Γ3) (*Ht2*) -∗
          (〈Δ; Γ3'〉 ⊨ₜ h ≤log≤ h :rename_type_row (Autosubst_Basics.lift 1%nat) ρ:
         Autosubst_Classes.subst
           (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) τ'⫤Γ3'') -∗
        (*Ht3 *) 
          (〈Δ; Γ1〉 ⊨ₜ e ≤log≤ e :ρ':τ⫤Γ2) (* Ht1*) -∗
    (〈Δ; ctx_append Γ1 Γ3〉 ⊨ₜ
      (handle: e with
       | effect (EffName s) x, rec k => h
       | return y => r
       end) ≤log≤
      (handle: e with
       | effect (EffName s) x, rec k => h
       | return y => r
       end) :ρ:τ'⫤Γ3).
  Proof.
        simpl.
        iIntros (??????) "%H0' %H1' #Ht2 #Ht3 #Ht1".
        iIntros (η μ δ ξ Hδ).
        rewrite !lbl_resolve_handle_name.
        rewrite !resolve_map_lookup H0' /=.
        rewrite !lbl_resolve_rec.
        unfold ctx_append. rewrite fmap_app.
        pose proof (multi_env_sound Γ3 H η μ δ ξ) as HME.
        pose proof (sig_labels_eff_name σ η μ δ ξ) as Hlbl. simpl.
        rewrite H1' in Hlbl.
        iApply (sem_typed_deep_handler_OS (δ !!! s)
                  (λ α, interp._ty (α :: η) μ δ ι ξ)
                  (λ α, interp._ty (α :: η) μ δ κ ξ)
                  (interp._ty η μ δ τ ξ)
                  (interp._ty η μ δ τ' ξ)
                  (interp._eff_sig η μ δ σ ξ)
                  (interp._row η μ δ ρ0 ξ)
                  _ _ _ x y k _ _ _ _ _ _
                  _ _ _ _ _ _ Hlbl).
        1:{
            iApply ("Ht1" $! η μ δ ξ Hδ). }
        1:{ iIntros (α). 
          iSpecialize ("Ht3" $! (α :: η) μ δ ξ Hδ).
          iEval (cbn [ctx_insert fmap list_fmap]) in "Ht3".
          iApply (sem_typed_row_cong _ _ _ _ _ _ _
                    (symmetry (row_tweaken (RCons σ ρ0) α η μ δ ξ))).
          iApply (sem_typed_type_cong _ _ _ _ _ _ _
                    (symmetry (ty_tweaken τ' α η μ δ ξ))).
          assert (Htail : ∀ (Γ0 : ctx), env_equiv_pw
                    ((λ '(s0, τ0), (s0, interp._ty η μ δ τ0 ξ)) <$> Γ0)
                    ((λ '(s0, τ0), (s0, interp._ty (α :: η) μ δ τ0 ξ)) <$>
                       ((λ '(x0, α0), (x0, Autosubst_Classes.subst
                           (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) α0))
                          <$> Γ0)))
            by (intros Γ0; induction Γ0 as [|[z β] Γ0' IH]; simpl; [constructor|];
                constructor; [split; [done|]|exact IH];
                simpl; symmetry; apply (ty_tweaken β α η μ δ ξ)).
          assert (Hhead : (interp._ty (α :: η) μ δ
                       (κ -{ rename_type_row (Autosubst_Basics.lift 1%nat) (RCons σ ρ0) }-[ OS
                        ]-> Autosubst_Classes.subst
                              (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) τ')
                       ξ)
                    ≡ sem_types.sem_ty_mbang syntax.OS
                (sem_types.sem_ty_arr
                   (sem_row.sem_row_cons (interp._eff_sig η μ δ σ ξ)
                      (interp._row η μ δ ρ0 ξ))
                   (interp._ty (α :: η) μ δ κ ξ) (interp._ty η μ δ τ' ξ))).
          { change (interp._ty (α :: η) μ δ
                       (κ -{ rename_type_row (Autosubst_Basics.lift 1%nat) (RCons σ ρ0) }-[ OS
                        ]-> Autosubst_Classes.subst
                              (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) τ')
                       ξ)
              with (sem_types.sem_ty_mbang syntax.OS
                (sem_types.sem_ty_arr
                   (interp._row (α :: η) μ δ
                      (rename_type_row (Autosubst_Basics.lift 1%nat) (RCons σ ρ0)) ξ)
                   (interp._ty (α :: η) μ δ κ ξ)
                   (interp._ty (α :: η) μ δ (Autosubst_Classes.subst
                       (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) τ') ξ))).
            rewrite (row_tweaken (RCons σ ρ0) α η μ δ ξ) (ty_tweaken τ' α η μ δ ξ).
            reflexivity. }
          destruct x as [|sx], k as [|sk]; simpl;
            unshelve (iApply (sem_typed_env_cong _ _ _ _ _ _ _ _ _ (Htail Γ3));
              iApply "Ht3");
            repeat (constructor; [ split; [ reflexivity
                | first [ exact (symmetry Hhead) | reflexivity ] ] | ]);
            try exact (Htail Γ3). }
        1:{ (*apply fundamental in Ht2. iPoseProof Ht2 as "Ht". *)
          iSpecialize ("Ht2" $! η μ δ ξ Hδ).
          iEval (cbn [ctx_insert ctx_append fmap list_fmap]) in "Ht2".
          destruct y as [|sy]; simpl; rewrite -fmap_app; iApply "Ht2". }
         Unshelve.
        all: try done; repeat case_match; simpl in *;
          first [ exact I | congruence | apply ctx_dom_env_dom; assumption ].
Qed.

  Lemma interp_c_deephandle_ms
           Δ Γ1 Γ2 Γ3 τ τ' ι κ r h e (*ρ ρ'*) ρ0 x y k s σ `{le.MultiC Γ3} :
       let ρ := RCons σ ρ0 in
       let ρ' := RCons (SFlip MS (SSig s ι κ)) ρ0 in
       let Γ3' := <[ x :=c ι]> (<[ k:=c κ -{ rename_type_row (Autosubst_Basics.lift 1%nat) ρ }-[ MS]-> Autosubst_Classes.subst (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat))
                           τ']> ((λ '(x0, α0), (x0, Autosubst_Classes.subst
                                                      (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) α0)) <$> Γ3)) in
       let Γ3'' := ( (λ '(x0, α0),
            (x0, Autosubst_Classes.subst
                   (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) α0)) <$> Γ3 ) in
       (match x with BNamed s => s ∉ ctx_dom Γ2 | BAnon => True end) →
       (match x with BNamed s => s ∉ ctx_dom Γ3 | BAnon => True end) →
       (match k with BNamed s => s ∉ ctx_dom Γ3 | BAnon => True end) →
       (match x, k with BNamed a, BNamed b => a ≠ b | _, _ => True end) →
       (match y with BNamed s => s ∉ ctx_dom Γ2 | BAnon => True end) →
       (match y with BNamed s => s ∉ ctx_dom Γ3 | BAnon => True end) →
       Δ !! s = Some () ->
       le.eff_name_from_sig σ = s ->
        ⊢ (〈Δ; <[ y :=c τ ]> (ctx_append Γ2 Γ3)〉 ⊨ₜ r ≤log≤ r :ρ:τ'⫤Γ3) (*Ht2*) -∗
          (〈Δ; Γ3'〉 ⊨ₜ h ≤log≤ h :rename_type_row (Autosubst_Basics.lift 1%nat) ρ:
         Autosubst_Classes.subst
           (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) τ'⫤Γ3'') -∗
        (*Ht3 *) 
          (〈Δ; Γ1〉 ⊨ₜ e ≤log≤ e :ρ':τ⫤Γ2) (* Ht1*) -∗         
    (〈Δ; ctx_append Γ1 Γ3〉 ⊨ₜ
      (handle: e with
       | effect (EffName s) x, rec k as multi => h
       | return y => r
       end)
    ≤log≤
      (handle: e with
       | effect (EffName s) x, rec k as multi => h
       | return y => r
       end) :ρ:τ'⫤Γ3).
  Proof.
        simpl.
        iIntros (??????) "%H0' %H1' #Ht2 #Ht3 #Ht1".
        iIntros (η μ δ ξ Hδ).
        rewrite !lbl_resolve_handle_name.
        rewrite !resolve_map_lookup H0' /=.
        rewrite !lbl_resolve_rec.
        unfold ctx_append. rewrite fmap_app.
        pose proof (multi_env_sound Γ3 H η μ δ ξ) as HME.
        pose proof (sig_labels_eff_name σ η μ δ ξ) as Hlbl.
        rewrite H1' in Hlbl.
        iApply (sem_typed_deep_handler_MS (δ !!! s)
                  (λ α, interp._ty (α :: η) μ δ ι ξ)
                  (λ α, interp._ty (α :: η) μ δ κ ξ)
                  syntax.MS
                  (interp._ty η μ δ τ ξ)
                  (interp._ty η μ δ τ' ξ)
                  (interp._eff_sig η μ δ σ ξ)
                  (interp._row η μ δ ρ0 ξ)
                  _ _ _ x y k _ _ _ _ _ _
                  _ _ _ _ _ _ Hlbl).
        1:{ 
            iApply ("Ht1" $! η μ δ ξ Hδ). }
        1:{ iIntros (α).
          iSpecialize ("Ht3" $! (α :: η) μ δ ξ Hδ).
          iEval (cbn [ctx_insert fmap list_fmap]) in "Ht3".
          iApply (sem_typed_row_cong _ _ _ _ _ _ _
                    (symmetry (row_tweaken (RCons σ ρ0) α η μ δ ξ))).
          iApply (sem_typed_type_cong _ _ _ _ _ _ _
                    (symmetry (ty_tweaken τ' α η μ δ ξ))).
          assert (Htail : ∀ (Γ0 : ctx), env_equiv_pw
                    ((λ '(s0, τ0), (s0, interp._ty η μ δ τ0 ξ)) <$> Γ0)
                    ((λ '(s0, τ0), (s0, interp._ty (α :: η) μ δ τ0 ξ)) <$>
                       ((λ '(x0, α0), (x0, Autosubst_Classes.subst
                           (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) α0))
                          <$> Γ0))) by
            (intros Γ0; induction Γ0 as [|[z β] Γ0' IH]; simpl; [constructor|];
                constructor; [split; [done|]|exact IH];
                simpl; symmetry; apply (ty_tweaken β α η μ δ ξ)).
          assert (Hhead : (interp._ty (α :: η) μ δ
                       (κ -{ rename_type_row (Autosubst_Basics.lift 1%nat) (RCons σ ρ0) }-[ MS
                        ]-> Autosubst_Classes.subst
                              (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) τ')
                       ξ)
                    ≡ sem_types.sem_ty_mbang syntax.MS
                (sem_types.sem_ty_arr
                   (sem_row.sem_row_cons (interp._eff_sig η μ δ σ ξ)
                      (interp._row η μ δ ρ0 ξ))
                   (interp._ty (α :: η) μ δ κ ξ) (interp._ty η μ δ τ' ξ))).
          { change (interp._ty (α :: η) μ δ
                       (κ -{ rename_type_row (Autosubst_Basics.lift 1%nat) (RCons σ ρ0) }-[ MS
                        ]-> Autosubst_Classes.subst
                              (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) τ')
                       ξ)
              with (sem_types.sem_ty_mbang syntax.MS
                (sem_types.sem_ty_arr
                   (interp._row (α :: η) μ δ
                      (rename_type_row (Autosubst_Basics.lift 1%nat) (RCons σ ρ0)) ξ)
                   (interp._ty (α :: η) μ δ κ ξ)
                   (interp._ty (α :: η) μ δ (Autosubst_Classes.subst
                       (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) τ') ξ))).
            rewrite (row_tweaken (RCons σ ρ0) α η μ δ ξ) (ty_tweaken τ' α η μ δ ξ).
            reflexivity. }
          destruct x as [|sx], k as [|sk]; simpl;
            unshelve (iApply (sem_typed_env_cong _ _ _ _ _ _ _ _ _ (Htail Γ3));
              iApply "Ht3");
            repeat (constructor; [ split; [ reflexivity
                | first [ exact (symmetry Hhead) | reflexivity ] ] | ]);
            try exact (Htail Γ3). }
        1:{ 
          iSpecialize ("Ht2" $! η μ δ ξ Hδ).
          iEval (cbn [ctx_insert ctx_append fmap list_fmap]) in "Ht2".
          destruct y as [|sy]; simpl; rewrite -fmap_app; iApply "Ht2". }
        Unshelve.
        all: try done; try (repeat case_match); simpl in *;
          first [ exact I | congruence | apply ctx_dom_env_dom; assumption ].
Qed.
          
  Lemma interp_c_shallowhandle_os  Δ Γ1 Γ2 Γ3 τ τ' ι κ r h e (*ρ ρ'*) ρ0 x y k s σ `{le.MultiC Γ3} :
       let ρ := RCons σ ρ0 in
       let ρ' := RCons (SFlip OS (SSig s ι κ)) ρ0 in
       let Γ3' := <[ x :=c ι]> (<[ k:=c κ -{ rename_type_row (Autosubst_Basics.lift 1%nat) ρ' }-[ OS]-> Autosubst_Classes.subst (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat))
                           τ]> ((λ '(x0, α0), (x0, Autosubst_Classes.subst
                                                      (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) α0)) <$> Γ3)) in
       let Γ3'' := ( (λ '(x0, α0),
            (x0, Autosubst_Classes.subst
                   (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) α0)) <$> Γ3 ) in
       (match x with BNamed s => s ∉ ctx_dom Γ2 | BAnon => True end) →
       (match x with BNamed s => s ∉ ctx_dom Γ3 | BAnon => True end) →
       (match k with BNamed s => s ∉ ctx_dom Γ3 | BAnon => True end) →
       (match x, k with BNamed a, BNamed b => a ≠ b | _, _ => True end) →
       (match y with BNamed s => s ∉ ctx_dom Γ2 | BAnon => True end) →
       (match y with BNamed s => s ∉ ctx_dom Γ3 | BAnon => True end) →
       Δ !! s = Some () ->
       le.eff_name_from_sig σ = s ->
        ⊢ (〈Δ; <[ y :=c τ ]> (ctx_append Γ2 Γ3)〉 ⊨ₜ r ≤log≤ r :ρ:τ'⫤Γ3) (*Ht2*) -∗
          (〈Δ; Γ3'〉 ⊨ₜ h ≤log≤ h :rename_type_row (Autosubst_Basics.lift 1%nat) ρ:
         Autosubst_Classes.subst
           (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) τ'⫤Γ3'') -∗
        (*Ht3 *) 
          (〈Δ; Γ1〉 ⊨ₜ e ≤log≤ e :ρ':τ⫤Γ2) (* Ht1*) -∗
     (〈Δ; ctx_append Γ1 Γ3〉 ⊨ₜ
      (handle: e with
       | effect s x, k => h
       | return y => r
       end)
    ≤log≤
      (handle: e with
       | effect s x, k => h
       | return y => r
       end) :ρ:τ'⫤Γ3).
  Proof.
     simpl.
        iIntros (??????) "%H0' %H1' #Ht2 #Ht3 #Ht1".
        iIntros (η μ δ ξ Hδ).
        rewrite !lbl_resolve_handle_name.
        rewrite !resolve_map_lookup H0' /=.
        rewrite !lbl_resolve_rec.
        unfold ctx_append. rewrite fmap_app.
        pose proof (multi_env_sound Γ3 H η μ δ ξ) as HME.
        pose proof (sig_labels_eff_name σ η μ δ ξ) as Hlbl.
        rewrite H1' in Hlbl.
        iApply (sem_typed_shallow_handler_OS (δ !!! s)
                  (λ α, interp._ty (α :: η) μ δ ι ξ)
                  (λ α, interp._ty (α :: η) μ δ κ ξ)
                  (interp._ty η μ δ τ ξ)
                  (interp._ty η μ δ τ' ξ)
                  (interp._eff_sig η μ δ σ ξ)
                  (interp._row η μ δ ρ0 ξ)
                  _ _ _ x y k _ _ _ _ _ _
                  _ _ _ _ _ _ Hlbl).
        1:{ 
            iApply ("Ht1" $! η μ δ ξ Hδ). }
        1:{ iIntros (α). 
          iSpecialize ("Ht3" $! (α :: η) μ δ ξ Hδ).
          iEval (cbn [ctx_insert fmap list_fmap]) in "Ht3".
          iApply (sem_typed_row_cong _ _ _ _ _ _ _
                    (symmetry (row_tweaken (RCons σ ρ0) α η μ δ ξ))).
          iApply (sem_typed_type_cong _ _ _ _ _ _ _
                    (symmetry (ty_tweaken τ' α η μ δ ξ))).
          assert (Htail : ∀ (Γ0 : ctx), env_equiv_pw
                    ((λ '(s0, τ0), (s0, interp._ty η μ δ τ0 ξ)) <$> Γ0)
                    ((λ '(s0, τ0), (s0, interp._ty (α :: η) μ δ τ0 ξ)) <$>
                       ((λ '(x0, α0), (x0, Autosubst_Classes.subst
                           (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) α0))
                          <$> Γ0)))
            by (intros Γ0; induction Γ0 as [|[z β] Γ0' IH]; simpl; [constructor|];
                constructor; [split; [done|]|exact IH];
                simpl; symmetry; apply (ty_tweaken β α η μ δ ξ)).
          assert (Hhead : (interp._ty (α :: η) μ δ
                       (κ -{ rename_type_row (Autosubst_Basics.lift 1%nat) (RCons (SFlip OS (SSig s ι κ)) ρ0) }-[ OS
                        ]-> Autosubst_Classes.subst
                              (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) τ)
                       ξ)
                    ≡ sem_types.sem_ty_mbang syntax.OS
                (sem_types.sem_ty_arr
                   (sem_row.sem_row_cons
                      (sem_sig.sem_sig_flip_mbang syntax.OS
                         (sem_sig.sem_sig_eff (δ !!! s).1 (δ !!! s).2
                            (λ α0 : sem_ty Σ, interp._ty (α0 :: η) μ δ ι ξ)
                            (λ α0 : sem_ty Σ, interp._ty (α0 :: η) μ δ κ ξ)))
                      (interp._row η μ δ ρ0 ξ))
                   (interp._ty (α :: η) μ δ κ ξ) (interp._ty η μ δ τ ξ))).
          { change (interp._ty (α :: η) μ δ
                       (κ -{ rename_type_row (Autosubst_Basics.lift 1%nat) (RCons (SFlip OS (SSig s ι κ)) ρ0) }-[ OS
                        ]-> Autosubst_Classes.subst
                              (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) τ)
                       ξ)
              with (sem_types.sem_ty_mbang syntax.OS
                (sem_types.sem_ty_arr
                   (interp._row (α :: η) μ δ
                      (rename_type_row (Autosubst_Basics.lift 1%nat) (RCons (SFlip OS (SSig s ι κ)) ρ0)) ξ)
                   (interp._ty (α :: η) μ δ κ ξ)
                   (interp._ty (α :: η) μ δ (Autosubst_Classes.subst
                       (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) τ) ξ))).
            rewrite (row_tweaken (RCons (SFlip OS (SSig s ι κ)) ρ0) α η μ δ ξ) (ty_tweaken τ α η μ δ ξ).
            reflexivity. }
          destruct x as [|sx], k as [|sk]; simpl;
            unshelve (iApply (sem_typed_env_cong _ _ _ _ _ _ _ _ _ (Htail Γ3));
              iApply "Ht3");
            repeat (constructor; [ split; [ reflexivity
                | first [ exact (symmetry Hhead) | reflexivity ] ] | ]);
             try exact (Htail Γ3). }
        1:{ 
          iSpecialize ("Ht2" $! η μ δ ξ Hδ).
          iEval (cbn [ctx_insert ctx_append fmap list_fmap]) in "Ht2".
          destruct y as [|sy]; simpl; rewrite -fmap_app; iApply "Ht2". }
        Unshelve.
        all: repeat case_match; simpl in *;
          first [ exact I | congruence | apply ctx_dom_env_dom; assumption ].
Qed.
     
  Lemma interp_c_shallowhandle_ms  Δ Γ1 Γ2 Γ3 τ τ' ι κ r h e (*ρ ρ'*) ρ0 x y k s σ `{le.MultiC Γ3} :
       let ρ := RCons σ ρ0 in
       let ρ' := RCons (SFlip MS (SSig s ι κ)) ρ0 in
       let Γ3' := <[ x :=c ι]> (<[ k:=c κ -{ rename_type_row (Autosubst_Basics.lift 1%nat) ρ' }-[ MS]-> Autosubst_Classes.subst (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat))
                           τ]> ((λ '(x0, α0), (x0, Autosubst_Classes.subst
                                                      (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) α0)) <$> Γ3)) in
       let Γ3'' := ( (λ '(x0, α0),
            (x0, Autosubst_Classes.subst
                   (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) α0)) <$> Γ3 ) in
       (match x with BNamed s => s ∉ ctx_dom Γ2 | BAnon => True end) →
       (match x with BNamed s => s ∉ ctx_dom Γ3 | BAnon => True end) →
       (match k with BNamed s => s ∉ ctx_dom Γ3 | BAnon => True end) →
       (match x, k with BNamed a, BNamed b => a ≠ b | _, _ => True end) →
       (match y with BNamed s => s ∉ ctx_dom Γ2 | BAnon => True end) →
       (match y with BNamed s => s ∉ ctx_dom Γ3 | BAnon => True end) →
       Δ !! s = Some () ->
       le.eff_name_from_sig σ = s ->
        ⊢ (〈Δ; <[ y :=c τ ]> (ctx_append Γ2 Γ3)〉 ⊨ₜ r ≤log≤ r :ρ:τ'⫤Γ3) (*Ht2*) -∗
          (〈Δ; Γ3'〉 ⊨ₜ h ≤log≤ h :rename_type_row (Autosubst_Basics.lift 1%nat) ρ:
         Autosubst_Classes.subst
           (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) τ'⫤Γ3'') -∗
        (*Ht3 *) 
          (〈Δ; Γ1〉 ⊨ₜ e ≤log≤ e :ρ':τ⫤Γ2) (* Ht1*) -∗        
         (〈Δ; ctx_append Γ1 Γ3〉 ⊨ₜ
      (handle: e with
       | effect s x, k as multi => h
       | return y => r
       end)
    ≤log≤
      (handle: e with
       | effect s x, k as multi => h
       | return y => r
       end) :ρ:τ'⫤Γ3).
  Proof.
     simpl.
        iIntros (??????) "%H0' %H1' #Ht2 #Ht3 #Ht1".
        iIntros (η μ δ ξ Hδ).
        rewrite !lbl_resolve_handle_name.
        rewrite !resolve_map_lookup H0' /=.
        rewrite !lbl_resolve_rec.
        unfold ctx_append. rewrite fmap_app.
        pose proof (multi_env_sound Γ3 H η μ δ ξ) as HME.
        pose proof (sig_labels_eff_name σ η μ δ ξ) as Hlbl.
        rewrite H1' in Hlbl.
        iApply (sem_typed_shallow_handler_MS (δ !!! s)
                  (λ α, interp._ty (α :: η) μ δ ι ξ)
                  (λ α, interp._ty (α :: η) μ δ κ ξ)
                  syntax.MS
                  (interp._ty η μ δ τ ξ)
                  (interp._ty η μ δ τ' ξ)
                  (interp._eff_sig η μ δ σ ξ)
                  (interp._row η μ δ ρ0 ξ)
                  _ _ _ x y k _ _ _ _ _ _
                  _ _ _ _ _ _ Hlbl).
        1:{ 
            iApply ("Ht1" $! η μ δ ξ Hδ). }
        1:{ iIntros (α).
          iSpecialize ("Ht3" $! (α :: η) μ δ ξ Hδ).
          iEval (cbn [ctx_insert fmap list_fmap]) in "Ht3".
          iApply (sem_typed_row_cong _ _ _ _ _ _ _
                    (symmetry (row_tweaken (RCons σ ρ0) α η μ δ ξ))).
          iApply (sem_typed_type_cong _ _ _ _ _ _ _
                    (symmetry (ty_tweaken τ' α η μ δ ξ))).
          assert (Htail : ∀ (Γ0 : ctx), env_equiv_pw
                    ((λ '(s0, τ0), (s0, interp._ty η μ δ τ0 ξ)) <$> Γ0)
                    ((λ '(s0, τ0), (s0, interp._ty (α :: η) μ δ τ0 ξ)) <$>
                       ((λ '(x0, α0), (x0, Autosubst_Classes.subst
                           (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) α0))
                          <$> Γ0)))
            by (intros Γ0; induction Γ0 as [|[z β] Γ0' IH]; simpl; [constructor|];
                constructor; [split; [done|]|exact IH];
                simpl; symmetry; apply (ty_tweaken β α η μ δ ξ)).
          assert (Hhead : (interp._ty (α :: η) μ δ
                       (κ -{ rename_type_row (Autosubst_Basics.lift 1%nat) (RCons (SFlip MS (SSig s ι κ)) ρ0) }-[ MS
                        ]-> Autosubst_Classes.subst
                              (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) τ)
                       ξ)
                    ≡ sem_types.sem_ty_mbang syntax.MS
                (sem_types.sem_ty_arr
                   (sem_row.sem_row_cons
                      (sem_sig.sem_sig_flip_mbang syntax.MS
                         (sem_sig.sem_sig_eff (δ !!! s).1 (δ !!! s).2
                            (λ α0 : sem_ty Σ, interp._ty (α0 :: η) μ δ ι ξ)
                            (λ α0 : sem_ty Σ, interp._ty (α0 :: η) μ δ κ ξ)))
                      (interp._row η μ δ ρ0 ξ))
                   (interp._ty (α :: η) μ δ κ ξ) (interp._ty η μ δ τ ξ))).
          { change (interp._ty (α :: η) μ δ
                       (κ -{ rename_type_row (Autosubst_Basics.lift 1%nat) (RCons (SFlip MS (SSig s ι κ)) ρ0) }-[ MS
                        ]-> Autosubst_Classes.subst
                              (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) τ)
                       ξ)
              with (sem_types.sem_ty_mbang syntax.MS
                (sem_types.sem_ty_arr
                   (interp._row (α :: η) μ δ
                      (rename_type_row (Autosubst_Basics.lift 1%nat) (RCons (SFlip MS (SSig s ι κ)) ρ0)) ξ)
                   (interp._ty (α :: η) μ δ κ ξ)
                   (interp._ty (α :: η) μ δ (Autosubst_Classes.subst
                       (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) τ) ξ))).
            rewrite (row_tweaken (RCons (SFlip MS (SSig s ι κ)) ρ0) α η μ δ ξ) (ty_tweaken τ α η μ δ ξ).
           reflexivity. }
          destruct x as [|sx], k as [|sk]; simpl;
            unshelve (iApply (sem_typed_env_cong _ _ _ _ _ _ _ _ _ (Htail Γ3));
              iApply "Ht3");
            repeat (constructor; [ split; [ reflexivity
                | first [ exact (symmetry Hhead) | reflexivity ] ] | ]);
             try exact (Htail Γ3). }
        1:{ (*apply fundamental in Ht2. iPoseProof Ht2 as "Ht". *)
          iSpecialize ("Ht2" $! η μ δ ξ Hδ).
          iEval (cbn [ctx_insert ctx_append fmap list_fmap]) in "Ht2".
          destruct y as [|sy]; simpl; rewrite -fmap_app; iApply "Ht2". }
        Unshelve.
        all: repeat case_match; simpl in *;
          first [ exact I | congruence | apply ctx_dom_env_dom; assumption ].
Qed.

(*          
Lemma interp_c_sub
Lemma interp_c_contraction
Lemma interp_c_weakening *)

End compatibility_interp.

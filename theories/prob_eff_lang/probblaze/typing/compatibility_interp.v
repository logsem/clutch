From iris.base_logic Require Export invariants.
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext.

From clutch.prob_eff_lang.probblaze Require Import metatheory notation syntax semantics sem_judgement sem_def sem_operators sem_row proofmode.
From clutch.prob_eff_lang.probblaze Require Import primitive_laws compatibility.
From clutch.prob_eff_lang.probblaze Require Import sem_env.
From clutch.prob_eff_lang.probblaze Require Import types.
From clutch.prob_eff_lang.probblaze Require Import interp logic.

Section compatibility_interp.

  Context `{!probblazeRGS Σ}.

  Lemma syn_typed_binop_typed_binop op ι κ τ η μ δ ξ:
  syn_typed_bin_op op ι κ τ → typed_bin_op op (interp._ty η μ δ ι ξ) (interp._ty η μ δ κ ξ) (interp._ty η μ δ τ ξ).
Proof.
  intros []; constructor.
Qed.
About brel_pure_l.
Print Grammar tactic.
  Lemma syn_typed_unop_typed_unop op κ τ η μ δ ξ:
  syn_typed_un_op op κ τ → typed_un_op op (interp._ty η μ δ κ ξ) (interp._ty η μ δ τ ξ).
Proof.
  intros []; constructor.
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

  (*Lemma interp_c_var η μ δ τ ξ' Δ Γ x :
    ⊢ sem_typed ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> (ctx_insert (BNamed x) τ Γ))
      (lbl_resolve (resolve_l Δ δ) (Var x))
      (lbl_resolve (resolve_r Δ δ) (Var x))
      ((interp._row η μ δ RNil ξ'))
      ((interp._ty η μ δ τ ξ'))
      ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ).
  Proof. rewrite !lbl_resolve_var.
         iApply sem_typed_var.
  Qed. *)

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
 (* Lemma interp_c_binop η μ δ ι κ τ ξ' Δ Γ1 Γ2 Γ3 e1 e2 ρ op :
    syn_typed_bin_op op ι κ τ ->
    ⊢ sem_typed ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ2)
        (lbl_resolve (resolve_l Δ δ) e1)
        (lbl_resolve (resolve_r Δ δ) e1)
        (interp._row η μ δ ρ ξ')
        (interp._ty η μ δ ι ξ')
        ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ3) -∗
      sem_typed ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ1)
        (lbl_resolve (resolve_l Δ δ) e2)
        (lbl_resolve (resolve_r Δ δ) e2)
        (interp._row η μ δ ρ ξ')
        (interp._ty η μ δ κ ξ')
        ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ2) -∗
      sem_typed ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ1)
        (lbl_resolve (resolve_l Δ δ) (BinOp op e1 e2))
        (lbl_resolve (resolve_r Δ δ) (BinOp op e1 e2))
        (interp._row η μ δ ρ ξ')
        (interp._ty η μ δ τ ξ')
        ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ3).
  Proof.  rewrite !lbl_resolve_binop. intros Hsyn. iIntros "#He1 #He2". iApply sem_typed_bin_op;
            [by apply syn_typed_binop_typed_binop | iApply "He1" | iApply "He2"].
  Qed. *)

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
  
  (*Lemma interp_c_unop η μ δ ρ κ τ ξ' Δ Γ1 Γ2 e op :
    syn_typed_un_op op κ τ ->
    ⊢ sem_typed ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ1)
        (lbl_resolve (resolve_l Δ δ) e)
        (lbl_resolve (resolve_r Δ δ) e)
        (interp._row η μ δ ρ ξ')
        (interp._ty η μ δ κ ξ')
        ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ2) -∗
      sem_typed ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ1)
        (lbl_resolve (resolve_l Δ δ) (UnOp op e))
        (lbl_resolve (resolve_r Δ δ) (UnOp op e))
        (interp._row η μ δ ρ ξ')
        (interp._ty η μ δ τ ξ')
        ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ2 ).
  Proof.
    rewrite !lbl_resolve_unop. iIntros "%Hsyn #He". iApply sem_typed_un_op; [by apply syn_typed_unop_typed_unop| iApply "He"].
  Qed. *)

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
  
  (*Lemma interp_c_val η μ δ τ ξ' Δ Γ v :
               ⊢ sem_val_typed  v v
                   ((interp._ty η μ δ τ ξ')) -∗
      sem_typed ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ)
        (lbl_resolve (resolve_l Δ δ) (Val v))
        (lbl_resolve (resolve_r Δ δ) (Val v))
        ((interp._row η μ δ RNil ξ'))
        ((interp._ty η μ δ τ ξ'))
        ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ).
  Proof. 
    rewrite !lbl_resolve_val. iIntros "#Hval". iApply sem_typed_val.
    iApply "Hval".
  Qed. *)

  (*Lemma interp_c_pure *)
                                
  Lemma interp_c_pair Δ Γ1 Γ2 Γ3 e1 e2 τ1 τ2 ρ :
   (∀ η μ δ ξ, (interp._row η μ δ ρ ξ) ᵣ⪯ₜ (interp._ty η μ δ τ2 ξ)) ->
   ⊢ (〈Δ; Γ2〉 ⊨ₜ e1 ≤log≤ e1 :ρ:τ1⫤Γ3) -∗
    (〈Δ; Γ1〉 ⊨ₜ e2 ≤log≤ e2 :ρ:τ2⫤Γ2) -∗
    (〈Δ; Γ1〉 ⊨ₜ (e1, e2) ≤log≤ (e1, e2) :ρ:(τ1 * τ2)⫤Γ3).
  Proof. intros Hrt. iIntros "#He1 #He2".
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
  
  (*Lemma interp_c_pair η μ δ ρ τ1 τ2 ξ' Δ Γ1 Γ2 Γ3 e1 e2 `{(interp._row η μ δ ρ ξ') ᵣ⪯ₜ (interp._ty η μ δ τ2 ξ') } :
                                   (*(interp._row η μ δ ρ ξ') ᵣ⪯ₜ (interp._ty η μ δ τ2 ξ') ->*)
                                   ⊢ sem_typed ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ2)
                                       (lbl_resolve (resolve_l Δ δ) e1)
                                       (lbl_resolve (resolve_r Δ δ) e1)
                                       (interp._row η μ δ ρ ξ')
                                       (interp._ty η μ δ τ1 ξ')
                                       ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ3) -∗
                                   sem_typed ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ1)
                                     (lbl_resolve (resolve_l Δ δ) e2)
                                     (lbl_resolve (resolve_r Δ δ) e2)
                                     (interp._row η μ δ ρ ξ')
                                     (interp._ty η μ δ τ2 ξ')
                                     ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ2) -∗                             
         sem_typed ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ1)
           (lbl_resolve (resolve_l Δ δ) (e1, e2))
           (lbl_resolve (resolve_r Δ δ) (e1, e2))
           (interp._row η μ δ ρ ξ')
           (interp._ty η μ δ (τ1 * τ2) ξ')
           ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ3).
  Proof. rewrite !lbl_resolve_pair. iIntros "#He1 #He2".
         iApply sem_typed_pair_gen; [iApply "He1" | iApply "He2"].
  Qed. *)

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
  
  (*Lemma interp_c_fst η μ δ ρ τ1 τ2 ξ' Δ Γ1 Γ2 e :
    ⊢ sem_typed ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ1)
        (lbl_resolve (resolve_l Δ δ) e)
        (lbl_resolve (resolve_r Δ δ) e)
        (interp._row η μ δ ρ ξ')
        (interp._ty η μ δ (τ1 * τ2) ξ')
        ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ2) -∗
    sem_typed ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ1)
      (lbl_resolve (resolve_l Δ δ) (Fst e))
      (lbl_resolve (resolve_r Δ δ) (Fst e))
      (interp._row η μ δ ρ ξ')
      (interp._ty η μ δ τ1 ξ')
      ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ2).
  Proof. rewrite !lbl_resolve_fst. iApply sem_typed_fst_expr.
  Qed. *)

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
  
  (*Lemma interp_c_snd  η μ δ ρ τ1 τ2 ξ' Δ Γ1 Γ2 e :
    ⊢ sem_typed ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ1)
        (lbl_resolve (resolve_l Δ δ) e)
        (lbl_resolve (resolve_r Δ δ) e)
        (interp._row η μ δ ρ ξ')
        (interp._ty η μ δ (τ1 * τ2) ξ')
        ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ2) -∗
    sem_typed ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ1)
      (lbl_resolve (resolve_l Δ δ) (Snd e))
      (lbl_resolve (resolve_r Δ δ) (Snd e))
      (interp._row η μ δ ρ ξ')
      (interp._ty η μ δ τ2 ξ')
      ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ2).
  Proof. rewrite !lbl_resolve_snd. iApply sem_typed_snd_expr.
  Qed. *)
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
  
  (*Lemma interp_c_left_inj η μ δ ρ τ1 τ2 ξ' Δ Γ1 Γ2 e :
    ⊢ sem_typed ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ1)
        (lbl_resolve (resolve_l Δ δ) e)
        (lbl_resolve (resolve_r Δ δ) e)
        (interp._row η μ δ ρ ξ')
        (interp._ty η μ δ τ1 ξ')
        ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ2) -∗
    sem_typed ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ1 )
      (lbl_resolve (resolve_l Δ δ) (InjL e))
      (lbl_resolve (resolve_r Δ δ) (InjL e))
      (interp._row η μ δ ρ ξ')
      (interp._ty η μ δ (τ1 + τ2) ξ')
      ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ2).
   Proof. rewrite !lbl_resolve_injl. iApply sem_typed_left_inj.
   Qed. *)

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
  
  (*Lemma interp_c_right_inj η μ δ ρ τ1 τ2 ξ' Δ Γ1 Γ2 e :
    ⊢ sem_typed ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ1)
        (lbl_resolve (resolve_l Δ δ) e)
        (lbl_resolve (resolve_r Δ δ) e)
        (interp._row η μ δ ρ ξ')
        (interp._ty η μ δ τ2 ξ')
        ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ2) -∗
    sem_typed ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ1 )
      (lbl_resolve (resolve_l Δ δ) (InjR e))
      (lbl_resolve (resolve_r Δ δ) (InjR e))
      (interp._row η μ δ ρ ξ')
      (interp._ty η μ δ (τ1 + τ2) ξ')
      ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ2).
  Proof. rewrite !lbl_resolve_injr. iApply sem_typed_right_inj.
  Qed.
  *)
(*Lemma interp_c_match
Lemma interp_c_if
Lemma interp_c_rec
Lemma interp_c_app
Lemma interp_c_row_elim
Lemma interp_c_mode_elim
Lemma interp_c_alloc_ref
Lemma interp_c_load_ref
Lemma interp_c_store_ref
Lemma interp_c_tape_alloc
Lemma interp_c_rand
Lemma interp_c_randu
Lemma interp_c_fold
Lemma interp_c_unfold
Lemma interp_c_pack
Lemma interp_c_unpack
Lemma interp_c_effect_gen
Lemma interp_c_effect_do
Lemma interp_c_deephandle_os
Lemma interp_c_deephandle_ms
Lemma interp_c_shallowhandle_os
Lemma interp_c_shallowhandle_ms
Lemma interp_c_sub
Lemma interp_c_contraction
Lemma interp_c_weakening *)

End compatibility_interp.

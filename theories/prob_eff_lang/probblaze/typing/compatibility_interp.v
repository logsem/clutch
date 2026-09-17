From iris.base_logic Require Export invariants.
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import metatheory notation syntax semantics sem_judgement sem_def sem_operators sem_row.
From clutch.prob_eff_lang.probblaze Require Import primitive_laws compatibility.
From clutch.prob_eff_lang.probblaze Require Import sem_env.
From clutch.prob_eff_lang.probblaze Require Import types.
From clutch.prob_eff_lang.probblaze Require Import interp logic.

Section compatibility_interp.

  Context `{!probblazeRGS Σ}.

  Print lbl_resolve.
  Locate "⫤".
  Locate ":=c".
  Print ctx_insert.
  Print binder.

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

  Lemma interp_c_var η μ δ τ ξ' Δ Γ x :
    ⊢ sem_typed ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> (ctx_insert (BNamed x) τ Γ))
      (lbl_resolve (resolve_l Δ δ) (Var x))
      (lbl_resolve (resolve_r Δ δ) (Var x))
      ((interp._row η μ δ RNil ξ'))
      ((interp._ty η μ δ τ ξ'))
      ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ).
  Proof. rewrite !lbl_resolve_var.
         iApply sem_typed_var.
  Qed.

  
  Lemma interp_c_binop η μ δ ι κ τ ξ' Δ Γ1 Γ2 Γ3 e1 e2 ρ op :
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
  Qed.
  
  Lemma interp_c_unop η μ δ ρ κ τ ξ' Δ Γ1 Γ2 e op :
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
  Qed.
  
  Lemma interp_c_val η μ δ τ ξ' Δ Γ v :
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
  Qed.

  (*Lemma interp_c_pure *)
                                 Locate " ρ ᵣ⪯ₜ τ2 ".
                                 Print RowTypeSub.
                                
  Lemma interp_c_pair η μ δ ρ τ1 τ2 ξ' Δ Γ1 Γ2 Γ3 e1 e2 `{(interp._row η μ δ ρ ξ') ᵣ⪯ₜ (interp._ty η μ δ τ2 ξ') } :
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
  Qed.
  
  Lemma interp_c_fst η μ δ ρ τ1 τ2 ξ' Δ Γ1 Γ2 e :
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
  Qed.
  
  Lemma interp_c_snd  η μ δ ρ τ1 τ2 ξ' Δ Γ1 Γ2 e :
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
  Qed.
  
  Lemma interp_c_left_inj η μ δ ρ τ1 τ2 ξ' Δ Γ1 Γ2 e :
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
   Qed.
   
  Lemma interp_c_right_inj η μ δ ρ τ1 τ2 ξ' Δ Γ1 Γ2 e :
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


(* compatibility.v *)

(* The compatibility lemmas are what one gets when the syntactic typing judgment
   is replaced with a semantic typing judgment. *)

From iris.proofmode Require Import base tactics.
From iris.base_logic.lib Require Import iprop invariants.

(* Local imports *)
From clutch.prob_eff_lang.probblaze Require Import notation class_instances proofmode  mode sem_def sem_sig sem_types sem_row sem_env logic sem_judgement.


Open Scope stdpp_scope.
Open Scope sem_ty_scope.
Open Scope sem_row_scope.
Open Scope bi_scope.
(* Semantic typing rules. *)

Section compatibility.

  Context `{!probblazeRGS Σ}.

  (*  Lemma sem_oval_typed_val τ v : 
       ⊨ᵥ v : τ -∗ [] ⊨ₚ v : τ.
     Proof.
       iIntros "#Hv !# %γ HΓ /=".
       iApply pwp_value'. iFrame.
       rewrite /sem_val_typed /tc_opaque.
       iApply "Hv".
     Qed.
     
     Lemma sem_typed_oval τ Γ₁ Γ₂ e :
       (Γ₁ ⊨ₚ e : τ) -∗ (Γ₁ ++ Γ₂ ⊨ e : ⟨⟩ : τ ⫤ Γ₂).
     Proof.
       iIntros "#Hv !# %γ HΓ₁₂ /=". iApply pwp_ewpw. 
       rewrite env_sem_typed_app. iDestruct "HΓ₁₂" as "[HΓ₁ HΓ₂]".
       iApply (pwp_strong_mono with "[HΓ₁] [HΓ₂]"); [reflexivity|by iApply "Hv"|].
       iIntros (?) "Hτ". iFrame.
     Qed. *)

  Lemma sem_typed_val τ Γ v1 v2 : 
    ⊢  ⊨ᵥ v1 ≤ v2 : τ -∗ sem_typed Γ v1 v2 sem_row_nil τ Γ.
  Proof.
    iIntros "#Hv". iIntros "!# %vvs HΓ /=".
    iApply brel_value. iFrame. unfold sem_val_typed. simpl. done.
  Qed.     
  (* Base rules *)
  
  Lemma sem_typed_var τ Γ x :
    ⊢ sem_typed ((x, τ) :: Γ) x x sem_row_nil τ Γ.
    (* ⊢ (x, τ) :: Γ ⊨ x ≤ x : ⟨⟩ : τ ⫤ Γ. *)
  Proof.
    iIntros (γ) "!# /= [%v (%Hrw & Hτ & HΓ₁)] /=".
    rewrite !lookup_fmap. rewrite Hrw. simpl.
    iApply brel_value. iFrame.
  Qed.

  Lemma sem_typed_unit Γ :
    ⊢ sem_typed Γ #()%V #()%V ⟨⟩ 𝟙 Γ.
    (* ⊢ Γ ⊨ #() ≤ #() : ⟨⟩ : 𝟙 ⫤ Γ. *)
  Proof.
    iIntros (γ) "!# HΓ₁ //=".
    iApply brel_value. by iFrame.
  Qed.
  
  Lemma sem_typed_bool Γ (b : bool) :
    ⊢ sem_typed Γ #b #b ⟨⟩ 𝔹 Γ.
    (* ⊢ Γ ⊨ #b : ⟨⟩ : 𝔹 ⫤ Γ. *)
  Proof.
    iIntros (γ) "!# HΓ₁ //=".
    iApply brel_value. iFrame. iExists b. done.
  Qed.
  
  Lemma sem_typed_int Γ (i : Z) :
    ⊢ sem_typed Γ #i #i ⟨⟩ ℤ Γ.
    (* ⊢ Γ ⊨ #i : ⟨⟩ : ℤ ⫤ Γ. *)
  Proof.
    iIntros (γ) "!# HΓ₁ //=". 
    iApply brel_value. iFrame. iExists i; done.
  Qed.

  Lemma sem_typed_void_in_env τ Γ1 Γ2 e1 e2 x :
    ⊢ sem_typed ((x, ⊥) :: Γ1) e1 e2 ⟨⟩ τ Γ2.
    (* ⊢ (x, ⊥) :: Γ₁ ⊨ e : ⟨⟩ : τ ⫤ Γ₂. *)
  Proof.
    iIntros (γ) "!# /= [%v (%Hrw & [] & _)] /=". 
  Qed.

  (* Lemma sem_typed_closure τ ρ κ f x e1 e2 :
       match f with BNamed f => BNamed f ≠ x | BAnon => True end →
       sem_typed ((x, τ) :: (f, τ -{ ρ }-> κ) :: []) e1 e2 ρ κ [] -∗ 
       ⊨ᵥ (rec: f x := e1) ≤ (rec: f x := e2): (τ -{ ρ }-> κ).
     Proof.
       iIntros (?) "#He !#". iLöb as "IH".
       rewrite /sem_ty_arr /sem_ty_mbang /=.
       iIntros "%v !# Hτ /=".
       ewpw_pure_steps. destruct x as [|x]; destruct f as [|f]; simpl.
       - rewrite - {3} [e]subst_map_empty.
         iApply (ewpw_mono with "[He]"); first (by iApply "He").
         iIntros "!# % [$ _] //=". 
       - rewrite -subst_map_singleton.
         iApply ewpw_mono; [iApply "He"; solve_env|solve_env].
         iIntros "!# % [$ _] //=".
       - rewrite -subst_map_singleton.
         iApply (ewpw_mono with "[Hτ]"); [iApply "He"; solve_env|solve_env].
         iIntros "!# % [$ _] //=".
       - rewrite -(subst_map_singleton f) -subst_map_singleton subst_map_union.
         iApply (ewpw_mono with "[Hτ]"); [iApply "He"|iIntros "!# % [$ _] //="].
         rewrite -insert_union_singleton_r; [solve_env|apply lookup_singleton_ne];
         intros ?; simplify_eq.
     Qed. *)
  
  Lemma sem_typed_Tclosure τ v1 v2 :
    ⊢ (∀ α, ⊨ᵥ v1 ≤ v2 : τ α) -∗ 
    ⊨ᵥ v1 ≤ v2 : (∀ₜ α, τ α).
  Proof.
    iIntros "#He !# %u". rewrite /sem_val_typed /=. iApply "He".
  Qed.
  
  (* row abstraction and application *)
  Lemma sem_typed_Rclosure C v1 v2 : 
    ⊢ (∀ θ, ⊨ᵥ v1 ≤ v2 : C θ) -∗
    ⊨ᵥ v1 ≤ v2 : (∀ᵣ θ , C θ)%T.
  Proof.
    iIntros "#He !# %u". rewrite /sem_val_typed /=. iApply "He".
  Qed.
  
  (* mode abstraction and application *)
  Lemma sem_typed_Mclosure C v1 v2 : 
    ⊢ (∀ ν, ⊨ᵥ v1 ≤ v2 : C ν) -∗
    ⊨ᵥ v1 ≤ v2 : (∀ₘ ν , C ν)%T.
  Proof.
    iIntros "#He !# %u". rewrite /sem_val_typed /=. iApply "He". 
  Qed.

  (* mode abstraction and application *)
  Lemma sem_val_typed_bang v1 v2 τ :
    ⊢ ⊨ᵥ v1 ≤ v2 : τ -∗
           ⊨ᵥ v1 ≤ v2 : ![MS] τ.
  Proof. iIntros "#He !# //". Qed.

  (* Subsumption rule *)
  Lemma sem_typed_sub Γ₁ Γ₁' Γ₂ Γ₂' e1 e2 ρ ρ' τ τ':
    ⊢ Γ₁  ≤ₑ Γ₁' -∗
    Γ₂' ≤ₑ Γ₂ -∗
    ρ'  ≤ᵣ ρ -∗ 
    τ'  ≤ₜ τ -∗
    sem_typed Γ₁' e1 e2 ρ' τ' Γ₂' -∗ sem_typed Γ₁ e1 e2 ρ τ Γ₂.
  Proof.
    iIntros "#HΓ₁le #HΓ₂le #Hρle #Hτle #He !# %γ HΓ₁ //=".
    iDestruct ("HΓ₁le" with "HΓ₁") as "HΓ₁'".
    rewrite -(to_iThyIfMonoMS (iLblSig_to_iLblThy ρ)).
    iApply (brel_mono with "[Hρle] [HΓ₁']"); [by iApply "Hρle"|by iApply "He" |]. simpl.
    iIntros "!# % % (Hτ & HΓ)".
    iSplitL "Hτ"; [by iApply "Hτle"|by iApply "HΓ₂le"].
  Qed.

  (* Convenient Subsumption rules *)
  Corollary sem_typed_sub_ty τ' τ Γ1 Γ2 e1 e2 ρ :
  ⊢ τ' ≤ₜ τ -∗
  (sem_typed Γ1 e1 e2 ρ τ' Γ2) -∗ (sem_typed Γ1 e1 e2 ρ τ Γ2).
  Proof.
    iIntros "#Hτ".
    iApply (sem_typed_sub Γ1 Γ1 Γ2 Γ2 _ _ ρ ρ);
      (iApply row_le_refl || iApply env_le_refl || done). 
  Qed.

  Corollary sem_typed_sub_row ρ ρ' Γ1 Γ2 e1 e2 τ :
    ⊢ ρ' ≤ᵣ ρ -∗
    (sem_typed Γ1 e1 e2 ρ' τ Γ2) -∗ (sem_typed Γ1 e1 e2 ρ τ Γ2).
  Proof.
    iIntros "#Hρ".
    iApply (sem_typed_sub Γ1 Γ1 Γ2 Γ2 _ _ ρ ρ' τ τ);
      (iApply env_le_refl || iApply ty_le_refl || done).
  Qed.

  Corollary sem_typed_sub_nil Γ1 Γ2 e1 e2 τ ρ :
   ⊢ (sem_typed Γ1 e1 e2 ⟨⟩ τ Γ2) -∗ (sem_typed Γ1 e1 e2 ρ τ Γ2).
  Proof. iApply sem_typed_sub_row. iApply row_le_nil. Qed.
  
  Corollary sem_typed_sub_u2aarr Γ1 Γ2 e1 e2 τ κ ρ ρ' :
    ⊢ (sem_typed Γ1 e1 e2 ρ' (τ -{ ρ }-> κ) Γ2) -∗ (sem_typed Γ1 e1 e2 ρ' (τ -{ ρ }-∘ κ) Γ2).
  Proof.
    iIntros "#He".
    iApply sem_typed_sub_ty; [iApply ty_le_u2aarr|done].
  Qed.

  Corollary sem_typed_sub_env Γ1 Γ1' Γ2 e1 e2 ρ τ :
    ⊢ Γ1 ≤ₑ Γ1' -∗
    (sem_typed Γ1' e1 e2 ρ τ Γ2) -∗ (sem_typed Γ1 e1 e2 ρ τ Γ2).
  Proof.
    iIntros "#HΓ₁".
    iApply (sem_typed_sub Γ1 Γ1' Γ2 Γ2 _ _ ρ ρ τ τ);
      (iApply row_le_refl || iApply env_le_refl || iApply ty_le_refl || done).
  Qed.

  Corollary sem_typed_sub_env_final Γ1 Γ2 Γ2' e1 e2 ρ τ :
    ⊢ Γ2' ≤ₑ Γ2 -∗
    (sem_typed Γ1 e1 e2 ρ τ Γ2') -∗ (sem_typed Γ1 e1 e2 ρ τ Γ2).
  Proof.
    iIntros "#HΓ₂".
    iApply (sem_typed_sub Γ1 Γ1 Γ2 Γ2' _ _ ρ ρ τ τ);
      (iApply row_le_refl || iApply env_le_refl || iApply ty_le_refl || done).
  Qed.

  Corollary sem_typed_swap_second Γ1 Γ2 x y e1 e2 ρ τ1 τ2 κ :
    ⊢ (sem_typed ((y, τ2) :: (x, τ1) :: Γ1) e1 e2 ρ κ Γ2) -∗ 
    (sem_typed ((x, τ1) :: (y, τ2) :: Γ1) e1 e2 ρ κ Γ2).
  Proof.
    iIntros "He".
    iApply sem_typed_sub_env; [iApply env_le_swap_second|iApply "He"].
  Qed.

  Corollary sem_typed_swap_third Γ₁ Γ₂ x y z e1 e2 ρ τ₁ τ₂ τ₃ κ :
    ⊢ (sem_typed ((z, τ₃) :: (x, τ₁) :: (y, τ₂) :: Γ₁) e1 e2 ρ κ Γ₂) -∗ 
    (sem_typed ((x, τ₁) :: (y, τ₂) :: (z, τ₃) :: Γ₁) e1 e2 ρ κ Γ₂).
  Proof.
    iIntros "He".
    iApply sem_typed_sub_env; [|iApply "He"].
    iApply env_le_trans; iApply env_le_swap_third.
  Qed.
  (* TODO: finish this rule -- it's easy *)
  (* Corollary sem_typed_swap_fourth Γ₁ Γ₂ x y z z' e ρ τ₁ τ₂ τ₃ τ₄ κ :
       ((z', τ₄) :: (x, τ₁) :: (y, τ₂) :: (z, τ₃) :: Γ₁ ⊨ e : ρ : κ ⫤ Γ₂) -∗ 
       ((x, τ₁) :: (y, τ₂) :: (z, τ₃) :: (z', τ₄) :: Γ₁ ⊨ e : ρ : κ ⫤ Γ₂).
     Proof.
       iIntros "He".
       iApply sem_typed_sub_env; [|iApply "He"].
       do 2 (iApply env_le_trans; [iApply env_le_swap_fourth|]).
       iApply env_le_swap_fourth.
     Qed. *)

  Corollary sem_typed_swap_env_singl Γ1 Γ2 x e1 e2 ρ τ κ :
    ⊢ (sem_typed (Γ1 ++ [(x, τ)]) e1 e2 ρ κ Γ2) -∗ 
    (sem_typed ((x, τ) :: Γ1) e1 e2 ρ κ Γ2). 
  Proof.
    iIntros "He".
    iApply sem_typed_sub_env; [|iApply "He"].
    iApply env_le_swap_env_sing.
  Qed.

  Corollary sem_typed_contraction Γ1 Γ2 x e1 e2 ρ τ κ `{! MultiT τ} :
    ⊢ sem_typed ((x, τ) :: (x, τ) :: Γ1) e1 e2 ρ κ Γ2 -∗ 
    sem_typed ((x, τ) :: Γ1) e1 e2 ρ κ Γ2.
  Proof.
    iIntros "He".
    iApply sem_typed_sub_env; 
      [by iApply env_le_contraction|iApply "He"].
  Qed.

  Corollary sem_typed_weaken Γ1 Γ2 x e1 e2 ρ τ κ :
    ⊢ (sem_typed Γ1 e1 e2 ρ κ Γ2) -∗ (sem_typed ((x, τ) :: Γ1) e1 e2 ρ κ Γ2).
  Proof.
    iIntros "He".
    iApply sem_typed_sub_env; [iApply env_le_weaken|iApply "He"].
  Qed.

  Corollary sem_typed_weaken_env Γ Γ1 Γ2 e1 e2 ρ τ :
    ⊢ (sem_typed Γ1 e1 e2 ρ τ Γ2) -∗ (sem_typed (Γ ++ Γ1) e1 e2 ρ τ Γ2).
  Proof.
    iIntros "#He".
    iInduction Γ as [|[x κ] Γ'] "IH"; simpl.
    { iApply "He". }
    iApply sem_typed_sub_env; [iApply env_le_weaken|iApply "IH"].
  Qed.

  (* TODO: type-related rules -- figure out where to place these *)
  Lemma brel_mono_on_prop e1 e2 ρ P R :
    ⊢ mono_prot_on_prop ρ P -∗ P -∗
    BREL e1 ≤ e2 <| iLblSig_to_iLblThy ρ |> {{ R }} -∗
    BREL e1 ≤ e2 <| iLblSig_to_iLblThy ρ |> {{ λ v1 v2, R v1 v2 ∗ P }}.
  Proof.
    iIntros "#Hmono HP".
    iIntros "Hbrel #Hvalid Hdistinct".
    iDestruct ("Hbrel" with "[$][$]") as "Hrel".
    iLöb as "IH" forall (e1 e2).
    rewrite !rel_unfold /rel_pre.
    iIntros "%k1 %k2 %T Hkwp".
    iApply "Hrel".
    iSplit.
    - iIntros (v1 v2) "HR". iApply "Hkwp". iFrame.
    - iIntros (e1' e2' Q) "HX #Hrel".
      iDestruct "Hkwp" as "[_ Hkwp]".
      (* set Q' := (λ s1 s2, REL s1 ≤ s2 <|iThyMono Y|> {{S}})%I. *)
      iApply ("Hkwp" $! e1' e2' (λ v1 v2, Q v1 v2 ∗ P) with "[HP HX]"); first iApply ("Hmono" with "[$][$]").
      iIntros (??) "!# !> (HQ & HP)".
      iApply ("IH" with "[$]"). by iApply "Hrel".
  Qed.
  
  Lemma sem_typed_frame_gen Γ1 e1 e2 ρ x τ κ Γ2 `{! ρ ᵣ⪯ₜ τ }:
    ⊢ sem_typed Γ1 e1 e2 ρ κ Γ2 -∗
    sem_typed ((x, τ) :: Γ1) e1 e2 ρ κ ((x, τ) :: Γ2).
  Proof.
    iIntros "#He %γ !# (%vv & %Hrw & Hτ & HΓ1)".
    iApply (brel_wand _ _ _ (λ v1 v2, (κ v1 v2 ∗ Γ2 ⊨ₑ γ) ∗ τ vv.1 vv.2) with "[Hτ HΓ1]").
    { iApply (brel_mono_on_prop with "[] [Hτ]"); [iApply row_type_sub |iApply "Hτ"|]. by iApply "He". }
    iIntros "!# % % ((Hκ & HΓ2) & Hτ)". iFrame. iExists vv. iFrame. by iPureIntro.
  Qed.

  Corollary sem_typed_frame Γ1 e1 e2 (ρ : sem_row Σ) x τ κ Γ2 `{! OnceR ρ}:
    ⊢ sem_typed Γ1 e1 e2 ρ κ Γ2 -∗
    sem_typed ((x, τ) :: Γ1) e1 e2 ρ κ ((x, τ) :: Γ2).
  Proof. iApply sem_typed_frame_gen. Qed.

  Corollary sem_typed_frame_ms Γ1 e1 e2 ρ x τ κ Γ2 `{! MultiT τ }:
    ⊢ sem_typed Γ1 e1 e2 ρ κ Γ2 -∗
    sem_typed ((x, τ) :: Γ1) e1 e2 ρ κ ((x, τ) :: Γ2).
  Proof. iApply sem_typed_frame_gen. Qed.

  Lemma sem_typed_frame_env_gen Γ1 Γ' e1 e2 (ρ : sem_row Σ) τ Γ2 `{! ρ ᵣ⪯ₑ Γ' }:
    ⊢ sem_typed Γ1 e1 e2 ρ τ Γ2 -∗
    sem_typed (Γ' ++ Γ1) e1 e2 ρ τ (Γ' ++ Γ2).
  Proof.
    iIntros "#He %γ !# HΓ'Γ₁".
    iDestruct (env_sem_typed_app with "HΓ'Γ₁") as "[HΓ' HΓ1]".
    iApply (brel_wand _ _ _ (λ v1 v2, (τ v1 v2 ∗ Γ2 ⊨ₑ γ) ∗ Γ' ⊨ₑ γ)  with "[HΓ' HΓ1]").
    { iApply (brel_mono_on_prop with "[][HΓ']"); [iApply row_env_sub| iFrame |by iApply "He"]. }
    iIntros "!# % % ((Hτ & HΓ2) & HΓ')". iFrame.
    iApply env_sem_typed_app. iFrame.
  Qed.

  Corollary sem_typed_frame_env Γ1 Γ' e1 e2 (ρ : sem_row Σ) τ Γ2 `{! OnceR ρ}:
    ⊢ sem_typed Γ1 e1 e2 ρ τ Γ2 -∗
    sem_typed (Γ' ++ Γ1) e1 e2 ρ τ (Γ' ++ Γ2).
  Proof. iApply sem_typed_frame_env_gen. Qed.

  Corollary sem_typed_frame_env_ms Γ1 Γ' e1 e2 ρ τ Γ2 `{! MultiE Γ'} :
    ⊢ sem_typed Γ1 e1 e2 ρ τ Γ2 -∗
    sem_typed (Γ' ++ Γ1) e1 e2 ρ τ (Γ' ++ Γ2).
  Proof. iApply sem_typed_frame_env_gen. Qed.

  Corollary sem_typed_unit' Γ ρ : 
    ⊢ sem_typed Γ #()%V #()%V ρ 𝟙 Γ.
  Proof.
    iApply sem_typed_sub_nil. iApply sem_typed_unit.
  Qed.
  
  Corollary sem_typed_bool' Γ ρ (b : bool) : 
    ⊢ sem_typed Γ #b #b ρ 𝔹 Γ.
  Proof.
    iApply sem_typed_sub_nil. iApply sem_typed_bool.
  Qed.
  
  Corollary sem_typed_int' Γ ρ (i : Z) : 
    ⊢ sem_typed Γ #i #i ρ ℤ Γ.
  Proof.
    iApply sem_typed_sub_nil. iApply sem_typed_int.
  Qed.
  
  Corollary sem_typed_var' τ Γ ρ x : 
    ⊢ sem_typed ((x, τ) :: Γ) x x ρ τ Γ.
  Proof.
    iApply sem_typed_sub_nil. iApply sem_typed_var.
  Qed.

  (* (* bang intro *)
     Lemma sem_typed_mbang m Γ v1 v2 τ `{ m ₘ⪯ₑ Γ } :
       ⊢ (sem_typed Γ (of_val v1) (of_val v2) ⊥ τ []) -∗
       sem_typed Γ (of_val v1) (of_val v2) ⊥ (![m] τ) [].
     Proof.
       iIntros "#He !# %γ HΓ₁ /=".
       inv H. iDestruct (mode_env_sub with "HΓ₁") as "HΓ". destruct m; simpl.
       - iDestruct ("He" with "HΓ") as "He'". done.
       - rewrite /sem_ty_mbang /=. iDestruct "HΓ" as "#HΓ".
         iDestruct ("He" with "HΓ") as "Hbrel". simpl.
         iApply (brel_wand with "Hbrel").
         iModIntro. iIntros "% % (Hτ & $)".
         iApply (pwp_wand with "(He HΓ)"). iIntros "% $".
     Qed. *)

  (* Generic App Rule *)
  Lemma sem_typed_app_gen τ ρ' ρ ρ'' κ Γ1 Γ2 Γ3 e1 e1' e2 e2' `{ ρ' ᵣ⪯ₜ τ } `{ ρ'' ᵣ⪯ₑ Γ3 } :
    ⊢ ρ' ≤ᵣ ρ -∗ ρ'' ≤ᵣ ρ -∗
    sem_typed Γ2 e1 e2 ρ' (τ -{ ρ'' }-∘ κ) Γ3 -∗
    sem_typed Γ1 e1' e2' ρ τ Γ2 -∗
    sem_typed Γ1 (e1 e1') (e2 e2') ρ κ Γ3.
  Proof.
    iIntros "#Hρ'ρ #Hρ''ρ #Hee1 #Hee2 !# %γ HΓ1 /=". 
    iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
    iDestruct ("Hee2" with "HΓ1") as "He2brel".
    iApply (brel_wand with "He2brel").
    iIntros "!# % % (Hτ & HΓ2) /=".
    iApply (brel_bind [AppLCtx _] [AppLCtx _]); [iApply traversable_to_iThy|iApply "Hρ'ρ"|].
    iApply (brel_wand with "[Hτ HΓ2]").
    { iApply (brel_mono_on_prop with "[][Hτ]"); [iApply row_type_sub| iApply "Hτ"|]. by iApply "Hee1". }
    iIntros "!# % % ((Hfun & HΓ3) & Hτ) /=".
    iDestruct ("Hfun" with "Hτ") as "Hfun".
    iApply brel_introduction_mono; [iApply "Hρ''ρ"|].
    iApply (brel_wand with "[Hfun HΓ3]").
    { iApply (brel_mono_on_prop with "[][HΓ3]"); [iApply row_env_sub|iApply "HΓ3" |done]. }
    iIntros "!# % % ($&$)". 
  Qed.

  (* Derived App Rules *)
  Corollary sem_typed_app τ ρ' ρ κ Γ1 Γ2 e1 e2 e1' e2' :
    ⊢ ¡ ρ' ≤ᵣ ρ -∗
    sem_typed Γ2 e1 e2 (¡ ρ') (τ -{ ρ }-∘ κ) [] -∗
    sem_typed Γ1 e1' e2' ρ τ Γ2 -∗
    sem_typed Γ1 (e1 e1') (e2 e2') ρ κ [].
  Proof.
    iIntros "#Hρ'ρ #He #He'". 
    iApply (sem_typed_app_gen with "Hρ'ρ [] He He'"). 
    iApply row_le_refl.
  Qed.

  Corollary sem_typed_app_nil τ ρ κ Γ1 Γ2 e1 e2 e1' e2' :
    ⊢ sem_typed Γ2 e1 e2 ⟨⟩ (τ -{ ρ }-∘ κ) [] -∗
    sem_typed Γ1 e1' e2' ρ τ Γ2 -∗
    sem_typed Γ1 (e1 e1') (e2 e2') ρ κ [].
  Proof.
    iIntros "#He₁ #He₂".
    iApply (sem_typed_app _ ⟨⟩%R).
    { iApply row_le_trans; [iApply (row_le_mfbang_elim_nil)|iApply row_le_nil]. }
    { iApply sem_typed_sub_nil. iApply "He₁". }
    iApply "He₂".
  Qed.

  Corollary sem_typed_app_os τ (ρ : sem_row Σ) κ Γ1 Γ2 Γ3 e1 e2 e1' e2' `{! OnceR ρ}: 
    ⊢ sem_typed Γ2 e1 e2 ρ (τ -{ ρ }-∘ κ) Γ3 -∗
    sem_typed Γ1 e1' e2' ρ τ Γ2 -∗
    sem_typed Γ1 (e1 e1') (e2 e2') ρ κ Γ3.
  Proof.
    iIntros "#He1 #He2". inv OnceR0.
    iApply sem_typed_sub_row; first iApply row_le_mfbang_elim.
    iApply (sem_typed_app_gen τ (¡ ρ)%R (¡ ρ)%R (¡ ρ)%R). 
    - iApply row_le_refl. 
    - iApply row_le_refl. 
    - iApply sem_typed_sub_row; first iApply (row_le_mfbang_intro OS).
      iApply sem_typed_sub_ty; [iApply ty_le_arr|iApply "He1"]; 
        first iApply (row_le_mfbang_intro OS); try iApply ty_le_refl.
    - iApply sem_typed_sub_row; first iApply (row_le_mfbang_intro OS).
      iApply "He2".
  Qed.

  Corollary sem_typed_app_ms τ ρ κ Γ1 Γ2 Γ3 e1 e2 e1' e2' `{! MultiE Γ3 } `{! MultiT τ } :
    ⊢ sem_typed Γ2 e1 e2 ρ (τ -{ ρ }-∘ κ) Γ3 -∗
    sem_typed Γ1 e1' e2' ρ τ Γ2 -∗
    sem_typed Γ1 (e1 e1') (e2 e2') ρ κ Γ3.
  Proof.
    iIntros "#He #He'".
    iApply (sem_typed_app_gen _ ρ ρ ρ). 
    - iApply row_le_refl.
    - iApply row_le_refl.
    - iApply "He".
    - iApply "He'".
  Qed.

  Lemma sem_typed_seq τ ρ κ Γ1 Γ2 Γ3 e1 e2 e1' e2' : 
    ⊢ sem_typed Γ1 e1 e2 ρ τ Γ2 -∗
    sem_typed Γ2 e1' e2' ρ κ Γ3 -∗
    sem_typed Γ1 (e1 ;; e1') (e2 ;; e2') ρ κ Γ3.
  Proof.
    iIntros "#He #He' !# %γ HΓ1 /=".
    iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy| iApply to_iThy_le_refl |].
    iApply (brel_wand with "[HΓ1]"); [by iApply "He"|].
    iIntros "!# % % (Hτ & HΓ2) /=". 
    brel_pures_l. brel_pures_r.
    iApply (brel_wand with "[Hτ HΓ2]"); [iApply "He'"|]; first done.
    iIntros "!# % % ($&$)".
  Qed.

  (* Generic Pair Rule *)
  Lemma sem_typed_pair_gen τ ρ κ Γ1 Γ2 Γ3 e1 e2 e1' e2' `{ ρ ᵣ⪯ₜ κ }:
    ⊢ sem_typed Γ2 e1 e2 ρ τ Γ3 -∗
    sem_typed Γ1 e1' e2' ρ κ Γ2 -∗
    sem_typed Γ1 (e1,e1') (e2, e2') ρ (τ × κ) Γ3.
  Proof.
    iIntros "#He #He' !# %γ HΓ1 //=".
    iApply (brel_bind [PairRCtx _] [PairRCtx _]); [iApply traversable_to_iThy| iApply to_iThy_le_refl |].
    iApply (brel_wand with "[HΓ1]"); first by iApply "He'".
    iIntros "!# % % (Hκ & HΓ2) /=".
    iApply (brel_bind [PairLCtx _] [PairLCtx _]); [iApply traversable_to_iThy| iApply to_iThy_le_refl|].
    iApply (brel_wand with "[Hκ HΓ2]").
    { iApply (brel_mono_on_prop with "[][Hκ]"); [by iApply row_type_sub| done| by iApply "He"]. }
    iIntros "!# % % ((Hτ & HΓ3) & Hκ) /=".
    brel_pures_l. brel_pures_r.
    by iFrame.
  Qed.

  (* TODO: Add the rest of the pair rules *)
  
  Lemma sem_typed_fst x τ κ Γ : 
    ⊢ sem_typed ((x, τ × κ) :: Γ) (Fst x) (Fst x) ⟨⟩ τ ((x, ⊤ × κ) :: Γ).
  Proof.
    iIntros "!# %γ /= (% & % & [(% & % & % & % &% & %  & Hτ & Hκ) HΓ]) //=". rewrite !lookup_fmap. rewrite H /= H0 H1.
    brel_pures_l. brel_pures_r. 
    solve_env.
  Qed.

  Lemma sem_typed_snd x τ κ Γ : 
    ⊢ sem_typed ((x, τ × κ) :: Γ) (Snd x) (Snd x) ⟨⟩ κ ((x, τ × ⊤) :: Γ).
  Proof.
    iIntros "!# %γ /= (% & % & [(% & % & % & % &% & %  & Hτ & Hκ) HΓ]) //=".
    rewrite !lookup_fmap. rewrite H /= H0 H1.
    brel_pures_l. brel_pures_r. 
    solve_env.
  Qed.

  Lemma sem_typed_pair_elim τ ρ κ ι Γ1 Γ2 Γ3 x1 x2 e1 e2 e1' e2' :
    x1 ∉ (env_dom Γ2) → x2 ∉ (env_dom Γ2) →
    x1 ∉ (env_dom Γ3) → x2 ∉ (env_dom Γ3) →
    x1 ≠ x2 →
    ⊢ sem_typed Γ1 e1 e2 ρ (τ × κ) Γ2 -∗
    sem_typed ((x1, τ) :: (x2, κ) :: Γ2) e1' e2' ρ ι Γ3 -∗
    sem_typed Γ1 (let, (x1, x2) := e1 in e1') (let, (x1, x2) := e2 in e2') ρ ι Γ3.
  Proof.
    iIntros (?????) "#He #He' !# %γ HΓ1 //=".
    iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy |iApply to_iThy_le_refl |].
    iApply (brel_wand with "[HΓ1]"); first by iApply "He".
    iIntros "!# % % ((% & % & % & % & % & % & Hτ & Hκ) & HΓ2) //=".
    rewrite H4 H5.
    brel_pures_l. brel_pures_r.
    rewrite !(delete_commute _ x1).
    rewrite !lookup_delete /=. destruct (decide _) as [[]|[]]; [|split; [done|congruence]].
    rewrite !(@decide_True _ (x2 = x2)); try done.
    rewrite !decide_False; try (intros (_& contra); done).
    brel_pures_l. brel_pures_r.
    rewrite !(delete_commute _ _ x1) -!(subst_map_insert x1) -!delete_insert_ne; try done.
    rewrite !delete_idemp.
    rewrite !decide_True; try (split; [done|congruence]).
    rewrite -!subst_map_insert.
    assert (w1 = fst (w1, w1')) as ->; first done.
    assert (w2 = fst (w2, w2')) as ->; first done.
    assert (w1' = snd (w1, w1')) as ->; first done.
    assert (w2' = snd (w2, w2')) as ->; first done.
    rewrite -!fmap_insert. simpl.
    iApply (brel_wand with "[Hτ Hκ HΓ2]"); first iApply "He'".
    - rewrite env_sem_typed_cons. iSplitL "Hτ".
      { iFrame. rewrite lookup_insert_ne; last done. by rewrite lookup_insert. }
      rewrite env_sem_typed_cons. iSplitL "Hκ"; last by do 2 (rewrite -env_sem_typed_insert; last done).
      iExists _, _. iFrame. iPureIntro. apply lookup_insert.
    - iIntros "!# % % ($ & HΓ3)". by do 2 (rewrite -env_sem_typed_insert; last done). 
  Qed.     
  
  (* Effect allocation rule *)
  (* TODO: type-related rules -- figure out where to place these *)
  Lemma brel_add_label_l_sem_sig e1 e2 l1 l1s l2s L R :
    ⊢ is_label l1 (DfracOwn 1) -∗
    BREL e1 ≤ e2 <|((l1 :: l1s, l2s, sem_sig_bottom : iThy Σ) :: L)|> {{R}} -∗
    BREL e1 ≤ e2 <|((l1s, l2s, sem_sig_bottom : iThy Σ) :: L)|> {{R}}.
  Proof.
    iIntros "Hl1 Hbrel
      [#Hvalid_l1s #Hvalid_l2s]
      [%Hdistinct_l1s %Hdistinct_l2s]".
    iDestruct (distinct_l_cons with "[$] [$] [//]") as %Hdistinct_cons_l1s.
    iApply fupd_rel.
    iMod (is_label_persist with "Hl1") as "#Hl1". iModIntro.
    iSpecialize ("Hbrel" with "[] []").
    { iSplit; [|done]. rewrite !/valid_l !labels_l_cons //=. by iSplit. }
    { by iSplit. }
    iApply (rel_introduction_mono with "Hbrel").
    iApply (iThy_le_trans _ (to_iThy L)).
    { iApply (iThy_le_trans _ (iThySum (iThyTraverse (l1 :: l1s) l2s sem_sig_bottom) (to_iThy L))).
      { iApply iThy_le_to_iThy_sum. }
      iIntros "!> %%% [(%&%&%&%&%&%&%&%&%&(%&%&%&%&%&%&%&H'&?)&?)|?]";[done|done]. }
    { by iApply iThy_le_to_iThy_2. }
  Qed.
 
  Lemma brel_add_label_r_sem_sig e1 e2 l1s l2 l2s L R :
    ⊢ spec_labels_frag l2 (DfracOwn 1) -∗
    BREL e1 ≤ e2 <|((l1s, l2 :: l2s, sem_sig_bottom : iThy Σ) :: L)|> {{R}} -∗
    BREL e1 ≤ e2 <|((l1s, l2s, sem_sig_bottom : iThy Σ) :: L)|> {{R}}.
  Proof.
    iIntros "Hl2 Hbrel
      [#Hvalid_l1s #Hvalid_l2s]
      [%Hdistinct_l1s %Hdistinct_l2s]".
    iDestruct (distinct_r_cons with "[$] [$] [//]") as %Hdistinct_cons_l2s.
    iApply fupd_rel.
    iMod (spec_label_persist with "Hl2") as "#Hl2". iModIntro.
    iSpecialize ("Hbrel" with "[] []").
    { iSplit; [done|]. rewrite !/valid_r !labels_r_cons //=. by iSplit. }
    { by iSplit. }
    iApply (rel_introduction_mono with "Hbrel").
    iApply (iThy_le_trans _ (to_iThy L)).
    { iApply (iThy_le_trans _ (iThySum (iThyTraverse l1s (l2 :: l2s) sem_sig_bottom) (to_iThy L))).
      { iApply iThy_le_to_iThy_sum. }
      iIntros "!> %%% [(%&%&%&%&%&%&%&%&%&(%&%&%&%&%&%&%&H'&?)&?)|?]";[done|done]. }
    { by iApply iThy_le_to_iThy_2. }
  Qed.
  
  Lemma sem_typed_effect Γ e1 e2 (ρ : sem_row Σ) τ :
    ⊢ (∀ l1 l2 : label, sem_typed Γ (lbl_subst "s" l1 e1) (lbl_subst "s'" l2 e2) (sem_row_cons l1 l2 (⊥ : sem_sig Σ) ρ) τ Γ) -∗
    sem_typed Γ (effect "s" e1) (effect "s'" e2) ρ τ Γ.
  Proof.
    iIntros "#H !# % Hvs /=".
    iApply (brel_effect_l _ _ []). iIntros (l1) "!> Hl1 !>". 
    iApply (brel_effect_r _ _ _ []). iIntros (l2) "Hl2 !>". simpl.
    iDestruct ("H" $! l1 l2 with "Hvs") as "He".
    iApply (brel_introduction_mono (([], [], sem_sig_bottom : iThy Σ) :: (iLblSig_to_iLblThy ρ))).
    { iSplit.
      - iApply (iThy_le_trans _ (iThySum (iThyTraverse [] [] sem_sig_bottom) (to_iThy (iLblSig_to_iLblThy ρ)))).
        { simpl. iApply iThy_le_to_iThy_sum. }
        iIntros "!> %%% [(%&%&%&%&%&%&%&%&%&(%&%&%&%&%&%&%&H'&?)&?)|?]";[done|done].
      - iSplit; iModIntro.
        + iApply valid_submseteq'; [rewrite labels_l_cons | rewrite labels_r_cons]; done.
        + iIntros (Hd). iPureIntro. apply (distinct_submseteq' _ (iLblSig_to_iLblThy ρ)); done. }
    iApply (brel_add_label_l_sem_sig with "Hl1").
    iApply (brel_add_label_r_sem_sig with "Hl2").
    simpl.
    by rewrite !subst_map_lbl_subst. 
  Qed.

End compatibility.

    

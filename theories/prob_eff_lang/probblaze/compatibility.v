
(* compatibility.v *)

(* The compatibility lemmas are what one gets when the syntactic typing judgment
   is replaced with a semantic typing judgment. *)

From iris.proofmode Require Import base tactics.
From iris.base_logic.lib Require Import iprop invariants.

(* Local imports *)
From clutch.prob_eff_lang.probblaze Require Import notation mode sem_def sem_sig sem_types sem_row sem_env logic sem_judgement.


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

  (* Lemma sem_typed_val τ Γ v1 v2 : 
       ⊨ᵥ v1 ≤ v2 : τ -∗ Γ ⊨ v1 ≤ v2 : ⟨⟩ : τ ⫤ Γ.
     Proof.
       iIntros "#Hv". rewrite - {1} (app_nil_l Γ).
       iApply sem_typed_oval. by iApply sem_oval_typed_val.
     Qed. *)

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

  (* Lemma sem_typed_closure τ ρ κ f x e :
       match f with BNamed f => BNamed f ≠ x | BAnon => True end →
       (x, τ) ::? (f, τ -{ ρ }-> κ) ::? [] ⊨ e : ρ : κ ⫤ [] -∗ 
       ⊨ᵥ (rec: f x := e) : (τ -{ ρ }-> κ).
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
     Qed.
     
     Lemma sem_typed_Tclosure τ v :
       (∀ α, ⊨ᵥ v : τ α) -∗ 
       ⊨ᵥ v : (∀ₜ α, τ α).
     Proof.
       iIntros "#He !# %u". rewrite /sem_val_typed /=. iApply "He".
     Qed.
     
     (* row abstraction and application *)
     Lemma sem_typed_Rclosure C v : 
       (∀ θ, ⊨ᵥ v : C θ) -∗
       ⊨ᵥ v : (∀ᵣ θ , C θ)%T.
     Proof.
       iIntros "#He !# %u". rewrite /sem_val_typed /=. iApply "He".
     Qed.
     
     (* mode abstraction and application *)
     Lemma sem_typed_Mclosure C v : 
       (∀ ν, ⊨ᵥ v : C ν) -∗
       ⊨ᵥ v : (∀ₘ ν , C ν)%T.
     Proof.
       iIntros "#He !# %u". rewrite /sem_val_typed /=. iApply "He". 
     Qed. *)

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

    

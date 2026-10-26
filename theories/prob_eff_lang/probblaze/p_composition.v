From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import agree excl auth frac excl_auth.
From iris.algebra.lib Require Import dfrac_agree.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode
 spec_rules spec_ra class_instances.
From clutch.prob_eff_lang.probblaze Require Import tactics.
From clutch.prob_eff_lang.probblaze Require Import sem_types sem_row sem_sig sem_judgement sem_def valgroup sem_env.

(*Import fingroup.

Import fingroup.fingroup.


*)
Import valgroup_tactics.
Section parallel_composition.
  Context `{probblazeRGS Σ}.
 
  (* r_x are effect operations raised by the functionality f_x, and c_x are effect operations
     handled by f_x.*) 
 
  Definition right_composition : val :=
    λ: "F₁" "F₂" "f" "r",
      let, ("r₁", "r₂") := "r" in
     "F₁" (λ: "h₁",
             "F₂" (λ: "h₂", "f" ("h₂","h₁")) "r₁") "r₂".  

  Definition functionality_composition : val :=
    λ: "F" "G" "f" "r",
      let, ("rH", "rF") := "r" in
      ("F" (λ: "rG", "G" "f" ("rH", "rG")) "rF").

  (*Notation " F₁ ||ₗ F₂" := (left_composition F₁ F₂)%V (at level 10). *)

  Notation "F₁ ||ᵣ F₂" := (right_composition F₁ F₂)%V (at level 10).
  
  Notation "F '∘F' G" := (functionality_composition F G)%V (at level 10).

 
  Definition func_comp : val :=
   λ: "F" "G" "f", "F" ("G" "f").

  Notation "F ∘f G" := (func_comp F G)%V (at level 10).

  Definition τ := ( ∀ᵣ θ, ∀ₜ α ,α ⊸ 𝟙)%T.
    
  Definition τ__f θ τ1' τ2' := (∀ᵣ θ1, ∀ᵣ θ2, ((τ1' θ1) × (τ2' θ2)) -{ sem_row_union θ1 (sem_row_union θ2 θ) }-∘ 𝟙)%T.
  Definition τ__fu θ τ1' τ2' := (∀ᵣ θ1, ∀ᵣ θ2, ((τ1' θ1) × (τ2' θ2)) -{ sem_row_union (¡θ1)%R (sem_row_union (¡θ2)%R θ) }-∘ 𝟙)%T.
  Definition τ__F τ τ' := (∀ᵣ θ, (∀ᵣ θ₁, τ' θ₁ -{ sem_row_union θ₁ θ}-∘ 𝟙) ⊸ (∀ᵣ θ₂, τ θ₂ -{ sem_row_union θ₂ θ }-∘ 𝟙))%T.
  Definition τ__FO τ τ' := (∀ᵣ θ, (∀ᵣ θ₁, τ' θ₁ -{ sem_row_union (¡θ₁) θ}-∘ 𝟙) ⊸ (∀ᵣ θ₂, τ θ₂ -{ sem_row_union (¡θ₂) θ }-∘ 𝟙))%T.
  Definition τ__FC τ τ' := (∀ᵣ θ, (∀ᵣ θ₁, τ' θ₁ -{ sem_row_union θ₁ θ}-∘ 𝟙) ⊸ (∀ᵣ θ₂, τ θ₂ -{ sem_row_union (¡θ₂) θ }-∘ 𝟙))%T. 
 
  Lemma iLblSig_to_iLblThy_distr L1 L2 :
    @iLblSig_to_iLblThy Σ (L1 ++ L2) = iLblSig_to_iLblThy L1 ++ (iLblSig_to_iLblThy L2).
  Proof.
    induction L1; first done.
    simpl. by rewrite IHL1.
  Qed.  
  
  Lemma func_comp_left (F1 F2 F : expr) τ τ' τ'':
    is_closed_expr ∅ F1 →
    is_closed_expr ∅ F2 →
    is_closed_expr ∅ F ->
    ⊢ sem_typed [] F1 F2 ⊥ (∀ᵣ θ,τ θ ⊸ τ' θ)%T [] -∗
      sem_typed [] F F ⊥ (∀ᵣ θ, τ'' θ ⊸ τ θ)%T [] -∗
    sem_typed [] (F1 ∘f F ) (F2 ∘f F) ⊥ (∀ᵣ θ, τ'' θ ⊸ τ' θ)%T [].
  Proof.
    iIntros (HF1closed HF2closed HFclosed) "#HFF #HF". rewrite /sem_val_typed /sem_typed //=.
    simpl.
    iIntros "!> %vs Hvs".
    rewrite /func_comp /=. 
    iAssert ([] ⊨ₑ ∅) as "HΓ"; first done.
    iSpecialize ("HFF" with "HΓ").
    iSpecialize ("HF" with "HΓ").
    erewrite !subst_map_is_closed_empty; try done. 
    iApply (brel_bind' [_] [_]); [iApply traversable_to_iThy_nil |].
    iApply (brel_wand with "HF").
    iIntros (v1 v2) "!# Hv1v2".  
    iApply (brel_bind' [_; _] [_ ;_ ]); [iApply traversable_to_iThy_nil|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS _ _ [] [] with "[][$HFF]");
      [iApply to_iThy_le_bot|].
    simpl.
    iIntros (v0 v3) "Hv0v3".
    brel_pures'.
    iModIntro.
    iSplitL "Hv1v2 Hv0v3"; try done.
    rewrite /sem_ty_arr /=.
    iIntros (θ w1 w2) "Hw1w2".
    brel_pures'. 
    iDestruct "Hv1v2" as "[Hv1v2 _] ".
    iSpecialize ("Hv1v2" $! θ).
    iSpecialize ("Hv1v2" $! w1 w2).
    iDestruct ("Hv1v2" with "Hw1w2") as "Hv1v2'".
    iDestruct "Hv0v3" as "[Hv0v3 _]".
    iSpecialize ("Hv0v3" $! θ).
    iApply (brel_bind' [_] [_] with "[][Hv0v3 Hv1v2']"); [iApply traversable_to_iThy_nil|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS _ _ [] [] with "[][Hv1v2']");
      [iApply to_iThy_le_bot| by iApply "Hv1v2'" |].
    simpl.
    iIntros (v4 v5) "Hv4v5".
    iSpecialize ("Hv0v3" $! v4 v5).
    iDestruct ("Hv0v3" with "Hv4v5") as "Hv0v3'".
    iApply "Hv0v3'".
  Qed. 

  
  Lemma parallel_comp_right (F1 F2 F : expr) τ1 τ2 τ1' τ2' :
    is_closed_expr ∅ F1 ->
    is_closed_expr ∅ F2 ->
    is_closed_expr ∅ F ->
    ⊢ sem_typed [] F1 F2 ⊥ (τ__FO τ2 τ2')%T [] -∗
    
    sem_typed [] F F ⊥ (τ__FO τ1 τ1')%T [] -∗
    
    sem_typed [] (F1 ||ᵣ F) (F2 ||ᵣ F) ⊥ (∀ᵣ θ, (τ__fu θ τ1' τ2') ⊸ (∀ᵣ θ1, ∀ᵣ θ2, (τ1 θ1 × τ2 θ2) -{ sem_row_union (¡θ1) (sem_row_union (¡θ2) θ) }-∘ 𝟙))%T [].
  Proof. 
     iIntros (HisclosedF1 HisclosedF2 HisclosedF) "#HFF #HF".
    iIntros (?) "!# Hvs //=".
    unfold right_composition.
    erewrite !subst_map_is_closed_empty; try done.
    rewrite /sem_typed /τ__F //=. 
    iAssert ([] ⊨ₑ ∅) as "HΓ"; first done. iSpecialize ("HFF" with "HΓ").
    iSpecialize ("HF" with "HΓ").
    rewrite !subst_map_empty.
    iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot |].
    assert (to_iThyIfMono OS [] = []) as <- by done. 
    iApply (brel_mono OS with "[][$HF]");[iApply to_iThy_le_refl |simpl].
    iIntros (vF vF') "HvF".
    iDestruct "HvF" as "[HvF _]".
    iApply (brel_bind [_ ; _] [_ ; _]); [iApply traversable_to_iThy_nil | iApply to_iThy_le_bot |].
    assert (to_iThyIfMono OS [] = []) as <- by done.  
    iApply (brel_mono OS with "[][$HFF]");[iApply to_iThy_le_refl | simpl].
    brel_pures'.
    iIntros (vF₁ vF₂) "HF1F2".
    iDestruct "HF1F2" as "[HF1F2 _]".
    brel_pures'. iModIntro.
    iSplitR "Hvs"; try done. 
    iIntros "%θ %f1 %f2 Hff". brel_pures'.
    iIntros "!> %θ1 %θ2 %r1 %r2 Heffs".
    brel_pures'.
    rewrite /sem_ty_prod.
    unfold τ__f.
    iDestruct "Heffs" as ( w1 w1' w2 w2') "[%Hr1 [%Hr2 [Hτ1 Hτ2]]]".
    rewrite -> Hr1. rewrite -> Hr2.
    brel_pures.   
    iAssert ((∀ᵣ θ2, τ2' θ2 -{ sem_row_union (¡θ2)%R (sem_row_union (¡ θ1)%R θ) }-∘ 𝟙)%T
               (λ: "h₁", vF (λ: "h₂", f1 ("h₂", "h₁")) w1)%V
               (λ: "h₁", vF' (λ: "h₂", f2 ("h₂", "h₁")) w1')%V) with "[Hτ1 Hff HvF]" as "Hclients".
    { iIntros (θ2' v1 v2) "Hτ2'". brel_pures'.
       
      iAssert ((∀ᵣ θ2, τ1' θ2 -{ sem_row_union (¡θ2)%R (sem_row_union (¡θ2')%R θ) }-∘ 𝟙)%T (λ: "h₂", f1 ("h₂", v1))%V (λ: "h₂", f2 ("h₂", v2))%V) 
        with "[Hτ2' Hff]" as "H".
      { iIntros (θ1' v1' v2') "Hτ1'". 
        brel_pures'.
        iSpecialize ("Hff" $! θ1' θ2'). 
         iAssert  (((τ1' θ1') × (τ2' θ2'))%T (v1', v1)%V (v2', v2)%V) with "[Hτ1' Hτ2']" as "Hprod".
        { rewrite /sem_ty_prod /=.  
          iExists v1', v2', v1, v2.
          iSplitR "Hτ1' Hτ2'"; [iPureIntro; reflexivity |].
          iSplitR "Hτ1' Hτ2'"; [iPureIntro; reflexivity | iFrame ]. }
        iDestruct ("Hff" with "Hprod") as "Hff".
        rewrite !iLblSig_to_iLblThy_distr.
        iApply (brel_introduction_mono (iLblSig_to_iLblThy (¡ θ1')%R ++ iLblSig_to_iLblThy (¡ θ2')%R ++ iLblSig_to_iLblThy θ)).
        { iApply to_iThy_le_intro'; solve_submseteq. }
        iApply "Hff". }
       rewrite !iLblSig_to_iLblThy_distr. 
      iApply (brel_bind [_] [_]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
      assert (to_iThyIfMono OS [] = []) as <- by done.  
      iApply (brel_mono OS with "[][H HvF]");[iApply to_iThy_le_refl |simpl |].
      {
        iApply (brel_bind [_] [_]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
      assert (to_iThyIfMono OS [] = []) as <- by done. 
      iApply (brel_mono OS with "[][HvF][H]");[iApply to_iThy_le_refl | |].
        + rewrite /sem_val_typed /=.
          iApply brel_value.
          iIntros "Hown".
          iModIntro. iFrame.
          iApply "HvF".
        + simpl.
          iIntros (v v') "Hf1f2".
          unfold τ__FO.
          iSpecialize ("Hf1f2" with "H").
          iApply "Hf1f2".
      }
      simpl.
      iIntros (v0 v3) "Hv0v3". 
      iSpecialize ("Hv0v3" with "Hτ1").  
      iApply (brel_introduction_mono ((iLblSig_to_iLblThy (¡ θ1)%R ++ iLblSig_to_iLblThy (¡θ2')%R ++ iLblSig_to_iLblThy θ))).
      { iApply to_iThy_le_intro'; solve_submseteq. }
      rewrite !iLblSig_to_iLblThy_distr. 
      iApply "Hv0v3".
    }
    unfold τ__FC. 
    iSpecialize ("HF1F2" with "Hclients"). 
    iApply (brel_bind [_] [_] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HF1F2]"); [iApply to_iThy_le_refl|simpl].
    iIntros (??) "Hvv".
    iSpecialize ("Hvv" $! θ2 with "Hτ2").
    rewrite !iLblSig_to_iLblThy_distr.
    iApply (brel_introduction_mono (iLblSig_to_iLblThy (¡ θ2)%R ++ iLblSig_to_iLblThy (¡ θ1)%R ++ iLblSig_to_iLblThy θ)).
    { iApply to_iThy_le_intro'; solve_submseteq. }
    iApply "Hvv".
  Qed.
  
  Definition τ__F' θ τ τ' := ((∀ᵣ θ₁, τ' θ₁ -{ sem_row_union θ₁ θ}-∘ 𝟙) ⊸ (∀ᵣ θ₂, τ θ₂ -{ sem_row_union θ₂ θ }-∘ 𝟙))%T.
  Definition τ__f' θ τ2' := (∀ᵣ θ2, τ2' θ2 -{ (sem_row_union θ2 θ) }-∘ 𝟙)%T.
  Definition τ__fO θ gk := (∀ᵣ θ2, gk θ2 -{ sem_row_union θ2 θ }-∘ 𝟙)%T.
 
  Lemma func_comp_parallel_comp_assoc (F J G : expr) (f x : string) τ1 τ2 τG τ1' τ2' θ :
    (BNamed f) ≠ (BNamed x) →
    is_closed_expr ∅ F ->
    is_closed_expr ∅ J ->
    ⊢ sem_typed [] F F ⊥ (τ__FO τ2 τG)%T [] -∗ 
    (∀ θ, ∀ θG, sem_typed [(f, τ__fO θ τ1'); (x, τG θG)] G G (sem_row_union (¡ θG)%R θ) 𝟙%T []) -∗ 
    sem_typed [] J J ⊥ (τ__F τ1 τ2')%T [] -∗
    sem_typed [] ((F ∘f (λ: f x, G)%V) ||ᵣ J) 
      (F ∘F ((λ: f x, G)%V ||ᵣ J)) ⊥ ((τ__f θ τ2' τ1') ⊸ (∀ᵣ θ1, ∀ᵣ θ2, (τ1 θ1 × τ2 θ2) -{ sem_row_union θ1 (sem_row_union (¡ θ2)%R θ) }-∘ 𝟙))%T []. 
  Proof.  
    iIntros (Hfx HisclosedF HisclosedJ) "#HFF #HGG #HJJ !# %vs _". simpl.
    unfold func_comp,right_composition,functionality_composition.
    brel_pures'.
    rewrite /sem_typed /=. 
    iAssert ([] ⊨ₑ ∅) as "HΓ"; first done.
    iSpecialize ("HFF" with "HΓ").
    iSpecialize ("HJJ" with "HΓ").
    rewrite !subst_map_is_closed_empty; try done. 
    iApply (brel_bind [AppRCtx _] [AppRCtx _ ; _]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot |].
    assert (to_iThyIfMono OS [] = []) as <- by done. 
    iApply (brel_mono OS with "[][$HJJ]");[iApply to_iThy_le_refl |simpl ].
    iIntros (vJ1 vJ2) "(HJ1J2 & _)".
    iApply (brel_bind [_; _ ; _ ; _] [AppLCtx _ ; _]); [iApply traversable_to_iThy_nil | iApply to_iThy_le_bot |].        
    assert (to_iThyIfMono OS [] = []) as <- by done. 
    iApply (brel_mono OS with "[][$HFF]");[iApply to_iThy_le_refl |simpl].
    iIntros (vF1 vF2) "(HF1F2 & _)".
    brel_pures'.
    iModIntro; iSplit; last done.
    iIntros (f1 f2) "Hff".
    brel_pures'.
    iModIntro.
    iIntros (θ1 θ2 v v') "Heffs".
    brel_pures'. 
    rewrite /sem_ty_prod.
    iDestruct "Heffs" as ( w1 w1' w2 w2') "[%Hr1 [%Hr2 [Hτ1 Hτ2]]]". 
    rewrite -> Hr1.
    rewrite -> Hr2. 
    brel_pures_l 3.  
    brel_pures_r. 
    brel_pures'.
    rewrite decide_True; last (split; done).
    simpl. 
    iAssert ((∀ᵣ θG, τG θG -{ sem_row_union (¡ θG) (sem_row_union θ1 θ) }-∘ 𝟙)%T
               (λ: x, val_subst f (λ: "h₁", vJ1 (λ: "h₂", f1 ("h₂","h₁")) w1) G)%V          
               (λ: "rG", (λ: "f" "r",
                            let: "r₂" := "r" in
                            let: "r₁" := Fst "r₂" in
                            let: "r₂" := Snd "r₂" in
                            (λ: f x, G)%V (λ: "h₁", vJ2 (λ: "h₂", "f" ("h₂", "h₁")) "r₁") "r₂")%V f2 (w1', "rG"))%V) with "[Hτ1 Hff HJ1J2]" as "Hgg". 
    { iIntros (θG rg1 rg2) "HτG".
      brel_pures_l.
      brel_pures_r 1. 
      brel_pures'.
      rewrite decide_True; last (split; done). 
      iSpecialize ("HGG" $! (sem_row_union θ1 θ) θG).
      brel_pures.
      iAssert ((τ__f' (sem_row_union θ1 θ) τ1' (λ: "h₁", vJ1 (λ: "h₂", f1 ("h₂", "h₁")) w1)%V (λ: "h₁", vJ2 (λ: "h₂", f2 ("h₂", "h₁")) w1')%V)) with "[Hff Hτ1 HJ1J2]" as "Hff".
      { iIntros (θ1' h1 h1') "Hhh". brel_pures'.
        iApply (brel_bind [_] [_]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot |].
        assert (to_iThyIfMono OS [] = []) as <- by done.
        iApply (brel_mono OS with "[][HJ1J2 Hff Hhh]"); [iApply to_iThy_le_refl|simpl|].
        { 
          iApply "HJ1J2". iIntros (θJ h2 h2') "Hhh2". brel_pures'.
          iAssert (((τ2' θJ) × (τ1' θ1'))%T (h2, h1)%V (h2', h1')%V) with "[Hhh2 Hhh] " as "Hprod".
         { rewrite /sem_ty_prod /=.  
          iExists h2, h2', h1, h1'.
          iSplitR "Hhh2 Hhh"; [iPureIntro; reflexivity |].
          iSplitR "Hhh2 Hhh"; [iPureIntro; reflexivity | iFrame ]. }
          iDestruct ("Hff" with "Hprod") as "Hff".
            simpl; by iApply "Hff". }
        simpl. iIntros (g1 g2) "Hgg".  
        iDestruct ("Hgg" with "Hτ1") as "Hgg".
        rewrite !iLblSig_to_iLblThy_distr.
        iApply (brel_introduction_mono (iLblSig_to_iLblThy θ1 ++ iLblSig_to_iLblThy θ1' ++ iLblSig_to_iLblThy θ)); [|done].
        iApply to_iThy_le_intro'; solve_submseteq. }
      iAssert ([(f, τ__f' (sem_row_union θ1 θ) τ1'); (x, τG θG)] ⊨ₑ {[ x := (rg1, rg2); f := ((λ: "h₁", vJ1 (λ: "h₂", f1 ("h₂","h₁")) w1)%V, (λ: "h₁", vJ2 (λ: "h₂", f2 ("h₂", "h₁")) w1')%V)]}) with "[HτG Hff]" as "HΓ'". 
      { solve_env. intros heq. apply Hfx. simpl. by destruct heq. }
      iDestruct ("HGG" with "HΓ'") as "Hrel".
      iApply (brel_wand with "[Hrel]"). 
      { rewrite !fmap_insert !fmap_empty //=. 
        rewrite !subst_map_insert !delete_insert_ne //=.
        2,3 : intros heq; apply Hfx; by destruct heq.
        rewrite !delete_empty.
        rewrite !subst_map_insert !delete_empty subst_map_empty.
       
        iApply "Hrel". }
      iIntros (??) "!# ($&_)". }

    iSpecialize ("HF1F2" with "Hgg").
    iApply (brel_bind [_] [_] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HF1F2]"); [iApply to_iThy_le_refl|simpl].
    iIntros (??) "Hτ".
    iSpecialize ("Hτ" with "Hτ2").
    rewrite !iLblSig_to_iLblThy_distr.
    iApply (brel_introduction_mono (iLblSig_to_iLblThy (¡ θ2)%R ++ iLblSig_to_iLblThy θ1 ++ iLblSig_to_iLblThy θ)); last done.
    iApply to_iThy_le_intro'; solve_submseteq.
  Qed.
  
  Lemma func_comp_parallel_comp_assoc_rev (F J G : expr) (f x : string) τ1 τ2 τG τ1' τ2' θ :
    (BNamed f) ≠ (BNamed x) →
    is_closed_expr ∅ F ->
    is_closed_expr ∅ J ->
    ⊢ sem_typed [] F F ⊥ (τ__FO τ2 τG)%T [] -∗
    (∀ θ, ∀ θG, sem_typed [(f, τ__f' θ τ1'); (x, τG θG)] G G (sem_row_union (¡ θG)%R θ) 𝟙%T []) -∗
    sem_typed [] J J ⊥ (τ__FC τ1 τ2')%T [] -∗
    sem_typed [] (F ∘F ((λ: f x, G)%V ||ᵣ J))
    ((F ∘f (λ: f x, G)%V) ||ᵣ J)  ⊥ ((τ__f θ τ2' τ1') ⊸ (∀ᵣ θ1, ∀ᵣ θ2, (τ1 θ1 × τ2 θ2) -{ sem_row_union (¡θ1)%R (sem_row_union (¡ θ2)%R θ) }-∘ 𝟙))%T [].          
  Proof.      
    iIntros (Hfx HisclosedF HisclosedJ) "#HFF #HGG #HJJ !# %vs _". simpl. 
    unfold func_comp,right_composition,functionality_composition. 
    brel_pures'.
    rewrite /sem_typed /=. 
    iAssert ([] ⊨ₑ ∅) as "HΓ"; first done.
    iSpecialize ("HFF" with "HΓ").
    iSpecialize ("HJJ" with "HΓ").
    rewrite !subst_map_is_closed_empty; try done. 
    iApply (brel_bind [AppRCtx _ ; _] [AppRCtx _ ]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot |].
    assert (to_iThyIfMono OS [] = []) as <- by done. 
    iApply (brel_mono OS with "[][$HJJ]");[iApply to_iThy_le_refl |simpl ].
    iIntros (vJ1 vJ2) "(HJ1J2 & _)".
    iApply (brel_bind [AppLCtx _; _ ] [ _ ; _ ; _ ; _]); [iApply traversable_to_iThy_nil | iApply to_iThy_le_bot |].        
    assert (to_iThyIfMono OS [] = []) as <- by done. 
    iApply (brel_mono OS with "[][$HFF]");[iApply to_iThy_le_refl |simpl].
    iIntros (vF1 vF2) "(HF1F2 & _)".
    brel_pures'.
    iModIntro; iSplit; last done.  
    iIntros (f1 f2) "Hff".
    brel_pures'.
    iModIntro.
    iIntros (θ1 θ2 v v') "Heffs".
    brel_pures'.
    rewrite /sem_ty_prod.
    iDestruct "Heffs" as ( w1 w1' w2 w2') "[%Hr1 [%Hr2 [Hτ1 Hτ2]]]". 
    rewrite -> Hr1.
    rewrite -> Hr2. 
    brel_pures_r 3.
    brel_pures_l.
    brel_pures'. 
    rewrite decide_True; last (split; done). 
    iAssert ((∀ᵣ θG, τG θG -{ sem_row_union (¡ θG)%R (sem_row_union (¡ θ1)%R θ) }-∘ 𝟙)%T 
               (λ: "rG", (λ: "f" "r",
                            let: "r₂" := "r" in
                            let: "r₁" := Fst "r₂" in
                            let: "r₂" := Snd "r₂" in
                            (λ: f x, G)%V (λ: "h₁", vJ1 (λ: "h₂", "f" ("h₂","h₁")) "r₁") "r₂")%V f1 (w1,"rG"))%V
               (λ: x, val_subst f (λ: "h₁", vJ2 (λ: "h₂", f2 ("h₂","h₁")) w1') G)%V) with "[Hτ1 Hff HJ1J2]" as "Hgg".
    { iIntros (θG rg1 rg2) "HτG".
      brel_pures'.
      rewrite decide_True; last (split; done). 
      iSpecialize ("HGG" $! (sem_row_union (¡ θ1)%R θ) θG). 
      iAssert ((τ__f' (sem_row_union (¡ θ1)%R θ) τ1' (λ: "h₁", vJ1 (λ: "h₂", f1 ("h₂","h₁")) w1)%V (λ: "h₁", vJ2 (λ: "h₂", f2 ("h₂","h₁")) w1')%V)) with "[Hff Hτ1 HJ1J2]" as "Hff".
      { iIntros (θ1' h1 h1') "Hhh". brel_pures'.
        iApply (brel_bind [_] [_]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot |].
        assert (to_iThyIfMono OS [] = []) as <- by done.
        iApply (brel_mono OS with "[][HJ1J2 Hff Hhh]"); [iApply to_iThy_le_refl|simpl|]. 
        { iApply "HJ1J2". iIntros (θJ h2 h2') "Hhh2". brel_pures'.
          unfold τ__f.
          iAssert (((τ2' θJ) × (τ1' θ1'))%T (h2, h1)%V (h2', h1')%V) with "[Hhh Hhh2]" as "Hprod".
          { rewrite /sem_ty_prod /=.  
          iExists h2, h2', h1, h1'.
          iSplitR "Hhh2 Hhh"; [iPureIntro; reflexivity |].
          iSplitR "Hhh2 Hhh"; [iPureIntro; reflexivity | iFrame ].
          }
          iDestruct ("Hff" with "Hprod") as "Hff".  
          iApply "Hff". }  
        simpl. iIntros (g1 g2) "Hgg".  
        iDestruct ("Hgg" with "Hτ1") as "Hgg".
        rewrite !iLblSig_to_iLblThy_distr.  
        iApply (brel_introduction_mono (iLblSig_to_iLblThy (¡ θ1)%R ++ iLblSig_to_iLblThy θ1' ++ iLblSig_to_iLblThy θ)); [|done].
        iApply to_iThy_le_intro'; solve_submseteq. }
      iAssert ([(f, τ__f' (sem_row_union  (¡ θ1)%R θ) τ1'); (x, τG θG)] ⊨ₑ {[ x := (rg1, rg2); f := ((λ: "h₁", vJ1 (λ: "h₂", f1 ("h₂","h₁")) w1)%V, (λ: "h₁", vJ2 (λ: "h₂", f2 ("h₂","h₁")) w1')%V)]}) with "[HτG Hff]" as "HΓ'". 
      { solve_env. intros heq. apply Hfx. simpl. by destruct heq. } 
      iDestruct ("HGG" with "HΓ'") as "Hrel". 
      iApply (brel_wand with "[Hrel]"). 
      { rewrite !fmap_insert !fmap_empty //=. 
        rewrite !subst_map_insert !delete_insert_ne //=.
        2,3 : intros heq; apply Hfx; by destruct heq.
        rewrite !delete_empty.
        rewrite !subst_map_insert !delete_empty subst_map_empty.
        iApply "Hrel". }
      iIntros (??) "!# ($&_)". 
     }
    unfold τ__FO.
    iSpecialize ("HF1F2" with "Hgg").
    iApply (brel_bind [_] [_] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done. 
    iApply (brel_mono OS with "[][$HF1F2]"); [iApply to_iThy_le_refl|simpl].
    iIntros (??) "Hτ".
    iSpecialize ("Hτ" with "Hτ2").
    rewrite !iLblSig_to_iLblThy_distr.
    iApply (brel_introduction_mono (iLblSig_to_iLblThy (¡ θ2)%R ++ iLblSig_to_iLblThy  (¡ θ1)%R ++ iLblSig_to_iLblThy θ)); last done.
    iApply to_iThy_le_intro'; solve_submseteq.
  Qed.

  Lemma func_comp_assoc (F G J : expr) τ1 τ2 τ3 τ4 :
    is_closed_expr ∅ F ->
    is_closed_expr ∅ G ->
    is_closed_expr ∅ J ->
    ⊢ sem_typed [] F F ⊥ (∀ᵣ θ, τ3 θ ⊸ τ4 θ)%T [] -∗
    sem_typed [] G G ⊥ (∀ᵣ θ, τ2 θ ⊸ τ3 θ)%T [] -∗
    sem_typed [] J J ⊥ (∀ᵣ θ, τ1 θ ⊸ τ2 θ)%T [] -∗
    sem_typed [] (F ∘f (G ∘f J)) ((F ∘f G) ∘f J) ⊥ (∀ᵣ θ, τ1 θ ⊸ τ4 θ)%T [].
  Proof. 
    iIntros (HisclosedF HisclosedG HisclosedJ) "#HFF #HGG #HJJ !# %vs _". simpl.
    unfold func_comp, functionality_composition.
    brel_pures'.
    rewrite /sem_typed /=.
    iAssert ([] ⊨ₑ ∅) as "HΓ"; first done.
    iSpecialize ("HFF" with "HΓ").
    iSpecialize ("HJJ" with "HΓ").
    iSpecialize ("HGG" with "HΓ").
    rewrite !subst_map_is_closed_empty; try done.  
    brel_pures'. 
    iApply (brel_bind' [_ ; _] [_]); [iApply traversable_to_iThy_nil|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HJJ]"); [iApply to_iThy_le_refl|simpl].
    iIntros (vJ1 vJ2) "(HvJ & _)". 
    brel_pures'. 
    iApply (brel_bind' [_ ; _ ; _] [ _ ; _ ; _]); [iApply traversable_to_iThy_nil|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
     iApply (brel_mono OS with "[][$HGG]"); [iApply to_iThy_le_refl|simpl].
     iIntros (vG1 vG2) "(HvG & _)".
     brel_pures'.
     iApply (brel_bind' [_ ; _] [_ ; _ ; _ ; _]); [iApply traversable_to_iThy_nil|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HFF]"); [iApply to_iThy_le_refl|simpl].
    iIntros (vF1 vF2) "HvF".
    iDestruct "HvF" as "(HvF & _)".
    brel_pures'.
    iModIntro; iSplitL "HvJ HvG HvF"; last done.
    rewrite /sem_ty_arr /=.
    iIntros (θ v1 v2) "Hτ1".
    iSpecialize ("HvJ" with "Hτ1").
    brel_pures'. 
    iApply (brel_bind' [_ ; _] [_ ]);  [iApply traversable_to_iThy_nil|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HvJ]"); [iApply to_iThy_le_refl|simpl].
    iIntros (v v') "Hvv'".
    iSpecialize ("HvG" with "Hvv'").
    brel_pures'.
    iApply (brel_bind' [_ ] [_ ]);  [iApply traversable_to_iThy_nil|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HvG]"); [iApply to_iThy_le_refl|simpl].
    iIntros (v3 v4) "Hv3v4".
    iSpecialize ("HvF" with "Hv3v4").
    iApply "HvF".
  Qed. 
   
   

  Lemma func_comp_assoc_rev (F G J : expr) τ1 τ2 τ3 τ4 :
    is_closed_expr ∅ F ->
    is_closed_expr ∅ G ->
    is_closed_expr ∅ J ->
    ⊢ sem_typed [] F F ⊥ (∀ᵣ θ, τ3 θ ⊸ τ4 θ)%T [] -∗
    sem_typed [] G G ⊥ (∀ᵣ θ, τ2 θ ⊸ τ3 θ)%T [] -∗
    sem_typed [] J J ⊥ (∀ᵣ θ, τ1 θ ⊸ τ2 θ)%T [] -∗
    sem_typed [] ((F ∘f G ) ∘f J) (F ∘f (G ∘f J)) ⊥ (∀ᵣ θ, τ1 θ ⊸ τ4 θ)%T [].
  Proof. 
    iIntros (HisclosedF HisclosedG HisclosedJ) "#HFF #HGG #HJJ !# %vs _". simpl.
    unfold func_comp, functionality_composition.
    brel_pures'.
    rewrite /sem_typed /=.
    iAssert ([] ⊨ₑ ∅) as "HΓ"; first done.
    iSpecialize ("HFF" with "HΓ").
    iSpecialize ("HJJ" with "HΓ").
    iSpecialize ("HGG" with "HΓ").
    rewrite !subst_map_is_closed_empty; try done.  
    brel_pures'. 
    iApply (brel_bind' [_ ] [_; _]); [iApply traversable_to_iThy_nil|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HJJ]"); [iApply to_iThy_le_refl|simpl].
    iIntros (vJ1 vJ2) "(HvJ & _)". 
    brel_pures'. 
    iApply (brel_bind' [_ ; _ ; _] [ _ ; _ ; _]); [iApply traversable_to_iThy_nil|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
     iApply (brel_mono OS with "[][$HGG]"); [iApply to_iThy_le_refl|simpl].
     iIntros (vG1 vG2) "(HvG & _)".
     brel_pures'.
     iApply (brel_bind' [_ ; _; _; _] [_ ; _ ]); [iApply traversable_to_iThy_nil|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HFF]"); [iApply to_iThy_le_refl|simpl].
    iIntros (vF1 vF2) "HvF".
    iDestruct "HvF" as "(HvF & _)".
    brel_pures'.
    iModIntro; iSplitL "HvJ HvG HvF"; last done.
    rewrite /sem_ty_arr /=.
    iIntros (θ v1 v2) "Hτ1".
    iSpecialize ("HvJ" with "Hτ1").
    brel_pures'. 
    iApply (brel_bind' [_ ] [_ ; _]);  [iApply traversable_to_iThy_nil|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HvJ]"); [iApply to_iThy_le_refl|simpl].
    iIntros (v v') "Hvv'".
    iSpecialize ("HvG" with "Hvv'").
    brel_pures'.
    iApply (brel_bind' [_ ] [_ ]);  [iApply traversable_to_iThy_nil|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HvG]"); [iApply to_iThy_le_refl|simpl].
    iIntros (v3 v4) "Hv3v4".
    iSpecialize ("HvF" with "Hv3v4").
    iApply "HvF".
  Qed. 
    
  Lemma functionality_comp_func_comp_assoc (F G : expr) (J : expr) (f x : string) τ1 τ2 τ1' τJ τF :
    (BNamed f) ≠ (BNamed x) →
     is_closed_expr ∅ F →
     is_closed_expr ∅ G →
    ⊢ sem_typed [] F F ⊥ (∀ᵣ θ, (∀ᵣ θF, τF θF -{ sem_row_union θF θ}-∘ 𝟙) ⊸ ∀ᵣ θ1, τ2 θ1 -{ sem_row_union θ1 θ }-∘ 𝟙)%T [] -∗

    sem_typed [] G G ⊥ (∀ᵣ θ, (∀ᵣ θJ, τJ θJ -{ sem_row_union θJ θ}-∘ 𝟙) ⊸ ∀ᵣ θ1, ∀ᵣ θ2, (τ1 θ1 × τF θ2) -{ sem_row_union θ2 (sem_row_union θ1 θ)}-∘ 𝟙)%T [] -∗
    (∀ θ θJ, sem_typed [(f, τ1' θ); (x, τJ θJ)] J J (sem_row_union θJ θ) (𝟙)%T []) -∗

      sem_typed [] (((F ∘F G)%V ∘f (λ: f x, J)%V)) (F ∘F (G ∘f (λ: f x, J)%V)) ⊥ 
      (∀ᵣ θ, (τ1' θ) ⊸ (∀ᵣ θ1, ∀ᵣ θ2, ((τ1 θ1) × (τ2 θ2)) -{ sem_row_union θ1 (sem_row_union θ2 θ) }-∘ 𝟙))%T [].
  Proof. 
   iIntros (Hfx HFclosed HGclosed) "#HFF #HGG #HJJ !# %vs _".
    rewrite /functionality_composition /func_comp //=. simpl.
    brel_pures'.
    rewrite /sem_typed /=. 
    iAssert ([] ⊨ₑ ∅) as "HΓ"; first done.
    iSpecialize ("HFF" with "HΓ").
    iSpecialize ("HGG" with "HΓ").
    rewrite !subst_map_is_closed_empty; try done.
    iApply (brel_bind [_ ; _ ; _] [_ ; _  ; _]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot |].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HGG]"); [iApply to_iThy_le_refl|simpl].
    iIntros (vG1 vG2) "(HG1G2 & _)".
    brel_pures'.
    iApply (brel_bind [_ ; _ ; _  ; _] [_ ; _]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot |].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HFF]"); [iApply to_iThy_le_refl|simpl].
    iIntros (vF1 vF2) "(HF1F2 & _)".
    brel_pures'.
    iModIntro; iSplit; last done.
    iIntros (θ f1 f2) "Hff".
    brel_pures'. 
    iModIntro.
    iIntros (θ1 θ2 v v') "Heffs".
    brel_pures'.
    rewrite /sem_ty_prod.
    iDestruct "Heffs" as ( w1 w1' w2 w2') "[%Hr1 [%Hr2 [Hτ1 Hτ2]]]". 
    rewrite -> Hr1.
    rewrite -> Hr2. 
    brel_pures'.
    rewrite decide_True; last (split; done). 
    iSpecialize ("HF1F2" $! (sem_row_union θ1 θ)).
    iApply (brel_bind [_] [_] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][HF1F2 Hff Hτ1 HG1G2]"); [iApply to_iThy_le_refl|iApply "HF1F2"|].
    - iIntros (θF rF1 rF2) "HτF". 
      brel_pures'.
      rewrite decide_True; last (split; done).
      iApply (brel_bind [_] [_] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
      assert (to_iThyIfMono OS [] = []) as <- by done. 
      iApply (brel_mono OS with "[][HG1G2 Hff]"); [iApply to_iThy_le_refl| iApply "HG1G2" |].
      + simpl. iIntros (θJ x1 x2) "HτJ". brel_pures'.
        iAssert ([(f, τ1' θ); (x, τJ θJ)] ⊨ₑ {[ x:= (x1,x2); f := (f1,f2) ]}) with "[Hff HτJ]" as "HΓ'".
        { solve_env. by intros ->. }
        iDestruct ("HJJ" with "HΓ'") as "Hrel".
        iApply (brel_wand with "[Hrel]"). 
        { rewrite !fmap_insert !fmap_empty //=. 
          rewrite !subst_map_insert !delete_insert_ne //=.
          2,3 : by intros ->.
          rewrite !delete_empty.
          rewrite !subst_map_insert !delete_empty subst_map_empty.
          iApply "Hrel". }
        iIntros (??) "!# ($&_)".  
      + simpl. iIntros (GJ1 GJ2) "HGJ". 
        iApply "HGJ".
        iExists w1, w1', rF1, rF2.
        iSplitR "Hτ1 HτF"; [ iPureIntro; reflexivity | iSplitR "Hτ1 HτF"; [iPureIntro; reflexivity| iFrame]].
    - simpl. iIntros (F1' F2') "HF'".
      iDestruct ("HF'" with "Hτ2") as "HF".
      rewrite !iLblSig_to_iLblThy_distr.
      iApply (brel_introduction_mono (iLblSig_to_iLblThy θ2 ++ iLblSig_to_iLblThy θ1 ++ iLblSig_to_iLblThy θ)); last done.
      iApply to_iThy_le_intro'; solve_submseteq.
  Qed.

  Lemma functionality_comp_func_comp_assoc_rev (F G J : expr) (f x : string) τ1 τ2 τ1' τJ τF :
    (BNamed f) ≠ (BNamed x) →
     is_closed_expr ∅ F →
     is_closed_expr ∅ G →
      ⊢ sem_typed [] F F ⊥ (∀ᵣ θ, (∀ᵣ θF, τF θF -{ sem_row_union θF θ}-∘ 𝟙) ⊸ ∀ᵣ θ1, τ2 θ1 -{ sem_row_union θ1 θ }-∘ 𝟙)%T [] -∗
    sem_typed [] G G ⊥ (∀ᵣ θ, (∀ᵣ θJ, τJ θJ -{ sem_row_union θJ θ}-∘ 𝟙) ⊸ ∀ᵣ θ1, ∀ᵣ θ2, (τ1 θ1 × τF θ2) -{ sem_row_union θ2 (sem_row_union θ1 θ)}-∘ 𝟙)%T [] -∗

    (∀ θ θJ, sem_typed [(f, τ1' θ); (x, τJ θJ)] J J (sem_row_union θJ θ) (𝟙)%T []) -∗

    sem_typed [] (F ∘F (G ∘f (λ: f x, J)%V)) ((F ∘F G)%V ∘f (λ: f x, J)%V) ⊥
      (∀ᵣ θ, (τ1' θ) ⊸ (∀ᵣ θ1, ∀ᵣ θ2, ((τ1 θ1) × (τ2 θ2)) -{ sem_row_union θ1 (sem_row_union θ2 θ) }-∘ 𝟙))%T []. 
  Proof. 
    iIntros (Hfx HFclosed HGclosed) "#HFF #HGG #HJJ  !# %vs _".
    rewrite /functionality_composition /func_comp //=. simpl.
    brel_pures'.
     iAssert ([] ⊨ₑ ∅) as "HΓ"; first done.
    iSpecialize ("HFF" with "HΓ").
    iSpecialize ("HGG" with "HΓ").
    rewrite !subst_map_is_closed_empty; try done.
    iApply (brel_bind [_ ; _ ; _] [_ ; _  ; _]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot |].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HGG]"); [iApply to_iThy_le_refl|simpl].
    iIntros (vG1 vG2) "(HG1G2 & _)".
    brel_pures'.
    iApply (brel_bind [_ ; _ ] [_ ; _ ; _ ; _ ]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot |].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HFF]"); [iApply to_iThy_le_refl|simpl].
    iIntros (vF1 vF2) "(HF1F2 & _)".
    brel_pures'.
    iModIntro; iSplit; last done.
    iIntros (θ f1 f2) "Hff".
    brel_pures'.
    iModIntro.
    iIntros (θ1 θ2 v v') "Heffs".
    brel_pures'.
    rewrite /sem_ty_prod.
    iDestruct "Heffs" as ( w1 w1' w2 w2') "[%Hr1 [%Hr2 [Hτ1 Hτ2]]]". 
    rewrite -> Hr1.
    rewrite -> Hr2.
    brel_pures'.
    rewrite decide_True; last (split; done).
    iSpecialize ("HF1F2" $! (sem_row_union θ1 θ)).
    iApply (brel_bind [_] [_] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][HF1F2 Hff Hτ1 HG1G2]"); [iApply to_iThy_le_refl|iApply "HF1F2"|].
    - iIntros (θF rF1 rF2) "HτF". 
      brel_pures'.
      rewrite decide_True; last (split; done).
      iApply (brel_bind [_] [_] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
      assert (to_iThyIfMono OS [] = []) as <- by done.
      iApply (brel_mono OS with "[][HG1G2 Hff]"); [iApply to_iThy_le_refl|iApply "HG1G2"|].
      + iIntros (θJ x1 x2) "HτJ". brel_pures'.
        iAssert ([(f, τ1' θ); (x, τJ θJ)] ⊨ₑ {[ x:= (x1,x2); f := (f1,f2) ]}) with "[Hff HτJ]" as "HΓ'".
        { solve_env. by intros ->. }
        iDestruct ("HJJ" with "HΓ'") as "Hrel".
        iApply (brel_wand with "[Hrel]"). 
        { rewrite !fmap_insert !fmap_empty //=. 
          rewrite !subst_map_insert !delete_insert_ne //=.
          2,3 : by intros ->.
          rewrite !delete_empty.
          rewrite !subst_map_insert !delete_empty subst_map_empty.
          iApply "Hrel". }
        iIntros (??) "!# ($&_)". 
      + simpl. iIntros (GJ1 GJ2) "HGJ".
        iApply "HGJ".
        iExists w1, w1', rF1, rF2.
        iSplitR "Hτ1 HτF"; [ iPureIntro; reflexivity | iSplitR "Hτ1 HτF"; [iPureIntro; reflexivity| iFrame]].
    - simpl. iIntros (F1' F2') "HF'".
      iDestruct ("HF'" with "Hτ2") as "HF".
      rewrite !iLblSig_to_iLblThy_distr.
      iApply (brel_introduction_mono (iLblSig_to_iLblThy θ2 ++ iLblSig_to_iLblThy θ1 ++ iLblSig_to_iLblThy θ)); last done.
      iApply to_iThy_le_intro'; solve_submseteq.
  Qed.

   Lemma functionality_comp_func_comp_assoc_curried (F G J : expr) (f x y : string) τ1 τ2 τ1' τJ τJ' τF :
    (BNamed f) ≠ (BNamed x) →
    (BNamed f) ≠ (BNamed y) →
    (BNamed x) ≠ (BNamed y) →
     is_closed_expr ∅ F →
     is_closed_expr ∅ G →
    ⊢ sem_typed [] F F ⊥ (∀ᵣ θ, (∀ᵣ θF, τF θF -{ sem_row_union (¡ θF)%R θ}-∘ 𝟙) ⊸ ∀ᵣ θ1, τ2 θ1 -{ sem_row_union (¡ θ1)%R θ }-∘ 𝟙)%T [] -∗

    sem_typed [] G G ⊥ (∀ᵣ θ, (∀ᵣ θJ, τJ θJ ⊸ τJ' θJ -{ sem_row_union  (¡ θJ)%R θ}-∘ 𝟙) ⊸ ∀ᵣ θ1, ∀ᵣ θ2, ((τ1 θ1) × (τF θ2)) -{ sem_row_union (¡ θ2)%R (sem_row_union (¡ θ1)%R θ)}-∘ 𝟙)%T [] -∗

    (∀ θ θJ, sem_typed [(f, τ1' θ); (x, τJ θJ); (y, τJ' θJ)] J J (sem_row_union  (¡ θJ)%R θ) (𝟙)%T []) -∗

    sem_typed [] ((F ∘F G) ∘f (λ: f x y, J)%V) (F ∘F (G ∘f (λ: f x y, J)%V)) ⊥
      (∀ᵣ θ, (τ1' θ) ⊸ (∀ᵣ θ1, ∀ᵣ θ2, ((τ1 θ1) × (τ2 θ2)) -{ sem_row_union (¡θ1) (sem_row_union (¡ θ2)%R θ) }-∘ 𝟙))%T [].
   Proof using All.
   iIntros (Hfx Hfy Hxy HFclosed HGclosed) "#HFF #HGG #HJJ !# %vs _".
    rewrite /functionality_composition /func_comp //=.
    brel_pures'.
    rewrite /sem_typed /=. 
    iAssert ([] ⊨ₑ ∅) as "HΓ"; first done.
    iSpecialize ("HFF" with "HΓ").
    iSpecialize ("HGG" with "HΓ").
    rewrite !subst_map_is_closed_empty; try done.
    iApply (brel_bind [_ ; _ ; _] [_ ; _  ; _]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot |].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HGG]"); [iApply to_iThy_le_refl|simpl].
    iIntros (vG1 vG2) "(HG1G2 & _)".
    brel_pures'.
    iApply (brel_bind [_ ; _ ; _  ; _] [_ ; _]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot |].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HFF]"); [iApply to_iThy_le_refl|simpl].
    iIntros (vF1 vF2) "(HF1F2 & _)".
    brel_pures'.
    iModIntro; iSplit; last done. 
    iIntros (θ f1 f2) "Hff".
    brel_pures'.
    iModIntro.
    iIntros (θ1 θ2 v v') "Heffs".
    brel_pures'.
    rewrite /sem_ty_prod.
    iDestruct "Heffs" as ( w1 w1' w2 w2') "[%Hr1 [%Hr2 [Hτ1 Hτ2]]]". 
    rewrite -> Hr1.
    rewrite -> Hr2.
    brel_pures'.
    rewrite decide_True; last (split; done).
    iSpecialize ("HF1F2" $! (sem_row_union  (¡ θ1)%R θ)).
    iApply (brel_bind [_] [_] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][HF1F2 Hff Hτ1 HG1G2]"); [iApply to_iThy_le_refl|iApply "HF1F2"|].
    - iIntros (θF rF1 rF2) "HτF".
      brel_pures'.
      rewrite decide_True; last (split; done). 
      iApply (brel_bind [_] [_] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
      assert (to_iThyIfMono OS [] = []) as <- by done.
      iApply (brel_mono OS with "[][HG1G2 Hff]"); [iApply to_iThy_le_refl|iApply "HG1G2"|].
      + iIntros (θJ x1 x2) "HτJ". brel_pures'.
        rewrite decide_True; [| (split; done)]; rewrite decide_True; [| (split; done)].
        simpl.
        repeat (rewrite decide_True; last (split; done)).
        brel_pures'.
        iModIntro.
        iIntros (y1 y2) "HτJ'". brel_pures'.
        assert (Hs1 : subst_map (fst <$> {[y:=(y1,y2); x:=(x1,x2); f:=(f1,f2)]}) J
                      = val_subst y y1 (val_subst x x1 (val_subst f f1 J))).
        { rewrite !fmap_insert fmap_empty /= subst_map_insert delete_insert_ne; [|naive_solver].
          rewrite delete_insert_ne; [|naive_solver]. rewrite delete_empty.
          rewrite subst_map_insert delete_insert_ne; [|naive_solver]. rewrite delete_empty.
          rewrite subst_map_insert delete_empty subst_map_empty //. }
        assert (Hs2 : subst_map (snd <$> {[y:=(y1,y2); x:=(x1,x2); f:=(f1,f2)]}) J
                      = val_subst y y2 (val_subst x x2 (val_subst f f2 J))).
        { rewrite !fmap_insert fmap_empty /= subst_map_insert delete_insert_ne; [|naive_solver].
          rewrite delete_insert_ne; [|naive_solver]. rewrite delete_empty.
          rewrite subst_map_insert delete_insert_ne; [|naive_solver]. rewrite delete_empty.
          rewrite subst_map_insert delete_empty subst_map_empty //. }
        iAssert ([(f, τ1' θ); (x, τJ θJ); (y, τJ' θJ)] ⊨ₑ {[ y:=(y1,y2); x:=(x1,x2); f:=(f1,f2) ]}) with "[Hff HτJ HτJ']" as "HΓ'".
        { rewrite !sem_env.env_sem_typed_cons sem_env.env_sem_typed_empty.
          iSplitL "Hff". { iExists f1, f2. iFrame "Hff". iPureIntro. rewrite lookup_insert_ne; [|naive_solver]. rewrite lookup_insert_ne; [|naive_solver]. by simplify_map_eq. }
          iSplitL "HτJ". { iExists x1, x2. iFrame "HτJ". iPureIntro. rewrite lookup_insert_ne; [|naive_solver]. by simplify_map_eq. }
          iSplitL "HτJ'". { iExists y1, y2. iFrame "HτJ'". iPureIntro. by simplify_map_eq. }
          done. } 
        iDestruct ("HJJ" $! θ θJ with "HΓ'") as "Hrel". 
        rewrite -Hs1 -Hs2.
        iApply (brel_wand with "[$Hrel]"). (*{ iApply "Hrel". }*)
        iIntros (v0 v3) "!# ($&_)".
      + simpl. iIntros (GJ1 GJ2) "HGJ".
        iApply "HGJ".
        iExists w1, w1', rF1, rF2.
        iSplitR "Hτ1 HτF"; [ iPureIntro; reflexivity | iSplitR "Hτ1 HτF"; [iPureIntro; reflexivity| iFrame]].
    - simpl. iIntros (F1' F2') "HF'".
      iDestruct ("HF'" with "Hτ2") as "HF".
      rewrite !iLblSig_to_iLblThy_distr.
      iApply (brel_introduction_mono (iLblSig_to_iLblThy  (¡θ2)%R ++ iLblSig_to_iLblThy  (¡θ1)%R ++ iLblSig_to_iLblThy θ)); last done.
      iApply to_iThy_le_intro'; solve_submseteq.
   Qed.
   
   Lemma functionality_comp_func_comp_assoc_curried_rev (F G J : expr) (f x y : string) τ1 τ2 τ1' τJ τJ' τF :
    (BNamed f) ≠ (BNamed x) →
    (BNamed f) ≠ (BNamed y) →
    (BNamed x) ≠ (BNamed y) →
     is_closed_expr ∅ F →
     is_closed_expr ∅ G →
    ⊢ sem_typed [] F F ⊥ (∀ᵣ θ, (∀ᵣ θF, τF θF -{ sem_row_union (¡ θF) θ}-∘ 𝟙) ⊸ ∀ᵣ θ1, τ2 θ1 -{ sem_row_union (¡ θ1) θ }-∘ 𝟙)%T [] -∗

    sem_typed [] G G ⊥ (∀ᵣ θ, (∀ᵣ θJ, τJ θJ ⊸ τJ' θJ -{ sem_row_union (¡ θJ) θ}-∘ 𝟙) ⊸ ∀ᵣ θ1, ∀ᵣ θ2, ((τ1 θ1) × (τF θ2)) -{ sem_row_union (¡ θ2) (sem_row_union (¡θ1) θ)}-∘ 𝟙)%T [] -∗

    (∀ θ θJ, sem_typed [(f, τ1' θ); (x, τJ θJ); (y, τJ' θJ)] J J (sem_row_union (¡ θJ)%R θ) (𝟙)%T []) -∗

    sem_typed [] (F ∘F (G ∘f (λ: f x y, J)%V)) ((F ∘F G) ∘f (λ: f x y, J)%V)  ⊥
      (∀ᵣ θ, (τ1' θ) ⊸ (∀ᵣ θ1, ∀ᵣ θ2, ((τ1 θ1) × (τ2 θ2)) -{ sem_row_union (¡θ1) (sem_row_union (¡ θ2)%R θ) }-∘ 𝟙))%T [].
   Proof using All.
    iIntros (Hfx Hfy Hxy HFclosed HGclosed) "#HFF #HGG #HJJ !# %vs _".
    rewrite /functionality_composition /func_comp //=.
    brel_pures'.
    iAssert ([] ⊨ₑ ∅) as "HΓ"; first done.
    iSpecialize ("HFF" with "HΓ").
    iSpecialize ("HGG" with "HΓ").
    rewrite !subst_map_is_closed_empty; try done.
    iApply (brel_bind [_ ; _ ; _] [_ ; _  ; _]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot |].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HGG]"); [iApply to_iThy_le_refl|simpl].
    iIntros (vG1 vG2) "(HG1G2 & _)".
    brel_pures'.
    iApply (brel_bind [_ ; _ ] [_ ; _ ; _ ; _ ]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot |].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HFF]"); [iApply to_iThy_le_refl|simpl].
    iIntros (vF1 vF2) "(HF1F2 & _)".
    brel_pures'.
    iModIntro; iSplit; last done.
    iIntros (θ f1 f2) "Hff".
    brel_pures'.
    iModIntro.
    iIntros (θ1 θ2 v v') "Heffs".
    brel_pures'.
    rewrite /sem_ty_prod.
    iDestruct "Heffs" as ( w1 w1' w2 w2') "[%Hr1 [%Hr2 [Hτ1 Hτ2]]]". 
    rewrite -> Hr1.
    rewrite -> Hr2.
    brel_pures'.
    rewrite decide_True; last (split; done).
    iSpecialize ("HF1F2" $! (sem_row_union (¡θ1)%R θ)).
    iApply (brel_bind [_] [_] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][HF1F2 Hff Hτ1 HG1G2]"); [iApply to_iThy_le_refl|iApply "HF1F2"|].
    - iIntros (θF rF1 rF2) "HτF".
      brel_pures'.
      rewrite decide_True; last (split; done).
      iApply (brel_bind [_] [_] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
      assert (to_iThyIfMono OS [] = []) as <- by done.
      iApply (brel_mono OS with "[][HG1G2 Hff]"); [iApply to_iThy_le_refl|iApply "HG1G2"|].
      + iIntros (θJ x1 x2) "HτJ". brel_pures'.
        rewrite decide_True; [| (split; done)]; rewrite decide_True; [| (split; done)].
        simpl.
        repeat (rewrite decide_True; last (split; done)).
        brel_pures'.
        iModIntro.
        iIntros (y1 y2) "HτJ'". brel_pures'.
        assert (Hs1 : subst_map (fst <$> {[y:=(y1,y2); x:=(x1,x2); f:=(f1,f2)]}) J
                      = val_subst y y1 (val_subst x x1 (val_subst f f1 J))).
        { rewrite !fmap_insert fmap_empty /= subst_map_insert delete_insert_ne; [|naive_solver].
          rewrite delete_insert_ne; [|naive_solver]. rewrite delete_empty.
          rewrite subst_map_insert delete_insert_ne; [|naive_solver]. rewrite delete_empty.
          rewrite subst_map_insert delete_empty subst_map_empty //. }
        assert (Hs2 : subst_map (snd <$> {[y:=(y1,y2); x:=(x1,x2); f:=(f1,f2)]}) J
                      = val_subst y y2 (val_subst x x2 (val_subst f f2 J))).
        { rewrite !fmap_insert fmap_empty /= subst_map_insert delete_insert_ne; [|naive_solver].
          rewrite delete_insert_ne; [|naive_solver]. rewrite delete_empty.
          rewrite subst_map_insert delete_insert_ne; [|naive_solver]. rewrite delete_empty.
          rewrite subst_map_insert delete_empty subst_map_empty //. }
        iAssert ([(f, τ1' θ); (x, τJ θJ); (y, τJ' θJ)] ⊨ₑ {[ y:=(y1,y2); x:=(x1,x2); f:=(f1,f2) ]}) with "[Hff HτJ HτJ']" as "HΓ'".
        { rewrite !sem_env.env_sem_typed_cons sem_env.env_sem_typed_empty.
          iSplitL "Hff". { iExists f1, f2. iFrame "Hff". iPureIntro. rewrite lookup_insert_ne; [|naive_solver]. rewrite lookup_insert_ne; [|naive_solver]. by simplify_map_eq. }
          iSplitL "HτJ". { iExists x1, x2. iFrame "HτJ". iPureIntro. rewrite lookup_insert_ne; [|naive_solver]. by simplify_map_eq. }
          iSplitL "HτJ'". { iExists y1, y2. iFrame "HτJ'". iPureIntro. by simplify_map_eq. }
          done. }
        iDestruct ("HJJ" $! θ θJ with "HΓ'") as "Hrel".
        rewrite -Hs1 -Hs2.
        iApply (brel_wand with "[Hrel]"). { iApply "Hrel". }
        iIntros (v0 v3) "!# ($&_)".
      + simpl. iIntros (GJ1 GJ2) "HGJ".
        iApply "HGJ".
        iExists w1, w1', rF1, rF2.
        iSplitR "Hτ1 HτF"; [ iPureIntro; reflexivity | iSplitR "Hτ1 HτF"; [iPureIntro; reflexivity| iFrame]].
    - simpl. iIntros (F1' F2') "HF'".
      iDestruct ("HF'" with "Hτ2") as "HF".
      rewrite !iLblSig_to_iLblThy_distr.
      iApply (brel_introduction_mono (iLblSig_to_iLblThy  (¡θ2)%R ++ iLblSig_to_iLblThy (¡ θ1)%R ++ iLblSig_to_iLblThy θ)); last done.
      iApply to_iThy_le_intro'; solve_submseteq.
  Qed.
    
  Lemma functionality_comp_cong (F G1 G2 : expr) τ1 τ2 τ1' τF :
    is_closed_expr ∅ F →
    is_closed_expr ∅ G1 →
    is_closed_expr ∅ G2 →
    ⊢ sem_typed [] G1 G2 ⊥ (∀ᵣ θ, τ1' θ ⊸ ∀ᵣ θ1, ∀ᵣ θ2, ((τ1 θ1) × (τF θ2)) -{ sem_row_union (¡ θ2)%R (sem_row_union (¡ θ1) θ)}-∘ 𝟙)%T [] -∗
    sem_typed [] F F ⊥ (∀ᵣ θ, (∀ᵣ θF, τF θF -{ sem_row_union (¡ θF) θ}-∘ 𝟙) ⊸ ∀ᵣ θ1, τ2 θ1 -{ sem_row_union (¡ θ1) θ }-∘ 𝟙)%T [] -∗
    sem_typed [] (F ∘F G1) (F ∘F G2) ⊥ 
      (∀ᵣ θ, τ1' θ ⊸ (∀ᵣ θ1, ∀ᵣ θ2, (τ1 θ1 × τ2 θ2) -{ sem_row_union (¡θ1) (sem_row_union (¡ θ2) θ) }-∘ 𝟙))%T []. 
  Proof.
    iIntros (HFclosed HG1closed HG2closed)  "#HGG #HFF !# %vs _".
    rewrite /functionality_composition /=.
    brel_pures'.
    iAssert ([] ⊨ₑ ∅) as "HΓ"; first done.
    iSpecialize ("HFF" with "HΓ").
    iSpecialize ("HGG" with "HΓ").
    rewrite !subst_map_is_closed_empty; try done.
    iApply (brel_bind [_ ] [_ ]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot |].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HGG]"); [iApply to_iThy_le_refl|simpl].
    iIntros (vG1 vG2) "(HG1G2 & _)".
    brel_pures'.
    iApply (brel_bind [_ ; _ ] [_ ; _]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot |].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HFF]"); [iApply to_iThy_le_refl|simpl].
    iIntros (vF1 vF2) "(HF1F2 & _)".
    brel_pures'.
    iModIntro; iSplit; last done.
    iIntros (θ f1 f2) "Hff".
    brel_pures'.
    iModIntro.
    iIntros (θ1 θ2 v v') "Heffs".
    brel_pures'.
    rewrite /sem_ty_prod.
    iDestruct "Heffs" as ( w1 w1' w2 w2') "[%Hr1 [%Hr2 [Hτ1 Hτ2]]]". 
    rewrite -> Hr1.
    rewrite -> Hr2.
    brel_pures'.
    iAssert ([] ⊨ₑ ∅) as "#Hempty"; first done.
    iAssert ((∀ᵣ θF, τF θF -{ sem_row_union (¡θF) (sem_row_union  (¡θ1) θ) }-∘ 𝟙)%T (λ: "rG", vG1 f1 (w1, "rG"))%V (λ: "rG", vG2 f2 (w1',"rG"))%V) with "[Hff Hτ1 HG1G2]" as "Hff'".
    { iIntros (θF rG1 rG2) "HτF".
      brel_pures'.
      unfold sem_typed. simpl. 
      iSpecialize ("HG1G2" with "Hff").
      iApply (brel_bind [_] [_]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
      assert (to_iThyIfMono OS [] = []) as <- by done.
      iApply (brel_mono OS with "[][$HG1G2]"); [iApply to_iThy_le_refl|simpl].
      iIntros (GfrGv1 GfrGv2) "HGfrGv".
      iApply "HGfrGv".
      iExists w1, w1', rG1, rG2.
      iSplitR "Hτ1 HτF"; [ iPureIntro; reflexivity | iSplitR "Hτ1 HτF"; [iPureIntro; reflexivity| iFrame]]. }
    iSpecialize ("HF1F2" with "Hff'").
    iApply (brel_bind [_] [_]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HF1F2]"); [iApply to_iThy_le_refl|simpl].
    iIntros (HFfv1 HFfv2) "HFfv".
    iSpecialize ("HFfv" with "Hτ2").
    rewrite !iLblSig_to_iLblThy_distr.
    iApply (brel_introduction_mono ((iLblSig_to_iLblThy (¡θ2)%R ++ iLblSig_to_iLblThy (¡θ1)%R ++ iLblSig_to_iLblThy θ))).
    { iApply to_iThy_le_intro'; solve_submseteq. }
    iApply "HFfv".
  Qed. 

  Lemma sem_typed_eta_expansion_l (Γ1 Γ2 : env Σ) e1 e2 v1 v2 s τ κ ρ : 
    s ∉ env_dom Γ1 → s ∉ env_dom Γ2 →
    sem_typed ((s, τ) ::? Γ1) e1 e2 ρ κ Γ2 -∗
    ⊨ᵥ v1 ≤ v2 : τ -∗
    sem_typed Γ1 (val_subst' s v1 e1) ((λ: s, e2)%E v2) ρ κ Γ2.  
  Proof. Admitted.
   (* iIntros (HΓ1 HΓ2) "#Hee #Hvv !# %vs Hvs".
    brel_pures'.
    rewrite -subst_map_binder_insert.
    rewrite /sem_typed /=.
    iDestruct "Hee" as "#Hee".
    destruct s; first by iApply "Hee".
    simpl.
    assert (subst_map (fst <$> vs) (val_subst s v1 e1) = subst_map (fst <$> (binder_insert s (v1, v2)(delete s vs))) e1) as ->.
    { 
      rewrite subst_map_val_subst. simpl.
      assert (v1 = fst (v1, v2)) as -> by done.  
      by rewrite -fmap_insert insert_delete_eq. }
    assert (subst_map (<[s:=v2]> (snd <$> vs)) e2 = subst_map (snd <$> (binder_insert s (v1, v2) (delete s vs))) e2) as ->.
    { by rewrite fmap_insert fmap_delete insert_delete_eq /=. }
    iSpecialize ("Hee" $! (binder_insert s (v1, v2)(delete s vs))).
    iApply (brel_wand with "[Hvs]").
    - iApply "Hee". 
      rewrite env_sem_typed_cons.
      iSplitR.
      + iExists v1, v2.
        rewrite /sem_val_typed /=.
        iSplit; last done.
        iPureIntro. apply lookup_insert_eq.
      + rewrite -env_sem_typed_insert; last done.
        by rewrite -env_sem_typed_delete.
    - iIntros (??) "!# ($&HΓ)".
      iClear "Hee".
      rewrite -env_sem_typed_insert; last done.
      by rewrite -env_sem_typed_delete.
  Qed. 
 *)
  Lemma sem_typed_eta_expansion_r (Γ1 Γ2 : env Σ) e1 e2 v1 v2 s τ κ ρ : 
    s ∉ env_dom Γ1 → s ∉ env_dom Γ2 →
    sem_typed ((s, τ) ::? Γ1) e1 e2 ρ κ Γ2 -∗
    ⊨ᵥ v1 ≤ v2 : τ -∗
                 sem_typed Γ1 ((λ: s, e1)%E v1) (val_subst' s v2 e2) ρ κ Γ2.  
  Proof. Admitted.
   (* iIntros (HΓ1 HΓ2) "#Hee #Hvv !# %vs Hvs".
    brel_pures'.
    rewrite -subst_map_binder_insert.
    rewrite /sem_typed /=.
    iDestruct "Hee" as "#Hee".
    destruct s; first by iApply "Hee".
    simpl.
    assert (subst_map (snd <$> vs) (val_subst s v2 e2) = subst_map (snd <$> (binder_insert s (v1, v2)(delete s vs))) e2) as ->.
    { rewrite subst_map_val_subst. simpl.
      assert (v2 = snd (v1, v2)) as -> by done.  
      by rewrite -fmap_insert insert_delete_eq. }
    assert (subst_map (<[s:=v1]> (fst <$> vs)) e1 = subst_map (fst <$> (binder_insert s (v1, v2) (delete s vs))) e1) as ->.
    { by rewrite fmap_insert fmap_delete insert_delete_eq /=. }
    iSpecialize ("Hee" $! (binder_insert s (v1, v2)(delete s vs))).
    iApply (brel_wand with "[Hvs]").
    - iApply "Hee". 
      rewrite env_sem_typed_cons.
      iSplitR.
      + iExists v1, v2.
        rewrite /sem_val_typed /=.
        iSplit; last done.
        iPureIntro. apply lookup_insert_eq.
      + rewrite -env_sem_typed_insert; last done.
        by rewrite -env_sem_typed_delete.
    - iIntros (??) "!# ($&HΓ)".
      iClear "Hee".
      rewrite -env_sem_typed_insert; last done.
      by rewrite -env_sem_typed_delete.
  Qed. *)
  

End parallel_composition.

Notation "F₁ ||ᵣ F₂" := (right_composition F₁ F₂) (at level 10).

Notation "F '∘F' G" := (functionality_composition F G) (at level 10). 

Notation "F ∘f G" := (func_comp F G) (at level 10).

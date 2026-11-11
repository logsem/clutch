From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import agree excl auth frac excl_auth.
From iris.algebra.lib Require Import dfrac_agree.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode
 spec_rules spec_ra class_instances.
From clutch.prob_eff_lang.probblaze Require Import tactics.
From clutch.prob_eff_lang.probblaze Require Import sem_types sem_row sem_sig sem_judgement sem_def valgroup sem_env.

Import valgroup_tactics.
Section composition_operators.
  Context `{probblazeRGS Σ}.
 
  (* r_x are effect operations raised by the functionality f_x, and c_x are effect operations
     handled by f_x.*) 
 
  Definition parallel_composition : val :=
    λ: "F" "G" "f" "r",
      let, ("r₁", "r₂") := "r" in
     "F" (λ: "h₁",
             "G" (λ: "h₂", "f" ("h₂","h₁")) "r₁") "r₂".  

  Definition functionality_composition : val :=
    λ: "F" "G" "f" "r",
      let, ("rH", "rF") := "r" in
      ("F" (λ: "rG", "G" "f" ("rH", "rG")) "rF").

  Notation "F ||ᵣₛ G" := (parallel_composition F G)%V (at level 10).
  
  Notation "F ∘Fₛ G" := (functionality_composition F G)%V (at level 10).

 
  Definition func_comp : val :=
   λ: "F" "G" "f", "F" (λ: "r", "G" "f" "r").

  Notation "F ∘fₛ G" := (func_comp F G)%V (at level 10).
    
  Definition τ__f θ τ1' τ2' := (∀ᵣ θ1, ∀ᵣ θ2, ((τ1' θ1) × (τ2' θ2)) -{ sem_row_union (¡θ1)%R (sem_row_union (¡θ2)%R θ) }-∘ 𝟙)%T.
  (* The session type: the session may be given a client any number of
     times, and all those calls share its state. *)
  Definition τ__F τ τ' := (∀ᵣ θ, (∀ᵣ θ₁, τ' θ₁ -{ sem_row_union (¡θ₁) θ}-∘ 𝟙) → (∀ᵣ θ₂, τ θ₂ -{ sem_row_union (¡θ₂) θ }-∘ 𝟙))%T.
 
  Lemma iLblSig_to_iLblThy_distr L1 L2 :
    @iLblSig_to_iLblThy Σ (L1 ++ L2) = iLblSig_to_iLblThy L1 ++ (iLblSig_to_iLblThy L2).
  Proof.
    induction L1; first done.
    simpl. by rewrite IHL1.
  Qed.  
  (* we are forced to use arrow types in comp_left_gen, cannot prove a lemma of the simpler form when func_comp was defined differently (without delayed evaluation), otherwise eta-expansion in certain places in the proof wont type check. The type τ__f in comp_left doesnt violate this, since it is itself in the shape of an arrow type. The difference between τ__f and the arrow types in comp_left_gen is that τ__f is an arrow type for an effectful computation *)
  
  Definition τ__f' θ τ2' := (∀ᵣ θ2, τ2' θ2 -{ (sem_row_union (¡θ2)%R θ) }-∘ 𝟙)%T.
 
  (* ---------------------------------------------------------------- *)
  (* Associativity of the session operators, for related pairs of      *)
  (* expressions (no closedness premises).  Every session takes its    *)
  (* client with [→]: the component relations are persistent, so the  *)
  (* composite is related under [□].                                   *)
  (* ---------------------------------------------------------------- *)

  Lemma func_comp_parallel_comp_assoc_core (F1 F2 G1 G2 J1 J2 : expr) τ1 τ2 τG τ1' τ2' (vs : gmap string (val * val)) :
    ⊢
    brel ⊤ F1 F2 (iLblSig_to_iLblThy ⊥) (λ v1 v2, (τ__F τ2 τG)%T v1 v2 ∗ [] ⊨ₑ vs) -∗
    brel ⊤ G1 G2 (iLblSig_to_iLblThy ⊥) (λ v1 v2, (τ__F τG τ1')%T v1 v2 ∗ [] ⊨ₑ vs) -∗
    brel ⊤ J1 J2 (iLblSig_to_iLblThy ⊥) (λ v1 v2, (τ__F τ1 τ2')%T v1 v2 ∗ [] ⊨ₑ vs) -∗
    brel ⊤ ((F1 ∘fₛ G1) ||ᵣₛ J1) (F2 ∘Fₛ (G2 ||ᵣₛ J2)) (iLblSig_to_iLblThy ⊥) (λ v1 v2, (∀ᵣ θ, (τ__f θ τ2' τ1') → (τ__f θ τ1 τ2))%T v1 v2 ∗ [] ⊨ₑ vs).
  Proof.
  iIntros "HFF HGG HJJ". simpl. 
    unfold func_comp, parallel_composition,functionality_composition. 
    brel_pures'.
    simpl. 
    iApply (brel_bind [AppRCtx _ ] [AppRCtx _ ; _ ]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot |].
    assert (to_iThyIfMono OS [] = []) as <- by done. 
    iApply (brel_mono OS with "[][$HJJ]");[iApply to_iThy_le_refl |simpl ].
    iIntros (vJ1 vJ2) "(#HJ1J2 & _)".
    iApply (brel_bind [_ ; _ ; _] [_ ; _ ; _]); [iApply traversable_to_iThy_nil | iApply to_iThy_le_bot |].        
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HGG]");[iApply to_iThy_le_refl |simpl].
    iIntros (vG1 vG2) "(#HG1G2 & _)".
    brel_pures'.
    iApply (brel_bind [_ ; _ ; _ ; _] [_ ; _  ]); [iApply traversable_to_iThy_nil | iApply to_iThy_le_bot |].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HFF]");[iApply to_iThy_le_refl |simpl].
    iIntros (vF1 vF2) "(#HF1F2 & _)".
    brel_pures'.
    iModIntro; iSplitR; last done.
    rewrite /τ__F /sem_ty_mbang /=. iIntros "%θ !# %f1 %f2 Hff".
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
    iAssert ((∀ᵣ θG, τG θG -{ sem_row_union (¡ θG)%R (sem_row_union (¡ θ1)%R θ) }-∘ 𝟙)%T
                (λ: "r", vG1 (λ: "h₁", vJ1 (λ: "h₂", f1 ("h₂","h₁")) w1)%V "r")%V                 
               (λ: "rG", (λ: "f" "r",
                            let: "r₂" := "r" in
                            let: "r₁" := Fst "r₂" in
                            let: "r₂" := Snd "r₂" in
                            vG2 (λ: "h₁", vJ2 (λ: "h₂", "f" ("h₂","h₁")) "r₁") "r₂")%V f2 (w1',"rG"))%V) with "[Hτ1 Hff HJ1J2 HG1G2]" as "Hgg".
    { iIntros (θG rg1 rg2) "HτG".
      brel_pures'.
      iSpecialize ("HG1G2" $! (sem_row_union (¡ θ1)%R θ)). (* θG). *)
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
        iApply (brel_introduction_mono (iLblSig_to_iLblThy (¡ θ1)%R ++ iLblSig_to_iLblThy (¡θ1')%R ++ iLblSig_to_iLblThy θ)); [|done].
        iApply to_iThy_le_intro'; solve_submseteq. }
      iApply (brel_wand with "[HG1G2 Hff HτG]"). 
      { iSpecialize ("HG1G2" with "Hff").
        iApply (brel_bind [_] [_]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot |].
        assert (to_iThyIfMono OS [] = []) as <- by done.
        iApply (brel_mono OS with "[][HG1G2][HτG]"); [iApply to_iThy_le_refl|simpl|].
        +  iApply "HG1G2".
        + simpl.
          iIntros (v1 v2) "Hv1v2".
          iSpecialize ("Hv1v2" with "HτG").
          iApply "Hv1v2". }
      iModIntro.
      iIntros (v1 v2) "Hv1v2". iApply "Hv1v2". }
    unfold τ__F.
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

  Lemma func_comp_parallel_comp_assoc_rev_core (F1 F2 G1 G2 J1 J2 : expr) τ1 τ2 τG τ1' τ2' (vs : gmap string (val * val)) :
    ⊢
    brel ⊤ F1 F2 (iLblSig_to_iLblThy ⊥) (λ v1 v2, (τ__F τ2 τG)%T v1 v2 ∗ [] ⊨ₑ vs) -∗
    brel ⊤ G1 G2 (iLblSig_to_iLblThy ⊥) (λ v1 v2, (τ__F τG τ1')%T v1 v2 ∗ [] ⊨ₑ vs) -∗
    brel ⊤ J1 J2 (iLblSig_to_iLblThy ⊥) (λ v1 v2, (τ__F τ1 τ2')%T v1 v2 ∗ [] ⊨ₑ vs) -∗
    brel ⊤ (F1 ∘Fₛ (G1 ||ᵣₛ J1)) ((F2 ∘fₛ G2) ||ᵣₛ J2) (iLblSig_to_iLblThy ⊥) (λ v1 v2, (∀ᵣ θ,(τ__f θ τ2' τ1') → (τ__f θ τ1 τ2))%T v1 v2 ∗ [] ⊨ₑ vs).
  Proof.
    iIntros "HFF HGG HJJ". simpl. 
    unfold func_comp, parallel_composition,functionality_composition. 
    brel_pures'.
    simpl. 
    iApply (brel_bind [AppRCtx _ ; _] [AppRCtx _ ]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot |].
    assert (to_iThyIfMono OS [] = []) as <- by done. 
    iApply (brel_mono OS with "[][$HJJ]");[iApply to_iThy_le_refl |simpl ].
    iIntros (vJ1 vJ2) "(#HJ1J2 & _)".
    iApply (brel_bind [_ ; _ ; _] [_ ; _ ; _]); [iApply traversable_to_iThy_nil | iApply to_iThy_le_bot |].        
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HGG]");[iApply to_iThy_le_refl |simpl].
    iIntros (vG1 vG2) "(#HG1G2 & _)".
    brel_pures'.
    iApply (brel_bind [_ ; _ ] [_ ; _  ; _ ; _]); [iApply traversable_to_iThy_nil | iApply to_iThy_le_bot |].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HFF]");[iApply to_iThy_le_refl |simpl].
    iIntros (vF1 vF2) "(#HF1F2 & _)".
    brel_pures'.
    iModIntro; iSplitR; last done.
    rewrite /τ__F /sem_ty_mbang /=. iIntros "%θ !# %f1 %f2 Hff".
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
    iAssert ((∀ᵣ θG, τG θG -{ sem_row_union (¡ θG)%R (sem_row_union (¡ θ1)%R θ) }-∘ 𝟙)%T 
               (λ: "rG", (λ: "f" "r",
                            let: "r₂" := "r" in
                            let: "r₁" := Fst "r₂" in
                            let: "r₂" := Snd "r₂" in
                            vG1 (λ: "h₁", vJ1 (λ: "h₂", "f" ("h₂","h₁")) "r₁") "r₂")%V f1 (w1,"rG"))%V


               (λ: "r", vG2 (λ: "h₁", vJ2 (λ: "h₂", f2 ("h₂","h₁")) w1')%V "r")%V) with "[Hτ1 Hff HJ1J2 HG1G2]" as "Hgg".
    { iIntros (θG rg1 rg2) "HτG".
      brel_pures'.
      iSpecialize ("HG1G2" $! (sem_row_union (¡ θ1)%R θ)). (*θG).*) 
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
        iApply (brel_introduction_mono (iLblSig_to_iLblThy (¡ θ1)%R ++ iLblSig_to_iLblThy (¡θ1')%R ++ iLblSig_to_iLblThy θ)); [|done].
        iApply to_iThy_le_intro'; solve_submseteq. }
      iApply (brel_wand with "[HG1G2 Hff HτG]"). 
      { iSpecialize ("HG1G2" with "Hff").
        iApply (brel_bind [_] [_]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot |].
        assert (to_iThyIfMono OS [] = []) as <- by done.
        iApply (brel_mono OS with "[][HG1G2][HτG]"); [iApply to_iThy_le_refl|simpl|].
        +  iApply "HG1G2".
        + simpl.
          iIntros (v1 v2) "Hv1v2".
          iSpecialize ("Hv1v2" with "HτG").
          iApply "Hv1v2". }
      iModIntro.
      iIntros (v1 v2) "Hv1v2". iApply "Hv1v2". }
    unfold τ__F.
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

  Lemma func_comp_assoc_core (F1 F2 G1 G2 J1 J2 : expr) τ1 τ2 τ3 τ4 (vs : gmap string (val * val)) :
    ⊢
    brel ⊤ F1 F2 (iLblSig_to_iLblThy ⊥) (λ v1 v2, (τ__F τ1 τ2)%T v1 v2 ∗ [] ⊨ₑ vs) -∗
    brel ⊤ G1 G2 (iLblSig_to_iLblThy ⊥) (λ v1 v2, (τ__F τ2 τ3)%T v1 v2 ∗ [] ⊨ₑ vs) -∗
    brel ⊤ J1 J2 (iLblSig_to_iLblThy ⊥) (λ v1 v2, (τ__F τ3 τ4)%T v1 v2 ∗ [] ⊨ₑ vs) -∗
    brel ⊤ (F1 ∘fₛ (G1 ∘fₛ J1)) ((F2 ∘fₛ G2) ∘fₛ J2) (iLblSig_to_iLblThy ⊥) (λ v1 v2, (τ__F τ1 τ4)%T v1 v2 ∗ [] ⊨ₑ vs).
  Proof.
     iIntros "HFF HGG HJJ". simpl.
    unfold func_comp, functionality_composition.
    brel_pures'.
    simpl.  
    brel_pures'. 
    iApply (brel_bind' [_ ; _] [_ ]); [iApply traversable_to_iThy_nil|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HJJ]"); [iApply to_iThy_le_refl|simpl].
    iIntros (vJ1 vJ2) "(#HvJ & _)". 
    brel_pures'. 
    iApply (brel_bind' [_ ; _ ; _] [ _ ; _ ; _]); [iApply traversable_to_iThy_nil|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
     iApply (brel_mono OS with "[][$HGG]"); [iApply to_iThy_le_refl|simpl].
     iIntros (vG1 vG2) "(#HvG & _)".
     brel_pures'.
     iApply (brel_bind' [_ ; _] [_ ; _ ; _ ; _]); [iApply traversable_to_iThy_nil|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HFF]"); [iApply to_iThy_le_refl|simpl].
    iIntros (vF1 vF2) "HvF".
    iDestruct "HvF" as "(#HvF & _)".
    brel_pures'.
    iModIntro; iSplitR; last done.
    rewrite /τ__F /sem_ty_mbang /=. iIntros "%θ !# %v1 %v2 Hτ1τ2". 
    brel_pures'.
    unfold τ__F.
    iSpecialize ("HvJ" $! θ).
    iSpecialize ("HvG" $! θ).
    iSpecialize ("HvF" $! θ).
    iAssert ((∀ᵣ θ₁, τ2 θ₁ -{ sem_row_union (¡ θ₁) θ }-∘ 𝟙)%T (λ: "r", (λ: "f", vG1 (λ: "r", vJ1 "f" "r"))%V v1 "r")%V (λ: "r", vG2 (λ: "r", vJ2 v2 "r")%V "r")%V) with "[Hτ1τ2 HvJ HvG]" as "HclientsF".
    { 
      iSpecialize ("HvJ" with "Hτ1τ2").  
      iEval (rewrite /sem_ty_arr /=).
      iIntros (θ1).
      iIntros (w1 w2) "Hw1w2".
      brel_pures'.
      iAssert ((∀ᵣ θ₁,τ3 θ₁ -{ sem_row_union (¡ θ₁) θ }-∘ 𝟙)%T (λ: "r", vJ1 v1 "r")%V (λ: "r", vJ2 v2 "r")%V) with "[HvJ]" as "HclientsG".
      { rewrite /sem_ty_arr /=.
        iIntros (θ₁).
        iIntros (w0 w3) "Hw0w3".
        brel_pures'.
        rewrite !iLblSig_to_iLblThy_distr.
        iApply (brel_bind'' [_] [_] [] [] with "[][Hw0w3 HvJ]"); try done.
        + simpl. iApply to_iThy_le_intro'. solve_submseteq.
        + assert (to_iThyIfMono OS [] = []) as <- by done.
        iApply (brel_mono OS _ _ [] [] with "[][$HvJ]");
          [iApply to_iThy_le_bot|].
        simpl.
        iIntros (v0 v3) "Hv0v3".
        iSpecialize ("Hv0v3" with "Hw0w3").
      rewrite !iLblSig_to_iLblThy_distr.
      iApply "Hv0v3". }
      iSpecialize ("HvG" with "HclientsG").
      rewrite !iLblSig_to_iLblThy_distr. 
      iApply (brel_bind'' [_] [_] [] [] with "[][HvG Hw1w2]"); try done.
      + simpl. iApply to_iThy_le_intro'. solve_submseteq.
      + assert (to_iThyIfMono OS [] = []) as <- by done.
        iApply (brel_mono OS _ _ [] [] with "[][$HvG]");
          [iApply to_iThy_le_bot|].
        simpl.
      iIntros (v0 v3) "Hv0v3".
      iSpecialize ("Hv0v3" with "Hw1w2").
      rewrite !iLblSig_to_iLblThy_distr. 
      iApply "Hv0v3".
    } 
    iSpecialize ("HvF" with "HclientsF").
    iApply "HvF".
  Qed.

   Lemma func_comp_assoc_rev_core (F1 F2 G1 G2 J1 J2 : expr) τ1 τ2 τ3 τ4 (vs : gmap string (val * val)) :
     ⊢
     brel ⊤ F1 F2 (iLblSig_to_iLblThy ⊥) (λ v1 v2, (τ__F τ1 τ2)%T v1 v2 ∗ [] ⊨ₑ vs) -∗
     brel ⊤ G1 G2 (iLblSig_to_iLblThy ⊥) (λ v1 v2, (τ__F τ2 τ3)%T v1 v2 ∗ [] ⊨ₑ vs) -∗
     brel ⊤ J1 J2 (iLblSig_to_iLblThy ⊥) (λ v1 v2, (τ__F τ3 τ4)%T v1 v2 ∗ [] ⊨ₑ vs) -∗
     brel ⊤ ((F1 ∘fₛ G1) ∘fₛ J1) (F2 ∘fₛ (G2 ∘fₛ J2)) (iLblSig_to_iLblThy ⊥) (λ v1 v2, (τ__F τ1 τ4)%T v1 v2 ∗ [] ⊨ₑ vs).
   Proof.
     iIntros "HFF HGG HJJ". simpl.
    unfold func_comp, functionality_composition.
    brel_pures'.
    simpl.  
    brel_pures'. 
    iApply (brel_bind' [_ ] [_ ; _]); [iApply traversable_to_iThy_nil|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HJJ]"); [iApply to_iThy_le_refl|simpl].
    iIntros (vJ1 vJ2) "(#HvJ & _)". 
    brel_pures'. 
    iApply (brel_bind' [_ ; _ ; _] [ _ ; _ ; _]); [iApply traversable_to_iThy_nil|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
     iApply (brel_mono OS with "[][$HGG]"); [iApply to_iThy_le_refl|simpl].
     iIntros (vG1 vG2) "(#HvG & _)".
     brel_pures'.
     iApply (brel_bind' [_ ; _ ; _ ; _] [_ ; _ ]); [iApply traversable_to_iThy_nil|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HFF]"); [iApply to_iThy_le_refl|simpl].
    iIntros (vF1 vF2) "HvF".
    iDestruct "HvF" as "(#HvF & _)".
    brel_pures'.
    iModIntro; iSplitR; last done.
    rewrite /τ__F /sem_ty_mbang /=. iIntros "%θ !# %v1 %v2 Hτ1τ2". 
    brel_pures'.
    unfold τ__F.
    iSpecialize ("HvJ" $! θ).
    iSpecialize ("HvG" $! θ).
    iSpecialize ("HvF" $! θ).
    iAssert ((∀ᵣ θ₁, τ2 θ₁ -{ sem_row_union (¡ θ₁) θ }-∘ 𝟙)%T (λ: "r", vG1 (λ: "r", vJ1 v1 "r")%V "r")%V
            (λ: "r", (λ: "f", vG2 (λ: "r", vJ2 "f" "r"))%V v2 "r")%V) with "[Hτ1τ2 HvJ HvG]" as "HclientsF".
    { 
      iSpecialize ("HvJ" with "Hτ1τ2").  
      iEval (rewrite /sem_ty_arr /=).
      iIntros (θ1).
      iIntros (w1 w2) "Hw1w2".
      brel_pures'.
      iAssert ((∀ᵣ θ₁,τ3 θ₁ -{ sem_row_union (¡ θ₁) θ }-∘ 𝟙)%T (λ: "r", vJ1 v1 "r")%V (λ: "r", vJ2 v2 "r")%V) with "[HvJ]" as "HclientsG".
      { rewrite /sem_ty_arr /=.
        iIntros (θ₁).
        iIntros (w0 w3) "Hw0w3".
        brel_pures'.
        rewrite !iLblSig_to_iLblThy_distr.
        iApply (brel_bind'' [_] [_] [] [] with "[][Hw0w3 HvJ]"); try done.
        + simpl. iApply to_iThy_le_intro'. solve_submseteq.
        + assert (to_iThyIfMono OS [] = []) as <- by done.
        iApply (brel_mono OS _ _ [] [] with "[][$HvJ]");
          [iApply to_iThy_le_bot|].
        simpl.
        iIntros (v0 v3) "Hv0v3".
        iSpecialize ("Hv0v3" with "Hw0w3").
      rewrite !iLblSig_to_iLblThy_distr.
      iApply "Hv0v3". }
      iSpecialize ("HvG" with "HclientsG").
      rewrite !iLblSig_to_iLblThy_distr. 
      iApply (brel_bind'' [_] [_] [] [] with "[][HvG Hw1w2]"); try done.
      + simpl. iApply to_iThy_le_intro'. solve_submseteq.
      + assert (to_iThyIfMono OS [] = []) as <- by done.
        iApply (brel_mono OS _ _ [] [] with "[][$HvG]");
          [iApply to_iThy_le_bot|].
        simpl.
      iIntros (v0 v3) "Hv0v3".
      iSpecialize ("Hv0v3" with "Hw1w2").
      rewrite !iLblSig_to_iLblThy_distr. 
      iApply "Hv0v3".
    } 
    iSpecialize ("HvF" with "HclientsF").
    iApply "HvF".
   Qed.

  Lemma functionality_comp_func_comp_assoc_gen_core (F1 F2 G1 G2 J1 J2 : expr) τ1 τ2 τ1' τJ τF (vs : gmap string (val * val)) :
    ⊢
    brel ⊤ F1 F2 (iLblSig_to_iLblThy ⊥) (λ v1 v2, (∀ᵣ θ, (∀ᵣ θF, τF θF -{ sem_row_union (¡θF)%R θ}-∘ 𝟙) → ∀ᵣ θ1, τ2 θ1 -{ sem_row_union (¡θ1)%R θ }-∘ 𝟙)%T v1 v2 ∗ [] ⊨ₑ vs) -∗
    brel ⊤ G1 G2 (iLblSig_to_iLblThy ⊥) (λ v1 v2, (∀ᵣ θ, (∀ᵣ θJ1, ∀ᵣ θJ2, τJ θJ1 θJ2 -{ sem_row_union (¡θJ1)%R (sem_row_union (¡θJ2)%R θ)}-∘ 𝟙) → (∀ᵣ θ1,( ∀ᵣ θ2, (τ1 θ1 × τF θ2) -{ sem_row_union (¡θ1)%R (sem_row_union (¡θ2)%R θ)}-∘ 𝟙)))%T v1 v2 ∗ [] ⊨ₑ vs) -∗
    brel ⊤ J1 J2 (iLblSig_to_iLblThy ⊥) (λ v1 v2, (∀ᵣ θ, (τ1' θ) → (∀ᵣ θJ1, ∀ᵣ θJ2, (τJ θJ1 θJ2) -{sem_row_union (¡θJ1)%R (sem_row_union (¡θJ2)%R θ)}-∘ 𝟙))%T v1 v2 ∗ [] ⊨ₑ vs) -∗
    brel ⊤ ((F1 ∘Fₛ G1)%V ∘fₛ J1)%V (F2 ∘Fₛ (G2 ∘fₛ J2)%V) (iLblSig_to_iLblThy ⊥) (λ v1 v2, (∀ᵣ θ, (τ1' θ) → (∀ᵣ θ1, ∀ᵣ θ2, ((τ1 θ1) × (τ2 θ2)) -{ sem_row_union (¡ θ1)%R (sem_row_union (¡ θ2)%R θ) }-∘ 𝟙))%T v1 v2 ∗ [] ⊨ₑ vs).
  Proof.
   iIntros "HFF HGG HJJ".
    rewrite /functionality_composition /func_comp //=. simpl.
    brel_pures'.
    simpl. 
    iApply (brel_bind [_ ] [_ ; _]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot |].
    assert (to_iThyIfMono OS [] = []) as <- by done. 
    iApply (brel_mono OS with "[][$HJJ]"); [iApply to_iThy_le_refl|simpl].
    iIntros (vJ1 vJ2) "(#HJ1J2 & _)".
    iApply (brel_bind [_ ; _; _] [_ ; _ ; _]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot |].
    assert (to_iThyIfMono OS [] = []) as <- by done. 
    iApply (brel_mono OS with "[][$HGG]"); [iApply to_iThy_le_refl|simpl].
    iIntros (vG1 vG2) "(#HG1G2 & _)".
    brel_pures'.
    iApply (brel_bind [_ ; _ ; _  ; _] [_ ; _]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot |].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HFF]"); [iApply to_iThy_le_refl|simpl].
    iIntros (vF1 vF2) "(#HF1F2 & _)".
    brel_pures'.
    iModIntro; iSplitR; last done.
    rewrite /τ__F /sem_ty_mbang /=. iIntros "%θ !# %f1 %f2 Hff".
    brel_pures'. 
    iModIntro.
    iIntros (θ1 θ2 v v') "Heffs".
    brel_pures'.
    rewrite /sem_ty_prod.
    iDestruct "Heffs" as ( w1 w1' w2 w2') "[%Hr1 [%Hr2 [Hτ1 Hτ2]]]". 
    rewrite -> Hr1.
    rewrite -> Hr2. 
    brel_pures'.
    iSpecialize ("HF1F2" $! (sem_row_union (¡θ1)%R θ)).
    iApply (brel_bind [_] [_] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][HF1F2 Hff Hτ1 HG1G2 HJ1J2]"); [iApply to_iThy_le_refl|iApply "HF1F2"|].
    - iIntros (θF rF1 rF2) "HτF". 
      brel_pures'.
      iApply (brel_bind [_] [_] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
      assert (to_iThyIfMono OS [] = []) as <- by done. 
      iApply (brel_mono OS with "[][HG1G2 Hff HJ1J2]"); [iApply to_iThy_le_refl| iApply "HG1G2" |].
      + simpl. iIntros (θJ1 θJ2 x1 x2) "HτJ". brel_pures'.
        iApply (brel_wand with "[HJ1J2 Hff HτJ]"). 
        { iSpecialize ("HJ1J2" $! θ).
          (*iSpecialize ("HJ1J2" $! θJ1 θJ2).*)
          iSpecialize ("HJ1J2" with "Hff").
          iApply (brel_bind [_] [_]); [iApply traversable_to_iThy_nil | iApply to_iThy_le_bot|].
          assert (to_iThyIfMono OS [] = []) as <- by done. 
          iApply (brel_mono OS _ _ [] [] with "[][HJ1J2]");
          [iApply to_iThy_le_bot| by iApply "HJ1J2" |].
          simpl.
          iIntros (v1 v2) "Hv1v2".
          iSpecialize ("Hv1v2" with "HτJ").
          iApply "Hv1v2". }
        iModIntro; iIntros (v1 v2) "Hv1v2".
        iApply "Hv1v2".
      + simpl. iIntros (GJ1 GJ2) "HGJ". 
        rewrite !iLblSig_to_iLblThy_distr.
        iApply (brel_introduction_mono (iLblSig_to_iLblThy (¡ θ1)%R ++ iLblSig_to_iLblThy  (¡ θF)%R ++ iLblSig_to_iLblThy θ)).
        { iApply to_iThy_le_intro'; solve_submseteq. }
        do 2 (rewrite <- iLblSig_to_iLblThy_distr).
        iApply "HGJ".
        iExists w1, w1', rF1, rF2.
        iSplitR "Hτ1 HτF"; [ iPureIntro; reflexivity | iSplitR "Hτ1 HτF"; [iPureIntro; reflexivity| iFrame]].
    - simpl. iIntros (F1' F2') "HF'".
      iDestruct ("HF'" with "Hτ2") as "HF".
      rewrite !iLblSig_to_iLblThy_distr.
      iApply (brel_introduction_mono (iLblSig_to_iLblThy (¡θ2)%R ++ iLblSig_to_iLblThy (¡ θ1)%R ++ iLblSig_to_iLblThy θ)); last done.
      iApply to_iThy_le_intro'; solve_submseteq.
  Qed.

   Lemma functionality_comp_func_comp_assoc_gen_rev_core (F1 F2 G1 G2 J1 J2 : expr) τ1 τ2 τ1' τJ τF (vs : gmap string (val * val)) :
     ⊢
     brel ⊤ F1 F2 (iLblSig_to_iLblThy ⊥) (λ v1 v2, (∀ᵣ θ, (∀ᵣ θF, τF θF -{ sem_row_union (¡θF)%R θ}-∘ 𝟙) → ∀ᵣ θ1, τ2 θ1 -{ sem_row_union (¡θ1)%R θ }-∘ 𝟙)%T v1 v2 ∗ [] ⊨ₑ vs) -∗
     brel ⊤ G1 G2 (iLblSig_to_iLblThy ⊥) (λ v1 v2, (∀ᵣ θ, (∀ᵣ θJ1, ∀ᵣ θJ2, τJ θJ1 θJ2 -{ sem_row_union (¡θJ1)%R (sem_row_union (¡θJ2)%R θ)}-∘ 𝟙) → (∀ᵣ θ1,( ∀ᵣ θ2, (τ1 θ1 × τF θ2) -{ sem_row_union (¡θ1)%R (sem_row_union (¡θ2)%R θ)}-∘ 𝟙)))%T v1 v2 ∗ [] ⊨ₑ vs) -∗
     brel ⊤ J1 J2 (iLblSig_to_iLblThy ⊥) (λ v1 v2, (∀ᵣ θ, (τ1' θ) → (∀ᵣ θJ1, ∀ᵣ θJ2, (τJ θJ1 θJ2) -{sem_row_union (¡θJ1)%R (sem_row_union (¡θJ2)%R θ)}-∘ 𝟙))%T v1 v2 ∗ [] ⊨ₑ vs) -∗
     brel ⊤ (F1 ∘Fₛ (G1 ∘fₛ J1)%V) ((F2 ∘Fₛ G2)%V ∘fₛ J2)%V (iLblSig_to_iLblThy ⊥) (λ v1 v2, (∀ᵣ θ, (τ1' θ) → (∀ᵣ θ1, ∀ᵣ θ2, ((τ1 θ1) × (τ2 θ2)) -{ sem_row_union (¡ θ1)%R (sem_row_union (¡ θ2)%R θ) }-∘ 𝟙))%T v1 v2 ∗ [] ⊨ₑ vs).
   Proof.
   iIntros "HFF HGG HJJ".
    rewrite /functionality_composition /func_comp //=. simpl.
    brel_pures'.
    simpl.
    iApply (brel_bind [_ ; _] [_ ]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot |].
    assert (to_iThyIfMono OS [] = []) as <- by done. 
    iApply (brel_mono OS with "[][$HJJ]"); [iApply to_iThy_le_refl|simpl].
    iIntros (vJ1 vJ2) "(#HJ1J2 & _)".
    iApply (brel_bind [_ ; _ ; _] [_ ; _  ; _]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot |].
    assert (to_iThyIfMono OS [] = []) as <- by done. 
    iApply (brel_mono OS with "[][$HGG]"); [iApply to_iThy_le_refl|simpl].
    iIntros (vG1 vG2) "(#HG1G2 & _)".
    brel_pures'.
    iApply (brel_bind [_ ; _ ] [_ ; _ ; _ ; _]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot |].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HFF]"); [iApply to_iThy_le_refl|simpl].
    iIntros (vF1 vF2) "(#HF1F2 & _)".
    brel_pures'.
    iModIntro; iSplitR; last done.
    rewrite /τ__F /sem_ty_mbang /=. iIntros "%θ !# %f1 %f2 Hff".
    brel_pures'. 
    iModIntro.
    iIntros (θ1 θ2 v v') "Heffs".
    brel_pures'.
    rewrite /sem_ty_prod.
    iDestruct "Heffs" as ( w1 w1' w2 w2') "[%Hr1 [%Hr2 [Hτ1 Hτ2]]]". 
    rewrite -> Hr1.
    rewrite -> Hr2. 
    brel_pures'.
    iSpecialize ("HF1F2" $! (sem_row_union (¡θ1)%R θ)).
    iApply (brel_bind [_] [_] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][HF1F2 Hff Hτ1 HG1G2 HJ1J2]"); [iApply to_iThy_le_refl|iApply "HF1F2"|].
    - iIntros (θF rF1 rF2) "HτF". 
      brel_pures'.
      iApply (brel_bind [_] [_] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
      assert (to_iThyIfMono OS [] = []) as <- by done. 
      iApply (brel_mono OS with "[][HG1G2 Hff HJ1J2]"); [iApply to_iThy_le_refl| iApply "HG1G2" |].
      + simpl. iIntros (θJ1 θJ2 x1 x2) "HτJ". brel_pures'.
         iApply (brel_wand with "[HJ1J2 Hff HτJ]"). 
        { iSpecialize ("HJ1J2" $! θ).
          (*iSpecialize ("HJ1J2" $! θJ1 θJ2).*)
          iSpecialize ("HJ1J2" with "Hff").
          iApply (brel_bind [_] [_]); [iApply traversable_to_iThy_nil | iApply to_iThy_le_bot|].
          assert (to_iThyIfMono OS [] = []) as <- by done. 
          iApply (brel_mono OS _ _ [] [] with "[][HJ1J2]");
          [iApply to_iThy_le_bot| by iApply "HJ1J2" |].
          simpl.
          iIntros (v1 v2) "Hv1v2".
          iSpecialize ("Hv1v2" with "HτJ").
          iApply "Hv1v2". }
        iModIntro; iIntros (v1 v2) "Hv1v2".
        iApply "Hv1v2".
      + simpl. iIntros (GJ1 GJ2) "HGJ". 
        rewrite !iLblSig_to_iLblThy_distr.
        iApply (brel_introduction_mono (iLblSig_to_iLblThy (¡ θ1)%R ++ iLblSig_to_iLblThy  (¡ θF)%R ++ iLblSig_to_iLblThy θ)).
        { iApply to_iThy_le_intro'; solve_submseteq. }
        do 2 (rewrite <- iLblSig_to_iLblThy_distr).
        iApply "HGJ".
        iExists w1, w1', rF1, rF2.
        iSplitR "Hτ1 HτF"; [ iPureIntro; reflexivity | iSplitR "Hτ1 HτF"; [iPureIntro; reflexivity| iFrame]].
    - simpl. iIntros (F1' F2') "HF'".
      iDestruct ("HF'" with "Hτ2") as "HF".
      rewrite !iLblSig_to_iLblThy_distr.
      iApply (brel_introduction_mono (iLblSig_to_iLblThy (¡θ2)%R ++ iLblSig_to_iLblThy (¡ θ1)%R ++ iLblSig_to_iLblThy θ)); last done.
      iApply to_iThy_le_intro'; solve_submseteq.
   Qed.

  Lemma functionality_comp_func_comp_assoc_core (F1 F2 G1 G2 J1 J2 : expr) τ1 τ2 τ1' τJ τF (vs : gmap string (val * val)) :
    ⊢
    brel ⊤ F1 F2 (iLblSig_to_iLblThy ⊥) (λ v1 v2, (∀ᵣ θ, (∀ᵣ θF, τF θF -{ sem_row_union (¡θF)%R θ}-∘ 𝟙) → ∀ᵣ θ1, τ2 θ1 -{ sem_row_union (¡θ1)%R θ }-∘ 𝟙)%T v1 v2 ∗ [] ⊨ₑ vs) -∗
    brel ⊤ G1 G2 (iLblSig_to_iLblThy ⊥) (λ v1 v2, (∀ᵣ θ, (∀ᵣ θJ, τJ θJ -{ sem_row_union (¡θJ)%R θ}-∘ 𝟙) → ∀ᵣ θ1, ∀ᵣ θ2, (τ1 θ1 × τF θ2) -{ sem_row_union (¡θ2)%R (sem_row_union (¡θ1)%R θ)}-∘ 𝟙)%T v1 v2 ∗ [] ⊨ₑ vs) -∗
    brel ⊤ J1 J2 (iLblSig_to_iLblThy ⊥) (λ v1 v2, (∀ᵣ θ, ∀ᵣ θJ, τ1' θ → τJ θJ -{sem_row_union (¡θJ)%R θ}-∘ 𝟙)%T v1 v2 ∗ [] ⊨ₑ vs) -∗
    brel ⊤ ((F1 ∘Fₛ G1)%V ∘fₛ J1)%V (F2 ∘Fₛ (G2 ∘fₛ J2)) (iLblSig_to_iLblThy ⊥) (λ v1 v2, (∀ᵣ θ, (τ1' θ) → (∀ᵣ θ1, ∀ᵣ θ2, ((τ1 θ1) × (τ2 θ2)) -{ sem_row_union (¡ θ1)%R (sem_row_union (¡ θ2)%R θ) }-∘ 𝟙))%T v1 v2 ∗ [] ⊨ₑ vs).
  Proof.
   iIntros "HFF HGG HJJ".
    rewrite /functionality_composition /func_comp //=. simpl.
    brel_pures'.
    simpl.
    iApply (brel_bind [_ ] [_ ;_ ]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot |].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HJJ]"); [iApply to_iThy_le_refl|simpl].
    iIntros (vJ1 vJ2) "(#HJ1J2 & _)".
    brel_pures'.
    iApply (brel_bind [_ ; _ ; _] [_ ; _  ; _]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot |].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HGG]"); [iApply to_iThy_le_refl|simpl].
    iIntros (vG1 vG2) "(#HG1G2 & _)".
    brel_pures'.
    iApply (brel_bind [_ ; _ ; _  ; _] [_ ; _]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot |].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HFF]"); [iApply to_iThy_le_refl|simpl].
    iIntros (vF1 vF2) "(#HF1F2 & _)".
    brel_pures'.
    iModIntro; iSplitR; last done.
    rewrite /τ__F /sem_ty_mbang /=. iIntros "%θ !# %f1 %f2 Hff".
    brel_pures'. 
    iModIntro.
    iIntros (θ1 θ2 v v') "Heffs".
    brel_pures'.
    rewrite /sem_ty_prod.
    iDestruct "Heffs" as ( w1 w1' w2 w2') "[%Hr1 [%Hr2 [Hτ1 Hτ2]]]". 
    rewrite -> Hr1.
    rewrite -> Hr2. 
    brel_pures'.
    iSpecialize ("HF1F2" $! (sem_row_union (¡θ1)%R θ)).
    iApply (brel_bind [_] [_] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][HF1F2 Hff Hτ1 HG1G2 HJ1J2]"); [iApply to_iThy_le_refl|iApply "HF1F2"|].
    - iIntros (θF rF1 rF2) "HτF". 
      brel_pures'.
      iApply (brel_bind [_] [_] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
      assert (to_iThyIfMono OS [] = []) as <- by done. 
      iApply (brel_mono OS with "[][HG1G2 Hff HJ1J2]"); [iApply to_iThy_le_refl| iApply "HG1G2" |].
      + simpl. iIntros (θJ x1 x2) "HτJ". brel_pures'.
         iSpecialize ("HJ1J2" $! θ).
          iSpecialize ("HJ1J2" $! θJ).
          iSpecialize ("HJ1J2" with "Hff").
          iApply (brel_bind [_] [_]); [iApply traversable_to_iThy_nil | iApply to_iThy_le_bot|].
          assert (to_iThyIfMono OS [] = []) as <- by done. 
          iApply (brel_mono OS _ _ [] [] with "[][HJ1J2]");
          [iApply to_iThy_le_bot| by iApply "HJ1J2" |].
          simpl.
          iIntros (v1 v2) "Hv1v2".
          iSpecialize ("Hv1v2" with "HτJ").
          iApply "Hv1v2".       
      + simpl. iIntros (GJ1 GJ2) "HGJ". 
        iApply "HGJ".
        iExists w1, w1', rF1, rF2.
        iSplitR "Hτ1 HτF"; [ iPureIntro; reflexivity | iSplitR "Hτ1 HτF"; [iPureIntro; reflexivity| iFrame]].
    - simpl. iIntros (F1' F2') "HF'".
      iDestruct ("HF'" with "Hτ2") as "HF".
      rewrite !iLblSig_to_iLblThy_distr.
      iApply (brel_introduction_mono (iLblSig_to_iLblThy (¡θ2)%R ++ iLblSig_to_iLblThy (¡ θ1)%R ++ iLblSig_to_iLblThy θ)); last done.
      iApply to_iThy_le_intro'; solve_submseteq.
  Qed.

  Lemma functionality_comp_func_comp_assoc_rev_core (F1 F2 G1 G2 J1 J2 : expr) τ1 τ2 τ1' τJ τF (vs : gmap string (val * val)) :
    ⊢
    brel ⊤ F1 F2 (iLblSig_to_iLblThy ⊥) (λ v1 v2, (∀ᵣ θ, (∀ᵣ θF, τF θF -{ sem_row_union (¡θF)%R θ}-∘ 𝟙) → ∀ᵣ θ1, τ2 θ1 -{ sem_row_union (¡θ1)%R θ }-∘ 𝟙)%T v1 v2 ∗ [] ⊨ₑ vs) -∗
    brel ⊤ G1 G2 (iLblSig_to_iLblThy ⊥) (λ v1 v2, (∀ᵣ θ, (∀ᵣ θJ, τJ θJ -{ sem_row_union (¡ θJ)%R θ}-∘ 𝟙) → ∀ᵣ θ1, ∀ᵣ θ2, (τ1 θ1 × τF θ2) -{ sem_row_union (¡θ2)%R (sem_row_union (¡θ1)%R θ)}-∘ 𝟙)%T v1 v2 ∗ [] ⊨ₑ vs) -∗
    brel ⊤ J1 J2 (iLblSig_to_iLblThy ⊥) (λ v1 v2, (∀ᵣ θ, ∀ᵣ θJ, τ1' θ → τJ θJ -{sem_row_union (¡θJ)%R θ}-∘ 𝟙)%T v1 v2 ∗ [] ⊨ₑ vs) -∗
    brel ⊤ (F1 ∘Fₛ (G1 ∘fₛ J1)%V) ((F2 ∘Fₛ G2)%V ∘fₛ J2) (iLblSig_to_iLblThy ⊥) (λ v1 v2, (∀ᵣ θ, (τ1' θ) → (∀ᵣ θ1, ∀ᵣ θ2, ((τ1 θ1) × (τ2 θ2)) -{ sem_row_union (¡ θ1)%R (sem_row_union (¡ θ2)%R θ) }-∘ 𝟙))%T v1 v2 ∗ [] ⊨ₑ vs).
  Proof.
    iIntros "HFF HGG HJJ".
    rewrite /functionality_composition /func_comp //=. simpl.
    brel_pures'.
     simpl.
    iApply (brel_bind [_ ; _] [_ ]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot |].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HJJ]"); [iApply to_iThy_le_refl|simpl].
    iIntros (vJ1 vJ2) "(#HJ1J2 & _)".
    brel_pures'.
    iApply (brel_bind [_ ; _ ; _] [_ ; _  ; _]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot |].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HGG]"); [iApply to_iThy_le_refl|simpl].
    iIntros (vG1 vG2) "(#HG1G2 & _)".
    brel_pures'.
    iApply (brel_bind [_ ; _ ] [_ ; _ ; _ ; _]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot |].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HFF]"); [iApply to_iThy_le_refl|simpl].
    iIntros (vF1 vF2) "(#HF1F2 & _)".
    brel_pures'.
    iModIntro; iSplitR; last done.
    rewrite /τ__F /sem_ty_mbang /=. iIntros "%θ !# %f1 %f2 Hff".
    brel_pures'.
    iModIntro.
    iIntros (θ1 θ2 v v') "Heffs".
    brel_pures'.
    rewrite /sem_ty_prod.
    iDestruct "Heffs" as ( w1 w1' w2 w2') "[%Hr1 [%Hr2 [Hτ1 Hτ2]]]". 
    rewrite -> Hr1.
    rewrite -> Hr2.
    brel_pures'.
    iSpecialize ("HF1F2" $! (sem_row_union (¡θ1)%R θ)).
    iApply (brel_bind [_] [_] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][HF1F2 Hff Hτ1 HG1G2 HJ1J2]"); [iApply to_iThy_le_refl|iApply "HF1F2"|].
    - iIntros (θF rF1 rF2) "HτF". 
      brel_pures'.
      iApply (brel_bind [_] [_] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
      assert (to_iThyIfMono OS [] = []) as <- by done.
      iApply (brel_mono OS with "[][HG1G2 Hff HJ1J2]"); [iApply to_iThy_le_refl|iApply "HG1G2"|].
      + iIntros (θJ x1 x2) "HτJ". brel_pures'.
        iSpecialize ("HJ1J2" $! θ).
          iSpecialize ("HJ1J2" $! θJ).
          iSpecialize ("HJ1J2" with "Hff").
          iApply (brel_bind [_] [_]); [iApply traversable_to_iThy_nil | iApply to_iThy_le_bot|].
          assert (to_iThyIfMono OS [] = []) as <- by done. 
          iApply (brel_mono OS _ _ [] [] with "[][HJ1J2]");
          [iApply to_iThy_le_bot| by iApply "HJ1J2" |].
          simpl.
          iIntros (v1 v2) "Hv1v2".
          iSpecialize ("Hv1v2" with "HτJ").
          iApply "Hv1v2".
      + simpl. iIntros (GJ1 GJ2) "HGJ".
        iApply "HGJ".
        iExists w1, w1', rF1, rF2.
        iSplitR "Hτ1 HτF"; [ iPureIntro; reflexivity | iSplitR "Hτ1 HτF"; [iPureIntro; reflexivity| iFrame]].
    - simpl. iIntros (F1' F2') "HF'".
      iDestruct ("HF'" with "Hτ2") as "HF".
      rewrite !iLblSig_to_iLblThy_distr.
      iApply (brel_introduction_mono (iLblSig_to_iLblThy (¡θ2)%R ++ iLblSig_to_iLblThy (¡θ1)%R ++ iLblSig_to_iLblThy θ)); last done.
      iApply to_iThy_le_intro'; solve_submseteq.
  Qed.


End composition_operators.

Notation "F₁ ||ᵣₛ F₂" := (parallel_composition F₁ F₂) (at level 10).

Notation "F ∘Fₛ G" := (functionality_composition F G) (at level 10). 

Notation "F ∘fₛ G" := (func_comp F G) (at level 10).

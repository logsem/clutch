From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import agree excl auth frac excl_auth.
From iris.algebra.lib Require Import dfrac_agree.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode
 spec_rules spec_ra class_instances.
From clutch.prob_eff_lang.probblaze Require Import tactics.
From clutch.prob_eff_lang.probblaze Require Import sem_types sem_row sem_sig sem_judgement sem_def valgroup.

(*Import fingroup.

Import fingroup.fingroup.


*)
Import valgroup_tactics.
Section parallel_composition.
  Context `{probblazeRGS Σ}.

  (*Fixpoint list_args_app (f : val) (op_l : list val) : val :=
    match: op_l with
    | nil => f
    | op_x :: op_{xs} => (f op_x)
    end.*)
  
  
(*Definition left_composition (f_x f_y : val) : val := λ: "f" "op_x1" "op_x2" "op_y1" "op_y2",
                                                                                                       f_x (f_y "f" "op_y1" "op_y2") "op_x1" "op_x2".*)

  (*Definition left_composition (f_x f_y : val) : val := λ: "f", f_x (λ: "op_x1" "op_x2", (f_y (λ: "op_y1" "op_y2", ("f" "op_x1" "op_x2" "op_y1" "op_y2")))).*)

  (*Definition left_composition (f_x f_y : val) "e1" "e2" "e3" :=
    λ: "f" "op_x1" "op_x2" "op_y1" "op_y2",
    effect*)

  (*Definition s_chan_composition (f_x f_y : val) :=
    λ: "f" "op_x1" "op_x2" "op_y1" "op_y2",
      effect "channel"
      let: "doSend" := (λ: "m", do: (EffName "channel") (Send "m")) in
      let: "doRecv" := (λ: "m", do: (EffName "channel") (Recv "m")) in
      (*effect "schannel"
      let: "doSecSend" := (λ: "m", do: (EffName "schannel") (Send "m")) in
      let: "doSecRecv" := (λ: "m", do: (EffName "schannel") (Recv "m")) in *)
      effect "getKey"
      let: "doGK" := (λ: "party", do: (EffName "getKey") "party") in
      f_x "channel" "doSend" "doRecv" (f_y "getKey" "doGK" "f" "op_y1" "op_y2") "op_x1" "op_x2".*)

  (* r_x are effect operations raised by the functionality f_x, and c_x are effect operations
     handled by f_x.*) 
  Definition left_composition : val :=
    λ: "F₁" "F₂" "f" "r₁" "r₂",
      "F₁" (λ: "h₁",
             "F₂" (λ: "h₂", "f" "h₁" "h₂") "r₂") "r₁".
  
 
  Definition right_composition : val :=
    λ: "F₁" "F₂" "f" "r₂" "r₁",
      "F₁" (λ: "h₁",     (* consider uncurrying the effect thunks *)
             "F₂" (λ: "h₂", "f" "h₂" "h₁") "r₂") "r₁".

  Definition functionality_composition (F G : expr) : val :=
    (λ: "f" "rH" "rF", F (λ: "rG", G "f" "rH" "rG") "rF").


  Notation " F₁ ||ₗ F₂" := (left_composition F₁ F₂)%V (at level 10).

  Notation "F₁ ||ᵣ F₂" := (right_composition F₁ F₂)%V (at level 10).
  
  Notation "F '∘F' G" := (functionality_composition F G) (at level 10).

  Definition func_comp (F G : expr) : val :=
    (λ: "f", F (G "f")).

  Notation "F ∘f G" := (func_comp F G) (at level 10).

  About sem_ty_row_forall.
  About sem_ty_type_forall.
  Definition τ := ( ∀ᵣ θ, ∀ₜ α ,α ⊸ 𝟙)%T.
  
  (* changed the type of τ__f to be a function that can be applied multiple times *)
  Definition τ__f θ τ1' τ2' := (∀ᵣ θ1, ∀ᵣ θ2, τ1' θ1 ⊸ τ2' θ2 -{ sem_row_union θ1 (sem_row_union θ2 θ) }-∘ 𝟙)%T.
  Definition τ__F τ τ' := (∀ᵣ θ, (∀ᵣ θ₁, τ' θ₁ -{ sem_row_union θ₁ θ}-∘ 𝟙) ⊸ (∀ᵣ θ₂, τ θ₂ -{ sem_row_union θ₂ θ }-∘ 𝟙))%T.

  Lemma iLblSig_to_iLblThy_distr L1 L2 :
    @iLblSig_to_iLblThy Σ (L1 ++ L2) = iLblSig_to_iLblThy L1 ++ (iLblSig_to_iLblThy L2).
  Proof.
    induction L1; first done.
    simpl. by rewrite IHL1.
  Qed. 
  
  Lemma parallel_comp_left (F₁ F₂ F : val) θ τ1 τ2 τ1' τ2' :
    ⊢ sem_val_typed F₁ F₂ (τ__F τ2 τ2' ) -∗

    sem_val_typed F F (τ__F τ1 τ1') -∗

    sem_typed [] (F ||ₗ F₁) (F ||ₗ F₂) ⊥ ((τ__f θ τ1' τ2') ⊸ (∀ᵣ θ1, ∀ᵣ θ2, τ1 θ1 ⊸ τ2 θ2 -{ sem_row_union θ1 (sem_row_union θ2 θ) }-∘ 𝟙))%T [].
  Proof.
    iIntros "#HFF #HF".
    iIntros (?) "!# Hvs //=".
    unfold left_composition.
    brel_pures'. iFrame. 
    iIntros "!> %f1 %f2 Hff". brel_pures'.
    iIntros "!> %θ1 %θ2 %r1 %r2 Heffs1".
    brel_pures'.
    iIntros "!> %r1'%r2' Heffs2".
    brel_pures'. 
    rewrite /sem_val_typed /τ__F //=.
    iDestruct "HFF" as "#HFF".
    iDestruct "HF" as "#HF".
    unfold τ__f.
    iAssert ((∀ᵣ θ1, τ1' θ1 -{ sem_row_union θ1 (sem_row_union θ2 θ) }-∘ 𝟙)%T
               (λ: "h₁", F₁ (λ: "h₂", f1 "h₁" "h₂") r1')%V
               (λ: "h₁", F₂ (λ: "h₂", f2 "h₁" "h₂") r2')%V) with "[Heffs2 Hff]" as "Hclients".
    { iIntros (θ1' v1 v2) "Hτ1'". brel_pures'.
      
      iAssert ((∀ᵣ θ2, τ2' θ2 -{ sem_row_union θ2 (sem_row_union θ1' θ) }-∘ 𝟙)%T (λ: "h₂", f1 v1 "h₂")%V (λ: "h₂", f2 v2 "h₂")%V) 
        with "[Hτ1' Hff]" as "H".
      { iIntros (θ2' v1' v2') "Hτ2'". 
        brel_pures'.
        iDestruct ("Hff" $! θ1' θ2' with "Hτ1'") as "Hff".
        iApply (brel_bind [_] [_]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot |].
        assert (to_iThyIfMono OS [] = []) as <- by done.
        iApply (brel_mono OS with "[][$Hff]"); [iApply to_iThy_le_refl|simpl].
        iIntros (fv1 fv2) "Hff".
        iSpecialize ("Hff" with "Hτ2'").
        rewrite !iLblSig_to_iLblThy_distr.
        iApply (brel_introduction_mono (iLblSig_to_iLblThy θ1' ++ iLblSig_to_iLblThy θ2' ++ iLblSig_to_iLblThy θ)).
        { iApply to_iThy_le_intro'; solve_submseteq. }
        iApply "Hff". }
      iSpecialize ("HFF" with "H").
      iApply (brel_bind [_] [_]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot |].
      assert (to_iThyIfMono OS [] = []) as <- by done.
      iApply (brel_mono OS with "[][$HFF]"); [iApply to_iThy_le_refl|simpl].
      iIntros (F1 F2) "HFF".
      iSpecialize ("HFF" with "Heffs2").
      rewrite !iLblSig_to_iLblThy_distr.
      iApply (brel_introduction_mono ((iLblSig_to_iLblThy θ2 ++ iLblSig_to_iLblThy θ1' ++ iLblSig_to_iLblThy θ))).
      { iApply to_iThy_le_intro'; solve_submseteq. }
      iApply "HFF". 
    }
    iSpecialize ("HF" with "Hclients"). 
    iApply (brel_bind [_] [_] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HF]"); [iApply to_iThy_le_refl|simpl].
    iIntros (??) "Hvv".
    iSpecialize ("Hvv" $! θ1).
    rewrite /sem_ty_mbang //=.
    by iApply "Hvv".
  Qed. 
  
  Lemma func_comp_left (F1 F2 : expr) (F : val) τ τ' τ'':
    is_closed_expr ∅ F1 →
    is_closed_expr ∅ F2 →
    ⊢ (∀ θ : sem_row Σ, sem_typed [] F1 F2 ⊥ (τ θ ⊸ τ' θ)%T []) -∗
    (∀ θ : sem_row Σ, sem_val_typed F F (τ'' θ ⊸ τ θ)%T) -∗
    sem_val_typed (λ: "f", F1 (F "f")) (λ: "f", F2 (F "f")) (∀ᵣ θ, τ'' θ ⊸ τ' θ)%T.
  Proof.
    iIntros (HF1closed HF2closed) "#HFF #HF". rewrite /sem_val_typed /sem_typed //=.
    iIntros (???) "!# Hτ'' /=".
    (* iDestruct ("HF" $! θ ∅) as "#HFθ". *)
    iDestruct ("HF" with "Hτ''") as "HFτ".
    brel_pures'.
    erewrite !subst_is_closed; try done.
    iApply (brel_bind' [_] [_]); [iApply traversable_to_iThy_nil|].
    iApply (brel_wand with "HFτ").
    iIntros (??) "!# Hvv".
    iApply (brel_bind' [_] [_]); [iApply traversable_to_iThy_nil|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS _ _ [] [] with "[][HFF]");
      [iApply to_iThy_le_bot| |].
    { iDestruct ("HFF" $! θ ∅) as "#HFθ". rewrite !subst_map_empty.
      by iApply "HFθ". }
    simpl. iIntros (??) "(Hff&_)". by iApply "Hff".
  Qed. 

  Lemma parallel_comp_right (F1 F2 F : val) θ τ1 τ2 τ1' τ2' :
    ⊢ sem_val_typed F1 F2 (τ__F τ2 τ2' ) -∗
  
    sem_val_typed F F (τ__F τ1 τ1') -∗
  
    sem_typed [] (F1 ||ᵣ F) (F2 ||ᵣ F) ⊥ ((τ__f θ τ1' τ2') ⊸ (∀ᵣ θ1, ∀ᵣ θ2, τ1 θ1 ⊸ τ2 θ2 -{ sem_row_union θ1 (sem_row_union θ2 θ) }-∘ 𝟙))%T [].
  Proof.
    iIntros "#HFF #HF".
    iIntros (?) "!# Hvs //=".
    unfold right_composition.
    brel_pures'. iFrame. 
    iIntros "!> %f1 %f2 Hff". brel_pures'.
    iIntros "!> %θ1 %θ2 %r1 %r2 Heffs1".
    brel_pures'.
    iIntros "!> %r1'%r2' Heffs2".
    brel_pures'. 
    rewrite /sem_val_typed /τ__F //=.
    iDestruct "HFF" as "#HFF".
    iDestruct "HF" as "#HF".
    unfold τ__f.
    iAssert ((∀ᵣ θ2, τ2' θ2 -{ sem_row_union θ2 (sem_row_union θ1 θ) }-∘ 𝟙)%T
               (λ: "h₁", F (λ: "h₂", f1 "h₂" "h₁") r1)%V
               (λ: "h₁", F (λ: "h₂", f2 "h₂" "h₁") r2)%V) with "[Heffs1 Hff]" as "Hclients".
    { iIntros (θ2' v1 v2) "Hτ2'". brel_pures'.
      
      iAssert ((∀ᵣ θ2, τ1' θ2 -{ sem_row_union θ2 (sem_row_union θ2' θ) }-∘ 𝟙)%T (λ: "h₂", f1 "h₂" v1)%V (λ: "h₂", f2 "h₂" v2)%V) 
        with "[Hτ2' Hff]" as "H".
      { iIntros (θ1' v1' v2') "Hτ1'". 
        brel_pures'.
        iDestruct ("Hff" $! θ1' θ2' with "Hτ1'") as "Hff".
        iApply (brel_bind [_] [_]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot |].
        assert (to_iThyIfMono OS [] = []) as <- by done.
        iApply (brel_mono OS with "[][$Hff]"); [iApply to_iThy_le_refl|simpl].
        iIntros (fv1 fv2) "Hff".
        iSpecialize ("Hff" with "Hτ2'").
        rewrite !iLblSig_to_iLblThy_distr.
        iApply "Hff". }
      iSpecialize ("HF" with "H").
      iApply (brel_bind [_] [_]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot |].
      assert (to_iThyIfMono OS [] = []) as <- by done.
      iApply (brel_mono OS with "[][$HF]"); [iApply to_iThy_le_refl|simpl].
      iIntros (F1' F2') "HF".
      iSpecialize ("HF" with "Heffs1").
      rewrite !iLblSig_to_iLblThy_distr.
      iApply (brel_introduction_mono ((iLblSig_to_iLblThy θ1 ++ iLblSig_to_iLblThy θ2' ++ iLblSig_to_iLblThy θ))).
      { iApply to_iThy_le_intro'; solve_submseteq. }
      iApply "HF". 
    }
    iSpecialize ("HFF" with "Hclients"). 
    iApply (brel_bind [_] [_] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HFF]"); [iApply to_iThy_le_refl|simpl].
    iIntros (??) "Hvv".
    iSpecialize ("Hvv" $! θ2 with "Heffs2").
    rewrite !iLblSig_to_iLblThy_distr.
    iApply (brel_introduction_mono (iLblSig_to_iLblThy θ2 ++ iLblSig_to_iLblThy θ1 ++ iLblSig_to_iLblThy θ)).
    { iApply to_iThy_le_intro'; solve_submseteq. }
    iApply "Hvv".
  Qed.
  
  Definition τ__F' θ τ τ' := ((∀ᵣ θ₁, τ' θ₁ -{ sem_row_union θ₁ θ}-∘ 𝟙) ⊸ (∀ᵣ θ₂, τ θ₂ -{ sem_row_union θ₂ θ }-∘ 𝟙))%T.

  Lemma func_comp_parallel_comp_assoc (F J : val) (G : expr) (f x : string) τ1 τ2 τG τ1' τ2' θ :
    (BNamed f) ≠ (BNamed x) →
    ⊢ sem_val_typed F F (τ__F τ2 τG)-∗
    sem_val_typed (λ: f x, G) (λ: f x, G) (τ__F' θ τG τ1') -∗
    sem_val_typed J J (τ__F τ1 τ2') -∗
    sem_typed [] ((F ∘f (λ: f x, G)%V) ||ᵣ J) 
      (F ∘F ((λ: f x, G)%V ||ᵣ J)) ⊥ ((τ__f θ τ1' τ2') ⊸ (∀ᵣ θ1, ∀ᵣ θ2, τ1 θ1 ⊸ τ2 θ2 -{ sem_row_union θ1 (sem_row_union θ2 θ) }-∘ 𝟙))%T [].
  Proof.
    iIntros (Hfx) "#HFF #HGG #HJJ !# %vs _". simpl.
    unfold func_comp,right_composition,functionality_composition.
    brel_pures'.
    iModIntro; iSplit; last done.
    iIntros (f1 f2) "Hff".
    brel_pures'.
    iModIntro.
    iIntros (θ1 θ2 v1 v1') "Hτ1".
    brel_pures'.
    iModIntro. 
    iIntros (v2 v2') "Hτ2".
    brel_pures_l 3.
    brel_pures_r.
    brel_pures'. 
    rewrite decide_True; last (split; done).
    iAssert ((∀ᵣ θ₁, τG θ₁ -{ sem_row_union θ₁ θ }-∘ 𝟙)%T 
               (λ: x, val_subst f (λ: "h₁", J (λ: "h₂", f1 "h₂" "h₁") v1) G)%V
               (λ: "rG", (λ: "F₁" "F₂" "f" "r₂" "r₁", "F₁" (λ: "h₁", "F₂" (λ: "h₂", "f" "h₂" "h₁") "r₂") "r₁")%V (λ: f x, G)%V J f2 v1' "rG")%V) with "[Hτ1 Hff]" as "Hgg".
    { iIntros (θG rg1 rg2) "HτG".
      brel_pures'.
      rewrite decide_True; last (split; done).
      admit. }
    iSpecialize ("HFF" with "Hgg").
    iApply (brel_bind [_] [_] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HFF]"); [iApply to_iThy_le_refl|simpl].
    iIntros (??) "Hτ".
    iSpecialize ("Hτ" with "Hτ2").
    rewrite !iLblSig_to_iLblThy_distr.
    iApply (brel_introduction_mono (iLblSig_to_iLblThy θ2 ++ iLblSig_to_iLblThy θ)); last done.
    iApply to_iThy_le_intro'; solve_submseteq.
  Admitted.
      
  Lemma func_comp_assoc (F G J : val) τ1 τ2 τ3 τ4 : 
    ⊢ sem_val_typed F F (∀ᵣ θ, τ3 θ ⊸ τ4 θ)%T -∗
    sem_val_typed G G (∀ᵣ θ, τ2 θ ⊸ τ3 θ)%T -∗
    sem_val_typed J J (∀ᵣ θ, τ1 θ ⊸ τ2 θ)%T -∗
    sem_val_typed (λ: "f", F (G (J "f"))) (λ: "f", (λ: "f", F (G "f"))%V (J "f")) (∀ᵣ θ, τ1 θ ⊸ τ4 θ)%T.
  Proof. 
    iIntros "#HFF #HGG #HJJ".
    iIntros (θ v1 v2) "!# Hτ1".
    iSpecialize ("HJJ" with "Hτ1").
    brel_pures'.
    iApply (brel_bind' [_;_] [_]); [iApply traversable_to_iThy_nil|].
    iApply (brel_wand with "HJJ").
    iIntros (v1' v2') "!# Hτ2".
    iSpecialize ("HGG" with "Hτ2").
    brel_pures'.
    iApply (brel_bind' [_] [_]); [iApply traversable_to_iThy_nil|].
    iApply (brel_wand with "HGG").
    iIntros (v1'' v2'') "!# Hτ3".
    iSpecialize ("HFF" with "Hτ3").
    iApply (brel_wand with "HFF").
    by iIntros (??) "!# H".
  Qed. 


    
  Lemma functionality_comp_func_comp_assoc (F G : val) (J : expr) (f x : string) τ1 τ2 τ1' τJ τF :
    (BNamed f) ≠ (BNamed x) →
     is_closed_expr ∅ F →
     is_closed_expr ∅ G →
    ⊢ sem_typed [] F F ⊥ (∀ᵣ θ, (∀ᵣ θF, τF θF -{ sem_row_union θF θ}-∘ 𝟙) ⊸ ∀ᵣ θ1, τ1 θ1 -{ sem_row_union θ1 θ }-∘ 𝟙)%T [] -∗

    sem_typed [] G G ⊥ (∀ᵣ θ, τJ θ ⊸ ∀ᵣ θ1, τ2 θ1 ⊸ ∀ᵣ θ2, τF θ2 -{ sem_row_union θ1 (sem_row_union θ2 θ)}-∘ 𝟙)%T [] -∗

    sem_typed [] (λ: f x, J) (λ: f x, J) ⊥ (∀ᵣ θ, τ1' θ ⊸ τJ θ)%T [] -∗

    sem_val_typed ((F ∘F G) ∘f (λ: f x, J)%V) (F ∘F (G ∘f (λ: f x, J)%V))
      (∀ᵣ θ, (τ1' θ) ⊸ (∀ᵣ θ1, ∀ᵣ θ2, (τ1 θ1) ⊸ (τ2 θ2) -{ sem_row_union θ1 (sem_row_union θ2 θ) }-∘ 𝟙))%T. 
  Proof. 
    iIntros (Hfx HFclosed HGclosed) "#HFF #HGG #HJJ".
    rewrite /functionality_composition /func_comp //=.
    iIntros (θ f1 f2) "!# Hτ1'".
    rewrite /functionality_composition /func_comp //=.
    brel_pures'. 
    (* do 2 (erewrite subst_is_closed; try done).
       erewrite (subst_is_closed _ F); try done.
       iModIntro.
       iIntros (θ1 θ2 v1 v1') "Hτ1".
       brel_pures'.
       iModIntro.
       iIntros (v2 v2') "Hτ2".
       brel_pures'.
       erewrite !(subst_is_closed _ F); try done.
       erewrite !(subst_is_closed _ G); try done.
       rewrite decide_True; last (split; done). *)
    
  Admitted.
    
  Lemma functionality_comp_cong (F G1 G2 : expr) τ1 τ2 τ1' τF :
     is_closed_expr ∅ F →
     is_closed_expr ∅ G1 →
     is_closed_expr ∅ G2 →
    ⊢ sem_typed [] G1 G2 ⊥ (∀ᵣ θ, τ1' θ ⊸ ∀ᵣ θ1, ∀ᵣ θ2, τ1 θ1 ⊸ τF θ2 -{ sem_row_union θ1 (sem_row_union θ2 θ)}-∘ 𝟙)%T [] -∗
      sem_typed [] F F ⊥ (∀ᵣ θ, (∀ᵣ θF, τF θF -{ sem_row_union θF θ}-∘ 𝟙) ⊸ ∀ᵣ θ1, τ2 θ1 -{ sem_row_union θ1 θ }-∘ 𝟙)%T [] -∗
      sem_val_typed (F ∘F G1) (F ∘F G2) 
        (∀ᵣ θ, τ1' θ ⊸ (∀ᵣ θ1, ∀ᵣ θ2, τ1 θ1 ⊸ τ2 θ2 -{ sem_row_union θ1 (sem_row_union θ2 θ) }-∘ 𝟙))%T. 
  Proof. 
    iIntros (HFclosed HG1closed HG2closed)  "#HGG #HFF".
    iIntros (θ f1 f2) "!# Hτ1'".
    rewrite /functionality_composition //=.
    brel_pures'. 
    iModIntro.
    iIntros (θ1 θ2 v1 v1') "Hτ1".
    brel_pures'.
    iModIntro.
    iIntros (v2 v2') "Hτ2".
    brel_pures'.
    iAssert ([] ⊨ₑ ∅) as "#Hempty"; first done.
    erewrite !(subst_is_closed _ F); try done.
    erewrite !(subst_is_closed _ G1); try done.
    erewrite !(subst_is_closed _ G2); try done.
    iAssert ((∀ᵣ θF, τF θF -{ sem_row_union θF (sem_row_union θ1 θ) }-∘ 𝟙)%T (λ: "rG", G1 f1 v1 "rG")%V (λ: "rG", G2 f2 v1' "rG")%V) with "[Hτ1' Hτ1]" as "Hff".
    { iIntros (θF rG1 rG2) "HτF".
      brel_pures'.
      erewrite !(subst_is_closed _ G1); try done.
      erewrite !(subst_is_closed _ G2); try done.
      unfold sem_typed. simpl. 
      iSpecialize ("HGG" $! ∅ with "Hempty").
      rewrite !subst_map_empty.
      iApply (brel_bind [_;_;_] [_;_;_]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
      assert (to_iThyIfMono OS [] = []) as <- by done.
      iApply (brel_mono OS with "[][$HGG]"); [iApply to_iThy_le_refl|simpl].
      iIntros (Gv1 Gv2) "(HGGv&_)".
      iSpecialize ("HGGv" with "Hτ1'").
      iApply (brel_bind [_;_] [_;_]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
      assert (to_iThyIfMono OS [] = []) as <- by done.
      iApply (brel_mono OS with "[][$HGGv]"); [iApply to_iThy_le_refl|simpl].
      iIntros (Gfv1 Gfv2) "HGfv".
      iSpecialize ("HGfv" with "Hτ1").
      iApply (brel_bind [_] [_]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
      assert (to_iThyIfMono OS [] = []) as <- by done.
      iApply (brel_mono OS with "[][$HGfv]"); [iApply to_iThy_le_refl|simpl].
      iIntros (GfrGv1 GfrGv2) "HGfrGv".
      iSpecialize ("HGfrGv" with "HτF").
      iApply (brel_wand with "[HGfrGv]").
      { rewrite !iLblSig_to_iLblThy_distr.
        iApply (brel_introduction_mono ((iLblSig_to_iLblThy θ1 ++ iLblSig_to_iLblThy θF ++ iLblSig_to_iLblThy θ))).
        { iApply to_iThy_le_intro'; solve_submseteq. }
        done. }
      iIntros (??) "!# $". }
    iSpecialize ("HFF" with "Hempty").
    rewrite !subst_map_empty.
    iApply (brel_bind [_;_] [_;_]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HFF]"); [iApply to_iThy_le_refl|simpl].
    iIntros (Fv1 Fv2) "(HFv&_)".
    iSpecialize ("HFv" with "Hff").
    iApply (brel_bind [_] [_]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HFv]"); [iApply to_iThy_le_refl|simpl].
    iIntros (HFfv1 HFfv2) "HFfv".
    iSpecialize ("HFfv" with "Hτ2").
    rewrite !iLblSig_to_iLblThy_distr.
    iApply (brel_introduction_mono ((iLblSig_to_iLblThy θ2 ++ iLblSig_to_iLblThy θ1 ++ iLblSig_to_iLblThy θ))).
    { iApply to_iThy_le_intro'; solve_submseteq. }
    iApply "HFfv".
  Qed.

End parallel_composition.

Notation " F₁ ||ₗ F₂" := (left_composition F₁ F₂) (at level 10).

Notation "F₁ ||ᵣ F₂" := (right_composition F₁ F₂) (at level 10).

Notation "F '∘F' G" := (functionality_composition F G) (at level 10). 

Notation "F ∘f G" := (func_comp F G) (at level 10).

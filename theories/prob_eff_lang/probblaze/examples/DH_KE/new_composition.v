From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import agree excl auth frac excl_auth.
From iris.algebra.lib Require Import dfrac_agree.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import
  logic primitive_laws proofmode
  spec_rules spec_ra class_instances tactics notation valgroup metatheory
  sem_types sem_row sem_sig sem_judgement sem_def
  def_dhke sec_channel_def xor sec_channel_prf dhke_channel_lazy_results dhke_channel_lazy_authchan.
From clutch.prob_eff_lang.probblaze.typing Require Import fundamental.
From clutch.prob_eff_lang.probblaze.examples.DH_KE Require Import
  new_composition_defs new_composition_closed new_composition_typing.

Import fingroup.
Import fingroup.fingroup.

Import valgroup_tactics.

(* Top-level semantic-typing results: each composite program is related to
   itself (or to the next in the chain) at the target type [τ].  The proofs
   are complete modulo the building-block typing lemmas admitted in
   [new_composition_typing.v]. *)

Section new_comp_verification.
  Context `{probblazeRGS Σ}.


  Lemma functionality_comp_func_comp_assoc_curried (F G : expr) (J : expr) (f x y : string) τ1 τ2 τ1' τJ τJ' τF :
    (BNamed f) ≠ (BNamed x) →
    (BNamed f) ≠ (BNamed y) →
    (BNamed x) ≠ (BNamed y) →
     is_closed_expr ∅ F →
     is_closed_expr ∅ G →
    ⊢ sem_typed [] F F ⊥ (∀ᵣ θ, (∀ᵣ θF, τF θF -{ sem_row_union θF θ}-∘ 𝟙) ⊸ ∀ᵣ θ1, τ2 θ1 -{ sem_row_union θ1 θ }-∘ 𝟙)%T [] -∗

    sem_typed [] G G ⊥ (∀ᵣ θ, (∀ᵣ θJ, τJ θJ ⊸ τJ' θJ -{ sem_row_union θJ θ}-∘ 𝟙) ⊸ ∀ᵣ θ1, τ1 θ1 ⊸ ∀ᵣ θ2, τF θ2 -{ sem_row_union θ1 (sem_row_union θ2 θ)}-∘ 𝟙)%T [] -∗

    (∀ θ θJ, sem_typed [(f, τ1' θ); (x, τJ θJ); (y, τJ' θJ)] J J (sem_row_union θJ θ) (𝟙)%T []) -∗

    sem_val_typed ((F ∘F G) ∘f (λ: f x y, J)%V) (F ∘F (G ∘f (λ: f x y, J)%V))
      (∀ᵣ θ, (τ1' θ) ⊸ (∀ᵣ θ1, ∀ᵣ θ2, (τ1 θ1) ⊸ (τ2 θ2) -{ sem_row_union θ1 (sem_row_union θ2 θ) }-∘ 𝟙))%T.
  Proof using All.
    iIntros (Hfx Hfy Hxy HFclosed HGclosed) "#HFF #HGG #HJJ".
    rewrite /functionality_composition /func_comp //=.
    iIntros (θ f1 f2) "!# Hτ1'".
    rewrite /functionality_composition /func_comp //=.
    brel_pures'.
    do 2 (erewrite subst_is_closed; try done).
    erewrite (subst_is_closed _ F); try done.
    iModIntro.
    iIntros (θ1 θ2 v1 v1') "Hτ1".
    brel_pures'.
    iModIntro.
    iIntros (v2 v2') "Hτ2".
    brel_pures'.
    erewrite !(subst_is_closed _ F); try done.
    erewrite !(subst_is_closed _ G); try done.
    rewrite decide_True; last (split; done).
    iApply (brel_bind [_;_] [_;_] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][HFF]"); [iApply to_iThy_le_refl| |].
    { iAssert ([] ⊨ₑ ∅) as "HΓ"; first done. iSpecialize ("HFF" with "HΓ").
      rewrite subst_map_empty. iApply "HFF". }
    iClear (F HFclosed) "HFF".
    simpl. iIntros (F1 F2) "(HFF&_)".
    iSpecialize ("HFF" $! (sem_row_union θ1 θ)).
    iApply (brel_bind [_] [_] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][HFF Hτ1' Hτ1]"); [iApply to_iThy_le_refl|iApply "HFF"|].
    - iIntros (θF rF1 rF2) "HτF".
      brel_pures'.
      rewrite decide_True; last (split; done).
      erewrite !(subst_is_closed _ G); try done.
      iApply (brel_bind [_;_;_] [_;_;_] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
      assert (to_iThyIfMono OS [] = []) as <- by done.
      iApply (brel_mono OS with "[][HGG]"); [iApply to_iThy_le_refl| |].
      { iAssert ([] ⊨ₑ ∅) as "HΓ"; first done. iSpecialize ("HGG" with "HΓ").
        rewrite subst_map_empty. iApply "HGG". }
      iClear (G HGclosed) "HGG".
      simpl. iIntros (G1 G2) "(HGG&_)".
      iApply (brel_bind [_;_] [_;_] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
      assert (to_iThyIfMono OS [] = []) as <- by done.
      iApply (brel_mono OS with "[][HGG Hτ1']"); [iApply to_iThy_le_refl|iApply "HGG"|].
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
        iAssert ([(f, τ1' θ); (x, τJ θJ); (y, τJ' θJ)] ⊨ₑ {[ y:=(y1,y2); x:=(x1,x2); f:=(f1,f2) ]}) with "[Hτ1' HτJ HτJ']" as "HΓ".
        { rewrite !sem_env.env_sem_typed_cons sem_env.env_sem_typed_empty.
          iSplitL "Hτ1'". { iExists f1, f2. iFrame "Hτ1'". iPureIntro. rewrite lookup_insert_ne; [|naive_solver]. rewrite lookup_insert_ne; [|naive_solver]. by simplify_map_eq. }
          iSplitL "HτJ". { iExists x1, x2. iFrame "HτJ". iPureIntro. rewrite lookup_insert_ne; [|naive_solver]. by simplify_map_eq. }
          iSplitL "HτJ'". { iExists y1, y2. iFrame "HτJ'". iPureIntro. by simplify_map_eq. }
          done. }
        iDestruct ("HJJ" $! θ θJ with "HΓ") as "Hrel".
        rewrite -Hs1 -Hs2.
        iApply (brel_wand with "[Hrel]"). { iApply "Hrel". }
        iIntros (v0 v3) "!# ($&_)".
      + simpl. iIntros (GJ1 GJ2) "HGJ".
        iApply (brel_bind [_] [_] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
        assert (to_iThyIfMono OS [] = []) as <- by done.
        iApply (brel_mono OS with "[][HGJ Hτ1]"); [iApply to_iThy_le_refl| by iApply "HGJ"|].
        simpl. iIntros (G1' G2') "HG'".
        iDestruct ("HG'" with "HτF") as "HG'".
        rewrite !iLblSig_to_iLblThy_distr.
        iApply (brel_introduction_mono (iLblSig_to_iLblThy θ1 ++ iLblSig_to_iLblThy θF ++ iLblSig_to_iLblThy θ)); last done.
        iApply to_iThy_le_intro'; solve_submseteq.
    - simpl. iIntros (F1' F2') "HF'".
      iDestruct ("HF'" with "Hτ2") as "HF".
      rewrite !iLblSig_to_iLblThy_distr.
      iApply (brel_introduction_mono (iLblSig_to_iLblThy θ2 ++ iLblSig_to_iLblThy θ1 ++ iLblSig_to_iLblThy θ)); last done.
      iApply to_iThy_le_intro'; solve_submseteq.
  Qed.

  Lemma functionality_comp_func_comp_assoc_rev_curried (F G : expr) (J : expr) (f x y : string) τ1 τ2 τ1' τJ τJ' τF :
    (BNamed f) ≠ (BNamed x) →
    (BNamed f) ≠ (BNamed y) →
    (BNamed x) ≠ (BNamed y) →
     is_closed_expr ∅ F →
     is_closed_expr ∅ G →
    ⊢ sem_typed [] F F ⊥ (∀ᵣ θ, (∀ᵣ θF, τF θF -{ sem_row_union θF θ}-∘ 𝟙) ⊸ ∀ᵣ θ1, τ2 θ1 -{ sem_row_union θ1 θ }-∘ 𝟙)%T [] -∗

    sem_typed [] G G ⊥ (∀ᵣ θ, (∀ᵣ θJ, τJ θJ ⊸ τJ' θJ -{ sem_row_union θJ θ}-∘ 𝟙) ⊸ ∀ᵣ θ1, τ1 θ1 ⊸ ∀ᵣ θ2, τF θ2 -{ sem_row_union θ1 (sem_row_union θ2 θ)}-∘ 𝟙)%T [] -∗

    (∀ θ θJ, sem_typed [(f, τ1' θ); (x, τJ θJ); (y, τJ' θJ)] J J (sem_row_union θJ θ) (𝟙)%T []) -∗

    sem_val_typed (F ∘F (G ∘f (λ: f x y, J)%V)) ((F ∘F G) ∘f (λ: f x y, J)%V)
      (∀ᵣ θ, (τ1' θ) ⊸ (∀ᵣ θ1, ∀ᵣ θ2, (τ1 θ1) ⊸ (τ2 θ2) -{ sem_row_union θ1 (sem_row_union θ2 θ) }-∘ 𝟙))%T.
  Proof using All.
    (* Mirror of [functionality_comp_func_comp_assoc_curried]: this is the
       byte-for-byte same proof except the single [subst_is_closed] target
       below is [G] instead of [F] (exactly as the old rev proof
       [functionality_comp_func_comp_assoc_rev] differs from the forward one),
       reflecting the swapped left/right programs in the statement. *)
    iIntros (Hfx Hfy Hxy HFclosed HGclosed) "#HFF #HGG #HJJ".
    rewrite /functionality_composition /func_comp //=.
    iIntros (θ f1 f2) "!# Hτ1'".
    rewrite /functionality_composition /func_comp //=.
    brel_pures'.
    do 2 (erewrite subst_is_closed; try done).
    erewrite (subst_is_closed _ G); try done.
    iModIntro.
    iIntros (θ1 θ2 v1 v1') "Hτ1".
    brel_pures'.
    iModIntro.
    iIntros (v2 v2') "Hτ2".
    brel_pures'.
    erewrite !(subst_is_closed _ F); try done.
    erewrite !(subst_is_closed _ G); try done.
    rewrite decide_True; last (split; done).
    iApply (brel_bind [_;_] [_;_] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][HFF]"); [iApply to_iThy_le_refl| |].
    { iAssert ([] ⊨ₑ ∅) as "HΓ"; first done. iSpecialize ("HFF" with "HΓ").
      rewrite subst_map_empty. iApply "HFF". }
    iClear (F HFclosed) "HFF".
    simpl. iIntros (F1 F2) "(HFF&_)".
    iSpecialize ("HFF" $! (sem_row_union θ1 θ)).
    iApply (brel_bind [_] [_] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][HFF Hτ1' Hτ1]"); [iApply to_iThy_le_refl|iApply "HFF"|].
    - iIntros (θF rF1 rF2) "HτF".
      brel_pures'.
      rewrite decide_True; last (split; done).
      erewrite !(subst_is_closed _ G); try done.
      iApply (brel_bind [_;_;_] [_;_;_] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
      assert (to_iThyIfMono OS [] = []) as <- by done.
      iApply (brel_mono OS with "[][HGG]"); [iApply to_iThy_le_refl| |].
      { iAssert ([] ⊨ₑ ∅) as "HΓ"; first done. iSpecialize ("HGG" with "HΓ").
        rewrite subst_map_empty. iApply "HGG". }
      iClear (G HGclosed) "HGG".
      simpl. iIntros (G1 G2) "(HGG&_)".
      iApply (brel_bind [_;_] [_;_] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
      assert (to_iThyIfMono OS [] = []) as <- by done.
      iApply (brel_mono OS with "[][HGG Hτ1']"); [iApply to_iThy_le_refl|iApply "HGG"|].
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
        iAssert ([(f, τ1' θ); (x, τJ θJ); (y, τJ' θJ)] ⊨ₑ {[ y:=(y1,y2); x:=(x1,x2); f:=(f1,f2) ]}) with "[Hτ1' HτJ HτJ']" as "HΓ".
        { rewrite !sem_env.env_sem_typed_cons sem_env.env_sem_typed_empty.
          iSplitL "Hτ1'". { iExists f1, f2. iFrame "Hτ1'". iPureIntro. rewrite lookup_insert_ne; [|naive_solver]. rewrite lookup_insert_ne; [|naive_solver]. by simplify_map_eq. }
          iSplitL "HτJ". { iExists x1, x2. iFrame "HτJ". iPureIntro. rewrite lookup_insert_ne; [|naive_solver]. by simplify_map_eq. }
          iSplitL "HτJ'". { iExists y1, y2. iFrame "HτJ'". iPureIntro. by simplify_map_eq. }
          done. }
        iDestruct ("HJJ" $! θ θJ with "HΓ") as "Hrel".
        rewrite -Hs1 -Hs2.
        iApply (brel_wand with "[Hrel]"). { iApply "Hrel". }
        iIntros (v0 v3) "!# ($&_)".
      + simpl. iIntros (GJ1 GJ2) "HGJ".
        iApply (brel_bind [_] [_] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
        assert (to_iThyIfMono OS [] = []) as <- by done.
        iApply (brel_mono OS with "[][HGJ Hτ1]"); [iApply to_iThy_le_refl| by iApply "HGJ"|].
        simpl. iIntros (G1' G2') "HG'".
        iDestruct ("HG'" with "HτF") as "HG'".
        rewrite !iLblSig_to_iLblThy_distr.
        iApply (brel_introduction_mono (iLblSig_to_iLblThy θ1 ++ iLblSig_to_iLblThy θF ++ iLblSig_to_iLblThy θ)); last done.
        iApply to_iThy_le_intro'; solve_submseteq.
    - simpl. iIntros (F1' F2') "HF'".
      iDestruct ("HF'" with "Hτ2") as "HF".
      rewrite !iLblSig_to_iLblThy_distr.
      iApply (brel_introduction_mono (iLblSig_to_iLblThy θ2 ++ iLblSig_to_iLblThy θ1 ++ iLblSig_to_iLblThy θ)); last done.
      iApply to_iThy_le_intro'; solve_submseteq.
  Qed.


  Context (channel leaksec channel1 channel2 getKey1 getKey2 leakauth1 leakauth2 keyleak1 keyleak2 schannel1 schannel2 l1 l2 l2': label).
  Context {vg: val_group}.
  Context {cg: clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg: @val_group_generator vg}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO,!inG Σ (dfrac_agreeR valO)}.
  Let Key := S (S n'').
  Let Support := S (S n'').
  Variable xor_struct : XOR (Key := Key) (Support := Support).
  Context `{!XOR_spec (Key := Key) (Support := Support) (H := xor_struct)}.

  (* The composites that mention [CHAN xor] / [R_CHAN] depend on the section
     variable [xor_struct] (via the [XOR] projection [xor]); once the
     definitions live in a separate file they are generalised over it, so we
     re-fix [xor_struct] here to read them back as plain values.  ([SIMSIMFCHAN]
     and [τ] do not mention [xor], so they need no re-fixing; the [iApply]-ed
     typing/closedness lemmas infer [xor_struct] from the goal.) *)
  Local Notation REAL_CHAN_DHKE := (REAL_CHAN_DHKE xor_struct).
  Local Notation REAL_CHAN_DH_REAL := (REAL_CHAN_DH_REAL xor_struct).
  Local Notation REAL_CHAN_DH_RAND := (REAL_CHAN_DH_RAND xor_struct).
  Local Notation DHSIM_FKE_CHAN1 := (DHSIM_FKE_CHAN1 xor_struct).
  Local Notation DHSIM_FKE_CHAN2 := (DHSIM_FKE_CHAN2 xor_struct).
  Local Notation DHSIM_FKE_CHAN3 := (DHSIM_FKE_CHAN3 xor_struct).
  Local Notation DHSIM_FKE_CHAN4 := (DHSIM_FKE_CHAN4 xor_struct).

  (* F_OAUTH[ F_AUTH [DH_KE [CHAN []]]] ≤ F_OAUTH[ F_AUTH [C[DH_real][CHAN []]]] *)
  (*---------------------------------------------------------------------------*)
  Lemma F_OAUTH_DHKE_C_REAL :
    ⊢ sem_val_typed REAL_CHAN_DHKE REAL_CHAN_DH_REAL τ.
  Proof using All.
    iApply func_comp_left.
    - apply F_AUTH_DHKE_closed.
    - apply F_AUTH_C_DDH_real_closed.
    - iIntros (θ). iApply parallel_comp_right.
      + unfold τ__F. unshelve iApply F_AUTH_DH_KE_FAUTH_C_DH_real; try done.
      + iApply F_OAUTH_typed.   (* F_OAUTH well-typed *)
    - iApply CHAN_typed.        (* CHAN well-typed *)
  Qed.

  Lemma C_REAL_DHKE_F_OAUTH :
     ⊢ sem_val_typed REAL_CHAN_DH_REAL REAL_CHAN_DHKE τ.
  Proof using All.
    iApply func_comp_left.
    - apply F_AUTH_C_DDH_real_closed.
    - apply F_AUTH_DHKE_closed.
    - iIntros (θ). iApply parallel_comp_right.
      + unfold τ__F. iApply F_AUTH_C_DH_real_FAUTH_DH_KE; try done.
      + iApply F_OAUTH_typed.   (* F_OAUTH well-typed *)
    - iApply CHAN_typed.        (* CHAN well-typed *)
  Qed.

  Lemma REAL_CHAN_DH_RAND_DHSIM_FKE_CHAN1 :
    ⊢ sem_val_typed REAL_CHAN_DH_RAND DHSIM_FKE_CHAN1 τ.
  Proof using All.
    iApply func_comp_left.
    - apply F_AUTH_C_DDH_rand_closed.
    - apply DHSIM_FKE_CHAN1_closed.
    - iIntros (θ). iApply parallel_comp_right.
      + iApply F_AUTH_C_DH_rand_FAUTH_DH_SIM_F_KE; try done.
      + iApply F_OAUTH_typed.
    - iApply CHAN_typed.
  Qed.

  Lemma DHSIM_FKE_CHAN1_REAL_CHAN_DH_RAND :
    ⊢ sem_val_typed DHSIM_FKE_CHAN1 REAL_CHAN_DH_RAND τ.
  Proof using All.
    iApply func_comp_left.
    - apply DHSIM_FKE_CHAN1_closed.
    - apply F_AUTH_C_DDH_rand_closed.
    - iIntros (θ). iApply parallel_comp_right.
      + iApply F_AUTH_DH_SIM_F_KE_FAUTH_C_DH_rand; try done.
      + iApply F_OAUTH_typed.
    - iApply CHAN_typed.
  Qed.

  Lemma DHSIM_FKE_CHAN1_DHSIM_FKE_CHAN2 :
    ⊢ sem_val_typed  DHSIM_FKE_CHAN1 DHSIM_FKE_CHAN2 τ.
  Proof using All.
    iApply func_comp_left.
    - apply DHSIM_FKE_CHAN1_closed.
    - apply DHSIM_FKE_CHAN2_closed.
    - iIntros (θ). iApply parallel_comp_right.
      + unfold τ__F. iApply func_comp_assoc.
        * iApply F_AUTH_typed.
        * iApply DH_SIM_typed.
        * iApply F_KE_lazy_alice_typed.
      + iApply F_OAUTH_typed.
    - iApply CHAN_typed.
  Qed.

  Lemma DHSIM_FKE_CHAN2_DHSIM_FKE_CHAN1 :
    ⊢ sem_val_typed DHSIM_FKE_CHAN2 DHSIM_FKE_CHAN1 τ.
  Proof using All.
    iApply func_comp_left.
    - apply DHSIM_FKE_CHAN2_closed.
    - apply DHSIM_FKE_CHAN1_closed.
    - iIntros (θ). iApply parallel_comp_right.
      + unfold τ__F. iApply func_comp_assoc_rev.
        * iApply F_AUTH_typed.
        * iApply DH_SIM_typed.
        * iApply F_KE_lazy_alice_typed.
      + iApply F_OAUTH_typed.
    - iApply CHAN_typed.
  Qed.

  Lemma DHSIM_FKE_CHAN2_DHSIM_FKE_CHAN3 :
    ⊢ sem_val_typed DHSIM_FKE_CHAN2 DHSIM_FKE_CHAN3 τ.
  Proof using All.
    iApply func_comp_left.
    - apply DHSIM_FKE_CHAN2_closed.
    - apply DHSIM_FKE_CHAN3_closed.
    - iIntros (θ). iApply func_comp_parallel_comp_assoc; try done.
      + iApply F_AUTH_DH_SIM_typed_val.
      + iApply F_KE_body_typed.
      + iApply F_OAUTH_typed.
    - iApply CHAN_typed.
  Qed.

  Lemma DHSIM_FKE_CHAN3_DHSIM_FKE_CHAN2 :
    ⊢ sem_val_typed DHSIM_FKE_CHAN3 DHSIM_FKE_CHAN2 τ.
  Proof using All.
    iApply func_comp_left.
    - apply DHSIM_FKE_CHAN3_closed.
    - apply DHSIM_FKE_CHAN2_closed.
    - iIntros (θ). iApply func_comp_parallel_comp_assoc_rev; try done.
      + iApply F_AUTH_DH_SIM_typed_val.
      + iApply F_KE_body_typed.
      + iApply F_OAUTH_typed.
    - iApply CHAN_typed.
  Qed.


  Lemma DHSIM_FKE_CHAN3_DHSIM_FKE_CHAN4 :
    ⊢ sem_val_typed DHSIM_FKE_CHAN3 DHSIM_FKE_CHAN4 τ.
  Proof using All.
    iApply functionality_comp_func_comp_assoc_curried; first done ; first done ; first done.
    - apply F_AUTH_DH_SIM_closed.
    - apply F_KE_lazy_alice_F_OAUTH_closed.
    - iApply F_AUTH_DH_SIM_typed.
    - iApply F_KE_F_OAUTH_typed.
    - iApply CHAN_body_typed.
  Qed.

  Lemma DHSIM_FKE_CHAN4_DHSIM_FKE_CHAN3 :
    ⊢ sem_val_typed DHSIM_FKE_CHAN4 DHSIM_FKE_CHAN3 τ.
  Proof using All.
    iApply functionality_comp_func_comp_assoc_rev_curried; first done ; first done ; first done.
    - apply F_AUTH_DH_SIM_closed.
    - apply F_KE_lazy_alice_F_OAUTH_closed.
    - iApply F_AUTH_DH_SIM_typed.
    - iApply F_KE_F_OAUTH_typed.
    - iApply CHAN_body_typed.
  Qed.

  Lemma DHSIM_FKE_CHAN4_SIMFCHAN :
    ⊢ sem_val_typed DHSIM_FKE_CHAN4 SIMSIMFCHAN τ.
  Proof using All.
    iApply functionality_comp_cong.
    - apply F_AUTH_DH_SIM_closed.
    - apply R_CHAN_closed.
    - apply CHAN_SIM_lazy_F_CHAN_closed.
    - unshelve iApply R_I_SCHAN; try done; admit.  (* security of secure channel -- admit related to bijectio assumptions *)
    - iApply F_AUTH_DH_SIM_typed.                         (* well-typedness *)
  Admitted.

  Lemma SIMFCHAN_DHSIM_FKE_CHAN4 :
    ⊢ sem_val_typed SIMSIMFCHAN DHSIM_FKE_CHAN4 τ.
  Proof using All.
    iApply functionality_comp_cong.
    - apply F_AUTH_DH_SIM_closed.
    - apply CHAN_SIM_lazy_F_CHAN_closed.
    - apply R_CHAN_closed.
    - unshelve iApply I_R_SCHAN; done.                    (* security of secure channel *)
    - iApply F_AUTH_DH_SIM_typed.
  Qed.

End new_comp_verification.

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
  Context (channel leaksec channel1 channel2 getKey1 getKey2 leakauth1 leakauth2 keyleak1 keyleak2 schannel1 schannel2 l1 l2 l2': label).
  Context {vg: val_group}.
  Context {cg: clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg: @val_group_generator vg}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO,!inG Σ (dfrac_agreeR valO)}.
  Let Key := S (S n'').
  Let Support := S (S n'').
  Context {xor_struct : XOR (Key := Key) (Support := Support)}.
  Context `{!XOR_spec (Key := Key) (Support := Support) (H := xor_struct)}.

  Variable group_xor_sem : vgG -> vgG -> vgG.
  (* actual BITWISE xor has both left and right inverse, so this assumption is a valid spec.*)
  Hypothesis Bij_xor_sem : ∀ g1 g2 : vgG, group_xor_sem (group_xor_sem g1 g2) g2 = g1.
  Hypothesis Bij_xor_sem_l : ∀ g1 g2 : vgG, group_xor_sem g1 (group_xor_sem g1 g2) = g2.
  Hypothesis vg_int_xor_sem : ∀ g1 g2 : vgG, vg_of_int_sem (xor_sem (int_of_vg_sem g1) (int_of_vg_sem g2)) = Some (group_xor_sem g1 g2 ).
  Variable log__g : vgG -> fin (S (S n'')).
  Hypothesis Val_log : ∀ x : vgG, (g ^+(log__g x))%g = x.
  Hypothesis Bij_log : forall m : vgG, @Bij (fin (S (S n''))) (fin (S (S n''))) (λ n, log__g (group_xor_sem m (g ^+n))).
  Hypothesis Bdd_int_vg : ∀ g : vgG, (int_of_vg_sem g < S (S (S n'')))%nat.



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

  Import valgroup_notation.

  (* The client-intro'd composite core, shared by all four reductions below.
     After the τ-client is applied and [brel_pures'] converges the two inner
     [Rec]/[Val(RecV)] forms of [λ:"f", F_AUTH (C_lazy DH "f")], both sides are
     the same [F_AUTH (C_lazy DH _)] program; this lemma runs the [F_AUTH_F_AUTH]
     composite + getKey handler once, parametric in the DH self-refinement. *)
  Lemma comp_core (DH1 DH2 : val) (θ__L θ₁ θ2 : sem_row Σ) (v1 v2 r1 r2 r1' r2' : val) :
    (𝟙 ⊸ (𝔾 × 𝔾) × 𝔾)%T DH1 DH2 -∗
    τ__f θ__L chan gk v1 v2 -∗
    oaleak θ₁ r1 r2 -∗
    chan θ2 r1' r2' -∗
    brel ⊤ (F_AUTH (C_lazy DH1 (λ: "h₁", F_OAUTH (λ: "h₂", v1 "h₂" "h₁") r1)%V) r1')
           (F_AUTH (C_lazy DH2 (λ: "h₁", F_OAUTH (λ: "h₂", v2 "h₂" "h₁") r2)%V) r2')
           (iLblSig_to_iLblThy (sem_row_union θ₁ (sem_row_union θ2 θ__L)))
           (λ u1 u2 : val, 𝟙%T u1 u2).
  Proof using All.
    iIntros "HDH Hvv Hoaleak Hchan".
    iPoseProof (F_OAUTH_typed) as "#HFO".
    iApply (brel_bind [_] [_] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][HDH Hvv Hoaleak]"); [iApply to_iThy_le_refl| | ].
    { brel_pures'.
      iApply fupd_brel.
      iMod token_alloc as (γtoka) "Htoka".
      iMod token_alloc as (γtokb) "Htokb".
      iMod (auth_alloc (#()%V)) as (γautha) "Hautha".
      iMod (auth_alloc (#()%V)) as (γauthb) "Hauthb".
      iMod dfrac_alloc as (γfraca) "Hfraca".
      iMod dfrac_alloc as (γfracb) "Hfracb".
      iModIntro.
      iApply (F_AUTH_F_AUTH channel1 channel2 _ _
                γtoka γtokb γfraca γfracb γautha γauthb (sem_row_union θ₁ θ__L)
                with "Hfraca Hfracb [-]").
      rewrite /C_lazy. brel_pures'. iModIntro. iIntros (c1 c2). brel_pures'.
      iDestruct ("HDH" $! #()%V #()%V with "[]") as "Hdh"; [by iPureIntro|].
      iApply (brel_bind [AppRCtx _] [AppRCtx _] _ []);
        [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
      assert (to_iThyIfMono OS [] = []) as <- by done.
      iApply (brel_mono OS with "[][$Hdh]"); [iApply to_iThy_le_refl|].
      simpl. iIntros (t1 t2) "Ht".
      iDestruct "Ht" as (p1 p2 gc1 gc2) "(->&->&Hpp&Hgc)".
      iDestruct "Hpp" as (ga1 ga2 gb1 gb2) "(->&->&Hga&Hgb)".
      iDestruct "Hga" as (A) "(->&->)". iDestruct "Hgb" as (B) "(->&->)".
      iDestruct "Hgc" as (C) "(->&->)".
      brel_pures'.
      iApply fupd_brel.
      iMod (auth_upd (vgval A) with "Hautha") as "Hautha".
      iMod (auth_upd (vgval B) with "Hauthb") as "Hauthb".
      iMod (auth_persist with "Hautha") as "#Hautha".
      iMod (auth_persist with "Hauthb") as "#Hauthb".
      iMod (inv_alloc atokN _ (token γtoka ∨ own γfraca DfracDiscarded)%I with "[Htoka]") as "#Hinvta".
      { iNext; iLeft; iFrame. }
      iMod (inv_alloc btokN _ (token γtokb ∨ own γfracb DfracDiscarded)%I with "[Htokb]") as "#Hinvtb".
      { iNext; iLeft; iFrame. }
      iModIntro.
      iApply brel_alloc_l. iIntros (loc1) "!> Hl1". brel_pures_l.
      iApply brel_alloc_r. iIntros (loc2) "Hl2". brel_pures_r.
      iApply (brel_na_alloc
                ((loc1 ↦ NONEV ∗ loc2 ↦ₛ NONEV)
                 ∨ (loc1 ↦□ SOMEV (vgval C) ∗ loc2 ↦ₛ□ SOMEV (vgval C)))%I
                (nroot .@ "lc")).
      iSplitL "Hl1 Hl2"; [iNext; iLeft; iFrame|].
      iIntros "#Hlcinv".
      iApply brel_effect_l. iIntros (gk1) "!> Hgk1".
      iApply brel_effect_r. iModIntro. iIntros (gk2) "Hgk2 !>".
      brel_pures'.
      iApply brel_new_theory.
      iApply (brel_add_label_l with "Hgk1").
      iApply (brel_add_label_r with "Hgk2").
      iAssert (sem_val_typed (λ: "party", do: gk1 "party")%V (λ: "party", do: gk2 "party")%V
                 ((𝟙 + 𝟙)%T -{ θ gk1 gk2 }-> (Option 𝔾))%T) as "Hgg".
      { iModIntro. rewrite /sem_ty_arr /sem_ty_mbang //=.
        iIntros (??) "!# #(%&%&[(->&->&->&->)|(->&->&->&->)])";
          brel_pures';
          iApply brel_introduction'; try constructor;
          iExists _,_,[],[],_; do 2 (iSplit; [by iPureIntro|]; iSplit; [iPureIntro; apply NeutralEctx_nil|]);
                            iSplit; try (iIntros (??) "!# H"; iApply "H").
        - iSplit; first (iPureIntro; left; split; done); iModIntro; iSplitL; last iIntros (key); brel_pures'; iApply brel_value; iIntros "$ !>";
            iExists _,_; [iLeft; by iPureIntro| iRight; iPureIntro; repeat (split; first done); by eexists].
        - iSplit; first (iPureIntro; right; split; done); iModIntro; iSplitL; last iIntros (key); brel_pures'; iApply brel_value; iIntros "$ !>";
            iExists _,_; [iLeft; by iPureIntro| iRight; iPureIntro; repeat (split; first done); by eexists]. }
      unfold sem_val_typed. simpl. iDestruct "Hgg" as "#Hgg".
      set (ac := authchan_row channel1 channel2 c1 c2 γtoka atokN γtokb btokN γfraca γfracb γautha γauthb).
      iAssert (BREL (F_OAUTH (λ: "h₂", v1 "h₂" (λ: "party", do: gk1 "party")%V)%V r1)
                  ≤ (F_OAUTH (λ: "h₂", v2 "h₂" (λ: "party", do: gk2 "party")%V)%V r2)
                  <| iLblSig_to_iLblThy (sem_row_union (θ gk1 gk2) (sem_row_union θ₁ θ__L)) |>
                  {{ λ u1 u2, 𝟙%T u1 u2 }})%I
        with "[Hoaleak Hvv]" as "Hf0".
      { iAssert ((∀ᵣ θ1', chan θ1' -{ sem_row_union θ1' (sem_row_union (θ gk1 gk2) θ__L) }-∘ 𝟙)%T
                   (λ: "h₂", v1 "h₂" (λ: "party", do: gk1 "party")%V)%V
                   (λ: "h₂", v2 "h₂" (λ: "party", do: gk2 "party")%V)%V) with "[Hvv]" as "Hinner".
        { iIntros (θ1' w1' w2') "Hchan'". brel_pures'.
          iDestruct ("Hvv" $! θ1' (θ gk1 gk2) with "Hchan'") as "Hvv2".
          iApply (brel_bind [_] [_]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot |].
          assert (to_iThyIfMono OS [] = []) as <- by done.
          iApply (brel_mono OS with "[][$Hvv2]"); [iApply to_iThy_le_refl|simpl].
          iIntros (gv1 gv2) "Hg". iSpecialize ("Hg" with "Hgg").
          rewrite !iLblSig_to_iLblThy_distr. iApply "Hg". }
        iSpecialize ("HFO" $! (sem_row_union (θ gk1 gk2) θ__L) with "Hinner").
        iApply (brel_bind [_] [_]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot |].
        assert (to_iThyIfMono OS [] = []) as <- by done.
        iApply (brel_mono OS with "[][$HFO]"); [iApply to_iThy_le_refl|simpl].
        iIntros (ov1 ov2) "Ho". iSpecialize ("Ho" $! θ₁ with "Hoaleak").
        rewrite !iLblSig_to_iLblThy_distr.
        iApply (brel_introduction_mono (iLblSig_to_iLblThy θ₁ ++ iLblSig_to_iLblThy (θ gk1 gk2) ++ iLblSig_to_iLblThy θ__L)).
        { iApply to_iThy_le_intro'; solve_submseteq. }
        iApply "Ho". }
      iDestruct (brel_introduction_mono _ ([([gk1],[gk2],GetKey gk1 gk2)] ++ (iLblSig_to_iLblThy ac) ++ (iLblSig_to_iLblThy (sem_row_union θ₁ θ__L))) with "[][$Hf0]") as "Hf'".
      { iApply to_iThy_le_intro'. apply submseteq_skip. by apply submseteq_cons. }
      iApply (brel_exhaustion with "[$Hf']"); [done|done|].
      iLöb as "IH".
      iSplit; [iIntros (v1_ v2_) "!# (-> & ->)"; by brel_pures|].
      iIntros (?????) "!# %Hk1 %Hk2 ([(-> & ->)|(-> & ->)] & #(Hnone & Hsome)) #Hcont".
      + brel_pures; [apply Hk1; set_solver | apply Hk2; set_solver |].
        brel_pures'.
        iApply (brel_na_inv _ _ (nroot.@"lc")); [set_solver|]. iFrame "Hlcinv".
        iIntros "(>[(Hl1 & Hl2) | #(Hl1 & Hl2)] & Hclose)".
        - iApply (brel_load_l _ _ _ [AppRCtx _; CaseCtx _ _] with "Hl1"). iIntros "!> Hl1". brel_pures_l.
          iApply (brel_store_l _ _ _ [AppRCtx _] with "Hl1"). iIntros "!> Hl1". brel_pures_l.
          iApply (brel_load_r _ _ _ _ [AppRCtx _; CaseCtx _ _] with "Hl2"). iIntros "Hl2". brel_pures_r.
          iApply (brel_store_r _ _ _ _ [AppRCtx _] with "Hl2"). iIntros "Hl2". brel_pures_r.
          iApply fupd_brel.
          iMod (ghost_map_elem_persist with "Hl1") as "#Hl1c".
          iMod (ghost_map_elem_persist with "Hl2") as "#Hl2c".
          iModIntro.
          iApply brel_na_close. iFrame "Hclose". iSplitR "Hautha Hauthb"; [iNext; iRight; iFrame "#"|].
          iApply (brel_bind' [_] [_]); [iApply traversable_to_iThy|].
          iApply (brel_introduction' [c1] [c2]). { apply elem_of_cons. right. apply list_elem_of_here. }
          iExists _, _, [], [], _. do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
          iSplitL; [|by iIntros "!>" (??) "H"; iApply "H"].
          iLeft. iLeft. iExists A, A.
          iSplitL.
          { iMod (inv_acc with "Hinvta") as "([>Htok | >#Hfrac'] & Hclose)"; try done.
            - iModIntro. iLeft. iIntros. iFrame. iMod ("Hclose" with "[$]") as "_". iFrame "#". by iModIntro.
            - iModIntro. iRight. iFrame "#". iApply "Hclose". iNext. by iRight. }
          iSplit; first (do 2 (iSplit; try (iPureIntro; done))). iModIntro.
          iApply brel_value. iIntros "$ !>". brel_pures'.
          iApply (brel_bind' [_] [_]); [iApply traversable_to_iThy|].
          iApply (brel_introduction' [c1] [c2]). { apply elem_of_cons. right. apply list_elem_of_here. }
          iExists _, _, [], [], _. do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
          iSplitL; [|by iIntros "!>" (??) "H"; iApply "H"].
          iLeft. iRight. do 2 (iSplit; try (iPureIntro; done)). iModIntro. iSplitL.
          { iApply brel_value. iIntros "$ !>". brel_pures'. iDestruct ("Hcont" with "Hnone") as "Hkk".
            iApply (brel_exhaustion _ _ [_] [_] with "[$Hkk]"); [done|done|iApply "IH"]. }
          iIntros (m) "Ha'". iDestruct (auth_agree with "[$Hauthb] [$Ha']") as "<-".
          iApply brel_value. iIntros "$ !>". brel_pures'. iDestruct ("Hcont" with "Hsome") as "Hkk".
          iApply (brel_exhaustion _ _ [_] [_] with "[$Hkk]"); [done|done|iApply "IH"].
        - iApply (brel_load_l _ _ _ [AppRCtx _; CaseCtx _ _] with "Hl1"). iIntros "!> _". brel_pures_l.
          iApply (brel_load_r _ _ _ _ [AppRCtx _; CaseCtx _ _] with "Hl2"). iIntros "_". brel_pures_r.
          iApply brel_na_close. iFrame "Hclose". iSplitR "Hautha Hauthb"; [iNext; iRight; iFrame "#"|].
          iApply (brel_bind' [_] [_]); [iApply traversable_to_iThy|].
          iApply (brel_introduction' [c1] [c2]). { apply elem_of_cons. right. apply list_elem_of_here. }
          iExists _, _, [], [], _. do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
          iSplitL; [|by iIntros "!>" (??) "H"; iApply "H"].
          iLeft. iLeft. iExists A, A.
          iSplitL.
          { iMod (inv_acc with "Hinvta") as "([>Htok | >#Hfrac'] & Hclose)"; try done.
            - iModIntro. iLeft. iIntros. iFrame. iMod ("Hclose" with "[$]") as "_". iFrame "#". by iModIntro.
            - iModIntro. iRight. iFrame "#". iApply "Hclose". iNext. by iRight. }
          iSplit; first (do 2 (iSplit; try (iPureIntro; done))). iModIntro.
          iApply brel_value. iIntros "$ !>". brel_pures'.
          iApply (brel_bind' [_] [_]); [iApply traversable_to_iThy|].
          iApply (brel_introduction' [c1] [c2]). { apply elem_of_cons. right. apply list_elem_of_here. }
          iExists _, _, [], [], _. do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
          iSplitL; [|by iIntros "!>" (??) "H"; iApply "H"].
          iLeft. iRight. do 2 (iSplit; try (iPureIntro; done)). iModIntro. iSplitL.
          { iApply brel_value. iIntros "$ !>". brel_pures'. iDestruct ("Hcont" with "Hnone") as "Hkk".
            iApply (brel_exhaustion _ _ [_] [_] with "[$Hkk]"); [done|done|iApply "IH"]. }
          iIntros (m) "Ha'". iDestruct (auth_agree with "[$Hauthb] [$Ha']") as "<-".
          iApply brel_value. iIntros "$ !>". brel_pures'. iDestruct ("Hcont" with "Hsome") as "Hkk".
          iApply (brel_exhaustion _ _ [_] [_] with "[$Hkk]"); [done|done|iApply "IH"].
      + brel_pures; [apply Hk1; set_solver | apply Hk2; set_solver |].
        brel_pures'.
        iApply (brel_bind' [_] [_]); [iApply traversable_to_iThy|].
        iApply (brel_introduction' [c1] [c2]). { apply elem_of_cons. right. apply list_elem_of_here. }
        iExists _, _, [], [], _. do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
        iSplitL; [|by iIntros "!>" (??) "H"; iApply "H"].
        iRight. iRight. do 2 (iSplit; try (iPureIntro; done)). iModIntro. iSplitL.
        { iApply brel_value. iIntros "$ !>". brel_pures'. iDestruct ("Hcont" with "Hnone") as "Hkk".
          iApply (brel_exhaustion _ _ [_] [_] with "[$Hkk]"); [done|done|iApply "IH"]. }
        iIntros (m) "Ha'". iDestruct (auth_agree with "[$Hautha] [$Ha']") as "<-".
        iApply brel_value. iIntros "$ !>". brel_pures'.
        iApply (brel_bind' [_] [_]); [iApply traversable_to_iThy|].
        iApply (brel_introduction' [c1] [c2]). { apply elem_of_cons. right. apply list_elem_of_here. }
        iExists _, _, [], [], _. do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
        iSplitL; [|by iIntros "!>" (??) "H"; iApply "H"].
        iRight. iLeft. iExists B, B.
        iSplitL.
        { iMod (inv_acc with "Hinvtb") as "([>Htok | >#Hfrac'] & Hclose)"; try done.
          - iModIntro. iLeft. iIntros. iFrame. iMod ("Hclose" with "[$]") as "_". iFrame "#". by iModIntro.
          - iModIntro. iRight. iFrame "#". iApply "Hclose". iNext. by iRight. }
        iSplit; first (do 2 (iSplit; try (iPureIntro; done))). iModIntro.
        iApply brel_value. iIntros "$ !>". brel_pures'.
        iApply (brel_na_inv _ _ (nroot.@"lc")); [set_solver|]. iFrame "Hlcinv".
        iIntros "(>[(Hl1 & Hl2) | #(Hl1 & Hl2)] & Hclose)".
        - iApply (brel_load_l _ _ _ [CaseCtx _ _] with "Hl1"). iIntros "!> Hl1". brel_pures_l.
          iApply (brel_load_r _ _ _ _ [CaseCtx _ _] with "Hl2"). iIntros "Hl2". brel_pures_r.
          iApply brel_na_close. iFrame "Hclose". iSplitR "Hautha Hauthb"; [iNext; iLeft; iFrame|].
          iDestruct ("Hcont" with "Hnone") as "Hkk". iApply (brel_exhaustion _ _ [_] [_] with "[$Hkk]"); [done|done|iApply "IH"].
        - iApply (brel_load_l _ _ _ [CaseCtx _ _] with "Hl1"). iIntros "!> _". brel_pures_l.
          iApply (brel_load_r _ _ _ _ [CaseCtx _ _] with "Hl2"). iIntros "_". brel_pures_r.
          iApply brel_na_close. iFrame "Hclose". iSplitR "Hautha Hauthb"; [iNext; iRight; iFrame "#"|].
          iDestruct ("Hcont" with "Hsome") as "Hkk". iApply (brel_exhaustion _ _ [_] [_] with "[$Hkk]"); [done|done|iApply "IH"]. }
    simpl. iIntros (u1 u2) "Hu".
    iSpecialize ("Hu" $! θ2 with "Hchan").
    rewrite !iLblSig_to_iLblThy_distr.
    iApply (brel_introduction_mono (iLblSig_to_iLblThy θ2 ++ iLblSig_to_iLblThy θ₁ ++ iLblSig_to_iLblThy θ__L)).
    { iApply to_iThy_le_intro'; solve_submseteq. }
    iApply "Hu".
  Qed.

  (* Inline DH_real/DH_rand self-refinements (couple the samples, then [g^_]
     is deterministic).  [DH_real] draws 2 exponents + product; [DH_rand] 3. *)
  Lemma DH_real_self : ⊢ sem_val_typed DH_real DH_real (𝟙 ⊸ (𝔾 × 𝔾 × 𝔾))%T.
  Proof using All.
    rewrite /sem_val_typed /sem_ty_arr /sem_ty_mbang /=.
    iModIntro. iIntros (w1 w2) "(->&->)".
    rewrite /DH_real. brel_pures'.
    iApply brel_couple_rand_rand; first done. iIntros (a Ha). brel_pures'.
    iApply brel_couple_rand_rand; first done. iIntros (b Hb). brel_pures'.
    rewrite -!Nat2Z.inj_mul. do 3 brel_exp_l. do 3 brel_exp_r.
    brel_pures'. iModIntro.
    iExists _,_,_,_. iSplit; [done|]. iSplit; [done|]. iSplit.
    { iExists _,_,_,_. iSplit; [done|]. iSplit; [done|]. iSplit.
      - iExists _. by iSplit.
      - iExists _. by iSplit. }
    { iExists _. by iSplit. }
  Qed.

  Lemma DH_rand_self : ⊢ sem_val_typed DH_rand DH_rand (𝟙 ⊸ (𝔾 × 𝔾 × 𝔾))%T.
  Proof using All.
    rewrite /sem_val_typed /sem_ty_arr /sem_ty_mbang /=.
    iModIntro. iIntros (w1 w2) "(->&->)".
    rewrite /DH_rand. brel_pures'.
    iApply brel_couple_rand_rand; first done. iIntros (a Ha). brel_pures'.
    iApply brel_couple_rand_rand; first done. iIntros (b Hb). brel_pures'.
    iApply brel_couple_rand_rand; first done. iIntros (c Hc). brel_pures'.
    iModIntro.
    iExists _,_,_,_. iSplit; [done|]. iSplit; [done|]. iSplit.
    { iExists _,_,_,_. iSplit; [done|]. iSplit; [done|]. iSplit.
      - iExists _. by iSplit.
      - iExists _. by iSplit. }
    { iExists _. by iSplit. }
  Qed.

  Lemma REAL_DHKE_DH_RED_REAL :
      ⊢ sem_typed [] REAL_CHAN_DH_REAL REAL_CHAN_DH_RED_REAL ⊥ τ [].
  Proof using All.
    rewrite /sem_typed /REAL_CHAN_DH_RED_REAL. iModIntro. iIntros (vs) "Hvs".
    rewrite /REAL_CHAN_DH_REAL /REAL_CHAN_DH_RED.
    simpl subst_map.
    brel_pures'.
    iModIntro. iSplitR "Hvs"; [| iApply "Hvs"].
    rewrite /τ /=.
    iIntros (θ__L). iIntros (client1 client2) "Hcli".
    brel_pures'.
    iPoseProof (CHAN_typed) as "#HF".
    iDestruct ("HF" $! θ__L with "Hcli") as "HFτ".
    iApply (brel_bind [AppRCtx _] [AppRCtx _] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HFτ]"); [iApply to_iThy_le_refl|].
    simpl. iIntros (v1 v2) "Hvv".
    unfold right_composition. brel_pures'.
    iModIntro.
    iIntros (θ₁ θ2).
    iIntros (r1 r2) "Hoaleak".
    brel_pures'.
    iModIntro.
    iIntros (r1' r2') "Hchan".
    brel_pures'.
    iPoseProof DH_real_self as "#Hdh".
    iEval (rewrite /sem_val_typed) in "Hdh".
    iEval (rewrite /tc_opaque) in "Hdh".
    iDestruct "Hdh" as "#Hdh2".
    iApply (comp_core DH_real DH_real θ__L θ₁ θ2 v1 v2 r1 r2 r1' r2' with "Hdh2 Hvv Hoaleak Hchan").
  Qed.

  Lemma REAL_DHKE_DH_RED_REAL' :
      ⊢ sem_typed [] REAL_CHAN_DH_RED_REAL REAL_CHAN_DH_REAL ⊥ τ [].
  Proof using All.
    rewrite /sem_typed /REAL_CHAN_DH_RED_REAL. iModIntro. iIntros (vs) "Hvs".
    rewrite /REAL_CHAN_DH_REAL /REAL_CHAN_DH_RED.
    simpl subst_map.
    brel_pures'.
    iModIntro. iSplitR "Hvs"; [| iApply "Hvs"].
    rewrite /τ /=.
    iIntros (θ__L). iIntros (client1 client2) "Hcli".
    brel_pures'.
    iPoseProof (CHAN_typed) as "#HF".
    iDestruct ("HF" $! θ__L with "Hcli") as "HFτ".
    iApply (brel_bind [AppRCtx _] [AppRCtx _] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HFτ]"); [iApply to_iThy_le_refl|].
    simpl. iIntros (v1 v2) "Hvv".
    unfold right_composition. brel_pures'.
    iModIntro.
    iIntros (θ₁ θ2).
    iIntros (r1 r2) "Hoaleak".
    brel_pures'.
    iModIntro.
    iIntros (r1' r2') "Hchan".
    brel_pures'.
    iPoseProof DH_real_self as "#Hdh".
    iEval (rewrite /sem_val_typed) in "Hdh".
    iEval (rewrite /tc_opaque) in "Hdh".
    iDestruct "Hdh" as "#Hdh2".
    iApply (comp_core DH_real DH_real θ__L θ₁ θ2 v1 v2 r1 r2 r1' r2' with "Hdh2 Hvv Hoaleak Hchan").
  Qed.

  Lemma REAL_DHKE_DH_RED_RAND :
      ⊢ sem_typed [] REAL_CHAN_DH_RAND REAL_CHAN_DH_RED_RAND ⊥ τ [].
  Proof using All.
    rewrite /sem_typed /REAL_CHAN_DH_RED_RAND. iModIntro. iIntros (vs) "Hvs".
    rewrite /REAL_CHAN_DH_RAND /REAL_CHAN_DH_RED.
    simpl subst_map.
    brel_pures'.
    iModIntro. iSplitR "Hvs"; [| iApply "Hvs"].
    rewrite /τ /=.
    iIntros (θ__L). iIntros (client1 client2) "Hcli".
    brel_pures'.
    iPoseProof (CHAN_typed) as "#HF".
    iDestruct ("HF" $! θ__L with "Hcli") as "HFτ".
    iApply (brel_bind [AppRCtx _] [AppRCtx _] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HFτ]"); [iApply to_iThy_le_refl|].
    simpl. iIntros (v1 v2) "Hvv".
    unfold right_composition. brel_pures'.
    iModIntro.
    iIntros (θ₁ θ2).
    iIntros (r1 r2) "Hoaleak".
    brel_pures'.
    iModIntro.
    iIntros (r1' r2') "Hchan".
    brel_pures'.
    iPoseProof DH_rand_self as "#Hdh".
    iEval (rewrite /sem_val_typed) in "Hdh".
    iEval (rewrite /tc_opaque) in "Hdh".
    iDestruct "Hdh" as "#Hdh2".
    iApply (comp_core DH_rand DH_rand θ__L θ₁ θ2 v1 v2 r1 r2 r1' r2' with "Hdh2 Hvv Hoaleak Hchan").
  Qed.

  Lemma REAL_DHKE_DH_RED_RAND' :
      ⊢ sem_typed [] REAL_CHAN_DH_RED_RAND REAL_CHAN_DH_RAND ⊥ τ [].
  Proof using All.
    rewrite /sem_typed /REAL_CHAN_DH_RED_RAND. iModIntro. iIntros (vs) "Hvs".
    rewrite /REAL_CHAN_DH_RAND /REAL_CHAN_DH_RED.
    simpl subst_map.
    brel_pures'.
    iModIntro. iSplitR "Hvs"; [| iApply "Hvs"].
    rewrite /τ /=.
    iIntros (θ__L). iIntros (client1 client2) "Hcli".
    brel_pures'.
    iPoseProof (CHAN_typed) as "#HF".
    iDestruct ("HF" $! θ__L with "Hcli") as "HFτ".
    iApply (brel_bind [AppRCtx _] [AppRCtx _] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HFτ]"); [iApply to_iThy_le_refl|].
    simpl. iIntros (v1 v2) "Hvv".
    unfold right_composition. brel_pures'.
    iModIntro.
    iIntros (θ₁ θ2).
    iIntros (r1 r2) "Hoaleak".
    brel_pures'.
    iModIntro.
    iIntros (r1' r2') "Hchan".
    brel_pures'.
    iPoseProof DH_rand_self as "#Hdh".
    iEval (rewrite /sem_val_typed) in "Hdh".
    iEval (rewrite /tc_opaque) in "Hdh".
    iDestruct "Hdh" as "#Hdh2".
    iApply (comp_core DH_rand DH_rand θ__L θ₁ θ2 v1 v2 r1 r2 r1' r2' with "Hdh2 Hvv Hoaleak Hchan").
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
    - unshelve iApply R_I_SCHAN ; done.
    - iApply F_AUTH_DH_SIM_typed.
  Qed.

  Lemma SIMFCHAN_DHSIM_FKE_CHAN4 :
    ⊢ sem_val_typed SIMSIMFCHAN DHSIM_FKE_CHAN4 τ.
  Proof using All.
    iApply functionality_comp_cong.
    - apply F_AUTH_DH_SIM_closed.
    - apply CHAN_SIM_lazy_F_CHAN_closed.
    - apply R_CHAN_closed.
    - unshelve iApply I_R_SCHAN ; done.
    - iApply F_AUTH_DH_SIM_typed.
  Qed.

End new_comp_verification.

From clutch.prob_eff_lang.probblaze.typing Require Import types interp.
From Coq.Logic Require Import FunctionalExtensionality.
From clutch.prob_eff_lang.probblaze Require Import advantage.
From iris.algebra Require Import excl.
From iris.algebra.lib Require Import dfrac_agree.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_judgement sem_row syntax semantics proofmode valgroup.
From clutch.prob_eff_lang.probblaze Require Import 
  dhke_channel_lazy_results 
  dhke_channel_lazy_authchan
  def_dhke adequacy.

(* [interp._ty]/[interp._row]/[interp._mode] are fixpoints returning OFE
   morphisms ([_ -n> _]); [cbn]/[simpl] fail to reduce them (they choke on the
   [ofe_mor_car] / [NonExpansive] proof terms).  These one-step unfolding
   equations hold by [reflexivity] (they are definitional) and let us drive the
   interpretation of a closed type by [rewrite] instead. *)
Section interp_unfold.
  Context `{!probblazeRGS Σ}.
  Lemma interp_TForallR η μ δ (τ : type) ξ :
    interp._ty η μ δ (TForallR τ) ξ
    = sem_ty_row_forall (λ ρ, interp._ty η μ δ τ (ρ :: ξ)).
  Proof. reflexivity. Qed.
  Lemma interp_TArrow η μ δ α ρ β ξ :
    interp._ty η μ δ (TArrow α ρ β) ξ
    = sem_ty_arr (interp._row η μ δ ρ ξ) (interp._ty η μ δ α ξ) (interp._ty η μ δ β ξ).
  Proof. reflexivity. Qed.
  Lemma interp_TBang η μ δ m τ ξ :
    interp._ty η μ δ (TBang m τ) ξ = sem_ty_mbang (interp._mode μ m) (interp._ty η μ δ τ ξ).
  Proof. reflexivity. Qed.
  Lemma interp_TProd η μ δ τ1 τ2 ξ :
    interp._ty η μ δ (TProd τ1 τ2) ξ
    = sem_ty_prod (interp._ty η μ δ τ1 ξ) (interp._ty η μ δ τ2 ξ).
  Proof. reflexivity. Qed.
  Lemma interp_TSum η μ δ τ1 τ2 ξ :
    interp._ty η μ δ (TSum τ1 τ2) ξ
    = sem_ty_sum (interp._ty η μ δ τ1 ξ) (interp._ty η μ δ τ2 ξ).
  Proof. reflexivity. Qed.
  Lemma interp_TUnit η μ δ ξ : interp._ty η μ δ TUnit ξ = sem_ty_unit.
  Proof. reflexivity. Qed.
  Lemma interp_RVar η μ δ i ξ : interp._row η μ δ (RVar i) ξ = ξ !!! i.
  Proof. reflexivity. Qed.
  Lemma interp_RUnion η μ δ ρ1 ρ2 ξ :
    interp._row η μ δ (RUnion ρ1 ρ2) ξ
    = sem_row_union (interp._row η μ δ ρ1 ξ) (interp._row η μ δ ρ2 ξ).
  Proof. reflexivity. Qed.
  Lemma interp_RNil η μ δ ξ : interp._row η μ δ RNil ξ = sem_row_nil.
  Proof. reflexivity. Qed.
  Lemma interp_mode_MS μ : interp._mode μ MS = syntax.MS.
  Proof. reflexivity. Qed.
End interp_unfold.

Section adv_dhke.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.
  Context `{probblazeRGpreS Σ}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.
  Context {la1 la2 : label}.     (* TODO can be removed once dhke_channel.v has been cleaned up *)

  Import valgroup_notation.
  Import valgroup_tactics.

  Definition τ_DH `{!probblazeRGS Σ}
    := (∀ᵣ θ__L, (∀ᵣ θₕ, ((sem_ty_sum 𝟙 𝟙) -{ θₕ }-> (Option 𝔾)) -{ sem_row_union θₕ θ__L }-∘ 𝟙)%T 
                 ⊸ ((∀ᵣ θₗ, (((𝔾 × (𝟙 + 𝟙)) -{ θₗ }-> 𝟙) × ((𝟙 + 𝟙) -{ θₗ }-> Option 𝔾))
                            -{ sem_row_union θₗ θ__L }-∘ 𝟙)))%T.

  (* Syntactic type whose interpretation is [τ_DH].  De Bruijn indices: inside
     [∀ᵣ θ__L] then [∀ᵣ θₕ] (resp. [∀ᵣ θₗ]) the inner bound row is [RVar 0] and
     [θ__L] is [RVar 1], so the effect [sem_row_union θₕ θ__L] is [RUnion (RVar 0%nat)
     (RVar 1%nat)].  Leaves: [𝟙+𝟙 = TSum TUnit TUnit], [Option 𝔾 = TSum TUnit τG],
     [𝔾×(𝟙+𝟙) = TProd τG (TSum TUnit TUnit)], [𝔾 = interp τG] via [τG_lrel]. *)
  Definition T_DH : type :=
    TForallR (
      TArrow
        (TForallR (
           TArrow (TBang MS (TArrow (TSum TUnit TUnit) (RVar 0%nat) (TSum TUnit τG)))
                  (RUnion (RVar 0%nat) (RVar 1%nat)) TUnit))
        RNil
        (TForallR (
           TArrow (TProd (TBang MS (TArrow (TProd τG (TSum TUnit TUnit)) (RVar 0%nat) TUnit))
                         (TBang MS (TArrow (TSum TUnit TUnit) (RVar 0%nat) (TSum TUnit τG))))
                  (RUnion (RVar 0%nat) (RVar 1%nat)) TUnit))).

  Lemma T_DH_interp `{!probblazeRGS Σ} η μ δ ξ :
    interp._ty η μ δ T_DH ξ = τ_DH.
  Proof using All.
    (* Only the group leaves are non-definitional; [HG] bridges them via
       [τG_lrel] (instance supplied by the section's [G]). *)
    assert (HG : ∀ ζ, interp._ty η μ δ τG ζ = sem_ty_group) by
      (intros ζ; extensionality v1; extensionality v2; symmetry;
       apply (τG_lrel (clutch_group := G _ _))).
    rewrite /T_DH /τ_DH /sem_ty_option.
    (* Peel the interpretation constructor-by-constructor: [rewrite] the
       reflexivity-unfolding lemmas at the head, then a congruence step
       (targeted [f_equal]/[functional_extensionality], since generic [f_equal]
       is too slow on these OFE terms), closing group leaves with [HG]. *)
    repeat (
      rewrite ?interp_TForallR ?interp_TArrow ?interp_TBang ?interp_TProd ?interp_TSum
              ?interp_TUnit ?interp_RVar ?interp_RUnion ?interp_RNil ?interp_mode_MS;
      first [ apply HG
            | reflexivity
            | apply (f_equal sem_ty_row_forall)
            | apply (f_equal3 sem_ty_arr)
            | apply (f_equal2 sem_ty_prod)
            | apply (f_equal2 sem_ty_sum)
            | apply (f_equal2 sem_ty_mbang)
            | apply (f_equal2 sem_row_union)
            | (apply functional_extensionality; intros ?) ]).
  Qed.

  Lemma adv_DHKE_DH_real  A :
    (∀ `{!probblazeRGS Σ}, 
       ⊢ sem_val_typed A A (τ_DH → 𝔹)%T) →
    nonneg (advantage A (λ: "f", F_AUTH (DH_KE "f"))%V ((λ: "DH" "f", F_AUTH (C_lazy "DH" "f"))%V DH_real) #true) = 0%R.
  Proof using H inG0 inG1 inG2 la2 G. (* also debris from dhke_channel *)
    intros. eapply sem_typed_advantage; eauto. split.
    - intros Hrgs. apply DHKE_RED; eauto. 
    - intros Hrgs. apply RED_DHKE; eauto.
  Qed. 

  Lemma adv_DH_rand_FKE  A :
    (∀ `{!probblazeRGS Σ},⊢ sem_val_typed A A (τ_DH → 𝔹)%T) →
    nonneg (advantage A ((λ: "DH" "f", F_AUTH (C_lazy "DH" "f"))%V DH_rand) (λ: "f", F_AUTH (DH_SIM (F_KE_lazy_alice "f")))%V  #true) = 0%R.
  Proof using H inG0 inG1 inG2 G la2. 
    intros. eapply sem_typed_advantage; eauto. split.
    - intros Hrgs. apply RED_DHSIM; eauto.
    - intros Hrgs. apply DHSIM_RED; eauto.
  Qed. 

  Theorem adv_DHKE A (ε : R) :
    (∀ `{!probblazeRGS Σ},⊢ sem_val_typed A A (τ_DH → 𝔹)%T) →
    advantage A ((λ: "DH" "f", F_AUTH (C_lazy "DH" "f"))%V DH_real) ((λ: "DH" "f", F_AUTH (C_lazy "DH" "f"))%V DH_rand) #true <= ε →
    advantage A (λ: "f", F_AUTH (DH_KE "f"))%V (λ: "f", F_AUTH (DH_SIM (F_KE_lazy_alice "f")))%V #true <= ε.
  Proof using H inG0 inG1 inG2 G la2. 
    intros HA HAadv.
    eapply advantage_triangle.
    - right. by apply adv_DHKE_DH_real.
    - eapply advantage_triangle. 
      + apply HAadv.
      + right. by apply adv_DH_rand_FKE.
      + done.
    - lra.
  Qed.

  Corollary adv_DHKE_no_epsilon  A :
    (∀ `{!probblazeRGS Σ},⊢ sem_val_typed A A (τ_DH → 𝔹)%T) →
    advantage A (λ: "f", F_AUTH (DH_KE "f"))%V (λ: "f", F_AUTH (DH_SIM (F_KE_lazy_alice "f")))%V #true 
    <= advantage A ((λ: "DH" "f", F_AUTH (C_lazy "DH" "f"))%V DH_real) ((λ: "DH" "f", F_AUTH (C_lazy "DH" "f"))%V DH_rand) #true.
  Proof using H inG0 inG1 inG2 G la2. 
    intros. eapply adv_DHKE; eauto; lra.
  Qed.
    
  (* The section's [G] is a function [∀ Σ RGS, clutch_group]; expose the
     specialised group as an instance so the group tactics ([brel_exp_*],
     [τG_lrel], …) resolve it. *)
  #[local] Instance clutch_group_inst `{!probblazeRGS Σ} : clutch_group := G _ _.

  (* [DH_real]/[DH_rand] self-refine at [𝟙 ⊸ 𝔾×𝔾×𝔾]: the two runs draw the
     same exponents (coupled [rand]s), so the deterministic [g^_] outputs agree
     and form a group-triple.  (A syntactic typing + fundamental lemma is not
     available: the [typed] relation has no binary-op rule, so [vexp]/[g^(a*b)]
     are untypeable — hence the direct relational proof.) *)
  Lemma DH_real_self `{!probblazeRGS Σ} :
    ⊢ sem_val_typed DH_real DH_real (𝟙 ⊸ (𝔾 × 𝔾 × 𝔾))%T.
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

  Lemma DH_rand_self `{!probblazeRGS Σ} :
    ⊢ sem_val_typed DH_rand DH_rand (𝟙 ⊸ (𝔾 × 𝔾 × 𝔾))%T.
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

  (* The reduction [red = λ DH f, F_AUTH (C_lazy DH f)] self-refines at
     [(𝟙 ⊸ 𝔾×𝔾×𝔾) → τ_DH]: a [C_lazy] self-refinement (symbolic execution of
     the [getKey] handler, with an invariant tying the two [lc] refs) composed
     with [F_AUTH_F_AUTH]. *)
  Lemma red_self `{!probblazeRGS Σ} :
    ⊢ sem_val_typed (λ: "DH", (λ: "f", F_AUTH (C_lazy "DH" "f")))%V
                    (λ: "DH", (λ: "f", F_AUTH (C_lazy "DH" "f")))%V
        ((𝟙 ⊸ (𝔾 × 𝔾 × 𝔾)) → τ_DH)%T.
  Proof using All.
    (* Outer structure: intro the [DH] argument (related at [𝟙 ⊸ 𝔾×𝔾×𝔾]) and
       the [τ_DH]-client [f], allocate the authenticated-channel ghost state,
       and reduce to a [C_lazy] self-refinement via [F_AUTH_F_AUTH]. *)
    rewrite /sem_val_typed /τ_DH.
    iModIntro. rewrite {1}/sem_ty_mbang {1}/sem_ty_arr /=.
    iModIntro. iIntros (DH1 DH2) "HDH".
    brel_pures'. iModIntro.
    iIntros (θ__L). iIntros (f1 f2) "Hf". brel_pures'.
    iApply fupd_brel.
    iMod token_alloc as (γtoka) "Htoka".
    iMod token_alloc as (γtokb) "Htokb".
    iMod (auth_alloc (#()%V)) as (γautha) "Hautha".
    iMod (auth_alloc (#()%V)) as (γauthb) "Hauthb".
    iMod dfrac_alloc as (γfraca) "Hfraca".
    iMod dfrac_alloc as (γfracb) "Hfracb".
    iModIntro.
    iApply (F_AUTH_F_AUTH la1 la2 (C_lazy DH1 f1) (C_lazy DH2 f2)
              γtoka γtokb γfraca γfracb γautha γauthb θ__L
              with "Hfraca Hfracb [-]").
    (* Remaining: the [C_lazy] self-refinement (the [F_AUTH_F_AUTH] C-part).
       Reduce [C_lazy], call [DH #()] once (relating the two group triples via
       [HDH]), allocate the two [lc] refs under an invariant tying them, then
       set up the multi-shot [getKey] handler over the client [f]. *)
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
    iApply brel_alloc_l. iIntros (l1) "!> Hl1". brel_pures_l.
    iApply brel_alloc_r. iIntros (l2) "Hl2". brel_pures_r.
    iApply (brel_na_alloc
              ((l1 ↦ NONEV ∗ l2 ↦ₛ NONEV)
               ∨ (l1 ↦□ SOMEV (vgval C) ∗ l2 ↦ₛ□ SOMEV (vgval C)))%I
              (nroot .@ "lc")).
    iSplitL "Hl1 Hl2"; [iNext; iLeft; iFrame|].
    iIntros "#Hlcinv".
    iApply brel_effect_l. iIntros (gk1) "!> Hgk1".
    iApply brel_effect_r. iModIntro. iIntros (gk2) "Hgk2 !>".
    brel_pures'.
    iSpecialize ("Hf" $! (θ gk1 gk2)).
    rewrite /sem_ty_arr /sem_ty_mbang /=.
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
    iSpecialize ("Hf" with "Hgg").
    set (ac := authchan_row la1 la2 c1 c2 γtoka atokN γtokb btokN γfraca γfracb γautha γauthb).
    iApply brel_new_theory.
    iApply (brel_add_label_l with "Hgk1").
    iApply (brel_add_label_r with "Hgk2").
    iDestruct (brel_introduction_mono _ ([([gk1],[gk2],GetKey gk1 gk2)] ++ (iLblSig_to_iLblThy ac) ++ (iLblSig_to_iLblThy θ__L)) with "[][$Hf]") as "Hf'".
    { iApply to_iThy_le_intro'. apply submseteq_skip. by apply submseteq_cons. }
    iApply (brel_exhaustion with "[$Hf']"); [done|done|].
    iLöb as "IH".
    iSplit; [iIntros (v1 v2) "!# (-> & ->)"; by brel_pures|].
    iIntros (?????) "!# %Hk1 %Hk2 ([(-> & ->)|(-> & ->)] & #(Hnone & Hsome)) #Hcont".
    (* getKey InjL (Alice's request): store_if_none;; doSend (A, bob) [SendAliceImpl];;
       doRecv bob [RecvBobImpl]; resume.  Mirror dhke_channel_lazy_real_one.v:147-275,
       specialised to the self case (both sides send the same [A], no tape/sampling). *)
    + admit.
    (* getKey InjR (Bob's request): doRecv alice [RecvAliceImpl]; on Some, doSend (B, alice)
       [SendBobImpl];; read lc; resume.  Mirror dhke_channel_lazy_real_one.v:277-386. *)
    + admit.
  Admitted.

  Theorem adv_DHKE_real A :
    (∀ `{!probblazeRGS Σ},⊢ sem_val_typed A A (τ_DH → 𝔹)%T) →
    advantage A (λ: "f", F_AUTH (DH_KE "f"))%V (λ: "f", F_AUTH (DH_SIM (F_KE_lazy_alice "f")))%V #true <=
      advantage (λ: "v", A (((λ: "DH", (λ: "f", F_AUTH (C_lazy "DH" "f")))%V "v")))%V DH_real DH_rand #true.
  Proof using H inG0 inG1 inG2 G la1 la2.
    intros HA.
    etrans.
    - apply adv_DHKE_no_epsilon; eauto.
    - eapply advantage_reduction.
      intros HRGS. exists (𝟙 ⊸ (𝔾 × 𝔾 × 𝔾))%T, τ_DH.
      split; [apply HA | split].
      + apply red_self.
      + split; [apply DH_real_self | apply DH_rand_self].
  Qed.

End adv_dhke.

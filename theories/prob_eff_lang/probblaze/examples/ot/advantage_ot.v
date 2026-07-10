From clutch.prob_eff_lang.probblaze Require Import advantage.
From iris.algebra Require Import excl.
From iris.algebra.lib Require Import dfrac_agree.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_judgement sem_row syntax semantics proofmode valgroup.
From clutch.prob_eff_lang.probblaze Require Import OT_Rcorrupt_thunk definition_thunk_receiver_corrupt adequacy.
Import fingroup.

Section adv_rc.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.
  Context `{probblazeRGpreS Σ}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.
  #[local] Notation n := (S (S n'')).
  Context `{n_prime : is_true (prime.prime n)}.

  Import valgroup_notation.

  Definition τ_rc `{probblazeRGS Σ} := (∀ᵣ θ, τC θ ⊸ ((((𝔾 × 𝔾) × (𝔾 × 𝔾)) -{ θ }-> 𝟙) × (𝟙 -{ θ }-> Option (𝔾 × 𝔾)))
            -{ ¡[OS] θ}-∘ 𝟙)%T.


  Theorem adv_ot_rc A (ε : R) :
    (∀ `{!probblazeRGS Σ},⊢ sem_val_typed A A (τ_rc → 𝔹)%T) →
    advantage A OT_SIM_FOT_thunk (λ: "f" "effs", F_CRS (λ: "doCRS", OT_Real_Receiver_Corrupted "f" ("effs", "doCRS"))%E)%V #true <= 3/n.
  Proof using n_prime G inG2 H.
    intros. eapply sem_typed_advantage_aff; try done; last split.
    - apply Rcomplements.Rdiv_le_0_compat; first lra.
      apply lt_0_INR. lia.
    - intros Hrgs. by unshelve iApply OT_ideal_real.
    - intros Hrgs. by unshelve iApply OT_real_ideal.
  Qed.

End adv_rc.

From clutch.prob_eff_lang.probblaze Require Import OT_SCorrupt_thunk definition_thunk_sender_corrupt.

Section adv_sc_typing.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.
  Context `{probblazeRGpreS Σ}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.
  #[local] Notation n := (S (S n'')).
  Context `{n_prime : is_true (prime.prime n)}.

  Import valgroup_notation.
  Import valgroup_tactics.

  (* reduction applied to related DH samplers is self-related: the sampled
     DH tuple is stored in a ghost variable and handed out as the CRS by
     the "CRS" handler on both sides. This is the self-related analogue of
     fcrs_dh_ideal and dh_ideal_fcrs. *)
  Lemma reduction_self `{!probblazeRGS Σ} γcrs (DH1 DH2 : val) :
    own γcrs (to_dfrac_agree (DfracOwn 1) #()%V) -∗
    (𝟙 ⊸ (𝔾 × 𝔾 × 𝔾 × 𝔾))%T DH1 DH2 -∗
    BREL (reduction DH1) ≤ (reduction DH2) <|⊥|> {{ λ v1 v2, (∀ᵣ θ__L, (∀ᵣ θ__CRS, ((𝟙 -{ θ__CRS }-> (𝔾 × 𝔾 × 𝔾 × 𝔾))) -{ sem_row_union (¡ θ__CRS) θ__L}-∘ 𝟙) -{ θ__L }-∘ 𝟙)%T v1 v2}}.
  Proof.
    iIntros "Hcrs HDH".
    unfold reduction. brel_pures.
    iModIntro.
    iIntros (θL f1 f2) "Hff". brel_pures'.
    iApply (brel_bind [_] [_]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][HDH]"); first iApply to_iThy_le_refl.
    { by iApply "HDH". }
    simpl.
    iIntros (??) "HG".
    iDestruct "HG" as "(%&%&%&%&->&->&H1&H2)".
    iDestruct "H1" as "(%&%&%&%&->&->&H1'&H2')".
    iDestruct "H1'" as "(%&%&%&%&->&->&H1''&H2'')".
    iDestruct "H1''" as "(%ga&->&->)".
    iDestruct "H2''" as "(%gb&->&->)".
    iDestruct "H2'" as "(%gc&->&->)".
    iDestruct "H2" as "(%gd&->&->)".
    brel_pures'.
    iApply fupd_brel.
    iDestruct (auth_upd (vgval ga, vgval gb, vgval gc, vgval gd)%V with "Hcrs") as ">Hcrs".
    iDestruct (auth_persist with "Hcrs") as ">Hcrs".
    iDestruct "Hcrs" as "#Hcrs".
    iModIntro.
    iApply brel_effect_l. iIntros (CRSl) "!> Hcrsl !>".
    iApply brel_effect_r. iIntros (CRSr) "Hcrsr !>".
    brel_pures'.
    iApply brel_new_theory.
    iApply (brel_add_label_l with "Hcrsl").
    iApply (brel_add_label_r with "Hcrsr").
    unfold sem_val_typed. simpl.
    set (CRSrow := crsrow CRSl CRSr γcrs).
    iSpecialize ("Hff" $! CRSrow).
    unfold sem_ty_arr, sem_ty_mbang. simpl.
    iAssert (sem_val_typed (λ: <>, do: CRSl #()%V)%V (λ: <>, do: CRSr #()%V)%V (𝟙 -{ CRSrow }-> (𝔾 × 𝔾 × 𝔾 × 𝔾))%T) as "Hgg".
    { iModIntro. rewrite /sem_ty_arr /sem_ty_mbang //=.
      iIntros (??) "!# (->&->)". brel_pures'.
      iApply brel_introduction'; first constructor.
      iExists _,_,[],[],_;do 2 (iSplit; [by iPureIntro|]; iSplit; [iPureIntro; apply NeutralEctx_nil|]); iSplit; try (iIntros (??) "!# H"; iApply "H").
      do 2 (iSplit; [by iPureIntro|]). iIntros (crs) "Hcrs'". iDestruct (auth_agree with "[$][$]") as "->".
      iApply brel_value. iIntros "$ !>".
      do 3 (iExists _,_,_,_; do 2 (iSplit; [by iPureIntro|]);
      iSplit; last (iExists _; done)). iExists _; done. }
    unfold sem_val_typed. simpl. iDestruct "Hgg" as "#Hgg".
    iSpecialize ("Hff" with "Hgg").
    iApply (brel_exhaustion (f1 _) (f2 _) with "Hff"); [done|done|].
    iLöb as "IH".
    iSplit; [iIntros (??) "!# (->&->)"; by brel_pures|].
    iIntros (?????) "!# %Hk1' %Hk2 (%&(->&->&HQ)&HQ'Q) #HQkont".
    iApply brel_handle_os_l; [apply neutral_ectx;constructor|]. iIntros (ul) "!> Hul".
    iApply brel_handle_os_r; [apply neutral_ectx;constructor|]. iIntros (ur) "Hur".
    brel_pures.
    iApply (brel_cont_l with "[$]"). iModIntro.
    iApply (brel_cont_r with "[$]").
    iDestruct ("HQ" with "Hcrs") as "HQ".
    iDestruct ("HQ'Q" with "HQ") as "HQ".
    iDestruct ("HQkont" with "HQ") as "Hkont".
    iApply (brel_exhaustion _ _ [_] [_] with "Hkont"); [done|done|].
    iApply "IH".
  Qed.

  Lemma OT_REDUCTION_sem_typed `{!probblazeRGS Σ} :
    ⊢ ⊨ᵥ OT_REDUCTION ≤ OT_REDUCTION : ((𝟙 ⊸ (𝔾 × 𝔾 × 𝔾 × 𝔾)) → τ_sc).
  Proof using G cg inG2 n_prime vg vgg Σ.
    unfold OT_REDUCTION. unfold sem_ty_mbang. simpl.
    iIntros (DH1 DH2) "!# !# HDH".
    brel_pures'.
    iModIntro.
    iIntros (θ f1 f2) "HτC".
    brel_pures'.
    iModIntro.
    iIntros (??) "(%doSend1&%doSend2&%doRecv1&%doRecv2&->&->&#Hsend&#Hrecv)".
    brel_pures'.
    iApply (brel_bind' [AppLCtx _] [AppLCtx _]).
    { iApply traversable_to_iThy. }
    iApply brel_introduction_mono; [iApply to_iThy_le_bot|].
    iApply fupd_brel.
    iDestruct auth_alloc as ">(%γcrs&Hcrs)".
    iModIntro.
    assert (to_iThyIfMono OS [] = ⊥) as <-; first done.
    iApply (brel_mono OS with "[][Hcrs HDH]"); [iApply to_iThy_le_refl|iApply (reduction_self with "Hcrs HDH")|simpl].
    iIntros (g1 g2) "Hgg /=".
    iApply "Hgg".
    by unshelve iApply (OT_Real_Sender_corrupt_self with "Hsend Hrecv HτC").
  Qed.


  Lemma DH_rand_sem_typed `{!probblazeRGS Σ} :
    ⊢ ⊨ᵥ DH_rand ≤ DH_rand : (𝟙 ⊸ (𝔾 × 𝔾 × 𝔾 × 𝔾)).
  Proof using All.
    unfold DH_rand.
    iIntros (??) "!# (->&->)" .
    brel_pures'.
    iApply brel_couple_rand_rand; first done.
    iIntros (x) "%".
    brel_pures'.
    iApply brel_couple_rand_rand; first done.
    iIntros (a) "%".
    brel_pures'.
    iApply brel_couple_rand_rand; first done.
    iIntros (b) "%".
    brel_pures'.
    iApply brel_couple_rand_rand; first done.
    iIntros (c) "%".
    brel_pures'. iModIntro.
    iExists _,_,_,_.
    repeat iSplit; try done.
    1 : repeat (iExists _,_,_,_; repeat iSplit; try done).
    all : iExists _; iSplit; try done.
  Qed.

  Lemma DH_real_sem_typed `{!probblazeRGS Σ} :
    ⊢ ⊨ᵥ DH_real ≤ DH_real : (𝟙 ⊸ (𝔾 × 𝔾 × 𝔾 × 𝔾)).
  Proof using All.
    unfold DH_real.
    iIntros (??) "!# (->&->)" .
    brel_pures'.
    iApply brel_couple_rand_rand; first done.
    iIntros (x) "%".
    brel_pures'.
    iApply brel_couple_rand_rand; first done.
    iIntros (a) "%".
    brel_pures'.
    iApply brel_couple_rand_rand; first done.
    iIntros (b) "%".
    brel_pures'.
    rewrite -Nat2Z.inj_mul.
    brel_pures'. iModIntro.
    iExists _,_,_,_.
    repeat iSplit; try done.
    1 : repeat (iExists _,_,_,_; repeat iSplit; try done).
    all : iExists _; iSplit; try done.
  Qed.

End adv_sc_typing.

Section adv_sc.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.
  Context `{probblazeRGpreS Σ}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.
  #[local] Notation n := (S (S n'')).
  Context `{n_prime : is_true (prime.prime n)}.

  Import valgroup_notation.

  Theorem adv_ot_real A :
    (∀ `{!probblazeRGS Σ},⊢ sem_val_typed A A (τ_sc → 𝔹)%T) →
    advantage A
      (λ: "f" "effs", F_CRS (λ: "doCRS", OT_Real_Sender_corrupt "f" ("effs", "doCRS")))%V
      ((λ: "DH" "f" "effs", (reduction "DH") (λ: "doCRS", OT_Real_Sender_corrupt "f" ("effs", "doCRS")))%V DH_rand)
        #true <= 1/n.
  Proof using n_prime G inG2 H.
    intros Hadv. eapply brel_advantage; try done; last split.
    - apply Rcomplements.Rdiv_le_0_compat; first lra.
      apply lt_0_INR. lia.
    - apply Hadv.
    - intros Hrgs. by unshelve iApply OT_real_DH_real.
    - intros Hrgs. by unshelve iApply DH_real_OT_real.
  Qed.

  Theorem adv_ot_sim A :
    (∀ `{!probblazeRGS Σ},⊢ sem_val_typed A A (τ_sc → 𝔹)%T) →
    advantage A ((λ: "DH" "f" "effs", (reduction "DH") (λ: "doCRS", OT_Real_Sender_corrupt "f" ("effs", "doCRS")))%V DH_real) OT_SIM_FOT_thunk #true <= 1/n.
  Proof using n_prime G inG2 H.
    intros Hadv. eapply brel_advantage; try done; last split.
    - apply Rcomplements.Rdiv_le_0_compat; first lra.
      apply lt_0_INR. lia.
    - apply Hadv.
    - intros Hrgs. by unshelve iApply DH_OT_sim.
    - intros Hrgs. by unshelve iApply OT_sim_DH.
  Qed.

  Theorem adv_ot A :
    (∀ `{!probblazeRGS Σ},⊢ sem_val_typed A A (τ_sc → 𝔹)%T) →
    advantage A
      (λ: "f" "effs", F_CRS (λ: "doCRS", OT_Real_Sender_corrupt "f" ("effs", "doCRS")))%V
      OT_SIM_FOT_thunk #true
    <= advantage A
         ((λ: "DH" "f" "effs", (reduction "DH") (λ: "doCRS", OT_Real_Sender_corrupt "f" ("effs", "doCRS")))%V DH_rand)
         ((λ: "DH" "f" "effs", (reduction "DH") (λ: "doCRS", OT_Real_Sender_corrupt "f" ("effs", "doCRS")))%V DH_real) #true + 2/n.
  Proof using n_prime G inG2 H.
    intros. eapply advantage_triangle.
    - by eapply adv_ot_real.
    - eapply advantage_triangle.
      + apply Rle_refl.
      + by eapply adv_ot_sim.
      + apply Rle_refl.
    - rewrite Rplus_comm.
      rewrite Rplus_assoc.
      rewrite -Rdiv_plus_distr.
      assert (1 + 1 = 2) as -> by lra.
      apply Rle_refl.
  Qed.

  Theorem adv_ot_final A :
    (∀ `{!probblazeRGS Σ},⊢ sem_val_typed A A (τ_sc → 𝔹)%T) →
    advantage A
      (λ: "f" "effs", F_CRS (λ: "doCRS", OT_Real_Sender_corrupt "f" ("effs", "doCRS")))%V
      OT_SIM_FOT_thunk #true
    <= advantage (λ: "v", A (OT_REDUCTION "v"))%V
                            DH_rand
                            DH_real #true + 2/n.
  Proof using All.
    intros HA.
    etrans.
    - apply adv_ot; eauto.
    - apply Rplus_le_compat_r.
      eapply (advantage_reduction A OT_REDUCTION DH_rand DH_real true).
      intros HRGS. exists (𝟙 ⊸ (𝔾 × 𝔾 × 𝔾 × 𝔾))%T, τ_sc.
      split; [apply HA | split].
      + by unshelve eapply OT_REDUCTION_sem_typed.
      + by unshelve (split; [eapply DH_rand_sem_typed | eapply DH_real_sem_typed ]).
  Qed.

End adv_sc.

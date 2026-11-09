From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import excl.
From iris.algebra.lib Require Import dfrac_agree.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import primitive_laws proofmode
  spec_rules spec_ra class_instances.
From clutch.prob_eff_lang.probblaze Require Import dhke_common.
From clutch.prob_eff_lang.probblaze Require Import sem_types sem_row sem_sig sem_judgement.
From iris.bi Require Import monpred.
From iris.proofmode Require Import monpred.
From clutch.prob_eff_lang.probblaze.eq Require Import eq_logic eq_valgroup eq_handlers.
From clutch.prob_eff_lang.probblaze Require Import dhke_eq.

(** * The real world against the protocol with the real DDH oracle

    [DH_KE] ([l]) against [C_DH_real] ([r]), one client call, as an
    equivalence; the two refinements are its instances. *)

Section dhke_real.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.
  #[local] Notation n := (S n'').
  #[local] Open Scope bi_scope.
  Import valgroup_notation.
  Local Notation θ := (θ (Σ:=Σ) (vg:=vg)).

  (* Alice's message carries [DH_KE]'s location of her exponent. *)
  Definition P γauth (m : vgG) : iPropD Σ :=
    ∃ l : loc, ⎡message γauth (#l, #(g_log m))%V⎤ ∗ l ↦ₗ□ SOMEV #(g_log m).
  Definition P' γauth (m : vgG) : iPropD Σ := ⎡message γauth (vgval m)⎤.
  Definition chan_thy γautha γauthb := eq_chan_thy (P γautha) (P' γauthb).

  (* The channel's theory is part of the handler's. *)
  Local Ltac chan_sub :=
    intros d; simpl; apply list_subseteq_cons; do 2 apply list_subseteq_skip; apply list_subseteq_nil.

  Lemma DH_KE_C_DH_real_EQ γtoka γtokb γfraca γfracb γautha γauthb :
    ⊢ ⎡token γtoka⎤ -∗ ⎡token γtokb⎤ -∗ ⎡empty_message γautha⎤ -∗ ⎡empty_message γauthb⎤ -∗
      EQ (DH_KE #()%V) ≈ (C_DH_real #()%V) <|iLblSig_to_iLblThy (⊥ : sem_row Σ)|> {{ λ Dl Dr,
        □ ∀ (L : sem_row Σ) (fl fr : val),
          ⟪ ∀ᵣ θₕ, ((𝟙 + 𝟙) -{ θₕ }-> (Option 𝔾)) -{ sem_row_union (¡ θₕ) L }-∘ 𝟙 ⟫ fl fr -∗
          EQ Dl fl ≈ Dr fr <|iLblSig_to_iLblThy (⊥ : sem_row Σ)|> {{ λ vl vr,
            ∀ sl sr rl rr : label,
              EQ vl ((λ: "m", do: sl "m"), (λ: "m", do: rl "m"))%V
               ≈ vr ((λ: "m", do: sr "m"), (λ: "m", do: rr "m"))%V
                <|EqThy (λ d, chan_thy γautha γauthb γtoka γtokb γfraca γfracb sl sr rl rr d
                                ++ iLblSig_to_iLblThy L)|> {{ ⟪ 𝟙 ⟫ }} }} }}.
  Proof with (repeat foldkont; eq_pures') using G.
    iIntros "Htoka Htokb Ha Hb"...
    (* [DH_KE] presamples Alice's and Bob's exponents on tapes; [C_DH_real]
       samples them eagerly *)
    eq_alloctape_l α as "Hα"... eq_alloctape_l β as "Hβ"...
    eq_alloc_l la as "Hla"... eq_alloc_l lb as "Hlb".
    rewrite Nat2Z.id. unfold C_lazy_sess, DH_real. eq_pures_r.
    eq_couple_tape_rand "Hα". iIntros (a Ha) "Hα". eq_pures_r.
    eq_couple_tape_rand "Hβ". iIntros (b Hb) "Hβ"...
    rewrite -Nat2Z.inj_mul...
    eq_alloc_r lcs as "Hlcs"...
    iMod (store_message ((#la, #a)%V) with "Ha") as "#Ha".
    iMod (store_message (vgval (g ^+ b)%g) with "Hb") as "#Hb".
    (* the protocol can be called several times: its tokens go into invariants *)
    iMod (inv_alloc atokN _ (token γtoka ∨ receipt γfraca)%I with "[Htoka]") as "#Hinvta".
    { iNext; iLeft; iFrame. }
    iMod (inv_alloc btokN _ (token γtokb ∨ receipt γfracb)%I with "[Htokb]") as "#Hinvtb".
    { iNext; iLeft; iFrame. }
    iApply (eq_na_alloc ((β ↪ₗN (n; [b]) ∗ lb ↦ₗ NONEV) ∨ (β ↪ₗ□N (n; []) ∗ lb ↦ₗ□ SOMEV #b))%I betaN).
    iSplitL "Hβ Hlb"; [iNext; iLeft; iFrame|].
    iIntros "#Hinvb".
    iApply (eq_na_alloc ((α ↪ₗN (n; [a]) ∗ la ↦ₗ NONEV ∗ lcs ↦ᵣ NONEV)
                         ∨ (α ↪ₗ□N (n; []) ∗ la ↦ₗ□ SOMEV #a ∗ lcs ↦ᵣ□ SOMEV (vgval (g ^+ (a * b)))))%I
              alphaN).
    iSplitL "Hα Hla Hlcs"; [iNext; iLeft; iFrame|].
    iIntros "#Hinva".
    iApply eq_value. iModIntro. iIntros "!>" (L fl fr) "Hff"...
    iApply eq_value. iModIntro. iIntros (sl sr rl rr)...
    eq_effect_l gl as "Hgl". eq_effect_r gr as "Hgr"...
    (* the client's row: the key queries, with the labels of the program on
       the left *)
    set (θc := λ d, θ (pick d gl gr) (pick d gr gl)).
    iApply eq_new_theory.
    iApply eq_add_label_l. iFrame "Hgl".
    iApply eq_add_label_r. iFrame "Hgr".
    eq_reshape_l (fl _). eq_reshape_r (fr _).
    iApply (eq_exhaustion _ _ _ _ (gk_thy gl gr) with "[Hff]"); [set_unfold; tauto | set_unfold; tauto | |].
    { iApply (eq_thy_mono _ _ (EqThy (λ d, iLblSig_to_iLblThy (sem_row_union (sem_row_flip_mbang OS (θc d)) L)))).
      { intros []; rewrite /θc /gk_thy /pick /=; iApply to_iThy_le_intro'; simpl; apply submseteq_skip;
          unfold sem_row_union;
          repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app);
          solve_submseteq. }
      iApply (eq_lift_forall_app (λ θ, ((𝟙 + 𝟙) -{ θ }-> (Option 𝔾))%T) (λ θ, sem_row_union (sem_row_flip_mbang OS θ) L) _ θc
               with "Hff").
      iApply eq_lift_dep_intro. intros []; rewrite /θc /pick /=; iApply gk_typed. }
    (* the key can be queried several times *)
    iLöb as "IH".
    iSplit.
    { iIntros "!>" (vl vr) "Hv". rewrite eq_lift_unit. iDestruct "Hv" as %[-> ->]...
      iApply eq_value. iModIntro. by rewrite eq_lift_unit. }
    iIntros "!>" (kl kr el er Q) "%Hkl %Hkr HT #Hcont".
    iDestruct (gk_thy_app with "HT") as (Q') "(%Hcase & #[Hnone Hsome] & HQ)".
    destruct Hcase as [[-> ->]|[-> ->]].
    - (* Alice's key: she sends [g^a], and receives Bob's half if he has sent it *)
      eq_handle_os ka kb as "Hka" "Hkb"...
      iApply (eq_na_open _ _ alphaN); [set_solver|]. iFrame "Hinva".
      iIntros "[>H Hclose]".
      eq_reshape_l (Case (Load #la) _ _). eq_reshape_r (Case (Load #lcs) _ _).
      iApply (eq_sample_or_read_store with "H"). iIntros "#Hla #Hα #Hlcs".
      iApply eq_na_close_rule. iFrame "Hclose". iSplitR; [iNext; iRight; iFrame "#"|]...
      eq_reshape_l (do: sl _)%E. eq_reshape_r (do: sr _)%E.
      iApply (eq_chan_send_bob (P γautha) (P' γauthb) with "[] Hinvta");
        [chan_sub | |].
      { iModIntro. iExists la. rewrite id_g_log_nat; last lia. iFrame "#". }
      repeat foldkont; eq_pures'.
      eq_reshape_l (do: rl _)%E. eq_reshape_r (do: rr _)%E.
      iApply eq_chan_recv_bob; [chan_sub |].
      iSplit.
      + (* Bob has not sent his half *)
        repeat foldkont; eq_pures'. eq_cont_l. eq_cont_r.
        eq_exhaustion (fill kl _) (fill kr _) with "[HQ]";
          [set_unfold; tauto | set_unfold; tauto | iApply "Hcont"; iApply "HQ"; iApply "Hnone" | iApply "IH"].
      + (* Bob's half is [g^b] *)
        iIntros (m) "Hm". iDestruct (message_unique with "Hb Hm") as "<-".
        repeat foldkont; eq_pures'.
        rewrite -expgM -ssrnat.multE (Nat.mul_comm b a). eq_cont_l. eq_cont_r.
        eq_exhaustion (fill kl _) (fill kr _) with "[HQ]";
          [set_unfold; tauto | set_unfold; tauto | iApply "Hcont"; iApply "HQ"; iApply "Hsome" | iApply "IH"].
    - (* Bob's key: he receives Alice's half, if she has sent it, and sends [g^b] *)
      eq_handle_os ka kb as "Hka" "Hkb"...
      eq_reshape_l (do: rl _)%E. eq_reshape_r (do: rr _)%E.
      iApply eq_chan_recv_alice; [chan_sub |].
      iSplit.
      { (* Alice has not sent her half *)
        repeat foldkont; eq_pures'. eq_cont_l. eq_cont_r.
        eq_exhaustion (fill kl _) (fill kr _) with "[HQ]";
          [set_unfold; tauto | set_unfold; tauto | iApply "Hcont"; iApply "HQ"; iApply "Hnone" | iApply "IH"]. }
      (* Alice's half is [g^a] *)
      iIntros (m) "(%l & #Hm & #Hl)".
      iDestruct (message_unique with "Ha Hm") as %Heq.
      inversion Heq as [[Hl Ha']]. subst l.
      rewrite -(g_log_id m) -(Nat2Z.inj _ _ Ha')...
      iApply (eq_na_open _ _ betaN); [set_solver|]. iFrame "Hinvb".
      iIntros "[>H Hclose]".
      eq_reshape_l (Case (Load #lb) _ _).
      iApply (eq_sample_or_read with "H"). iIntros "#Hlb #Hβ".
      iApply eq_na_close_rule. iFrame "Hclose". iSplitR; [iNext; iRight; iFrame "#"|]...
      eq_reshape_l (do: sl _)%E. eq_reshape_r (do: sr _)%E.
      iApply (eq_chan_send_alice (P γautha) (P' γauthb) with "[] Hinvtb");
        [chan_sub | by iModIntro |].
      repeat foldkont; eq_pures'.
      rewrite -expgM -ssrnat.multE.
      (* Alice has stored the key in [r] *)
      iApply (eq_na_open _ _ alphaN); [set_solver|]. iFrame "Hinva".
      iIntros "[>[(Hα & Hla & Hlcs) | (#Hα & #Hla & #Hlcs)] Hclose]".
      { by iDestruct (eq_pt_l_agree with "Hla Hl") as %?. }
      iApply eq_na_close_rule. iFrame "Hclose". iSplitR; [iNext; iRight; iFrame "#"|].
      eq_load_r...
      eq_cont_l. eq_cont_r.
      apply Nat2Z.inj in Ha' as ->.
      eq_exhaustion (fill kl _) (fill kr _) with "[HQ]";
        [set_unfold; tauto | set_unfold; tauto | iApply "Hcont"; iApply "HQ"; iApply "Hsome" | iApply "IH"].
  Qed.

  (** The two refinements *)

  (* The channel's predicates in direction [d], as [F_AUTH_F_AUTH_new] takes them. *)
  Definition P_at (d : dir) γauth (m : vgG) : iProp Σ := P γauth m d.
  Definition P'_at (d : dir) γauth (m : vgG) : iProp Σ := P' γauth m d.

  Global Instance P_at_timeless d γ m : Timeless (P_at d γ m).
  Proof. rewrite /P_at /P. apply _. Qed.
  Global Instance P'_at_timeless d γ m : Timeless (P'_at d γ m).
  Proof. rewrite /P'_at /P'. apply _. Qed.

  Definition chan_at (d : dir) γautha γauthb := chan_new_row (P_at d γautha) (P'_at d γauthb).

  Lemma DH_KE_C_DH_real γtoka γtokb γfraca γfracb γautha γauthb :
    ⊢ token γtoka -∗
    token γtokb -∗
    empty_message γautha -∗
    empty_message γauthb -∗
    BREL (DH_KE #()%V) ≤ (C_DH_real #()%V) <|⊥|> {{ λ D1 D2, □ ∀ (L : sem_row Σ) (f1 f2 : val),
      (∀ᵣ θₕ, ((sem_ty_sum 𝟙 𝟙) -{ θₕ }-> (Option 𝔾)) -{ sem_row_union (¡ θₕ) L }-∘ 𝟙)%T f1 f2 -∗
      BREL D1 f1 ≤ D2 f2 <|⊥|> {{ λ v1 v2,
        ∀ send1 send2 recv1 recv2 : label,
          let ac := chan_at Fwd γautha γauthb γtoka atokN γtokb btokN γfraca γfracb send1 send2 recv1 recv2 in
          BREL v1 ((λ: "m", do: send1 "m"), (λ: "m", do: recv1 "m"))%V
             ≤ v2 ((λ: "m", do: send2 "m"), (λ: "m", do: recv2 "m"))%V
            <| (iLblSig_to_iLblThy ac) ++ (iLblSig_to_iLblThy L) |> {{ (λ w1 w2, 𝟙%T w1 w2) }} }} }}.
  Proof using G.
    iIntros "Hta Htb Ha Hb".
    have [H] := DH_KE_C_DH_real_EQ γtoka γtokb γfraca γfracb γautha γauthb.
    specialize (H Fwd). rewrite monPred_at_emp in H. iPoseProof H as "H".
    iSpecialize ("H" with "[//] Hta Htb Ha Hb"). rewrite eq_rel_at /pick /=.
    iApply (brel_wand with "H"). iIntros "!>" (D1 D2) "#HD". iIntros "!>" (L f1 f2) "Hf".
    iSpecialize ("HD" $! L f1 f2 with "[Hf]"); first by rewrite eq_lift_at /pick /=.
    rewrite eq_rel_at /pick /=.
    iApply (brel_wand with "HD"). iIntros "!>" (v1 v2) "Hv". iIntros (s1 s2 r1 r2).
    iSpecialize ("Hv" $! s1 s2 r1 r2). rewrite eq_rel_at /pick /=.
    iApply (brel_wand with "Hv"). iIntros "!>" (w1 w2) "Hw". by rewrite eq_lift_at /pick /=.
  Qed.

  Lemma C_DH_real_DH_KE γtoka γtokb γfraca γfracb γautha γauthb :
    ⊢ token γtoka -∗
    token γtokb -∗
    empty_message γautha -∗
    empty_message γauthb -∗
    BREL (C_DH_real #()%V) ≤ (DH_KE #()%V) <|⊥|> {{ λ D1 D2, □ ∀ (L : sem_row Σ) (f1 f2 : val),
      (∀ᵣ θₕ, ((sem_ty_sum 𝟙 𝟙) -{ θₕ }-> (Option 𝔾)) -{ sem_row_union (¡ θₕ) L }-∘ 𝟙)%T f1 f2 -∗
      BREL D1 f1 ≤ D2 f2 <|⊥|> {{ λ v1 v2,
        ∀ send1 send2 recv1 recv2 : label,
          let ac := chan_at Bwd γautha γauthb γtoka atokN γtokb btokN γfraca γfracb send1 send2 recv1 recv2 in
          BREL v1 ((λ: "m", do: send1 "m"), (λ: "m", do: recv1 "m"))%V
             ≤ v2 ((λ: "m", do: send2 "m"), (λ: "m", do: recv2 "m"))%V
            <| (iLblSig_to_iLblThy ac) ++ (iLblSig_to_iLblThy L) |> {{ (λ w1 w2, 𝟙%T w1 w2) }} }} }}.
  Proof using G.
    iIntros "Hta Htb Ha Hb".
    have [H] := DH_KE_C_DH_real_EQ γtoka γtokb γfraca γfracb γautha γauthb.
    specialize (H Bwd). rewrite monPred_at_emp in H. iPoseProof H as "H".
    iSpecialize ("H" with "[//] Hta Htb Ha Hb"). rewrite eq_rel_at /pick /=.
    iApply (brel_wand with "H"). iIntros "!>" (D1 D2) "#HD". iIntros "!>" (L f1 f2) "Hf".
    iSpecialize ("HD" $! L f2 f1 with "[Hf]"); first by rewrite eq_lift_at /pick /=.
    rewrite eq_rel_at /pick /=.
    iApply (brel_wand with "HD"). iIntros "!>" (v1 v2) "Hv". iIntros (s1 s2 r1 r2).
    iSpecialize ("Hv" $! s2 s1 r2 r1). rewrite eq_rel_at /pick /=.
    iApply (brel_wand with "Hv"). iIntros "!>" (w1 w2) "Hw". by rewrite eq_lift_at /pick /=.
  Qed.

End dhke_real.

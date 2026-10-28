From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode
  spec_rules spec_ra class_instances.
From clutch.prob_eff_lang.probblaze Require Import tactics.
From clutch.prob_eff_lang.probblaze Require Import sem_types sem_row sem_sig sem_judgement sem_def.
From clutch.prob_eff_lang.probblaze.examples.secure_add Require Import add_def add_bijection.

Import fingroup.
Import fingroup.fingroup.

Import valgroup_notation.
Import valgroup_tactics.

Section add_security.
  Context `{probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  #[local] Notation n := (S (S n'')).

  Definition addN : namespace := nroot .@ "add".

  (* The theory of the client's input ports: [InA m] or [InB m] on both
     sides, returning unit. *)
  Program Definition AddThy (add1 add2 : label) : iThy Σ :=
    λ e1 e2, (λne Q,
      ∃ m : nat,
        ((⌜ e1 = do: add1 (InjLV #m) ⌝%E ∗ ⌜ e2 = do: add2 (InjLV #m) ⌝%E) ∨
         (⌜ e1 = do: add1 (InjRV #m) ⌝%E ∗ ⌜ e2 = do: add2 (InjRV #m) ⌝%E)) ∗
        □ Q #()%V #()%V)%I.
  Next Obligation. solve_proper. Qed.

  Program Definition add_mono (add1 add2 : label) :=
    {| pmono_prot_car := AddThy add1 add2; pmono_prot_prop := _ |}.
  Next Obligation.
    iIntros (??????) "#HΦ (%m & Hm & #HQ)".
    iExists m. iFrame. iModIntro. by iApply "HΦ".
  Qed.

  Definition add_sig (add1 add2 : label) := @SemSig Σ (add_mono add1 add2) (add1, add2).

  Lemma add_pers_mono_row l1s l2s (add1 add2 : label) :
    ⊢ pers_mono_row (iLblSig_to_iLblThy [(l1s, l2s, add_sig add1 add2)]).
  Proof.
    iIntros (????) "#HΦΦ'". iIntros (???) "(%H1 & H2)".
    iSplitR "H2"; [iPureIntro; apply H1 |].
    apply list_elem_of_singleton in H1. inversion H1. simplify_eq/=.
    iDestruct "H2" as (?e1' ?e2' ?k1 ?k2 ?S) "(%Hv1 & %HNk1 & %Hv2 & %HNk2 & He1e2 & #Hs1s2)".
    iExists e1', e2', k1, k2, S.
    repeat iSplit; try iPureIntro; try done.
    iModIntro. iIntros (??) "HS". iApply "HΦΦ'". by iApply "Hs1s2".
  Qed.

  Definition add_row l1s l2s (add1 add2 : label) :=
    SemRow [(l1s, l2s, add_sig add1 add2)] (add_pers_mono_row l1s l2s add1 add2).

  (* The client's two input ports are well typed against [add_row]. *)
  Lemma add_ports_typed l1s l2s (add1 add2 : label) :
    let θ := add_row l1s l2s add1 add2 in
    ⊢ sem_val_typed
        ((λ: "x", do: add1 (InjL "x")), (λ: "y", do: add1 (InjR "y")))%V
        ((λ: "x", do: add2 (InjL "x")), (λ: "y", do: add2 (InjR "y")))%V
        ((sem_ty_nat -{ θ }-> 𝟙) × (sem_ty_nat -{ θ }-> 𝟙))%T.
  Proof.
    intros θ. unfold sem_val_typed. iModIntro.
    rewrite /sem_ty_arr /sem_ty_mbang /sem_ty_prod //=.
    iExists _, _, _, _. do 2 (iSplit; first done).
    iSplit; iModIntro; iIntros (w1 w2) "(%m & -> & ->)"; brel_pures';
      (iApply brel_introduction'; first constructor);
      iExists _,_,[],[],_; do 2 (iSplit; [by iPureIntro|]; iSplit; [iPureIntro; apply NeutralEctx_nil|]);
      (iSplit; [|iIntros (??) "!# H"; iApply "H"]);
      iExists m; [iSplit; [by iLeft|] | iSplit; [by iRight|]];
      iModIntro; iApply brel_value; iIntros "$ !>"; done.
  Qed.

  (* Calling related operations of the env (in row [θ]) from inside the
     scenario's handlers, whose labels are [l1s] and [l2s]. *)
  Lemma brel_env_call l1s l2s k1 k2 (f1 f2 v1 v2 : val) (τ κ : sem_ty Σ) (θ L : sem_row Σ) R :
    ectx_labels k1 ⊆ l1s →
    ectx_labels k2 ⊆ l2s →
    (τ -{ θ }-> κ)%T f1 f2 -∗
    τ v1 v2 -∗
    (∀ w1 w2, κ w1 w2 -∗
       BREL fill k1 w1 ≤ fill k2 w2
         <|(l1s, l2s, iThyBot) :: iLblSig_to_iLblThy (sem_row_union (¡ θ)%R L)|> {{R}}) -∗
    BREL fill k1 (f1 v1) ≤ fill k2 (f2 v2)
      <|(l1s, l2s, iThyBot) :: iLblSig_to_iLblThy (sem_row_union (¡ θ)%R L)|> {{R}}.
  Proof.
    iIntros (Hk1 Hk2) "Hf Hv Hk".
    iApply (brel_bind'' _ _ (iLblSig_to_iLblThy (¡ θ)%R) [(l1s, l2s, iThyBot)]).
    { rewrite labels_l_cons /=. set_solver. }
    { rewrite labels_r_cons /=. set_solver. }
    { iApply to_iThy_le_intro'. unfold sem_row_union.
      repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app).
      solve_submseteq. }
    rewrite iThyIfMono_iLblSig_to_iThyIfMono.
    iApply (brel_mono OS with "[] [Hf Hv] Hk"); first iApply to_iThy_le_refl.
    rewrite /sem_ty_mbang /sem_ty_arr /=. by iApply "Hf".
  Qed.

  Lemma R_ADD_I_ADD : ⊢ sem_typed [] R_ADD I_ADD ⊥ τ_ADD [].
  Proof with (repeat foldkont; brel_pures') using All.
    iIntros (vs) "!> _ /=".
    unfold R_ADD, I_ADD, functionality_composition, func_comp, π_ADD, F_ADD, S_ADD, F_CHAN...
    iModIntro. iSplitR; last done.
    iIntros (L f1 f2) "Hf"...
    iModIntro.
    iIntros (θ e1 e2) "Heffs"...
    iDestruct "Heffs" as (toC1 toC2 ch1 ch2) "(-> & -> & HtoC & Hch)".
    iDestruct "HtoC" as (sAC1 sAC2 sBC1 sBC2) "(-> & -> & #HsAC & #HsBC)".
    iDestruct "Hch" as (ls1 ls2 lr1 lr2) "(-> & -> & #Hls & #Hlr)"...
    brel_alloc_l msg as "Hmsg"...
    brel_effect_l ssend as "Hssend"...
    brel_effect_l srecv as "Hsrecv"...
    brel_alloc_l doneA as "HdoneA"...
    brel_alloc_l doneB as "HdoneB"...
    brel_effect_l add_l as "Hadd_l"...
    brel_alloc_r lu as "Hlu"...
    brel_effect_r leak as "Hleak"...
    brel_alloc_r lx as "Hlx"...
    brel_alloc_r ly as "Hly"...
    brel_effect_r add_r as "Hadd_r"...
    set (l1s := [add_l; srecv; ssend]).
    set (l2s := [add_r; leak]).
    set (θc := add_row l1s l2s add_l add_r).
    iSpecialize ("Hf" $! θc).
    iPoseProof (add_ports_typed l1s l2s add_l add_r) as "Hports".
    unfold sem_val_typed. simpl. iDestruct "Hports" as "#Hports".
    iSpecialize ("Hf" with "Hports").
    set (IA := ((doneA ↦ #false ∗ msg ↦ NONEV ∗ lx ↦ₛ NONEV ∗ lu ↦ₛ NONEV) ∨
                (∃ x r : vgG, doneA ↦□ #true ∗ msg ↦□ SOMEV (vgval r) ∗
                   lx ↦ₛ□ SOMEV (vgval x) ∗ lu ↦ₛ□ SOMEV (vgval (x * r)%g)))%I).
    set (IB := ((doneB ↦ #false ∗ ly ↦ₛ NONEV) ∨
                (∃ y : vgG, doneB ↦ #true ∗ ly ↦ₛ SOMEV (vgval y)))%I).
    iApply (brel_na_alloc (IA ∗ IB)%I addN).
    iSplitL "HdoneA Hmsg Hlx Hlu HdoneB Hly".
    { iNext. iSplitL "HdoneA Hmsg Hlx Hlu"; iLeft; iFrame. }
    iIntros "#Hinv".
    iApply brel_new_theory.
    iApply (brel_add_label_l with "Hssend").
    iApply (brel_add_label_l with "Hsrecv").
    iApply (brel_add_label_l with "Hadd_l").
    iApply (brel_add_label_r with "Hleak").
    iApply (brel_add_label_r with "Hadd_r").
    iApply brel_learn. iIntros "%Hdist _".
    iApply (brel_exhaustion (f1 _) (f2 _) with "[Hf]");
      [set_unfold; tauto | set_unfold; tauto | | ].
    { iApply (brel_introduction_mono with "[] Hf").
      iApply to_iThy_le_intro'. simpl.
      apply submseteq_skip.
      unfold sem_row_union.
      repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app).
      solve_submseteq. }
    iLöb as "IH".
    iSplit; [iIntros (v1 v2) "%Hv1v2"; iModIntro; brel_pures; iModIntro; done |].
    iIntros (k1 k2 e1 e2 Q) "!# %Hk1 %Hk2 HXQ #Hrel".
    simpl.
    iDestruct "HXQ" as (m) "[[[-> ->]|[-> ->]] #HQ]".
    - (* Alice's input *)
      brel_handle_os_l (ka) as "Hka"...
      brel_handle_os_r (fa) as "Hfa"...
      destruct (vg_of_int_sem m) as [x|] eqn:Hm; last first.
      { iApply brel_vg_of_int_none_l; first done.
        iApply brel_vg_of_int_none_r; first done...
        brel_cont_l. brel_cont_r.
        iApply (brel_exhaustion (fill k1 #()%V) (fill k2 #()%V));
          [set_unfold; tauto | set_unfold; tauto | by iApply "Hrel" | iApply "IH"]. }
      iApply brel_vg_of_int_correct_l; first done.
      iApply brel_vg_of_int_correct_r; first done...
      iApply (brel_na_inv _ _ addN); first (set_unfold; tauto).
      iFrame "Hinv".
      iIntros "[[[>HA0 | >HA1] HB] Hclose]".
      + (* Alice's first input *)
        iDestruct "HA0" as "(HdoneA & Hmsg & Hlx & Hlu)".
        brel_load_l... brel_store_l...
        brel_load_r... brel_store_r...
        iApply (brel_handle_os_r [] [AppRCtx _]); first (simpl; set_solver).
        iIntros (sa) "Hsa"...
        (* Alice's mask [g^ρ] against the simulator's [u = x · g^ρ] *)
        iApply (brel_couple_rand_rand _ _ (add_coupling_nat x));
          first apply add_coupling_nat_bound.
        iIntros (ρ) "%Hρ"...
        rewrite add_coupling_nat_mult; last lia...
        iApply brel_int_of_vg_sem_correct_l...
        iApply (brel_handle_os_l [HandleCtx _ _ _ _ _] [AppRCtx _]); first (simpl; set_solver).
        iIntros "!>" (ks) "Hks"...
        iApply brel_vg_of_int_correct_l; first apply int_of_vg_of_int_sem...
        brel_load_l... brel_store_l...
        brel_store_r...
        iMod (ghost_map_elem_persist with "HdoneA") as "#HdoneA".
        iMod (ghost_map_elem_persist with "Hmsg") as "#Hmsg".
        iMod (ghost_map_elem_persist with "Hlx") as "#Hlx".
        iMod (ghost_map_elem_persist with "Hlu") as "#Hlu".
        iApply brel_na_close. iFrame "Hclose".
        iSplitR "Hka Hfa Hsa Hks".
        { iNext. iFrame "HB". iRight. iExists x, (g ^+ ρ)%g. iFrame "#". }
        (* F_CHAN leaks that Alice sent *)
        iApply (brel_env_call l1s l2s [HandleCtx _ _ _ _ _; AppRCtx _] [AppRCtx _] with "Hls []");
          [simpl; set_solver | simpl; set_solver | |].
        { iExists #()%V, #()%V. iRight. repeat iSplit; try iPureIntro; done. }
        iIntros (w1 w2) "(->&->)"...
        brel_cont_l...
        (* Alice's message to the aggregator *)
        iApply (brel_env_call l1s l2s [HandleCtx _ _ _ _ _; HandleCtx _ _ _ _ _; AppRCtx _] [AppRCtx _]
                 with "HsAC []");
          [simpl; set_solver | simpl; set_solver | by iExists _ |].
        iIntros (w1 w2) "(->&->)"...
        brel_cont_l. brel_cont_r... brel_cont_r.
        iApply (brel_exhaustion (fill k1 #()%V) (fill k2 #()%V));
          [set_unfold; tauto | set_unfold; tauto | by iApply "Hrel" | iApply "IH"].
      + (* Alice already gave her input *)
        iDestruct "HA1" as (x' r) "(#HdoneA & #Hmsg & #Hlx & #Hlu)".
        brel_load_l... brel_load_r...
        iApply brel_na_close. iFrame "Hclose".
        iSplitR "Hka Hfa".
        { iNext. iFrame "HB". iRight. iExists x', r. iFrame "#". }
        brel_cont_l. brel_cont_r.
        iApply (brel_exhaustion (fill k1 #()%V) (fill k2 #()%V));
          [set_unfold; tauto | set_unfold; tauto | by iApply "Hrel" | iApply "IH"].
    - (* Bob's input *)
      destruct Hdist as [Hdl Hdr].
      apply distinct_l_cons_inv in Hdl as [Hnd_l _].
      apply NoDup_cons in Hnd_l as [Hn_add Hnd_l].
      apply NoDup_cons in Hnd_l as [Hn_srecv _].
      brel_handle_os_l (kb) as "Hkb"...
      brel_handle_os_r (fb) as "Hfb"...
      destruct (vg_of_int_sem m) as [y|] eqn:Hm; last first.
      { iApply brel_vg_of_int_none_l; first done.
        iApply brel_vg_of_int_none_r; first done...
        brel_cont_l. brel_cont_r.
        iApply (brel_exhaustion (fill k1 #()%V) (fill k2 #()%V));
          [set_unfold; tauto | set_unfold; tauto | by iApply "Hrel" | iApply "IH"]. }
      iApply brel_vg_of_int_correct_l; first done.
      iApply brel_vg_of_int_correct_r; first done...
      iApply (brel_na_inv _ _ addN); first (set_unfold; tauto).
      iFrame "Hinv".
      iIntros "[[HA [>HB0 | >HB1]] Hclose]".
      + (* Bob has not given an input yet *)
        iDestruct "HB0" as "(HdoneB & Hly)".
        brel_load_l... brel_load_r...
        iApply brel_na_close. iFrame "Hclose".
        iSplitR "Hkb Hfb".
        { iNext. iFrame "HA". iLeft. iFrame. }
        (* Bob asks F_CHAN for [r]; the simulator forwards the env's decision *)
        iApply (brel_handle_os_l [] [HandleCtx _ _ _ _ _; CaseCtx _ _]); first (simpl; set_solver).
        iIntros "!>" (kr) "Hkr"...
        iApply (brel_handle_os_r [] [CaseCtx _ _]); first (simpl; set_solver).
        iIntros (sb) "Hsb"...
        iApply (brel_env_call l1s l2s [AppRCtx _] [AppRCtx _] with "Hlr []");
          [simpl; set_solver | simpl; set_solver | |].
        { iExists #()%V, #()%V. iLeft. repeat iSplit; try iPureIntro; done. }
        iIntros (w1 w2) "(%a1 & %a2 & [(->&->&->&->)|(->&->&->&->)])"...
        * (* [r] is not delivered *)
          brel_cont_l... brel_cont_l. brel_cont_r... brel_cont_r.
          iApply (brel_exhaustion (fill k1 #()%V) (fill k2 #()%V));
            [set_unfold; tauto | set_unfold; tauto | by iApply "Hrel" | iApply "IH"].
        * (* [r] is delivered, if Alice has sent it *)
          iApply (brel_na_inv _ _ addN); first (set_unfold; tauto).
          iFrame "Hinv".
          iIntros "[[[>HA0 | >HA1] >HB] Hclose]".
          -- (* Alice has not sent [r] yet *)
             iDestruct "HA0" as "(HdoneA & Hmsg & Hlx & Hlu)".
             brel_load_l... brel_cont_l... brel_cont_r... brel_load_r...
             iApply brel_na_close. iFrame "Hclose".
             iSplitL "HdoneA Hmsg Hlx Hlu HB".
             { iNext. iFrame "HB". iLeft. iFrame. }
             brel_cont_l. brel_cont_r.
             iApply (brel_exhaustion (fill k1 #()%V) (fill k2 #()%V));
               [set_unfold; tauto | set_unfold; tauto | by iApply "Hrel" | iApply "IH"].
          -- (* Bob sends [y · r^-1] *)
             iDestruct "HA1" as (x r) "(#HdoneA & #Hmsg & #Hlx & #Hlu)".
             iAssert (∃ (b : bool) v, doneB ↦ #b ∗ ly ↦ₛ v)%I with "[HB]" as (b v) "[HdoneB Hly]".
             { iDestruct "HB" as "[[? ?]|(% & ? & ?)]"; iExists _, _; iFrame. }
             brel_load_l... brel_cont_l... brel_store_l...
             brel_cont_r... brel_load_r... brel_store_r...
             iApply (brel_handle_os_r [] [AppRCtx _]); first (simpl; set_solver).
             iIntros (so) "Hso"...
             brel_load_r...
             rewrite add_mask_cancel.
             iApply brel_na_close. iFrame "Hclose".
             iSplitL "HdoneB Hly".
             { iNext. iSplitR; [iRight; iExists x, r; iFrame "#" |]. iRight. iExists y. iFrame. }
             iApply (brel_env_call l1s l2s [HandleCtx _ _ _ _ _; HandleCtx _ _ _ _ _; AppRCtx _] [AppRCtx _]
                      with "HsBC []");
               [simpl; set_solver | simpl; set_solver | by iExists _ |].
             iIntros (w1 w2) "(->&->)"...
             brel_cont_l. brel_cont_r... brel_cont_r.
             iApply (brel_exhaustion (fill k1 #()%V) (fill k2 #()%V));
               [set_unfold; tauto | set_unfold; tauto | by iApply "Hrel" | iApply "IH"].
      + (* Bob already gave his input *)
        iDestruct "HB1" as (y') "(HdoneB & Hly)".
        brel_load_l... brel_load_r...
        iApply brel_na_close. iFrame "Hclose".
        iSplitR "Hkb Hfb".
        { iNext. iFrame "HA". iRight. iExists y'. iFrame. }
        brel_cont_l. brel_cont_r.
        iApply (brel_exhaustion (fill k1 #()%V) (fill k2 #()%V));
          [set_unfold; tauto | set_unfold; tauto | by iApply "Hrel" | iApply "IH"].
  Qed.

  Lemma I_ADD_R_ADD : ⊢ sem_typed [] I_ADD R_ADD ⊥ τ_ADD [].
  Proof with (repeat foldkont; brel_pures') using All.
    iIntros (vs) "!> _ /=".
    unfold R_ADD, I_ADD, functionality_composition, func_comp, π_ADD, F_ADD, S_ADD, F_CHAN...
    iModIntro. iSplitR; last done.
    iIntros (L f1 f2) "Hf"...
    iModIntro.
    iIntros (θ e1 e2) "Heffs"...
    iDestruct "Heffs" as (toC1 toC2 ch1 ch2) "(-> & -> & HtoC & Hch)".
    iDestruct "HtoC" as (sAC1 sAC2 sBC1 sBC2) "(-> & -> & #HsAC & #HsBC)".
    iDestruct "Hch" as (ls1 ls2 lr1 lr2) "(-> & -> & #Hls & #Hlr)"...
    brel_alloc_l lu as "Hlu"...
    brel_effect_l leak as "Hleak"...
    brel_alloc_l lx as "Hlx"...
    brel_alloc_l ly as "Hly"...
    brel_effect_l add_l as "Hadd_l"...
    brel_alloc_r msg as "Hmsg"...
    brel_effect_r ssend as "Hssend"...
    brel_effect_r srecv as "Hsrecv"...
    brel_alloc_r doneA as "HdoneA"...
    brel_alloc_r doneB as "HdoneB"...
    brel_effect_r add_r as "Hadd_r"...
    set (l1s := [add_l; leak]).
    set (l2s := [add_r; srecv; ssend]).
    set (θc := add_row l1s l2s add_l add_r).
    iSpecialize ("Hf" $! θc).
    iPoseProof (add_ports_typed l1s l2s add_l add_r) as "Hports".
    unfold sem_val_typed. simpl. iDestruct "Hports" as "#Hports".
    iSpecialize ("Hf" with "Hports").
    set (IA := ((lx ↦ NONEV ∗ lu ↦ NONEV ∗ doneA ↦ₛ #false ∗ msg ↦ₛ NONEV) ∨
                (∃ x r : vgG, lx ↦□ SOMEV (vgval x) ∗ lu ↦□ SOMEV (vgval (x * r)%g) ∗
                   doneA ↦ₛ□ #true ∗ msg ↦ₛ□ SOMEV (vgval r)))%I).
    set (IB := ((ly ↦ NONEV ∗ doneB ↦ₛ #false) ∨
                (∃ y : vgG, ly ↦ SOMEV (vgval y) ∗ doneB ↦ₛ #true))%I).
    iApply (brel_na_alloc (IA ∗ IB)%I addN).
    iSplitL "HdoneA Hmsg Hlx Hlu HdoneB Hly".
    { iNext. iSplitL "HdoneA Hmsg Hlx Hlu"; iLeft; iFrame. }
    iIntros "#Hinv".
    iApply brel_new_theory.
    iApply (brel_add_label_l with "Hleak").
    iApply (brel_add_label_l with "Hadd_l").
    iApply (brel_add_label_r with "Hssend").
    iApply (brel_add_label_r with "Hsrecv").
    iApply (brel_add_label_r with "Hadd_r").
    iApply brel_learn. iIntros "%Hdist _".
    iApply (brel_exhaustion (f1 _) (f2 _) with "[Hf]");
      [set_unfold; tauto | set_unfold; tauto | | ].
    { iApply (brel_introduction_mono with "[] Hf").
      iApply to_iThy_le_intro'. simpl.
      apply submseteq_skip.
      unfold sem_row_union.
      repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app).
      solve_submseteq. }
    iLöb as "IH".
    iSplit; [iIntros (v1 v2) "%Hv1v2"; iModIntro; brel_pures; iModIntro; done |].
    iIntros (k1 k2 e1 e2 Q) "!# %Hk1 %Hk2 HXQ #Hrel".
    simpl.
    iDestruct "HXQ" as (m) "[[[-> ->]|[-> ->]] #HQ]".
    - (* Alice's input *)
      brel_handle_os_l (fa) as "Hfa"...
      brel_handle_os_r (ka) as "Hka"...
      destruct (vg_of_int_sem m) as [x|] eqn:Hm; last first.
      { iApply brel_vg_of_int_none_l; first done.
        iApply brel_vg_of_int_none_r; first done...
        brel_cont_l. brel_cont_r.
        iApply (brel_exhaustion (fill k1 #()%V) (fill k2 #()%V));
          [set_unfold; tauto | set_unfold; tauto | by iApply "Hrel" | iApply "IH"]. }
      iApply brel_vg_of_int_correct_l; first done.
      iApply brel_vg_of_int_correct_r; first done...
      iApply (brel_na_inv _ _ addN); first (set_unfold; tauto).
      iFrame "Hinv".
      iIntros "[[[>HA0 | >HA1] HB] Hclose]".
      + (* Alice's first input *)
        iDestruct "HA0" as "(Hlx & Hlu & HdoneA & Hmsg)".
        brel_load_l... brel_store_l...
        iApply (brel_handle_os_l [] [AppRCtx _]); first (simpl; set_solver).
        iIntros "!>" (sa) "Hsa"...
        brel_load_r... brel_store_r...
        (* the simulator's [u = g^μ] against Alice's mask [x^-1 · g^μ] *)
        iApply (brel_couple_rand_rand _ _ (add_coupling_nat x^-1));
          first apply add_coupling_nat_bound.
        iIntros (μ) "%Hμ"...
        rewrite add_coupling_nat_mult; last lia...
        iApply brel_int_of_vg_sem_correct_r...
        iApply (brel_handle_os_r [HandleCtx _ _ _ _ _] [AppRCtx _]); first (simpl; set_solver).
        iIntros (ks) "Hks"...
        iApply brel_vg_of_int_correct_r; first apply int_of_vg_of_int_sem...
        brel_load_r... brel_store_r...
        brel_store_l...
        iMod (ghost_map_elem_persist with "HdoneA") as "#HdoneA".
        iMod (ghost_map_elem_persist with "Hmsg") as "#Hmsg".
        iMod (ghost_map_elem_persist with "Hlx") as "#Hlx".
        iMod (ghost_map_elem_persist with "Hlu") as "#Hlu".
        iApply brel_na_close. iFrame "Hclose".
        iSplitR "Hka Hfa Hsa Hks".
        { iNext. iFrame "HB". iRight. iExists x, (x^-1 * g ^+ μ)%g.
          rewrite mulKVg. iFrame "#". }
        (* F_CHAN leaks that Alice sent *)
        iApply (brel_env_call l1s l2s [AppRCtx _] [HandleCtx _ _ _ _ _; AppRCtx _] with "Hls []");
          [simpl; set_solver | simpl; set_solver | |].
        { iExists #()%V, #()%V. iRight. repeat iSplit; try iPureIntro; done. }
        iIntros (w1 w2) "(->&->)"...
        brel_cont_r...
        rewrite mulKVg.
        (* Alice's message to the aggregator *)
        iApply (brel_env_call l1s l2s [AppRCtx _] [HandleCtx _ _ _ _ _; HandleCtx _ _ _ _ _; AppRCtx _]
                 with "HsAC []");
          [simpl; set_solver | simpl; set_solver | by iExists _ |].
        iIntros (w1 w2) "(->&->)"...
        brel_cont_l... brel_cont_l. brel_cont_r.
        iApply (brel_exhaustion (fill k1 #()%V) (fill k2 #()%V));
          [set_unfold; tauto | set_unfold; tauto | by iApply "Hrel" | iApply "IH"].
      + (* Alice already gave her input *)
        iDestruct "HA1" as (x' r) "(#Hlx & #Hlu & #HdoneA & #Hmsg)".
        brel_load_l... brel_load_r...
        iApply brel_na_close. iFrame "Hclose".
        iSplitR "Hka Hfa".
        { iNext. iFrame "HB". iRight. iExists x', r. iFrame "#". }
        brel_cont_l. brel_cont_r.
        iApply (brel_exhaustion (fill k1 #()%V) (fill k2 #()%V));
          [set_unfold; tauto | set_unfold; tauto | by iApply "Hrel" | iApply "IH"].
    - (* Bob's input *)
      destruct Hdist as [Hdl Hdr].
      apply distinct_r_cons_inv in Hdr as [Hnd_r _].
      apply NoDup_cons in Hnd_r as [Hn_add Hnd_r].
      apply NoDup_cons in Hnd_r as [Hn_srecv _].
      brel_handle_os_l (fb) as "Hfb"...
      brel_handle_os_r (kb) as "Hkb"...
      destruct (vg_of_int_sem m) as [y|] eqn:Hm; last first.
      { iApply brel_vg_of_int_none_l; first done.
        iApply brel_vg_of_int_none_r; first done...
        brel_cont_l. brel_cont_r.
        iApply (brel_exhaustion (fill k1 #()%V) (fill k2 #()%V));
          [set_unfold; tauto | set_unfold; tauto | by iApply "Hrel" | iApply "IH"]. }
      iApply brel_vg_of_int_correct_l; first done.
      iApply brel_vg_of_int_correct_r; first done...
      iApply (brel_na_inv _ _ addN); first (set_unfold; tauto).
      iFrame "Hinv".
      iIntros "[[HA [>HB0 | >HB1]] Hclose]".
      + (* Bob has not given an input yet *)
        iDestruct "HB0" as "(Hly & HdoneB)".
        brel_load_l... brel_load_r...
        iApply brel_na_close. iFrame "Hclose".
        iSplitR "Hkb Hfb".
        { iNext. iFrame "HA". iLeft. iFrame. }
        (* the simulator forwards the env's decision; Bob asks F_CHAN for [r] *)
        iApply (brel_handle_os_l [] [CaseCtx _ _]); first (simpl; set_solver).
        iIntros "!>" (sb) "Hsb"...
        iApply (brel_handle_os_r [] [HandleCtx _ _ _ _ _; CaseCtx _ _]); first (simpl; set_solver).
        iIntros (kr) "Hkr"...
        iApply (brel_env_call l1s l2s [AppRCtx _] [AppRCtx _] with "Hlr []");
          [simpl; set_solver | simpl; set_solver | |].
        { iExists #()%V, #()%V. iLeft. repeat iSplit; try iPureIntro; done. }
        iIntros (w1 w2) "(%a1 & %a2 & [(->&->&->&->)|(->&->&->&->)])"...
        * (* [r] is not delivered *)
          brel_cont_l... brel_cont_l. brel_cont_r... brel_cont_r.
          iApply (brel_exhaustion (fill k1 #()%V) (fill k2 #()%V));
            [set_unfold; tauto | set_unfold; tauto | by iApply "Hrel" | iApply "IH"].
        * (* [r] is delivered, if Alice has sent it *)
          iApply (brel_na_inv _ _ addN); first (set_unfold; tauto).
          iFrame "Hinv".
          iIntros "[[[>HA0 | >HA1] >HB] Hclose]".
          -- (* Alice has not sent [r] yet *)
             iDestruct "HA0" as "(Hlx & Hlu & HdoneA & Hmsg)".
             brel_cont_l... brel_load_l... brel_load_r... brel_cont_r...
             iApply brel_na_close. iFrame "Hclose".
             iSplitL "HdoneA Hmsg Hlx Hlu HB".
             { iNext. iFrame "HB". iLeft. iFrame. }
             brel_cont_l. brel_cont_r.
             iApply (brel_exhaustion (fill k1 #()%V) (fill k2 #()%V));
               [set_unfold; tauto | set_unfold; tauto | by iApply "Hrel" | iApply "IH"].
          -- (* Bob sends [y · r^-1] *)
             iDestruct "HA1" as (x r) "(#Hlx & #Hlu & #HdoneA & #Hmsg)".
             iAssert (∃ v (b : bool), ly ↦ v ∗ doneB ↦ₛ #b)%I with "[HB]" as (v b) "[Hly HdoneB]".
             { iDestruct "HB" as "[[? ?]|(% & ? & ?)]"; iExists _, _; iFrame. }
             brel_cont_l... brel_load_l... brel_store_l...
             iApply (brel_handle_os_l [] [AppRCtx _]); first (simpl; set_solver).
             iIntros "!>" (so) "Hso"...
             brel_load_l...
             rewrite add_mask_cancel.
             brel_load_r... brel_cont_r... brel_store_r...
             iApply brel_na_close. iFrame "Hclose".
             iSplitL "HdoneB Hly".
             { iNext. iSplitR; [iRight; iExists x, r; iFrame "#" |]. iRight. iExists y. iFrame. }
             iApply (brel_env_call l1s l2s [AppRCtx _] [HandleCtx _ _ _ _ _; HandleCtx _ _ _ _ _; AppRCtx _]
                      with "HsBC []");
               [simpl; set_solver | simpl; set_solver | by iExists _ |].
             iIntros (w1 w2) "(->&->)"...
             brel_cont_l... brel_cont_l. brel_cont_r.
             iApply (brel_exhaustion (fill k1 #()%V) (fill k2 #()%V));
               [set_unfold; tauto | set_unfold; tauto | by iApply "Hrel" | iApply "IH"].
      + (* Bob already gave his input *)
        iDestruct "HB1" as (y') "(Hly & HdoneB)".
        brel_load_l... brel_load_r...
        iApply brel_na_close. iFrame "Hclose".
        iSplitR "Hkb Hfb".
        { iNext. iFrame "HA". iRight. iExists y'. iFrame. }
        brel_cont_l. brel_cont_r.
        iApply (brel_exhaustion (fill k1 #()%V) (fill k2 #()%V));
          [set_unfold; tauto | set_unfold; tauto | by iApply "Hrel" | iApply "IH"].
  Qed.

End add_security.

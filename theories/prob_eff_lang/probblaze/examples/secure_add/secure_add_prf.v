From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode
  spec_rules spec_ra class_instances.
From clutch.prob_eff_lang.probblaze Require Import tactics.
From clutch.prob_eff_lang.probblaze Require Import sem_types sem_row sem_sig sem_judgement sem_def.
From iris.bi Require Import monpred.
From iris.proofmode Require Import monpred.
From clutch.prob_eff_lang.probblaze.examples.secure_add Require Import secure_add_def secure_add_bijection.
From clutch.prob_eff_lang.probblaze.eq Require Import eq_logic eq_valgroup eq_handlers eq_compat.

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

  (* The theory of the client's input ports, with the labels of [l] ([al])
     and of [r] ([ar]); it is symmetric, so in direction [Bwd] it is the same
     theory with the labels swapped. *)
  Definition add_thy (al ar : label) : dir → iThy Σ := λ d, AddThy (pick d al ar) (pick d ar al).

  Lemma add_thy_app al ar el er Q :
    eq_thy_app (add_thy al ar) el er Q ⊢
      ∃ m : nat, ⌜(el = (do: al (InjLV #m))%E ∧ er = (do: ar (InjLV #m))%E) ∨
                  (el = (do: al (InjRV #m))%E ∧ er = (do: ar (InjRV #m))%E)⌝ ∗ ⎡□ Q #()%V #()%V⎤.
  Proof.
    split=> d. rewrite monPred_at_exist.
    destruct d; rewrite /eq_thy_app /add_thy /pick /=;
      iIntros "(%m & [[-> ->]|[-> ->]] & #HQ)"; iExists m;
      rewrite monPred_at_sep monPred_at_pure monPred_at_embed; iFrame "HQ"; iPureIntro; naive_solver.
  Qed.

  (* The protocol [REAL_ADD] is [l], the simulated functionality [r]. *)
  Lemma ADD_EQ :
    ⊢ EQ REAL_ADD ≈ SIM_IDEAL_ADD <|iLblSig_to_iLblThy (⊥ : sem_row Σ)|> {{ ⟪ 𝟙 -{ ⟨⟩ }-[ MS ]-> τ_ADD ⟫ }}.
  Proof with (repeat foldkont; eq_pures') using All.
    iApply eq_value. iModIntro. iModIntro.
    iApply eq_lift_arr. iIntros (u1 u2) "Hu". rewrite eq_lift_unit. iDestruct "Hu" as %[-> ->].
    unfold REAL_ADD, SIM_IDEAL_ADD, SIM_ADD, IDEAL_ADD, functionality_composition, func_comp...
    (* Calling the composites allocates the state: the protocol's flags and
       F_CHAN's message in [l], F_ADD's inputs and the simulator's message in
       [r]. *)
    eq_alloc_l doneA as "HdoneA"...
    eq_alloc_l doneB as "HdoneB"...
    eq_alloc_l msg as "Hmsg"...
    eq_alloc_r lx as "Hlx"...
    eq_alloc_r ly as "Hly"...
    eq_alloc_r lu as "Hlu"...
    iApply eq_value. iModIntro. rewrite /τ_ADD. iEval (rewrite eq_lift_forall). iIntros (L).
    iApply eq_lift_arr. iIntros (f1 f2) "Hf"...
    iApply eq_value. iModIntro. iEval (rewrite eq_lift_forall). iIntros (θ).
    iApply eq_lift_arr. iIntros (e1 e2) "Heffs"...
    iEval (rewrite eq_lift_prod) in "Heffs". iDestruct "Heffs" as (toC1 toC2 ch1 ch2) "(-> & -> & HtoC & Hch)".
    iEval (rewrite eq_lift_prod) in "HtoC". iDestruct "HtoC" as (sAC1 sAC2 sBC1 sBC2) "(-> & -> & #HsAC & #HsBC)".
    iEval (rewrite eq_lift_prod) in "Hch". iDestruct "Hch" as (ls1 ls2 lr1 lr2) "(-> & -> & #Hls & #Hlr)"...
    eq_effect_l ssend as "Hssend"...
    eq_effect_l srecv as "Hsrecv"...
    eq_effect_l add_l as "Hadd_l"...
    eq_effect_r leak as "Hleak"...
    eq_effect_r add_r as "Hadd_r"...
    set (lls := [add_l; srecv; ssend]).
    set (rls := [add_r; leak]).
    (* The client's row: its input ports, with the labels of the program on
       the left. *)
    set (θc := λ d, add_row (pick d lls rls) (pick d rls lls) (pick d add_l add_r) (pick d add_r add_l)).
    set (IA := ((doneA ↦ₗ #false ∗ msg ↦ₗ NONEV ∗ lx ↦ᵣ NONEV ∗ lu ↦ᵣ NONEV) ∨
                (∃ x r : vgG, doneA ↦ₗ□ #true ∗ msg ↦ₗ□ SOMEV (vgval r) ∗
                   lx ↦ᵣ□ SOMEV (vgval x) ∗ lu ↦ᵣ□ SOMEV (vgval (x * r)%g)))%I : iPropD Σ).
    set (IB := ((doneB ↦ₗ #false ∗ ly ↦ᵣ NONEV) ∨
                (∃ y : vgG, doneB ↦ₗ #true ∗ ly ↦ᵣ SOMEV (vgval y)))%I : iPropD Σ).
    iApply (eq_na_alloc (IA ∗ IB) addN).
    iSplitL "HdoneA Hmsg Hlx Hlu HdoneB Hly".
    { iNext. iSplitL "HdoneA Hmsg Hlx Hlu"; iLeft; iFrame. }
    iIntros "#Hinv".
    iApply eq_new_theory.
    iApply eq_add_label_l. iFrame "Hssend".
    iApply eq_add_label_l. iFrame "Hsrecv".
    iApply eq_add_label_l. iFrame "Hadd_l".
    iApply eq_add_label_r. iFrame "Hleak".
    iApply eq_add_label_r. iFrame "Hadd_r".
    iApply eq_learn_nodup. iIntros ([Hndl _]).
    eq_reshape_l (f1 _). eq_reshape_r (f2 _).
    iApply (eq_exhaustion _ _ _ _ (add_thy add_l add_r) with "[Hf]");
      [set_unfold; tauto | set_unfold; tauto | |].
    { iApply (eq_thy_mono _ _ (EqThy (λ d, iLblSig_to_iLblThy (sem_row_union (θc d) L)))).
      { intros []; rewrite /θc /add_thy /pick /=; iApply to_iThy_le_intro'; simpl;
          apply submseteq_skip; unfold sem_row_union;
          repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app);
          solve_submseteq. }
      iApply (eq_lift_forall_app _ _ _ θc with "Hf").
      iApply eq_lift_dep_intro. intros []; rewrite /θc /pick /=;
        iPoseProof (add_ports_typed _ _ _ _) as "H"; unfold sem_val_typed; simpl; iDestruct "H" as "#H"; iApply "H". }
    iLöb as "IH".
    iSplit.
    { iIntros "!>" (vl vr) "Hv". rewrite eq_lift_unit. iDestruct "Hv" as %[-> ->].
      eq_pures_l. eq_pures_r. iApply eq_value. iModIntro. by rewrite eq_lift_unit. }
    iIntros "!>" (k1 k2 e1 e2 Q) "%Hk1 %Hk2 HXQ #Hrel".
    iDestruct (add_thy_app with "HXQ") as (m) "[%Hm #HQ]".
    destruct Hm as [[-> ->]|[-> ->]].
    - (* Alice's input *)
      eq_handle_os ka fa as "Hka" "Hfa"...
      destruct (vg_of_int_sem m) as [x|] eqn:Hm; last first.
      { eq_vg_of_int_none_l. eq_vg_of_int_none_r...
        eq_cont_l. eq_cont_r.
        eq_exhaustion (fill k1 #()%V) (fill k2 #()%V);
          [set_unfold; tauto | set_unfold; tauto | by iApply "Hrel" | iApply "IH"]. }
      eq_vg_of_int_l. eq_vg_of_int_r...
      iApply (eq_na_open _ _ addN); first (set_unfold; tauto).
      iFrame "Hinv".
      iIntros "[[[>HA0 | >HA1] HB] Hclose]".
      + (* Alice's first input *)
        iDestruct "HA0" as "(HdoneA & Hmsg & Hlx & Hlu)".
        eq_load_l... eq_store_l...
        eq_load_r... eq_store_r...
        iApply (eq_handle_os_r [] [AppRCtx _]); first (simpl; set_solver).
        iIntros (sa) "Hsa"...
        (* Alice's mask [g^ρ] against the simulator's [u = x · g^ρ] *)
        eq_focus_l (rand #_)%E. eq_focus_r (rand #_)%E.
        iApply (eq_couple_rand_rand_bij _ _ (add_coupling_nat x)); first apply add_coupling_nat_bound.
        iIntros (ρ) "%Hρ". simpl...
        rewrite add_coupling_nat_mult; last lia...
        eq_int_of_vg_l...
        iApply (eq_handle_os_l [HandleCtx _ _ _ _ _] [AppRCtx _]); first (simpl; set_solver).
        iIntros (ks) "Hks"...
        pose proof (int_of_vg_of_int_sem (g ^+ ρ)%g).
        eq_vg_of_int_l...
        eq_load_l... eq_store_l...
        eq_store_r...
        iMod (eq_pt_l_persist with "HdoneA") as "#HdoneA".
        iMod (eq_pt_l_persist with "Hmsg") as "#Hmsg".
        iMod (eq_pt_r_persist with "Hlx") as "#Hlx".
        iMod (eq_pt_r_persist with "Hlu") as "#Hlu".
        iApply eq_na_close_rule. iFrame "Hclose".
        iSplitR "Hka Hfa Hsa Hks".
        { iNext. iFrame "HB". iRight. iExists x, (g ^+ ρ)%g. iFrame "#". }
        (* F_CHAN leaks that Alice sent *)
        iApply (eq_env_call lls rls _ [HandleCtx _ _ _ _ _; AppRCtx _] [AppRCtx _] with "Hls [] [-]");
          [simpl; set_solver | simpl; set_solver | |].
        { iApply eq_lift_same. iExists #()%V, #()%V. iRight. repeat iSplit; try iPureIntro; done. }
        iIntros (w1 w2) "Hw". rewrite eq_lift_unit. iDestruct "Hw" as %[-> ->]...
        eq_cont_l...
        (* Alice's message to the aggregator *)
        iApply (eq_env_call lls rls _ [HandleCtx _ _ _ _ _; HandleCtx _ _ _ _ _; AppRCtx _] [AppRCtx _]
                 with "HsAC [] [-]");
          [simpl; set_solver | simpl; set_solver | iApply eq_lift_same; by iExists _ |].
        iIntros (w1 w2) "Hw". rewrite eq_lift_unit. iDestruct "Hw" as %[-> ->]...
        eq_cont_l. eq_cont_r... eq_cont_r.
        eq_exhaustion (fill k1 #()%V) (fill k2 #()%V);
          [set_unfold; tauto | set_unfold; tauto | by iApply "Hrel" | iApply "IH"].
      + (* Alice already gave her input *)
        iDestruct "HA1" as (x' r) "(#HdoneA & #Hmsg & #Hlx & #Hlu)".
        eq_load_l... eq_load_r...
        iApply eq_na_close_rule. iFrame "Hclose".
        iSplitR "Hka Hfa".
        { iNext. iFrame "HB". iRight. iExists x', r. iFrame "#". }
        eq_cont_l. eq_cont_r.
        eq_exhaustion (fill k1 #()%V) (fill k2 #()%V);
          [set_unfold; tauto | set_unfold; tauto | by iApply "Hrel" | iApply "IH"].
    - (* Bob's input *)
      apply NoDup_cons in Hndl as [Hn_add Hndl].
      apply NoDup_cons in Hndl as [Hn_srecv _].
      eq_handle_os kb fb as "Hkb" "Hfb"...
      destruct (vg_of_int_sem m) as [y|] eqn:Hm; last first.
      { eq_vg_of_int_none_l. eq_vg_of_int_none_r...
        eq_cont_l. eq_cont_r.
        eq_exhaustion (fill k1 #()%V) (fill k2 #()%V);
          [set_unfold; tauto | set_unfold; tauto | by iApply "Hrel" | iApply "IH"]. }
      eq_vg_of_int_l. eq_vg_of_int_r...
      iApply (eq_na_open _ _ addN); first (set_unfold; tauto).
      iFrame "Hinv".
      iIntros "[[HA [>HB0 | >HB1]] Hclose]".
      + (* Bob has not given an input yet *)
        iDestruct "HB0" as "(HdoneB & Hly)".
        eq_load_l... eq_load_r...
        iApply eq_na_close_rule. iFrame "Hclose".
        iSplitR "Hkb Hfb".
        { iNext. iFrame "HA". iLeft. iFrame. }
        (* Bob asks F_CHAN for [r]; the simulator forwards the env's decision *)
        iApply (eq_handle_os_l [] [HandleCtx _ _ _ _ _; CaseCtx _ _]); first (simpl; set_solver).
        iIntros (kr) "Hkr"...
        iApply (eq_handle_os_r [] [CaseCtx _ _]); first (simpl; set_solver).
        iIntros (sb) "Hsb"...
        iApply (eq_env_call lls rls _ [AppRCtx _] [AppRCtx _] with "Hlr [] [-]");
          [simpl; set_solver | simpl; set_solver | |].
        { iApply eq_lift_same. iExists #()%V, #()%V. iLeft. repeat iSplit; try iPureIntro; done. }
        iIntros (w1 w2) "Hw". iEval (rewrite eq_lift_sum) in "Hw".
        iDestruct "Hw" as (a1 a2) "[(-> & -> & Hu)|(-> & -> & Hu)]";
          iEval (rewrite eq_lift_unit) in "Hu"; iDestruct "Hu" as %[-> ->]...
        * (* [r] is not delivered *)
          eq_cont_l... eq_cont_l. eq_cont_r... eq_cont_r.
          eq_exhaustion (fill k1 #()%V) (fill k2 #()%V);
            [set_unfold; tauto | set_unfold; tauto | by iApply "Hrel" | iApply "IH"].
        * (* [r] is delivered, if Alice has sent it *)
          iApply (eq_na_open _ _ addN); first (set_unfold; tauto).
          iFrame "Hinv".
          iIntros "[[[>HA0 | >HA1] >HB] Hclose]".
          -- (* Alice has not sent [r] yet *)
             iDestruct "HA0" as "(HdoneA & Hmsg & Hlx & Hlu)".
             eq_load_l... eq_cont_l... eq_cont_r... eq_load_r...
             iApply eq_na_close_rule. iFrame "Hclose".
             iSplitL "HdoneA Hmsg Hlx Hlu HB".
             { iNext. iFrame "HB". iLeft. iFrame. }
             eq_cont_l. eq_cont_r.
             eq_exhaustion (fill k1 #()%V) (fill k2 #()%V);
               [set_unfold; tauto | set_unfold; tauto | by iApply "Hrel" | iApply "IH"].
          -- (* Bob sends [y · r^-1] *)
             iDestruct "HA1" as (x r) "(#HdoneA & #Hmsg & #Hlx & #Hlu)".
             iAssert (∃ (b : bool) v, doneB ↦ₗ #b ∗ ly ↦ᵣ v)%I with "[HB]" as (b v) "[HdoneB Hly]".
             { iDestruct "HB" as "[[? ?]|(% & ? & ?)]"; iExists _, _; iFrame. }
             eq_load_l... eq_cont_l... eq_store_l...
             eq_cont_r... eq_load_r... eq_store_r...
             iApply (eq_handle_os_r [] [AppRCtx _]); first (simpl; set_solver).
             iIntros (so) "Hso"...
             eq_load_r...
             rewrite add_mask_cancel.
             iApply eq_na_close_rule. iFrame "Hclose".
             iSplitL "HdoneB Hly".
             { iNext. iSplitR; [iRight; iExists x, r; iFrame "#" |]. iRight. iExists y. iFrame. }
             iApply (eq_env_call lls rls _ [HandleCtx _ _ _ _ _; HandleCtx _ _ _ _ _; AppRCtx _] [AppRCtx _]
                      with "HsBC [] [-]");
               [simpl; set_solver | simpl; set_solver | iApply eq_lift_same; by iExists _ |].
             iIntros (w1 w2) "Hw". rewrite eq_lift_unit. iDestruct "Hw" as %[-> ->]...
             eq_cont_l. eq_cont_r... eq_cont_r.
             eq_exhaustion (fill k1 #()%V) (fill k2 #()%V);
               [set_unfold; tauto | set_unfold; tauto | by iApply "Hrel" | iApply "IH"].
      + (* Bob already gave his input *)
        iDestruct "HB1" as (y') "(HdoneB & Hly)".
        eq_load_l... eq_load_r...
        iApply eq_na_close_rule. iFrame "Hclose".
        iSplitR "Hkb Hfb".
        { iNext. iFrame "HA". iRight. iExists y'. iFrame. }
        eq_cont_l. eq_cont_r.
        eq_exhaustion (fill k1 #()%V) (fill k2 #()%V);
          [set_unfold; tauto | set_unfold; tauto | by iApply "Hrel" | iApply "IH"].
  Qed.

  Lemma REAL_ADD_IDEAL_MS :
    ⊢ sem_typed [] REAL_ADD SIM_IDEAL_ADD ⊥ (𝟙 -{ ⟨⟩ }-[ MS ]-> τ_ADD)%T [].
  Proof using All. apply (EQ_sem_typed _ _ _ _ ADD_EQ Fwd). Qed.

  Lemma IDEAL_REAL_ADD_MS :
    ⊢ sem_typed [] SIM_IDEAL_ADD REAL_ADD ⊥ (𝟙 -{ ⟨⟩ }-[ MS ]-> τ_ADD)%T [].
  Proof using All. apply (EQ_sem_typed _ _ _ _ ADD_EQ Bwd). Qed.

End add_security.

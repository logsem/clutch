From iris.proofmode Require Import base proofmode classes.                                             
From iris.base_logic.lib Require Import  na_invariants.   
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode
  spec_rules spec_ra
  class_instances.
From clutch.prob_eff_lang.probblaze Require Import tactics.
From clutch.prob_eff_lang.probblaze Require Import sem_types sem_row sem_sig sem_judgement sem_def.
From iris.bi Require Import monpred.
From iris.proofmode Require Import monpred.
From clutch.prob_eff_lang.probblaze.examples Require Import ske ske_sec_chan_def ske_sec_chan_common.
From clutch.prob_eff_lang.probblaze.eq Require Import eq_logic eq_valgroup eq_finval eq_handlers eq_compat.


Import fingroup.

Import fingroup.fingroup.

Import valgroup_notation.
Import valgroup_tactics.


Section schan_ideal.
  Context `{probblazeRGS Σ}.
  Context {vg: val_group}.
  Context {cg: clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  #[local] Notation n := (S n'').
  (* message and cipher spaces: abstract *)
  Context {mt ct : fin_val_type}.
  Context {ms : @fin_val_type_struct mt} {cs : @fin_val_type_struct ct}.
  Context {msg : @fin_val Σ _ mt ms} {cipher : @fin_val Σ _ ct cs}.
  (* key space is valgroup *)
  Context {ske : @SYM_struct vg_fvt vg_fvts mt ms ct cs}.
  Context {SKE : @SYM Σ _ vg_fvt mt ct vg_fvts ms cs vg_fv msg cipher ske}.

  #[local] Notation sec_channel := (@sec_channel Σ mt).
  #[local] Notation skechan_thy := (@skechan_thy Σ mt).
  #[local] Notation τsc := (@τsc Σ _ mt ct ms cs msg cipher).
  #[local] Notation τsc_OS := (@τsc_OS Σ _ mt ct ms cs msg cipher).
  #[local] Notation SEM_TYPED_EFF := (@SEM_TYPED_EFF Σ _ mt ms msg).

  (* The client's row for this refinement.  Unlike the real/reduction games,
     the ideal side has NO key-exchange functionality, hence no [getKey] label:
     the left label list has five entries and the right one four. *)
  Lemma client_pers_mono_row (csend crecv lsend lrecv getKey1 ssend1 srecv1 ssend2 srecv2 : label) : ⊢ pers_mono_row (iLblSig_to_iLblThy [([csend; crecv; getKey1; srecv1; ssend1] , [lrecv; lsend; srecv2; ssend2] , sec_channel ssend1 ssend2 srecv1 srecv2)]).
  Proof.
    intros. unfold pers_mono_row. iIntros (????) "#HΦΦ'". iIntros (???) "(%H1 & H2)".
    iSplitR "H2"; [iPureIntro; apply H1 |].
    unfold keyleak in H1. simpl in H1. unfold keyleak_mono in H1. simpl in H1. apply list_elem_of_singleton in H1. simpl in H1.
    inversion H1. simpl in *.
    iDestruct "H2" as (?e1' ?e2' ?k1 ?k2 ?S) "H2e1e2".
    iExists e1', e2', k1, k2, S.
    iDestruct "H2e1e2" as "(%Hv1 & (%HNk1 & (%Hv2 & (%HNk2 & HS))))".
    repeat iSplit; try iPureIntro; try auto.
    - iDestruct "HS" as "(He1e2 & Hs1s2)". iApply "He1e2".
    - iDestruct "HS" as "(He1e2 & #Hs1s2)". iModIntro.
      iIntros (??) "HS". iApply "HΦΦ'". iApply "Hs1s2". iApply "HS".
  Qed.

  Program Definition client_row (csend crecv lsend lrecv getKey1 ssend1 srecv1 ssend2 srecv2 : label) := SemRow [([csend; crecv; getKey1; srecv1; ssend1], [lrecv; lsend; srecv2; ssend2], sec_channel ssend1 ssend2 srecv1 srecv2)] (client_pers_mono_row csend crecv lsend lrecv getKey1 ssend1 srecv1 ssend2 srecv2).

  (* The same row for the reversed refinement, where the ideal side -- with no
     key exchange, hence four labels -- is on the LEFT. *)
  Lemma client_pers_mono_row' (csend crecv lsend lrecv getKey1 ssend1 srecv1 ssend2 srecv2 : label) : ⊢ pers_mono_row (iLblSig_to_iLblThy [([lrecv; lsend; srecv1; ssend1] , [csend; crecv; getKey1; srecv2; ssend2] , sec_channel ssend1 ssend2 srecv1 srecv2)]).
  Proof.
    intros. unfold pers_mono_row. iIntros (????) "#HΦΦ'". iIntros (???) "(%H1 & H2)".
    iSplitR "H2"; [iPureIntro; apply H1 |].
    unfold keyleak in H1. simpl in H1. unfold keyleak_mono in H1. simpl in H1. apply list_elem_of_singleton in H1. simpl in H1.
    inversion H1. simpl in *.
    iDestruct "H2" as (?e1' ?e2' ?k1 ?k2 ?S) "H2e1e2".
    iExists e1', e2', k1, k2, S.
    iDestruct "H2e1e2" as "(%Hv1 & (%HNk1 & (%Hv2 & (%HNk2 & HS))))".
    repeat iSplit; try iPureIntro; try auto.
    - iDestruct "HS" as "(He1e2 & Hs1s2)". iApply "He1e2".
    - iDestruct "HS" as "(He1e2 & #Hs1s2)". iModIntro.
      iIntros (??) "HS". iApply "HΦΦ'". iApply "Hs1s2". iApply "HS".
  Qed.

  Program Definition client_row' (csend crecv lsend lrecv getKey1 ssend1 srecv1 ssend2 srecv2 : label) := SemRow [([lrecv; lsend; srecv1; ssend1], [csend; crecv; getKey1; srecv2; ssend2], sec_channel ssend1 ssend2 srecv1 srecv2)] (client_pers_mono_row' csend crecv lsend lrecv getKey1 ssend1 srecv1 ssend2 srecv2).

  (* [GAME2] is [l], the simulated ideal system [r].  The invariant has three
     states: nothing has happened; a valid send has started (the plaintext is
     recorded on both sides, [l] has cached a key and [r] has flipped its
     [started] flag); the ciphertext has been drawn and leaked, the same on
     both sides.  [l]'s key tape [γl] is never presampled and acts as the
     sender's exclusive token. *)
  Lemma GAME2_IDEAL_SKE_EQ :
    ⊢ EQ GAME2 ≈ SIM_IDEAL_SKE <|iLblSig_to_iLblThy (⊥ : sem_row Σ)|> {{ ⟪ 𝟙 -{ ⟨⟩ }-[ MS ]-> τsc ⟫ }}.
  Proof using All with (eq_pures'; repeat foldkont).
    iApply eq_value. iModIntro. iModIntro.
    iApply eq_lift_arr. iIntros (u1 u2) "Hu". rewrite eq_lift_unit. iDestruct "Hu" as %[-> ->].
    rewrite /GAME2 /SIM_IDEAL_SKE /SIM_SKE /IDEAL_SKE /C_ENC_ideal /enc_ideal /RED_CHAN_sess /func_comp /parallel_composition...
    (* Setup: [r] (sc_ideal) F_CHAN's state, the simulator's ciphertext cell
       and its [started] flag; [l] (game2) RED_CHAN, F_OAUTH, F_KE. *)
    eq_alloc_r lmr as "Hlmr"...
    eq_alloc_r lamr as "Hlamr"...
    eq_alloc_r lstr as "Hlstr"...
    eq_alloc_l lml as "Hlml"...
    eq_alloc_l laml as "Hlaml"...
    eq_alloctape_l γl as "Hγl"...
    eq_alloc_l lcl as "Hlcl".
    rewrite Nat2Z.id.
    set (I0 := (lml ↦ₗ NONEV ∗ lcl ↦ₗ NONEV ∗ laml ↦ₗ NONEV ∗ lmr ↦ᵣ NONEV ∗ lstr ↦ᵣ NONEV ∗ lamr ↦ᵣ NONEV
                ∗ γl ↪ₗN (n; []))%I : iPropD Σ).
    set (I1 := (∃ (mv : mt) (c : nat), lml ↦ₗ□ SOMEV (fvtval mv) ∗ lcl ↦ₗ□ SOMEV #c ∗ laml ↦ₗ NONEV ∗
                  lmr ↦ᵣ□ SOMEV (fvtval mv) ∗ lstr ↦ᵣ□ SOMEV #()%V ∗ lamr ↦ᵣ NONEV)%I : iPropD Σ).
    set (I2 := (∃ (mv : mt) (c : nat) (cph : ct), lml ↦ₗ□ SOMEV (fvtval mv) ∗ lcl ↦ₗ□ SOMEV #c ∗
                  laml ↦ₗ□ SOMEV (fvtval cph) ∗ lmr ↦ᵣ□ SOMEV (fvtval mv) ∗ lstr ↦ᵣ□ SOMEV #()%V ∗
                  lamr ↦ᵣ□ SOMEV (fvtval cph) ∗ γl ↪ₗ□N (n; []))%I : iPropD Σ).
    iApply (eq_na_alloc (I0 ∨ I1 ∨ I2) alphaN).
    iSplitL "Hlml Hlcl Hlaml Hlmr Hlstr Hlamr Hγl"; [iNext; iLeft; iFrame|].
    iIntros "#HI"...
    (* One call: a client and its effect handlers *)
    iApply eq_value. iModIntro. iEval (rewrite eq_lift_forall). iIntros (θL). iModIntro.
    iApply eq_lift_arr. iIntros (f1 f2) "Hff"...
    iApply eq_value. iModIntro. iEval (rewrite eq_lift_forall). iIntros (autheff).
    iEval (rewrite eq_lift_forall). iIntros (keyeff).
    iApply eq_lift_arr. iIntros (ak_l ak_r) "Hauthkey".
    iEval (rewrite eq_lift_prod) in "Hauthkey".
    iDestruct "Hauthkey" as (w1 w1' w2 w2') "(-> & -> & Hautheff & Hkeyeff)"...
    iEval (rewrite eq_lift_prod) in "Hautheff".
    iDestruct "Hautheff" as (asnd_l asnd_r arcv_l arcv_r) "(-> & -> & #Hasnd & #Harcv)"...
    iEval (rewrite eq_lift_prod) in "Hkeyeff".
    iDestruct "Hkeyeff" as (kysnd_l kysnd_r kyrcv_l kyrcv_r) "(-> & -> & #Hkeysnd & #Hkeyrcv)"...
    (* Per-call effect labels *)
    eq_effect_l gkl as "Hgkl"...
    eq_effect_l sl as "Hsl"...
    eq_effect_l rl as "Hrl"...
    eq_effect_l ssl as "Hssl"...
    eq_effect_l srl as "Hsrl"...
    eq_effect_r lsr as "Hlsr"...
    eq_effect_r lrr as "Hlrr"...
    eq_effect_r ssr as "Hssr"...
    eq_effect_r srr as "Hsrr"...
    set (lls := [sl; rl; gkl; srl; ssl]).
    set (rls := [lrr; lsr; srr; ssr]).
    (* The client's row: the secure channel, with the labels of the program
       on the left. *)
    set (θc := λ d, pick d (client_row sl rl lsr lrr gkl ssl srl ssr srr)
                           (client_row' sl rl lsr lrr gkl ssr srr ssl srl)).
    iApply eq_new_theory.
    iApply eq_add_label_l. iFrame "Hssl".
    iApply eq_add_label_l. iFrame "Hsrl".
    iApply eq_add_label_l. iFrame "Hgkl".
    iApply eq_add_label_l. iFrame "Hrl".
    iApply eq_add_label_l. iFrame "Hsl".
    iApply eq_add_label_r. iFrame "Hssr".
    iApply eq_add_label_r. iFrame "Hsrr".
    iApply eq_add_label_r. iFrame "Hlsr".
    iApply eq_add_label_r. iFrame "Hlrr".
    iApply eq_learn_nodup. iIntros ([Hnd_l Hnd_r]).
    eq_reshape_l (f1 _). eq_reshape_r (f2 _).
    iApply (eq_exhaustion _ _ _ _ (skechan_thy ssl ssr srl srr) with "[Hff]");
      [set_unfold; tauto | set_unfold; tauto | |].
    { iApply (eq_thy_mono _ _ (EqThy (λ d, iLblSig_to_iLblThy (sem_row_union (θc d) θL)))).
      { intros []; rewrite /θc /skechan_thy /lls /rls /pick /=; iApply to_iThy_le_intro'; simpl;
          apply submseteq_skip; unfold sem_row_union;
          repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app);
          solve_submseteq. }
      iApply (eq_lift_forall_app _ _ _ θc with "Hff").
      iApply eq_lift_dep_intro. intros []; rewrite /θc /pick /=.
      - iPoseProof (SEM_TYPED_EFF _ _ _ _ _ _ (client_pers_mono_row _ _ _ _ _ _ _ _ _)) as "H".
        unfold sem_val_typed. simpl. iDestruct "H" as "#H". iApply "H".
      - iPoseProof (SEM_TYPED_EFF _ _ _ _ _ _ (client_pers_mono_row' _ _ _ _ _ _ _ _ _)) as "H".
        unfold sem_val_typed. simpl. iDestruct "H" as "#H". iApply "H". }
    iLöb as "IH".
    iSplit.
    { iIntros "!>" (vl vr) "Hv". rewrite eq_lift_unit. iDestruct "Hv" as %[-> ->].
      eq_pures_l. eq_pures_r. iApply eq_value. iModIntro. by rewrite eq_lift_unit. }
    iIntros "!>" (k1' k2' e1 e2 Q) "%Hk1 %Hk2 HXQ #Hrel".
    iDestruct (skechan_thy_app (mt := mt) with "HXQ") as "[(%m & %Hm' & HQ) | (%Hrecv & HQ)]".
    (* Alice tries to send a message m *)
    - destruct Hm' as [-> ->].
      eq_handle_os rssl rssr as "Hssl" "Hssr"...
      destruct (fvt_of_int_sem (fin_val := msg) m) as [mv|] eqn:Hmv.
      2: { eq_lift_l (brel_fvt_of_int_none_l (fin_val := msg)) (brel_fvt_of_int_none_r (fin_val := msg)).
           eq_lift_r (brel_fvt_of_int_none_l (fin_val := msg)) (brel_fvt_of_int_none_r (fin_val := msg))...
           eq_cont_l. eq_cont_r.
           eq_exhaustion (fill k1' #()%V) (fill k2' #()%V) with "[HQ]";
             [set_solver|set_solver|by iApply "Hrel"|iApply "IH"]. }
      eq_fvt_of_int_l Hmv. eq_fvt_of_int_r Hmv...
      iApply (eq_na_open _ _ alphaN); first set_solver.
      iFrame "HI".
      iIntros "[>[(Hlml&Hlcl&Hlaml&Hlmr&Hlstr&Hlamr&Hγl)|[H2|H3]] Hclose]".
      + (* the first valid send *)
        eq_load_l... eq_load_r... eq_store_l... eq_store_r...
        eq_handle_os_r_in [HandleCtx _ _ _ _ _; AppRCtx _].
        { simpl. rewrite !NoDup_cons in Hnd_r. set_unfold. tauto. }
        iIntros (rlsr) "Hlsr"...
        eq_store_r...
        (* [l] enters F_KE's [getKey] handler and takes the key sample, which
           is never used: the tape is never presampled. *)
        eq_handle_os_l_in [HandleCtx _ _ _ _ _; HandleCtx _ _ _ _ _; HandleCtx _ _ _ _ _; AppRCtx _].
        { eapply NoDup_cons_1_1. simpl.
          eapply (submseteq_NoDup _ [sl; rl; gkl; srl; ssl]); [solve_submseteq|exact Hnd_l]. }
        iIntros (rgkl) "Hrgkl"...
        eq_load_l...
        eq_reshape_l (rand(#lbl:γl) #_)%E.
        iApply eq_rand_empty_l. iFrame "Hγl". iIntros (c) "Hγl %Hc"...
        eq_store_l...
        iMod (eq_pt_l_persist with "Hlml") as "#Hlml".
        iMod (eq_pt_l_persist with "Hlcl") as "#Hlcl".
        iMod (eq_pt_r_persist with "Hlmr") as "#Hlmr".
        iMod (eq_pt_r_persist with "Hlstr") as "#Hlstr".
        iApply eq_na_close_rule. iFrame "Hclose".
        iSplitL "Hlaml Hlamr".
        { iNext. iRight. iLeft. iExists _, _. iFrame "∗#". }
        (* The two key leaks, send(bob) then recv(bob), in lockstep. *)
        eq_reshape_l (kysnd_l _). eq_reshape_r (kysnd_r _).
        iApply (eq_env_call_gen lls rls (λ _, iThyBot) _ _ with "Hkeysnd [] [-]");
          [set_unfold; tauto | set_unfold; tauto | | |].
        { intros []; rewrite /lls /rls /pick /=; iApply to_iThy_le_intro'; unfold sem_row_union;
            repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app); solve_submseteq. }
        { iApply eq_lift_same. iExists _, _. by iLeft. }
        iIntros (v1 v2) "Hv". rewrite eq_lift_unit. iDestruct "Hv" as %[-> ->]...
        eq_reshape_l (kyrcv_l _). eq_reshape_r (kyrcv_r _).
        iApply (eq_env_call_gen lls rls (λ _, iThyBot) _ _ with "Hkeyrcv [] [-]");
          [set_unfold; tauto | set_unfold; tauto | | |].
        { intros []; rewrite /lls /rls /pick /=; iApply to_iThy_le_intro'; unfold sem_row_union;
            repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app); solve_submseteq. }
        { iApply eq_lift_same. iExists _, _. by iLeft. }
        iIntros (v1' v2') "Hv". iEval (rewrite eq_lift_sum) in "Hv".
        iDestruct "Hv" as (a1 a2) "[(-> & -> & Hu)|(-> & -> & Hu)]";
          iEval (rewrite eq_lift_unit) in "Hu"; iDestruct "Hu" as %[-> ->]...
        (* Key establishment failed: neither side produces a ciphertext. *)
        { eq_cont_l... eq_cont_l. eq_cont_r... eq_cont_r...
          eq_exhaustion (fill k1' #()%V) (fill k2' #()%V) with "[HQ]";
            [set_solver|set_solver|by iApply "Hrel"|iApply "IH"]. }
        eq_cont_l...
        iApply (eq_na_open _ _ alphaN); first set_solver.
        iFrame "HI".
        iIntros "[>[(_&_&_&_&_&_&Hγl')|[(%&%&_&_&Hlaml&_&_&Hlamr)|(%&%&%&_&_&_&_&_&_&Hγl')]] Hclose]".
        (* We still hold the key tape, so the invariant cannot have moved. *)
        { iExFalso. iApply (eq_tp_l_excl with "Hγl Hγl'"). }
        2: { iExFalso. iApply (eq_tp_l_excl with "Hγl Hγl'"). }
        eq_load_r...
        (* Both sides draw a ciphertext; the draws are coupled. *)
        eq_reshape_l (rand_cipher #()%V). eq_reshape_r (rand_cipher #()%V).
        iApply (eq_rand_cipher_coupl (ske := SKE)).
        iIntros (cph)...
        eq_handle_os_l_in [HandleCtx _ _ _ _ _; AppRCtx _].
        { simpl. rewrite !NoDup_cons in Hnd_l. set_unfold. tauto. }
        iIntros (rsl) "Hsl"...
        eq_load_l... eq_store_l... eq_store_r...
        iMod (eq_pt_l_persist with "Hlaml") as "#Hlaml".
        iMod (eq_pt_r_persist with "Hlamr") as "#Hlamr".
        iMod (eq_tp_l_persist with "Hγl") as "#Hγl".
        iApply eq_na_close_rule. iFrame "Hclose".
        iSplitR; [iNext; do 2 iRight; iExists _, _, _; iFrame "#"|].
        (* Both sides leak the same ciphertext on the authenticated channel. *)
        eq_reshape_l (asnd_l _). eq_reshape_r (asnd_r _).
        iApply (eq_env_call_gen lls rls (λ _, iThyBot) _ _ with "Hasnd [] [-]");
          [set_unfold; tauto | set_unfold; tauto | | |].
        { intros []; rewrite /lls /rls /pick /=; iApply to_iThy_le_intro'; unfold sem_row_union;
            repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app); solve_submseteq. }
        { iApply eq_lift_same. iExists _, _, _, _.
          repeat (iSplit; first done).
          iSplit; last (iExists _, _; by iLeft).
          by iExists _. }
        iIntros (v1'' v2'') "Hv". rewrite eq_lift_unit. iDestruct "Hv" as %[-> ->]...
        eq_cont_l... eq_cont_l. eq_cont_r... eq_cont_r...
        eq_exhaustion (fill k1' #()%V) (fill k2' #()%V) with "[HQ]";
          [set_solver|set_solver|by iApply "Hrel"|iApply "IH"].
      + (* a send is already in flight or has failed *)
        iDestruct "H2" as "(%&%&#Hlml&#Hlcl&Hlaml&#Hlmr&#Hlstr&Hlamr)".
        eq_load_l... eq_load_r...
        iApply eq_na_close_rule. iFrame "Hclose".
        iSplitR "HQ Hssl Hssr"; [iNext; iRight; iLeft; iExists _, _; iFrame "∗#"|].
        eq_cont_l. eq_cont_r...
        eq_exhaustion (fill k1' #()%V) (fill k2' #()%V) with "[HQ]";
          [set_solver|set_solver|by iApply "Hrel"|iApply "IH"].
      + (* the ciphertext has already been leaked *)
        iDestruct "H3" as "(%&%&%&#Hlml&#Hlcl&#Hlaml&#Hlmr&#Hlstr&#Hlamr&#Hγl)".
        eq_load_l... eq_load_r...
        iApply eq_na_close_rule. iFrame "Hclose".
        iSplitR "HQ Hssl Hssr"; [iNext; iRight; iRight; iExists _, _, _; iFrame "#"|].
        eq_cont_l. eq_cont_r...
        eq_exhaustion (fill k1' #()%V) (fill k2' #()%V) with "[HQ]";
          [set_solver|set_solver|by iApply "Hrel"|iApply "IH"].
    (* Bob tries to receive a message *)
    - destruct Hrecv as [-> ->]...
      eq_handle_os_in ([HandleCtx _ _ _ _ _] ++ k1') ([HandleCtx _ _ _ _ _] ++ k2').
      { apply not_elem_of_cons; split; last (apply neutral_ectx; repeat constructor).
        intro Heq.
        apply NoDup_ListNoDup in Hnd_l.
        do 4 (apply NoDup_cons_iff in Hnd_l as [?Hn Hnd_l]).
        apply Hn2. by left. }
      { apply not_elem_of_cons; split; last (apply neutral_ectx; repeat constructor).
        intro Heq.
        apply NoDup_ListNoDup in Hnd_r.
        do 3 (apply NoDup_cons_iff in Hnd_r as [?Hn Hnd_r]).
        apply Hn1. by left. }
      iIntros "!>" (rsrl rsrr) "Hsrl Hsrr"...
      eq_handle_os_r_in [HandleCtx _ _ _ _ _; AppRCtx _].
      { simpl. rewrite !NoDup_cons in Hnd_r. set_unfold. tauto. }
      iIntros (rlrr) "Hlrr"...
      repeat foldkont.
      eq_handle_os_l_in [HandleCtx _ _ _ _ _; HandleCtx _ _ _ _ _; AppRCtx _].
      { eapply NoDup_cons_1_1. simpl.
        eapply (submseteq_NoDup _ [sl; rl; gkl; srl; ssl]); [solve_submseteq|exact Hnd_l]. }
      iIntros (rgkl) "Hrgkl"...
      (* key leaks, this time recv(alice) then send(alice) *)
      eq_reshape_l (kyrcv_l _). eq_reshape_r (kyrcv_r _).
      iApply (eq_env_call_gen lls rls (λ _, iThyBot) _ _ with "Hkeyrcv [] [-]");
        [set_unfold; tauto | set_unfold; tauto | | |].
      { intros []; rewrite /lls /rls /pick /=; iApply to_iThy_le_intro'; unfold sem_row_union;
          repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app); solve_submseteq. }
      { iApply eq_lift_same. iExists _, _. by iRight. }
      iIntros (v1' v2') "Hv". iEval (rewrite eq_lift_sum) in "Hv".
      iDestruct "Hv" as (a1 a2) "[(-> & -> & Hu)|(-> & -> & Hu)]";
        iEval (rewrite eq_lift_unit) in "Hu"; iDestruct "Hu" as %[-> ->]...
      { eq_cont_l. eq_cont_r... eq_cont_l. eq_cont_r...
        eq_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"; [set_solver|set_solver|iApply "Hrel"|iApply "IH"].
        iDestruct "HQ" as "[_ $]". }
      eq_reshape_l (kysnd_l _). eq_reshape_r (kysnd_r _).
      iApply (eq_env_call_gen lls rls (λ _, iThyBot) _ _ with "Hkeysnd [] [-]");
        [set_unfold; tauto | set_unfold; tauto | | |].
      { intros []; rewrite /lls /rls /pick /=; iApply to_iThy_le_intro'; unfold sem_row_union;
          repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app); solve_submseteq. }
      { iApply eq_lift_same. iExists _, _. by iRight. }
      iIntros (v1 v2) "Hv". rewrite eq_lift_unit. iDestruct "Hv" as %[-> ->]...
      (* Both sides consult their guard: [lcl] in [l], [started] in [r]. *)
      iApply (eq_na_open _ _ alphaN); first set_solver.
      iFrame "HI".
      iIntros "[>[(Hlml&Hlcl&Hlaml&Hlmr&Hlstr&Hlamr&Hγl)|[H2|H3]] Hclose]".
      + (* no send has started: both answer NONE *)
        eq_load_l... eq_load_r...
        eq_cont_l. eq_cont_r... eq_cont_l. eq_cont_r...
        iApply eq_na_close_rule. iFrame "Hclose".
        iSplitR "HQ"; [iNext; iLeft; iFrame|].
        eq_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"; [set_solver|set_solver|iApply "Hrel"|iApply "IH"].
        iDestruct "HQ" as "[_ $]".
      + (* a send has started but nothing was leaked *)
        iDestruct "H2" as "(%&%&#Hlml&#Hlcl&Hlaml&#Hlmr&#Hlstr&Hlamr)".
        eq_load_l... eq_load_r...
        eq_cont_l...
        eq_handle_os_l_in [HandleCtx _ _ _ _ _; AppRCtx _].
        { apply not_elem_of_cons; split;
            last (first [ solve [apply neutral_ectx; repeat constructor]
                        | solve [rewrite /frame_label /=; set_solver]
                        | solve [cbv [frame_label]; simpl; set_solver] ]).
          intro Heq. subst rl.
          apply NoDup_ListNoDup in Hnd_l.
          apply NoDup_cons_iff in Hnd_l as [Hn _].
          apply Hn. by left. }
        iIntros (rrl) "Hrl"...
        iApply eq_na_close_rule. iFrame "Hclose".
        iSplitR "HQ Hsrl Hrl Hsrr Hlrr"; [iNext; iRight; iLeft; iExists _, _; iFrame "∗#"|].
        eq_reshape_l (arcv_l _). eq_reshape_r (arcv_r _).
        iApply (eq_env_call_gen lls rls (λ _, iThyBot) _ _ with "Harcv [] [-]");
          [set_unfold; tauto | set_unfold; tauto | | |].
        { intros []; rewrite /lls /rls /pick /=; iApply to_iThy_le_intro'; unfold sem_row_union;
            repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app); solve_submseteq. }
        { iApply eq_lift_same. iExists _, _; by iLeft. }
        iIntros (w1 w2) "Hv". iEval (rewrite eq_lift_sum) in "Hv".
        iDestruct "Hv" as (a1 a2) "[(-> & -> & Hu)|(-> & -> & Hu)]";
          iEval (rewrite eq_lift_unit) in "Hu"; iDestruct "Hu" as %[-> ->]...
        { eq_cont_l. eq_cont_r... eq_cont_l. eq_cont_r...
          eq_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"; [set_solver|set_solver|iApply "Hrel"|iApply "IH"].
          iDestruct "HQ" as "[_ $]". }
        iApply (eq_na_open _ _ alphaN); first set_solver.
        iFrame "HI".
        iIntros "[>[(Hlml'&H')|[H2'|H3']] Hclose]".
        (* [lml] already holds the message, so the first state is impossible. *)
        { iExFalso. iApply (eq_pt_l_excl with "Hlml' Hlml"). }
        * iDestruct "H2'" as "(%&%&_&_&HlamlI&_&_&HlamrI)".
          eq_load_l... eq_load_r...
          eq_cont_l. eq_cont_r... eq_cont_l. eq_cont_r...
          iApply eq_na_close_rule. iFrame "Hclose".
          iSplitR "HQ"; [iNext; iRight; iLeft; iExists _, _; iFrame "∗#"|].
          eq_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"; [set_solver|set_solver|iApply "Hrel"|iApply "IH"].
          iDestruct "HQ" as "[_ $]".
        * iDestruct "H3'" as "(%&%&%&#Hlml2&#Hlcl2&#Hlaml2&#Hlmr2&#Hlstr2&#Hlamr2&#Hγl2)".
          eq_load_l... eq_load_r...
          eq_cont_l. eq_cont_r...
          eq_load_l... eq_load_r...
          eq_cont_l. eq_cont_r...
          iApply eq_na_close_rule. iFrame "Hclose".
          iSplitR "HQ"; [iNext; iRight; iRight; iExists _, _, _; iFrame "#"|].
          eq_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"; [set_solver|set_solver|iApply "Hrel"|iApply "IH"].
          iDestruct "HQ" as "[HQ _]". iApply "HQ".
      + (* the ciphertext has been leaked *)
        iDestruct "H3" as "(%&%&%&#Hlml&#Hlcl&#Hlaml&#Hlmr&#Hlstr&#Hlamr&#Hγl)".
        eq_load_l... eq_load_r...
        eq_cont_l...
        eq_handle_os_l_in [HandleCtx _ _ _ _ _; AppRCtx _].
        { apply not_elem_of_cons; split;
            last (first [ solve [apply neutral_ectx; repeat constructor]
                        | solve [rewrite /frame_label /=; set_solver]
                        | solve [cbv [frame_label]; simpl; set_solver] ]).
          intro Heq. subst rl.
          apply NoDup_ListNoDup in Hnd_l.
          apply NoDup_cons_iff in Hnd_l as [Hn _].
          apply Hn. by left. }
        iIntros (rrl) "Hrl"...
        iApply eq_na_close_rule. iFrame "Hclose".
        iSplitR "HQ Hsrl Hrl Hsrr Hlrr"; [iNext; iRight; iRight; iExists _, _, _; iFrame "#"|].
        eq_reshape_l (arcv_l _). eq_reshape_r (arcv_r _).
        iApply (eq_env_call_gen lls rls (λ _, iThyBot) _ _ with "Harcv [] [-]");
          [set_unfold; tauto | set_unfold; tauto | | |].
        { intros []; rewrite /lls /rls /pick /=; iApply to_iThy_le_intro'; unfold sem_row_union;
            repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app); solve_submseteq. }
        { iApply eq_lift_same. iExists _, _; by iLeft. }
        iIntros (w1 w2) "Hv". iEval (rewrite eq_lift_sum) in "Hv".
        iDestruct "Hv" as (a1 a2) "[(-> & -> & Hu)|(-> & -> & Hu)]";
          iEval (rewrite eq_lift_unit) in "Hu"; iDestruct "Hu" as %[-> ->]...
        { eq_cont_l. eq_cont_r... eq_cont_l. eq_cont_r...
          eq_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"; [set_solver|set_solver|iApply "Hrel"|iApply "IH"].
          iDestruct "HQ" as "[_ $]". }
        iApply (eq_na_open _ _ alphaN); first set_solver.
        iFrame "HI".
        iIntros "[>[(Hlml'&H')|[H2'|H3']] Hclose]".
        (* [lml] already holds the message, so the first state is impossible. *)
        { iExFalso. iApply (eq_pt_l_excl with "Hlml' Hlml"). }
        * iDestruct "H2'" as "(%&%&_&_&HlamlI&_&_&HlamrI)".
          eq_load_l... eq_load_r...
          iApply eq_na_close_rule. iFrame "Hclose".
          iSplitR "HQ Hsrl Hrl Hsrr Hlrr"; [iNext; iRight; iLeft; iExists _, _; iFrame "∗#"|].
          eq_cont_l. eq_cont_r...
          eq_load_l... eq_load_r...
          eq_cont_l. eq_cont_r...
          eq_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"; [set_solver|set_solver|iApply "Hrel"|iApply "IH"].
          iDestruct "HQ" as "[HQ _]". iApply "HQ".
        * iDestruct "H3'" as "(%&%&%&#Hlml2&#Hlcl2&#Hlaml2&#Hlmr2&#Hlstr2&#Hlamr2&#Hγl2)".
          eq_load_l... eq_load_r...
          eq_cont_l. eq_cont_r...
          eq_load_l... eq_load_r...
          eq_cont_l. eq_cont_r...
          iApply eq_na_close_rule. iFrame "Hclose".
          iSplitR "HQ"; [iNext; iRight; iRight; iExists _, _, _; iFrame "#"|].
          eq_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"; [set_solver|set_solver|iApply "Hrel"|iApply "IH"].
          iDestruct "HQ" as "[HQ _]". iApply "HQ".
  Qed.

  Lemma GAME2_IDEAL_SKE_MS :
    ⊢ sem_typed [] GAME2 SIM_IDEAL_SKE ⊥ (𝟙 -{ ⟨⟩ }-[ MS ]-> τsc)%T [].
  Proof using All. apply (EQ_sem_typed _ _ _ _ GAME2_IDEAL_SKE_EQ Fwd). Qed.

  Lemma IDEAL_SKE_GAME2_MS :
    ⊢ sem_typed [] SIM_IDEAL_SKE GAME2 ⊥ (𝟙 -{ ⟨⟩ }-[ MS ]-> τsc)%T [].
  Proof using All. apply (EQ_sem_typed _ _ _ _ GAME2_IDEAL_SKE_EQ Bwd). Qed.

  (* One-shot versions, the shape the composition operators expect *)
End schan_ideal.

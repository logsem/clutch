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


Section schan_security.
  Context `{probblazeRGS Σ}.
  Context {vg: val_group}.
  Context {cg: clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  #[local] Notation n := (S n'').
  (* message and cipher spaces: abstract *)
  Context {mt ct : fin_val_type}.
  Context {ms : @fin_val_type_struct mt} {cs : @fin_val_type_struct ct}.
  (* key space is valgroup *)
  Context {ske : @SYM_struct vg_fvt vg_fvts mt ms ct cs}.
  (* the semantic side of the scheme: the key space is [vg_fv], the message and
     cipher spaces are abstract.  [enc_sem]/[dec_sem] take and return VALUES of
     those spaces, so nothing below ever decodes a key or a message. *)
  Context {msg : @fin_val Σ _ mt ms} {cipher : @fin_val Σ _ ct cs}.
  Context {SKE : @SYM Σ _ vg_fvt mt ct vg_fvts ms cs vg_fv msg cipher ske}.

  #[local] Notation sec_channel := (@sec_channel Σ mt).
  #[local] Notation skechan_thy := (@skechan_thy Σ mt).
  #[local] Notation τsc := (@τsc Σ _ mt ct ms cs msg cipher).
  #[local] Notation τsc_OS := (@τsc_OS Σ _ mt ct ms cs msg cipher).
  #[local] Notation SEM_TYPED_EFF := (@SEM_TYPED_EFF Σ _ mt ms msg).


  Lemma client_pers_mono_row (csend crecv lsend lrecv getKey1 getKey2 ssend1 srecv1 ssend2 srecv2 : label) : ⊢ pers_mono_row (iLblSig_to_iLblThy [([csend; crecv; getKey1; srecv1; ssend1] , [lrecv; lsend; getKey2; srecv2; ssend2] , sec_channel ssend1 ssend2 srecv1 srecv2)]).
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

  Lemma client_pers_mono_row' (csend crecv lsend lrecv getKey1 getKey2 ssend1 srecv1 ssend2 srecv2 : label) : ⊢ pers_mono_row (iLblSig_to_iLblThy [([lrecv; lsend; getKey2; srecv1; ssend1] , [csend; crecv; getKey1; srecv2; ssend2] , sec_channel ssend1 ssend2 srecv1 srecv2)]).
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

  Program Definition client_row (csend crecv lsend lrecv getKey1 getKey2 ssend1 srecv1 ssend2 srecv2 : label) := SemRow [([csend; crecv; getKey1; srecv1; ssend1], [lrecv; lsend; getKey2; srecv2; ssend2], sec_channel ssend1 ssend2 srecv1 srecv2)] (client_pers_mono_row csend crecv lsend lrecv getKey1 getKey2 ssend1 srecv1 ssend2 srecv2).

  Program Definition client_row' (csend crecv lsend lrecv getKey1 getKey2 ssend1 srecv1 ssend2 srecv2 : label) := SemRow [([lrecv; lsend; getKey2; srecv1; ssend1], [csend; crecv; getKey1; srecv2; ssend2], sec_channel ssend1 ssend2 srecv1 srecv2)] (client_pers_mono_row' csend crecv lsend lrecv getKey1 getKey2 ssend1 srecv1 ssend2 srecv2).

  (* [REAL_SKE] is [l], [GAME1] is [r].  [l]'s exponent tape [γl] and [r]'s
     key tape [ι] are coupled along [keyf], so both sides encrypt under the
     same key. *)
  Lemma REAL_SKE_GAME1_EQ :
    ⊢ EQ REAL_SKE ≈ GAME1 <|iLblSig_to_iLblThy (⊥ : sem_row Σ)|> {{ ⟪ 𝟙 -{ ⟨⟩ }-[ MS ]-> τsc ⟫ }}.
  Proof using All with (eq_pures'; repeat foldkont).
    iApply eq_value. iModIntro. iModIntro.
    iApply eq_lift_arr. iIntros (u1 u2) "Hu". rewrite eq_lift_unit. iDestruct "Hu" as %[-> ->].
    rewrite /GAME1 /REAL_SKE /C_ENC_real /RED_CHAN_sess /parallel_composition /enc_real_tape /func_comp...
    (* Setup, shared by all calls: [l] (sc_real) CHAN, F_OAUTH, F_KE; [r]
       (game1) the encryption scheme, RED_CHAN, F_OAUTH, F_KE. *)
    eq_alloc_l lml as "Hlml"...
    eq_alloc_l laml as "Hlaml"...
    eq_alloctape_l γl as "Hγl"...
    eq_alloc_l lcl as "Hlcl"...
    eq_alloctape_r ι as "Hι"...
    eq_alloc_r lmr as "Hlmr"...
    eq_alloc_r lamr as "Hlamr"...
    eq_alloctape_r γr as "Hγr"...
    eq_alloc_r lcr as "Hlcr".
    rewrite vg_fvt_card. assert (S n - 1 = n)%Z as -> by lia.
    rewrite Nat2Z.id.
    iMod (eq_tp_r_persist with "Hγr") as "#Hγr".
    iApply (eq_couple_tapes_bij _ n keyf); first apply keyf_dom.
    iFrame "Hγl Hι". iIntros (x Hx) "[Hγl Hι] /=".
    set (I1 := (lml ↦ₗ NONEV ∗ lcl ↦ₗ NONEV ∗ lmr ↦ᵣ NONEV ∗ lcr ↦ᵣ NONEV ∗ laml ↦ₗ NONEV ∗ lamr ↦ᵣ NONEV
                ∗ γl ↪ₗN (n; [x]) ∗ ι ↪ᵣN (n; [keyf x]))%I : iPropD Σ).
    set (I2 := (∃ (c' : nat) (mv : mt), lml ↦ₗ□ SOMEV (fvtval mv) ∗ lcl ↦ₗ□ SOMEV #x ∗
                  lmr ↦ᵣ□ SOMEV (fvtval mv) ∗ lcr ↦ᵣ□ SOMEV #c' ∗ laml ↦ₗ NONEV ∗ lamr ↦ᵣ NONEV ∗
                  γl ↪ₗ□N (n; []))%I : iPropD Σ).
    set (I3 := (∃ (c' : nat) (mv : mt) (cv : ct), ⎡□ P (key := vg_fv) (g ^+ x)%g mv cv⎤ ∗
                  lml ↦ₗ□ SOMEV (fvtval mv) ∗ lcl ↦ₗ□ SOMEV #x ∗ lmr ↦ᵣ□ SOMEV (fvtval mv) ∗ lcr ↦ᵣ□ SOMEV #c' ∗
                  laml ↦ₗ□ SOMEV (fvtval cv) ∗ lamr ↦ᵣ□ SOMEV (fvtval cv) ∗
                  γl ↪ₗ□N (n; []) ∗ ι ↪ᵣ□N (n; []))%I : iPropD Σ).
    iApply (eq_na_alloc (I1 ∨ I2 ∨ I3) alphaN).
    iSplitL "Hlml Hlmr Hlcl Hlcr Hγl Hι Hlaml Hlamr"; [iNext; iLeft; iFrame|].
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
    (* Allocation/initialization *)
    eq_effect_l gkl as "Hgkl". eq_effect_r gkr as "Hgkr"...
    eq_effect_l sl as "Hsl". eq_effect_r sr as "Hsr"...
    eq_effect_l rl as "Hrl". eq_effect_r rr as "Hrr"...
    eq_effect_l ssl as "Hssl". eq_effect_r ssr as "Hssr"...
    eq_effect_l srl as "Hsrl". eq_effect_r srr as "Hsrr"...
    set (lls := [sl; rl; gkl; srl; ssl]).
    set (rls := [rr; sr; gkr; srr; ssr]).
    (* The client's row: the secure channel, with the labels of the program
       on the left. *)
    set (θc := λ d, pick d (client_row sl rl sr rr gkl gkr ssl srl ssr srr)
                           (client_row' sl rl sr rr gkl gkr ssr srr ssl srl)).
    iApply eq_new_theory.
    iApply eq_add_label_l. iFrame "Hssl".
    iApply eq_add_label_l. iFrame "Hsrl".
    iApply eq_add_label_l. iFrame "Hgkl".
    iApply eq_add_label_l. iFrame "Hrl".
    iApply eq_add_label_l. iFrame "Hsl".
    iApply eq_add_label_r. iFrame "Hssr".
    iApply eq_add_label_r. iFrame "Hsrr".
    iApply eq_add_label_r. iFrame "Hgkr".
    iApply eq_add_label_r. iFrame "Hsr".
    iApply eq_add_label_r. iFrame "Hrr".
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
      - iPoseProof (SEM_TYPED_EFF _ _ _ _ _ _ (client_pers_mono_row _ _ _ _ _ _ _ _ _ _)) as "H".
        unfold sem_val_typed. simpl. iDestruct "H" as "#H". iApply "H".
      - iPoseProof (SEM_TYPED_EFF _ _ _ _ _ _ (client_pers_mono_row' _ _ _ _ _ _ _ _ _ _)) as "H".
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
      iIntros "[[>(Hlml&Hlcl&Hlmr&Hlcr&Hlaml&Hlamr&Hγl&Hι)|[>H2|H3]] Hclose]".
      + eq_load_l... eq_load_r... eq_store_l... eq_store_r...
        eq_handle_os_l_in [HandleCtx _ _ _ _ _; HandleCtx _ _ _ _ _; HandleCtx _ _ _ _ _; AppRCtx _].
        { eapply NoDup_cons_1_1. simpl.
          eapply (submseteq_NoDup _ [sl; rl; gkl; srl; ssl]); [solve_submseteq|exact Hnd_l]. }
        iIntros (rgkl) "Hrgkl"...
        eq_handle_os_r_in [HandleCtx _ _ _ _ _; HandleCtx _ _ _ _ _; HandleCtx _ _ _ _ _; AppRCtx _].
        { eapply NoDup_cons_1_1. simpl.
          eapply (submseteq_NoDup _ [rr; sr; gkr; srr; ssr]); [solve_submseteq | exact Hnd_r]. }
        iIntros (rgkr) "Hrgkr"...
        eq_load_l... eq_load_r...
        eq_rand_l as "%Hx'"...
        eq_reshape_r (rand(#lbl:γr) #_)%E.
        iApply eq_rand_empty_r. iFrame "Hγr".
        iIntros (c') "_ %Hc'"...
        eq_store_l... eq_store_r...
        iMod (eq_pt_l_persist with "Hlml") as "#Hlml".
        iMod (eq_pt_l_persist with "Hlcl") as "#Hlcl".
        iMod (eq_pt_r_persist with "Hlmr") as "#Hlmr".
        iMod (eq_pt_r_persist with "Hlcr") as "#Hlcr".
        iMod (eq_tp_l_persist with "Hγl") as "#Hγl".
        iApply eq_na_close_rule. iFrame "Hclose".
        iSplitL "Hlaml Hlamr".
        { iNext. iRight. iLeft. iExists _, _. iFrame "∗#". }
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
        { eq_cont_l... eq_cont_l. eq_cont_r... eq_cont_r...
          eq_exhaustion (fill k1' #()%V) (fill k2' #()%V) with "[HQ]";
            [set_solver|set_solver|by iApply "Hrel"|iApply "IH"]. }
        eq_cont_l. eq_cont_r...
        eq_rand_r as "%Hk"...
        (* [enc_real_tape] decodes the key code [keyf x] it just drew: the DH
           key [g ^+ x] that [l] derives from its exponent. *)
        pose proof (vg_of_int_sem_keyf x ltac:(lia)) as Hkx.
        eq_vg_of_int_r. eq_pures'.
        eq_reshape_l (enc (ks := vg_fvts) (ms := ms) _ _). eq_reshape_r (enc (ks := vg_fvts) (ms := ms) _ _).
        iApply eq_bind_nil.
        iApply (eq_brel_self _ _ _ _ (brel_enc_couple (key := vg_fv) (msg := msg) _ _)).
        { intros ??. iIntros "(%c & -> & -> & HP)". iExists c. by iFrame. }
        iIntros (vl vr) "(%c & -> & -> & #P)". simpl...
        eq_handle_os_l_in [HandleCtx _ _ _ _ _; AppRCtx _].
        { eapply NoDup_cons_1_1.
          eapply (submseteq_NoDup _ [sl; rl; gkl; srl; ssl]); [solve_submseteq|exact Hnd_l]. }
        iIntros (rsl) "Hsl"...
        eq_handle_os_r_in [HandleCtx _ _ _ _ _; AppRCtx _].
        { eapply NoDup_cons_1_1.
          eapply (submseteq_NoDup _ [rr; sr; gkr; srr; ssr]); [solve_submseteq|exact Hnd_r]. }
        iIntros (rsr) "Hsr"...
        iApply (eq_na_open _ _ alphaN); first set_solver.
        iFrame "HI".
        iIntros "[[>(_&_&_&_&_&_&_&Hι')|[>(%&%&_&_&_&_&Hlaml&Hlamr&_)|(%&%&%&_&_&_&_&_&_&_&_&>Hι')]] Hclose]".
        (* The key tape [ι] has already been read, so the "fresh" and the
           "already sent" disjuncts are both impossible. *)
        3: { iExFalso. iApply (eq_tp_r_excl with "Hι Hι'"). }
        1: { iExFalso. iApply (eq_tp_r_excl with "Hι Hι'"). }
        eq_load_l... eq_load_r... eq_store_l... eq_store_r...
        iMod (eq_pt_l_persist with "Hlaml") as "#Hlaml".
        iMod (eq_pt_r_persist with "Hlamr") as "#Hlamr".
        iMod (eq_tp_r_persist with "Hι") as "#Hι".
        iApply eq_na_close_rule. iFrame "Hclose".
        iSplitR; [iNext; do 2 iRight; iExists _, _, _; iFrame "#"|].
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
      + iDestruct "H2" as "(%&%&#Hlml&#Hlcl&#Hlmr&#Hlcr&Hlaml&Hlamr&#Hγ)".
        eq_load_l. eq_load_r...
        iApply eq_na_close_rule. iFrame "Hclose".
        iSplitR "HQ Hssl Hssr"; [iNext; iRight; iLeft; iExists _, _; iFrame "∗#"|].
        eq_cont_l. eq_cont_r...
        eq_exhaustion (fill k1' #()%V) (fill k2' #()%V) with "[HQ]";
          [set_solver|set_solver|by iApply "Hrel"|iApply "IH"].
      + iDestruct "H3" as "(%&%&%&#HP&>#Hlml&>#Hlcl&>#Hlmr&>#Hlcr&>#Hlaml&>#Hlamr&>#Hγl&>#Hι)".
        eq_load_l. eq_load_r...
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
        do 4 (apply NoDup_cons_iff in Hnd_r as [?Hn Hnd_r]).
        apply Hn2. by left. }
      iIntros "!>" (rsrl rsrr) "Hsrl Hsrr"...
      repeat foldkont.
      eq_handle_os_l_in [HandleCtx _ _ _ _ _; HandleCtx _ _ _ _ _; AppRCtx _].
      { eapply NoDup_cons_1_1. simpl.
        eapply (submseteq_NoDup _ [sl; rl; gkl; srl; ssl]); [solve_submseteq|exact Hnd_l]. }
      iIntros (rgkl) "Hrgkl"...
      eq_handle_os_r_in [HandleCtx _ _ _ _ _; HandleCtx _ _ _ _ _; AppRCtx _].
      { eapply NoDup_cons_1_1. simpl.
        eapply (submseteq_NoDup _ [rr; sr; gkr; srr; ssr]); [solve_submseteq | exact Hnd_r]. }
      iIntros (rgkr) "Hrgkr"...
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
      iApply (eq_na_open _ _ alphaN); first set_solver.
      iFrame "HI".
      iIntros "[[>(Hlml&Hlcl&Hlmr&Hlcr&Hlaml&Hlamr&Hγl&Hι)|[>H2|H3]] Hclose]".
      + eq_load_l... eq_load_r...
        eq_cont_l. eq_cont_r... eq_cont_l. eq_cont_r...
        iApply eq_na_close_rule. iFrame "Hclose".
        iSplitR "HQ"; [iNext; iLeft; iFrame|].
        eq_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"; [set_solver|set_solver|iApply "Hrel"|iApply "IH"].
        iDestruct "HQ" as "[_ $]".
      + iDestruct "H2" as "(%c'&%mv&#Hlml&#Hlcl&#Hlmr&#Hlcr&Hlaml&Hlamr&#Hγ)".
        eq_load_l... eq_load_r...
        eq_cont_l. eq_cont_r...
        eq_handle_os_l_in [HandleCtx _ _ _ _ _; AppRCtx _].
        { eapply NoDup_cons_1_1. simpl.
          eapply (submseteq_NoDup _ [sl; rl; gkl; srl; ssl]); [solve_submseteq|exact Hnd_l]. }
        iIntros (rrl) "Hrl"...
        eq_handle_os_r_in [HandleCtx _ _ _ _ _; AppRCtx _].
        { eapply NoDup_cons_1_1. simpl.
          eapply (submseteq_NoDup _ [rr; sr; gkr; srr; ssr]); [solve_submseteq | exact Hnd_r]. }
        iIntros (rrr) "Hrr"...
        iApply eq_na_close_rule. iFrame "Hclose".
        iSplitR "HQ Hsrl Hsrr Hrl Hrr"; [iNext; iRight; iLeft; iExists _, _; iFrame "∗#"|].
        eq_reshape_l (arcv_l _). eq_reshape_r (arcv_r _).
        iApply (eq_env_call_gen lls rls (λ _, iThyBot) _ _ with "Harcv [] [-]");
          [set_unfold; tauto | set_unfold; tauto | | |].
        { intros []; rewrite /lls /rls /pick /=; iApply to_iThy_le_intro'; unfold sem_row_union;
            repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app); solve_submseteq. }
        { iApply eq_lift_same. iExists _, _; by iLeft. }
        iIntros (v1' v2') "Hv". iEval (rewrite eq_lift_sum) in "Hv".
        iDestruct "Hv" as (a1 a2) "[(-> & -> & Hu)|(-> & -> & Hu)]";
          iEval (rewrite eq_lift_unit) in "Hu"; iDestruct "Hu" as %[-> ->]...
        { eq_cont_l. eq_cont_r... eq_cont_l. eq_cont_r...
          eq_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"; [set_solver|set_solver|iApply "Hrel"|iApply "IH"].
          iDestruct "HQ" as "[_ $]". }
        iApply (eq_na_open _ _ alphaN); first set_solver.
        iFrame "HI".
        iIntros "[[>(Hlml'&H')|[>H2|H3]] Hclose]".
        (* [lml] already holds the message, so the "fresh" disjunct is impossible. *)
        { iExFalso. iApply (eq_pt_l_excl with "Hlml' Hlml"). }
        * iDestruct "H2" as "(%&%&_&_&_&_&Hlaml&Hlamr&_)".
          eq_load_l... eq_load_r...
          eq_cont_l. eq_cont_r... eq_cont_l. eq_cont_r...
          iApply eq_na_close_rule. iFrame "Hclose".
          iSplitR "HQ"; [iNext; iRight; iLeft; iExists _, _; iFrame "∗#"|].
          eq_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"; [set_solver|set_solver|iApply "Hrel"|iApply "IH"].
          iDestruct "HQ" as "[_ $]".
        * iDestruct "H3" as "(%c''&%mv'&%cv&#HP&>#Hlml'&_&_&_&>#Hlaml&>#Hlamr&>#Hγl3&>#Hι)".
          iDestruct (eq_pt_l_agree with "Hlml Hlml'") as %Hmv.
          assert (mv' = mv) as -> by (simplify_eq; by apply (@fvtval_inj mt)).
          eq_load_l. eq_load_r...
          eq_cont...
          eq_load_r... eq_cont_r.
          iApply eq_na_close_rule. iFrame "Hclose".
          iSplitR "HQ Hsrl"; [iNext; iRight; iRight; iExists _, _, _; iFrame "#"|]...
          rewrite (@vgval_fvtval Σ _ vg cg G vgg (g ^+ x)%g).
          eq_reshape_l (dec _ _).
          iApply (eq_step_l_with (P (SYM := SKE) (g ^+ x)%g mv cv)).
          { intros e S. iIntros "[HP H]". by iApply (brel_dec_enc_correct_l (SYM := SKE) with "HP H"). }
          { intros e S. iIntros "[HP H]". by iApply (brel_dec_enc_correct_r (SYM := SKE) with "HP H"). }
          iSplitR; [iApply bi.intuitionistically_elim; rewrite -embed_intuitionistically; iExact "HP"|]. simpl...
          eq_cont_l.
          eq_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"; [set_solver|set_solver|iApply "Hrel"|iApply "IH"].
          iDestruct "HQ" as "[HQ _]". iApply "HQ".
      + iDestruct "H3" as "(%c'&%mv&%cv&#HP&>#Hlml&>#Hlcl&>#Hlmr&>#Hlcr&>#Hlaml&>#Hlamr&>#Hγl&>#Hι)".
        eq_load_l. eq_load_r...
        eq_cont...
        eq_handle_os_l_in [HandleCtx _ _ _ _ _; AppRCtx _].
        { eapply NoDup_cons_1_1. simpl.
          eapply (submseteq_NoDup _ [sl; rl; gkl; srl; ssl]); [solve_submseteq|exact Hnd_l]. }
        iIntros (rrl) "Hrl"...
        eq_handle_os_r_in [HandleCtx _ _ _ _ _; AppRCtx _].
        { eapply NoDup_cons_1_1. simpl.
          eapply (submseteq_NoDup _ [rr; sr; gkr; srr; ssr]); [solve_submseteq | exact Hnd_r]. }
        iIntros (rrr) "Hrr"...
        iApply eq_na_close_rule. iFrame "Hclose".
        iSplitR "HQ Hsrl Hsrr Hrl Hrr"; [iNext; iRight; iRight; iExists _, _, _; iFrame "#"|].
        eq_reshape_l (arcv_l _). eq_reshape_r (arcv_r _).
        iApply (eq_env_call_gen lls rls (λ _, iThyBot) _ _ with "Harcv [] [-]");
          [set_unfold; tauto | set_unfold; tauto | | |].
        { intros []; rewrite /lls /rls /pick /=; iApply to_iThy_le_intro'; unfold sem_row_union;
            repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app); solve_submseteq. }
        { iApply eq_lift_same. iExists _, _; by iLeft. }
        iIntros (v1' v2') "Hv". iEval (rewrite eq_lift_sum) in "Hv".
        iDestruct "Hv" as (a1 a2) "[(-> & -> & Hu)|(-> & -> & Hu)]";
          iEval (rewrite eq_lift_unit) in "Hu"; iDestruct "Hu" as %[-> ->]...
        { eq_cont_l. eq_cont_r... eq_cont_l. eq_cont_r...
          eq_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"; [set_solver|set_solver|iApply "Hrel"|iApply "IH"].
          iDestruct "HQ" as "[_ $]". }
        eq_load_l. eq_load_r...
        eq_cont_l. eq_cont_r...
        eq_load_r...
        rewrite (@vgval_fvtval Σ _ vg cg G vgg (g ^+ x)%g).
        eq_reshape_l (dec _ _).
        iApply (eq_step_l_with (P (SYM := SKE) (g ^+ x)%g mv cv)).
        { intros e S. iIntros "[HP H]". by iApply (brel_dec_enc_correct_l (SYM := SKE) with "HP H"). }
        { intros e S. iIntros "[HP H]". by iApply (brel_dec_enc_correct_r (SYM := SKE) with "HP H"). }
        iSplitR; [iApply bi.intuitionistically_elim; rewrite -embed_intuitionistically; iExact "HP"|]. simpl...
        eq_cont_r.
        eq_cont_l...
        eq_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"; [set_solver|set_solver|iApply "Hrel"|iApply "IH"].
        iDestruct "HQ" as "[HQ _]". iApply "HQ".
  Qed.

  Lemma REAL_SKE_GAME1_MS :
    ⊢ sem_typed [] REAL_SKE GAME1 ⊥ (𝟙 -{ ⟨⟩ }-[ MS ]-> τsc)%T [].
  Proof using All. apply (EQ_sem_typed _ _ _ _ REAL_SKE_GAME1_EQ Fwd). Qed.

  Lemma GAME1_REAL_SKE_MS :
    ⊢ sem_typed [] GAME1 REAL_SKE ⊥ (𝟙 -{ ⟨⟩ }-[ MS ]-> τsc)%T [].
  Proof using All. apply (EQ_sem_typed _ _ _ _ REAL_SKE_GAME1_EQ Bwd). Qed.

  (* One-shot versions, the shape the composition operators expect *)
End schan_security.

From iris.proofmode Require Import base proofmode classes.                                             
From iris.base_logic.lib Require Import  na_invariants.   
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode
  spec_rules spec_ra
  class_instances.
From clutch.prob_eff_lang.probblaze Require Import tactics.
From clutch.prob_eff_lang.probblaze Require Import sem_types sem_row sem_sig sem_judgement sem_def.
From clutch.prob_eff_lang.probblaze.examples Require Import ske ske_sec_chan_def ske_sec_chan_common.


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
  #[local] Notation τsc := (@τsc Σ _ mt ct ms cs msg cipher).
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

  (* The reverse refinement.  Mirror image of [sc_real_game1] below: every
     left-hand step becomes a right-hand step and vice versa, the heap and tape
     assertions swap between the implementation and the specification side, and
     the tapes are coupled along the inverse bijection [f_inv keyf]. *)
  Lemma game1_sc_real : 
    ⊢ sem_typed [] game1 sc_real ⊥ τsc [].
  Proof using All with (brel_pures'; repeat foldkont). 
    iIntros (?) "!# _ //=". 
    rewrite /sc_real /reduction /CHAN /RED_CHAN /F_OAUTH /F_KE_lazy_alice /right_composition /enc_real_tape /func_comp...
    iModIntro. iSplit; last done.
    iIntros (θL f1 f2) "Hff"...
    iIntros "!>" (autheff keyeff autheffkeyeff_l autheffkeyeff_r) "Hauthkey".
    iDestruct "Hauthkey" as (w1 w1' w2 w2') "[-> [-> [Hautheff Hkeyeff]]]"...
    iDestruct "Hautheff" as (asnd_l asnd_r arcv_l arcv_r) "(-> & -> & (#Hasnd & #Harcv))"...
    iDestruct "Hkeyeff" as (kysnd_l kysnd_r kyrcv_l kyrcv_r) "(-> & -> & (#Hkeysnd & #Hkeyrcv))"...

    
    (* Allocation/initialization *)
    brel_alloctape_r γr as "Hγr"...
    brel_alloctape_l γl as "Hγl"...
    brel_alloc_r lcr as "Hlcr"...
    brel_alloc_l lcl as "Hlcl"...
    brel_effect_r gkr as "Hgkr".
    brel_effect_l gkl as "Hgkl"...
    brel_alloc_r lamr as "Hlamr".
    brel_alloc_l laml as "Hlaml"...
    brel_effect_r sr as "Hsr".
    brel_effect_l sl as "Hsl"...
    brel_effect_r rr as "Hrr".
    brel_effect_l rl as "Hrl"...
    brel_alloc_r lmr as "Hlmr".
    brel_alloctape_l (ι) as "Hι"... (* Initialization of the encryption scheme *)
    brel_alloc_l lml as "Hlml"...
    brel_effect_r ssr as "Hssr".
    brel_effect_l ssl as "Hssl"...
    brel_effect_r srr as "Hsrr".
    brel_effect_l srl as "Hsrl"...

    (* Setting up clients *)
    set (θ := client_row' sr rr sl rl gkr gkl ssl srl ssr srr).
    iSpecialize ("Hff" $! θ).
    unfold sem_ty_arr, sem_ty_mbang. simpl.
    iAssert (sem_val_typed  ((λ: "m", do: ssl "m"), (λ: <>, do: srl bob))%V ((λ: "m", do: ssr "m") , (λ: <>, do: srr bob))%V (((sem_ty_nat -{ θ }-> 𝟙) × (𝟙 -{ θ }-> (Option msg.(sem_τFT))))%T)) as "Hschn".
    { iApply SEM_TYPED_EFF. }
     unfold sem_val_typed. simpl.
    iDestruct "Hschn" as "#Hschn".
    iSpecialize ("Hff" with "Hschn"). 

    (* Theories *)
    iApply brel_new_theory.
    iApply (brel_add_label_r with "Hssr").
    iApply (brel_add_label_r with "Hsrr").
    iApply (brel_add_label_l with "Hssl").
    iApply (brel_add_label_l with "Hsrl").
    iApply (brel_add_label_r with "Hgkr").
    iApply (brel_add_label_l with "Hgkl").
    iApply (brel_add_label_r with "Hrr").
    iApply (brel_add_label_r with "Hsr").
    iApply (brel_add_label_l with "Hsl").
    iApply (brel_add_label_l with "Hrl"). 

    iApply brel_learn. iIntros "%Hdist' _".
    assert (NoDup [sr; rr; gkr; srr; ssr]) as Hnd_r.
    { unfold distinct in Hdist'. destruct Hdist' as [_ Hd'].
      unfold distinct_r in Hd'. simpl in Hd'.
      repeat (rewrite -> labels_r_cons in Hd').
      by (eapply NoDup_app in Hd'; destruct Hd' as [Hd' _]). }
    
    assert (NoDup [rl; sl; gkl; srl; ssl]) as Hnd_l.
    { unfold distinct in Hdist'. destruct Hdist' as [Hd' _].
      unfold distinct_l in Hd'. simpl in Hd'.
      rewrite !labels_l_cons in Hd'.
      by (eapply NoDup_app in Hd'; destruct Hd' as [Hd' _]). }

    (* Invariants *)
    rewrite Nat2Z.id.
    iAssert (γr ↪ₛN (n; []))%I with "[Hγr]" as "Hγr". 
    { iExists []. simpl. iFrame. done. }
    iDestruct (tapeN_to_persistent with "Hγl") as ">#Hγl".
    (* Mirror image of the coupling in [sc_real_game1]: here [game1] is on the
       left, so the left tape [ι] draws the symmetric key [x] and the right tape
       [γr] draws Alice's DH exponent [f_inv keyf x] -- whose encoding is again
       [x], by [keyf_inv_spec]. *)
    iApply (brel_couple_TT _ n (f_inv keyf)).
    { apply keyf_inv_dom. }
    rewrite vg_fvt_card. assert (S n - 1 = n)%Z as -> by lia.
    rewrite Nat2Z.id. iFrame.
    iIntros (x) "(Hι&Hγr) //=".
    iDestruct (tapeN_hd_bound with "Hι") as "(%Hx&Hι)".
    
    iApply (brel_na_alloc ((lmr ↦ₛ NONEV ∗ lcr ↦ₛ NONEV ∗ lml ↦ NONEV ∗ lcl ↦ NONEV ∗ lamr ↦ₛ NONEV ∗ laml ↦ NONEV
                           ∗ γr ↪ₛN (n; [f_inv keyf x]) ∗ (Loc ι) ↪N (n; [x]))
                           ∨ (∃ (c' : nat) (mv : mt), lmr ↦ₛ□ SOMEV (fvtval mv) ∗ lcr ↦ₛ□ SOMEV #(f_inv keyf x) ∗ lml ↦□ SOMEV (fvtval mv) ∗ lcl ↦□ SOMEV #c'
                                            ∗ lamr ↦ₛ NONEV ∗ laml ↦ NONEV
                                            ∗ γr ↪ₛ□N (n; []))
                           ∨ (∃ (c' : nat) (mv : mt) (cv : ct), (□ P (key := vg_fv) (g ^+ f_inv keyf x)%g mv cv) ∗
                                                                lmr ↦ₛ□ SOMEV (fvtval mv) ∗ lcr ↦ₛ□ SOMEV #(f_inv keyf x) ∗ lml ↦□ SOMEV (fvtval mv) ∗ lcl ↦□ SOMEV #c'
                                                                ∗ lamr ↦ₛ□ SOMEV (fvtval cv) ∗ laml ↦□ SOMEV (fvtval cv)
                                                                ∗ γr ↪ₛ□N (n; []) ∗ (Loc ι) ↪□N (n; []))
              ) alphaN).
    iSplitL "Hlmr Hlml Hlcr Hlcl Hγr Hι Hlamr Hlaml"; [iNext; iLeft; iFrame|].
    iIntros "#HI".

    (* Case on the clients behaviour and induction *)
    rewrite !iLblSig_to_iLblThy_app !iThyIfMono_iLblSig_to_iThyIfMono.
    iDestruct (brel_introduction_mono _ (([rl; sl; gkl; srl; ssl], [sr; rr; gkr; srr; ssr], sec_channel ssl ssr srl srr : iThy Σ) :: to_iThyIfMono OS (iLblSig_to_iLblThy autheff) ++ to_iThyIfMono OS (iLblSig_to_iLblThy keyeff) ++ iLblSig_to_iLblThy θL) with "[][$Hff]") as "Hff".
    { iApply to_iThy_le_intro'. solve_submseteq. }
    iApply ((brel_exhaustion (f1 _) ( f2 _)) with "[$Hff]"); [set_solver|set_solver| ].
    
    iLöb as "IH".
    iSplit; [iIntros (v1 v2) "%Hv1v2 !>"; by brel_pures'|].
    iIntros (?????) "!# %Hk1 %Hk2 [(%m&(->&->)&HQ)|(->&->&HQ)] #Hrel".
    (* Alice tries to send a message m *)
    - 
      brel_handle_os_l (rssl) as "Hssl".
      brel_handle_os_r (rssr) as "Hssr"...
      (* Both sides decode the client's integer code with the SAME [fvt_of_int],
         so the case split is on [fvt_of_int_sem m] rather than on a bound, and
         the message carried through the invariant is the decoded VALUE [mv]. *)
      (* [fin_val := msg] MUST be pinned: left implicit, the [fvt_of_int] in the
         rule's conclusion is headed by an evar and the [fill K] unification
         against the handler stack has nothing to match on. *)
      destruct (fvt_of_int_sem (fin_val := msg) m) as [mv|] eqn:Hmv.
      2 : { iApply (brel_fvt_of_int_none_l (fin_val := msg)); first exact Hmv.
            iApply (brel_fvt_of_int_none_r (fin_val := msg)); first exact Hmv...
             brel_cont_l. 
             brel_cont_r.
            iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V) with "[HQ]"); [set_solver|set_solver|by iApply "Hrel"|iApply "IH"]. }
      iApply (brel_fvt_of_int_correct_l (fin_val := msg)); first exact Hmv.
      iApply (brel_fvt_of_int_correct_r (fin_val := msg)); first exact Hmv...
      iApply (brel_na_inv _ _ alphaN); first set_solver.
      iFrame "HI".
      iIntros "([>(Hlmr&Hlcr&Hlml&Hlcl&Hlamr&Hlaml&Hγr&Hι)|[H2|H3]]&Hclose)".
      + brel_load_r...
        brel_load_l...
        brel_store_r...
        brel_store_l...
        iApply (brel_handle_os_r [] [HandleCtx _ _ _ _ _;HandleCtx _ _ _ _ _;HandleCtx _ _ _ _ _;AppRCtx _]).
        { eapply NoDup_cons_1_1. simpl.
          eapply (submseteq_NoDup _ [sr; rr; gkr; srr; ssr]); [solve_submseteq|exact Hnd_r]. }
        iIntros (rgkr) "Hrgkr"...
        iApply (brel_handle_os_l [] [HandleCtx _ _ _ _ _;HandleCtx _ _ _ _ _;HandleCtx _ _ _ _ _;AppRCtx _]).
        { eapply NoDup_cons_1_1. simpl.
          eapply (submseteq_NoDup _ [rl; sl; gkl; srl; ssl]); [solve_submseteq | exact Hnd_l]. }
        iIntros (rgkl) "!> Hrgkl"...
        brel_load_r...
        brel_load_l...
        brel_rand_r...
        iApply brel_randT_empty_l. 
        iSplitR; first by iFrame "#".
        iIntros "!>" (c') "_ _".
        brel_store_r...
        brel_store_l...

        iMod (ghost_map_elem_persist with "Hlmr") as "#Hlmr".
        iMod (ghost_map_elem_persist with "Hlcr") as "#Hlcr".
        iMod (ghost_map_elem_persist with "Hlml") as "#Hlml".
        iMod (ghost_map_elem_persist with "Hlcl") as "#Hlcl".
        iDestruct (spec_tape_to_persistent with "Hγr") as ">#Hγr".
        iApply brel_na_close. iFrame.
        iSplitL "Hlamr Hlaml".
        { iModIntro. iRight. iLeft. iExists _, _. iFrame "#". iFrame. }

        iApply (brel_bind'' [AppRCtx _] [AppRCtx _] (to_iThyIfMono OS (iLblSig_to_iLblThy keyeff))); try (apply list_subseteq_nil).
        { iApply to_iThy_le_intro'. solve_submseteq. }
        iApply brel_mono; [iApply to_iThy_le_refl| |simpl].
        { iApply "Hkeysnd". iExists _, _. by iLeft. }
        iIntros (v1 v2) "(->&->)"...
        iApply (brel_bind'' [AppRCtx _] [AppRCtx _] (to_iThyIfMono OS (iLblSig_to_iLblThy keyeff))); try (apply list_subseteq_nil).
        { iApply to_iThy_le_intro'. solve_submseteq. }
        iApply brel_mono; [iApply to_iThy_le_refl| |simpl].
        { iApply "Hkeyrcv". iExists _, _. by iLeft. }
        iIntros (v1' v2') "(%&%&[(->&->&->&->)|(->&->&->&->)])"...
        { brel_cont_r... brel_cont_r. 
          brel_cont_l... brel_cont_l...
          iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V) with "[HQ]"); [set_solver|set_solver|by iApply "Hrel"|iApply "IH"]. }
        brel_cont_r. 
        brel_cont_l...
        brel_rand_l...
        (* [enc_real_tape] decodes the key code [x] it just drew; by
           [vg_of_int_sem_keyf_inv] that is exactly the DH key [g ^+ f_inv keyf x]
           the right-hand side obtained from the key exchange, so after the
           decode both sides encrypt under the same key.  (The old proof instead
           ENCODED the right-hand key with [int_of_vg]; the scheme now takes a
           group value, so that step is gone.) *)
        iApply brel_vg_of_int_correct_l; first (by apply vg_of_int_sem_keyf_inv).
        brel_pures'.
        iApply (brel_bind _ _ _ [] _ _ (enc (ks := vg_fv) (ms := ms)_ _) (enc (ks := vg_fv) (ms := ms)_ _)); 
          [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
        assert (to_iThyIfMono OS [] = []) as <- by done.
        iApply brel_mono; first iApply to_iThy_le_refl.
        { iApply (brel_enc_couple (key := vg_fv) (msg := msg)). }
        simpl.
        iIntros (??) "(%c&->&->&#P)".
        brel_pures'; simpl.
        (* [brel_pures'] raises one label-freshness goal per side; which side
           comes first is fixed by the tactic, not by the direction, so let
           each goal pick its own [NoDup] fact. *)
        iApply (brel_handle_os_l _ [HandleCtx _ _ _ _ _;AppRCtx _]).
        { eapply NoDup_cons_1_1. first [ eapply (submseteq_NoDup _ [sr; rr; gkr; srr; ssr]); [solve_submseteq|exact Hnd_r]
                | eapply (submseteq_NoDup _ [rl; sl; gkl; srl; ssl]); [solve_submseteq|exact Hnd_l] ]. }
        iIntros (rsl) "!> Hsl"...
        iApply (brel_handle_os_r _ [HandleCtx _ _ _ _ _;AppRCtx _]).
        { eapply NoDup_cons_1_1. first [ eapply (submseteq_NoDup _ [sr; rr; gkr; srr; ssr]); [solve_submseteq|exact Hnd_r]
                | eapply (submseteq_NoDup _ [rl; sl; gkl; srl; ssl]); [solve_submseteq|exact Hnd_l] ]. }
        iIntros (rsr) "Hsr"...
        iApply (brel_na_inv _ _ alphaN); first set_solver.
        iFrame "HI".
        iIntros "([>(_&_&_&_&_&_&_&Hι')|[>(%&%&_&_&_&_&Hlamr&Hlaml&_)|(%&%&%&_&_&_&_&_&_&_&_&>Hι')]]&Hclose)".
        (* The key tape [ι] has already been read, so the "fresh" and the
           "already sent" disjuncts are both impossible: each hands back an
           assertion for [ι] that cannot coexist with the one we hold. *)
        3 : { iExFalso. iApply (tapeN_excl with "Hι Hι'"). }
        1 : { iExFalso. iApply (tapeN_excl with "Hι Hι'"). }
        brel_load_r...
        brel_load_l...
        brel_store_r...
        brel_store_l...

        iMod (ghost_map_elem_persist with "Hlamr") as "#Hlamr".
        iMod (ghost_map_elem_persist with "Hlaml") as "#Hlaml".
        iDestruct (tapeN_to_persistent with "Hι") as ">#Hι".
        iApply brel_na_close.
        iFrame. iSplitR; [iNext; do 2 iRight; iExists _,_; iFrame "#"|].
        iApply (brel_bind'' _ _ (to_iThyIfMono OS (iLblSig_to_iLblThy autheff)) _ _ _ (asnd_l _) (asnd_r _)).
        3 : { iApply to_iThy_le_intro'. 
              eassert (_ :: _ = [_] ++ _) as -> by done.
              eapply submseteq_app_middle. simpl.
              apply singleton_submseteq_l. constructor. }
        1,2 : set_unfold; tauto.
        iApply brel_mono; [iApply to_iThy_le_refl| |simpl].
        { iApply "Hasnd". iExists _, _, _, _. 
          repeat (iSplit; first done). 
          iSplit; last (iExists _,_; by iLeft). 
          by iExists _. }
        iIntros (v1'' v2'') "(->&->)"...
        brel_cont_l... brel_cont_l.
        brel_cont_r... brel_cont_r...
        iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V) with "[HQ]"); [set_solver|set_solver|by iApply "Hrel"|iApply "IH"].
      + iDestruct "H2" as ">(%&%&Hlmr&Hlcr&Hlml&Hlcl&Hγ)".
        brel_load_r.
        brel_load_l...
        iApply brel_na_close.
        iFrame. 
        iSplitR "HQ Hssl Hssr"; [iRight; iLeft; iExists _,_; iFrame|].
        brel_cont_l. brel_cont_r...
        iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V) with "[HQ]"); [set_solver|set_solver|by iApply "Hrel"|iApply "IH"].
      + iDestruct "H3" as "(%&%&%&HP&>Hlmr&>Hlcr&>Hlml&>Hlamr&>Hlaml&>Hι)".
        brel_load_r.
        brel_load_l...
        iApply brel_na_close.
        iFrame. 
        iSplitR "HQ Hssl Hssr"; [iRight; iRight; iExists _,_; iFrame|].
        brel_cont_l. brel_cont_r...
        iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V) with "[HQ]"); [set_solver|set_solver|by iApply "Hrel"|iApply "IH"].
    (* Bob tries to receive a message *)
    - brel_pures'.
      iApply (brel_handle_os_l _ ([HandleCtx _ _ _ _ _] ++ k1')).
      {  apply not_elem_of_cons; split; last (apply neutral_ectx; repeat constructor).
         intro Heq. first [ apply NoDup_ListNoDup in Hnd_r;
                 do 4 (apply NoDup_cons_iff in Hnd_r as [?Hn Hnd_r]); apply Hn2; by left
               | apply NoDup_ListNoDup in Hnd_l;
                 do 4 (apply NoDup_cons_iff in Hnd_l as [?Hn Hnd_l]); apply Hn2; by left ]. }
      iIntros (rsrl) "!> Hsrl"...
      iApply (brel_handle_os_r _ ([HandleCtx _ _ _ _ _] ++ k2')).
      {  apply not_elem_of_cons; split; last (apply neutral_ectx; repeat constructor).
         intro Heq. first [ apply NoDup_ListNoDup in Hnd_r;
                 do 4 (apply NoDup_cons_iff in Hnd_r as [?Hn Hnd_r]); apply Hn2; by left
               | apply NoDup_ListNoDup in Hnd_l;
                 do 4 (apply NoDup_cons_iff in Hnd_l as [?Hn Hnd_l]); apply Hn2; by left ]. }
      iIntros (rsrr) "Hsrr"...
      repeat foldkont.
      iApply (brel_handle_os_r [] [HandleCtx _ _ _ _ _;HandleCtx _ _ _ _ _;AppRCtx _]).
      { eapply NoDup_cons_1_1. simpl.
        eapply (submseteq_NoDup _ [sr; rr; gkr; srr; ssr]); [solve_submseteq|exact Hnd_r]. }
      iIntros (rgkr) "Hrgkr"...
      iApply (brel_handle_os_l [] [HandleCtx _ _ _ _ _;HandleCtx _ _ _ _ _;AppRCtx _]).
      { eapply NoDup_cons_1_1. simpl.
        eapply (submseteq_NoDup _ [rl; sl; gkl; srl; ssl]); [solve_submseteq | exact Hnd_l]. }
      iIntros (rgkl) "!> Hrgkl"...
      iApply (brel_bind'' [AppRCtx _] [AppRCtx _] (to_iThyIfMono OS (iLblSig_to_iLblThy keyeff))); try (apply list_subseteq_nil).
      { iApply to_iThy_le_intro'. solve_submseteq. }
      iApply brel_mono; [iApply to_iThy_le_refl| |simpl].
      { iApply "Hkeyrcv". iExists _, _. by iRight. }
      iIntros (v1' v2') "(%&%&[(->&->&->&->)|(->&->&->&->)])"...
      { brel_cont_r. brel_cont_l...  brel_cont_r. brel_cont_l...
        iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"]. 
        iDestruct "HQ" as "[_ $]". }
      iApply (brel_bind'' [AppRCtx _] [AppRCtx _] (to_iThyIfMono OS (iLblSig_to_iLblThy keyeff))); try (apply list_subseteq_nil).
      { iApply to_iThy_le_intro'. solve_submseteq. }
      iApply brel_mono; [iApply to_iThy_le_refl| |simpl].
      { iApply "Hkeysnd". iExists _, _. by iRight. }
      iIntros (v1 v2) "(->&->)"...      
      iApply (brel_na_inv _ _ alphaN); first set_solver.
      iFrame "HI".
      iIntros "([>(Hlmr&Hlcr&Hlml&Hlcl&Hlamr&Hlaml&Hγr&Hι)|[H2|H3]]&Hclose)".
      + brel_load_r...
        brel_load_l...
        brel_cont_r.
        brel_cont_l...
        brel_cont_r.
        brel_cont_l...
        iApply brel_na_close.
        iFrame. 
        iSplitR "HQ"; [iLeft; iFrame|].
        iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"].
        iDestruct "HQ" as "[_ $]".
      + iDestruct "H2" as ">(%&%&#Hlmr&#Hlcr&#Hlml&#Hlcl&Hlamr&Hlaml&#Hγ)".
        brel_load_r...
        brel_load_l...
        brel_cont_r.
        brel_cont_l...
        iApply (brel_handle_os_l _ [HandleCtx _ _ _ _ _; AppRCtx _]).
        { eapply NoDup_cons_1_1. simpl. first [ eapply (submseteq_NoDup _ [sr; rr; gkr; srr; ssr]); [solve_submseteq|exact Hnd_r]
                | eapply (submseteq_NoDup _ [rl; sl; gkl; srl; ssl]); [solve_submseteq|exact Hnd_l] ]. }
        iIntros (rrl) "!> Hrl"...
        iApply (brel_handle_os_r _ [HandleCtx _ _ _ _ _; AppRCtx _]).
        { eapply NoDup_cons_1_1. simpl. first [ eapply (submseteq_NoDup _ [sr; rr; gkr; srr; ssr]); [solve_submseteq|exact Hnd_r]
                | eapply (submseteq_NoDup _ [rl; sl; gkl; srl; ssl]); [solve_submseteq|exact Hnd_l] ]. }        
        iIntros (rrr) "Hrr"...
        iApply brel_na_close.
        iFrame. 
        iSplitR "HQ Hsrl Hsrr Hrl Hrr"; [iRight; iLeft; iExists _,_; iFrame "#"; iFrame|].
        iApply (brel_bind'' _ _ (to_iThyIfMono OS (iLblSig_to_iLblThy autheff)) _ _ _ (arcv_l _) (arcv_r _)).
        3 : { iApply to_iThy_le_intro'. 
              eassert (_ :: _ = [_] ++ _) as -> by done.
              eapply submseteq_app_middle. simpl.
              apply singleton_submseteq_l. constructor. }
        1,2 : set_unfold; tauto.
        iApply brel_mono; [iApply to_iThy_le_refl| |simpl].
        { iApply "Harcv". iExists _,_; by iLeft. }
        iIntros (v1' v2') "(%&%&[(->&->&->&->)|(->&->&->&->)])"...
        { brel_cont_l.
          brel_cont_r...
          brel_cont_l.
          brel_cont_r...
          iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"]. 
          iDestruct "HQ" as "[_ $]". }
        iApply (brel_na_inv _ _ alphaN); first set_solver.
        iFrame "HI".
        iIntros "([>(Hlmr'&H')|[>H2|H3]]&Hclose)".
        (* [lmr] already holds the message (persistently), so the "fresh"
           disjunct of the invariant is impossible. *)
        { iExFalso. by iDestruct (ghost_map_elem_ne with "Hlmr' Hlmr") as %?. }
        * iDestruct "H2" as "(%&%&_&_&_&_&Hlamr&Hlaml&_)".
          brel_load_r...
          brel_load_l... 
          brel_cont_l.
          brel_cont_r...
          brel_cont_l.
          brel_cont_r...
          iApply brel_na_close.
          iFrame. 
          iSplitR "HQ"; [iRight; iLeft; iExists _,_; iFrame "#"; iFrame|].
          iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"]. 
          iDestruct "HQ" as "[_ $]".
        * iDestruct "H3" as "(%c3&%mv3&%cv&#HP&>Hlmr'&_&_&_&>Hlamr&>Hlaml&>Hγr3&>Hι)".
          iDestruct (ghost_map_elem_agree with "Hlmr Hlmr'") as "->".
          brel_load_r.
          brel_load_l...
          brel_cont_l.
          brel_cont_r...
          brel_load_l...
          brel_cont_l.
          iApply brel_na_close.
          iFrame. 
          (* [iFrame "#"] already discharges the [γr] conjunct from the
             persistent [Hγ], so naming [Hγr3] here would fail with nothing left
             to frame; let [iFrame] take whatever remains. *)
          iSplitR "HQ Hsrr"; [iNext;iRight; iRight; iExists _,_; iFrame "#"; iFrame|]...

          (* [dec_enc_sem_correct] is now unconditional, and the key reaching
             [dec] is the group value itself -- no [int_of_vg] step, no bounds. *)
          (* [SYM := SKE] MUST be pinned.  Left to instance resolution, [dec] in
             the rule's conclusion stays evar-headed and the [fill K] matching
             against the handler stack has nothing to key on -- supplying [key]
             or even [K] and both elements does not help. *)
          rewrite (vgval_fvtval (g ^+ f_inv keyf x)%g).
          iApply (brel_dec_enc_correct_r (SYM := SKE)); first done.
          iApply (brel_cont_r with "Hsrr").
          iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"]. 
          iDestruct "HQ" as "[HQ _]".
          iApply "HQ".
      + iDestruct "H3" as "(%c4&%mv4&%cv&#HP&#Hlmr&>#Hlcr&#Hlcl&#Hlml&#Hlamr&#Hlaml&#Hγr&#Hι)".
        brel_load_r.
        brel_load_l...
        brel_cont_r.
        brel_cont_l...
        iApply (brel_handle_os_l _ [HandleCtx _ _ _ _ _; AppRCtx _]).
        { eapply NoDup_cons_1_1. simpl. first [ eapply (submseteq_NoDup _ [sr; rr; gkr; srr; ssr]); [solve_submseteq|exact Hnd_r]
                | eapply (submseteq_NoDup _ [rl; sl; gkl; srl; ssl]); [solve_submseteq|exact Hnd_l] ]. }
        iIntros (rrl) "!> Hrl"...
        iApply (brel_handle_os_r _ [HandleCtx _ _ _ _ _; AppRCtx _]).
        { eapply NoDup_cons_1_1. simpl. first [ eapply (submseteq_NoDup _ [sr; rr; gkr; srr; ssr]); [solve_submseteq|exact Hnd_r]
                | eapply (submseteq_NoDup _ [rl; sl; gkl; srl; ssl]); [solve_submseteq|exact Hnd_l] ]. }        
        iIntros (rrr) "Hrr"...
        iApply brel_na_close.
        iFrame. 
        iSplitR "HQ Hsrl Hsrr Hrl Hrr"; [iRight; iRight; iExists _,_; iFrame "#"; iFrame|].
        iApply (brel_bind'' _ _ (to_iThyIfMono OS (iLblSig_to_iLblThy autheff)) _ _ _ (arcv_l _) (arcv_r _)).
        3 : { iApply to_iThy_le_intro'. 
              eassert (_ :: _ = [_] ++ _) as -> by done.
              eapply submseteq_app_middle. simpl.
              apply singleton_submseteq_l. constructor. }
        1,2 : set_unfold; tauto.
        iApply brel_mono; [iApply to_iThy_le_refl| |simpl].
        { iApply "Harcv". iExists _,_; by iLeft. }
        iIntros (v1' v2') "(%&%&[(->&->&->&->)|(->&->&->&->)])"...
        { brel_cont_l. brel_cont_r...
          brel_cont_l. brel_cont_r...
          iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"]. 
          iDestruct "HQ" as "[_ $]". }
        brel_load_r.
        brel_load_l...
        brel_cont_l. brel_cont_r...
        brel_load_l...
        rewrite (vgval_fvtval (g ^+ f_inv keyf x)%g).
        iApply (brel_dec_enc_correct_r (SYM := SKE)); first done.
        brel_cont_l. 
        iApply (brel_cont_r with "Hsrr")... 
        iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"]. 
        iDestruct "HQ" as "[HQ _]".
        iApply "HQ".
  Qed. 

  Lemma sc_real_game1 : 
    ⊢ sem_typed [] sc_real game1 ⊥ τsc [].
  Proof using All with (brel_pures'; repeat foldkont). 
    iIntros (?) "!# _ //=". 
    rewrite /sc_real /reduction /CHAN /RED_CHAN /F_OAUTH /F_KE_lazy_alice /right_composition /enc_real_tape /func_comp...
    iModIntro. iSplit; last done.
    iIntros (θL f1 f2) "Hff"...
    iIntros "!>" (autheff keyeff autheffkeyeff_l autheffkeyeff_r) "Hauthkey".
    iDestruct "Hauthkey" as (w1 w1' w2 w2') "[-> [-> [Hautheff Hkeyeff]]]"...
    iDestruct "Hautheff" as (asnd_l asnd_r arcv_l arcv_r) "(-> & -> & (#Hasnd & #Harcv))"...
    iDestruct "Hkeyeff" as (kysnd_l kysnd_r kyrcv_l kyrcv_r) "(-> & -> & (#Hkeysnd & #Hkeyrcv))"...
    


    (* Allocation/initialization *)
    brel_alloctape_l γl as "Hγl"...
    brel_alloctape_r γr as "Hγr"...
    brel_alloc_l lcl as "Hlcl"...
    brel_alloc_r lcr as "Hlcr"...
    brel_effect_l gkl as "Hgkl".
    brel_effect_r gkr as "Hgkr"...
    brel_alloc_l laml as "Hlaml".
    brel_alloc_r lamr as "Hlamr"...
    brel_effect_l sl as "Hsl".
    brel_effect_r sr as "Hsr"...
    brel_effect_l rl as "Hrl".
    brel_effect_r rr as "Hrr"...
    brel_alloc_l lml as "Hlml".
    brel_alloctape_r (ι) as "Hι"... (* Initialization of encryption scheme *)
    brel_alloc_r lmr as "Hlmr"...
    brel_effect_l ssl as "Hssl".
    brel_effect_r ssr as "Hssr"...
    brel_effect_l srl as "Hsrl".
    brel_effect_r srr as "Hsrr"...

    (* Setting up clients *)
    set (θ := client_row  sl rl sr rr gkl gkr ssl srl ssr srr).
    iSpecialize ("Hff" $! θ).
    unfold sem_ty_arr, sem_ty_mbang. simpl.
    iAssert (sem_val_typed  ((λ: "m", do: ssl "m"), (λ: <>, do: srl bob))%V ((λ: "m", do: ssr "m") , (λ: <>, do: srr bob))%V (((sem_ty_nat -{ θ }-> 𝟙) × (𝟙 -{ θ }-> (Option msg.(sem_τFT))))%T)) as "Hschn".
    { iApply SEM_TYPED_EFF. }
     unfold sem_val_typed. simpl.
    iDestruct "Hschn" as "#Hschn".
    iSpecialize ("Hff" with "Hschn"). 

    (* Theories *)
    iApply brel_new_theory.
    iApply (brel_add_label_l with "Hssl").
    iApply (brel_add_label_l with "Hsrl").
    iApply (brel_add_label_r with "Hssr").
    iApply (brel_add_label_r with "Hsrr").
    iApply (brel_add_label_l with "Hgkl").
    iApply (brel_add_label_r with "Hgkr").
    iApply (brel_add_label_l with "Hrl").
    iApply (brel_add_label_l with "Hsl").
    iApply (brel_add_label_r with "Hsr").
    iApply (brel_add_label_r with "Hrr"). 

    iApply brel_learn. iIntros "%Hdist' _".
    assert (NoDup [sl; rl; gkl; srl; ssl]) as Hnd_l.
    { unfold distinct in Hdist'. destruct Hdist' as [Hd' _].
      unfold distinct_l in Hd'. simpl in Hd'.
      repeat (rewrite -> labels_l_cons in Hd').
      by (eapply NoDup_app in Hd'; destruct Hd' as [Hd' _]). }
    
    assert (NoDup [rr; sr; gkr; srr; ssr]) as Hnd_r.
    { unfold distinct in Hdist'. destruct Hdist' as [_ Hd'].
      unfold distinct_r in Hd'. simpl in Hd'.
      rewrite !labels_r_cons in Hd'.
      by (eapply NoDup_app in Hd'; destruct Hd' as [Hd' _]). }

    (* Invariants *)
    rewrite vg_fvt_card. assert (S n - 1 = n)%Z as -> by lia.
    rewrite Nat2Z.id.
    iAssert ((Loc ι) ↪ₛN (n; []))%I with "[Hι]" as "Hι". 
    { iExists []. simpl. iFrame. done. }
    iAssert (γr ↪ₛN (n; []))%I with "[Hγr]" as "Hγr". 
    { iExists []. simpl. iFrame. done. }
    iDestruct (spec_tape_to_persistent with "Hγr") as ">#Hγr".
    (* Couple Alice's exponent tape [γl] with [game1]'s key tape [ι] along
       [keyf]: the left draws the DH exponent [x], the right draws the symmetric
       key [keyf x], which is exactly the key the left derives from [x]. *)
    iApply (brel_couple_TT _ n keyf).
    { apply keyf_dom. }
    iSplitL "Hγl"; first (iNext; iFrame); iSplitL "Hι"; first iFrame.
    iIntros (x) "(Hγl&Hι) //=".
    iDestruct (tapeN_hd_bound with "Hγl") as "(%Hx&Hγl)".
    
    iApply (brel_na_alloc ((lml ↦ NONEV ∗ lcl ↦ NONEV ∗ lmr ↦ₛ NONEV ∗ lcr ↦ₛ NONEV ∗ laml ↦ NONEV ∗ lamr ↦ₛ NONEV
                           ∗ γl ↪N (n; [x]) ∗ (Loc ι) ↪ₛN (n; [keyf x]))
                           ∨ (∃ (c' : nat) (mv : mt), lml ↦□ SOMEV (fvtval mv) ∗ lcl ↦□ SOMEV #x ∗ lmr ↦ₛ□ SOMEV (fvtval mv) ∗ lcr ↦ₛ□ SOMEV #c'
                                            ∗ laml ↦ NONEV ∗ lamr ↦ₛ NONEV
                                            ∗ γl ↪□N (n; []))
                           ∨ (∃ (c' : nat) (mv : mt) (cv : ct), □ P  (key := vg_fv) (g ^+ x)%g mv cv ∗ lml ↦□ SOMEV (fvtval mv) ∗ lcl ↦□ SOMEV #x ∗ lmr ↦ₛ□ SOMEV (fvtval mv) ∗ lcr ↦ₛ□ SOMEV #c'
                                            ∗ laml ↦□ SOMEV (fvtval cv) ∗ lamr ↦ₛ□ SOMEV (fvtval cv)
                                            ∗ γl ↪□N (n; []) ∗ (Loc ι) ↪ₛ□N (n; []))
              ) alphaN).
    iSplitL "Hlml Hlmr Hlcl Hlcr Hγl Hι Hlaml Hlamr"; [iNext; iLeft; iFrame|].
    iIntros "#HI".

    (* Case on the clients behaviour and induction *)
    rewrite !iLblSig_to_iLblThy_app !iThyIfMono_iLblSig_to_iThyIfMono.
    iDestruct (brel_introduction_mono _ (([sl; rl; gkl; srl; ssl], [rr; sr; gkr; srr; ssr], sec_channel ssl ssr srl srr : iThy Σ) :: to_iThyIfMono OS (iLblSig_to_iLblThy autheff) ++ to_iThyIfMono OS (iLblSig_to_iLblThy keyeff) ++ iLblSig_to_iLblThy θL) with "[][$Hff]") as "Hff".
    { iApply to_iThy_le_intro'. solve_submseteq. }
    iApply ((brel_exhaustion (f1 _) ( f2 _)) with "[$Hff]"); [set_solver|set_solver| ].
    
    iLöb as "IH".
    iSplit; [iIntros (v1 v2) "%Hv1v2 !>"; by brel_pures'|].
    iIntros (?????) "!# %Hk1 %Hk2 [(%m&(->&->)&HQ)|(->&->&HQ)] #Hrel".
    (* Alice tries to send a message m *)
    - 
      brel_handle_os_l (rssl) as "Hssl".
      brel_handle_os_r (rssr) as "Hssr"...
      destruct (fvt_of_int_sem (fin_val := msg) m) as [mv|] eqn:Hmv.
      2 : { iApply (brel_fvt_of_int_none_l (fin_val := msg)); first exact Hmv.
            iApply (brel_fvt_of_int_none_r (fin_val := msg)); first exact Hmv...
             brel_cont_l. 
             brel_cont_r.
            iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V) with "[HQ]"); [set_solver|set_solver|by iApply "Hrel"|iApply "IH"]. }
      iApply (brel_fvt_of_int_correct_l (fin_val := msg)); first exact Hmv.
      iApply (brel_fvt_of_int_correct_r (fin_val := msg)); first exact Hmv...
      iApply (brel_na_inv _ _ alphaN); first set_solver.
      iFrame "HI".
      iIntros "([>(Hlml&Hlcl&Hlmr&Hlcr&Hlaml&Hlamr&Hγl&Hι)|[>H2|H3]]&Hclose)".
      + brel_load_l...
        brel_load_r...
        brel_store_l...
        brel_store_r...
        iApply (brel_handle_os_l [] [HandleCtx _ _ _ _ _;HandleCtx _ _ _ _ _;HandleCtx _ _ _ _ _;AppRCtx _]).
        { eapply NoDup_cons_1_1. simpl.
          eapply (submseteq_NoDup _ [sl; rl; gkl; srl; ssl]); [solve_submseteq|exact Hnd_l]. }
        iIntros (rgkl) "!> Hrgkl"...
        iApply (brel_handle_os_r [] [HandleCtx _ _ _ _ _;HandleCtx _ _ _ _ _;HandleCtx _ _ _ _ _;AppRCtx _]).
        { eapply NoDup_cons_1_1. simpl.
          eapply (submseteq_NoDup _ [rr; sr; gkr; srr; ssr]); [solve_submseteq | exact Hnd_r]. }
        iIntros (rgkr) "Hrgkr"...
        brel_load_l...
        brel_load_r...
        brel_rand_l...
        iApply brel_randT_empty_r. 
        iSplitR; first by iFrame "#".
        iIntros (c') "_ _".
        brel_store_l...
        brel_store_r...

        iMod (ghost_map_elem_persist with "Hlml") as "#Hlml".
        iMod (ghost_map_elem_persist with "Hlcl") as "#Hlcl".
        iMod (ghost_map_elem_persist with "Hlmr") as "#Hlmr".
        iMod (ghost_map_elem_persist with "Hlcr") as "#Hlcr".
        iDestruct (tapeN_to_persistent with "Hγl") as ">#Hγl".
        iApply brel_na_close. iFrame.
        iSplitL "Hlaml Hlamr".
        { iModIntro. iRight. iLeft. iExists _, _. iFrame "#". iFrame. }
        
        iApply (brel_bind'' [AppRCtx _] [AppRCtx _] (to_iThyIfMono OS (iLblSig_to_iLblThy keyeff))); try (apply list_subseteq_nil).
        { iApply to_iThy_le_intro'. solve_submseteq. }
        iApply brel_mono; [iApply to_iThy_le_refl| |simpl].
        { iApply "Hkeysnd". iExists _, _. by iLeft. }
        iIntros (v1 v2) "(->&->)"...
        iApply (brel_bind'' [AppRCtx _] [AppRCtx _] (to_iThyIfMono OS (iLblSig_to_iLblThy keyeff))); try (apply list_subseteq_nil).
        { iApply to_iThy_le_intro'. solve_submseteq. }
        iApply brel_mono; [iApply to_iThy_le_refl| |simpl].
        { iApply "Hkeyrcv". iExists _, _. by iLeft. }
        iIntros (v1' v2') "(%&%&[(->&->&->&->)|(->&->&->&->)])"...
        { brel_cont_l... brel_cont_l. 
          brel_cont_r... brel_cont_r...
          iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V) with "[HQ]"); [set_solver|set_solver|by iApply "Hrel"|iApply "IH"]. }
        brel_cont_l. 
        brel_cont_r...
        brel_rand_r...
        (* [enc_real_tape] decodes the key code [keyf x] it just drew; by
           [vg_of_int_sem_keyf] that is the DH key [g ^+ x] the left-hand side
           derived from its exponent, so both sides encrypt under the same key. *)
        iApply brel_vg_of_int_correct_r; first (by apply vg_of_int_sem_keyf).
        brel_pures'.
        iApply (brel_bind _ _ _ [] _ _ (enc (ks := vg_fv) (ms := ms)_ _) (enc (ks := vg_fv) (ms := ms)_ _)); 
          [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
        assert (to_iThyIfMono OS [] = []) as <- by done.
        iApply brel_mono; first iApply to_iThy_le_refl.
        { iApply (brel_enc_couple (key := vg_fv) (msg := msg)). }
        simpl.
        iIntros (??) "(%c&->&->&#P)".
        brel_pures'; simpl.
        iApply (brel_handle_os_l _ [HandleCtx _ _ _ _ _;AppRCtx _]).
        { eapply NoDup_cons_1_1.
          eapply (submseteq_NoDup _ [sl; rl; gkl; srl; ssl]); [solve_submseteq|exact Hnd_l]. }
        iIntros (rsl) "!> Hsl"...
        iApply (brel_handle_os_r _ [HandleCtx _ _ _ _ _;AppRCtx _]).
        { eapply NoDup_cons_1_1.
          eapply (submseteq_NoDup _ [rr; sr; gkr; srr; ssr]); [solve_submseteq|exact Hnd_r]. }
        iIntros (rsr) "Hsr"...
        iApply (brel_na_inv _ _ alphaN); first set_solver.
        iFrame "HI".
        iIntros "([>(_&_&_&_&_&_&_&Hι')|[>(%&%&_&_&_&_&Hlaml&Hlamr&_)|(%&%&%&_&_&_&_&_&_&_&_&>Hι')]]&Hclose)".
        (* The key tape [ι] has already been read, so the "fresh" and the
           "already sent" disjuncts are both impossible: each hands back an
           assertion for [ι] that cannot coexist with the one we hold. *)
        3 : { iExFalso. iApply (spec_tapeN_excl with "Hι Hι'"). }
        1 : { iExFalso. iApply (spec_tapeN_excl with "Hι Hι'"). }
        brel_load_l...
        brel_load_r...
        brel_store_l...
        brel_store_r...

        iMod (ghost_map_elem_persist with "Hlaml") as "#Hlaml".
        iMod (ghost_map_elem_persist with "Hlamr") as "#Hlamr".
        iDestruct (spec_tape_to_persistent with "Hι") as ">#Hι".
        iApply brel_na_close.
        iFrame. iSplitR; [iNext; do 2 iRight; iExists _,_; iFrame "#"|].
        iApply (brel_bind'' _ _ (to_iThyIfMono OS (iLblSig_to_iLblThy autheff)) _ _ _ (asnd_l _) (asnd_r _)).
        3 : { iApply to_iThy_le_intro'. 
              eassert (_ :: _ = [_] ++ _) as -> by done.
              eapply submseteq_app_middle. simpl.
              apply singleton_submseteq_l. constructor. }
        1,2 : set_unfold; tauto.
        iApply brel_mono; [iApply to_iThy_le_refl| |simpl].
        { iApply "Hasnd". iExists _, _, _, _. 
          repeat (iSplit; first done). 
          iSplit; last (iExists _,_; by iLeft). 
          by iExists _. }
        iIntros (v1'' v2'') "(->&->)"...
        brel_cont_l... brel_cont_l.
        brel_cont_r... brel_cont_r...
        iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V) with "[HQ]"); [set_solver|set_solver|by iApply "Hrel"|iApply "IH"].
      + iDestruct "H2" as "(%&%&Hlml&Hlcl&Hlmr&Hlcr&Hγ)".
        brel_load_l.
        brel_load_r...
        iApply brel_na_close.
        iFrame. 
        iSplitR "HQ Hssl Hssr"; [iRight; iLeft; iExists _,_; iFrame|].
        brel_cont_l. brel_cont_r...
        iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V) with "[HQ]"); [set_solver|set_solver|by iApply "Hrel"|iApply "IH"].
      + iDestruct "H3" as "(%&%&%&HP&Hlml&>Hlcl&Hlmr&Hlaml&Hlamr&Hι)".
        brel_load_l.
        brel_load_r...
        iApply brel_na_close.
        iFrame. 
        iSplitR "HQ Hssl Hssr"; [iRight; iRight; iExists _,_; iFrame|].
        brel_cont_l. brel_cont_r...
        iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V) with "[HQ]"); [set_solver|set_solver|by iApply "Hrel"|iApply "IH"].
    (* Bob tries to receive a message *)
    - brel_pures'.
      iApply (brel_handle_os_l _ ([HandleCtx _ _ _ _ _] ++ k1')).
      {  apply not_elem_of_cons; split; last (apply neutral_ectx; repeat constructor).
         intro Heq.
         apply NoDup_ListNoDup in Hnd_l.
         do 4 (apply NoDup_cons_iff in Hnd_l as [?Hn Hnd_l]). 
         apply Hn2. by left. }
      iIntros (rsrl) "!> Hsrl"...
      iApply (brel_handle_os_r _ ([HandleCtx _ _ _ _ _] ++ k2')).
      {  apply not_elem_of_cons; split; last (apply neutral_ectx; repeat constructor).
         intro Heq.
         apply NoDup_ListNoDup in Hnd_r.
         do 4 (apply NoDup_cons_iff in Hnd_r as [?Hn Hnd_r]). 
         apply Hn2. by left. }
      iIntros (rsrr) "Hsrr"...
      repeat foldkont.
      iApply (brel_handle_os_l [] [HandleCtx _ _ _ _ _;HandleCtx _ _ _ _ _;AppRCtx _]).
      { eapply NoDup_cons_1_1. simpl.
        eapply (submseteq_NoDup _ [sl; rl; gkl; srl; ssl]); [solve_submseteq|exact Hnd_l]. }
      iIntros (rgkl) "!> Hrgkl"...
      iApply (brel_handle_os_r [] [HandleCtx _ _ _ _ _;HandleCtx _ _ _ _ _;AppRCtx _]).
      { eapply NoDup_cons_1_1. simpl.
        eapply (submseteq_NoDup _ [rr; sr; gkr; srr; ssr]); [solve_submseteq | exact Hnd_r]. }
      iIntros (rgkr) "Hrgkr"...
      iApply (brel_bind'' [AppRCtx _] [AppRCtx _] (to_iThyIfMono OS (iLblSig_to_iLblThy keyeff))); try (apply list_subseteq_nil).
      { iApply to_iThy_le_intro'. solve_submseteq. }
      iApply brel_mono; [iApply to_iThy_le_refl| |simpl].
      { iApply "Hkeyrcv". iExists _, _. by iRight. }
      iIntros (v1' v2') "(%&%&[(->&->&->&->)|(->&->&->&->)])"...
      { brel_cont_l. brel_cont_r...  brel_cont_l. brel_cont_r...
        iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"]. 
        iDestruct "HQ" as "[_ $]". }
      iApply (brel_bind'' [AppRCtx _] [AppRCtx _] (to_iThyIfMono OS (iLblSig_to_iLblThy keyeff))); try (apply list_subseteq_nil).
      { iApply to_iThy_le_intro'. solve_submseteq. }
      iApply brel_mono; [iApply to_iThy_le_refl| |simpl].
      { iApply "Hkeysnd". iExists _, _. by iRight. }
      iIntros (v1 v2) "(->&->)"...      
      iApply (brel_na_inv _ _ alphaN); first set_solver.
      iFrame "HI".
      iIntros "([>(Hlml&Hlcl&Hlmr&Hlcr&Hlaml&Hlamr&Hγl&Hι)|[>H2|H3]]&Hclose)".
      + brel_load_l...
        brel_load_r...
        brel_cont_l.
        brel_cont_r...
        brel_cont_l.
        brel_cont_r...
        iApply brel_na_close.
        iFrame. 
        iSplitR "HQ"; [iLeft; iFrame|].
        iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"].
        iDestruct "HQ" as "[_ $]".
      + iDestruct "H2" as "(%&%&#Hlml&#Hlcl&#Hlmr&#Hlcr&Hlaml&Hlamr&#Hγ)".
        brel_load_l...
        brel_load_r...
        brel_cont_l.
        brel_cont_r...
        iApply (brel_handle_os_l _ [HandleCtx _ _ _ _ _; AppRCtx _]).
        { eapply NoDup_cons_1_1. simpl.
          eapply (submseteq_NoDup _ [sl; rl; gkl; srl; ssl]); [solve_submseteq|exact Hnd_l]. }
        iIntros (rrl) "!> Hrl"...
        iApply (brel_handle_os_r _ [HandleCtx _ _ _ _ _; AppRCtx _]).
        { eapply NoDup_cons_1_1. simpl.
          eapply (submseteq_NoDup _ [rr; sr; gkr; srr; ssr]); [solve_submseteq | exact Hnd_r]. }        
        iIntros (rrr) "Hrr"...
        iApply brel_na_close.
        iFrame. 
        iSplitR "HQ Hsrl Hsrr Hrl Hrr"; [iRight; iLeft; iExists _,_; iFrame "#"; iFrame|].
        iApply (brel_bind'' _ _ (to_iThyIfMono OS (iLblSig_to_iLblThy autheff)) _ _ _ (arcv_l _) (arcv_r _)).
        3 : { iApply to_iThy_le_intro'. 
              eassert (_ :: _ = [_] ++ _) as -> by done.
              eapply submseteq_app_middle. simpl.
              apply singleton_submseteq_l. constructor. }
        1,2 : set_unfold; tauto.
        iApply brel_mono; [iApply to_iThy_le_refl| |simpl].
        { iApply "Harcv". iExists _,_; by iLeft. }
        iIntros (v1' v2') "(%&%&[(->&->&->&->)|(->&->&->&->)])"...
        { brel_cont_l.
          brel_cont_r...
          brel_cont_l.
          brel_cont_r...
          iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"]. 
          iDestruct "HQ" as "[_ $]". }
        iApply (brel_na_inv _ _ alphaN); first set_solver.
        iFrame "HI".
        iIntros "([>(Hlml'&H')|[>H2|H3]]&Hclose)".
        (* [lml] already holds the message (persistently), so the "fresh"
           disjunct of the invariant is impossible. *)
        { iExFalso. by iDestruct (ghost_map_elem_ne with "Hlml' Hlml") as %?. }
        * iDestruct "H2" as "(%&%&_&_&_&_&Hlaml&Hlamr&_)".
          brel_load_l...
          brel_load_r... 
          brel_cont_l.
          brel_cont_r...
          brel_cont_l.
          brel_cont_r...
          iApply brel_na_close.
          iFrame. 
          iSplitR "HQ"; [iRight; iLeft; iExists _,_; iFrame "#"; iFrame|].
          iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"]. 
          iDestruct "HQ" as "[_ $]".
        * iDestruct "H3" as "(%&%&%&#HP&>Hlml'&_&_&_&Hlaml&Hlamr&Hγl3&Hι)".
          iDestruct (ghost_map_elem_agree with "Hlml Hlml'") as "->".
          brel_load_l.
          brel_load_r...
          brel_cont_l.
          brel_cont_r...
          brel_load_r...
          brel_cont_r.
          iApply brel_na_close.
          iFrame. 
          iSplitR "HQ Hsrl"; [iNext;iRight; iRight; iExists _,_; iFrame "#"; iFrame|]...

          rewrite (vgval_fvtval (g ^+ x)%g).
          iApply (brel_dec_enc_correct_l (SYM := SKE)); first done.
          iApply (brel_cont_l with "Hsrl").
          iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"]. 
          iDestruct "HQ" as "[HQ _]".
          iApply "HQ".
      + iDestruct "H3" as "(%&%&%&#HP&#Hlml&#Hlcl&#Hlcr&#Hlmr&#Hlaml&#Hlamr&#Hγl&#Hι)".
        brel_load_l.
        brel_load_r...
        brel_cont_l.
        brel_cont_r...
        iApply (brel_handle_os_l _ [HandleCtx _ _ _ _ _; AppRCtx _]).
        { eapply NoDup_cons_1_1. simpl.
          eapply (submseteq_NoDup _ [sl; rl; gkl; srl; ssl]); [solve_submseteq|exact Hnd_l]. }
        iIntros (rrl) "!> Hrl"...
        iApply (brel_handle_os_r _ [HandleCtx _ _ _ _ _; AppRCtx _]).
        { eapply NoDup_cons_1_1. simpl.
          eapply (submseteq_NoDup _ [rr; sr; gkr; srr; ssr]); [solve_submseteq | exact Hnd_r]. }        
        iIntros (rrr) "Hrr"...
        iApply brel_na_close.
        iFrame. 
        iSplitR "HQ Hsrl Hsrr Hrl Hrr"; [iRight; iRight; iExists _,_; iFrame "#"; iFrame|].
        iApply (brel_bind'' _ _ (to_iThyIfMono OS (iLblSig_to_iLblThy autheff)) _ _ _ (arcv_l _) (arcv_r _)).
        3 : { iApply to_iThy_le_intro'. 
              eassert (_ :: _ = [_] ++ _) as -> by done.
              eapply submseteq_app_middle. simpl.
              apply singleton_submseteq_l. constructor. }
        1,2 : set_unfold; tauto.
        iApply brel_mono; [iApply to_iThy_le_refl| |simpl].
        { iApply "Harcv". iExists _,_; by iLeft. }
        iIntros (v1' v2') "(%&%&[(->&->&->&->)|(->&->&->&->)])"...
        { brel_cont_l.
          brel_cont_r...
          brel_cont_l.
          brel_cont_r...
          iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"]. 
          iDestruct "HQ" as "[_ $]". }
        brel_load_l.
        brel_load_r...
        brel_cont_l. brel_cont_r...
        brel_load_r...
        rewrite (vgval_fvtval (g ^+ x)%g).
        iApply (brel_dec_enc_correct_l (SYM := SKE)); first done.
        brel_cont_r. 
        iApply (brel_cont_l with "Hsrl")... 
        iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"]. 
        iDestruct "HQ" as "[HQ _]".
        iApply "HQ".
  Qed. 

End schan_security.

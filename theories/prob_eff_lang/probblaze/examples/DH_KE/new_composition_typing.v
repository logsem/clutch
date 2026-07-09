From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import agree excl auth frac excl_auth.
From iris.algebra.lib Require Import dfrac_agree.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import
  logic primitive_laws proofmode
  spec_rules spec_ra class_instances tactics notation valgroup metatheory
  sem_types sem_row sem_sig sem_env sem_judgement sem_def
  def_dhke sec_channel_def xor sec_channel_prf dhke_channel_lazy_results dhke_channel_lazy_authchan
  new_composition_defs.
From clutch.prob_eff_lang.probblaze.typing Require Import fundamental.

Import fingroup.
Import fingroup.fingroup.

Import valgroup_tactics.

(* ------------------------------------------------------------------ *)
(* Semantic typing of the building blocks.                            *)
(*                                                                    *)
(* Each of these is a term related to itself at a semantic type.  All *)
(* the types below are meant to be in the image of the interpretation *)
(* ⟦·⟧ of the syntactic types, so each lemma can (in a later step) be *)
(* discharged by applying the fundamental lemma of the logical        *)
(* relation to a syntactic typing derivation:                         *)
(*   - 𝔾 = ⟦τG⟧ (the clutch-group syntactic type),                    *)
(*   - Option = sem_ty_option,                                        *)
(*   - the row parameters range over ⟦row-variables⟧,                 *)
(*   - products/sums/arrows/∀ᵣ/row-unions all have syntactic formers. *)
(*                                                                    *)
(* For now they are admitted; the interface definitions below may     *)
(* need minor adjustments once the proofs are carried out.  This file *)
(* only imports the base theory, so it can be iterated on quickly.    *)
(* ------------------------------------------------------------------ *)

Section new_comp_verification.
  Context `{probblazeRGS Σ}.
  Context (channel leaksec channel1 channel2 getKey1 getKey2 leakauth1 leakauth2 keyleak1 keyleak2 schannel1 schannel2 l1 l2 l2': label).
  Context {vg: val_group}.
  Context {cg: clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg: @val_group_generator vg}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO,!inG Σ (dfrac_agreeR valO)}.
  (* The group index [int_of_vg_sem g] is bounded by the group order
     [#|[set : vgG]| = S (S n'')] (class field [int_of_vg_sem_bound] +
     [vgG_card]); in particular it is [< S (S (S n''))]. *)
  Lemma Bdd_int_vg : ∀ g : vgG, (int_of_vg_sem g < S (S (S n'')))%nat.
  Proof using Type*.
    intros g. pose proof (int_of_vg_sem_bound g) as Hb.
    rewrite vgG_card in Hb. lia.
  Qed.
  Let Key := S (S n'').
  Let Support := S (S n'').
  Variable xor_struct : XOR (Key := Key) (Support := Support).
  Context `{!XOR_spec (Key := Key) (Support := Support) (H := xor_struct)}.

  Import valgroup_notation.

  (* Interface families (each parametrised by the effect row of its ops).*)
  (* [chan]   : authenticated channel — group send, group recv.          *)
  (* [oaleak] : F_OAUTH's leak — group send, recv only leaks presence.    *)
  (* [leakI]  : direction-only send/recv (unit messages).                 *)
  (* [gk]     : the getKey operation.                                     *)
  (* [cli]    : the top-level secure-channel client interface.            *)
  Definition chan (θ : sem_row Σ) : sem_ty Σ :=
    (((𝔾 × (𝟙 + 𝟙)) -{ θ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ }-> Option 𝔾))%T.
  Definition oaleak (θ : sem_row Σ) : sem_ty Σ :=
    (((𝔾 × (𝟙 + 𝟙)) -{ θ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ }-> Option 𝟙))%T.
  Definition leakI (θ : sem_row Σ) : sem_ty Σ :=
    (((𝟙 + 𝟙) -{ θ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ }-> Option 𝟙))%T.
  Definition gk (θ : sem_row Σ) : sem_ty Σ := ((𝟙 + 𝟙) -{ θ }-> Option 𝔾)%T.
  Definition cli (θ : sem_row Σ) : sem_ty Σ :=
    ((𝔾 -{ θ }-> 𝟙) × (𝟙 -{ θ }-> Option 𝔾))%T.
  (* the handler consuming an interface I, polymorphic over I's row *)
  Definition hdl (I : sem_row Σ -> sem_ty Σ) (θ : sem_row Σ) : sem_ty Σ :=
    (∀ᵣ θ', I θ' -{ sem_row_union θ' θ }-∘ 𝟙)%T.

  (* Atomic functionalities, as effect-handler transformers (τ__F τ τ' takes
     a τ'-consuming handler to a τ-consuming handler). *)

  (* ----------------------------------------------------------------- *)
  (* Effect theory for [F_OAUTH]'s [channel] effect.                    *)
  (*                                                                    *)
  (* F_OAUTH gives its client [f] a [chan]-interface: [doSend] takes a  *)
  (* (group, direction) and returns unit; [doRecv] takes a direction    *)
  (* and returns [Option 𝔾].  We cannot type this syntactically as a    *)
  (* self-refinement because F_OAUTH forwards the client's [Recv] to     *)
  (* the environment's [doLeakRecv : dir → Option 𝟙] (a presence flag)   *)
  (* while returning [!message : Option 𝔾] to the client's continuation. *)
  (* Instead we relate F_OAUTH to itself in BREL, running both copies    *)
  (* in lockstep with a plain invariant tying the two message refs.      *)
  (*                                                                    *)
  (* [OASend]/[OARecv] are the two branches of the [channel] theory the *)
  (* client raises through [doSend]/[doRecv]; the [Send] branch returns  *)
  (* unit, the [Recv] branch returns an [Option 𝔾].                      *)
  Program Definition OASend (c1 c2 : label) : iThy Σ :=
    (λ e1 e2, λne Q,
      ∃ (m1 m2 dst1 dst2 : val),
        𝔾 m1 m2 ∗ (𝟙 + 𝟙)%T dst1 dst2 ∗
        ⌜ e1 = do: c1 (SendV (m1, dst1)) ⌝%E ∗
        ⌜ e2 = do: c2 (SendV (m2, dst2)) ⌝%E ∗
        □ (Q #()%V #()%V))%I.
  Next Obligation. solve_proper. Qed.

  Program Definition OARecv (c1 c2 : label) : iThy Σ :=
    (λ e1 e2, λne Q,
      ∃ (from1 from2 : val),
        (𝟙 + 𝟙)%T from1 from2 ∗
        ⌜ e1 = do: c1 (RecvV from1) ⌝%E ∗
        ⌜ e2 = do: c2 (RecvV from2) ⌝%E ∗
        □ (Q NONEV NONEV ∗ ∀ m : vgG, Q (SOMEV m) (SOMEV m)))%I.
  Next Obligation. solve_proper. Qed.

  Program Definition oachan_mono (c1 c2 : label) :=
    {| pmono_prot_car := iThySum (OASend c1 c2) (OARecv c1 c2); pmono_prot_prop := _ |}.
  Next Obligation.
    intros ??.
    iIntros (????) "#HΦ [H|H]".
    - iLeft. iDestruct "H" as (????) "(HG&Hd&%&%&#H)".
      iExists _,_,_,_. iFrame. repeat (iSplit; first done). iModIntro. by iApply "HΦ".
    - iRight. iDestruct "H" as (??) "(Hd&%&%&#(H1&H2))".
      iExists _,_. iFrame. repeat (iSplit; first done). iModIntro.
      iSplitL; [by iApply "HΦ"|]. iIntros (m); by iApply "HΦ".
  Qed.

  Definition oachan (c1 c2 : label) := @SemSig Σ (oachan_mono c1 c2) (c1, c2).
  Program Definition oachan_row (c1 c2 : label) := SemRow [([c1],[c2], oachan c1 c2)] _.
  Next Obligation.
    intros ??.
    iIntros (????) "#HΦ % % % ($&H)". iDestruct "H" as (?????) "(->&%&->&%&HX&#H)".
    iExists _,_,_,_,_.
    repeat (iSplit; first done). iIntros (??) "!# HS". iApply "HΦ". by iApply "H".
  Qed.

  Lemma F_OAUTH_typed :
    ⊢ sem_val_typed F_OAUTH F_OAUTH (τ__F oaleak chan).
  Proof using Type*.
    rewrite /sem_val_typed /τ__F //=.
    iModIntro. iIntros (θ).
    iIntros (f1 f2) "Hff".
    unfold F_OAUTH. brel_pures'. iModIntro. iIntros (θ₂).
    iIntros (LeakOp1 LeakOp2) "HLeak".
    iDestruct "HLeak" as (dls1 dls2 dlr1 dlr2) "(->&->&#Hls&#Hlr)".
    brel_pures'.
    iApply brel_alloc_l. iIntros (lm) "!> Hlm".
    brel_pures_l.
    iApply brel_alloc_r. iIntros (lm') "Hlm'".
    brel_pures_r.
    iApply (brel_na_alloc (∃ v1 v2, lm ↦ v1 ∗ lm' ↦ₛ v2 ∗ (Option 𝔾)%T v1 v2)%I
                          (nroot .@ "oamsg")).
    iSplitL "Hlm Hlm'".
    { iNext. iExists _, _. iFrame. iExists _,_. iLeft. done. }
    iIntros "#Hinv".
    iApply brel_effect_l. iIntros (chan1) "!> Hchan1".
    iApply brel_effect_r. iModIntro. iIntros (chan2) "Hchan2 !>".
    brel_pures'.
    (* Build the (doSend,doRecv) pair related at [chan (oachan_row chan1 chan2)]. *)
    iAssert (chan (oachan_row chan1 chan2)
               (λ: "m", do: chan1 InjL "m", λ: "m", do: chan1 InjR "m")%V
               (λ: "m", do: chan2 InjL "m", λ: "m", do: chan2 InjR "m")%V) as "#Hops".
    { iExists _, _, _, _. iSplit; [done|]. iSplit; [done|].
      rewrite /sem_ty_mbang /=. iSplit.
      - iModIntro. iIntros (a1 a2) "Ha".
        iDestruct "Ha" as (m1 m2 d1 d2) "(->&->&#Hm&#Hd)".
        brel_pures'.
        iApply (brel_introduction' [chan1] [chan2]
                  (iThySum (OASend chan1 chan2) (OARecv chan1 chan2))); [ by left | ].
        rewrite /iThyTraverse /=.
        iExists _, _, [], [], (λ s1 s2, ⌜ s1 = Val #()%V ⌝ ∗ ⌜ s2 = Val #()%V ⌝)%I.
        iSplit; [done|]. iSplit; [iPureIntro; apply NeutralEctx_nil|].
        iSplit; [done|]. iSplit; [iPureIntro; apply NeutralEctx_nil|].
        iSplitL.
        + iLeft. iExists m1, m2, d1, d2. iFrame "Hm Hd". do 2 (iSplit; [done|]).
          iModIntro. iSplit; done.
        + iIntros "!>" (s1 s2) "(->&->)". iApply brel_value. iIntros "$ !>". done.
      - iModIntro. iIntros (a1 a2) "#Hfr".
        brel_pures'.
        iApply (brel_introduction' [chan1] [chan2]
                  (iThySum (OASend chan1 chan2) (OARecv chan1 chan2))); [ by left | ].
        rewrite /iThyTraverse /=.
        iExists _, _, [], [],
          (λ s1 s2, ∃ v1 v2 : val, ⌜ s1 = Val v1 ⌝ ∗ ⌜ s2 = Val v2 ⌝ ∗ (Option 𝔾)%T v1 v2)%I.
        iSplit; [done|]. iSplit; [iPureIntro; apply NeutralEctx_nil|].
        iSplit; [done|]. iSplit; [iPureIntro; apply NeutralEctx_nil|].
        iSplitL.
        + iRight. iExists a1, a2. iFrame "Hfr". do 2 (iSplit; [done|]).
          iModIntro. iSplit.
          * iExists NONEV, NONEV. do 2 (iSplit; [done|]). iExists _,_. iLeft. done.
          * iIntros (m). iExists (SOMEV m), (SOMEV m). do 2 (iSplit; [done|]).
            iExists _,_. iRight. iSplit; [done|]. iSplit; [done|]. iExists m. done.
        + iIntros "!>" (s1 s2) "(%v1&%v2&->&->&#Hopt)". iApply brel_value. iIntros "$ !>". done. }
    iDestruct ("Hff" $! (oachan_row chan1 chan2) with "Hops") as "Hfbrel".
    iApply brel_new_theory.
    iApply (brel_add_label_l with "Hchan1").
    iApply (brel_add_label_r with "Hchan2").
    iApply (brel_exhaustion _ _ [_] [_] with "[Hfbrel]"); [done|done| |].
    { iApply (brel_introduction_mono with "[][$Hfbrel]").
      iApply to_iThy_le_intro'. apply submseteq_skip. rewrite iLblSig_to_iLblThy_app.
      by apply submseteq_inserts_l. }
    iLöb as "IH".
    iSplit; [iIntros (v1 v2) "!# (->&->)"; by brel_pures|].
    iIntros (k1' k2' e1' e2' Q) "!# %Hk1 %Hk2 Hpayload #Hkont".
    iDestruct "Hpayload" as "[HSend|HRecv]".
    - (* Send. *)
      iDestruct "HSend" as (m1 m2 d1 d2) "(#Hm & #Hd & -> & -> & #HQ)".
      brel_pures; [apply Hk1|apply Hk2|]; try set_solver.
      iApply (brel_na_inv _ _ (nroot.@"oamsg")); [set_solver|]. iFrame "Hinv".
      iIntros "((%v1 & %v2 & Hlm & Hlm' & #Hopt) & Hclose)".
      iApply (brel_load_l _ _ _ [CaseCtx _ _] with "Hlm"). iIntros "!> Hlm".
      iApply (brel_load_r _ _ _ _ [CaseCtx _ _] with "Hlm'"). iIntros "Hlm'".
      iDestruct "Hopt" as (w1 w2) "[(->&->&_)|(->&->&#Hgm)]".
      + (* First message: store, leak, resume. *)
        brel_pures.
        iApply (brel_store_l _ _ _ [AppRCtx _] with "Hlm"). iIntros "!> Hlm".
        iApply (brel_store_r _ _ _ _ [AppRCtx _] with "Hlm'"). iIntros "Hlm'".
        brel_pures.
        iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy| |].
        { iApply to_iThy_le_intro'. apply submseteq_cons. rewrite iLblSig_to_iLblThy_app.
          by apply submseteq_inserts_r. }
        iApply brel_na_close. iFrame "Hclose".
        iSplitL "Hlm Hlm'".
        { iNext. iExists (SOMEV m1), (SOMEV m2). iFrame. iExists _,_. iRight.
          do 2 (iSplit; [done|]). iApply "Hm". }
        iAssert ((𝔾 × (𝟙 + 𝟙))%T (m1, d1)%V (m2, d2)%V) as "#Hmm".
        { iExists m1, m2, d1, d2. iSplit; [done|]. iSplit; [done|]. iFrame "Hm Hd". }
        iEval (rewrite /sem_ty_arr /sem_ty_mbang /=) in "Hls".
        iDestruct ("Hls" with "Hmm") as "Hsend1".
        iApply (brel_wand with "[$Hsend1]").
        iIntros (u1 u2) "!# (->&->)".
        brel_pures'.
        iDestruct ("Hkont" with "HQ") as "Hbrel".
        iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
      + (* Message already stored: just resume. *)
        brel_pures.
        iApply brel_na_close. iFrame "Hclose".
        iSplitL "Hlm Hlm'".
        { iNext. iExists (SOMEV w1), (SOMEV w2). iFrame. iExists _,_. iRight.
          do 2 (iSplit; [done|]). iApply "Hgm". }
        iDestruct ("Hkont" with "HQ") as "Hbrel".
        iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
    - (* Recv. *)
      iDestruct "HRecv" as (fr1 fr2) "(#Hfr & -> & -> & #HQ)".
      iDestruct "HQ" as "(#HQN & #HQS)".
      brel_pures; [apply Hk1|apply Hk2|]; try set_solver.
      iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy| |].
      { iApply to_iThy_le_intro'. apply submseteq_cons. rewrite iLblSig_to_iLblThy_app.
        by apply submseteq_inserts_r. }
      iEval (rewrite /sem_ty_arr /sem_ty_mbang /=) in "Hlr".
      iDestruct ("Hlr" with "Hfr") as "Hrecv1".
      iApply (brel_wand with "[$Hrecv1]").
      iIntros (r1 r2) "!# #Hr".
      iDestruct "Hr" as (rw1 rw2) "[(->&->&_)|(->&->&_)]".
      + (* Leak reports absent: forward NONE to the client. *)
        brel_pures'.
        iDestruct ("Hkont" with "HQN") as "Hbrel".
        iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
      + (* Leak reports present: forward !message (Option 𝔾) to the client. *)
        brel_pures'.
        iApply (brel_na_inv _ _ (nroot.@"oamsg")); [set_solver|]. iFrame "Hinv".
        iIntros "((%v1 & %v2 & Hlm & Hlm' & #Hopt) & Hclose)".
        iApply (brel_load_l _ _ _ [AppRCtx _] with "Hlm"). iIntros "!> Hlm".
        iApply (brel_load_r _ _ _ _ [AppRCtx _] with "Hlm'"). iIntros "Hlm'".
        iApply brel_na_close. iFrame "Hclose".
        iSplitL "Hlm Hlm'".
        { iNext. iExists v1, v2. iFrame "Hlm Hlm'". iFrame "Hopt". }
        iDestruct "Hopt" as (og1 og2) "[(->&->&%Hu)|(->&->&#Hgm)]".
        * destruct Hu as [-> ->]. brel_pures'.
          iDestruct ("Hkont" with "HQN") as "Hbrel".
          iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
        * iDestruct "Hgm" as (gg) "(->&->)".
          brel_pures'.
          iDestruct ("HQS" $! gg) as "HQSg".
          iDestruct ("Hkont" with "HQSg") as "Hbrel".
          iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
  Qed.

  (* F_AUTH is F_OAUTH's sibling: an authenticated channel with TWO message
     refs (m1 for one direction, m2 for the other), no ghost/auth state.  It
     reuses the same client-facing [channel] effect theory [oachan] as
     F_OAUTH.  The self-refinement runs both copies in lockstep under a plain
     invariant tying both ref pairs at [Option 𝔾].  Here the leak interface is
     also [chan] (its [doLeakRecv] returns [Option 𝔾]); the handler discards
     the leaked value and returns [!m1]/[!m2] to the client (the auth
     cross-over). *)
  Lemma F_AUTH_typed :
    ⊢ sem_val_typed F_AUTH F_AUTH (τ__F chan chan).
  Proof using Type*.
    rewrite /sem_val_typed /τ__F //=.
    iModIntro. iIntros (θ).
    iIntros (f1 f2) "Hff".
    unfold F_AUTH. brel_pures'. iModIntro. iIntros (θ₂).
    iIntros (LeakOp1 LeakOp2) "HLeak".
    iDestruct "HLeak" as (dls1 dls2 dlr1 dlr2) "(->&->&#Hls&#Hlr)".
    brel_pures'.
    iApply brel_alloc_l. iIntros (la) "!> Hl1".
    iApply brel_alloc_l. iIntros (lb) "!> Hl2".
    brel_pures_l.
    iApply brel_alloc_r. iIntros (la') "Hl1s".
    iApply brel_alloc_r. iIntros (lb') "Hl2s".
    brel_pures_r.
    iApply (brel_na_alloc
              (∃ a1 a2 b1 b2, la ↦ a1 ∗ la' ↦ₛ a2 ∗ lb ↦ b1 ∗ lb' ↦ₛ b2 ∗
                              (Option 𝔾)%T a1 a2 ∗ (Option 𝔾)%T b1 b2)%I
              (nroot .@ "authmsg")).
    iSplitL "Hl1 Hl1s Hl2 Hl2s".
    { iNext. iExists _, _, _, _. iFrame. iSplit; iExists _,_; iLeft; done. }
    iIntros "#Hinv".
    iApply brel_effect_l. iIntros (chan1) "!> Hchan1".
    iApply brel_effect_r. iModIntro. iIntros (chan2) "Hchan2 !>".
    brel_pures'.
    (* Same (doSend,doRecv) construction as F_OAUTH, at [chan (oachan_row …)]. *)
    iAssert (chan (oachan_row chan1 chan2)
               (λ: "m", do: chan1 InjL "m", λ: "m", do: chan1 InjR "m")%V
               (λ: "m", do: chan2 InjL "m", λ: "m", do: chan2 InjR "m")%V) as "#Hops".
    { iExists _, _, _, _. iSplit; [done|]. iSplit; [done|].
      rewrite /sem_ty_mbang /=. iSplit.
      - iModIntro. iIntros (a1 a2) "Ha".
        iDestruct "Ha" as (mm1 mm2 dd1 dd2) "(->&->&#Hm&#Hd)".
        brel_pures'.
        iApply (brel_introduction' [chan1] [chan2]
                  (iThySum (OASend chan1 chan2) (OARecv chan1 chan2))); [ by left | ].
        rewrite /iThyTraverse /=.
        iExists _, _, [], [], (λ s1 s2, ⌜ s1 = Val #()%V ⌝ ∗ ⌜ s2 = Val #()%V ⌝)%I.
        iSplit; [done|]. iSplit; [iPureIntro; apply NeutralEctx_nil|].
        iSplit; [done|]. iSplit; [iPureIntro; apply NeutralEctx_nil|].
        iSplitL.
        + iLeft. iExists mm1, mm2, dd1, dd2. iFrame "Hm Hd". do 2 (iSplit; [done|]).
          iModIntro. iSplit; done.
        + iIntros "!>" (s1 s2) "(->&->)". iApply brel_value. iIntros "$ !>". done.
      - iModIntro. iIntros (a1 a2) "#Hfr".
        brel_pures'.
        iApply (brel_introduction' [chan1] [chan2]
                  (iThySum (OASend chan1 chan2) (OARecv chan1 chan2))); [ by left | ].
        rewrite /iThyTraverse /=.
        iExists _, _, [], [],
          (λ s1 s2, ∃ v1 v2 : val, ⌜ s1 = Val v1 ⌝ ∗ ⌜ s2 = Val v2 ⌝ ∗ (Option 𝔾)%T v1 v2)%I.
        iSplit; [done|]. iSplit; [iPureIntro; apply NeutralEctx_nil|].
        iSplit; [done|]. iSplit; [iPureIntro; apply NeutralEctx_nil|].
        iSplitL.
        + iRight. iExists a1, a2. iFrame "Hfr". do 2 (iSplit; [done|]).
          iModIntro. iSplit.
          * iExists NONEV, NONEV. do 2 (iSplit; [done|]). iExists _,_. iLeft. done.
          * iIntros (m). iExists (SOMEV m), (SOMEV m). do 2 (iSplit; [done|]).
            iExists _,_. iRight. iSplit; [done|]. iSplit; [done|]. iExists m. done.
        + iIntros "!>" (s1 s2) "(%v1&%v2&->&->&#Hopt)". iApply brel_value. iIntros "$ !>". done. }
    iDestruct ("Hff" $! (oachan_row chan1 chan2) with "Hops") as "Hfbrel".
    iApply brel_new_theory.
    iApply (brel_add_label_l with "Hchan1").
    iApply (brel_add_label_r with "Hchan2").
    iApply (brel_exhaustion _ _ [_] [_] with "[Hfbrel]"); [done|done| |].
    { iApply (brel_introduction_mono with "[][$Hfbrel]").
      iApply to_iThy_le_intro'. apply submseteq_skip. rewrite iLblSig_to_iLblThy_app.
      by apply submseteq_inserts_l. }
    iLöb as "IH".
    iSplit; [iIntros (v1 v2) "!# (->&->)"; by brel_pures|].
    iIntros (k1' k2' e1' e2' Q) "!# %Hk1 %Hk2 Hpayload #Hkont".
    iDestruct "Hpayload" as "[HSend|HRecv]".
    - (* Send. *)
      iDestruct "HSend" as (mm1 mm2 d1 d2) "(#Hm & #Hd & -> & -> & #HQ)".
      iDestruct "Hd" as (dw1 dw2) "[(-> & -> & #Hu)|(-> & -> & #Hu)]".
      + (* dst = InjL: store to l1. *)
        brel_pures; [apply Hk1|apply Hk2|]; try set_solver.
        iApply (brel_na_inv _ _ (nroot.@"authmsg")); [set_solver|]. iFrame "Hinv".
        iIntros "((%a1 & %a2 & %b1 & %b2 & Hl1 & Hl1s & Hl2 & Hl2s & #Hoa & #Hob) & Hclose)".
        iApply (brel_load_l _ _ _ [CaseCtx _ _] with "Hl1"). iIntros "!> Hl1".
        iApply (brel_load_r _ _ _ _ [CaseCtx _ _] with "Hl1s"). iIntros "Hl1s".
        iDestruct "Hoa" as (w1 w2) "[(->&->&_)|(->&->&#Hgm)]".
        * (* first message on this ref: store, leak, resume. *)
          brel_pures.
          iApply (brel_store_l _ _ _ [AppRCtx _] with "Hl1"). iIntros "!> Hl1".
          iApply (brel_store_r _ _ _ _ [AppRCtx _] with "Hl1s"). iIntros "Hl1s".
          brel_pures.
          iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy| |].
          { iApply to_iThy_le_intro'. apply submseteq_cons. rewrite iLblSig_to_iLblThy_app.
            by apply submseteq_inserts_r. }
          iApply brel_na_close. iFrame "Hclose".
          iSplitL "Hl1 Hl1s Hl2 Hl2s".
          { iNext. iExists (SOMEV mm1), (SOMEV mm2), b1, b2.
            iFrame "Hl1 Hl1s Hl2 Hl2s Hob". iExists _,_. iRight.
            do 2 (iSplit; [done|]). iApply "Hm". }
          iAssert ((𝔾 × (𝟙 + 𝟙))%T (mm1, InjLV dw1)%V (mm2, InjLV dw2)%V) as "#Hmm".
          { iExists mm1, mm2, (InjLV dw1), (InjLV dw2). iSplit; [done|]. iSplit; [done|].
            iFrame "Hm". iExists dw1, dw2. iLeft. iSplit; [done|]. iSplit; [done|]. iApply "Hu". }
          iEval (rewrite /sem_ty_arr /sem_ty_mbang /=) in "Hls".
          iDestruct ("Hls" with "Hmm") as "Hsend1".
          iApply (brel_wand with "[$Hsend1]").
          iIntros (u1 u2) "!# (->&->)".
          brel_pures'.
          iDestruct ("Hkont" with "HQ") as "Hbrel".
          iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
        * (* already stored: just resume. *)
          brel_pures.
          iApply brel_na_close. iFrame "Hclose".
          iSplitL "Hl1 Hl1s Hl2 Hl2s".
          { iNext. iExists (SOMEV w1), (SOMEV w2), b1, b2.
            iFrame "Hl1 Hl1s Hl2 Hl2s Hob". iExists _,_. iRight.
            do 2 (iSplit; [done|]). iApply "Hgm". }
          iDestruct ("Hkont" with "HQ") as "Hbrel".
          iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
      + (* dst = InjR: store to l2. *)
        brel_pures; [apply Hk1|apply Hk2|]; try set_solver.
        iApply (brel_na_inv _ _ (nroot.@"authmsg")); [set_solver|]. iFrame "Hinv".
        iIntros "((%a1 & %a2 & %b1 & %b2 & Hl1 & Hl1s & Hl2 & Hl2s & #Hoa & #Hob) & Hclose)".
        iApply (brel_load_l _ _ _ [CaseCtx _ _] with "Hl2"). iIntros "!> Hl2".
        iApply (brel_load_r _ _ _ _ [CaseCtx _ _] with "Hl2s"). iIntros "Hl2s".
        iDestruct "Hob" as (w1 w2) "[(->&->&_)|(->&->&#Hgm)]".
        * brel_pures.
          iApply (brel_store_l _ _ _ [AppRCtx _] with "Hl2"). iIntros "!> Hl2".
          iApply (brel_store_r _ _ _ _ [AppRCtx _] with "Hl2s"). iIntros "Hl2s".
          brel_pures.
          iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy| |].
          { iApply to_iThy_le_intro'. apply submseteq_cons. rewrite iLblSig_to_iLblThy_app.
            by apply submseteq_inserts_r. }
          iApply brel_na_close. iFrame "Hclose".
          iSplitL "Hl1 Hl1s Hl2 Hl2s".
          { iNext. iExists a1, a2, (SOMEV mm1), (SOMEV mm2).
            iFrame "Hl1 Hl1s Hl2 Hl2s Hoa". iExists _,_. iRight.
            do 2 (iSplit; [done|]). iApply "Hm". }
          iAssert ((𝔾 × (𝟙 + 𝟙))%T (mm1, InjRV dw1)%V (mm2, InjRV dw2)%V) as "#Hmm".
          { iExists mm1, mm2, (InjRV dw1), (InjRV dw2). iSplit; [done|]. iSplit; [done|].
            iFrame "Hm". iExists dw1, dw2. iRight. iSplit; [done|]. iSplit; [done|]. iApply "Hu". }
          iEval (rewrite /sem_ty_arr /sem_ty_mbang /=) in "Hls".
          iDestruct ("Hls" with "Hmm") as "Hsend1".
          iApply (brel_wand with "[$Hsend1]").
          iIntros (u1 u2) "!# (->&->)".
          brel_pures'.
          iDestruct ("Hkont" with "HQ") as "Hbrel".
          iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
        * brel_pures.
          iApply brel_na_close. iFrame "Hclose".
          iSplitL "Hl1 Hl1s Hl2 Hl2s".
          { iNext. iExists a1, a2, (SOMEV w1), (SOMEV w2).
            iFrame "Hl1 Hl1s Hl2 Hl2s Hoa". iExists _,_. iRight.
            do 2 (iSplit; [done|]). iApply "Hgm". }
          iDestruct ("Hkont" with "HQ") as "Hbrel".
          iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
    - (* Recv. *)
      iDestruct "HRecv" as (fr1 fr2) "(#Hfr & -> & -> & #HQ)".
      iDestruct "HQ" as "(#HQN & #HQS)".
      brel_pures; [apply Hk1|apply Hk2|]; try set_solver.
      iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy| |].
      { iApply to_iThy_le_intro'. apply submseteq_cons. rewrite iLblSig_to_iLblThy_app.
        by apply submseteq_inserts_r. }
      iEval (rewrite /sem_ty_arr /sem_ty_mbang /=) in "Hlr".
      iDestruct ("Hlr" with "Hfr") as "Hrecv1".
      iApply (brel_wand with "[$Hrecv1]").
      iIntros (r1 r2) "!# #Hr".
      iDestruct "Hr" as (rw1 rw2) "[(->&->&_)|(->&->&_)]".
      + (* leak reports absent: forward NONE. *)
        brel_pures'.
        iDestruct ("Hkont" with "HQN") as "Hbrel".
        iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
      + (* leak reports present: cross-over read (from=InjL → !l2, from=InjR → !l1). *)
        iDestruct "Hfr" as (fw1 fw2) "[(-> & -> & _)|(-> & -> & _)]".
        * (* from = InjL: read !l2. *)
          brel_pures'.
          iApply (brel_na_inv _ _ (nroot.@"authmsg")); [set_solver|]. iFrame "Hinv".
          iIntros "((%a1 & %a2 & %b1 & %b2 & Hl1 & Hl1s & Hl2 & Hl2s & #Hoa & #Hob) & Hclose)".
          iApply (brel_load_l _ _ _ [CaseCtx _ _] with "Hl2"). iIntros "!> Hl2".
          iApply (brel_load_r _ _ _ _ [CaseCtx _ _] with "Hl2s"). iIntros "Hl2s".
          iApply brel_na_close. iFrame "Hclose".
          iSplitL "Hl1 Hl1s Hl2 Hl2s".
          { iNext. iExists a1, a2, b1, b2. iFrame "Hl1 Hl1s Hl2 Hl2s Hoa Hob". }
          iDestruct "Hob" as (og1 og2) "[(->&->&_)|(->&->&#Hgm)]".
          -- brel_pures'.
             iDestruct ("Hkont" with "HQN") as "Hbrel".
             iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
          -- iDestruct "Hgm" as (gg) "(->&->)".
             brel_pures'.
             iDestruct ("HQS" $! gg) as "HQSg".
             iDestruct ("Hkont" with "HQSg") as "Hbrel".
             iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
        * (* from = InjR: read !l1. *)
          brel_pures'.
          iApply (brel_na_inv _ _ (nroot.@"authmsg")); [set_solver|]. iFrame "Hinv".
          iIntros "((%a1 & %a2 & %b1 & %b2 & Hl1 & Hl1s & Hl2 & Hl2s & #Hoa & #Hob) & Hclose)".
          iApply (brel_load_l _ _ _ [CaseCtx _ _] with "Hl1"). iIntros "!> Hl1".
          iApply (brel_load_r _ _ _ _ [CaseCtx _ _] with "Hl1s"). iIntros "Hl1s".
          iApply brel_na_close. iFrame "Hclose".
          iSplitL "Hl1 Hl1s Hl2 Hl2s".
          { iNext. iExists a1, a2, b1, b2. iFrame "Hl1 Hl1s Hl2 Hl2s Hoa Hob". }
          iDestruct "Hoa" as (og1 og2) "[(->&->&_)|(->&->&#Hgm)]".
          -- brel_pures'.
             iDestruct ("Hkont" with "HQN") as "Hbrel".
             iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
          -- iDestruct "Hgm" as (gg) "(->&->)".
             brel_pures'.
             iDestruct ("HQS" $! gg) as "HQSg".
             iDestruct ("Hkont" with "HQSg") as "Hbrel".
             iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
  Qed.

  (* ----------------------------------------------------------------- *)
  (* Effect theory for DH_SIM's [leak] effect.  The client [f] raises   *)
  (* [leak] via [doLeakSend]/[doLeakRecv]; both carry only a direction   *)
  (* [(𝟙+𝟙)].  [Send] returns [𝟙]; [Recv] returns [Option 𝟙] (the        *)
  (* handler forwards presence, discarding the value).                   *)
  Program Definition SLSend (c1 c2 : label) : iThy Σ :=
    (λ e1 e2, λne Q,
      ∃ (d1 d2 : val),
        (𝟙 + 𝟙)%T d1 d2 ∗
        ⌜ e1 = do: c1 (SendV d1) ⌝%E ∗
        ⌜ e2 = do: c2 (SendV d2) ⌝%E ∗
        □ (Q #()%V #()%V))%I.
  Next Obligation. solve_proper. Qed.

  Program Definition SLRecv (c1 c2 : label) : iThy Σ :=
    (λ e1 e2, λne Q,
      ∃ (from1 from2 : val),
        (𝟙 + 𝟙)%T from1 from2 ∗
        ⌜ e1 = do: c1 (RecvV from1) ⌝%E ∗
        ⌜ e2 = do: c2 (RecvV from2) ⌝%E ∗
        □ (Q NONEV NONEV ∗ Q (SOMEV #()%V) (SOMEV #()%V)))%I.
  Next Obligation. solve_proper. Qed.

  Program Definition simleak_mono (c1 c2 : label) :=
    {| pmono_prot_car := iThySum (SLSend c1 c2) (SLRecv c1 c2); pmono_prot_prop := _ |}.
  Next Obligation.
    intros ??.
    iIntros (????) "#HΦ [H|H]".
    - iLeft. iDestruct "H" as (??) "(Hd&%&%&#H)".
      iExists _,_. iFrame. repeat (iSplit; first done). iModIntro. by iApply "HΦ".
    - iRight. iDestruct "H" as (??) "(Hd&%&%&#(H1&H2))".
      iExists _,_. iFrame. repeat (iSplit; first done). iModIntro.
      iSplitL; [by iApply "HΦ" | by iApply "HΦ"].
  Qed.

  Definition simleak (c1 c2 : label) := @SemSig Σ (simleak_mono c1 c2) (c1, c2).
  Program Definition simleak_row (c1 c2 : label) := SemRow [([c1],[c2], simleak c1 c2)] _.
  Next Obligation.
    intros ??.
    iIntros (????) "#HΦ % % % ($&H)". iDestruct "H" as (?????) "(->&%&->&%&HX&#H)".
    iExists _,_,_,_,_.
    repeat (iSplit; first done). iIntros (??) "!# HS". iApply "HΦ". by iApply "H".
  Qed.

  (* DH_SIM samples group exponents.  For a self-refinement both copies must
     draw the SAME exponent, so we couple the two [samplelbl] draws
     synchronously with the identity bijection.  The [na_inv] keeps all four
     tapes EMPTY between handler invocations and keeps the two cache refs
     (per direction) holding the same optional exponent; the tape is only
     transiently non-empty inside a clause (presample via [brel_couple_TT_frag],
     immediately consumed by [rand]).  Equal exponent [c] ⇒ equal [g^c] ⇒
     𝔾-related [doSend] argument. *)
  Lemma DH_SIM_typed :
    ⊢ sem_val_typed DH_SIM DH_SIM (τ__F chan leakI).
  Proof using Type*.
    rewrite /sem_val_typed /τ__F //=.
    iModIntro. iIntros (θ).
    iIntros (f1 f2) "Hff".
    unfold DH_SIM. brel_pures'. iModIntro. iIntros (θ₂).
    iIntros (effs1 effs2) "Heffs".
    iDestruct "Heffs" as (ds1 ds2 dr1 dr2) "(->&->&#Hds&#Hdr)".
    brel_pures'.
    iApply brel_alloctape_l. iIntros (α) "!> Hα". brel_pures_l.
    iApply brel_alloctape_l. iIntros (β) "!> Hβ". brel_pures_l.
    iApply brel_alloc_l. iIntros (lca) "!> Hlca". brel_pures_l.
    iApply brel_alloc_l. iIntros (lcb) "!> Hlcb". brel_pures_l.
    iApply brel_alloctape_r. iIntros (αs) "Hαs". brel_pures_r.
    iApply brel_alloctape_r. iIntros (βs) "Hβs". brel_pures_r.
    iApply brel_alloc_r. iIntros (lcas) "Hlcas". brel_pures_r.
    iApply brel_alloc_r. iIntros (lcbs) "Hlcbs". brel_pures_r.
    iAssert (αs ↪ₛN (S n''; []))%I with "[Hαs]" as "Hαs". { iExists []. by iFrame. }
    iAssert (βs ↪ₛN (S n''; []))%I with "[Hβs]" as "Hβs". { iExists []. by iFrame. }
    iApply (brel_na_alloc
      (α ↪N (S n''; []) ∗ αs ↪ₛN (S n''; []) ∗ β ↪N (S n''; []) ∗ βs ↪ₛN (S n''; []) ∗
       ((lca ↦ NONEV ∗ lcas ↦ₛ NONEV) ∨ (∃ c : nat, lca ↦ SOMEV #c ∗ lcas ↦ₛ SOMEV #c)) ∗
       ((lcb ↦ NONEV ∗ lcbs ↦ₛ NONEV) ∨ (∃ c : nat, lcb ↦ SOMEV #c ∗ lcbs ↦ₛ SOMEV #c)))%I
      (nroot .@ "simleak")).
    iSplitL "Hα Hαs Hβ Hβs Hlca Hlcas Hlcb Hlcbs".
    { iNext. iFrame "Hα Hαs Hβ Hβs". iSplitL "Hlca Hlcas"; iLeft; iFrame. }
    iIntros "#Hinv".
    iApply brel_effect_l. iIntros (leak1) "!> Hleak1".
    iApply brel_effect_r. iModIntro. iIntros (leak2) "Hleak2 !>".
    brel_pures'.
    (* Build (doLeakSend,doLeakRecv) at [leakI (simleak_row leak1 leak2)]. *)
    iAssert (leakI (simleak_row leak1 leak2)
               (λ: "m", do: leak1 InjL "m", λ: "m", do: leak1 InjR "m")%V
               (λ: "m", do: leak2 InjL "m", λ: "m", do: leak2 InjR "m")%V) as "#Hlops".
    { iExists _, _, _, _. iSplit; [done|]. iSplit; [done|].
      rewrite /sem_ty_mbang /=. iSplit.
      - iModIntro. iIntros (a1 a2) "#Hd". brel_pures'.
        iApply (brel_introduction' [leak1] [leak2]
                  (iThySum (SLSend leak1 leak2) (SLRecv leak1 leak2))); [ by left | ].
        rewrite /iThyTraverse /=.
        iExists _, _, [], [], (λ s1 s2, ⌜ s1 = Val #()%V ⌝ ∗ ⌜ s2 = Val #()%V ⌝)%I.
        iSplit; [done|]. iSplit; [iPureIntro; apply NeutralEctx_nil|].
        iSplit; [done|]. iSplit; [iPureIntro; apply NeutralEctx_nil|].
        iSplitL.
        + iLeft. iExists a1, a2. iSplit; [iApply "Hd"|]. do 2 (iSplit; [done|]).
          iModIntro. iSplit; done.
        + iIntros "!>" (s1 s2) "(->&->)". iApply brel_value. iIntros "$ !>". done.
      - iModIntro. iIntros (a1 a2) "#Hfr". brel_pures'.
        iApply (brel_introduction' [leak1] [leak2]
                  (iThySum (SLSend leak1 leak2) (SLRecv leak1 leak2))); [ by left | ].
        rewrite /iThyTraverse /=.
        iExists _, _, [], [],
          (λ s1 s2, ∃ v1 v2 : val, ⌜ s1 = Val v1 ⌝ ∗ ⌜ s2 = Val v2 ⌝ ∗ (Option 𝟙)%T v1 v2)%I.
        iSplit; [done|]. iSplit; [iPureIntro; apply NeutralEctx_nil|].
        iSplit; [done|]. iSplit; [iPureIntro; apply NeutralEctx_nil|].
        iSplitL.
        + iRight. iExists a1, a2. iSplit; [iApply "Hfr"|]. do 2 (iSplit; [done|]).
          iModIntro. iSplit.
          * iExists NONEV, NONEV. do 2 (iSplit; [done|]). iExists _,_. iLeft. done.
          * iExists (SOMEV #()%V), (SOMEV #()%V). do 2 (iSplit; [done|]).
            iExists _,_. iRight. iSplit; [done|]. iSplit; [done|]. done.
        + iIntros "!>" (s1 s2) "(%v1&%v2&->&->&#Hopt)". iApply brel_value. iIntros "$ !>". done. }
    iDestruct ("Hff" $! (simleak_row leak1 leak2) with "Hlops") as "Hfbrel".
    iApply brel_new_theory.
    iApply (brel_add_label_l with "Hleak1").
    iApply (brel_add_label_r with "Hleak2").
    iApply (brel_exhaustion _ _ [_] [_] with "[Hfbrel]"); [done|done| |].
    { iApply (brel_introduction_mono with "[][$Hfbrel]").
      iApply to_iThy_le_intro'. apply submseteq_skip. rewrite iLblSig_to_iLblThy_app.
      by apply submseteq_inserts_l. }
    iLöb as "IH".
    iSplit; [iIntros (v1 v2) "!# (->&->)"; by brel_pures|].
    iIntros (k1' k2' e1' e2' Q) "!# %Hk1 %Hk2 Hpayload #Hkont".
    iDestruct "Hpayload" as "[HSend|HRecv]".
    - (* Send: sample exponent, compute g^c, forward via [doSend]. *)
      iDestruct "HSend" as (d1 d2) "(#Hd & -> & -> & #HQ)".
      iDestruct "Hd" as (dw1 dw2) "[(-> & -> & _)|(-> & -> & _)]".
      + (* dst = InjL: tape α / cache lca / [doSend (_, bob)]. *)
        brel_pures; [apply Hk1|apply Hk2|]; try set_solver.
        iApply (brel_na_inv _ _ (nroot.@"simleak")); [set_solver|]. iFrame "Hinv".
        iIntros "((Hα & Hαs & Hβ & Hβs & Hca & Hcb) & Hclose)".
        iDestruct "Hca" as "[(Hlca & Hlcas)|(%cc & Hlca & Hlcas)]".
        * (* fresh: couple the two draws, sample, cache. *)
          iApply (brel_load_l _ _ _ [AppRCtx _; CaseCtx _ _] with "Hlca"). iIntros "!> Hlca".
          iApply (brel_load_r _ _ _ _ [AppRCtx _; CaseCtx _ _] with "Hlcas"). iIntros "Hlcas".
          brel_pures'.
          iApply (brel_couple_TT_frag _ (S n'') (S n'') (λ x:nat, x) _ _ _ _ α αs [] []);
            [ lia | by (intros ??; lia) | ].
          iFrame "Hα Hαs".
          iIntros (kk) "%Hkk".
          rewrite bool_decide_eq_true_2; [| by exists kk].
          iIntros (mm) "(Hα & Hαs & %Hle1 & %Hle2)".
          iApply (brel_randT_l _ [AppRCtx _; AppRCtx _]). iFrame "Hα". iIntros "!> Hα _".
          iApply (brel_randT_r _ [AppRCtx _; AppRCtx _] with "Hαs"). iIntros "Hαs _".
          brel_pures'.
          iApply (brel_store_l _ _ _ [AppRCtx _; AppRCtx _] with "Hlca"). iIntros "!> Hlca".
          iApply (brel_store_r _ _ _ _ [AppRCtx _; AppRCtx _] with "Hlcas"). iIntros "Hlcas".
          brel_pures'.
          iApply brel_na_close. iFrame "Hclose".
          iSplitL "Hα Hαs Hβ Hβs Hlca Hlcas Hcb".
          { iNext. iFrame "Hα Hαs Hβ Hβs Hcb". iRight. iExists mm. iFrame. }
          iApply (brel_exp_l [AppRCtx _]). iApply (brel_exp_r [AppRCtx _]). brel_pures'.
          iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy| |].
          { iApply to_iThy_le_intro'. apply submseteq_cons. rewrite iLblSig_to_iLblThy_app.
            by apply submseteq_inserts_r. }
          iAssert ((𝔾 × (𝟙 + 𝟙))%T (vgval (g ^+ mm)%g, bob)%V (vgval (g ^+ mm)%g, bob)%V) as "#Harg".
          { iExists _, _, _, _. iSplit; [done|]. iSplit; [done|]. iSplit.
            - iExists (g ^+ mm)%g. done.
            - iExists _,_. iLeft. done. }
          iEval (rewrite /sem_ty_arr /sem_ty_mbang /=) in "Hds".
          iDestruct ("Hds" with "Harg") as "Hsend1".
          iApply (brel_wand with "[$Hsend1]").
          iIntros (u1 u2) "!# (->&->)".
          brel_pures'.
          iDestruct ("Hkont" with "HQ") as "Hbrel".
          iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
        * (* cached: reuse exponent. *)
          iApply (brel_load_l _ _ _ [AppRCtx _; CaseCtx _ _] with "Hlca"). iIntros "!> Hlca".
          iApply (brel_load_r _ _ _ _ [AppRCtx _; CaseCtx _ _] with "Hlcas"). iIntros "Hlcas".
          brel_pures'.
          iApply brel_na_close. iFrame "Hclose".
          iSplitL "Hα Hαs Hβ Hβs Hlca Hlcas Hcb".
          { iNext. iFrame "Hα Hαs Hβ Hβs Hcb". iRight. iExists cc. iFrame. }
          iApply (brel_exp_l [AppRCtx _]). iApply (brel_exp_r [AppRCtx _]). brel_pures'.
          iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy| |].
          { iApply to_iThy_le_intro'. apply submseteq_cons. rewrite iLblSig_to_iLblThy_app.
            by apply submseteq_inserts_r. }
          iAssert ((𝔾 × (𝟙 + 𝟙))%T (vgval (g ^+ cc)%g, bob)%V (vgval (g ^+ cc)%g, bob)%V) as "#Harg".
          { iExists _, _, _, _. iSplit; [done|]. iSplit; [done|]. iSplit.
            - iExists (g ^+ cc)%g. done.
            - iExists _,_. iLeft. done. }
          iEval (rewrite /sem_ty_arr /sem_ty_mbang /=) in "Hds".
          iDestruct ("Hds" with "Harg") as "Hsend1".
          iApply (brel_wand with "[$Hsend1]").
          iIntros (u1 u2) "!# (->&->)".
          brel_pures'.
          iDestruct ("Hkont" with "HQ") as "Hbrel".
          iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
      + (* dst = InjR: tape β / cache lcb / [doSend (_, alice)]. *)
        brel_pures; [apply Hk1|apply Hk2|]; try set_solver.
        iApply (brel_na_inv _ _ (nroot.@"simleak")); [set_solver|]. iFrame "Hinv".
        iIntros "((Hα & Hαs & Hβ & Hβs & Hca & Hcb) & Hclose)".
        iDestruct "Hcb" as "[(Hlcb & Hlcbs)|(%cc & Hlcb & Hlcbs)]".
        * iApply (brel_load_l _ _ _ [AppRCtx _; CaseCtx _ _] with "Hlcb"). iIntros "!> Hlcb".
          iApply (brel_load_r _ _ _ _ [AppRCtx _; CaseCtx _ _] with "Hlcbs"). iIntros "Hlcbs".
          brel_pures'.
          iApply (brel_couple_TT_frag _ (S n'') (S n'') (λ x:nat, x) _ _ _ _ β βs [] []);
            [ lia | by (intros ??; lia) | ].
          iFrame "Hβ Hβs".
          iIntros (kk) "%Hkk".
          rewrite bool_decide_eq_true_2; [| by exists kk].
          iIntros (mm) "(Hβ & Hβs & %Hle1 & %Hle2)".
          iApply (brel_randT_l _ [AppRCtx _; AppRCtx _]). iFrame "Hβ". iIntros "!> Hβ _".
          iApply (brel_randT_r _ [AppRCtx _; AppRCtx _] with "Hβs"). iIntros "Hβs _".
          brel_pures'.
          iApply (brel_store_l _ _ _ [AppRCtx _; AppRCtx _] with "Hlcb"). iIntros "!> Hlcb".
          iApply (brel_store_r _ _ _ _ [AppRCtx _; AppRCtx _] with "Hlcbs"). iIntros "Hlcbs".
          brel_pures'.
          iApply brel_na_close. iFrame "Hclose".
          iSplitL "Hα Hαs Hβ Hβs Hlcb Hlcbs Hca".
          { iNext. iFrame "Hα Hαs Hβ Hβs Hca". iRight. iExists mm. iFrame. }
          iApply (brel_exp_l [AppRCtx _]). iApply (brel_exp_r [AppRCtx _]). brel_pures'.
          iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy| |].
          { iApply to_iThy_le_intro'. apply submseteq_cons. rewrite iLblSig_to_iLblThy_app.
            by apply submseteq_inserts_r. }
          iAssert ((𝔾 × (𝟙 + 𝟙))%T (vgval (g ^+ mm)%g, alice)%V (vgval (g ^+ mm)%g, alice)%V) as "#Harg".
          { iExists _, _, _, _. iSplit; [done|]. iSplit; [done|]. iSplit.
            - iExists (g ^+ mm)%g. done.
            - iExists _,_. iRight. done. }
          iEval (rewrite /sem_ty_arr /sem_ty_mbang /=) in "Hds".
          iDestruct ("Hds" with "Harg") as "Hsend1".
          iApply (brel_wand with "[$Hsend1]").
          iIntros (u1 u2) "!# (->&->)".
          brel_pures'.
          iDestruct ("Hkont" with "HQ") as "Hbrel".
          iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
        * iApply (brel_load_l _ _ _ [AppRCtx _; CaseCtx _ _] with "Hlcb"). iIntros "!> Hlcb".
          iApply (brel_load_r _ _ _ _ [AppRCtx _; CaseCtx _ _] with "Hlcbs"). iIntros "Hlcbs".
          brel_pures'.
          iApply brel_na_close. iFrame "Hclose".
          iSplitL "Hα Hαs Hβ Hβs Hlcb Hlcbs Hca".
          { iNext. iFrame "Hα Hαs Hβ Hβs Hca". iRight. iExists cc. iFrame. }
          iApply (brel_exp_l [AppRCtx _]). iApply (brel_exp_r [AppRCtx _]). brel_pures'.
          iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy| |].
          { iApply to_iThy_le_intro'. apply submseteq_cons. rewrite iLblSig_to_iLblThy_app.
            by apply submseteq_inserts_r. }
          iAssert ((𝔾 × (𝟙 + 𝟙))%T (vgval (g ^+ cc)%g, alice)%V (vgval (g ^+ cc)%g, alice)%V) as "#Harg".
          { iExists _, _, _, _. iSplit; [done|]. iSplit; [done|]. iSplit.
            - iExists (g ^+ cc)%g. done.
            - iExists _,_. iRight. done. }
          iEval (rewrite /sem_ty_arr /sem_ty_mbang /=) in "Hds".
          iDestruct ("Hds" with "Harg") as "Hsend1".
          iApply (brel_wand with "[$Hsend1]").
          iIntros (u1 u2) "!# (->&->)".
          brel_pures'.
          iDestruct ("Hkont" with "HQ") as "Hbrel".
          iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
    - (* Recv: forward the external [doRecv]'s presence (value discarded). *)
      iDestruct "HRecv" as (fr1 fr2) "(#Hfr & -> & -> & #HQ)".
      iDestruct "HQ" as "(#HQN & #HQS)".
      brel_pures; [apply Hk1|apply Hk2|]; try set_solver.
      iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy| |].
      { iApply to_iThy_le_intro'. apply submseteq_cons. rewrite iLblSig_to_iLblThy_app.
        by apply submseteq_inserts_r. }
      iEval (rewrite /sem_ty_arr /sem_ty_mbang /=) in "Hdr".
      iDestruct ("Hdr" with "Hfr") as "Hrecv1".
      iApply (brel_wand with "[$Hrecv1]").
      iIntros (r1 r2) "!# #Hr".
      iDestruct "Hr" as (rw1 rw2) "[(->&->&_)|(->&->&_)]".
      + brel_pures'.
        iDestruct ("Hkont" with "HQN") as "Hbrel".
        iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
      + brel_pures'.
        iDestruct ("Hkont" with "HQS") as "Hbrel".
        iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
  Qed.

  (* ----------------------------------------------------------------- *)
  (* Effect theory for F_KE_lazy_alice's [getKey] effect.  This is a     *)
  (* SINGLE operation (not a Send/Recv sum), so a plain [iThy]: payload  *)
  (* [(𝟙+𝟙)] (the party), result [Option 𝔾] (the key).                   *)
  Program Definition GKeff (c1 c2 : label) : iThy Σ :=
    (λ e1 e2, λne Q,
      ∃ (p1 p2 : val), (𝟙 + 𝟙)%T p1 p2 ∗
        ⌜ e1 = do: c1 p1 ⌝%E ∗ ⌜ e2 = do: c2 p2 ⌝%E ∗
        □ (Q NONEV NONEV ∗ ∀ g : vgG, Q (SOMEV g) (SOMEV g)))%I.
  Next Obligation. solve_proper. Qed.

  Program Definition gkeff_mono (c1 c2 : label) :=
    {| pmono_prot_car := GKeff c1 c2; pmono_prot_prop := _ |}.
  Next Obligation.
    intros ??.
    iIntros (????) "#HΦ H". iDestruct "H" as (??) "(Hp&%&%&#(H1&H2))".
    iExists _,_. iFrame. repeat (iSplit; first done). iModIntro.
    iSplitL; [by iApply "HΦ"|]. iIntros (g); by iApply "HΦ".
  Qed.

  Definition gkeff (c1 c2 : label) := @SemSig Σ (gkeff_mono c1 c2) (c1, c2).
  Program Definition gkeff_row (c1 c2 : label) := SemRow [([c1],[c2], gkeff c1 c2)] _.
  Next Obligation.
    intros ??.
    iIntros (????) "#HΦ % % % ($&H)". iDestruct "H" as (?????) "(->&%&->&%&HX&#H)".
    iExists _,_,_,_,_.
    repeat (iSplit; first done). iIntros (??) "!# HS". iApply "HΦ". by iApply "H".
  Qed.

  (* F_KE_lazy_alice lazily samples a shared key [g^c].  As in DH_SIM the two
     copies must draw the SAME exponent, so we couple the [samplelbl γ] draws
     with the identity bijection.  The [na_inv] keeps the tape EMPTY between
     invocations and both cache refs holding [SOMEV (vgval (g^+c))] for the SAME
     [c:nat] (storing the exponent [c] rather than a [vgG] element avoids an
     [Inhabited vgG] obligation when destructing under the invariant's later).
     Equal [c] ⇒ equal key ⇒ 𝔾-related value handed to the client. *)
  Lemma F_KE_lazy_alice_typed :
    ⊢ sem_val_typed F_KE_lazy_alice F_KE_lazy_alice (τ__F leakI gk).
  Proof using Type*.
    rewrite /sem_val_typed /τ__F //=.
    iModIntro. iIntros (θ).
    iIntros (f1 f2) "Hff".
    unfold F_KE_lazy_alice. brel_pures'. iModIntro. iIntros (θ₂).
    iIntros (effs1 effs2) "Heffs".
    iDestruct "Heffs" as (dls1 dls2 dlr1 dlr2) "(->&->&#Hls&#Hlr)".
    brel_pures'.
    iApply brel_alloctape_l. iIntros (γ) "!> Hγ". brel_pures_l.
    iApply brel_alloc_l. iIntros (ko) "!> Hko". brel_pures_l.
    iApply brel_alloctape_r. iIntros (γs) "Hγs". brel_pures_r.
    iApply brel_alloc_r. iIntros (kos) "Hkos". brel_pures_r.
    iAssert (γs ↪ₛN (S n''; []))%I with "[Hγs]" as "Hγs". { iExists []. by iFrame. }
    iApply (brel_na_alloc
      (γ ↪N (S n''; []) ∗ γs ↪ₛN (S n''; []) ∗
       ((ko ↦ NONEV ∗ kos ↦ₛ NONEV)
        ∨ (∃ c : nat, ko ↦ SOMEV (vgval (g ^+ c)%g) ∗ kos ↦ₛ SOMEV (vgval (g ^+ c)%g))))%I
      (nroot .@ "keyinv")).
    iSplitL "Hγ Hγs Hko Hkos".
    { iNext. iFrame "Hγ Hγs". iLeft. iFrame. }
    iIntros "#Hinv".
    iApply brel_effect_l. iIntros (gk1) "!> Hgk1".
    iApply brel_effect_r. iModIntro. iIntros (gk2) "Hgk2 !>".
    brel_pures'.
    (* Build the [doGK] operation related at [gk (gkeff_row gk1 gk2)]. *)
    iAssert (gk (gkeff_row gk1 gk2)
               (λ: "party", do: gk1 "party")%V (λ: "party", do: gk2 "party")%V) as "#Hgg".
    { rewrite /gk /sem_ty_mbang /=. iModIntro. iIntros (a1 a2) "#Hp". brel_pures'.
      iApply (brel_introduction' [gk1] [gk2] (gkeff gk1 gk2)); [ by left | ].
      rewrite /iThyTraverse /=.
      iExists _, _, [], [],
        (λ s1 s2, ∃ v1 v2 : val, ⌜ s1 = Val v1 ⌝ ∗ ⌜ s2 = Val v2 ⌝ ∗ (Option 𝔾)%T v1 v2)%I.
      iSplit; [done|]. iSplit; [iPureIntro; apply NeutralEctx_nil|].
      iSplit; [done|]. iSplit; [iPureIntro; apply NeutralEctx_nil|].
      iSplitL.
      + iExists a1, a2. iSplit; [iApply "Hp"|]. do 2 (iSplit; [done|]).
        iModIntro. iSplit.
        * iExists NONEV, NONEV. do 2 (iSplit; [done|]). iExists _,_. iLeft. done.
        * iIntros (gg). iExists (SOMEV gg), (SOMEV gg). do 2 (iSplit; [done|]).
          iExists _,_. iRight. iSplit; [done|]. iSplit; [done|]. iExists gg. done.
      + iIntros "!>" (s1 s2) "(%v1&%v2&->&->&#Hopt)". iApply brel_value. iIntros "$ !>". done. }
    iDestruct ("Hff" $! (gkeff_row gk1 gk2) with "Hgg") as "Hfbrel".
    iApply brel_new_theory.
    iApply (brel_add_label_l with "Hgk1").
    iApply (brel_add_label_r with "Hgk2").
    iApply (brel_exhaustion _ _ [_] [_] with "[Hfbrel]"); [done|done| |].
    { iApply (brel_introduction_mono with "[][$Hfbrel]").
      iApply to_iThy_le_intro'. apply submseteq_skip. rewrite iLblSig_to_iLblThy_app.
      by apply submseteq_inserts_l. }
    iLöb as "IH".
    iSplit; [iIntros (v1 v2) "!# (->&->)"; by brel_pures|].
    iIntros (k1' k2' e1' e2' Q) "!# %Hk1 %Hk2 Hpayload #Hkont".
    iDestruct "Hpayload" as (p1 p2) "(#Hp & -> & -> & #HQ)".
    iDestruct "HQ" as "(#HQN & #HQS)".
    iDestruct "Hp" as (pw1 pw2) "[(-> & -> & _)|(-> & -> & _)]".
    - (* Alice: sample-or-load the key, leak send+recv, forward the key. *)
      iAssert ((𝟙 + 𝟙)%T bob bob) as "#Hbob". { iExists _,_. iLeft. done. }
      brel_pures; [apply Hk1|apply Hk2|]; try set_solver.
      iApply (brel_na_inv _ _ (nroot.@"keyinv")); [set_solver|]. iFrame "Hinv".
      iIntros "((Hγ & Hγs & Hko) & Hclose)".
      iDestruct "Hko" as "[(Hko & Hkos)|(%cc & Hko & Hkos)]".
      + (* first use: couple the two draws, sample, cache the key. *)
        iApply (brel_load_l _ _ _ [AppRCtx _; CaseCtx _ _] with "Hko"). iIntros "!> Hko".
        iApply (brel_load_r _ _ _ _ [AppRCtx _; CaseCtx _ _] with "Hkos"). iIntros "Hkos".
        brel_pures'.
        iApply (brel_couple_TT_frag _ (S n'') (S n'') (λ x:nat, x) _ _ _ _ γ γs [] []);
          [ lia | by (intros ??; lia) | ].
        iFrame "Hγ Hγs". iIntros (kk) "%Hkk". rewrite bool_decide_eq_true_2; [| by exists kk].
        iIntros (mm) "(Hγ & Hγs & %Hle1 & %Hle2)".
        iApply (brel_randT_l _ [AppRCtx _; AppRCtx _]). iFrame "Hγ". iIntros "!> Hγ _".
        iApply (brel_randT_r _ [AppRCtx _; AppRCtx _] with "Hγs"). iIntros "Hγs _".
        brel_pures'.
        iApply (brel_exp_l [AppRCtx _; AppRCtx _]). iApply (brel_exp_r [AppRCtx _; AppRCtx _]).
        brel_pures'.
        iApply (brel_store_l _ _ _ [AppRCtx _; AppRCtx _] with "Hko"). iIntros "!> Hko".
        iApply (brel_store_r _ _ _ _ [AppRCtx _; AppRCtx _] with "Hkos"). iIntros "Hkos".
        brel_pures'.
        iApply brel_na_close. iFrame "Hclose".
        iSplitL "Hγ Hγs Hko Hkos".
        { iNext. iFrame "Hγ Hγs". iRight. iExists mm. iFrame. }
        iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy| |].
        { iApply to_iThy_le_intro'. apply submseteq_cons. rewrite iLblSig_to_iLblThy_app.
          by apply submseteq_inserts_r. }
        iEval (rewrite /sem_ty_arr /sem_ty_mbang /=) in "Hls".
        iDestruct ("Hls" with "Hbob") as "Hsend1".
        iApply (brel_wand with "[$Hsend1]"). iIntros (u1 u2) "!# (->&->)". brel_pures'.
        iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy| |].
        { iApply to_iThy_le_intro'. apply submseteq_cons. rewrite iLblSig_to_iLblThy_app.
          by apply submseteq_inserts_r. }
        iEval (rewrite /sem_ty_arr /sem_ty_mbang /=) in "Hlr".
        iDestruct ("Hlr" with "Hbob") as "Hrecv1".
        iApply (brel_wand with "[$Hrecv1]"). iIntros (r1 r2) "!# #Hr".
        iDestruct "Hr" as (rw1 rw2) "[(->&->&_)|(->&->&_)]".
        * brel_pures'. iDestruct ("Hkont" with "HQN") as "Hbrel".
          iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
        * brel_pures'. iDestruct ("HQS" $! (g ^+ mm)%g) as "HQSg".
          iDestruct ("Hkont" with "HQSg") as "Hbrel".
          iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
      + (* cached: reuse the key. *)
        iApply (brel_load_l _ _ _ [AppRCtx _; CaseCtx _ _] with "Hko"). iIntros "!> Hko".
        iApply (brel_load_r _ _ _ _ [AppRCtx _; CaseCtx _ _] with "Hkos"). iIntros "Hkos".
        brel_pures'.
        iApply brel_na_close. iFrame "Hclose".
        iSplitL "Hγ Hγs Hko Hkos".
        { iNext. iFrame "Hγ Hγs". iRight. iExists cc. iFrame. }
        iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy| |].
        { iApply to_iThy_le_intro'. apply submseteq_cons. rewrite iLblSig_to_iLblThy_app.
          by apply submseteq_inserts_r. }
        iEval (rewrite /sem_ty_arr /sem_ty_mbang /=) in "Hls".
        iDestruct ("Hls" with "Hbob") as "Hsend1".
        iApply (brel_wand with "[$Hsend1]"). iIntros (u1 u2) "!# (->&->)". brel_pures'.
        iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy| |].
        { iApply to_iThy_le_intro'. apply submseteq_cons. rewrite iLblSig_to_iLblThy_app.
          by apply submseteq_inserts_r. }
        iEval (rewrite /sem_ty_arr /sem_ty_mbang /=) in "Hlr".
        iDestruct ("Hlr" with "Hbob") as "Hrecv1".
        iApply (brel_wand with "[$Hrecv1]"). iIntros (r1 r2) "!# #Hr".
        iDestruct "Hr" as (rw1 rw2) "[(->&->&_)|(->&->&_)]".
        * brel_pures'. iDestruct ("Hkont" with "HQN") as "Hbrel".
          iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
        * brel_pures'. iDestruct ("HQS" $! (g ^+ cc)%g) as "HQSg".
          iDestruct ("Hkont" with "HQSg") as "Hbrel".
          iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
    - (* Bob: leak recv; on presence, leak send and forward the cached key. *)
      iAssert ((𝟙 + 𝟙)%T alice alice) as "#Halice". { iExists _,_. iRight. done. }
      brel_pures; [apply Hk1|apply Hk2|]; try set_solver.
      iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy| |].
      { iApply to_iThy_le_intro'. apply submseteq_cons. rewrite iLblSig_to_iLblThy_app.
        by apply submseteq_inserts_r. }
      iEval (rewrite /sem_ty_arr /sem_ty_mbang /=) in "Hlr".
      iDestruct ("Hlr" with "Halice") as "Hrecv1".
      iApply (brel_wand with "[$Hrecv1]"). iIntros (r1 r2) "!# #Hr".
      iDestruct "Hr" as (rw1 rw2) "[(->&->&_)|(->&->&_)]".
      + brel_pures'. iDestruct ("Hkont" with "HQN") as "Hbrel".
        iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
      + brel_pures'.
        iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy| |].
        { iApply to_iThy_le_intro'. apply submseteq_cons. rewrite iLblSig_to_iLblThy_app.
          by apply submseteq_inserts_r. }
        iEval (rewrite /sem_ty_arr /sem_ty_mbang /=) in "Hls".
        iDestruct ("Hls" with "Halice") as "Hsend1".
        iApply (brel_wand with "[$Hsend1]"). iIntros (u1 u2) "!# (->&->)". brel_pures'.
        iApply (brel_na_inv _ _ (nroot.@"keyinv")); [set_solver|]. iFrame "Hinv".
        iIntros "((Hγ & Hγs & Hko) & Hclose)".
        iDestruct "Hko" as "[(Hko & Hkos)|(%cc & Hko & Hkos)]".
        * iApply (brel_load_l _ _ _ [CaseCtx _ _] with "Hko"). iIntros "!> Hko".
          iApply (brel_load_r _ _ _ _ [CaseCtx _ _] with "Hkos"). iIntros "Hkos".
          iApply brel_na_close. iFrame "Hclose". iSplitL "Hγ Hγs Hko Hkos".
          { iNext. iFrame "Hγ Hγs". iLeft. iFrame. }
          brel_pures'. iDestruct ("Hkont" with "HQN") as "Hbrel".
          iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
        * iApply (brel_load_l _ _ _ [CaseCtx _ _] with "Hko"). iIntros "!> Hko".
          iApply (brel_load_r _ _ _ _ [CaseCtx _ _] with "Hkos"). iIntros "Hkos".
          iApply brel_na_close. iFrame "Hclose". iSplitL "Hγ Hγs Hko Hkos".
          { iNext. iFrame "Hγ Hγs". iRight. iExists cc. iFrame. }
          brel_pures'. iDestruct ("HQS" $! (g ^+ cc)%g) as "HQSg".
          iDestruct ("Hkont" with "HQSg") as "Hbrel".
          iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
  Qed.

  (* ----------------------------------------------------------------- *)
  (* Effect theory for CHAN's [schannel] effect (the [cli] interface as an
     effect): [SendSecure] payload 𝔾 (a group message) → result 𝟙;
     [RecvSecure] payload is the fixed [Recv bob] → result [Option 𝔾]. *)
  Program Definition SCSend (c1 c2 : label) : iThy Σ :=
    (λ e1 e2, λne Q, ∃ m1 m2 : val, 𝔾 m1 m2 ∗
      ⌜ e1 = do: c1 (SendV m1) ⌝%E ∗ ⌜ e2 = do: c2 (SendV m2) ⌝%E ∗ □ (Q #()%V #()%V))%I.
  Next Obligation. solve_proper. Qed.
  Program Definition SCRecv (c1 c2 : label) : iThy Σ :=
    (λ e1 e2, λne Q, ⌜ e1 = do: c1 (RecvV bob) ⌝%E ∗ ⌜ e2 = do: c2 (RecvV bob) ⌝%E ∗
      □ (Q NONEV NONEV ∗ ∀ g : vgG, Q (SOMEV g) (SOMEV g)))%I.
  Next Obligation. solve_proper. Qed.
  Program Definition scchan_mono (c1 c2 : label) :=
    {| pmono_prot_car := iThySum (SCSend c1 c2) (SCRecv c1 c2); pmono_prot_prop := _ |}.
  Next Obligation.
    intros ??. iIntros (????) "#HΦ [H|H]".
    - iLeft. iDestruct "H" as (m1 m2) "(HG&%&%&#H)".
      iExists _,_. iFrame. repeat (iSplit; first done). iModIntro. by iApply "HΦ".
    - iRight. iDestruct "H" as "(%&%&#(H1&H2))".
      repeat (iSplit; first done). iModIntro.
      iSplitL; [by iApply "HΦ" | iIntros (g); by iApply "HΦ"].
  Qed.
  Definition scchan (c1 c2 : label) := @SemSig Σ (scchan_mono c1 c2) (c1, c2).
  Program Definition scchan_row (c1 c2 : label) := SemRow [([c1],[c2], scchan c1 c2)] _.
  Next Obligation.
    intros ??. iIntros (????) "#HΦ % % % ($&H)". iDestruct "H" as (?????) "(->&%&->&%&HX&#H)".
    iExists _,_,_,_,_. repeat (iSplit; first done). iIntros (??) "!# HS". iApply "HΦ". by iApply "H".
  Qed.

  (* Symmetric stepping of [G_XOR xor (vgval gm) (vgval gk0)] on both sides.
     Both copies run identical deterministic code on equal (𝔾-related) inputs,
     so they reduce to the SAME [Option 𝔾] value; we case-split on whether
     [vg_of_int_sem] succeeds (using the new [brel_vg_of_int_correct_r] /
     [brel_vg_of_int_none_l/r] class fields), and the [xor] bound comes from
     [Bdd_int_vg]. *)
  Lemma brel_gxor (gm gk0 : vgG) (X : logic.iLblThy Σ) (R : val -> val -> iProp Σ) :
    (∀ mg : vgG, ⌜vg_of_int_sem (xor_sem (int_of_vg_sem gm) (int_of_vg_sem gk0)) = Some mg⌝ -∗
       R (SOMEV (vgval mg)) (SOMEV (vgval mg))) -∗
    (⌜vg_of_int_sem (xor_sem (int_of_vg_sem gm) (int_of_vg_sem gk0)) = None⌝ -∗
       R NONEV NONEV) -∗
    BREL (G_XOR xor (vgval gm) (vgval gk0)) ≤ (G_XOR xor (vgval gm) (vgval gk0)) <|X|> {{R}}.
  Proof using Type* XOR_spec0.
    iIntros "HSome HNone". rewrite /G_XOR. brel_pures'.
    iApply (brel_int_of_vg_sem_correct_l _ [AppRCtx vg_of_int; AppRCtx (App xor (int_of_vg (vgval gm)))] gk0).
    iApply (brel_int_of_vg_sem_correct_r _ [AppRCtx vg_of_int; AppRCtx (App xor (int_of_vg (vgval gm)))] gk0).
    iApply (brel_int_of_vg_sem_correct_l _ [AppRCtx vg_of_int; AppLCtx #(int_of_vg_sem gk0); AppRCtx xor] gm).
    iApply (brel_int_of_vg_sem_correct_r _ [AppRCtx vg_of_int; AppLCtx #(int_of_vg_sem gk0); AppRCtx xor] gm).
    iApply (xor_correct_l _ [AppRCtx vg_of_int]);
      [ rewrite /Key; eapply Nat.lt_le_trans; [apply Bdd_int_vg| lia]
      | rewrite /Support; eapply Nat.lt_le_trans; [apply Bdd_int_vg| lia] | ].
    iApply (xor_correct_r _ [AppRCtx vg_of_int]);
      [ rewrite /Key; eapply Nat.lt_le_trans; [apply Bdd_int_vg| lia]
      | rewrite /Support; eapply Nat.lt_le_trans; [apply Bdd_int_vg| lia] | ].
    destruct (vg_of_int_sem (xor_sem (int_of_vg_sem gm) (int_of_vg_sem gk0))) as [mg|] eqn:Hvz.
    - iApply (brel_vg_of_int_correct_l _ [] _ _ _ _ mg Hvz).
      iApply (brel_vg_of_int_correct_r _ [] _ _ _ _ mg Hvz).
      iApply brel_value. iIntros "$ !>". iApply ("HSome" $! mg). iPureIntro. reflexivity.
    - iApply (brel_vg_of_int_none_l _ [] _ _ _ _ Hvz).
      iApply (brel_vg_of_int_none_r _ [] _ _ _ _ Hvz).
      iApply brel_value. iIntros "$ !>". iApply "HNone". iPureIntro. reflexivity.
  Qed.

  Lemma CHAN_typed :
    ⊢ ∀ θ, sem_val_typed (CHAN xor) (CHAN xor) ((hdl cli θ ⊸ τ__f θ chan gk)%T).
  Proof using Type*.
    iIntros (θ). rewrite /sem_val_typed. iModIntro.
    rewrite /hdl /τ__f /=.
    iIntros (f1 f2) "Hff".
    unfold CHAN. brel_pures'.
    iModIntro. iIntros (θ1 θ2).
    iIntros (ChanOp1 ChanOp2) "HChanOp".
    iDestruct "HChanOp" as (dsend1 dsend2 drecv1 drecv2) "(->&->&#Hsend&#Hrecv)".
    brel_pures'.
    iModIntro. iIntros (doGK1 doGK2) "#Hgk".
    brel_pures'.
    iApply brel_alloc_l. iIntros (lm) "!> Hlm". brel_pures_l.
    iApply brel_alloc_r. iIntros (lms) "Hlms". brel_pures_r.
    iApply (brel_na_alloc (∃ v1 v2, lm ↦ v1 ∗ lms ↦ₛ v2 ∗ (Option 𝔾)%T v1 v2)%I
                          (nroot .@ "scmsg")).
    iSplitL "Hlm Hlms". { iNext. iExists _,_. iFrame. iExists _,_. iLeft. done. }
    iIntros "#Hinv".
    iApply brel_effect_l. iIntros (schan1) "!> Hschan1".
    iApply brel_effect_r. iModIntro. iIntros (schan2) "Hschan2 !>".
    brel_pures'.
    (* Build the (doSecSend, doSecRecv) pair related at [cli (scchan_row …)]. *)
    iAssert (cli (scchan_row schan1 schan2)
               (λ: "m", do: schan1 (Send "m"), λ: <>, do: schan1 (Recv bob))%V
               (λ: "m", do: schan2 (Send "m"), λ: <>, do: schan2 (Recv bob))%V) as "#Hcli".
    { iExists _,_,_,_. iSplit; [done|]. iSplit; [done|]. rewrite /sem_ty_mbang /=. iSplit.
      - iModIntro. iIntros (a1 a2) "#Hm". brel_pures'.
        iApply (brel_introduction' [schan1] [schan2] (iThySum (SCSend schan1 schan2) (SCRecv schan1 schan2))); [ by left | ].
        rewrite /iThyTraverse /=.
        iExists _,_,[],[], (λ s1 s2, ⌜ s1 = Val #()%V ⌝ ∗ ⌜ s2 = Val #()%V ⌝)%I.
        iSplit;[done|]. iSplit;[iPureIntro; apply NeutralEctx_nil|]. iSplit;[done|]. iSplit;[iPureIntro; apply NeutralEctx_nil|].
        iSplitL.
        + iLeft. iExists a1, a2. iSplit; [iApply "Hm"|]. do 2 (iSplit;[done|]). iModIntro. iSplit; done.
        + iIntros "!>" (s1 s2) "(->&->)". iApply brel_value. iIntros "$ !>". done.
      - iModIntro. iIntros (a1 a2) "#Hu". brel_pures'.
        iApply (brel_introduction' [schan1] [schan2] (iThySum (SCSend schan1 schan2) (SCRecv schan1 schan2))); [ by left | ].
        rewrite /iThyTraverse /=.
        iExists _,_,[],[], (λ s1 s2, ∃ v1 v2 : val, ⌜ s1 = Val v1 ⌝ ∗ ⌜ s2 = Val v2 ⌝ ∗ (Option 𝔾)%T v1 v2)%I.
        iSplit;[done|]. iSplit;[iPureIntro; apply NeutralEctx_nil|]. iSplit;[done|]. iSplit;[iPureIntro; apply NeutralEctx_nil|].
        iSplitL.
        + iRight. do 2 (iSplit;[done|]). iModIntro. iSplit.
          * iExists NONEV, NONEV. do 2 (iSplit;[done|]). iExists _,_. iLeft. done.
          * iIntros (g). iExists (SOMEV g), (SOMEV g). do 2 (iSplit;[done|]). iExists _,_. iRight. iSplit;[done|]. iSplit;[done|]. iExists g. done.
        + iIntros "!>" (s1 s2) "(%v1&%v2&->&->&#Hopt)". iApply brel_value. iIntros "$ !>". done. }
    iDestruct ("Hff" $! (scchan_row schan1 schan2) with "Hcli") as "Hfbrel".
    iApply brel_new_theory.
    iApply (brel_add_label_l with "Hschan1").
    iApply (brel_add_label_r with "Hschan2").
    iApply (brel_exhaustion _ _ [_] [_] with "[Hfbrel]"); [done|done| |].
    { iApply (brel_introduction_mono with "[][$Hfbrel]").
      iApply to_iThy_le_intro'. apply submseteq_skip. rewrite !iLblSig_to_iLblThy_app.
      apply submseteq_inserts_l. apply submseteq_inserts_l. reflexivity. }
    iLöb as "IH".
    iSplit; [iIntros (v1 v2) "!# (->&->)"; by brel_pures|].
    iIntros (k1' k2' e1' e2' Q) "!# %Hk1 %Hk2 Hpayload #Hkont".
    iDestruct "Hpayload" as "[HS|HR]".
    - (* SendSecure: store the message, [doGK], encrypt via [G_XOR], [doSend]. *)
      iDestruct "HS" as (m1 m2) "(#Hm & -> & -> & #HQ)".
      iDestruct "Hm" as (gm) "(-> & ->)".
      brel_pures; try (solve [apply Hk1; set_solver]); try (solve [apply Hk2; set_solver]).
      all: try iModIntro.
      iApply (brel_na_inv _ _ (nroot.@"scmsg")); [set_solver|]. iFrame "Hinv".
      iIntros "((%v1 & %v2 & Hlm & Hlms & #Hopt) & Hclose)".
      iApply (brel_load_l _ _ _ [CaseCtx _ _] with "Hlm"). iIntros "!> Hlm".
      iApply (brel_load_r _ _ _ _ [CaseCtx _ _] with "Hlms"). iIntros "Hlms".
      iDestruct "Hopt" as (w1 w2) "[(->&->&_)|(->&->&#Hgw)]".
      + (* first message: store, get key, encrypt, forward. *)
        brel_pures.
        iApply (brel_store_l _ _ _ [AppRCtx _] with "Hlm"). iIntros "!> Hlm".
        iApply (brel_store_r _ _ _ _ [AppRCtx _] with "Hlms"). iIntros "Hlms".
        brel_pures.
        iApply brel_na_close. iFrame "Hclose". iSplitL "Hlm Hlms".
        { iNext. iExists (SOMEV (vgval gm)), (SOMEV (vgval gm)). iFrame. iExists _,_. iRight.
          do 2 (iSplit;[done|]). iExists gm. done. }
        iApply (brel_bind [AppRCtx _] [AppRCtx _] _ (iLblSig_to_iLblThy θ2)); [iApply traversable_to_iThy| |].
        { iApply to_iThy_le_intro'. apply submseteq_cons. rewrite !iLblSig_to_iLblThy_app.
          apply submseteq_inserts_l. apply submseteq_inserts_r. reflexivity. }
        iAssert ((𝟙 + 𝟙)%T bob bob) as "#Hbob". { iExists _,_. iLeft. done. }
        iEval (rewrite /gk /sem_ty_arr /sem_ty_mbang /=) in "Hgk".
        iDestruct ("Hgk" with "Hbob") as "Hgkbob".
        iApply (brel_wand with "[$Hgkbob]"). iIntros (key1 key2) "!# #Hkey".
        iDestruct "Hkey" as (kw1 kw2) "[(->&->&_)|(->&->&#Hgkey)]".
        * brel_pures'. iDestruct ("Hkont" with "HQ") as "Hbrel".
          iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
        * iDestruct "Hgkey" as (gkey) "(->&->)".
          brel_pures'.
          iApply (brel_bind' [CaseCtx _ _] [CaseCtx _ _]); [iApply traversable_to_iThy|].
          iApply (brel_gxor gm gkey).
          -- iIntros (mg) "%Hmg". brel_pures'.
             iApply (brel_bind [AppRCtx _] [AppRCtx _] _ (iLblSig_to_iLblThy θ1)); [iApply traversable_to_iThy| |].
             { iApply to_iThy_le_intro'. apply submseteq_cons. rewrite !iLblSig_to_iLblThy_app.
               apply submseteq_inserts_r. reflexivity. }
             iAssert ((𝔾 × (𝟙 + 𝟙))%T (vgval mg, bob)%V (vgval mg, bob)%V) as "#Harg".
             { iExists _,_,_,_. iSplit;[done|]. iSplit;[done|]. iSplit; [iExists mg; done | iExists _,_; iLeft; done]. }
             iEval (rewrite /sem_ty_arr /sem_ty_mbang /=) in "Hsend".
             iDestruct ("Hsend" with "Harg") as "Hsend1".
             iApply (brel_wand with "[$Hsend1]"). iIntros (u1 u2) "!# (->&->)". brel_pures'.
             iDestruct ("Hkont" with "HQ") as "Hbrel".
             iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
          -- iIntros "%Hnone". brel_pures'.
             iDestruct ("Hkont" with "HQ") as "Hbrel".
             iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
      + (* message already stored: just resume. *)
        brel_pures.
        iApply brel_na_close. iFrame "Hclose". iSplitL "Hlm Hlms".
        { iNext. iExists (InjRV w1), (InjRV w2). iFrame "Hlm Hlms". iExists _,_. iRight.
          do 2 (iSplit;[done|]). iApply "Hgw". }
        iDestruct ("Hkont" with "HQ") as "Hbrel".
        iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
    - (* RecvSecure: get key, [doRecv], decrypt via [G_XOR], forward. *)
      iDestruct "HR" as "(-> & -> & #HQ)". iDestruct "HQ" as "(#HQN & #HQS)".
      brel_pures; try (solve [apply Hk1; set_solver]); try (solve [apply Hk2; set_solver]).
      iAssert ((𝟙 + 𝟙)%T alice alice) as "#Halice". { iExists _,_. iRight. done. }
      iApply (brel_bind [AppRCtx _] [AppRCtx _] _ (iLblSig_to_iLblThy θ2)); [iApply traversable_to_iThy| |].
      { iApply to_iThy_le_intro'. apply submseteq_cons. rewrite !iLblSig_to_iLblThy_app.
        apply submseteq_inserts_l. apply submseteq_inserts_r. reflexivity. }
      iEval (rewrite /gk /sem_ty_arr /sem_ty_mbang /=) in "Hgk".
      iDestruct ("Hgk" with "Halice") as "Hgkal".
      iApply (brel_wand with "[$Hgkal]"). iIntros (key1 key2) "!# #Hkey".
      iDestruct "Hkey" as (kw1 kw2) "[(->&->&_)|(->&->&#Hgkey)]".
      + brel_pures'. iDestruct ("Hkont" with "HQN") as "Hbrel".
        iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
      + iDestruct "Hgkey" as (gkey) "(->&->)".
        brel_pures'.
        iApply (brel_bind [AppRCtx _] [AppRCtx _] _ (iLblSig_to_iLblThy θ1)); [iApply traversable_to_iThy| |].
        { iApply to_iThy_le_intro'. apply submseteq_cons. rewrite !iLblSig_to_iLblThy_app.
          apply submseteq_inserts_r. reflexivity. }
        iAssert ((𝟙 + 𝟙)%T bob bob) as "#Hbob". { iExists _,_. iLeft. done. }
        iEval (rewrite /sem_ty_arr /sem_ty_mbang /=) in "Hrecv".
        iDestruct ("Hrecv" with "Hbob") as "Hrecvbob".
        iApply (brel_wand with "[$Hrecvbob]"). iIntros (r1 r2) "!# #Hr".
        iDestruct "Hr" as (rw1 rw2) "[(->&->&_)|(->&->&#Hgx)]".
        * brel_pures'. iDestruct ("Hkont" with "HQN") as "Hbrel".
          iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
        * iDestruct "Hgx" as (gx) "(->&->)".
          brel_pures'.
          iApply (brel_bind' [CaseCtx _ _] [CaseCtx _ _]); [iApply traversable_to_iThy|].
          iApply (brel_gxor gx gkey).
          -- iIntros (mg) "%Hmg". brel_pures'. iDestruct ("HQS" $! mg) as "HQSmg".
             iDestruct ("Hkont" with "HQSmg") as "Hbrel".
             iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
          -- iIntros "%Hnone". brel_pures'. iDestruct ("Hkont" with "HQN") as "Hbrel".
             iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
  Qed.

  (* Generic composition of two functionality transformers:
     [F : τ__F A B] and [G : τ__F B B'] compose to [F ∘f G : τ__F A B'].
     Pure plumbing of the two [τ__F] applications (no effects/invariants):
     [G] turns the [B']-client [f] into a [B]-handler, and [F] turns that
     into the [A]-handler. *)
  Lemma func_comp_typed (F J : val) (A B B' : sem_row Σ → sem_ty Σ) :
    ⊢ sem_val_typed F F (τ__F A B) -∗ sem_val_typed J J (τ__F B B') -∗
      sem_val_typed (F ∘f J) (F ∘f J) (τ__F A B').
  Proof using Type*.
    iIntros "#HF #HJ". rewrite /sem_val_typed /τ__F /func_comp //=.
    iModIntro. iIntros (θ). iIntros (f1 f2) "Hff". brel_pures'.
    iDestruct ("HJ" $! θ f1 f2 with "Hff") as "HJf".
    iApply (brel_bind' [AppRCtx F] [AppRCtx F]); [iApply traversable_to_iThy_nil|].
    iApply (brel_wand with "HJf").
    iIntros (gv1 gv2) "!# Hgv".
    iApply ("HF" $! θ gv1 gv2 with "Hgv").
  Qed.

  (* [F_AUTH ∘f DH_SIM], in both value and open (sem_typed) presentations. *)
  Lemma F_AUTH_DH_SIM_typed_val :
    ⊢ sem_val_typed (F_AUTH ∘f DH_SIM) (F_AUTH ∘f DH_SIM) (τ__F chan leakI).
  Proof using Type*.
    iApply func_comp_typed; [iApply F_AUTH_typed | iApply DH_SIM_typed].
  Qed.

  Lemma F_AUTH_DH_SIM_typed :
    ⊢ sem_typed [] (F_AUTH ∘f DH_SIM) (F_AUTH ∘f DH_SIM) ⊥ (τ__F chan leakI) [].
  Proof using Type*.
    iIntros (vs) "!# _". simpl. brel_pures'.
    iApply brel_value. iIntros "$ !>". iSplit; last done.
    iPoseProof F_AUTH_DH_SIM_typed_val as "H". rewrite /sem_val_typed //=.
  Qed.

  (* [chan]/[gk] interfaces (products of [-{θ}->] arrows) are usable at any
     larger effect row θ' ⊇ θ (covariant effect subtyping). *)
  Lemma chan_le (θ θ' : sem_row Σ) : θ ≤ᵣ θ' -∗ chan θ ≤ₜ chan θ'.
  Proof using Type*.
    iIntros "#Hle". rewrite /chan.
    iApply ty_le_prod; iApply ty_le_uarr; try iApply "Hle"; iApply ty_le_refl.
  Qed.
  Lemma gk_le (θ θ' : sem_row Σ) : θ ≤ᵣ θ' -∗ gk θ ≤ₜ gk θ'.
  Proof using Type*.
    iIntros "#Hle". rewrite /gk.
    iApply ty_le_uarr; [iApply "Hle" | iApply ty_le_refl | iApply ty_le_refl].
  Qed.

  Lemma F_KE_F_OAUTH_typed :
    ⊢ sem_typed [] (F_KE_lazy_alice ||ᵣ F_OAUTH) (F_KE_lazy_alice ||ᵣ F_OAUTH) ⊥
        ((∀ᵣ θ, (∀ᵣ θJ, chan θJ ⊸ gk θJ -{ sem_row_union θJ θ }-∘ 𝟙) ⊸
            (∀ᵣ θ1, oaleak θ1 ⊸ ∀ᵣ θ2, leakI θ2
                    -{ sem_row_union θ1 (sem_row_union θ2 θ) }-∘ 𝟙))%T) [].
  Proof using Type*.
    iPoseProof F_KE_lazy_alice_typed as "#HFF".
    iPoseProof F_OAUTH_typed as "#HF".
    rewrite /sem_val_typed /τ__F //=.
    iIntros (vs) "!# Hvs". simpl.
    rewrite /right_composition.
    brel_pures'.
    iModIntro.
    iSplitR "Hvs"; last (iApply "Hvs").
    iIntros (θ).
    iIntros (f1 f2) "Hff".
    brel_pures'.
    iModIntro.
    iIntros (θ1).
    iIntros (r2a r2b) "#Hoa".
    brel_pures'.
    iModIntro.
    iIntros (θ2).
    iIntros (r1a r1b) "#Hleak".
    brel_pures'.
    iAssert ((∀ᵣ θ2', gk θ2' -{ sem_row_union θ2' (sem_row_union θ1 θ) }-∘ 𝟙)%T
               (λ: "h₁", F_OAUTH (λ: "h₂", f1 "h₂" "h₁") r2a)%V
               (λ: "h₁", F_OAUTH (λ: "h₂", f2 "h₂" "h₁") r2b)%V) with "[Hff]" as "Hclients".
    { iIntros (θ2' v1 v2) "Hgk". brel_pures'.
      iAssert ((∀ᵣ θ1', chan θ1' -{ sem_row_union θ1' (sem_row_union θ2' θ) }-∘ 𝟙)%T
                 (λ: "h₂", f1 "h₂" v1)%V (λ: "h₂", f2 "h₂" v2)%V)
        with "[Hff Hgk]" as "Hinner".
      { iIntros (θ1' v1' v2') "Hchan". brel_pures'.
        iAssert (θ1' ≤ᵣ sem_row_union θ1' θ2')%I as "#Hle1".
        { iApply to_iThy_le_intro'. unfold sem_row_union. simpl.
          rewrite iLblSig_to_iLblThy_app. apply submseteq_inserts_r. done. }
        iAssert (θ2' ≤ᵣ sem_row_union θ1' θ2')%I as "#Hle2".
        { iApply to_iThy_le_intro'. unfold sem_row_union. simpl.
          rewrite iLblSig_to_iLblThy_app. apply submseteq_inserts_l. done. }
        iDestruct (chan_le with "Hle1") as "#Hcw". iDestruct ("Hcw" with "Hchan") as "Hchan'".
        iDestruct (gk_le with "Hle2") as "#Hgw". iDestruct ("Hgw" with "Hgk") as "Hgk'".
        iDestruct ("Hff" $! (sem_row_union θ1' θ2') with "Hchan'") as "Hff1".
        iApply (brel_bind [AppLCtx v1] [AppLCtx v2]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
        assert (to_iThyIfMono OS [] = []) as <- by done.
        iApply (brel_mono OS with "[][$Hff1]"); [iApply to_iThy_le_refl|simpl].
        iIntros (fv1 fv2) "Hff1".
        iSpecialize ("Hff1" with "Hgk'").
        iApply (brel_introduction_mono (iLblSig_to_iLblThy (sem_row_union (sem_row_union θ1' θ2') θ)) with "[] Hff1").
        iApply to_iThy_le_intro'. unfold sem_row_union. simpl.
        rewrite !iLblSig_to_iLblThy_app. rewrite -app_assoc. done. }
      iSpecialize ("HF" with "Hinner").
      iApply (brel_bind [AppLCtx r2a] [AppLCtx r2b]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
      assert (to_iThyIfMono OS [] = []) as <- by done.
      iApply (brel_mono OS with "[][$HF]"); [iApply to_iThy_le_refl|simpl].
      iIntros (FO1 FO2) "HF".
      iSpecialize ("HF" $! θ1 with "Hoa").
      iApply (brel_introduction_mono (iLblSig_to_iLblThy (sem_row_union θ1 (sem_row_union θ2' θ))) with "[] HF").
      iApply to_iThy_le_intro'. unfold sem_row_union. simpl.
      rewrite !iLblSig_to_iLblThy_app. solve_submseteq. }
    iSpecialize ("HFF" with "Hclients").
    iApply (brel_bind [AppLCtx r1a] [AppLCtx r1b] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][$HFF]"); [iApply to_iThy_le_refl|simpl].
    iIntros (FK1 FK2) "Hvv".
    iSpecialize ("Hvv" $! θ2 with "Hleak").
    iApply (brel_introduction_mono (iLblSig_to_iLblThy (sem_row_union θ2 (sem_row_union θ1 θ))) with "[] Hvv").
    iApply to_iThy_le_intro'. unfold sem_row_union. simpl.
    rewrite !iLblSig_to_iLblThy_app. solve_submseteq.
  Qed.

  (* Open bodies of [F_KE_lazy_alice] and [CHAN xor], needed as the [G]/[J]
     premises of the (functionality-)composition-associativity lemmas.
     [F_KE_body] is free in "f","effs"; [CHAN_body] is free in "f","ChanOp".
     These are copied verbatim from the source definitions
     ([def_dhke.F_KE_lazy_alice] and [sec_channel_def.CHAN]). *)
  Definition F_KE_body : expr :=
    (let, ("doLeakSend", "doLeakRecv") := "effs" in
     let: "γ" := alloc #(S n'') in
     let: "key_opt" := ref NONEV in
     let: "sample_or_load" :=
       λ:<>, match: !"key_opt" with
         | NONE =>
             let: "c" := (samplelbl "γ" #()%V) in
             let: "key" := vexp g "c" in
             "key_opt" <- SOME "key" ;;
             "key"
         | SOME "key" => "key"
         end
     in
     effect "getKey"
       let: "doGK" := (λ: "party", do: (EffName "getKey") "party") in
       handle: "f" "doGK" with
     | effect (EffName "getKey") "p", rec "k" as multi =>
         match: "p" with
           InjL <> =>
             let: "key" := "sample_or_load" #()%V in
             ("doLeakSend" bob);;
             let: "r" := ("doLeakRecv" bob) in
             match: "r" with
               NONE => "k" NONEV
             | SOME "w" => "k" (SOME "key")
             end
         | InjR <> =>
             let: "r" := ("doLeakRecv" alice) in
             match: "r" with
               NONE => "k" NONEV
             | SOME "w" =>
                 ("doLeakSend" alice);;
                 match: !"key_opt" with
                 | NONE => "k" NONEV
                 | SOME "key" => "k" (SOME "key")
                 end
             end
         end
     | return "y" => "y" end)%E.

  Definition CHAN_body : expr :=
    ( let, ("doSend", "doRecv") := "ChanOp" in
      let: "message" := ref NONEV in
      effect "schannel"
      let: "doSecSend" := (λ: "m", do: (EffName "schannel") (Send "m")) in
      let: "doSecRecv" := (λ: <>, do: (EffName "schannel") (Recv bob)) in
      handle: "f" ("doSecSend", "doSecRecv") with
      | effect (EffName "schannel") "payload", rec "k" as multi =>
        match: "payload" with
          | InjL "m" =>
            match: !"message" with
              | NONE => "message" <- SOME "m";;
                     let: "key" := "doGK" (bob) in
                     match: "key" with
                     | NONE => "k" #()%V
                     | SOME "x" =>
                         match: G_XOR xor "m" "x" with
                         | SOME "mg" => ("doSend" ("mg", bob));; "k" #()%V
                         | NONE => "k" #()%V
                         end
                     end
              | SOME "m" => "k" #()%V
            end
        | InjR <> =>
            let: "key" := "doGK" (alice) in
            match: "key" with
            | NONE => "k" NONEV
            | SOME "key" =>
                let: "r" := ("doRecv" bob) in
                match: "r" with
                | NONE => "k" NONEV
                | SOME "x" =>
                    match: G_XOR xor "x" "key" with
                    | SOME "mg" => "k" (SOME "mg")
                    | NONE => "k" NONE
                    end
                end
            end
        end
      | return "y" => "y"
    end)%E.

  Lemma F_KE_body_typed :
    ⊢ ∀ (θ θG : sem_row Σ),
      sem_typed [("f", τ__f' θ gk); ("effs", leakI θG)]
        F_KE_body F_KE_body (sem_row_union θG θ) (𝟙)%T [].
  Proof using Type*.
    iIntros (θ θ₂). iIntros (vs) "!# Henv".
    rewrite !env_sem_typed_cons env_sem_typed_empty.
    iDestruct "Henv" as "((%f1 & %f2 & %Hlf & Hff) & (%e1 & %e2 & %Hle & Heffs) & _)".
    rewrite /F_KE_body.
    assert (Hf' : (fst<$>vs) !! "f" = Some f1) by (rewrite lookup_fmap Hlf //).
    assert (He' : (fst<$>vs) !! "effs" = Some e1) by (rewrite lookup_fmap Hle //).
    assert (Hf2' : (snd<$>vs) !! "f" = Some f2) by (rewrite lookup_fmap Hlf //).
    assert (He2' : (snd<$>vs) !! "effs" = Some e2) by (rewrite lookup_fmap Hle //).
    simpl; simplify_map_eq.
    iApply (brel_wand _ _ _ (λ v1 v2 : val, 𝟙%T v1 v2) with "[-]"); last first.
    { iModIntro. iIntros (v1 v2) "H". iFrame. }
    iDestruct "Heffs" as (dls1 dls2 dlr1 dlr2) "(->&->&#Hls&#Hlr)".
    brel_pures'.
    iApply brel_alloctape_l. iIntros (γ) "!> Hγ". brel_pures_l.
    iApply brel_alloc_l. iIntros (ko) "!> Hko". brel_pures_l.
    iApply brel_alloctape_r. iIntros (γs) "Hγs". brel_pures_r.
    iApply brel_alloc_r. iIntros (kos) "Hkos". brel_pures_r.
    iAssert (γs ↪ₛN (S n''; []))%I with "[Hγs]" as "Hγs". { iExists []. by iFrame. }
    iApply (brel_na_alloc
      (γ ↪N (S n''; []) ∗ γs ↪ₛN (S n''; []) ∗
       ((ko ↦ NONEV ∗ kos ↦ₛ NONEV)
        ∨ (∃ c : nat, ko ↦ SOMEV (vgval (g ^+ c)%g) ∗ kos ↦ₛ SOMEV (vgval (g ^+ c)%g))))%I
      (nroot .@ "keyinv")).
    iSplitL "Hγ Hγs Hko Hkos".
    { iNext. iFrame "Hγ Hγs". iLeft. iFrame. }
    iIntros "#Hinv".
    iApply brel_effect_l. iIntros (gk1) "!> Hgk1".
    iApply brel_effect_r. iModIntro. iIntros (gk2) "Hgk2 !>".
    brel_pures'.
    (* Build the [doGK] operation related at [gk (gkeff_row gk1 gk2)]. *)
    iAssert (gk (gkeff_row gk1 gk2)
               (λ: "party", do: gk1 "party")%V (λ: "party", do: gk2 "party")%V) as "#Hgg".
    { rewrite /gk /sem_ty_mbang /=. iModIntro. iIntros (a1 a2) "#Hp". brel_pures'.
      iApply (brel_introduction' [gk1] [gk2] (gkeff gk1 gk2)); [ by left | ].
      rewrite /iThyTraverse /=.
      iExists _, _, [], [],
        (λ s1 s2, ∃ v1 v2 : val, ⌜ s1 = Val v1 ⌝ ∗ ⌜ s2 = Val v2 ⌝ ∗ (Option 𝔾)%T v1 v2)%I.
      iSplit; [done|]. iSplit; [iPureIntro; apply NeutralEctx_nil|].
      iSplit; [done|]. iSplit; [iPureIntro; apply NeutralEctx_nil|].
      iSplitL.
      + iExists a1, a2. iSplit; [iApply "Hp"|]. do 2 (iSplit; [done|]).
        iModIntro. iSplit.
        * iExists NONEV, NONEV. do 2 (iSplit; [done|]). iExists _,_. iLeft. done.
        * iIntros (gg). iExists (SOMEV gg), (SOMEV gg). do 2 (iSplit; [done|]).
          iExists _,_. iRight. iSplit; [done|]. iSplit; [done|]. iExists gg. done.
      + iIntros "!>" (s1 s2) "(%v1&%v2&->&->&#Hopt)". iApply brel_value. iIntros "$ !>". done. }
    iDestruct ("Hff" $! (gkeff_row gk1 gk2) with "Hgg") as "Hfbrel".
    iApply brel_new_theory.
    iApply (brel_add_label_l with "Hgk1").
    iApply (brel_add_label_r with "Hgk2").
    iApply (brel_exhaustion _ _ [_] [_] with "[Hfbrel]"); [done|done| |].
    { iApply (brel_introduction_mono with "[][$Hfbrel]").
      iApply to_iThy_le_intro'. apply submseteq_skip. rewrite iLblSig_to_iLblThy_app.
      by apply submseteq_inserts_l. }
    iLöb as "IH".
    iSplit; [iIntros (v1 v2) "!# (->&->)"; by brel_pures|].
    iIntros (k1' k2' e1' e2' Q) "!# %Hk1 %Hk2 Hpayload #Hkont".
    iDestruct "Hpayload" as (p1 p2) "(#Hp & -> & -> & #HQ)".
    iDestruct "HQ" as "(#HQN & #HQS)".
    iDestruct "Hp" as (pw1 pw2) "[(-> & -> & _)|(-> & -> & _)]".
    - (* Alice: sample-or-load the key, leak send+recv, forward the key. *)
      iAssert ((𝟙 + 𝟙)%T bob bob) as "#Hbob". { iExists _,_. iLeft. done. }
      brel_pures; [apply Hk1|apply Hk2|]; try set_solver.
      iApply (brel_na_inv _ _ (nroot.@"keyinv")); [set_solver|]. iFrame "Hinv".
      iIntros "((Hγ & Hγs & Hko) & Hclose)".
      iDestruct "Hko" as "[(Hko & Hkos)|(%cc & Hko & Hkos)]".
      + (* first use: couple the two draws, sample, cache the key. *)
        iApply (brel_load_l _ _ _ [AppRCtx _; CaseCtx _ _] with "Hko"). iIntros "!> Hko".
        iApply (brel_load_r _ _ _ _ [AppRCtx _; CaseCtx _ _] with "Hkos"). iIntros "Hkos".
        brel_pures'.
        iApply (brel_couple_TT_frag _ (S n'') (S n'') (λ x:nat, x) _ _ _ _ γ γs [] []);
          [ lia | by (intros ??; lia) | ].
        iFrame "Hγ Hγs". iIntros (kk) "%Hkk". rewrite bool_decide_eq_true_2; [| by exists kk].
        iIntros (mm) "(Hγ & Hγs & %Hle1 & %Hle2)".
        iApply (brel_randT_l _ [AppRCtx _; AppRCtx _]). iFrame "Hγ". iIntros "!> Hγ _".
        iApply (brel_randT_r _ [AppRCtx _; AppRCtx _] with "Hγs"). iIntros "Hγs _".
        brel_pures'.
        iApply (brel_exp_l [AppRCtx _; AppRCtx _]). iApply (brel_exp_r [AppRCtx _; AppRCtx _]).
        brel_pures'.
        iApply (brel_store_l _ _ _ [AppRCtx _; AppRCtx _] with "Hko"). iIntros "!> Hko".
        iApply (brel_store_r _ _ _ _ [AppRCtx _; AppRCtx _] with "Hkos"). iIntros "Hkos".
        brel_pures'.
        iApply brel_na_close. iFrame "Hclose".
        iSplitL "Hγ Hγs Hko Hkos".
        { iNext. iFrame "Hγ Hγs". iRight. iExists mm. iFrame. }
        iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy| |].
        { iApply to_iThy_le_intro'. apply submseteq_cons. rewrite iLblSig_to_iLblThy_app.
          by apply submseteq_inserts_r. }
        iEval (rewrite /sem_ty_arr /sem_ty_mbang /=) in "Hls".
        iDestruct ("Hls" with "Hbob") as "Hsend1".
        iApply (brel_wand with "[$Hsend1]"). iIntros (u1 u2) "!# (->&->)". brel_pures'.
        iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy| |].
        { iApply to_iThy_le_intro'. apply submseteq_cons. rewrite iLblSig_to_iLblThy_app.
          by apply submseteq_inserts_r. }
        iEval (rewrite /sem_ty_arr /sem_ty_mbang /=) in "Hlr".
        iDestruct ("Hlr" with "Hbob") as "Hrecv1".
        iApply (brel_wand with "[$Hrecv1]"). iIntros (r1 r2) "!# #Hr".
        iDestruct "Hr" as (rw1 rw2) "[(->&->&_)|(->&->&_)]".
        * brel_pures'. iDestruct ("Hkont" with "HQN") as "Hbrel".
          iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
        * brel_pures'. iDestruct ("HQS" $! (g ^+ mm)%g) as "HQSg".
          iDestruct ("Hkont" with "HQSg") as "Hbrel".
          iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
      + (* cached: reuse the key. *)
        iApply (brel_load_l _ _ _ [AppRCtx _; CaseCtx _ _] with "Hko"). iIntros "!> Hko".
        iApply (brel_load_r _ _ _ _ [AppRCtx _; CaseCtx _ _] with "Hkos"). iIntros "Hkos".
        brel_pures'.
        iApply brel_na_close. iFrame "Hclose".
        iSplitL "Hγ Hγs Hko Hkos".
        { iNext. iFrame "Hγ Hγs". iRight. iExists cc. iFrame. }
        iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy| |].
        { iApply to_iThy_le_intro'. apply submseteq_cons. rewrite iLblSig_to_iLblThy_app.
          by apply submseteq_inserts_r. }
        iEval (rewrite /sem_ty_arr /sem_ty_mbang /=) in "Hls".
        iDestruct ("Hls" with "Hbob") as "Hsend1".
        iApply (brel_wand with "[$Hsend1]"). iIntros (u1 u2) "!# (->&->)". brel_pures'.
        iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy| |].
        { iApply to_iThy_le_intro'. apply submseteq_cons. rewrite iLblSig_to_iLblThy_app.
          by apply submseteq_inserts_r. }
        iEval (rewrite /sem_ty_arr /sem_ty_mbang /=) in "Hlr".
        iDestruct ("Hlr" with "Hbob") as "Hrecv1".
        iApply (brel_wand with "[$Hrecv1]"). iIntros (r1 r2) "!# #Hr".
        iDestruct "Hr" as (rw1 rw2) "[(->&->&_)|(->&->&_)]".
        * brel_pures'. iDestruct ("Hkont" with "HQN") as "Hbrel".
          iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
        * brel_pures'. iDestruct ("HQS" $! (g ^+ cc)%g) as "HQSg".
          iDestruct ("Hkont" with "HQSg") as "Hbrel".
          iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
    - (* Bob: leak recv; on presence, leak send and forward the cached key. *)
      iAssert ((𝟙 + 𝟙)%T alice alice) as "#Halice". { iExists _,_. iRight. done. }
      brel_pures; [apply Hk1|apply Hk2|]; try set_solver.
      iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy| |].
      { iApply to_iThy_le_intro'. apply submseteq_cons. rewrite iLblSig_to_iLblThy_app.
        by apply submseteq_inserts_r. }
      iEval (rewrite /sem_ty_arr /sem_ty_mbang /=) in "Hlr".
      iDestruct ("Hlr" with "Halice") as "Hrecv1".
      iApply (brel_wand with "[$Hrecv1]"). iIntros (r1 r2) "!# #Hr".
      iDestruct "Hr" as (rw1 rw2) "[(->&->&_)|(->&->&_)]".
      + brel_pures'. iDestruct ("Hkont" with "HQN") as "Hbrel".
        iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
      + brel_pures'.
        iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy| |].
        { iApply to_iThy_le_intro'. apply submseteq_cons. rewrite iLblSig_to_iLblThy_app.
          by apply submseteq_inserts_r. }
        iEval (rewrite /sem_ty_arr /sem_ty_mbang /=) in "Hls".
        iDestruct ("Hls" with "Halice") as "Hsend1".
        iApply (brel_wand with "[$Hsend1]"). iIntros (u1 u2) "!# (->&->)". brel_pures'.
        iApply (brel_na_inv _ _ (nroot.@"keyinv")); [set_solver|]. iFrame "Hinv".
        iIntros "((Hγ & Hγs & Hko) & Hclose)".
        iDestruct "Hko" as "[(Hko & Hkos)|(%cc & Hko & Hkos)]".
        * iApply (brel_load_l _ _ _ [CaseCtx _ _] with "Hko"). iIntros "!> Hko".
          iApply (brel_load_r _ _ _ _ [CaseCtx _ _] with "Hkos"). iIntros "Hkos".
          iApply brel_na_close. iFrame "Hclose". iSplitL "Hγ Hγs Hko Hkos".
          { iNext. iFrame "Hγ Hγs". iLeft. iFrame. }
          brel_pures'. iDestruct ("Hkont" with "HQN") as "Hbrel".
          iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
        * iApply (brel_load_l _ _ _ [CaseCtx _ _] with "Hko"). iIntros "!> Hko".
          iApply (brel_load_r _ _ _ _ [CaseCtx _ _] with "Hkos"). iIntros "Hkos".
          iApply brel_na_close. iFrame "Hclose". iSplitL "Hγ Hγs Hko Hkos".
          { iNext. iFrame "Hγ Hγs". iRight. iExists cc. iFrame. }
          brel_pures'. iDestruct ("HQS" $! (g ^+ cc)%g) as "HQSg".
          iDestruct ("Hkont" with "HQSg") as "Hbrel".
          iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
  Qed.

  Lemma CHAN_body_typed :
    ⊢ ∀ (θ θJ : sem_row Σ),
      sem_typed [("f", hdl cli θ); ("ChanOp", chan θJ); ("doGK", gk θJ)]
        CHAN_body CHAN_body (sem_row_union θJ θ) (𝟙)%T [].
  Proof using Type*.
    (* Open-body version of [CHAN_typed]: [f]/[ChanOp]/[doGK] come from the
       environment, and both interfaces are at the SAME row [θJ] (whereas
       [CHAN_typed] uses two independent rows [θ1],[θ2]).  Row idempotence is
       NOT derivable ([to_iThy_le] enforces [distinct']), so we re-prove the
       body directly at the single row [θJ]: the effect firing at [θJ] once
       makes the residual effect [θJ ∪ θ] (not [θJ ∪ (θJ ∪ θ)]).  Compared to
       [CHAN_typed], every row-management [submseteq] script drops one segment
       ([Lθ1 ++ Lθ2 ++ Lθ] collapses to [LθJ ++ Lθ]). *)
    iIntros (θ θJ). iIntros (vs) "!# Henv".
    rewrite !env_sem_typed_cons env_sem_typed_empty.
    iDestruct "Henv" as "((%f1 & %f2 & %Hlf & Hff) & (%c1 & %c2 & %Hlc & HChanOp) & (%d1 & %d2 & %Hld & #Hgk) & _)".
    rewrite /CHAN_body.
    assert (Hf' : (fst<$>vs) !! "f" = Some f1) by (rewrite lookup_fmap Hlf //).
    assert (Hc' : (fst<$>vs) !! "ChanOp" = Some c1) by (rewrite lookup_fmap Hlc //).
    assert (Hd' : (fst<$>vs) !! "doGK" = Some d1) by (rewrite lookup_fmap Hld //).
    assert (Hf2' : (snd<$>vs) !! "f" = Some f2) by (rewrite lookup_fmap Hlf //).
    assert (Hc2' : (snd<$>vs) !! "ChanOp" = Some c2) by (rewrite lookup_fmap Hlc //).
    assert (Hd2' : (snd<$>vs) !! "doGK" = Some d2) by (rewrite lookup_fmap Hld //).
    simpl; simplify_map_eq.
    iApply (brel_wand _ _ _ (λ v1 v2 : val, 𝟙%T v1 v2) with "[-]"); last first.
    { iModIntro. iIntros (v1 v2) "H". iFrame. }
    iDestruct "HChanOp" as (dsend1 dsend2 drecv1 drecv2) "(->&->&#Hsend&#Hrecv)".
    brel_pures'.
    iApply brel_alloc_l. iIntros (lm) "!> Hlm". brel_pures_l.
    iApply brel_alloc_r. iIntros (lms) "Hlms". brel_pures_r.
    iApply (brel_na_alloc (∃ v1 v2, lm ↦ v1 ∗ lms ↦ₛ v2 ∗ (Option 𝔾)%T v1 v2)%I
                          (nroot .@ "scmsg")).
    iSplitL "Hlm Hlms". { iNext. iExists _,_. iFrame. iExists _,_. iLeft. done. }
    iIntros "#Hinv".
    iApply brel_effect_l. iIntros (schan1) "!> Hschan1".
    iApply brel_effect_r. iModIntro. iIntros (schan2) "Hschan2 !>".
    brel_pures'.
    iAssert (cli (scchan_row schan1 schan2)
               (λ: "m", do: schan1 (Send "m"), λ: <>, do: schan1 (Recv bob))%V
               (λ: "m", do: schan2 (Send "m"), λ: <>, do: schan2 (Recv bob))%V) as "#Hcli".
    { iExists _,_,_,_. iSplit; [done|]. iSplit; [done|]. rewrite /sem_ty_mbang /=. iSplit.
      - iModIntro. iIntros (a1 a2) "#Hm". brel_pures'.
        iApply (brel_introduction' [schan1] [schan2] (iThySum (SCSend schan1 schan2) (SCRecv schan1 schan2))); [ by left | ].
        rewrite /iThyTraverse /=.
        iExists _,_,[],[], (λ s1 s2, ⌜ s1 = Val #()%V ⌝ ∗ ⌜ s2 = Val #()%V ⌝)%I.
        iSplit;[done|]. iSplit;[iPureIntro; apply NeutralEctx_nil|]. iSplit;[done|]. iSplit;[iPureIntro; apply NeutralEctx_nil|].
        iSplitL.
        + iLeft. iExists a1, a2. iSplit; [iApply "Hm"|]. do 2 (iSplit;[done|]). iModIntro. iSplit; done.
        + iIntros "!>" (s1 s2) "(->&->)". iApply brel_value. iIntros "$ !>". done.
      - iModIntro. iIntros (a1 a2) "#Hu". brel_pures'.
        iApply (brel_introduction' [schan1] [schan2] (iThySum (SCSend schan1 schan2) (SCRecv schan1 schan2))); [ by left | ].
        rewrite /iThyTraverse /=.
        iExists _,_,[],[], (λ s1 s2, ∃ v1 v2 : val, ⌜ s1 = Val v1 ⌝ ∗ ⌜ s2 = Val v2 ⌝ ∗ (Option 𝔾)%T v1 v2)%I.
        iSplit;[done|]. iSplit;[iPureIntro; apply NeutralEctx_nil|]. iSplit;[done|]. iSplit;[iPureIntro; apply NeutralEctx_nil|].
        iSplitL.
        + iRight. do 2 (iSplit;[done|]). iModIntro. iSplit.
          * iExists NONEV, NONEV. do 2 (iSplit;[done|]). iExists _,_. iLeft. done.
          * iIntros (g). iExists (SOMEV g), (SOMEV g). do 2 (iSplit;[done|]). iExists _,_. iRight. iSplit;[done|]. iSplit;[done|]. iExists g. done.
        + iIntros "!>" (s1 s2) "(%v1&%v2&->&->&#Hopt)". iApply brel_value. iIntros "$ !>". done. }
    iDestruct ("Hff" $! (scchan_row schan1 schan2) with "Hcli") as "Hfbrel".
    iApply brel_new_theory.
    iApply (brel_add_label_l with "Hschan1").
    iApply (brel_add_label_r with "Hschan2").
    iApply (brel_exhaustion _ _ [_] [_] with "[Hfbrel]"); [done|done| |].
    { iApply (brel_introduction_mono with "[][$Hfbrel]").
      iApply to_iThy_le_intro'. apply submseteq_skip. rewrite !iLblSig_to_iLblThy_app.
      apply submseteq_inserts_l. reflexivity. }
    iLöb as "IH".
    iSplit; [iIntros (v1 v2) "!# (->&->)"; by brel_pures|].
    iIntros (k1' k2' e1' e2' Q) "!# %Hk1 %Hk2 Hpayload #Hkont".
    iDestruct "Hpayload" as "[HS|HR]".
    - (* SendSecure: store the message, [doGK], encrypt via [G_XOR], [doSend]. *)
      iDestruct "HS" as (m1 m2) "(#Hm & -> & -> & #HQ)".
      iDestruct "Hm" as (gm) "(-> & ->)".
      brel_pures; try (solve [apply Hk1; set_solver]); try (solve [apply Hk2; set_solver]).
      all: try iModIntro.
      iApply (brel_na_inv _ _ (nroot.@"scmsg")); [set_solver|]. iFrame "Hinv".
      iIntros "((%v1 & %v2 & Hlm & Hlms & #Hopt) & Hclose)".
      iApply (brel_load_l _ _ _ [CaseCtx _ _] with "Hlm"). iIntros "!> Hlm".
      iApply (brel_load_r _ _ _ _ [CaseCtx _ _] with "Hlms"). iIntros "Hlms".
      iDestruct "Hopt" as (w1 w2) "[(->&->&_)|(->&->&#Hgw)]".
      + (* first message: store, get key, encrypt, forward. *)
        brel_pures.
        iApply (brel_store_l _ _ _ [AppRCtx _] with "Hlm"). iIntros "!> Hlm".
        iApply (brel_store_r _ _ _ _ [AppRCtx _] with "Hlms"). iIntros "Hlms".
        brel_pures.
        iApply brel_na_close. iFrame "Hclose". iSplitL "Hlm Hlms".
        { iNext. iExists (SOMEV (vgval gm)), (SOMEV (vgval gm)). iFrame. iExists _,_. iRight.
          do 2 (iSplit;[done|]). iExists gm. done. }
        iApply (brel_bind [AppRCtx _] [AppRCtx _] _ (iLblSig_to_iLblThy θJ)); [iApply traversable_to_iThy| |].
        { iApply to_iThy_le_intro'. apply submseteq_cons. rewrite !iLblSig_to_iLblThy_app.
          apply submseteq_inserts_r. reflexivity. }
        iAssert ((𝟙 + 𝟙)%T bob bob) as "#Hbob". { iExists _,_. iLeft. done. }
        iEval (rewrite /gk /sem_ty_arr /sem_ty_mbang /=) in "Hgk".
        iDestruct ("Hgk" with "Hbob") as "Hgkbob".
        iApply (brel_wand with "[$Hgkbob]"). iIntros (key1 key2) "!# #Hkey".
        iDestruct "Hkey" as (kw1 kw2) "[(->&->&_)|(->&->&#Hgkey)]".
        * brel_pures'. iDestruct ("Hkont" with "HQ") as "Hbrel".
          iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
        * iDestruct "Hgkey" as (gkey) "(->&->)".
          brel_pures'.
          iApply (brel_bind' [CaseCtx _ _] [CaseCtx _ _]); [iApply traversable_to_iThy|].
          iApply (brel_gxor gm gkey).
          -- iIntros (mg) "%Hmg". brel_pures'.
             iApply (brel_bind [AppRCtx _] [AppRCtx _] _ (iLblSig_to_iLblThy θJ)); [iApply traversable_to_iThy| |].
             { iApply to_iThy_le_intro'. apply submseteq_cons. rewrite !iLblSig_to_iLblThy_app.
               apply submseteq_inserts_r. reflexivity. }
             iAssert ((𝔾 × (𝟙 + 𝟙))%T (vgval mg, bob)%V (vgval mg, bob)%V) as "#Harg".
             { iExists _,_,_,_. iSplit;[done|]. iSplit;[done|]. iSplit; [iExists mg; done | iExists _,_; iLeft; done]. }
             iEval (rewrite /sem_ty_arr /sem_ty_mbang /=) in "Hsend".
             iDestruct ("Hsend" with "Harg") as "Hsend1".
             iApply (brel_wand with "[$Hsend1]"). iIntros (u1 u2) "!# (->&->)". brel_pures'.
             iDestruct ("Hkont" with "HQ") as "Hbrel".
             iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
          -- iIntros "%Hnone". brel_pures'.
             iDestruct ("Hkont" with "HQ") as "Hbrel".
             iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
      + (* message already stored: just resume. *)
        brel_pures.
        iApply brel_na_close. iFrame "Hclose". iSplitL "Hlm Hlms".
        { iNext. iExists (InjRV w1), (InjRV w2). iFrame "Hlm Hlms". iExists _,_. iRight.
          do 2 (iSplit;[done|]). iApply "Hgw". }
        iDestruct ("Hkont" with "HQ") as "Hbrel".
        iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
    - (* RecvSecure: get key, [doRecv], decrypt via [G_XOR], forward. *)
      iDestruct "HR" as "(-> & -> & #HQ)". iDestruct "HQ" as "(#HQN & #HQS)".
      brel_pures; try (solve [apply Hk1; set_solver]); try (solve [apply Hk2; set_solver]).
      iAssert ((𝟙 + 𝟙)%T alice alice) as "#Halice". { iExists _,_. iRight. done. }
      iApply (brel_bind [AppRCtx _] [AppRCtx _] _ (iLblSig_to_iLblThy θJ)); [iApply traversable_to_iThy| |].
      { iApply to_iThy_le_intro'. apply submseteq_cons. rewrite !iLblSig_to_iLblThy_app.
        apply submseteq_inserts_r. reflexivity. }
      iEval (rewrite /gk /sem_ty_arr /sem_ty_mbang /=) in "Hgk".
      iDestruct ("Hgk" with "Halice") as "Hgkal".
      iApply (brel_wand with "[$Hgkal]"). iIntros (key1 key2) "!# #Hkey".
      iDestruct "Hkey" as (kw1 kw2) "[(->&->&_)|(->&->&#Hgkey)]".
      + brel_pures'. iDestruct ("Hkont" with "HQN") as "Hbrel".
        iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
      + iDestruct "Hgkey" as (gkey) "(->&->)".
        brel_pures'.
        iApply (brel_bind [AppRCtx _] [AppRCtx _] _ (iLblSig_to_iLblThy θJ)); [iApply traversable_to_iThy| |].
        { iApply to_iThy_le_intro'. apply submseteq_cons. rewrite !iLblSig_to_iLblThy_app.
          apply submseteq_inserts_r. reflexivity. }
        iAssert ((𝟙 + 𝟙)%T bob bob) as "#Hbob". { iExists _,_. iLeft. done. }
        iEval (rewrite /sem_ty_arr /sem_ty_mbang /=) in "Hrecv".
        iDestruct ("Hrecv" with "Hbob") as "Hrecvbob".
        iApply (brel_wand with "[$Hrecvbob]"). iIntros (r1 r2) "!# #Hr".
        iDestruct "Hr" as (rw1 rw2) "[(->&->&_)|(->&->&#Hgx)]".
        * brel_pures'. iDestruct ("Hkont" with "HQN") as "Hbrel".
          iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
        * iDestruct "Hgx" as (gx) "(->&->)".
          brel_pures'.
          iApply (brel_bind' [CaseCtx _ _] [CaseCtx _ _]); [iApply traversable_to_iThy|].
          iApply (brel_gxor gx gkey).
          -- iIntros (mg) "%Hmg". brel_pures'. iDestruct ("HQS" $! mg) as "HQSmg".
             iDestruct ("Hkont" with "HQSmg") as "Hbrel".
             iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
          -- iIntros "%Hnone". brel_pures'. iDestruct ("Hkont" with "HQN") as "Hbrel".
             iApply (brel_exhaustion _ _ [_] [_] with "[$Hbrel]"); [done|done|]. iApply "IH".
  Qed.

  Lemma REAL_CHAN_DH_RED_sem_typed `{!probblazeRGS Σ} :
    ⊢ ⊨ᵥ REAL_CHAN_DH_RED ≤ REAL_CHAN_DH_RED
      : ((𝟙 ⊸ (sem_ty_group × sem_ty_group) × sem_ty_group) → τ).
  Admitted.

End new_comp_verification.

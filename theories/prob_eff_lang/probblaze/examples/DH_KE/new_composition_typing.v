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
  Let Key := S (S n'').
  Let Support := S (S n'').
  Variable xor_struct : XOR (Key := Key) (Support := Support).
  Context `{!XOR_spec (Key := Key) (Support := Support) (H := xor_struct)}.

  Notation "'𝔾'" := sem_ty_group.

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

  Lemma F_AUTH_typed :
    ⊢ sem_val_typed F_AUTH F_AUTH (τ__F chan chan).
  Proof using Type*. Admitted.

  Lemma DH_SIM_typed :
    ⊢ sem_val_typed DH_SIM DH_SIM (τ__F chan leakI).
  Proof using Type*. Admitted.

  Lemma F_KE_lazy_alice_typed :
    ⊢ sem_val_typed F_KE_lazy_alice F_KE_lazy_alice (τ__F leakI gk).
  Proof using Type*. Admitted.

  Lemma CHAN_typed :
    ⊢ ∀ θ, sem_val_typed (CHAN xor) (CHAN xor) ((hdl cli θ ⊸ τ__f θ chan gk)%T).
  Proof using Type*. Admitted.

  (* [F_AUTH ∘f DH_SIM], in both value and open (sem_typed) presentations. *)
  Lemma F_AUTH_DH_SIM_typed_val :
    ⊢ sem_val_typed (F_AUTH ∘f DH_SIM) (F_AUTH ∘f DH_SIM) (τ__F chan leakI).
  Proof using Type*. Admitted.

  Lemma F_AUTH_DH_SIM_typed :
    ⊢ sem_typed [] (F_AUTH ∘f DH_SIM) (F_AUTH ∘f DH_SIM) ⊥ (τ__F chan leakI) [].
  Proof using Type*. Admitted.

  Lemma F_KE_F_OAUTH_typed :
    ⊢ sem_typed [] (F_KE_lazy_alice ||ᵣ F_OAUTH) (F_KE_lazy_alice ||ᵣ F_OAUTH) ⊥
        ((∀ᵣ θ, hdl chan θ ⊸
            (∀ᵣ θ1, oaleak θ1 ⊸ ∀ᵣ θ2, leakI θ2
                    -{ sem_row_union θ1 (sem_row_union θ2 θ) }-∘ 𝟙))%T) [].
  Proof using Type*. Admitted.

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
    (λ: "doGK",
      let, ("doSend", "doRecv") := "ChanOp" in
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
  Proof using Type*. Admitted.

  Lemma CHAN_body_typed :
    ⊢ ∀ (θ θJ : sem_row Σ),
      sem_typed [("f", hdl cli θ); ("ChanOp", chan θJ)]
        CHAN_body CHAN_body (sem_row_union θJ θ) (𝟙)%T [].
  Proof using Type*. Admitted.

End new_comp_verification.

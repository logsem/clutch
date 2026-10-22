From iris.proofmode Require Import base proofmode classes.                                             
From iris.base_logic.lib Require Import  na_invariants.   
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode
  spec_rules spec_ra
  class_instances.
From clutch.prob_eff_lang.probblaze Require Import tactics.
From clutch.prob_eff_lang.probblaze Require Import sem_types sem_row sem_sig sem_judgement sem_def.
From clutch.prob_eff_lang.probblaze.examples.DH_KE Require Import ske ske_sec_chan_def.


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
  

  Definition alphaN : namespace := nroot .@ "alpha".
  Definition betaN : namespace := nroot .@ "beta".
 
  (*Theories for the interaction of the secure channel with the environment*)
  (*-------------------------------------------------------------*)

  (* Theories for the authenticated channel leaks *)
  (*-------------------------------------------------------------*)
  Program Definition LASend (l1 l2 : label) dst : iThy Σ :=
    λ e1 e2, (λne Q,
                ∃ m1 m2 : val,
                  ⌜e1 = (do: l1 (SendV (m1, dst)))⌝%E ∗
                  ⌜e2 = (do: l2 (SendV (m2, dst)))⌝%E ∗
                  Q (Val #()%V) (Val #()%V))%I.
  Next Obligation. solve_proper. Qed.
  (* Sent BY Bob TO Alice*)
  Definition LASendBob (la1 la2 : label) : iThy Σ := LASend la1 la2 alice.
  (* Sent BY Alice TO Bob*)
  Definition LASendAlice (la1 la2 : label) : iThy Σ := LASend la1 la2 bob.

  Program Definition LARecv (l1 l2 : label) from : iThy Σ :=
     λ e1 e2, (λne Q,
                ⌜ e1 = do: l1 (RecvV from) ⌝%E ∗
                ⌜ e2 = do: l2 (RecvV from) ⌝%E ∗
                ((∀ b1 b2 : nat, Q (SOMEV #b1) (SOMEV #b2)) ∧ Q NONEV NONEV)
             )%I.
  Next Obligation. solve_proper. Qed.

  (*Recv FROM Bob *)
  Definition LARecvBob (la1 la2 : label) : iThy Σ :=
    LARecv la1 la2 bob.
  (*Recv FROM Alice*)
  Definition LARecvAlice (la1 la2 : label) : iThy Σ :=
    LARecv la1 la2 alice.
  
  (* Theories for the key exchange leaks*)
  (*---------------------------------------------------------*)

  Program Definition KLeakSend (l1 l2 : label) dst : iThy Σ :=
     λ e1 e2, (λne Q,
                ⌜ e1 = do: l1 (SendV dst) ⌝%E ∗
                ⌜ e2 = do: l2 (SendV dst) ⌝%E ∗
                Q (Val #()%V) (Val #()%V))%I.
  Next Obligation. solve_proper. Qed.
  (*Send TO Alice*)
  Definition KLeakSendAlice (kl1 kl2 : label) : iThy Σ :=
    KLeakSend kl1 kl2 alice.
  (*Send TO Bob *)
  Definition KLeakSendBob (kl1 kl2 : label) : iThy Σ :=
    KLeakSend kl1 kl2 bob.
  
  Program Definition KLeakRecv (kl1 kl2 : label) from : iThy Σ :=
     λ e1 e2, (λne Q,
                ⌜ e1 = do: kl1 (RecvV from) ⌝%E ∗
                ⌜ e2 = do: kl2 (RecvV from) ⌝%E ∗
                (Q NONEV NONEV ∗ Q (SOMEV #0) (SOMEV #0)))%I.
  Next Obligation. solve_proper. Qed.
  (* Recv FROM Alice *)
  Definition KLeakRecvAlice (kl1 kl2 : label) : iThy Σ := KLeakRecv kl1 kl2 alice.
  (* Recv FROM Bob *)
  Definition KLeakRecvBob (kl1 kl2 : label) : iThy Σ := KLeakRecv kl1 kl2 bob.
  

  (*Theories relating the secure channel effects for the client*)
  (*---------------------------------------------------------*)

  Program Definition SendSec (ssend1 ssend2 : label) : iThy Σ :=
    λ e1 e2, (λne Q,
                ∃ m : nat,
                  (⌜ e1 = do: ssend1 (#m) ⌝%E ∗
                   ⌜ e2 = do: ssend2 (#m) ⌝%E)  ∗
                  (Q (Val #()%V) (Val #()%V))
             )%I.
  Next Obligation. solve_proper. Qed.

  (* [doSecRecv] is a thunk, so the INTERFACE argument type is 𝟙 -- but the
     effect PAYLOAD is the closed constant [bob].  Do not "simplify" it to #(). *)
  Program Definition RecvSecB (srecv1 srecv2 : label) : iThy Σ :=
    λ e1 e2, (λne Q,
                ⌜ e1 = do: srecv1 bob ⌝%E ∗
                ⌜ e2 = do: srecv2 bob ⌝%E ∗
                ((∀ g : mt, Q (SOMEV (fvtval g)) (SOMEV (fvtval g))) ∧ Q NONEV NONEV)
             )%I.
  Next Obligation. solve_proper. Qed.

  Program Definition keyleak_mono (keyleak1 keyleak2 : label) := {| pmono_prot_car := iThySum (iThySum (KLeakSendAlice keyleak1 keyleak2) (KLeakRecvAlice keyleak1 keyleak2)) (iThySum (KLeakSendBob keyleak1 keyleak2) (KLeakRecvBob keyleak1 keyleak2)) ; pmono_prot_prop := _|}.
  Next Obligation.
    iIntros (????).
    iIntros (??) "#HΦ [[HS | HR] | [HS | HR]]".
    1: iLeft; iLeft. 2: iLeft; iRight. 3: iRight; iLeft. 4: iRight; iRight.
    1,3 : iDestruct "HS" as (??) "H"; simpl; iSplit; first done; iSplit; first done; by iApply "HΦ".
    all: iDestruct "HR" as (??) "(H1 & H2)"; simpl; do 2 (iSplit; first done); iSplitL "H1"; iApply "HΦ"; [iApply "H1"|iApply "H2"]. 
  Qed.
  Definition keyleak (keyleak1 keyleak2 : label) := @SemSig Σ (keyleak_mono keyleak1 keyleak2) (keyleak1, keyleak2).
  Lemma keyleak_pers_mono_row (keyleak1 keyleak2 : label) : ⊢ pers_mono_row (iLblSig_to_iLblThy [([keyleak1] , [keyleak2] , keyleak keyleak1 keyleak2)]).
  Proof.
    intros. unfold pers_mono_row. iIntros (????) "#HΦΦ'". iIntros (???) "(%H1 & H2)".
    iSplitR "H2"; [iPureIntro; apply H1 |].
    unfold keyleak in H1. simpl in H1. unfold keyleak_mono in H1. simpl in H1.
    apply list_elem_of_singleton in H1. simpl in H1.
    inversion H1. simpl in *.
    iDestruct "H2" as (?e1' ?e2' ?k1 ?k2 ?S) "H2e1e2".
    iExists e1', e2', k1, k2, S.
    iDestruct "H2e1e2" as "(%Hv1 & (%HNk1 & (%Hv2 & (%HNk2 & HS))))".
    repeat iSplit; try iPureIntro; try auto.
    { iDestruct "HS" as "(He1e2 & Hs1s2)". iApply "He1e2". }
    { iDestruct "HS" as "(He1e2 & #Hs1s2)". iModIntro.
      iIntros (??) "HS". iApply "HΦΦ'". iApply "Hs1s2". iApply "HS".
    }
  Qed.

  Definition keyleak_row (keyleak1 keyleak2 : label) := SemRow [([keyleak1] , [keyleak2] , keyleak keyleak1 keyleak2)] (keyleak_pers_mono_row keyleak1 keyleak2).

  Program Definition leakauth_mono (leakauth1 leakauth2 : label) := {| pmono_prot_car := iThySum (iThySum (LASendAlice leakauth1 leakauth2) (LASendBob leakauth1 leakauth2)) (iThySum (LARecvAlice leakauth1 leakauth2) (LARecvBob leakauth1 leakauth2)) ; pmono_prot_prop := _ |}.
  Next Obligation.
    iIntros (??????) "#HΦ [[HS | HS] | [HR | HR]]".
    1: iLeft; iLeft. 2: iLeft; iRight. 3: iRight; iLeft. 4: iRight; iRight.
    1,2 : iDestruct "HS" as (??) "(H1 & H2 & H3)"; simpl; iExists m1, m2; iSplit; first done; iSplit; first done;
                                                                         by iApply "HΦ".
    all : iDestruct "HR" as "(H1 & H2 & H3)"; simpl; do 2 (iSplit; first done); iSplit; try iIntros (??); iApply "HΦ".
    1,3 : iDestruct "H3" as "[H3 _]"; iApply "H3".
    all : iDestruct "H3" as "[_ $]".
  Qed.

  Definition leakauth (leakauth1 leakauth2 : label) := @SemSig Σ (leakauth_mono leakauth1 leakauth2) (leakauth1, leakauth2).
  Lemma leakauth_pers_mono_row (leakauth1 leakauth2 : label) : ⊢ pers_mono_row (iLblSig_to_iLblThy [([leakauth1], [leakauth2], leakauth leakauth1 leakauth2)]).
  Proof.
    intros. unfold pers_mono_row. iIntros (????) "#HΦΦ'". iIntros (???) "(%H1 & H2)".
    iSplitR "H2"; [iPureIntro; apply H1 |].
    unfold keyleak in H1. simpl in H1. unfold keyleak_mono in H1. simpl in H1.       
    apply list_elem_of_singleton in H1. simpl in H1.
    inversion H1. simpl in *.
    iDestruct "H2" as (?e1' ?e2' ?k1 ?k2 ?S) "H2e1e2".
    iExists e1', e2', k1, k2, S.
    iDestruct "H2e1e2" as "(%Hv1 & (%HNk1 & (%Hv2 & (%HNk2 & HS))))".
    repeat iSplit; try iPureIntro; try auto.
    - iDestruct "HS" as "(He1e2 & Hs1s2)". iApply "He1e2".
    - iDestruct "HS" as "(He1e2 & #Hs1s2)". iModIntro.
      iIntros (??) "HS". iApply "HΦΦ'". iApply "Hs1s2". iApply "HS".
  Qed.

  Definition leakauth_row (leakauth1 leakauth2 : label) := SemRow [([leakauth1],[leakauth2] , leakauth leakauth1 leakauth2 )] (leakauth_pers_mono_row leakauth1 leakauth2).
  Program Definition envsec_row (keyleak1 keyleak2 leakauth1 leakauth2 : label) :=
    sem_row_union (keyleak_row keyleak1 keyleak2) (leakauth_row leakauth1 leakauth2).

  Program Definition sec_channel_mono (ssend1 ssend2 srecv1 srecv2 : label) := {| pmono_prot_car := iThySum (SendSec ssend1 ssend2) (RecvSecB srecv1 srecv2) ; pmono_prot_prop := _ |}.
  Next Obligation.
    iIntros (????). unfold pers_mono. iIntros (????) "#Hw1w2 [HS | HR]".
    - iLeft. simpl.  iDestruct "HS" as (?m) "(Hv1v2 & HS)". iExists m.
      iSplitL "Hv1v2"; [iFrame |iApply "Hw1w2"; iApply "HS"].
    - iRight. simpl.   iDestruct "HR" as "(%Hv1 &(%Hv2 & HR))". repeat iSplit; (try by iPureIntro); try iIntros (?); iApply "Hw1w2".
      + iDestruct "HR" as "(HR&_)"; iApply "HR".
      + iDestruct "HR" as "(_&$)".
  Qed.

  (* [SemSig] carries only ONE label pair; it is dropped by [iLblSig_to_iLblThy]
     and every row below is built by hand, so the [send] pair is a safe choice. *)
  Definition sec_channel (ssend1 ssend2 srecv1 srecv2 : label) := @SemSig Σ (sec_channel_mono ssend1 ssend2 srecv1 srecv2) (ssend1, ssend2).

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

  (* The client's two thunks are typed against ANY single-entry row whose theory
     is [sec_channel ssend_l ssend_r srecv_l srecv_r]; the proof never looks at
     the label lists, so the asymmetric [client_row] above fits it unchanged. *)
  Lemma SEM_TYPED_EFF (l1s l2s : list label) (ssend_l ssend_r srecv_l srecv_r : label)
        (Hpm : ⊢ pers_mono_row
                   (iLblSig_to_iLblThy [(l1s, l2s, sec_channel ssend_l ssend_r srecv_l srecv_r)])) :
      let θ := SemRow [(l1s, l2s, sec_channel ssend_l ssend_r srecv_l srecv_r)] Hpm in
      ⊢
        (sem_val_typed  ((λ: "m", do: ssend_l "m"), (λ: <>, do: srecv_l bob))%V ((λ: "m", do: ssend_r "m") , (λ: <>, do: srecv_r bob))%V (((sem_ty_nat)%T -{ θ }-> 𝟙) × (𝟙 -{ θ }-> (Option msg.(sem_τFT))))%T)%I.
  Proof.
    unfold sem_val_typed. simpl. intros.
    iModIntro. rewrite /sem_ty_arr /sem_ty_mbang /sem_ty_option /sem_ty_sum //=. rewrite /sem_ty_prod.
    iExists (λ: "m", do: ssend_l "m")%V , (λ: "m", do: ssend_r "m")%V , (λ: <>, do: srecv_l bob)%V , (λ: <>, do: srecv_r bob)%V.  repeat iSplit; try iPureIntro; try auto.
    + iModIntro. iIntros (??) "Hw1w1". brel_pures'.
      iApply brel_introduction'; try constructor;
        iExists _,_,[],[],_; do 2 (iSplit; [by iPureIntro|]; iSplit; [iPureIntro; apply NeutralEctx_nil|]);
                          iSplit; try (iIntros (??) "!# H"; iApply "H").
      simpl. iLeft. 
      iDestruct "Hw1w1" as (m) "[%Hw1 %Hw2]".
      iExists _. repeat iSplit; try iPureIntro; try auto; unfold SendV; try rewrite -> Hw1;
        try rewrite -> Hw2; try reflexivity.
      iApply brel_value. iIntros "$ !>".
      unfold sem_ty_unit; iPureIntro.
      split; reflexivity.
    + iModIntro. iIntros (??) "Hw1w1". unfold sem_ty_unit.
      iDestruct "Hw1w1" as "[%Hw1 %Hw2]". unfold bob. rewrite -> Hw1. rewrite -> Hw2.
      brel_pures'.
      iApply brel_introduction'; try constructor.
      iExists _,_,[],[],_; do 2 (iSplit; [by iPureIntro|]; iSplit; [iPureIntro; apply NeutralEctx_nil|]);
                        iSplit; try (iIntros (??) "!# H"; iApply "H"). iRight.
      do 2 (iSplit; first done). iSplit.
      - iIntros (?). iApply brel_value. iIntros "$ !>".
        iExists _,_; iRight; iPureIntro; do 2 (split; first done); by exists g.
      - iApply brel_value. iIntros "$ !>".
        iExists _,_; iLeft; by iPureIntro. 
  Qed.

  (* Tape assertions are [ghost_map_elem]s, so a full one is exclusive: it
     cannot coexist with any other assertion -- full or discarded -- for the
     same location.  [tapeN_excl] is what rules out the stale disjuncts of the
     invariant while the sender holds the (never-presampled) key tape. *)
  Lemma spec_tapeN_excl (l : loc) M dq ns ns' :
    l ↪ₛN (M; ns) -∗ l ↪ₛ{dq}N (M; ns') -∗ False.
  Proof.
    iIntros "(%&%&H1) (%&%&H2)".
    by iDestruct (ghost_map_elem_ne with "H1 H2") as %?.
  Qed.

  Lemma tapeN_excl (l : loc) M dq ns ns' :
    l ↪N (M; ns) -∗ l ↪{dq}N (M; ns') -∗ False.
  Proof.
    iIntros "(%&%&H1) (%&%&H2)".
    by iDestruct (ghost_map_elem_ne with "H1 H2") as %?.
  Qed.

  Definition τsc :=  (∀ᵣ θ__L ,(∀ᵣ θₕ, (((sem_ty_nat -{ θₕ }->  𝟙) × (𝟙 -{ θₕ }-> (Option msg.(sem_τFT)))) -{ sem_row_union  θₕ θ__L }-∘ 𝟙)) ⊸ (*type of client*)
                  (∀ᵣ θ₁, ∀ᵣ θ₂,  ((((cipher.(sem_τFT) × (𝟙 + 𝟙)) -{ θ₁ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ₁ }-> Option 𝟙)) × (((𝟙 + 𝟙) -{ θ₂ }-> 𝟙) × (𝟙 + 𝟙) -{ θ₂ }-> Option 𝟙)) -{ sem_row_union (¡θ₁) (sem_row_union (¡θ₂)%R θ__L) }-∘ 𝟙))%T.

  (* The reversed refinement.  Mirror image of [game2_sc_ideal] below: every
     left-hand step becomes a right-hand step and vice versa, the heap and tape
     assertions swap sides, and the client's row becomes [client_row'] because
     the four-label ideal side is now on the left. *)
  Lemma sc_ideal_game2 :
    ⊢ sem_typed [] sc_ideal game2 ⊥ τsc [].
  Proof using All with (brel_pures'; repeat foldkont;
                        try (lazymatch goal with
                             | |- _ ∉ _ => simpl;
                                 repeat (match goal with
                                         | HND : NoDup _ |- _ => rewrite !NoDup_cons in HND
                                         end);
                                 set_unfold; tauto
                             | |- _ ∧ _ => simpl;
                                 repeat (match goal with
                                         | HND : NoDup _ |- _ => rewrite !NoDup_cons in HND
                                         end);
                                 set_unfold; tauto
                             end)).
    iIntros (?) "!# _ //=". 
    rewrite /game2 /sc_ideal /reduction /enc_ideal /RED_CHAN /CHAN_SIM /F_CHAN /F_KE_lazy_alice /F_OAUTH /func_comp /right_composition.
    repeat (rewrite lookup_delete_eq || (rewrite lookup_delete_ne; last done))...

    iModIntro. iSplit; last done.
    iIntros (θL f1 f2) "Hff"...
    iIntros "!>" (autheff keyeff autheffkeyeff_l autheffkeyeff_r) "Hauthkey".
    rewrite /sem_ty_prod /=.
    iDestruct "Hauthkey" as (w1 w1' w2 w2') "(-> & -> & [Hautheff Hkeyeff])".
    iDestruct "Hautheff" as (asnd_l asnd_r arcv_l arcv_r) "(-> & -> & (#Hasnd & #Harcv))"...
    iDestruct "Hkeyeff" as (kysnd_l kysnd_r kyrcv_l kyrcv_r) "(-> & -> & (#Hkeysnd & #Hkeyrcv))".
    brel_pures'.

    (* Allocation/initialization.  Left (game2): the key tape, the lazy key
       cache, [getKey], then F_OAUTH's and RED_CHAN's state.  Right (sc_ideal):
       the simulator's ciphertext cell and its new [started] flag, then
       F_CHAN's state. *)
    brel_alloctape_r γr as "Hγr"...
    brel_alloc_r lcr as "Hlcr"...
    brel_effect_r gkr as "Hgkr"...
    brel_alloc_r lamr as "Hlamr"...
    brel_effect_r sr as "Hsr"...
    brel_effect_r rr as "Hrr"...
    brel_alloc_r lmr as "Hlmr"...
    brel_effect_r ssr as "Hssr"...
    brel_effect_r srr as "Hsrr"...
    brel_alloc_l laml as "Hlaml"...
    brel_alloc_l lstl as "Hlstl"...
    brel_effect_l lsl as "Hlsl"...
    brel_effect_l lrl as "Hlrl"...
    brel_alloc_l lml as "Hlml"...
    brel_effect_l ssl as "Hssl"...
    brel_effect_l srl as "Hsrl"...

    (* Setting up the client *)
    set (θ := client_row' sr rr lsl lrl gkr ssl srl ssr srr).
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
    iApply (brel_add_label_r with "Hrr").
    iApply (brel_add_label_r with "Hsr").
    iApply (brel_add_label_l with "Hlsl").
    iApply (brel_add_label_l with "Hlrl").

    iApply brel_learn. iIntros "%Hdist' _".
    assert (NoDup [sr; rr; gkr; srr; ssr]) as Hnd_r.
    { unfold distinct in Hdist'. destruct Hdist' as [_ Hd'].
      unfold distinct_r in Hd'. simpl in Hd'.
      repeat (rewrite -> labels_r_cons in Hd').
      by (eapply NoDup_app in Hd'; destruct Hd' as [Hd' _]). }

    assert (NoDup [lrl; lsl; srl; ssl]) as Hnd_l.
    { unfold distinct in Hdist'. destruct Hdist' as [Hd' _].
      unfold distinct_l in Hd'. simpl in Hd'.
      rewrite !labels_l_cons in Hd'.
      by (eapply NoDup_app in Hd'; destruct Hd' as [Hd' _]). }

    (* The invariant.  Three states, as in the real/reduction proof:
         I0  nothing has happened;
         I1  a valid secure send has STARTED -- the plaintext is recorded on
             both sides, the real side has cached a key ([lcr]) and the
             simulator has flipped its [started] flag, but no ciphertext has
             been produced (the key leak may still fail, or be in flight);
         I2  the ciphertext has been drawn and leaked; it is the SAME on both
             sides, because the two [rand_cipher] draws are coupled by the
             identity.
       [lcr] and [lstl] move together: that is exactly the agreement that makes
       the receive branch work in state I0.  The key tape [γr] is never
       presampled and acts as the sender's exclusive token: it is absent from
       I1 (the sender holds it across the two key leaks), which is how the
       stale disjuncts are ruled out on re-entry. *)
    rewrite Nat2Z.id.
    iAssert (γr ↪ₛN (n; []))%I with "[Hγr]" as "Hγr".
    { iExists []. simpl. iFrame. done. }
    iApply (brel_na_alloc ((lmr ↦ₛ NONEV ∗ lcr ↦ₛ NONEV ∗ lamr ↦ₛ NONEV
                            ∗ lml ↦ NONEV ∗ lstl ↦ NONEV ∗ laml ↦ NONEV
                            ∗ γr ↪ₛN (n; []))
                           ∨ (∃ (mv : mt) (c : nat), lmr ↦ₛ□ SOMEV (fvtval mv) ∗ lcr ↦ₛ□ SOMEV #c ∗ lamr ↦ₛ NONEV
                                           ∗ lml ↦□ SOMEV (fvtval mv) ∗ lstl ↦□ SOMEV #()%V ∗ laml ↦ NONEV)
                           ∨ (∃ (mv : mt) (c : nat) (cph : ct), lmr ↦ₛ□ SOMEV (fvtval mv) ∗ lcr ↦ₛ□ SOMEV #c ∗ lamr ↦ₛ□ SOMEV (fvtval cph)
                                           ∗ lml ↦□ SOMEV (fvtval mv) ∗ lstl ↦□ SOMEV #()%V ∗ laml ↦□ SOMEV (fvtval cph)
                                           ∗ γr ↪ₛ□N (n; []))
              ) alphaN).
    iSplitL "Hlmr Hlcr Hlamr Hlml Hlstl Hlaml Hγr"; [iNext; iLeft; iFrame|].
    iIntros "#HI".

    (* Case on the client's behaviour, and induction *)
    rewrite !iLblSig_to_iLblThy_app !iThyIfMono_iLblSig_to_iThyIfMono.
    iDestruct (brel_introduction_mono _ (([lrl; lsl; srl; ssl], [sr; rr; gkr; srr; ssr], sec_channel ssl ssr srl srr : iThy Σ) :: to_iThyIfMono OS (iLblSig_to_iLblThy autheff) ++ to_iThyIfMono OS (iLblSig_to_iLblThy keyeff) ++ iLblSig_to_iLblThy θL) with "[][$Hff]") as "Hff".
    { iApply to_iThy_le_intro'. solve_submseteq. }
    iApply ((brel_exhaustion (f1 _) ( f2 _)) with "[$Hff]"); [set_solver|set_solver| ].

    iLöb as "IH".
    iSplit; [iIntros (v1 v2) "%Hv1v2 !>"; by brel_pures'|].
    iIntros (?????) "!# %Hk1 %Hk2 [(%m&(->&->)&HQ)|(->&->&HQ)] #Hrel".
    (* Alice tries to send a message m *)
    - brel_pures'; try (apply neutral_ectx); repeat constructor.
      destruct (fvt_of_int_sem (fin_val := msg) m) as [mv|] eqn:Hmv...
      2 : { iApply (brel_fvt_of_int_none_l (fin_val := msg)); first exact Hmv.
            iApply (brel_fvt_of_int_none_r (fin_val := msg)); first exact Hmv...
            iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V) with "[HQ]"); [set_solver|set_solver|by iApply "Hrel"|iApply "IH"]. }
      iApply (brel_fvt_of_int_correct_l (fin_val := msg)); first exact Hmv.
      iApply (brel_fvt_of_int_correct_r (fin_val := msg)); first exact Hmv...
      iApply (brel_na_inv _ _ alphaN); first set_solver.
      iFrame "HI".
      iIntros "(>[(Hlmr&Hlcr&Hlamr&Hlml&Hlstl&Hlaml&Hγr)|[H2|H3]]&Hclose)".
      + (* I0 : this is the first valid send *)
        brel_load_r...
        brel_load_l...
        brel_store_r...
        brel_store_l...
        brel_store_l...
        (* Left: enter [F_KE_lazy_alice]'s one-shot [getKey] handler and take
           the single key sample.  The sample is never used -- [enc_ideal]
           ignores its argument -- so it needs no counterpart on the ideal
           side: the tape is never presampled and [brel_randT_empty_r] resolves
           the draw universally. *)
        iApply (brel_handle_os_r [] [HandleCtx _ _ _ _ _;HandleCtx _ _ _ _ _;HandleCtx _ _ _ _ _;AppRCtx _]).
        { eapply NoDup_cons_1_1. simpl.
          eapply (submseteq_NoDup _ [sr; rr; gkr; srr; ssr]); [solve_submseteq|exact Hnd_r]. }
        iIntros (rgkr) "Hrgkr"...
        brel_load_r...
        iApply brel_randT_empty_r.
        iSplitL "Hγr"; first (iNext; iFrame).
        iIntros (c) "Hγr %Hc"...
        brel_store_r...

        (* Close in state I1, keeping the key tape as the sender's token. *)
        iMod (ghost_map_elem_persist with "Hlmr") as "#Hlmr".
        iMod (ghost_map_elem_persist with "Hlcr") as "#Hlcr".
        iMod (ghost_map_elem_persist with "Hlml") as "#Hlml".
        iMod (ghost_map_elem_persist with "Hlstl") as "#Hlstl".
        iApply brel_na_close. iFrame.
        iSplitL "Hlamr Hlaml".
        { iModIntro. iRight. iLeft. iExists _, _. iFrame "#". iFrame. }

        (* The two key leaks, send(bob) then recv(bob), in lockstep.  On the
           ideal side the call still sits inside the simulator's [lrecv]
           handler, so the right-hand context carries that [HandleCtx] and the
           residual theory [M] must be given explicitly (it has to mention
           [lrl]). *)
        iApply (brel_bind'' [HandleCtx _ _ _ _ _; AppRCtx _] [AppRCtx _]
                  (to_iThyIfMono OS (iLblSig_to_iLblThy keyeff)) [([lrl; lsl; srl; ssl], [sr; rr; gkr; srr; ssr], @iThyBot Σ)]).
        1,2 : set_unfold; tauto.
        { iApply to_iThy_le_intro'. solve_submseteq. }
        iApply brel_mono; [iApply to_iThy_le_refl| |simpl].
        { iApply "Hkeysnd". iExists _, _. by iLeft. }
        iIntros (v1 v2) "(->&->)"...
        iApply (brel_bind'' [HandleCtx _ _ _ _ _; AppRCtx _] [AppRCtx _]
                  (to_iThyIfMono OS (iLblSig_to_iLblThy keyeff)) [([lrl; lsl; srl; ssl], [sr; rr; gkr; srr; ssr], @iThyBot Σ)]).
        1,2 : set_unfold; tauto.
        { iApply to_iThy_le_intro'. solve_submseteq. }
        iApply brel_mono; [iApply to_iThy_le_refl| |simpl].
        { iApply "Hkeyrcv". iExists _, _. by iLeft. }
        iIntros (v1' v2') "(%&%&[(->&->&->&->)|(->&->&->&->)])"...
        (* Key establishment failed: neither side produces a ciphertext, and
           neither raises the authenticated-send leak. *)
        { brel_cont_r... iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V) with "[HQ]"); [set_solver|set_solver|by iApply "Hrel"|iApply "IH"]. }
        brel_cont_r...
        iApply (brel_na_inv _ _ alphaN); first set_solver.
        iFrame "HI".
        iIntros "(>[(_&_&_&_&_&_&Hγr')|[(%&%&_&_&Hlamr&_&_&Hlaml)|(%&%&%&_&_&_&_&_&_&Hγr')]]&Hclose)".
        (* We still hold the key tape, so the invariant cannot have moved. *)
        { iExFalso. iApply (spec_tapeN_excl with "Hγr Hγr'"). }
        2 : { iExFalso. iApply (spec_tapeN_excl with "Hγr Hγr'"). }
        brel_load_l...
        (* The one coupling of the whole proof: both sides draw a ciphertext
           and we make the two draws agree. *)
        iApply (rand_cipher_coupl (H := SKE)).
        iIntros (cph)...
        brel_load_r...
        brel_store_r...
        brel_store_l...
        iMod (ghost_map_elem_persist with "Hlamr") as "#Hlamr".
        iMod (ghost_map_elem_persist with "Hlaml") as "#Hlaml".
        iDestruct (spec_tape_to_persistent with "Hγr") as ">#Hγr".
        iApply brel_na_close.
        iFrame. iSplitR; [iNext; do 2 iRight; iExists _,_,_; iFrame "#"|].
        (* Both sides leak the SAME ciphertext on the authenticated channel. *)
        iApply (brel_bind'' _ _ (to_iThyIfMono OS (iLblSig_to_iLblThy autheff)) [([lrl; lsl; srl; ssl], [sr; rr; gkr; srr; ssr], @iThyBot Σ)] _ _ (asnd_l _) (asnd_r _)).
        1,2 : set_unfold; tauto.
        { iApply to_iThy_le_intro'. solve_submseteq. }
        iApply brel_mono; [iApply to_iThy_le_refl| |simpl].
        { iApply "Hasnd". iExists _, _, _, _.
          repeat (iSplit; first done).
          iSplit; last (iExists _,_; by iLeft).
          by iExists _. }
        iIntros (v1'' v2'') "(->&->)"...
        iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V) with "[HQ]"); [set_solver|set_solver|by iApply "Hrel"|iApply "IH"].
      + (* I1 : a send is already in flight or has failed -- both sides just
             observe their recorded plaintext and return. *)
        iDestruct "H2" as "(%&%&#Hlmr&#Hlcr&Hlamr&#Hlml&#Hlstl&Hlaml)".
        brel_load_r...
        brel_load_l...
        iApply brel_na_close.
        iFrame.
        iSplitR "HQ"; [iRight; iLeft; iExists _,_; iFrame "#"; iFrame|].
        iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V) with "[HQ]"); [set_solver|set_solver|by iApply "Hrel"|iApply "IH"].
      + (* I2 : likewise, with the ciphertext already leaked. *)
        iDestruct "H3" as "(%&%&%&#Hlmr&#Hlcr&#Hlamr&#Hlml&#Hlstl&#Hlaml&#Hγr)".
        brel_load_r...
        brel_load_l...
        iApply brel_na_close.
        iFrame.
        iSplitR "HQ"; [iRight; iRight; iExists _,_,_; iFrame "#"|].
        iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V) with "[HQ]"); [set_solver|set_solver|by iApply "Hrel"|iApply "IH"].
    (* Bob tries to receive a message *)
    - brel_pures'.
      { apply not_elem_of_cons; split; last (apply neutral_ectx; repeat constructor).
        intro Heq.
        apply NoDup_ListNoDup in Hnd_r.
        do 4 (apply NoDup_cons_iff in Hnd_r as [?Hn Hnd_r]).
        apply Hn2. by left. }
      { split.
        + apply not_elem_of_cons; split; last (apply neutral_ectx; repeat constructor).
          intro Heq.
          apply NoDup_ListNoDup in Hnd_l.
          do 3 (apply NoDup_cons_iff in Hnd_l as [?Hn Hnd_l]).
          apply Hn1. by left.
        + simpl. rewrite !NoDup_cons in Hnd_r, Hnd_l; set_unfold; tauto. }
      repeat foldkont.
      iApply (brel_handle_os_r [] [HandleCtx _ _ _ _ _;HandleCtx _ _ _ _ _;AppRCtx _]).
      { eapply NoDup_cons_1_1. simpl.
        eapply (submseteq_NoDup _ [sr; rr; gkr; srr; ssr]); [solve_submseteq|exact Hnd_r]. }
      iIntros (rgkr) "Hrgkr"...
      (* key leaks, this time recv(alice) then send(alice) *)
      iApply (brel_bind'' [AppRCtx _] [AppRCtx _] (to_iThyIfMono OS (iLblSig_to_iLblThy keyeff))); try (apply list_subseteq_nil).
      { iApply to_iThy_le_intro'. solve_submseteq. }
      iApply brel_mono; [iApply to_iThy_le_refl| |simpl].
      { iApply "Hkeyrcv". iExists _, _. by iRight. }
      iIntros (v1' v2') "(%&%&[(->&->&->&->)|(->&->&->&->)])"...
      { brel_cont_r...
        iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"].
        iDestruct "HQ" as "[_ $]". }
      iApply (brel_bind'' [AppRCtx _] [AppRCtx _] (to_iThyIfMono OS (iLblSig_to_iLblThy keyeff))); try (apply list_subseteq_nil).
      { iApply to_iThy_le_intro'. solve_submseteq. }
      iApply brel_mono; [iApply to_iThy_le_refl| |simpl].
      { iApply "Hkeysnd". iExists _, _. by iRight. }
      iIntros (v1 v2) "(->&->)"...
      (* Both sides now consult their guard: [lcr] on the real side, [started]
         on the ideal side.  They agree, which is the whole point. *)
      iApply (brel_na_inv _ _ alphaN); first set_solver.
      iFrame "HI".
      iIntros "(>[(Hlmr&Hlcr&Hlamr&Hlml&Hlstl&Hlaml&Hγr)|[H2|H3]]&Hclose)".
      + (* I0 : no send has started, so NEITHER side touches the
           authenticated channel -- both answer NONE straight away. *)
        brel_load_r...
        brel_load_l...
        brel_cont_r...
        iApply brel_na_close.
        iFrame.
        iSplitR "HQ"; [iLeft; iFrame|].
        iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"].
        iDestruct "HQ" as "[_ $]".
      + (* I1 : a send has started but nothing was leaked. *)
        iDestruct "H2" as "(%&%&#Hlmr&#Hlcr&Hlamr&#Hlml&#Hlstl&Hlaml)".
        brel_load_r...
        brel_load_l...
        brel_cont_r...
        (* crossing F_OAUTH's receive handler leaves one label-freshness goal *)
        1 : { apply not_elem_of_cons; split;
                last (first [ solve [apply neutral_ectx; repeat constructor]
                            | solve [rewrite /frame_label /=; set_solver]
                            | solve [cbv [frame_label]; simpl; set_solver] ]).
              intro Heq. subst rr.
              apply NoDup_ListNoDup in Hnd_r.
              apply NoDup_cons_iff in Hnd_r as [Hn _].
              apply Hn. by left. }
        iApply brel_na_close.
        iFrame.
        iSplitR "HQ"; [iRight; iLeft; iExists _,_; iFrame "#"; iFrame|].
        iApply (brel_bind'' _ _ (to_iThyIfMono OS (iLblSig_to_iLblThy autheff)) [([lrl; lsl; srl; ssl], [sr; rr; gkr; srr; ssr], @iThyBot Σ)] _ _ (arcv_l _) (arcv_r _)).
        1,2 : set_unfold; tauto.
        { iApply to_iThy_le_intro'. solve_submseteq. }
        iApply brel_mono; [iApply to_iThy_le_refl| |simpl].
        { iApply "Harcv". iExists _,_; by iLeft. }
        iIntros (w1 w2) "(%&%&[(->&->&->&->)|(->&->&->&->)])"...
        { iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"].
          iDestruct "HQ" as "[_ $]". }
        iApply (brel_na_inv _ _ alphaN); first set_solver.
        iFrame "HI".
        iIntros "(>[(Hlmr'&H')|[H2'|H3']]&Hclose)".
        (* [lmr] already holds the message, so I0 is impossible. *)
        { iExFalso. by iDestruct (ghost_map_elem_ne with "Hlmr' Hlmr") as %?. }
        * iDestruct "H2'" as "(%&%&_&_&HlamrI&_&_&HlamlI)".
          brel_load_r...
          brel_load_l...
          iApply brel_na_close.
          iFrame.
          iSplitR "HQ"; [iRight; iLeft; iExists _,_; iFrame "#"; iFrame|].
          iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"].
          iDestruct "HQ" as "[_ $]".
        * iDestruct "H3'" as "(%&%&%&#Hlmr2&#Hlcr2&#Hlamr2&#Hlml2&#Hlstl2&#Hlaml2&#Hγr2)".
          brel_load_r...
          brel_load_l...
          brel_load_r...
          brel_load_l...
          iApply brel_na_close.
          iFrame.
          iSplitR "HQ"; [iRight; iRight; iExists _,_,_; iFrame "#"|].
          iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"].
          iDestruct "HQ" as "[HQ _]".
          iApply "HQ".
      + (* I2 : the ciphertext has been leaked. *)
        iDestruct "H3" as "(%&%&%&#Hlmr&#Hlcr&#Hlamr&#Hlml&#Hlstl&#Hlaml&#Hγr)".
        brel_load_r...
        brel_load_l...
        brel_cont_r...
        (* crossing F_OAUTH's receive handler leaves one label-freshness goal *)
        1 : { apply not_elem_of_cons; split;
                last (first [ solve [apply neutral_ectx; repeat constructor]
                            | solve [rewrite /frame_label /=; set_solver]
                            | solve [cbv [frame_label]; simpl; set_solver] ]).
              intro Heq. subst rr.
              apply NoDup_ListNoDup in Hnd_r.
              apply NoDup_cons_iff in Hnd_r as [Hn _].
              apply Hn. by left. }
        iApply brel_na_close.
        iFrame.
        iSplitR "HQ"; [iRight; iRight; iExists _,_,_; iFrame "#"|].
        iApply (brel_bind'' _ _ (to_iThyIfMono OS (iLblSig_to_iLblThy autheff)) [([lrl; lsl; srl; ssl], [sr; rr; gkr; srr; ssr], @iThyBot Σ)] _ _ (arcv_l _) (arcv_r _)).
        1,2 : set_unfold; tauto.
        { iApply to_iThy_le_intro'. solve_submseteq. }
        iApply brel_mono; [iApply to_iThy_le_refl| |simpl].
        { iApply "Harcv". iExists _,_; by iLeft. }
        iIntros (w1 w2) "(%&%&[(->&->&->&->)|(->&->&->&->)])"...
        { iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"].
          iDestruct "HQ" as "[_ $]". }
        iApply (brel_na_inv _ _ alphaN); first set_solver.
        iFrame "HI".
        iIntros "(>[(Hlmr'&H')|[H2'|H3']]&Hclose)".
        (* [lmr] already holds the message, so I0 is impossible. *)
        { iExFalso. by iDestruct (ghost_map_elem_ne with "Hlmr' Hlmr") as %?. }
        * iDestruct "H2'" as "(%&%&_&_&HlamrI&_&_&HlamlI)".
          brel_load_r...
          brel_load_l...
          iApply brel_na_close.
          iFrame.
          iSplitR "HQ"; [iRight; iLeft; iExists _,_; iFrame "#"; iFrame|].
          brel_load_r... 
          brel_load_l...
          iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"].
          iDestruct "HQ" as "[HQ _]".
          iApply "HQ".
        * iDestruct "H3'" as "(%&%&%&#Hlmr2&#Hlcr2&#Hlamr2&#Hlml2&#Hlstl2&#Hlaml2&#Hγr2)".
          brel_load_r...
          brel_load_l...
          brel_load_r...
          brel_load_l...
          iApply brel_na_close.
          iFrame.
          iSplitR "HQ"; [iRight; iRight; iExists _,_,_; iFrame "#"|].
          iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"].
          iDestruct "HQ" as "[HQ _]".
          iApply "HQ".
  Qed.

  Lemma game2_sc_ideal :
    ⊢ sem_typed [] game2 sc_ideal ⊥ τsc [].
  (* [brel_pures'] raises a label-freshness side goal every time a reduction
     crosses one of the four/five nested handlers.  They are all consequences
     of [Hnd_l]/[Hnd_r], so discharge them as part of the [...] tactic; the
     [try] makes this a no-op on the main goal (and before [Hnd_l]/[Hnd_r]
     exist). *)
  Proof using All with (brel_pures'; repeat foldkont;
                        try (lazymatch goal with
                             | |- _ ∉ _ => simpl;
                                 repeat (match goal with
                                         | HND : NoDup _ |- _ => rewrite !NoDup_cons in HND
                                         end);
                                 set_unfold; tauto
                             | |- _ ∧ _ => simpl;
                                 repeat (match goal with
                                         | HND : NoDup _ |- _ => rewrite !NoDup_cons in HND
                                         end);
                                 set_unfold; tauto
                             end)).
    iIntros (?) "!# _ //=". rewrite /game2 /sc_ideal /reduction /enc_ideal /RED_CHAN /CHAN_SIM /F_CHAN /F_KE_lazy_alice /F_OAUTH /func_comp /right_composition.
    repeat (rewrite lookup_delete_eq || (rewrite lookup_delete_ne; last done))...
    iModIntro. iSplit; last done.
    iIntros (θL f1 f2) "Hff"...
    iIntros "!>" (autheff keyeff autheffkeyeff_l autheffkeyeff_r) "Hauthkey".
    rewrite /sem_ty_prod /=.
    iDestruct "Hauthkey" as (w1 w1' w2 w2') "(-> & -> & [Hautheff Hkeyeff])".
    iDestruct "Hautheff" as (asnd_l asnd_r arcv_l arcv_r) "(-> & -> & (#Hasnd & #Harcv))"...
    iDestruct "Hkeyeff" as (kysnd_l kysnd_r kyrcv_l kyrcv_r) "(-> & -> & (#Hkeysnd & #Hkeyrcv))".
    brel_pures'.

    (* Allocation/initialization.  Left (game2): the key tape, the lazy key
       cache, [getKey], then F_OAUTH's and RED_CHAN's state.  Right (sc_ideal):
       the simulator's ciphertext cell and its new [started] flag, then
       F_CHAN's state. *)
    brel_alloctape_l γl as "Hγl"...
    brel_alloc_l lcl as "Hlcl"...
    brel_effect_l gkl as "Hgkl"...
    brel_alloc_l laml as "Hlaml"...
    brel_effect_l sl as "Hsl"...
    brel_effect_l rl as "Hrl"...
    brel_alloc_l lml as "Hlml"...
    brel_effect_l ssl as "Hssl"...
    brel_effect_l srl as "Hsrl"...
    brel_alloc_r lamr as "Hlamr"...
    brel_alloc_r lstr as "Hlstr"...
    brel_effect_r lsr as "Hlsr"...
    brel_effect_r lrr as "Hlrr"...
    brel_alloc_r lmr as "Hlmr"...
    brel_effect_r ssr as "Hssr"...
    brel_effect_r srr as "Hsrr"...

    (* Setting up the client *)
    set (θ := client_row sl rl lsr lrr gkl ssl srl ssr srr).
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
    iApply (brel_add_label_l with "Hrl").
    iApply (brel_add_label_l with "Hsl").
    iApply (brel_add_label_r with "Hlsr").
    iApply (brel_add_label_r with "Hlrr").

    iApply brel_learn. iIntros "%Hdist' _".
    assert (NoDup [sl; rl; gkl; srl; ssl]) as Hnd_l.
    { unfold distinct in Hdist'. destruct Hdist' as [Hd' _].
      unfold distinct_l in Hd'. simpl in Hd'.
      repeat (rewrite -> labels_l_cons in Hd').
      by (eapply NoDup_app in Hd'; destruct Hd' as [Hd' _]). }

    assert (NoDup [lrr; lsr; srr; ssr]) as Hnd_r.
    { unfold distinct in Hdist'. destruct Hdist' as [_ Hd'].
      unfold distinct_r in Hd'. simpl in Hd'.
      rewrite !labels_r_cons in Hd'.
      by (eapply NoDup_app in Hd'; destruct Hd' as [Hd' _]). }

    (* The invariant.  Three states, as in the real/reduction proof:
         I0  nothing has happened;
         I1  a valid secure send has STARTED -- the plaintext is recorded on
             both sides, the real side has cached a key ([lcl]) and the
             simulator has flipped its [started] flag, but no ciphertext has
             been produced (the key leak may still fail, or be in flight);
         I2  the ciphertext has been drawn and leaked; it is the SAME on both
             sides, because the two [rand_cipher] draws are coupled by the
             identity.
       [lcl] and [lstr] move together: that is exactly the agreement that makes
       the receive branch work in state I0.  The key tape [γl] is never
       presampled and acts as the sender's exclusive token: it is absent from
       I1 (the sender holds it across the two key leaks), which is how the
       stale disjuncts are ruled out on re-entry. *)
    rewrite Nat2Z.id.
    iApply (brel_na_alloc ((lml ↦ NONEV ∗ lcl ↦ NONEV ∗ laml ↦ NONEV
                            ∗ lmr ↦ₛ NONEV ∗ lstr ↦ₛ NONEV ∗ lamr ↦ₛ NONEV
                            ∗ γl ↪N (n; []))
                           ∨ (∃ (mv : mt) (c : nat), lml ↦□ SOMEV (fvtval mv) ∗ lcl ↦□ SOMEV #c ∗ laml ↦ NONEV
                                           ∗ lmr ↦ₛ□ SOMEV (fvtval mv) ∗ lstr ↦ₛ□ SOMEV #()%V ∗ lamr ↦ₛ NONEV)
                           ∨ (∃ (mv : mt) (c : nat) (cph : ct), lml ↦□ SOMEV (fvtval mv) ∗ lcl ↦□ SOMEV #c ∗ laml ↦□ SOMEV (fvtval cph)
                                           ∗ lmr ↦ₛ□ SOMEV (fvtval mv) ∗ lstr ↦ₛ□ SOMEV #()%V ∗ lamr ↦ₛ□ SOMEV (fvtval cph)
                                           ∗ γl ↪□N (n; []))
              ) alphaN).
    iSplitL "Hlml Hlcl Hlaml Hlmr Hlstr Hlamr Hγl"; [iNext; iLeft; iFrame|].
    iIntros "#HI".

    (* Case on the client's behaviour, and induction *)
    rewrite !iLblSig_to_iLblThy_app !iThyIfMono_iLblSig_to_iThyIfMono.
    iDestruct (brel_introduction_mono _ (([sl; rl; gkl; srl; ssl], [lrr; lsr; srr; ssr], sec_channel ssl ssr srl srr : iThy Σ) :: to_iThyIfMono OS (iLblSig_to_iLblThy autheff) ++ to_iThyIfMono OS (iLblSig_to_iLblThy keyeff) ++ iLblSig_to_iLblThy θL) with "[][$Hff]") as "Hff".
    { iApply to_iThy_le_intro'. solve_submseteq. }
    iApply ((brel_exhaustion (f1 _) ( f2 _)) with "[$Hff]"); [set_solver|set_solver| ].

    iLöb as "IH".
    iSplit; [iIntros (v1 v2) "%Hv1v2 !>"; by brel_pures'|].
    iIntros (?????) "!# %Hk1 %Hk2 [(%m&(->&->)&HQ)|(->&->&HQ)] #Hrel".
    (* Alice tries to send a message m *)
    - brel_pures'; try (apply neutral_ectx); repeat constructor.
      destruct (fvt_of_int_sem (fin_val := msg) m) as [mv|] eqn:Hmv...
      2 : { iApply (brel_fvt_of_int_none_l (fin_val := msg)); first exact Hmv.
            iApply (brel_fvt_of_int_none_r (fin_val := msg)); first exact Hmv...
            iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V) with "[HQ]"); [set_solver|set_solver|by iApply "Hrel"|iApply "IH"]. }
      iApply (brel_fvt_of_int_correct_l (fin_val := msg)); first exact Hmv.
      iApply (brel_fvt_of_int_correct_r (fin_val := msg)); first exact Hmv...
      iApply (brel_na_inv _ _ alphaN); first set_solver.
      iFrame "HI".
      iIntros "(>[(Hlml&Hlcl&Hlaml&Hlmr&Hlstr&Hlamr&Hγl)|[H2|H3]]&Hclose)".
      + (* I0 : this is the first valid send *)
        brel_load_l...
        brel_load_r...
        brel_store_l...
        brel_store_r...
        brel_store_r...
        (* Left: enter [F_KE_lazy_alice]'s one-shot [getKey] handler and take
           the single key sample.  The sample is never used -- [enc_ideal]
           ignores its argument -- so it needs no counterpart on the ideal
           side: the tape is never presampled and [brel_randT_empty_l] resolves
           the draw universally. *)
        iApply (brel_handle_os_l [] [HandleCtx _ _ _ _ _;HandleCtx _ _ _ _ _;HandleCtx _ _ _ _ _;AppRCtx _]).
        { eapply NoDup_cons_1_1. simpl.
          eapply (submseteq_NoDup _ [sl; rl; gkl; srl; ssl]); [solve_submseteq|exact Hnd_l]. }
        iIntros (rgkl) "!> Hrgkl"...
        brel_load_l...
        iApply brel_randT_empty_l.
        iSplitL "Hγl"; first (iNext; iFrame).
        iIntros "!>" (c) "Hγl %Hc"...
        brel_store_l...

        (* Close in state I1, keeping the key tape as the sender's token. *)
        iMod (ghost_map_elem_persist with "Hlml") as "#Hlml".
        iMod (ghost_map_elem_persist with "Hlcl") as "#Hlcl".
        iMod (ghost_map_elem_persist with "Hlmr") as "#Hlmr".
        iMod (ghost_map_elem_persist with "Hlstr") as "#Hlstr".
        iApply brel_na_close. iFrame.
        iSplitL "Hlaml Hlamr".
        { iModIntro. iRight. iLeft. iExists _, _. iFrame "#". iFrame. }

        (* The two key leaks, send(bob) then recv(bob), in lockstep.  On the
           ideal side the call still sits inside the simulator's [lrecv]
           handler, so the right-hand context carries that [HandleCtx] and the
           residual theory [M] must be given explicitly (it has to mention
           [lrr]). *)
        iApply (brel_bind'' [AppRCtx _] [HandleCtx _ _ _ _ _; AppRCtx _]
                  (to_iThyIfMono OS (iLblSig_to_iLblThy keyeff)) [([sl; rl; gkl; srl; ssl], [lrr; lsr; srr; ssr], @iThyBot Σ)]).
        1,2 : set_unfold; tauto.
        { iApply to_iThy_le_intro'. solve_submseteq. }
        iApply brel_mono; [iApply to_iThy_le_refl| |simpl].
        { iApply "Hkeysnd". iExists _, _. by iLeft. }
        iIntros (v1 v2) "(->&->)"...
        iApply (brel_bind'' [AppRCtx _] [HandleCtx _ _ _ _ _; AppRCtx _]
                  (to_iThyIfMono OS (iLblSig_to_iLblThy keyeff)) [([sl; rl; gkl; srl; ssl], [lrr; lsr; srr; ssr], @iThyBot Σ)]).
        1,2 : set_unfold; tauto.
        { iApply to_iThy_le_intro'. solve_submseteq. }
        iApply brel_mono; [iApply to_iThy_le_refl| |simpl].
        { iApply "Hkeyrcv". iExists _, _. by iLeft. }
        iIntros (v1' v2') "(%&%&[(->&->&->&->)|(->&->&->&->)])"...
        (* Key establishment failed: neither side produces a ciphertext, and
           neither raises the authenticated-send leak. *)
        { brel_cont_l... iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V) with "[HQ]"); [set_solver|set_solver|by iApply "Hrel"|iApply "IH"]. }
        brel_cont_l...
        iApply (brel_na_inv _ _ alphaN); first set_solver.
        iFrame "HI".
        iIntros "(>[(_&_&_&_&_&_&Hγl')|[(%&%&_&_&Hlaml&_&_&Hlamr)|(%&%&%&_&_&_&_&_&_&Hγl')]]&Hclose)".
        (* We still hold the key tape, so the invariant cannot have moved. *)
        { iExFalso. iApply (tapeN_excl with "Hγl Hγl'"). }
        2 : { iExFalso. iApply (tapeN_excl with "Hγl Hγl'"). }
        brel_load_r...
        (* The one coupling of the whole proof: both sides draw a ciphertext
           and we make the two draws agree. *)
        iApply (rand_cipher_coupl (H := SKE)).
        iIntros (cph)...
        brel_load_l...
        brel_store_l...
        brel_store_r...
        iMod (ghost_map_elem_persist with "Hlaml") as "#Hlaml".
        iMod (ghost_map_elem_persist with "Hlamr") as "#Hlamr".
        iDestruct (tapeN_to_persistent with "Hγl") as ">#Hγl".
        iApply brel_na_close.
        iFrame. iSplitR; [iNext; do 2 iRight; iExists _,_,_; iFrame "#"|].
        (* Both sides leak the SAME ciphertext on the authenticated channel. *)
        iApply (brel_bind'' _ _ (to_iThyIfMono OS (iLblSig_to_iLblThy autheff)) [([sl; rl; gkl; srl; ssl], [lrr; lsr; srr; ssr], @iThyBot Σ)] _ _ (asnd_l _) (asnd_r _)).
        1,2 : set_unfold; tauto.
        { iApply to_iThy_le_intro'. solve_submseteq. }
        iApply brel_mono; [iApply to_iThy_le_refl| |simpl].
        { iApply "Hasnd". iExists _, _, _, _.
          repeat (iSplit; first done).
          iSplit; last (iExists _,_; by iLeft).
          by iExists _. }
        iIntros (v1'' v2'') "(->&->)"...
        iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V) with "[HQ]"); [set_solver|set_solver|by iApply "Hrel"|iApply "IH"].
      + (* I1 : a send is already in flight or has failed -- both sides just
             observe their recorded plaintext and return. *)
        iDestruct "H2" as "(%&%&#Hlml&#Hlcl&Hlaml&#Hlmr&#Hlstr&Hlamr)".
        brel_load_l...
        brel_load_r...
        iApply brel_na_close.
        iFrame.
        iSplitR "HQ"; [iRight; iLeft; iExists _,_; iFrame "#"; iFrame|].
        iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V) with "[HQ]"); [set_solver|set_solver|by iApply "Hrel"|iApply "IH"].
      + (* I2 : likewise, with the ciphertext already leaked. *)
        iDestruct "H3" as "(%&%&%&#Hlml&#Hlcl&#Hlaml&#Hlmr&#Hlstr&#Hlamr&#Hγl)".
        brel_load_l...
        brel_load_r...
        iApply brel_na_close.
        iFrame.
        iSplitR "HQ"; [iRight; iRight; iExists _,_,_; iFrame "#"|].
        iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V) with "[HQ]"); [set_solver|set_solver|by iApply "Hrel"|iApply "IH"].
    (* Bob tries to receive a message *)
    - brel_pures'.
      { split.
        + apply not_elem_of_cons; split; last (apply neutral_ectx; repeat constructor).
          intro Heq.
          apply NoDup_ListNoDup in Hnd_r.
          do 3 (apply NoDup_cons_iff in Hnd_r as [?Hn Hnd_r]).
          apply Hn1. by left.
        + simpl. rewrite !NoDup_cons in Hnd_l, Hnd_r; set_unfold; tauto. }
      { apply not_elem_of_cons; split; last (apply neutral_ectx; repeat constructor).
        intro Heq.
        apply NoDup_ListNoDup in Hnd_l.
        do 4 (apply NoDup_cons_iff in Hnd_l as [?Hn Hnd_l]).
        apply Hn2. by left. }
      repeat foldkont.
      iApply (brel_handle_os_l [] [HandleCtx _ _ _ _ _;HandleCtx _ _ _ _ _;AppRCtx _]).
      { eapply NoDup_cons_1_1. simpl.
        eapply (submseteq_NoDup _ [sl; rl; gkl; srl; ssl]); [solve_submseteq|exact Hnd_l]. }
      iIntros (rgkl) "!> Hrgkl"...
      (* key leaks, this time recv(alice) then send(alice) *)
      iApply (brel_bind'' [AppRCtx _] [AppRCtx _] (to_iThyIfMono OS (iLblSig_to_iLblThy keyeff))); try (apply list_subseteq_nil).
      { iApply to_iThy_le_intro'. solve_submseteq. }
      iApply brel_mono; [iApply to_iThy_le_refl| |simpl].
      { iApply "Hkeyrcv". iExists _, _. by iRight. }
      iIntros (v1' v2') "(%&%&[(->&->&->&->)|(->&->&->&->)])"...
      { brel_cont_l...
        iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"].
        iDestruct "HQ" as "[_ $]". }
      iApply (brel_bind'' [AppRCtx _] [AppRCtx _] (to_iThyIfMono OS (iLblSig_to_iLblThy keyeff))); try (apply list_subseteq_nil).
      { iApply to_iThy_le_intro'. solve_submseteq. }
      iApply brel_mono; [iApply to_iThy_le_refl| |simpl].
      { iApply "Hkeysnd". iExists _, _. by iRight. }
      iIntros (v1 v2) "(->&->)"...
      (* Both sides now consult their guard: [lcl] on the real side, [started]
         on the ideal side.  They agree, which is the whole point. *)
      iApply (brel_na_inv _ _ alphaN); first set_solver.
      iFrame "HI".
      iIntros "(>[(Hlml&Hlcl&Hlaml&Hlmr&Hlstr&Hlamr&Hγl)|[H2|H3]]&Hclose)".
      + (* I0 : no send has started, so NEITHER side touches the
           authenticated channel -- both answer NONE straight away. *)
        brel_load_l...
        brel_load_r...
        brel_cont_l...
        iApply brel_na_close.
        iFrame.
        iSplitR "HQ"; [iLeft; iFrame|].
        iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"].
        iDestruct "HQ" as "[_ $]".
      + (* I1 : a send has started but nothing was leaked. *)
        iDestruct "H2" as "(%&%&#Hlml&#Hlcl&Hlaml&#Hlmr&#Hlstr&Hlamr)".
        brel_load_l...
        brel_load_r...
        brel_cont_l...
        (* crossing F_OAUTH's receive handler leaves one label-freshness goal *)
        1 : { apply not_elem_of_cons; split;
                last (first [ solve [apply neutral_ectx; repeat constructor]
                            | solve [rewrite /frame_label /=; set_solver]
                            | solve [cbv [frame_label]; simpl; set_solver] ]).
              intro Heq. subst rl.
              apply NoDup_ListNoDup in Hnd_l.
              apply NoDup_cons_iff in Hnd_l as [Hn _].
              apply Hn. by left. }
        iApply brel_na_close.
        iFrame.
        iSplitR "HQ"; [iRight; iLeft; iExists _,_; iFrame "#"; iFrame|].
        iApply (brel_bind'' _ _ (to_iThyIfMono OS (iLblSig_to_iLblThy autheff)) [([sl; rl; gkl; srl; ssl], [lrr; lsr; srr; ssr], @iThyBot Σ)] _ _ (arcv_l _) (arcv_r _)).
        1,2 : set_unfold; tauto.
        { iApply to_iThy_le_intro'. solve_submseteq. }
        iApply brel_mono; [iApply to_iThy_le_refl| |simpl].
        { iApply "Harcv". iExists _,_; by iLeft. }
        iIntros (w1 w2) "(%&%&[(->&->&->&->)|(->&->&->&->)])"...
        { iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"].
          iDestruct "HQ" as "[_ $]". }
        iApply (brel_na_inv _ _ alphaN); first set_solver.
        iFrame "HI".
        iIntros "(>[(Hlml'&H')|[H2'|H3']]&Hclose)".
        (* [lml] already holds the message, so I0 is impossible. *)
        { iExFalso. by iDestruct (ghost_map_elem_ne with "Hlml' Hlml") as %?. }
        * iDestruct "H2'" as "(%&%&_&_&HlamlI&_&_&HlamrI)".
          brel_load_l...
          brel_load_r...
          iApply brel_na_close.
          iFrame.
          iSplitR "HQ"; [iRight; iLeft; iExists _,_; iFrame "#"; iFrame|].
          iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"].
          iDestruct "HQ" as "[_ $]".
        * iDestruct "H3'" as "(%&%&%&#Hlml2&#Hlcl2&#Hlaml2&#Hlmr2&#Hlstr2&#Hlamr2&#Hγl2)".
          brel_load_l...
          brel_load_r...
          brel_load_l...
          brel_load_r...
          iApply brel_na_close.
          iFrame.
          iSplitR "HQ"; [iRight; iRight; iExists _,_,_; iFrame "#"|].
          iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"].
          iDestruct "HQ" as "[HQ _]".
          iApply "HQ".
      + (* I2 : the ciphertext has been leaked. *)
        iDestruct "H3" as "(%&%&%&#Hlml&#Hlcl&#Hlaml&#Hlmr&#Hlstr&#Hlamr&#Hγl)".
        brel_load_l...
        brel_load_r...
        brel_cont_l...
        (* crossing F_OAUTH's receive handler leaves one label-freshness goal *)
        1 : { apply not_elem_of_cons; split;
                last (first [ solve [apply neutral_ectx; repeat constructor]
                            | solve [rewrite /frame_label /=; set_solver]
                            | solve [cbv [frame_label]; simpl; set_solver] ]).
              intro Heq. subst rl.
              apply NoDup_ListNoDup in Hnd_l.
              apply NoDup_cons_iff in Hnd_l as [Hn _].
              apply Hn. by left. }
        iApply brel_na_close.
        iFrame.
        iSplitR "HQ"; [iRight; iRight; iExists _,_,_; iFrame "#"|].
        iApply (brel_bind'' _ _ (to_iThyIfMono OS (iLblSig_to_iLblThy autheff)) [([sl; rl; gkl; srl; ssl], [lrr; lsr; srr; ssr], @iThyBot Σ)] _ _ (arcv_l _) (arcv_r _)).
        1,2 : set_unfold; tauto.
        { iApply to_iThy_le_intro'. solve_submseteq. }
        iApply brel_mono; [iApply to_iThy_le_refl| |simpl].
        { iApply "Harcv". iExists _,_; by iLeft. }
        iIntros (w1 w2) "(%&%&[(->&->&->&->)|(->&->&->&->)])"...
        { iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"].
          iDestruct "HQ" as "[_ $]". }
        iApply (brel_na_inv _ _ alphaN); first set_solver.
        iFrame "HI".
        iIntros "(>[(Hlml'&H')|[H2'|H3']]&Hclose)".
        (* [lml] already holds the message, so I0 is impossible. *)
        { iExFalso. by iDestruct (ghost_map_elem_ne with "Hlml' Hlml") as %?. }
        * iDestruct "H2'" as "(%&%&_&_&HlamlI&_&_&HlamrI)".
          brel_load_l...
          brel_load_r...
          iApply brel_na_close.
          iFrame.
          iSplitR "HQ"; [iRight; iLeft; iExists _,_; iFrame "#"; iFrame|].
          brel_load_l... 
          brel_load_r...
          iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"].
          iDestruct "HQ" as "[HQ _]".
          iApply "HQ".
        * iDestruct "H3'" as "(%&%&%&#Hlml2&#Hlcl2&#Hlaml2&#Hlmr2&#Hlstr2&#Hlamr2&#Hγl2)".
          brel_load_l...
          brel_load_r...
          brel_load_l...
          brel_load_r...
          iApply brel_na_close.
          iFrame.
          iSplitR "HQ"; [iRight; iRight; iExists _,_,_; iFrame "#"|].
          iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"].
          iDestruct "HQ" as "[HQ _]".
          iApply "HQ".
  Qed.

End schan_ideal.

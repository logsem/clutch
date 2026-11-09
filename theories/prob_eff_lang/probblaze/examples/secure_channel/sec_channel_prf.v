From iris.proofmode Require Import base proofmode classes.                                              
From iris.base_logic.lib Require Import  na_invariants.   
From iris.algebra Require Import agree excl auth frac excl_auth. 
From iris.algebra.lib Require Import dfrac_agree.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode
  spec_rules spec_ra
  class_instances.
From clutch.prob_eff_lang.probblaze Require Import tactics.
From clutch.prob_eff_lang.probblaze Require Import sem_types sem_row sem_sig sem_judgement sem_def compatibility.
From clutch.prob_eff_lang.probblaze.uc Require Import uc_systems.
From iris.bi Require Import monpred.
From iris.proofmode Require Import monpred.
From clutch.prob_eff_lang.probblaze.examples Require Import mask sec_channel_def mask_bijection.
From clutch.prob_eff_lang.probblaze.eq Require Import eq_logic eq_valgroup eq_handlers eq_compat.


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
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.
  Context {msk : @Mask (@vgG vg) vgval}.
  Context `{!Mask_struc}.
  #[local] Notation n := (S (S n'')).

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
                  □ Q (Val #()%V) (Val #()%V))%I.
  Next Obligation. solve_proper. Qed.
  (* Sent BY Bob TO Alice*)
  Definition LASendBob (la1 la2 : label) : iThy Σ := LASend la1 la2 alice.
  (* Sent BY Alice TO Bob*)
  Definition LASendAlice (la1 la2 : label) : iThy Σ := LASend la1 la2 bob.

  Program Definition LARecv (l1 l2 : label) from : iThy Σ :=
     λ e1 e2, (λne Q,
                ⌜ e1 = do: l1 (RecvV from) ⌝%E ∗
                ⌜ e2 = do: l2 (RecvV from) ⌝%E ∗
                □ ((∀ b1 b2 : nat, Q (SOMEV #b1) (SOMEV #b2)) ∧ Q NONEV NONEV)
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
                □ Q (Val #()%V) (Val #()%V))%I.
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
                □ (Q NONEV NONEV ∗ Q (SOMEV #0) (SOMEV #0)))%I.
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
                  □ (Q (Val #()%V) (Val #()%V))
             )%I.
  Next Obligation. solve_proper. Qed.

  (* [doSecRecv] is a thunk, so the INTERFACE argument type is 𝟙 -- but the
     effect PAYLOAD is the closed constant [bob].  Do not "simplify" it to #(). *)
  Program Definition RecvSecB (srecv1 srecv2 : label) : iThy Σ :=
    λ e1 e2, (λne Q,
                ⌜ e1 = do: srecv1 bob ⌝%E ∗
                ⌜ e2 = do: srecv2 bob ⌝%E ∗
                □ ((∀ g : vgG, Q (SOMEV (vgval g)) (SOMEV (vgval g))) ∧ Q NONEV NONEV)
             )%I.
  Next Obligation. solve_proper. Qed.

  Program Definition keyleak_mono (keyleak1 keyleak2 : label) := {| pmono_prot_car := iThySum (iThySum (KLeakSendAlice keyleak1 keyleak2) (KLeakRecvAlice keyleak1 keyleak2)) (iThySum (KLeakSendBob keyleak1 keyleak2) (KLeakRecvBob keyleak1 keyleak2)) ; pmono_prot_prop := _|}.
  Next Obligation.
    iIntros (????).
    iIntros (??) "#HΦ [[HS | HR] | [HS | HR]]".
    1: iLeft; iLeft. 2: iLeft; iRight. 3: iRight; iLeft. 4: iRight; iRight.
    1,3 : iDestruct "HS" as (??) "#H"; simpl; iSplit; first done; iSplit; first done; iModIntro; by iApply "HΦ".
    all: iDestruct "HR" as (??) "(#H1 & #H2)"; simpl; iSplit; first done; iSplit; first done; iModIntro; iSplitL " "; iApply "HΦ"; try (iApply "H1"); try (iApply "H2").
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
    1,2 : iDestruct "HS" as (??) "(#H1 & #H2 & #H3)"; simpl; iExists m1, m2; iSplit; first done; iSplit; first done;
                                                                         iModIntro; by iApply "HΦ".
    all : iDestruct "HR" as "(#H1 & #H2 & #H3)"; simpl; iSplit; first done; iSplit; first done; iModIntro;
      iDestruct "H3" as "[Hs Hn]"; iSplitL " "; try (iIntros (??)); iApply "HΦ"; try (iApply "Hs"); try (iApply "Hn").
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
    { iDestruct "HS" as "(He1e2 & Hs1s2)". iApply "He1e2". }
    { iDestruct "HS" as "(He1e2 & #Hs1s2)". iModIntro.
      iIntros (??) "HS". iApply "HΦΦ'". iApply "Hs1s2". iApply "HS".
    }
  Qed.

  Definition leakauth_row (leakauth1 leakauth2 : label) := SemRow [([leakauth1],[leakauth2] , leakauth leakauth1 leakauth2 )] (leakauth_pers_mono_row leakauth1 leakauth2).
  Program Definition envsec_row (keyleak1 keyleak2 leakauth1 leakauth2 : label) :=
    sem_row_union (keyleak_row keyleak1 keyleak2) (leakauth_row leakauth1 leakauth2).

  Program Definition sec_channel_mono (ssend1 ssend2 srecv1 srecv2 : label) := {| pmono_prot_car := iThySum (SendSec ssend1 ssend2) (RecvSecB srecv1 srecv2) ; pmono_prot_prop := _ |}.
  Next Obligation.
    iIntros (????). unfold pers_mono. iIntros (????) "#Hw1w2 [HS | HR]".
    { iLeft. simpl.  iDestruct "HS" as (?m) "(Hv1v2 & #HS)". iExists m.
      iSplitL "Hv1v2"; [iFrame |iModIntro; iApply "Hw1w2"; iApply "HS"]. }
    { iRight. simpl.   iDestruct "HR" as "(%Hv1 &(%Hv2 & #HR))". repeat iSplit; try iPureIntro; try apply Hv1; try apply Hv2.
      iModIntro. iDestruct "HR" as "(HR1 & HR2)".
      iSplit; [iIntros (?); iApply "Hw1w2"; iApply "HR1" | iApply "Hw1w2"; iApply "HR2"].
    }
  Qed.

  (* [SemSig] carries only ONE label pair; it is dropped by [iLblSig_to_iLblThy]
     and every row below is built by hand, so the [send] pair is a safe choice. *)
  Definition sec_channel (ssend1 ssend2 srecv1 srecv2 : label) := @SemSig Σ (sec_channel_mono ssend1 ssend2 srecv1 srecv2) (ssend1, ssend2).

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
    { iDestruct "HS" as "(He1e2 & Hs1s2)". iApply "He1e2". }
    { iDestruct "HS" as "(He1e2 & #Hs1s2)". iModIntro.
      iIntros (??) "HS". iApply "HΦΦ'". iApply "Hs1s2". iApply "HS".
    }
  Qed.

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
    { iDestruct "HS" as "(He1e2 & Hs1s2)". iApply "He1e2". }
    { iDestruct "HS" as "(He1e2 & #Hs1s2)". iModIntro.
      iIntros (??) "HS". iApply "HΦΦ'". iApply "Hs1s2". iApply "HS".
    }
  Qed.

  Lemma sec_channel_pers_mono_row (ssend1 srecv1 ssend2 srecv2 : label) : ⊢ pers_mono_row (iLblSig_to_iLblThy [([srecv1; ssend1] , [srecv2; ssend2], sec_channel ssend1 ssend2 srecv1 srecv2)]).
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

  Program Definition sec_channel_row (ssend1 srecv1 ssend2 srecv2 : label) := SemRow [([srecv1; ssend1], [srecv2; ssend2], sec_channel ssend1 ssend2 srecv1 srecv2)] (sec_channel_pers_mono_row ssend1 srecv1 ssend2 srecv2).
  Program Definition client_row (csend crecv lsend lrecv getKey1 ssend1 srecv1 ssend2 srecv2 : label) := SemRow [([csend; crecv; getKey1; srecv1; ssend1], [lrecv; lsend; srecv2; ssend2], sec_channel ssend1 ssend2 srecv1 srecv2)] (client_pers_mono_row csend crecv lsend lrecv getKey1 ssend1 srecv1 ssend2 srecv2).

  Program Definition client_row' (csend crecv lsend lrecv getKey1 ssend1 srecv1 ssend2 srecv2 : label) := SemRow [([lrecv; lsend; srecv1; ssend1], [csend; crecv; getKey1; srecv2; ssend2], sec_channel ssend1 ssend2 srecv1 srecv2)] (client_pers_mono_row' csend crecv lsend lrecv getKey1 ssend1 srecv1 ssend2 srecv2).

  (* we have assumed that the secure channel only provides a fixed direction message passing from Alice to Bob, so this needs to reflect in the types of the thunks given to the secure channel client to raise the secure channel effect*)
  (* The client's two thunks are typed against ANY single-entry row whose theory
     is [sec_channel schannel_l schannel_r]; the proof never looks at the label
     lists (membership is [elem_of_list_here], and the raise ectx is []).  Stating
     it this way lets both [client_row] (SEM_R_CHAN_SIM) and [client_row']
     (SEM_R_CHAN_SIM_rev) use it, instead of the latter inlining a copy. *)
  Lemma SEM_TYPED_EFF (l1s l2s : list label) (ssend_l ssend_r srecv_l srecv_r : label)
        (Hpm : ⊢ pers_mono_row
                   (iLblSig_to_iLblThy [(l1s, l2s, sec_channel ssend_l ssend_r srecv_l srecv_r)])) :
      let θ := SemRow [(l1s, l2s, sec_channel ssend_l ssend_r srecv_l srecv_r)] Hpm in
      ⊢
        (sem_val_typed  ((λ: "m", do: ssend_l "m"), (λ: <>, do: srecv_l bob))%V ((λ: "m", do: ssend_r "m") , (λ: <>, do: srecv_r bob))%V (((sem_ty_nat)%T -{ θ }-> 𝟙) × (𝟙 -{ θ }-> (Option 𝔾)))%T)%I.
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
      iModIntro. iApply brel_value. iIntros "$ !>".
      unfold sem_ty_unit; iPureIntro.
      split; reflexivity.
    + iModIntro. iIntros (??) "Hw1w1". unfold sem_ty_unit.
      iDestruct "Hw1w1" as "[%Hw1 %Hw2]". unfold bob. rewrite -> Hw1. rewrite -> Hw2.
      brel_pures'.
      iApply brel_introduction'; try constructor.
      iExists _,_,[],[],_; do 2 (iSplit; [by iPureIntro|]; iSplit; [iPureIntro; apply NeutralEctx_nil|]);
                        iSplit; try (iIntros (??) "!# H"; iApply "H").     simpl. iRight.
      repeat iSplit; try iPureIntro; try auto; unfold RecvV; unfold bob; try rewrite -> Hw1;
        try rewrite -> Hw2; try simpl; try reflexivity.
      iModIntro. iSplit.
      { iIntros (?). iApply brel_value. iIntros "$ !>".
        iExists _,_; iRight; iPureIntro; repeat (split; first done). exists g. split; reflexivity. }
      { iApply brel_value. iIntros "$ !>".
        iExists _,_; iLeft; iPureIntro; repeat (split; first done); reflexivity. }
  Qed.


  (* The interface of the secure channel: the client may be called any number
     of times, and all calls share one session. *)
  Definition τ_CHAN : sem_ty Σ :=
    (∀ᵣ θ__L ,(∀ᵣ θₕ, (((sem_ty_nat -{ θₕ }-> 𝟙) × (𝟙 -{ θₕ }-> (Option  𝔾))) -{ sem_row_union  θₕ θ__L }-∘ 𝟙)) → (*type of client*)
              (∀ᵣ θ₁, ∀ᵣ θ₂,  ((((𝔾 × (𝟙 + 𝟙)) -{ θ₁ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ₁ }-> Option 𝟙)) × (((𝟙 + 𝟙) -{ θ₂ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ₂ }-> Option 𝟙))) -{ sem_row_union (¡ θ₁)%R (sem_row_union (¡θ₂)%R θ__L) }-∘ 𝟙))%T.

  (* One-shot variant of [τ_CHAN], the shape the composition operators expect *)
  Definition τ_CHAN_OS : sem_ty Σ :=
    (∀ᵣ θ__L ,(∀ᵣ θₕ, (((sem_ty_nat -{ θₕ }-> 𝟙) × (𝟙 -{ θₕ }-> (Option  𝔾))) -{ sem_row_union  θₕ θ__L }-∘ 𝟙)) ⊸ (*type of client*)
              (∀ᵣ θ₁, ∀ᵣ θ₂,  ((((𝔾 × (𝟙 + 𝟙)) -{ θ₁ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ₁ }-> Option 𝟙)) × (((𝟙 + 𝟙) -{ θ₂ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ₂ }-> Option 𝟙))) -{ sem_row_union (¡ θ₁)%R (sem_row_union (¡θ₂)%R θ__L) }-∘ 𝟙))%T.

  Lemma τ_CHAN_le_τ_CHAN_OS : ⊢ τ_CHAN ≤ₜ τ_CHAN_OS.
  Proof. iApply ty_le_row_forall. iIntros (θ). iApply ty_le_mbang_elim. Qed.

  (* ---------------------------------------------------------------- *)
  (* The two relations, on the factories: calling the composites        *)
  (* allocates the functionalities' state (in evaluation order), then   *)
  (* one client call is related step by step.                           *)
  (* ---------------------------------------------------------------- *)

  (* The theory of the client's secure channel, with the labels of [l]
     ([sl], [rl]) and of [r] ([sr], [rr]); it is symmetric, so in direction
     [Bwd] it is the same theory with the labels swapped. *)
  Definition schan_thy (sl sr rl rr : label) : dir → iThy Σ :=
    λ d, iThySum (SendSec (pick d sl sr) (pick d sr sl)) (RecvSecB (pick d rl rr) (pick d rr rl)).

  Lemma schan_thy_app sl sr rl rr el er Q :
    eq_thy_app (schan_thy sl sr rl rr) el er Q ⊢
      (∃ m : nat, ⌜el = (do: sl #m)%E ∧ er = (do: sr #m)%E⌝ ∗ ⎡□ Q #()%V #()%V⎤) ∨
      (⌜el = (do: rl bob)%E ∧ er = (do: rr bob)%E⌝ ∗
       □ ((∀ g : vgG, ⎡Q (SOMEV (vgval g)) (SOMEV (vgval g))⎤) ∧ ⎡Q NONEV NONEV⎤)).
  Proof.
    split=> d. destruct d; rewrite /eq_thy_app /schan_thy /pick /=;
      iIntros "[(%m & [-> ->] & #HQ)|(-> & -> & #HQ)]"; rewrite monPred_at_or.
    all: try (iLeft; rewrite monPred_at_exist; iExists m;
              rewrite monPred_at_sep monPred_at_pure monPred_at_embed; iFrame "HQ"; by iPureIntro).
    all: iRight; rewrite monPred_at_sep monPred_at_pure monPred_at_intuitionistically monPred_at_and monPred_at_forall;
      iSplit; first by iPureIntro.
    all: iDestruct "HQ" as "[HQs HQn]"; iModIntro;
      iSplit; [iIntros (g); rewrite monPred_at_embed; iApply "HQs"|rewrite monPred_at_embed; iApply "HQn"].
  Qed.

  (* The real channel [REAL_SCHAN] is [l], the simulated functionality [r].
     The first message fixes the key: [r]'s simulator samples [c], [l]'s
     key generation reads [sc_coupling_nat m c] from its tape. *)
  Lemma SCHAN_EQ :
    ⊢ EQ REAL_SCHAN ≈ (SIM_SCHAN ∘f IDEAL_SCHAN)%fac <|iLblSig_to_iLblThy (⊥ : sem_row Σ)|>
        {{ ⟪ fac MS τ_CHAN ⟫ }}.
  Proof with (repeat foldkont; eq_pures') using All.
    iApply eq_value. iModIntro. rewrite /fac. iModIntro.
    iApply eq_lift_arr. iIntros (u1 u2) "Hu". rewrite eq_lift_unit. iDestruct "Hu" as %[-> ->].
    unfold τ_CHAN, REAL_SCHAN, SIM_SCHAN, IDEAL_SCHAN, parallel_composition, func_comp...
    (* Setup: the functionalities' state, in evaluation order *)
    eq_alloc_l l_rchan as "Hlrchan"...
    eq_alloc_l l_auth as "Hl_auth"...
    eq_alloctape_l γ as "Hγ"...
    rewrite Nat2Z.id.
    eq_alloc_l l_key as "Hl_key"...
    eq_alloc_r l_fchan as "Hlfchan"...
    eq_alloc_r l_sim as "Hl_sim"...
    eq_alloc_r l_m'sim as "Hl_m'sim".
    set (d1 := (γ ↪ₗN (S n''; []) ∗ l_m'sim ↦ᵣ NONEV ∗ l_sim ↦ᵣ NONEV ∗ l_auth ↦ₗ NONEV ∗
                l_fchan ↦ᵣ NONEV ∗ l_rchan ↦ₗ NONEV ∗ l_key ↦ₗ NONEV)%I : iPropD Σ).
    set (d2 := (∃ (m : vgG) (c : nat), ⌜(c < n)%nat⌝ ∗ γ ↪ₗN (S n''; []) ∗
                  l_m'sim ↦ᵣ□ SOMEV #c ∗ l_sim ↦ᵣ□ SOMEV #c ∗ l_auth ↦ₗ□ SOMEV (vgval (g ^+ c)%g) ∗
                  l_fchan ↦ᵣ□ SOMEV (vgval m) ∗ l_rchan ↦ₗ□ SOMEV (vgval m) ∗
                  l_key ↦ₗ□ SOMEV #(sc_coupling_nat m c))%I : iPropD Σ).
    set (d3 := (∃ (m : vgG) (c : nat), ⌜(c < n)%nat⌝ ∗ γ ↪ₗN (S n''; []) ∗
                  l_m'sim ↦ᵣ□ SOMEV #c ∗ l_sim ↦ᵣ NONEV ∗ l_auth ↦ₗ NONEV ∗
                  l_fchan ↦ᵣ□ SOMEV (vgval m) ∗ l_rchan ↦ₗ□ SOMEV (vgval m) ∗
                  l_key ↦ₗ□ SOMEV #(sc_coupling_nat m c))%I : iPropD Σ).
    iApply (eq_na_alloc (d1 ∨ (d2 ∨ d3)) alphaN).
    iSplitL "Hγ Hl_m'sim Hl_sim Hl_auth Hlfchan Hlrchan Hl_key"; [iNext; iLeft; iFrame|].
    iIntros "#Hinvα"...
    (* One call: a client and its effect handlers *)
    iApply eq_value. iModIntro. iEval (rewrite eq_lift_forall). iIntros (L). iModIntro.
    iApply eq_lift_arr. iIntros (f1 f2) "Hrelf1f2"...
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
    eq_effect_l getKey' as "HgK"...
    eq_effect_r lsend' as "Hlsend"...
    eq_effect_r lrecv' as "Hlrecv"...
    eq_effect_l csend' as "Hcsend"...
    eq_effect_l crecv' as "Hcrecv"...
    eq_effect_r ssend_r as "Hssend_r"...
    eq_effect_r srecv_r as "Hsrecv_r"...
    eq_effect_l ssend_l as "Hssend_l"...
    eq_effect_l srecv_l as "Hsrecv_l"...
    set (lls := [csend'; crecv'; getKey'; srecv_l; ssend_l]).
    set (rls := [lrecv'; lsend'; srecv_r; ssend_r]).
    (* The client's row: the secure channel, with the labels of the program
       on the left. *)
    set (θc := λ d, pick d (client_row csend' crecv' lsend' lrecv' getKey' ssend_l srecv_l ssend_r srecv_r)
                           (client_row' csend' crecv' lsend' lrecv' getKey' ssend_r srecv_r ssend_l srecv_l)).
    iApply eq_new_theory.
    iApply eq_add_label_l. iFrame "Hssend_l".
    iApply eq_add_label_l. iFrame "Hsrecv_l".
    iApply eq_add_label_l. iFrame "HgK".
    iApply eq_add_label_l. iFrame "Hcrecv".
    iApply eq_add_label_l. iFrame "Hcsend".
    iApply eq_add_label_r. iFrame "Hssend_r".
    iApply eq_add_label_r. iFrame "Hsrecv_r".
    iApply eq_add_label_r. iFrame "Hlsend".
    iApply eq_add_label_r. iFrame "Hlrecv".
    iApply eq_learn_nodup. iIntros ([Hnd_l Hnd_r]).
    eq_reshape_l (f1 _). eq_reshape_r (f2 _).
    iApply (eq_exhaustion _ _ _ _ (schan_thy ssend_l ssend_r srecv_l srecv_r) with "[Hrelf1f2]");
      [set_unfold; tauto | set_unfold; tauto | |].
    { iApply (eq_thy_mono _ _ (EqThy (λ d, iLblSig_to_iLblThy (sem_row_union (θc d) L)))).
      { intros []; rewrite /θc /schan_thy /pick /=; iApply to_iThy_le_intro'; simpl;
          apply submseteq_skip; unfold sem_row_union;
          repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app);
          solve_submseteq. }
      iApply (eq_lift_forall_app _ _ _ θc with "Hrelf1f2").
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
    iDestruct (schan_thy_app with "HXQ") as "[(%mz & %Hmz' & #HmQ) | (%Hrecv & #HmQ)]".
    (* Send a message using the secure channel from Alice to Bob *)
    - destruct Hmz' as [-> ->]...
      eq_handle_os ssendl ssendr as "Hssendl" "Hssendr".
      simpl. eq_pures_l. eq_pures_r.
      (* Interpreting a group element from mz *)
      destruct (vg_of_int_sem mz) as [m|] eqn:Hmz.
      2: {
        eq_vg_of_int_none_l. eq_vg_of_int_none_r.
        eq_pures_l. eq_pures_r.
        eq_cont_l. eq_cont_r.
        eq_exhaustion (fill k1' #()%V) (fill k2' #()%V);
          [set_unfold; tauto|set_unfold; tauto|by iApply "Hrel"|iApply "IH"]. }
      eq_vg_of_int_l. eq_vg_of_int_r...
      iApply (eq_na_open _ _ alphaN); first (set_unfold; tauto).
      iFrame "Hinvα".
      iIntros "[[(>Hγ & >Hl_m'sim & >Hl_sim & >Hl_auth & >Hl_fchan & >Hl_rchan & >Hl_key) | [>Hd2 | >Hd3]] Hclose]".
      (* First message to be sent by the secure channel *)
      + eq_load_r... eq_load_l... eq_store_r...
        eq_handle_os_r_in [HandleCtx _ _ _ _ _; AppRCtx _].
        { rewrite !NoDup_cons in Hnd_l, Hnd_r. set_unfold; tauto. }
        iIntros (r) "Hlsendr".
        eq_store_l... eq_load_r...
        eq_handle_os_l_in [HandleCtx _ _ _ _ _; HandleCtx _ _ _ _ _; HandleCtx _ _ _ _ _; AppRCtx _].
        { eapply NoDup_cons_1_1.
          eapply (submseteq_NoDup _ [csend'; crecv'; getKey'; srecv_l; ssend_l]); [solve_submseteq | exact Hnd_l]. }
        iIntros (gkl) "Hgkl"...
        eq_load_l...
        eq_reshape_r (rand #_)%E.
        iApply (eq_couple_tape_rand_bij _ _ (sc_coupling_nat m)); [apply sc_coupling_nat_bound|done|].
        iFrame "Hγ". iIntros (c Hc) "Hγ". simpl...
        eq_rand_l as "%Hc'"...
        eq_store_l... eq_store_r...
        iMod (eq_pt_r_persist with "Hl_fchan") as "#Hl_fchan".
        iMod (eq_pt_l_persist with "Hl_rchan") as "#Hl_rchan".
        iMod (eq_pt_l_persist with "Hl_key") as "#Hl_key".
        iMod (eq_pt_r_persist with "Hl_m'sim") as "#Hl_m'sim".
        iApply eq_na_close_rule. iFrame "Hclose".
        iSplitR "Hgkl Hlsendr Hssendl Hssendr".
        { iNext. iRight. iRight. iExists m, c. iFrame "∗#". iPureIntro. lia. }
        eq_reshape_l (kysnd_l _). eq_reshape_r (kysnd_r _).
        iApply (eq_env_call_gen lls rls (λ _, iThyBot) _ _ with "Hkeysnd [] [-]");
          [set_unfold; tauto | set_unfold; tauto | | |].
        { intros []; rewrite /lls /rls /pick /=; iApply to_iThy_le_intro'; unfold sem_row_union;
            repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app); solve_submseteq. }
        { iApply eq_lift_same. iExists #()%V, #()%V. iLeft. repeat iSplit; try iPureIntro; try reflexivity. }
        iIntros (v1 v2) "Hv". rewrite eq_lift_unit. iDestruct "Hv" as %[-> ->]...
        eq_reshape_l (kyrcv_l _). eq_reshape_r (kyrcv_r _).
        iApply (eq_env_call_gen lls rls (λ _, iThyBot) _ _ with "Hkeyrcv [] [-]");
          [set_unfold; tauto | set_unfold; tauto | | |].
        { intros []; rewrite /lls /rls /pick /=; iApply to_iThy_le_intro'; unfold sem_row_union;
            repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app); solve_submseteq. }
        { iApply eq_lift_same. iExists #()%V, #()%V.
          repeat iSplit; try iPureIntro; try reflexivity; try left; repeat split; try reflexivity. }
        iIntros (v0 v3) "Hv". iEval (rewrite eq_lift_sum) in "Hv".
        iDestruct "Hv" as (w1 w2) "[(-> & -> & Hu)|(-> & -> & Hu)]";
          iEval (rewrite eq_lift_unit) in "Hu"; iDestruct "Hu" as %[-> ->]...
        (* keyleak recv returns successfully or not *)
        * eq_cont_l. eq_pures'. eq_cont_r. eq_pures'.
          eq_cont_l. eq_cont_r.
          eq_exhaustion (fill k1' #()%V) (fill k2' #()%V);
            [set_solver|set_solver|iApply "Hrel"; iApply "HmQ"|iApply "IH"].
        * eq_cont_l...
          eq_lift_l mask_correct_l mask_correct_r.
          eq_pures'.
          eq_handle_os_l_in [HandleCtx _ _ _ _ _; AppRCtx _].
          { eapply NoDup_cons_1_1.
            eapply (submseteq_NoDup _ [csend'; crecv'; getKey'; srecv_l; ssend_l]); [solve_submseteq | exact Hnd_l]. }
          iIntros (r0) "Hcsendl".
          iApply (eq_na_open _ _ alphaN); first (set_unfold; tauto).
          iFrame "Hinvα".
          iIntros "[[(>Hγ & >Hl_m'sim' & >Hl_sim' & >Hl_auth & >Hl_fchan' & >Hl_rchan' & Hl_key') | [>Hd2 | >Hd3]] Hclose]".
          (* the first message has been sent and stored *)
          { by iDestruct (eq_pt_r_agree with "Hl_fchan Hl_fchan'") as %Heq. }
          -- iDestruct "Hd2" as (?m ?c) "(%Hlt & Hγ & #Hl_m'sim' & #Hl_sim & #Hl_auth & #Hl_fchan' & #Hl_rchan' & #Hl_key')".
             eq_pures'.
             eq_load_l... eq_load_r...
             iApply eq_na_close_rule. iFrame "Hclose".
             iSplitR "Hlsendr Hssendr Hssendl Hcsendl"...
             { iNext. iRight. iLeft. iExists _, _. by iFrame "∗#%". }
             eq_cont_l. eq_cont_r. eq_pures'.
             eq_cont_l. eq_cont_r.
             eq_exhaustion (fill k1' #()%V) (fill k2' #()%V);
               [set_unfold; tauto|set_unfold; tauto|iApply "Hrel"; iApply "HmQ"|iApply "IH"].
          -- iDestruct "Hd3" as (?m ?c) "(%Hlt & Hγ & #Hl_m'sim' & Hl_sim & Hl_auth & #Hl_fchan' & #Hl_rchan' & #Hl_key')".
             iDestruct (eq_pt_r_agree with "Hl_m'sim Hl_m'sim'") as %Hc0.
             assert (c0 = c) as -> by (inversion Hc0; lia).
             eq_pures'.
             eq_load_l... eq_load_r...
             eq_store_r... eq_store_l...
             iMod (eq_pt_r_persist with "Hl_sim") as "#Hl_sim".
             iMod (eq_pt_l_persist with "Hl_auth") as "#Hl_auth".
             iApply eq_na_close_rule. iFrame "Hclose".
             iSplitR "Hlsendr Hssendr Hssendl Hcsendl".
             { iNext. iRight. iLeft. rewrite -sc_coupling_nat_mask; last lia.
               iExists m0, c. iFrame "∗#". iPureIntro. lia. }
             rewrite -sc_coupling_nat_mask; last lia.
             eq_reshape_l (asnd_l _). eq_reshape_r (asnd_r _).
             iApply (eq_env_call_gen lls rls (λ _, iThyBot) _ _ with "Hasnd [] [-]");
               [set_unfold; tauto | set_unfold; tauto | | |].
             { intros []; rewrite /lls /rls /pick /=; iApply to_iThy_le_intro'; unfold sem_row_union;
                 repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app); solve_submseteq. }
             { iApply eq_lift_same. iExists _, _, _, _.
               do 2 (iSplit; first (by iPureIntro)).
               iSplit; first by iExists _.
               iExists _, _; iLeft; done. }
             iIntros (v0 v3) "Hv". rewrite eq_lift_unit. iDestruct "Hv" as %[-> ->].
             eq_pures'.
             eq_cont_l. eq_cont_r. eq_pures'.
             eq_cont_l. eq_cont_r.
             eq_exhaustion (fill k1' #()%V) (fill k2' #()%V);
               [set_unfold; tauto|set_unfold; tauto|iApply "Hrel"; iApply "HmQ"|iApply "IH"].
      (* A message has already been sent by the secure channel *)
      + iDestruct "Hd2" as (?m ?c) "(%Hlt & Hγ & #Hl_m'sim & #Hl_sim & #Hl_auth & #Hl_fchan & #Hl_rchan & #Hl_key)".
        eq_load_l... eq_load_r...
        iApply eq_na_close_rule. iFrame "Hclose".
        iSplitR "Hssendl Hssendr".
        { iNext. iRight. iLeft. iExists _, _. by iFrame "∗#%". }
        eq_cont_l. eq_cont_r.
        eq_exhaustion (fill k1' #()%V) (fill k2' #()%V);
          [set_solver|set_solver|iApply "Hrel"; iApply "HmQ"|iApply "IH"].
      + iDestruct "Hd3" as (?m ?c) "(%Hlt & Hγ & #Hl_m'sim & Hl_sim & Hl_auth & #Hl_fchan & #Hl_rchan & #Hl_key)".
        eq_load_l... eq_load_r...
        iApply eq_na_close_rule. iFrame "Hclose".
        iSplitR "Hssendr Hssendl".
        { iNext. do 2 iRight. iExists _, _. by iFrame "∗#%". }
        eq_cont_l. eq_cont_r.
        eq_exhaustion (fill k1' #()%V) (fill k2' #()%V);
          [set_solver|set_solver|iApply "Hrel"; iApply "HmQ"|iApply "IH"].
    (* Receive *)
    - destruct Hrecv as [-> ->]...
      eq_handle_os_in (HandleCtx _ _ _ _ _ :: k1') (HandleCtx _ _ _ _ _ :: k2').
      { simpl. apply not_elem_of_cons; split; last (apply neutral_ectx; repeat constructor).
        apply NoDup_ListNoDup in Hnd_l.
        do 4 (apply NoDup_cons_iff in Hnd_l as [?Hn Hnd_l]).
        intro Heq. apply Hn2. by left. }
      { apply not_elem_of_cons; split; last (apply neutral_ectx; repeat constructor).
        intro Heq.
        apply NoDup_ListNoDup in Hnd_r.
        do 4 (apply NoDup_cons_iff in Hnd_r as [?Hn Hnd_r]).
        apply Hn1. by left. }
      iIntros "!>" (r r0) "Hsrecvl Hsrecvr".
      eq_pures_l. eq_pures_r.
      eq_handle_os_l_in [HandleCtx _ _ _ _ _; HandleCtx _ _ _ _ _; AppRCtx _].
      { eapply NoDup_cons_1_1.
        eapply (submseteq_NoDup _ [csend'; crecv'; getKey'; srecv_l; ssend_l]); [solve_submseteq | exact Hnd_l]. }
      iIntros (gkl) "Hgkl"...
      eq_handle_os_r_in [HandleCtx _ _ _ _ _; AppRCtx _].
      { simpl.
        apply NoDup_ListNoDup in Hnd_r.
        do 3 (apply NoDup_cons_iff in Hnd_r as [?Hn Hnd_r]).
        apply not_elem_of_cons; split; [| apply not_elem_of_nil].
        intro Heq. apply Hn. by left. }
      iIntros (r1) "Hlrecvr"...
      eq_reshape_l (kyrcv_l _). eq_reshape_r (kyrcv_r _).
      iApply (eq_env_call_gen lls rls (λ _, iThyBot) _ _ with "Hkeyrcv [] [-]");
        [set_unfold; tauto | set_unfold; tauto | | |].
      { intros []; rewrite /lls /rls /pick /=; iApply to_iThy_le_intro'; unfold sem_row_union;
          repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app); solve_submseteq. }
      { iApply eq_lift_same. iExists #()%V, #()%V.
        repeat iSplit; try iPureIntro; try reflexivity. right. repeat split; try reflexivity. }
      iIntros (v1 v2) "Hv". iEval (rewrite eq_lift_sum) in "Hv".
      iDestruct "Hv" as (w1 w2) "[(-> & -> & Hu)|(-> & -> & Hu)]";
        iEval (rewrite eq_lift_unit) in "Hu"; iDestruct "Hu" as %[-> ->]...
      (* key receive did not return successfully *)
      + eq_cont_l... eq_cont_l. eq_cont_r... eq_cont_r.
        eq_exhaustion (fill k1' _) (fill k2' _);
          [set_solver|set_solver|iApply "Hrel"; iDestruct "HmQ" as "(_&$)"|iApply "IH"].
      (* key receive returned successfully *)
      + eq_reshape_l (kysnd_l _). eq_reshape_r (kysnd_r _).
        iApply (eq_env_call_gen lls rls (λ _, iThyBot) _ _ with "Hkeysnd [] [-]");
          [set_unfold; tauto | set_unfold; tauto | | |].
        { intros []; rewrite /lls /rls /pick /=; iApply to_iThy_le_intro'; unfold sem_row_union;
            repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app); solve_submseteq. }
        { iApply eq_lift_same. iExists #()%V, #()%V. iRight. repeat iSplit; try iPureIntro; try reflexivity. }
        iIntros (v0 v3) "Hv". rewrite eq_lift_unit. iDestruct "Hv" as %[-> ->]...
        iApply (eq_na_open _ _ alphaN); first (set_unfold; tauto).
        iFrame "Hinvα".
        iIntros "[[(>Hγ & >Hl_m'sim & >Hl_sim & >Hl_auth & >Hl_fchan & >Hl_rchan & >Hl_key) | [>Hd2 | >Hd3]] Hclose]".
        (* no message has been sent yet by the secure channel *)
        * eq_load_l... eq_load_r...
          iApply eq_na_close_rule. iFrame "Hclose".
          iSplitR "Hgkl Hsrecvl Hsrecvr Hlrecvr".
          { iNext. iLeft. iFrame. }
          eq_cont_l. eq_cont_r. eq_pures'.
          eq_cont_l. eq_cont_r.
          eq_exhaustion (fill k1' _) (fill k2' _);
            [set_solver|set_solver|iApply "Hrel"; iDestruct "HmQ" as "(_&$)"|iApply "IH"].
        (* a message has been sent by both the secure channel and the authenticated channel *)
        * iDestruct "Hd2" as (?m ?c) "(%Hlt & Hγ & #Hl_m'sim & #Hl_sim & #Hl_auth & #Hl_fchan & #Hl_rchan & #Hl_key)".
          eq_load_l... eq_load_r...
          iApply eq_na_close_rule. iFrame "Hclose".
          iSplitR "Hgkl Hsrecvl Hsrecvr Hlrecvr".
          { iNext. iRight. iLeft. iExists _, _. by iFrame "∗#%". }
          eq_cont_l...
          eq_handle_os_l_in [HandleCtx _ _ _ _ _; AppRCtx _].
          { eapply NoDup_cons_1_1.
            eapply (submseteq_NoDup _ [csend'; crecv'; getKey'; srecv_l; ssend_l]); [solve_submseteq | exact Hnd_l]. }
          iIntros (r2) "Hcrecvl"...
          eq_reshape_l (arcv_l _). eq_reshape_r (arcv_r _).
          iApply (eq_env_call_gen lls rls (λ _, iThyBot) _ _ with "Harcv [] [-]");
            [set_unfold; tauto | set_unfold; tauto | | |].
          { intros []; rewrite /lls /rls /pick /=; iApply to_iThy_le_intro'; unfold sem_row_union;
              repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app); solve_submseteq. }
          { iApply eq_lift_same. iExists #()%V, #()%V. iLeft. repeat iSplit; try iPureIntro; try reflexivity. }
          iIntros (v4 v5) "Hv". iEval (rewrite eq_lift_sum) in "Hv".
          iDestruct "Hv" as (w0 w3) "[(-> & -> & Hu)|(-> & -> & Hu)]".
          (* leakauth does not return successfully *)
          -- iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->]...
             eq_cont_l. eq_cont_r. eq_pures'.
             eq_cont_l. eq_cont_r.
             eq_exhaustion (fill k1' (InjLV #()%V)) (fill k2' (InjLV #()%V));
               [set_solver|set_solver|iApply "Hrel"; iDestruct "HmQ" as "(_&$)"|iApply "IH"].
          (* leakauth returns successfully with a value *)
          -- iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->]...
             eq_load_r. eq_load_l...
             eq_cont_l. eq_cont_r.
             eq_lift_l mask_correct_l mask_correct_r...
             eq_load_r...
             rewrite -sc_coupling_nat_invol; last done.
             eq_cont_l. eq_cont_r.
             iDestruct "HmQ" as "[Hsome Hnone]".
             eq_exhaustion (fill k1' (InjRV _)%V) (fill k2' (InjRV _)%V);
               [set_unfold; tauto|set_unfold; tauto|iApply "Hrel"; iApply "Hsome"|iApply "IH"].
        (* a message has been sent by the secure channel but not the authenticated channel *)
        * iDestruct "Hd3" as (?m ?c) "(%Hlt & Hγ & #Hl_m'sim & Hl_sim & Hl_auth & #Hl_fchan & #Hl_rchan & #Hl_key)"...
          eq_load_l... eq_load_r...
          iApply eq_na_close_rule. iFrame "Hclose".
          iSplitR "Hgkl Hsrecvl Hsrecvr Hlrecvr".
          { iNext. iRight. iRight. iExists _, _. iFrame "∗#%". }
          eq_cont_l...
          eq_handle_os_l_in [HandleCtx _ _ _ _ _; AppRCtx _].
          { eapply NoDup_cons_1_1.
            eapply (submseteq_NoDup _ [csend'; crecv'; getKey'; srecv_l; ssend_l]); [solve_submseteq | exact Hnd_l]. }
          iIntros (r2) "Hcrecvl".
          eq_pures'.
          eq_reshape_l (arcv_l _). eq_reshape_r (arcv_r _).
          iApply (eq_env_call_gen lls rls (λ _, iThyBot) _ _ with "Harcv [] [-]");
            [set_unfold; tauto | set_unfold; tauto | | |].
          { intros []; rewrite /lls /rls /pick /=; iApply to_iThy_le_intro'; unfold sem_row_union;
              repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app); solve_submseteq. }
          { iApply eq_lift_same. iExists #()%V, #()%V. iLeft. repeat iSplit; try iPureIntro; try reflexivity. }
          iIntros (v4 v5) "Hv". iEval (rewrite eq_lift_sum) in "Hv".
          iDestruct "Hv" as (w0 w3) "[(-> & -> & Hu)|(-> & -> & Hu)]".
          (* leakauth does not return successfully *)
          -- iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->]...
             eq_cont_l. eq_cont_r. eq_pures'.
             eq_cont_l. eq_cont_r.
             eq_exhaustion (fill k1' _) (fill k2' _);
               [set_unfold; tauto|set_unfold; tauto|iApply "Hrel"; iDestruct "HmQ" as "(_&$)"|iApply "IH"].
          (* leakauth returns successfully with a value: open the invariant
             again, for [l_sim] and [l_auth] *)
          -- iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->]...
             iApply (eq_na_open _ _ alphaN); first (set_unfold; tauto).
             iFrame "Hinvα".
             iIntros "[[(>Hγ & >Hl_m'sim' & >Hl_sim & >Hl_auth & >Hl_fchan' & >Hl_rchan' & >Hl_key') | [>Hd2 | >Hd3]] Hclose]".
             (* a message has already been sent by the secure channel *)
             { by iDestruct (eq_pt_r_agree with "Hl_fchan Hl_fchan'") as %Heq. }
             ** iDestruct "Hd2" as (?m ?c) "(%Hlt' & Hγ & #Hl_m'sim' & #Hl_sim & #Hl_auth & #Hl_fchan' & #Hl_rchan' & #Hl_key')".
                eq_load_r... eq_load_l.
                iApply eq_na_close_rule. iFrame "Hclose".
                iSplitR "Hcrecvl Hsrecvl Hsrecvr Hlrecvr".
                { iNext. iRight. iLeft. iExists _, _. by iFrame "∗#%". }
                iDestruct (eq_pt_r_agree with "Hl_fchan Hl_fchan'") as %Hval.
                assert (m0 = m) as -> by (simplify_eq; symmetry; by apply vgval_inj).
                eq_cont_l. eq_cont_r. eq_pures'.
                eq_load_r...
                eq_lift_l mask_correct_l mask_correct_r...
                iDestruct (eq_pt_r_agree with "Hl_m'sim Hl_m'sim'") as %Hsim.
                simplify_eq. rewrite -sc_coupling_nat_invol; last done.
                eq_cont_l. eq_cont_r.
                eq_exhaustion (fill k1' _) (fill k2' _); [set_unfold; tauto|set_solver|iApply "Hrel"|iApply "IH"].
                iDestruct "HmQ" as "[Hsome _]". iApply "Hsome".
             ** iDestruct "Hd3" as (?m ?c) "(%Hlt' & Hγ & #Hl_m'sim' & Hl_sim & Hl_auth & #Hl_fchan' & #Hl_rchan' & #Hl_key')".
                eq_load_r... eq_load_l.
                iApply eq_na_close_rule. iFrame "Hclose".
                iSplitR "Hcrecvl Hsrecvl Hsrecvr Hlrecvr".
                { iNext. iRight. iRight. iExists _, _. iFrame "∗#%". }
                eq_cont_l. eq_cont_r. eq_pures'.
                eq_cont_l. eq_cont_r.
                eq_exhaustion (fill k1' _) (fill k2' _); [set_unfold; tauto|set_solver|iApply "Hrel"|iApply "IH"].
                iDestruct "HmQ" as "[_ Hnone]". iApply "Hnone".
  Qed.

  Lemma R_CHAN_SIM_f md :
    ⊢ sem_typed [] REAL_SCHAN (SIM_SCHAN ∘f IDEAL_SCHAN)%fac ⊥ (fac md τ_CHAN) [].
  Proof using All.
    iApply sem_typed_sub_ty; first iApply fac_MS_le.
    iApply (EQ_sem_typed_expr _ _ _ _ Fwd SCHAN_EQ); intros; done.
  Qed.

  Lemma SIM_R_CHAN_f md :
    ⊢ sem_typed [] (SIM_SCHAN ∘f IDEAL_SCHAN)%fac REAL_SCHAN ⊥ (fac md τ_CHAN) [].
  Proof using All.
    iApply sem_typed_sub_ty; first iApply fac_MS_le.
    iApply (EQ_sem_typed_expr _ _ _ _ Bwd SCHAN_EQ); intros; done.
  Qed.

End schan_security.

From iris.proofmode Require Import base proofmode classes.                                             
From iris.base_logic.lib Require Import  na_invariants.   
From iris.algebra Require Import agree excl auth frac excl_auth. 
From iris.algebra.lib Require Import dfrac_agree.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode
  spec_rules spec_ra
  class_instances.
From clutch.prob_eff_lang.probblaze Require Import tactics.
From clutch.prob_eff_lang.probblaze Require Import sem_types sem_row sem_sig sem_judgement sem_def.
From clutch.prob_eff_lang.probblaze Require Import p_composition.
From clutch.prob_eff_lang.probblaze.examples.DH_KE Require Import (* def_dhke  *)(* dhke_channel *) xor sec_channel_def sc_bijection.


Import fingroup.

Import fingroup.fingroup.

(*Import valgroup_notation.*)
Import valgroup_tactics.


Section schan_security.
  Context `{probblazeRGS Σ}.
  (* Context (lka1 lka2 klk1 klk2 : label). *)
  Context {vg: val_group}.
  Context {cg: clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.
  (* Context {Key Support : nat}.*)
  Variable xor_struct : XOR (Key := (S n'')) (Support := (S n'')).
  Context `{!XOR_spec (Key := (S n'')) (Support := (S n'')) (H := xor_struct)}.
  (* [group_xor_sem] and its four assumptions ([Bij_xor_sem], [Bij_xor_sem_l],
     [vg_int_xor_sem], [Bij_log]) are gone: the group xor is now [sc_coupling]
     from sc_bijection.v, and the facts that were assumed here are derived
     there -- [sc_coupling_bij] (was [Bij_log]), [sc_coupling_invol] (was
     [Bij_xor_sem], from [xor_sem_inverse_r]) and [sc_coupling_involutive]
     (was [Bij_xor_sem_l], from [xor_sem_invol]).  [vg_int_xor_sem] is not
     needed at all: with the 0-based encoding [vg_of_int] never fails. *)

  Definition alphaN : namespace := nroot .@ "alpha".
  Definition betaN : namespace := nroot .@ "beta".

  (*Theories for the interaction of the secure channel with the environment*)
  (*-------------------------------------------------------------*)

  (* Theories for the authenticated channel leaks *)
  (*-------------------------------------------------------------*)
  (* Sent BY Bob TO Alice*)
  Program Definition LASendBob (leakauth1 leakauth2 : label) : iThy Σ :=
    λ e1 e2, (λne Q,
                ∃ m1 m2 : val,
                  ⌜e1 = (do: leakauth1 (SendV (m1, alice)))⌝%E ∗
                  ⌜ e2 = do: leakauth2 (SendV (m2, alice)) ⌝%E ∗
                  □ Q (Val #()%V) (Val #()%V))%I.
  Next Obligation. solve_proper. Qed.
  (* Sent BY Alice TO Bob*)
  Program Definition LASendAlice (leakauth1 leakauth2 : label) : iThy Σ :=
    λ e1 e2, (λne Q,
                ∃ m1 m2 : val,
                  ⌜e1 = (do: leakauth1 (SendV (m1, bob)))⌝%E ∗
                  ⌜ e2 = do: leakauth2 (SendV (m2, bob)) ⌝%E ∗
                  □ Q (Val #()%V) (Val #()%V))%I.
  Next Obligation. solve_proper. Qed.
  (*Recv FROM bob*)
  Program Definition LARecvBob (leakauth1 leakauth2 : label) : iThy Σ :=
    λ e1 e2, (λne Q,
                ⌜ e1 = do: leakauth1 (RecvV bob) ⌝%E ∗
                ⌜ e2 = do: leakauth2 (RecvV bob) ⌝%E ∗
                □ ((∀ b1 b2 : nat, Q (SOMEV #b1) (SOMEV #b2)) ∧ Q NONEV NONEV)
             )%I.
  Next Obligation. solve_proper. Qed.
  (* Recv FROM Alice *)
  Program Definition LARecvAlice (leakauth1 leakauth2 : label) : iThy Σ :=
    λ e1 e2, (λne Q,
                ⌜ e1 = do: leakauth1 (RecvV alice) ⌝%E ∗
                ⌜ e2 = do: leakauth2 (RecvV alice) ⌝%E ∗
                □ ((∀ b1 b2 : nat, Q (SOMEV #b1) (SOMEV #b2)) ∧ Q NONEV NONEV)
             )%I.
  Next Obligation. solve_proper. Qed.


  (* Theories for the key exchange leaks*)
  (*---------------------------------------------------------*)
  (*Send TO Alice*)
  Program Definition KLeakSendAlice (keyleak1 keyleak2 : label) : iThy Σ :=
    λ e1 e2, (λne Q,
                ⌜ e1 = do: keyleak1 (SendV alice) ⌝%E ∗
                ⌜ e2 = do: keyleak2 (SendV alice) ⌝%E ∗
                □ Q (Val #()%V) (Val #()%V))%I.
  Next Obligation. solve_proper. Qed.
  (* Send TO Bob *)
  Program Definition KLeakSendBob (keyleak1 keyleak2 : label) : iThy Σ :=
    λ e1 e2, (λne Q,
                ⌜ e1 = do: keyleak1 (SendV bob) ⌝%E ∗
                ⌜ e2 = do: keyleak2 (SendV bob) ⌝%E ∗
                □ Q (Val #()%V) (Val #()%V))%I.
  Next Obligation. solve_proper. Qed.


  (*Program Definition KLeakRecvAlice : iThy Σ :=
    λ e1 e2, (λne Q,
                ⌜ e1 = do: keyleak1 (RecvV alice) ⌝%E ∗
                           ⌜ e2 = do: keyleak2 (RecvV alice) ⌝%E ∗
                                      □ Q (Val #()%V) (Val #()%V))%I.
  Next Obligation. solve_proper. Qed.*)
  (* Recv FROM Alice *)
  Program Definition KLeakRecvAlice (keyleak1 keyleak2 : label) : iThy Σ :=
    λ e1 e2, (λne Q,
                ⌜ e1 = do: keyleak1 (RecvV alice) ⌝%E ∗
                ⌜ e2 = do: keyleak2 (RecvV alice) ⌝%E ∗
                □ (Q NONEV NONEV ∗ Q (SOMEV #0) (SOMEV #0)))%I.
  Next Obligation. solve_proper. Qed.
  (* Recv FROM Bob *)
  Program Definition KLeakRecvBob (keyleak1 keyleak2 : label) : iThy Σ :=
    λ e1 e2, (λne Q,
                ⌜ e1 = do: keyleak1 (RecvV bob) ⌝%E ∗
                ⌜ e2 = do: keyleak2 (RecvV bob) ⌝%E ∗
                □ (Q NONEV NONEV ∗ Q (SOMEV #0) (SOMEV #0)))%I.
  Next Obligation. solve_proper. Qed.

  (* Theories relating the authenticated channel with the secure channel leak*)
  (*-----------------------------------------------------------------------------*)
  (* STALE: these four are dead code -- nothing in the development references
     them -- and they describe [F_OAUTH]'s OLD single tagged [channel] effect
     ([do: channel (SendV ...)]), which has been split into untagged
     [send]/[recv].  They were left unported; delete them, or re-derive them
     against [csend]/[crecv] if a use ever appears. *)
  Program Definition SendALSAlice (channel leaksec : label) : iThy Σ :=
    λ e1 e2, (λne Q,
                ∃ m : val,
                  (⌜ e1 = do: channel (SendV (m, alice)) ⌝%E ∗
                   ⌜  e2 = do: leaksec (SendV alice)⌝%E) ∗ □ (Q (Val #()%V) (Val #()%V)))%I.
  Next Obligation. solve_proper. Qed.

  Program Definition SendALSBob (channel leaksec : label) : iThy Σ :=
    λ e1 e2, (λne Q,
                ∃ m : val,
                  (⌜ e1 = do: channel (SendV (m, bob)) ⌝%E ∗
                   ⌜  e2 = do: leaksec (SendV bob)⌝%E) ∗ □ (Q (Val #()%V) (Val #()%V)))%I.
  Next Obligation. solve_proper. Qed.

  Program Definition RecvALSAlice (channel leaksec : label) : iThy Σ :=
    λ e1 e2, (λne Q,
                (⌜ e1 = do: channel (RecvV alice) ⌝%E ∗
                 ⌜  e2 = do: leaksec (RecvV alice)⌝%E) ∗ □ (Q (Val #()%V) (Val #()%V)))%I.
  Next Obligation. solve_proper. Qed.

  Program Definition RecvALSBob (channel leaksec : label) : iThy Σ :=
    λ e1 e2, (λne Q,
                (⌜ e1 = do: channel (RecvV bob) ⌝%E ∗
                 ⌜  e2 = do: leaksec (RecvV bob)⌝%E) ∗ □ (Q (Val #()%V) (Val #()%V)))%I.
  Next Obligation. solve_proper. Qed.


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
  
  Import valgroup_notation.

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
    unfold keyleak in H1. simpl in H1. unfold keyleak_mono in H1. simpl in H1.       Search "∈". apply list_elem_of_singleton in H1. simpl in H1.
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
    unfold keyleak in H1. simpl in H1. unfold keyleak_mono in H1. simpl in H1.       Search "∈". apply list_elem_of_singleton in H1. simpl in H1.
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
  
  Definition REAL_CHAN : val :=
    λ: "f",
      (F_OAUTH ||ₗ F_KE_lazy_alice) (CHAN xor "f").
  About CHAN.

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

  (* Unconditional: with the 0-based encoding every code in [0, #|G|-1] is
     decodable, so [vg_of_int] never yields NONE and the result is exactly the
     bijection [sc_coupling] of sc_bijection.v. *)
  Lemma G_XOR_CORRECT_l (g1 g2 : vgG) E K X e R :
    (BREL (fill K (SOMEV (vgval (g ^+ sc_coupling g1 (g_log g2))%g))) ≤ e @ E <|X|> {{R}}) -∗
    (BREL (fill K (G_XOR xor (vgval g1) (vgval g2))) ≤ e @ E <|X|> {{R}}).
  Proof using  G H XOR_spec0 cg vg vgg xor_struct
    Σ.
    assert (H1 : (int_of_vg_sem g1 < S (S n''))%nat).
    { pose proof (int_of_vg_sem_bound g1) as Hb. rewrite vgG_card in Hb. lia. }
    assert (H2 : (int_of_vg_sem g2 < S (S n''))%nat).
    { pose proof (int_of_vg_sem_bound g2) as Hb. rewrite vgG_card in Hb. lia. }
    pose proof (xor_dom _ H1 _ H2) as H3.
    pose proof H3 as H4. rewrite -vgG_card in H4.
    destruct (vg_of_int_sem_surj _ H4) as [h [Hg1g2 Hint]].
    assert (Hsc : (g ^+ sc_coupling g1 (g_log g2))%g = h).
    { rewrite /sc_coupling. cbv zeta. rewrite g_log_id Hg1g2. apply g_log_id. }
    rewrite Hsc.
    iIntros "Hrelxor".
    unfold G_XOR.
    brel_pures'.
    assert (fill (K ++  [AppRCtx vg_of_int  ; AppRCtx (App xor (int_of_vg (vgval g1)))]) (int_of_vg (vgval g2)) = fill K (fill [AppRCtx vg_of_int  ; AppRCtx (App xor (int_of_vg (vgval g1)))] (int_of_vg (vgval g2)))) as Hectxappg2.
    { rewrite fill_app. auto. }
    rewrite -Hectxappg2.
    iApply (brel_int_of_vg_sem_correct_l _ _ g2).
    simpl.
    rewrite fill_app. simpl.
    assert (fill (K ++  [AppRCtx vg_of_int  ; AppLCtx #(int_of_vg_sem g2); AppRCtx xor]) (int_of_vg (vgval g1)) = fill K (fill [AppRCtx vg_of_int  ; AppLCtx #(int_of_vg_sem g2); AppRCtx xor] (int_of_vg (vgval g1)))) as Hectxappg1.
    { rewrite fill_app. auto. }
    rewrite -Hectxappg1.
    iApply (brel_int_of_vg_sem_correct_l _ _ g1).
    rewrite fill_app. simpl.
    assert (fill (K ++ [AppRCtx vg_of_int ]) (xor #(int_of_vg_sem g1) #(int_of_vg_sem g2)) = fill K (fill [AppRCtx vg_of_int] (xor #(int_of_vg_sem g1) #(int_of_vg_sem g2)))) as Hectxxor.
    { rewrite fill_app. auto. }
    rewrite -Hectxxor.
    iApply xor_correct_l. 
    1,2: rewrite -vgG_card; apply int_of_vg_sem_bound. 
    rewrite fill_app. simpl.
    iApply brel_vg_of_int_correct_l.
    { apply Hg1g2. }
    { simpl. iApply "Hrelxor". }
  Qed.


  Lemma G_XOR_CORRECT_r (g1 g2 : vgG) E K X e R :
    (BREL e ≤ (fill K (SOMEV (vgval (g ^+ sc_coupling g1 (g_log g2))%g))) @ E <|X|> {{R}}) -∗
    (BREL e ≤ (fill K (G_XOR xor (vgval g1) (vgval g2))) @ E <|X|> {{R}}).
  Proof using  G H XOR_spec0 cg vg vgg xor_struct
    Σ.
    assert (H1 : (int_of_vg_sem g1 < S (S n''))%nat).
    { pose proof (int_of_vg_sem_bound g1) as Hb. rewrite vgG_card in Hb. lia. }
    assert (H2 : (int_of_vg_sem g2 < S (S n''))%nat).
    { pose proof (int_of_vg_sem_bound g2) as Hb. rewrite vgG_card in Hb. lia. }
    pose proof (xor_dom _ H1 _ H2) as H3.
    pose proof H3 as H4. rewrite -vgG_card in H4.
    destruct (vg_of_int_sem_surj _ H4) as [h [Hg1g2 Hint]].
    assert (Hsc : (g ^+ sc_coupling g1 (g_log g2))%g = h).
    { rewrite /sc_coupling. cbv zeta. rewrite g_log_id Hg1g2. apply g_log_id. }
    rewrite Hsc.
    iIntros "Hrelxor".
    unfold G_XOR.
    brel_pures. 
    assert (fill (K ++  [AppRCtx vg_of_int  ; AppRCtx (App xor (int_of_vg (vgval g1)))]) (int_of_vg (vgval g2)) = fill K (fill [AppRCtx vg_of_int  ; AppRCtx (App xor (int_of_vg (vgval g1)))] (int_of_vg (vgval g2)))) as Hectxappg2.
    { rewrite fill_app. auto. }
    rewrite -Hectxappg2.
    iApply (brel_int_of_vg_sem_correct_r _ _ g2).
    simpl.
    rewrite fill_app. simpl.
    assert (fill (K ++  [AppRCtx vg_of_int  ; AppLCtx #(int_of_vg_sem g2); AppRCtx xor]) (int_of_vg (vgval g1)) = fill K (fill [AppRCtx vg_of_int  ; AppLCtx #(int_of_vg_sem g2); AppRCtx xor] (int_of_vg (vgval g1)))) as Hectxappg1.
    { rewrite fill_app. auto. }
    rewrite -Hectxappg1.
    iApply (brel_int_of_vg_sem_correct_r _ _ g1).
    rewrite fill_app. simpl.
    assert (fill (K ++ [AppRCtx vg_of_int ]) (xor #(int_of_vg_sem g1) #(int_of_vg_sem g2)) = fill K (fill [AppRCtx vg_of_int] (xor #(int_of_vg_sem g1) #(int_of_vg_sem g2)))) as Hectxxor.
    { rewrite fill_app. auto. }
    rewrite -Hectxxor.
    iApply xor_correct_r.
    1,2: rewrite -vgG_card; apply int_of_vg_sem_bound. 
    rewrite fill_app. simpl.
    iApply brel_vg_of_int_correct_r.
    { apply Hg1g2. }
    { simpl. iApply "Hrelxor". }
  Qed.

  (*secure channel only assumes a fixed direction of messag epassing, so this needs to relfect in the type of the thunks that its client receives*)


  Definition R_CHAN : val :=
    λ: "f",
      (F_KE_lazy_alice ||ᵣ F_OAUTH) (CHAN xor "f").

  (*Verification of F_KE_L[F_OAUTH[CHAN[]]] ≤ CHAN_SIM[F_CHAN[]]*)
  (*----------------------------------------------------------*)
  (* NOTE: [F_OAUTH_CHAN_SIM] has no consumers anywhere in the development
     (the live chain is [SEM_R_CHAN_SIM]/[SEM_R_CHAN_SIM_rev] ->
     [R_CHAN_CHAN_SIM_F_CHAN]/[CHAN_SIM_F_CHAN_R_CHAN] -> [R_I_SCHAN]/[I_R_SCHAN]).
     It was therefore NOT ported when [F_OAUTH]'s single [channel] effect was
     split into [send]/[recv]; it is commented out rather than updated.  To
     revive it, apply the same treatment as [SEM_R_CHAN_SIM] below. *)
(*
  Lemma F_OAUTH_CHAN_SIM (f1 f2 : val) (L : sem_row Σ) :
    (∀ᵣ θₕ, ((sem_ty_nat -{ θₕ }-> 𝟙) × (𝟙 -{ θₕ }-> Option 𝔾)) -{ sem_row_union θₕ L }-∘ 𝟙)%T
      f1 f2 -∗
    BREL R_CHAN f1
      ≤ CHAN_SIM_lazy (F_CHAN f2) <|⊥|> {{λ v1 v2,
                                            ∀ (leakauth1 leakauth2 keyleak1 keyleak2 : label),
                                              BREL v1 ((λ: "m", do: leakauth1 (Send "m")), (λ: "m", do: leakauth1 (Recv "m")))%V ((λ: "m", do: keyleak1 (Send "m")), (λ: "m", do: keyleak1 (Recv "m")))%V ≤ v2 ((λ: "m", do: leakauth2 (Send "m")), (λ: "m", do: leakauth2 (Recv "m")))%V ((λ: "m", do: keyleak2 (Send "m")), (λ: "m", do: keyleak2 (Recv "m")))%V  <| (iLblSig_to_iLblThy (envsec_row keyleak1 keyleak2 leakauth1 leakauth2 )) ++ (iLblSig_to_iLblThy L) |> {{ (λ w1 w2, 𝟙%T w1 w2)}}}}.
  Proof with (repeat foldkont) using  G
             H XOR_spec0 cg inG0
             inG1 inG2 (* klk1 klk2 lka1 lka2 *) vg
             vgg xor_struct Σ.
    iIntros "Hrelf1f2".
    repeat simpl.
    unfold R_CHAN.
    unfold CHAN, F_CHAN.
    brel_pures.
    unfold right_composition. brel_pures.
    unfold CHAN.
    repeat simpl. brel_pures'.

    
    unfold F_CHAN, CHAN_SIM_lazy, F_KE_lazy_alice, F_OAUTH.


    repeat simpl. brel_pures. iModIntro. iIntros (????).
    brel_pures.

    iApply brel_alloc_r. iIntros (l_sim) "Hl_sim". brel_pures_r.
    iApply brel_alloc_r. iIntros (l_m'sim) "Hl_m'sim". brel_pures_r.
    
    iApply brel_alloctape_l. iIntros (γ) "!> Hγ". brel_pures_l.
    iApply brel_alloc_l. iIntros (l_key) "!> Hl_key". brel_pures_l.
    iApply brel_effect_l. iIntros (getKey') "!> HgK !>". brel_pures_l.
    iApply brel_effect_r. iIntros (leaksec') "Hleaksec !>". brel_pures.
    iApply brel_alloc_l. iIntros (l_auth) "!>Hl_auth". brel_pures_l.
    iApply brel_effect_l. iIntros (channel') "!> Hchannel !>". brel_pures_l.


    iApply brel_alloc_r. iIntros (l_fchan) "Hlfchan". brel_pures_r.
    iApply brel_effect_r. iIntros (schannel_r) "Hschannel_r !>". brel_pures_r.
    brel_pures'. repeat simpl. brel_pures'.
    iApply brel_alloc_l. iIntros (l_rchan) "!>Hlrchan". brel_pures_l.
    iApply brel_effect_l. iIntros (schannel_l) "!> Hschannel_l !>". brel_pures_l.
    set (kl1 := ( match: "payload" with
                    InjL "m" =>
                      match: ! #l_rchan with
                        InjL <> =>
                          #l_rchan <- InjR "m";;
                          let: "key" := (λ: "party", do: getKey' "party")%V bob in
                          match: "key" with
                            InjL <> => "k" #()%V
                          | InjR "x" =>
                              match: G_XOR xor "m" "x" with
                                InjL <> => "k" #()%V
                              | InjR "mg" =>
                                  (λ: "m", do: channel' InjL "m")%V ("mg", bob);; "k" #()%V
                              end
                          end
                      | InjR "m" => "k" #()%V
                      end
                  | InjR <> =>
                      let: "key" := (λ: "party", do: getKey' "party")%V alice in
                      match: "key" with
                        InjL <> => "k" (InjLV #()%V)
                      | InjR "key" =>
                          let: "r" := (λ: "m", do: channel' InjR "m")%V bob in
                          match: "r" with
                            InjL <> => "k" (InjLV #()%V)
                          | InjR "x" =>
                              match: G_XOR xor "x" "key" with
                                InjL <> => "k" (InjL #()%V)
                              | InjR "mg" => "k" (InjR "mg")
                              end
                          end
                      end
                  end )%E ).
    set (kl2 := ( match: "payload" with
                    InjL "payload" =>
                      let: "dst" := "payload" in
                      let: "m" := Fst "dst" in
                      let: "dst" := Snd "dst" in
                      match: ! #l_auth with
                        InjL <> =>
                          #l_auth <- InjR "m";;
                          (λ: "m", do: leakauth1 Send "m")%V ("m", "dst");; "k" #()%V
                      | InjR "message" => "k" #()%V
                      end
                  | InjR "from" =>
                      let: "r" := (λ: "m", do: leakauth1 Recv "m")%V "from" in
                      match: "r" with InjL <> => "k" (InjLV #()%V) | InjR "x" => "k" ! #l_auth end
                  end )%E).
    set (kl3 := (match: "p" with
                   InjL <> =>
                     let: "key" := (λ: <>,
                                      match: ! #l_key with
                                        InjL <> =>
                                          let: "c" := #();; rand(#lbl:γ) #(S n'') in
                                          let: "key" := vexp g "c" in
                                          #l_key <- InjR "key";; "key"
                                      | InjR "key" => "key"
                                      end)%V
                                     #()%V in
                     (λ: "m", do: keyleak1 Send "m")%V bob;;
                     let: "r" := (λ: "m", do: keyleak1 Recv "m")%V bob in
                     match: "r" with
                       InjL <> => "k" (InjLV #()%V)
                     | InjR "w" => "k" (InjR "key")
                     end
                 | InjR <> =>
                     let: "r" := (λ: "m", do: keyleak1 Recv "m")%V alice in
                     match: "r" with
                       InjL <> => "k" (InjLV #()%V)
                     | InjR "w" =>
                         (λ: "m", do: keyleak1 Send "m")%V alice;;
                         match: ! #l_key with
                           InjL <> => "k" (InjLV #()%V)
                         | InjR "key" => "k" (InjR "key")
                         end
                     end
                 end)%E).
    set (kr1 := ( match: "payload" with
                    InjL "m" =>
                      match: ! #l_fchan with
                        InjL <> =>
                          #l_fchan <- InjR "m";;
                          (λ: "m", do: leaksec' InjL "m")%V alice;; "k" #()%V
                      | InjR "x" => "k" #()%V
                      end
                  | InjR <> =>
                      let: "r" := (λ: "m", do: leaksec' InjR "m")%V bob in
                      match: "r" with
                        InjL <> => "k" (InjLV #()%V)
                      | InjR "x" => "k" (InjR ! #l_fchan)
                      end
                  end )%E).
    set (kr2 := ( match: "payload" with
                    InjL <> =>
                      let: "m'" := (λ: <>,
                                      match: ! #l_m'sim with
                                        InjL <> =>
                                          let: "m'" := #();; rand #(S n'') in
                                          #l_m'sim <- InjR "m'";; "m'"
                                      | InjR "m'" => "m'"
                                      end)%V
                                     #()%V in
                      (λ: "m", do: keyleak2 Send "m")%V bob;;
                      let: "r" := (λ: "m", do: keyleak2 Recv "m")%V bob in
                      match: "r" with
                        InjL <> => "k" (InjLV #()%V)
                      | InjR "x" =>
                          match: ! #l_sim with
                            InjL <> =>
                              let: "mA" := vexp g "m'" in
                              #l_sim <- InjR "m'";;
                              (λ: "m", do: leakauth2 Send "m")%V ("mA", bob);; "k" #()%V
                          | InjR "m" => "k" #()%V
                          end
                      end
                  | InjR <> =>
                      let: "r" := (λ: "m", do: keyleak2 Recv "m")%V alice in
                      match: "r" with
                        InjL <> => "k" (InjLV #()%V)
                      | InjR "x" =>
                          (λ: "m", do: keyleak2 Send "m")%V alice;;
                          match: ! #l_m'sim with
                            InjL <> => "k" (InjLV #()%V)
                          | InjR "_" =>
                              let: "rla" := (λ: "m", do: leakauth2 Recv "m")%V bob in
                              match: "rla" with
                                InjL <> => "k" (InjLV #()%V)
                              | InjR "x" => "k" ! #l_sim
                              end
                          end
                      end
                  end )%E).
    set (θ := client_row channel' leaksec' getKey' schannel_l schannel_r).
    iSpecialize ("Hrelf1f2" $! θ).
    unfold sem_ty_arr, sem_ty_mbang. simpl.
    iAssert (sem_val_typed  ((λ: "m", do: schannel_l InjL "m"), (λ: <>, do: schannel_l InjR bob))%V ((λ: "m", do: schannel_r InjL "m") , (λ: <>, do: schannel_r InjR bob))%V (((sem_ty_nat -{ θ }-> 𝟙) × (𝟙 -{ θ }-> (Option 𝔾)))%T)) as "Hschn".
    { iApply SEM_TYPED_EFF. }
    unfold sem_val_typed. simpl.
    iDestruct "Hschn" as "#Hschn".
    iSpecialize ("Hrelf1f2" with "Hschn"). simpl.
    set (f m := sc_coupling m).
    set (d1 := (γ ↪N (S n''; []) ∗ l_m'sim ↦ₛ NONEV ∗ l_sim ↦ₛ NONEV ∗ l_auth ↦ NONEV ∗ l_fchan ↦ₛ NONEV ∗ l_rchan ↦ NONEV ∗  l_key ↦ NONEV)%I).
    set (d2 := ((∃ m : vgG, ∃ n : fin (S (S n'')), γ ↪N (S n''; []) ∗ l_m'sim ↦ₛ□ SOMEV #(f m n) ∗ l_sim ↦ₛ□ SOMEV #(f m n) ∗
                                                   l_auth ↦□ SOMEV (vgval
                                                                      (g ^+ f m n))%V ∗  l_fchan ↦ₛ□ SOMEV (vgval m) ∗  l_rchan ↦□ SOMEV (vgval m) ∗ l_key ↦□ SOMEV (vgval (g ^+n)))%I)).

    set (d3 := (∃ m : vgG, ∃ n : fin (S (S n'')), γ ↪N (S n''; []) ∗ l_m'sim ↦ₛ□ SOMEV #(f m n) ∗ l_sim ↦ₛ NONEV ∗ l_auth ↦ NONEV ∗ l_fchan ↦ₛ□ SOMEV (vgval m) ∗  l_rchan ↦□ SOMEV (vgval m) ∗ l_key ↦□ SOMEV (vgval (g ^+n)))%I).
    iApply (brel_na_alloc (d1 ∨ (d2 ∨ d3))%I alphaN).
    iSplitL "Hγ Hl_m'sim Hl_sim Hl_auth Hlfchan Hlrchan Hl_key"; [iNext; iLeft; iFrame|].
    iIntros "#Hinvα".
    iApply brel_new_theory.
    iApply (brel_add_label_l with "Hschannel_l").
    iApply (brel_add_label_r with "Hschannel_r").
    iApply (brel_add_label_l with "HgK").
    iApply (brel_add_label_l with "Hchannel").
    iApply (brel_add_label_r with "Hleaksec").
    set (X :=  iLblSig_to_iLblThy [([schannel_l] , [schannel_r] , sec_channel schannel_l schannel_r)]).
    set (R := (λ u1 u2 : val, 𝟙%T u1 u2)).
    set (X' := sec_channel schannel_l schannel_r).
    iApply brel_learn. iIntros "%Hdist' _".
    iApply ((brel_exhaustion (f1 ((λ: "m", do: schannel_l InjL "m"),(λ: <>, do: schannel_l InjR bob))%V) (f2 ((λ: "m", do: schannel_r InjL "m"),(λ: <>, do: schannel_r InjR bob))%V) _ _ X' _ _ R _ _ _) with "[Hrelf1f2]").
    { simpl; (set_unfold; tauto). }
    { simpl; (set_unfold; tauto). }
    {
      set clt := ([channel'; getKey'; schannel_l], [leaksec'; schannel_r], X').
      set cltheory := iLblSig_to_iLblThy [([channel'; getKey'; schannel_l] , [leaksec'; schannel_r] , X')].
      set (L' := cltheory ++ (iLblSig_to_iLblThy L)).
      set (keytheory := iLblSig_to_iLblThy [([keyleak1], [keyleak2], keyleak keyleak1 keyleak2)]).
      set (leaktheory := (iLblSig_to_iLblThy [([leakauth1], [leakauth2], leakauth leakauth1 leakauth2)])).
      set (M := cltheory ++ keytheory ++ leaktheory ++ (iLblSig_to_iLblThy L)).
      iApply (brel_introduction_mono L' M).
      + simpl.
        iApply to_iThy_le_intro'.
        unfold L'. unfold M.
        set (l := cltheory ++ keytheory ++ leaktheory).

        apply (submseteq_skips_r (iLblSig_to_iLblThy L) (cltheory) (cltheory ++ keytheory ++ leaktheory)).
        eapply submseteq_inserts_r. eapply Permutation_submseteq. auto.
      + unfold L'. iApply "Hrelf1f2". }
    iLöb as "IH".
    unfold kl1.
    iSplit; [iIntros (v1 v2) "%Hv1v2"; iModIntro; brel_pures; iModIntro; done |].
    iIntros (?????) "!# %Hk1 %Hk2 HXQ #Hrel".
    iDestruct "HXQ" as "[HSendAlice | HRecvBob]".
    (* Send a message using the secure channel from Alice To Bob *)
    + iDestruct "HSendAlice" as (?mz) "[[%He1 %He2] #HmQ]".
      rewrite -> He1. rewrite -> He2. brel_pures.
      { apply -> NeutralEctx_ectx_labels_singleton.
        do 2 (eapply NeutralEctx_label_cons_inv_2 in Hk1). eapply Hk1. }
      {  apply -> NeutralEctx_ectx_labels_singleton.
         eapply NeutralEctx_label_cons_inv_2 in Hk2.
         eapply NeutralEctx_label_cons_inv_1 in Hk2. eapply Hk2. }

      (* Interpreting a group element from mz *)
      destruct (vg_of_int_sem mz) as [m|] eqn:Hmz .
      2 : {
        iApply brel_vg_of_int_none_l; first done.
        iApply brel_vg_of_int_none_r; first done.
        brel_pures'. 
        iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V));
          [(set_unfold; tauto)|done|by iApply "Hrel"|iApply "IH"]. }
      
      iApply brel_vg_of_int_correct_l; first done.
      iApply brel_vg_of_int_correct_r; first done.
      brel_pures'. 
      
      iApply (brel_na_inv _ _ alphaN); first (set_unfold; tauto).
      iFrame "Hinvα".
      iIntros "([(>Hγ & >Hl_m'sim & >Hl_sim & >Hl_auth & >Hl_fchan & >Hl_rchan & >Hl_key) | [>Hd2 | >Hd3 ]] & Hclose)".
      (* First message to be sent by the secure channel*)
      ++
        iApply (brel_load_r _ _ _ _ [HandleCtx _ _ _ _ _ ; CaseCtx _ _] with "Hl_fchan").
        iIntros "Hl_fchan".
        iApply (brel_load_l _ _ _  [HandleCtx Deep MS getKey' _ _ ; HandleCtx Deep MS channel' _ _; CaseCtx _ _] with "Hl_rchan").
        iIntros "!>Hl_rchan". brel_pures.
        simpl. brel_pures.
        iApply (brel_store_r _ _ _ _ [HandleCtx _ _ _ _ _ ; AppRCtx _] with "Hl_fchan"). iIntros "Hl_fchan".
        simpl.
        brel_pures.
        { simpl. apply not_elem_of_nil. }
        iApply (brel_store_l _ _ _  [HandleCtx _ _ _ _ _ ; HandleCtx _ _ _ _ _ ; AppRCtx _] with "Hl_rchan").
        iIntros "!>Hl_rchan". brel_pures; try (simpl); try (apply not_elem_of_nil).
        { unfold distinct in Hdist'. destruct Hdist'. unfold distinct_l in H0.
          simpl in H0.
          repeat (rewrite -> labels_l_cons in H0).
          eapply NoDup_app in H0.
          eapply NoDup_cons_1_1. destruct H0.
          eapply (submseteq_NoDup _ [channel'; getKey'; schannel_l]); [solve_submseteq | apply H0]. }
        repeat foldkont.
        iApply (brel_load_l _ _ _ [AppRCtx _ ; CaseCtx _ _] with "Hl_key"). iIntros "!> Hl_key".
        brel_pures_l.
        iApply (brel_load_r _ _ _ _ [AppRCtx _ ; CaseCtx _ _] with "Hl_m'sim"). iIntros "Hl_m'sim".
        brel_pures.
        iDestruct "Hγ" as (ms) "(%Hf' & Hγ)". apply map_eq_nil in Hf'. simplify_eq.
        iApply (brel_couple_TU _ _ (f m) [AppRCtx _; AppRCtx _] _ _ _ _ _ _); simpl; auto.
        simpl. iSplitL "Hγ". {iModIntro ; iFrame "Hγ". }
        iIntros (c) "Hγ".
        brel_pures.
        iApply (brel_randT_l _ [AppRCtx _ ; AppRCtx _] γ _ _ _ _); auto.
        simpl. iSplitL "Hγ"; [iFrame "Hγ"; auto |].
        iModIntro. iIntros "Hγ %Hc".
        brel_pures.
        simpl.
        iApply (brel_exp_l [AppRCtx _ ; AppRCtx _] _ _ _ g c _).
        brel_pures.
        iApply (brel_store_l _ _ _ [AppRCtx _; AppRCtx _ ] with "Hl_key"). iIntros "!> Hl_key".
        iApply (brel_store_r _ _ _ _ [AppRCtx _; AppRCtx _] with "Hl_m'sim").
        iIntros "Hl_m'sim". brel_pures. simpl.
        iApply fupd_brel.
        iMod (ghost_map_elem_persist with "Hl_fchan") as "#Hl_fchan".
        iMod (ghost_map_elem_persist with "Hl_rchan") as "#Hl_rchan".
        iMod (ghost_map_elem_persist with "Hl_key") as "#Hl_key".
        iMod (ghost_map_elem_persist with "Hl_m'sim") as "#Hl_m'sim".
        iModIntro.
        iApply brel_na_close. iFrame.
        iSplitL.
        { iModIntro. iRight. iRight. unfold d3.  iExists m, c.
          iFrame "Hγ Hl_m'sim Hl_sim Hl_auth Hl_fchan Hl_rchan Hl_key". }



        set (keytheory := iLblSig_to_iLblThy [([keyleak1], [keyleak2], keyleak keyleak1 keyleak2)]).
        set (leaktheory := (iLblSig_to_iLblThy [([leakauth1], [leakauth2], leakauth leakauth1 leakauth2)])).
        set (M := [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)] ++ leaktheory ++ (iLblSig_to_iLblThy L)).
        set (N := [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)] ++ keytheory ++ leaktheory ++ (iLblSig_to_iLblThy L)).
        brel_pures. simpl.
        iApply (brel_bind'' [AppRCtx _] [AppRCtx _] keytheory M N (𝟙%T) (Do keyleak1 (InjLV bob)) (Do keyleak2 (InjLV bob))).
        { simpl. (set_unfold; tauto). }
        { simpl. (set_unfold; tauto). }
        { simpl. unfold M. unfold N. iApply to_iThy_le_intro'. eapply Permutation_submseteq.
          eapply perm_swap. }
        {  iApply (brel_introduction' [keyleak1] [keyleak2]).
           1: { unfold keytheory.
                eapply list_elem_of_here. }
           iExists _, _, [], [],_.
           do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
           iSplitL;  [|by iIntros "!>" (??) "H"; iApply "H"].
           iRight. iLeft. simpl.
           repeat (iSplit; try (iPureIntro); try (unfold SendV); try reflexivity).
           iModIntro.
           iApply brel_value.
           iIntros "$ !>". brel_pures.
           iAssert (distinct' N) as "%Hdistinct".
           { unfold N. unfold keytheory. unfold leaktheory. simpl.
             unfold distinct'. iPureIntro. apply Hdist'. }
           iApply (brel_bind'' _ _ keytheory M N 𝟙%T (Do keyleak1 (InjRV bob)) (Do keyleak2 (InjRV bob))).
           { simpl. unfold M.  repeat (rewrite -> labels_l_cons). (set_unfold; tauto). }
           { simpl. apply list_subseteq_nil. }
           { simpl. unfold M. unfold N. iApply to_iThy_le_intro'. eapply Permutation_submseteq.
             eapply perm_swap. }
           { iApply (brel_introduction' [keyleak1] [keyleak2]).
             1: { unfold keytheory.
                  eapply list_elem_of_here. }
             iExists _, _, [], [],_.
             do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
             iSplitL;  [|by iIntros "!>" (??) "H"; iApply "H"].
             iRight. iRight. simpl.
             repeat (iSplit; try (iPureIntro); try (unfold RecvV); try reflexivity);
               try (iModIntro); simpl. iSplitL.
             +++    iApply brel_value.
                    iIntros "$ !>". brel_pures.
                    simpl. brel_pures.
                    iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)).
                    { simpl. auto. (set_unfold; tauto). }
                    { simpl. repeat (eapply list_subseteq_skip). eapply list_subseteq_nil. }
                    { iApply "Hrel". iApply "HmQ". }
                    { iApply "IH". }
             +++ iApply brel_value.
                 iIntros "$ !>".
                 unfold kont.
                 brel_pures.
                 iApply (G_XOR_CORRECT_l m (g ^+ c)%g _ _ _ _).
                 rewrite g_log_exp.
                 brel_pures.
                 { simpl. unfold distinct in Hdistinct. destruct Hdistinct.
                   unfold distinct_l in H0. (*unfold LblClients in H1. simpl in H1.*)
                   unfold N in H0. simpl in H0.
                   repeat (rewrite -> labels_l_cons in H0).
                   (set_unfold; tauto).  }
                 {  simpl.
                    iApply (brel_na_inv _ _ alphaN); first (set_unfold; tauto).
                    iFrame "Hinvα".
                    iIntros "([ (>Hγ & (>Hl_m'sim' & (>Hl_asim & (>Hl_auth &
(>Hl_fchan' & (>Hl_rchan' & Hl_key')))))) | [>Hd2 | >Hd3]] & Hclose)".
                    (*contradiction branch as the first message has been sent and stored*)
                    - iDestruct (ghost_map_elem_agree
                                  with "Hl_fchan Hl_fchan'") as %Heq.
                      congruence.
                    - unfold d2.
                      iDestruct "Hd2" as (?m ?n) "(Hγ & (Hl_m'sim' & (Hl_sim & (Hl_auth & (Hl_fchan' & (Hl_rchan' & Hl_key'))))))".
                      iApply (brel_load_l _ _ _ [HandleCtx _ _ _ _ _ ;CaseCtx _ _] with "Hl_auth").
                      iIntros "!> Hl_auth".
                      simpl. brel_pures_l.
                      iApply (brel_load_r _ _ _ _ [CaseCtx _ _] with "Hl_sim").
                      iIntros "Hl_sim". brel_pures. simpl.
                      iApply fupd_brel.
                      iModIntro.
                      iApply brel_na_close. iFrame "Hclose".
                      iSplitL.
                      { iModIntro. iRight. iLeft. iFrame "Hγ Hl_m'sim' Hl_sim Hl_auth Hl_fchan' Hl_rchan' Hl_key'". }

                      brel_pures.
                      iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)).
                      { simpl. auto. (set_unfold; tauto). }
                      { simpl. auto. }
                      { iApply "Hrel". iApply "HmQ". }
                      { iApply "IH". }
                    - unfold d3.
                      iDestruct "Hd3" as  (?m ?n) "(Hγ & (Hl_m'sim' & (Hl_sim & (Hl_auth & (Hl_fchan' & (Hl_rchan' & Hl_key'))))))".
                      iApply (brel_load_l _ _ _ [HandleCtx _ _ _ _ _ ;CaseCtx _ _] with "Hl_auth").
                      iIntros "!> Hl_auth".
                      simpl. brel_pures_l.
                      iApply (brel_load_r _ _ _ _ [CaseCtx _ _] with "Hl_sim").
                      iIntros "Hl_sim". brel_pures. simpl.
                      iApply (brel_exp_r [AppRCtx _]). brel_pures.
                      iApply (brel_store_r _ _ _ _ [AppRCtx _] with "Hl_sim").
                      iIntros "Hl_sim". rel_pures.
                      iApply (brel_store_l _ _ _ [HandleCtx _ _ _ _ _ ; AppRCtx _] with "Hl_auth").
                      iIntros "!> Hl_auth". brel_pures.
                      iApply fupd_brel.
                      iMod (ghost_map_elem_persist with "Hl_sim") as "#Hl_sim".
                      iMod (ghost_map_elem_persist with "Hl_auth") as "#Hl_auth".
                      iDestruct "Hγ" as (ns) "(%Hfγ & Hγ)".
                      apply map_eq_nil in Hfγ. simplify_eq.
                      (* iMod (ghost_map_elem_persist with "Hγ") as "#Hγ".*)
                      iModIntro.
                      iApply brel_na_close. iFrame.
                      iSplitL; [iModIntro; iRight; iLeft; iFrame "#" |]; try auto.
                      simpl. brel_pures.
                      set (g_sem := (valgroup.g ^+ sc_coupling m c)%g).
                      iApply (brel_bind [HandleCtx _ _ _ _ _ ; AppRCtx _] [AppRCtx _] ⊤ leaktheory
                                N _ (Do leakauth1 (InjLV (vgval g_sem, bob)))
                                (Do leakauth2 (InjLV (vgval (valgroup.g ^+ f m c), bob)))).
                      { simpl. unfold leaktheory. auto.
                        iApply (traversable_ectx_labels _ _ [getKey'] [] iThyBot _).
                        + simpl. auto.
                        + unfold kont0. simpl. auto.
                        + unfold N in Hdistinct.
                          unfold keytheory, leaktheory, distinct in *.
                          unfold distinct_l, distinct_r in *.
                          unfold labels_l, labels_r in *. simpl in *.
                          destruct Hdistinct as [Hl Hr].
                          split.
                          ++ eapply (submseteq_NoDup [getKey'; leakauth1] _); try eapply Hl.
                             solve_submseteq.
                          ++ eapply (submseteq_NoDup [leakauth2] _); try eapply Hr.
                             solve_submseteq.
                      }
                      { simpl. unfold N. iApply to_iThy_le_intro'.
                        set (k1 :=  [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], iThyBot)] ++ keytheory).
                        apply (submseteq_middle leaktheory k1 (iLblSig_to_iLblThy L)). }
                      { iApply (brel_introduction' [leakauth1] [leakauth2]); try (unfold leaktheory);
                          try (apply list_elem_of_here).
                        iExists _, _, [], [],_.
                        do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
                        iSplitL;  [|by iIntros "!>" (??) "H"; iApply "H"].
                        iLeft. iLeft. simpl.
                        iExists _,_. repeat (iSplit; try (iPureIntro); try (unfold SendV); try reflexivity).
                        iModIntro. iApply brel_value. iIntros "$ !>".
                        brel_pures.
                        iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)).
                        { simpl. auto. (set_unfold; tauto). }
                        { simpl. auto. }
                        { iApply "Hrel". iApply "HmQ". }
                        { iApply "IH". }          }  }  }  }
      (* A message has already been sent by the secure channel *)
      ++ unfold d2.
         iDestruct "Hd2" as (?m ?n) "(Hγ & (Hl_m'sim & (Hl_sim & (Hl_auth & (Hl_fchan & (Hl_rchan & Hl_key))))))".
         iDestruct "Hl_fchan" as "#Hl_fchan".
         iDestruct "Hl_rchan" as "#Hl_rchan".
         iApply (brel_load_l _ _ _  [HandleCtx _ _ _ _ _ ; HandleCtx _ _ _ _ _ ; CaseCtx _ _] with "Hl_rchan").
         iIntros "!> Hl_rchan'".
         brel_pures.
         iApply (brel_load_r _ _ _ _  [HandleCtx _ _ _ _ _ ; CaseCtx _ _] with "Hl_fchan").
         iIntros "Hl_fchan'".
         brel_pures.
         iApply brel_na_close. iFrame.
         iSplitL.
         { iModIntro. iRight. iLeft. iFrame. }
         iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)).
         { simpl. auto. (set_unfold; tauto). }
         { simpl. auto. (*admit.*) }
         { iApply "Hrel". iApply "HmQ". }
         { iApply "IH". }
      ++ unfold d3.
         iDestruct "Hd3" as (?m ?n) "(Hγ & (Hl_m'sim & (Hl_sim & (Hl_auth & (Hl_fchan & (Hl_rchan & Hl_key))))))".               
         iApply (brel_load_l _ _ _  [HandleCtx _ _ _ _ _ ; HandleCtx _ _ _ _ _ ; CaseCtx _ _] with "Hl_rchan").
         iIntros "!> Hl_rchan'".
         brel_pures.
         iApply (brel_load_r _ _ _ _  [HandleCtx _ _ _ _ _ ; CaseCtx _ _] with "Hl_fchan").
         iIntros "Hl_fchan'".
         brel_pures.
         iApply brel_na_close. iFrame.
         iSplitL.
         { iModIntro. iRight. iRight. iFrame. }
         iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)).
         { simpl. auto. (set_unfold; tauto). }
         { simpl. auto. }
         { iApply "Hrel". iApply "HmQ". }
         { iApply "IH". }
    (* Bob receives the message *)
    + iDestruct "HRecvBob" as "[%He1 [%He2 #HmQ]]".
      rewrite -> He1. rewrite -> He2. brel_pures.
      { split.
        + apply -> NeutralEctx_ectx_labels_singleton.
          do 2 (eapply NeutralEctx_label_cons_inv_2 in Hk1). eapply Hk1.
        + simpl. unfold distinct in Hdist'. destruct Hdist'. unfold distinct_l in H0.
          simpl in H0.
          repeat (rewrite -> labels_l_cons in H0).
          eapply NoDup_app in H0.
          eapply NoDup_cons_1_1. destruct H0.
          eapply (submseteq_NoDup _ [channel'; getKey'; schannel_l]); [solve_submseteq | apply H0]. }
      { split.
        + apply -> NeutralEctx_ectx_labels_singleton.
          eapply NeutralEctx_label_cons_inv_2 in Hk2.
          eapply NeutralEctx_label_cons_inv_1 in Hk2. eapply Hk2.
        + simpl. (set_unfold; tauto). }
      brel_pures.
      set (keytheory := iLblSig_to_iLblThy [([keyleak1], [keyleak2], keyleak keyleak1 keyleak2)]).
      set (leaktheory := (iLblSig_to_iLblThy [([leakauth1], [leakauth2], leakauth leakauth1 leakauth2)])).
      set (M := [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)]).
      set (N := [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)] ++ keytheory ++ leaktheory ++ (iLblSig_to_iLblThy L)).
      iApply (brel_bind'' _ _ keytheory M N _ (Do keyleak1 (InjRV alice)) (Do keyleak2 (InjRV alice))).
      { simpl. unfold M. unfold labels_l. simpl. (set_unfold; tauto). }
      { simpl. unfold M. unfold labels_r. simpl. (set_unfold; tauto). }
      { iApply to_iThy_le_intro'. unfold M. unfold N.
        eapply submseteq_sublist_r.
        exists ([([channel'; getKey'; schannel_l], [leaksec'; schannel_r],
                    iThyBot)] ++ keytheory). split.
        + repeat simpl. unfold keytheory. simpl. eapply Permutation_swap.
        + set (l1 :=  [([channel'; getKey'; schannel_l], [leaksec'; schannel_r],
                          iThyBot)] ++ keytheory).
          set (l2 := leaktheory ++ iLblSig_to_iLblThy L).
          apply (sublist_inserts_r l2 l1 l1). auto. }
      {  iApply (brel_introduction' [keyleak1] [keyleak2]).
         { unfold keytheory. eapply list_elem_of_here. }
         { iExists _, _, [], [],_.
           do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
           iSplitL;  [|by iIntros "!>" (??) "H"; iApply "H"].
           iLeft. iRight. simpl.
           repeat (iSplit; try (iPureIntro); try (unfold RecvV); try reflexivity).
           iModIntro.
           (* two cases now; either keyleakrecv alice returns without a value, or it returns with a value *)
           iSplitL.
           { (* keyleak recv alice returns without a value *)
             repeat foldkont.
             iApply brel_value.
             iIntros "$ !>". brel_pures.
             iApply (brel_exhaustion (fill k1' (InjLV #()%V)) (fill k2' (InjLV #()%V))).
             { simpl. (set_unfold; tauto). }
             { simpl. (set_unfold; tauto). }
             { iApply "Hrel".  iDestruct "HmQ" as "[Hsome Hnone]". iApply "Hnone". }
             {iApply "IH". } }
           { (*keyleak alice returns with a value *)
             repeat foldkont.
             iApply brel_value. iIntros "$ !>". brel_pures.
             iApply (brel_bind'' _ _ keytheory M N _ (Do keyleak1 (InjLV alice)) (Do keyleak2 (InjLV alice))).
             { simpl. unfold M. unfold labels_l. simpl. (*apply (list_subseteq_skip channel' [] [getKey'; schannel_l]).*) (set_unfold; tauto). }
             { simpl. unfold M. unfold labels_r. simpl. (set_unfold; tauto). }
             {  iApply to_iThy_le_intro'. unfold M. unfold N. solve_submseteq. }
             iApply (brel_introduction' [keyleak1] [keyleak2]).
             1: { unfold keytheory.
                  eapply list_elem_of_here. }
             iExists _, _, [], [],_.
             do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
             iSplitL;  [|by iIntros "!>" (??) "H"; iApply "H"].
             iLeft. iLeft. simpl.
             repeat (iSplit; try (iPureIntro); try (unfold SendV); try reflexivity).
             iModIntro. iApply brel_value.
             iIntros "$ !>". brel_pures.
             { simpl. unfold distinct in Hdist'. destruct Hdist' as [Hdl HdR].
               unfold distinct_l in Hdl. unfold labels_l in Hdl. simpl in Hdl.
               assert (HNoDup : NoDup [channel'; getKey']).
               { eapply sublist_NoDup; [eapply Hdl| auto].
                 eapply (sublist_inserts_r _ [channel'; getKey'] [channel'; getKey']). auto. }
               brel_pures.
               repeat foldkont.
               (* open invariant for case analysis *)
               iApply (brel_na_inv _ _ alphaN); first (set_unfold; tauto).
               iFrame "Hinvα".
               iIntros "([(>Hγ & >Hl_m'sim & >Hl_sim & >Hl_auth & >Hl_fchan & >Hl_rchan & >Hl_key) | [>Hd2 | >Hd3 ]] & Hclose)".
               (* no message has been sent yet by the secure channel*)
               ++ iApply (brel_load_l _ _ _ [CaseCtx _ _] with "Hl_key").
                  iIntros "!> Hl_key". brel_pures.
                  iApply (brel_load_r _ _ _ _ [CaseCtx _ _] with "Hl_m'sim").
                  iIntros "Hl_m'sim". brel_pures. simpl.
                  iApply brel_na_close. iFrame.
                  iSplitL.
                  { iModIntro. iLeft. iFrame. }

                  iApply (brel_exhaustion (fill k1'(InjLV #()%V)) (fill k2' (InjLV #()%V))).
                  { simpl. auto. (set_unfold; tauto). }
                  { simpl. (set_unfold; tauto). }
                  { iApply "Hrel". iDestruct "HmQ" as "[Hsome Hnone]". iApply "Hnone".  }
                  { iApply "IH". }
               (* a message has been sent by both the secure channel and the authenticated channel *)
               ++ unfold d2.
                  iDestruct "Hd2" as (?m ?n) "(Hγ & (Hl_m'sim & (Hl_sim & (Hl_auth & (Hl_fchan & (Hl_rchan & Hl_key))))))".
                  iApply (brel_load_l _ _ _ [CaseCtx _ _] with "Hl_key").
                  iIntros "!> Hl_key". brel_pures.
                  { simpl. (set_unfold; tauto). }
                  iApply (brel_load_r _ _ _ _ [CaseCtx _ _] with "Hl_m'sim").
                  iIntros "Hl_m'sim". brel_pures. simpl.
                  repeat foldkont.
                  iApply fupd_brel.
                  iMod (ghost_map_elem_persist with "Hl_fchan") as "#Hl_fchan".
                  iMod (ghost_map_elem_persist with "Hl_rchan") as "#Hl_rchan".
                  iMod (ghost_map_elem_persist with "Hl_key") as "#Hl_key".
                  iMod (ghost_map_elem_persist with "Hl_m'sim") as "#Hl_m'sim".
                  iMod (ghost_map_elem_persist with "Hl_auth") as "#Hl_auth".
                  iMod (ghost_map_elem_persist with "Hl_sim") as "#Hl_sim".
                  iModIntro.

                  iApply brel_na_close. iFrame.
                  iSplitL.
                  { iModIntro. iRight. iLeft. iFrame "#". }
                  iApply (brel_bind'' _ _ leaktheory M N _ (Do leakauth1 (InjRV bob)) (Do leakauth2 (InjRV bob))).
                  { simpl. unfold M. unfold labels_l. simpl. (set_unfold; tauto). }
                  { simpl. unfold M. unfold labels_r. simpl. (set_unfold; tauto). }
                  {  iApply to_iThy_le_intro'. unfold M. unfold N.
                     eapply submseteq_sublist_r.
                     exists ([([channel'; getKey'; schannel_l], [leaksec'; schannel_r],
                                 iThyBot)] ++ leaktheory). split.
                     + repeat simpl. unfold leaktheory. simpl. eapply Permutation_swap.
                     + eapply sublist_skip. eapply sublist_inserts_l. eapply sublist_inserts_r. auto. }
                  { iApply (brel_introduction' [leakauth1] [leakauth2]).
                    1: { unfold leaktheory.
                         eapply list_elem_of_here. }
                    simpl.
                    iExists _, _, [], [],_.
                    do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
                    iSplitL;  [|by iIntros "!>" (??) "H"; iApply "H"].
                    iRight. iRight. simpl.
                    repeat (iSplit; try (iPureIntro); try (unfold RecvV); try reflexivity).
                    iModIntro. iSplit.
                    (* leakauth returns successfully with a value *)
                    -  iIntros (b1 b2). iApply brel_value. iIntros "$ !>".
                       brel_pures. simpl.
                       iApply (brel_load_r _ _ _ _ [AppRCtx _] with "Hl_sim").
                       iIntros "Hl_sim'".
                       iApply (brel_load_l _ _ _ [HandleCtx _ _ _ _ _ ; AppRCtx _] with "Hl_auth").
                       iIntros "!>Hl_auth'".
                       iDestruct "Hl_fchan" as "#Hl_fchan".
                       simpl. brel_pures.
                       iApply G_XOR_CORRECT_l.
                       rewrite g_log_exp.
                       brel_pures.
                       iApply (brel_load_r _ _ _ _ [HandleCtx _ _ _ _ _ ; AppRCtx _ ] with "Hl_fchan").
                       iIntros "Hl_fchan'".
                       brel_pures.
                       set (g_enc := (g ^+ sc_coupling (g ^+ f m n) n)%g).
                       iApply (brel_exhaustion (fill k1'((InjRV (vgval g_enc))%V)) (fill k2' ((InjRV (vgval m))%V))).
                       { simpl. auto. (set_unfold; tauto). }
                       { simpl. (set_unfold; tauto). }
                       { unfold kont0. iApply "Hrel". iDestruct "HmQ" as "[Hsome Hnone]". unfold g_enc. rewrite sc_coupling_invol. iApply "Hsome". }
                       { iApply "IH". }
                    (* leakauth doesnt return with a value *)
                    -  iApply brel_value. iIntros "$ !>".
                       brel_pures. simpl.
                       iApply (brel_exhaustion (fill k1' (InjLV #()%V)) (fill k2' (InjLV #()%V))).
                       { simpl. (set_unfold; tauto). }
                       { simpl. (set_unfold; tauto). }
                       { iApply "Hrel".  iDestruct "HmQ" as "[Hsome Hnone]". iApply "Hnone". }
                       {iApply "IH". } }
               (* a message has been sent by the secure channel but not the authenticated channel*)
               ++ simpl. brel_pures.
                  unfold d3.
                  iDestruct "Hd3" as (?m ?n) "(Hγ & (Hl_m'sim & (Hl_sim & (Hl_auth & (Hl_fchan & (Hl_rchan & Hl_key))))))".
                  iApply (brel_load_l _ _ _ [CaseCtx _ _] with "Hl_key").
                  iIntros "!> Hl_key". brel_pures.
                  { simpl. (set_unfold; tauto). }
                  iApply (brel_load_r _ _ _ _ [CaseCtx _ _] with "Hl_m'sim").
                  iIntros "Hl_m'sim". brel_pures. simpl.
                  repeat foldkont.
                  iApply fupd_brel.
                  iMod (ghost_map_elem_persist with "Hl_fchan") as "#Hl_fchan".
                  iMod (ghost_map_elem_persist with "Hl_rchan") as "#Hl_rchan".
                  iMod (ghost_map_elem_persist with "Hl_key") as "#Hl_key".
                  iMod (ghost_map_elem_persist with "Hl_m'sim") as "#Hl_m'sim".
                  iModIntro.

                  iApply brel_na_close. iFrame.
                  iSplitL.
                  { iModIntro. iRight. iRight. iFrame "#". iFrame. }
                  iApply (brel_bind'' _ _ leaktheory M N _ (Do leakauth1 (InjRV bob)) (Do leakauth2 (InjRV bob))).
                  { simpl. unfold M. unfold labels_l. simpl. (set_unfold; tauto). }
                  { simpl. unfold M. unfold labels_r. simpl. (set_unfold; tauto). }
                  {  iApply to_iThy_le_intro'. unfold M. unfold N.
                     eapply submseteq_sublist_r.
                     exists ([([channel'; getKey'; schannel_l], [leaksec'; schannel_r],
                                 iThyBot)] ++ leaktheory). split.
                     + repeat simpl. unfold leaktheory. simpl. eapply Permutation_swap.
                     + eapply sublist_skip. eapply sublist_inserts_l. eapply sublist_inserts_r. auto. }
                  { iApply (brel_introduction' [leakauth1] [leakauth2]).
                    1: { unfold leaktheory.
                         eapply list_elem_of_here. }
                    simpl.
                    iExists _, _, [], [],_.
                    do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
                    iSplitL;  [|by iIntros "!>" (??) "H"; iApply "H"].
                    iRight. iRight. simpl.
                    repeat (iSplit; try (iPureIntro); try (unfold RecvV); try reflexivity).
                    iModIntro. iSplit.
                    (* leakauth returns successfully with a value *)
                    -  iIntros (b1 b2). iApply brel_value. iIntros "$ !>".
                       brel_pures. simpl.
                       (*another case analysis by opening the invariant again, since we need access to the pointers l_sim and l_auth *)
                       iApply (brel_na_inv _ _ alphaN); first (set_unfold; tauto).
                       iFrame "Hinvα".
                       iIntros "([(>Hγ & >Hl_m'sim' & >Hl_sim & >Hl_auth & >Hl_fchan' & >Hl_rchan' & >Hl_key') | [>Hd2 | >Hd3 ]] & Hclose)".
                       (*contradiction branch since we already know that a message has been sent by the secure channel *)
                       -- iDestruct (ghost_map_elem_agree
                                      with "Hl_fchan Hl_fchan'") as %Heq.
                          congruence.
                       (*the next two brances will move the proof forward with a case analysis on l_auth and l_sim having been set or not *)
                       -- unfold d2.
                          iDestruct "Hd2" as (?m ?n) "(Hγ & (Hl_m'sim' & (Hl_sim & (Hl_auth & (Hl_fchan' & (Hl_rchan' & Hl_key'))))))".
                          iApply (brel_load_r _ _ _ _ [AppRCtx _] with "Hl_sim").
                          iIntros "Hl_sim".
                          iApply (brel_load_l _ _ _ [HandleCtx _ _ _ _ _ ; AppRCtx _] with "Hl_auth").
                          iIntros "!> Hl_auth".
                          iApply fupd_brel.
                          iMod (ghost_map_elem_persist with "Hl_fchan'") as "#Hl_fchan'".
                          iMod (ghost_map_elem_persist with "Hl_rchan'") as "#Hl_rchan'".
                          iMod (ghost_map_elem_persist with "Hl_key'") as "#Hl_key'".
                          iMod (ghost_map_elem_persist with "Hl_m'sim'") as "#Hl_m'sim'".
                          iMod (ghost_map_elem_persist with "Hl_auth") as "#Hl_auth".
                          iMod (ghost_map_elem_persist with "Hl_sim") as "#Hl_sim".
                          iModIntro.

                          iApply brel_na_close. iFrame.
                          iSplitL.
                          { iModIntro. iRight. iLeft. iFrame "#". }
                          simpl. brel_pures.
                          iCombine "Hl_fchan Hl_fchan'" gives %[Hval Hval2].
                          inversion Hval2. apply vgval_inj in H1. rewrite -> H1.
                          iCombine "Hl_m'sim Hl_m'sim'" gives %[Hsim Hsim2]. clear Hval Hsim.
                          inversion Hsim2. destruct (sc_coupling_bij m0) as [Hfinj Hfsurj].
                          apply Nat2Z.inj in H2.
                          apply fin_to_nat_inj in H2.
                          apply (@inj _ _ eq eq (f m0) Hfinj n n0) in H2. rewrite -> H2.

                          iApply G_XOR_CORRECT_l.
                          rewrite g_log_exp.
                          brel_pures.
                          iApply (brel_load_r _ _ _ _ [HandleCtx _ _ _ _ _ ; AppRCtx _ ] with "Hl_fchan").
                          iIntros "Hl_fchan''".
                          brel_pures.
                          set (g_enc := (g ^+ sc_coupling (g ^+ f m0 n0) n0)%g).
                          iApply (brel_exhaustion (fill k1'((InjRV (vgval g_enc))%V)) (fill k2' ((InjRV (vgval m0))%V))).
                          { simpl. auto. (set_unfold; tauto). }
                          { simpl. (set_unfold; tauto). }
                          { unfold kont0. iApply "Hrel". iDestruct "HmQ" as "[Hsome Hnone]". unfold xor. unfold g_enc.
                            rewrite sc_coupling_invol. iApply "Hsome". }
                          { iApply "IH". }
                       -- unfold d3.
                          iDestruct "Hd3" as (?m ?n) "(Hγ & (Hl_m'sim' & (Hl_sim & (Hl_auth & (Hl_fchan' & (Hl_rchan' & Hl_key'))))))".
                          iApply (brel_load_r _ _ _ _ [AppRCtx _] with "Hl_sim").
                          iIntros "Hl_sim".
                          iApply (brel_load_l _ _ _ [HandleCtx _ _ _ _ _ ; AppRCtx _] with "Hl_auth").
                          iIntros "!> Hl_auth".
                          iApply fupd_brel.
                          iMod (ghost_map_elem_persist with "Hl_fchan'") as "#Hl_fchan'".
                          iMod (ghost_map_elem_persist with "Hl_rchan'") as "#Hl_rchan'".
                          iMod (ghost_map_elem_persist with "Hl_key'") as "#Hl_key'".
                          iMod (ghost_map_elem_persist with "Hl_m'sim'") as "#Hl_m'sim'".
                          iModIntro.

                          iApply brel_na_close. iFrame.
                          iSplitL.
                          { iModIntro. iRight. iRight. iFrame "#". iFrame. }
                          simpl. brel_pures.
                          iApply (brel_exhaustion (fill k1' (InjLV #()%V)) (fill k2' (InjLV #()%V))).
                          { simpl. (set_unfold; tauto). }
                          { simpl. (set_unfold; tauto). }
                          { iApply "Hrel".  iDestruct "HmQ" as "[Hsome Hnone]". iApply "Hnone". }
                          {iApply "IH". }
                    (* leakauth doesnt return with a value *)
                    -  iApply brel_value. iIntros "$ !>".
                       brel_pures. simpl.
                       iApply (brel_exhaustion (fill k1' (InjLV #()%V)) (fill k2' (InjLV #()%V))).
                       { simpl. (set_unfold; tauto). }
                       { simpl. (set_unfold; tauto). }
                       { iApply "Hrel".  iDestruct "HmQ" as "[Hsome Hnone]". iApply "Hnone". }
                       {iApply "IH". } } } } } }
  Qed.
*)
  (* end of commented-out F_OAUTH_CHAN_SIM *)


  Lemma SEM_R_CHAN_SIM (f1 f2 : val) (L : sem_row Σ) :
    (∀ᵣ θₕ, (((sem_ty_nat -{ θₕ }-> 𝟙) × (𝟙 -{ θₕ }-> Option 𝔾)) -{ sem_row_union θₕ L }-∘ 𝟙))%T
      f1 f2 -∗
    BREL R_CHAN f1
      ≤ CHAN_SIM_lazy (F_CHAN f2) <|⊥|> {{λ v1 v2,
                                            (∀ᵣ θ₁, ∀ᵣ θ₂,  (((𝔾 × (𝟙 + 𝟙)) -{ θ₁ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ₁ }-> Option 𝟙)) ⊸ (((𝟙 + 𝟙) -{ θ₂ }-> 𝟙) ×(𝟙 + 𝟙) -{ θ₂ }-> Option 𝟙) -{ sem_row_union θ₁ (sem_row_union θ₂ L) }-∘ 𝟙)%T v1 v2 }}. 
  Proof with (repeat foldkont; brel_pures') using G H XOR_spec0 cg vg vgg xor_struct Σ.
    iIntros "Hrelf1f2".
    unfold R_CHAN, right_composition, CHAN, F_CHAN, CHAN_SIM_lazy...
    iIntros "!>" (autheff keyeff autheff_l autheff_r) "Hautheff".
    iDestruct "Hautheff" as (asnd_l asnd_r arcv_l arcv_r) "(%H1al & %H2al & (#Hasnd & #Harcv))"...
    iIntros "!>" (keyeff_l keyeff_r) "Hkeyeff".
    iDestruct "Hkeyeff" as (kysnd_l kysnd_r kyrcv_l kyrcv_r) "(%H1k & %H2k & (#Hkeysnd & #Hkeyrcv))".
    rewrite H1al. rewrite H2al. rewrite H1k. rewrite H2k.
    unfold F_OAUTH, F_KE_lazy_alice...

    brel_alloc_r l_sim as "Hl_sim"...
    brel_alloc_r l_m'sim as "Hl_m'sim"...
    brel_alloctape_l γ as "Hγ"...
    brel_alloc_l l_key as "Hl_key"...
    brel_effect_l getKey' as "HgK"...
    brel_effect_r lsend' as "Hlsend"...
    brel_effect_r lrecv' as "Hlrecv"...
    brel_alloc_l l_auth as "Hl_auth"...
    brel_effect_l csend' as "Hcsend"...
    brel_effect_l crecv' as "Hcrecv"...
    brel_alloc_r l_fchan as "Hlfchan"...
    brel_effect_r ssend_r as "Hssend_r"...
    brel_effect_r srecv_r as "Hsrecv_r"...
    brel_alloc_l l_rchan as "Hlrchan"...
    brel_effect_l ssend_l as "Hssend_l"...
    brel_effect_l srecv_l as "Hsrecv_l"...
    rewrite Nat2Z.id.

    set (kl1 := ( match: "payload" with
                    InjL "m" =>
                      match: ! #l_rchan with
                        InjL <> =>
                          #l_rchan <- InjR "m";;
                          let: "key" := (λ: "party", do: getKey' "party")%V bob in
                          match: "key" with
                            InjL <> => "k" #()%V
                          | InjR "x" =>
                              match: G_XOR xor "m" "x" with
                                InjL <> => "k" #()%V
                              | InjR "mg" =>
                                  (λ: "m", do: csend' "m")%V ("mg", bob);; "k" #()%V
                              end
                          end
                      | InjR "m" => "k" #()%V
                      end
                  | InjR <> =>
                      let: "key" := (λ: "party", do: getKey' "party")%V alice in
                      match: "key" with
                        InjL <> => "k" (InjLV #()%V)
                      | InjR "key" =>
                          let: "r" := (λ: "m", do: crecv' "m")%V bob in
                          match: "r" with
                            InjL <> => "k" (InjLV #()%V)
                          | InjR "x" =>
                              match: G_XOR xor "x" "key" with
                                InjL <> => "k" (InjL #()%V)
                              | InjR "mg" => "k" (InjR "mg")
                              end
                          end
                      end
                  end )%E ).
    (* F_OAUTH's single [channel] handler is now two handlers, so its old
       continuation body [kl2] splits into [kl2s] (send) and [kl2r] (recv). *)
    set (kl2s := ( let: "dst" := "payload" in
                   let: "m" := Fst "dst" in
                   let: "dst" := Snd "dst" in
                   match: ! #l_auth with
                     InjL <> => #l_auth <- InjR "m";; asnd_l ("m", "dst");; "k" #()%V
                   | InjR "message" => "k" #()%V
                   end )%E).
    set (kl2r := ( let: "r" := arcv_l "from" in
                   match: "r" with
                     InjL <> => "k" (InjLV #()%V)
                   | InjR "x" => "k" ! #l_auth
                   end )%E).
    set (kl3 := ( match: "p" with
                    InjL <> =>
                      let: "key" := (λ: <>,
                                       match: ! #l_key with
                                         InjL <> =>
                                           let: "c" := #();; rand(#lbl:γ) #(S n'') in
                                           let: "key" := vexp g "c" in
                                           #l_key <- InjR "key";; "key"
                                       | InjR "key" => "key"
                                       end)%V
                                      #()%V in
                      kysnd_l bob;;
                      let: "r" := kyrcv_l bob in
                      match: "r" with
                        InjL <> => "k" (InjLV #()%V)
                      | InjR "w" => "k" (InjR "key")
                      end
                  | InjR <> =>
                      let: "r" := kyrcv_l alice in
                      match: "r" with
                        InjL <> => "k" (InjLV #()%V)
                      | InjR "w" =>
                          kysnd_l alice;;
                          match: ! #l_key with
                            InjL <> => "k" (InjLV #()%V)
                          | InjR "key" => "k" (InjR "key")
                          end
                      end
                  end )%E).
    set (kr1 := ( match: "payload" with
                    InjL "m" =>
                      match: ! #l_fchan with
                        InjL <> =>
                          #l_fchan <- InjR "m";;
                          (λ: "m", do: lsend' "m")%V alice;; "k" #()%V
                      | InjR "x" => "k" #()%V
                      end
                  | InjR <> =>
                      let: "r" := (λ: "m", do: lrecv' "m")%V bob in
                      match: "r" with
                        InjL <> => "k" (InjLV #()%V)
                      | InjR "x" => "k" (InjR ! #l_fchan)
                      end
                  end )%E).
    set (kr2 := ( match: "payload" with
                    InjL <> =>
                      let: "m'" := (λ: <>,
                                      match: ! #l_m'sim with
                                        InjL <> =>
                                          let: "m'" := #();; rand #(S n'') in
                                          #l_m'sim <- InjR "m'";; "m'"
                                      | InjR "m'" => "m'"
                                      end)%V
                                     #()%V in
                      kysnd_r bob;;
                      let: "r" := kyrcv_r bob in
                      match: "r" with
                        InjL <> => "k" (InjLV #()%V)
                      | InjR "x" =>
                          match: ! #l_sim with
                            InjL <> =>
                              let: "mA" := vexp g "m'" in
                              #l_sim <- InjR "m'";; asnd_r ("mA", bob);; "k" #()%V
                          | InjR "m" => "k" #()%V
                          end
                      end
                  | InjR <> =>
                      let: "r" := kyrcv_r alice in
                      match: "r" with
                        InjL <> => "k" (InjLV #()%V)
                      | InjR "x" =>
                          kysnd_r alice;;
                          match: ! #l_m'sim with
                            InjL <> => "k" (InjLV #()%V)
                          | InjR "_" =>
                              let: "rla" := arcv_r bob in
                              match: "rla" with
                                InjL <> => "k" (InjLV #()%V)
                              | InjR "x" => "k" ! #l_sim
                              end
                          end
                      end
                  end )%E).
    set (θ := client_row csend' crecv' lsend' lrecv' getKey' ssend_l srecv_l ssend_r srecv_r).
    iSpecialize ("Hrelf1f2" $! θ).
    unfold sem_ty_arr, sem_ty_mbang. simpl.
    iAssert (sem_val_typed  ((λ: "m", do: ssend_l "m"), (λ: <>, do: srecv_l bob))%V ((λ: "m", do: ssend_r "m") , (λ: <>, do: srecv_r bob))%V (((sem_ty_nat -{ θ }-> 𝟙) × (𝟙 -{ θ }-> (Option 𝔾)))%T)) as "Hschn".
    { iApply SEM_TYPED_EFF. }
    unfold sem_val_typed. simpl.
    iDestruct "Hschn" as "#Hschn".
    iSpecialize ("Hrelf1f2" with "Hschn"). simpl.
    set (f m := sc_coupling m).
    set (d1 := (γ ↪N (S n''; []) ∗ l_m'sim ↦ₛ NONEV ∗ l_sim ↦ₛ NONEV ∗ l_auth ↦ NONEV ∗ l_fchan ↦ₛ NONEV ∗ l_rchan ↦ NONEV ∗  l_key ↦ NONEV)%I).
    set (d2 := ((∃ m : vgG, ∃ n : fin (S (S n'')), γ ↪N (S n''; []) ∗ l_m'sim ↦ₛ□ SOMEV #(f m n) ∗ l_sim ↦ₛ□ SOMEV #(f m n) ∗
                                                   l_auth ↦□ SOMEV (vgval
                                                                      (g ^+ f m n))%V ∗  l_fchan ↦ₛ□ SOMEV (vgval m) ∗  l_rchan ↦□ SOMEV (vgval m) ∗ l_key ↦□ SOMEV (vgval (g ^+n)))%I)).

    set (d3 := (∃ m : vgG, ∃ n : fin (S (S n'')), γ ↪N (S n''; []) ∗ l_m'sim ↦ₛ□ SOMEV #(f m n) ∗ l_sim ↦ₛ NONEV ∗ l_auth ↦ NONEV ∗ l_fchan ↦ₛ□ SOMEV (vgval m) ∗  l_rchan ↦□ SOMEV (vgval m) ∗ l_key ↦□ SOMEV (vgval (g ^+n)))%I).
    iApply (brel_na_alloc (d1 ∨ (d2 ∨ d3))%I alphaN).
    iSplitL "Hγ Hl_m'sim Hl_sim Hl_auth Hlfchan Hlrchan Hl_key"; [iNext; iLeft; iFrame|].
    iIntros "#Hinvα".
    iApply brel_new_theory.
    iApply (brel_add_label_l with "Hssend_l").
    iApply (brel_add_label_l with "Hsrecv_l").
    iApply (brel_add_label_r with "Hssend_r").
    iApply (brel_add_label_r with "Hsrecv_r").
    iApply (brel_add_label_l with "HgK").
    iApply (brel_add_label_l with "Hcrecv").
    iApply (brel_add_label_l with "Hcsend").
    iApply (brel_add_label_r with "Hlsend").
    iApply (brel_add_label_r with "Hlrecv").
    set (X :=  iLblSig_to_iLblThy [([srecv_l; ssend_l] , [srecv_r; ssend_r] , sec_channel ssend_l ssend_r srecv_l srecv_r)]).
    set (R := (λ u1 u2 : val, 𝟙%T u1 u2)).
    set (X' := sec_channel ssend_l ssend_r srecv_l srecv_r).
    iApply brel_learn. iIntros "%Hdist' _".
    (* Splitting F_OAUTH's [channel] and CHAN/F_CHAN's [schannel] into two
       handlers each makes [brel_pures] emit label-freshness side goals
       ([crecv' ∉ [csend']], [lrecv' ∉ [lsend']], ...) at every reduction
       that crosses one of the new handlers.  Derive the FULL pairwise
       distinctness of each side's label list once from [Hdist']; every such
       goal then closes with the [set_unfold; tauto] already in the script. *)
    assert (NoDup [csend'; crecv'; getKey'; srecv_l; ssend_l]) as Hnd_l.
    { unfold distinct in Hdist'. destruct Hdist' as [Hd' _].
      unfold distinct_l in Hd'. simpl in Hd'.
      repeat (rewrite -> labels_l_cons in Hd').
      try (eapply NoDup_app in Hd'; destruct Hd' as [Hd' _]).
      eapply (submseteq_NoDup [csend'; crecv'; getKey'; srecv_l; ssend_l] _) in Hd'; [|solve_submseteq]. exact Hd'. }
    assert (NoDup [lrecv'; lsend'; srecv_r; ssend_r]) as Hnd_r.
    { unfold distinct in Hdist'. destruct Hdist' as [_ Hd'].
      unfold distinct_r in Hd'. simpl in Hd'.
      repeat (rewrite -> labels_r_cons in Hd').
      try (eapply NoDup_app in Hd'; destruct Hd' as [Hd' _]).
      eapply (submseteq_NoDup [lrecv'; lsend'; srecv_r; ssend_r] _) in Hd'; [|solve_submseteq]. exact Hd'. }
    iApply ((brel_exhaustion (f1 ((λ: "m", do: ssend_l "m"),(λ: <>, do: srecv_l bob))%V) (f2 ((λ: "m", do: ssend_r "m"),(λ: <>, do: srecv_r bob))%V) _ _ X' _ _ R _ _ _) with "[Hrelf1f2]").
    { simpl. (set_unfold; tauto). }
    { simpl. (set_unfold; tauto). }
    {
      set clt := ([csend'; crecv'; getKey'; srecv_l; ssend_l], [lrecv'; lsend'; srecv_r; ssend_r], X').
      set cltheory := iLblSig_to_iLblThy [([csend'; crecv'; getKey'; srecv_l; ssend_l] , [lrecv'; lsend'; srecv_r; ssend_r] , X')].
      set (L' := cltheory ++ (iLblSig_to_iLblThy L)).
      set (keytheory := keyeff).
      set (leaktheory := autheff).
      set (M := cltheory ++ (iLblSig_to_iLblThy (sem_row_union leaktheory (sem_row_union keytheory L)))).
      iApply (brel_introduction_mono L' M).
      + simpl.
        iApply to_iThy_le_intro'.
        unfold L'. unfold M.
        set (ρ__c := (sem_row_union leaktheory (sem_row_union keytheory L))).
        apply (submseteq_skips_l cltheory (iLblSig_to_iLblThy L) (iLblSig_to_iLblThy ρ__c)).
        unfold ρ__c. unfold sem_row_union. repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app).
        solve_submseteq.
      + unfold L'. unfold cltheory. simpl. iApply "Hrelf1f2". }
    iLöb as "IH".
    unfold kl1.
    iSplit; [iIntros (v1 v2) "%Hv1v2"; iModIntro; brel_pures; iModIntro; done |].
    iIntros (?????) "!# %Hk1 %Hk2 HXQ #Hrel".
    iDestruct "HXQ" as "[HSendAlice | HRecvBob]".
    (* Send a message using the secure channel from Alice To Bob *)
    + iDestruct "HSendAlice" as (?mz) "[[-> ->] #HmQ]"...
      {  apply -> NeutralEctx_ectx_labels_singleton.
         do 3 (eapply NeutralEctx_label_cons_inv_2 in Hk2). eapply Hk2. }
      { apply -> NeutralEctx_ectx_labels_singleton.
        do 4 (eapply NeutralEctx_label_cons_inv_2 in Hk1). eapply Hk1. }

      (* Interpreting a group element from mz *)
      destruct (vg_of_int_sem mz) as [m|] eqn:Hmz .
      2 : {
        iApply brel_vg_of_int_none_l; first done.
        iApply brel_vg_of_int_none_r; first done...
        iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V));
          [(set_unfold; tauto)|done|by iApply "Hrel"|iApply "IH"]. }
      
      iApply brel_vg_of_int_correct_l; first done.
      iApply brel_vg_of_int_correct_r; first done...

      iApply (brel_na_inv _ _ alphaN); first (set_unfold; tauto).
      iFrame "Hinvα".
      iIntros "([(>Hγ & >Hl_m'sim & >Hl_sim & >Hl_auth & >Hl_fchan & >Hl_rchan & >Hl_key) | [>Hd2 | >Hd3 ]] & Hclose)".
      (* First message to be sent by the secure channel*)
      ++
        iApply (brel_load_r _ _ _ _ [HandleCtx _ _ _ _ _ ; HandleCtx _ _ _ _ _ ; HandleCtx _ _ _ _ _ ; CaseCtx _ _] with "Hl_fchan").
        iIntros "Hl_fchan".
        brel_load_l...
        brel_store_r... 1 : rewrite !NoDup_cons in Hnd_l, Hnd_r; (set_unfold; tauto). 
        brel_store_l...
        { eapply NoDup_cons_1_1.
          eapply (submseteq_NoDup _ [csend'; crecv'; getKey'; srecv_l; ssend_l]); [solve_submseteq | exact Hnd_l]. }
        brel_load_l...
        brel_load_r...
        iApply (brel_couple_TU _ _ (f m) [HandleCtx _ _ _ _ _ ; AppRCtx _; AppRCtx _] _ _ _ _ _ _); simpl; auto.
        iSplitL "Hγ". { iDestruct "Hγ" as (ms) "(%Hf' & Hγ)". apply map_eq_nil in Hf'. simplify_eq. iModIntro ; iFrame "Hγ". }
        iIntros (c) "Hγ"...
        (* TODO: fix fin/nat tapes *)
        iApply (brel_randT_l _ [AppRCtx _ ; AppRCtx _] γ _ _ _ _); auto.
        simpl. iSplitL "Hγ"; [iFrame "Hγ"; auto |].
        iModIntro. iIntros "Hγ %Hc"...
        brel_store_l...
        brel_store_r...

        iApply fupd_brel.
        iMod (ghost_map_elem_persist with "Hl_fchan") as "#Hl_fchan".
        iMod (ghost_map_elem_persist with "Hl_rchan") as "#Hl_rchan".
        iMod (ghost_map_elem_persist with "Hl_key") as "#Hl_key".
        iMod (ghost_map_elem_persist with "Hl_m'sim") as "#Hl_m'sim".
        iModIntro.
        iApply brel_na_close. iFrame.
        iSplitL.
        { iModIntro. iRight. iRight. unfold d3.  iExists m, c.
          iFrame "#". iFrame. }
        set (keytheory := keyeff).
        set (leaktheory := autheff).
        set (M := [([csend'; crecv'; getKey'; srecv_l; ssend_l], [lrecv'; lsend'; srecv_r; ssend_r], @iThyBot Σ)] ++ (iLblSig_to_iLblThy (sem_row_union leaktheory L))).
        set (N := [([csend'; crecv'; getKey'; srecv_l; ssend_l], [lrecv'; lsend'; srecv_r; ssend_r], @iThyBot Σ)] ++ (iLblSig_to_iLblThy (sem_row_union leaktheory (sem_row_union keytheory L)))).
        iApply (brel_bind'' [ AppRCtx _] [HandleCtx _ _ _ _ _ ; AppRCtx _] (iLblSig_to_iLblThy keytheory) M N (𝟙%T) (kysnd_l bob) (kysnd_r bob)).
        { simpl. (set_unfold; tauto). }
        { simpl. (set_unfold; tauto). }
        { simpl. unfold M. unfold N. iApply to_iThy_le_intro'.
          unfold sem_row_union. repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app).
          solve_submseteq. }
        {
          iApply (brel_wand _ _ _  R _ ).
          { iDestruct "Hkeysnd" as "#Hkeysnd".
            iSpecialize ("Hkeysnd" $! bob bob).
            iApply "Hkeysnd".
            { unfold sem_ty_sum, sem_ty_unit. unfold bob. iExists #()%V, #()%V.
              iLeft. repeat (iSplit); try (iPureIntro); try reflexivity. } }
          iModIntro. iIntros (v1 v2) "#HRv1v2"...
          iApply (brel_bind'' _ _ (iLblSig_to_iLblThy keytheory) M N 𝟙%T (kyrcv_l bob) (kyrcv_r bob)).
          { simpl. unfold M.  repeat (rewrite -> labels_l_cons). (set_unfold; tauto). }
          { simpl. unfold M. repeat (rewrite -> labels_r_cons). (set_unfold; tauto). }
          { simpl. unfold M. unfold N. iApply to_iThy_le_intro'.
            unfold sem_row_union. repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app).
            solve_submseteq. }
          iApply brel_wand.
          { iDestruct "Hkeyrcv" as "#Hkeyrcv".
            iSpecialize ("Hkeyrcv" $! bob bob).
            iApply "Hkeyrcv".
            { unfold bob. unfold sem_ty_sum. iExists #()%V, #()%V.
              repeat iSplit; try (iPureIntro); try reflexivity; try (left); repeat split;
                try reflexivity. } }
          iModIntro. iIntros (v0 v3) "#Hv0v3".
          unfold sem_ty_group, sem_ty_option, sem_ty_sum.
          iDestruct "Hv0v3" as (?w1 ?w2) "#Hv0v3".
          (* keyleak recv returns succesfully or not *)
          iDestruct "Hv0v3" as "[Hnone | Hsome]".
          ++ iDestruct "Hnone" as "(->&->&->&->)"...
             iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)).
             { simpl. auto. (set_unfold; tauto). }
             { simpl. repeat (eapply list_subseteq_skip). eapply list_subseteq_nil. }
             { iApply "Hrel". iApply "HmQ". }
             { iApply "IH". }
          ++ iDestruct "Hsome" as "(->&->&->&->)"...
             iApply G_XOR_CORRECT_l...
             { eapply NoDup_cons_1_1.
               eapply (submseteq_NoDup _ [csend'; crecv'; getKey'; srecv_l; ssend_l]); [solve_submseteq | exact Hnd_l]. }
             iApply (brel_na_inv _ _ alphaN); first (set_unfold; tauto).
             iFrame "Hinvα".
             iIntros "([ (>Hγ & (>Hl_m'sim' & (>Hl_sim' & (>Hl_auth & (>Hl_fchan' & (>Hl_rchan' & Hl_key')))))) | [>Hd2 | >Hd3]] & Hclose)".
          (*contradiction branch as the first message has been sent and stored*)
          - iDestruct (ghost_map_elem_agree
                        with "Hl_fchan Hl_fchan'") as %Heq.
            congruence.
          - unfold d2.
            iDestruct "Hd2" as (?m ?n) "(Hγ & (Hl_m'sim' & (Hl_sim & (Hl_auth & (Hl_fchan' & (Hl_rchan' & Hl_key'))))))".
            iApply (brel_load_l _ _ _ [HandleCtx _ _ _ _ _ ; HandleCtx _ _ _ _ _ ;CaseCtx _ _] with "Hl_auth").
            iIntros "!> Hl_auth"...
            brel_load_r...

            iApply fupd_brel.
            iModIntro.
            iApply brel_na_close. iFrame "Hclose".
            iSplitL...
            { iModIntro. iRight. iLeft. iFrame. }

            iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)).
            { (set_unfold; tauto). }
            { done. }
            { iApply "Hrel". iApply "HmQ". }
            { iApply "IH". }
          - iDestruct "Hd3" as (?m ?n) "(Hγ & (Hl_m'sim' & (Hl_sim & (Hl_auth & (Hl_fchan' & (Hl_rchan' & Hl_key'))))))".
            iApply (brel_load_l _ _ _ [HandleCtx _ _ _ _ _ ; HandleCtx _ _ _ _ _ ;CaseCtx _ _] with "Hl_auth").
            iIntros "!> Hl_auth"...
            brel_load_r...
            brel_store_r...
            brel_store_l...

            iApply fupd_brel.
            iMod (ghost_map_elem_persist with "Hl_sim") as "#Hl_sim".
            iMod (ghost_map_elem_persist with "Hl_auth") as "#Hl_auth".
            iDestruct "Hγ" as (ns) "(%Hfγ & Hγ)".
            apply map_eq_nil in Hfγ. simplify_eq.
            iModIntro.
            iApply brel_na_close. iFrame.
            iSplitL; [iModIntro; iRight; iLeft; rewrite g_log_exp; iFrame "#" |]; try auto...
            set (g_sem := (g ^+ sc_coupling m c)%g).
            unfold kl3.
            set (hbranchleft := (λ: "p" "k",
                                   match: "p" with
                                     InjL <> =>
                                       let: "key" := (λ: <>,
                                                        match: ! #l_key with
                                                          InjL <> =>
                                                            let: "c" :=
                                                              #();; rand(#lbl:γ) #(S n'') in
                                                            let: "key" :=
                                                              vexp valgroup.g "c" in
                                                            #l_key <- InjR "key";; "key"
                                                        | InjR "key" => "key"
                                                        end)%V
                                                       #()%V in
                                       kysnd_l bob;;
                                       let: "r" := kyrcv_l bob in
                                       match: "r" with
                                         InjL <> => "k" (InjLV #()%V)
                                       | InjR "w" => "k" (InjR "key")
                                       end
                                   | InjR <> =>
                                       let: "r" := kyrcv_l alice in
                                       match: "r" with
                                         InjL <> => "k" (InjLV #()%V)
                                       | InjR "w" =>
                                           kysnd_l alice;;
                                           match: ! #l_key with
                                             InjL <> => "k" (InjLV #()%V)
                                           | InjR "key" => "k" (InjR "key")
                                           end
                                       end
                                   end)%E).

            iPoseProof (brel_bind [HandleCtx Deep MS getKey' hbranchleft (λ: "y", "y"); HandleCtx _ _ _ _ _ ; AppRCtx (λ: <>, kont3 #()%V)]
                          [HandleCtx _ _ _ _ _ ; AppRCtx (λ: <>, kont1 #()%V)]
                          ⊤ (iLblSig_to_iLblThy leaktheory) N  𝟙%T
                          (asnd_l (vgval g_sem, bob))%V
                          (asnd_r (vgval (valgroup.g ^+ f m c), bob))%V) as "Hbind".
            rewrite g_log_exp...
            iApply "Hbind".
            { simpl. unfold leaktheory. auto.
              iApply (traversable_ectx_labels _ _ [crecv'; getKey'] [lrecv'] iThyBot _).
              + set_unfold; tauto.
              + set_solver. 
              + simpl.
                unfold sem_row_union in Hdist'.
                unfold distinct in *.
                unfold distinct_l, distinct_r in *.
                unfold labels_l, labels_r in *.
                destruct Hdist' as [Hl Hr].
                split.
                ++
                  set (l1 := (concat  (([crecv'; getKey'], [lrecv'], iThyBot) :: iLblSig_to_iLblThy autheff).*1.*1)).
                  eapply (submseteq_NoDup l1 _); try eapply Hl.
                  unfold l1. simpl. eapply submseteq_cons. do 2 eapply submseteq_skip.
                  repeat (rewrite -> iLblSig_to_iLblThy_proj;
                          rewrite -> iLblSig_to_iLblThy_app).
                  repeat (rewrite -> fmap_app). simpl. do 2 apply submseteq_cons.
                  eapply concat_submseteq. simpl. solve_submseteq.
                ++ set (l2 := (concat (([crecv'; getKey'], [lrecv'], iThyBot)
                                         :: iLblSig_to_iLblThy autheff).*1.*2)).
                   eapply (submseteq_NoDup l2 _); try eapply Hr.
                   unfold l2. simpl. eapply submseteq_skip. do 3 eapply submseteq_cons.
                   repeat (rewrite -> iLblSig_to_iLblThy_proj;
                           rewrite -> iLblSig_to_iLblThy_app).
                   repeat (rewrite -> fmap_app). simpl.
                   eapply concat_submseteq. simpl. solve_submseteq.
            }
            { simpl. unfold N. iApply to_iThy_le_intro'.
              unfold sem_row_union. repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app).
              solve_submseteq. }
            {  iApply (brel_wand _ _ _ R _).
               {  iDestruct "Hasnd" as "#Hasnd".
                  iSpecialize ("Hasnd" $! (vgval g_sem, bob)%V).
                  iSpecialize ("Hasnd" $! (vgval (valgroup.g ^+ f m c), bob)%V).
                  iApply "Hasnd".
                  unfold g_sem. simpl. unfold sem_ty_prod.
                  iExists _, (vgval (valgroup.g ^+ f m c)), bob, bob.
                  repeat (iSplit); try (iPureIntro); try reflexivity.
                  + auto. simpl. unfold f. by eexists. 
                  + simpl. exists #()%V, #()%V. 
                    by left. }
               iModIntro. iIntros (v0 v3) "(->&->)"...

               iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)).
               { set_unfold; tauto. }
               { done. }
               { iApply "Hrel". iApply "HmQ". }
               { iApply "IH". } } }

      (* A message has already been sent by the secure channel *)
      ++ iDestruct "Hd2" as (?m ?n) "(Hγ & (Hl_m'sim & (Hl_sim & (Hl_auth & (Hl_fchan & (#Hl_rchan & Hl_key))))))".
         iApply (brel_load_l _ _ _  [HandleCtx _ _ _ _ _; HandleCtx _ _ _ _ _ ; HandleCtx _ _ _ _ _ ; HandleCtx _ _ _ _ _ ; CaseCtx _ _] with "Hl_rchan").
         iIntros "!> Hl_rchan'"...
         brel_load_r...
         iApply brel_na_close. iFrame.
         iSplitL.
         { iModIntro. iRight. iLeft. iFrame. }
         iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)); [set_solver|done|iApply "Hrel";iApply"HmQ"|iApply "IH"].
      ++ iDestruct "Hd3" as (?m ?n) "(Hγ & (Hl_m'sim & (Hl_sim & (Hl_auth & (Hl_fchan & (Hl_rchan & Hl_key))))))".                
         iApply (brel_load_l _ _ _  [HandleCtx _ _ _ _ _; HandleCtx _ _ _ _ _ ; HandleCtx _ _ _ _ _ ; HandleCtx _ _ _ _ _ ; CaseCtx _ _] with "Hl_rchan").
         iIntros "!> Hl_rchan'"...
         brel_load_r...
         iApply brel_na_close. iFrame.
         iSplitL.
         { iModIntro. do 2 iRight. iFrame. }
         iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)); [set_solver|done|iApply "Hrel";iApply"HmQ"|iApply "IH"].

    + iDestruct "HRecvBob" as "[-> [-> #HmQ]]"...
      { split.
        + apply -> NeutralEctx_ectx_labels_singleton.
          do 2 (eapply NeutralEctx_label_cons_inv_2 in Hk2).
          eapply NeutralEctx_label_cons_inv_1 in Hk2. 
          eapply HandleCtx_NeutralEctx; last eapply Hk2.
          unfold distinct in Hdist'. destruct Hdist'. unfold distinct_r in H0.
          simpl in H0.
          repeat (rewrite -> labels_r_cons in H0).
          eapply NoDup_app in H0.
          eapply NoDup_cons_1_1. destruct H0.
          eapply (submseteq_NoDup _ [lrecv'; lsend'; srecv_r; ssend_r]); [solve_submseteq | done].
        + simpl. rewrite !NoDup_cons in Hnd_l, Hnd_r; (set_unfold; tauto). }
      { split.
        + apply -> NeutralEctx_ectx_labels_singleton.
          do 3 (eapply NeutralEctx_label_cons_inv_2 in Hk1). 
          eapply NeutralEctx_label_cons_inv_1 in Hk1. 
          eapply HandleCtx_NeutralEctx; last eapply Hk1.
          eapply NoDup_cons_1_1.
            eapply (submseteq_NoDup _ [csend'; crecv'; getKey'; srecv_l; ssend_l]); [solve_submseteq | exact Hnd_l].
        + simpl. eapply NoDup_cons_1_1.
          eapply (submseteq_NoDup _ [csend'; crecv'; getKey'; srecv_l; ssend_l]); [solve_submseteq | exact Hnd_l].
      }

      set (keytheory := keyeff).
      set (leaktheory := autheff).
      set (M := [([csend'; crecv'; getKey'; srecv_l; ssend_l], [lrecv'; lsend'; srecv_r; ssend_r], @iThyBot Σ)]).
      set (N := [([csend'; crecv'; getKey'; srecv_l; ssend_l], [lrecv'; lsend'; srecv_r; ssend_r], @iThyBot Σ)] ++
                  iLblSig_to_iLblThy (sem_row_union keytheory (sem_row_union leaktheory L)))...
      set (leftkontbind := ( match: "r" with
                               InjL <> => kont (InjLV #()%V)
                             | InjR "w" =>
                                 kysnd_l alice;;
                                 match: ! #l_key with
                                   InjL <> => kont (InjLV #()%V)
                                 | InjR "key" => kont (InjR "key")
                                 end
                             end )%E).
      set (rightkontbind := ( match: "r" with
                                InjL <> => kont0 (InjLV #()%V)
                              | InjR "x" =>
                                  kysnd_r alice;;
                                  match: ! #l_m'sim with
                                    InjL <> => kont0 (InjLV #()%V)
                                  | InjR "_" =>
                                      let: "rla" := arcv_r bob in
                                      match: "rla" with
                                        InjL <> => kont0 (InjLV #()%V)
                                      | InjR "x" => kont0 ! #l_sim
                                      end
                                  end
                              end )%E)...
      iApply (brel_bind'' _ _  (iLblSig_to_iLblThy (keytheory))  [([csend'; crecv'; getKey'; srecv_l; ssend_l], [lrecv'; lsend'; srecv_r; ssend_r], @iThyBot Σ)] (([csend'; crecv'; getKey'; srecv_l; ssend_l], [lrecv'; lsend'; srecv_r; ssend_r], iThyBot)
                                                                                                                                            :: iLblSig_to_iLblThy (sem_row_union leaktheory (sem_row_union keytheory L))) (𝟙%T) (kyrcv_l alice) (kyrcv_r alice)).
      { set_solver. }
      { set_solver. }
      { iApply to_iThy_le_intro'. unfold sem_row_union. repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app). solve_submseteq. }
      iApply brel_wand.
      {  iDestruct "Hkeyrcv" as "#Hkeyrcv".
         iSpecialize ("Hkeyrcv" $! alice alice).
         iApply "Hkeyrcv". unfold sem_ty_sum, sem_ty_unit.
         iExists #()%V, #()%V. unfold alice.
         repeat (iSplit); try (iPureIntro); try reflexivity.
         right. repeat split; try reflexivity. }
      iModIntro. iIntros (v1 v2) "#Hv1v2". brel_pures.
      unfold sem_ty_group, sem_ty_option, sem_ty_sum.
      iDestruct "Hv1v2" as (?w1 ?w2) "[#Hnone | #Hsome]".
    (*key receive didnt return successfully*)
    - iDestruct "Hnone" as "(->&->&->&->)"...
      iApply (brel_exhaustion (fill k1' _) (fill k2' _)); [set_solver|done|iApply "Hrel"; iDestruct "HmQ" as "(_&$)"|iApply "IH"].
    (*key receive returned successfully*)
    - iDestruct "Hsome" as "(->&->&->&->)"...
      set (rightapp := ( match: "rla" with
                           InjL <> => kont0 (InjLV #()%V)
                         | InjR "x" => kont0 ! #l_sim
                         end)%E).
      iApply (brel_bind'' _ _ (iLblSig_to_iLblThy keytheory)  [([csend'; crecv'; getKey'; srecv_l; ssend_l], [lrecv'; lsend'; srecv_r; ssend_r], @iThyBot Σ)] ([([csend'; crecv'; getKey'; srecv_l; ssend_l], [lrecv'; lsend'; srecv_r; ssend_r], @iThyBot Σ)] ++
                                                                                                                                         iLblSig_to_iLblThy (sem_row_union leaktheory (sem_row_union keytheory L))) 𝟙%T (kysnd_l alice) (kysnd_r alice)).
      { set_solver. }
      { set_unfold; tauto. }
      { iApply to_iThy_le_intro'. unfold sem_row_union. repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app). solve_submseteq. }
      iApply brel_wand.
      { iDestruct "Hkeysnd" as "#Hkeysnd".
        iSpecialize ("Hkeysnd" $! alice alice).
        iApply "Hkeysnd".
        iExists #()%V, #()%V. unfold alice.
        iRight. repeat (iSplit); try (iPureIntro); try reflexivity. }
      iIntros "!>" (v0 v3) "(->&->)"...
      iApply (brel_na_inv _ _ alphaN); first (set_unfold; tauto).
      iFrame "Hinvα".
      iIntros "([(>Hγ & >Hl_m'sim & >Hl_sim & >Hl_auth & >Hl_fchan & >Hl_rchan & >Hl_key) | [>Hd2 | >Hd3 ]] & Hclose)".
      (* no message has been sent yet by the secure channel*)
      ++ iApply (brel_load_l _ _ _ [CaseCtx _ _] with "Hl_key").
         iIntros "!> Hl_key"... 
         brel_load_r...
         iApply brel_na_close. iFrame.
         iSplitL.
         { iModIntro. iLeft. iFrame. }
         iApply (brel_exhaustion (fill k1' _) (fill k2' _)); [set_solver|done|iApply "Hrel"; iDestruct "HmQ" as "(_&$)"|iApply "IH"].
      (* a message has been sent by both the secure channel and the authenticated channel *)
      ++ iDestruct "Hd2" as (?m ?n) "(Hγ & (Hl_m'sim & (Hl_sim & (Hl_auth & (Hl_fchan & (Hl_rchan & Hl_key))))))".
         iApply (brel_load_l _ _ _ [CaseCtx _ _] with "Hl_key").
         iIntros "!> Hl_key"...
         { eapply NoDup_cons_1_1.
           eapply (submseteq_NoDup _ [csend'; crecv'; getKey'; srecv_l; ssend_l]); [solve_submseteq | exact Hnd_l]. }
         brel_load_r...

         iApply fupd_brel.
         iMod (ghost_map_elem_persist with "Hl_fchan") as "#Hl_fchan".
         iMod (ghost_map_elem_persist with "Hl_rchan") as "#Hl_rchan".
         iMod (ghost_map_elem_persist with "Hl_key") as "#Hl_key".
         iMod (ghost_map_elem_persist with "Hl_m'sim") as "#Hl_m'sim".
         iMod (ghost_map_elem_persist with "Hl_auth") as "#Hl_auth".
         iMod (ghost_map_elem_persist with "Hl_sim") as "#Hl_sim".
         iModIntro.

         iApply brel_na_close. iFrame.
         iSplitL.
         { iModIntro. iRight. iLeft. iFrame "#". }
         iApply (brel_bind'' _ _  (iLblSig_to_iLblThy leaktheory)  [([csend'; crecv'; getKey'; srecv_l; ssend_l], [lrecv'; lsend'; srecv_r; ssend_r], @iThyBot Σ)] ([([csend'; crecv'; getKey'; srecv_l; ssend_l], [lrecv'; lsend'; srecv_r; ssend_r], @iThyBot Σ)] ++
                                                                                                                                              iLblSig_to_iLblThy (sem_row_union leaktheory (sem_row_union keytheory L))) 𝟙%T (arcv_l bob) (arcv_r bob)).
         { set_unfold; tauto. }
         { set_unfold; tauto. }
         { iApply to_iThy_le_intro'. unfold sem_row_union. repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app). solve_submseteq. }

         iApply brel_wand.
         { iDestruct "Harcv" as "#Harcv".
           iSpecialize ("Harcv" $! bob bob).
           iApply "Harcv".
           iExists #()%V, #()%V. unfold bob.
           iLeft. repeat (iSplit); try (iPureIntro); try reflexivity. }
         iIntros "!>" (v4 v5) "(%w0&%w3&[Hnone|Hsome])".
         +++ (* leakauth doesnt return successfully *)
           iDestruct "Hnone" as "(->&->&->&->)"...
           iApply (brel_exhaustion (fill k1' (InjLV #()%V)) (fill k2' (InjLV #()%V))); [set_solver|done|iApply "Hrel"; iDestruct "HmQ" as "(_&$)"|iApply "IH"].
         +++ (* leakauth returns successfully with a value *)
           iDestruct "Hsome" as "(-> & -> & -> & ->)"...
           brel_load_r.
           brel_load_l...
           iDestruct "Hl_fchan" as "#Hl_fchan".
           iApply G_XOR_CORRECT_l. rewrite g_log_exp...
           brel_load_r...
           rewrite sc_coupling_invol.
           iApply (brel_exhaustion (fill k1'((InjRV (vgval m))%V)) (fill k2' ((InjRV (vgval m)))%V)); [set_unfold;tauto|done| |].
           { iApply "Hrel". iDestruct "HmQ" as "[Hsome Hnone]". iApply "Hsome". }
           { iApply "IH". }
      (* a message has been sent by the secure channel but not the authenticated channel*)
      ++ iDestruct "Hd3" as (?m ?n) "(Hγ & (Hl_m'sim & (Hl_sim & (Hl_auth & (Hl_fchan & (Hl_rchan & Hl_key))))))"...
         iApply (brel_load_l _ _ _ [CaseCtx _ _] with "Hl_key").
         iIntros "!> Hl_key"...
         { eapply NoDup_cons_1_1.
           eapply (submseteq_NoDup _ [csend'; crecv'; getKey'; srecv_l; ssend_l]); [solve_submseteq | exact Hnd_l]. }
         brel_load_r...

         iApply fupd_brel.
         iMod (ghost_map_elem_persist with "Hl_fchan") as "#Hl_fchan".
         iMod (ghost_map_elem_persist with "Hl_rchan") as "#Hl_rchan".
         iMod (ghost_map_elem_persist with "Hl_key") as "#Hl_key".
         iMod (ghost_map_elem_persist with "Hl_m'sim") as "#Hl_m'sim".
         iModIntro.

         iApply brel_na_close. iFrame.
         iSplitL.
         { iModIntro. iRight. iRight. iFrame "#". iFrame. }
         iApply (brel_bind'' _ _  (iLblSig_to_iLblThy leaktheory)  [([csend'; crecv'; getKey'; srecv_l; ssend_l], [lrecv'; lsend'; srecv_r; ssend_r], @iThyBot Σ)] ([([csend'; crecv'; getKey'; srecv_l; ssend_l], [lrecv'; lsend'; srecv_r; ssend_r], @iThyBot Σ)] ++
                                                                                                                                              iLblSig_to_iLblThy (sem_row_union leaktheory (sem_row_union keytheory L))) 𝟙%T (arcv_l bob) (arcv_r bob)); [set_solver|set_solver| | ].
         { iApply to_iThy_le_intro'. unfold sem_row_union. repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app). solve_submseteq. }

         iApply brel_wand.
         { iDestruct "Harcv" as "#Harcv".
           iSpecialize ("Harcv" $! bob bob).
           iApply "Harcv".
           iExists #()%V, #()%V. unfold bob.
           iLeft. repeat (iSplit); try (iPureIntro); try reflexivity. }
         iIntros "!>" (v4 v5) "(%w0&%w3&[Hnone|Hsome])".
         (* leakauth doesnt return successfully *)
         +++ iDestruct "Hnone" as "(->&->&->&->)"...
             iApply (brel_exhaustion (fill k1' _) (fill k2' _)); [set_unfold;tauto|done|iApply "Hrel"; iDestruct "HmQ" as "(_&$)"|iApply "IH"].
         (* leakauth returns successfully with a value *)
         +++ iDestruct "Hsome" as "(->&->&->&->)"...
             (*another case analysis by opening the invariant again, since we need access to the pointers l_sim and l_auth *)
             iApply (brel_na_inv _ _ alphaN); first (set_unfold; tauto).
             iFrame "Hinvα".
             iIntros "([(>Hγ & >Hl_m'sim' & >Hl_sim & >Hl_auth & >Hl_fchan' & >Hl_rchan' & >Hl_key') | [>Hd2 | >Hd3 ]] & Hclose)".
      (*contradiction branch since we already know that a message has been sent by the secure channel *)
      -- iDestruct (ghost_map_elem_agree
                     with "Hl_fchan Hl_fchan'") as %Heq.
         congruence.
      (*the next two brances will move the proof forward with a case analysis on l_auth and l_sim having been set or not *)
      -- iDestruct "Hd2" as (?m ?n) "(Hγ & (Hl_m'sim' & (Hl_sim & (Hl_auth & (Hl_fchan' & (Hl_rchan' & Hl_key'))))))".
         iApply (brel_load_r _ _ _ _ [AppRCtx _] with "Hl_sim").
         iIntros "Hl_sim".
         brel_load_l.
         iApply fupd_brel.
         iMod (ghost_map_elem_persist with "Hl_fchan'") as "#Hl_fchan'".
         iMod (ghost_map_elem_persist with "Hl_rchan'") as "#Hl_rchan'".
         iMod (ghost_map_elem_persist with "Hl_key'") as "#Hl_key'".
         iMod (ghost_map_elem_persist with "Hl_m'sim'") as "#Hl_m'sim'".
         iMod (ghost_map_elem_persist with "Hl_auth") as "#Hl_auth".
         iMod (ghost_map_elem_persist with "Hl_sim") as "#Hl_sim".
         iModIntro.

         iApply brel_na_close. iFrame.
         iSplitL...
         { iModIntro. iRight. iLeft. iFrame "#". }
         iCombine "Hl_fchan Hl_fchan'" gives %[Hval Hval2].
         inversion Hval2. apply vgval_inj in H1. rewrite -> H1.
         iCombine "Hl_m'sim Hl_m'sim'" gives %[Hsim Hsim2]. clear Hval Hsim.
         inversion Hsim2.
         iApply G_XOR_CORRECT_l. rewrite g_log_exp. 
         apply Nat2Z.inj in H2.
         rewrite -H2. rewrite sc_coupling_invol...
         brel_load_r...
         iApply (brel_exhaustion (fill k1'((InjRV (vgval m0))%V)) (fill k2' ((InjRV (vgval m0)))%V)); [set_unfold;tauto|set_solver| |].
         { iApply "Hrel". by iDestruct "HmQ" as "[Hsome Hnone]". }
         { iApply "IH". }
      -- iDestruct "Hd3" as (?m ?n) "(Hγ & (Hl_m'sim' & (Hl_sim & (Hl_auth & (Hl_fchan' & (Hl_rchan' & Hl_key'))))))".
         iApply (brel_load_r _ _ _ _ [AppRCtx _] with "Hl_sim").
         iIntros "Hl_sim".
         brel_load_l. 
         iApply fupd_brel.
         iMod (ghost_map_elem_persist with "Hl_fchan'") as "#Hl_fchan'".
         iMod (ghost_map_elem_persist with "Hl_rchan'") as "#Hl_rchan'".
         iMod (ghost_map_elem_persist with "Hl_key'") as "#Hl_key'".
         iMod (ghost_map_elem_persist with "Hl_m'sim'") as "#Hl_m'sim'".
         iModIntro.

         iApply brel_na_close. iFrame.
         iSplitL...
         { iModIntro. iRight. iRight. iFrame "#". iFrame. }
         iApply (brel_exhaustion (fill k1' (InjLV #()%V)) (fill k2' (InjLV #()%V))); [set_unfold; tauto|set_solver| |].
         { iApply "Hrel".  iDestruct "HmQ" as "[Hsome Hnone]". iApply "Hnone". }
         { iApply "IH". }
  Qed.


  Lemma SEM_R_CHAN_SIM_rev (f1 f2 : val) (L : sem_row Σ) :
    (∀ᵣ θₕ, (((sem_ty_nat -{ θₕ }-> 𝟙) × (𝟙 -{ θₕ }-> Option 𝔾)) -{ sem_row_union θₕ L }-∘ 𝟙))%T
      f1 f2 -∗
    BREL CHAN_SIM_lazy (F_CHAN f1)
      ≤ (R_CHAN f2) <|⊥|> {{λ v1 v2,
                              (∀ᵣ θ₁, ∀ᵣ θ₂,  (((𝔾 × (𝟙 + 𝟙)) -{ θ₁ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ₁ }-> Option 𝟙)) ⊸ (((𝟙 + 𝟙) -{ θ₂ }-> 𝟙) ×(𝟙 + 𝟙) -{ θ₂ }-> Option 𝟙) -{ sem_row_union θ₁ (sem_row_union θ₂ L) }-∘ 𝟙)%T v1 v2 }}.
  Proof with (repeat foldkont; brel_pures') using G H XOR_spec0 cg vg vgg xor_struct Σ.
    iIntros "Hrelf1f2".  
    unfold R_CHAN, right_composition, CHAN, F_CHAN, CHAN_SIM_lazy...

    iModIntro. 
    iIntros (autheff keyeff autheff_l autheff_r) "Hautheff".
    iDestruct "Hautheff" as (asnd_l asnd_r arcv_l arcv_r) "(%H1al & %H2al & (#Hasnd & #Harcv))"...
    iModIntro.
    iIntros (keyeff_l keyeff_r) "Hkeyeff".
    iDestruct "Hkeyeff" as (kysnd_l kysnd_r kyrcv_l kyrcv_r) "(%H1k & %H2k & (#Hkeysnd & #Hkeyrcv))".
    rewrite H1al. rewrite H2al. rewrite H1k. rewrite H2k.
    unfold F_OAUTH, F_KE_lazy_alice...

    brel_alloc_l l_sim as "Hl_sim"...
    brel_alloc_l l_m'sim as "Hl_m'sim"...
    brel_alloctape_r γ as "Hγ"...
    brel_alloc_r l_key as "Hl_key"...
    iApply brel_effect_r. iIntros (getKey') "HgK !>"... 
    (* CHAN_SIM_lazy now binds two labels: [lsend] first, then [lrecv]. *)
    iApply brel_effect_l. iIntros (lsend') "!> Hlsend !>".
    iApply brel_effect_l. iIntros (lrecv') "!> Hlrecv !>"...
    brel_alloc_r l_auth as "Hl_auth"...

    (* F_OAUTH now binds two labels: [send] first, then [recv]. *)
    iApply brel_effect_r. iIntros (csend') "Hcsend !>".
    iApply brel_effect_r. iIntros (crecv') "Hcrecv !>"...
        
    brel_alloc_l l_fchan as "Hlfchan"...
    iApply brel_effect_l. iIntros (ssend_l) "!> Hssend_l !>"...
    iApply brel_effect_l. iIntros (srecv_l) "!> Hsrecv_l !>"...
    brel_alloc_r l_rchan as "Hlrchan"...
    iApply brel_effect_r. iIntros (ssend_r) "Hssend_r !>".
    iApply brel_effect_r. iIntros (srecv_r) "Hsrecv_r !>"...
    set (kl1 := ( match: "payload" with
                    InjL "m" =>
                      match: ! #l_rchan with
                        InjL <> =>
                          #l_rchan <- InjR "m";; 
                          let: "key" := (λ: "party", do: getKey' "party")%V bob in
                          match: "key" with
                            InjL <> => "k" #()%V
                          | InjR "x" =>
                              match: G_XOR xor "m" "x" with
                                InjL <> => "k" #()%V
                              | InjR "mg" =>
                                  (λ: "m", do: csend' "m")%V ("mg", bob);; "k" #()%V
                              end
                          end
                      | InjR "m" => "k" #()%V
                      end
                  | InjR <> =>
                      let: "key" := (λ: "party", do: getKey' "party")%V alice in
                      match: "key" with
                        InjL <> => "k" (InjLV #()%V)
                      | InjR "key" =>
                          let: "r" := (λ: "m", do: crecv' "m")%V bob in
                          match: "r" with
                            InjL <> => "k" (InjLV #()%V)
                          | InjR "x" =>
                              match: G_XOR xor "x" "key" with
                                InjL <> => "k" (InjL #()%V)
                              | InjR "mg" => "k" (InjR "mg")
                              end
                          end
                      end
                  end )%E ).
    set (kl2 := ( match: "payload" with
                    InjL "payload" =>
                      let: "dst" := "payload" in
                      let: "m" := Fst "dst" in
                      let: "dst" := Snd "dst" in
                      match: ! #l_auth with
                        InjL <> => #l_auth <- InjR "m";; asnd_l ("m", "dst");; "k" #()%V
                      | InjR "message" => "k" #()%V
                      end
                  | InjR "from" =>
                      let: "r" := arcv_l "from" in
                      match: "r" with
                        InjL <> => "k" (InjLV #()%V)
                      | InjR "x" => "k" ! #l_auth
                      end
                  end )%E).
    set (kl3 := ( match: "p" with
                    InjL <> =>
                      let: "key" := (λ: <>,
                                       match: ! #l_key with
                                         InjL <> =>
                                           let: "c" := #();; rand(#lbl:γ) #(S n'') in
                                           let: "key" := vexp g "c" in
                                           #l_key <- InjR "key";; "key"
                                       | InjR "key" => "key"
                                       end)%V
                                      #()%V in
                      kysnd_l bob;; 
                      let: "r" := kyrcv_l bob in
                      match: "r" with
                        InjL <> => "k" (InjLV #()%V)
                      | InjR "w" => "k" (InjR "key")
                      end
                  | InjR <> =>
                      let: "r" := kyrcv_l alice in
                      match: "r" with
                        InjL <> => "k" (InjLV #()%V)
                      | InjR "w" =>
                          kysnd_l alice;; 
                          match: ! #l_key with
                            InjL <> => "k" (InjLV #()%V)
                          | InjR "key" => "k" (InjR "key")
                          end
                      end
                  end )%E).
    set (kr1 := ( match: "payload" with
                    InjL "m" =>
                      match: ! #l_fchan with
                        InjL <> =>
                          #l_fchan <- InjR "m";; 
                          (λ: "m", do: lsend' "m")%V alice;; "k" #()%V
                      | InjR "x" => "k" #()%V
                      end
                  | InjR <> =>
                      let: "r" := (λ: "m", do: lrecv' "m")%V bob in
                      match: "r" with
                        InjL <> => "k" (InjLV #()%V)
                      | InjR "x" => "k" (InjR ! #l_fchan)
                      end
                  end )%E).
    set (kr2 := ( match: "payload" with
                    InjL <> =>
                      let: "m'" := (λ: <>,
                                      match: ! #l_m'sim with
                                        InjL <> =>
                                          let: "m'" := #();; rand #(S n'') in
                                          #l_m'sim <- InjR "m'";; "m'"
                                      | InjR "m'" => "m'"
                                      end)%V
                                     #()%V in
                      kysnd_r bob;; 
                      let: "r" := kyrcv_r bob in
                      match: "r" with
                        InjL <> => "k" (InjLV #()%V)
                      | InjR "x" =>
                          match: ! #l_sim with
                            InjL <> =>
                              let: "mA" := vexp g "m'" in
                              #l_sim <- InjR "m'";; asnd_r ("mA", bob);; "k" #()%V
                          | InjR "m" => "k" #()%V
                          end
                      end
                  | InjR <> =>
                      let: "r" := kyrcv_r alice in
                      match: "r" with
                        InjL <> => "k" (InjLV #()%V)
                      | InjR "x" =>
                          kysnd_r alice;; 
                          match: ! #l_m'sim with
                            InjL <> => "k" (InjLV #()%V)
                          | InjR "_" =>
                              let: "rla" := arcv_r bob in
                              match: "rla" with
                                InjL <> => "k" (InjLV #()%V)
                              | InjR "x" => "k" ! #l_sim
                              end
                          end
                      end
                  end )%E).
    set (θ := client_row' csend' crecv' lsend' lrecv' getKey' ssend_l srecv_l ssend_r srecv_r).
    iSpecialize ("Hrelf1f2" $! θ).
    unfold sem_ty_arr, sem_ty_mbang. simpl.
    iAssert (sem_val_typed  ((λ: "m", do: ssend_l "m"), (λ: <>, do: srecv_l bob))%V ((λ: "m", do: ssend_r "m") , (λ: <>, do: srecv_r bob))%V (((sem_ty_nat -{ θ }-> 𝟙) × (𝟙 -{ θ }-> (Option 𝔾)))%T)) as "Hschn".
    { iApply SEM_TYPED_EFF. }
    unfold sem_val_typed. simpl.
    iDestruct "Hschn" as "#Hschn".
    iSpecialize ("Hrelf1f2" with "Hschn"). simpl.
    set (f m := (fun (x : nat) =>
                   match (decide (x < S (S n'')))%nat with
                   | left H => fin_to_nat (sc_coupling m (nat_to_fin H))
                   | right _ => x
                   end )).
    assert (Hf : ∀ m : vgG, @Bij nat nat (f m)).
    { intro m. split. 
      - intros x y Hxy. unfold f in Hxy.
        case_decide as Hx; case_decide as Hy. 
        + apply fin_to_nat_inj in Hxy.
          apply (inj _) in Hxy. apply (f_equal fin_to_nat) in Hxy. 
          by rewrite !fin_to_nat_to_fin in Hxy. 
        + pose proof (fin_to_nat_lt (sc_coupling m (nat_to_fin Hx))) as Hlt.
          rewrite Hxy in Hlt. lia. 
        + pose proof (fin_to_nat_lt (sc_coupling m (nat_to_fin Hy))) as Hlt.
          rewrite -Hxy in Hlt. lia.
        + done.
      - intros z. unfold f.
        destruct (decide (z < S (S n''))%nat) as [Hz | Hz].
        + destruct (surj (sc_coupling m) (nat_to_fin Hz)) as [i Hi].
          exists (fin_to_nat i).
          case_decide as Hi'; [| pose proof (fin_to_nat_lt i); lia].
          rewrite -(fin_to_nat_to_fin _ _ Hz).
          rewrite -Hi. by rewrite nat_to_fin_to_nat.
        + exists z. case_decide; [lia | reflexivity].
    }
    set (d1 := (γ ↪ₛN (S n''; []) ∗ l_m'sim ↦ NONEV ∗ l_sim ↦ NONEV ∗ l_auth ↦ₛ NONEV ∗ l_fchan ↦ NONEV ∗ l_rchan ↦ₛ NONEV ∗  l_key ↦ₛ NONEV)%I).
    set (d2 := ((∃ m : vgG, ∃ n : nat, ∃ Hfm : (f m n < S (S n''))%nat, γ ↪ₛN (S n''; []) ∗ l_m'sim ↦□ SOMEV #n ∗ l_sim ↦□ SOMEV #n ∗
                                                                        l_auth ↦ₛ□ SOMEV (vgval
                                                                                            ((g ^+(sc_coupling m (nat_to_fin Hfm)))%g))%V ∗  l_fchan ↦□ SOMEV (vgval m) ∗  l_rchan ↦ₛ□ SOMEV (vgval m) ∗ l_key ↦ₛ□ SOMEV (vgval (g ^+(f m n))))%I)).

    set (d3 := (∃ m : vgG, ∃ n : nat, γ ↪ₛN (S n''; []) ∗ l_m'sim ↦□ SOMEV #n ∗ l_sim ↦ NONEV ∗ l_auth ↦ₛ NONEV ∗ l_fchan ↦□ SOMEV (vgval m) ∗  l_rchan ↦ₛ□ SOMEV (vgval m) ∗ l_key ↦ₛ□ SOMEV (vgval (g ^+(f m n))))%I). 
    iApply (brel_na_alloc (d1 ∨ (d2 ∨ d3))%I alphaN).
    iSplitL "Hγ Hl_m'sim Hl_sim Hl_auth Hlfchan Hlrchan Hl_key"; [iNext; iLeft; rewrite Nat2Z.id; iFrame|].
    { iPureIntro. auto. }
    iIntros "#Hinvα".
    iApply brel_new_theory.
    iApply (brel_add_label_l with "Hssend_l").
    iApply (brel_add_label_l with "Hsrecv_l").
    iApply (brel_add_label_r with "Hssend_r").
    iApply (brel_add_label_r with "Hsrecv_r").
    iApply (brel_add_label_r with "HgK").
    iApply (brel_add_label_r with "Hcrecv").
    iApply (brel_add_label_r with "Hcsend").
    iApply (brel_add_label_l with "Hlsend").
    iApply (brel_add_label_l with "Hlrecv").
    set (X :=  iLblSig_to_iLblThy [([srecv_l; ssend_l] , [srecv_r; ssend_r] , sec_channel ssend_l ssend_r srecv_l srecv_r)]).
    set (R := (λ u1 u2 : val, 𝟙%T u1 u2)).
    set (X' := sec_channel ssend_l ssend_r srecv_l srecv_r).
    iApply brel_learn. iIntros "%Hdist' _".
    (* Splitting F_OAUTH's [channel] and CHAN/F_CHAN's [schannel] into two
       handlers each makes [brel_pures] emit label-freshness side goals
       ([crecv' ∉ [csend']], [lrecv' ∉ [lsend']], ...) at every reduction
       that crosses one of the new handlers.  Derive the FULL pairwise
       distinctness of each side's label list once from [Hdist']; every such
       goal then closes with the [set_unfold; tauto] already in the script. *)
    assert (NoDup [lrecv'; lsend'; srecv_l; ssend_l]) as Hnd_l.
    { unfold distinct in Hdist'. destruct Hdist' as [Hd' _].
      unfold distinct_l in Hd'. simpl in Hd'.
      repeat (rewrite -> labels_l_cons in Hd').
      try (eapply NoDup_app in Hd'; destruct Hd' as [Hd' _]).
      eapply (submseteq_NoDup [lrecv'; lsend'; srecv_l; ssend_l] _) in Hd'; [|solve_submseteq]. exact Hd'. }
    assert (NoDup [csend'; crecv'; getKey'; srecv_r; ssend_r]) as Hnd_r.
    { unfold distinct in Hdist'. destruct Hdist' as [_ Hd'].
      unfold distinct_r in Hd'. simpl in Hd'.
      repeat (rewrite -> labels_r_cons in Hd').
      try (eapply NoDup_app in Hd'; destruct Hd' as [Hd' _]).
      eapply (submseteq_NoDup [csend'; crecv'; getKey'; srecv_r; ssend_r] _) in Hd'; [|solve_submseteq]. exact Hd'. }
    iApply ((brel_exhaustion (f1 ((λ: "m", do: ssend_l "m"),(λ: <>, do: srecv_l bob))%V) (f2 ((λ: "m", do: ssend_r "m"),(λ: <>, do: srecv_r bob))%V) _ _ X' _ _ R _ _ _) with "[Hrelf1f2]").
    {  simpl. (set_unfold; tauto). }
    { simpl. (set_unfold; tauto). }   
    {
      set clt := ([lrecv'; lsend'; srecv_l; ssend_l], [csend'; crecv'; getKey'; srecv_r; ssend_r], X').
      set cltheory := iLblSig_to_iLblThy [([lrecv'; lsend'; srecv_l; ssend_l] , [csend'; crecv'; getKey'; srecv_r; ssend_r] , X')].
      set (L' := cltheory ++ (iLblSig_to_iLblThy L)).
      set (keytheory := keyeff).
      set (leaktheory := autheff).
      set (M := cltheory ++ (iLblSig_to_iLblThy (sem_row_union leaktheory (sem_row_union keytheory L)))).
      iApply (brel_introduction_mono L' M).
      + simpl.
        iApply to_iThy_le_intro'.
        unfold L'. unfold M.
        set (ρ__c := (sem_row_union leaktheory (sem_row_union keytheory L))).
        apply (submseteq_skips_l cltheory (iLblSig_to_iLblThy L) (iLblSig_to_iLblThy ρ__c)).
        unfold ρ__c. unfold sem_row_union. repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app).
        solve_submseteq.
      + unfold L'. unfold cltheory. simpl. iApply "Hrelf1f2". } 
    iLöb as "IH".
    unfold kl1.
    iSplit; [iIntros (v1 v2) "%Hv1v2"; iModIntro; brel_pures; iModIntro; done |].  
    iIntros (?????) "!# %Hk1 %Hk2 HXQ #Hrel".  
    iDestruct "HXQ" as "[HSendAlice | HRecvBob]". 
    (* Send a message using the secure channel from Alice To Bob *)
    + iDestruct "HSendAlice" as (?mz) "[[%He1 %He2] #HmQ]".
      rewrite -> He1. rewrite -> He2. brel_pures.
      { apply -> NeutralEctx_ectx_labels_singleton.
        do 3 (eapply NeutralEctx_label_cons_inv_2 in Hk1).
        eapply Hk1. }
      {  apply -> NeutralEctx_ectx_labels_singleton.
         do 4 (eapply NeutralEctx_label_cons_inv_2 in Hk2). eapply Hk2. } 

      (* Interpreting a group element from mz *)
      destruct (vg_of_int_sem mz) as [m|] eqn:Hmz .
      2 : {
        iApply brel_vg_of_int_none_l; first done.
        iApply brel_vg_of_int_none_r; first done.
        brel_pures'. 
        iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V));
          [done|(set_unfold; tauto)|by iApply "Hrel"|iApply "IH"]. }
      
      iApply brel_vg_of_int_correct_l; first done.
      iApply brel_vg_of_int_correct_r; first done.
      brel_pures'. 

      iApply (brel_na_inv _ _ alphaN); first (set_unfold; tauto).
      iFrame "Hinvα".
      iIntros "([(>Hγ & >Hl_m'sim & >Hl_sim & >Hl_auth & >Hl_fchan & >Hl_rchan & >Hl_key) | [>Hd2 | >Hd3 ]] & Hclose)".
      (* First message to be sent by the secure channel*)
      ++ 
        iApply (brel_load_l _ _ _ [HandleCtx _ _ _ _ _; HandleCtx _ _ _ _ _ ; HandleCtx _ _ _ _ _ ; CaseCtx _ _] with "Hl_fchan").
        iIntros "!>Hl_fchan".
        brel_load_r...
        brel_store_l...
        { simpl. rewrite !NoDup_cons in Hnd_l, Hnd_r; set_unfold; tauto. }
        brel_store_r...
        { eapply NoDup_cons_1_1.
          eapply (submseteq_NoDup _ [csend'; crecv'; getKey'; srecv_r; ssend_r]); [solve_submseteq | exact Hnd_r]. }
        brel_load_r...
        brel_load_l...
        iDestruct "Hγ" as (ms) "(%Hf' & Hγ)". apply map_eq_nil in Hf'. simplify_eq.
        iApply (brel_couple_UT _ _ (f m) [HandleCtx _ _ _ _ _ ; AppRCtx _; AppRCtx _] _ _ _ _ _ _).
        1: auto.
        { intros. unfold f. case_decide as Hn.
          + apply fin_to_nat_lt.
          + contradiction. }
        iFrame "Hγ". simpl. iSplit => //. iIntros (c ?) "!> Hγ"...
        brel_store_l...
        brel_rand_r as "%Hc"...
        iApply (brel_exp_r [AppRCtx _ ; AppRCtx _] _ _ _ g (f m c) _)...
        brel_store_r...
        
        iApply fupd_brel.
        iMod (ghost_map_elem_persist with "Hl_fchan") as "#Hl_fchan".
        iMod (ghost_map_elem_persist with "Hl_rchan") as "#Hl_rchan".
        iMod (ghost_map_elem_persist with "Hl_key") as "#Hl_key".
        iMod (ghost_map_elem_persist with "Hl_m'sim") as "#Hl_m'sim".
        iModIntro.
        iApply brel_na_close. iFrame.
        iSplitL.
        { iModIntro. iRight. iRight. unfold d3.  iExists m, c.
          iFrame "Hγ Hl_m'sim Hl_sim Hl_auth Hl_fchan Hl_rchan Hl_key". }
        set (keytheory := keyeff).
        set (leaktheory := autheff).
        set (M := [([lrecv'; lsend'; srecv_l; ssend_l], [csend'; crecv'; getKey'; srecv_r; ssend_r], @iThyBot Σ)] ++ (iLblSig_to_iLblThy (sem_row_union leaktheory L))).
        set (N := [([lrecv'; lsend'; srecv_l; ssend_l], [csend'; crecv'; getKey'; srecv_r; ssend_r], @iThyBot Σ)] ++ (iLblSig_to_iLblThy (sem_row_union leaktheory (sem_row_union keytheory L)))).
        brel_pures'.
        iApply (brel_bind'' [ HandleCtx _ _ _ _ _ ; AppRCtx _] [AppRCtx _] (iLblSig_to_iLblThy keytheory) M N (𝟙%T) (kysnd_l bob) (kysnd_r bob)).
        { set_unfold; tauto. }
        { set_unfold; tauto. }
        { simpl. unfold M. unfold N. iApply to_iThy_le_intro'. 
          unfold sem_row_union. repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app).
          solve_submseteq. }
        {
          iApply (brel_wand _ _ _  R _ ).
          { iDestruct "Hkeysnd" as "#Hkeysnd".
            iSpecialize ("Hkeysnd" $! bob bob).
            iApply "Hkeysnd".
            { unfold sem_ty_sum, sem_ty_unit. unfold bob. iExists #()%V, #()%V.
              iLeft. repeat (iSplit); try (iPureIntro); try reflexivity. } }
          iModIntro. iIntros (v1 v2) "#HRv1v2".
          brel_pures'.
          iApply (brel_bind'' _ _ (iLblSig_to_iLblThy keytheory) M N 𝟙%T (kyrcv_l bob) (kyrcv_r bob)).
          { set_unfold; tauto. }
          { simpl. apply list_subseteq_nil. }
          { simpl. unfold M. unfold N. iApply to_iThy_le_intro'.
            unfold sem_row_union. repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app).
            solve_submseteq. }
          iApply brel_wand.
          { iDestruct "Hkeyrcv" as "#Hkeyrcv".
            iSpecialize ("Hkeyrcv" $! bob bob).
            iApply "Hkeyrcv".
            { unfold bob. unfold sem_ty_sum. iExists #()%V, #()%V.
              repeat iSplit; try (iPureIntro); try reflexivity; try (left); repeat split;
                try reflexivity. } }
          iModIntro. iIntros (v0 v3) "#Hv0v3".
          unfold sem_ty_group, sem_ty_option, sem_ty_sum.
          iDestruct "Hv0v3" as (?w1 ?w2) "#Hv0v3".
          (* keyleak recv returns succesfully or not *)
          iDestruct "Hv0v3" as "[Hnone | Hsome]".
          ++ iDestruct "Hnone" as "(%Hv0 & (%Hv3 & Hw1w2))".
             rewrite -> Hv0. rewrite -> Hv3. unfold sem_ty_unit.
             iDestruct "Hw1w2" as "(%Hw1 & %Hw2)".
             rewrite -> Hw1. rewrite -> Hw2.
             brel_pures'.
             iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)). 
             { simpl. auto. }
             { simpl. set_unfold; tauto. }
             { iApply "Hrel". iApply "HmQ". }
             { iApply "IH". }
          ++ iDestruct "Hsome" as "(%Hv0 & (%Hv3 &Hw1w2))".
             rewrite -> Hv0. rewrite -> Hv3.
             unfold sem_ty_unit.
             iDestruct "Hw1w2" as "(%Hw1 & %Hw2)".
             rewrite -> Hw1. rewrite -> Hw2.
             brel_pures'.
             iApply G_XOR_CORRECT_r. 
             brel_pures'.
             { eapply NoDup_cons_1_1.
               eapply (submseteq_NoDup _ [csend'; crecv'; getKey'; srecv_r; ssend_r]); [solve_submseteq | exact Hnd_r]. }
             apply Nat.lt_succ_r in Hc.
             rewrite -(fin.fin_to_nat_to_fin _ _ Hc) g_log_exp.
             iApply (brel_na_inv _ _ alphaN); first (set_unfold; tauto).
             iFrame "Hinvα".
             iIntros "([ (>Hγ & (>Hl_m'sim' & (>Hl_sim' & (>Hl_auth & (>Hl_fchan' & (>Hl_rchan' & Hl_key')))))) | [>Hd2 | >Hd3]] & Hclose)".
          (*contradiction branch as the first message has been sent and stored*)
          - iDestruct (ghost_map_elem_agree
                        with "Hl_fchan Hl_fchan'") as %Heq.
            congruence.
          -
            unfold d2. 
            iDestruct "Hd2" as (?m ?n ?Hfm) "(Hγ & (Hl_m'sim' & (Hl_sim & (Hl_auth & (Hl_fchan' & (Hl_rchan' & Hl_key'))))))". 
            iApply (brel_load_r _ _ _ _ [HandleCtx _ _ _ _ _ ; HandleCtx _ _ _ _ _ ;CaseCtx _ _] with "Hl_auth").                                          
            iIntros "Hl_auth".
            simpl. brel_pures_r.
            brel_load_l...
            iApply fupd_brel.
            iModIntro.
            iApply brel_na_close. iFrame "Hclose".
            iSplitL.
            { iModIntro. iRight. iLeft. iFrame "Hγ Hl_m'sim' Hl_sim Hl_auth Hl_fchan' Hl_rchan' Hl_key'". }
            
            brel_pures'. 
            iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)); [auto|set_unfold; tauto|iApply "Hrel";iApply "HmQ"|iApply "IH"].
          - unfold d3.
            iDestruct "Hd3" as (?m ?n) "(Hγ & (Hl_m'sim' & (Hl_sim & (Hl_auth & (Hl_fchan' & (Hl_rchan' & Hl_key'))))))". 
            iApply (brel_load_r _ _ _ _ [HandleCtx _ _ _ _ _ ; HandleCtx _ _ _ _ _ ;CaseCtx _ _] with "Hl_auth").                                          
            iIntros "Hl_auth"...
            brel_load_l...
            iApply (brel_exp_l [HandleCtx _ _ _ _ _ ; AppRCtx _])... 
            brel_store_l...
            brel_store_r...
            iApply fupd_brel.
            iMod (ghost_map_elem_persist with "Hl_sim") as "#Hl_sim".
            iMod (ghost_map_elem_persist with "Hl_auth") as "#Hl_auth".
            iDestruct "Hγ" as (ns) "(%Hfγ & Hγ)".
            apply map_eq_nil in Hfγ. simplify_eq. 
            iModIntro.
            iApply brel_na_close. iFrame.
            iSplitL.
            { iModIntro. iRight. iLeft. 
              apply Nat.lt_succ_r in H0.
              iExists m, c. 
              rewrite fin.fin_to_nat_to_fin.
              iFrame "#".  by iPureIntro. }
            brel_pures'...
            unfold kl3.
            set (hbranchright := (λ: "p" "k",
                                    match: "p" with
                                      InjL <> =>
                                        let: "key" := (λ: <>,
                                                         match: ! #l_key with
                                                           InjL <> =>
                                                             let: "c" := 
                                                               #();; 
                                                               rand(#lbl:γ) #
                                                                 (S n'') in
                                                             let: "key" := 
                                                               vexp g "c" in
                                                             #l_key <-
                                                               InjR "key";; "key"
                                                         | InjR "key" => "key"
                                                         end)%V
                                                        #()%V in
                                        kysnd_r bob;; 
                                        let: "r" := kyrcv_r bob in
                                        match: "r" with
                                          InjL <> => "k" (InjLV #()%V)
                                        | InjR "w" => "k" (InjR "key")
                                        end
                                    | InjR <> =>
                                        let: "r" := kyrcv_r alice in
                                        match: "r" with
                                          InjL <> => "k" (InjLV #()%V)
                                        | InjR "w" =>
                                            kysnd_r alice;; 
                                            match: ! #l_key with
                                              InjL <> => "k" (InjLV #()%V)
                                            | InjR "key" => "k" (InjR "key")
                                            end
                                        end end )%E).
            
            iPoseProof (brel_bind _ _ _ _ _ _
                          (asnd_l (vgval (g ^+c), bob))%V
                          (asnd_r (vgval (g ^+ sc_coupling m (nat_to_fin Hc)), bob))%V) as "Hbind".
            iApply "Hbind".
            { simpl. unfold leaktheory. auto.
              iApply (traversable_ectx_labels _ _ [lrecv'] [crecv'; getKey'] iThyBot _). 
              + simpl. (set_unfold; tauto).
              + unfold kont1. simpl. set_unfold; tauto.
              + simpl.
                unfold sem_row_union in Hdist'.
                unfold distinct in *.
                unfold distinct_l, distinct_r in *.
                unfold labels_l, labels_r in *.
                destruct Hdist' as [Hl Hr].
                split.
                ++ 
                  set (l1 := (concat  (([lrecv'], [crecv'; getKey'], iThyBot) :: iLblSig_to_iLblThy autheff).*1.*1)).
                  eapply (submseteq_NoDup l1 _); try eapply Hl.
                  unfold l1. simpl. eapply submseteq_skip. (*eapply submseteq_skip.*)
                  repeat (rewrite -> iLblSig_to_iLblThy_proj;
                          rewrite -> iLblSig_to_iLblThy_app). 
                  repeat (rewrite -> fmap_app). do 3 eapply submseteq_cons. 
                  eapply concat_submseteq. solve_submseteq.
                ++ set (l2 := (concat (([lrecv'], [crecv'; getKey'], iThyBot)
                                         :: iLblSig_to_iLblThy autheff).*1.*2)).
                   eapply (submseteq_NoDup l2 _); try eapply Hr.
                   unfold l2. simpl. (*eapply submseteq_skip.*)
                   eapply submseteq_cons. do 2 eapply submseteq_skip.
                   repeat (rewrite -> iLblSig_to_iLblThy_proj;
                           rewrite -> iLblSig_to_iLblThy_app). 
                   repeat (rewrite -> fmap_app). simpl.  do 2 eapply submseteq_cons.
                   eapply concat_submseteq. simpl. solve_submseteq.
            }
            { simpl. unfold N. iApply to_iThy_le_intro'. 
              unfold sem_row_union. repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app).
              solve_submseteq. }
            {  iApply (brel_wand _ _ _ R _).
               {  iDestruct "Hasnd" as "#Hasnd".
                  iSpecialize ("Hasnd" $! (vgval (g ^+c), bob)%V).
                  iSpecialize ("Hasnd" $! (vgval _, bob)%V).
                  iApply "Hasnd".
                  simpl. unfold sem_ty_prod.
                  iExists (vgval (valgroup.g ^+ c)), _, bob, bob.
                  repeat (iSplit); try (iPureIntro); try reflexivity.
                  + auto. simpl. unfold f. 
                    eexists; split; first done.
                    unfold f in Hc.
                    apply Nat.lt_succ_r in H0.
                    destruct (decide (c < S (S n''))%nat) as [H1 | H1]; last lia.
                    rewrite fin.nat_to_fin_to_nat. 
                    rewrite sc_coupling_involutive. 
                    rewrite fin.fin_to_nat_to_fin. done.
                  + simpl. exists #()%V, #()%V. repeat split; unfold bob; try reflexivity.
                    left. repeat split; reflexivity. }
               iModIntro. iIntros (v0 v3) "#HRv0v3".
               unfold R. unfold sem_ty_unit.
               iDestruct "HRv0v3" as "(%Hv0 & %Hv3)".
               rewrite -> Hv0. rewrite -> Hv3.
               brel_pures.
               iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)); [auto|set_unfold; tauto|iApply "Hrel"; iApply "HmQ"|iApply "IH"]. } }
      (* A message has already been sent by the secure channel *)     
      ++ unfold d2.
         iDestruct "Hd2" as (?m ?n ?Hfm) "(Hγ & (Hl_m'sim & (Hl_sim & (Hl_auth & (Hl_fchan & (Hl_rchan & Hl_key))))))".
         iDestruct "Hl_rchan" as "#Hl_rchan".
         iApply (brel_load_r _ _ _ _  [HandleCtx _ _ _ _ _; HandleCtx _ _ _ _ _ ; HandleCtx _ _ _ _ _ ; HandleCtx _ _ _ _ _ ; CaseCtx _ _] with "Hl_rchan").
         iIntros "Hl_rchan'".
         brel_pures'.
         brel_load_l...
         iApply brel_na_close. iFrame.
         iSplitL.
         { iModIntro. iRight. iLeft. iFrame. }
         iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)); [auto|set_unfold;tauto|iApply "Hrel";iApply "HmQ"|iApply "IH"].
      ++ unfold d3.
         iDestruct "Hd3" as (?m ?n) "(Hγ & (Hl_m'sim & (Hl_sim & (Hl_auth & (Hl_fchan & (Hl_rchan & Hl_key))))))".
         iApply (brel_load_r _ _ _ _ [HandleCtx _ _ _ _ _; HandleCtx _ _ _ _ _ ; HandleCtx _ _ _ _ _ ; HandleCtx _ _ _ _ _ ; CaseCtx _ _] with "Hl_rchan").
         iIntros "Hl_rchan'".
         brel_pures'.
         brel_load_l...
         iApply brel_na_close. iFrame.
         iSplitL.
         { iModIntro. iRight. iRight. iFrame. }
         iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)); [auto|set_unfold;tauto|iApply "Hrel";iApply "HmQ"|iApply "IH"].
         
    + iDestruct "HRecvBob" as "[%He1 [%He2 #HmQ]]".  
      rewrite -> He1. rewrite -> He2. brel_pures.
      { split.
        + apply -> NeutralEctx_ectx_labels_singleton.
          do 2 (eapply NeutralEctx_label_cons_inv_2 in Hk1). 
          eapply NeutralEctx_label_cons_inv_1 in Hk1. 
          eapply HandleCtx_NeutralEctx; last eapply Hk1.
          { eapply NoDup_cons_1_1.
            eapply (submseteq_NoDup _ [lrecv'; lsend'; srecv_l; ssend_l]); [solve_submseteq | done]. }
        + simpl. rewrite !NoDup_cons in Hnd_l, Hnd_r; (set_unfold; tauto). }
      { split.
        + apply -> NeutralEctx_ectx_labels_singleton.
          do 3 (eapply NeutralEctx_label_cons_inv_2 in Hk2).
          eapply NeutralEctx_label_cons_inv_1 in Hk2.
          eapply HandleCtx_NeutralEctx; last eapply Hk2.
          { eapply NoDup_cons_1_1.
            eapply (submseteq_NoDup _ [csend'; crecv'; getKey'; srecv_r; ssend_r]); [solve_submseteq | done]. }
        + simpl.
          eapply NoDup_cons_1_1.
          eapply (submseteq_NoDup _ [csend'; crecv'; getKey'; srecv_r; ssend_r]); [solve_submseteq | done].  }
      brel_pures.
      set (keytheory := keyeff).
      set (leaktheory := autheff).
      set (M := [([lrecv'; lsend'; srecv_l; ssend_l], [csend'; crecv'; getKey'; srecv_r; ssend_r], @iThyBot Σ)]).
      set (N := [([lrecv'; lsend'; srecv_l; ssend_l], [csend'; crecv'; getKey'; srecv_r; ssend_r], @iThyBot Σ)] ++
                  iLblSig_to_iLblThy (sem_row_union keytheory (sem_row_union leaktheory L))).
      repeat foldkont.
      brel_pures'.
      set (leftkontbind := ( match: "r" with
                               InjL <> => kont (InjLV #()%V)
                             | InjR "w" =>
                                 kysnd_l alice;; 
                                 match: ! #l_key with
                                   InjL <> => kont (InjLV #()%V)
                                 | InjR "key" => kont (InjR "key")
                                 end
                             end )%E).
      set (rightkontbind := ( match: "r" with
                                InjL <> => kont0 (InjLV #()%V)
                              | InjR "x" =>
                                  kysnd_r alice;; 
                                  match: ! #l_m'sim with
                                    InjL <> => kont0 (InjLV #()%V)
                                  | InjR "_" =>
                                      let: "rla" := arcv_r bob in
                                      match: "rla" with
                                        InjL <> => kont0 (InjLV #()%V)
                                      | InjR "x" => kont0 ! #l_sim
                                      end
                                  end
                              end )%E).
      iApply (brel_bind'' _ _  (iLblSig_to_iLblThy (keytheory))  [([lrecv'; lsend'; srecv_l; ssend_l], [csend'; crecv'; getKey'; srecv_r; ssend_r], @iThyBot Σ)] (([lrecv'; lsend'; srecv_l; ssend_l], [csend'; crecv'; getKey'; srecv_r; ssend_r], iThyBot)
                                                                                                                                            :: iLblSig_to_iLblThy (sem_row_union leaktheory (sem_row_union keytheory L))) (𝟙%T) (kyrcv_l alice) (kyrcv_r alice)).
      { unfold labels_l. set_unfold; tauto. }
      { unfold labels_r. set_unfold; tauto. }
      { iApply to_iThy_le_intro'. unfold M. unfold N. unfold sem_row_union. repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app). solve_submseteq. }
      iApply brel_wand.
      {  iDestruct "Hkeyrcv" as "#Hkeyrcv".
         iSpecialize ("Hkeyrcv" $! alice alice).
         iApply "Hkeyrcv". unfold sem_ty_sum, sem_ty_unit.
         iExists #()%V, #()%V. unfold alice.
         repeat (iSplit); try (iPureIntro); try reflexivity.
         right. repeat split; try reflexivity. }
      iModIntro. iIntros (v1 v2) "#Hv1v2". brel_pures'.
      unfold sem_ty_group, sem_ty_option, sem_ty_sum.
      iDestruct "Hv1v2" as (?w1 ?w2) "[#Hnone | #Hsome]".
    (*key receive didnt return successfully*)
    - iDestruct "Hnone" as "[%Hv1 [%Hv2 #Hw1w2]]".
      rewrite -> Hv1. rewrite -> Hv2. unfold sem_ty_unit.
      iDestruct "Hw1w2" as "(%Hw1 & %Hw2)".
      rewrite -> Hw1. rewrite -> Hw2. brel_pures'.
      iApply (brel_exhaustion (fill k1'(InjLV #()%V)) (fill k2' (InjLV #()%V))); [auto|set_unfold; tauto| |].
      { iApply "Hrel". iDestruct "HmQ" as "[Hsome Hnone]". iApply "Hnone".  }
      { iApply "IH". }
    (*key receive returned successfully*)
    - iDestruct "Hsome" as "[%Hv1 [%Hv2 #Hw1w2]]". 
      rewrite -> Hv1. rewrite -> Hv2.
      iDestruct "Hw1w2" as "(%Hw1 & %Hw2)".
      rewrite -> Hw1. rewrite -> Hw2. brel_pures'.
      set (rightapp := ( match: "rla" with
                           InjL <> => kont0 (InjLV #()%V)
                         | InjR "x" => kont0 ! #l_sim
                         end)%E).
      iApply (brel_bind'' _ _ (iLblSig_to_iLblThy keytheory)  [([lrecv'; lsend'; srecv_l; ssend_l], [csend'; crecv'; getKey'; srecv_r; ssend_r], @iThyBot Σ)] ([([lrecv'; lsend'; srecv_l; ssend_l], [csend'; crecv'; getKey'; srecv_r; ssend_r], @iThyBot Σ)] ++
                                                                                                                                         iLblSig_to_iLblThy (sem_row_union leaktheory (sem_row_union keytheory L))) 𝟙%T (kysnd_l alice) (kysnd_r alice)).
      1,2: set_unfold; tauto. 
      { iApply to_iThy_le_intro'. unfold M. unfold N. unfold sem_row_union. repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app). solve_submseteq. } 
      iApply brel_wand.
      { iDestruct "Hkeysnd" as "#Hkeysnd".
        iSpecialize ("Hkeysnd" $! alice alice).
        iApply "Hkeysnd".
        iExists #()%V, #()%V. unfold alice.
        iRight. repeat (iSplit); try (iPureIntro); try reflexivity. }
      iModIntro. iIntros (v0 v3) "#HRv0v3".
      unfold R. unfold sem_ty_unit.
      iDestruct "HRv0v3" as "(%Hv0 & %Hv3)".
      rewrite -> Hv0. rewrite -> Hv3...
      iApply (brel_na_inv _ _ alphaN); first (set_unfold; tauto). 
      iFrame "Hinvα".
      iIntros "([(>Hγ & >Hl_m'sim & >Hl_sim & >Hl_auth & >Hl_fchan & >Hl_rchan & >Hl_key) | [>Hd2 | >Hd3 ]] & Hclose)".
      (* no message has been sent yet by the secure channel*)
      ++ iApply (brel_load_r _ _ _ _ [CaseCtx _ _] with "Hl_key").
         iIntros "Hl_key"...
         brel_load_l...
         iApply brel_na_close. iFrame.
         iSplitL.
         { iModIntro. iLeft. iFrame. }
         
         iApply (brel_exhaustion (fill k1'(InjLV #()%V)) (fill k2' (InjLV #()%V))); [auto|set_unfold; tauto| |].
         { iApply "Hrel". iDestruct "HmQ" as "[Hsome Hnone]". iApply "Hnone".  }
         { iApply "IH". }
      (* a message has been sent by both the secure channel and the authenticated channel *)
      ++ unfold d2.
         iDestruct "Hd2" as (?m ?n ?Hfm) "(Hγ & (Hl_m'sim & (Hl_sim & (Hl_auth & (Hl_fchan & (Hl_rchan & Hl_key))))))".
         iApply (brel_load_r _ _ _ _ [CaseCtx _ _] with "Hl_key").
         iIntros "Hl_key"...
         { simpl. eapply NoDup_cons_1_1.
           eapply (submseteq_NoDup _ [csend'; crecv'; getKey'; srecv_r; ssend_r]); [solve_submseteq | done]. }
         brel_load_l...
         iApply fupd_brel.
         iMod (ghost_map_elem_persist with "Hl_fchan") as "#Hl_fchan".
         iMod (ghost_map_elem_persist with "Hl_rchan") as "#Hl_rchan".
         iMod (ghost_map_elem_persist with "Hl_key") as "#Hl_key".
         iMod (ghost_map_elem_persist with "Hl_m'sim") as "#Hl_m'sim".
         iMod (ghost_map_elem_persist with "Hl_auth") as "#Hl_auth".
         iMod (ghost_map_elem_persist with "Hl_sim") as "#Hl_sim".
         iModIntro.
         
         iApply brel_na_close. iFrame.
         iSplitL.
         { iModIntro. iRight. iLeft. iFrame "#". }
         iApply (brel_bind'' _ _  (iLblSig_to_iLblThy leaktheory)  [([lrecv'; lsend'; srecv_l; ssend_l], [csend'; crecv'; getKey'; srecv_r; ssend_r], @iThyBot Σ)] ([([lrecv'; lsend'; srecv_l; ssend_l], [csend'; crecv'; getKey'; srecv_r; ssend_r], @iThyBot Σ)] ++
                                                                                                                                              iLblSig_to_iLblThy (sem_row_union leaktheory (sem_row_union keytheory L))) 𝟙%T (arcv_l bob) (arcv_r bob)).
         1,2: set_unfold; tauto.
         { iApply to_iThy_le_intro'. unfold sem_row_union. repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app). solve_submseteq. }
         
         iApply brel_wand.
         { iDestruct "Harcv" as "#Harcv".
           iSpecialize ("Harcv" $! bob bob).
           iApply "Harcv".
           iExists #()%V, #()%V. unfold bob.
           iLeft. repeat (iSplit); try (iPureIntro); try reflexivity. }
         iModIntro. iIntros (v4 v5) "#Hv4v5".
         iDestruct "Hv4v5" as (?w0 ?w3) "Hv4v5".
         iDestruct "Hv4v5" as "[Hnone | Hsome]".
         +++ (* leakauth doesnt return successfully *)
           iDestruct "Hnone" as "(%Hv4 & (%Hv5 & (%Hw0 & %Hw3)))".
           rewrite -> Hv4. rewrite -> Hv5. rewrite -> Hw0. rewrite -> Hw3...
           iApply (brel_exhaustion (fill k1' (InjLV #()%V)) (fill k2' (InjLV #()%V))).
           1,2 : set_unfold; tauto.
           { iApply "Hrel".  iDestruct "HmQ" as "[Hsome Hnone]". iApply "Hnone". }
           {iApply "IH". }
         +++ (* leakauth returns successfully with a value *)
           iDestruct "Hsome" as "(%Hv4 & (%Hv5 & (%Hw0 & %Hw3)))".
           rewrite -> Hv4. rewrite -> Hv5. rewrite -> Hw0. rewrite -> Hw3...
           brel_load_l...
           brel_load_r...
           iDestruct "Hl_fchan" as "#Hl_fchan".
           iApply G_XOR_CORRECT_r...
           brel_load_l...
           rewrite (g_log_exp_bounded (f m n) Hfm).
           set (g_enc := (g ^+ sc_coupling (g ^+ sc_coupling m (fin.nat_to_fin Hfm))
                                           (fin.nat_to_fin Hfm))%g).
           iApply (brel_exhaustion (fill k1'((InjRV (vgval m))%V)) (fill k2' ((InjRV (vgval g_enc)))%V)).
           1,2 : set_unfold; tauto.
           { unfold kont0. iApply "Hrel". iDestruct "HmQ" as "[Hsome Hnone]". unfold g_enc. rewrite sc_coupling_invol. iApply "Hsome". }
           { iApply "IH". }
      (* a message has been sent by the secure channel but not the authenticated channel*)
      ++ unfold d3.
         iDestruct "Hd3" as (?m ?n) "(Hγ & (Hl_m'sim & (Hl_sim & (Hl_auth & (Hl_fchan & (Hl_rchan & Hl_key))))))". 
         iApply (brel_load_r _ _ _ _ [CaseCtx _ _] with "Hl_key").
         iIntros "Hl_key"... 
         { simpl. eapply NoDup_cons_1_1.
           eapply (submseteq_NoDup _ [csend'; crecv'; getKey'; srecv_r; ssend_r]); [solve_submseteq | done]. }
         brel_load_l...
         iApply fupd_brel.
         iMod (ghost_map_elem_persist with "Hl_fchan") as "#Hl_fchan".
         iMod (ghost_map_elem_persist with "Hl_rchan") as "#Hl_rchan".
         iMod (ghost_map_elem_persist with "Hl_key") as "#Hl_key".
         iMod (ghost_map_elem_persist with "Hl_m'sim") as "#Hl_m'sim".
         iModIntro.
         
         iApply brel_na_close. iFrame.
         iSplitL.
         { iModIntro. iRight. iRight. iFrame "#". iFrame. }
         iApply (brel_bind'' _ _  (iLblSig_to_iLblThy leaktheory)  [([lrecv'; lsend'; srecv_l; ssend_l], [csend'; crecv'; getKey'; srecv_r; ssend_r], @iThyBot Σ)] ([([lrecv'; lsend'; srecv_l; ssend_l], [csend'; crecv'; getKey'; srecv_r; ssend_r], @iThyBot Σ)] ++
                                                                                                                                              iLblSig_to_iLblThy (sem_row_union leaktheory (sem_row_union keytheory L))) 𝟙%T (arcv_l bob) (arcv_r bob)).
         1,2 : set_unfold; tauto.
         { iApply to_iThy_le_intro'. unfold sem_row_union. repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app). solve_submseteq. }
         
         iApply brel_wand.
         { iDestruct "Harcv" as "#Harcv".
           iSpecialize ("Harcv" $! bob bob).
           iApply "Harcv".
           iExists #()%V, #()%V. unfold bob.
           iLeft. repeat (iSplit); try (iPureIntro); try reflexivity. }
         iModIntro. iIntros (v4 v5) "#Hv4v5".
         iDestruct "Hv4v5" as (?w0 ?w3) "Hv4v5".
         iDestruct "Hv4v5" as "[Hnone | Hsome]".
         (* leakauth doesnt return successfully *)
         +++ iDestruct "Hnone" as "(%Hv4 & (%Hv5 & (%Hw0 & %Hw3)))".
             rewrite -> Hv4. rewrite -> Hv5. rewrite -> Hw0. rewrite -> Hw3...
             iApply (brel_exhaustion (fill k1' (InjLV #()%V)) (fill k2' (InjLV #()%V))).
             1,2 : set_unfold; tauto.
             { iApply "Hrel".  iDestruct "HmQ" as "[Hsome Hnone]". iApply "Hnone". }
             {iApply "IH". }
         (* leakauth returns successfully with a value *)
         +++ iDestruct "Hsome" as "(%Hv4 & (%Hv5 & (%Hw0 & %Hw3)))".
             rewrite -> Hv4. rewrite -> Hv5. rewrite -> Hw0. rewrite -> Hw3...
             (*another case analysis by opening the invariant again, since we need access to the pointers l_sim and l_auth *)
             iApply (brel_na_inv _ _ alphaN); first (set_unfold; tauto). 
             iFrame "Hinvα".
             iIntros "([(>Hγ & >Hl_m'sim' & >Hl_sim & >Hl_auth & >Hl_fchan' & >Hl_rchan' & >Hl_key') | [>Hd2 | >Hd3 ]] & Hclose)".
      (*contradiction branch since we already know that a message has been sent by the secure channel *)
      -- iDestruct (ghost_map_elem_agree
                     with "Hl_fchan Hl_fchan'") as %Heq.
         congruence.
      (*the next two brances will move the proof forward with a case analysis on l_auth and l_sim having been set or not *)
      -- unfold d2.
         iDestruct "Hd2" as (?m ?n Hfm) "(Hγ & (Hl_m'sim' & (Hl_sim & (Hl_auth & (Hl_fchan' & (Hl_rchan' & Hl_key'))))))".
         iApply (brel_load_l _ _ _ [AppRCtx _] with "Hl_sim").
         iIntros "!> Hl_sim".
         brel_load_r... 
         iApply fupd_brel.
         iMod (ghost_map_elem_persist with "Hl_fchan'") as "#Hl_fchan'".
         iMod (ghost_map_elem_persist with "Hl_rchan'") as "#Hl_rchan'".
         iMod (ghost_map_elem_persist with "Hl_key'") as "#Hl_key'".
         iMod (ghost_map_elem_persist with "Hl_m'sim'") as "#Hl_m'sim'".
         iMod (ghost_map_elem_persist with "Hl_auth") as "#Hl_auth".
         iMod (ghost_map_elem_persist with "Hl_sim") as "#Hl_sim".
         iModIntro.
         
         iApply brel_na_close. iFrame.
         iSplitL.
         { iModIntro. iRight. iLeft. iFrame "#". }
         simpl. brel_pures'.
         iCombine "Hl_fchan Hl_fchan'" gives %[Hval Hval2].
         inversion Hval2. apply vgval_inj in H1. rewrite -> H1.
         iCombine "Hl_m'sim Hl_m'sim'" gives %[Hsim Hsim2]. clear Hval Hsim.
         inversion Hsim2. specialize (Hf m0). destruct Hf as [Hfinj Hfsurj].
         apply Nat2Z.inj in H2.
         rewrite -> H2.
         iApply G_XOR_CORRECT_r...
         brel_load_l...
         rewrite (g_log_exp_bounded (f m0 n0) Hfm).
         set (g_enc := (g ^+ sc_coupling (g ^+ sc_coupling m0 (fin.nat_to_fin Hfm))
                                         (fin.nat_to_fin Hfm))%g).
         iApply (brel_exhaustion (fill k1'((InjRV (vgval m0))%V)) (fill k2' ((InjRV (vgval g_enc)))%V)).
         1,2 : set_unfold; tauto.
         { unfold kont0. iApply "Hrel". iDestruct "HmQ" as "[Hsome Hnone]".
           unfold g_enc.
           rewrite sc_coupling_invol. iApply "Hsome". }
         { iApply "IH". }
      -- unfold d3.
         iDestruct "Hd3" as (?m ?n) "(Hγ & (Hl_m'sim' & (Hl_sim & (Hl_auth & (Hl_fchan' & (Hl_rchan' & Hl_key'))))))".
         iApply (brel_load_l _ _ _ [AppRCtx _] with "Hl_sim").
         iIntros "!> Hl_sim".
         brel_load_r...
         iApply fupd_brel.
         iMod (ghost_map_elem_persist with "Hl_fchan'") as "#Hl_fchan'".
         iMod (ghost_map_elem_persist with "Hl_rchan'") as "#Hl_rchan'".
         iMod (ghost_map_elem_persist with "Hl_key'") as "#Hl_key'".
         iMod (ghost_map_elem_persist with "Hl_m'sim'") as "#Hl_m'sim'".
         iModIntro.
         
         iApply brel_na_close. iFrame.
         iSplitL.
         { iModIntro. iRight. iRight. iFrame "#". iFrame. }
         simpl. brel_pures'.
         iApply (brel_exhaustion (fill k1' (InjLV #()%V)) (fill k2' (InjLV #()%V))).
         1,2 : set_unfold; tauto.
         { iApply "Hrel".  iDestruct "HmQ" as "[Hsome Hnone]". iApply "Hnone". }
         { iApply "IH". }
  Qed.

  Lemma R_CHAN_CHAN_SIM_F_CHAN :
    ⊢ sem_val_typed (R_CHAN)%V (λ: "f", CHAN_SIM_lazy (F_CHAN "f"))%V
        (∀ᵣ θ__L ,(∀ᵣ θₕ, (((sem_ty_nat -{ θₕ }->  𝟙) × (𝟙 -{ θₕ }-> (Option  𝔾))) -{ sem_row_union  θₕ θ__L }-∘ 𝟙)) ⊸ (*type of client*)
                  (∀ᵣ θ₁, ∀ᵣ θ₂,  (((𝔾 × (𝟙 + 𝟙)) -{ θ₁ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ₁ }-> Option 𝟙)) ⊸ (((𝟙 + 𝟙) -{ θ₂ }-> 𝟙) × (𝟙 + 𝟙) -{ θ₂ }-> Option 𝟙) -{ sem_row_union θ₁ (sem_row_union θ₂ θ__L) }-∘ 𝟙))%T.
  Proof using  G H XOR_spec0 cg inG0 inG1 inG2
    vg vgg xor_struct Σ.
    iModIntro. iIntros (L).
    iIntros (f1 f2) "Hrelf1f2".
    brel_pures'.
    simpl.
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][Hrelf1f2]");
      [iApply to_iThy_le_refl|simpl|simpl].
    +  iApply (SEM_R_CHAN_SIM _ _ L).
       iApply "Hrelf1f2".
    +  iIntros (??) "$".
  Qed.

  Lemma CHAN_SIM_F_CHAN_R_CHAN :
    ⊢ sem_val_typed (λ: "f", CHAN_SIM_lazy (F_CHAN "f"))%V (R_CHAN)%V
        (∀ᵣ θ__L ,(∀ᵣ θₕ, (((sem_ty_nat -{ θₕ }->  𝟙) × (𝟙 -{ θₕ }-> (Option  𝔾))) -{ sem_row_union  θₕ θ__L }-∘ 𝟙)) ⊸ (*type of client*)
                  (∀ᵣ θ₁, ∀ᵣ θ₂,  (((𝔾 × (𝟙 + 𝟙)) -{ θ₁ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ₁ }-> Option 𝟙)) ⊸ (((𝟙 + 𝟙) -{ θ₂ }-> 𝟙) × (𝟙 + 𝟙) -{ θ₂ }-> Option 𝟙) -{ sem_row_union θ₁ (sem_row_union θ₂ θ__L) }-∘ 𝟙))%T.
  Proof using  G H XOR_spec0 cg
    inG0 inG1 inG2 vg
    vgg xor_struct Σ.
    iModIntro. iIntros (L).
    iIntros (f1 f2) "Hrelf1f2".
    brel_pures'.
    simpl.
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][Hrelf1f2]");
      [iApply to_iThy_le_refl|simpl|simpl].
    +  iApply (SEM_R_CHAN_SIM_rev _ _ L).
       iApply "Hrelf1f2".
    +  iIntros (??) "$".
  Qed.

  (*top level statements for the secure channel *)
  (*----------------------------------------------------------------*)
  Lemma R_I_SCHAN :
    ⊢ sem_typed [] R_CHAN (λ: "f", (CHAN_SIM_lazy (F_CHAN "f")))%V ⊥
        (∀ᵣ θ__L ,(∀ᵣ θₕ, (((sem_ty_nat -{ θₕ }-> 𝟙) × (𝟙 -{ θₕ }-> (Option  𝔾))) -{ sem_row_union  θₕ θ__L }-∘ 𝟙)) ⊸ (*type of client*)
                  (∀ᵣ θ₁, ∀ᵣ θ₂,  (((𝔾 × (𝟙 + 𝟙)) -{ θ₁ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ₁ }-> Option 𝟙)) ⊸ (((𝟙 + 𝟙) -{ θ₂ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ₂ }-> Option 𝟙)) -{ sem_row_union θ₁ (sem_row_union θ₂ θ__L) }-∘ 𝟙))%T [].
  Proof using  G H XOR_spec0 cg inG0 inG1 inG2 vg vgg
    xor_struct Σ.
    iIntros (vs) "!# H". simpl.
    iApply brel_value.
    iIntros "$ !>".
    iSplit; try (done).
    iPoseProof R_CHAN_CHAN_SIM_F_CHAN as "Hsemty".
    rewrite /sem_val_typed /=.
    iDestruct "Hsemty" as "#Hsemty".
    iApply "Hsemty".
  Qed.

  Lemma I_R_SCHAN :
    ⊢ sem_typed [] (λ: "f", (CHAN_SIM_lazy (F_CHAN "f")))%V R_CHAN ⊥
        (∀ᵣ θ__L ,(∀ᵣ θₕ, (((sem_ty_nat -{ θₕ }-> 𝟙) × (𝟙 -{ θₕ }-> (Option  𝔾))) -{ sem_row_union  θₕ θ__L }-∘ 𝟙)) ⊸ (*type of client*)
                  (∀ᵣ θ₁, ∀ᵣ θ₂,  (((𝔾 × (𝟙 + 𝟙)) -{ θ₁ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ₁ }-> Option 𝟙)) ⊸ (((𝟙 + 𝟙) -{ θ₂ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ₂ }-> Option 𝟙)) -{ sem_row_union θ₁ (sem_row_union θ₂ θ__L) }-∘ 𝟙))%T [].
  Proof using G H XOR_spec0 cg
    inG0 inG1 inG2 vg vgg xor_struct Σ.
    iIntros (vs) "!# H". simpl.
    iApply brel_value.
    iIntros "$ !>".
    iSplit; try (done).
    iPoseProof CHAN_SIM_F_CHAN_R_CHAN as "Hsemty".
    rewrite /sem_val_typed /=.
    iDestruct "Hsemty" as "#Hsemty".
    iApply "Hsemty".
  Qed.

End schan_security.

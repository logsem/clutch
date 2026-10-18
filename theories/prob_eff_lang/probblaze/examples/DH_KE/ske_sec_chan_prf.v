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
From clutch.prob_eff_lang.probblaze.examples.DH_KE Require Import ske ske_sec_chan_def.


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
  Context {msg_card : nat}.
  Context {cipher_card : nat}.
  Instance ske_params : SYM_params := {
      card_key := n;
      card_message := msg_card;
      card_cipher := cipher_card }.
  Context {ske_struct : @SYM_struct ske_params}.
  Context {ske : SYM}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.
  

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
                ((∀ g : nat, Q (SOMEV #g) (SOMEV #g)) ∧ Q NONEV NONEV)
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
    - iDestruct "HS" as "(He1e2 & Hs1s2)". iApply "He1e2".
    - iDestruct "HS" as "(He1e2 & #Hs1s2)". iModIntro.
      iIntros (??) "HS". iApply "HΦΦ'". iApply "Hs1s2". iApply "HS".
  Qed.

  Program Definition sec_channel_row (ssend1 srecv1 ssend2 srecv2 : label) := SemRow [([srecv1; ssend1], [srecv2; ssend2], sec_channel ssend1 ssend2 srecv1 srecv2)] (sec_channel_pers_mono_row ssend1 srecv1 ssend2 srecv2).
  Program Definition client_row (csend crecv lsend lrecv getKey1 getKey2 ssend1 srecv1 ssend2 srecv2 : label) := SemRow [([csend; crecv; getKey1; srecv1; ssend1], [lrecv; lsend; getKey2; srecv2; ssend2], sec_channel ssend1 ssend2 srecv1 srecv2)] (client_pers_mono_row csend crecv lsend lrecv getKey1 getKey2 ssend1 srecv1 ssend2 srecv2).

  Program Definition client_row' (csend crecv lsend lrecv getKey1 getKey2 ssend1 srecv1 ssend2 srecv2 : label) := SemRow [([lrecv; lsend; getKey2; srecv1; ssend1], [csend; crecv; getKey1; srecv2; ssend2], sec_channel ssend1 ssend2 srecv1 srecv2)] (client_pers_mono_row' csend crecv lsend lrecv getKey1 getKey2 ssend1 srecv1 ssend2 srecv2).

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
        (sem_val_typed  ((λ: "m", do: ssend_l "m"), (λ: <>, do: srecv_l bob))%V ((λ: "m", do: ssend_r "m") , (λ: <>, do: srecv_r bob))%V (((sem_ty_nat)%T -{ θ }-> 𝟙) × (𝟙 -{ θ }-> (Option ℕ)))%T)%I.
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

  (** ** The key-coupling bijection

      [sc_real] samples the exponent [x ∈ {0,..,n}] of Alice's DH key and then
      uses the group element [g ^+ x] as the symmetric key, passing it through
      [int_of_vg] to get a [nat].  [game1] instead samples a key [k ∈ {0,..,n}]
      directly.  The two tapes are coupled along

        [keyf x = int_of_vg_sem (g ^+ x)]   (extended by the identity off-range)

      which is a bijection of [nat]: on the range [{0,..,n}] it is the
      composition of [x ↦ g ^+ x] — a bijection of [{0,..,S n''} = {0,..,n}]
      onto [vgG] because [g] generates a group of order [S (S n'') = S n]
      ([vgG_card]) — with the encoding [int_of_vg_sem], which is injective
      ([int_of_vg_sem_inj]) and lands in [{0,..,n}] ([int_of_vg_sem_bound]),
      hence onto it ([vg_of_int_sem_surj]).  Off the range it is the identity,
      and the two pieces have disjoint images, so the extension stays bijective.

      [brel_couple_TT] then hands the proof the exponent [x] drawn on the left
      together with the key [keyf x] drawn on the right, which is precisely the
      key the left-hand program derives from [x] -- see [keyf_lt]. *)

  Definition keyf : nat → nat :=
    λ x, if bool_decide (x < S n)%nat then int_of_vg_sem (g ^+ x)%g else x.

  Lemma keyf_lt (m : nat) : (m < S n)%nat → keyf m = int_of_vg_sem (g ^+ m)%g.
  Proof. intros Hm. rewrite /keyf bool_decide_eq_true_2 //. Qed.

  Lemma keyf_ge (m : nat) : ¬ (m < S n)%nat → keyf m = m.
  Proof. intros Hm. rewrite /keyf bool_decide_eq_false_2 //. Qed.

  (* [keyf] maps the tape's value range [{0,..,n}] into itself. *)
  Lemma keyf_dom (m : nat) : (m < S n)%nat → (keyf m < S n)%nat.
  Proof.
    intros Hm. rewrite keyf_lt //.
    pose proof (int_of_vg_sem_bound (g ^+ m)%g) as Hb.
    rewrite vgG_card in Hb. lia.
  Qed.

  Global Instance keyf_bij : Bij keyf.
  Proof.
    split.
    - intros x y Hxy.
      destruct (decide (x < S n)%nat) as [Hx|Hx]; destruct (decide (y < S n)%nat) as [Hy|Hy].
      + (* both in range: [int_of_vg_sem] and [x ↦ g ^+ x] are both injective *)
        rewrite (keyf_lt x Hx) (keyf_lt y Hy) in Hxy.
        apply int_of_vg_sem_inj in Hxy.
        rewrite -(id_g_log_nat x Hx) -(id_g_log_nat y Hy). by rewrite Hxy.
      + (* mixed: the images are disjoint, by [keyf_dom] *)
        exfalso. pose proof (keyf_dom x Hx) as Hb.
        rewrite Hxy (keyf_ge y Hy) in Hb. lia.
      + exfalso. pose proof (keyf_dom y Hy) as Hb.
        rewrite -Hxy (keyf_ge x Hx) in Hb. lia.
      + by rewrite (keyf_ge x Hx) (keyf_ge y Hy) in Hxy.
    - intros y. destruct (decide (y < S n)%nat) as [Hy|Hy].
      + destruct (vg_of_int_sem_surj y) as (xg & _ & Hxg); first (rewrite vgG_card; lia).
        exists (fin_to_nat (g_log xg)).
        rewrite keyf_lt; first by rewrite g_log_id.
        pose proof (fin_to_nat_lt (g_log xg)). lia.
      + exists y. by rewrite (keyf_ge y Hy).
  Qed.

  (* The reverse refinement couples along the inverse bijection, so it needs
     [f_inv keyf] as a [Bij] instance, its range preservation, and the fact
     that the exponent [f_inv keyf d] really does encode back to [d]. *)
  Global Instance keyf_inv_bij : Bij (f_inv keyf) := f_inv_bij keyf.

  Lemma keyf_inv_dom (d : nat) : (d < S n)%nat → (f_inv keyf d < S n)%nat.
  Proof. apply (fin.f_inv_restr (S n) keyf keyf_dom). Qed.

  Lemma keyf_inv_spec (d : nat) : (d < S n)%nat → int_of_vg_sem (g ^+ f_inv keyf d)%g = d.
  Proof. intros Hd. rewrite -(keyf_lt _ (keyf_inv_dom d Hd)). apply f_inv_cancel_r. Qed.

  (* [brel_couple_TT] does not say that the sample it produces is in range, but
     a tape only ever holds values below its bound, so the bound can be read
     back off the tape assertion. *)
  Lemma tapeN_hd_bound (l : loc) dq M x ns :
    l ↪{dq}N (M; x :: ns) ⊢ ⌜(x < S M)%nat⌝ ∗ l ↪{dq}N (M; x :: ns).
  Proof.
    iIntros "(%fs & %Hfs & Hl)".
    destruct fs as [|f fs']; first done.
    simpl in Hfs. injection Hfs as Hx Hns.
    iSplit.
    - iPureIntro. rewrite -Hx. apply fin_to_nat_lt.
    - iExists (f :: fs'). iFrame. iPureIntro. simpl. by rewrite Hx Hns.
  Qed.

  (* Tape assertions are [ghost_map_elem]s, so a full one is exclusive: it
     cannot coexist with any other assertion -- full or discarded -- for the
     same location.  Used to rule out the stale disjuncts of the invariant
     after the key tape has been consumed. *)
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

  Definition τsc :=  (∀ᵣ θ__L ,(∀ᵣ θₕ, (((sem_ty_nat -{ θₕ }->  𝟙) × (𝟙 -{ θₕ }-> (Option ℕ))) -{ sem_row_union  θₕ θ__L }-∘ 𝟙)) ⊸ (*type of client*)
                  (∀ᵣ θ₁, ∀ᵣ θ₂,  (((ℕ × (𝟙 + 𝟙)) -{ θ₁ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ₁ }-> Option 𝟙)) ⊸ (((𝟙 + 𝟙) -{ θ₂ }-> 𝟙) × (𝟙 + 𝟙) -{ θ₂ }-> Option 𝟙) -{ sem_row_union (¡θ₁) (sem_row_union (¡θ₂)%R θ__L) }-∘ 𝟙))%T.

  (* The reverse refinement.  Mirror image of [sc_real_game1] below: every
     left-hand step becomes a right-hand step and vice versa, the heap and tape
     assertions swap between the implementation and the specification side, and
     the tapes are coupled along the inverse bijection [f_inv keyf]. *)
  Lemma game1_sc_real : 
    ⊢ sem_typed [] game1 sc_real ⊥ τsc [].
  Proof using All with (brel_pures'; repeat foldkont). 
    iIntros (?) "!# _ //=". rewrite /sc_real /reduction /CHAN /RED_CHAN /right_composition.
    do 2 (rewrite !lookup_delete_eq; 
          rewrite lookup_delete_ne; last done).
    rewrite !lookup_delete_eq.
    brel_alloctape_l (ι) as "Hι"...
    iModIntro. iSplit; last done.
    iIntros (θL f1 f2) "Hff"...
    iIntros "!#" (autheff keyeff autheff_l autheff_r) "Hautheff".
    iDestruct "Hautheff" as (asnd_l asnd_r arcv_l arcv_r) "(%H1al & %H2al & (#Hasnd & #Harcv))"...
    iIntros "!>" (keyeff_l keyeff_r) "Hkeyeff".
    iDestruct "Hkeyeff" as (kysnd_l kysnd_r kyrcv_l kyrcv_r) "(%H1k & %H2k & (#Hkeysnd & #Hkeyrcv))".
    rewrite H1al H2al H1k H2k /F_OAUTH /F_KE_lazy_alice...
    
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
    brel_alloc_l lml as "Hlml"...
    brel_effect_r ssr as "Hssr".
    brel_effect_l ssl as "Hssl"...
    brel_effect_r srr as "Hsrr".
    brel_effect_l srl as "Hsrl"...

    (* Setting up clients *)
    set (θ := client_row' sr rr sl rl gkr gkl ssl srl ssr srr).
    iSpecialize ("Hff" $! θ).
    unfold sem_ty_arr, sem_ty_mbang. simpl.
    iAssert (sem_val_typed  ((λ: "m", do: ssl "m"), (λ: <>, do: srl bob))%V ((λ: "m", do: ssr "m") , (λ: <>, do: srr bob))%V (((sem_ty_nat -{ θ }-> 𝟙) × (𝟙 -{ θ }-> (Option ℕ)))%T)) as "Hschn".
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
    iSplitL "Hι"; first (iNext; iFrame); iSplitL "Hγr"; first iFrame.
    iIntros (x) "(Hι&Hγr) //=".
    iDestruct (tapeN_hd_bound with "Hι") as "(%Hx&Hι)".
    
    iApply (brel_na_alloc ((lmr ↦ₛ NONEV ∗ lcr ↦ₛ NONEV ∗ lml ↦ NONEV ∗ lcl ↦ NONEV ∗ lamr ↦ₛ NONEV ∗ laml ↦ NONEV
                           ∗ γr ↪ₛN (n; [f_inv keyf x]) ∗ (Loc ι) ↪N (n; [x]))
                           ∨ (∃ c' m : nat, lmr ↦ₛ□ SOMEV #m ∗ lcr ↦ₛ□ SOMEV #(f_inv keyf x) ∗ lml ↦□ SOMEV #m ∗ lcl ↦□ SOMEV #c'
                                            ∗ lamr ↦ₛ NONEV ∗ laml ↦ NONEV 
                                            ∗ γr ↪ₛ□N (n; []) ∗ ⌜(m ≤ msg_card)%nat⌝)
                           ∨ (∃ c' m : nat, lmr ↦ₛ□ SOMEV #m ∗ lcr ↦ₛ□ SOMEV #(f_inv keyf x) ∗ lml ↦□ SOMEV #m ∗ lcl ↦□ SOMEV #c' 
                                            ∗ lamr ↦ₛ□ SOMEV #(enc_sem x m) ∗ laml ↦□ SOMEV #(enc_sem x m)
                                            ∗ γr ↪ₛ□N (n; []) ∗ (Loc ι) ↪□N (n; []) ∗ ⌜(m ≤ msg_card)%nat⌝)
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
    - brel_pures'; [apply neutral_ectx|apply neutral_ectx|]; repeat constructor.
      unfold msg_of_int...
      case_decide...
      2 : { iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V) with "[HQ]"); [set_solver|set_solver|by iApply "Hrel"|iApply "IH"]. }
      iApply (brel_na_inv _ _ alphaN); first set_solver.
      iFrame "HI".
      iIntros "(>[(Hlmr&Hlcr&Hlml&Hlcl&Hlamr&Hlaml&Hγr&Hι)|[H2|H3]]&Hclose)".
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
        { iModIntro. iRight. iLeft. iExists _, _. iFrame "#". iFrame. iPureIntro. lia. }
        
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
        { brel_cont_r. brel_cont_l... iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V) with "[HQ]"); [set_solver|set_solver|by iApply "Hrel"|iApply "IH"]. }
        brel_cont_r. 
        brel_cont_l...
        brel_rand_l...
        iApply brel_int_of_vg_sem_correct_r.
        assert (int_of_vg_sem (g ^+ f_inv keyf x) = x) as ->.
        { exact (keyf_inv_spec x Hx). }
        iApply enc_correct_r.
        iApply enc_correct_l.
        brel_pures'; simpl.
        (* [brel_pures'] raises one label-freshness goal per side; which side
           comes first is fixed by the tactic, not by the direction, so let
           each goal pick its own [NoDup] fact. *)
        { eapply NoDup_cons_1_1. first [ eapply (submseteq_NoDup _ [sr; rr; gkr; srr; ssr]); [solve_submseteq|exact Hnd_r]
                | eapply (submseteq_NoDup _ [rl; sl; gkl; srl; ssl]); [solve_submseteq|exact Hnd_l] ]. }
        { eapply NoDup_cons_1_1. first [ eapply (submseteq_NoDup _ [sr; rr; gkr; srr; ssr]); [solve_submseteq|exact Hnd_r]
                | eapply (submseteq_NoDup _ [rl; sl; gkl; srl; ssl]); [solve_submseteq|exact Hnd_l] ]. }
        iApply (brel_na_inv _ _ alphaN); first set_solver.
        iFrame "HI".
        iIntros "(>[(_&_&_&_&_&_&_&Hι')|[(%&%&_&_&_&_&Hlamr&Hlaml&_)|(%&%&_&_&_&_&_&_&_&Hι'&_)]]&Hclose)".
        (* The key tape [ι] has already been read, so the "fresh" and the
           "already sent" disjuncts are both impossible: each hands back an
           assertion for [ι] that cannot coexist with the one we hold. *)
        { iExFalso. iApply (tapeN_excl with "Hι Hι'"). }
        2 : { iExFalso. iApply (tapeN_excl with "Hι Hι'"). }
        brel_load_r...
        brel_load_l...
        brel_store_r...
        brel_store_l...

        iMod (ghost_map_elem_persist with "Hlamr") as "#Hlamr".
        iMod (ghost_map_elem_persist with "Hlaml") as "#Hlaml".
        iDestruct (tapeN_to_persistent with "Hι") as ">#Hι".
        iApply brel_na_close.
        iFrame. iSplitR; [iNext; do 2 iRight; iExists _,_; iFrame "#"; iPureIntro; lia|].
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
        iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V) with "[HQ]"); [set_solver|set_solver|by iApply "Hrel"|iApply "IH"].
      + iDestruct "H2" as "(%&%&Hlmr&Hlcr&Hlml&Hlcl&Hγ)".
        brel_load_r.
        brel_load_l...
        iApply brel_na_close.
        iFrame. 
        iSplitR "HQ"; [iRight; iLeft; iExists _,_; iFrame|].
        iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V) with "[HQ]"); [set_solver|set_solver|by iApply "Hrel"|iApply "IH"].
      + iDestruct "H3" as "(%&%&Hlmr&Hlcr&Hlml&Hlamr&Hlaml&Hι)".
        brel_load_r.
        brel_load_l...
        iApply brel_na_close.
        iFrame. 
        iSplitR "HQ"; [iRight; iRight; iExists _,_; iFrame|].
        iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V) with "[HQ]"); [set_solver|set_solver|by iApply "Hrel"|iApply "IH"].
    (* Bob tries to receive a message *)
    - brel_pures'.
      {  apply not_elem_of_cons; split; last (apply neutral_ectx; repeat constructor).
         intro Heq. first [ apply NoDup_ListNoDup in Hnd_r;
                 do 4 (apply NoDup_cons_iff in Hnd_r as [?Hn Hnd_r]); apply Hn2; by left
               | apply NoDup_ListNoDup in Hnd_l;
                 do 4 (apply NoDup_cons_iff in Hnd_l as [?Hn Hnd_l]); apply Hn2; by left ]. }
      {  apply not_elem_of_cons; split; last (apply neutral_ectx; repeat constructor).
         intro Heq. first [ apply NoDup_ListNoDup in Hnd_r;
                 do 4 (apply NoDup_cons_iff in Hnd_r as [?Hn Hnd_r]); apply Hn2; by left
               | apply NoDup_ListNoDup in Hnd_l;
                 do 4 (apply NoDup_cons_iff in Hnd_l as [?Hn Hnd_l]); apply Hn2; by left ]. }
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
      { brel_cont_r. brel_cont_l... 
        iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"]. 
        iDestruct "HQ" as "[_ $]". }
      iApply (brel_bind'' [AppRCtx _] [AppRCtx _] (to_iThyIfMono OS (iLblSig_to_iLblThy keyeff))); try (apply list_subseteq_nil).
      { iApply to_iThy_le_intro'. solve_submseteq. }
      iApply brel_mono; [iApply to_iThy_le_refl| |simpl].
      { iApply "Hkeysnd". iExists _, _. by iRight. }
      iIntros (v1 v2) "(->&->)"...      
      iApply (brel_na_inv _ _ alphaN); first set_solver.
      iFrame "HI".
      iIntros "(>[(Hlmr&Hlcr&Hlml&Hlcl&Hlamr&Hlaml&Hγr&Hι)|[H2|H3]]&Hclose)".
      + brel_load_r...
        brel_load_l...
        brel_cont_r.
        brel_cont_l...
        iApply brel_na_close.
        iFrame. 
        iSplitR "HQ"; [iLeft; iFrame|].
        iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"].
        iDestruct "HQ" as "[_ $]".
      + iDestruct "H2" as "(%&%&#Hlmr&#Hlcr&#Hlml&#Hlcl&Hlamr&Hlaml&#Hγ)".
        brel_load_r...
        brel_load_l...
        brel_cont_r.
        brel_cont_l...
        { eapply NoDup_cons_1_1. simpl. first [ eapply (submseteq_NoDup _ [sr; rr; gkr; srr; ssr]); [solve_submseteq|exact Hnd_r]
                | eapply (submseteq_NoDup _ [rl; sl; gkl; srl; ssl]); [solve_submseteq|exact Hnd_l] ]. }
        { eapply NoDup_cons_1_1. simpl. first [ eapply (submseteq_NoDup _ [sr; rr; gkr; srr; ssr]); [solve_submseteq|exact Hnd_r]
                | eapply (submseteq_NoDup _ [rl; sl; gkl; srl; ssl]); [solve_submseteq|exact Hnd_l] ]. }        
        iApply brel_na_close.
        iFrame. 
        iSplitR "HQ"; [iRight; iLeft; iExists _,_; iFrame "#"; iFrame|].
        iApply (brel_bind'' _ _ (to_iThyIfMono OS (iLblSig_to_iLblThy autheff)) _ _ _ (arcv_l _) (arcv_r _)).
        3 : { iApply to_iThy_le_intro'. 
              eassert (_ :: _ = [_] ++ _) as -> by done.
              eapply submseteq_app_middle. simpl.
              apply singleton_submseteq_l. constructor. }
        1,2 : set_unfold; tauto.
        iApply brel_mono; [iApply to_iThy_le_refl| |simpl].
        { iApply "Harcv". iExists _,_; by iLeft. }
        iIntros (v1' v2') "(%&%&[(->&->&->&->)|(->&->&->&->)])"...
        { iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"]. 
          iDestruct "HQ" as "[_ $]". }
        iApply (brel_na_inv _ _ alphaN); first set_solver.
        iFrame "HI".
        iIntros "(>[(Hlmr'&H')|[H2|H3]]&Hclose)".
        (* [lmr] already holds the message (persistently), so the "fresh"
           disjunct of the invariant is impossible. *)
        { iExFalso. by iDestruct (ghost_map_elem_ne with "Hlmr' Hlmr") as %?. }
        * iDestruct "H2" as "(%&%&_&_&_&_&Hlamr&Hlaml&_)".
          brel_load_r...
          brel_load_l... 
          iApply brel_na_close.
          iFrame. 
          iSplitR "HQ"; [iRight; iLeft; iExists _,_; iFrame "#"; iFrame|].
          iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"]. 
          iDestruct "HQ" as "[_ $]".
        * iDestruct "H3" as "(%&%&Hlmr'&_&_&_&Hlamr&Hlaml&Hγr3&Hι&%Hmb)".
          iDestruct (ghost_map_elem_agree with "Hlmr Hlmr'") as "->".
          brel_load_r.
          brel_load_l...
          iApply brel_na_close.
          iFrame. 
          iSplitR "HQ"; [iNext;iRight; iRight; iExists _,_; iFrame "#"; iFrame "Hlamr Hlaml Hγr3 Hι"; iPureIntro; exact Hmb|]...
          brel_load_l...
          iApply brel_int_of_vg_sem_correct_r.
          assert (int_of_vg_sem (g ^+ f_inv keyf x) = x) as ->.
          { exact (keyf_inv_spec x Hx). }
          iApply dec_correct_r.
          rewrite dec_enc_sem_correct.
          2 : { apply Nat.lt_succ_r. exact Hx. }
          2 : { exact Hmb. }
          iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"]. 
          iDestruct "HQ" as "[HQ _]".
          iApply "HQ".
      + iDestruct "H3" as "(%&%&#Hlmr&#Hlcr&#Hlcl&#Hlml&#Hlamr&#Hlaml&#Hγr&#Hι&%Hmb)".
        brel_load_r.
        brel_load_l...
        brel_cont_r.
        brel_cont_l...
        { eapply NoDup_cons_1_1. simpl. first [ eapply (submseteq_NoDup _ [sr; rr; gkr; srr; ssr]); [solve_submseteq|exact Hnd_r]
                | eapply (submseteq_NoDup _ [rl; sl; gkl; srl; ssl]); [solve_submseteq|exact Hnd_l] ]. }
        { eapply NoDup_cons_1_1. simpl. first [ eapply (submseteq_NoDup _ [sr; rr; gkr; srr; ssr]); [solve_submseteq|exact Hnd_r]
                | eapply (submseteq_NoDup _ [rl; sl; gkl; srl; ssl]); [solve_submseteq|exact Hnd_l] ]. }        
        iApply brel_na_close.
        iFrame. 
        iSplitR "HQ"; [iRight; iRight; iExists _,_; iFrame "#"; iFrame; iPureIntro; exact Hmb|].
        iApply (brel_bind'' _ _ (to_iThyIfMono OS (iLblSig_to_iLblThy autheff)) _ _ _ (arcv_l _) (arcv_r _)).
        3 : { iApply to_iThy_le_intro'. 
              eassert (_ :: _ = [_] ++ _) as -> by done.
              eapply submseteq_app_middle. simpl.
              apply singleton_submseteq_l. constructor. }
        1,2 : set_unfold; tauto.
        iApply brel_mono; [iApply to_iThy_le_refl| |simpl].
        { iApply "Harcv". iExists _,_; by iLeft. }
        iIntros (v1' v2') "(%&%&[(->&->&->&->)|(->&->&->&->)])"...
        { iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"]. 
          iDestruct "HQ" as "[_ $]". }
        brel_load_r.
        brel_load_l...
        brel_load_l...
        iApply brel_int_of_vg_sem_correct_r.
        assert (int_of_vg_sem (g ^+ f_inv keyf x) = x) as ->.
        { exact (keyf_inv_spec x Hx). }
        iApply dec_correct_r.
        rewrite dec_enc_sem_correct.
        2 : { apply Nat.lt_succ_r. exact Hx. }
        2 : { exact Hmb. } 
        iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"]. 
        iDestruct "HQ" as "[HQ _]".
        iApply "HQ".
  Qed. 

  Lemma sc_real_game1 : 
    ⊢ sem_typed [] sc_real game1 ⊥ τsc [].
  Proof using All with (brel_pures'; repeat foldkont). 
    iIntros (?) "!# _ //=". rewrite /sc_real /reduction /CHAN /RED_CHAN /right_composition.
    do 2 (rewrite !lookup_delete_eq; 
          rewrite lookup_delete_ne; last done).
    rewrite !lookup_delete_eq.
    brel_alloctape_r (ι) as "Hι"...
    iModIntro. iSplit; last done.
    iIntros (θL f1 f2) "Hff"...
    iIntros "!#" (autheff keyeff autheff_l autheff_r) "Hautheff".
    iDestruct "Hautheff" as (asnd_l asnd_r arcv_l arcv_r) "(%H1al & %H2al & (#Hasnd & #Harcv))"...
    iIntros "!>" (keyeff_l keyeff_r) "Hkeyeff".
    iDestruct "Hkeyeff" as (kysnd_l kysnd_r kyrcv_l kyrcv_r) "(%H1k & %H2k & (#Hkeysnd & #Hkeyrcv))".
    rewrite H1al H2al H1k H2k /F_OAUTH /F_KE_lazy_alice...
    
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
    brel_alloc_r lmr as "Hlmr"...
    brel_effect_l ssl as "Hssl".
    brel_effect_r ssr as "Hssr"...
    brel_effect_l srl as "Hsrl".
    brel_effect_r srr as "Hsrr"...

    (* Setting up clients *)
    set (θ := client_row  sl rl sr rr gkl gkr ssl srl ssr srr).
    iSpecialize ("Hff" $! θ).
    unfold sem_ty_arr, sem_ty_mbang. simpl.
    iAssert (sem_val_typed  ((λ: "m", do: ssl "m"), (λ: <>, do: srl bob))%V ((λ: "m", do: ssr "m") , (λ: <>, do: srr bob))%V (((sem_ty_nat -{ θ }-> 𝟙) × (𝟙 -{ θ }-> (Option ℕ)))%T)) as "Hschn".
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
                           ∨ (∃ c' m : nat, lml ↦□ SOMEV #m ∗ lcl ↦□ SOMEV #x ∗ lmr ↦ₛ□ SOMEV #m ∗ lcr ↦ₛ□ SOMEV #c'
                                            ∗ laml ↦ NONEV ∗ lamr ↦ₛ NONEV 
                                            ∗ γl ↪□N (n; []) ∗ ⌜(m ≤ msg_card)%nat⌝)
                           ∨ (∃ c' m : nat, lml ↦□ SOMEV #m ∗ lcl ↦□ SOMEV #x ∗ lmr ↦ₛ□ SOMEV #m ∗ lcr ↦ₛ□ SOMEV #c' 
                                            ∗ laml ↦□ SOMEV #(enc_sem (keyf x) m) ∗ lamr ↦ₛ□ SOMEV #(enc_sem (keyf x) m)
                                            ∗ γl ↪□N (n; []) ∗ (Loc ι) ↪ₛ□N (n; []) ∗ ⌜(m ≤ msg_card)%nat⌝)
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
    - brel_pures'; [apply neutral_ectx|apply neutral_ectx|]; repeat constructor.
      unfold msg_of_int...
      case_decide...
      2 : { iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V) with "[HQ]"); [set_solver|set_solver|by iApply "Hrel"|iApply "IH"]. }
      iApply (brel_na_inv _ _ alphaN); first set_solver.
      iFrame "HI".
      iIntros "(>[(Hlml&Hlcl&Hlmr&Hlcr&Hlaml&Hlamr&Hγl&Hι)|[H2|H3]]&Hclose)".
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
        { iModIntro. iRight. iLeft. iExists _, _. iFrame "#". iFrame. iPureIntro. lia. }
        
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
        { brel_cont_l. brel_cont_r... iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V) with "[HQ]"); [set_solver|set_solver|by iApply "Hrel"|iApply "IH"]. }
        brel_cont_l. 
        brel_cont_r...
        brel_rand_r...
        iApply brel_int_of_vg_sem_correct_l.
        assert (int_of_vg_sem (g ^+ x) = keyf x) as ->.
        { by rewrite (keyf_lt x Hx). }
        iApply enc_correct_l.
        iApply enc_correct_r.
        brel_pures'; simpl.
        { eapply NoDup_cons_1_1.
          eapply (submseteq_NoDup _ [rr; sr; gkr; srr; ssr]); [solve_submseteq|exact Hnd_r]. }
        { eapply NoDup_cons_1_1.
          eapply (submseteq_NoDup _ [sl; rl; gkl; srl; ssl]); [solve_submseteq|exact Hnd_l]. }
        iApply (brel_na_inv _ _ alphaN); first set_solver.
        iFrame "HI".
        iIntros "(>[(_&_&_&_&_&_&_&Hι')|[(%&%&_&_&_&_&Hlaml&Hlamr&_)|(%&%&_&_&_&_&_&_&_&Hι'&_)]]&Hclose)".
        (* The key tape [ι] has already been read, so the "fresh" and the
           "already sent" disjuncts are both impossible: each hands back an
           assertion for [ι] that cannot coexist with the one we hold. *)
        { iExFalso. iApply (spec_tapeN_excl with "Hι Hι'"). }
        2 : { iExFalso. iApply (spec_tapeN_excl with "Hι Hι'"). }
        brel_load_l...
        brel_load_r...
        brel_store_l...
        brel_store_r...

        iMod (ghost_map_elem_persist with "Hlaml") as "#Hlaml".
        iMod (ghost_map_elem_persist with "Hlamr") as "#Hlamr".
        iDestruct (spec_tape_to_persistent with "Hι") as ">#Hι".
        iApply brel_na_close.
        iFrame. iSplitR; [iNext; do 2 iRight; iExists _,_; iFrame "#"; iPureIntro; lia|].
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
        iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V) with "[HQ]"); [set_solver|set_solver|by iApply "Hrel"|iApply "IH"].
      + iDestruct "H2" as "(%&%&Hlml&Hlcl&Hlmr&Hlcr&Hγ)".
        brel_load_l.
        brel_load_r...
        iApply brel_na_close.
        iFrame. 
        iSplitR "HQ"; [iRight; iLeft; iExists _,_; iFrame|].
        iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V) with "[HQ]"); [set_solver|set_solver|by iApply "Hrel"|iApply "IH"].
      + iDestruct "H3" as "(%&%&Hlml&Hlcl&Hlmr&Hlaml&Hlamr&Hι)".
        brel_load_l.
        brel_load_r...
        iApply brel_na_close.
        iFrame. 
        iSplitR "HQ"; [iRight; iRight; iExists _,_; iFrame|].
        iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V) with "[HQ]"); [set_solver|set_solver|by iApply "Hrel"|iApply "IH"].
    (* Bob tries to receive a message *)
    - brel_pures'.
      {  apply not_elem_of_cons; split; last (apply neutral_ectx; repeat constructor).
         intro Heq.
         apply NoDup_ListNoDup in Hnd_r.
         do 4 (apply NoDup_cons_iff in Hnd_r as [?Hn Hnd_r]). 
         apply Hn2. by left. }
      {  apply not_elem_of_cons; split; last (apply neutral_ectx; repeat constructor).
         intro Heq.
         apply NoDup_ListNoDup in Hnd_l.
         do 4 (apply NoDup_cons_iff in Hnd_l as [?Hn Hnd_l]). 
         apply Hn2. by left. }
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
      { brel_cont_l. brel_cont_r... 
        iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"]. 
        iDestruct "HQ" as "[_ $]". }
      iApply (brel_bind'' [AppRCtx _] [AppRCtx _] (to_iThyIfMono OS (iLblSig_to_iLblThy keyeff))); try (apply list_subseteq_nil).
      { iApply to_iThy_le_intro'. solve_submseteq. }
      iApply brel_mono; [iApply to_iThy_le_refl| |simpl].
      { iApply "Hkeysnd". iExists _, _. by iRight. }
      iIntros (v1 v2) "(->&->)"...      
      iApply (brel_na_inv _ _ alphaN); first set_solver.
      iFrame "HI".
      iIntros "(>[(Hlml&Hlcl&Hlmr&Hlcr&Hlaml&Hlamr&Hγl&Hι)|[H2|H3]]&Hclose)".
      + brel_load_l...
        brel_load_r...
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
        { eapply NoDup_cons_1_1. simpl.
          eapply (submseteq_NoDup _ [rr; sr; gkr; srr; ssr]); [solve_submseteq | exact Hnd_r]. }
        { eapply NoDup_cons_1_1. simpl.
          eapply (submseteq_NoDup _ [sl; rl; gkl; srl; ssl]); [solve_submseteq|exact Hnd_l]. }        
        iApply brel_na_close.
        iFrame. 
        iSplitR "HQ"; [iRight; iLeft; iExists _,_; iFrame "#"; iFrame|].
        iApply (brel_bind'' _ _ (to_iThyIfMono OS (iLblSig_to_iLblThy autheff)) _ _ _ (arcv_l _) (arcv_r _)).
        3 : { iApply to_iThy_le_intro'. 
              eassert (_ :: _ = [_] ++ _) as -> by done.
              eapply submseteq_app_middle. simpl.
              apply singleton_submseteq_l. constructor. }
        1,2 : set_unfold; tauto.
        iApply brel_mono; [iApply to_iThy_le_refl| |simpl].
        { iApply "Harcv". iExists _,_; by iLeft. }
        iIntros (v1' v2') "(%&%&[(->&->&->&->)|(->&->&->&->)])"...
        { iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"]. 
          iDestruct "HQ" as "[_ $]". }
        iApply (brel_na_inv _ _ alphaN); first set_solver.
        iFrame "HI".
        iIntros "(>[(Hlml'&H')|[H2|H3]]&Hclose)".
        (* [lml] already holds the message (persistently), so the "fresh"
           disjunct of the invariant is impossible. *)
        { iExFalso. by iDestruct (ghost_map_elem_ne with "Hlml' Hlml") as %?. }
        * iDestruct "H2" as "(%&%&_&_&_&_&Hlaml&Hlamr&_)".
          brel_load_l...
          brel_load_r... 
          iApply brel_na_close.
          iFrame. 
          iSplitR "HQ"; [iRight; iLeft; iExists _,_; iFrame "#"; iFrame|].
          iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"]. 
          iDestruct "HQ" as "[_ $]".
        * iDestruct "H3" as "(%&%&Hlml'&_&_&_&Hlaml&Hlamr&Hγl3&Hι&%Hmb)".
          iDestruct (ghost_map_elem_agree with "Hlml Hlml'") as "->".
          brel_load_l.
          brel_load_r...
          iApply brel_na_close.
          iFrame. 
          iSplitR "HQ"; [iNext;iRight; iRight; iExists _,_; iFrame "#"; iFrame "Hlaml Hlamr Hγl3 Hι"; iPureIntro; exact Hmb|]...
          brel_load_r...
          iApply brel_int_of_vg_sem_correct_l.
          assert (int_of_vg_sem (g ^+ x) = keyf x) as ->.
          { by rewrite (keyf_lt x Hx). }
          iApply dec_correct_l.
          rewrite dec_enc_sem_correct.
          2 : { apply Nat.lt_succ_r. exact (keyf_dom x Hx). }
          2 : { exact Hmb. }
          iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"]. 
          iDestruct "HQ" as "[HQ _]".
          iApply "HQ".
      + iDestruct "H3" as "(%&%&#Hlml&#Hlcl&#Hlcr&#Hlmr&#Hlaml&#Hlamr&#Hγl&#Hι&%Hmb)".
        brel_load_l.
        brel_load_r...
        brel_cont_l.
        brel_cont_r...
        { eapply NoDup_cons_1_1. simpl.
          eapply (submseteq_NoDup _ [rr; sr; gkr; srr; ssr]); [solve_submseteq | exact Hnd_r]. }
        { eapply NoDup_cons_1_1. simpl.
          eapply (submseteq_NoDup _ [sl; rl; gkl; srl; ssl]); [solve_submseteq|exact Hnd_l]. }        
        iApply brel_na_close.
        iFrame. 
        iSplitR "HQ"; [iRight; iRight; iExists _,_; iFrame "#"; iFrame; iPureIntro; exact Hmb|].
        iApply (brel_bind'' _ _ (to_iThyIfMono OS (iLblSig_to_iLblThy autheff)) _ _ _ (arcv_l _) (arcv_r _)).
        3 : { iApply to_iThy_le_intro'. 
              eassert (_ :: _ = [_] ++ _) as -> by done.
              eapply submseteq_app_middle. simpl.
              apply singleton_submseteq_l. constructor. }
        1,2 : set_unfold; tauto.
        iApply brel_mono; [iApply to_iThy_le_refl| |simpl].
        { iApply "Harcv". iExists _,_; by iLeft. }
        iIntros (v1' v2') "(%&%&[(->&->&->&->)|(->&->&->&->)])"...
        { iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"]. 
          iDestruct "HQ" as "[_ $]". }
        brel_load_l.
        brel_load_r...
        brel_load_r...
        iApply brel_int_of_vg_sem_correct_l.
        assert (int_of_vg_sem (g ^+ x) = keyf x) as ->.
        { by rewrite (keyf_lt x Hx). }
        iApply dec_correct_l.
        rewrite dec_enc_sem_correct.
        2 : { apply Nat.lt_succ_r. exact (keyf_dom x Hx). }
        2 : { exact Hmb. } 
        iApply (brel_exhaustion (fill k1' _) (fill k2' _) with "[HQ]"); [set_solver|set_solver|iApply "Hrel"|iApply "IH"]. 
        iDestruct "HQ" as "[HQ _]".
        iApply "HQ".
  Qed. 


End schan_security.

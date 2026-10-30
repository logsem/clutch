From iris.proofmode Require Import base proofmode classes.                                             
From iris.base_logic.lib Require Import  na_invariants.   
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode
  spec_rules spec_ra
  class_instances.
From clutch.prob_eff_lang.probblaze Require Import tactics.
From clutch.prob_eff_lang.probblaze Require Import sem_types sem_row sem_sig sem_judgement sem_def.
From clutch.prob_eff_lang.probblaze.examples Require Import ske ske_sec_chan_def.


Import fingroup.

Import fingroup.fingroup.

Import valgroup_notation.
Import valgroup_tactics.


Section schan_common.
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
  (* The channel hands back a DECODED message, i.e. a value of the abstract
     message space, not its integer code: [CHAN] returns [SOME (dec key m)] and
     [RED_CHAN] / [F_CHAN] return the stored [!"message"], all of which are
     [fvtval]s.  Hence the quantifier ranges over [mt], not over [nat]. *)
  Program Definition RecvSecB (srecv1 srecv2 : label) : iThy Σ :=
    λ e1 e2, (λne Q,
                ⌜ e1 = do: srecv1 bob ⌝%E ∗
                ⌜ e2 = do: srecv2 bob ⌝%E ∗
                ((∀ mv : mt, Q (SOMEV (fvtval mv)) (SOMEV (fvtval mv))) ∧ Q NONEV NONEV)
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
      - iIntros (mv). iApply brel_value. iIntros "$ !>".
        iExists _,_; iRight; iPureIntro; do 2 (split; first done); by exists mv.
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

  (* Under the [fin_val] interface the key is passed to [enc]/[dec] as a group
     VALUE, so the scheme never applies [int_of_vg] and the proof never needs
     [brel_int_of_vg_sem_correct_*].  What it needs instead is the other
     direction: the key code drawn on the [game1] side DECODES to exactly the
     DH key held on the [sc_real] side.  Both directions of the coupling are
     immediate from [int_of_vg_of_int_sem] once [keyf] has been unfolded. *)
  Lemma vg_of_int_sem_keyf (x : nat) :
    (x < S n)%nat → vg_of_int_sem (keyf x) = Some (g ^+ x)%g.
  Proof. intros Hx. rewrite (keyf_lt x Hx). apply int_of_vg_of_int_sem. Qed.

  (* [vgval] and the key space's [fin_val] injection are the same function, but
     not the same TERM.  [enc_correct_*]/[dec_correct_*] are matched against the
     goal up to syntax (their [fill K] leaves [K] an evar), so a key that the
     key exchange produced as [vgval k] has to be rewritten into [fvtval] form
     before those rules apply. *)
  Lemma vgval_fvtval (k : vgG) : vgval k = fvtval (fin_val_type := vg_fv) k.
  Proof. reflexivity. Qed.

  Lemma vg_of_int_sem_keyf_inv (d : nat) :
    (d < S n)%nat → vg_of_int_sem d = Some (g ^+ f_inv keyf d)%g.
  (* NB: rewriting with [keyf_inv_spec] right-to-left in the goal would also hit
     the [d] under [f_inv keyf]; rewrite left-to-right in the round-trip law
     instead, whose right-hand side does not mention the code. *)
  Proof.
    intros Hd. pose proof (int_of_vg_of_int_sem (g ^+ f_inv keyf d)%g) as Hr.
    by rewrite (keyf_inv_spec d Hd) in Hr.
  Qed.

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

  Definition τsc :=  (∀ᵣ θ__L ,(∀ᵣ θₕ, (((sem_ty_nat -{ θₕ }->  𝟙) × (𝟙 -{ θₕ }-> (Option msg.(sem_τFT)))) -{ sem_row_union  θₕ θ__L }-∘ 𝟙)) ⊸ (*type of client*)
                  (∀ᵣ θ₁, ∀ᵣ θ₂,  ((((cipher.(sem_τFT) × (𝟙 + 𝟙)) -{ θ₁ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ₁ }-> Option 𝟙)) × (((𝟙 + 𝟙) -{ θ₂ }-> 𝟙) × (𝟙 + 𝟙) -{ θ₂ }-> Option 𝟙)) -{ sem_row_union (¡θ₁) (sem_row_union (¡θ₂)%R θ__L) }-∘ 𝟙))%T.
End schan_common.

From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode
  spec_rules spec_ra class_instances.
From clutch.prob_eff_lang.probblaze Require Import tactics.
From clutch.prob_eff_lang.probblaze Require Import sem_types sem_row sem_sig sem_judgement sem_def.
From clutch.prob_eff_lang.probblaze.examples.secure_add3 Require Import add3_def add3_tbl.

Import valgroup_notation.
Import valgroup_tactics.

(** A relational specification of one session of the network.

    The two mailboxes (left and right) are related by a persistent relation
    [Rmsg] on the messages stored under each key; the client sees the network
    through the theory [NetThy], which hands out messages related by [Rdeliv]
    (after the two networks' patches). *)

Section net.
  Context `{probblazeRGS Σ}.

  (* The key of header [(s, d, t)], as computed by [hkey]. *)
  Definition key (s d t : Z) : Z := 6 * s + 2 * d + t.

  (* Headers of the three-party protocol: [hkey] is injective on them. *)
  Definition hdr_ok (s d t : Z) : Prop := (0 ≤ s < 3 ∧ 0 ≤ d < 3 ∧ 0 ≤ t < 2)%Z.

  Lemma key_inj s d t s' d' t' :
    hdr_ok s d t → hdr_ok s' d' t' → key s d t = key s' d' t' → s = s' ∧ d = d' ∧ t = t'.
  Proof. rewrite /hdr_ok /key. lia. Qed.

  (* The endpoints F_NET hands to its client in a session with label [l]. *)
  Definition net_ep (l : label) (i : Z) : val :=
    ((λ: "msg", do: l (InjL (#i, "msg"))), (λ: "h", do: l (InjR (#i, "h"))))%V.
  Definition net_eps (l : label) : val := (net_ep l 0, net_ep l 1, net_ep l 2)%V.

  Definition net_inv (ℓ1 ℓ2 : loc) (Rmsg : Z → val → val → iProp Σ) : iProp Σ :=
    ∃ v1 v2 M1 M2,
      ℓ1 ↦ v1 ∗ ℓ2 ↦ₛ v2 ∗ ⌜is_tbl v1 M1⌝ ∗ ⌜is_tbl v2 M2⌝ ∗
      [∗ map] k ↦ m1; m2 ∈ M1; M2, Rmsg k m1 m2.

  (* Sends with equal headers and [Rmsg]-related messages; receives with equal
     headers, answered by [Rdeliv]-related messages. *)
  Program Definition NetThy (Rmsg Rdeliv : Z → val → val → iProp Σ) (l1 l2 : label) : iThy Σ :=
    λ e1 e2, (λne Q,
      (∃ (i d t : Z) (m1 m2 : val),
          ⌜e1 = do: l1 (InjLV (#i, ((#d, #t), m1)))⌝%E ∗
          ⌜e2 = do: l2 (InjLV (#i, ((#d, #t), m2)))⌝%E ∗
          Rmsg (key i d t) m1 m2 ∗ Q #()%V #()%V) ∨
      (∃ (d s t : Z),
          ⌜e1 = do: l1 (InjRV (#d, (#s, #t)))⌝%E ∗
          ⌜e2 = do: l2 (InjRV (#d, (#s, #t)))⌝%E ∗
          ⌜hdr_ok s d t⌝ ∗ (∀ u1 u2, Rdeliv (key s d t) u1 u2 -∗ Q u1 u2)))%I.
  Next Obligation. solve_proper. Qed.

  (* [f] can be called on a header from inside the network's handler, which
     runs with labels [l1s], [l2s] in a context with theories [L]. *)
  Definition env_op_spec (L : iLblThy Σ) (f1 f2 : val) : iProp Σ :=
    □ ∀ l1s l2s k1 k2 (s d t : Z) S,
      ⌜ectx_labels k1 ⊆ l1s⌝ → ⌜ectx_labels k2 ⊆ l2s⌝ →
      BREL fill k1 #()%V ≤ fill k2 #()%V <|(l1s, l2s, iThyBot) :: L|> {{S}} -∗
      BREL fill k1 (f1 (#s, #d, #t)%V) ≤ fill k2 (f2 (#s, #d, #t)%V)
        <|(l1s, l2s, iThyBot) :: L|> {{S}}.

  (* The patches turn [Rmsg]-related messages into [Rdeliv]-related ones. *)
  Definition patch_spec (L : iLblThy Σ) (p1 p2 : val) (Rmsg Rdeliv : Z → val → val → iProp Σ) : iProp Σ :=
    □ ∀ l1s l2s k1 k2 (s d t : Z) m1 m2 S,
      ⌜ectx_labels k1 ⊆ l1s⌝ → ⌜ectx_labels k2 ⊆ l2s⌝ → ⌜hdr_ok s d t⌝ →
      Rmsg (key s d t) m1 m2 -∗
      (∀ u1 u2, Rdeliv (key s d t) u1 u2 -∗
         BREL fill k1 u1 ≤ fill k2 u2 <|(l1s, l2s, iThyBot) :: L|> {{S}}) -∗
      BREL fill k1 (p1 #s #d #t m1) ≤ fill k2 (p2 #s #d #t m2)
        <|(l1s, l2s, iThyBot) :: L|> {{S}}.

  (* One request, handled from inside the session's handler, whose labels
     are [l1s], [l2s]; [c1], [c2] are the captured continuations. *)
  Lemma net_handle_send_spec N (p1 p2 : val) (ℓ1 ℓ2 : loc) (nl1 nl2 w1 w2 : val) Rmsg L
    l1s l2s (i d t : Z) (m1 m2 c1 c2 : val) S
    `{!∀ k m1 m2, Persistent (Rmsg k m1 m2), !∀ k m1 m2, Timeless (Rmsg k m1 m2)} :
    na_invP N (net_inv ℓ1 ℓ2 Rmsg) -∗
    env_op_spec L nl1 nl2 -∗
    Rmsg (key i d t) m1 m2 -∗
    BREL c1 #()%V ≤ c2 #()%V <|(l1s, l2s, iThyBot) :: L|> {{S}} -∗
    BREL net_handle p1 #ℓ1 nl1 w1 (InjLV (#i, ((#d, #t), m1))) c1
       ≤ net_handle p2 #ℓ2 nl2 w2 (InjLV (#i, ((#d, #t), m2))) c2
      <|(l1s, l2s, iThyBot) :: L|> {{S}}.
  Proof.
    iIntros "#Hinv #Hnl #Hm Hc".
    rewrite /net_handle /hkey. brel_pures.
    iApply (brel_na_inv _ _ N); first set_solver. iFrame "Hinv".
    iIntros "[(%v1 & %v2 & %M1 & %M2 & >Hl1 & >Hl2 & >%Htb1 & >%Htb2 & >HM) Hclose]".
    brel_load_l. brel_load_r. rewrite -/(key i d t).
    iApply (brel_tbl_lookup_l _ [AppRCtx _; CaseCtx _ _]); first done.
    iApply (brel_tbl_lookup_r _ [AppRCtx _; CaseCtx _ _]); first done.
    iDestruct (big_sepM2_lookup_iff with "HM") as %Hdom.
    specialize (Hdom (key i d t)). simpl.
    destruct (M1 !! key i d t) eqn:HM1, (M2 !! key i d t) eqn:HM2;
      [| exfalso; by apply (is_Some_None (A:=val)), Hdom
       | exfalso; by apply (is_Some_None (A:=val)), Hdom |].
    - (* already sent: nothing changes *)
      rewrite /optv. brel_pures.
      iApply brel_na_close. iFrame "Hclose Hc". iFrame "∗ %".
    - (* first send: store it and leak the header *)
      rewrite /optv /tbl_add. brel_pures.
      brel_load_l. brel_load_r. brel_pures.
      brel_store_l. brel_store_r. brel_pures.
      iApply brel_na_close. iFrame "Hclose".
      iSplitR "Hc".
      { iExists _, _, (<[key i d t := m1]> M1), (<[key i d t := m2]> M2). iFrame.
        iNext. iSplit; [iPureIntro; by apply is_tbl_add|].
        iSplit; [iPureIntro; by apply is_tbl_add|].
        iApply (big_sepM2_insert_2 with "Hm HM"). }
      iApply ("Hnl" $! l1s l2s [AppRCtx _] [AppRCtx _]);
        [iPureIntro; simpl; set_solver.. |].
      simpl. brel_pures. done.
  Qed.

  Lemma net_handle_recv_spec N (p1 p2 : val) (ℓ1 ℓ2 : loc) (nl1 nl2 w1 w2 : val) Rmsg Rdeliv L
    l1s l2s (d s t : Z) (c1 c2 : val) S
    `{!∀ k m1 m2, Persistent (Rmsg k m1 m2), !∀ k m1 m2, Timeless (Rmsg k m1 m2)} :
    hdr_ok s d t →
    na_invP N (net_inv ℓ1 ℓ2 Rmsg) -∗
    env_op_spec L w1 w2 -∗
    patch_spec L p1 p2 Rmsg Rdeliv -∗
    (∀ u1 u2, Rdeliv (key s d t) u1 u2 -∗
       BREL c1 u1 ≤ c2 u2 <|(l1s, l2s, iThyBot) :: L|> {{S}}) -∗
    BREL net_handle p1 #ℓ1 nl1 w1 (InjRV (#d, (#s, #t))) c1
       ≤ net_handle p2 #ℓ2 nl2 w2 (InjRV (#d, (#s, #t))) c2
      <|(l1s, l2s, iThyBot) :: L|> {{S}}.
  Proof.
    iIntros (Hhdr) "#Hinv #Hw #Hp Hc".
    rewrite /net_handle /hkey. brel_pures.
    (* one attempt *)
    iLöb as "IH".
    iApply ("Hw" $! l1s l2s [AppRCtx _; AppRCtx _] [AppRCtx _; AppRCtx _]);
      [iPureIntro; simpl; set_solver.. |].
    simpl. brel_pures.
    iApply (brel_na_inv _ _ N); first set_solver. iFrame "Hinv".
    iIntros "[(%v1 & %v2 & %M1 & %M2 & >Hl1 & >Hl2 & >%Htb1 & >%Htb2 & >HM) Hclose]".
    brel_load_l. brel_load_r. rewrite -/(key s d t).
    iApply (brel_tbl_lookup_l _ [AppRCtx _; CaseCtx _ _]); first done.
    iApply (brel_tbl_lookup_r _ [AppRCtx _; CaseCtx _ _]); first done.
    iDestruct (big_sepM2_lookup_iff with "HM") as %Hdom.
    specialize (Hdom (key s d t)). simpl.
    destruct (M1 !! key s d t) as [u1|] eqn:HM1, (M2 !! key s d t) as [u2|] eqn:HM2;
      [| exfalso; by apply (is_Some_None (A:=val)), Hdom
       | exfalso; by apply (is_Some_None (A:=val)), Hdom |].
    - (* delivered, through the patches *)
      iDestruct (big_sepM2_lookup with "HM") as "#Hu"; [done|done|].
      iApply brel_na_close. iFrame "Hclose". iSplitL "Hl1 Hl2 HM"; [iFrame "∗ %"|].
      rewrite /optv. brel_pures.
      iApply ("Hp" $! l1s l2s [AppRCtx _] [AppRCtx _] with "[] [] [] Hu");
        [iPureIntro; simpl; set_solver.. | done |].
      simpl. iApply "Hc".
    - (* not there yet: try again *)
      iApply brel_na_close. iFrame "Hclose". iSplitL "Hl1 Hl2 HM"; [iFrame "∗ %"|].
      rewrite /optv. brel_pures.
      by iApply "IH".
  Qed.

  Lemma brel_sel3_net K1 K2 l1 l2 (j : Z) L R :
    (0 ≤ j < 3)%Z →
    BREL fill K1 (net_ep l1 j) ≤ fill K2 (net_ep l2 j) <|L|> {{R}} ⊢
    BREL fill K1 (sel3 (net_eps l1) #j) ≤ fill K2 (sel3 (net_eps l2) #j) <|L|> {{R}}.
  Proof.
    intros Hj. iIntros "H". rewrite /sel3 /net_eps.
    assert (j = 0 ∨ j = 1 ∨ j = 2)%Z as [ -> | [ -> | -> ] ] by lia; by brel_pures.
  Qed.

  (** The client's side: sending and receiving under [NetThy]. *)
  Lemma brel_net_send (Rmsg Rdeliv : Z → val → val → iProp Σ) l1 l2 L K1 K2 (i d t : Z) (m1 m2 : val) R :
    NeutralEctx [l1] K1 → NeutralEctx [l2] K2 →
    Rmsg (key i d t) m1 m2 -∗
    BREL fill K1 #()%V ≤ fill K2 #()%V <|([l1], [l2], NetThy Rmsg Rdeliv l1 l2) :: L|> {{R}} -∗
    BREL fill K1 (do: l1 (InjLV (#i, ((#d, #t), m1))))
       ≤ fill K2 (do: l2 (InjLV (#i, ((#d, #t), m2))))
      <|([l1], [l2], NetThy Rmsg Rdeliv l1 l2) :: L|> {{R}}.
  Proof.
    iIntros (HK1 HK2) "Hm Hk".
    iApply brel_introduction'; first by left.
    iExists _, _, K1, K2,
      (λ s1 s2 : expr, ⌜s1 = #()%V⌝ ∗ ⌜s2 = #()%V⌝ ∗
         BREL fill K1 #()%V ≤ fill K2 #()%V
           <|([l1], [l2], NetThy Rmsg Rdeliv l1 l2) :: L|> {{R}})%I.
    do 4 (iSplit; first done).
    iSplitL.
    - iLeft. iExists i, d, t, m1, m2. by iFrame.
    - iIntros "!>" (s1 s2) "(-> & -> & $)".
  Qed.

  Lemma brel_net_recv (Rmsg Rdeliv : Z → val → val → iProp Σ) l1 l2 L K1 K2 (d s t : Z) R :
    NeutralEctx [l1] K1 → NeutralEctx [l2] K2 → hdr_ok s d t →
    (∀ u1 u2 : val, Rdeliv (key s d t) u1 u2 -∗
       BREL fill K1 u1 ≤ fill K2 u2 <|([l1], [l2], NetThy Rmsg Rdeliv l1 l2) :: L|> {{R}}) -∗
    BREL fill K1 (do: l1 (InjRV (#d, (#s, #t))))
       ≤ fill K2 (do: l2 (InjRV (#d, (#s, #t))))
      <|([l1], [l2], NetThy Rmsg Rdeliv l1 l2) :: L|> {{R}}.
  Proof.
    iIntros (HK1 HK2 Hhdr) "Hk".
    iApply brel_introduction'; first by left.
    iExists _, _, K1, K2,
      (λ s1 s2 : expr, BREL fill K1 s1 ≤ fill K2 s2
           <|([l1], [l2], NetThy Rmsg Rdeliv l1 l2) :: L|> {{R}})%I.
    do 4 (iSplit; first done).
    iSplitL.
    - iRight. iExists d, s, t. do 3 (iSplit; first done). iIntros (u1 u2) "Hu". by iApply "Hk".
    - iIntros "!>" (s1 s2) "$".
  Qed.

  Lemma F_NET_sess_spec N (p1 p2 : val) (ℓ1 ℓ2 : loc) (f1 f2 nl1 nl2 w1 w2 : val) Rmsg Rdeliv L R
    `{!∀ k m1 m2, Persistent (Rmsg k m1 m2), !∀ k m1 m2, Timeless (Rmsg k m1 m2)} :
    na_invP N (net_inv ℓ1 ℓ2 Rmsg) -∗
    env_op_spec L nl1 nl2 -∗
    env_op_spec L w1 w2 -∗
    patch_spec L p1 p2 Rmsg Rdeliv -∗
    (∀ l1 l2, BREL App f1 (net_eps l1) ≤ App f2 (net_eps l2)
                <|([l1], [l2], NetThy Rmsg Rdeliv l1 l2) :: L|> {{R}}) -∗
    BREL F_NET_sess p1 #ℓ1 f1 (nl1, w1)%V ≤ F_NET_sess p2 #ℓ2 f2 (nl2, w2)%V <|L|> {{R}}.
  Proof.
    iIntros "#Hinv #Hnl #Hw #Hp Hf".
    rewrite /F_NET_sess. brel_pures.
    brel_effect_l net1 as "Hn1". brel_effect_r net2 as "Hn2". brel_pures.
    iApply brel_new_theory.
    iApply (brel_add_label_l with "Hn1").
    iApply (brel_add_label_r with "Hn2").
    iApply (brel_exhaustion (f1 _) (f2 _) _ _ (NetThy Rmsg Rdeliv net1 net2) with "[Hf]");
      [set_unfold; tauto | set_unfold; tauto | by iApply "Hf" | ].
    iLöb as "IH".
    iSplit; [iIntros "!>" (v1 v2) "HR"; brel_pures; iModIntro; done |].
    iIntros "!>" (k1 k2 e1 e2 Q) "%Hk1 %Hk2 HXQ #Hrel".
    iDestruct "HXQ" as "[(%i & %d & %t & %m1 & %m2 & -> & -> & #Hm & HQ)
                       | (%d & %s & %t & -> & -> & %Hhdr & HQ)]".
    - (* send *)
      brel_handle_os_l ka as "Hka". brel_handle_os_r kb as "Hkb". brel_pures.
      iApply (net_handle_send_spec with "Hinv Hnl Hm").
      brel_cont_l. brel_cont_r.
      iApply (brel_exhaustion (fill k1 #()%V) (fill k2 #()%V) with "[HQ]");
        [set_unfold; tauto | set_unfold; tauto | by iApply "Hrel" | iApply "IH"].
    - (* receive *)
      brel_handle_os_l ka as "Hka". brel_handle_os_r kb as "Hkb". brel_pures.
      iApply (net_handle_recv_spec with "Hinv Hw Hp"); first done.
      iIntros (u1 u2) "Hu".
      brel_cont_l. brel_cont_r.
      iApply (brel_exhaustion (fill k1 u1) (fill k2 u2) with "[Hu HQ]");
        [set_unfold; tauto | set_unfold; tauto | iApply "Hrel"; by iApply ("HQ" with "Hu") | iApply "IH"].
  Qed.

End net.

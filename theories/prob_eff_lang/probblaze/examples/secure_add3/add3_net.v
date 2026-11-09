From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode
  spec_rules spec_ra class_instances.
From clutch.prob_eff_lang.probblaze Require Import tactics.
From clutch.prob_eff_lang.probblaze Require Import sem_types sem_row sem_sig sem_judgement sem_def.
From iris.bi Require Import monpred.
From iris.proofmode Require Import monpred.
From clutch.prob_eff_lang.probblaze.examples.secure_add3 Require Import add3_def add3_tbl.
From clutch.prob_eff_lang.probblaze.eq Require Import eq_logic eq_handlers eq_compat.

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

  Lemma NetThy_mono Rmsg Rdeliv l1 l2 : iThy_mono (NetThy Rmsg Rdeliv l1 l2).
  Proof.
    iIntros (e1 e2 Q Q') "[[(%i & %d & %t & %m1 & %m2 & -> & -> & Hm & HQ)|(%d & %s & %t & -> & -> & %Hhdr & HQ)] HQQ]".
    - iLeft. iExists i, d, t, m1, m2. iFrame. do 2 (iSplit; first done). by iApply "HQQ".
    - iRight. iExists d, s, t. do 3 (iSplit; first done). iIntros (u1 u2) "Hu". iApply "HQQ". by iApply "HQ".
  Qed.

  (* Headers are values of the header type. *)
  Lemma hdr_typed (s d t : Z) : ⊢ (τ_hdr : sem_ty Σ) (#s, #d, #t)%V (#s, #d, #t)%V.
  Proof.
    rewrite /τ_hdr /sem_ty_prod.
    iExists _, _, _, _. repeat iSplit; try done; last by iExists _.
    iExists _, _, _, _. repeat iSplit; try done; by iExists _.
  Qed.

End net.

(** * The network in the logic for equivalences

    The program [l] uses the mailbox [ℓl], the program [r] the mailbox
    [ℓr]; [Rmsg] relates the message of [l] stored under a key to the one
    of [r]. *)

Section net_eq.
  Context `{probblazeRGS Σ}.
  #[local] Open Scope bi_scope.

  (* The network's theory, with the labels of [l] ([ll]) and of [r] ([lr]);
     the relations [Rmsg] and [Rdeliv] relate a message of [l] to one of [r],
     so in direction [Bwd] they are flipped. *)
  Definition flipR (R : Z → val → val → iProp Σ) : Z → val → val → iProp Σ := λ k v1 v2, R k v2 v1.

  Definition net_thy (Rmsg Rdeliv : Z → val → val → iProp Σ) (ll lr : label) : dir → iThy Σ :=
    λ d, match d with
         | Fwd => NetThy Rmsg Rdeliv ll lr
         | Bwd => NetThy (flipR Rmsg) (flipR Rdeliv) lr ll
         end.

  Lemma net_thy_sym Rmsg Rdeliv ll lr : eq_thy_sym (net_thy Rmsg Rdeliv ll lr).
  Proof.
    intros e1 e2 Q. rewrite /net_thy /flipR /=.
    iSplit; iIntros "[(%i & %d & %t & %m1 & %m2 & -> & -> & Hm & HQ)|(%d & %s & %t & -> & -> & %Hhdr & HQ)]".
    1,3: iLeft; iExists i, d, t, m2, m1; by iFrame.
    all: iRight; iExists d, s, t; do 3 (iSplit; first done); iIntros (u1 u2) "Hu"; iApply ("HQ" $! u2 u1 with "Hu").
  Qed.

  Lemma eq_tbl_lookup_l E K er X R v M (k : Z) :
    is_tbl v M →
    EQ fill K (optv (M !! k)) ≈ er @ E <|X|> {{ R }} ⊢ EQ fill K (tbl_lookup v #k) ≈ er @ E <|X|> {{ R }}.
  Proof. intros Htbl. apply eq_step_l=> e S; [by apply brel_tbl_lookup_l|by apply brel_tbl_lookup_r]. Qed.

  Lemma eq_tbl_lookup_r E K el X R v M (k : Z) :
    is_tbl v M →
    EQ el ≈ fill K (optv (M !! k)) @ E <|X|> {{ R }} ⊢ EQ el ≈ fill K (tbl_lookup v #k) @ E <|X|> {{ R }}.
  Proof. intros Htbl. apply eq_step_r=> e S; [by apply brel_tbl_lookup_l|by apply brel_tbl_lookup_r]. Qed.

  (* The two mailboxes, with [Rmsg]-related messages under each key. *)
  Definition eq_net_inv (ℓl ℓr : loc) (Rmsg : Z → val → val → iProp Σ) : iPropD Σ :=
    ∃ vl vr Ml Mr,
      ℓl ↦ₗ vl ∗ ℓr ↦ᵣ vr ∗ ⌜is_tbl vl Ml⌝ ∗ ⌜is_tbl vr Mr⌝ ∗
      ⎡[∗ map] k ↦ ml; mr ∈ Ml; Mr, Rmsg k ml mr⎤.

  (* The network's invariant, for two empty mailboxes. *)
  Lemma eq_net_inv_alloc (ℓl ℓr : loc) (vl vr : val) Rmsg :
    is_tbl vl ∅ → is_tbl vr ∅ → ℓl ↦ₗ vl ∗ ℓr ↦ᵣ vr ⊢ eq_net_inv ℓl ℓr Rmsg.
  Proof.
    iIntros (Hl Hr) "[H1 H2]". iExists _, _, ∅, ∅. iFrame. do 2 (iSplit; first done).
    by rewrite big_sepM2_empty embed_emp.
  Qed.

  (* The patches turn [Rmsg]-related messages into [Rdeliv]-related ones; they
     are called from inside the network's handler, whose labels are [lls],
     [rls]. *)
  Definition eq_patch_spec_eq (X : eqThy Σ) (pl pr : val) (Rmsg Rdeliv : Z → val → val → iProp Σ) : iPropD Σ :=
    □ ∀ lls rls kl kr (s d t : Z) (ml mr : val) (S : val → val → iPropD Σ),
      ⌜hdr_ok s d t⌝ -∗ ⎡Rmsg (key s d t) ml mr⎤ -∗
      (∀ ul ur, ⎡Rdeliv (key s d t) ul ur⎤ -∗
         EQ fill kl ul ≈ fill kr ur <|eq_thy_cons lls rls (λ _, iThyBot) X|> {{ S }}) -∗
      EQ fill kl (pl #s #d #t ml) ≈ fill kr (pr #s #d #t mr) <|eq_thy_cons lls rls (λ _, iThyBot) X|> {{ S }}.

  Section sess.
    Context (θ L : sem_row Σ).
    Local Notation X := (iLblSig_to_iLblThy (sem_row_union (¡ θ)%R L)).

    (* One request, handled from inside the session's handler, whose labels
       are [lls], [rls]; [cl], [cr] are the captured continuations. *)
    Lemma eq_net_handle_send N (pl pr : val) (ℓl ℓr : loc) (nll nlr wl wr : val) Rmsg
      lls rls (i d t : Z) (ml mr cl cr : val) S
      `{!∀ k m1 m2, Persistent (Rmsg k m1 m2), !∀ k m1 m2, Timeless (Rmsg k m1 m2)} :
      ⊢ eq_na_inv N (eq_net_inv ℓl ℓr Rmsg) -∗
        ⟪ τ_hdr -{ θ }-> 𝟙 ⟫ nll nlr -∗
        ⎡Rmsg (key i d t) ml mr⎤ -∗
        EQ cl #()%V ≈ cr #()%V <|eq_thy_cons lls rls (λ _, iThyBot) X|> {{ S }} -∗
        EQ net_handle pl #ℓl nll wl (InjLV (#i, ((#d, #t), ml))) cl
         ≈ net_handle pr #ℓr nlr wr (InjLV (#i, ((#d, #t), mr))) cr
          <|eq_thy_cons lls rls (λ _, iThyBot) X|> {{ S }}.
    Proof.
      iIntros "#Hinv #Hnl #Hm Hc".
      rewrite /net_handle /hkey. eq_pures_l. eq_pures_r.
      iApply (eq_na_open _ _ N); first set_solver. iFrame "Hinv".
      iIntros "[(%vl & %vr & %Ml & %Mr & >Hll & >Hlr & >%Htbl & >%Htbr & >HM) Hclose]".
      eq_load_l. eq_load_r. rewrite -/(key i d t).
      iApply (eq_tbl_lookup_l _ [AppRCtx _; CaseCtx _ _]); first done.
      iApply (eq_tbl_lookup_r _ [AppRCtx _; CaseCtx _ _]); first done.
      iDestruct (big_sepM2_lookup_iff (PROP:=iPropI Σ) with "HM") as %Hdom.
      specialize (Hdom (key i d t)). simpl.
      destruct (Ml !! key i d t) eqn:HMl, (Mr !! key i d t) eqn:HMr;
        [| exfalso; by apply (is_Some_None (A:=val)), Hdom
         | exfalso; by apply (is_Some_None (A:=val)), Hdom |].
      - (* already sent: nothing changes *)
        rewrite /optv. eq_pures_l. eq_pures_r.
        iApply eq_na_close_rule. iFrame "Hclose". iSplitR "Hc"; [iNext; iFrame "∗ %"|].
        done.
      - (* first send: store it and leak the header *)
        rewrite /optv /tbl_add. eq_pures_l. eq_pures_r.
        eq_load_l. eq_load_r. eq_pures_l. eq_pures_r.
        eq_store_l. eq_store_r. eq_pures_l. eq_pures_r.
        iApply eq_na_close_rule. iFrame "Hclose".
        iSplitR "Hc".
        { iNext. iExists _, _, (<[key i d t := ml]> Ml), (<[key i d t := mr]> Mr). iFrame.
          iSplit; [iPureIntro; by apply is_tbl_add|].
          iSplit; [iPureIntro; by apply is_tbl_add|].
          iModIntro. iApply (big_sepM2_insert_2 with "Hm HM"). }
        eq_reshape_l (nll _)%E. eq_reshape_r (nlr _)%E.
        iApply (eq_env_call with "Hnl [] [Hc]"); [set_solver | set_solver | iApply eq_lift_same; iApply hdr_typed |].
        iIntros (ul ur) "Hu". rewrite eq_lift_unit. iDestruct "Hu" as %[-> ->].
        simpl. eq_pures_l. eq_pures_r. done.
    Qed.

    Lemma eq_net_handle_recv N (pl pr : val) (ℓl ℓr : loc) (nll nlr wl wr : val) Rmsg Rdeliv
      lls rls (d s t : Z) (cl cr : val) S
      `{!∀ k m1 m2, Persistent (Rmsg k m1 m2), !∀ k m1 m2, Timeless (Rmsg k m1 m2)} :
      hdr_ok s d t →
      ⊢ eq_na_inv N (eq_net_inv ℓl ℓr Rmsg) -∗
        ⟪ τ_hdr -{ θ }-> 𝟙 ⟫ wl wr -∗
        eq_patch_spec_eq X pl pr Rmsg Rdeliv -∗
        (∀ ul ur, ⎡Rdeliv (key s d t) ul ur⎤ -∗
           EQ cl ul ≈ cr ur <|eq_thy_cons lls rls (λ _, iThyBot) X|> {{ S }}) -∗
        EQ net_handle pl #ℓl nll wl (InjRV (#d, (#s, #t))) cl
         ≈ net_handle pr #ℓr nlr wr (InjRV (#d, (#s, #t))) cr
          <|eq_thy_cons lls rls (λ _, iThyBot) X|> {{ S }}.
    Proof.
      iIntros (Hhdr) "#Hinv #Hw #Hp Hc".
      rewrite /net_handle /hkey. eq_pures_l. eq_pures_r.
      (* one attempt *)
      iLöb as "IH".
      eq_reshape_l (wl _)%E. eq_reshape_r (wr _)%E.
      iApply (eq_env_call with "Hw [] [Hc]"); [set_solver | set_solver | iApply eq_lift_same; iApply hdr_typed |].
      iIntros (u1 u2) "Hu". rewrite eq_lift_unit. iDestruct "Hu" as %[-> ->].
      simpl. eq_pures_l. eq_pures_r.
      iApply (eq_na_open _ _ N); first set_solver. iFrame "Hinv".
      iIntros "[(%vl & %vr & %Ml & %Mr & >Hll & >Hlr & >%Htbl & >%Htbr & >HM) Hclose]".
      eq_load_l. eq_load_r. rewrite -/(key s d t).
      iApply (eq_tbl_lookup_l _ [AppRCtx _; CaseCtx _ _]); first done.
      iApply (eq_tbl_lookup_r _ [AppRCtx _; CaseCtx _ _]); first done.
      iDestruct (big_sepM2_lookup_iff (PROP:=iPropI Σ) with "HM") as %Hdom.
      specialize (Hdom (key s d t)). simpl.
      destruct (Ml !! key s d t) as [ul|] eqn:HMl, (Mr !! key s d t) as [ur|] eqn:HMr;
        [| exfalso; by apply (is_Some_None (A:=val)), Hdom
         | exfalso; by apply (is_Some_None (A:=val)), Hdom |].
      - (* delivered, through the patches *)
        iDestruct (big_sepM2_lookup (PROP:=iPropI Σ) with "HM") as "#Hu"; [done|done|].
        iApply eq_na_close_rule. iFrame "Hclose". iSplitL "Hll Hlr HM"; [iNext; iFrame "∗ %"|].
        rewrite /optv. eq_pures_l. eq_pures_r.
        iApply ("Hp" $! lls rls [AppRCtx _] [AppRCtx _] with "[] Hu"); first done.
        simpl. iApply "Hc".
      - (* not there yet: try again *)
        iApply eq_na_close_rule. iFrame "Hclose". iSplitL "Hll Hlr HM"; [iNext; iFrame "∗ %"|].
        rewrite /optv. eq_pures_lr.
        by iApply "IH".
    Qed.

    (* One session of the network: the client [fl], [fr] is related under the
       network's theory. *)
    Lemma eq_F_NET_sess_spec N (pl pr : val) (ℓl ℓr : loc) (fl fr nll nlr wl wr : val) Rmsg Rdeliv R
      `{!∀ k m1 m2, Persistent (Rmsg k m1 m2), !∀ k m1 m2, Timeless (Rmsg k m1 m2)} :
      ⊢ eq_na_inv N (eq_net_inv ℓl ℓr Rmsg) -∗
        ⟪ τ_hdr -{ θ }-> 𝟙 ⟫ nll nlr -∗ ⟪ τ_hdr -{ θ }-> 𝟙 ⟫ wl wr -∗
        eq_patch_spec_eq X pl pr Rmsg Rdeliv -∗
        (∀ ll lr, EQ App fl (net_eps ll) ≈ App fr (net_eps lr)
                    <|eq_thy_cons [ll] [lr] (net_thy Rmsg Rdeliv ll lr) X|> {{ R }}) -∗
        EQ F_NET_sess pl #ℓl fl (nll, wl)%V ≈ F_NET_sess pr #ℓr fr (nlr, wr)%V <|X|> {{ R }}.
    Proof.
      iIntros "#Hinv #Hnl #Hw #Hp Hf".
      rewrite /F_NET_sess. eq_pures_l. eq_pures_r.
      eq_effect_l nl as "Hnl'". eq_effect_r nr as "Hnr'". eq_pures_l. eq_pures_r.
      iApply eq_new_theory.
      iApply eq_add_label_l. iFrame "Hnl'".
      iApply eq_add_label_r. iFrame "Hnr'".
      eq_reshape_l (fl _). eq_reshape_r (fr _).
      iApply (eq_exhaustion _ _ _ _ (net_thy Rmsg Rdeliv nl nr) with "[Hf]");
        [set_unfold; tauto | set_unfold; tauto | by iApply "Hf" |].
      iLöb as "IH".
      iSplit; [iIntros "!>" (vl vr) "HR"; eq_pures_l; eq_pures_r; iApply eq_value; by iModIntro |].
      iIntros "!>" (kl kr el er Q) "%Hkl %Hkr HT #Hrel".
      iDestruct (eq_thy_app_sym with "HT") as "HT"; first apply net_thy_sym.
      rewrite /net_thy.
      iDestruct "HT" as "[(%i & %d & %t & %ml & %mr & -> & -> & #Hm & HQ)
                         | (%d & %s & %t & -> & -> & %Hhdr & HQ)]".
      - (* send *)
        eq_handle_os ka kb as "Hka" "Hkb". eq_pures_l. eq_pures_r.
        iApply (eq_net_handle_send with "Hinv Hnl Hm").
        eq_cont_l. eq_cont_r.
        eq_exhaustion (fill kl _) (fill kr _) with "[HQ]";
          [set_unfold; tauto | set_unfold; tauto | by iApply "Hrel" | iApply "IH"].
      - (* receive *)
        eq_handle_os ka kb as "Hka" "Hkb". eq_pures_l. eq_pures_r.
        iApply (eq_net_handle_recv with "Hinv Hw Hp"); first done.
        iIntros (ul ur) "Hu".
        eq_cont_l. eq_cont_r.
        iEval (rewrite embed_forall) in "HQ". iSpecialize ("HQ" $! ul).
        iEval (rewrite embed_forall) in "HQ". iSpecialize ("HQ" $! ur).
        iEval (rewrite embed_wand) in "HQ".
        eq_exhaustion (fill kl _) (fill kr _) with "[Hu HQ]";
          [set_unfold; tauto | set_unfold; tauto | iApply "Hrel"; by iApply ("HQ" with "Hu") | iApply "IH"].
    Qed.
  End sess.

  (** The client's side *)
  Lemma eq_sel3_net Kl Kr ll lr (j : Z) E X R :
    (0 ≤ j < 3)%Z →
    EQ fill Kl (net_ep ll j) ≈ fill Kr (net_ep lr j) @ E <|X|> {{ R }} ⊢
    EQ fill Kl (sel3 (net_eps ll) #j) ≈ fill Kr (sel3 (net_eps lr) #j) @ E <|X|> {{ R }}.
  Proof.
    intros Hj. iIntros "H". rewrite /sel3 /net_eps.
    assert (j = 0%Z ∨ j = 1%Z ∨ j = 2%Z)%type as [ -> | [ -> | -> ] ] by lia; eq_pures_l; by eq_pures_r.
  Qed.

  Lemma eq_net_send Rmsg Rdeliv ll lr X Kl Kr (i d t : Z) (ml mr : val) R :
    NeutralEctx [ll] Kl → NeutralEctx [lr] Kr →
    ⊢ ⎡Rmsg (key i d t) ml mr⎤ -∗
      EQ fill Kl #()%V ≈ fill Kr #()%V <|eq_thy_cons [ll] [lr] (net_thy Rmsg Rdeliv ll lr) X|> {{ R }} -∗
      EQ fill Kl (do: ll (InjLV (#i, ((#d, #t), ml)))) ≈ fill Kr (do: lr (InjLV (#i, ((#d, #t), mr))))
        <|eq_thy_cons [ll] [lr] (net_thy Rmsg Rdeliv ll lr) X|> {{ R }}.
  Proof.
    iIntros (HKl HKr) "Hm Hk".
    iApply (eq_introduction_sym [ll] [lr] (net_thy Rmsg Rdeliv ll lr)
              (eq_thy_cons [ll] [lr] (net_thy Rmsg Rdeliv ll lr) X) Kl Kr _ _ R
              (λ sl sr, ⌜sl = #()%V⌝ ∗ ⌜sr = #()%V⌝)%I (net_thy_sym _ _ _ _) (NetThy_mono _ _ _ _)
              (λ dd, list_elem_of_here _ _) HKl HKr with "[Hm] [Hk]").
    - iModIntro. iLeft. iExists i, d, t, ml, mr. by iFrame.
    - by iIntros (sl sr) "[-> ->]".
  Qed.

  Lemma eq_net_recv Rmsg Rdeliv ll lr X Kl Kr (d s t : Z) R :
    NeutralEctx [ll] Kl → NeutralEctx [lr] Kr → hdr_ok s d t →
    ⊢ (∀ ul ur : val, ⎡Rdeliv (key s d t) ul ur⎤ -∗
         EQ fill Kl ul ≈ fill Kr ur <|eq_thy_cons [ll] [lr] (net_thy Rmsg Rdeliv ll lr) X|> {{ R }}) -∗
      EQ fill Kl (do: ll (InjRV (#d, (#s, #t)))) ≈ fill Kr (do: lr (InjRV (#d, (#s, #t))))
        <|eq_thy_cons [ll] [lr] (net_thy Rmsg Rdeliv ll lr) X|> {{ R }}.
  Proof.
    iIntros (HKl HKr Hhdr) "Hk".
    iApply (eq_introduction_sym [ll] [lr] (net_thy Rmsg Rdeliv ll lr)
              (eq_thy_cons [ll] [lr] (net_thy Rmsg Rdeliv ll lr) X) Kl Kr _ _ R
              (λ sl sr, ∃ ul ur : val, ⌜sl = Val ul ∧ sr = Val ur⌝ ∗ Rdeliv (key s d t) ul ur)%I
              (net_thy_sym _ _ _ _) (NetThy_mono _ _ _ _)
              (λ dd, list_elem_of_here _ _) HKl HKr with "[] [Hk]").
    - iModIntro. iRight. iExists d, s, t. do 3 (iSplit; first done).
      iIntros (u1 u2) "Hu". iExists u1, u2. by iFrame.
    - iIntros (sl sr) "(%ul & %ur & [-> ->] & Hu)". by iApply "Hk".
  Qed.

End net_eq.

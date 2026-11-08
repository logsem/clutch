(* The three MAC instances, related.

   [MAC ≈ MAC_pad]: exactly.  The key of [MAC] is sampled at first use; when
   the tag comes first, its exponent [k2] is coupled with the pad exponent
   [r] of [MAC_pad] by the bijection [k2 ↦ k2 + a·k1] (for the tagged
   message [m = g^a]), so that both tags are [m^k1 · g^k2 = g^r], and [k1] is
   presampled on the tape of [MAC_pad] for its later verification.

   [MAC_pad ≈ MAC_ideal]: up to [1/q].  They differ in the verdict on a pair
   that was not tagged: [MAC_pad] accepts it iff a key exponent, read from a
   tape only now, takes one specific value; the error credit excludes that
   value (the group has prime order, so [k ↦ u^k] is injective).

   Both are relations between the factories at the interface type [MACT]. *)

From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_row sem_sig sem_env sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze.uc Require Import uc_systems.
From clutch.prob_eff_lang.probblaze.examples.dhke Require Import dhke_def.
From clutch.prob_eff_lang.probblaze.examples.auth Require Import auth_def auth_typing rand_avoid.
From Stdlib Require Import Lia.

Set Default Proof Using "Type*".

(* ------------------------------------------------------------------ *)
(* Group facts.                                                        *)
(* ------------------------------------------------------------------ *)

Section mac_group.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  Import ssrbool eqtype fintype finset div prime.
  Import fingroup.
  Import fingroup.fingroup.
  Import cyclic.
  Import GroupScope.
  #[local] Notation q := (S (S n'')).

  (* Every element is a power of [g]. *)
  Lemma vg_in_cycle (x : vgG) : is_true (x \in cycle g).
  Proof.
    pose proof g_generator as Hg. unfold generator in Hg.
    assert ([set: vgG] = cycle g)%g as <-. 2: apply in_setT.
    by destruct (@eqtype.eqP _ [set: vgG] (cycle g)).
  Qed.

  (* The group is abelian. *)
  Lemma vg_commute (x y : vgG) : commute x y.
  Proof.
    exact: (centsP (cycle_abelian g) x (vg_in_cycle x) y (vg_in_cycle y)).
  Qed.

  (* [g] has order [q]. *)
  Lemma g_order : #[g] = q.
  Proof. exact: g_nontriv. Qed.

  Lemma g_expg_q : g ^+ q = 1.
  Proof. by rewrite -g_order expg_order. Qed.

  (* Exponents of [g] live modulo [q]. *)
  Lemma g_expg_mul (j : nat) : g ^+ (q * j) = 1.
  Proof.
    induction j as [|j IH]; first by rewrite Nat.mul_0_r expg0.
    by rewrite Nat.mul_succ_r Nat.add_comm ssrnat.plusE expgD g_expg_q IH mul1g.
  Qed.

  Lemma expg_q (k : nat) : g ^+ (k mod q) = g ^+ k.
  Proof.
    rewrite {2}(Nat.div_mod k q); last lia.
    by rewrite ssrnat.plusE expgD g_expg_mul mul1g.
  Qed.

  (* The tag as a power of [g]: [m^k1 * g^k2 = g^(k2 + a*k1)] for [m = g^a]. *)
  Lemma tag_expg (m : vgG) (k1 k2 : nat) :
    m ^+ k1 * g ^+ k2 = g ^+ ((k2 + g_log m * k1) mod q).
  Proof.
    rewrite expg_q - {1}(g_log_id m) -expgM -expgD. f_equal.
    rewrite -(ssrnat.plusE). rewrite -(ssrnat.multE). lia.
  Qed.

  (* The pad reparametrisation: [t * (m' * m^-1)^k1 = m'^k1 * g^k2] for
     [t = m^k1 * g^k2]. *)
  Lemma tag_shift (m m' : vgG) (k1 k2 : nat) :
    (m ^+ k1 * g ^+ k2) * (m' * m^-1) ^+ k1 = m' ^+ k1 * g ^+ k2.
  Proof.
    rewrite expgMn; last exact: vg_commute.
    rewrite expgVn.
    rewrite (vg_commute (m' ^+ k1) ((m ^+ k1)^-1)) -mulgA.
    rewrite (mulgA (g ^+ k2)) (vg_commute (g ^+ k2) ((m ^+ k1)^-1)) -mulgA.
    rewrite mulKVg. exact: vg_commute.
  Qed.

  (* In a group of prime order, the map [k ↦ u^k] is injective on [0, q)
     for [u ≠ 1]. *)
  Lemma expg_inj_prime (Hq : is_true (prime q)) (u : vgG) (i j : nat) :
    u ≠ 1 → is_true (ssrnat.leq (S i) q) → is_true (ssrnat.leq (S j) q) → u ^+ i = u ^+ j → i = j.
  Proof.
    move=> Hu Hi Hj Hij.
    have Hord : #[u] = q.
    { have Huq : u ^+ q = 1.
      { rewrite -(g_log_id u) -expgM ssrnat.mulnC expgM g_expg_q. exact: expg1n. }
      have Hdvd : is_true (#[u] %| q) by rewrite order_dvdn Huq eqxx.
      have [_ Hd] := elimT primeP Hq.
      move: (elimT orP (Hd _ Hdvd)) => [H1|H2].
      - exfalso. apply Hu. apply (elimT eqP). by rewrite -order_eq1.
      - exact: (elimT eqP H2). }
    have Hij' := introT eqP Hij.
    rewrite eq_expg_mod_order Hord (modn_small Hi) (modn_small Hj) in Hij'.
    exact: (elimT eqP Hij').
  Qed.

  (* The bad exponents for [u^k = w]: at most one when [u ≠ 1]. *)
  Definition bad (u w : vgG) : list (fin q) :=
    filter (λ k : fin q, u ^+ (fin_to_nat k) = w) (finite.enum (fin q)).

  Lemma bad_NoDup u w : NoDup (bad u w).
  Proof. apply NoDup_filter, finite.NoDup_enum. Qed.

  Lemma bad_spec u w (k : fin q) : u ^+ (fin_to_nat k) = w → k ∈ bad u w.
  Proof.
    intros Hk. apply list_elem_of_filter. split; [done|apply finite.elem_of_enum].
  Qed.

  Lemma bad_length (Hq : is_true (prime q)) u w : u ≠ 1 → length (bad u w) ≤ 1.
  Proof.
    intros Hu.
    destruct (bad u w) as [|k1 [|k2 l]] eqn:Hb; [simpl; lia|simpl; lia|exfalso].
    pose proof (bad_NoDup u w) as Hnd. rewrite Hb in Hnd.
    apply NoDup_cons in Hnd as [Hk1 _].
    assert (k1 ∈ bad u w) as Hin1 by (rewrite Hb; apply elem_of_cons; by left).
    assert (k2 ∈ bad u w) as Hin2 by (rewrite Hb; apply elem_of_cons; right; apply elem_of_cons; by left).
    apply list_elem_of_filter in Hin1 as [Hin1 _]. apply list_elem_of_filter in Hin2 as [Hin2 _].
    assert (fin_to_nat k1 = fin_to_nat k2) as Heq.
    { apply (expg_inj_prime Hq u); [done| | |by rewrite Hin1 Hin2].
      - apply (introT ssrnat.ltP), fin_to_nat_lt.
      - apply (introT ssrnat.ltP), fin_to_nat_lt. }
    apply fin_to_nat_inj in Heq. subst. apply Hk1, elem_of_cons. by left.
  Qed.

End mac_group.

(* ------------------------------------------------------------------ *)
(* The shift bijection on exponents.                                   *)
(* ------------------------------------------------------------------ *)

Section shift.
  Context (q : nat) (Hq : (0 < q)%nat).
  #[local] Open Scope nat_scope.

  (* [x ↦ x + c] modulo [q] on [0, q), the identity elsewhere. *)
  Definition shift (c x : nat) : nat := if bool_decide (x < q) then (x + c) mod q else x.

  Lemma shift_lt c x : x < q → shift c x < q.
  Proof using Hq. intros Hx. rewrite /shift bool_decide_eq_true_2 //. by apply Nat.mod_upper_bound; lia. Qed.

  Lemma shift_dom c (N : nat) : S N = q → ∀ x, x < S N → shift c x < S N.
  Proof using Hq. intros HN x Hx. rewrite HN. rewrite HN in Hx. by apply shift_lt. Qed.

  Lemma shift_small c x : x < q → shift c x = (x + c) mod q.
  Proof using Hq. intros Hx. rewrite /shift bool_decide_eq_true_2 //. Qed.

  Lemma shift_cancel c x : shift (q - c mod q) (shift c x) = x.
  Proof using Hq.
    destruct (decide (x < q)) as [Hx|Hx].
    - rewrite (shift_small c x) //.
      rewrite shift_small; last by apply Nat.mod_upper_bound; lia.
      rewrite Nat.Div0.add_mod_idemp_l.
      pose proof (Nat.mod_upper_bound c q ltac:(lia)).
      pose proof (Nat.div_mod c q ltac:(lia)).
      replace (x + c + (q - c mod q)) with (x + (1 + c / q) * q) by lia.
      rewrite Nat.Div0.mod_add. by apply Nat.mod_small.
    - rewrite /shift (bool_decide_eq_false_2 (x < q)) //=.
      by rewrite (bool_decide_eq_false_2 (x < q)).
  Qed.

  Lemma shift_cancel' c x : shift c (shift (q - c mod q) x) = x.
  Proof using Hq.
    destruct (decide (x < q)) as [Hx|Hx].
    - rewrite (shift_small (q - c mod q) x) //.
      rewrite shift_small; last by apply Nat.mod_upper_bound; lia.
      rewrite Nat.Div0.add_mod_idemp_l.
      pose proof (Nat.mod_upper_bound c q ltac:(lia)).
      pose proof (Nat.div_mod c q ltac:(lia)).
      replace (x + (q - c mod q) + c) with (x + (1 + c / q) * q) by lia.
      rewrite Nat.Div0.mod_add. by apply Nat.mod_small.
    - rewrite /shift (bool_decide_eq_false_2 (x < q)) //=.
      by rewrite (bool_decide_eq_false_2 (x < q)).
  Qed.

  Global Instance shift_inj c : Inj (=) (=) (shift c).
  Proof using Hq. intros x y Hxy. by rewrite -(shift_cancel c x) Hxy shift_cancel. Qed.

  Global Instance shift_surj c : Surj (=) (shift c).
  Proof using Hq. intros y. exists (shift (q - c mod q) y). apply shift_cancel'. Qed.

  Global Instance shift_bij c : Bij (shift c) := {}.

End shift.

(* ------------------------------------------------------------------ *)
(* [MAC] and [MAC_pad].                                                 *)
(* ------------------------------------------------------------------ *)

Section mac_pad.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  Import valgroup_notation.
  Import valgroup_tactics.
  Import fingroup.
  Import fingroup.fingroup.
  #[local] Notation n := (S n'').
  #[local] Notation q := (S (S n'')).

  Definition macN : namespace := nroot .@ "mac".
  Definition optv (v : option val) : val := match v with None => NONEV | Some w => SOMEV w end.
  Definition optb (v : option bool) : val := match v with None => NONEV | Some b => SOMEV #b end.

  (* The joint state of [MAC] (left) and [MAC_pad] (right). *)
  Definition mac_pad_inv (α1 β1 : loc) (key1 tagged1 verdict1 : loc)
                         (α2 β2 : loc) (key2 tg2 verdict2 : loc) : iProp Σ :=
    (* nothing happened *)
    (α1 ↪N (n; []) ∗ β1 ↪N (n; []) ∗ key1 ↦ NONEV ∗ tagged1 ↦ #false ∗ verdict1 ↦ NONEV ∗
     α2 ↪ₛN (n; []) ∗ β2 ↪ₛN (n; []) ∗ key2 ↦ₛ NONEV ∗ tg2 ↦ₛ NONEV ∗ verdict2 ↦ₛ NONEV)
    ∨
    (* tag first: [MAC_pad] keeps [k1] on its tape until a different message is verified *)
    (∃ (k1 k2 : nat) (m0 : vgG) (v : option bool) (ns : list nat),
       ⌜k1 ≤ n ∧ k2 ≤ n⌝ ∗ ⌜ns = [k1] ∨ (ns = [] ∧ is_Some v)⌝ ∗
       α1 ↪N (n; []) ∗ β1 ↪N (n; []) ∗ key1 ↦ SOMEV (#k1, #k2) ∗ tagged1 ↦ #true ∗ verdict1 ↦ optb v ∗
       α2 ↪ₛN (n; ns) ∗ β2 ↪ₛN (n; []) ∗ key2 ↦ₛ NONEV ∗
       tg2 ↦ₛ SOMEV (vgval m0, vgval (m0 ^+ k1 * g ^+ k2)%g) ∗ verdict2 ↦ₛ optb v)
    ∨
    (* verify first: both hold the same key *)
    (∃ (k1 k2 : nat) (b : bool) (tg : option vgG),
       ⌜k1 ≤ n ∧ k2 ≤ n⌝ ∗
       α1 ↪N (n; []) ∗ β1 ↪N (n; []) ∗ key1 ↦ SOMEV (#k1, #k2) ∗ tagged1 ↦ #(bool_decide (is_Some tg)) ∗
       verdict1 ↦ SOMEV #b ∗
       α2 ↪ₛN (n; []) ∗ β2 ↪ₛN (n; []) ∗ key2 ↦ₛ SOMEV (#k1, #k2) ∗
       tg2 ↦ₛ optv ((λ m0, (vgval m0, vgval (m0 ^+ k1 * g ^+ k2)%g)%V) <$> tg) ∗ verdict2 ↦ₛ SOMEV #b).

  Lemma MAC_MAC_pad_body : ⊢ BREL (MAC #()%V) ≤ (MAC_pad #()%V) <|⊥|> {{ MACT }}.
  Proof.
    rewrite /MAC /MAC_pad. brel_pures_l. brel_pures_r.
    brel_alloctape_l α1 as "Hα1". brel_pures_l.
    brel_alloctape_l β1 as "Hβ1". brel_pures_l.
    brel_alloc_l key1 as "Hkey1". brel_pures_l.
    brel_alloc_l tagged1 as "Htagged1". brel_pures_l.
    brel_alloc_l verdict1 as "Hverdict1". brel_pures_l.
    brel_alloctape_r α2 as "Hα2". brel_pures_r.
    brel_alloctape_r β2 as "Hβ2". brel_pures_r.
    brel_alloc_r key2 as "Hkey2". brel_pures_r.
    brel_alloc_r tg2 as "Htg2". brel_pures_r.
    brel_alloc_r verdict2 as "Hverdict2".
    rewrite !Nat2Z.id.
    iAssert (α2 ↪ₛN (n; []))%I with "[Hα2]" as "Hα2"; first (iExists []; by iFrame).
    iAssert (β2 ↪ₛN (n; []))%I with "[Hβ2]" as "Hβ2"; first (iExists []; by iFrame).
    iApply (brel_na_alloc (mac_pad_inv α1 β1 key1 tagged1 verdict1 α2 β2 key2 tg2 verdict2) macN).
    iSplitL; [iNext; iLeft; iFrame|].
    iIntros "#Hinv". brel_pures_r.
    iModIntro. rewrite /MACT /sem_ty_prod /tagT /verifyT.
    iExists _, _, _, _. do 2 (iSplit; first done). iSplit.
    - (* tag *)
      rewrite /sem_ty_mbang /sem_ty_arr /=. iIntros "!>" (m1 m2) "(%m & -> & ->)".
      brel_pures_l. brel_pures_r.
      iApply (brel_na_inv _ _ macN); [set_solver|]. iFrame "Hinv".
      iIntros "(>HI & Hclose)". rewrite /mac_pad_inv.
      iDestruct "HI" as "[(Hα1 & Hβ1 & Hkey1 & Htagged1 & Hverdict1 & Hα2 & Hβ2 & Hkey2 & Htg2 & Hverdict2) | [HI | HI]]".
      + brel_load_l. brel_pures_l. brel_store_l. brel_pures_l.
        brel_load_r. brel_pures_r.
        brel_load_l. brel_pures_l.
        brel_load_r. brel_pures_r.
        iApply (brel_couple_TT _ _ (λ x, x) _ _ _ _ α1 α2 [] []); first done.
        iFrame "Hα1 Hα2". iIntros (k1) "[Hα1 Hα2]".
        brel_rand_l as "%Hk1". brel_pures_l.
        iApply (brel_couple_TT _ _ (shift q (g_log m * k1)) (H := shift_bij q (Nat.lt_0_succ _) _) _ _ _ _ β1 β2 [] []);
          first (apply (shift_dom q (Nat.lt_0_succ _) _ n eq_refl)).
        iFrame "Hβ1 Hβ2". iIntros (k2) "[Hβ1 Hβ2]".
        brel_rand_l as "%Hk2". brel_pures_l. brel_store_l. brel_pures_l.
        brel_rand_r as "%Hfk2".
        iApply (brel_exp_r [AppRCtx _]). brel_pures_r. brel_store_r. brel_pures_r.
        rewrite /tag. brel_pures_l.
        brel_exp_l. brel_exp_l. brel_mult_l.
        rewrite (shift_small q (Nat.lt_0_succ _) _ k2); last lia. rewrite -tag_expg.
        iApply brel_na_close. iFrame "Hclose".
        iSplitL "Hα1 Hβ1 Hkey1 Htagged1 Hverdict1 Hα2 Hβ2 Hkey2 Htg2 Hverdict2".
        { iNext. iRight. iLeft. iExists k1, k2, m, None, [k1]. iFrame. iPureIntro. split; [lia|by left]. }
        brel_pures_l. iModIntro. iExists _, _. iRight. iSplit; [done|]. iSplit; [done|]. by iExists _.
      + iDestruct "HI" as (k1 k2 m0 v ns) "(%Hk & %Hns & Hα1 & Hβ1 & Hkey1 & Htagged1 & Hverdict1 & Hα2 & Hβ2 & Hkey2 & Htg2 & Hverdict2)".
        brel_load_l. brel_pures_l. brel_load_r.
        iApply brel_na_close. iFrame "Hclose".
        iSplitL "Hα1 Hβ1 Hkey1 Htagged1 Hverdict1 Hα2 Hβ2 Hkey2 Htg2 Hverdict2".
        { iNext. iRight. iLeft. iExists k1, k2, m0, v, ns. by iFrame. }
        brel_pures_r. iModIntro. iExists _, _. iLeft. by (iSplit; [|iSplit]).
      + iDestruct "HI" as (k1 k2 b tg) "(%Hk & Hα1 & Hβ1 & Hkey1 & Htagged1 & Hverdict1 & Hα2 & Hβ2 & Hkey2 & Htg2 & Hverdict2)".
        destruct tg as [m0|]; simpl.
        * brel_load_l. brel_pures_l. brel_load_r.
          iApply brel_na_close. iFrame "Hclose".
          iSplitL "Hα1 Hβ1 Hkey1 Htagged1 Hverdict1 Hα2 Hβ2 Hkey2 Htg2 Hverdict2".
          { iNext. iRight. iRight. iExists k1, k2, b, (Some m0). by iFrame. }
          brel_pures_r. iModIntro. iExists _, _. iLeft. by (iSplit; [|iSplit]).
        * brel_load_l. brel_pures_l. brel_store_l. brel_pures_l.
          brel_load_l. brel_pures_l.
          brel_load_r. brel_pures_r. brel_load_r. brel_pures_r.
          rewrite /tag. brel_pures_l. brel_exp_l. brel_exp_l. brel_mult_l.
          brel_pures_r. brel_exp_r. brel_exp_r. brel_mult_r. brel_pures_r. brel_store_r.
          iApply brel_na_close. iFrame "Hclose".
          iSplitL "Hα1 Hβ1 Hkey1 Htagged1 Hverdict1 Hα2 Hβ2 Hkey2 Htg2 Hverdict2".
          { iNext. iRight. iRight. iExists k1, k2, b, (Some m). simpl. by iFrame. }
          brel_pures_r. brel_pures_l. iModIntro. iExists _, _. iRight. iSplit; [done|]. iSplit; [done|]. by iExists _.
    - (* verify *)
      rewrite /sem_ty_mbang /sem_ty_arr /=.
      iIntros "!>" (p1 p2) "(%w1 & %w1' & %w2 & %w2' & -> & -> & (%m' & -> & ->) & (%t' & -> & ->))".
      brel_pures_l. brel_pures_r.
      iApply (brel_na_inv _ _ macN); [set_solver|]. iFrame "Hinv".
      iIntros "(>HI & Hclose)". rewrite /mac_pad_inv.
      iDestruct "HI" as "[(Hα1 & Hβ1 & Hkey1 & Htagged1 & Hverdict1 & Hα2 & Hβ2 & Hkey2 & Htg2 & Hverdict2) | [HI | HI]]".
      + (* verify first *)
        brel_load_l. brel_pures_l. brel_load_l. brel_pures_l.
        brel_load_r. brel_pures_r. brel_load_r. brel_pures_r.
        iApply (brel_couple_TT _ _ (λ x, x) _ _ _ _ α1 α2 [] []); first done.
        iFrame "Hα1 Hα2". iIntros (k1) "[Hα1 Hα2]".
        brel_rand_l as "%Hk1". brel_pures_l. brel_rand_r as "%Hk1'". brel_pures_r.
        iApply (brel_couple_TT _ _ (λ x, x) _ _ _ _ β1 β2 [] []); first done.
        iFrame "Hβ1 Hβ2". iIntros (k2) "[Hβ1 Hβ2]".
        brel_rand_l as "%Hk2". brel_pures_l. brel_rand_r as "%Hk2'". brel_pures_r.
        brel_store_l. brel_pures_l. brel_store_r. brel_pures_r.
        rewrite /tag. brel_pures_l. brel_exp_l. brel_exp_l. brel_mult_l. brel_eq_l. brel_pures_l.
        brel_pures_r. brel_exp_r. brel_exp_r. brel_mult_r. brel_eq_r. brel_pures_r.
        brel_store_l. brel_pures_l. brel_store_r.
        iApply brel_na_close. iFrame "Hclose".
        iSplitL "Hα1 Hβ1 Hkey1 Htagged1 Hverdict1 Hα2 Hβ2 Hkey2 Htg2 Hverdict2".
        { iNext. iRight. iRight. iExists k1, k2, _, None. simpl. iFrame. iPureIntro. lia. }
        brel_pures_r. iModIntro. by iExists _.
      + (* tag first *)
        iDestruct "HI" as (k1 k2 m0 v ns) "(%Hk & %Hns & Hα1 & Hβ1 & Hkey1 & Htagged1 & Hverdict1 & Hα2 & Hβ2 & Hkey2 & Htg2 & Hverdict2)".
        destruct v as [b|]; simpl.
        * (* decided *)
          brel_load_l. brel_pures_l. brel_load_r.
          iApply brel_na_close. iFrame "Hclose".
          iSplitL "Hα1 Hβ1 Hkey1 Htagged1 Hverdict1 Hα2 Hβ2 Hkey2 Htg2 Hverdict2".
          { iNext. iRight. iLeft. iExists k1, k2, m0, (Some b), ns. by iFrame. }
          brel_pures_r. iModIntro. by iExists _.
        * destruct Hns as [-> | [_ [? ?]]]; last done.
          brel_load_l. brel_pures_l. brel_load_l. brel_pures_l.
          rewrite /tag. brel_pures_l. brel_exp_l. brel_exp_l. brel_mult_l. brel_eq_l. brel_pures_l.
          brel_load_r. brel_pures_r. brel_load_r. brel_pures_r. brel_eq_r.
          destruct (decide (m' = m0)) as [->|Hne].
          -- rewrite (bool_decide_eq_true_2 _ eq_refl); try apply _. brel_pures_r. brel_eq_r. brel_pures_r.
             brel_store_l. brel_pures_l. brel_store_r.
             iApply brel_na_close. iFrame "Hclose".
             iSplitL "Hα1 Hβ1 Hkey1 Htagged1 Hverdict1 Hα2 Hβ2 Hkey2 Htg2 Hverdict2".
             { iNext. iRight. iLeft. iExists k1, k2, m0, (Some _), [k1]. iFrame. iPureIntro. split; [done|by left]. }
             brel_pures_r. iModIntro. by iExists _.
          -- rewrite (bool_decide_eq_false_2 _ Hne); try apply _. brel_pures_r.
             brel_rand_r as "%Hk1'". brel_pures_r.
             brel_inv_r. brel_mult_r. brel_exp_r. brel_mult_r. brel_eq_r. brel_pures_r.
             rewrite tag_shift.
             brel_store_l. brel_pures_l. brel_store_r.
             iApply brel_na_close. iFrame "Hclose".
             iSplitL "Hα1 Hβ1 Hkey1 Htagged1 Hverdict1 Hα2 Hβ2 Hkey2 Htg2 Hverdict2".
             { iNext. iRight. iLeft. iExists k1, k2, m0, (Some _), []. iFrame. iPureIntro. split; [done|right; split; [done|by eexists]]. }
             brel_pures_r. iModIntro. by iExists _.
      + (* verify first, decided *)
        iDestruct "HI" as (k1 k2 b tg) "(%Hk & Hα1 & Hβ1 & Hkey1 & Htagged1 & Hverdict1 & Hα2 & Hβ2 & Hkey2 & Htg2 & Hverdict2)".
        brel_load_l. brel_pures_l. brel_load_r.
        iApply brel_na_close. iFrame "Hclose".
        iSplitL "Hα1 Hβ1 Hkey1 Htagged1 Hverdict1 Hα2 Hβ2 Hkey2 Htg2 Hverdict2".
        { iNext. iRight. iRight. iExists k1, k2, b, tg. by iFrame. }
        brel_pures_r. iModIntro. by iExists _.
  Qed.



  (* The joint state of [MAC_pad] (left) and [MAC] (right). *)
  Definition pad_mac_inv (α1 β1 : loc) (key1 tg1 verdict1 : loc)
                         (α2 β2 : loc) (key2 tagged2 verdict2 : loc) : iProp Σ :=
    (α1 ↪N (n; []) ∗ β1 ↪N (n; []) ∗ key1 ↦ NONEV ∗ tg1 ↦ NONEV ∗ verdict1 ↦ NONEV ∗
     α2 ↪ₛN (n; []) ∗ β2 ↪ₛN (n; []) ∗ key2 ↦ₛ NONEV ∗ tagged2 ↦ₛ #false ∗ verdict2 ↦ₛ NONEV)
    ∨
    (∃ (k1 k2 : nat) (m0 t0 : vgG) (v : option bool) (ns : list nat),
       ⌜k1 ≤ n ∧ k2 ≤ n⌝ ∗ ⌜t0 = (m0 ^+ k1 * g ^+ k2)%g⌝ ∗ ⌜ns = [k1] ∨ (ns = [] ∧ is_Some v)⌝ ∗
       α1 ↪N (n; ns) ∗ β1 ↪N (n; []) ∗ key1 ↦ NONEV ∗ tg1 ↦ SOMEV (vgval m0, vgval t0) ∗ verdict1 ↦ optb v ∗
       α2 ↪ₛN (n; []) ∗ β2 ↪ₛN (n; []) ∗ key2 ↦ₛ SOMEV (#k1, #k2) ∗ tagged2 ↦ₛ #true ∗ verdict2 ↦ₛ optb v)
    ∨
    (∃ (k1 k2 : nat) (b : bool) (tg : option vgG),
       ⌜k1 ≤ n ∧ k2 ≤ n⌝ ∗
       α1 ↪N (n; []) ∗ β1 ↪N (n; []) ∗ key1 ↦ SOMEV (#k1, #k2) ∗
       tg1 ↦ optv ((λ m0, (vgval m0, vgval (m0 ^+ k1 * g ^+ k2)%g)%V) <$> tg) ∗ verdict1 ↦ SOMEV #b ∗
       α2 ↪ₛN (n; []) ∗ β2 ↪ₛN (n; []) ∗ key2 ↦ₛ SOMEV (#k1, #k2) ∗
       tagged2 ↦ₛ #(bool_decide (is_Some tg)) ∗ verdict2 ↦ₛ SOMEV #b).

  Lemma MAC_pad_MAC_body : ⊢ BREL (MAC_pad #()%V) ≤ (MAC #()%V) <|⊥|> {{ MACT }}.
  Proof.
    rewrite /MAC /MAC_pad. brel_pures_l. brel_pures_r.
    brel_alloctape_l α1 as "Hα1". brel_pures_l.
    brel_alloctape_l β1 as "Hβ1". brel_pures_l.
    brel_alloc_l key1 as "Hkey1". brel_pures_l.
    brel_alloc_l tg1 as "Htg1". brel_pures_l.
    brel_alloc_l verdict1 as "Hverdict1". brel_pures_l.
    brel_alloctape_r α2 as "Hα2". brel_pures_r.
    brel_alloctape_r β2 as "Hβ2". brel_pures_r.
    brel_alloc_r key2 as "Hkey2". brel_pures_r.
    brel_alloc_r tagged2 as "Htagged2". brel_pures_r.
    brel_alloc_r verdict2 as "Hverdict2".
    rewrite !Nat2Z.id.
    iAssert (α2 ↪ₛN (n; []))%I with "[Hα2]" as "Hα2"; first (iExists []; by iFrame).
    iAssert (β2 ↪ₛN (n; []))%I with "[Hβ2]" as "Hβ2"; first (iExists []; by iFrame).
    iApply (brel_na_alloc (pad_mac_inv α1 β1 key1 tg1 verdict1 α2 β2 key2 tagged2 verdict2) macN).
    iSplitL; [iNext; iLeft; iFrame|].
    iIntros "#Hinv". brel_pures_r.
    iModIntro. rewrite /MACT /sem_ty_prod /tagT /verifyT.
    iExists _, _, _, _. do 2 (iSplit; first done). iSplit.
    - (* tag *)
      rewrite /sem_ty_mbang /sem_ty_arr /=. iIntros "!>" (m1 m2) "(%m & -> & ->)".
      brel_pures_l. brel_pures_r.
      iApply (brel_na_inv _ _ macN); [set_solver|]. iFrame "Hinv".
      iIntros "(>HI & Hclose)". rewrite /pad_mac_inv.
      iDestruct "HI" as "[(Hα1 & Hβ1 & Hkey1 & Htg1 & Hverdict1 & Hα2 & Hβ2 & Hkey2 & Htagged2 & Hverdict2) | [HI | HI]]".
      + brel_load_l. brel_pures_l. brel_load_l. brel_pures_l.
        brel_load_r. brel_pures_r. brel_store_r. brel_pures_r. brel_load_r. brel_pures_r.
        iApply (brel_couple_TT _ _ (λ x, x) _ _ _ _ α1 α2 [] []); first done.
        iFrame "Hα1 Hα2". iIntros (k1) "[Hα1 Hα2]".
        brel_rand_r as "%Hk1". brel_pures_r.
        set (c := (fin_to_nat (g_log m) * k1)%nat).
        iApply (brel_couple_TT _ _ (shift q (q - c mod q)) (H := shift_bij q (Nat.lt_0_succ _) _) _ _ _ _ β1 β2 [] []);
          first (apply (shift_dom q (Nat.lt_0_succ _) _ n eq_refl)).
        iFrame "Hβ1 Hβ2". iIntros (r) "[Hβ1 Hβ2]".
        brel_rand_l as "%Hr".
        iApply (brel_exp_l [AppRCtx _]). brel_pures_l. brel_store_l. brel_pures_l.
        brel_rand_r as "%Hk2". brel_pures_r. brel_store_r. brel_pures_r.
        rewrite /tag. brel_pures_r. brel_exp_r. brel_exp_r. brel_mult_r.
        assert (g ^+ r = m ^+ k1 * g ^+ shift q (q - c mod q) r)%g as Heq.
        { rewrite tag_expg.
          rewrite -(shift_small q (Nat.lt_0_succ _) c (shift q (q - c mod q) r)).
          2: { apply (shift_lt q (Nat.lt_0_succ _)). lia. }
          by rewrite (shift_cancel' q (Nat.lt_0_succ _)). }
        iApply brel_na_close. iFrame "Hclose".
        iSplitL "Hα1 Hβ1 Hkey1 Htg1 Hverdict1 Hα2 Hβ2 Hkey2 Htagged2 Hverdict2".
        { iNext. iRight. iLeft. iExists k1, (shift q (q - c mod q) r), m, _, None, [k1]. iFrame.
          iPureIntro. split; [split; [lia|exact Hk2]|]. split; [exact Heq|by left]. }
        rewrite Heq.
        brel_pures_r. iModIntro. iExists _, _. iRight. iSplit; [done|]. iSplit; [done|]. by iExists _.
      + iDestruct "HI" as (k1 k2 m0 t0 v ns) "(%Hk & %Ht0 & %Hns & Hα1 & Hβ1 & Hkey1 & Htg1 & Hverdict1 & Hα2 & Hβ2 & Hkey2 & Htagged2 & Hverdict2)".
        brel_load_l. brel_pures_l. brel_load_r.
        iApply brel_na_close. iFrame "Hclose".
        iSplitL "Hα1 Hβ1 Hkey1 Htg1 Hverdict1 Hα2 Hβ2 Hkey2 Htagged2 Hverdict2".
        { iNext. iRight. iLeft. iExists k1, k2, m0, t0, v, ns. by iFrame. }
        brel_pures_r. iModIntro. iExists _, _. iLeft. by (iSplit; [|iSplit]).
      + iDestruct "HI" as (k1 k2 b tg) "(%Hk & Hα1 & Hβ1 & Hkey1 & Htg1 & Hverdict1 & Hα2 & Hβ2 & Hkey2 & Htagged2 & Hverdict2)".
        destruct tg as [m0|]; simpl.
        * brel_load_l. brel_pures_l. brel_load_r.
          iApply brel_na_close. iFrame "Hclose".
          iSplitL "Hα1 Hβ1 Hkey1 Htg1 Hverdict1 Hα2 Hβ2 Hkey2 Htagged2 Hverdict2".
          { iNext. iRight. iRight. iExists k1, k2, b, (Some m0). by iFrame. }
          brel_pures_r. iModIntro. iExists _, _. iLeft. by (iSplit; [|iSplit]).
        * brel_load_l. brel_pures_l. brel_load_l. brel_pures_l.
          brel_load_r. brel_pures_r. brel_store_r. brel_pures_r. brel_load_r. brel_pures_r.
          rewrite /tag. brel_pures_l. brel_exp_l. brel_exp_l. brel_mult_l. brel_pures_l. brel_store_l.
          brel_pures_r. brel_exp_r. brel_exp_r. brel_mult_r.
          iApply brel_na_close. iFrame "Hclose".
          iSplitL "Hα1 Hβ1 Hkey1 Htg1 Hverdict1 Hα2 Hβ2 Hkey2 Htagged2 Hverdict2".
          { iNext. iRight. iRight. iExists k1, k2, b, (Some m). simpl. by iFrame. }
          brel_pures_l. brel_pures_r. iModIntro. iExists _, _. iRight. iSplit; [done|]. iSplit; [done|]. by iExists _.
    - (* verify *)
      rewrite /sem_ty_mbang /sem_ty_arr /=.
      iIntros "!>" (p1 p2) "(%w1 & %w1' & %w2 & %w2' & -> & -> & (%m' & -> & ->) & (%t' & -> & ->))".
      brel_pures_l. brel_pures_r.
      iApply (brel_na_inv _ _ macN); [set_solver|]. iFrame "Hinv".
      iIntros "(>HI & Hclose)". rewrite /pad_mac_inv.
      iDestruct "HI" as "[(Hα1 & Hβ1 & Hkey1 & Htg1 & Hverdict1 & Hα2 & Hβ2 & Hkey2 & Htagged2 & Hverdict2) | [HI | HI]]".
      + (* verify first *)
        brel_load_l. brel_pures_l. brel_load_l. brel_pures_l.
        brel_load_r. brel_pures_r. brel_load_r. brel_pures_r.
        iApply (brel_couple_TT _ _ (λ x, x) _ _ _ _ α1 α2 [] []); first done.
        iFrame "Hα1 Hα2". iIntros (k1) "[Hα1 Hα2]".
        brel_rand_l as "%Hk1". brel_pures_l. brel_rand_r as "%Hk1'". brel_pures_r.
        iApply (brel_couple_TT _ _ (λ x, x) _ _ _ _ β1 β2 [] []); first done.
        iFrame "Hβ1 Hβ2". iIntros (k2) "[Hβ1 Hβ2]".
        brel_rand_l as "%Hk2". brel_pures_l. brel_rand_r as "%Hk2'". brel_pures_r.
        brel_store_l. brel_pures_l. brel_store_r. brel_pures_r.
        rewrite /tag. brel_pures_l. brel_exp_l. brel_exp_l. brel_mult_l. brel_eq_l. brel_pures_l.
        brel_pures_r. brel_exp_r. brel_exp_r. brel_mult_r. brel_eq_r. brel_pures_r.
        brel_store_l. brel_pures_l. brel_store_r.
        iApply brel_na_close. iFrame "Hclose".
        iSplitL "Hα1 Hβ1 Hkey1 Htg1 Hverdict1 Hα2 Hβ2 Hkey2 Htagged2 Hverdict2".
        { iNext. iRight. iRight. iExists k1, k2, _, None. simpl. iFrame. iPureIntro. lia. }
        brel_pures_r. iModIntro. by iExists _.
      + (* tag first *)
        iDestruct "HI" as (k1 k2 m0 t0 v ns) "(%Hk & %Ht0 & %Hns & Hα1 & Hβ1 & Hkey1 & Htg1 & Hverdict1 & Hα2 & Hβ2 & Hkey2 & Htagged2 & Hverdict2)".
        destruct v as [b|]; simpl.
        * brel_load_l. brel_pures_l. brel_load_r.
          iApply brel_na_close. iFrame "Hclose".
          iSplitL "Hα1 Hβ1 Hkey1 Htg1 Hverdict1 Hα2 Hβ2 Hkey2 Htagged2 Hverdict2".
          { iNext. iRight. iLeft. iExists k1, k2, m0, t0, (Some b), ns. by iFrame. }
          brel_pures_r. iModIntro. by iExists _.
        * destruct Hns as [-> | [_ [? ?]]]; last done. subst t0.
          brel_load_r. brel_pures_r. brel_load_r. brel_pures_r.
          rewrite /tag. brel_pures_r. brel_exp_r. brel_exp_r. brel_mult_r. brel_eq_r. brel_pures_r.
          brel_load_l. brel_pures_l. brel_load_l. brel_pures_l. brel_eq_l.
          destruct (decide (m' = m0)) as [->|Hne].
          -- rewrite (bool_decide_eq_true_2 _ eq_refl); try apply _. brel_pures_l. brel_eq_l. brel_pures_l.
             brel_store_l. brel_pures_l. brel_store_r.
             iApply brel_na_close. iFrame "Hclose".
             iSplitL "Hα1 Hβ1 Hkey1 Htg1 Hverdict1 Hα2 Hβ2 Hkey2 Htagged2 Hverdict2".
             { iNext. iRight. iLeft. iExists k1, k2, m0, _, (Some _), [k1]. iFrame. iPureIntro. split; [done|]. split; [done|by left]. }
             brel_pures_r. iModIntro. by iExists _.
          -- rewrite (bool_decide_eq_false_2 _ Hne); try apply _. brel_pures_l.
             brel_rand_l as "%Hk1'". brel_pures_l.
             brel_inv_l. brel_mult_l. brel_exp_l. brel_mult_l. brel_eq_l. brel_pures_l.
             rewrite tag_shift.
             brel_store_l. brel_pures_l. brel_store_r.
             iApply brel_na_close. iFrame "Hclose".
             iSplitL "Hα1 Hβ1 Hkey1 Htg1 Hverdict1 Hα2 Hβ2 Hkey2 Htagged2 Hverdict2".
             { iNext. iRight. iLeft. iExists k1, k2, m0, _, (Some _), []. iFrame. iPureIntro. split; [done|]. split; [done|right; split; [done|by eexists]]. }
             brel_pures_r. iModIntro. by iExists _.
      + iDestruct "HI" as (k1 k2 b tg) "(%Hk & Hα1 & Hβ1 & Hkey1 & Htg1 & Hverdict1 & Hα2 & Hβ2 & Hkey2 & Htagged2 & Hverdict2)".
        brel_load_l. brel_pures_l. brel_load_r.
        iApply brel_na_close. iFrame "Hclose".
        iSplitL "Hα1 Hβ1 Hkey1 Htg1 Hverdict1 Hα2 Hβ2 Hkey2 Htagged2 Hverdict2".
        { iNext. iRight. iRight. iExists k1, k2, b, tg. by iFrame. }
        brel_pures_r. iModIntro. by iExists _.
  Qed.

End mac_pad.

(* ------------------------------------------------------------------ *)
(* [MAC_pad] and [MAC_ideal], up to [1/q].                             *)
(* ------------------------------------------------------------------ *)

Section mac_ideal.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  Import valgroup_notation.
  Import valgroup_tactics.
  Import fingroup.
  Import fingroup.fingroup.
  #[local] Notation n := (S n'').
  #[local] Notation q := (S (S n'')).
  #[local] Open Scope R_scope.

  Context (Hq : is_true (prime.prime q)).

  Lemma tag_neq (u t0 t' : vgG) (k : nat) : (u ^+ k)%g ≠ (t' * t0^-1)%g → t' ≠ (t0 * u ^+ k)%g.
  Proof. intros Hne ->. apply Hne. by rewrite (vg_commute t0) mulgK. Qed.

  (* The credit for one verification, as the avoid rule wants it. *)
  Lemma bad_ec (u w : vgG) : u ≠ 1%g → ↯ (1 / q) -∗ ↯ (length (bad u w) / S n).
  Proof.
    intros Hu. iApply ec_weaken. split.
    { apply Rcomplements.Rdiv_le_0_compat; [apply pos_INR|apply lt_0_INR; lia]. }
    apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat, lt_0_INR; lia|].
    change 1 with (INR 1). apply le_INR. by apply bad_length.
  Qed.

  Lemma g_neq_1 : g ≠ 1%g.
  Proof.
    intros Hg. pose proof g_order as Ho. rewrite Hg order1 in Ho. lia.
  Qed.

  Definition tgv (tg : option (vgG * vgG)) : val :=
    optv ((λ p, (vgval p.1, vgval p.2)%V) <$> tg).

  (* The joint state of [MAC_pad] (left) and [MAC_ideal] (right). *)
  Definition pad_ideal_inv (α1 β1 : loc) (key1 tg1 verdict1 : loc)
                           (α2 β2 : loc) (key2 tg2 verdict2 : loc) : iProp Σ :=
    (↯ (1 / q) ∗
     α1 ↪N (n; []) ∗ β1 ↪N (n; []) ∗ key1 ↦ NONEV ∗ tg1 ↦ NONEV ∗ verdict1 ↦ NONEV ∗
     α2 ↪ₛN (n; []) ∗ β2 ↪ₛN (n; []) ∗ key2 ↦ₛ NONEV ∗ tg2 ↦ₛ NONEV ∗ verdict2 ↦ₛ NONEV)
    ∨
    (∃ (m0 t0 : vgG) (v : option bool) (ns2 : list nat),
       (match v with None => ↯ (1 / q) | Some _ => True end) ∗
       α1 ↪N (n; []) ∗ β1 ↪N (n; []) ∗ key1 ↦ NONEV ∗ tg1 ↦ SOMEV (vgval m0, vgval t0) ∗ verdict1 ↦ optb v ∗
       α2 ↪ₛN (n; ns2) ∗ β2 ↪ₛN (n; []) ∗ key2 ↦ₛ NONEV ∗ tg2 ↦ₛ SOMEV (vgval m0, vgval t0) ∗ verdict2 ↦ₛ optb v)
    ∨
    (∃ (k1 k2 : nat) (tg : option (vgG * vgG)),
       ⌜k1 ≤ n ∧ k2 ≤ n⌝ ∗
       α1 ↪N (n; []) ∗ β1 ↪N (n; []) ∗ key1 ↦ SOMEV (#k1, #k2) ∗ tg1 ↦ tgv tg ∗ verdict1 ↦ SOMEV #false ∗
       α2 ↪ₛN (n; []) ∗ β2 ↪ₛN (n; []) ∗ key2 ↦ₛ SOMEV (#k1, #k2) ∗ tg2 ↦ₛ tgv tg ∗ verdict2 ↦ₛ SOMEV #false).

  Lemma MAC_pad_MAC_ideal_body : ↯ (1 / q) ⊢ BREL (MAC_pad #()%V) ≤ (MAC_ideal #()%V) <|⊥|> {{ MACT }}.
  Proof.
    iIntros "Hε".
    rewrite /MAC_pad /MAC_ideal. brel_pures_l. brel_pures_r.
    brel_alloctape_l α1 as "Hα1". brel_pures_l.
    brel_alloctape_l β1 as "Hβ1". brel_pures_l.
    brel_alloc_l key1 as "Hkey1". brel_pures_l.
    brel_alloc_l tg1 as "Htg1". brel_pures_l.
    brel_alloc_l verdict1 as "Hverdict1". brel_pures_l.
    brel_alloctape_r α2 as "Hα2". brel_pures_r.
    brel_alloctape_r β2 as "Hβ2". brel_pures_r.
    brel_alloc_r key2 as "Hkey2". brel_pures_r.
    brel_alloc_r tg2 as "Htg2". brel_pures_r.
    brel_alloc_r verdict2 as "Hverdict2".
    rewrite !Nat2Z.id.
    iAssert (α2 ↪ₛN (n; []))%I with "[Hα2]" as "Hα2"; first (iExists []; by iFrame).
    iAssert (β2 ↪ₛN (n; []))%I with "[Hβ2]" as "Hβ2"; first (iExists []; by iFrame).
    iApply (brel_na_alloc (pad_ideal_inv α1 β1 key1 tg1 verdict1 α2 β2 key2 tg2 verdict2) macN).
    iSplitL; [iNext; iLeft; iFrame|].
    iIntros "#Hinv". brel_pures_r.
    iModIntro. rewrite /MACT /sem_ty_prod /tagT /verifyT.
    iExists _, _, _, _. do 2 (iSplit; first done). iSplit.
    - (* tag *)
      rewrite /sem_ty_mbang /sem_ty_arr /=. iIntros "!>" (m1 m2) "(%m & -> & ->)".
      brel_pures_l. brel_pures_r.
      iApply (brel_na_inv _ _ macN); [set_solver|]. iFrame "Hinv".
      iIntros "(>HI & Hclose)". rewrite /pad_ideal_inv.
      iDestruct "HI" as "[(Hε & Hα1 & Hβ1 & Hkey1 & Htg1 & Hverdict1 & Hα2 & Hβ2 & Hkey2 & Htg2 & Hverdict2) | [HI | HI]]".
      + brel_load_l. brel_pures_l. brel_load_l. brel_pures_l.
        brel_load_r. brel_pures_r. brel_load_r. brel_pures_r.
        iApply (brel_couple_TT _ _ (λ x, x) _ _ _ _ β1 β2 [] []); first done.
        iFrame "Hβ1 Hβ2". iIntros (r) "[Hβ1 Hβ2]".
        brel_rand_l as "%Hr". iApply (brel_exp_l [AppRCtx _]). brel_pures_l. brel_store_l. brel_pures_l.
        brel_rand_r as "%Hr'". iApply (brel_exp_r [AppRCtx _]). brel_pures_r. brel_store_r.
        iApply brel_na_close. iFrame "Hclose".
        iSplitL "Hε Hα1 Hβ1 Hkey1 Htg1 Hverdict1 Hα2 Hβ2 Hkey2 Htg2 Hverdict2".
        { iNext. iRight. iLeft. iExists m, _, None, []. iFrame. }
        brel_pures_r. iModIntro. iExists _, _. iRight. iSplit; [done|]. iSplit; [done|]. by iExists _.
      + iDestruct "HI" as (m0 t0 v ns2) "(Hε & Hα1 & Hβ1 & Hkey1 & Htg1 & Hverdict1 & Hα2 & Hβ2 & Hkey2 & Htg2 & Hverdict2)".
        brel_load_l. brel_pures_l. brel_load_r.
        iApply brel_na_close. iFrame "Hclose".
        iSplitL "Hε Hα1 Hβ1 Hkey1 Htg1 Hverdict1 Hα2 Hβ2 Hkey2 Htg2 Hverdict2".
        { iNext. iRight. iLeft. iExists m0, t0, v, ns2. by iFrame. }
        brel_pures_r. iModIntro. iExists _, _. iLeft. by (iSplit; [|iSplit]).
      + iDestruct "HI" as (k1 k2 tg) "(%Hk & Hα1 & Hβ1 & Hkey1 & Htg1 & Hverdict1 & Hα2 & Hβ2 & Hkey2 & Htg2 & Hverdict2)".
        destruct tg as [[m0 t0]|]; rewrite /tgv /=.
        * brel_load_l. brel_pures_l. brel_load_r.
          iApply brel_na_close. iFrame "Hclose".
          iSplitL "Hα1 Hβ1 Hkey1 Htg1 Hverdict1 Hα2 Hβ2 Hkey2 Htg2 Hverdict2".
          { iNext. iRight. iRight. iExists k1, k2, (Some (m0, t0)). rewrite /tgv /=. by iFrame. }
          brel_pures_r. iModIntro. iExists _, _. iLeft. by (iSplit; [|iSplit]).
        * brel_load_l. brel_pures_l. brel_load_l. brel_pures_l.
          brel_load_r. brel_pures_r. brel_load_r. brel_pures_r.
          rewrite /tag. brel_pures_l. brel_exp_l. brel_exp_l. brel_mult_l. brel_pures_l. brel_store_l.
          brel_pures_r. brel_exp_r. brel_exp_r. brel_mult_r. brel_pures_r. brel_store_r.
          iApply brel_na_close. iFrame "Hclose".
          iSplitL "Hα1 Hβ1 Hkey1 Htg1 Hverdict1 Hα2 Hβ2 Hkey2 Htg2 Hverdict2".
          { iNext. iRight. iRight. iExists k1, k2, (Some (m, (m ^+ k1 * g ^+ k2)%g)). rewrite /tgv /=. by iFrame. }
          brel_pures_l. brel_pures_r. iModIntro. iExists _, _. iRight. iSplit; [done|]. iSplit; [done|]. by iExists _.
    - (* verify *)
      rewrite /sem_ty_mbang /sem_ty_arr /=.
      iIntros "!>" (p1 p2) "(%w1 & %w1' & %w2 & %w2' & -> & -> & (%m' & -> & ->) & (%t' & -> & ->))".
      brel_pures_l. brel_pures_r.
      iApply (brel_na_inv _ _ macN); [set_solver|]. iFrame "Hinv".
      iIntros "(>HI & Hclose)". rewrite /pad_ideal_inv.
      iDestruct "HI" as "[(Hε & Hα1 & Hβ1 & Hkey1 & Htg1 & Hverdict1 & Hα2 & Hβ2 & Hkey2 & Htg2 & Hverdict2) | [HI | HI]]".
      + (* verify first: the pad rejects unless [k2] is the one bad exponent *)
        brel_load_l. brel_pures_l. brel_load_l. brel_pures_l.
        brel_load_r. brel_pures_r. brel_load_r. brel_pures_r.
        iApply (brel_couple_TT _ _ (λ x, x) _ _ _ _ α1 α2 [] []); first done.
        iFrame "Hα1 Hα2". iIntros (k1) "[Hα1 Hα2]".
        brel_rand_l as "%Hk1". brel_pures_l. brel_rand_r as "%Hk1'". brel_pures_r.
        iDestruct (bad_ec g (t' * (m' ^+ k1)^-1)%g g_neq_1 with "Hε") as "Hε".
        iApply (brel_couple_TT_avoid _ (bad g (t' * (m' ^+ k1)^-1)%g) (λ x, x) _ _ _ _ _ β1 β2 [] []);
          [apply bad_NoDup|done|].
        iFrame "Hβ1 Hβ2 Hε". iIntros (k2 Hk2bad) "[Hβ1 Hβ2]".
        brel_rand_l as "%Hk2". brel_pures_l. brel_rand_r as "%Hk2'". brel_pures_r.
        brel_store_l. brel_pures_l. brel_store_r. brel_pures_r.
        rewrite /tag. brel_pures_l. brel_exp_l. brel_exp_l. brel_mult_l. brel_eq_l. brel_pures_l.
        rewrite bool_decide_eq_false_2; last (apply tag_neq; intros Hbad; apply Hk2bad; by apply bad_spec).
        brel_store_l. brel_pures_l. brel_store_r.
        iApply brel_na_close. iFrame "Hclose".
        iSplitL "Hα1 Hβ1 Hkey1 Htg1 Hverdict1 Hα2 Hβ2 Hkey2 Htg2 Hverdict2".
        { iNext. iRight. iRight. iExists k1, k2, None. rewrite /tgv /=. iFrame. iPureIntro. lia. }
        brel_pures_r. iModIntro. by iExists _.
      + (* tag first *)
        iDestruct "HI" as (m0 t0 v ns2) "(Hε & Hα1 & Hβ1 & Hkey1 & Htg1 & Hverdict1 & Hα2 & Hβ2 & Hkey2 & Htg2 & Hverdict2)".
        destruct v as [b|]; simpl.
        * brel_load_l. brel_pures_l. brel_load_r.
          iApply brel_na_close. iFrame "Hclose".
          iSplitL "Hα1 Hβ1 Hkey1 Htg1 Hverdict1 Hα2 Hβ2 Hkey2 Htg2 Hverdict2".
          { iNext. iRight. iLeft. iExists m0, t0, (Some b), ns2. by iFrame. }
          brel_pures_r. iModIntro. by iExists _.
        * brel_load_l. brel_pures_l. brel_load_l. brel_pures_l. brel_eq_l.
          brel_load_r. brel_pures_r. brel_load_r. brel_pures_r. brel_eq_r.
          destruct (decide (m' = m0)) as [->|Hne].
          -- rewrite (bool_decide_eq_true_2 _ eq_refl); try apply _.
             brel_pures_l. brel_eq_l. brel_pures_l. brel_pures_r. brel_eq_r. brel_pures_r.
             brel_store_l. brel_pures_l. brel_store_r.
             iApply brel_na_close. iFrame "Hclose".
             iSplitL "Hα1 Hβ1 Hkey1 Htg1 Hverdict1 Hα2 Hβ2 Hkey2 Htg2 Hverdict2".
             { iNext. iRight. iLeft. iExists m0, t0, (Some _), ns2. by iFrame. }
             brel_pures_r. iModIntro. by iExists _.
          -- rewrite (bool_decide_eq_false_2 _ Hne); try apply _.
             brel_pures_l. brel_pures_r.
             iDestruct (bad_ec (m' * m0^-1)%g (t' * t0^-1)%g with "Hε") as "Hε".
             { intros Hu. apply Hne. by rewrite -(mulgKV m0 m') Hu mul1g. }
             iApply (brel_couple_TT_avoid _ (bad (m' * m0^-1)%g (t' * t0^-1)%g) (λ x, x) _ _ _ _ _ α1 α2 [] ns2);
               [apply bad_NoDup|done|].
             iFrame "Hα1 Hα2 Hε". iIntros (k1 Hk1bad) "[Hα1 Hα2]".
             brel_rand_l as "%Hk1". brel_pures_l.
             brel_inv_l. brel_mult_l. brel_exp_l. brel_mult_l. brel_eq_l. brel_pures_l.
             rewrite bool_decide_eq_false_2; last (apply tag_neq; intros Hbad; apply Hk1bad; by apply bad_spec).
             brel_store_l. brel_pures_l. brel_store_r.
             iApply brel_na_close. iFrame "Hclose".
             iSplitL "Hα1 Hβ1 Hkey1 Htg1 Hverdict1 Hα2 Hβ2 Hkey2 Htg2 Hverdict2".
             { iNext. iRight. iLeft. iExists m0, t0, (Some false), (ns2 ++ [fin_to_nat k1]). by iFrame. }
             brel_pures_r. iModIntro. by iExists _.
      + iDestruct "HI" as (k1 k2 tg) "(%Hk & Hα1 & Hβ1 & Hkey1 & Htg1 & Hverdict1 & Hα2 & Hβ2 & Hkey2 & Htg2 & Hverdict2)".
        brel_load_l. brel_pures_l. brel_load_r.
        iApply brel_na_close. iFrame "Hclose".
        iSplitL "Hα1 Hβ1 Hkey1 Htg1 Hverdict1 Hα2 Hβ2 Hkey2 Htg2 Hverdict2".
        { iNext. iRight. iRight. iExists k1, k2, tg. by iFrame. }
        brel_pures_r. iModIntro. by iExists _.
  Qed.

  (* The joint state of [MAC_ideal] (left) and [MAC_pad] (right). *)
  Definition ideal_pad_inv (α1 β1 : loc) (key1 tg1 verdict1 : loc)
                           (α2 β2 : loc) (key2 tg2 verdict2 : loc) : iProp Σ :=
    (↯ (1 / q) ∗
     α1 ↪N (n; []) ∗ β1 ↪N (n; []) ∗ key1 ↦ NONEV ∗ tg1 ↦ NONEV ∗ verdict1 ↦ NONEV ∗
     α2 ↪ₛN (n; []) ∗ β2 ↪ₛN (n; []) ∗ key2 ↦ₛ NONEV ∗ tg2 ↦ₛ NONEV ∗ verdict2 ↦ₛ NONEV)
    ∨
    (∃ (m0 t0 : vgG) (v : option bool) (ns1 : list nat),
       (match v with None => ↯ (1 / q) | Some _ => True end) ∗
       α1 ↪N (n; ns1) ∗ β1 ↪N (n; []) ∗ key1 ↦ NONEV ∗ tg1 ↦ SOMEV (vgval m0, vgval t0) ∗ verdict1 ↦ optb v ∗
       α2 ↪ₛN (n; []) ∗ β2 ↪ₛN (n; []) ∗ key2 ↦ₛ NONEV ∗ tg2 ↦ₛ SOMEV (vgval m0, vgval t0) ∗ verdict2 ↦ₛ optb v)
    ∨
    (∃ (k1 k2 : nat) (tg : option (vgG * vgG)),
       ⌜k1 ≤ n ∧ k2 ≤ n⌝ ∗
       α1 ↪N (n; []) ∗ β1 ↪N (n; []) ∗ key1 ↦ SOMEV (#k1, #k2) ∗ tg1 ↦ tgv tg ∗ verdict1 ↦ SOMEV #false ∗
       α2 ↪ₛN (n; []) ∗ β2 ↪ₛN (n; []) ∗ key2 ↦ₛ SOMEV (#k1, #k2) ∗ tg2 ↦ₛ tgv tg ∗ verdict2 ↦ₛ SOMEV #false).

  Lemma MAC_ideal_MAC_pad_body : ↯ (1 / q) ⊢ BREL (MAC_ideal #()%V) ≤ (MAC_pad #()%V) <|⊥|> {{ MACT }}.
  Proof.
    iIntros "Hε".
    rewrite /MAC_pad /MAC_ideal. brel_pures_l. brel_pures_r.
    brel_alloctape_l α1 as "Hα1". brel_pures_l.
    brel_alloctape_l β1 as "Hβ1". brel_pures_l.
    brel_alloc_l key1 as "Hkey1". brel_pures_l.
    brel_alloc_l tg1 as "Htg1". brel_pures_l.
    brel_alloc_l verdict1 as "Hverdict1". brel_pures_l.
    brel_alloctape_r α2 as "Hα2". brel_pures_r.
    brel_alloctape_r β2 as "Hβ2". brel_pures_r.
    brel_alloc_r key2 as "Hkey2". brel_pures_r.
    brel_alloc_r tg2 as "Htg2". brel_pures_r.
    brel_alloc_r verdict2 as "Hverdict2".
    rewrite !Nat2Z.id.
    iAssert (α2 ↪ₛN (n; []))%I with "[Hα2]" as "Hα2"; first (iExists []; by iFrame).
    iAssert (β2 ↪ₛN (n; []))%I with "[Hβ2]" as "Hβ2"; first (iExists []; by iFrame).
    iApply (brel_na_alloc (ideal_pad_inv α1 β1 key1 tg1 verdict1 α2 β2 key2 tg2 verdict2) macN).
    iSplitL; [iNext; iLeft; iFrame|].
    iIntros "#Hinv". brel_pures_r.
    iModIntro. rewrite /MACT /sem_ty_prod /tagT /verifyT.
    iExists _, _, _, _. do 2 (iSplit; first done). iSplit.
    - (* tag *)
      rewrite /sem_ty_mbang /sem_ty_arr /=. iIntros "!>" (m1 m2) "(%m & -> & ->)".
      brel_pures_l. brel_pures_r.
      iApply (brel_na_inv _ _ macN); [set_solver|]. iFrame "Hinv".
      iIntros "(>HI & Hclose)". rewrite /ideal_pad_inv.
      iDestruct "HI" as "[(Hε & Hα1 & Hβ1 & Hkey1 & Htg1 & Hverdict1 & Hα2 & Hβ2 & Hkey2 & Htg2 & Hverdict2) | [HI | HI]]".
      + brel_load_l. brel_pures_l. brel_load_l. brel_pures_l.
        brel_load_r. brel_pures_r. brel_load_r. brel_pures_r.
        iApply (brel_couple_TT _ _ (λ x, x) _ _ _ _ β1 β2 [] []); first done.
        iFrame "Hβ1 Hβ2". iIntros (r) "[Hβ1 Hβ2]".
        brel_rand_l as "%Hr". iApply (brel_exp_l [AppRCtx _]). brel_pures_l. brel_store_l. brel_pures_l.
        brel_rand_r as "%Hr'". iApply (brel_exp_r [AppRCtx _]). brel_pures_r. brel_store_r.
        iApply brel_na_close. iFrame "Hclose".
        iSplitL "Hε Hα1 Hβ1 Hkey1 Htg1 Hverdict1 Hα2 Hβ2 Hkey2 Htg2 Hverdict2".
        { iNext. iRight. iLeft. iExists m, _, None, []. iFrame. }
        brel_pures_r. iModIntro. iExists _, _. iRight. iSplit; [done|]. iSplit; [done|]. by iExists _.
      + iDestruct "HI" as (m0 t0 v ns1) "(Hε & Hα1 & Hβ1 & Hkey1 & Htg1 & Hverdict1 & Hα2 & Hβ2 & Hkey2 & Htg2 & Hverdict2)".
        brel_load_l. brel_pures_l. brel_load_r.
        iApply brel_na_close. iFrame "Hclose".
        iSplitL "Hε Hα1 Hβ1 Hkey1 Htg1 Hverdict1 Hα2 Hβ2 Hkey2 Htg2 Hverdict2".
        { iNext. iRight. iLeft. iExists m0, t0, v, ns1. by iFrame. }
        brel_pures_r. iModIntro. iExists _, _. iLeft. by (iSplit; [|iSplit]).
      + iDestruct "HI" as (k1 k2 tg) "(%Hk & Hα1 & Hβ1 & Hkey1 & Htg1 & Hverdict1 & Hα2 & Hβ2 & Hkey2 & Htg2 & Hverdict2)".
        destruct tg as [[m0 t0]|]; rewrite /tgv /=.
        * brel_load_l. brel_pures_l. brel_load_r.
          iApply brel_na_close. iFrame "Hclose".
          iSplitL "Hα1 Hβ1 Hkey1 Htg1 Hverdict1 Hα2 Hβ2 Hkey2 Htg2 Hverdict2".
          { iNext. iRight. iRight. iExists k1, k2, (Some (m0, t0)). rewrite /tgv /=. by iFrame. }
          brel_pures_r. iModIntro. iExists _, _. iLeft. by (iSplit; [|iSplit]).
        * brel_load_l. brel_pures_l. brel_load_l. brel_pures_l.
          brel_load_r. brel_pures_r. brel_load_r. brel_pures_r.
          rewrite /tag. brel_pures_l. brel_exp_l. brel_exp_l. brel_mult_l. brel_pures_l. brel_store_l.
          brel_pures_r. brel_exp_r. brel_exp_r. brel_mult_r. brel_pures_r. brel_store_r.
          iApply brel_na_close. iFrame "Hclose".
          iSplitL "Hα1 Hβ1 Hkey1 Htg1 Hverdict1 Hα2 Hβ2 Hkey2 Htg2 Hverdict2".
          { iNext. iRight. iRight. iExists k1, k2, (Some (m, (m ^+ k1 * g ^+ k2)%g)). rewrite /tgv /=. by iFrame. }
          brel_pures_l. brel_pures_r. iModIntro. iExists _, _. iRight. iSplit; [done|]. iSplit; [done|]. by iExists _.
    - (* verify *)
      rewrite /sem_ty_mbang /sem_ty_arr /=.
      iIntros "!>" (p1 p2) "(%w1 & %w1' & %w2 & %w2' & -> & -> & (%m' & -> & ->) & (%t' & -> & ->))".
      brel_pures_l. brel_pures_r.
      iApply (brel_na_inv _ _ macN); [set_solver|]. iFrame "Hinv".
      iIntros "(>HI & Hclose)". rewrite /ideal_pad_inv.
      iDestruct "HI" as "[(Hε & Hα1 & Hβ1 & Hkey1 & Htg1 & Hverdict1 & Hα2 & Hβ2 & Hkey2 & Htg2 & Hverdict2) | [HI | HI]]".
      + (* verify first *)
        brel_load_l. brel_pures_l. brel_load_l. brel_pures_l.
        brel_load_r. brel_pures_r. brel_load_r. brel_pures_r.
        iApply (brel_couple_TT _ _ (λ x, x) _ _ _ _ α1 α2 [] []); first done.
        iFrame "Hα1 Hα2". iIntros (k1) "[Hα1 Hα2]".
        brel_rand_l as "%Hk1". brel_pures_l. brel_rand_r as "%Hk1'". brel_pures_r.
        iDestruct (bad_ec g (t' * (m' ^+ k1)^-1)%g g_neq_1 with "Hε") as "Hε".
        iApply (brel_couple_TT_avoid _ (bad g (t' * (m' ^+ k1)^-1)%g) (λ x, x) _ _ _ _ _ β1 β2 [] []);
          [apply bad_NoDup|done|].
        iFrame "Hβ1 Hβ2 Hε". iIntros (k2 Hk2bad) "[Hβ1 Hβ2]".
        brel_rand_l as "%Hk2". brel_pures_l. brel_rand_r as "%Hk2'". brel_pures_r.
        brel_store_l. brel_pures_l. brel_store_r. brel_pures_r.
        rewrite /tag. brel_pures_r. brel_exp_r. brel_exp_r. brel_mult_r. brel_eq_r. brel_pures_r.
        rewrite bool_decide_eq_false_2; last (apply tag_neq; intros Hbad; apply Hk2bad; by apply bad_spec).
        brel_store_l. brel_pures_l. brel_store_r.
        iApply brel_na_close. iFrame "Hclose".
        iSplitL "Hα1 Hβ1 Hkey1 Htg1 Hverdict1 Hα2 Hβ2 Hkey2 Htg2 Hverdict2".
        { iNext. iRight. iRight. iExists k1, k2, None. rewrite /tgv /=. iFrame. iPureIntro. lia. }
        brel_pures_r. iModIntro. by iExists _.
      + (* tag first *)
        iDestruct "HI" as (m0 t0 v ns1) "(Hε & Hα1 & Hβ1 & Hkey1 & Htg1 & Hverdict1 & Hα2 & Hβ2 & Hkey2 & Htg2 & Hverdict2)".
        destruct v as [b|]; simpl.
        * brel_load_l. brel_pures_l. brel_load_r.
          iApply brel_na_close. iFrame "Hclose".
          iSplitL "Hα1 Hβ1 Hkey1 Htg1 Hverdict1 Hα2 Hβ2 Hkey2 Htg2 Hverdict2".
          { iNext. iRight. iLeft. iExists m0, t0, (Some b), ns1. by iFrame. }
          brel_pures_r. iModIntro. by iExists _.
        * brel_load_l. brel_pures_l. brel_load_l. brel_pures_l. brel_eq_l.
          brel_load_r. brel_pures_r. brel_load_r. brel_pures_r. brel_eq_r.
          destruct (decide (m' = m0)) as [->|Hne].
          -- rewrite (bool_decide_eq_true_2 _ eq_refl); try apply _.
             brel_pures_l. brel_eq_l. brel_pures_l. brel_pures_r. brel_eq_r. brel_pures_r.
             brel_store_l. brel_pures_l. brel_store_r.
             iApply brel_na_close. iFrame "Hclose".
             iSplitL "Hα1 Hβ1 Hkey1 Htg1 Hverdict1 Hα2 Hβ2 Hkey2 Htg2 Hverdict2".
             { iNext. iRight. iLeft. iExists m0, t0, (Some _), ns1. by iFrame. }
             brel_pures_r. iModIntro. by iExists _.
          -- rewrite (bool_decide_eq_false_2 _ Hne); try apply _.
             brel_pures_l. brel_pures_r.
             iDestruct (bad_ec (m' * m0^-1)%g (t' * t0^-1)%g with "Hε") as "Hε".
             { intros Hu. apply Hne. by rewrite -(mulgKV m0 m') Hu mul1g. }
             iApply (brel_couple_TT_avoid _ (bad (m' * m0^-1)%g (t' * t0^-1)%g) (λ x, x) _ _ _ _ _ α1 α2 ns1 []);
               [apply bad_NoDup|done|].
             iFrame "Hα1 Hα2 Hε". iIntros (k1 Hk1bad) "[Hα1 Hα2]".
             brel_rand_r as "%Hk1". brel_pures_r.
             brel_inv_r. brel_mult_r. brel_exp_r. brel_mult_r. brel_eq_r. brel_pures_r.
             rewrite bool_decide_eq_false_2; last (apply tag_neq; intros Hbad; apply Hk1bad; by apply bad_spec).
             brel_store_l. brel_pures_l. brel_store_r.
             iApply brel_na_close. iFrame "Hclose".
             iSplitL "Hα1 Hβ1 Hkey1 Htg1 Hverdict1 Hα2 Hβ2 Hkey2 Htg2 Hverdict2".
             { iNext. iRight. iLeft. iExists m0, t0, (Some false), (ns1 ++ [fin_to_nat k1]). by iFrame. }
             brel_pures_r. iModIntro. by iExists _.
      + iDestruct "HI" as (k1 k2 tg) "(%Hk & Hα1 & Hβ1 & Hkey1 & Htg1 & Hverdict1 & Hα2 & Hβ2 & Hkey2 & Htg2 & Hverdict2)".
        brel_load_l. brel_pures_l. brel_load_r.
        iApply brel_na_close. iFrame "Hclose".
        iSplitL "Hα1 Hβ1 Hkey1 Htg1 Hverdict1 Hα2 Hβ2 Hkey2 Htg2 Hverdict2".
        { iNext. iRight. iRight. iExists k1, k2, tg. by iFrame. }
        brel_pures_r. iModIntro. by iExists _.
  Qed.

End mac_ideal.

(* ------------------------------------------------------------------ *)
(* The relations between the instances, as factories.                 *)
(* ------------------------------------------------------------------ *)

Section mac_fac.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  Import valgroup_notation.
  #[local] Notation n := (S n'').
  #[local] Notation q := (S (S n'')).

  Lemma mac_fac_of_body (M M' : val) :
    (⊢ BREL (M #()%V) ≤ (M' #()%V) <|⊥|> {{ MACT }}) →
    ⊢ ⊨ᵥ M ≤ M' : fac MS MACT.
  Proof.
    iIntros (HM). rewrite /sem_val_typed /fac /sem_ty_mbang /sem_ty_arr /=.
    iIntros "!> !>" (u1 u2) "[-> ->]". iApply HM.
  Qed.

  Lemma MAC_MAC_pad : ⊢ ⊨ᵥ MAC ≤ MAC_pad : fac MS MACT.
  Proof. apply mac_fac_of_body, MAC_MAC_pad_body. Qed.

  Lemma MAC_pad_MAC : ⊢ ⊨ᵥ MAC_pad ≤ MAC : fac MS MACT.
  Proof. apply mac_fac_of_body, MAC_pad_MAC_body. Qed.

End mac_fac.

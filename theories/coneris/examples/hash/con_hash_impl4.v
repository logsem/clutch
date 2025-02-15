From iris.base_logic.lib Require Import ghost_map.
From clutch.coneris Require Import coneris.
From clutch.coneris.lib Require Import map lock.
Set Default Proof Using "Type*".

Class con_hashG Σ `{conerisGS Σ} := {
  con_hash_lock :: lock.lock;
  con_hash_lockG : lockG Σ;
  con_hash_ghost_mapG1 :: ghost_mapG Σ nat loc;
  con_hash_ghost_mapG2 :: ghost_mapG Σ nat (option nat);
}.

Section con_hash_impl.
  Context `{!conerisGS Σ, !con_hashG Σ}.

  Variable val_size : nat.

  (** * Sequential hash function with per key presampling tapes *)
  Definition alloc_tapes : val :=
    rec: "alloc_tapes" "tm" "n" :=
     if: ("n" - #1) < #0 then
        #()
      else
       let: "α" := alloc #val_size in
        map.set "tm" ("n" - #1) "α";;
       "alloc_tapes" "tm" ("n" - #1).

  Definition init_hash_state : val :=
   λ: "max_val",
      let: "val_map" := init_map #() in
      let: "tape_map" := init_map #() in
      alloc_tapes "tape_map" ("max_val" + #1);;
      ("val_map", "tape_map").

  Definition compute_hash : val :=
    λ: "vm" "tm" "v",
      match: map.get "vm" "v" with
      | SOME "b" => "b"
      | NONE =>
          match: map.get "tm" "v" with
            | SOME "α" =>
                let: "b" := rand("α") #val_size  in
                set "vm" "v" "b";;
                "b"
          | NONE => #0
          end
      end.

  Definition compute_hash_specialized vm tm : val :=
    λ: "v",
      match: map.get vm "v" with
      | SOME "b" => "b"
      | NONE =>
          match: map.get tm "v" with
            | SOME "α" =>
                let: "b" := rand("α") #val_size in
                set vm "v" "b";;
                "b"
            | NONE => #false
            end
      end.

  Lemma wp_alloc_tapes E ltm max :
    {{{ map_list ltm ∅ }}}
      alloc_tapes #ltm #max @ E
    {{{ RET #(); ∃ tm,
        map_list ltm ((λ v, LitV (LitLbl v)) <$> tm) ∗
        ⌜(∀ i : nat, i < max ↔ i ∈ dom tm)⌝ ∗
        ([∗ map] i ↦ α ∈ tm, α ↪N (val_size; [])) }}}.
  Proof.
    iIntros (Φ) "Htm HΦ".
    rewrite /alloc_tapes.
    remember max as k eqn:Heqk.
    iEval (setoid_rewrite Heqk) in "HΦ".
    iAssert (∃ tm, ⌜ (∀ i : nat, (k <= i < max)%nat ↔ i ∈ dom tm) ⌝ ∗
                   map_list ltm ((λ v, LitV (LitLbl v)) <$> tm) ∗
                   ([∗ map] i ↦ α ∈ tm, α ↪N (val_size; [])))%I with "[Htm]" as "Htm".
    { iExists ∅. rewrite fmap_empty. iFrame. iSplit.
      { iPureIntro. subst. intros; split; try lia. rewrite dom_empty_L. inversion 1. }
      { rewrite big_sepM_empty. auto. } }
    assert (Hlek: k <= max) by lia.
    clear Heqk.
    iInduction k as [| k] "IH" forall (Hlek).
    - wp_pures. iApply "HΦ". iModIntro. iDestruct "Htm" as (tm Hdom) "(Hm&Htapes)".
      iFrame. iPureIntro. split.
      { intros. apply Hdom. lia. }
      { intros. apply Hdom. auto. }
    - iSpecialize ("IH" with "[] HΦ").
      { iPureIntro; lia. }
      wp_pures.
      case_bool_decide; first by lia.
      wp_pures.
      wp_apply (wp_alloc_tape with "[//]").
      iIntros (α) "Hα". wp_pures.
      iDestruct "Htm" as (tm Hdom) "(Htm&Htapes)".
      replace (Z.of_nat (S k) - 1)%Z with (Z.of_nat k)%Z by lia.
      wp_apply (wp_set with "Htm"). iIntros "Htm".
      wp_pure _. wp_pure _. wp_pure _.
      replace (Z.of_nat (S k) - 1)%Z with (Z.of_nat k)%Z by lia.
      iApply "IH".
      iExists (<[k := α]>tm). rewrite fmap_insert. iFrame.
      iSplit.
      { iPureIntro. intros i. split.
        * intros Hle. set_unfold.
          destruct (decide (i = k)); auto.
          right. apply Hdom; lia.
        * set_unfold. intros [?|Hdom']; try lia.
          apply Hdom in Hdom'. lia. }
      iApply (big_sepM_insert with "[$Htapes $Hα]").
      apply not_elem_of_dom_1. intros Hbad.
      assert (S k <= k).
      { apply Hdom; auto. }
      lia.
  Qed.

  Definition hashkey (γt γv : gname) (k : nat) (v : option nat) : iProp Σ :=
    ∃ (α : loc) (w : option nat),
      k ↪[γt] α ∗ k ↪[γv] w ∗
      match v with
      | None => α ↪N (val_size; []) ∗ ⌜w = None⌝
      | Some n => α ↪N (val_size; [n]) ∗ ⌜w = None⌝ ∨ ⌜w = Some n⌝
      end.

  Definition hashfun γtm γvm (max : nat) (f : val) : iProp Σ :=
    ∃ (lvm ltm : loc) (vm : gmap nat nat) (vm' : gmap nat (option nat)) (tm : gmap nat loc),
       ⌜ (∀ i : nat, i <= max ↔ i ∈ dom tm) ⌝ ∗
       ⌜ dom vm ⊆ dom tm ⌝ ∗
       ⌜ f = compute_hash_specialized #lvm #ltm ⌝ ∗
       map_list lvm ((λ (n : nat), LitV (LitInt n)) <$> vm) ∗
       map_list ltm ((λ (α : loc), LitV (LitLbl α)) <$> tm) ∗
       ghost_map_auth γtm 1 tm ∗
       ghost_map_auth γvm 1 vm' ∗
       (** [vm] is the physical value map, whereas [vm'] is the logical value map. In this way, the
           points-to [k ↪[γv] None] represents a "permission" to write to the key [k]. *)
       ⌜∀ i v, vm !! i = Some v ↔ vm' !! i = Some (Some v)⌝.

  Lemma wp_init_hash_state max :
    {{{ True }}}
      init_hash_state #max
    {{{ (γt γv : gname) (lvm ltm : loc) (tm : gmap nat loc), RET (#lvm, #ltm);
        hashfun γt γv max (compute_hash_specialized #lvm #ltm) ∗
        ⌜(∀ i : nat, i < S max ↔ i ∈ dom tm)⌝ ∗
        ([∗ map] k ↦ v ∈ tm, hashkey γt γv k None) }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite /init_hash_state.
    wp_pures.
    wp_apply (wp_init_map with "[//]").
    iIntros (lvm) "Hvm". wp_pures.
    wp_apply (wp_init_map with "[//]").
    iIntros (ltm) "Htm". wp_pures.
    rewrite /compute_hash. wp_pures.
    replace (Z.of_nat max + 1)%Z with (Z.of_nat (S max))%Z by lia.
    wp_apply (wp_alloc_tapes with "Htm").
    iDestruct 1 as (tm) "(Htm&%Hdom&Htapes)".
    wp_pures.
    iMod (ghost_map_alloc tm) as (γt) "[Htauth Hkey]".
    iMod (ghost_map_alloc (gset_to_gmap None (dom tm))) as (γv) "[Hvauth Hvals]".
    iCombine "Hkey Hvals Htapes" as "Htapes".
    rewrite gset_to_gmap_dom big_sepM_fmap -!big_sepM_sep /=.
    iApply ("HΦ" $! _ _ _ _ tm). iModIntro.
    iSplitR "Htapes".
    { iExists lvm, ltm, ∅, _, tm.
      rewrite ?fmap_empty. iFrame. iSplit.
      { iPureIntro. intros. rewrite -Hdom. split; lia. }
      iSplit; [done|].
      iSplit; [done|].
      iPureIntro. intros ??.
      rewrite lookup_empty.
      split; [done|].
      by intros (?&?&?)%lookup_fmap_Some. }
    iSplit; [done|].
    iApply (big_sepM_mono with "Htapes").
    iIntros (k α Hlookup) "(? & ? & ?)". by iFrame.
  Qed.

  Lemma wp_hashfun_prev E f (max k n : nat) γt γv :
    {{{ hashfun γt γv max f ∗ hashkey γt γv k (Some n) }}}
      f #k @ E
    {{{ RET #n; hashfun γt γv max f ∗ hashkey γt γv k (Some n) }}}.
  Proof.
    iIntros (Φ) "[Hhash (%α & %w & Hk & Hw & Hv)] HΦ".
    iDestruct "Hhash" as (lvm ltm vm vm' tm Hdom1 Hdom2 ->) "(Hvm & Htm & Htapes & Hvals & %Hvm)".
    rewrite /compute_hash_specialized.
    wp_pures.
    wp_apply (wp_get with "Hvm").
    iIntros (vret) "(Hhash&->)".
    rewrite lookup_fmap.
    iDestruct (ghost_map_lookup with "Htapes Hk") as %Ht.
    iDestruct "Hv" as "[[Hα %] | %]".
    - iDestruct (ghost_map_lookup with "Hvals Hw") as %Hv.
      assert (vm !! k = None) as ->.
      { destruct (vm !! k) eqn:?; [|done]. set_solver. }
      wp_pures.
      wp_apply (wp_get with "Htm").
      iIntros (α') "[Htm ->]".
      rewrite lookup_fmap Ht.
      wp_pures.
      wp_apply (wp_rand_tape with "Hα").
      iIntros "[Htape %]". wp_pures.
      wp_apply (wp_set with "Hhash").
      iIntros "Hhash". wp_pures. iApply "HΦ".
      iMod (ghost_map_update (Some _) with "Hvals Hw") as "[Hvals Hw]".
      iModIntro.
      iSplitR "Hk Hw Htape"; last first.
      { iFrame. by iRight. }
      iExists _, _, (<[k:=n]>vm), _, tm.
      iFrame.
      iSplit; first done.
      iSplit.
      { iPureIntro; rewrite dom_insert_L. set_unfold; intros ? [?|?]; auto.
        subst. apply elem_of_dom; eauto. }
      iSplit; first done.
      rewrite fmap_insert; iFrame.
      iPureIntro.
      split.
      { intros [[-> ->] | [? ?]]%lookup_insert_Some.
        { rewrite lookup_insert //. }
        rewrite lookup_insert_ne //.
        by apply Hvm. }
      { intros [[-> ?] | [? ?]]%lookup_insert_Some.
        { rewrite lookup_insert //. }
        rewrite lookup_insert_ne //.
        set_solver. }
    - iDestruct (ghost_map_lookup with "Hvals Hw") as %Hv. subst.
      rewrite -Hvm in Hv. rewrite Hv.
      wp_pures.
      iApply "HΦ". iModIntro.
      iFrame. eauto.
  Qed.

  Lemma hashfun_presample E k (bad : gset nat) (ε εI εO: nonnegreal) max γt γv :
    k ≤ max →
    (∀ x, x ∈ bad → x < S val_size) →
    (εI * size bad + εO * (val_size + 1 - size bad) <= ε * (val_size + 1))%R →
    hashkey γt γv k None -∗
    ↯ ε -∗
    state_update E E (∃ (n : fin (S val_size)),
      ((⌜fin_to_nat n ∉ bad⌝ ∗ ↯ εO) ∨ (⌜fin_to_nat n ∈ bad⌝ ∗ ↯ εI)) ∗
        hashkey γt γv k (Some (fin_to_nat n))).
  Proof.
    iIntros (Hmax Hsize Heps) "Hkey Herr".
    iDestruct "Hkey" as (α w) "(Hk & Hw & Hα & %)".
    iMod (state_step_err_set_in_out _ bad _ εI εO
           with "Hα Herr") as (n) "[Herr Htape] /=".
    { apply cond_nonneg. }
    { apply cond_nonneg. }
    { done. }
    { done. }
    iModIntro. iExists _.
    iFrame "Herr".
    iExists _, _. iFrame.
    iLeft. by iFrame.
  Qed.

  (** * Concurrent hash function with per key presampling tapes*)
  Definition compute_con_hash : val :=
    λ: "l" "hm" "tm" "v",
      acquire "l";;
      let: "output" := compute_hash "hm" "tm" "v" in
      release "l";;
      "output".

  Definition compute_con_hash_specialized (l hm tm : val) : val:=
    λ: "v",
      acquire "l";;
      let: "output" := compute_hash "hm" "tm" "v" in
      release "l";;
      "output".

  Definition init_hash : val :=
    λ: "max_val",
      let, ("hm", "tm") := init_hash_state "max_val" in
      let: "l" := newlock  #() in
      compute_hash ("l", "hm", "tm").

  (** TODO: the lock should just protect [hashfun] *)

End con_hash_impl.

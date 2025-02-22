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

  (** * Sequential hash function with per key presampling tapes *)
  Definition alloc_tapes : val :=
    rec: "alloc_tapes" "val_size" "tm" "n" :=
     if: ("n" - #1) < #0 then
        #()
      else
       let: "α" := alloc "val_size" in
        map.set "tm" ("n" - #1) "α";;
       "alloc_tapes" "val_size" "tm" ("n" - #1).

  Definition compute_hash : val :=
    λ: "val_size" "vm" "tm" "v",
      match: map.get "vm" "v" with
      | SOME "b" => "b"
      | NONE =>
          match: map.get "tm" "v" with
            | SOME "α" =>
                let: "b" := rand("α") "val_size"  in
                set "vm" "v" "b";;
                "b"
          | NONE => #0
          end
      end.

  Definition compute_hash_specialized val_size vm tm : val :=
    λ: "v",
      match: map.get vm "v" with
      | SOME "b" => "b"
      | NONE =>
          match: map.get tm "v" with
            | SOME "α" =>
                let: "b" := rand("α") val_size in
                set vm "v" "b";;
                "b"
            | NONE => #0
            end
      end.

  Definition init_hash_state : val :=
   λ: "val_size" "max_val",
      let: "val_map" := init_map #() in
      let: "tape_map" := init_map #() in
      alloc_tapes "val_size" "tape_map" ("max_val" + #1);;
      compute_hash "val_size" "val_map" "tape_map".

  Lemma wp_alloc_tapes E val_size ltm max :
    {{{ map_list ltm ∅ }}}
      alloc_tapes #val_size #ltm #max @ E
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

  (** Exclusive ownership of the hash key [k], including the ability to presample its hash value.
      We could also make [hashkey] persistent after the first (physical) hash by converting the
      points-to into a persistent points-to. *)
  Definition hashkey (γs : gname * gname) (val_size : nat) (k : nat) (v : option nat) : iProp Σ :=
    ∃ (α : loc) (w : option nat),
      k ↪[γs.1] α ∗ k ↪[γs.2] w ∗
      match v with
      | None => α ↪N (val_size; []) ∗ ⌜w = None⌝
      | Some n => α ↪N (val_size; [n]) ∗ ⌜w = None⌝ ∨ ⌜w = Some n⌝
      end.

  (** (Sequential) hash function *)
  Definition hashfun (γs : gname * gname) (val_size max : nat) (f : val) : iProp Σ :=
    ∃ (lvm ltm : loc) (vm : gmap nat nat) (vm' : gmap nat (option nat)) (tm : gmap nat loc),
       ⌜ (∀ i : nat, i <= max ↔ i ∈ dom tm) ⌝ ∗
       ⌜ dom vm ⊆ dom tm ⌝ ∗
       ⌜ f = compute_hash_specialized #val_size #lvm #ltm ⌝ ∗
       map_list lvm ((λ (n : nat), LitV (LitInt n)) <$> vm) ∗
       map_list ltm ((λ (α : loc), LitV (LitLbl α)) <$> tm) ∗
       ghost_map_auth γs.1 1 tm ∗
       ghost_map_auth γs.2 1 vm' ∗
       (** [vm] is the physical value map, whereas [vm'] is the logical value map. In this way, the
           points-to [k ↪[γv] None] represents a "permission" to write to the key [k]. *)
       ⌜∀ i v, vm !! i = Some v ↔ vm' !! i = Some (Some v)⌝.

  Lemma wp_init_hash_state val_size max :
    {{{ True }}}
      init_hash_state #val_size #max
    {{{ (γs : gname * gname) (tm : gmap nat loc) hash, RET hash;
        hashfun γs val_size max hash ∗
        ⌜(∀ i : nat, i < S max ↔ i ∈ dom tm)⌝ ∗
        ([∗ map] k ↦ v ∈ tm, hashkey γs val_size k None) }}}.
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
    iApply ("HΦ" $! (_, _) tm). iModIntro.
    iSplitR "Htapes".
    { iExists lvm, ltm, ∅, _, tm.
      rewrite ?fmap_empty. iFrame. iSplit.
      { iPureIntro. intros. rewrite -Hdom. split; lia. }
      iSplit; [done|].
      rewrite /compute_hash_specialized.
      iSplit; [done|].
      iPureIntro. intros ??.
      rewrite lookup_empty.
      split; [done|].
      by intros (?&?&?)%lookup_fmap_Some. }
    iSplit; [done|].
    iApply (big_sepM_mono with "Htapes").
    iIntros (k α Hlookup) "(? & ? & ?)". by iFrame.
  Qed.

  Lemma wp_hashfun_prev E f (val_size max k n : nat) γs :
    {{{ hashfun γs val_size max f ∗ hashkey γs val_size k (Some n) }}}
      f #k @ E
    {{{ RET #n; hashfun γs val_size max f ∗ hashkey γs val_size k (Some n) }}}.
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

  (** Presampling of hash key  *)
  Lemma hashkey_presample E val_size k (bad : gset nat) (ε εI εO: nonnegreal) max γs :
    k ≤ max →
    (∀ x, x ∈ bad → x < S val_size) →
    (εI * size bad + εO * (val_size + 1 - size bad) <= ε * (val_size + 1))%R →
    hashkey γs val_size k None -∗
    ↯ ε -∗
    state_update E E (∃ (n : fin (S val_size)),
      ((⌜fin_to_nat n ∉ bad⌝ ∗ ↯ εO) ∨ (⌜fin_to_nat n ∈ bad⌝ ∗ ↯ εI)) ∗
        hashkey γs val_size k (Some (fin_to_nat n))).
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

  Definition compute_con_hash : val :=
    λ: "lk" "hash" "v",
      acquire "lk";;
      let: "output" := "hash" "v" in
      release "lk";;
      "output".

  Definition compute_con_hash_specialized (lk hash : val) : val :=
    λ: "v",
      acquire (lock := con_hash_lock) lk;;
      let: "output" := hash "v" in
      release (lock := con_hash_lock) lk;;
      "output".

  Definition init_con_hash : val :=
    λ: "val_size" "max_val",
      let: "hash" := init_hash_state "val_size" "max_val" in
      let: "lk" := newlock #() in
      compute_con_hash "lk" "hash".

  (** Concurrent hashfun *)
  Definition conhashfun γs val_size f :=
    (∃ γ lk hash max,
        ⌜f = compute_con_hash_specialized lk hash⌝ ∗
        is_lock (L := con_hash_lockG) γ lk (hashfun γs val_size max hash))%I.

  #[global] Instance conhashfun_persistent γs val_size f :
    Persistent (conhashfun γs val_size f).
  Proof. apply _. Qed.

  Lemma wp_init_hash val_size max :
    {{{ True }}}
      init_con_hash #val_size #max
    {{{ (keys : gset nat) (γs : gname * gname) conhash, RET conhash;
        conhashfun γs val_size conhash ∗
        ⌜(∀ i : nat, i < S max ↔ i ∈ keys)⌝ ∗
        ([∗ set] k ∈ keys, hashkey γs val_size k None) }}}.
  Proof.
    iIntros (Φ) "_ HΦ". rewrite /init_con_hash.
    wp_pures.
    wp_apply (wp_init_hash_state with "[//]").
    iIntros (γs tm hash) "(Hfun & % & Hkeys)". wp_pures.
    wp_apply (newlock_spec with "Hfun").
    iIntros (lk γ) "Hlk". wp_pures.
    rewrite /compute_con_hash. wp_pures.
    iModIntro. iApply ("HΦ" $! (dom tm)).
    iSplitL "Hlk".
    { iExists _, _, _, _. iSplit; [done|]. iFrame. }
    iSplit; [done|].
    rewrite big_sepM_dom //.
  Qed.

  Lemma wp_init_hash_alt val_size max :
    {{{ True }}}
      init_con_hash #val_size #max
      {{{ (γs : gname * gname) conhash, RET conhash;
          conhashfun γs val_size conhash ∗
            ([∗ set] k ∈ (set_seq 0 (S max)), hashkey γs val_size k None) }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_apply wp_init_hash; auto.
    iIntros (keys γs conhash) "(?&%Hmax&?)".
    iApply "HΦ"; iFrame.
    iApply (big_sepS_subseteq with "[$]").
    apply elem_of_subseteq.
    intros x Hx.
    apply Hmax.
    apply elem_of_set_seq in Hx.
    lia.
  Qed.

  Lemma wp_conhashfun_prev f (val_size k n : nat) γs :
    {{{ conhashfun γs val_size f ∗ hashkey γs val_size k (Some n) }}}
      f #k
    {{{ RET #n; conhashfun γs val_size f ∗ hashkey γs val_size k (Some n) }}}.
  Proof.
    iIntros (Φ) "[#Hchf Hkey] HΦ".
    iDestruct "Hchf" as (γ lk hash max ->) "Hlk".
    rewrite /compute_con_hash_specialized.
    wp_pures.
    wp_apply (acquire_spec with "Hlk").
    iIntros "[Hlocked Hfun]". wp_pures.
    wp_apply (wp_hashfun_prev with "[$Hfun $Hkey]").
    iIntros "[Hfun Hkey]". wp_pures.
    wp_apply (release_spec with "[$Hlocked $Hlk $Hfun]").
    iIntros "_".
    wp_pures.
    iApply "HΦ".
    iFrame. iModIntro.
    by iFrame "Hlk".
  Qed.

End con_hash_impl.

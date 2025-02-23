From iris.base_logic.lib Require Import ghost_var ghost_map.
From clutch.coneris Require Import coneris.
From clutch.coneris.lib Require Import map lock.
From clutch.coneris.examples.hash Require Import con_hash_interface4.
Set Default Proof Using "Type*".

Class con_hashG Σ `{conerisGS Σ} := {
  con_hash_lock :: lock.lock;
  con_hash_lockG : lockG Σ;
  con_hash_ghost_mapG1 :: ghost_mapG Σ nat (option nat);
  con_hash_ghost_mapG2 :: ghost_mapG Σ nat loc;
  con_hash_ghost_mapG3 :: ghost_mapG Σ nat nat;
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

  Definition hashkey (γs : gname * gname * gname) (k : nat) (v : option nat) : iProp Σ :=
    if v is Some n then
      ∃ α : loc, k ↪[γs.1.2]□ α ∗ k ↪[γs.1.1]□ (Some n)
    else k ↪[γs.1.1] None.

  #[global] Instance haskey_persistent γs k n :
    Persistent (hashkey γs k (Some n)).
  Proof. apply _. Qed.

  Definition hashfunI (γs : gname * gname * gname) (val_size : nat) : iProp Σ :=
    ∃ (m : gmap nat (option nat)),
      ghost_map_auth γs.1.1 1 m ∗
      [∗ map] k ↦ o ∈ m,
        ∃ α : loc, k ↪[γs.1.2]□ α ∗
           if o is Some n then α ↪N (val_size; [n]) ∨ k ↪[γs.2]□ n
           else α ↪N (val_size; []).

  Definition hashfunInv N (γs : gname * gname * gname) (val_size : nat) : iProp Σ :=
    inv N (hashfunI γs val_size).

  (** (Sequential) hash function *)
  Definition hashfun (γs : gname * gname * gname) (val_size max : nat) (f : val) : iProp Σ :=
    ∃ (lvm ltm : loc) (vm : gmap nat nat) (tm : gmap nat loc),
       ⌜(∀ i : nat, i <= max ↔ i ∈ dom tm)⌝ ∗
       ⌜f = compute_hash_specialized #val_size #lvm #ltm ⌝ ∗
       map_list lvm ((λ (n : nat), LitV (LitInt n)) <$> vm) ∗
       map_list ltm ((λ (α : loc), LitV (LitLbl α)) <$> tm) ∗
       ghost_map_auth γs.1.2 1 tm ∗
       ghost_map_auth γs.2   1 vm ∗
       ([∗ map] k ↦ n ∈ vm, k ↪[γs.1.1]□ (Some n)).

  Lemma wp_init_hash_state N val_size max :
    {{{ True }}}
      init_hash_state #val_size #max
    {{{ (γs : gname * gname * gname) (tm : gmap nat loc) hash, RET hash;
        hashfun γs val_size max hash ∗
        hashfunInv N γs val_size ∗
        ⌜(∀ i : nat, i < S max ↔ i ∈ dom tm)⌝ ∗
        ([∗ map] k ↦ v ∈ tm, hashkey γs k None) }}}.
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
    iMod (ghost_map_alloc (gset_to_gmap None (dom tm))) as (γk) "[HkeyA Hkeys]".
    iMod (ghost_map_alloc_empty (V := loc)) as (γt) "HtapesA".
    iMod (ghost_map_insert_persist_big tm with "HtapesA") as "[HtapesA #Htapes']".
    { solve_map_disjoint. }
    iMod (ghost_map_alloc_empty) as (γv) "HvalsA".
    rewrite !gset_to_gmap_dom !big_sepM_fmap.
    iMod (inv_alloc N _ (hashfunI (γk, γt, γv) val_size) with "[$HkeyA Htapes]") as "#HI".
    { iModIntro. iCombine "Htapes' Htapes" as "Htapes".
      rewrite -big_sepM_sep big_sepM_fmap.
      iApply (big_sepM_mono with "Htapes"). iIntros (? α ?) "Hα". by iFrame. }
    iModIntro.
    iApply ("HΦ" $! (_, _) tm).
    iFrame "# % Hkeys".
    rewrite right_id.
    iExists lvm, ltm, ∅, tm.
    rewrite ?fmap_empty. iFrame.
    rewrite big_sepM_empty.
    iSplit; [|done].
    iPureIntro. intros. rewrite -Hdom. split; lia.
  Qed.

  Lemma wp_hashfun_prev N E f (val_size max k n : nat) γs :
    ↑N ⊆ E →
    {{{ hashfunInv N γs val_size ∗ hashfun γs val_size max f ∗ hashkey γs k (Some n) }}}
      f #k @ E
    {{{ RET #n; hashfun γs val_size max f }}}.
  Proof.
    iIntros (? Φ) "(#HI & Hhash & (%α & #Hα & Hkey)) HΦ".
    iDestruct "Hhash" as (lvm ltm vm tm Hdom ->) "(Hvm & Htm & HtmA & HvmA & #HkeysV)".
    rewrite /compute_hash_specialized.
    wp_pures.
    wp_apply (wp_get with "Hvm").
    iIntros (vret) "(Hhash&->)".
    rewrite lookup_fmap.
    destruct (vm !! k) eqn:Hvmk.
    - wp_pures.
      iDestruct (big_sepM_lookup with "HkeysV") as "Hk"; [done|].
      iDestruct (ghost_map_elem_agree with "Hk Hkey") as %[= ->].
      iApply "HΦ". by iFrame "∗ # %".
    - wp_pures.
      wp_apply (wp_get with "Htm").
      iIntros (α') "[Htm ->]".
      rewrite lookup_fmap.
      iDestruct (ghost_map_lookup with "HtmA Hα") as %->.
      wp_pures.
      wp_bind (rand(_) _)%E.
      iInv N as ">(%m & Hm & Hkeys)" "Hclose".
      iDestruct (ghost_map_lookup with "Hm Hkey") as %?.
      iDestruct (big_sepM_lookup_acc with "Hkeys") as "[Hk Hkeys]"; [done|].
      iDestruct "Hk" as (α') "[Hα' Hk]".
      iDestruct (ghost_map_elem_agree with "Hα Hα'") as %<-.
      iMod (ghost_map_insert _ n with "HvmA") as "[HvmA HkV]"; [done|].
      iDestruct "Hk" as "[Htape | HkV']"; last first.
      { by iDestruct (ghost_map_elem_valid_2 with "HkV HkV'") as %[? ?]. }
      wp_apply (wp_rand_tape with "Htape").
      iIntros "[_ %]".
      iMod (ghost_map_elem_persist with "HkV") as "#HkV".
      iMod ("Hclose" with "[Hkeys $Hm]") as "_".
      { iModIntro. iApply "Hkeys". iFrame "#". }
      iModIntro.
      wp_pures.
      wp_apply (wp_set with "Hhash").
      iIntros "Hhash". wp_pures.
      iApply "HΦ".
      iModIntro.
      iExists _, _, (<[k:=n]>vm), tm.
      iFrame. iFrame "%".
      iSplit; [done|].
      rewrite big_sepM_insert //.
      iFrame "# ∗".
      rewrite fmap_insert. iFrame "Hhash".
  Qed.

  (** Presampling of hash key  *)
  Lemma hashkey_presample N E val_size k (bad : gset nat) (ε εI εO: nonnegreal) γs :
    ↑N ⊆ E →
    (∀ x, x ∈ bad → x < S val_size) →
    (εI * size bad + εO * (val_size + 1 - size bad) <= ε * (val_size + 1))%R →
    hashfunInv N γs val_size -∗
    hashkey γs k None -∗
    ↯ ε -∗
    state_update E E (∃ (n : fin (S val_size)),
      ((⌜fin_to_nat n ∉ bad⌝ ∗ ↯ εO) ∨ (⌜fin_to_nat n ∈ bad⌝ ∗ ↯ εI)) ∗
        hashkey γs k (Some (fin_to_nat n))).
  Proof.
    iIntros (HE Hsize Heps) "Hinv Hkey Herr".
    iInv N as ">(%m & Hm & Hkeys)" "Hclose".
    iDestruct (ghost_map_lookup with "Hm Hkey") as %Hkm.
    iDestruct (big_sepM_delete with "Hkeys") as "[Hk Hkeys]"; [done|].
    iDestruct "Hk" as (α) "[#Hk Hα]".
    iMod (state_step_err_set_in_out _ bad _ εI εO
           with "Hα Herr") as (n) "[Herr Htape] /=".
    { apply cond_nonneg. }
    { apply cond_nonneg. }
    { done. }
    { done. }
    iMod (ghost_map_update (Some (fin_to_nat n)) with "Hm Hkey") as "[Hm Hkey]".
    iMod (ghost_map_elem_persist with "Hkey") as "#Hkey".
    iMod ("Hclose" with "[Hkeys Htape $Hm]") as "_".
    { iModIntro. rewrite big_sepM_insert_delete. by iFrame. }
    iModIntro. eauto.
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

  (** Concurrent hashfun, hiding as many details as possible *)
  Definition conhashfun γs val_size f :=
    (∃ γ lk hash max N,
        ⌜f = compute_con_hash_specialized lk hash⌝ ∗
        hashfunInv N γs val_size ∗
        is_lock (L := con_hash_lockG) γ lk (hashfun γs val_size max hash))%I.

  #[global] Instance conhashfun_persistent γs val_size f :
    Persistent (conhashfun γs val_size f).
  Proof. apply _. Qed.

  Lemma wp_init_hash val_size max :
    {{{ True }}}
      init_con_hash #val_size #max
    {{{ (keys : gset nat) γs conhash, RET conhash;
        conhashfun γs val_size conhash ∗
        ⌜(∀ i : nat, i < S max ↔ i ∈ keys)⌝ ∗
        ([∗ set] k ∈ keys, hashkey γs k None) }}}.
  Proof.
    iIntros (Φ) "_ HΦ". rewrite /init_con_hash.
    wp_pures.
    wp_apply (wp_init_hash_state nroot with "[//]").
    iIntros (γs tm hash) "(Hfun & #HI & % & Hkeys)".
    wp_pures.
    wp_apply (newlock_spec with "Hfun").
    iIntros (lk γ) "Hlk". wp_pures.
    rewrite /compute_con_hash. wp_pures.
    iModIntro. iApply ("HΦ" $! (dom tm)).
    iSplitL "Hlk".
    { iExists _, _, _, _, _. iSplit; [done|]. by iFrame. }
    iSplit; [done|].
    rewrite big_sepM_dom //.
  Qed.

  Lemma wp_init_hash_alt val_size max :
    {{{ True }}}
      init_con_hash #val_size #max
    {{{ γs conhash, RET conhash;
        conhashfun γs val_size conhash ∗
        ([∗ set] k ∈ (set_seq 0 (S max)), hashkey γs k None) }}}.
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

  Lemma wp_conhashfun_prev f (k n : nat) γs val_size :
    {{{ conhashfun γs val_size f ∗ hashkey γs k (Some n) }}}
      f #k
    {{{ RET #n; conhashfun γs val_size f }}}.
  Proof.
    iIntros (Φ) "[#Hchf Hkey] HΦ".
    iDestruct "Hchf" as (γ lk hash max N ->) "[#HI Hlk]".
    rewrite /compute_con_hash_specialized.
    wp_pures.
    wp_apply (acquire_spec with "Hlk").
    iIntros "[Hlocked Hfun]". wp_pures.
    wp_apply (wp_hashfun_prev with "[$Hfun $Hkey $HI]"); [done|].
    iIntros "Hfun". wp_pures.
    wp_apply (release_spec with "[$Hlocked $Hlk $Hfun]").
    iIntros "_".
    wp_pures.
    iApply "HΦ".
    iFrame. iModIntro.
    by iFrame "Hlk HI".
  Qed.

End con_hash_impl.

Section con_hash_interface_impl.
  Context `{!conerisGS Σ, !con_hashG Σ}.

   Program Definition con_hash4_implements_interface4 : con_hash4 Σ :=
     Con_Hash4 _ _ init_con_hash conhashfun hashkey _ _ _ _ wp_init_hash_alt wp_conhashfun_prev.
   Next Obligation.
     iIntros (??????????) "#Hinv Hk Herr".
     iDestruct "Hinv" as (??????) "[HI ?]".
     by iApply (hashkey_presample  with "HI Hk Herr").
   Qed.

End con_hash_interface_impl.

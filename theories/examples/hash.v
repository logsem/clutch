From clutch Require Export clutch lib.map lib.flip.
Set Default Proof Using "Type*".

Module simple_bit_hash.

  Context `{!clutchRGS Σ}.

  (* A simple bit hash map. *)

  (* A hash function's internal state is a map from previously queried keys to their hash value *)
  Definition init_hash_state : val := init_map.

  (* To hash a value v, we check whether it is in the map (i.e. it has been previously hashed).
     If it has we return the saved hash value, otherwise we flip a bit and save it in the map *)
  Definition compute_hash_specialized hm : val :=
    λ: "v",
      match: get hm "v" with
      | SOME "b" => "b"
      | NONE =>
          let: "b" := flip in
          set hm "v" "b";;
          "b"
      end.
  Definition compute_hash : val :=
    λ: "hm" "v",
      match: get "hm" "v" with
      | SOME "b" => "b"
      | NONE =>
          let: "b" := flip in
          set "hm" "v" "b";;
          "b"
      end.

  (* init_hash returns a hash as a function, basically wrapping the internal state
     in the returned function *)
  Definition init_hash : val :=
    λ: "_",
      let: "hm" := init_hash_state #() in
      compute_hash "hm".

  Definition hashfun f m : iProp Σ :=
    ∃ (hm : loc), ⌜ f = compute_hash_specialized #hm ⌝ ∗ map_list hm ((λ b, LitV (LitBool b)) <$> m).

  Definition shashfun f m : iProp Σ :=
    ∃ (hm : loc), ⌜ f = compute_hash_specialized #hm ⌝ ∗ map_slist hm ((λ b, LitV (LitBool b)) <$> m).

  #[global] Instance timeless_hashfun f m :
    Timeless (hashfun f m).
  Proof. apply _. Qed.

  #[global] Instance timeless_shashfun f m :
    Timeless (shashfun f m).
  Proof. apply _. Qed.

  Lemma wp_init_hash E :
    {{{ True }}}
      init_hash #() @ E
    {{{ f, RET f; hashfun f ∅ }}}.
  Proof.
    rewrite /init_hash.
    iIntros (Φ) "_ HΦ".
    wp_pures. rewrite /init_hash_state.
    wp_apply (wp_init_map with "[//]").
    iIntros (?) "Hm". wp_pures.
    rewrite /compute_hash. wp_pures.
    iApply "HΦ". iExists _. rewrite fmap_empty. iFrame. eauto.
  Qed.

  Lemma spec_init_hash E K :
    ↑specN ⊆ E →
    refines_right K (init_hash #()) ={E}=∗ ∃ f, refines_right K (of_val f) ∗ shashfun f ∅.
  Proof.
    rewrite /init_hash.
    iIntros (?) "Hspec".
    rewrite /init_hash_state.
    tp_pures.
    tp_bind (init_map _).
    iEval (rewrite refines_right_bind) in "Hspec".
    iMod (spec_init_map with "[$]") as (l) "(Hspec&Hm)"; auto.
    iEval (rewrite -refines_right_bind /=) in "Hspec".
    rewrite /compute_hash.
    tp_pures.
    iExists _. iDestruct "Hspec" as "(#$&$)".
    iModIntro. iExists _. iSplit; first done. rewrite fmap_empty. iFrame.
  Qed.

  Lemma wp_hashfun_prev E f m (n : nat) (b : bool) :
    m !! n = Some b →
    {{{ hashfun f m }}}
      f #n @ E
    {{{ RET #b; hashfun f m }}}.
  Proof.
    iIntros (Hlookup Φ) "Hhash HΦ".
    iDestruct "Hhash" as (hm ->) "H".
    rewrite /compute_hash_specialized.
    wp_pures.
    wp_apply (wp_get with "[$]").
    iIntros (vret) "(Hhash&->)".
    rewrite lookup_fmap Hlookup /=. wp_pures. iModIntro. iApply "HΦ".
    iExists _. eauto.
  Qed.

  Lemma spec_hashfun_prev E K f m (n : nat) (b: bool) :
    m !! n = Some b →
    ↑specN ⊆ E →
    shashfun f m -∗
    refines_right K (f #n) ={E}=∗ refines_right K (of_val #b) ∗ shashfun f m.
  Proof.
    iIntros (Hlookup ?) "Hhash HK".
    iDestruct "Hhash" as (hm ->) "H".
    rewrite /compute_hash_specialized.
    tp_pures.
    tp_bind (get _ _).
    iEval (rewrite refines_right_bind) in "HK".
    iMod (spec_get with "[$] [$]") as "(HK&Hm)"; first done.
    iEval (rewrite -refines_right_bind /=) in "HK".
    rewrite lookup_fmap Hlookup /=.
    tp_pures. iFrame. iModIntro. iExists _. eauto.
  Qed.

  Lemma wp_hashfun_couple_eq E K (f : val) (m : gmap nat bool) (sf: val) (sm : gmap nat bool) (n : nat) :
    ↑specN ⊆ E →
    m !! n = None →
    sm !! n = None →
    {{{ refines_right K (sf #n) ∗ hashfun f m ∗ shashfun sf sm }}}
      f #n @ E
    {{{ (b: bool), RET #b;
        refines_right K (of_val #b) ∗ hashfun f (<[ n := b ]>m) ∗ shashfun sf (<[n := b]>sm) }}}.
  Proof.
    iIntros (Hspec Hnonem Hnonesm Φ) "(HK&Hhash&Hshash) HΦ".
    iDestruct "Hhash" as (hm ->) "Hm".
    iDestruct "Hshash" as (hsm ->) "Hsm".
    rewrite /compute_hash_specialized.
    wp_pures.
    tp_pures.

    (* spec get *)
    tp_bind (get _ _).
    iEval (rewrite refines_right_bind) in "HK".
    iMod (spec_get with "[$] [$]") as "(HK&Hsm)"; first done.
    iEval (rewrite -refines_right_bind /=) in "HK".
    rewrite lookup_fmap Hnonesm /=.
    tp_pures.

    (* impl get *)
    wp_apply (wp_get with "[$]").
    iIntros (res) "(Hm&->)".
    rewrite lookup_fmap Hnonem /=.
    wp_pures.

    (* couple -- FIXME: breaking abstraction *)
    tp_bind flip.
    iEval (rewrite refines_right_bind) in "HK".
    wp_apply (wp_couple_flip_flip Datatypes.id); [done|]. 
    iDestruct "HK" as "(#Hspec&HK)".
    iFrame "Hspec". iFrame "HK".
    iIntros "!>" (b) "HK".
    iEval (rewrite -refines_right_bind /=) in "HK".
    tp_pures.
    do 2 wp_pures.

    tp_bind (set _ _ _).
    iEval (rewrite refines_right_bind) in "HK".
    iMod (spec_set with "[$] [$]") as "(HK&Hsm)"; first done.
    iEval (rewrite -refines_right_bind /=) in "HK".
    tp_pures.

    wp_apply (wp_set with "[$]").
    iIntros "Hm". wp_pures. iApply "HΦ".
    iFrame. iModIntro.
    iSplitL "Hm".
    { iExists _. iSplit; first auto. rewrite fmap_insert //. }
    { iExists _. iSplit; first auto. rewrite fmap_insert //. }
  Qed.


  (* But we cannot sample ahead, so for example one cannot prove that if f is a hashmap
    (f 1; f 2) refines (f 2; f1)  *)

End simple_bit_hash.

Section tape_bit_hash.

  Context `{!clutchRGS Σ}.

  (* A more complicated bit hash map.

     To support pre-sampling as a ghost step, we allocate tapes to store pre sampled hash values.

     However, we want to support hashing in different orders between
     the left and right sides of the refinement, so we need separate
     tapes for each possible hash value. To support that, we assume
     the domain is bounded.

   *)

  (* A hash function's internal state is a pair of maps:
     - the first map stores hash values for previously queried keys
     - the second map stores tapes for each potential key in the domain *)

  Definition alloc_tapes : val :=
    (rec: "alloc_tapes" "tm" "n" :=
       if: ("n" - #1) < #0 then
         #()
       else
        let: "α" := allocB in
         set "tm" ("n" - #1) "α";;
        "alloc_tapes" "tm" ("n" - #1)).

  Definition init_hash_state : val :=
   λ: "max_val",
      let: "val_map" := init_map #() in
      let: "tape_map" := init_map #() in
      alloc_tapes "tape_map" ("max_val" + #1);;
      ("val_map", "tape_map").

  (* To hash a value v, we check whether it is in the map (i.e. it has been previously hashed).
     If it has we return the saved hash value, otherwise we look up the tape for this value
     flip a bit with that tape, and save it in the map *)
  Definition compute_hash_specialized vm tm : val :=
    λ: "v",
      match: get vm "v" with
      | SOME "b" => "b"
      | NONE =>
          match: get tm "v" with
            | SOME "α" =>
                let: "b" := flipL "α" in
                set vm "v" "b";;
                "b"
            | NONE => #false
            end
      end.

  Definition compute_hash : val :=
    λ: "vm" "tm" "v",
      match: get "vm" "v" with
      | SOME "b" => "b"
      | NONE =>
          match: get "tm" "v" with
            | SOME "α" =>
                let: "b" := flipL "α" in
                set "vm" "v" "b";;
                "b"
            | NONE => #false
            end
      end.

  (* init_hash returns a hash as a function, basically wrapping the internal state
     in the returned function *)
  Definition init_hash : val :=
    λ: "max_val",
      let: "ms" := init_hash_state "max_val" in
      compute_hash (Fst "ms") (Snd "ms").

  (* for each k <= max, it's in tm, and either:
     (1) it's in vm and has value given by m,
     (2) the tape given by tm has a value b and m !! k = Some b
     (3) the tape given by tm is empty and m !! k = None
   *)
  Definition hashfun (max : nat) f (m : gmap nat bool) : iProp Σ :=
    ∃ (lvm ltm: loc) (vm: gmap nat bool) (tm: gmap nat loc),
       ⌜ (∀ i : nat, i <= max ↔ i ∈ dom tm) ⌝ ∗
       ⌜ dom m ⊆ dom tm ∧ dom vm ⊆ dom tm ⌝ ∗
       ⌜ f = compute_hash_specialized #lvm #ltm ⌝ ∗
       map_list lvm ((λ v, LitV (LitBool v)) <$> vm) ∗
       map_list ltm ((λ v, LitV (LitLbl v)) <$> tm) ∗
       ([∗ map] i ↦ α ∈ tm,
          (∃ b : bool, ⌜ m !! i = Some b ⌝ ∗ ⌜ vm !! i = Some b ⌝) ∨
          (∃ b : bool, ⌜ m !! i = Some b ⌝ ∗ ⌜ vm !! i = None ⌝ ∗ α ↪B (b :: nil) ) ∨
          (⌜ m !! i = None ⌝ ∗ ⌜ vm !! i = None ⌝ ∗ α ↪B nil)).

  Definition shashfun (max : nat) f (m : gmap nat bool) : iProp Σ :=
    ∃ (lvm ltm: loc) (vm: gmap nat bool) (tm: gmap nat loc),
       ⌜ (∀ i : nat, i <= max ↔ i ∈ dom tm) ⌝ ∗
       ⌜ dom m ⊆ dom tm ∧ dom vm ⊆ dom tm ⌝ ∗
       ⌜ f = compute_hash_specialized #lvm #ltm ⌝ ∗
       map_slist lvm ((λ v, LitV (LitBool v)) <$> vm) ∗
       map_slist ltm ((λ v, LitV (LitLbl v)) <$> tm) ∗
       ([∗ map] i ↦ α ∈ tm,
          (∃ b : bool, ⌜ m !! i = Some b ⌝ ∗ ⌜ vm !! i = Some b ⌝) ∨
          (∃ b : bool, ⌜ m !! i = Some b ⌝ ∗ ⌜ vm !! i = None ⌝ ∗ α ↪ₛB (b :: nil) ) ∨
          (⌜ m !! i = None ⌝ ∗ ⌜ vm !! i = None ⌝ ∗ α ↪ₛB nil)).

  #[global] Instance timeless_hashfun n f m :
    Timeless (hashfun n f m).
  Proof. apply _. Qed.

  #[global] Instance timeless_shashfun n f m :
    Timeless (shashfun n f m).
  Proof.
    rewrite /shashfun.
    (* Strange that just doing apply _ here is slow, but after exist_timeless it's fast *)
    repeat (apply bi.exist_timeless => ?).
    apply _.
  Qed.

  Lemma wp_alloc_tapes E ltm max :
    {{{ map_list ltm ∅ }}}
      alloc_tapes #ltm #max @ E
    {{{ RET #(); ∃ tm,
            map_list ltm ((λ v, LitV (LitLbl v)) <$> tm) ∗
            ⌜ (∀ i : nat, i < max ↔ i ∈ dom tm) ⌝ ∗
            ([∗ map] i ↦ α ∈ tm, α ↪B nil) }}}.
  Proof.
    iIntros (Φ) "Htm HΦ".
    rewrite /alloc_tapes.
    remember max as k eqn:Heqk.
    iEval (setoid_rewrite Heqk) in "HΦ".
    iAssert (∃ tm, ⌜ (∀ i : nat, (k <= i < max)%nat ↔ i ∈ dom tm) ⌝ ∗
                   map_list ltm ((λ v, LitV (LitLbl v)) <$> tm) ∗
                   ([∗ map] i ↦ α ∈ tm, α ↪B nil))%I with "[Htm]" as "Htm".
    { iExists ∅. rewrite fmap_empty. iFrame. iSplit.
      { iPureIntro. subst. intros; split; try lia. rewrite dom_empty_L. inversion 1. }
      { rewrite big_sepM_empty. auto. } }
    assert (Hlek: k <= max) by lia.
    clear Heqk.
    iInduction k as [| k] "IH" forall (Hlek).
    - wp_pures. iApply "HΦ". iModIntro. iDestruct "Htm" as (tm Hdom) "(Hm&Htapes)".
      iExists tm. iFrame. iPureIntro. split.
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
          apply Hdom in Hdom'. lia.
      }
      iApply (big_sepM_insert).
      { apply not_elem_of_dom_1. intros Hbad.
        assert (S k <= k).
        { apply Hdom; auto. }
        lia.
      }
      iFrame.
  Qed.

  Lemma spec_alloc_tapes E K ltm (max : nat) :
    ↑specN ⊆ E →
    map_slist ltm ∅ -∗
    refines_right K (alloc_tapes #ltm #max) ={E}=∗
    refines_right K (#()) ∗ ∃ tm, map_slist ltm ((λ v, LitV (LitLbl v)) <$> tm) ∗
                                    ⌜ (∀ i : nat, i < max ↔ i ∈ dom tm) ⌝ ∗
                                    ([∗ map] i ↦ α ∈ tm, α ↪ₛB nil).
  Proof.
    iIntros (Φ) "Htm HK".
    rewrite /alloc_tapes.
    remember max as k eqn:Heqk.
    iAssert (∃ tm, ⌜ (∀ i : nat, (k <= i < max)%nat ↔ i ∈ dom tm) ⌝ ∗
                   map_slist ltm ((λ v, LitV (LitLbl v)) <$> tm) ∗
                   ([∗ map] i ↦ α ∈ tm, α ↪ₛB nil))%I with "[Htm]" as "Htm".
    { iExists ∅. rewrite fmap_empty. iFrame. iSplit.
      { iPureIntro. subst. intros; split; try lia. rewrite dom_empty_L. inversion 1. }
      { rewrite big_sepM_empty. auto. } }
    iEval (rewrite Heqk).
    assert (Hlek: k <= max) by lia.
    clear Heqk.
    iInduction k as [| k] "IH" forall (Hlek).
    - tp_pures. iFrame. iModIntro. iDestruct "Htm" as (tm Hdom) "(Hm&Htapes)".
      iExists tm. iFrame. iPureIntro. split.
      { intros. apply Hdom. lia. }
      { intros. apply Hdom. auto. }
    - iSpecialize ("IH" with "[]").
      { iPureIntro; lia. }
      tp_pures.
      case_bool_decide; first by lia.
      tp_pures.
      tp_bind (allocB).
      rewrite refines_right_bind.
      iMod (refines_right_allocB_tape with "HK") as (α) "(HK&Hα)"; first done.
      rewrite -refines_right_bind /=.

      tp_pures.
      tp_bind (set _ _ _).
      rewrite refines_right_bind.
      iDestruct "Htm" as (tm Hdom) "(Htm&Htapes)".
      replace (Z.of_nat (S k) - 1)%Z with (Z.of_nat k)%Z by lia.
      iMod (spec_set with "[$] HK") as "(HK&Htm)"; first done.
      rewrite -refines_right_bind /=.
      tp_pure.
      tp_pure.
      tp_pure.
      replace (Z.of_nat (S k) - 1)%Z with (Z.of_nat k)%Z by lia.
      iApply ("IH" with "[$]").
      iExists (<[k := α]>tm). rewrite fmap_insert. iFrame.
      iSplit.
      { iPureIntro. intros i. split.
        * intros Hle. set_unfold.
          destruct (decide (i = k)); auto.
          right. apply Hdom; lia.
        * set_unfold. intros [?|Hdom']; try lia.
          apply Hdom in Hdom'. lia.
      }
      iApply (big_sepM_insert).
      { apply not_elem_of_dom_1. intros Hbad.
        assert (S k <= k).
        { apply Hdom; auto. }
        lia.
      }
      iFrame.
  Qed.

  Lemma wp_init_hash_state max E :
    {{{ True }}}
      init_hash_state #max @ E
    {{{ (lvm ltm : loc), RET (#lvm, #ltm); hashfun max (compute_hash_specialized #lvm #ltm) ∅ }}}.
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
    wp_apply (wp_alloc_tapes with "[$]").
    iIntros "Htm".
    wp_pures. iModIntro.
    iApply "HΦ". iDestruct "Htm" as (tm) "(Htm&%Hdom&Htapes)".
    iExists lvm, ltm, ∅, tm.
    rewrite ?fmap_empty. iFrame. iSplit.
    { iPureIntro. intros. rewrite -Hdom. lia. }
    iSplit; first eauto.
    iSplit; first eauto.
    iApply (big_sepM_mono with "Htapes").
    { iIntros (k α Hlookup) "Htape". iRight. iRight. rewrite ?lookup_empty; iFrame; auto. }
  Qed.

  Lemma wp_init_hash max E :
    {{{ True }}}
      init_hash #max @ E
    {{{ f, RET f; hashfun max f ∅ }}}.
  Proof.
    rewrite /init_hash.
    iIntros (Φ) "_ HΦ".
    wp_pures. wp_apply (wp_init_hash_state with "[//]").
    iIntros (lvm ltm) "H". wp_pures.
    rewrite /compute_hash. wp_pures.
    iApply "HΦ".
    eauto.
  Qed.

  Lemma spec_init_hash (max : nat) E K :
    ↑specN ⊆ E →
    refines_right K (init_hash #max) ={E}=∗ ∃ f, refines_right K (of_val f) ∗ shashfun max f ∅.
  Proof.
    iIntros (?) "H".
    rewrite /init_hash.
    tp_pures.
    rewrite /init_hash_state.
    tp_pures.
    tp_bind (init_map #()).
    rewrite refines_right_bind.
    iMod (spec_init_map with "[$]") as (lvm) "(HK&Hvm)"; first done.
    iEval (rewrite -refines_right_bind /=) in "HK".

    tp_pures.
    tp_bind (init_map #()).
    rewrite refines_right_bind.
    iMod (spec_init_map with "[$]") as (ltm) "(HK&Htm)"; first done.
    iEval (rewrite -refines_right_bind /=) in "HK".
    tp_pures.

    tp_bind (alloc_tapes _ _).
    rewrite refines_right_bind.
    replace (Z.of_nat max + 1)%Z with (Z.of_nat (S max))%Z by lia.
    iMod (spec_alloc_tapes with "[$] [$]") as "(HK&Htm)"; first done.
    iDestruct "Htm" as (tm) "(Htm&%Hdom&Htapes)".
    iEval (rewrite -refines_right_bind /=) in "HK".
    tp_pures.
    rewrite /compute_hash. tp_pures.
    iModIntro. iExists _.
    iDestruct "HK" as "(#?&?)".
    iFrame "# ∗".
    iExists lvm, ltm, ∅, tm.
    rewrite ?fmap_empty. iFrame. iSplit.
    { iPureIntro. intros. rewrite -Hdom; lia. }
    iSplit; first eauto.
    iSplit; first eauto.
    iApply (big_sepM_mono with "Htapes").
    { iIntros (k α Hlookup) "Htape". iRight. iRight. rewrite ?lookup_empty; iFrame; auto. }
  Qed.


  Lemma wp_hashfun_prev E f m (max n : nat) (b : bool) :
    m !! n = Some b →
    {{{ hashfun max f m }}}
      f #n @ E
    {{{ RET #b; hashfun max f m }}}.
  Proof.
    iIntros (Hlookup Φ) "Hhash HΦ".
    iDestruct "Hhash" as (lvm ltm vm tm Hdom1 Hdom2 ->) "(Hvm&Htm&Htapes)".
    rewrite /compute_hash_specialized.
    wp_pures.
    wp_apply (wp_get with "Hvm").
    iIntros (vret) "(Hhash&->)".
    rewrite lookup_fmap.
    assert (is_Some (tm !! n)) as (α&Hα).
    { apply elem_of_dom.
      destruct Hdom2 as (Hdom_mtm&Hdom_vmtm).
      apply Hdom_mtm. apply elem_of_dom. auto. }
    iDestruct (big_sepM_delete with "Htapes") as "(Hn&Htapes)"; first eauto.
    iDestruct "Hn" as "[#Hvm|Hnvm]".
    - iDestruct "Hvm" as (b') "(%Heq1&%Heq2)".
      assert (b = b') by congruence; subst.
      rewrite Heq2. wp_pures.
      iApply "HΦ".
      iModIntro.
      iExists _, _, vm, tm. iFrame.
      iSplit; first done.
      iSplit; first done.
      iSplit; first done.
      iApply big_sepM_delete; first eauto.
      iFrame "Htapes".
      iLeft. auto.
    - iDestruct "Hnvm" as "[Hnvm|Hbad]"; last first.
      { iDestruct "Hbad" as (??) "_". congruence. }
      iDestruct "Hnvm" as (b') "(%Heq1&%Heq2&Htape)".
      assert (b = b') by congruence; subst.
      rewrite Heq2. wp_pures.
      wp_apply (wp_get with "Htm").
      iIntros (α') "Hα'".
      rewrite lookup_fmap Hα.
      iDestruct "Hα'" as "(Hα&->)".
      wp_pures.
      wp_apply (wp_flipL with "Htape").
      iIntros "Htape". wp_pures.
      wp_apply (wp_set with "Hhash").
      iIntros "Hhash". wp_pures. iApply "HΦ".
      iModIntro. iExists _, _, (<[n:=b']>vm), tm.
      iFrame.
      iSplit; first done.
      iSplit.
      { iPureIntro; split; intuition auto. rewrite dom_insert_L. set_unfold; intros ? [?|?]; auto.
        subst. apply elem_of_dom; eauto. }
      iSplit; first done.
      rewrite fmap_insert; iFrame.
      iApply big_sepM_delete; first eauto.
      iSplitL "Htape".
      { iLeft. iExists _. iSplit; eauto. rewrite lookup_insert //. }
      iApply (big_sepM_mono with "Htapes").
      { iIntros (k ? Hlookup').
        assert (n ≠ k).
        { apply lookup_delete_Some in Hlookup'. intuition auto. }
        rewrite ?lookup_insert_ne //.
      }
  Qed.

  Lemma wp_hashfun_out_of_range E f m (max : nat) (z : Z) :
    (z < 0 ∨ max < z)%Z →
    {{{ hashfun max f m }}}
      f #z @ E
    {{{ RET #false; hashfun max f m }}}.
  Proof.
    iIntros (Hrange Φ) "Hhash HΦ".
    iDestruct "Hhash" as (lvm ltm vm tm Hdom1 Hdom2 ->) "(Hvm&Htm&Htapes)".
    rewrite /compute_hash_specialized.
    wp_pures.
    wp_apply (wp_get_Z with "Hvm").
    iIntros (vret) "(Hhash&->)".
    rewrite lookup_fmap.
    case_bool_decide.
    { wp_pures. wp_apply (wp_get_Z with "Htm"). iIntros (?).
      rewrite bool_decide_true //. iIntros "(Htm&->)". wp_pures.
      iApply "HΦ". iModIntro. iExists _, _, _, _. iFrame. auto. }
    assert (tm !! Z.to_nat z = None) as Htm_none.
    { apply not_elem_of_dom_1. rewrite -Hdom1. lia. }
    assert (vm !! Z.to_nat z = None) as ->.
    { apply not_elem_of_dom_1. apply not_elem_of_dom_2 in Htm_none. set_solver. }
    wp_pures.
    wp_apply (wp_get_Z with "Htm"). iIntros (?).
    rewrite bool_decide_false //. iIntros "(Htm&->)". rewrite lookup_fmap Htm_none. wp_pures.
    iApply "HΦ". iModIntro. iExists _, _, _, _. iFrame. auto.
  Qed.

  Lemma spec_hashfun_prev E K f m max (n : nat) (b: bool) :
    m !! n = Some b →
    ↑specN ⊆ E →
    shashfun max f m -∗
    refines_right K (f #n) ={E}=∗ refines_right K (of_val #b) ∗ shashfun max f m.
  Proof.
    iIntros (Hlookup Φ) "Hhash HΦ".
    iDestruct "Hhash" as (lvm ltm vm tm Hdom1 Hdom2 ->) "(Hvm&Htm&Htapes)".
    rewrite /compute_hash_specialized.
    tp_pures.

    tp_bind (get _ _).
    rewrite refines_right_bind.
    iMod (spec_get with "Hvm [$]") as "(HK&Hvm_all)"; first done.
    iEval (rewrite -refines_right_bind /=) in "HK".
    rewrite lookup_fmap.
    assert (is_Some (tm !! n)) as (α&Hα).
    { apply elem_of_dom.
      destruct Hdom2 as (Hdom_mtm&Hdom_vmtm).
      apply Hdom_mtm. apply elem_of_dom. auto. }
    iDestruct (big_sepM_delete with "Htapes") as "(Hn&Htapes)"; first eauto.
    iDestruct "Hn" as "[#Hvm|Hnvm]".
    - iDestruct "Hvm" as (b') "(%Heq1&%Heq2)".
      assert (b = b') by congruence; subst.
      rewrite Heq2. tp_pures.
      iModIntro.
      iFrame.
      iExists _, _, vm, tm. iFrame.
      iSplit; first done.
      iSplit; first done.
      iSplit; first done.
      iApply big_sepM_delete; first eauto.
      iFrame "Htapes".
      iLeft. auto.
    - iDestruct "Hnvm" as "[Hnvm|Hbad]"; last first.
      { iDestruct "Hbad" as (??) "_". congruence. }
      iDestruct "Hnvm" as (b') "(%Heq1&%Heq2&Htape)".
      assert (b = b') by congruence; subst.
      rewrite Heq2. tp_pures.
      tp_bind (get _ _).
      rewrite refines_right_bind.
      iMod (spec_get with "Htm [$]") as "(HK&Htm)"; first done.
      rewrite -refines_right_bind/=.
      rewrite lookup_fmap Hα.
      tp_pures.

      tp_bind (flipL _)%E.
      rewrite refines_right_bind.
      iMod (refines_right_flipL with "[$] [$]") as "(HK&Hα)"; first done.
      rewrite -refines_right_bind/=.
      tp_pures.

      tp_bind (set _ _ _).
      rewrite refines_right_bind.
      iMod (spec_set with "Hvm_all HK") as "(HK&Hvm_all)"; first done.
      rewrite -refines_right_bind/=.
      tp_pures.

      iFrame.
      iModIntro. iExists _, _, (<[n:=b']>vm), tm.
      iFrame.
      iSplit; first done.
      iSplit.
      { iPureIntro; split; intuition auto. rewrite dom_insert_L. set_unfold; intros ? [?|?]; auto.
        subst. apply elem_of_dom; eauto. }
      iSplit; first done.
      rewrite fmap_insert; iFrame.
      iApply big_sepM_delete; first eauto.
      iSplitL "Hα".
      { iLeft. iExists _. iSplit; eauto. rewrite lookup_insert //. }
      iApply (big_sepM_mono with "Htapes").
      { iIntros (k ? Hlookup').
        assert (n ≠ k).
        { apply lookup_delete_Some in Hlookup'. intuition auto. }
        rewrite ?lookup_insert_ne //.
      }
  Qed.

  Lemma spec_hashfun_out_of_range E K f m (max : nat) (z : Z) :
    (z < 0 ∨ max < z)%Z →
    ↑specN ⊆ E →
    shashfun max f m -∗
    refines_right K (f #z) ={E}=∗ refines_right K (of_val #false) ∗ shashfun max f m.
  Proof.
    iIntros (Hrange Φ) "Hhash HΦ".
    iDestruct "Hhash" as (lvm ltm vm tm Hdom1 Hdom2 ->) "(Hvm&Htm&Htapes)".
    rewrite /compute_hash_specialized.
    tp_pures.
    tp_bind (get _ _).
    rewrite refines_right_bind.
    iMod (spec_get_Z with "Hvm [$]") as "(HK&Hvm_all)"; first done.
    iEval (rewrite -refines_right_bind /=) in "HK".
    rewrite lookup_fmap.
    case_bool_decide.
    { tp_pures.
      tp_bind (get _ _).
      rewrite refines_right_bind.
      iMod (spec_get_Z with "Htm HK") as "(HK&Htm)"; first done.
      rewrite bool_decide_true //.
      rewrite -refines_right_bind /=.
      tp_pures. iFrame. iModIntro. iExists _, _, _, _. iFrame. auto. }
    assert (tm !! Z.to_nat z = None) as Htm_none.
    { apply not_elem_of_dom_1. rewrite -Hdom1. lia. }
    assert (vm !! Z.to_nat z = None) as ->.
    { apply not_elem_of_dom_1. apply not_elem_of_dom_2 in Htm_none. set_solver. }
    tp_pures.
    tp_bind (get _ _).
    rewrite refines_right_bind.
    iMod (spec_get_Z with "Htm HK") as "(HK&Htm)"; first done.
    rewrite bool_decide_false //. rewrite lookup_fmap Htm_none.
    rewrite -refines_right_bind /=.
    tp_pures. iFrame.
    iModIntro. iExists _, _, _, _. iFrame. auto.
  Qed.

  Definition impl_couplable (P : bool → iProp Σ) : iProp Σ :=
    (∃ α bs, α ↪B bs ∗ (∀ b, α ↪B (bs ++ [b]) -∗ P b)).
  Definition spec_couplable (P : bool → iProp Σ) : iProp Σ :=
    (∃ α bs, α ↪ₛB bs ∗ (∀ b, α ↪ₛB (bs ++ [b]) -∗ P b)).

  Lemma hashfun_couplable k max f m :
    k ≤ max →
    m !! k = None →
    hashfun max f m -∗ impl_couplable (λ b, hashfun max f (<[k:=b]>m)).
  Proof.
    iIntros (Hmax Hlookup) "Hhashfun".
    iDestruct "Hhashfun" as (lvm ltm vm tm Hdom1 Hdom2 ->) "(Hvm&Htm&Htapes)".
    (* Get the tape id for k *)
    assert (is_Some (tm !! k)) as (α&Hα).
    { apply elem_of_dom. apply Hdom1. lia. }

    iDestruct (big_sepM_delete with "Htapes") as "(Hk&Htapes)"; first eauto.
    iDestruct "Hk" as "[Hbad|[Hbad|Hk]]".
    { iExFalso. iDestruct "Hbad" as (?) "(%Hbadlook&_)". congruence. }
    { iExFalso. iDestruct "Hbad" as (?) "(%Hbadlook&_)". congruence. }
    iDestruct "Hk" as "(%Hnone1&%Hnone2&Hα)".

    rewrite /impl_couplable. iExists α, [].
    iFrame. iIntros (b) "Hα".
    iExists _, _, _, _. iFrame.
    iSplit; first done.
    iSplit.
    { iPureIntro; split; intuition auto. rewrite dom_insert_L.
      set_solver. }
    iSplit; first done.
    iApply big_sepM_delete; first eauto.
    iSplitL "Hα".
    { iRight. iLeft. iExists b. iFrame. iPureIntro; split; auto. rewrite lookup_insert //. }
    iApply (big_sepM_mono with "Htapes").
    iIntros (k' x' Hdel) "H".
    assert (k ≠ k').
    { apply lookup_delete_Some in Hdel. intuition auto. }
    rewrite ?lookup_insert_ne //.
  Qed.

  Lemma shashfun_couplable k max f m :
    k ≤ max →
    m !! k = None →
    shashfun max f m -∗ spec_couplable (λ b, shashfun max f (<[k:=b]>m)).
  Proof.
    iIntros (Hmax Hlookup) "Hhashfun".
    iDestruct "Hhashfun" as (lvm ltm vm tm Hdom1 Hdom2 ->) "(Hvm&Htm&Htapes)".
    (* Get the tape id for k *)
    assert (is_Some (tm !! k)) as (α&Hα).
    { apply elem_of_dom. apply Hdom1. lia. }

    iDestruct (big_sepM_delete with "Htapes") as "(Hk&Htapes)"; first eauto.
    iDestruct "Hk" as "[Hbad|[Hbad|Hk]]".
    { iExFalso. iDestruct "Hbad" as (?) "(%Hbadlook&_)". congruence. }
    { iExFalso. iDestruct "Hbad" as (?) "(%Hbadlook&_)". congruence. }
    iDestruct "Hk" as "(%Hnone1&%Hnone2&Hα)".

    rewrite /spec_couplable. iExists α, [].
    iFrame. iIntros (b) "Hα".
    iExists _, _, _, _. iFrame.
    iSplit; first done.
    iSplit.
    { iPureIntro; split; intuition auto. rewrite dom_insert_L.
      set_solver. }
    iSplit; first done.
    iFrame "#".
    iApply big_sepM_delete; first eauto.
    iSplitL "Hα".
    { iRight. iLeft. iExists b. iFrame. iPureIntro; split; auto. rewrite lookup_insert //. }
    iApply (big_sepM_mono with "Htapes").
    iIntros (k' x' Hdel) "H".
    assert (k ≠ k').
    { apply lookup_delete_Some in Hdel. intuition auto. }
    rewrite ?lookup_insert_ne //.
  Qed.

  Lemma couplable_elim E e P Q Φ :
    to_val e = None →
    nclose specN ⊆ E →
    spec_ctx ∗ spec_couplable P ∗ impl_couplable Q ∗
    ((∃ b, P b ∗ Q b) -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (??) "(Hspec_ctx&Hscoupl&Hicoupl&Hwp)".
    iDestruct "Hscoupl" as (sα sbs) "(Hsα&Hsαclo)".
    iDestruct "Hicoupl" as (α bs) "(Hα&Hαclo)".
    iApply (wp_couple_bool_tape_tape Datatypes.id with "[-]"); try done; iFrame "Hsα Hα Hspec_ctx".
    iIntros (b) "(Hsα&Hα)". iApply "Hwp".
    iExists b. iSplitL "Hsα Hsαclo".
    { iApply "Hsαclo". iFrame. }
    { iApply "Hαclo". iFrame. }
  Qed.

  (* TODO: move *)
  Lemma spec_couplable_elim E P Φ :
    nclose specN ⊆ E →
    spec_ctx ∗ spec_couplable P ∗
    (∀ b, P b -∗ Φ #b)
    ⊢ WP flip @ E {{ Φ }}.
  Proof.
    iIntros (?) "(Hspec_ctx&Hscoupl&Hwp)".
    iDestruct "Hscoupl" as (sα sbs) "(Hsα&Hsαclo)".
    iApply (wp_couple_flip_tape Datatypes.id); first done.
    iFrame "Hspec_ctx Hsα". iIntros "!>" (b) "H".
    iApply "Hwp". iApply "Hsαclo". auto.
  Qed.

  (* TODO: move. It would nice to be able to impl coupl steps as a ghost action for this *)
  Lemma impl_couplable_elim E K P Φ e :
    to_val e = None →
    nclose specN ⊆ E →
    impl_couplable P ∗
    refines_right K flip ∗
    (∀ b, P b -∗ refines_right K (of_val #b) -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (??) "(Hcoupl&HK&Hwp)".
    iDestruct "Hcoupl" as (α bs) "(Hα&Hαclo)".
    iApply (wp_couple_tape_flip Datatypes.id); [ done | done | ].
    iFrame "Hα HK". iIntros (b) "(?&?)".
    iDestruct ("Hαclo" with "[$]") as "HP".
    iApply ("Hwp" with "[$] [$]").
  Qed.

  Lemma wp_couple_hash E e f sf max m sm k sk Φ :
    (* Both keys need to be in hash domain *)
    k ≤ max →
    sk ≤ max →
    (* Cannot have queried the key in either hash *)
    m !! k = None →
    sm !! sk = None →
    to_val e = None →
    nclose specN ⊆ E →
    spec_ctx ∗ hashfun max f m ∗ shashfun max sf sm ∗
    ((∃ b, hashfun max f (<[k:=b]>m) ∗ shashfun max sf (<[sk:=b]>sm)) -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (Hmax Hsmax Hlookup Hslookup Hval Hspec) "(Hspec_ctx&Hhashfun&Hshashfun&Hwp)".
    iDestruct (hashfun_couplable k with "Hhashfun") as "Hhashfun"; try eauto.
    iDestruct (shashfun_couplable sk with "Hshashfun") as "Hshashfun"; try eauto.
    iApply (couplable_elim); try done.
    iFrame "Hspec_ctx Hshashfun Hhashfun".
    iIntros "H". iApply "Hwp". iDestruct "H" as (b) "(?&?)". iExists _; by iFrame.
  Qed.

End tape_bit_hash.

Section eager_hash.

  Context `{!clutchRGS Σ}.

  (* An eager hash map that samples every key's value *)

  Definition sample_keys : val :=
    (rec: "sample_keys" "vm" "n" :=
       if: ("n" - #1) < #0 then
         #()
       else
        let: "b" := flip in
         set "vm" ("n" - #1) "b";;
        "sample_keys" "vm" ("n" - #1)).

  Definition eager_init_hash_state : val :=
   λ: "max_val",
      let: "val_map" := init_map #() in
      sample_keys "val_map" ("max_val" + #1);;
      "val_map".

  Definition eager_compute_hash_specialized hm : val :=
    λ: "v",
      match: get hm "v" with
      | SOME "b" => "b"
      | NONE => #false
      end.

  Definition eager_compute_hash : val :=
    λ: "hm" "v",
      match: get "hm" "v" with
      | SOME "b" => "b"
      | NONE => #false
      end.

  (* eager_init_hash returns a hash as a function, basically wrapping the internal state
     in the returned function *)
  Definition eager_init_hash : val :=
    λ: "max_val",
      let: "hm" := eager_init_hash_state "max_val" in
      eager_compute_hash "hm".

  Definition eager_hashfun (max : nat) f (m : gmap nat bool) : iProp Σ :=
    ∃ (hm : loc), ⌜ f = eager_compute_hash_specialized #hm ⌝ ∗
                  ⌜ (∀ i : nat, i <= max ↔ i ∈ dom m) ⌝ ∗
                  map_list hm ((λ b, LitV (LitBool b)) <$> m).

  Definition eager_shashfun (max : nat) f m : iProp Σ :=
    ∃ (hm : loc), ⌜ f = eager_compute_hash_specialized #hm ⌝ ∗
                  ⌜ (∀ i : nat, i <= max ↔ i ∈ dom m) ⌝ ∗
                  map_slist hm ((λ b, LitV (LitBool b)) <$> m).

  #[global] Instance timeless_eager_hashfun n f m :
    Timeless (eager_hashfun n f m).
  Proof. apply _. Qed.

  #[global] Instance timeless_eager_shashfun n f m :
    Timeless (eager_shashfun n f m).
  Proof. apply _. Qed.

  (* Couples the eager key sampling with a spec lazy hash table *)
  Lemma wp_sample_keys E lvm f max :
    ↑ specN ⊆ E →
    {{{ spec_ctx ∗ map_list lvm ∅ ∗ shashfun (max - 1)%nat f ∅ }}}
      sample_keys #lvm #max @ E
    {{{ RET #(); ∃ bm,
            map_list lvm ((λ v, LitV (LitBool v)) <$> bm) ∗
            ⌜ (∀ i : nat, i < max ↔ i ∈ dom bm) ⌝ ∗
            shashfun (max - 1)%nat f bm }}}.
  Proof.
    iIntros (? Φ) "(#?&Htm) HΦ".
    rewrite /sample_keys.
    remember max as k eqn:Heqk.
    iEval (setoid_rewrite Heqk) in "Htm".
    iEval (setoid_rewrite Heqk) in "HΦ".
    iAssert (∃ bm, ⌜ (∀ i : nat, (k <= i < max)%nat ↔ i ∈ dom bm) ⌝ ∗
                   map_list lvm ((λ v, LitV (LitBool v)) <$> bm) ∗
                   shashfun (max - 1)%nat f bm)%I with "[Htm]" as "Htm".
    { iExists ∅. rewrite fmap_empty. iFrame.
      iPureIntro. subst. intros; split; try lia. rewrite dom_empty_L. inversion 1. }
    assert (Hlek: k <= max) by lia.
    clear Heqk.
    iInduction k as [| k] "IH" forall (Hlek).
    - wp_pures. iApply "HΦ". iModIntro. iDestruct "Htm" as (tm Hdom) "(Hm&Htapes)".
      iExists tm. iFrame. iPureIntro. split.
      { intros. apply Hdom. lia. }
      { intros. apply Hdom. auto. }
    - iSpecialize ("IH" with "[] HΦ").
      { iPureIntro; lia. }
      wp_pures.
      case_bool_decide; first by lia.
      wp_pures.
      wp_bind flip.
      iDestruct "Htm" as (bm Hdom) "(Hmap&Hshash)".
      iApply (spec_couplable_elim); first by auto.

      iSplit.
      { iFrame "#". }
      iSplitL "Hshash".
      { iApply (shashfun_couplable k with "[$]"); auto.
        { lia. }
        { apply not_elem_of_dom_1. intros Hin. apply Hdom in Hin. lia. }
      }
      iIntros (b) "Hshash".
      wp_pures.
      replace (Z.of_nat (S k) - 1)%Z with (Z.of_nat k)%Z by lia.
      wp_apply (wp_set with "Hmap"). iIntros "Hmap".
      wp_pure _. wp_pure _. wp_pure _.
      replace (Z.of_nat (S k) - 1)%Z with (Z.of_nat k)%Z by lia.
      iApply "IH".
      iExists (<[k := b]>bm). rewrite fmap_insert. iFrame.
      { iPureIntro. intros i. split.
        * intros Hle. set_unfold.
          destruct (decide (i = k)); auto.
          right. apply Hdom; lia.
        * set_unfold. intros [?|Hdom']; try lia.
          apply Hdom in Hdom'. lia.
      }
  Qed.

  Lemma wp_eager_init_hash_couple (max : nat) E K :
    ↑specN ⊆ E →
    {{{ refines_right K (init_hash #max) }}}
      eager_init_hash #max @ E
    {{{ f, RET f; ∃ sf m, refines_right K (of_val sf) ∗ eager_hashfun max f m ∗ shashfun max sf m }}}.
  Proof.
    iIntros (? Φ) "HK HΦ".
    iMod (spec_init_hash with "[$]") as "Hf"; first done.
    rewrite /eager_init_hash/eager_init_hash_state.
    wp_pures.
    wp_apply (wp_init_map with "[//]").
    iIntros (l) "Hvm".
    wp_pures.
    iDestruct "Hf" as (f) "(HK&Hshash)".
      wp_pures.
      replace (Z.of_nat max + 1)%Z with (Z.of_nat (S max))%Z by lia.
    iAssert (spec_ctx)%I with "[HK]" as "#?".
    { iDestruct "HK" as "($&_)". }
    wp_apply (wp_sample_keys _ _ _ (S max)  with "[$Hvm Hshash]"); first done.
    { simpl. assert (max - 0 = max) as -> by lia. iFrame "#∗". }
    iDestruct 1 as (bm) "(Hvm&%Hdom&Hshash)".
    wp_pures.
    rewrite /eager_compute_hash.
    wp_pures.
    iModIntro. iApply "HΦ".
    iExists _, _.
    replace (S max - 1) with max by lia.
    iFrame.
    iExists _. iFrame. iPureIntro; split; eauto.
    intros. rewrite -Hdom. lia.
  Qed.

  (* Couples the spec eager key sampling with an impl tape hash table *)
  Lemma spec_sample_keys E K lvm f max e Φ :
    to_val e = None →
    ↑ specN ⊆ E →
    (map_slist lvm ∅ ∗ hashfun (max - 1)%nat f ∅) -∗
    refines_right K (sample_keys #lvm #max) -∗
    ((∃ bm, map_slist lvm ((λ v, LitV (LitBool v)) <$> bm) ∗
            ⌜ (∀ i : nat, i < max ↔ i ∈ dom bm) ⌝ ∗
            hashfun (max - 1)%nat f bm ∗
            refines_right K (of_val #())) -∗ WP e @ E {{ Φ }}) -∗
    WP e @ E {{ Φ }}.
  Proof.
    iIntros (??) "Htm HK HΦ".
    rewrite /sample_keys.
    remember max as k eqn:Heqk.
    iEval (setoid_rewrite Heqk) in "Htm".
    iEval (setoid_rewrite Heqk) in "HΦ".
    iAssert (∃ bm, ⌜ (∀ i : nat, (k <= i < max)%nat ↔ i ∈ dom bm) ⌝ ∗
                   map_slist lvm ((λ v, LitV (LitBool v)) <$> bm) ∗
                   hashfun (max - 1)%nat f bm)%I with "[Htm]" as "Htm".
    { iExists ∅. rewrite fmap_empty. iFrame.
      iPureIntro. subst. intros; split; try lia. rewrite dom_empty_L. inversion 1. }
    assert (Hlek: k <= max) by lia.
    clear Heqk.
    iInduction k as [| k] "IH" forall (Hlek).
    - tp_pures. iApply "HΦ". iDestruct "Htm" as (tm Hdom) "(Hm&Htapes)".
      iExists tm. iFrame. iPureIntro. split.
      { intros. apply Hdom. lia. }
      { intros. apply Hdom. auto. }
    - iSpecialize ("IH" with "[]").
      { iPureIntro; lia. }
      tp_pures.
      case_bool_decide; first by lia.
      tp_pures.
      tp_bind flip.
      rewrite refines_right_bind.
      iDestruct "Htm" as (bm Hdom) "(Hmap&Hshash)".
      iApply (impl_couplable_elim); [ done | done | ].
      iSplitL "Hshash".
      { iApply (hashfun_couplable k with "[$]"); auto.
        { lia. }
        { apply not_elem_of_dom_1. intros Hin. apply Hdom in Hin. lia. }
      }
      iFrame "HK".
      iIntros (b) "Hshash HK".
      rewrite -refines_right_bind /=.
      tp_pures.
      replace (Z.of_nat (S k) - 1)%Z with (Z.of_nat k)%Z by lia.
      tp_bind (set _ _ _).
      rewrite refines_right_bind.
      iMod (spec_set with "[$] [$]") as "(HK&Hmap)"; first done.
      rewrite -refines_right_bind /=.
      tp_pure. tp_pure. tp_pure.
      replace (Z.of_nat (S k) - 1)%Z with (Z.of_nat k)%Z by lia.
      iApply ("IH" with "[$] [$]").
      iExists (<[k := b]>bm). rewrite fmap_insert. iFrame.
      { iPureIntro. intros i. split.
        * intros Hle. set_unfold.
          destruct (decide (i = k)); auto.
          right. apply Hdom; lia.
        * set_unfold. intros [?|Hdom']; try lia.
          apply Hdom in Hdom'. lia.
      }
  Qed.

  (* TODO: unfortunately the to_val e restriction on our tape coupling lemmas
     means we have to unfold init_hash here to prove this *)
  Lemma spec_eager_init_hash_couple (max : nat) E K :
    ↑specN ⊆ E →
    {{{ refines_right K (eager_init_hash #max) }}}
      init_hash #max @ E
    {{{ f, RET f; ∃ sf m, refines_right K (of_val sf) ∗ eager_shashfun max sf m ∗ hashfun max f m }}}.
  Proof.
    iIntros (? Φ) "HK HΦ".
    rewrite /init_hash.
    wp_pures.
    wp_apply (wp_init_hash_state with "[//]").
    iIntros (??) "Hhash".
    rewrite /eager_init_hash.
    rewrite /eager_init_hash_state.
    tp_pures.
    tp_bind (init_map _).
    rewrite refines_right_bind.
    iMod (spec_init_map with "[$]") as (l) "(HK&Hm)"; first done.
    rewrite -refines_right_bind /=.
    tp_pures.
    replace (Z.of_nat max + 1)%Z with (Z.of_nat (S max))%Z by lia.
    tp_bind (sample_keys _ _).
    rewrite refines_right_bind.
    iApply (spec_sample_keys _ _ _ _ (S max) with "[Hm Hhash] [HK]"); [ done | done | | |].
    { iFrame "Hm". simpl. assert (max - 0 = max) as -> by lia. iFrame. }
    { iApply "HK". }
    iDestruct 1 as (bm) "(Hvm&%Hdom&Hshash&HK)".
    rewrite -refines_right_bind /=.
    rewrite /compute_hash/eager_compute_hash.
    tp_pures.
    wp_pures.
    iModIntro. iApply "HΦ". iExists _, _.
    iSplitL "HK".
    { iExact "HK". }
    iSplitL "Hvm".
    { iExists _. iFrame. iPureIntro. split; eauto.
      intros. rewrite -Hdom. lia. }
    assert (max - 0 = max) as -> by lia. eauto.
  Qed.

  Lemma wp_eager_hashfun_prev E f m (max n : nat) (b : bool) :
    m !! n = Some b →
    {{{ eager_hashfun max f m }}}
      f #n @ E
    {{{ RET #b; eager_hashfun max f m }}}.
  Proof.
    iIntros (Hlookup Φ) "Hhash HΦ".
    iDestruct "Hhash" as (lvm -> Hdom) "Hvm".
    rewrite /eager_compute_hash_specialized.
    wp_pures.
    wp_apply (wp_get with "Hvm").
    iIntros (vret) "(Hhash&->)".
    rewrite lookup_fmap Hlookup /=. wp_pures.
    iModIntro. iApply "HΦ". iExists _. iFrame. eauto.
  Qed.

  Lemma spec_eager_hashfun_prev E K f m (max n : nat) (b : bool) :
    m !! n = Some b →
    ↑specN ⊆ E →
    eager_shashfun max f m -∗
    refines_right K (f #n) ={E}=∗ refines_right K (of_val #b) ∗ eager_shashfun max f m.
  Proof.
    iIntros (Hlookup ?) "Hhash HK".
    iDestruct "Hhash" as (hm ->) "(%&H)".
    rewrite /eager_compute_hash_specialized.
    tp_pures.
    tp_bind (get _ _).
    iEval (rewrite refines_right_bind) in "HK".
    iMod (spec_get with "[$] [$]") as "(HK&Hm)"; first done.
    iEval (rewrite -refines_right_bind /=) in "HK".
    rewrite lookup_fmap Hlookup /=.
    tp_pures. iFrame. iModIntro. iExists _. eauto.
  Qed.

  Lemma wp_eager_hashfun_out_of_range E f m (max : nat) (z : Z) :
    (z < 0 ∨ max < z)%Z →
    {{{ eager_hashfun max f m }}}
      f #z @ E
    {{{ RET #false; eager_hashfun max f m }}}.
  Proof.
    iIntros (Hrange Φ) "Hhash HΦ".
    iDestruct "Hhash" as (lvm -> Hdom) "Hvm".
    rewrite /eager_compute_hash_specialized.
    wp_pures.
    wp_apply (wp_get_Z with "Hvm").
    iIntros (vret) "(Hhash&->)".
    rewrite lookup_fmap.
    case_bool_decide.
    { wp_pures. iApply "HΦ". iModIntro. iExists _. iFrame. auto. }
    assert (m !! Z.to_nat z = None) as ->.
    { apply not_elem_of_dom_1. rewrite -Hdom. lia. }
    wp_pures.
    iApply "HΦ". iModIntro. iExists _. iFrame. auto.
  Qed.

  Lemma spec_eager_hashfun_out_of_range E K f m (max : nat) (z : Z) :
    (z < 0 ∨ max < z)%Z →
    ↑specN ⊆ E →
    eager_shashfun max f m -∗
    refines_right K (f #z) ={E}=∗ refines_right K (of_val #false) ∗ eager_shashfun max f m.
  Proof.
    iIntros (Hlookup ?) "Hhash HK".
    iDestruct "Hhash" as (hm ->) "(%Hdom&H)".
    rewrite /eager_compute_hash_specialized.
    tp_pures.
    tp_bind (get _ _).
    iEval (rewrite refines_right_bind) in "HK".
    iMod (spec_get_Z with "[$] [$]") as "(HK&Hm)"; first done.
    iEval (rewrite -refines_right_bind /=) in "HK".
    rewrite lookup_fmap.
    case_bool_decide.
    { tp_pures. iFrame. iModIntro. iExists _. iFrame. auto. }
    assert (m !! Z.to_nat z = None) as ->.
    { apply not_elem_of_dom_1. rewrite -Hdom. lia. }
    tp_pures. iFrame "HK".
    iModIntro. iExists _. iFrame. auto.
  Qed.

  Definition hashN := nroot.@"hash".

  Lemma eager_hashfun_dom (max : nat) (z: Z) m f:
    ¬ ((z < 0)%Z ∨ (max < z)%Z) →
    eager_hashfun max f m -∗
    ⌜ is_Some (m !! (Z.to_nat z)) ⌝.
  Proof.
    iIntros (?). iDestruct 1 as (?? Hdom ?) "H".
    iPureIntro. apply elem_of_dom. apply Hdom. lia.
  Qed.

  Lemma eager_shashfun_dom (max : nat) (z: Z) m f:
    ¬ ((z < 0)%Z ∨ (max < z)%Z) →
    eager_shashfun max f m -∗
    ⌜ is_Some (m !! (Z.to_nat z)) ⌝.
  Proof.
    iIntros (?). iDestruct 1 as (?? Hdom ?) "H".
    iPureIntro. apply elem_of_dom. apply Hdom. lia.
  Qed.

  Lemma eager_lazy_refinement (max: nat) :
    ⊢ REL eager_init_hash #max << init_hash #max : lrel_int → lrel_bool.
  Proof.
    rewrite refines_eq. iIntros (K) "HK Hown".
    iApply wp_fupd.
    wp_apply (wp_eager_init_hash_couple with "HK"); first done.
    iIntros (f) "H". iDestruct "H" as (sf m) "(HK&Hsf)".
    set (P := (∃ m, eager_hashfun max f m ∗ shashfun max sf m)%I).
    iMod (na_inv_alloc clutchRGS_nais _ hashN P with "[Hsf]") as "#Hinv".
    { iNext. iExists m. iFrame. }
    iModIntro. iExists _. iFrame.
    iIntros (v1 v2) "!> Hint".
    iDestruct "Hint" as (z) "(->&->)".
    clear m K.
    rewrite /P.
    iApply (refines_na_inv with "[$Hinv]") ; auto ; iIntros "[HP Hclose]".
    rewrite refines_eq. iIntros (K) "HK Hown".
    iDestruct "HP" as (m) "(>Hf&>Hsf)".
    destruct (decide (z < 0 ∨ max < z)%Z).
    - iApply wp_fupd.
      iMod (spec_hashfun_out_of_range with "[$] [$]") as "(HK&Hsf)"; try done.
      wp_apply (wp_eager_hashfun_out_of_range with "[$]"); first done.
      iIntros "Hf".
      iMod ("Hclose" with "[-HK]").
      { iFrame. iNext. iExists _. iFrame. }
      iExists _. iFrame. iExists _. auto.
    - assert (z = Z.to_nat z) as -> by lia.
      iDestruct (eager_hashfun_dom with "[$]") as (b) "%Hb"; first eassumption.
      iMod (spec_hashfun_prev with "[$] [$]") as "(HK&Hsf)"; try eassumption; auto.
      iApply wp_fupd.
      wp_apply (wp_eager_hashfun_prev with "[$]"); try eassumption.
      iIntros "Hf".
      iMod ("Hclose" with "[-HK]").
      { iFrame. iNext. iExists _. iFrame. }
      iExists _. iFrame. iExists _. auto.
  Qed.

  Lemma lazy_eager_refinement (max: nat) :
    ⊢ REL init_hash #max << eager_init_hash #max : lrel_int → lrel_bool.
  Proof.
    rewrite refines_eq. iIntros (K) "HK Hown".
    iApply wp_fupd.
    wp_apply (spec_eager_init_hash_couple with "HK"); first done.
    iIntros (f) "H". iDestruct "H" as (sf m) "(HK&Hsf)".
    set (P := (∃ m, eager_shashfun max sf m ∗ hashfun max f m)%I).
    iMod (na_inv_alloc clutchRGS_nais _ hashN P with "[Hsf]") as "#Hinv".
    { iNext. iExists m. iFrame. }
    iModIntro. iExists _. iFrame.
    iIntros (v1 v2) "!> Hint".
    iDestruct "Hint" as (z) "(->&->)".
    clear m K.
    rewrite /P.
    iApply (refines_na_inv with "[$Hinv]") ; auto ; iIntros "[HP Hclose]".
    rewrite refines_eq. iIntros (K) "HK Hown".
    iDestruct "HP" as (m) "(Hsf&Hf)".
    iDestruct "Hsf" as ">Hsf".
    (* TODO: why is TC inference so slow for timeless_hashfun? having to rewrite manually *)
    rewrite timeless_hashfun.
    iDestruct "Hf" as ">Hf".
    destruct (decide (z < 0 ∨ max < z)%Z).
    - iApply wp_fupd.
      iMod (spec_eager_hashfun_out_of_range with "[$] [$]") as "(HK&Hsf)"; try done.
      wp_apply (wp_hashfun_out_of_range with "[$]"); first done.
      iIntros "Hf".
      iMod ("Hclose" with "[-HK]").
      { iFrame. iNext. iExists _. iFrame. }
      iExists _. iFrame. iExists _. auto.
    - assert (z = Z.to_nat z) as -> by lia.
      iDestruct (eager_shashfun_dom with "[$]") as (b) "%Hb"; first eassumption.
      iMod (spec_eager_hashfun_prev with "[$] [$]") as "(HK&Hsf)"; try eassumption; auto.
      iApply wp_fupd.
      wp_apply (wp_hashfun_prev with "[$]"); try eassumption.
      iIntros "Hf".
      iMod ("Hclose" with "[-HK]").
      { iFrame. iNext. iExists _. iFrame. }
      iExists _. iFrame. iExists _. auto.
  Qed.

End eager_hash.

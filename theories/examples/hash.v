From stdpp Require Import namespaces.
From iris.base_logic Require Import invariants na_invariants.
From self.prob_lang Require Import notation proofmode primitive_laws spec_rules spec_tactics.
From self.logrel Require Import model rel_rules rel_tactics.
From iris.algebra Require Import auth gmap excl frac agree.
From self.prelude Require Import base.

Set Default Proof Using "Type*".


Section map.

(* Simple map as an associative linked list, based on the examples
   from the transfinite Iris repo *)

  Definition find_list : val :=
    (rec: "find" "h" "k" :=
       match: !"h" with
         NONE => NONE
       | SOME "p" =>
           let: "kv" := Fst "p" in
           let: "next" := Snd "p" in
           if: (Fst "kv") = "k" then SOME (Snd "kv") else "find" "next" "k"
       end).

  Definition cons_list : val :=
    λ: "h" "v", ref (SOME ("v", "h")).

  Definition init_list : val :=
    λ:<>, ref NONE.

  Context `{!prelogrelGS Σ}.

  (* Impl *)
  Fixpoint assoc_list (l: loc) (vs: list (nat * val)) : iProp Σ :=
    match vs with
    | nil => l ↦ NONEV
    | (k, v) :: vs => ∃ (l' : loc), l ↦ SOMEV ((#k, v), #l') ∗ assoc_list l' vs
  end.

  (* Spec/ghost *)
  Fixpoint assoc_slist (l: loc) (vs: list (nat * val)) : iProp Σ :=
    match vs with
    | nil => l ↦ₛ NONEV
    | (k, v) :: vs => ∃ (l' : loc), l ↦ₛ SOMEV ((#k, v), #l') ∗ assoc_slist l' vs
  end.

  Lemma wp_init_list E :
    {{{ True }}}
      init_list #() @ E
    {{{ l, RET LitV (LitLoc l); assoc_list l nil }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite /init_list. wp_pures. wp_alloc l. iModIntro. iApply "HΦ". eauto.
  Qed.

  Lemma spec_init_list E K :
    ↑specN ⊆ E →
    refines_right K (init_list #()) ={E}=∗ ∃ (l: loc), refines_right K (#l) ∗ assoc_slist l [].
  Proof.
    iIntros (?) "H".
    rewrite /init_list.
    tp_pures K.
    tp_alloc K as l "Hl".
    iExists _. iFrame. auto.
  Qed.

  Lemma wp_cons_list E l vs (k : nat) (v : val) :
    {{{ assoc_list l vs }}}
      cons_list #l (#k, v)%V @ E
    {{{ l', RET LitV (LitLoc l'); assoc_list l' ((k, v) :: vs) }}}.
  Proof.
    iIntros (Φ) "H HΦ".
    rewrite /cons_list. wp_pures. wp_alloc l' as "H'". iModIntro. iApply "HΦ".
    iExists l. iFrame.
  Qed.

  Lemma spec_cons_list E K l vs (k : nat) v :
    ↑specN ⊆ E →
    assoc_slist l vs -∗
    refines_right K (cons_list #l (#k, v)%V) ={E}=∗
    ∃ (l: loc), refines_right K (#l) ∗ assoc_slist l ((k, v) :: vs).
  Proof.
    iIntros (?) "H Hr".
    rewrite /cons_list.
    tp_pures K.
    tp_alloc K as l' "Hl".
    iExists _. iFrame. iExists _; iFrame. auto.
  Qed.

  Fixpoint find_list_gallina (vs: list (nat * val)) (k: nat) :=
    match vs with
    | nil => None
    | (k', v') :: vs =>
        if bool_decide (k' = k) then
          Some v'
        else
          find_list_gallina vs k
    end.

  Definition opt_to_val (ov: option val) :=
    match ov with
    | Some v => SOMEV v
    | None => NONEV
    end.

  Lemma wp_find_list E l vs (k: nat) :
    {{{ assoc_list l vs }}}
      find_list #l #k @ E
    {{{ v, RET v;
        assoc_list l vs ∗ ⌜ v = opt_to_val (find_list_gallina vs k) ⌝
    }}}.
  Proof.
    iIntros (Φ) "Hassoc HΦ".
    rewrite /find_list. iInduction vs as [|(k', v') vs] "IH" forall (l).
    - wp_pures. rewrite /assoc_list. wp_load. wp_pures. iModIntro. iApply "HΦ"; auto.
    - wp_pures. iDestruct "Hassoc" as (?) "(Hl&Hassoc)".
      wp_load. wp_pures. case_bool_decide as Hcase.
      { wp_pures.  iApply "HΦ". simpl. rewrite bool_decide_true //; last first.
        { inversion Hcase; auto. lia. }
        iModIntro. iSplit; last done. iExists _; iFrame; eauto. }
      { wp_pure. iApply ("IH" with "[$]"). iNext.
        iIntros (v) "Hfind". iApply "HΦ".
        iEval simpl. rewrite bool_decide_false //; last by congruence.
        iDestruct "Hfind" as "(?&$)". iExists _; iFrame.
      }
  Qed.

  Lemma spec_find_list E K l vs (k : nat):
    ↑specN ⊆ E →
    assoc_slist l vs -∗
    refines_right K (find_list #l #k) ={E}=∗
    refines_right K (opt_to_val (find_list_gallina vs k)) ∗ assoc_slist l vs.
  Proof.
    iIntros (?) "H Hr".
    rewrite /find_list. iInduction vs as [|(k', v') vs] "IH" forall (l).
    - tp_pures K. rewrite /assoc_list. tp_load K. tp_pures K. iModIntro. iFrame.
    - tp_pures K. iDestruct "H" as (?) "(Hl&Hassoc)".
      tp_load K. tp_pures K; first solve_vals_compare_safe. case_bool_decide as Hcase.
      { tp_pures K. simpl. rewrite bool_decide_true //; last first.
        { inversion Hcase; auto. lia. }
        iModIntro. iFrame "Hr". iExists _; iFrame; eauto. }
      { tp_pure K _. iMod ("IH" with "[$Hassoc] [$]") as "(?&?)".
        iEval simpl. rewrite bool_decide_false //; last by congruence.
        iFrame. iModIntro. iExists _; iFrame.
      }
  Qed.

  Definition init_map : val :=
    λ: <>, ref (init_list #()).

  Definition get : val :=
    λ: "m" "k", find_list !"m" "k".

  Definition set : val :=
    λ: "m" "k" "v", "m" <- cons_list !"m" ("k", "v").

  Definition map_list lm (m: gmap nat val) : iProp Σ :=
    ∃ (lv : loc) vs, lm ↦ #lv ∗ ⌜ list_to_map vs = m ⌝ ∗ assoc_list lv vs.

  Definition map_slist lm (m: gmap nat val) : iProp Σ :=
    ∃ (lv : loc) vs, lm ↦ₛ #lv ∗ ⌜ list_to_map vs = m ⌝ ∗ assoc_slist lv vs.

  Lemma wp_init_map E :
    {{{ True }}}
      init_map #() @ E
    {{{ l, RET LitV (LitLoc l); map_list l ∅ }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite /init_map. wp_pures. wp_apply (wp_init_list with "[//]").
    iIntros (l) "Halloc". wp_alloc lm. iApply "HΦ".
    iModIntro. iExists _, _. iFrame. eauto.
  Qed.

  Lemma spec_init_map E K :
    ↑specN ⊆ E →
    refines_right K (init_map #()) ={E}=∗ ∃ (l: loc), refines_right K (#l) ∗ map_slist l ∅.
  Proof.
    iIntros (?) "H".
    rewrite /init_map.
    tp_pures K.
    tp_bind K (init_list #()).
    rewrite refines_right_bind.
    iMod (spec_init_list with "[$]") as (l) "(HK&Halloc)"; first done.
    iEval (rewrite -refines_right_bind /=) in "HK".
    tp_alloc K as lm "Hl".
    iExists _. iFrame. iExists _, _; iFrame; auto.
  Qed.

  Lemma find_list_gallina_map_lookup vs (m : gmap nat val) n :
    list_to_map vs = m →
    find_list_gallina vs n = m !! n.
  Proof.
    revert m.
    induction vs as [| (k, v) vs IH] => m Heq.
    - rewrite /=. simpl in Heq. subst; auto.
    - rewrite list_to_map_cons in Heq. subst.
      destruct (decide (k = n)).
      { subst. rewrite lookup_insert /= bool_decide_true //. }
      rewrite lookup_insert_ne //= bool_decide_false //. eauto.
  Qed.

  Lemma wp_get E lm m (n: nat) :
    {{{ map_list lm m }}}
      get #lm #n @ E
    {{{ res, RET res; map_list lm m ∗ ⌜ res = opt_to_val (m !! n) ⌝ }}}.
  Proof.
    iIntros (Φ) "Hm HΦ".
    rewrite /get. wp_pures.
    iDestruct "Hm" as (ll vs) "(Hll&%Heq&Hassoc)".
    wp_load. wp_apply (wp_find_list with "[$]").
    iIntros (vret) "(Hassoc&Hm)". iApply "HΦ". iSplit.
    { iExists _, _. iFrame. eauto. }
    rewrite (find_list_gallina_map_lookup vs m) //.
  Qed.

  Lemma spec_get E K lm m (n : nat) :
    ↑specN ⊆ E →
    map_slist lm m -∗
    refines_right K (get #lm #n) ={E}=∗ refines_right K (opt_to_val (m !! n)) ∗ map_slist lm m.
  Proof.
    iIntros (?) "Hm Hr".
    rewrite /get.
    tp_pures K.
    iDestruct "Hm" as (ll vs) "(Hll&%Heq&Hassoc)".
    tp_load K.
    iMod (spec_find_list with "[$] [$]") as "(HK&Halloc)"; first done.
    rewrite (find_list_gallina_map_lookup vs m) //. iFrame.
    iExists _ ,_. iFrame. eauto.
  Qed.

  Lemma wp_set E lm m (n: nat) (v: val) :
    {{{ map_list lm m }}}
      set #lm #n v @ E
    {{{ RET #(); map_list lm (<[n := v]>m) }}}.
  Proof.
    iIntros (Φ) "Hm HΦ".
    rewrite /set. wp_pures.
    iDestruct "Hm" as (??) "(?&%Heq&Hassoc)".
    wp_load. wp_pures. wp_apply (wp_cons_list with "[$]").
    iIntros (l') "Hassoc'". wp_store. iModIntro.
    iApply "HΦ". iExists _, _. iFrame. rewrite list_to_map_cons Heq //.
  Qed.

  Lemma spec_set E K lm m (n : nat) (v: val) :
    ↑specN ⊆ E →
    map_slist lm m -∗
    refines_right K (set #lm #n v) ={E}=∗ refines_right K #() ∗ map_slist lm (<[n := v]>m).
  Proof.
    iIntros (?) "Hm Hr".
    rewrite /set.
    tp_pures K.
    iDestruct "Hm" as (ll vs) "(Hll&%Heq&Hassoc)".
    tp_load K. tp_pures K.
    tp_bind K (cons_list _ _).
    iEval (rewrite refines_right_bind) in "Hr".
    iMod (spec_cons_list with "[$] [$]") as (?)"(Hr&Halloc)"; first done.
    iEval (rewrite -refines_right_bind /=) in "Hr".
    tp_store K.
    iFrame. iExists _, _. iFrame. rewrite list_to_map_cons Heq //.
  Qed.

End map.


Module simple_bit_hash.

  Context `{!prelogrelGS Σ}.

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
          let: "b" := flip #() in
          set hm "v" "b";;
          "b"
      end.
  Definition compute_hash : val :=
    λ: "hm" "v",
      match: get "hm" "v" with
      | SOME "b" => "b"
      | NONE =>
          let: "b" := flip #() in
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
    ∃ (hm : loc), ⌜ f = compute_hash_specialized #hm ⌝ ∗ spec_ctx ∗ map_slist hm ((λ b, LitV (LitBool b)) <$> m).

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
    tp_pures K.
    tp_bind K (init_map _).
    iEval (rewrite refines_right_bind) in "Hspec".
    iMod (spec_init_map with "[$]") as (l) "(Hspec&Hm)"; auto.
    iEval (rewrite -refines_right_bind /=) in "Hspec".
    rewrite /compute_hash.
    tp_pures K.
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
    iDestruct "Hhash" as (hm ->) "(#?&H)".
    rewrite /compute_hash_specialized.
    tp_pures K.
    tp_bind K (get _ _).
    iEval (rewrite refines_right_bind) in "HK".
    iMod (spec_get with "[$] [$]") as "(HK&Hm)"; first done.
    iEval (rewrite -refines_right_bind /=) in "HK".
    rewrite lookup_fmap Hlookup /=.
    tp_pures K. iFrame. iModIntro. iExists _. eauto.
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
    iDestruct "Hshash" as (hsm ->) "(#?&Hsm)".
    rewrite /compute_hash_specialized.
    wp_pures.
    tp_pures K.

    (* spec get *)
    tp_bind K (get _ _).
    iEval (rewrite refines_right_bind) in "HK".
    iMod (spec_get with "[$] [$]") as "(HK&Hsm)"; first done.
    iEval (rewrite -refines_right_bind /=) in "HK".
    rewrite lookup_fmap Hnonesm /=.
    tp_pures K.

    (* impl get *)
    wp_apply (wp_get with "[$]").
    iIntros (res) "(Hm&->)".
    rewrite lookup_fmap Hnonem /=.
    wp_pures.

    (* couple -- FIXME: breaking abstraction *)
    tp_bind K (flip #()) %E.
    iEval (rewrite refines_right_bind) in "HK".
    wp_apply (wp_couple_flips_lr); first done.
    iDestruct "HK" as "(#Hspec&HK)".
    iFrame "Hspec". iFrame "HK".
    iIntros (b) "HK".
    iAssert (refines_right _ _) with "[$Hspec $HK]" as "HK".
    iEval (rewrite -refines_right_bind /=) in "HK".
    tp_pures K.
    do 2 wp_pures.

    tp_bind K (set _ _ _).
    iEval (rewrite refines_right_bind) in "HK".
    iMod (spec_set with "[$] [$]") as "(HK&Hsm)"; first done.
    iEval (rewrite -refines_right_bind /=) in "HK".
    tp_pures K.

    wp_apply (wp_set with "[$]").
    iIntros "Hm". wp_pures. iApply "HΦ".
    iFrame. iModIntro.
    iSplitL "Hm".
    { iExists _. iSplit; first auto. rewrite fmap_insert //. }
    { iExists _. iSplit; first auto. rewrite fmap_insert //. iFrame "#∗". }
  Qed.


  (* But we cannot sample ahead, so for example one cannot prove that if f is a hashmap
    (f 1; f 2) refines (f 2; f1)  *)

End simple_bit_hash.

Section tape_bit_hash.

  Context `{!prelogrelGS Σ}.

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
        let: "α" := alloc in
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
          let: "α" :=
            match: get tm "v" with
            | SOME "α" => "α"
            | NONE => #()
            end in
          let: "b" := flip "α" in
          set vm "v" "b";;
          "b"
      end.

  Definition compute_hash : val :=
    λ: "vm" "tm" "v",
      match: get "vm" "v" with
      | SOME "b" => "b"
      | NONE =>
          let: "α" :=
            match: get "tm" "v" with
            | SOME "α" => "α"
            | NONE => #()
            end in
          let: "b" := flip "α" in
          set "vm" "v" "b";;
          "b"
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
       ⌜ (∀ i : nat, i <= max → i ∈ dom tm) ⌝ ∗
       ⌜ dom m ⊆ dom tm ∧ dom vm ⊆ dom tm ⌝ ∗
       ⌜ f = compute_hash_specialized #lvm #ltm ⌝ ∗
       map_list lvm ((λ v, LitV (LitBool v)) <$> vm) ∗
       map_list ltm ((λ v, LitV (LitLbl v)) <$> tm) ∗
       ([∗ map] i ↦ α ∈ tm,
          (∃ b : bool, ⌜ m !! i = Some b ⌝ ∗ ⌜ vm !! i = Some b ⌝) ∨
          (∃ b : bool, ⌜ m !! i = Some b ⌝ ∗ ⌜ vm !! i = None ⌝ ∗ α ↪ (b :: nil) ) ∨
          (⌜ m !! i = None ⌝ ∗ ⌜ vm !! i = None ⌝ ∗ α ↪ nil)).

  Definition shashfun (max : nat) f (m : gmap nat bool) : iProp Σ :=
    ∃ (lvm ltm: loc) (vm: gmap nat bool) (tm: gmap nat loc),
       ⌜ (∀ i : nat, i <= max → i ∈ dom tm) ⌝ ∗
       ⌜ dom m ⊆ dom tm ∧ dom vm ⊆ dom tm ⌝ ∗
       ⌜ f = compute_hash_specialized #lvm #ltm ⌝ ∗
       spec_ctx ∗
       map_slist lvm ((λ v, LitV (LitBool v)) <$> vm) ∗
       map_slist ltm ((λ v, LitV (LitLbl v)) <$> tm) ∗
       ([∗ map] i ↦ α ∈ tm,
          (∃ b : bool, ⌜ m !! i = Some b ⌝ ∗ ⌜ vm !! i = Some b ⌝) ∨
          (∃ b : bool, ⌜ m !! i = Some b ⌝ ∗ ⌜ vm !! i = None ⌝ ∗ α ↪ₛ (b :: nil) ) ∨
          (⌜ m !! i = None ⌝ ∗ ⌜ vm !! i = None ⌝ ∗ α ↪ₛ nil)).

  Lemma wp_alloc_tapes E ltm max :
    {{{ map_list ltm ∅ }}}
      alloc_tapes #ltm #max @ E
    {{{ RET #(); ∃ tm,
            map_list ltm ((λ v, LitV (LitLbl v)) <$> tm) ∗
            ⌜ (∀ i : nat, i < max ↔ i ∈ dom tm) ⌝ ∗
            ([∗ map] i ↦ α ∈ tm, α ↪ nil) }}}.
  Proof.
    iIntros (Φ) "Htm HΦ".
    rewrite /alloc_tapes.
    remember max as k eqn:Heqk.
    iEval (setoid_rewrite Heqk) in "HΦ".
    iAssert (∃ tm, ⌜ (∀ i : nat, (k <= i < max)%nat ↔ i ∈ dom tm) ⌝ ∗
                   map_list ltm ((λ v, LitV (LitLbl v)) <$> tm) ∗
                   ([∗ map] i ↦ α ∈ tm, α ↪ nil))%I with "[Htm]" as "Htm".
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
                                    ([∗ map] i ↦ α ∈ tm, α ↪ₛ nil).
  Proof.
    iIntros (Φ) "Htm HK".
    rewrite /alloc_tapes.
    remember max as k eqn:Heqk.
    iAssert (∃ tm, ⌜ (∀ i : nat, (k <= i < max)%nat ↔ i ∈ dom tm) ⌝ ∗
                   map_slist ltm ((λ v, LitV (LitLbl v)) <$> tm) ∗
                   ([∗ map] i ↦ α ∈ tm, α ↪ₛ nil))%I with "[Htm]" as "Htm".
    { iExists ∅. rewrite fmap_empty. iFrame. iSplit.
      { iPureIntro. subst. intros; split; try lia. rewrite dom_empty_L. inversion 1. }
      { rewrite big_sepM_empty. auto. } }
    iEval (rewrite Heqk).
    assert (Hlek: k <= max) by lia.
    clear Heqk.
    iInduction k as [| k] "IH" forall (Hlek).
    - tp_pures K. iFrame. iModIntro. iDestruct "Htm" as (tm Hdom) "(Hm&Htapes)".
      iExists tm. iFrame. iPureIntro. split.
      { intros. apply Hdom. lia. }
      { intros. apply Hdom. auto. }
    - iSpecialize ("IH" with "[]").
      { iPureIntro; lia. }
      tp_pures K.
      case_bool_decide; first by lia.
      tp_pures K.
      tp_bind K (alloc).
      rewrite refines_right_bind.
      iMod (refines_right_alloctape with "HK") as (α) "(HK&Hα)"; first done.
      rewrite -refines_right_bind /=.

      tp_pures K.
      tp_bind K (set _ _ _).
      rewrite refines_right_bind.
      iDestruct "Htm" as (tm Hdom) "(Htm&Htapes)".
      replace (Z.of_nat (S k) - 1)%Z with (Z.of_nat k)%Z by lia.
      iMod (spec_set with "[$] HK") as "(HK&Htm)"; first done.
      rewrite -refines_right_bind /=.
      tp_pure K _.
      tp_pure K _.
      tp_pure K _.
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

  Lemma wp_init_hash max E :
    {{{ True }}}
      init_hash #max @ E
    {{{ f, RET f; hashfun max f ∅ }}}.
  Proof.
    rewrite /init_hash.
    iIntros (Φ) "_ HΦ".
    wp_pures. rewrite /init_hash_state.
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
    { iPureIntro. intros. apply Hdom; lia. }
    iSplit; first eauto.
    iSplit; first eauto.
    iApply (big_sepM_mono with "Htapes").
    { iIntros (k α Hlookup) "Htape". iRight. iRight. rewrite ?lookup_empty; iFrame; auto. }
  Qed.

  Lemma spec_init_hash (max : nat) E K :
    ↑specN ⊆ E →
    refines_right K (init_hash #max) ={E}=∗ ∃ f, refines_right K (of_val f) ∗ shashfun max f ∅.
  Proof.
    iIntros (?) "H".
    rewrite /init_hash.
    tp_pures K.
    rewrite /init_hash_state.
    tp_pures K.
    tp_bind K (init_map #()).
    rewrite refines_right_bind.
    iMod (spec_init_map with "[$]") as (lvm) "(HK&Hvm)"; first done.
    iEval (rewrite -refines_right_bind /=) in "HK".

    tp_pures K.
    tp_bind K (init_map #()).
    rewrite refines_right_bind.
    iMod (spec_init_map with "[$]") as (ltm) "(HK&Htm)"; first done.
    iEval (rewrite -refines_right_bind /=) in "HK".
    tp_pures K.

    tp_bind K (alloc_tapes _ _).
    rewrite refines_right_bind.
    replace (Z.of_nat max + 1)%Z with (Z.of_nat (S max))%Z by lia.
    iMod (spec_alloc_tapes with "[$] [$]") as "(HK&Htm)"; first done.
    iDestruct "Htm" as (tm) "(Htm&%Hdom&Htapes)".
    iEval (rewrite -refines_right_bind /=) in "HK".
    tp_pures K.
    rewrite /compute_hash. tp_pures K.
    iModIntro. iExists _.
    iDestruct "HK" as "(#?&?)".
    iFrame "# ∗".
    iExists lvm, ltm, ∅, tm.
    rewrite ?fmap_empty. iFrame. iSplit.
    { iPureIntro. intros. apply Hdom; lia. }
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
      wp_apply (wp_flip with "Htape").
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

  Lemma spec_hashfun_prev E K f m max (n : nat) (b: bool) :
    m !! n = Some b →
    ↑specN ⊆ E →
    shashfun max f m -∗
    refines_right K (f #n) ={E}=∗ refines_right K (of_val #b) ∗ shashfun max f m.
  Proof.
    iIntros (Hlookup Φ) "Hhash HΦ".
    iDestruct "Hhash" as (lvm ltm vm tm Hdom1 Hdom2 ->) "(#?&Hvm&Htm&Htapes)".
    rewrite /compute_hash_specialized.
    tp_pures K.

    tp_bind K (get _ _).
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
      rewrite Heq2. tp_pures K.
      iModIntro.
      iFrame.
      iExists _, _, vm, tm. iFrame.
      iSplit; first done.
      iSplit; first done.
      iSplit; first done.
      iFrame "#".
      iApply big_sepM_delete; first eauto.
      iFrame "Htapes".
      iLeft. auto.
    - iDestruct "Hnvm" as "[Hnvm|Hbad]"; last first.
      { iDestruct "Hbad" as (??) "_". congruence. }
      iDestruct "Hnvm" as (b') "(%Heq1&%Heq2&Htape)".
      assert (b = b') by congruence; subst.
      rewrite Heq2. tp_pures K.
      tp_bind K (get _ _).
      rewrite refines_right_bind.
      iMod (spec_get with "Htm [$]") as "(HK&Htm)"; first done.
      rewrite -refines_right_bind/=.
      rewrite lookup_fmap Hα.
      tp_pures K.

      tp_bind K (flip _)%E.
      rewrite refines_right_bind.
      iMod (refines_right_flip with "[$] [$]") as "(HK&Hα)"; first done.
      rewrite -refines_right_bind/=.
      tp_pures K.

      tp_bind K (set _ _ _).
      rewrite refines_right_bind.
      iMod (spec_set with "Hvm_all HK") as "(HK&Hvm_all)"; first done.
      rewrite -refines_right_bind/=.
      tp_pures K.

      iFrame.
      iModIntro. iExists _, _, (<[n:=b']>vm), tm.
      iFrame.
      iSplit; first done.
      iSplit.
      { iPureIntro; split; intuition auto. rewrite dom_insert_L. set_unfold; intros ? [?|?]; auto.
        subst. apply elem_of_dom; eauto. }
      iFrame "#".
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

  Definition impl_couplable (P : bool → iProp Σ) : iProp Σ :=
    (∃ α bs, α ↪ bs ∗ (∀ b, α ↪ (bs ++ [b]) -∗ P b)).
  Definition spec_couplable (P : bool → iProp Σ) : iProp Σ :=
    (∃ α bs, α ↪ₛ bs ∗ (∀ b, α ↪ₛ (bs ++ [b]) -∗ P b)).

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
    iDestruct "Hhashfun" as (lvm ltm vm tm Hdom1 Hdom2 ->) "(#?&Hvm&Htm&Htapes)".
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
    iApply (wp_couple_tapes with "[-]"); try done; iFrame "Hsα Hα Hspec_ctx".
    iDestruct 1 as (b) "(Hsα&Hα)". iApply "Hwp".
    iExists b. iSplitL "Hsα Hsαclo".
    { iApply "Hsαclo". iFrame. }
    { iApply "Hαclo". iFrame. }
  Qed.

  Lemma spec_couplable_elim E P Φ :
    nclose specN ⊆ E →
    spec_ctx ∗ spec_couplable P ∗
    (∀ b, P b -∗ Φ #b)
    ⊢ WP flip #() @ E {{ Φ }}.
  Proof.
    iIntros (?) "(Hspec_ctx&Hscoupl&Hwp)".
    iDestruct "Hscoupl" as (sα sbs) "(Hsα&Hsαclo)".
    iApply wp_couple_flip_tape; first done.
    iFrame "Hspec_ctx Hsα". iIntros (b) "H".
    iApply "Hwp". iApply "Hsαclo". auto.
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

  Context `{!prelogrelGS Σ}.

  (* An eager hash map that samples every key's value *)

  Definition sample_keys : val :=
    (rec: "sample_keys" "vm" "n" :=
       if: ("n" - #1) < #0 then
         #()
       else
        let: "b" := flip #() in
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
                  ⌜ (∀ i : nat, i <= max → i ∈ dom m) ⌝ ∗
                  map_list hm ((λ b, LitV (LitBool b)) <$> m).

  Definition eager_shashfun (max : nat) f m : iProp Σ :=
    ∃ (hm : loc), ⌜ f = eager_compute_hash_specialized #hm ⌝ ∗
                  ⌜ (∀ i : nat, i <= max → i ∈ dom m) ⌝ ∗
                  map_slist hm ((λ b, LitV (LitBool b)) <$> m).

  (* Couples the eager key sampling with a spec lazy hash table *)
  Lemma wp_sample_keys E lvm f max :
    ↑ specN ⊆ E →
    {{{ map_list lvm ∅ ∗ shashfun (max - 1)%nat f ∅ }}}
      sample_keys #lvm #max @ E
    {{{ RET #(); ∃ bm,
            map_list lvm ((λ v, LitV (LitBool v)) <$> bm) ∗
            ⌜ (∀ i : nat, i < max ↔ i ∈ dom bm) ⌝ ∗
            shashfun (max - 1)%nat f bm }}}.
  Proof.
    iIntros (? Φ) "Htm HΦ".
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
      wp_bind (flip #())%E.
      iDestruct "Htm" as (bm Hdom) "(Hmap&Hshash)".
      iApply (spec_couplable_elim); first by auto.

      iSplit.
      { iDestruct "Hshash" as (????) "(?&?&?&$&_)". }
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
    {{{ f, RET f; ∃ sf m, eager_hashfun max f m ∗ shashfun max sf m }}}.
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
    wp_apply (wp_sample_keys _ _ _ (S max)  with "[$Hvm Hshash]"); first done.
    { simpl. assert (max - 0 = max) as -> by lia. iFrame. }
    iDestruct 1 as (bm) "(Hvm&%Hdom&Hshash)".
    wp_pures.
    rewrite /eager_compute_hash.
    wp_pures.
    iModIntro. iApply "HΦ".
    iExists _, _.
    replace (S max - 1) with max by lia.
    iFrame.
    iExists _. iFrame. iPureIntro; split; eauto.
    intros. apply Hdom. lia.
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

End eager_hash.

(** * Hashmap *)
From stdpp Require Export list_numbers.
From clutch.ert_logic Require Export expected_time_credits ert_weakestpre problang_wp proofmode
  derived_laws cost_models ert_rules.
From clutch.prob_lang Require Import notation tactics metatheory lang.
From iris.proofmode Require Export proofmode.
From Coq Require Export Reals Psatz.
From Coquelicot Require Export Hierarchy.
Require Import Lra.
From clutch.ert_logic.examples.hashmap Require Export map hash linkedlist.

Set Default Proof Using "Type*".

Section hashmap.
  Context `{!ert_clutchGS Σ CostTick}.

  Variable val_size : nat.
  Definition insert_elem: val :=
    λ: "hm" "v",
      let, ("l", "hf") := "hm" in
      let: "off" := compute_hash val_size "hf" "v" in
      let: "w" := !("l" +ₗ "off") in
      tick #1;;
      "w" <- insert "w" "v";;
      "off"
  .

  Definition lookup_elem: val :=
    λ: "hm" "v",
      let, ("l", "hf") := "hm" in
      let: "off" := compute_hash val_size "hf" "v" in
      let: "w" := !("l" +ₗ "off") in
      tick #1;;
      lookup "w" "v".

  Definition ishashmaplist (l:val) (m:gmap nat (list (nat))) :=
    (∃ (a:loc) (arr:list val) , ⌜l=#a⌝ ∗ a ↦∗ arr ∗ ⌜(length arr = S val_size)%nat⌝ ∗
                                (∀ (x:nat) (k:val), ⌜arr!!x = Some k⌝-∗
                                                              ∃ lis,  ⌜m!!x = Some lis⌝ ∗ isList k lis)
    )%I.

  Definition ishashmap (hm:val) (m1:gmap nat nat) (m2:gmap nat (list nat)) :=
    (∃ (l hf:val), ⌜hm = (l, hf)%V⌝ ∗ hashfun val_size hf m1 ∗ ishashmaplist l m2 ∗
                   ⌜∀ k v l, m2!!v=Some l -> k∈l -> m1!!k=Some v⌝
    )%I.

  Definition hashmap_size (m:gmap nat (list nat)):= sum_list_with (λ x, if m!!x is Some l then length l else 0%nat ) (seq 0 (S val_size)).

  Lemma wp_hm_insert_new E hm m1 m2 (n : nat) :
    n∉dom m1 -> 
    {{{ ishashmap hm m1 m2 ∗
          ⧖ (1+ (hashmap_size m2/(S val_size))%R) }}}
      insert_elem hm #n  @ E
      {{{ (off:nat), RET #off;
          ishashmap hm (<[n:=off]>m1) (<[off:=(m2!!!off)++n::[]]>m2) }}}.
  Proof.
  Admitted.

  
  Lemma wp_hm_lookup_new E hm m1 m2 (n : nat) :
    n∉dom m1 -> 
    {{{ ishashmap hm m1 m2 ∗
          ⧖ (1+ (hashmap_size m2/(S val_size))%R) }}}
      lookup_elem hm #n  @ E
      {{{ RET #false;
          ishashmap hm m1 m2 }}}.
  Proof.
  Admitted.
  
  
End hashmap.

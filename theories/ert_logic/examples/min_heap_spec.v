From clutch.prob_lang Require Import lang notation.
From clutch.ert_logic Require Export problang_wp.
Set Default Proof Using "Type*".

Record comparator (K : Type) (c : Costfun prob_lang) := Comparator {
  cmp :> val;
  cmp_rel : relation K;
  cmp_rel_dec :: RelDecision cmp_rel;
  cmp_rel_total :: TotalOrder cmp_rel;

  cmp_cost : R;

  cmp_has_key `{!ert_clutchGS Σ c} : K → val → iProp Σ;

  wp_cmp `{!ert_clutchGS Σ c} k1 k2 v1 v2 :
    {{{ cmp_has_key k1 v1 ∗ cmp_has_key k2 v2 ∗ ⧖ cmp_cost }}}
      cmp v1 v2
    {{{ RET #(bool_decide (cmp_rel k1 k2)); cmp_has_key k1 v1 ∗ cmp_has_key k2 v2 }}};
}.
Arguments Comparator {_ _} _ _ {_ _} _ _ _.
Arguments cmp_rel {_ _}.
Arguments cmp_cost {_ _}.
Arguments cmp_has_key {_ _} _ {_ _}.
Arguments wp_cmp {_ _ _ _ _ _}.

Class min_heap {K c} (cmp : comparator K c) := MinHeap {
  heap_new : val;
  heap_insert : val;
  heap_remove : val;

  heap_insert_cost : nat → R;
  heap_remove_cost : nat → R;

  is_min_heap `{!ert_clutchGS Σ c} (l : list K) (v : val) : iProp Σ;

  wp_heap_new `{!ert_clutchGS Σ c} :
    {{{ True }}}
      heap_new #()
    {{{ v, RET v; is_min_heap [] v }}};

  wp_heap_insert `{!ert_clutchGS Σ c} l k v w :
    {{{ is_min_heap l v ∗ cmp.(cmp_has_key) k w ∗ ⧖ (heap_insert_cost (length l)) }}}
      heap_insert v w
    {{{ v l', RET v; is_min_heap l' v ∗ ⌜l' ≡ₚ k :: l⌝ }}};

  wp_heap_remove `{!ert_clutchGS Σ c} l v :
    {{{ is_min_heap l v ∗ ⧖ (heap_remove_cost (length l)) }}}
      heap_remove v
    {{{ w, RET w;
        (⌜w = NONEV⌝ ∗ ⌜l = []⌝ ∗ is_min_heap [] v) ∨
        (∃ k u l',
            ⌜w = SOMEV u⌝ ∗ ⌜l ≡ₚ k :: l'⌝ ∗ cmp.(cmp_has_key) k u ∗
            ⌜Forall (cmp.(cmp_rel) k) l⌝ ∗ is_min_heap l' v) }}};
}.

Arguments heap_new {_ _ _ _}.
Arguments heap_insert {_ _ _ _}.
Arguments heap_remove {_ _ _ _}.
Arguments heap_insert_cost {_ _ _ _}.
Arguments heap_remove_cost {_ _ _ _}.
Arguments is_min_heap {_ _ _ _}.
Arguments wp_heap_new {_ _ _ _}.
Arguments wp_heap_insert {_ _ _ _}.
Arguments wp_heap_remove {_ _ _ _}.

From clutch.prob_lang Require Import lang notation.
From clutch.tachis Require Export problang_wp.
Set Default Proof Using "Type*".

Record comparator (K : Type) (c : Costfun prob_lang) := Comparator {
  cmp :> val;
  cmp_rel : relation K;
  cmp_rel_dec :: RelDecision cmp_rel;
  cmp_rel_preorder :: PreOrder cmp_rel;
  cmp_rel_total :: Total cmp_rel;

  cmp_cost : R;

  cmp_nonneg : (0 <= cmp_cost)%R ;

  cmp_has_key `{!tachisGS Σ c} : K → val → iProp Σ;

  wp_cmp `{!tachisGS Σ c} k1 k2 v1 v2 :
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

  heap_insert_cost_nonneg n : (0 <= heap_insert_cost n)%R;
  heap_remove_cost_nonneg n : (0 <= heap_remove_cost n)%R;
  heap_insert_cost_mono n m :
    n ≤ m → (heap_insert_cost n <= heap_insert_cost m)%R;
  heap_remove_cost_mono n m :
    n ≤ m → (heap_remove_cost n <= heap_remove_cost m)%R;

  is_min_heap `{!tachisGS Σ c} (l : list K) (v : val) : iProp Σ;
  is_min_heap_proper `{!tachisGS Σ c} ::
    Proper ((≡ₚ) ==> (=) ==> (≡)) is_min_heap;

  wp_heap_new `{!tachisGS Σ c} :
    {{{ True }}}
      heap_new #()
    {{{ v, RET v; is_min_heap [] v }}};

  wp_heap_insert `{!tachisGS Σ c} l k v w :
    {{{ is_min_heap l v ∗ cmp.(cmp_has_key) k w ∗ ⧖ (heap_insert_cost (length l)) }}}
      heap_insert v w
    {{{ l', RET #(); is_min_heap l' v ∗ ⌜l' ≡ₚ k :: l⌝ }}};

  wp_heap_remove `{!tachisGS Σ c} l v :
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
Arguments is_min_heap {_ _ _ _ _ _}.
Arguments wp_heap_new {_ _ _ _ _ _}.
Arguments wp_heap_insert {_ _ _ _ _ _}.
Arguments wp_heap_remove {_ _ _ _ _ _}.

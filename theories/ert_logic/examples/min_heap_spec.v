From clutch.prob_lang Require Import lang notation.
From clutch.ert_logic Require Export problang_wp.
Set Default Proof Using "Type*".

Record comparator (K : Type) := Comparator {
  cmp :> val;
  cmp_rel : relation K;
  cmp_rel_dec :: RelDecision cmp_rel;
  cmp_rel_total :: TotalOrder cmp_rel;

  cmp_cost : R;

  cmp_has_key `{!ert_clutchGS Σ c} : K → val → iProp Σ;

  wp_cmp `{!ert_clutchGS Σ c} k1 k2 v1 v2 :
    {{{ cmp_has_key k1 v1 ∗ cmp_has_key k2 v2 ∗ ⧖ cmp_cost }}}
      cmp v1 v2
    {{{ RET #(bool_decide (cmp_rel k1 k2)); True }}};
}.

Arguments cmp_rel {_}.
Arguments cmp_cost {_}.
Arguments cmp_has_key {_ _ _ _ _}.
Arguments wp_cmp {_ _ _ _ _}.

Class min_heap := MinHeap {
  heap_new : val;
  heap_insert : val;
  heap_remove : val;

  heap_insert_cost : nat → R → R;
  heap_remove_cost : nat → R → R;

  is_min_heap `{!ert_clutchGS Σ c} {K} (cmp : comparator K) (l : list K) (v : val) : iProp Σ;

  wp_heap_new `{!ert_clutchGS Σ c} {K} (cmp : comparator K) :
    {{{ True }}}
      heap_new cmp
    {{{ v, RET v; is_min_heap cmp [] v }}};

  wp_heap_insert `{!ert_clutchGS Σ c} {K} (cmp : comparator K) l k v w :
    {{{ is_min_heap cmp l v ∗ cmp.(cmp_has_key) k w ∗ ⧖ (heap_insert_cost (length l) cmp.(cmp_cost)) }}}
      heap_insert v w
    {{{ v l', RET v; is_min_heap cmp l' v ∗ ⌜l' ≡ₚ k :: l⌝ }}};

  wp_heap_remove `{!ert_clutchGS Σ c} {K} (cmp : comparator K) l v :
    {{{ is_min_heap cmp l v ∗ ⧖ (heap_remove_cost (length l) cmp.(cmp_cost)) }}}
      heap_remove v
    {{{ w, RET w;
        (⌜w = #()⌝ ∗ ⌜l = []⌝ ∗ is_min_heap cmp [] v) ∨
        (∃ k l',
            ⌜k ∈ l⌝ ∗ ⌜l ≡ₚ k :: l'⌝ ∗ cmp.(cmp_has_key) k w ∗
            ⌜Forall (cmp.(cmp_rel) k) l⌝ ∗ is_min_heap cmp l' v) }}};
}.

From clutch.prob_lang Require Import lang notation.
From clutch.ert_logic Require Export problang_wp.
Set Default Proof Using "Type*".

Record comparator Σ c `{!ert_clutchGS Σ c} := Comparator {
  cmp :> val;
  cmp_key : Type;
  cmp_rel : relation cmp_key;
  cmp_rel_dec x y :: Decision (cmp_rel x y);
  cmpmp_rel_total :: TotalOrder cmp_rel;

  cmp_has_key : cmp_key → val → iProp Σ;

  wp_cmp (k1 k2 : cmp_key) (v1 v2 : val) :
    {{{ cmp_has_key k1 v1 ∗ cmp_has_key k2 v2 }}}
      cmp v1 v2
    {{{ RET #(bool_decide (cmp_rel k1 k2)); True }}};
}.
Arguments cmp {_ _ _ _}.
Arguments cmp_key {_ _ _ _}.
Arguments cmp_rel {_ _ _ _}.
Arguments cmp_has_key {_ _ _ _}.
Arguments wp_cmp {_ _ _ _}.

Record min_heap Σ c `{!ert_clutchGS Σ c} := MinHeap {
  heap_new : val;
  heap_insert : val;
  heap_remove : val;

  heap_insert_cost {cmp} : list (cmp.(cmp_key)) → R;
  heap_remove_cost {cmp} : list (cmp.(cmp_key)) → R;

  is_min_heap (cmp : comparator Σ c) (l : list cmp.(cmp_key)) (v : val) : iProp Σ;

  wp_heap_new c :
    {{{ True }}}
      heap_new c
    {{{ v, RET v; is_min_heap c [] v }}};

  wp_heap_insert c l k v w :
    {{{ is_min_heap c l v ∗ c.(cmp_has_key) k w ∗ ⧖ (heap_insert_cost l) }}}
      heap_insert v w
    {{{ v l', RET v; is_min_heap c l' v ∗ ⌜l' ≡ₚ k :: l⌝ }}};

  wp_heap_remove c l v :
    {{{ is_min_heap c l v ∗ ⧖ (heap_remove_cost l) }}}
      heap_remove v
    {{{ w, RET w;
        (⌜w = #()⌝ ∗ ⌜l = []⌝ ∗ is_min_heap c [] v) ∨
        (∃ k l',
            ⌜k ∈ l⌝ ∗ ⌜l ≡ₚ k :: l'⌝ ∗ c.(cmp_has_key) k w ∗
            ⌜Forall (c.(cmp_rel) k) l⌝ ∗ is_min_heap c l' v) }}};
}.

From stdpp Require Import sorting.
From iris.proofmode Require Export proofmode.
From clutch.ert_logic Require Export problang_wp proofmode derived_laws ert_rules cost_models.
From clutch.ert_logic.examples Require Import lib.list min_heap_spec.
Set Default Proof Using "Type*".

Global Instance : Trichotomy (strict Z.le).
Proof.
  intros ??.
  destruct (decide (x = y)); [firstorder|].
  destruct (decide (Z.le x y)).
  - left. split; lia.
  - right; right. split; lia.
Qed.

Global Instance : TotalOrder Z.le. Proof. constructor; apply _. Qed.

(** * A [≤] head comparator for lists of intergers *)
Definition cmp_Z_list : val :=
  λ: "zs1" "zs2",
    let: "h1" := list_head "zs1" in
    let: "h2" := list_head "zs2" in
    match: "h1" with
    | NONE => #true
    | SOME "z1" =>
        match: "h2" with
        | NONE => #false
        | SOME "z2" => "z1" ≤ "z2"
        end
    end.

Section Z_comparator_spec.
  Context `{!ert_clutchGS Σ CostTick}.

  Definition is_Z_list (z : Z) (v : val) : iProp Σ := ∃ zs, ⌜is_list (z :: zs) v⌝.

  Lemma wp_cmp_Z_list z1 z2 v1 v2 :
    {{{ is_Z_list z1 v1 ∗ is_Z_list z2 v2 }}}
      cmp_Z_list v1 v2
    {{{ RET #(bool_decide (z1 ≤ z2)); is_Z_list z1 v1 ∗ is_Z_list z2 v2 }}}.
  Proof.
    iIntros (?) "[[%zs1 %H1] [%zs2 %H2]] H".
    wp_rec. wp_pures.
    wp_apply (wp_list_head _ _ (z1 :: _) with "[//]").
    iIntros (v) "[[% %] | (% & % & % & %)]"; [done|]; simplify_eq.
    wp_pures.
    wp_apply (wp_list_head _ _ (z2 :: _) with "[//]").
    iIntros (v) "[[% %] | (% & % & % & %)]"; [done|]; simplify_eq.
    wp_pures.
    iApply "H".
    iModIntro.
    iSplit; by iExists _.
  Qed.

End Z_comparator_spec.

Program Definition Z_loc_comparator : comparator Z CostTick :=
  {| cmp := cmp_Z_list;
     cmp_rel := Z.le;
     cmp_cost := 0%R;
     cmp_has_key _ _ := is_Z_list;
     wp_cmp := _;
  |}.
Next Obligation.
  iIntros (???????) "(Hzs1 & Hzs2 & _) H".
  by wp_apply (wp_cmp_Z_list with "[$Hzs1 $Hzs2]").
Qed.

Section kway_merge.
  Context `{min_heap c}.

  Definition repeat_remove : val :=
    rec: "repeat_remove" "h" "out" :=
      match: heap_remove "h" with
      | NONE => #()
      | SOME "zs" =>
          match: list_head "zs" with
          | NONE => "repeat_remove" "h" "out"
          | SOME "h" =>
              "out" <- list_cons "h" !"out";;
              heap_insert "h" (list_tail "zs");;
              "repeat_remove" "h" "out"
          end
      end.

  Definition merge : val :=
    λ: "zss",
      let: "h" := heap_new #() in
      list_iter (heap_insert "h") "zss";;
      let: "out" := ref list_nil in
      repeat_remove "h" "out";;
      list_rev !"out".

End kway_merge.

Section kway_merge_spec.
  Context `{!ert_clutchGS Σ CostTick} `{!min_heap Z_loc_comparator}.

  Definition merge_cost (zss : list (list Z)) : R :=
    let len := length zss in
    let total := sum_list_with length zss in
    (** initial insertion  *)
    len * heap_insert_cost len +
    (** loop  *)
    (total + len) * heap_remove_cost len +
    total * heap_insert_cost len.

  Lemma wp_merge (v : val) (zss : list (list Z)) :
    is_list zss v →
    Forall (λ zs, is_list zs (inject zs) ∧ Sorted Z.le zs) zss →
    {{{ ⧖ (merge_cost zss) }}}
      merge v
    {{{ v zs, RET v; ⌜is_list zs v⌝ ∗ ⌜zs ≡ₚ concat zss⌝ ∗ ⌜Sorted Z.le zs⌝ }}}.
  Proof.
    Admitted.

End kway_merge_spec.

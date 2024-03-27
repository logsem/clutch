From stdpp Require Import sorting.
From iris.proofmode Require Export proofmode.
From clutch.ert_logic Require Export problang_wp proofmode derived_laws ert_rules cost_models.
From clutch.ert_logic.examples Require Import lib.list min_heap_spec.
Set Default Proof Using "Type*".

(** * A [≤] head comparator for lists of intergers *)
Definition list_Z_le : relation (list Z) :=
  λ zs1 zs2,
    match zs1, zs2 with
    | [], _ => True
    | _, [] => False
    | z1 :: _, z2 :: _ => (z1 ≤ z2)%Z
    end.

Global Instance : RelDecision list_Z_le.
Proof. intros [] []; firstorder. simpl. apply _. Qed.

Global Instance : PreOrder list_Z_le.
Proof.
  constructor.
  - intros []; by simpl.
  - intros [] [] []; firstorder.
    simpl in *. by etrans.
Qed.

Definition cmp_Z_list : val :=
  λ: "zs1" "zs2",
    let: "h1" := list_head "zs1" in
    match: "h1" with
    | NONE => #true
    | SOME "z1" =>
        let: "h2" := list_head "zs2" in
        match: "h2" with
        | NONE => #false
        | SOME "z2" => "z1" ≤ "z2"
        end
    end.

Section Z_comparator_spec.
  Context `{!ert_clutchGS Σ CostTick}.

  Definition is_Z_list (zs : list Z) (v : val) : iProp Σ := ⌜is_list zs v⌝.

  Lemma wp_cmp_Z_list zs1 zs2 v1 v2 :
    {{{ is_Z_list zs1 v1 ∗ is_Z_list zs2 v2 }}}
      cmp_Z_list v1 v2
    {{{ RET #(bool_decide (list_Z_le zs1 zs2)); is_Z_list zs1 v1 ∗ is_Z_list zs2 v2 }}}.
  Proof.
    iIntros (?) "[%Hzs1 %Hzs2] H".
    wp_rec. wp_pures.
    wp_apply (wp_list_head _ _ zs1 with "[//]").
    iIntros (v) "[[-> ->] | (%z1 & %zs1' & -> & ->)]".
    { wp_pures. rewrite bool_decide_eq_true_2 //. by iApply "H". }
    wp_pures.
    wp_apply (wp_list_head _ _ zs2 with "[//]").
    iIntros (v) "[[-> ->] | (%z2 & %zs2' & -> & ->)]".
    { wp_pures. rewrite bool_decide_eq_false_2 /=; auto. by iApply "H". }
    wp_pures.
    simpl.
    iModIntro.
    iSpecialize ("H" with "[//]").
    destruct (decide (z1 ≤ z2)%Z).
    { do 2 (rewrite bool_decide_eq_true_2 //). }
    do 2 (rewrite bool_decide_eq_false_2 //).
  Qed.

End Z_comparator_spec.

Program Definition Z_list_comparator : comparator (list Z) CostTick :=
  {| cmp := cmp_Z_list;
     cmp_rel := list_Z_le;
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
      list_iter (λ: "zs", heap_insert "h" "zs") "zss";;
      let: "out" := ref list_nil in
      repeat_remove "h" "out";;
      list_rev !"out".

End kway_merge.

Section kway_merge_spec.
  Context `{!ert_clutchGS Σ CostTick} `{!min_heap Z_list_comparator}.

  Local Hint Resolve heap_insert_cost_nonneg : core.
  Local Hint Resolve heap_remove_cost_nonneg : core.

  (** We give a rough bound by requiring, e.g., [len * (heap_insert_cost len)] credits even though,
      in reality, only

        [heap_insert_cost 0 + heap_insert_cost 1 + ... + heap_insert_cost len]

      should be necessary. *)
  Definition repeat_remove_cost (zss : list (list Z)) : R :=
    let len := length zss in
    let total := sum_list_with length zss in
    (** A list is removed from the heap for all elements + an extra removal for the empty lists *)
    (total + len) * heap_remove_cost len +
    (** A list is inserted for all elements, (except the initial head elements which are inserted as
        part of [merge] so we should in theory subtract [len] from [total]. *)
    total * heap_insert_cost len.

  Definition merge_cost (zss : list (list Z)) : R :=
    let len := length zss in
    len * heap_insert_cost len + repeat_remove_cost zss.


  Lemma repeat_remove_cost_nonneg zss :
    (0 <= repeat_remove_cost zss)%R.
  Proof.
    rewrite /repeat_remove_cost.
  Admitted.

  Local Hint Resolve repeat_remove_cost_nonneg : core.

  Lemma wp_repeat_remove h out (zss : list (list Z)) v :
    is_list zss v →
    Forall (Sorted Z.le) zss →
    {{{ ⧖ (repeat_remove_cost zss) ∗ is_min_heap zss h ∗ out ↦ NONEV }}}
      repeat_remove h #out
    {{{ zs v, RET #();
        is_min_heap [] h ∗ out ↦ inject zs ∗
        ⌜is_list zs v⌝ ∗ ⌜zs ≡ₚ concat zss⌝ ∗ ⌜Sorted (flip Z.le) zs⌝}}}.
  Proof.
    Admitted.


  Lemma wp_merge (v : val) (zss : list (list Z)) :
    is_list zss v →
    Forall (Sorted Z.le) zss →
    {{{ ⧖ (merge_cost zss) }}}
      merge v
    {{{ v zs, RET v; ⌜is_list zs v⌝ ∗ ⌜zs ≡ₚ concat zss⌝ ∗ ⌜Sorted Z.le zs⌝ }}}.
  Proof.
    iIntros (Hv Hzss Ψ) "Hc HΨ".
    rewrite /merge_cost.
    iDestruct (etc_split with "Hc") as "[Hinit Hc]".
    { assert (0 <= length zss)%R by eauto with real. real_solver. }
    { auto. }
    wp_rec.
    wp_apply wp_heap_new; [done|].
    iIntros (h) "Hh"; wp_pures.
    rewrite etc_split_list; [|apply heap_insert_cost_nonneg].
    wp_apply (wp_list_iter_invariant (λ _, ⧖ (heap_insert_cost (length zss))) (λ _, True)
                (λ l, is_min_heap l h) True with "[] [$Hh $Hinit //]")%I.
    { iIntros (l l' Ψ') "!# ([% ->] & _ & Hh & Hc) HΨ'".
      rewrite app_length /=.
      (** Here we possibly throw away some credits *)
      iDestruct (etc_weaken _ (heap_insert_cost (length l')) with "Hc") as "Hc".
      { split; [auto|]. apply heap_insert_cost_mono. lia. }
      wp_pures.
      wp_apply (wp_heap_insert _ l with "[$Hh $Hc]").
      { rewrite /= /is_Z_list is_list_inject //. }
      iIntros (zss') "[Hh ->]".
      iApply "HΨ'".
      rewrite Permutation_cons_append.
      iFrame. }
    iIntros "(_ & Hh & _)".
    wp_pures.
    wp_alloc out as "Hout".
    wp_pures.
    wp_apply (wp_repeat_remove with "[$Hc $Hh $Hout]"); [done|done|].
    iIntros (zs w) "(Hh & Hout & %Hzs & %Hp & %Hsorted)".
    wp_pures.
    wp_load; iIntros "Hout".
    wp_apply (wp_list_rev _ _ zs with "[]").
    { rewrite is_list_inject //. }
    iIntros (u Hu) .
    iApply "HΨ".
    iFrame "%".
    iSplit; iPureIntro.
    { rewrite reverse_Permutation //. }
    by apply Sorted_reverse in Hsorted.
  Qed.

End kway_merge_spec.

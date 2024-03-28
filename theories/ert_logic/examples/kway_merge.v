From Coquelicot Require Import Hierarchy.
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

  Definition is_Z_list (zs : list Z) (v : val) : iProp Σ := ⌜is_list zs v⌝ ∗ ⌜Sorted Z.le zs⌝.

  Lemma wp_cmp_Z_list zs1 zs2 v1 v2 :
    {{{ is_Z_list zs1 v1 ∗ is_Z_list zs2 v2 }}}
      cmp_Z_list v1 v2
    {{{ RET #(bool_decide (list_Z_le zs1 zs2)); is_Z_list zs1 v1 ∗ is_Z_list zs2 v2 }}}.
  Proof.
    iIntros (?) "[[%Hzs1 %] [%Hzs2 %]] H".
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

(* TODO: move *)
Section list_length_ind.
  Variable A : Type.
  Variable P : list A -> Prop.

  Hypothesis H : ∀ xs, (∀ l, length l < length xs -> P l) -> P xs.

  Theorem list_length_ind : ∀ xs, P xs.
  Proof.
    assert (∀ xs l : list A, length l <= length xs → P l) as H_ind.
    { induction xs; intros l Hlen; apply H; intros l0 H0.
      - destruct l, l0; simpl in *; lia.
      - apply IHxs. simpl in Hlen. lia. }
    intros xs.
    by eapply H_ind.
  Qed.
End list_length_ind.

Open Scope R.

Program Definition Z_list_comparator : comparator (list Z) CostTick :=
  {| cmp := cmp_Z_list;
     cmp_rel := list_Z_le;
     cmp_cost := 0;
     cmp_has_key _ _ := is_Z_list;
     wp_cmp := _;
  |}.
Next Obligation. lra. Qed.
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

(* TODO: move *)
Definition sum_seq (f : nat → R) (n m : nat) :=
  foldr (Rplus ∘ f) 0 (seq n m).

Lemma sum_seq_S (f : nat → R) (n m : nat) :
  sum_seq f n (S m) = sum_seq f n m + f (n + m)%nat.
Proof.
  rewrite /sum_seq.
  rewrite seq_S.
  rewrite foldr_app /=.
  rewrite foldr_comm_acc_strong; [lra|].
  intros ??? =>/=. lra.
Qed.

Lemma sum_seq_nonneg f n m:
  (∀ n, 0 <= f n) →
  0 <= sum_seq f n m.
Proof. Admitted.

Local Hint Resolve sum_seq_nonneg : core.

Section kway_merge_spec.
  Context `{!ert_clutchGS Σ CostTick} `{!min_heap Z_list_comparator}.

  Local Hint Resolve heap_insert_cost_nonneg : core.
  Local Hint Resolve heap_remove_cost_nonneg : core.

  Definition repeat_remove_cost (zss : list (list Z)) : R :=
    sum_seq heap_remove_cost 0 (S (length zss)) +
    sum_seq heap_insert_cost 0 (length zss).

  Lemma repeat_remove_cost_nonneg zss :
    0 <= repeat_remove_cost zss.
  Proof.
    rewrite /repeat_remove_cost.
  Admitted.

  Lemma repeat_remove_cost_length zss1 zss2 :
    length zss1 = length zss2 →
    repeat_remove_cost zss1 = repeat_remove_cost zss2.
  Proof. rewrite /repeat_remove_cost. by intros ->. Qed.

  Local Hint Resolve Rplus_le_le_0_compat : core.

  Lemma repeat_remove_cost_cons zs zss :
    ⧖ (repeat_remove_cost (zs :: zss)) ⊢
      ⧖ (heap_remove_cost (S (length zss))) ∗
      ⧖ (heap_insert_cost (length zss)) ∗ ⧖ (repeat_remove_cost zss).
  Proof.
    rewrite {1}/repeat_remove_cost.
    rewrite cons_length.
    rewrite (sum_seq_S heap_remove_cost) Nat.add_0_l.
    do 2 (rewrite etc_split; [|auto..]).
    rewrite -!assoc.
    rewrite (sum_seq_S heap_insert_cost) Nat.add_0_l.
    rewrite etc_split; [|auto..].
    iIntros "(H1 & $ & H2 & $)".
    iCombine "H1 H2" as "H".
    rewrite /repeat_remove_cost //.
  Qed.

  Local Hint Resolve repeat_remove_cost_nonneg : core.

  Local Lemma wp_repeat_remove_aux (zss : list (list Z)) zs0 h out :
    Forall (Sorted Z.le) zss →
    Sorted (flip Z.le) zs0 →
    (∀ z, z ∈ zs0 → Forall (Z.le z) (concat zss)) →
    {{{ ⧖ (repeat_remove_cost zss) ∗ is_min_heap zss h ∗ out ↦ inject zs0 }}}
      repeat_remove h #out
    {{{ zs', RET #();
        is_min_heap [] h ∗ out ↦ inject (zs0 ++ zs') ∗
          (* TODO: the permutation is not true if [zs'] contains empty lists! *)
        ⌜zs' ≡ₚ concat zss⌝ ∗ ⌜Sorted (flip Z.le) (zs0 ++ zs')⌝}}}.
  Proof.
    iIntros (Hzss Hzs0 Hle Ψ) "(Hc & Hh & Hout) HΨ".
    iInduction (zss) as [] "IH" using list_length_ind forall (zs0 Hle Hzss Hzs0).
    destruct zss.
    - wp_rec; wp_pures.
      wp_apply (wp_heap_remove with "[$Hh Hc]").
      { rewrite /repeat_remove_cost sum_seq_S /=.
        iApply (etc_irrel with "Hc"). cbn. lra. }
      iIntros (?) "[(-> & % & Hh) | (% & % & % & % & % & H)]";
        [|exfalso; by eapply Permutation_nil_cons].
      wp_pures.
      iApply ("HΨ" $! []). rewrite app_nil_r. by iFrame.
    - wp_rec; wp_pures.
      iDestruct (repeat_remove_cost_cons with "Hc") as "(Hr & Hi & Hzss)".
      wp_apply (wp_heap_remove with "[$Hh $Hr]").
      iIntros (w) "[(_ & % & _) | (%zs' & %u & %zss' & -> & %Hp & [%Hu %] & %Hs & Hh)]";
        simplify_eq/=.
      wp_pures.
      wp_apply (wp_list_head with "[//]").
      iIntros (w) "[[-> ->] | (% & % & -> & ->)]".
      + wp_pures.
        assert (length zss = length zss').
        { by apply Permutation_length in Hp as [=]. }
        rewrite (repeat_remove_cost_length _ zss') //.
        wp_apply ("IH" with "[] [] [] [] Hzss Hh Hout").
        { iPureIntro. lia. }
        { admit. }
        { admit. }
        { done. }
        iIntros (?) "(? & ?& %Heqp & %)".
        iApply "HΨ". iFrame. iSplit; [|done].
        iPureIntro.
        rewrite Heqp.
  Admitted.

  Lemma wp_repeat_remove h out (zss : list (list Z)) :
    Forall (Sorted Z.le) zss →
    {{{ ⧖ (repeat_remove_cost zss) ∗ is_min_heap zss h ∗ out ↦ NONEV }}}
      repeat_remove h #out
    {{{ zs, RET #();
        is_min_heap [] h ∗ out ↦ inject zs ∗
        ⌜zs ≡ₚ concat zss⌝ ∗ ⌜Sorted (flip Z.le) zs⌝}}}.
  Proof.
    iIntros (??) "(?&?&?) H".
    wp_apply (wp_repeat_remove_aux _ [] with "[$]"); [done|done| |done].
    set_solver.
  Qed.

  Definition merge_cost (zss : list (list Z)) : R :=
    sum_seq heap_insert_cost 0 (length zss) + repeat_remove_cost zss.

  Lemma etc_split_sum_seq {A} f (xs : list A) :
    (∀ n, 0 <= f n) →
    ⧖ (sum_seq f 0 (length xs)) ⊢ [∗ list] i ↦ _ ∈ xs, ⧖ (f i).
  Proof.
    iIntros (Hf).
    iInduction xs as [|x xs] "IH" using rev_ind; [auto|].
    rewrite app_length /=.
    rewrite Nat.add_1_r sum_seq_S.
    rewrite /Hierarchy.plus /=.
    rewrite etc_split; [|auto..].
    rewrite big_sepL_snoc.
    iIntros "[? $]".
    by iApply "IH".
  Qed.

  Lemma wp_merge (v : val) (zss : list (list Z)) :
    is_list zss v →
    Forall (Sorted Z.le) zss →
    {{{ ⧖ (merge_cost zss) }}}
      merge v
    {{{ v zs, RET v; ⌜is_list zs v⌝ ∗ ⌜zs ≡ₚ concat zss⌝ ∗ ⌜Sorted Z.le zs⌝ }}}.
  Proof.
    iIntros (Hv Hzss Ψ) "Hc HΨ".
    rewrite /merge_cost.
    iDestruct (etc_split with "Hc") as "[Hinit Hc]"; [auto..|].
    wp_rec.
    wp_apply wp_heap_new; [done|].
    iIntros (h) "Hh"; wp_pures.
    rewrite etc_split_sum_seq; [|auto].
    wp_apply (wp_list_iter_invariant (λ n _, ⧖ (heap_insert_cost n)) (λ _ _, True)
                (λ l, is_min_heap l h) True with "[] [$Hh $Hinit //]")%I.
    { iIntros (l l' Ψ') "!# ([% ->] & _ & Hh & Hc) HΨ'".
      wp_pures.
      wp_apply (wp_heap_insert _ l with "[$Hh $Hc]").
      { rewrite /= /is_Z_list is_list_inject. iSplit; [done|].
        by apply Forall_app in Hzss as [_ [? ?]%Forall_cons]. }
      iIntros (zss') "[Hh ->]".
      iApply "HΨ'".
      rewrite Permutation_cons_append.
      iFrame. }
    iIntros "(_ & Hh & _)".
    wp_pures.
    wp_alloc out as "Hout".
    wp_pures.
    wp_apply (wp_repeat_remove with "[$Hc $Hh $Hout]"); [done|].
    iIntros (zs) "(Hh & Hout & %Hp & %Hsorted)".
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

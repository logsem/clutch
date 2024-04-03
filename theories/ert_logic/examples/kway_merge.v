From Coquelicot Require Import Hierarchy.
From stdpp Require Import sorting.
From iris.proofmode Require Export proofmode.
From clutch.ert_logic Require Export problang_wp proofmode derived_laws ert_rules cost_models.
From clutch.ert_logic.examples Require Import lib.list min_heap_spec.
Set Default Proof Using "Type*".

Open Scope R.

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

Global Instance : Total list_Z_le.
Proof. intros [] [] => /=; firstorder. lia. Qed.

Definition cmp_Z_list : val :=
  λ: "zs1" "zs2",
    tick #1;;
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
    {{{ is_Z_list zs1 v1 ∗ is_Z_list zs2 v2 ∗ ⧖ 1 }}}
      cmp_Z_list v1 v2
    {{{ RET #(bool_decide (list_Z_le zs1 zs2)); is_Z_list zs1 v1 ∗ is_Z_list zs2 v2 }}}.
  Proof.
    iIntros (?) "([%Hzs1 %] & [%Hzs2 %] & Hc) H".
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
     cmp_cost := 1;
     cmp_has_key _ _ := is_Z_list;
     wp_cmp := _;
  |}.
Next Obligation. lra. Qed.
Next Obligation.
  iIntros (???????) "(Hzs1 & Hzs2 & Hc) H".
  by wp_apply (wp_cmp_Z_list with "[$Hzs1 $Hzs2 $Hc]").
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
          | SOME "z" =>
              "out" <- list_cons "z" !"out";;
              let: "tl" := list_tail "zs" in
              let: "empty" := list_is_empty "tl" in
              (if: ~ "empty" then heap_insert "h" "tl" else #());;
              "repeat_remove" "h" "out"
          end
      end.

  Definition merge : val :=
    λ: "zss",
      let: "h" := heap_new #() in
      list_iter (λ: "zs",
          let: "empty" := list_is_empty "zs" in
          if: ~ "empty" then heap_insert "h" "zs" else #()) "zss";;
      let: "out" := ref list_nil in
      repeat_remove "h" "out";;
      list_rev !"out".

End kway_merge.

Section kway_merge_spec.
  Context `{!ert_clutchGS Σ CostTick} `{!min_heap Z_list_comparator}.

  Local Hint Resolve heap_insert_cost_nonneg : real.
  Local Hint Resolve heap_remove_cost_nonneg : real.
  Local Hint Resolve Rmult_le_pos Rplus_le_le_0_compat : real.
  Local Hint Resolve Rle_plus_plus : real.

  Definition repeat_remove_cost (zss : list (list Z)) : R :=
    length (concat zss) * heap_remove_cost (length zss) +
    length (concat zss) * heap_insert_cost (length zss) +
    heap_remove_cost 0.

  Lemma repeat_remove_cost_nonneg zss :
    0 <= repeat_remove_cost zss.
  Proof.
    rewrite /repeat_remove_cost.
    eauto 10 with real.
  Qed.

  Local Hint Resolve repeat_remove_cost_nonneg : real.

  Global Instance repeat_remove_cost_proper :
    Proper ((≡ₚ) ==> (=)) repeat_remove_cost.
  Proof.
    rewrite /repeat_remove_cost.
    intros ?? Hp.
    rewrite Hp //.
  Qed.

  Lemma repeat_remove_cost_nil zss :
    length zss = 0%nat →
    repeat_remove_cost zss = heap_remove_cost 0.
  Proof.
    intros ->%nil_length_inv.
    rewrite /repeat_remove_cost /=.
    lra.
  Qed.

  Lemma length_inv_not_zero {A} (xs : list A) :
    length xs ≠ 0%nat → ∃ a, a ∈ xs.
  Proof.
    destruct xs; [done|].
    intros _. eexists. by left.
  Qed.

  Lemma length_pos {A} (xs : list A) :
    0 <= length xs.
  Proof.
    induction xs; [done|].
    rewrite cons_length S_INR. lra.
  Qed.

  Lemma list_list_non_empty {A} (zss : list (list A)) :
    length zss ≠ 0%nat →
    Forall (λ zs, length zs ≠ 0%nat) zss →
    length (concat zss) ≠ 0%nat.
  Proof.
    intros [zs [zss' Hzss]%elem_of_Permutation]%length_inv_not_zero.
    setoid_rewrite Hzss.
    intros [[z [zs' Hzs]%elem_of_Permutation]%length_inv_not_zero _]%Forall_cons.
    rewrite /= Hzs /=. lia.
  Qed.

  Local Hint Resolve length_pos : real.

  Lemma etc_repeat_remove_cost_split zss :
    Forall (λ zs, length zs ≠ 0%nat) zss →
    length zss ≠ 0%nat →
    ⧖ (repeat_remove_cost zss) ⊢
      ⧖ (heap_remove_cost (length zss)) ∗
      ⧖ (heap_insert_cost (length zss)) ∗
      ⧖ (repeat_remove_cost zss
           - heap_remove_cost (length zss)
           - heap_insert_cost (length zss)).
  Proof.
    intros Hzs Hzss.
    rewrite /repeat_remove_cost.
    destruct (length (concat zss)) eqn:Heq.
    { pose proof (list_list_non_empty _ Hzss Hzs). lia. }
    do 2 (rewrite etc_split; eauto 10 with real).
    rewrite -!bi.sep_assoc.
    iIntros "(Hr & Hi & H0)".
    rewrite S_INR !Rmult_plus_distr_r !Rmult_1_l.
    iDestruct (etc_split with "Hr") as "[Hr $]"; auto with real.
    iDestruct (etc_split with "Hi") as "[Hi $]"; auto with real.
    iCombine "Hr Hi H0" as "H".
    iApply (etc_irrel with "H").
    lra.
  Qed.

  Local Lemma wp_repeat_remove_aux (zss : list (list Z)) zs0 h out :
    Forall (Sorted Z.le) zss →
    Sorted (flip Z.le) zs0 →
    Forall (λ zs, length zs ≠ 0%nat) zss →
    Forall (λ z, Forall (Z.le z) (concat zss)) zs0 →
    {{{ ⧖ (repeat_remove_cost zss) ∗ is_min_heap zss h ∗ out ↦ inject zs0 }}}
      repeat_remove h #out
    {{{ zs', RET #();
          is_min_heap [] h ∗ out ↦ inject (zs' ++ zs0) ∗
          ⌜zs' ≡ₚ concat zss⌝ ∗ ⌜Sorted (flip Z.le) (zs' ++ zs0)⌝}}}.
  Proof.
    iIntros (Hzss Hzs0 Hne Hle Ψ) "(Hc & Hh & Hout) HΨ".
    iLöb as "IH" forall (zss zs0 Hzss Hzs0 Hne Hle Ψ) "Hc Hh Hout HΨ".
    wp_rec; wp_pures.
    destruct (length zss) eqn:Hlen.
    - rewrite repeat_remove_cost_nil //.
      wp_apply (wp_heap_remove with "[$Hh Hc]").
      { rewrite Hlen //. }
      iIntros (?) "[(-> & -> & Hh) | (% & % & % & % & %Hp & H)]"; last first.
      { rewrite Hp /= in Hlen. lia. }
      wp_pures.
      iApply ("HΨ" $! []). rewrite app_nil_l /=. by iFrame.
    - iDestruct (etc_repeat_remove_cost_split with "Hc") as "(Hr & Hi & Hrest)"; [done|lia|].
      wp_apply (wp_heap_remove with "[$Hh $Hr]").
      iIntros (w) "[(_ & % & _) | (%zs' & %u & %zss' & -> & %Hp & [%Hu %HuS] & %Hs & Hh)]";
        simplify_eq.
      wp_pures.
      wp_apply (wp_list_head with "[//]").
      iIntros (w) "[[-> ->] | (%z & %zs'' & -> & ->)]".
      { rewrite Hp Forall_cons in Hne. by destruct Hne. }
      wp_pures.
      wp_load; iIntros "Hout".
      wp_apply (wp_list_cons z zs0).
      { rewrite is_list_inject //. }
      iIntros (r Hr).
      wp_store; iIntros "Hout".
      wp_pures.
      wp_apply (wp_list_tail _ _ (z :: zs'') with "[//]"); simpl.
      iIntros (w Hw).
      wp_pures.
      wp_apply (wp_list_is_empty with "[//]"); iIntros "_".
      wp_pures.
      destruct zs'' as [|z'' zs'']; wp_pures.
      + apply is_list_inject in Hr as ->.
        wp_apply ("IH" $! zss' (z :: zs0) with "[] [] [] [] [Hrest] Hh Hout").
        { iPureIntro. rewrite Hp Forall_cons in Hzss. by destruct Hzss. }
        { iPureIntro.  constructor; [done|].
          (* TODO: extract to a separate lemma *)
          destruct zs0; [done|]. constructor.
          rewrite Forall_cons in Hle; destruct Hle as [Hle _].
          setoid_rewrite Hp in Hle.
          setoid_rewrite Forall_concat in Hle.
          rewrite Forall_cons in Hle; destruct Hle as [Hle _].
          rewrite Forall_cons in Hle. by destruct Hle. }
        { iPureIntro. rewrite Hp Forall_cons in Hne. by destruct Hne. }
        { iPureIntro.
          (* TODO: extract to a separate lemma *)
          rewrite Hp in Hzss Hs.
          setoid_rewrite Hp in Hle; clear Hlen Hp zss Hne.
          apply Forall_cons in Hs as [_ Hs].
          apply Forall_cons.
          split.
          - apply Forall_cons in Hzss as [Hzss' Hzss'S].
            eapply Sorted_extends in Hzss'; [|intros ?????; by etrans].
            apply Forall_concat, Forall_forall.
            intros ys Hys.
            rewrite Forall_forall in Hs.
            destruct ys; [done|].
            rewrite Forall_cons.
            pose proof (Hs _ Hys).
            split; [done|].
            rewrite Forall_forall in Hzss'S.
            specialize (Hzss'S _ Hys).
            eapply Sorted_extends in Hzss'S; [|intros ?????; by etrans].
            simpl in Hzss'.
            specialize (Hs _ Hys).
            simpl in Hs.
            eapply Forall_impl; [done|].
            intros ??. by etrans.
          - setoid_rewrite Forall_cons in Hle.
            eapply Forall_impl; [done|]. by intros ? []. }
        { iApply (etc_weaken with "Hrest").
          split; [auto with real|].
          rewrite Hp cons_length.
          rewrite {2}/repeat_remove_cost.
          rewrite concat_cons app_length !cons_length nil_length.
          rewrite plus_INR !Rmult_plus_distr_r !Rmult_1_l.
          rewrite /repeat_remove_cost.

          assert (heap_remove_cost (length zss') <= heap_remove_cost (S (length zss'))).
          { apply heap_remove_cost_mono. lia. }
          assert (heap_insert_cost (length zss') <= heap_insert_cost (S (length zss'))).
          { apply heap_insert_cost_mono. lia. }

          remember (heap_remove_cost (length zss')) as R.
          remember (heap_insert_cost (length zss')) as I.
          remember (heap_remove_cost (S (length zss'))) as RS.
          remember (heap_insert_cost (S (length zss'))) as IS.

          transitivity
            (length (concat zss') * RS +
             length (concat zss') * IS + heap_remove_cost 0); [|lra].
          eauto 10 with real. }
        iIntros (zs') "(Hh & Hout & %Hp' & %Hs')".
        assert ((zs' ++ z :: zs0) = (zs' ++ [z]) ++ zs0) as ->.
        { rewrite -app_assoc //. }
        iApply ("HΨ" with "[$Hh $Hout]").
        rewrite -app_assoc.
        iSplit; [|done].
        iPureIntro. rewrite Hp' Hp Permutation_app_comm //.
      + remember (z'' :: zs'') as zs'.
        wp_apply (wp_heap_insert _ zs' with "[$Hh Hi]").
        { iSplit.
          * iSplit; [done|]. by inversion HuS.
          * iApply (etc_weaken with "Hi"). split; [auto with real|].
            rewrite Hp. apply heap_insert_cost_mono => /=. lia. }
        iIntros (zss'') "(Hh & %Hp')".
        wp_pures.
        apply is_list_inject in Hr as ->.
        wp_apply ("IH" $! _ (z :: zs0) with "[] [] [] [] [Hrest] Hh Hout").
        { iPureIntro.
          rewrite Hp' Forall_cons.
          inversion HuS; subst.
          split; [done|].
          rewrite Hp Forall_cons in Hzss.
          by destruct Hzss. }
        { iPureIntro.  constructor; [done|].
          destruct zs0; [done|]. constructor.
          rewrite Forall_cons in Hle; destruct Hle as [Hle _].
          setoid_rewrite Hp in Hle.
          setoid_rewrite Forall_concat in Hle.
          rewrite Forall_cons in Hle; destruct Hle as [Hle _].
          rewrite Forall_cons in Hle. by destruct Hle. }
        { iPureIntro.
          rewrite Hp Forall_cons in Hne. destruct Hne.
          rewrite Hp' Forall_cons. split; [|done].
          rewrite Heqzs' //. }
        { iPureIntro.
          rewrite Hp in Hzss Hs.
          setoid_rewrite Hp in Hle; clear Hlen Hne Hp zss.
          setoid_rewrite Hp'; clear Hp' zss''.
          apply Forall_cons in Hs as [_ Hs].
          apply Forall_cons.
          split.
          * rewrite concat_cons. apply Forall_app.
            apply Forall_cons in Hzss as [Hzss' Hzss'S].
            eapply Sorted_extends in Hzss'; [|intros ?????; by etrans].
            split; [done|].
            apply Forall_concat, Forall_forall.
            intros ys Hys.
            rewrite Forall_forall in Hs.
            destruct ys; [done|].
            rewrite Forall_cons.
            pose proof (Hs _ Hys).
            split; [done|].
            rewrite Forall_forall in Hzss'S.
            specialize (Hzss'S _ Hys).
            eapply Sorted_extends in Hzss'S; [|intros ?????; by etrans].
            simpl in Hzss'.
            specialize (Hs _ Hys).
            simpl in Hs.
            eapply Forall_impl; [done|].
            intros ??. by etrans.
          * rewrite /= -concat_cons in Hle.
            setoid_rewrite Forall_cons in Hle.
            eapply Forall_impl; [done|]. by intros ? []. }
        { iApply (etc_irrel with "Hrest").
          rewrite Hp Hp'.
          rewrite /repeat_remove_cost.
          rewrite !concat_cons !app_length !cons_length.
          rewrite !plus_INR !S_INR.
          remember (heap_remove_cost (S (length zss'))) as R.
          remember (heap_insert_cost (S (length zss'))) as I.
          lra. }
      iIntros (zs''') "(Hh & Hout & %Hp'' & %HS)".
      assert ((zs''' ++ z :: zs0) = (zs''' ++ [z]) ++ zs0) as ->.
      { rewrite -app_assoc //. }
      iApply "HΨ".
      iFrame.
      rewrite -app_assoc /=.
      iSplit; [|done].
      iPureIntro.
      rewrite Hp Hp'' Hp'.
      rewrite Permutation_app_comm //.
  Qed.

  Lemma wp_repeat_remove h out (zss : list (list Z)) :
    Forall (Sorted Z.le) zss →
    Forall (λ zs, length zs ≠ 0%nat) zss →
    {{{ ⧖ (repeat_remove_cost zss) ∗ is_min_heap zss h ∗ out ↦ NONEV }}}
      repeat_remove h #out
    {{{ zs, RET #();
        is_min_heap [] h ∗ out ↦ inject zs ∗
        ⌜zs ≡ₚ concat zss⌝ ∗ ⌜Sorted (flip Z.le) zs⌝}}}.
  Proof.
    iIntros (???) "(?&?&?) H".
    wp_apply (wp_repeat_remove_aux _ [] with "[$]"); [done|done|done|done|].
    iIntros (?). rewrite app_nil_r //.
  Qed.

  Definition merge_cost (zss : list (list Z)) : R :=
    length zss * heap_insert_cost (length zss) + repeat_remove_cost zss.

  Lemma concat_filter_nempty (zss : list (list Z)) :
    concat (filter ([] ≠.) zss) = concat zss.
  Proof.
    induction zss as [|zs zss]; [done|].
    rewrite filter_cons.
    destruct zs => /=; [done|].
    rewrite IHzss //.
  Qed.

  Lemma wp_merge (v : val) (zss : list (list Z)) :
    is_list zss v →
    Forall (Sorted Z.le) zss →
    {{{ ⧖ (merge_cost zss) }}}
      merge v
    {{{ v zs, RET v; ⌜is_list zs v⌝ ∗ ⌜zs ≡ₚ concat (filter ([] ≠.) zss)⌝ ∗ ⌜Sorted Z.le zs⌝ }}}.
  Proof.
    iIntros (Hv Hzss Ψ) "Hc HΨ".
    rewrite /merge_cost.
    iDestruct (etc_split with "Hc") as "[Hinit Hc]"; [auto with real..|].
    wp_rec.
    wp_apply wp_heap_new; [done|].
    iIntros (h) "Hh"; wp_pures.
    rewrite etc_split_list; [|auto with real].
    wp_apply (wp_list_iter_invariant (λ _ _, ⧖ (heap_insert_cost (length zss))) (λ _ _, True)
                (λ zss', is_min_heap (filter (([] ≠.)) zss') h) True
               with "[] [$Hh $Hinit //]")%I.
    { iIntros (zs zss' Ψ') "!# ([% ->] & _ & Hh & Hc) HΨ'".
      wp_pures.
      wp_apply (wp_list_is_empty zs); [|iIntros "_"].
      { rewrite is_list_inject //. }
      destruct zs as [|z zs'] eqn:Hzs; wp_pures.
      - iApply "HΨ'". iModIntro.
        rewrite filter_app filter_cons_False ?filter_nil; [|auto].
        rewrite app_nil_r. by iFrame.
      - wp_apply (wp_heap_insert _ (z :: zs') with "[$Hh Hc]").
        { rewrite /= /is_Z_list is_list_inject.
          iSplit.
          - iSplit; [done|]. by apply Forall_app in Hzss as [_ [? ?]%Forall_cons].
          - iApply (etc_weaken with "Hc"). split; [auto with real|].
            apply heap_insert_cost_mono.
            etrans; [apply filter_length|].
            rewrite app_length. lia. }
        iIntros (zss'') "[Hh ->]".
        iApply "HΨ'".
        rewrite Permutation_cons_append.
        rewrite right_id left_id.
        rewrite filter_app filter_cons /= filter_nil //. }
    iIntros "(_ & Hh & _)".
    wp_pures.
    wp_alloc out as "Hout".
    wp_pures.
    wp_apply (wp_repeat_remove with "[Hc $Hh $Hout]"); [ | | |].
    { apply Forall_forall => zs Hzs.
      apply list_filter_subseteq in Hzs.
      by eapply Forall_forall in Hzss. }
    { apply Forall_forall => zs Hz.
      rewrite elem_of_list_filter in Hz.
      by destruct Hz, zs. }
    { iApply (etc_weaken with "Hc").
      split; [apply repeat_remove_cost_nonneg|].
      rewrite /repeat_remove_cost /= .
      rewrite concat_filter_nempty.
      assert (heap_remove_cost (length (filter (λ y : list Z, [] ≠ y) zss))
              <= heap_remove_cost (length zss)).
      { apply heap_remove_cost_mono. apply filter_length. }
      assert (heap_insert_cost (length (filter (λ y : list Z, [] ≠ y) zss))
              <= heap_insert_cost (length zss)).
      { apply heap_insert_cost_mono. apply filter_length. }
      eauto with real. }
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

  Lemma merge_cost_alt zss :
    let k := length zss in
    let n := length (concat zss) in
    merge_cost zss = (k + n) * heap_insert_cost k +
                     n * heap_remove_cost k +
                     heap_remove_cost 0.
  Proof. rewrite /merge_cost /repeat_remove_cost. lra. Qed.

End kway_merge_spec.

From clutch.ert_logic.examples Require Import meldable_heap.

Section kway_merge_meldable_heap.
  Context `{!ert_clutchGS Σ CostTick}.

  Definition heap := meld_heap_spec Z_list_comparator.
  Definition meldable_merge := @kway_merge.merge _ _ _ heap.

  Variable (zss : list (list Z)).

  Notation k := (length zss).
  Notation n := (length (concat zss)).

  Lemma wp_meldable_merge (v : val) :
    is_list zss v →
    Forall (Sorted Z.le) zss →
    {{{ ⧖ ((k + 3 * n) * tc_meld 1 k + 3 * k + 4 * n + 1) }}}
      meldable_merge v
    {{{ v zs, RET v; ⌜is_list zs v⌝ ∗ ⌜zs ≡ₚ concat zss⌝ ∗ ⌜Sorted Z.le zs⌝ }}}.
  Proof.
    iIntros (???) "Hcost H".
    iApply (wp_merge with "[Hcost]"); [done|done| |].
    { iApply (etc_irrel with "Hcost").
      rewrite merge_cost_alt.
      rewrite /merge_cost /repeat_remove_cost.
      rewrite /heap_insert_cost /heap_remove_cost /=.
      rewrite /meld_heap_insert_cost /meld_heap_remove_cost /=.
      rewrite tc_meld_0 tc_meld_1. lra. }
    rewrite concat_filter_nempty //.
  Qed.

End kway_merge_meldable_heap.

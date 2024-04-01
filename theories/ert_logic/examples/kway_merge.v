From Coquelicot Require Import Hierarchy.
From stdpp Require Import sorting.
From iris.proofmode Require Export proofmode.
From clutch.ert_logic Require Export problang_wp proofmode derived_laws ert_rules cost_models.
From clutch.ert_logic.examples Require Import lib.list min_heap_spec.
Set Default Proof Using "Type*".

(* Section list_length_ind. *)
(*   Variable A : Type. *)
(*   Variable P : list A -> Prop. *)

(*   Hypothesis H : ∀ xs, (∀ l, length l < length xs → P l) → P xs. *)

(*   Theorem list_length_ind : ∀ xs, P xs. *)
(*   Proof. *)
(*     assert (∀ xs l : list A, length l ≤ length xs → P l) as H_ind. *)
(*     { induction xs; intros l Hlen; apply H; intros l0 H0. *)
(*       - destruct l, l0; simpl in *; lia. *)
(*       - apply IHxs. simpl in Hlen. lia. } *)
(*     intros xs. *)
(*     by eapply H_ind. *)
(*   Qed. *)
(* End list_length_ind. *)

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
          | SOME "z" =>
              "out" <- list_cons "z" !"out";;
              heap_insert "h" (list_tail "zs") ;;
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

  Local Hint Resolve heap_insert_cost_nonneg : real.
  Local Hint Resolve heap_remove_cost_nonneg : real.
  Local Hint Resolve Rmult_le_pos Rplus_le_le_0_compat : real.
  Local Hint Resolve Rle_plus_plus : real.

  Definition repeat_remove_cost (zss : list (list Z)) : R :=
    length (concat zss) * heap_remove_cost (length zss) +
    length (concat zss) * heap_insert_cost (length zss) +
    length zss * heap_remove_cost (length zss) +
    length zss * heap_insert_cost (length zss) +
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

  Lemma length_concat_inv {A} (xss : list (list A)) :
    length (concat xss) ≠ 0%nat → ∃ x xs, xs ∈ xss ∧ x ∈ xs.
  Proof.
    induction xss as [|xs xss]; [done|].
    rewrite concat_cons app_length.
    destruct xs as [|x xs] => /=.
    - intros Hlen; destruct (IHxss Hlen) as (?&?&?&?).
      do 2 eexists. by split; [right|].
    - intros _. do 2 eexists. by split; left.
  Qed.

  Lemma length_pos {A} (xs : list A) :
    0 <= length xs.
  Proof.
    induction xs; [done|].
    rewrite cons_length S_INR. lra.
  Qed.

  Local Hint Resolve length_pos : real.

  Lemma etc_repeat_remove_cost_split zss :
    length zss ≠ 0%nat →
    ⧖ (repeat_remove_cost zss) ⊢
      ⧖ (heap_remove_cost (length zss)) ∗
      ⧖ (heap_insert_cost (length zss)) ∗
      ⧖ (repeat_remove_cost zss
           - heap_remove_cost (length zss)
           - heap_insert_cost (length zss)).
  Proof.
    intros [zs [zss' Hzs]%elem_of_Permutation]%length_inv_not_zero.
    setoid_rewrite Hzs.
    rewrite /repeat_remove_cost.
    do 4 (rewrite etc_split; eauto 10 with real).
    rewrite -!bi.sep_assoc.
    iIntros "(Hr & Hi & Hrnils & Hinils & H0)".
    rewrite concat_cons app_length cons_length.
    rewrite plus_INR S_INR !Rmult_plus_distr_r !Rmult_1_l.
    iDestruct (etc_split with "Hr") as "[Hr1 Hr2]"; auto with real.
    iDestruct (etc_split with "Hi") as "[Hi1 Hi2]"; auto with real.
    (* if [zs] is empty, we pay with "Hnils", if not we pay with "Hr1" and "Hi1" *)
    destruct zs.
    - iDestruct (etc_split with "Hrnils") as "[Hrnils $]"; auto with real.
      iDestruct (etc_split with "Hinils") as "[Hinils $]"; auto with real.
      iClear "Hr1 Hi1".
      iCombine "Hr2 Hi2 Hrnils Hinils H0" as "H".
      iApply (etc_irrel with "H").
      simpl. lra.
    - rewrite cons_length S_INR !Rmult_plus_distr_r !Rmult_1_l.
      iDestruct (etc_split with "Hr1") as "[Hr1 $]"; auto with real.
      iDestruct (etc_split with "Hi1") as "[Hi1 $]"; auto with real.
      iCombine "Hr1 Hr2 Hi1 Hi2 Hrnils Hinils H0" as "H".
      iApply (etc_irrel with "H"). lra.
  Qed.

  Local Lemma wp_repeat_remove_aux (zss : list (list Z)) zs0 h out :
    Forall (Sorted Z.le) zss →
    Sorted (flip Z.le) zs0 →
    Forall (λ z, Forall (Z.le z) (concat zss)) zs0 →
    {{{ ⧖ (repeat_remove_cost zss) ∗ is_min_heap zss h ∗ out ↦ inject zs0 }}}
      repeat_remove h #out
    {{{ zs', RET #();
          is_min_heap [] h ∗ out ↦ inject (zs' ++ zs0) ∗
          ⌜zs' ≡ₚ concat zss⌝ ∗ ⌜Sorted (flip Z.le) (zs' ++ zs0)⌝}}}.
  Proof.
    iIntros (Hzss Hzs0 Hle Ψ) "(Hc & Hh & Hout) HΨ".
    iLöb as "IH" forall (zss zs0 Hzss Hzs0 Hle Ψ) "Hc Hh Hout HΨ".
    wp_rec; wp_pures.
    destruct (length zss) eqn:Hlen.
    - rewrite repeat_remove_cost_nil //.
      wp_apply (wp_heap_remove with "[$Hh Hc]").
      { rewrite Hlen //. }
      iIntros (?) "[(-> & -> & Hh) | (% & % & % & % & %Hp & H)]"; last first.
      { rewrite Hp /= in Hlen. lia. }
      wp_pures.
      iApply ("HΨ" $! []). rewrite app_nil_l /=. by iFrame.
    - iDestruct (etc_repeat_remove_cost_split with "Hc") as "(Hr & Hi & Hrest)"; [lia|].
      wp_apply (wp_heap_remove with "[$Hh $Hr]").
      iIntros (w) "[(_ & % & _) | (%zs' & %u & %zss' & -> & %Hp & [%Hu %HuS] & %Hs & Hh)]";
        simplify_eq.
      wp_pures.
      wp_apply (wp_list_head with "[//]").
      iIntros (w) "[[-> ->] | (%z & %zs'' & -> & ->)]".
      + wp_pures.
        wp_apply ("IH" $! zss' zs0 with "[] [//] [] [Hrest] Hh Hout").
        { iPureIntro. rewrite Hp Forall_cons in Hzss. by destruct Hzss. }
        { iPureIntro. eapply Forall_impl; [exact Hle|].
          intros z => /=. rewrite Hp concat_cons app_nil_l //. }
        { iApply (etc_weaken with "Hrest").
          split; [auto with real|].
          rewrite Hp cons_length.
          rewrite {2}/repeat_remove_cost.
          rewrite concat_cons cons_length app_length nil_length.

          rewrite Nat.add_0_l.
          rewrite !S_INR !Rmult_plus_distr_r 2!Rmult_1_l.
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
             length (concat zss') * IS +
               length zss' * RS +
               length zss' * IS + heap_remove_cost 0); [|lra].

          eauto 10 with real. }
        iIntros (zs') "(Hh & Hout & %Hp' & %Hs')".
        iApply ("HΨ" with "[$Hh $Hout]"). iSplit; [|done].
        iPureIntro. rewrite Hp' Hp //.
      + wp_pures.
        wp_load; iIntros "Hout".
        wp_apply (wp_list_cons z zs0).
        { rewrite is_list_inject //. }
        iIntros (r Hr).
        wp_store; iIntros "Hout".
        wp_pures.
        wp_apply (wp_list_tail _ _ (z :: zs'') with "[//]"); simpl.
        iIntros (w Hw).
        wp_apply (wp_heap_insert _ zs'' with "[$Hh Hi]").
        { iSplit.
          * iSplit; [done|]. by inversion HuS.
          * iApply (etc_weaken with "Hi"). split; [auto with real|].
            rewrite Hp. apply heap_insert_cost_mono => /=. lia. }
        iIntros (zss'') "(Hh & %Hp')".
        wp_pures.
        apply is_list_inject in Hr as ->.
        wp_apply ("IH" $! _ (z :: zs0) with "[] [] [] [Hrest] Hh Hout").
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
          rewrite Hp in Hzss Hs.
          setoid_rewrite Hp in Hle; clear Hlen Hp zss.
          setoid_rewrite Hp'; clear Hp' zss''.
          simpl in Hs.
          apply Forall_cons in Hs as [_ Hs].
          apply Forall_cons.
          split.
          - rewrite concat_cons. apply Forall_app.
            apply Forall_cons in Hzss as [? ?].
            eapply Sorted_extends in H; [|intros ?????; by etrans].
            split; [done|].
            apply Forall_concat.
            apply Forall_forall.
            intros ys Hys.
            rewrite Forall_forall in Hs.
            pose proof (Hs _ Hys).
            destruct ys; [done|].
            rewrite Forall_cons. split; [done|].
            rewrite Forall_forall in H0.
            specialize (H0 _ Hys).
            eapply Sorted_extends in H0; [|intros ?????; by etrans].
            simpl in H1.
            specialize (Hs _ Hys).
            simpl in Hs.
            eapply Forall_impl; [done|].
            intros ??. by etrans.
          - rewrite /= -concat_cons in Hle.
            setoid_rewrite Forall_cons in Hle.
            eapply Forall_impl; [done|]. by intros ? [] . }
        { iApply (etc_irrel with "Hrest").
          rewrite Hp Hp'.
          rewrite /repeat_remove_cost.
          rewrite !concat_cons !app_length !cons_length.
          rewrite !plus_INR !S_INR.
          rewrite !Rmult_plus_distr_r !Rmult_1_l.
          remember (heap_remove_cost (S (length zss'))) as R.
          remember (heap_insert_cost (S (length zss'))) as I.
          lra. }
        iIntros (zs') "(Hh & Hout & %Hp'' & %HS)".
        assert ((zs' ++ z :: zs0) = (zs' ++ [z]) ++ zs0) as ->.
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
    {{{ ⧖ (repeat_remove_cost zss) ∗ is_min_heap zss h ∗ out ↦ NONEV }}}
      repeat_remove h #out
    {{{ zs, RET #();
        is_min_heap [] h ∗ out ↦ inject zs ∗
        ⌜zs ≡ₚ concat zss⌝ ∗ ⌜Sorted (flip Z.le) zs⌝}}}.
  Proof.
    iIntros (??) "(?&?&?) H".
    wp_apply (wp_repeat_remove_aux _ [] with "[$]"); [done|done|done|].
    iIntros (?). rewrite app_nil_r //.
  Qed.

  Definition merge_cost (zss : list (list Z)) : R :=
    length zss * heap_insert_cost (length zss) + repeat_remove_cost zss.

  Lemma wp_merge (v : val) (zss : list (list Z)) :
    is_list zss v →
    Forall (Sorted Z.le) zss →
    {{{ ⧖ (merge_cost zss) }}}
      merge v
    {{{ v zs, RET v; ⌜is_list zs v⌝ ∗ ⌜zs ≡ₚ concat zss⌝ ∗ ⌜Sorted Z.le zs⌝ }}}.
  Proof.
    iIntros (Hv Hzss Ψ) "Hc HΨ".
    rewrite /merge_cost.
    iDestruct (etc_split with "Hc") as "[Hinit Hc]"; [auto with real..|].
    wp_rec.
    wp_apply wp_heap_new; [done|].
    iIntros (h) "Hh"; wp_pures.
    rewrite etc_split_list; [|auto with real].
    wp_apply (wp_list_iter_invariant (λ _ _, ⧖ (heap_insert_cost (length zss))) (λ _ _, True)
                (λ l, is_min_heap l h) True with "[] [$Hh $Hinit //]")%I.
    { iIntros (l l' Ψ') "!# ([% ->] & _ & Hh & Hc) HΨ'".
      wp_pures.
      wp_apply (wp_heap_insert _ l with "[$Hh Hc]").
      { rewrite /= /is_Z_list is_list_inject.
        iSplit.
        - iSplit; [done|]. by apply Forall_app in Hzss as [_ [? ?]%Forall_cons].
        - iApply (etc_weaken with "Hc"). split; [auto with real|].
          apply heap_insert_cost_mono. rewrite app_length. lia. }
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

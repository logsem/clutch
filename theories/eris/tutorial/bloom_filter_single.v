From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import gset_bij.
From clutch.eris Require Import eris.
From clutch.eris.tutorial Require Import hash_interface.
From clutch.eris.lib Require Import list array.

Set Default Proof Using "Type*".


Section bloom_filter_single.



  Variable filter_size : nat.
  Variable key_size : nat.

  Context `{!erisGS Σ, !hash_function Σ}.

  (*
     Instead of computing the probability of false positive explicitly, we will
     use a recurrence relation, which will simplify the math in the proof.

     Probability of false positive of one insertion after hashing m elements into a
     Bloom filter containing b bits set to 1 *)

  Fixpoint fp_error (m b : nat) : R :=
    if bool_decide (b >= filter_size + 1) then 1 else
      (match m with
      | 0 => b/(filter_size + 1)
      | S m' => (b / (filter_size + 1)) * fp_error m' b +
               ((filter_size + 1 - b) / (filter_size + 1)) * fp_error m' (S b)
       end)%R.

  (* Auxiliary lemmas about fp_error *)

  Lemma fp_error_max (m b : nat) :
    (filter_size + 1 ≤ b) ->
    fp_error m b = 1.
  Proof.
    intros Hb.
    destruct m; simpl.
    - case_bool_decide; done.
    - case_bool_decide; done.
  Qed.


  Lemma fp_error_bounded (m b : nat) :
    (0 <= fp_error m b <= 1)%R.
  Proof.
    revert b.
    induction m; intros b.
    - simpl.
      case_bool_decide as H; [lra |].
      split.
      + apply Rcomplements.Rdiv_le_0_compat; real_solver.
      + apply not_ge in H.
        apply (Rcomplements.Rdiv_le_1 b); [real_solver |].
        left.
        apply lt_INR in H.
        rewrite plus_INR /= in H.
        real_solver.
   - simpl.
     case_bool_decide as H; [lra |].
     replace ((filter_size + 1 - b) / (filter_size + 1))%R with
       ( 1 - b / (filter_size + 1))%R; last first.
     {
       rewrite {2}/Rdiv.
       rewrite (Rmult_plus_distr_r).
       rewrite Rmult_inv_r; [real_solver |].
       pose proof (pos_INR filter_size).
       lra.
     }
     apply (convex_sum_conv_alt); auto.
     split.
     + apply Rcomplements.Rdiv_le_0_compat; real_solver.
     + apply (Rcomplements.Rdiv_le_1 b); [real_solver |].
       apply not_ge in H.
       apply lt_INR in H.
       rewrite plus_INR /= in H.
       real_solver.
  Qed.


  Lemma fp_error_weaken (m b : nat):
    (fp_error 0 b <= fp_error m b)%R.
  Proof.
    revert b.
    induction m; intros b; [lra |].
    pose proof (IHm (S b)) as H2.
    assert (fp_error 0 b <= fp_error 0 (S b))%R as H3.
    {
      rewrite /fp_error.
      case_bool_decide as H4; case_bool_decide as H5.
      - lra.
      - lia.
      - apply not_ge in H4.
        apply (Rcomplements.Rdiv_le_1 b); [real_solver |].
        left.
        apply lt_INR in H4.
        rewrite plus_INR /= in H4.
        real_solver.
      - apply Rmult_le_compat_r; real_solver.
    }
    rewrite {2}/fp_error.
    case_bool_decide as H.
    - apply fp_error_bounded.
    - fold fp_error.
      replace (fp_error 0 b) with
        (b / (filter_size + 1) * fp_error 0 b + (filter_size + 1 - b) / (filter_size + 1) * fp_error 0 b)%R; last first.
      {
        rewrite -Rmult_plus_distr_r
         -Rmult_plus_distr_r
         Rplus_comm
         -Rplus_minus_swap
         Rplus_minus_r.
        rewrite Rmult_inv_r; real_solver.
      }
      apply Rplus_le_compat.
      + apply Rmult_le_compat_l; auto.
        apply Rcomplements.Rdiv_le_0_compat; real_solver.
      + apply Rmult_le_compat_l; [|lra].
        apply Rcomplements.Rdiv_le_0_compat; [|real_solver].
        apply not_ge in H.
        apply lt_INR in H.
        rewrite plus_INR /= in H.
        real_solver.
  Qed.

  Lemma fp_error_step (m b: nat) :
    (fp_error m b * b +
    fp_error m (S b) * (filter_size + 1 - b) <=
    fp_error (S m) b * (filter_size + 1))%R.
  Proof.
    simpl.
    case_bool_decide.
    * rewrite fp_error_max /=; auto.
      rewrite fp_error_max /=; auto.
      lra.
    * right.
      rewrite (Rmult_comm (b / (filter_size + 1))).
      rewrite (Rmult_comm ((filter_size + 1 - b) / (filter_size + 1))).
      rewrite Rmult_plus_distr_r.
      rewrite !(Rmult_assoc _ _ (filter_size + 1)).
      rewrite !Rinv_l; [lra|].
      real_solver.
  Qed.



  Definition init_bloom_filter : expr :=
    λ: "_" ,
      let: "hf" := init_hash #key_size #filter_size in
      let: "arr" := array_init #(S filter_size) (λ: "x", #false)%E in
      let: "l" := ref ("hf", "arr") in
      "l".

  Definition insert_bloom_filter : expr :=
    λ: "l" "v" ,
      let, ("hf", "arr") := !"l" in
      let: "i" := "hf" "v" in
      "arr" +ₗ "i" <- #true.


  Definition lookup_bloom_filter : expr :=
    λ: "l" "v" ,
      let, ("hf", "arr") := !"l" in
      let: "i" := "hf" "v" in
      !("arr" +ₗ "i").

  Definition bloom_filter_correct_content
    (m : gmap nat nat) (arr : list val) (els : gset nat) (idxs : gset nat) :=
    (els = dom m) /\
    (forall e, e ∈ els -> (m !!! e) ∈ idxs) /\
    (length arr = S filter_size) /\
    (size idxs ≤ filter_size + 1) /\
    (forall i, i ∈ idxs -> arr !! i = Some #true) /\
    (forall i, i ∈ idxs -> (i < S filter_size)%nat) /\
    (forall i, i < length arr -> i ∉ idxs -> arr !! i = Some #false).

  Definition is_bloom_filter (l : loc) (els : gset nat) (rem : nat) : iProp Σ :=
    ∃ hf m a arr (idxs : gset nat),
      ↯ (fp_error rem (size idxs)) ∗
      l ↦ (hf, LitV (LitLoc a))%V ∗
      (a ↦∗ arr) ∗
      hashfun filter_size hf m ∗
      ⌜bloom_filter_correct_content m arr els idxs⌝.


  Lemma bloom_filter_init_content (arr : list val) :
    length arr = S filter_size ->
    (∀ (k : nat) (x : val), arr !! k = Some x → x = #false) ->
    bloom_filter_correct_content ∅ arr ∅ ∅.
  Proof.
    intros Hlen Hf.
    repeat split; auto.
    - rewrite size_empty.
      lia.
    - set_solver.
    - set_solver.
    - intros i Hi Hi2.
      destruct (lookup_lt_is_Some_2 arr i Hi) as [v Hv].
      specialize (Hf _ _ Hv).
      simplify_eq; done.
  Qed.


  Lemma bfcc_map_els (m : gmap nat nat)
    (arr : list val) (els : gset nat) (idxs : gset nat) (k : nat) :
    bloom_filter_correct_content m arr els idxs ->
    (k ∈ els <-> is_Some (m !! k)).
  Proof.
    intros Hbf.
    destruct Hbf as (-> & Hels & Hlen & Hsize & Ht & Hidxs & Hf); split.
    - intros Hk.
      rewrite <- elem_of_dom; auto.
    - intros Hk.
      rewrite elem_of_dom; auto.
  Qed.

  Lemma bfcc_lookup_arr (m : gmap nat nat)
    (arr : list val) (els : gset nat) (idxs : gset nat) (i : nat) :
    i < S filter_size ->
    bloom_filter_correct_content m arr els idxs ->
    is_Some (arr !! i).
  Proof.
    intros Hi Hbf.
    destruct Hbf as (-> & Hels & Hlen & Hsize & Ht & Hidxs & Hf).
    apply lookup_lt_is_Some_2.
    rewrite Hlen //.
  Qed.

  Lemma bfcc_idxs_arr_true (m : gmap nat nat)
    (arr : list val) (els : gset nat) (idxs : gset nat) (i : nat) :
    i ∈ idxs ->
    bloom_filter_correct_content m arr els idxs ->
    arr !! i = Some #true.
  Proof.
    intros Hi Hbf.
    destruct Hbf as (-> & Hels & Hlen & Hsize & Ht & Hidxs & Hf).
    by apply Ht.
  Qed.

  Lemma bfcc_idxs_arr_false (m : gmap nat nat)
    (arr : list val) (els : gset nat) (idxs : gset nat) (i : nat) :
    i ∉ idxs ->
    i < S filter_size ->
    bloom_filter_correct_content m arr els idxs ->
    arr !! i = Some #false.
  Proof.
    intros Hi1 Hi2 Hbf.
    destruct Hbf as (-> & Hels & Hlen & Hsize & Ht & Hidxs & Hf).
    apply Hf; auto.
    rewrite Hlen //.
  Qed.

  Lemma bfcc_map_to_idx (m : gmap nat nat)
    (arr : list val) (els : gset nat) (idxs : gset nat) (k i : nat) :
    m !! k = Some i ->
    bloom_filter_correct_content m arr els idxs ->
    i ∈ idxs.
  Proof.
    intros Hki Hbf.
    destruct Hbf as (-> & Hels & Hlen & Hsize & Ht & Hidxs & Hf).
    rewrite <- (lookup_total_correct _ _ _ Hki).
    apply Hels.
    eapply elem_of_dom_2; eauto.
  Qed.

  Lemma bfcc_idx_bd (m : gmap nat nat)
    (arr : list val) (els : gset nat) (idxs : gset nat) (i : nat) :
    i ∈ idxs ->
    bloom_filter_correct_content m arr els idxs ->
    i < S filter_size.
  Proof.
    intros Hki Hbf.
    destruct Hbf as (-> & Hels & Hlen & Hsize & Ht & Hidxs & Hf).
    apply Hidxs; auto.
  Qed.

  Lemma bloom_filter_update_content_no_coll (m : gmap nat nat)
    (arr : list val) (els : gset nat) (idxs : gset nat) (k : nat) (v : nat) :
    v < S filter_size ->
    k ∉ els ->
    v ∉ idxs ->
    bloom_filter_correct_content m arr els idxs ->
      bloom_filter_correct_content (<[k := v]> m) (<[v := #true]> arr)
      (els ∪ {[k]}) (idxs ∪ {[v]}).
  Proof.
    intros Hv Hk Hnelem Hbf.
    destruct Hbf as (-> & Hels & Hlen & Hsize & Ht & Hidxs & Hf).
    repeat split.
    - set_solver.
    - intros e He.
      apply elem_of_union in He as [He|He].
      + rewrite lookup_total_insert_ne; [|set_solver].
        specialize (Hels e He).
        set_solver.
      + apply elem_of_singleton in He as ->.
        rewrite lookup_total_insert.
        set_solver.
    - rewrite -Hlen length_insert //.
    - rewrite size_union; [|set_solver].
      rewrite size_singleton.
      apply Nat.add_le_mono_r.
      assert (idxs ⊆ (set_seq 0 (filter_size + 1) ∖ {[v]} )) as Hsub.
      {
        apply elem_of_subseteq.
        intros z Hz.
        apply elem_of_difference.
        split; [|set_solver].
        apply elem_of_set_seq.
        split; [lia|].
        simpl.
        replace (filter_size + 1) with (S filter_size) by lia.
        apply Hidxs.
        set_solver.
      }
      etransitivity.
      *** apply subseteq_size, Hsub.
      *** rewrite size_difference.
          **** rewrite size_set_seq size_singleton.
               lia.
          **** apply singleton_subseteq_l.
               apply elem_of_set_seq.
               split; lia.
    - intros i Hi.
      apply elem_of_union in Hi as [Hi|Hi]; auto.
      + rewrite list_lookup_insert_ne; auto.
        set_solver.
      + apply elem_of_singleton in Hi as ->.
        rewrite list_lookup_insert //.
        real_solver.
    - intros i Hi.
      apply elem_of_union in Hi as [Hi|Hi]; auto.
      apply elem_of_singleton in Hi as ->; done.
    - intros i Hleq Hi.
      rewrite length_insert in Hleq.
      apply not_elem_of_union in Hi as [Hi1 Hi2].
      apply not_elem_of_singleton in Hi2.
      rewrite list_lookup_insert_ne; auto.
  Qed.

  Lemma bloom_filter_update_content_coll (m : gmap nat nat)
    (arr : list val) (els : gset nat) (idxs : gset nat) (k : nat) (v : nat) :
    v < S filter_size ->
    k ∉ els ->
    v ∈ idxs ->
    bloom_filter_correct_content m arr els idxs ->
    bloom_filter_correct_content (<[k := v]> m) (<[v := #true]> arr)
      (els ∪ {[k]}) idxs.
  Proof.
    intros Hv Hk Helem Hbf.
    destruct Hbf as (-> & Hels & Hlen & Hsize & Ht & Hidxs & Hf).
    repeat split; auto.
    - set_solver.
    - intros e He.
      apply elem_of_union in He as [He|He].
      + rewrite lookup_total_insert_ne; [|set_solver].
        specialize (Hels e He).
        set_solver.
      + apply elem_of_singleton in He as ->.
        rewrite lookup_total_insert.
        set_solver.
    - rewrite -Hlen length_insert //.
    - intros i Hi.
      destruct (decide (v = i)) as [-> | ?].
      *** rewrite list_lookup_insert //.
          real_solver.
      *** rewrite list_lookup_insert_ne //; auto.
    - intros i Hleq Hi.
      rewrite length_insert in Hleq.
      destruct (decide (v = i)) as [-> | ?].
      + rewrite list_lookup_insert //.
      + rewrite list_lookup_insert_ne //; auto.
  Qed.


 Lemma bloom_filter_init_spec (rem : nat) :
    {{{ ↯ (fp_error rem 0) }}}
      init_bloom_filter #()
      {{{ (l:loc), RET #l ; is_bloom_filter l ∅ rem }}}.
 Proof.
    iIntros (Φ) "Herr HΦ".
    rewrite /init_bloom_filter.
    wp_pures.
    wp_apply hash_init_spec; auto.
    iIntros (hf) "Hhf".
    wp_pures.
    wp_apply (wp_array_init (λ _ v, ⌜ v = #false ⌝%I)).
    + real_solver.
    + iApply big_sepL_intro.
      iModIntro.
      iIntros (??) "?".
      wp_pures.
      done.
    + iIntros (a arr) "(%HlenA & Ha & %Harr)".
      wp_pures.
      wp_alloc l as "Hl".
      wp_pures.
      iModIntro.
      iApply "HΦ".
      rewrite /is_bloom_filter.
      iExists hf, ∅, a, arr, ∅.
      rewrite size_empty.
      iFrame.
      iPureIntro.
      eapply bloom_filter_init_content.
      - lia.
      - auto.
  Qed.


  Lemma bloom_filter_insert_spec (l : loc) (s : gset nat) (x rem : nat) :
    {{{ is_bloom_filter l s (S rem) ∗ ⌜ x ∉ s ⌝
    }}}
      insert_bloom_filter #l #x
      {{{ RET #() ; is_bloom_filter l (s ∪ {[x]}) rem
      }}}.
  Proof using erisGS0 filter_size hash_function0 key_size Σ.
    iIntros (Φ) "(Hbf & %Hx ) HΦ".
    rewrite /insert_bloom_filter {1}/is_bloom_filter.
    wp_pures.
    iDestruct "Hbf" as (hf m a arr idxs) "(Herr & Hl & Ha & Hhf & %Hcont)".
    wp_load.
    wp_pures.
    wp_apply (hash_query_spec_fresh x idxs
       (fp_error (S rem) (size idxs))
       (fp_error rem (size idxs))
       (fp_error rem (S (size idxs)))
       filter_size hf m with "[$]"); auto.
    + rewrite eq_None_not_Some.
      rewrite <- bfcc_map_els; eauto.
    + apply fp_error_bounded.
    + apply fp_error_bounded.
    + intros. eapply bfcc_idx_bd; eauto.
    + apply fp_error_step.
    + simpl.
      iIntros (v) "(% & ? & [(% & ?) | (% &? )])".
      * wp_pures.
        wp_apply (wp_store_offset with "Ha").
        {
          eapply bfcc_lookup_arr; eauto.
        }
        iIntros "Ha".
        iApply "HΦ".
        rewrite /is_bloom_filter.
        iExists hf, (<[x:=v]> m), a, (<[v:=#true]> arr), (idxs ∪ {[v]}).
        iFrame.
        rewrite size_union; [|set_solver].
        rewrite size_singleton.
        replace (S (size idxs)) with (size idxs + 1) by lia.
        iFrame.
        iPureIntro.
        by apply bloom_filter_update_content_no_coll.

      * wp_pures.
        wp_apply (wp_store_offset with "Ha").
        {
          eapply bfcc_lookup_arr; eauto.
        }
        iIntros "Ha".
        iApply "HΦ".
        rewrite /is_bloom_filter.
        iExists hf, (<[x:=v]> m), a, (<[v:=#true]> arr), idxs.
        simpl.
        iFrame.
        iPureIntro.
        by apply bloom_filter_update_content_coll.
  Qed.


  Lemma bloom_filter_lookup_in_spec (l : loc) (s : gset nat) (x rem : nat) :
    {{{ is_bloom_filter l s rem ∗ ⌜ x ∈ s ⌝
    }}}
      lookup_bloom_filter #l #x
      {{{ v, RET v ; ⌜v = #true⌝ }}}.
  Proof using erisGS0 filter_size hash_function0 key_size Σ.
    iIntros (Φ) "(Hbf & %Hx ) HΦ".
    rewrite /insert_bloom_filter {1}/is_bloom_filter.
    iDestruct "Hbf" as (hf m a arr idxs) "(Herr & Hl & Ha & Hhf & %Hcont)".
    wp_pures.
    wp_load.
    wp_pures.
    destruct (bfcc_map_els m arr s idxs x Hcont) as [H1 H2].
    destruct (H1 Hx) as [v Hv].
    wp_apply (hash_query_spec_prev x _ _ hf m with "Hhf"); eauto.
    iIntros "Hhf".
    wp_pures.
    wp_apply (wp_load_offset with "Ha").
    {
      eapply bfcc_idxs_arr_true; eauto.
      eapply bfcc_map_to_idx; eauto.
    }
    iIntros "Ha".
    iApply "HΦ".
    done.
 Qed.

  Lemma bloom_filter_lookup_not_in_spec (l : loc) (s : gset nat) (x rem : nat) :
    {{{ is_bloom_filter l s (S rem) ∗ ⌜ x ∉ s ⌝
    }}}
      lookup_bloom_filter #l #x
      {{{ v, RET v ; ⌜v = #false⌝ }}}.
  Proof using erisGS0 filter_size hash_function0 key_size Σ.
    iIntros (Φ) "(Hbf & %Hx) HΦ".
    rewrite /insert_bloom_filter {1}/is_bloom_filter.
    iDestruct "Hbf" as (hf m a arr idxs) "(Herr & Hl & Ha & Hhf & %Hcont)".
    wp_pures.
    wp_load.
    wp_pures.
    iPoseProof (ec_weaken _ (fp_error 0 (size idxs)) with "Herr") as "Herr".
    {
      split.
      - apply fp_error_bounded.
      - apply fp_error_weaken.
    }
    simpl.
    case_bool_decide.
    {
      iExFalso.
      iApply (ec_contradict with "[$]").
      lra.
    }
    wp_apply (hash_query_spec_fresh  _ idxs
                _ 1 0 filter_size _ m
                        with "[$]"); auto.
   - rewrite eq_None_not_Some.
     rewrite <- bfcc_map_els; eauto.
   - lra.
   - lra.
   - intros.
     eapply bfcc_idx_bd; eauto.
   - rewrite Rmult_1_l Rmult_0_l Rplus_0_r.
     rewrite -Rmult_div_swap.
     rewrite Rmult_div_l //.
     real_solver.
   - iIntros (v) "(%Hv & Hhfw & Herr)".
     iDestruct "Herr" as "[(%Hvout & Herr) | (%Hvin & Herr)]"; wp_pures.

     + wp_apply (wp_load_offset _ _ _ _ _ #false with "Ha").
       {
         eapply bfcc_idxs_arr_false; eauto.
       }
        iIntros "Ha".
        iApply "HΦ".
        done.

     + iPoseProof (ec_contradict with "[$Herr]") as "?"; [lra|].
        done.
 Qed.

End bloom_filter_single.


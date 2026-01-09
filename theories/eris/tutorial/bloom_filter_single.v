From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import gset_bij.
From clutch.eris Require Import eris.
From clutch.eris.tutorial Require Import hash_interface.
From clutch.eris.lib Require Import list array.

Set Default Proof Using "Type*".

(** * Bloom filters *)

(** Our main case study will be bloom filters. A bloom filter is a probabilistic
    data structure to represent sets with constant time insertion and membership
    queries. It consists of a boolean array a, initially set to [false]
    everywhere and a set of hash functions h1,...,hn. When inserting a new
    element e, it computes for every i∈{1,...n} the hash hi[e], and sets
    a[hi[e]%(size a)]=true. Queries work similarly, except that we just compute
    ⋀_{i∈{1,...,n}} a[hi[e]%(size a)] and return it. Therefore, there is a small
    probability of a false positive for membership queries if all indices
    collide with previously inserted elements

    Here we will work with a simplified version, where the bloom filter uses a
    single hash function and the size of the array is equal to the size of the
    hash function value space. We will consider a scenario of a client that
    executes a sequence of insertions followed by a single membership query for
    an element not in the filter, and want to reason about the probability of a
    false positive *)

Section bloom_filter_single.



  Variable filter_size : nat.
  Variable key_size : nat.

  Context `{!erisGS Σ, !hash_function Σ}.

  (** Instead of computing the probability of false positive explicitly, we will
      use a recurrence relation, which will simplify the math in the proof.

      The recurrence below corresponds to the probability of false positive of one
      membership query after inserting m elements into a Bloom filter that
      initially contains b bits set to 1 *)

  Fixpoint fp_error (m b : nat) : R :=
    if bool_decide (b >= filter_size + 1) then 1 else
      (match m with
      (** If we are not inserting any more elements, then the probability of false
          positive is the probability of hitting one of the bits set to 1 *)
      | 0 => b/(filter_size + 1)
      (** If we are inserting S m' elements, then the first one will be hashed
          into a bit set to 1 with probability (b / (filter_size + 1)) and to a
          bit set to 0 with probability (filter_size + 1 - b), and we keep
          computing recurively
      *)
      | S m' => (b / (filter_size + 1)) * fp_error m' b +
               ((filter_size + 1 - b) / (filter_size + 1)) * fp_error m' (S b)
       end)%R.

  (** Some auxiliary lemmas about fp_error *)

  Lemma fp_error_max (m b : nat) :
    (filter_size + 1 ≤ b) ->
    fp_error m b = 1.
  Proof.
    intros Hb.
    destruct m; simpl.
    - case_bool_decide; done.
    - case_bool_decide; done.
  Qed.

  Lemma fp_error_unfold_S (m b : nat)  :
    fp_error (S m) b =
      if bool_decide (b >= filter_size + 1) then 1 else
        ((b / (filter_size + 1)) * fp_error m b +
               ((filter_size + 1 - b) / (filter_size + 1)) * fp_error m (S b))%R.
  Proof.
    auto.
  Qed.


  Lemma fp_error_bounded (m b : nat) :
    (0 <= fp_error m b <= 1)%R.
  Proof.
    revert b.
    induction m; intros b.
    - simpl.
      case_bool_decide as H; [real_solver |].
      split.
      + apply Rcomplements.Rdiv_le_0_compat; real_solver.
      + apply not_ge in H.
        apply (Rcomplements.Rdiv_le_1 b); [real_solver |].
        left.
        apply lt_INR in H.
        rewrite plus_INR /= in H.
        real_solver.
   - simpl.
     case_bool_decide as H; [real_solver |].
     replace ((filter_size + 1 - b) / (filter_size + 1))%R with
       ( 1 - b / (filter_size + 1))%R; last first.
     {
       rewrite {2}/Rdiv.
       rewrite (Rmult_plus_distr_r).
       rewrite Rmult_inv_r; [real_solver |].
       pose proof (pos_INR filter_size).
       real_solver.
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



  Lemma fp_error_mon_2 (m b : nat):
    (fp_error m b <= fp_error m (S b))%R.
  Proof.
    revert b.
    induction m; intros b.
    - rewrite {2}/fp_error.
      case_bool_decide.
      + apply fp_error_bounded.
      + rewrite /fp_error.
        rewrite bool_decide_eq_false_2.
        * apply Rmult_le_compat_r.
          ** real_solver.
          ** rewrite S_INR.
             real_solver.
        * nat_solver.
    - rewrite (fp_error_unfold_S _ (S b)).
      case_bool_decide as H.
      + apply fp_error_bounded.
      + rewrite fp_error_unfold_S.
        rewrite bool_decide_eq_false_2; last by nat_solver.
        assert(
            (filter_size + 1 - b) / (filter_size + 1) * fp_error m (S b) =
            (filter_size + 1 - S b) / (filter_size + 1) * fp_error m (S b) +
              1 / (filter_size + 1) * fp_error m (S b) )%R as ->.
        { rewrite S_INR. real_solver. }
        assert(
            S b / (filter_size + 1) * fp_error m (S b) =
            b / (filter_size + 1) * fp_error m (S b) +
            1 / (filter_size + 1) * fp_error m (S b))%R as ->.
        { rewrite S_INR. real_solver. }
        rewrite Rplus_assoc.
        * apply Rplus_le_compat.
          ** apply Rmult_le_compat.
             *** real_solver.
             *** apply fp_error_bounded.
             *** apply Rmult_le_compat_r; [real_solver|].
                 real_solver.
             *** apply IHm.
          ** rewrite Rplus_comm.
             apply Rplus_le_compat_l.
             apply Rmult_le_compat_l; [|apply IHm].
             *** left.
                 apply Rdiv_lt_0_compat.
                 **** apply not_ge, lt_INR in H.
                      rewrite S_INR plus_INR /= in H.
                      rewrite S_INR.
                      real_solver.
                 **** real_solver.
    Qed.


  Lemma fp_error_mon_1 (m b : nat):
    (fp_error m b <= fp_error (m + 1) b)%R.
  Proof.
    replace (m+1) with (S m) by nat_solver.
    rewrite fp_error_unfold_S.
    case_bool_decide.
    - apply fp_error_bounded.
    - transitivity
        (b / (filter_size + 1) * fp_error m b +
           (filter_size + 1 - b) / (filter_size + 1) * fp_error m b)%R.
      + rewrite -Rmult_plus_distr_r.
        rewrite -{1}(Rmult_1_l (fp_error m b)).
        apply Rmult_le_compat_r; [apply fp_error_bounded|].
        rewrite -Rmult_plus_distr_r.
        replace (b + (filter_size + 1 - b))%R with
          (filter_size + 1)%R by real_solver.
        rewrite -Rdiv_def.
        rewrite Rdiv_diag; real_solver.
      + apply Rplus_le_compat_l.
        apply Rmult_le_compat_l; [|apply fp_error_mon_2].
        left.
        apply Rdiv_lt_0_compat; [|real_solver].
        apply not_ge, lt_INR in H.
        rewrite plus_INR /= in H.
        real_solver.
  Qed.

    Lemma fp_error_weaken (m b : nat):
      (fp_error 0 b <= fp_error m b)%R.
    Proof.
      revert b.
    induction m; intros b; [real_solver |].
    pose proof (IHm (S b)) as H2.
    assert (fp_error 0 b <= fp_error 0 (S b))%R as H3.
    {
      rewrite /fp_error.
      case_bool_decide as H4; case_bool_decide as H5.
      - real_solver.
      - nat_solver.
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
      + apply Rmult_le_compat_l; [|real_solver].
        apply Rcomplements.Rdiv_le_0_compat; [|real_solver].
        apply not_ge in H.
        apply lt_INR in H.
        rewrite plus_INR /= in H.
        real_solver.
  Qed.

  Lemma fp_error_step (m b: nat) :
    (fp_error m b * b +
    fp_error m (b + 1) * (filter_size + 1 - b) <=
    fp_error (m + 1) b * (filter_size + 1))%R.
  Proof.
    replace (m+1) with (S m) by nat_solver.
    simpl.
    case_bool_decide.
    * rewrite fp_error_max /=; auto.
      rewrite fp_error_max /=; [|nat_solver].
      real_solver.
    * right.
      replace (S b) with (b + 1) by nat_solver.
      rewrite (Rmult_comm (b / (filter_size + 1))).
      rewrite (Rmult_comm ((filter_size + 1 - b) / (filter_size + 1))).
      rewrite Rmult_plus_distr_r.
      rewrite !(Rmult_assoc _ _ (filter_size + 1)).
      rewrite !Rinv_l; [real_solver|].
      real_solver.
  Qed.


  (** Below we present the code for the Bloom filter. It consists of three
      methods: initialization, insertion and querying

      Code for initializing the bloom filter. It first initializes a hash
      function hf, then it creates an array arr and sets every element to false.
      The result is the pair (hf, arr) *)

  Definition init_bloom_filter : expr :=
    λ: "_" ,
      let: "hf" := init_hash #key_size #filter_size in
      let: "arr" := array_init #(S filter_size) (λ: "x", #false)%E in
      let: "l" := ref ("hf", "arr") in
      "l".


  (** The insertion method receives a bloom filter (hf, arr) and a value v to be
      inserted. Then, an index i is computed by computing hf v, and arr[i] is
      set to true *)

  Definition insert_bloom_filter : expr :=
    λ: "l" "v" ,
      let, ("hf", "arr") := !"l" in
      let: "i" := "hf" "v" in
      "arr" +ₗ "i" <- #true.

   (** The lookup method receives a bloom filter (hf, arr) and a value v to be
       looked up. Then, an index i is computed by computing hf v, and the value
       of arr[i] is looked up and returned. *)


  Definition lookup_bloom_filter : expr :=
    λ: "l" "v" ,
      let, ("hf", "arr") := !"l" in
      let: "i" := "hf" "v" in
      !("arr" +ₗ "i").

  (**  ** Representation predicate for Bloom filters *)

  (** Before introducing the representation predicate for the Bloom filter, we
      define an auxiliary predicate that states that the contents of the array
      are correct. Here the arguments are:
      - m : the abstract map representing the current view of the hash function
      - arr : the bloom filter array
      - els : the set of natural numbers currently represented by the Bloom
        filter
      - idxs : the set of indices currently set to true in the array

      Note that this is a pure Rocq proposition.
  *)

  Definition bloom_filter_correct_content
    (m : gmap nat nat) (arr : list val) (els : gset nat) (idxs : gset nat) :=
    (** The set of elements coincides with the domain of m *)
    (els = dom m) /\
    (** The image of every element is in idxs *)
    (forall e, e ∈ els -> (m !!! e) ∈ idxs) /\
    (length arr = S filter_size) /\
    (size idxs ≤ filter_size + 1) /\
    (** Every arr[i] in idxs is set to true *)
    (forall i, i ∈ idxs -> arr !! i = Some #true) /\
    (** Every idx is smaller than the size of the filter array *)
    (forall i, i ∈ idxs -> (i < S filter_size)%nat) /\
    (** Every arr[i[] within bounds not in is set to false *)
    (forall i, i < length arr -> i ∉ idxs -> arr !! i = Some #false).


  (** Representing probabilistic error as a separation logic resource has the
      advantage that it enables new reasoning principles. Here, we will show a
      form of "amortized error". Instead of spending error credits on every
      operation of the array, we will only pay once on initialization. The error
      credits will then be stored in the representation predicate for the Bloom
      filter, as a form of "error potential". The operations we will later run
      on the Bloom filter will have access to that error budget as they need.

     The representation predicate for the Bloom filter is below. We expose:
      - l : the location containing the Bloom filter
      - els : the set currently represented by the Bloom filter
      - rem : the number of remaining insertions. Although this limits the
        expressivity of the spec, it simplifies the proof by allowing us to use
        amortized error reasoning
   *)

  Definition is_bloom_filter (l : loc) (els : gset nat) (rem : nat) : iProp Σ :=
    (** A bloom filter logically consists of:
       - hf: a hash function
       - m : an abstract map that represents the hash function
       - a : a reference to the array
       - arr : the array
       - idxs : the set of indices currently set to true in arr. Note
         that we expose them at this point for convenience, when hashing
         a new element we will want to distribute credits depending on
         whether the new index falls or not in idxs

        Additionally, the Bloom filter owns ↯ (fp_error rem (size idxs)), which
        is the error budget we need to avoid a false positive on an insertion
        query after inserting rem elements.
    *)
    ∃ hf m a arr (idxs : gset nat),
      ↯ (fp_error rem (size idxs)) ∗
      l ↦ (hf, LitV (LitLoc a))%V ∗
      (a ↦∗ arr) ∗
      hashfun filter_size hf m ∗
      ⌜bloom_filter_correct_content m arr els idxs⌝.

  (** We will now prove a series of lemmas that will allow us to work with the
      representation predicates in a more abstract fashion. *)


  (** The set of elements coindices with the domain of the map *)

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

  (** All indices within range are in the domain of the array *)

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

  (** All indices in idxs are set to [true] in the array *)

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

  (** All indices within range not in idxs are set to [false] in the array *)

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

  (** All elements in the codomain of the map are in idxs *)

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

  (** All elements in idxs are within range *)

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


  (** Below, we define some lemmas to initialize and update the Bloom
      filter representation predicate.

      First, an empty Bloom filter is correctly represented by an empty map, an
      array set to [false] everywhere, and empty sets of elements and indices
  *)

  Lemma bloom_filter_init_content (arr : list val) :
    length arr = S filter_size ->
    (∀ (k : nat) (x : val), arr !! k = Some x → x = #false) ->
    bloom_filter_correct_content ∅ arr ∅ ∅.
  Proof.
    intros Hlen Hf.
    repeat split; auto.
    - rewrite size_empty.
      nat_solver.
    - set_solver.
    - set_solver.
    - intros i Hi Hi2.
      destruct (lookup_lt_is_Some_2 arr i Hi) as [v Hv].
      specialize (Hf _ _ Hv).
      simplify_eq; done.
  Qed.


  (** We will use this lemma to update the content of the bloom filter with a
     new element k when there is no collision for the new index v. This means:
     - The map gets updated with key-value pair (k,v)
     - The array gets updated by setting arr[v] to true
     - k gets added to the set of elements
     - v gets added to the set of indices
   *)


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
        split; [nat_solver|].
        simpl.
        replace (filter_size + 1) with (S filter_size) by nat_solver.
        apply Hidxs.
        set_solver.
      }
      etransitivity.
      *** apply subseteq_size, Hsub.
      *** rewrite size_difference.
          **** rewrite size_set_seq size_singleton.
               nat_solver.
          **** apply singleton_subseteq_l.
               apply elem_of_set_seq.
               split; nat_solver.
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


  (** We will use this lemma to update the content of the bloom filter with a
     new element k when there is a collision for the new index v. This means:
     - The map gets updated with key-value pair (k,v)
     - The array gets updated by setting arr[v] to true (though note
       it must have been true before)
     - k gets added to the set of elements

     However, the set of indices does not need be updated
   *)


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

 (**  ** Proving the specifications for the Bloom filter  *)

 (** We will now prove specs for all the Bloom filter methods.

    When initializing the bloom tilter we will choose how many insertions (rem)
    we plan to do, and will have to pay ↯ (fp_error rem 0). The result will be
    an empty bloom filter that still allows rem insertions. *)

 Lemma bloom_filter_init_spec (rem : nat) :
    {{{ ↯ (fp_error rem 0) }}}
      init_bloom_filter #()
      {{{ (l:loc), RET #l ; is_bloom_filter l ∅ rem }}}.
 Proof.
    iIntros (Φ) "Herr HΦ".
    unfold init_bloom_filter.
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
      unfold is_bloom_filter.
      iExists hf, ∅, a, arr, ∅.
      rewrite size_empty.
      iFrame.
      iPureIntro.
      eapply bloom_filter_init_content.
      - nat_solver.
      - auto.
  Qed.


  (**  The spec below describes inserting a new element, not in the current
       filter. Note that we require that at least 1 extra insertion must
       be possible, i.e. the number of remaining insertions must be a successor
   *)

  Lemma bloom_filter_insert_fresh_spec (l : loc) (els : gset nat) (x rem : nat) :
    {{{ is_bloom_filter l els (rem + 1) ∗ ⌜ x ∉ els ⌝ }}}
      insert_bloom_filter #l #x
    {{{ RET #() ; is_bloom_filter l (els ∪ {[x]}) rem }}}.
  Proof using erisGS0 filter_size hash_function0 key_size Σ.
    iIntros (Φ) "(Hbf & %Hx ) HΦ".
    wp_pures.
    unfold is_bloom_filter at 1.
    iDestruct "Hbf" as (hf m a arr idxs) "(Herr & Hl & Ha & Hhf & %Hcont)".
    wp_load.
    wp_pures.
    (** We now get to the point in the proof where error credits are used. Note
        here how useful the recurrence relation is. We can simply assign ↯
        (fp_error rem (size idxs)) to the branch where the new index falls in
        idxs (i.e. the set of indices set to 1 does not grow) and we assign ↯
        (fp_error rem (size idxs)) to the branch where the new index falls
        outside of idxs. *)
    wp_apply (hash_query_spec_fresh x idxs
       (fp_error (rem + 1) (size idxs))
       (fp_error rem (size idxs))
       (fp_error rem (size idxs + 1))
       filter_size hf m with "[$]"); auto.
    + rewrite eq_None_not_Some.
      rewrite <- bfcc_map_els; eauto.
    + apply fp_error_bounded.
    + apply fp_error_bounded.
    + intros. eapply bfcc_idx_bd; eauto.
    +
      (** The previously proven lemma for distributing error credits for
          on insertion of the bloom filter clears this goal in one line
      *)
      apply fp_error_step.
    +iIntros (v) "(% & ? & [(% & ?) | (% &? )])".
      (** We first consider the case where v does not fall in idxs *)
      * wp_pures.
        wp_apply (wp_store_offset with "Ha").
        {
          eapply bfcc_lookup_arr; eauto.
        }
        iIntros "Ha".
        iApply "HΦ".
        unfold is_bloom_filter.
        (** We now have to reconstruct the bloom filter predicate *)
        iExists hf, (<[x:=v]> m), a, (<[v:=#true]> arr), (idxs ∪ {[v]}).
        iFrame.
        rewrite size_union; [|set_solver].
        rewrite size_singleton.
        iFrame.
        iPureIntro.
        (** Finally, we have to prove that the new contents of the bloom filter
           are correct *)
        by apply bloom_filter_update_content_no_coll.

      (** We now have the case where v falls in idxs *)
      * (* exercise *)
        (* Admitted. *)

        (* Sample solution *)
        wp_pures.
        wp_apply (wp_store_offset with "Ha").
        {
          eapply bfcc_lookup_arr; eauto.
        }
        iIntros "Ha".
        iApply "HΦ".
        unfold is_bloom_filter.
        iExists hf, (<[x:=v]> m), a, (<[v:=#true]> arr), idxs.
        simpl.
        iFrame.
        iPureIntro.
        by apply bloom_filter_update_content_coll.
  Qed.

   (** For completeness, let's also prove a spec where we insert a previously
      inserted element. In principle, there is no need to spend credits here,
      but we will do it nevertheless to facilitate reasoning about a sequence of
      insertions. *)

  Lemma bloom_filter_insert_old_spec (l : loc) (els : gset nat) (x rem : nat) :
    {{{ is_bloom_filter l els (rem + 1) ∗ ⌜ x ∈ els ⌝ }}}
      insert_bloom_filter #l #x
      {{{ RET #() ; is_bloom_filter l els rem }}}.
  Proof using erisGS0 filter_size hash_function0 key_size Σ.
    iIntros (Φ) "(Hbf & %Hx ) HΦ".
    wp_pures.
    unfold is_bloom_filter at 1.
    iDestruct "Hbf" as (hf m a arr idxs) "(Herr & Hl & Ha & Hhf & %Hcont)".
    wp_load.
    wp_pures.
    rewrite bfcc_map_els in Hx; eauto.
    destruct Hx as [v Hv].
    (* exercise *)
    (* Admitted. *)

    (* Sample solution: *)
    wp_apply (hash_query_spec_prev x _ v hf m with "[$]"); eauto.
    iIntros "Hhf".
    wp_pures.
    iPoseProof (hash_val_in_bd with "Hhf") as "%Hvbd"; eauto.
    wp_apply (wp_store_offset with "Ha").
    {
       eapply bfcc_lookup_arr; eauto.
    }
    iIntros "Ha".
    iApply "HΦ".
    rewrite /is_bloom_filter.
    (** We now have to reconstruct the bloom filter predicate *)
    iExists hf, m, a, arr, idxs.
    iFrame.
    iPoseProof (ec_weaken with "Herr") as "Herr".
    {
      split; last first.
      - apply fp_error_mon_1.
      - apply fp_error_bounded.
    }
    iFrame.
    iSplit; auto.
    assert (<[v:=#true]> arr = arr) as ->; auto.
    apply list_insert_id.
    eapply bfcc_idxs_arr_true; eauto.
    eapply bfcc_map_to_idx; eauto.
  Qed.


  (** For simplicity, we will unify both specs into one *)

  Lemma bloom_filter_insert_spec (l : loc) (els : gset nat) (x rem : nat) :
    {{{ is_bloom_filter l els (rem + 1) }}}
      insert_bloom_filter #l #x
    {{{ RET #() ; is_bloom_filter l (els ∪ {[x]}) rem }}}.
  Proof using erisGS0 filter_size hash_function0 key_size Σ.
    iIntros (Φ) "Hbf HΦ".
    destruct (decide (x∈els)).
    - wp_apply (bloom_filter_insert_old_spec with "[$Hbf]"); auto.
      iIntros "Hbf".
      iApply "HΦ".
      replace (els ∪ {[x]}) with els by set_solver.
      done.
    - wp_apply (bloom_filter_insert_fresh_spec with "[$Hbf]"); done.
  Qed.


  (** We also prove two specs for lookups. First, we prove a spec for the case
      where the elements we lookup x is in the set of elements els. In this case,
      we should deterministically return true, since the element must have been
      hashed before, and thus can be queried without spending error credits *)

  Lemma bloom_filter_lookup_in_spec (l : loc) (els : gset nat) (x rem : nat) :
    {{{ is_bloom_filter l els rem ∗ ⌜ x ∈ els ⌝ }}}
      lookup_bloom_filter #l #x
      {{{ v, RET v ; ⌜v = #true⌝ }}}.
  Proof using erisGS0 filter_size hash_function0 key_size Σ.
    iIntros (Φ) "(Hbf & %Hx ) HΦ".
    unfold is_bloom_filter.
    iDestruct "Hbf" as (hf m a arr idxs) "(Herr & Hl & Ha & Hhf & %Hcont)".
    wp_pures.
    wp_load.
    wp_pures.
    destruct (bfcc_map_els m arr els idxs x Hcont) as [H1 H2].
    destruct (H1 Hx) as [v Hv].
    (** Here we use the spec for querying a previously hashed element *)
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


  (**
     Finally we have the spec for looking up an element x that is not in the
     bloom filter. The error credits that we will use are inside the representation
     predicate, and currently equal ↯ (size idxs / (filter_size + 1)). This means
     we can spend them to avoid hashing x to a value in idxs, and thus we can
     ensure we return false
  *)


  Lemma bloom_filter_lookup_not_in_spec (l : loc) (s : gset nat) (x : nat) :
    {{{ is_bloom_filter l s 0 ∗ ⌜ x ∉ s ⌝ }}}
      lookup_bloom_filter #l #x
      {{{ v, RET v ; ⌜v = #false⌝ }}}.
  Proof using erisGS0 filter_size hash_function0 key_size Σ.
    iIntros (Φ) "(Hbf & %Hx) HΦ".
    unfold is_bloom_filter.
    iDestruct "Hbf" as (hf m a arr idxs) "(Herr & Hl & Ha & Hhf & %Hcont)".
    wp_pures.
    wp_load.
    wp_pures.
    simpl.
    (** We get rid of a trivial case where size idxs = filter_size + 1 *)
    case_bool_decide.
    {
      iExFalso.
      iApply (ec_contradict with "[$]").
      real_solver.
    }
    (** We now use the spec for hasing a fresh element. We have enough credits
      to completely avoid idxs *)
    (* exercise *)
    (* Admitted. *)

    (* Sample solution: *)
    wp_apply (hash_query_spec_fresh_avoid  _ idxs
                _ filter_size _ m
               with "[$]"); auto.
    - rewrite eq_None_not_Some.
      rewrite <- bfcc_map_els; eauto.
    - rewrite -Rmult_div_swap.
      rewrite Rmult_div_l //.
      real_solver.
    - iIntros (v) "(%Hv & Hhfw & %Hidxs)".
      wp_pures.
      wp_apply (wp_load_offset _ _ _ _ _ #false with "Ha").
      {
        eapply bfcc_idxs_arr_false; eauto.
      }
      iIntros "Ha".
      iApply "HΦ".
      done.
  Qed.

  (** ** A client of the Bloom filter *)

  (** To conclude, let's write a client of the bloom filter. This will create an
     empty bloom filter, execute a sequence of insertions and then execute a
     single lookup. The main loop, which takes care of the insertions is shown
     below. *)


  Definition insert_bloom_filter_loop_seq : val :=
    (rec: "aux" "bfl" "ks" :=
       match: "ks" with
         NONE => #()
       | SOME "p" =>
           let: "h" := Fst "p" in
           let: "t" := Snd "p" in
           (insert_bloom_filter "bfl" "h") ;; ("aux" "bfl" "t")
       end).

  (** Finally, we can write the code for the Bloom filter client *)

  Definition main_bloom_filter_seq (ksv ktest : val) : expr :=
      let: "bfl" := init_bloom_filter #() in
      insert_bloom_filter_loop_seq "bfl" ksv ;;
      lookup_bloom_filter "bfl" ktest.


  (** Let's now prove a spec for the loop. We will prove one with a stronger
    premise to get a stronger induction hypothesis. Assuming that we start with
    elements els, and we still have budget for (length ks) insertions left, we
    can insert all of the elements in ks and at the end get a bloom filter
    containing els ∪ ks.

    The proof follows by induction on ks and relatively simple separation logic
    reasoning, using the specs we have proven above. *)

  Lemma insert_bloom_filter_loop_seq_spec bfl els
          (ks : list nat) (ksv : val) :
    is_list ks ksv ->
    {{{ is_bloom_filter bfl els (length ks) }}}
      insert_bloom_filter_loop_seq #bfl ksv
    {{{ v, RET v; is_bloom_filter bfl (els ∪ (list_to_set ks)) 0 }}}.
  Proof using erisGS0 filter_size hash_function0 key_size Σ.
    iInduction ks as [|k ks'] "IH" forall (els ksv).
    - iIntros (Hksv Φ) "Hbf HΦ".
      simpl in Hksv.
      simplify_eq.
      unfold insert_bloom_filter_loop_seq.
      wp_pures.
      iApply "HΦ".
      simpl.
      replace (els ∪ ∅) with els by set_solver.
      done.
    - iIntros (Hksv Φ) "Hbf HΦ".
      destruct Hksv as [kv [Hrw Htail]].
      rewrite Hrw.
      unfold insert_bloom_filter_loop_seq at 2.
      do 12 wp_pure.
      fold insert_bloom_filter.
      wp_bind (insert_bloom_filter _ _).
      simpl.
      replace (S (length ks')) with (length ks' + 1) by nat_solver.
      wp_apply (bloom_filter_insert_spec with "Hbf").
      iIntros "Hbf".
      do 2 wp_pure.
      fold insert_bloom_filter_loop_seq.
      iApply ("IH" with "[] Hbf"); auto.
      iModIntro.
      iIntros (v) "Hbf".
      iApply "HΦ".
      replace (els ∪ ({[k]} ∪ list_to_set ks'))
        with (els ∪ {[k]} ∪ list_to_set ks') by set_solver.
      by iFrame.
  Qed.

 (** Finally, the spec for the main program. If we own ↯ (fp_error (length ks) 0),
     and ktest ∉ ks, then we can create a Bloom filter, insert all elements in
     ks in the filter, lookup ktest, and get false as a result. In other words,
     the probability of a false positive is upper bounded by
     ↯ (fp_error (length ks) 0) *)

 Lemma main_bloom_filter_seq_spec (ks : list nat) (ksv : val) (ktest : nat) :
      is_list ks ksv ->
      ktest ∉ ks ->
      {{{  ↯ (fp_error (length ks) 0) }}}
        main_bloom_filter_seq ksv #ktest
      {{{ v, RET v; ⌜ v = #false ⌝ }}}.
 Proof using erisGS0 filter_size hash_function0 key_size Σ.
   iIntros (Hksv Hktest Φ) "Herr HΦ".
   rewrite /main_bloom_filter_seq.
   wp_apply (bloom_filter_init_spec with "Herr"); auto.
   iIntros (bfl) "Hbf".
   wp_pures.
   wp_bind (insert_bloom_filter_loop_seq _ _).
   wp_apply (insert_bloom_filter_loop_seq_spec with "Hbf"); eauto.
   iIntros (?) "Hbf".
   do 2 wp_pure.
   wp_apply (bloom_filter_lookup_not_in_spec with "[$Hbf]"); auto.
   iPureIntro.
   set_solver.
 Qed.




End bloom_filter_single.


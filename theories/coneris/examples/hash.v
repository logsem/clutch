From stdpp Require Export fin_maps.
From iris.algebra Require Import excl_auth numbers gset_bij.
From clutch.coneris Require Export coneris lib.map.
Import Hierarchy.
Set Default Proof Using "Type*".

Section simple_bit_hash.

  Context `{!conerisGS Σ, HinG: inG Σ (gset_bijR nat nat)}.

  Variable val_size : nat.

  (* A hash function's internal state is a map from previously queried keys to their hash value *)
  Definition init_hash_state : val := init_map.

  (* To hash a value v, we check whether it is in the map (i.e. it has been previously hashed).
     If it has we return the saved hash value, otherwise we draw a hash value and save it in the map *)
  Definition compute_hash_specialized hm : val :=
    λ: "v",
      match: get hm "v" with
      | SOME "b" => "b"
      | NONE =>
          let: "b" := (rand #val_size) in
          set hm "v" "b";;
          "b"
      end.
  Definition compute_hash : val :=
    λ: "hm" "v",
      match: get "hm" "v" with
      | SOME "b" => "b"
      | NONE =>
          let: "b" := (rand #val_size) in
          set "hm" "v" "b";;
          "b"
      end.

  (* init_hash returns a hash as a function, basically wrapping the internal state
     in the returned function *)
  Definition init_hash : val :=
    λ: "_",
      let: "hm" := init_hash_state #() in
      compute_hash "hm".

  (* A hash function is collision free if the partial map it
     implements is an injective function *)
  Definition coll_free (m : gmap nat nat) :=
    forall k1 k2,
    is_Some (m !! k1) ->
    is_Some (m !! k2) ->
    m !!! k1 = m !!! k2 ->
    k1 = k2.
  
  Definition hash_view_auth m γ := (own γ (gset_bij_auth (DfracOwn 1) (map_to_set pair m)))%I.
  Definition hash_view_frag k v γ := (own γ (gset_bij_elem k v)).

  Lemma hash_view_auth_coll_free m γ2:
    hash_view_auth m γ2 -∗ ⌜coll_free m⌝.
  Proof.
    rewrite /hash_view_auth.
    iIntros "H".
    iDestruct (own_valid with "[$]") as "%H".
    rewrite gset_bij_auth_valid in H.
    iPureIntro.
    intros k1 k2 H1 H2 H3.
    destruct H1 as [v1 K1].
    destruct H2 as [v2 H2].
    assert (v1 = v2) as ->; first by erewrite !lookup_total_correct in H3.
    unshelve epose proof (H k1 v2 _) as [_ H']; first by rewrite elem_of_map_to_set_pair.
    unshelve epose proof (H' k2 _) as ->; last done.
    by rewrite elem_of_map_to_set_pair.
  Qed.

  Lemma hash_view_auth_duplicate_frag m n b γ2:
    m!!n=Some b -> hash_view_auth m γ2 ==∗ hash_view_auth m γ2 ∗ hash_view_frag n b γ2.
  Proof.
    iIntros (Hsome) "Hauth".
    rewrite /hash_view_auth/hash_view_frag.
    rewrite -own_op.
    iApply own_update; last done.
    rewrite -core_id_extract; first done.
    apply bij_view_included.
    rewrite elem_of_map_to_set.
    naive_solver.
  Qed.
  
  Lemma hash_view_auth_frag_agree m γ2 k v:
    hash_view_auth m γ2  ∗ hash_view_frag k v γ2 -∗
    ⌜m!!k=Some v⌝.
  Proof.
    rewrite /hash_view_auth/hash_view_frag.
    rewrite -own_op.
    iIntros "H".
    iDestruct (own_valid with "[$]") as "%H".
    rewrite bij_both_valid in H.
    destruct H as [? H].
    rewrite elem_of_map_to_set in H.
    iPureIntro.
    destruct H as (?&?&?&?).
    by simplify_eq.
  Qed.

  Lemma hash_view_auth_insert m n x γ:
    m!!n=None ->
    Forall (λ m : nat, x ≠ m) (map (λ p : nat * nat, p.2) (map_to_list m)) ->
    hash_view_auth m γ ==∗
    hash_view_auth (<[n:=x]> m) γ ∗ hash_view_frag n x γ.
  Proof.
    iIntros (H1 H2) "H".
    rewrite /hash_view_auth/hash_view_frag.
    rewrite -own_op.
    iApply own_update; last done.
    rewrite -core_id_extract; last first.
    { apply bij_view_included. rewrite elem_of_map_to_set.
      eexists _, _; split; last done.
      apply lookup_insert.
    }
    etrans; first apply gset_bij_auth_extend; last by rewrite map_to_set_insert_L.
    - intros b. rewrite elem_of_map_to_set; intros (?&?&?&?).
      simplify_eq.
    - intros a. rewrite elem_of_map_to_set; intros (?&?&?&?).
      simplify_eq.
      rewrite Forall_map in H2.
      rewrite Forall_forall in H2.
      unfold not in H2.
      eapply H2; [by erewrite elem_of_map_to_list|done].
  Qed.

  Definition hashfun f m : iProp Σ :=
    ∃ (hm : loc), ⌜ f = compute_hash_specialized #hm ⌝ ∗
                  map_list hm ((λ b, LitV (LitInt (Z.of_nat b))) <$> m) ∗
                  ⌜map_Forall (λ ind i, (0<= i <=val_size)%nat) m⌝
  .

  Definition coll_free_hashfun f m γ: iProp Σ :=
    hashfun f m ∗ hash_view_auth m γ.

  Lemma coll_free_hashfun_implies_hashfun f m γ:
    coll_free_hashfun f m γ -∗ hashfun f m.
  Proof.
    by iIntros "[??]".
  Qed.

  #[global] Instance timeless_hashfun f m :
    Timeless (hashfun f m).
  Proof. apply _. Qed.

  #[global] Instance timeless_hashfun_amortized f m γ:
    Timeless (coll_free_hashfun f m γ).
  Proof. apply _. Qed.

  Lemma coll_free_hashfun_implies_coll_free f m γ:
    coll_free_hashfun f m γ-∗ ⌜coll_free m⌝.
  Proof.
    iIntros "[??]".
    by iApply hash_view_auth_coll_free.
  Qed.

  Lemma hashfun_implies_bounded_range f m idx x:
    hashfun f m -∗ ⌜m!!idx = Some x⌝ -∗ ⌜(0<=x<=val_size)%nat⌝.
  Proof.
    iIntros "(%&%&H&%K) %".
    iPureIntro.
    by eapply map_Forall_lookup_1 in K.
  Qed.

  Lemma coll_free_hashfun_implies_bounded_range f m idx x γ:
    coll_free_hashfun f m γ -∗ ⌜m!!idx = Some x⌝ -∗ ⌜(0<=x<=val_size)%nat⌝.
  Proof.
    iIntros "(H&?) %".
    by iApply (hashfun_implies_bounded_range with "[$]").
  Qed.

  Lemma wp_init_hash E :
    {{{ True }}}
      init_hash #() @ E
    {{{ f, RET f; ∃ γ, |={E}=> coll_free_hashfun f ∅ γ}}}.
  Proof.
    rewrite /init_hash.
    iIntros (Φ) "_ HΦ".
    wp_pures. rewrite /init_hash_state.
    wp_apply (wp_init_map with "[//]").
    iIntros (?) "Hm". wp_pures.
    rewrite /compute_hash. wp_pures.
    iAssert (|==> (∃ γ2, hash_view_auth ∅ γ2))%I as ">(%γ2 & Hview)".
    { rewrite /hash_view_auth.
      iApply own_alloc.
      by rewrite gset_bij_auth_valid.
    }
    iApply "HΦ". repeat iModIntro. rewrite /coll_free_hashfun. by iFrame.
  Qed.

  Lemma coll_free_insert (m : gmap nat nat) (n : nat) (z : nat) :
    m !! n = None ->
    coll_free m ->
    Forall (λ x, z ≠ snd x) (map_to_list m) ->
    coll_free (<[ n := z ]>m).
  Proof.
    intros Hnone Hcoll HForall.
    intros k1 k2 Hk1 Hk2 Heq.
    apply lookup_insert_is_Some' in Hk1.
    apply lookup_insert_is_Some' in Hk2.
    destruct (decide (n = k1)).
    - destruct (decide (n = k2)); simplify_eq; auto.
      destruct Hk2 as [|Hk2]; auto.
      rewrite lookup_total_insert in Heq.
      rewrite lookup_total_insert_ne // in Heq.
      apply lookup_lookup_total in Hk2.
      rewrite -Heq in Hk2.
      eapply (Forall_iff (uncurry ((λ (k : nat) (v : nat), z ≠ v)))) in HForall; last first.
      { intros (?&?); eauto. }
      eapply map_Forall_to_list in HForall.
      rewrite /map_Forall in HForall.
      eapply HForall in Hk2; congruence.
    - destruct (decide (n = k2)); simplify_eq; auto.
      {
        destruct Hk1 as [|Hk1]; auto.
        rewrite lookup_total_insert in Heq.
        rewrite lookup_total_insert_ne // in Heq.
        apply lookup_lookup_total in Hk1.
        rewrite Heq in Hk1.
        eapply (Forall_iff (uncurry ((λ (k : nat) (v : nat), z ≠ v)))) in HForall; last first.
        { intros (?&?); eauto. }
        eapply map_Forall_to_list in HForall.
        rewrite /map_Forall in HForall.
        eapply HForall in Hk1; congruence.
      }
      rewrite ?lookup_total_insert_ne // in Heq.
      destruct Hk1 as [|Hk1]; try congruence; [].
      destruct Hk2 as [|Hk2]; try congruence; [].
      apply Hcoll; eauto.
  Qed.


  Lemma wp_hashfun_prev E f m (n : nat) (b : nat) :
    m !! n = Some b →
    {{{ hashfun f m }}}
      f #n @ E
    {{{ RET #b; hashfun f m }}}.
  Proof.
    iIntros (Hlookup Φ) "Hhash HΦ".
    iDestruct "Hhash" as (hm ->) "[H Hbound]".
    rewrite /compute_hash_specialized.
    wp_pures.
    wp_apply (wp_get with "[$]").
    iIntros (vret) "(Hhash&->)".
    rewrite lookup_fmap Hlookup /=. wp_pures. iModIntro. iApply "HΦ".
    iExists _. eauto.
  Qed.

  
  Lemma wp_coll_free_hashfun_prev E f m γ (n : nat) (b : nat) :
    m !! n = Some b →
    {{{ coll_free_hashfun f m γ }}}
      f #n @ E
    {{{ RET #b; coll_free_hashfun f m γ ∗ hash_view_frag n b γ }}}.
  Proof.
    iIntros (Hlookup Φ) "(Hhash & Hauth) HΦ".
    iDestruct "Hhash" as (hm ->) "[H Hbound]".
    rewrite /compute_hash_specialized.
    wp_pures.
    wp_apply (wp_get with "[$]").
    iIntros (vret) "(Hhash&->)".
    rewrite lookup_fmap Hlookup /=. wp_pures.
    iMod (hash_view_auth_duplicate_frag with "[$]") as "[??]"; first done.
    iModIntro. iApply "HΦ". by iFrame.
  Qed.

  Lemma wp_coll_free_hashfun_frag_prev E f m γ (n : nat) (b : nat) :
    {{{ coll_free_hashfun f m γ ∗ hash_view_frag n b γ}}}
      f #n @ E
    {{{ RET #b; coll_free_hashfun f m γ }}}.
  Proof.
    iIntros (Φ) "[[Hhash ?] #Hfrag] HΦ".
    iDestruct (hash_view_auth_frag_agree with "[$]") as "%".
    iApply (wp_coll_free_hashfun_prev with "[$]"); first done.
    iIntros "!> [??]".
    by iApply "HΦ".
  Qed.
  

  Lemma wp_insert_no_coll E f m (n : nat) γ:
    m !! n = None →
    {{{ coll_free_hashfun f m γ ∗ ↯ (nnreal_div (nnreal_nat (length (map_to_list m))) (nnreal_nat(val_size+1)))
    }}}
      f #n @ E
    {{{ (v : nat), RET #v; coll_free_hashfun f (<[ n := v ]>m) γ ∗ hash_view_frag n v γ }}}.
  Proof.
    iIntros (Hlookup Φ) "([Hhash Hauth] & Herr) HΦ".
    iDestruct "Hhash" as (hm ->) "[H %Hbound]".
    rewrite /compute_hash_specialized.
    wp_pures.
    wp_apply (wp_get with "[$]").
    iIntros (vret) "(Hhash&->)".
    rewrite lookup_fmap Hlookup /=. wp_pures.
    wp_bind (rand _)%E.
    wp_apply (wp_rand_err_list_nat _ val_size (map (λ p, snd p) (map_to_list m))); auto.
    rewrite map_length.
    rewrite plus_INR INR_1.
    iFrame.
    iIntros "%x %HForall".
    wp_pures.
    wp_apply (wp_set with "Hhash").
    iIntros "Hlist".
    wp_pures.
    iMod (hash_view_auth_insert with "[$]") as "[??]"; [done..|].
    iModIntro.
    iApply "HΦ".
    iFrame.
    rewrite /hashfun.
    iExists _.
    iSplit; first auto.
    iSplitL.
    - rewrite fmap_insert //.
    - iPureIntro.
      apply map_Forall_insert_2; last done.
      split.
      + lia.
      + pose proof (fin_to_nat_lt x).
        lia.
  Qed.


  Lemma wp_insert_avoid_set_adv E f m (n : nat) (xs : gset nat) (ε εI εO : nonnegreal) :
    m !! n = None →
    (forall x : nat, x ∈ xs -> (x < S val_size)%nat) ->
    (nonneg ε = εI * (size xs) / (val_size+1) + εO * (val_size +1 - size xs) / (val_size+1))%R ->
    {{{ hashfun f m ∗ ↯ ε }}}
      f #n @ E
      {{{ (v : nat), RET #v; ⌜ (v < S val_size)%nat ⌝ ∗ hashfun f (<[ n := v ]>m) ∗
                             ((⌜ v ∉ xs ⌝ ∗ ↯ εO ) ∨ (⌜ v ∈ xs ⌝ ∗ ↯ εI))
      }}}.
  Proof.
    iIntros (Hlookup Hlt HεEq Φ) "(Hhash & Herr) HΦ".
    iDestruct "Hhash" as (hm ->) "[H %Hbound]".
    rewrite /compute_hash_specialized.
    wp_pures.
    wp_apply (wp_get with "[$]").
    iIntros (vret) "(Hhash&->)".
    rewrite lookup_fmap Hlookup /=. wp_pures.

    wp_bind (rand _)%E.
    wp_apply (wp_rand_err_set_in_out _ _ xs ε εI εO); auto.
    - apply cond_nonneg.
    - apply cond_nonneg.
    - rewrite !match_nonneg_coercions.
      rewrite HεEq /=.
      rewrite -Rmult_plus_distr_r.
      rewrite Rmult_assoc.
      rewrite Rmult_inv_l; real_solver.
    - iFrame.
      iIntros "%x HK".
      wp_pures.
      wp_apply (wp_set with "Hhash").
      iIntros "Hlist".
      wp_pures.
      iModIntro.
      iApply "HΦ".
      iFrame.
      iSplitR.
      {
        iPureIntro.
        apply fin_to_nat_lt.
      }
      rewrite /hashfun.
      iExists hm.
      iSplit; first auto.
      iSplitL.
      * rewrite fmap_insert //.
      * iPureIntro.
        apply map_Forall_insert_2; last done.
        split.
        ** lia.
        ** pose proof (fin_to_nat_lt x).
           lia.
  Qed.


End simple_bit_hash.



Section amortized_hash.

  Class amortized_hashG Σ :=
    {
        amortized_hash_credit :: inG Σ (authR natR) ;
        amortized_hash_gset_bij :: inG Σ (gset_bijR nat nat)
      }.
       
  Context `{!conerisGS Σ, Hah: amortized_hashG Σ}.
  Variable val_size:nat.
  Variable max_hash_size : nat.
  Hypothesis max_hash_size_pos: (0<max_hash_size)%nat.
  (* Variable Hineq : (max_hash_size <= (val_size+1))%nat. *)
  Program Definition amortized_error : nonnegreal :=
    mknonnegreal ((max_hash_size-1) /(2*(val_size + 1)))%R _.
  Next Obligation.
    pose proof (pos_INR val_size) as H.
    pose proof (pos_INR max_hash_size) as H'.
    apply Rcomplements.Rdiv_le_0_compat; try lra.
    assert (1 <= INR max_hash_size); try lra.
    replace 1 with (INR 1); last simpl; [by apply le_INR|done].
  Qed.

  
  Definition hashfun_amortized f m γ: iProp Σ :=
    ∃ (k : nat) (ε : nonnegreal),
      hashfun val_size f m ∗
      ⌜k = size m⌝ ∗
      ⌜ (ε.(nonneg) = (((max_hash_size-1) * k)/2 - sum_n_m (λ x, INR x) 0%nat (k-1)) / (val_size + 1))%R⌝ ∗
      ↯ ε ∗
      (** token *)
      own γ (● max_hash_size) ∗
      own γ (◯ k) 
  .

  
  Definition coll_free_hashfun_amortized f m γ1 γ2: iProp Σ :=
    hashfun_amortized f m γ1 ∗
      (** gset_bij *)
      hash_view_auth m γ2.

  #[global] Instance timeless_coll_free_hashfun_amortized f m γ:
    Timeless (hashfun_amortized f m γ).
  Proof. apply _. Qed.


  Lemma coll_free_hashfun_amortized_implies_coll_free f m γ1 γ2:
    coll_free_hashfun_amortized f m γ1 γ2 -∗ ⌜coll_free m⌝.
  Proof.
    iIntros "[??]".
    by iApply hash_view_auth_coll_free. 
  Qed.

  Lemma hashfun_amortized_implies_bounded_range f m γ idx x:
    hashfun_amortized f m γ -∗ ⌜m!!idx = Some x⌝ -∗ ⌜(0<=x<=val_size)%nat⌝.
  Proof.
    iIntros "H %".
    iApply (hashfun_implies_bounded_range with "[H]"); [by iDestruct "H" as "(%&%&H&H')"|done].
  Qed.

  Lemma coll_free_hashfun_amortized_implies_bounded_range f m γ1 γ2 idx x:
    coll_free_hashfun_amortized f m γ1 γ2 -∗ ⌜m!!idx = Some x⌝ -∗ ⌜(0<=x<=val_size)%nat⌝.
  Proof.
    iIntros "(H&?) %".
    by iApply (hashfun_amortized_implies_bounded_range with "[$]").
  Qed.

  Lemma wp_init_hash_amortized E :
    {{{ True }}}
      init_hash val_size #() @ E
      {{{ f, RET f; |={E}=> ∃ γ1 γ2,  coll_free_hashfun_amortized f ∅ γ1 γ2 ∗ own γ1 (◯ max_hash_size) }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_apply wp_init_hash; first done.
    iIntros (f) "(%γ2&H)".
    iApply "HΦ".
    iMod ec_zero.
    iMod "H".
    iMod (own_alloc (● max_hash_size ⋅ ◯ (0+max_hash_size)%nat)) as (γ1) "[H● [? H◯]]"; first (simpl; by apply auth_both_valid_2).
    iModIntro.
    iExists _, _.
    iSplitR "H◯"; last done.
    iDestruct "H" as "[??]".
    (* iExists 0%nat, nnreal_zero. *)
    iFrame.
    iExists nnreal_zero.
    repeat (iSplit; [done|]). iFrame.
    iPureIntro.
    simpl.
    replace (sum_n_m _ _ _) with 0; first lra.
    rewrite sum_n_n. by simpl.
  Qed.


  Lemma hashfun_amortized_hashfun f m γ: ⊢ hashfun_amortized f m γ -∗ hashfun val_size f m.
  Proof.
    by iIntros "(%&%&?&?)".
  Qed.

  Lemma wp_hashfun_prev_amortized E f m γ (n : nat) (b : nat) :
    m !! n = Some b →
    {{{ hashfun_amortized f m γ }}}
      f #n @ E
      {{{ RET #b; hashfun_amortized f m γ}}}.
  Proof.
    iIntros (Hlookup Φ) "(%&%&Hhash&->&%&Herr) HΦ".
    wp_apply (wp_hashfun_prev with "[$Hhash]"); [done|].
    iIntros "H". iApply "HΦ".
    iExists _, _. iFrame. naive_solver.
  Qed.

  Lemma wp_coll_free_hashfun_prev_amortized E f m γ1 γ2 (n : nat) (b : nat) :
    m !! n = Some b →
    {{{ coll_free_hashfun_amortized f m γ1 γ2 }}}
      f #n @ E
      {{{ RET #b; coll_free_hashfun_amortized f m γ1 γ2 ∗ hash_view_frag n b γ2 }}}.
  Proof.
    iIntros (Hlookup Φ) "(H & Hauth) HΦ".
    iMod (hash_view_auth_duplicate_frag with "[$]") as "[??]"; first done.
    wp_apply (wp_hashfun_prev_amortized with "[$]"); [done|].
    iIntros "H". iApply "HΦ".
    by iFrame. 
  Qed.

  
  Lemma wp_coll_free_hashfun_prev_frag_amortized E f m γ1 γ2 (n : nat) (b : nat) :
    {{{ coll_free_hashfun_amortized f m γ1 γ2 ∗ hash_view_frag n b γ2 }}}
      f #n @ E
      {{{ RET #b; coll_free_hashfun_amortized f m γ1 γ2 }}}.
  Proof.
    iIntros (Φ) "([??] & #H') HΦ".
    iDestruct (hash_view_auth_frag_agree with "[$]") as "%".
    iApply (wp_coll_free_hashfun_prev_amortized with "[$]"); first done.
    iIntros "!> [??]".
    by iApply "HΦ".
  Qed.

  Lemma amortized_inequality (k : nat):
    (k <= max_hash_size)%nat ->
    0 <= ((max_hash_size-1) * k / 2 - sum_n_m (λ x : nat, INR x) 0 (k - 1)) / (val_size + 1).
  Proof.
    intros H.
    pose proof (pos_INR max_hash_size) as H1.
    pose proof (pos_INR val_size) as H2.
    pose proof (pos_INR k) as H3.
    apply Rcomplements.Rdiv_le_0_compat; last lra.
    assert (sum_n_m (λ x : nat, INR x) 0 (k - 1) = (k-1)*k/2) as ->.
    - clear.
      induction k.
      + simpl. rewrite sum_n_n.
        rewrite Rmult_0_r. by assert (0/2 = 0) as -> by lra.
      + clear. induction k.
        * simpl. rewrite sum_n_n.
          replace (_-_) with 0 by lra.
          rewrite Rmult_0_l. by assert (0/2 = 0) as -> by lra.
        * assert (S (S k) - 1 = S (S k - 1))%nat as -> by lia.
          rewrite sum_n_Sm; last lia.
          rewrite IHk.
          replace (plus _ _) with (((S k - 1) * S k / 2) + (S (S k - 1))) by done.
          assert (∀ k, (INR (S k) - 1) = (INR k)) as H'.
          { intros. simpl. case_match; first replace (1 - 1) with 0 by lra.
            - done.
            - by replace (_+1-1) with (INR (S n)) by lra.
          }
          rewrite !H'.
          replace (S k - 1)%nat with (k)%nat by lia.
          assert (k * (S k) + S k + S k = S k * S (S k)); last lra.
          assert (k * S k + S k + S k = S k * (k+1+1)) as ->; try lra.
          assert (k+1+1 = S (S k)).
          -- rewrite !S_INR. lra.
          -- by rewrite H.
    - rewrite -!Rmult_minus_distr_r.
      apply Rcomplements.Rdiv_le_0_compat; try lra.
      apply Rmult_le_pos; try lra.
      assert (INR k <= INR max_hash_size); try lra.
      by apply le_INR.
  Qed.

  Lemma hashfun_amortized_token_ineq f m γ:
    hashfun_amortized f m γ -∗ own γ (◯ 1%nat) -∗ ⌜(size m < max_hash_size)%nat⌝.
  Proof.
    iIntros "H1 H2".
    destruct (Nat.lt_ge_cases (size m) max_hash_size); first done.
    iDestruct "H1" as "(%&%&_&->&_&_&H1&H3)".
    iCombine "H2 H3" as "H2".
    iCombine "H1 H2" gives "H'".
    rewrite auth_both_validI.
    iDestruct "H'" as "[[% %H']_]". simpl in *.
    rewrite nat_op in H'. lia.
  Qed.

  Lemma wp_insert_new_amortized E f m γ1 γ2  (n : nat) :
    m !! n = None →
    (size m < max_hash_size)%nat ->
    {{{ coll_free_hashfun_amortized f m γ1 γ2 ∗ ↯ amortized_error ∗ own γ1 (◯ 1%nat)}}}
      f #n @ E
      {{{ (v : nat), RET #v; coll_free_hashfun_amortized f (<[ n := v ]>m) γ1 γ2 ∗ hash_view_frag n v γ2}}}.
  Proof.
    iIntros (Hlookup Hineq Φ) "([Hhash Hview] & Herr & Htoken) HΦ".
    iDestruct (hashfun_amortized_token_ineq with "[$Hhash][$]") as "%".
    iDestruct "Hhash" as (k ε) "(H&->&%H0&Herr'& Hauth &Hfrag)".
    set (ε' := (((max_hash_size-1) * size (<[n:=0%nat]> m) / 2 -
                   sum_n_m (λ x, INR x) 0%nat (size (<[n:=0%nat]> m) - 1)) / (val_size + 1))).
    assert (0 <= ε') as Hε'.
    { apply amortized_inequality.
      rewrite map_size_insert.
      case_match => /=; lia. }
    set (ε'' := mknonnegreal _ Hε').

    iAssert (↯ (nnreal_div (nnreal_nat (size m)) (nnreal_nat (val_size + 1))) ∗ ↯ ε'')%I
      with "[Herr Herr']" as "[Hε Herr]".
    - iApply ec_split; [apply cond_nonneg|apply cond_nonneg|].
      iCombine "Herr Herr'" as "H".
      iApply (ec_eq with "[$]").
      rewrite /ε'' /ε'.
      simpl. rewrite H0. rewrite map_size_insert_None //.
      remember (size m) as k.
      remember (val_size + 1) as v.
      remember (max_hash_size) as h.
      assert (∀ x y, x/y = x*/y) as Hdiv.
      { intros. lra. }
      destruct k.
      + simpl. rewrite sum_n_n. rewrite Rmult_0_l Rmult_0_r.
        replace (INR 0%nat) with 0; last done.
        rewrite !Rminus_0_r.
        replace (0/_/_) with 0; last lra.
        rewrite !Rplus_0_l.
        rewrite Rmult_1_r.
        rewrite !Hdiv.
        rewrite Rinv_mult.
        lra.
      + assert (forall k, S k - 1 = k)%nat as H' by lia.
        rewrite !H'.
        clear H'.
        rewrite sum_n_Sm; last lia.
        replace (plus _ (INR (S k))) with ((sum_n_m (λ x : nat, INR x) 0 k) + (S k)) by done.
        rewrite !Hdiv.
        rewrite !Rmult_minus_distr_r.
        rewrite (Rmult_plus_distr_r (sum_n_m _ _ _)).
        rewrite -!Rplus_assoc.
        rewrite Ropp_plus_distr.
        rewrite -!Rplus_assoc.
        assert ((h-1) * S k * / 2 * / v+ (h-1) * / (2 * v) = S k * / (val_size + 1)%nat + (h-1) * S (S k) * / 2 * / v  + - (S k * / v)); try lra.
        replace (INR((_+_)%nat)) with v; last first.
        { rewrite Heqv. rewrite -S_INR. f_equal. lia. }
        assert ( (h-1) * S k * / 2 * / v + (h-1) * / (2 * v) = (h-1) * S (S k) * / 2 * / v); try lra.
        replace (_*_*_*_) with ((h-1) * (S k) * /(2*v)); last first.
        { rewrite Rinv_mult. lra. }
        replace (_*_*_*_) with ((h-1) * (S(S k)) * /(2*v)); last first.
        { rewrite Rinv_mult. lra. }
        rewrite -Rdiv_plus_distr.
        rewrite Hdiv.
        f_equal.
        rewrite -{2}(Rmult_1_r (h-1)).
        rewrite -Rmult_plus_distr_l.
        f_equal.
    - wp_apply (wp_insert_no_coll with "[H Hε Hview]"); [done|..].
      + rewrite map_to_list_length. iFrame. 
      + iIntros (v) "[[??] ?]".
        iApply "HΦ".
        iCombine "Hfrag Htoken" as "Hfrag".
        iFrame.
        rewrite !map_size_insert Hlookup.
        iPureIntro. split; first lia.
        rewrite /ε''. simpl. rewrite /ε'. do 3 f_equal.
        all: repeat rewrite map_size_insert Hlookup; try (simpl; lia).
        rewrite S_INR plus_INR; simpl; lra.
  Qed.

  Lemma wp_insert_amortized E f m γ1 γ2 (n : nat) :
    {{{ coll_free_hashfun_amortized f m γ1 γ2 ∗ ↯ amortized_error ∗ own γ1 (◯ 1%nat)}}}
      f #n @ E
      {{{ (v : nat), RET #v; ∃ m', coll_free_hashfun_amortized f m' γ1 γ2 ∗ ⌜m'!!n = Some v⌝ ∗ ⌜(size m' <= S $ size(m))%nat⌝ ∗ ⌜m⊆m'⌝ ∗ hash_view_frag n v γ2 }}}.
  Proof.
    iIntros (Φ) "([Hh Hview]& Herr & Hfrag) HΦ".
    iDestruct (hashfun_amortized_token_ineq with "[$Hh][$]") as "%".
    destruct (m!!n) eqn:Heq.
    - wp_apply (wp_coll_free_hashfun_prev_amortized with "[$Hh $Hview]") as "[??]"; first done.
      iIntros. iApply "HΦ".
      iExists _; iFrame.
      repeat iSplit; try done. iPureIntro; lia.
    - wp_apply (wp_insert_new_amortized with "[$Hh $Herr $Hfrag $Hview]"); try done.
      iIntros (?) "[??]"; iApply "HΦ".
      iExists _; iFrame. iPureIntro. repeat split.
      + rewrite lookup_insert_Some. naive_solver.
      + rewrite map_size_insert. case_match; try (simpl; lia).
      + by apply insert_subseteq.
  Qed.

  
  
End amortized_hash.

  

From clutch.ub_logic Require Export ub_clutch lib.map.
From stdpp Require Export fin_maps.
Import Hierarchy.
Set Default Proof Using "Type*".

Section simple_bit_hash.

  Context `{!ub_clutchGS Σ}.

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

  Definition hashfun f m : iProp Σ :=
    ∃ (hm : loc), ⌜ f = compute_hash_specialized #hm ⌝ ∗
                  map_list hm ((λ b, LitV (LitInt (Z.of_nat b))) <$> m) ∗
                  ⌜map_Forall (λ ind i, (0<= i <=val_size)%nat) m⌝ 
  .

  Definition coll_free_hashfun f m: iProp Σ :=
    hashfun f m ∗ ⌜coll_free m⌝.

  Lemma coll_free_hashfun_implies_hashfun f m:
    coll_free_hashfun f m -∗ hashfun f m.
  Proof.
    by iIntros "[??]".
  Qed.

  #[global] Instance timeless_hashfun f m :
    Timeless (hashfun f m).
  Proof. apply _. Qed.

  #[global] Instance timeless_hashfun_amortized f m:
    Timeless (coll_free_hashfun f m).
  Proof. apply _. Qed.

  Lemma coll_free_hashfun_implies_coll_free f m:
    coll_free_hashfun f m -∗ ⌜coll_free m⌝.
  Proof.
    by iIntros "[??]".
  Qed.

  Lemma hashfun_implies_bounded_range f m idx x:
    hashfun f m -∗ ⌜m!!idx = Some x⌝ -∗ ⌜(0<=x<=val_size)%nat⌝.
  Proof.
    iIntros "(%&%&H&%K) %".
    iPureIntro.
    by eapply map_Forall_lookup_1 in K.
  Qed.

  Lemma coll_free_hashfun_implies_bounded_range f m idx x:
    coll_free_hashfun f m -∗ ⌜m!!idx = Some x⌝ -∗ ⌜(0<=x<=val_size)%nat⌝.
  Proof.
    iIntros "(H&%) %".
    by iApply (hashfun_implies_bounded_range with "[$]").
  Qed.

  Lemma wp_init_hash E :
    {{{ True }}}
      init_hash #() @ E
    {{{ f, RET f; |={E}=> coll_free_hashfun f ∅ }}}.
  Proof.
    rewrite /init_hash.
    iIntros (Φ) "_ HΦ".
    wp_pures. rewrite /init_hash_state.
    wp_apply (wp_init_map with "[//]").
    iIntros (?) "Hm". wp_pures.
    rewrite /compute_hash. wp_pures.
    iApply "HΦ". repeat iModIntro. rewrite /coll_free_hashfun. iSplit.
    - iExists _. rewrite fmap_empty. iFrame. eauto.
    - iPureIntro. rewrite /coll_free. intros ???H?. destruct H.
      by apply lookup_empty_Some in H.
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

  Lemma wp_coll_free_hashfun_prev E f m (n : nat) (b : nat) :
    m !! n = Some b →
    {{{ coll_free_hashfun f m }}}
      f #n @ E
    {{{ RET #b; coll_free_hashfun f m }}}.
  Proof.
    iIntros (Hlookup Φ) "(Hhash & %Hcoll_free) HΦ".
    iDestruct "Hhash" as (hm ->) "[H Hbound]".
    rewrite /compute_hash_specialized.
    wp_pures.
    wp_apply (wp_get with "[$]").
    iIntros (vret) "(Hhash&->)".
    rewrite lookup_fmap Hlookup /=. wp_pures. iModIntro. iApply "HΦ".
    iSplitL; last done.
    iExists _. eauto.
  Qed.


  Lemma wp_insert_no_coll E f m (n : nat) :
    m !! n = None →
    {{{ coll_free_hashfun f m ∗ € (nnreal_div (nnreal_nat (length (map_to_list m))) (nnreal_nat(val_size+1)))
    }}}
      f #n @ E
    {{{ (v : nat), RET #v; coll_free_hashfun f (<[ n := v ]>m) }}}.
  Proof.
    iIntros (Hlookup Φ) "([Hhash %Hcoll_free] & Herr) HΦ".
    iDestruct "Hhash" as (hm ->) "[H %Hbound]".
    rewrite /compute_hash_specialized.
    wp_pures.
    wp_apply (wp_get with "[$]").
    iIntros (vret) "(Hhash&->)".
    rewrite lookup_fmap Hlookup /=. wp_pures.
    wp_bind (rand _)%E.
    wp_apply (wp_rand_err_list_nat _ val_size (map (λ p, snd p) (map_to_list m))); auto.
    rewrite map_length. iFrame.
    iIntros "%x %HForall".
    wp_pures.
    wp_apply (wp_set with "Hhash").
    iIntros "Hlist".
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iSplit.
    - rewrite /hashfun.
      iExists _.
      iSplit; first auto.
      iSplitL.
      + rewrite fmap_insert //.
      + iPureIntro.
        apply map_Forall_insert_2; last done.
        split.
        * lia.
        * pose proof (fin_to_nat_lt x).
          lia. 
    - iPureIntro.
      apply coll_free_insert; auto.
      apply (Forall_map (λ p : nat * nat, p.2)) in HForall; auto.
  Qed.

  
End simple_bit_hash.



Section amortized_hash.
  Context `{!ub_clutchGS Σ}.
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
  
  Definition hashfun_amortized f m : iProp Σ :=
    ∃ (k : nat) (ε : nonnegreal),
      hashfun val_size f m ∗
      ⌜k = size m⌝ ∗
      ⌜ (ε.(nonneg) = (((max_hash_size-1) * k)/2 - sum_n_m (λ x, INR x) 0%nat (k-1)) / (val_size + 1))%R⌝ ∗
      € ε 
  .

  Definition coll_free_hashfun_amortized f m: iProp Σ :=
    hashfun_amortized f m ∗ ⌜coll_free m⌝.

  #[global] Instance timeless_coll_free_hashfun_amortized f m :
    Timeless (hashfun_amortized f m).
  Proof. apply _. Qed.

  Lemma coll_free_hashfun_amortized_implies_coll_free f m:
    coll_free_hashfun_amortized f m -∗ ⌜coll_free m⌝.
  Proof.
    by iIntros "[??]".
  Qed.

  Lemma hashfun_amortized_implies_bounded_range f m idx x:
    hashfun_amortized f m -∗ ⌜m!!idx = Some x⌝ -∗ ⌜(0<=x<=val_size)%nat⌝.
  Proof.
    iIntros "H %".
    iApply (hashfun_implies_bounded_range with "[H]"); [by iDestruct "H" as "(%&%&H&H')"|done].
  Qed.

  Lemma coll_free_hashfun_amortized_implies_bounded_range f m idx x:
    coll_free_hashfun_amortized f m -∗ ⌜m!!idx = Some x⌝ -∗ ⌜(0<=x<=val_size)%nat⌝.
  Proof.
    iIntros "(H&%) %".
    by iApply (hashfun_amortized_implies_bounded_range with "[$]").
  Qed.

  Lemma wp_init_hash_amortized E :
    {{{ True }}}
      init_hash val_size #() @ E
      {{{ f, RET f; |={E}=> coll_free_hashfun_amortized f ∅ }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_apply wp_init_hash; first done.
    iIntros (f) "H".
    iApply "HΦ".
    iMod ec_zero.
    iMod "H".
    iModIntro.
    iSplit; last by iApply coll_free_hashfun_implies_coll_free.
    iDestruct "H" as "[??]".
    iFrame.
    iExists 0%nat, nnreal_zero.
    repeat (iSplit; [done|]). iFrame.
    iPureIntro.
    simpl.
    replace (sum_n_m _ _ _) with 0; first lra.
    rewrite sum_n_n. by simpl. 
  Qed.

  
  Lemma hashfun_amortized_hashfun f m: ⊢ hashfun_amortized f m -∗ hashfun val_size f m.
  Proof.
    by iIntros "(%&%&?&?)". 
  Qed.
  
  Lemma wp_hashfun_prev_amortized E f m (n : nat) (b : nat) :
    m !! n = Some b →
    {{{ hashfun_amortized f m }}}
      f #n @ E
      {{{ RET #b; hashfun_amortized f m }}}.
  Proof.
    iIntros (Hlookup Φ) "(%&%&Hhash&->&%&Herr) HΦ".
    wp_apply (wp_hashfun_prev with "[$Hhash]"); [done|].
    iIntros "H". iApply "HΦ".
    iExists _, _. iFrame. naive_solver.
  Qed.

  Lemma wp_coll_free_hashfun_prev_amortized E f m (n : nat) (b : nat) :
    m !! n = Some b →
    {{{ coll_free_hashfun_amortized f m }}}
      f #n @ E
      {{{ RET #b; coll_free_hashfun_amortized f m }}}.
  Proof.
    iIntros (Hlookup Φ) "[H %Hcoll_free] HΦ".
    wp_apply (wp_hashfun_prev_amortized with "[$]"); [done|].
    iIntros "H". iApply "HΦ".
    by iSplitL. 
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
  
  Lemma wp_insert_new_amortized E f m (n : nat) :
    m !! n = None →
    (size m < max_hash_size)%nat ->
    {{{ coll_free_hashfun_amortized f m ∗ € amortized_error }}}
      f #n @ E
      {{{ (v : nat), RET #v; coll_free_hashfun_amortized f (<[ n := v ]>m) }}}.
  Proof.
    iIntros (Hlookup Hsize Φ) "([Hhash %Hcoll_free] & Herr) HΦ".
    iDestruct "Hhash" as (k ε) "(H&->&%H0&Herr')".
    iAssert (€ (nnreal_div (nnreal_nat (size m)) (nnreal_nat (val_size + 1))) ∗
             € (mknonnegreal (((max_hash_size-1) * size (<[n:=0%nat]> m) / 2 - sum_n_m (λ x, INR x) 0%nat (size (<[n:=0%nat]> m) - 1)) / (val_size + 1)) _ )
            )%I with "[Herr Herr']" as "[Hε Herr]".
    - iApply ec_split. 
      iCombine "Herr Herr'" as "H".
      iApply (ec_spend_irrel with "[$]").
      simpl. rewrite H0. rewrite map_size_insert_None; [|done].
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
    - wp_apply (wp_insert_no_coll with "[H Hε]"); [done|..].
      + rewrite map_to_list_length. iFrame. done.
      + iIntros (v) "[H %]".
        iApply "HΦ".
        iSplitL; last done.
        iExists _, _. iFrame.
        repeat (iSplitR); try done.
        iPureIntro. simpl. do 3 f_equal.
        all: by repeat rewrite map_size_insert.
        Unshelve.
        apply amortized_inequality.
        rewrite map_size_insert.
        case_match => /=; lia.
  Qed.

  Lemma wp_insert_amortized E f m (n : nat) :
    (size m < max_hash_size)%nat ->
    {{{ coll_free_hashfun_amortized f m ∗ € amortized_error }}}
      f #n @ E
      {{{ (v : nat), RET #v; ∃ m', coll_free_hashfun_amortized f m' ∗ ⌜m'!!n = Some v⌝ ∗ ⌜(size m' <= S $ size(m))%nat⌝ ∗ ⌜m⊆m'⌝ }}}.
  Proof.
    iIntros (Hsize Φ) "[[Hh %Hc]Herr] HΦ".
    destruct (m!!n) eqn:Heq.
    - wp_apply (wp_hashfun_prev_amortized with "[$]"); first done.
      iIntros. iApply "HΦ".
      iExists _; iFrame.
      repeat iSplit; try done. iPureIntro; lia.
    - wp_apply (wp_insert_new_amortized with "[$Hh $Herr]"); try done.
      iIntros (?) "[??]"; iApply "HΦ".
      iExists _; iFrame. iPureIntro. repeat split.
      + rewrite lookup_insert_Some. naive_solver.
      + rewrite map_size_insert. case_match; try (simpl; lia).
      + by apply insert_subseteq.
  Qed.
  
End amortized_hash.

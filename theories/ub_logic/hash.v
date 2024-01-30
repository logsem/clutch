From clutch.ub_logic Require Export ub_clutch lib.map.
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

  Definition hashfun f m : iProp Σ :=
    ∃ (hm : loc), ⌜ f = compute_hash_specialized #hm ⌝ ∗ map_list hm ((λ b, LitV (LitInt b)) <$> m).

  #[global] Instance timeless_hashfun f m :
    Timeless (hashfun f m).
  Proof. apply _. Qed.

  Lemma wp_init_hash E :
    {{{ True }}}
      init_hash #() @ E
    {{{ f, RET f; hashfun f ∅ }}}.
  Proof.
    rewrite /init_hash.
    iIntros (Φ) "_ HΦ".
    wp_pures. rewrite /init_hash_state.
    wp_apply (wp_init_map with "[//]").
    iIntros (?) "Hm". wp_pures.
    rewrite /compute_hash. wp_pures.
    iApply "HΦ". iExists _. rewrite fmap_empty. iFrame. eauto.
  Qed.

  Definition coll_free (m : gmap nat Z) :=
    forall k1 k2,
      is_Some (m !! k1) ->
      is_Some (m !! k2) ->
      m !!! k1 = m !!! k2 ->
      k1 = k2.

  Lemma coll_free_insert (m : gmap nat Z) (n : nat) (z : Z) :
    m !! n = None ->
    coll_free m ->
    Forall (λ x, z ≠ snd x) (gmap_to_list m) ->
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
      eapply (Forall_iff (uncurry ((λ (k : nat) (v : Z), z ≠ v)))) in HForall; last first.
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
        eapply (Forall_iff (uncurry ((λ (k : nat) (v : Z), z ≠ v)))) in HForall; last first.
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


  Lemma wp_hashfun_prev E f m (n : nat) (b : Z) :
    m !! n = Some b →
    {{{ hashfun f m }}}
      f #n @ E
    {{{ RET #b; hashfun f m }}}.
  Proof.
    iIntros (Hlookup Φ) "Hhash HΦ".
    iDestruct "Hhash" as (hm ->) "H".
    rewrite /compute_hash_specialized.
    wp_pures.
    wp_apply (wp_get with "[$]").
    iIntros (vret) "(Hhash&->)".
    rewrite lookup_fmap Hlookup /=. wp_pures. iModIntro. iApply "HΦ".
    iExists _. eauto.
  Qed.


  Lemma wp_insert_no_coll E f m (n : nat) (z : Z) :
    m !! n = None →
    {{{ hashfun f m ∗ € (nnreal_div (nnreal_nat (length (gmap_to_list m))) (nnreal_nat(val_size+1))) ∗
          ⌜coll_free m⌝ }}}
      f #n @ E
    {{{ (v : Z), RET #v; hashfun f (<[ n := v ]>m) ∗ ⌜coll_free (<[ n := v ]>m)⌝ }}}.
  Proof.
    iIntros (Hlookup Φ) "(Hhash & Herr & %Hcoll) HΦ".
    iDestruct "Hhash" as (hm ->) "H".
    rewrite /compute_hash_specialized.
    wp_pures.
    wp_apply (wp_get with "[$]").
    iIntros (vret) "(Hhash&->)".
    rewrite lookup_fmap Hlookup /=. wp_pures.
    wp_bind (rand _)%E.
    wp_apply (wp_rand_err_list_int _ val_size (map (λ p, snd p) (gmap_to_list m))); auto.
    rewrite map_length.
    iFrame.
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
      rewrite fmap_insert //.
    - iPureIntro.
      apply coll_free_insert; auto.
      apply (Forall_map (λ p : nat * Z, p.2)) in HForall; auto.
  Qed.

  
End simple_bit_hash.



Section amortized_hash.
  Context `{!ub_clutchGS Σ}.
  Variable val_size:nat.
  Variable max_hash_size : nat.
  Variable Hineq : max_hash_size <= (val_size+1).
  Program Definition amortized_error : nonnegreal :=
    mknonnegreal ((max_hash_size + 1)/(2*(val_size + 1)))%R _.
  Next Obligation.
    pose proof (pos_INR val_size) as H.
    pose proof (pos_INR max_hash_size) as H'.
    apply Rcomplements.Rdiv_le_0_compat; lra.
  Qed.
  
  Definition hashfun_amortized f m : iProp Σ :=
    ∃ (hm : loc) (k : nat) (ε : nonnegreal),
      ⌜ f = compute_hash_specialized val_size #hm ⌝ ∗
      ⌜k = size m⌝ ∗
      ⌜ (ε.(nonneg) = (((max_hash_size + 1) * k)/2 - sum_n_m (λ x, INR x) 0%nat (k-1)) / (val_size + 1))%R⌝ ∗
      € ε ∗
      map_list hm ((λ b, LitV (LitInt b)) <$> m) 
  .

  #[global] Instance timeless_hashfun_amortized f m :
    Timeless (hashfun_amortized f m).
  Proof. apply _. Qed.

  Lemma wp_init_hash_amortized E :
    {{{ True }}}
      init_hash val_size #() @ E
      {{{ f, RET f; hashfun_amortized f ∅ }}}.
  Proof.
    rewrite /init_hash.
    iIntros (Φ) "_ HΦ".
    wp_pures. rewrite /init_hash_state.
    wp_apply (wp_init_map with "[//]").
    iIntros (?) "Hm". wp_pures.
    rewrite /compute_hash. wp_pures.
    iApply "HΦ". iExists _. rewrite fmap_empty. iFrame.
    iMod ec_zero.
    iModIntro. iExists 0%nat, nnreal_zero.
    repeat (iSplit; [done|]). iFrame.
    iPureIntro.
    simpl.
    replace (sum_n_m _ _ _) with 0; first lra.
    rewrite sum_n_n. by simpl. 
  Qed.

  Lemma wp_hashfun_prev_amortized E f m (n : nat) (b : Z) :
    m !! n = Some b →
    {{{ hashfun_amortized f m }}}
      f #n @ E
      {{{ RET #b; hashfun_amortized f m }}}.
  Proof.
    iIntros (Hlookup Φ) "Hhash HΦ".
    iDestruct "Hhash" as (hm k ε -> ->) "[% [Hε H]]".
    wp_apply (wp_hashfun_prev with "[H]"); first done.
    - iExists _. by iFrame.
    - iIntros "(%&%&H)". iApply "HΦ".
      iExists _,_,_. by iFrame.
  Qed.

  Lemma hashfun_amortized_hashfun f m: ⊢ hashfun_amortized f m -∗ hashfun val_size f m.
  Proof.
    iIntros "(%&%&%&->&->&%&He&H)".
    iExists _; by iFrame.
  Qed.

  Lemma amortized_inequality (k : nat):
    (k <= max_hash_size)%nat ->
    0 <= ((max_hash_size + 1) * k / 2 - sum_n_m (λ x : nat, INR x) 0 (k - 1)) / (val_size + 1).
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
  

  Lemma wp_insert_no_coll_amortized E f m (n : nat) (z : Z) :
    m !! n = None →
    (size m < max_hash_size)%nat ->
    {{{ hashfun_amortized f m ∗ € amortized_error ∗
        ⌜coll_free m⌝ }}}
      f #n @ E
      {{{ (v : Z), RET #v; hashfun_amortized f (<[ n := v ]>m) ∗ ⌜coll_free (<[ n := v ]>m)⌝ }}}.
  Proof.
    iIntros (Hlookup Hsize Φ) "(Hhash & Herr & %Hcoll) HΦ".
    iDestruct "Hhash" as (hm k ε -> ->) "[% [Hε H]]".
    iAssert (€ (nnreal_div (nnreal_nat (size m)) (nnreal_nat (val_size + 1))) ∗
             € (mknonnegreal (((max_hash_size + 1) * size (<[n:=0%Z]> m) / 2 - sum_n_m (λ x, INR x) 0%nat (size (<[n:=0%Z]> m) - 1)) / (val_size + 1)) _ )
            )%I with "[Hε Herr]" as "[Hε Herr]".
    - iApply ec_split.
      iCombine "Hε Herr" as "H".
      iApply (ec_spend_irrel with "[$]").
      simpl. rewrite H. rewrite map_size_insert_None; [|done].
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
        assert ((h + 1) * S k * / 2 * / v+ (h + 1) * / (2 * v) = S k * / (val_size + 1)%nat + (h + 1) * S (S k) * / 2 * / v  + - (S k * / v)); try lra.
        replace (INR((_+_)%nat)) with v; last first.
        { rewrite Heqv. rewrite -S_INR. f_equal. lia. }
        assert ( (h + 1) * S k * / 2 * / v + (h + 1) * / (2 * v) = (h + 1) * S (S k) * / 2 * / v); try lra.
        replace (_*_*_*_) with ((h+1) * (S k) * /(2*v)); last first.
        { rewrite Rinv_mult. lra. }
        replace (_*_*_*_) with ((h+1) * (S(S k)) * /(2*v)); last first.
        { rewrite Rinv_mult. lra. }
        rewrite -Rdiv_plus_distr.
        rewrite Hdiv.
        f_equal.
        rewrite -{2}(Rmult_1_r (h+1)).
        rewrite -Rmult_plus_distr_l.
        f_equal.
    - wp_apply (wp_insert_no_coll with "[H Hε]"); [done|done|..].
      + iFrame. iSplitL; try done.
        iExists _. by iFrame.
      + iIntros (v) "[H %]".
        iApply "HΦ".
        iSplitL; last done.
        iExists _, _, _. iFrame.
        repeat (iSplitR); try done.
        * iPureIntro. simpl. do 3 f_equal.
          all: by repeat rewrite map_size_insert.
        * iDestruct "H" as "[% [% H]]".
          inversion H1; subst.
          iFrame.
          Unshelve.
          apply amortized_inequality.
          rewrite map_size_insert.
          case_match => /=; lia.
  Qed.

End amortized_hash.

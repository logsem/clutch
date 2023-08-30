From clutch.ub_logic Require Export ub_clutch lib.map.
Set Default Proof Using "Type*".

Module simple_bit_hash.

  Context `{!clutchGS Σ}.

  (* A simple bit hash map. *)

  Variable val_size : nat.

  (* A hash function's internal state is a map from previously queried keys to their hash value *)
  Definition init_hash_state : val := init_map.

  (* To hash a value v, we check whether it is in the map (i.e. it has been previously hashed).
     If it has we return the saved hash value, otherwise we flip a bit and save it in the map *)
  Definition compute_hash_specialized hm : val :=
    λ: "v",
      match: get hm "v" with
      | SOME "b" => "b"
      | NONE =>
          let: "b" := (rand #val_size from #()) in
          set hm "v" "b";;
          "b"
      end.
  Definition compute_hash : val :=
    λ: "hm" "v",
      match: get "hm" "v" with
      | SOME "b" => "b"
      | NONE =>
          let: "b" := (rand #val_size from #()) in
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
    wp_bind (rand _ from #())%E.
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

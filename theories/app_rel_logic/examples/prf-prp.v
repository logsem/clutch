From clutch.app_rel_logic Require Export app_clutch map list.
Set Default Proof Using "Type*".

Module prf_prp.

  (* This is the same as the simple hash *)

  Context `{!app_clutchGS Σ}.

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

  (*
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
*)

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


  (* A prp's internal state is a tuple of:
       - a map from previously queried keys to their value, and
       - a list of fresh (unsampled) values
       - an integer corresponding to the size of the list above minus one

     The last element is redundant, but it removes the need to sample from (length fv) - 1
     in the program.

     We use list_init to initialize the list of fresh values to [0,1,...,max_val]
  *)


  Definition init_prp_state : val :=
   λ: "_",
      let: "val_map" := init_map #() in
      let: "fr_val" := list_seq #0 #(S val_size) in
      let: "fr_size" := #(val_size) in
      ("val_map", ref "fr_val", ref "fr_size").

  (* To hash a value v, we check whether it is in the map (i.e. it has been previously hashed).
     If it has we return the saved hash value, otherwise we draw a hash value and save it in the map *)
  Definition query_prp_specialized hm fv fs : val :=
    λ: "v",
      match: get hm "v" with
      | SOME "n" => "n"
      | NONE =>
          let: "n" := (rand !fs from #()) in
          (match: list_remove_nth fv "n" with
          | SOME "p" =>
              set hm "v" (Fst "p");;
              fv <- (Snd "p") ;;
              fs <- !fs - #1 ;;
              (Fst "p")
          (* This should never be reached *)
          | NONE => "b"
          end)
      end.

  Definition query_prp : val :=
    λ: "hm" "fv" "fs" "v",
      match: get "hm" "v" with
      | SOME "n" => "n"
      | NONE =>
          let: "n" := (rand !"fs" from #()) in
          (match: list_remove_nth "fv" "n" with
          | SOME "p" =>
              set "hm" "v" (Fst "p");;
              "fv" <- (Snd "p") ;;
              "fs" <- !"fs" - #1 ;;
              (Fst "p")
          (* This should never be reached *)
          | NONE => "b"
          end)
      end.

  (* init_hash returns a hash as a function, basically wrapping the internal state
     in the returned function *)
  Definition init_prp : val :=
    λ: "_",
      let: "p" := init_prp_state #() in
      query_prp (Fst (Fst "p")) (Snd (Fst "p")) (Snd "p").


  Definition is_prp f (m : gmap nat Z) (r : list Z) : iProp Σ :=
    ∃ (hm : loc) (fv : loc) (fs : loc),
      ⌜ f = query_prp_specialized #hm #fv #fs⌝
      ∗ map_list hm ((λ b, LitV (LitInt b)) <$> m)
      ∗ (∃ lf , fv ↦ lf ∗ ⌜ is_list r lf ⌝ )
      ∗ (∃ vl : nat , fs ↦ #vl ∗ ⌜ length r = S (vl) ⌝)
      ∗ ⌜((snd <$> (map_to_list m)) ++ r) ≡ₚ (Z.of_nat) <$> (seq 0 (S val_size))⌝.

  #[global] Instance timeless_is_prp f m r:
    Timeless (is_prp f m r).
  Proof. apply _. Qed.


  Definition is_sprp f (m : gmap nat Z) (r : list Z) : iProp Σ :=
    ∃ (hm : loc) (fv : loc) (fs : loc),
      ⌜ f = query_prp_specialized #hm #fv #fs⌝
      ∗ map_slist hm ((λ b, LitV (LitInt b)) <$> m)
      ∗ (∃ lf , fv ↦ₛ lf ∗ ⌜ is_list r lf ⌝)
      ∗ (∃ vl : nat , fs ↦ₛ #vl ∗ ⌜ length r = S (vl) ⌝)
      ∗ ⌜((snd <$> (map_to_list m)) ++ r) ≡ₚ (Z.of_nat) <$> (seq 0 (S val_size))⌝.

  #[global] Instance timeless_is_sprp f m r:
    Timeless (is_sprp f m r).
  Proof. apply _. Qed.

  Local Lemma inject_seq m s :
    inject (seq m s) = inject ((Z.of_nat) <$> (seq m s)).
  Proof.
    revert m. induction s; [done |].
    intro m.
    rewrite /inject/=.
    do 2 f_equal.
    apply IHs.
  Qed.

  Lemma wp_init_prp E :
    {{{ True }}}
      init_prp #() @ E
    {{{ f, RET f; is_prp f ∅ (Z.of_nat <$> (seq 0 (S val_size))) }}}.
  Proof.
    rewrite /init_prp.
    iIntros (Φ) "_ Hφ".
    wp_pures.
    rewrite /init_prp_state.
    wp_pures.
    wp_apply (wp_init_map with "[//]").
    iIntros (?) "Hm". wp_pures.
    wp_bind (list_seq _ _).
    iApply (wp_list_seq E 0 (S val_size)); auto.
    iIntros "!>" (v Hv).
    wp_pures.
    wp_apply (wp_alloc); auto.
    iIntros (ls) "Hls".
    wp_apply (wp_alloc); auto.
    iIntros (lm) "Hlm".
    wp_pures.
    rewrite /query_prp.
    wp_pures.
    iApply "Hφ".
    iModIntro.
    rewrite /is_prp.
    iExists l, lm, ls.
    iSplit.
    {
      iPureIntro.
      rewrite /query_prp_specialized //.
    }
    rewrite fmap_empty.
    iFrame.
    iSplitL "Hlm".
    {
      iExists _.
      iFrame.
      iPureIntro.
      apply is_list_inject.
      apply is_list_inject in Hv as ->.
      apply inject_seq.
    }
    iSplit.
    {
      iExists _.
      iFrame.
      iPureIntro.
      rewrite fmap_length seq_length //.
    }
    iPureIntro.
    rewrite map_to_list_empty //.
  Qed.


  Lemma spec_init_prp E K :
    ↑specN ⊆ E →
    refines_right K (init_prp #()) ={E}=∗ ∃ f, refines_right K (of_val f) ∗ is_sprp f ∅ (Z.of_nat <$> (seq 0 (S val_size))).
  Proof.
    rewrite /init_prp.
    iIntros (?) "Hspec".
    rewrite /init_prp_state.
    tp_pures.
    tp_bind (init_map _).
    iEval (rewrite refines_right_bind) in "Hspec".
    iMod (spec_init_map with "[$]") as (l) "(Hspec&Hm)"; auto.
    iEval (rewrite -refines_right_bind /=) in "Hspec".
    rewrite /query_prp.
    tp_pures.
    tp_bind (list_seq _ _).
    iEval (rewrite refines_right_bind) in "Hspec".
    (* TODO: Instantiate this properly *)
    iMod (spec_list_seq with "[Hspec]") as (v) "(Hspec & %Hv)".
    { done. }.
    Unshelve.
    4: { exact 0. }
    4: { exact (S val_size). }
    { done. }
    iEval (rewrite -refines_right_bind /=) in "Hspec".
    tp_pures.
    tp_alloc as ls "Hls".
    tp_alloc as lm "Hlm".
    tp_pures.
    iModIntro.
    iExists _.
    iFrame.
    rewrite /is_sprp.
    iExists l, lm, ls.
    iSplit.
    {
      iPureIntro.
      rewrite /query_prp_specialized //.
    }
    rewrite fmap_empty.
    iFrame.
    iSplitL "Hlm".
    {
      iExists _.
      iFrame.
      iPureIntro.
      apply is_list_inject.
      apply is_list_inject in Hv as ->.
      apply inject_seq.
    }
    iSplit.
    {
      iExists _.
      iFrame.
      iPureIntro.
      rewrite fmap_length seq_length //.
    }
    iPureIntro.
    rewrite map_to_list_empty //.
  Qed.


  Lemma wp_prp_prev E f m r (n : nat) (b : Z) :
    m !! n = Some b →
    {{{ is_prp f m r }}}
      f #n @ E
    {{{ RET #b; is_prp f m r }}}.
  Proof.
    iIntros (Hlookup Φ) "Hprp HΦ".
    iDestruct "Hprp" as (lm lr ls) "(-> & Hlm & Hlr & Hls)".
    rewrite /query_prp_specialized.
    wp_pures.
    wp_apply (wp_get with "[$]").
    iIntros (res) "(Hmap&->)".
    rewrite lookup_fmap Hlookup /=. wp_pures. iModIntro. iApply "HΦ".
    iExists lm,lr,ls.
    iSplit.
    {
      rewrite /query_prp_specialized //.
    }
    iFrame.
  Qed.


 Lemma wp_prf_prp_couple_eq_err E K (f : val) (m : gmap nat Z) (sf : val) (sr : list Z) (n : nat) (ε : nonnegreal):
    ↑specN ⊆ E →
    m !! n = None →
    ((S val_size - (length sr)) / S val_size)%R = ε ->
    {{{ refines_right K (sf #n) ∗ hashfun f m ∗ is_sprp sf m sr ∗ € ε }}}
      f #n @ E
    {{{ (z: Z), RET #z;
        refines_right K (of_val #z) ∗ hashfun f (<[ n := z ]>m) ∗
          ∃ l1 l2,
                ⌜ sr = l1 ++ z :: l2 ⌝ ∗
          is_sprp sf (<[n := z]>m) (l1 ++ l2) }}}.
 Proof.
    iIntros (Hspec Hnone Hε Φ) "(HK & Hprf & Hprp & Herr) HΦ".
    iDestruct "Hprf" as (hm ->) "Hm".
    iDestruct "Hprp" as (lsm lsr lsl) "(-> & Hsm & Hlsr & Hlsl & %Hperm)".
    rewrite /compute_hash_specialized.
    rewrite /query_prp_specialized.
    wp_pures.
    tp_pures.

    (* spec get *)
    tp_bind (get _ _).
    iEval (rewrite refines_right_bind) in "HK".
    iMod (spec_get with "[$] [$]") as "(HK&Hsm)"; first done.
    iEval (rewrite -refines_right_bind /=) in "HK".
    rewrite lookup_fmap Hnone /=.
    tp_pures.

    (* impl get *)
    wp_apply (wp_get with "[$]").
    iIntros (res) "(Hm&->)".
    rewrite lookup_fmap Hnone /=.
    wp_pures.

    iDestruct "Hlsl" as (vl) "(Hlsl & %Hvl)".
    tp_load.
    tp_bind (rand _ from _ )%E.
    iEval (rewrite refines_right_bind) in "HK".
    assert (fin (S vl) -> fin (S val_size)) as f; [admit | ].
    assert (forall n : fin (S vl), nth n sr 0 = f n) as Hnth; [admit | ].
    wp_apply (wp_couple_rand_rand_rev_inj val_size vl f (Z.of_nat val_size) (Z.of_nat vl)); first done.
    {
      admit.
    }
    { rewrite -Hvl. apply Hε. }
    iFrame.
    iIntros "!>" (x) "HK".
    iEval (rewrite -refines_right_bind /=) in "HK".

    tp_pures.
    wp_pures.
    pose proof (fin_to_nat_lt x).
    tp_bind (list_remove_nth _ _).
    iEval (rewrite refines_right_bind) in "HK".
    iMod (spec_remove_nth _ _ sr $! _ with "HK") as (v) "(HK & (%e & %v' & %l1 & %l2 & (%Hsr & %Hlen & -> & %Hil)))"; first done.
    iEval (rewrite -refines_right_bind /=) in "HK".

    tp_pures.
    iDestruct "Hlsr" as (lf) "(Hlsr & %Hlf)".
    assert (#(f x) = # e) as ->.
    {
      do 3 f_equal.
      rewrite -Hnth Hsr -Hlen nth_middle //.
    }
    wp_pures.

    tp_bind (set _ _ _).
    iEval (rewrite refines_right_bind) in "HK".
    iMod (spec_set with "[$] [$]") as "(HK&Hsm)"; first done.
    iEval (rewrite -refines_right_bind /=) in "HK".
    tp_pures.
    tp_store.
    tp_pures.
    tp_load.
    tp_pures.
    tp_store.
    tp_pures.

    wp_apply (wp_set with "[$]").
    iIntros "Hm". wp_pures. iApply "HΦ".
    iModIntro. iFrame.
    iSplitL "Hm".
    { iExists _. iSplit; first auto. rewrite fmap_insert //. }
    { iExists _, _. iSplit; first auto.
      rewrite /is_prp.
      iExists _,_,_.
      iSplit; first auto.
      rewrite fmap_insert.
      iFrame.
      iSplitL "Hlsr".
      - iExists _ ; auto.
      - iSplit.
        + (* Argh *) admit.
        + iPureIntro.
          (* Should be true? *)
          admit.
    Admitted.

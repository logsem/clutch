From clutch.app_rel_logic Require Export app_clutch map list.
Set Default Proof Using "Type*".

Section prf_prp.

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
      ("val_map", ref "fr_val").

  (* To hash a value v, we check whether it is in the map (i.e. it has been previously hashed).
     If it has we return the saved hash value, otherwise we draw a hash value and save it in the map *)
  Definition query_prp_specialized hm fv : val :=
    λ: "v",
      match: get hm "v" with
      | SOME "n" => "n"
      | NONE =>
          let: "ln" := list_length !fv in
          let: "n" := (rand ("ln" - #1)) in
          (match: list_remove_nth !fv "n" with
          | SOME "p" =>
              set hm "v" (Fst "p");;
              fv <- (Snd "p") ;;
              (Fst "p")
          (* This should never be reached *)
          | NONE => "b"
          end)
      end.

  Definition query_prp : val :=
    λ: "hm" "fv" "v",
      match: get "hm" "v" with
      | SOME "n" => "n"
      | NONE =>
          let: "ln" := list_length !"fv" in
          let: "n" := (rand ("ln" - #1)) in
          (match: list_remove_nth !"fv" "n" with
          | SOME "p" =>
              set "hm" "v" (Fst "p");;
              "fv" <- (Snd "p") ;;
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
      query_prp (Fst "p") (Snd "p").


  Definition is_prp f (m : gmap nat Z) (r : list Z) : iProp Σ :=
    ∃ (hm : loc) (fv : loc),
      ⌜ f = query_prp_specialized #hm #fv⌝
      ∗ map_list hm ((λ b, LitV (LitInt b)) <$> m)
      ∗ (∃ lf , fv ↦ lf ∗ ⌜ is_list r lf ⌝ )
      ∗ ⌜((snd <$> (map_to_list m)) ++ r) ≡ₚ (Z.of_nat) <$> (seq 0 (S val_size))⌝.

  #[global] Instance timeless_is_prp f m r:
    Timeless (is_prp f m r).
  Proof. apply _. Qed.


  Definition is_sprp f (m : gmap nat Z) (r : list Z) : iProp Σ :=
    ∃ (hm : loc) (fv : loc),
      ⌜ f = query_prp_specialized #hm #fv ⌝
      ∗ map_slist hm ((λ b, LitV (LitInt b)) <$> m)
      ∗ (∃ lf , fv ↦ₛ lf ∗ ⌜ is_list r lf ⌝)
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
    wp_pures.
    rewrite /query_prp.
    wp_pures.
    iApply "Hφ".
    iModIntro.
    rewrite /is_prp.
    iExists l, ls.
    iSplit.
    {
      iPureIntro.
      rewrite /query_prp_specialized //.
    }
    rewrite fmap_empty.
    iFrame.
    iSplitL "Hls".
    {
      iExists _.
      iFrame.
      iPureIntro.
      apply is_list_inject.
      apply is_list_inject in Hv as ->.
      apply inject_seq.
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
    { done. }
    Unshelve.
    4: { exact 0. }
    4: { exact (S val_size). }
    { done. }
    iEval (rewrite -refines_right_bind /=) in "Hspec".
    tp_pures.
    tp_alloc as ls "Hls".
    tp_pures.
    iModIntro.
    iExists _.
    iFrame.
    rewrite /is_sprp.
    iExists l, ls.
    iSplit.
    {
      iPureIntro.
      rewrite /query_prp_specialized //.
    }
    rewrite fmap_empty.
    iFrame.
    iSplitL "Hls".
    {
      iExists _.
      iFrame.
      iPureIntro.
      apply is_list_inject.
      apply is_list_inject in Hv as ->.
      apply inject_seq.
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
    iDestruct "Hprp" as (lm lr) "(-> & Hlm & Hlr)".
    rewrite /query_prp_specialized.
    wp_pures.
    wp_apply (wp_get with "[$]").
    iIntros (res) "(Hmap&->)".
    rewrite lookup_fmap Hlookup /=. wp_pures. iModIntro. iApply "HΦ".
    iExists lm,lr.
    iSplit.
    {
      rewrite /query_prp_specialized //.
    }
    iFrame.
  Qed.

 Lemma seq_to_seqZ (l : nat) :
    Z.of_nat <$> seq 0 l = seqZ 0 l.
 Proof.
   rewrite /seqZ.
   rewrite Nat2Z.id.
   apply list_fmap_ext.
   intros. lia.
 Qed.

 Lemma NoDup_remove_pref [A : Type] (l l' : list A):
   List.NoDup (l ++ l') → List.NoDup (l').
 Proof.
   induction l as [| a l]; simpl; auto.
   intros H.
   apply IHl.
   replace (l ++ l') with ([] ++ (l ++ l')); auto.
   replace (a :: l ++ l') with ([] ++ a :: (l ++ l')) in H; auto.
   eapply NoDup_remove_1; eauto.
 Qed.

 Lemma prp_None_non_full (m : gmap nat Z) (sr : list Z) (n : nat) :
    n <= val_size ->
    m !! n = None ->
    (forall n', val_size < n' -> m !! n' = None) ->
    ((snd <$> (map_to_list m)) ++ sr) ≡ₚ (Z.of_nat) <$> (seq 0 (S val_size)) →
    (exists vl, length sr = (S vl)).
 Admitted.




 Lemma wp_prf_prp_couple_eq_err E K (f : val) (m : gmap nat Z) (sf : val) (sr : list Z) (n : nat) (ε : nonnegreal):
    ↑specN ⊆ E →
    m !! n = None →
    n <= val_size ->
    (∀ n' : nat, val_size < n' → m !! n' = None) ->
    ((S val_size - (length sr)) / S val_size)%R = ε ->
    {{{ refines_right K (sf #n) ∗ hashfun f m ∗ is_sprp sf m sr ∗ € ε }}}
      f #n @ E
    {{{ (z: Z), RET #z;
        refines_right K (of_val #z) ∗ hashfun f (<[ n := z ]>m) ∗
          ∃ l1 l2,
                ⌜ sr = l1 ++ z :: l2 ⌝ ∗
          is_sprp sf (<[n := z]>m) (l1 ++ l2) }}}.
 Proof.
    iIntros (Hspec Hnone Hrange Hdom Hε Φ) "(HK & Hprf & Hprp & Herr) HΦ".
    iDestruct "Hprf" as (hm ->) "Hm".
    iDestruct "Hprp" as (lsm lsr) "(-> & Hsm & Hlsr & %Hperm)".
    rewrite /compute_hash_specialized.
    rewrite /query_prp_specialized.
    wp_pures.
    tp_pures.

    (* Some helper lemmas *)
    assert (Forall (λ z: Z , (Z.of_nat (Z.to_nat z)) = z) sr) as HZsr.
    {
      eapply (Forall_app _ ((map_to_list m).*2) sr).
      rewrite Hperm.
      apply Forall_fmap.
      apply Forall_seq.
      intros j Hj. simpl.
      lia.
    }

    edestruct prp_None_non_full as (vl & Hvl); eauto.


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

    iDestruct "Hlsr" as (lf) "(Hlsr & %Hlf)".

    tp_load.
    tp_bind (list_length _).
    iEval (rewrite refines_right_bind) in "HK".
    iMod (spec_list_length with "[% //] HK") as (len) "(HK&->)"; first done.
    iEval (rewrite -refines_right_bind /=) in "HK".
    rewrite Hvl.
    tp_pure.
    tp_pure.
    tp_pure.
    assert (#(S vl - 1) = #vl) as ->.
    {
     do 3 f_equal; lia.
    }

    tp_bind (rand _)%E.
    iEval (rewrite refines_right_bind) in "HK".
    set f := (λ n : nat, if (n <=? vl) then Z.to_nat (nth n sr 0) else n + val_size).
    wp_apply (wp_couple_rand_rand_rev_inj val_size vl f val_size vl).
    {
      intros x Hx.
      rewrite /f.
      rewrite leb_correct; [ | lia].
      apply Forall_nth; [ | lia].
      eapply (Forall_app _ ((map_to_list m).*2) sr).
      rewrite Hperm.
      apply Forall_fmap.
      apply Forall_seq.
      intros j Hj. simpl.
      rewrite Nat2Z.id.
      lia.
    }
    {
      rewrite /f.
      intros x y Hx Hy Hxy.
      rewrite leb_correct in Hxy; [ | lia].
      rewrite leb_correct in Hxy; [ | lia].
      eapply (NoDup_nth sr 0); try lia.
      + apply (NoDup_remove_pref ((map_to_list m).*2)).
        rewrite Hperm.
        rewrite seq_to_seqZ.
        apply NoDup_ListNoDup.
        apply NoDup_seqZ.
      + pose proof (Forall_nth (λ z : Z, Z.of_nat (Z.to_nat z) = z) 0 sr ) as [Haux ?].
        specialize (Haux HZsr).
        rewrite -Haux; [ |lia].
        rewrite -(Haux y); [ |lia].
        by rewrite Hxy.
    }
    1:done.
    {
      apply Permutation_length in Hperm.
      rewrite app_length in Hperm.
      do 2 rewrite fmap_length in Hperm.
      rewrite seq_length Hvl in Hperm.
      apply le_INR.
      lia.
    }
    { rewrite -Hvl. apply Hε. }
    iFrame.
    iIntros "!>" (x) "HK".
    iEval (rewrite -refines_right_bind /=) in "HK".


    tp_pures.
    wp_pures.
    pose proof (fin_to_nat_lt x).
    tp_load.
    tp_bind (list_remove_nth _ _).
    iEval (rewrite refines_right_bind) in "HK".
    unshelve iMod (spec_remove_nth _ _ sr _ with "[#] HK")
      as (v) "(HK & (%e & %v' & %l1 & %l2 & (%Hsr & %Hlen & -> & %Hil)))"; first done.
    {
      iPureIntro; split; auto.
      lia.
    }
    iEval (rewrite -refines_right_bind /=) in "HK".
    tp_pures.


    assert (#(f x) = # e) as ->.
    {
      do 3 f_equal.
      rewrite /f.
      rewrite Hsr -Hlen nth_middle leb_correct; [ | lia].
      rewrite Hsr in HZsr.
      eapply (Forall_elt _ _ _ HZsr).
    }
    wp_pures.

    tp_bind (set _ _ _).
    iEval (rewrite refines_right_bind) in "HK".
    iMod (spec_set with "[$] [$]") as "(HK&Hsm)"; first done.
    iEval (rewrite -refines_right_bind /=) in "HK".
    tp_pures.
    tp_store.
    tp_pures.

    wp_apply (wp_set with "[$]").
    iIntros "Hm". wp_pures. iApply "HΦ".
    iModIntro. iFrame.
    iSplitL "Hm".
    { iExists _. iSplit; first auto. rewrite fmap_insert //. }
    iExists _, _. iSplit; first auto.
    rewrite /is_sprp.
    iExists _,_.
    iSplit; first auto.
    rewrite fmap_insert.
    iFrame.
    iSplitL "Hlsr".
    - iExists _ ; auto.
    - iPureIntro.
      etrans; [ | apply Hperm ].
      rewrite Hsr.
      rewrite map_to_list_insert; auto.
      replace (((n, e) :: map_to_list m).*2) with (e :: (map_to_list m).*2); [ | auto].
      rewrite Permutation_app_rot.
      rewrite (Permutation_app_rot ((map_to_list m).*2) l1 (e :: l2)).
      apply Permutation_app_head.
      rewrite Permutation_app_comm.
      simpl.
      apply perm_skip.
      by rewrite Permutation_app_comm.
 Qed.


Definition test_prf: val :=
  λ: "n",
    let: "f" := init_hash #() in
  letrec: "aux" "f" "i" :=
    (if: "i" ≤ #0
     then  "f"
     else let: "x" := rand #val_size in
          "f" "x";;
          "aux" "f" ("i" - #1)) in
    "aux" "f" "n".


Definition test_prp: val :=
  λ: "n",
    let: "f" := init_prp #() in
  letrec: "aux" "f" "i" :=
    (if: "i" ≤ #0
     then  "f"
     else let: "x" := rand #val_size in
          "f" "x";;
          "aux" "f" ("i" - #1)) in
    "aux" "f" "n".


 Lemma wp_prf_prp_test_err E K (n : nat) (ε : nonnegreal):
    ↑specN ⊆ E →
    (INR(fold_left (Nat.add) (seq 0 n) 0%nat) / INR (S val_size))%R = ε ->
    {{{ refines_right K (test_prp #n) ∗ € ε }}}
      test_prf #n @ E
    {{{ f, RET f;
        ∃ g m l, refines_right K (of_val g) ∗ hashfun f m∗
          is_sprp g m l }}}.
 Proof.
   iIntros (Hspec Hε Φ) "(HK & Herr) HΦ ".

   rewrite /test_prf.
   wp_pure.
   wp_bind (init_hash _).
   wp_apply (wp_init_hash); first done.
   iIntros (f) "Hf".
   do 2 wp_pure.

   rewrite /test_prp.
   tp_pure.
   tp_bind (init_prp _).
   iEval (rewrite refines_right_bind) in "HK".
   iMod (spec_init_prp with "HK") as (g) "(HK & Hg)"; first done.
   iEval (rewrite -refines_right_bind /=) in "HK".

   do 5 tp_pure.
   do 3 wp_pure.
   iInduction n as [|m] "IH".
   - wp_pures.
     tp_pures.
     iModIntro.
     iApply "HΦ".
     iExists _,_,_. iFrame.

   - wp_pures.
     wp_bind (rand _)%E.

     tp_pures.
     tp_bind (rand _)%E.
     iEval (rewrite refines_right_bind) in "HK".

     iMod (ec_zero).
     wp_apply (wp_couple_rand_rand_leq val_size val_size val_size val_size _ _ _ nnreal_zero); first done.
     { lra. }
     { rewrite Rminus_diag /Rdiv Rmult_0_l /=//. }

     iFrame.
     iIntros "!>" (n2 m2 ->) "HK".
     iEval (rewrite -refines_right_bind /=) in "HK".

     wp_pures.
     wp_pures.
     tp_pures.
     wp_bind (f _).
     tp_bind (g _).
     iEval (rewrite refines_right_bind) in "HK".

     iMod (ec_zero).
     wp_apply (wp_prf_prp_couple_eq_err _ _ _ ∅ _ ((Z.of_nat) <$> (seq 0 (S val_size))) m2 nnreal_zero
                with "[$]"); first done.
     { apply lookup_empty. }
     { pose proof (fin_to_nat_lt m2); lia. }
     { intros; apply lookup_empty. }
     { rewrite fmap_length seq_length.
       rewrite Rminus_diag /Rdiv Rmult_0_l /=//.
     }

     iIntros (z) "(HK & Hf & (%l1 & %l2 & %Hperm & Hg))".
     iEval (rewrite -refines_right_bind /=) in "HK".
     do 3 wp_pure.
     do 3 tp_pure.
     assert (#(S m - 1) = #m) as ->.
     {
       do 3 f_equal. lia.
     }
     iApply "IH".
 Abort.

End prf_prp.

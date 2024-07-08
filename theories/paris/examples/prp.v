From clutch Require Import lib.flip.
From clutch.paris Require Import paris map list.
From clutch.paris Require Export bounded_oracle.
Set Default Proof Using "Type*".


Section PRP.

  Context `{!parisGS Σ}.

  Variable val_size : nat.

  Let keygen PRP_scheme : expr := Fst PRP_scheme.
  Let prp PRP_scheme : expr := Fst (Snd PRP_scheme).

  (* A prp's internal state is a tuple of:
       - a map from previously queried keys to their value, and
       - a list of fresh (unsampled) values
       - an integer corresponding to the size of the list above minus one

     The last element is redundant, but it removes the need to sample from (length fv) - 1
     in the program.

     We use list_init to initialize the list of fresh values to [0,1,...,max_val]
   *)


  Definition random_permutation_state : val :=
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
  Definition random_permutation : val :=
    λ: "_",
      let: "p" := random_permutation_state #() in
      query_prp (Fst "p") (Snd "p").


  Let q_calls := q_calls val_size.

  Definition PRP : val :=
    λ:"b" "adv" "PRP_scheme" "Q",
      let: "key" := keygen "PRP_scheme" #() in
      let: "prp_key_b" :=
        if: "b" then
          prp "PRP_scheme" "key"
        else
          random_permutation "key" in
      let: "oracle" := q_calls "Q" "prp_key_b" in
      let: "b'" := "adv" "oracle" in
      "b'".

  Definition wPRP : val :=
    λ:"b" "PRP_scheme" "Q",
      let: "key" := keygen "PRP_scheme" #() in
      let: "prp_key_b" :=
        if: "b" then
          prp "PRP_scheme" "key"
        else
          random_permutation "key" in
      let: "res" := ref list_nil in
      let: "loop" := rec: "loop" "i" :=
          if: "i" = #0 then #() else
            let: "x" := rand #val_size in
            let: "y" := "prp_key_b" "x" in
            "res" <- list_cons ("x", "y") (!"res") ;;
            "loop" ("i" - #1)
      in
      "loop" "Q" ;;
      ! "res"
  .

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

  Lemma wp_random_permutation E :
    {{{ True }}}
      random_permutation #() @ E
      {{{ f, RET f; is_prp f ∅ (Z.of_nat <$> (seq 0 (S val_size))) }}}.
  Proof.
    rewrite /random_permutation.
    iIntros (Φ) "_ Hφ".
    wp_pures.
    rewrite /random_permutation_state.
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
    iSplit.
    {
      iPureIntro.
      apply is_list_inject.
      apply is_list_inject in Hv as ->.
      apply inject_seq.
    }
    iPureIntro.
    rewrite map_to_list_empty //.
  Qed.


  Lemma spec_random_permutation E K :
    ⤇ fill K (random_permutation #()) -∗ spec_update E (∃ f, ⤇ fill K (of_val f) ∗ is_sprp f ∅ (Z.of_nat <$> (seq 0 (S val_size)))).
  Proof.
    rewrite /random_permutation.
    iIntros "Hspec".
    rewrite /random_permutation_state.
    tp_pures.
    tp_bind (init_map _).
    iMod (spec_init_map with "[$]") as (l) "(Hspec&Hm)"; auto.
    rewrite /query_prp/=.
    tp_pures.
    tp_bind (list_seq _ _).
    iMod (spec_list_seq with "[Hspec]") as (v) "(Hspec & %Hv)".
    Unshelve.
    4: { exact 0. }
    4: { exact (S val_size). }
    { done. }
    simpl; tp_pures.
    tp_alloc as ls "Hls".
    tp_pures.
    iModIntro.
    iExists _.
    iFrame.
    rewrite /is_sprp.
    iSplit.
    {
      iPureIntro.
      rewrite /query_prp_specialized //.
    }
    (* rewrite fmap_empty. *)
    iFrame.
    iSplit.
    {
      iPureIntro.
      apply is_list_inject.
      apply is_list_inject in Hv as ->.
      apply inject_seq.
    }
    iPureIntro.
    rewrite map_to_list_empty //.
  Qed.


  Lemma spec_prp_prev E (f:val) m r (n : nat) (b : Z) K:
    m !! n = Some b →
    ⤇ fill K (f #n) ∗ is_sprp f m r -∗
                                       spec_update E (⤇ fill K (#b) ∗ is_sprp f m r ).
  Proof.
    iIntros (Hlookup) "[HK Hprp]".
    iDestruct "Hprp" as (lm lr) "(-> & Hlm & Hlr)".
    rewrite /query_prp_specialized.
    tp_pures.
    tp_bind (get _ _)%E.
    iMod (spec_get with "[$][$]") as "[HK Hm]".
    rewrite lookup_fmap Hlookup /=.
    tp_pures.
    iModIntro. by iFrame.
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
  Proof.
    intros Hineq Hm Hm' Hp.
    cut (length sr ≠ 0).
    { destruct sr; first done.
      intros. eexists _. done.
    }
    move => /nil_length_inv. intros ->. rewrite app_nil_r in Hp.
    apply Permutation_length in Hp.
    rewrite !fmap_length seq_length in Hp.
    cut (length (map_to_list m) <= val_size); first lia.
    clear Hp. rewrite map_to_list_length.
    replace (val_size) with (size (gset_to_gmap (0)%Z (set_seq 0 (S val_size) ∖ {[n]}))); last first.
    { rewrite -size_dom dom_gset_to_gmap size_difference.
      - rewrite size_set_seq size_singleton. lia.
      - rewrite singleton_subseteq_l elem_of_set_seq. lia.
    }
    apply dom_subseteq_size. rewrite dom_gset_to_gmap. intros x Hx.
    rewrite elem_of_difference. split.
    - rewrite elem_of_set_seq; split; first lia.
      rewrite Nat.add_0_l Nat.lt_nge.
      intro. assert (val_size < x) as H' by lia.
      specialize (Hm' _ H').
      by apply not_elem_of_dom_2 in Hx.
    - apply not_elem_of_singleton_2. intros ->.
      by apply not_elem_of_dom_2 in Hm.
  Qed.

End PRP.

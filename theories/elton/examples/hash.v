From clutch.elton Require Import elton.
From clutch.elton.lib Require Import map.

Set Default Proof Using "Type*".

(** * This specification of the hash is modified to support delayed values as dom *)
Section simple_bit_hash.

  Context `{!eltonGS Σ}.

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

  Definition hashfun f (m:gmap base_lit nat) : iProp Σ :=
    ∃ (hm : loc), ⌜ f = compute_hash_specialized #hm ⌝ ∗
                  map_list' hm ((λ b, LitV (LitInt (Z.of_nat b))) <$> m) ∗
                  ⌜map_Forall (λ ind i, (0<= i <=val_size)%nat) m⌝
  .

  #[global] Instance timeless_hashfun f m :
    Timeless (hashfun f m).
  Proof. apply _. Qed.

  Lemma hashfun_implies_bounded_range f m idx x:
    hashfun f m -∗ ⌜m!!idx = Some x⌝ -∗ ⌜(0<=x<=val_size)%nat⌝.
  Proof.
    iIntros "(%&%&H&%K) %".
    iPureIntro.
    by eapply map_Forall_lookup_1 in K.
  Qed.

  Lemma wp_init_hash E :
    {{{ True }}}
      init_hash #() @ E
    {{{ f, RET f; |={E}=> hashfun f ∅ }}}.
  Proof.
    rewrite /init_hash.
    iIntros (Φ) "_ HΦ".
    wp_pures. rewrite /init_hash_state.
    wp_apply (wp_init_map' with "[//]").
    iIntros (?) "Hm". wp_pures.
    rewrite /compute_hash. wp_pures.
    iApply "HΦ". repeat iModIntro. rewrite /hashfun. iFrame.
    iSplit; first done.
    iPureIntro. intros ???. simplify_map_eq.
  Qed.

  Lemma wp_hashfun_prev E f m k (n:nat) k' R:
    base_lit_type_check k = Some BLTInt ->
    m!!k' = Some n ->
    {{{ hashfun f m ∗ R ∗ □(R -∗ rupd (λ v, v=true) R (k'=ᵥ k)%V) ∗
        □[∗ set] x∈dom m ∖ {[k']}, R -∗ rupd (λ v, v=false) R (x=ᵥ k)%V }}}
      f #k @ E
    {{{ RET #n; hashfun f m ∗ R}}}.
  Proof.
    iIntros (Htype Hlookup Φ) "(Hhash&R&#HR1&#HR2) HΦ".
    iDestruct "Hhash" as (hm ->) "[H Hbound]".
    rewrite /compute_hash_specialized.
    wp_pures.
    wp_apply (wp_get_some' with "[$H R ]"); first done.
    { rewrite lookup_fmap_Some. naive_solver. }
    { iSplit; first iExact "R". iFrame "HR1". rewrite dom_fmap_L. iFrame "HR2". }
    iIntros (vret) "(Hhash&R&->)".
    wp_pures. iApply "HΦ".
    by iFrame.
  Qed.

  Lemma wp_insert_new_avoid_one E f m (k:base_lit) (ε : R) (ε2 : fin (S val_size) -> R) R:
    base_lit_type_check k = Some BLTInt ->
    (∀ n, (0<=ε2 n)%R) ->
    (SeriesC (λ n, (1 / (S val_size)) * ε2 n)%R <= ε)%R →
    {{{ hashfun f m ∗ R ∗ (□[∗ set] x∈dom m, R -∗ rupd (λ v, v=false) R (x=ᵥ k)%V) ∗ ↯ ε
    }}}
      f #k @ E
    {{{ v, RET #v; hashfun f (<[ k := fin_to_nat v ]>m) ∗ R ∗ ↯ (ε2 v)}}}.
  Proof.
    iIntros (Htype Hpos Hineq Φ) "(Hhash & R & #HR&Herr) HΦ".
    iDestruct "Hhash" as (hm ->) "[H %Hbound]".
    rewrite /compute_hash_specialized.
    wp_pures.
    wp_apply (wp_get_none' with "[$H R]"); first done.
    { iSplit; first iExact "R".
      by rewrite dom_fmap_L.
    }
    iIntros (vret) "(Hhash&R&->)".
    wp_pures.
    wp_apply (wp_couple_rand_adv_comp'  with "[$]").
    { done. }
    { done. }
    iIntros (n) "Herr".
    wp_pures.
    wp_apply (wp_set' with "[$]"); first done.
    iIntros "?".
    wp_pures.
    iApply "HΦ".
    iFrame.
    iModIntro.
    iExists _. rewrite fmap_insert. iFrame.
    iSplit; first done.
    iPureIntro.
    intros i ? H.
    destruct (decide (k=i)); subst; simplify_map_eq.
    - pose proof fin_to_nat_lt n. lia.
    - unfold map_Forall in *. naive_solver.
  Qed. 

End simple_bit_hash.

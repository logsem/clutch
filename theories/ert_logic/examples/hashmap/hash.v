(** * Hash *)
From clutch.ert_logic Require Export expected_time_credits ert_weakestpre problang_wp proofmode
  derived_laws cost_models ert_rules.
From clutch.prob_lang Require Import notation tactics metatheory lang.
From iris.proofmode Require Export proofmode.
From Coq Require Export Reals Psatz.
From Coquelicot Require Export Hierarchy.
Require Import Lra.
From clutch.ert_logic.examples.hashmap Require Export map.

Set Default Proof Using "Type*".

Section simple_bit_hash.

  Context `{!ert_clutchGS Σ CostTick}.

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
    ∃ (hm : loc), ⌜ f = compute_hash_specialized #hm ⌝ ∗
                  map_list hm ((λ b, LitV (LitInt (Z.of_nat b))) <$> m) ∗
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
    wp_apply (wp_init_map with "[//]").
    iIntros (?) "Hm". wp_pures.
    rewrite /compute_hash. wp_pures.
    iApply "HΦ". repeat iModIntro. rewrite /hashfun.
    iExists _. rewrite fmap_empty. iFrame. eauto.
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


  Lemma wp_insert E f m (n : nat) :
    m !! n = None →
    {{{ hashfun f m 
    }}}
      f #n @ E
    {{{ (v : nat), RET #v; hashfun f (<[ n := v ]>m) }}}.
  Proof.
    iIntros (Hlookup Φ) "Hhash HΦ".
    iDestruct "Hhash" as (hm ->) "[H %Hbound]".
    rewrite /compute_hash_specialized.
    wp_pures.
    wp_apply (wp_get with "[$]").
    iIntros (vret) "(Hhash&->)".
    rewrite lookup_fmap Hlookup /=. wp_pures.
    wp_bind (rand _)%E.
    iMod etc_zero as "Hz".
    wp_apply (wp_couple_rand_constant with "[Hz]"); [done|iApply etc_irrel; last iFrame|].
    { simpl; lra. }
    iIntros "%x _".
    wp_pures.
    wp_apply (wp_set with "Hhash").
    iIntros "Hlist".
    wp_pures.
    iModIntro.
    iApply "HΦ".
    rewrite /hashfun.
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
  Qed.

  Lemma wp_insert_tc E f m (n : nat) x x2:
    m !! n = None →
    SeriesC (λ n0, 1 / S val_size * x2 n0)%R = x ->
    (∀ n0, (0 <= x2 n0)%R) ->
    {{{ ⧖ x ∗ hashfun f m 
    }}}
      f #n @ E
    {{{ (v : nat), RET #v; ∃ v': fin (S val_size), ⧖ (x2 (v')) ∗ ⌜fin_to_nat v' = v⌝ ∗ hashfun f (<[ n := v ]>m) }}}.
  Proof.
    iIntros (Hlookup Hsum Hpos Φ) "[Hx Hhash] HΦ".
    iDestruct "Hhash" as (hm ->) "[H %Hbound]".
    rewrite /compute_hash_specialized.
    wp_pures.
    wp_apply (wp_get with "[$]").
    iIntros (vret) "(Hhash&->)".
    rewrite lookup_fmap Hlookup /=. wp_pures.
    wp_bind (rand _)%E.
    wp_apply (wp_couple_rand_adv_comp' _ _ _ _ _ x2 with "[$Hx]"); try done.
    { rewrite Hsum. simpl. lra. }
    iIntros "%v Hx".
    wp_pures.
    wp_apply (wp_set with "Hhash").
    iIntros "Hlist".
    wp_pures.
    iModIntro.
    iApply "HΦ".
    rewrite /hashfun.
    iExists v. iFrame. iSplit; first done.
    iExists _.
    iSplit; first auto.
    iSplitL.
    + rewrite fmap_insert //.
    + iPureIntro.
      apply map_Forall_insert_2; last done.
      split.
      * lia.
      * pose proof (fin_to_nat_lt v).
        lia.
  Qed.
    
  
End simple_bit_hash.


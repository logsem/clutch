From stdpp Require Import namespaces finite.
From iris.base_logic Require Import invariants na_invariants.
From self.prob_lang Require Import notation proofmode primitive_laws spec_rules spec_tactics.
From self.logrel Require Import model rel_rules rel_tactics.
From iris.algebra Require Import auth gmap excl frac agree.
From self.prelude Require Import base.
From self.examples Require Import hash.

Set Default Proof Using "Type*".

(* A wrapper around the tape hash that gives an interface where the hashing function now takes as input
   a key k and a value v to be hashed. Different keys yield different hashes, and the library
   splits up ownership along keys.

   This is implemented by actually just having a single hash function,
   and on input k and v, we convert the pair (k, v) to a single integer that is then
   hashed.

 *)


Section keyed_hash.

  (* we assume the key space / value space are integers in the range {0, ..., 2^n - 1} for some power n. *)
  Context (MAX_KEYS_POW : nat).
  Context (MAX_VALS_POW : nat).

  Definition MAX_KEYS : nat := (Nat.pow 2 MAX_KEYS_POW) - 1.
  Definition MAX_VALS : nat := (Nat.pow 2 MAX_VALS_POW) - 1.
  Definition MAX_KEYS_Z : Z := (Z.pow 2 MAX_KEYS_POW) - 1.
  Definition MAX_VALS_Z : Z := (Z.pow 2 MAX_VALS_POW) - 1.

  Definition MAX_HASH_DOM : nat := ((Nat.pow 2 (MAX_KEYS_POW + MAX_VALS_POW)) - 1).

  Definition enc : val :=
    λ: "k" "v", ("k" ≪ #MAX_VALS_POW) + "v".

  Definition enc_gallina (k : nat) (v: nat) : nat :=
    (Nat.shiftl k MAX_VALS_POW) + v.

  Definition val_of_enc_gallina (x: nat) : nat :=
    x `mod` (Nat.pow 2 MAX_VALS_POW).

  Definition key_of_enc_gallina (x: nat) : nat :=
    (Nat.shiftr (x - val_of_enc_gallina x) MAX_VALS_POW).

  Lemma pow2_nonzero: ∀ x, 0 < 2 ^ x.
  Proof.
    intros x. induction x => /=; try lia.
  Qed.

  Definition not_in_key x k : Prop := (¬ ∃ v, enc_gallina k v = x).

  Lemma val_of_enc_gallina_spec1 k v :
    v <= MAX_VALS →
    val_of_enc_gallina (enc_gallina k v) = v.
  Proof.
    rewrite /val_of_enc_gallina /enc_gallina/MAX_VALS.
    rewrite ?Nat.shiftr_div_pow2 ?Nat.shiftl_mul_pow2.
    intros Hv.
    specialize (pow2_nonzero MAX_VALS_POW) => ?.
    rewrite plus_comm Nat.mod_add; last lia.
    rewrite Nat.mod_small; lia.
  Qed.

  Lemma val_of_enc_gallina_spec2 (x : nat) :
    val_of_enc_gallina x <= MAX_VALS.
  Proof.
    specialize (pow2_nonzero MAX_VALS_POW) => ?.
    cut (x `mod` (Nat.pow 2 MAX_VALS_POW) < Nat.pow 2 MAX_VALS_POW).
    { rewrite /val_of_enc_gallina/MAX_VALS. lia. }
    apply Nat.mod_upper_bound. lia.
  Qed.

  Lemma key_of_enc_gallina_spec1 (x : nat) k v :
    v <= MAX_VALS →
    key_of_enc_gallina (enc_gallina k v) = k.
  Proof.
    intros Hle.
    rewrite /key_of_enc_gallina val_of_enc_gallina_spec1 //.
    rewrite /enc_gallina/MAX_VALS.
    rewrite Nat.add_sub.
    rewrite Nat.shiftr_shiftl_r //.
    assert (MAX_VALS_POW - MAX_VALS_POW = 0) as -> by lia.
    rewrite Nat.shiftr_0_r //.
  Qed.

  Lemma Nat_div_sub_mod x k :
   0 < k ->
   x `div` k = (x - x `mod` k) `div` k.
  Proof.
    intros Hlt.
    rewrite Nat.mod_eq; last by lia.
    replace (x - (x - k * x `div` k)) with (k * x `div` k); last first.
    { remember (x `div` k) as y. cut (k * y <= x); try lia.
      rewrite Heqy. apply Nat.mul_div_le; lia. }
    rewrite Nat.mul_comm Nat.div_mul; lia.
  Qed.

  Lemma enc_gallina_inv x :
    enc_gallina (key_of_enc_gallina x) (val_of_enc_gallina x) = x.
  Proof.
    rewrite /enc_gallina/key_of_enc_gallina/val_of_enc_gallina.
    rewrite ?Nat.shiftr_div_pow2 ?Nat.shiftl_mul_pow2.
    symmetry.
    rewrite {1}(Nat.div_mod_eq x (Nat.pow 2 MAX_VALS_POW)).
    f_equal.
    rewrite Nat.mul_comm.
    rewrite Nat_div_sub_mod //. apply pow2_nonzero.
  Qed.

  Lemma enc_gallina_mono1 k1 k2 v1 v2:
    k1 < k2 -> v1 <= v2 -> enc_gallina k1 v1 < enc_gallina k2 v2.
  Proof.
    intros Hlt Hle.
    rewrite /enc_gallina.
    rewrite ?Nat.shiftr_div_pow2 ?Nat.shiftl_mul_pow2.
    specialize (pow2_nonzero MAX_VALS_POW) => Hnz.
    remember (2 ^ MAX_VALS_POW) as z.
    cut (k1 * z < k2 * z); first by lia.
    apply Mult.mult_lt_compat_r_stt; auto.
  Qed.

  Lemma enc_gallina_mono2 k1 k2 v1 v2:
    k1 < k2 -> v1 <= MAX_VALS -> v2 <= MAX_VALS -> enc_gallina k1 v1 < enc_gallina k2 v2.
  Proof.
    intros Hlt Hle1 Hle2.
    rewrite /enc_gallina.
    specialize (pow2_nonzero MAX_VALS_POW) => Hnz.
    rewrite ?Nat.shiftr_div_pow2 ?Nat.shiftl_mul_pow2.
    apply (Nat.lt_le_trans _ (k2 * 2 ^ MAX_VALS_POW)); last by lia.
    apply (Nat.lt_le_trans _ ((k1 + 1) * 2 ^ MAX_VALS_POW)); last first.
    { apply Nat.mul_le_mono_r; lia. }
    ring_simplify.
    rewrite /MAX_VALS in Hle1. lia.
  Qed.

  Lemma enc_gallina_mono2_inv k1 k2 v1 v2:
    enc_gallina k1 v1 <= enc_gallina k2 v2 ->
    v1 <= MAX_VALS ->
    v2 <= MAX_VALS ->
    k1 <= k2.
  Proof.
    intros Henc Hle1 Hle2.
    destruct (decide (k2 < k1)) as [Hlt|]; try lia.
    specialize (enc_gallina_mono2 _ _ _ _ Hlt Hle2 Hle1). lia.
  Qed.

  Lemma enc_hits_max :
    enc_gallina MAX_KEYS MAX_VALS = MAX_HASH_DOM.
  Proof.
    rewrite /enc_gallina/MAX_HASH_DOM/MAX_KEYS/MAX_VALS.
    rewrite ?Nat.shiftr_div_pow2 ?Nat.shiftl_mul_pow2.
    rewrite Nat.pow_add_r.
    specialize (pow2_nonzero MAX_VALS_POW) => ?.
    specialize (pow2_nonzero MAX_KEYS_POW) => ?.
    assert (2 ^ MAX_KEYS_POW = (2 ^ MAX_KEYS_POW - 1) + 1) as Hsub1 by lia.
    lia.
  Qed.

  Lemma key_of_enc_gallina_spec2 (x : nat) :
    x <= MAX_HASH_DOM →
    key_of_enc_gallina x <= MAX_KEYS.
  Proof.
    intros.
    eapply (enc_gallina_mono2_inv _ _ (val_of_enc_gallina x) (MAX_VALS));
      auto using val_of_enc_gallina_spec2.
    rewrite enc_gallina_inv enc_hits_max //.
  Qed.

  Lemma enc_gallina_range k v :
    k < S MAX_KEYS →
    v < S MAX_VALS →
    enc_gallina k v < S MAX_HASH_DOM.
  Proof.
    rewrite /enc_gallina/MAX_KEYS/MAX_VALS/MAX_HASH_DOM.
    rewrite ?Nat.shiftl_mul_pow2.
    assert (Hsub_le: ∀ a b, 0 < b -> a < S (b - 1) → a <= b - 1).
    { intros. lia. }
    assert (Hsub: ∀ x, 0 < x -> S (x - 1) = x).
    { intros. lia. }
    intros Hlt1 Hlt2.
    specialize (pow2_nonzero MAX_VALS_POW) => ?.
    specialize (pow2_nonzero MAX_KEYS_POW) => ?.
    apply Hsub_le in Hlt1; auto.
    apply Hsub_le in Hlt2; auto.
    rewrite ?Hsub; try (apply pow2_nonzero).
    rewrite Nat.pow_add_r.
    apply (le_lt_trans _ ((2 ^ MAX_KEYS_POW - 1) * 2 ^ MAX_VALS_POW + (2 ^ MAX_VALS_POW - 1))).
    { assert (Hcompat: ∀ a b c d, a <= b → c <= d → a + c <= b + d) by lia.
      apply Hcompat; try lia.
      apply Nat.mul_le_mono_r; auto.
    }
    assert (2 ^ MAX_KEYS_POW = (2 ^ MAX_KEYS_POW - 1) + 1) as Hsub1 by lia.
    lia.
  Qed.

  Definition init_keyed_hash : val :=
    λ: "_",
      let: "f" := init_hash #MAX_HASH_DOM in
      (λ: "k" "v", "f" (enc "k" "v")).

  Context `{!prelogrelGS Σ}.

  Lemma wp_enc_spec (k v : nat) E :
    {{{ ⌜ k <= MAX_KEYS ∧ v ≤ MAX_VALS ⌝ }}}
      enc #k #v @ E
    {{{ (n: nat), RET #n; ⌜ n = enc_gallina k v ⌝ }}}.
  Proof.
    rewrite /enc. iIntros (Φ) "%Hdom HΦ". wp_pures.
    rewrite Z.shiftl_mul_pow2; last by lia.
    iSpecialize ("HΦ" $! (Z.to_nat (Z.of_nat (enc_gallina k v)))).
    rewrite /enc_gallina Nat.shiftl_mul_pow2.
    rewrite Nat2Z.id Nat2Z.inj_add Nat2Z.inj_mul Nat2Z.inj_pow.
    iApply "HΦ". auto.
  Qed.


  Definition fin_hash_dom_space : Type := fin (S (MAX_HASH_DOM)).
  Definition fin_key_space : Type := fin (S (MAX_KEYS)).
  Definition fin_val_space : Type := fin (S (MAX_VALS)).

  Instance finite_fin_val_space : Finite (fin_val_space).
  Proof. apply _. Qed.
  Instance finite_fin_key_space : Finite (fin_key_space).
  Proof. apply _. Qed.
  Instance finite_fin_hash_dom_space : Finite (fin_hash_dom_space).
  Proof. apply _. Qed.

  Context {GHOST_MAP: ghost_mapG Σ fin_hash_dom_space (option bool)}.

  Definition enc_gallina_fin (k : fin_key_space) (v: fin_val_space) : fin_hash_dom_space.
    refine (@nat_to_fin (enc_gallina (fin_to_nat k) (fin_to_nat v)) _ _).
    apply (enc_gallina_range); apply fin_to_nat_lt.
  Defined.

  Definition keyed_hash_inv (γ : gname) (f : val) : iProp Σ :=
    ∃ (f0 : val) (mphys : gmap nat bool) (mghost : gmap fin_hash_dom_space (option bool)),
      ⌜ f = (λ: "k" "v", f0 (enc "k" "v"))%V ⌝ ∗
      ⌜ ∀ x b, mphys !! (fin_to_nat x) = Some b → mghost !! x = Some (Some b) ⌝ ∗
      ⌜ ∀ x, mphys !! (fin_to_nat x) = None → mghost !! x = Some (None) ⌝ ∗
      ghost_map_auth γ 1 mghost ∗
      hashfun MAX_HASH_DOM f0 mphys.

  (* This encoding is annoying to work with because we don't have good lemmas for
     "set products" and big_sepS over such products. *)
  (*
  Definition khashfun_own γ k (m : gmap nat bool) : iProp Σ :=
    ⌜ ∀ x, x ∈ dom m → x <= MAX_VALS ⌝ ∗
    [∗ set] v ∈ fin_to_set (fin_val_space), (enc_gallina_fin k v) ↪[γ] (m !! (fin_to_nat v)).
   *)

  Definition not_in_key_fin x k : Prop := (¬ ∃ v, enc_gallina_fin k v = x).

  (* This encoding is equivalent to the above in some sense but ends up being more workable
     in the absence of the above lemmas; I learned this trick from an encoding Upamanyu Sharma used
     used for representing "shards" of a key value store's key space, which is essentially equivalent
     to the problem here. *)
  Definition khashfun_own γ k (m : gmap nat bool) : iProp Σ :=
    ⌜ ∀ x, x ∈ dom m → x <= MAX_VALS ⌝ ∗
    [∗ set] kv ∈ fin_to_set (fin_hash_dom_space),
      (∃ v, ⌜ enc_gallina_fin k v = kv ⌝ ∗ kv ↪[γ] (m !! (fin_to_nat v))) ∨ ⌜ not_in_key_fin kv k ⌝.


  Lemma wp_init_keyed_hash E :
    {{{ True }}}
      init_keyed_hash #() @ E
    {{{ (f: val), RET f; ∃ γ, keyed_hash_inv γ f ∗
                              [∗ set] k ∈ fin_to_set (fin_key_space), khashfun_own γ k ∅ }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite /init_keyed_hash.
    wp_pures.
    wp_apply (wp_init_hash with "[//]").
    iIntros (f0) "Hf0".
    wp_pures. iApply "HΦ".
    set (m := gset_to_gmap None (fin_to_set (fin_hash_dom_space)) : gmap _ (option bool)).
    iMod (ghost_map_alloc m) as (γ) "(Hauth&Hfrags)".
    iModIntro. iExists γ.
    iSplitL "Hf0 Hauth".
    { iExists _, _, _. iFrame. iPureIntro; split_and!; eauto.
      { intros ??; rewrite lookup_empty; inversion 1. }
      { intros ? _. rewrite /m.
        rewrite lookup_gset_to_gmap_Some; split; auto.
        apply elem_of_fin_to_set. }
    }
    { rewrite /khashfun_own.
      iApply big_sepS_sep.
      iSplit.
      { iPureIntro. rewrite /set_Forall. intros ???. rewrite dom_empty_L. set_solver. }
      iApply big_sepS_sepS.
      rewrite /m.
      (* This proof is similar to one Ralf Jung developed for the above mentioned kv store's
         ghost state initialization *)
      iAssert ([∗ map] k↦v ∈ gset_to_gmap None (fin_to_set fin_hash_dom_space), k ↪[γ] None)%I with "[Hfrags]"
        as "H".
      { iApply (big_sepM_impl with "Hfrags"). iIntros "!>" (k x Hlookup).
        rewrite lookup_gset_to_gmap_Some in Hlookup.
        destruct Hlookup as (?&->). auto.
      }
      iDestruct (big_sepM_dom with "H") as "H".
      rewrite dom_gset_to_gmap.
      iApply (big_sepS_impl with "H").
      iIntros "!>" (x Hin) "Hx".
  Abort.
End keyed_hash.

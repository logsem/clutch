From stdpp Require Import countable.
From clutch Require Export clutch. 
From clutch.examples Require Export hash.

Set Default Proof Using "Type*".

(* A wrapper around the tape hash that gives an interface where the hashing function now takes as input
   a key k and a value v to be hashed. Different keys yield different hashes, and the library
   splits up ownership along keys.

   This is implemented by actually just having a single hash function,
   and on input k and v, we convert the pair (k, v) to a single integer that is then
   hashed.

 *)


Section keyed_hash.

  (* we assume the key space / value space are integers in the range
  {0, ..., 2^n_k - 1} and {0, ..., 2^n_v} for some natural numbers n_k
  and n_v. *)

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
    rewrite Nat.add_comm Nat.Div0.mod_add.
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
    rewrite Nat.Div0.mod_eq.
    replace (x - (x - k * x `div` k)) with (k * x `div` k); last first.
    { remember (x `div` k) as y. cut (k * y <= x); try lia.
      rewrite Heqy. apply Nat.Div0.mul_div_le; lia. }
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

  Lemma enc_gallina_inj k1 k2 v1 v2:
    enc_gallina k1 v1 = enc_gallina k2 v2 ->
    v1 <= MAX_VALS ->
    v2 <= MAX_VALS ->
    k1 = k2 /\ v1 = v2.
  Proof.
    intros Henc Hle1 Hle2.
    assert (k1 = k2) as ->.
    {
      apply Nat.le_antisymm.
      * eapply (enc_gallina_mono2_inv k1 k2 v1 v2); eauto; lia.
      * eapply (enc_gallina_mono2_inv k2 k1 v2 v1); eauto; lia.
    }
    split; auto.
    rewrite /enc_gallina in Henc. lia.
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
    apply (Nat.le_lt_trans _ ((2 ^ MAX_KEYS_POW - 1) * 2 ^ MAX_VALS_POW + (2 ^ MAX_VALS_POW - 1))).
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

  Context `{!clutchRGS Σ}.

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

  #[global] Instance countable_fin_hash_dom_space : Countable (fin_hash_dom_space).
  Proof. apply _. Qed.

  Context {GHOST_MAP: ghost_mapG Σ fin_hash_dom_space (option bool)}.

  Lemma fin_to_nat_S_le n (i: fin (S n)) : i <= n.
  Proof. specialize (fin_to_nat_lt i). lia. Qed.

  Definition enc_gallina_fin (k : fin_key_space) (v: fin_val_space) : fin_hash_dom_space.
    refine (@nat_to_fin (enc_gallina (fin_to_nat k) (fin_to_nat v)) _ _).
    abstract (apply (enc_gallina_range); apply fin_to_nat_lt).
  Defined.

  Definition key_of_enc_gallina_fin (x: fin_hash_dom_space) : fin_key_space.
  refine (@nat_to_fin (key_of_enc_gallina x) _ _).
  { abstract (cut (key_of_enc_gallina x <= MAX_KEYS); first lia;
              apply key_of_enc_gallina_spec2; specialize (fin_to_nat_lt x); lia; auto). }
  Defined.

  Definition val_of_enc_gallina_fin (x: fin_hash_dom_space) : fin_val_space.
  refine (@nat_to_fin (val_of_enc_gallina x) _ _).
  { abstract (cut (val_of_enc_gallina x <= MAX_VALS); first lia;
              apply val_of_enc_gallina_spec2; lia; auto). }
  Defined.

  Lemma enc_gallina_fin_inv x :
    enc_gallina_fin (key_of_enc_gallina_fin x) (val_of_enc_gallina_fin x) = x.
  Proof.
    rewrite /enc_gallina_fin/key_of_enc_gallina_fin/val_of_enc_gallina_fin/=.
    apply (inj fin_to_nat).
    rewrite ?fin_to_nat_to_fin enc_gallina_inv //.
  Qed.

  Lemma enc_gallina_fin_inj k1 k2 v1 v2 :
    enc_gallina_fin k1 v1 = enc_gallina_fin k2 v2 ->
    k1 = k2 /\ v1 = v2.
  Proof.
    rewrite /enc_gallina_fin.
    intros Hfeq%(f_equal fin_to_nat).
    rewrite ?fin_to_nat_to_fin in Hfeq.
    apply enc_gallina_inj in Hfeq; auto using fin_to_nat_S_le.
    split; apply (inj fin_to_nat); intuition auto.
  Qed.

  Definition khashN := nroot.@"khash".

  Definition ghost_phys_dom (mphys : gmap nat bool) (mghost : gmap fin_hash_dom_space (option bool)) :=
      (∀ x b, mphys !! (fin_to_nat x) = Some b → mghost !! x = Some (Some b)) ∧
      (∀ x, mphys !! (fin_to_nat x) = None → mghost !! x = Some (None)).

  Definition keyed_hash_auth_pure (f f0 : expr) (mphys : gmap nat bool) (mghost : gmap fin_hash_dom_space (option bool))
    : iProp Σ :=
      ⌜ f = (λ: "k" "v", f0 (enc "k" "v"))%V ⌝ ∗
      ⌜ ghost_phys_dom mphys mghost ⌝.

  Definition keyed_hash_auth (γ : gname) (f : val) : iProp Σ :=
    ∃ (f0 : val) (mphys : gmap nat bool) (mghost : gmap fin_hash_dom_space (option bool)),
      keyed_hash_auth_pure f f0 mphys mghost ∗
      ghost_map_auth γ 1 mghost ∗
      hashfun MAX_HASH_DOM f0 mphys.

  Definition skeyed_hash_auth (γ : gname) (f : val) : iProp Σ :=
    ∃ (f0 : val) (mphys : gmap nat bool) (mghost : gmap fin_hash_dom_space (option bool)),
      keyed_hash_auth_pure f f0 mphys mghost ∗
      ghost_map_auth γ 1 mghost ∗
      shashfun MAX_HASH_DOM f0 mphys.

  Section timeless_spec.
    Existing Instance timeless_shashfun.
    Lemma timeless_skeyed_hash_auth γ f :
      Timeless (skeyed_hash_auth γ f).
    Proof. apply _. Qed.
  End timeless_spec.

  Existing Instance timeless_hashfun.
  #[global] Instance timeless_keyed_hash_auth γ f :
    Timeless (keyed_hash_auth γ f).
  Proof. apply _. Qed.


  (*
  Definition is_keyed_hash γ f :=
    inv khashN (keyed_hash_auth γ f).
   *)

  (* This encoding is annoying to work with because we don't have good lemmas for
     "set products" and big_sepS over such products. *)
  (*
  Definition khashfun_own γ k (m : gmap nat bool) : iProp Σ :=
    ⌜ ∀ x, x ∈ dom m → x <= MAX_VALS ⌝ ∗
    [∗ set] v ∈ fin_to_set (fin_val_space), (enc_gallina_fin k v) ↪[γ] (m !! (fin_to_nat v)).
   *)

  Definition not_in_key_fin x k : Prop := (¬ ∃ v, enc_gallina_fin k v = x).

  Lemma not_in_key_fin_spec x k :
    k ≠ key_of_enc_gallina_fin x →
    not_in_key_fin x k.
  Proof.
    intros Hneq (v&Henc). apply Hneq.
    rewrite -Henc.
    rewrite /enc_gallina_fin/key_of_enc_gallina_fin/val_of_enc_gallina_fin/=.
    apply (inj fin_to_nat).
    rewrite ?fin_to_nat_to_fin.
    rewrite key_of_enc_gallina_spec1 //.
    specialize (fin_to_nat_lt v); lia.
  Qed.

  (* This encoding is equivalent to the above in some sense but ends up being more workable
     in the absence of the above lemmas; I learned this trick from an encoding Upamanyu Sharma used
     used for representing "shards" of a key value store's key space, which is essentially equivalent
     to the problem here. *)
  Definition khashfun_own γ k (m : gmap nat bool) : iProp Σ :=
    ⌜ ∀ x, x ∈ dom m → x <= MAX_VALS ⌝ ∗
    [∗ set] kv ∈ fin_to_set (fin_hash_dom_space),
      (∃ v, ⌜ enc_gallina_fin k v = kv ⌝ ∗ kv ↪[γ] (m !! (fin_to_nat v))) ∨ ⌜ not_in_key_fin kv k ⌝.

  Lemma keyed_hash_ghost_init_split γ :
   ([∗ map] k↦v ∈ gset_to_gmap None (fin_to_set fin_hash_dom_space), k ↪[γ] v) -∗
   [∗ set] k ∈ fin_to_set fin_key_space, khashfun_own γ k ∅.
  Proof.
    rewrite /khashfun_own.
    iIntros "Hfrags".
    iApply big_sepS_sep.
    iSplit.
    { iPureIntro. rewrite /set_Forall. intros ???. rewrite dom_empty_L. set_solver. }
    iApply big_sepS_sepS.
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
    rewrite (big_sepS_delete _ _ (key_of_enc_gallina_fin x)); last first.
    { apply elem_of_fin_to_set. }
    iSplitL "Hx".
    - iLeft. iExists (val_of_enc_gallina_fin x). rewrite lookup_empty //. iFrame.
      iPureIntro. rewrite enc_gallina_fin_inv //.
    - iApply big_sepS_intro.
      iIntros "!#" (k [Hk Hne]%elem_of_difference).
      iRight.
      iPureIntro.
      set_unfold.
      apply not_in_key_fin_spec; auto.
  Qed.

  Lemma ghost_phys_dom_init :
    ghost_phys_dom ∅ (gset_to_gmap None (fin_to_set fin_hash_dom_space)).
  Proof.
    split.
    - intros ??; rewrite lookup_empty; inversion 1.
    - intros ? _.
     rewrite lookup_gset_to_gmap_Some; split; auto.
     apply elem_of_fin_to_set.
  Qed.

  Lemma wp_init_keyed_hash E :
    {{{ True }}}
      init_keyed_hash #() @ E
    {{{ (f: val), RET f; ∃ γ, keyed_hash_auth γ f ∗
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
    iExists γ.
    iSplitL "Hf0 Hauth".
    { iExists _, _, _. iFrame. iPureIntro; split_and!; eauto using ghost_phys_dom_init. }
    { iApply keyed_hash_ghost_init_split. auto. }
  Qed.

  Lemma spec_init_keyed_hash E K :
    ↑specN ⊆ E →
    refines_right K (init_keyed_hash #()) ={E}=∗
    ∃ f γ, refines_right K (of_val f) ∗ skeyed_hash_auth γ f ∗
           [∗ set] k ∈ fin_to_set (fin_key_space), khashfun_own γ k ∅.
  Proof.
    iIntros (?) "HK".
    rewrite /init_keyed_hash.
    tp_pures.
    tp_bind (init_hash _).
    rewrite refines_right_bind.
    iMod (spec_init_hash with "[$]") as (f0) "(HK&Hf0)"; first done.
    rewrite -refines_right_bind /=.
    tp_pures.
    set (m := gset_to_gmap None (fin_to_set (fin_hash_dom_space)) : gmap _ (option bool)).
    iMod (ghost_map_alloc m) as (γ) "(Hauth&Hfrags)".
    iExists _, γ. iFrame "HK".
    iSplitL "Hf0 Hauth".
    { iExists _, _, _. iFrame. iPureIntro; split_and!; eauto using ghost_phys_dom_init. }
    { iApply keyed_hash_ghost_init_split. auto. }
  Qed.

  Lemma khashfun_own_acc_assign_hash γ k v m :
    khashfun_own γ k m -∗
    (enc_gallina_fin k v) ↪[γ] (m !! (fin_to_nat v)) ∗
    (∀ b, (enc_gallina_fin k v) ↪[γ] (Some b) -∗ khashfun_own γ k (<[fin_to_nat v := b]>m)).
  Proof.
    iIntros "(%Hdom&Hk)".
    rewrite (big_sepS_delete _ _ (enc_gallina_fin k v)); last first.
    { apply elem_of_fin_to_set. }
    iDestruct "Hk" as "(Hkv&Hrest)".
    iSplitL "Hkv".
    { iDestruct "Hkv" as "[Hleft|%Hbad]".
      { iDestruct "Hleft" as (? Heq) "H". apply enc_gallina_fin_inj in Heq as (Heq1&Heq2). subst. auto. }
      iExFalso. iPureIntro. apply Hbad. eexists; eauto.
    }
    iIntros (b) "Hkv". iSplit.
    { iPureIntro. set_unfold. intros ? [?|?]; auto. subst.
      apply fin_to_nat_S_le. }
    iApply (big_sepS_delete _ _ (enc_gallina_fin k v)).
    { apply elem_of_fin_to_set. }
    iSplitL "Hkv".
    { iLeft. iExists _. iSplit; first eauto. rewrite lookup_insert //. }
    iApply (big_sepS_mono with "Hrest").
    { iIntros (x [Hx Hne]%elem_of_difference).
      set_unfold. iIntros "H".
      iDestruct "H" as "[Hleft|Hright]"; last by (iRight; eauto).
      iDestruct "Hleft" as (? Heq) "Hx". iLeft. iExists _; iSplit; first done.
      rewrite lookup_insert_ne //. subst. intros Heq.
      apply (inj fin_to_nat) in Heq. congruence.
    }
  Qed.

  Lemma khashfun_own_acc_lookup γ k v m :
    khashfun_own γ k m -∗
    (enc_gallina_fin k v) ↪[γ] (m !! (fin_to_nat v)) ∗
    ((enc_gallina_fin k v) ↪[γ] (m !! (fin_to_nat v)) -∗ khashfun_own γ k m).
  Proof.
    iIntros "(%Hdom&Hk)".
    rewrite (big_sepS_delete _ _ (enc_gallina_fin k v)); last first.
    { apply elem_of_fin_to_set. }
    iDestruct "Hk" as "(Hkv&Hrest)".
    iSplitL "Hkv".
    { iDestruct "Hkv" as "[Hleft|%Hbad]".
      { iDestruct "Hleft" as (? Heq) "H". apply enc_gallina_fin_inj in Heq as (Heq1&Heq2). subst. auto. }
      iExFalso. iPureIntro. apply Hbad. eexists; eauto.
    }
    iIntros "Hkv". iSplit; auto. iApply big_sepS_delete; first by apply elem_of_fin_to_set. iFrame.
    iLeft. eauto.
  Qed.

 (* TODO: move *)
  Lemma impl_couplable_wand (P Q: bool → iProp Σ) :
    impl_couplable P -∗
    (∀ b, P b -∗ Q b) -∗
    impl_couplable Q.
  Proof.
    rewrite /impl_couplable.
    iDestruct 1 as (α bs) "(Hα&HP)".
    iIntros "HPQ".
    iExists α, bs. iFrame. iIntros (?) "H". iApply "HPQ".
    iApply "HP". auto.
  Qed.

 (* TODO: move *)
  Lemma spec_couplable_wand (P Q: bool → iProp Σ) :
    spec_couplable P -∗
    (∀ b, P b -∗ Q b) -∗
    spec_couplable Q.
  Proof.
    iDestruct 1 as (α bs) "(Hα&HP)".
    iIntros "HPQ".
    iExists α, bs. iFrame. iIntros (?) "H". iApply "HPQ".
    iApply "HP". auto.
  Qed.

  Lemma ghost_phys_dom_insert x b mphys mghost :
    ghost_phys_dom mphys mghost →
    ghost_phys_dom (<[fin_to_nat x :=b]> mphys) (<[x :=Some b]> mghost).
  Proof.
    intros (?&?).
    split.
  - intros x' b'. destruct (decide (x = x')).
    { subst. rewrite ?lookup_insert // => -> //. }
    rewrite ?lookup_insert_ne //; eauto. intros ?%(inj fin_to_nat); congruence.
  - intros x'. destruct (decide (x = x')).
    { subst. rewrite ?lookup_insert // => -> //. }
    rewrite ?lookup_insert_ne //; eauto. intros ?%(inj fin_to_nat); congruence.
  Qed.

  Lemma ghost_phys_dom_rev mphys mghost x ob :
    ghost_phys_dom mphys mghost →
    mghost !! x = Some ob →
    mphys !! (fin_to_nat x) = ob.
  Proof.
    intros (Hdom1&Hdom2) Hlook_ghost.
    destruct ob as [b'|] eqn:Hob.
    - destruct (mphys !! (fin_to_nat x)) as [b|] eqn:Hlook_phys; last first.
      { exfalso. apply Hdom2 in Hlook_phys. rewrite Hlook_phys in Hlook_ghost. inversion Hlook_ghost. }
      { apply Hdom1 in Hlook_phys. congruence. }
    - destruct (mphys !! (fin_to_nat x)) as [b|] eqn:Hlook_phys.
      { exfalso. apply Hdom1 in Hlook_phys. rewrite Hlook_phys in Hlook_ghost. inversion Hlook_ghost. }
      { apply Hdom2 in Hlook_phys. congruence. }
  Qed.

  Lemma khashfun_own_couplable γ k f m v:
    v <= MAX_VALS →
    m !! v = None →
    keyed_hash_auth γ f -∗
    khashfun_own γ k m -∗ impl_couplable (λ b, |==> keyed_hash_auth γ f ∗ khashfun_own γ k (<[v:=b]>m)).
  Proof.
    iIntros (Hmax Hlookup) "Hhash Hk".
    assert (Hmax': v < S MAX_VALS) by lia.
    set (v' := nat_to_fin Hmax' : fin_val_space).
    iDestruct "Hhash" as (??? (Heq1&Hdom1&Hdom2)) "(Hauth&H)".
    set (x := enc_gallina_fin k v').
    iDestruct (khashfun_own_acc_assign_hash _ _ v' with "Hk") as "(Hpts&Hclo')".
    iDestruct (ghost_map_lookup with "[$] [$]") as %Hlook.
    assert (m !! fin_to_nat v' = None) as Hnone.
    { rewrite fin_to_nat_to_fin //. }
    rewrite Hnone in Hlook.
    iDestruct (hashfun_couplable (enc_gallina_fin k v') with "H") as "H".
    { apply fin_to_nat_S_le. }
    { eapply ghost_phys_dom_rev; eauto. split; auto. }
    iApply (impl_couplable_wand with "H").
    iIntros (b) "Hhash".
    iMod (ghost_map_update (Some b) with "[$] [$]") as "(Hauth&Hpts)".
    iDestruct ("Hclo'" with "[$]") as "Hk".
    iModIntro.
    iSplitL "Hhash Hauth".
    { iExists _, _, _.
      iFrame. iPureIntro; split_and!; eauto.
      apply ghost_phys_dom_insert. split; auto.
    }
    rewrite /v' fin_to_nat_to_fin //.
  Qed.

  Lemma khashfun_own_spec_couplable γ k f m v:
    v <= MAX_VALS →
    m !! v = None →
    skeyed_hash_auth γ f -∗
    khashfun_own γ k m -∗ spec_couplable (λ b, |==> skeyed_hash_auth γ f ∗ khashfun_own γ k (<[v:=b]>m)).
  Proof.
    iIntros (Hmax Hlookup) "Hhash Hk".
    assert (Hmax': v < S MAX_VALS) by lia.
    set (v' := nat_to_fin Hmax' : fin_val_space).
    iDestruct "Hhash" as (??? (Heq1&Hdom1&Hdom2)) "(Hauth&H)".
    set (x := enc_gallina_fin k v').
    iDestruct (khashfun_own_acc_assign_hash _ _ v' with "Hk") as "(Hpts&Hclo')".
    iDestruct (ghost_map_lookup with "[$] [$]") as %Hlook.
    assert (m !! fin_to_nat v' = None) as Hnone.
    { rewrite fin_to_nat_to_fin //. }
    rewrite Hnone in Hlook.
    iDestruct (shashfun_couplable (enc_gallina_fin k v') with "H") as "H".
    { apply fin_to_nat_S_le. }
    { eapply ghost_phys_dom_rev; eauto. split; auto. }
    iApply (spec_couplable_wand with "H").
    iIntros (b) "Hhash".
    iMod (ghost_map_update (Some b) with "[$] [$]") as "(Hauth&Hpts)".
    iDestruct ("Hclo'" with "[$]") as "Hk".
    iModIntro.
    iSplitL "Hhash Hauth".
    { iExists _, _, _.
      iFrame. iPureIntro; split_and!; eauto.
      apply ghost_phys_dom_insert. split; auto.
    }
    rewrite /v' fin_to_nat_to_fin //.
  Qed.

  Lemma wp_khashfun_prev E f m k (v : nat) γ (b : bool) :
    m !! v = Some b →
    {{{ keyed_hash_auth γ f ∗ khashfun_own γ k m }}}
      f #k #v @ E
    {{{ RET #b; keyed_hash_auth γ f ∗ khashfun_own γ k m }}}.
  Proof.
    iIntros (Hlookup Φ) "(H&Hown) HΦ".
    iDestruct "H" as (??? (Heq1&Hdom1&Hdom2)) "(Hauth&H)".
    rewrite Heq1. rewrite /enc. wp_pures.
    iAssert (⌜ v < S MAX_VALS ⌝)%I as "%Hmax'".
    { iDestruct "Hown" as "(%Hdom&_)". iPureIntro. apply elem_of_dom_2 in Hlookup.
      apply Hdom in Hlookup. lia. }
    set (v' := nat_to_fin Hmax' : fin_val_space).
    replace (#(k ≪ MAX_VALS_POW + v)) with #(fin_to_nat (enc_gallina_fin k v')); last first.
    { f_equal. rewrite /enc_gallina_fin ?fin_to_nat_to_fin /enc_gallina.
      rewrite /enc_gallina Nat.shiftl_mul_pow2 Z.shiftl_mul_pow2; last by lia.
      rewrite Nat2Z.inj_add Nat2Z.inj_mul Nat2Z.inj_pow //.
    }
    iDestruct (khashfun_own_acc_lookup _ _ v' with "Hown") as "(Hkv&Hclo)".
    iDestruct (ghost_map_lookup with "[$] [$]") as %Hlook.
    eapply ghost_phys_dom_rev in Hlook; last by (split; eauto).
    wp_apply (wp_hashfun_prev with "H").
    { rewrite Hlook. rewrite ?fin_to_nat_to_fin //. }
    iIntros "H".
    iApply "HΦ". iSplitL "Hauth H".
    { iExists _, _, _. iFrame. eauto. }
    iApply "Hclo". eauto.
  Qed.

  Lemma spec_khashfun_prev E K f m k (v : nat) γ (b : bool) :
    m !! v = Some b →
    ↑specN ⊆ E →
    skeyed_hash_auth γ f -∗
    khashfun_own γ k m -∗
    refines_right K (f #k #v) ={E}=∗
    refines_right K (of_val #b) ∗ skeyed_hash_auth γ f ∗ khashfun_own γ k m.
  Proof.
    iIntros (Hlookup ?) "Hauth Hown HK".
    iDestruct "Hauth" as (??? (Heq1&Hdom1&Hdom2)) "(Hauth&H)".
    rewrite Heq1. rewrite /enc. tp_pures.
    iAssert (⌜ v < S MAX_VALS ⌝)%I as "%Hmax'".
    { iDestruct "Hown" as "(%Hdom&_)". iPureIntro. apply elem_of_dom_2 in Hlookup.
      apply Hdom in Hlookup. lia. }
    set (v' := nat_to_fin Hmax' : fin_val_space).
    replace (#(k ≪ MAX_VALS_POW + v)) with #(fin_to_nat (enc_gallina_fin k v')); last first.
    { f_equal. rewrite /enc_gallina_fin ?fin_to_nat_to_fin /enc_gallina.
      rewrite /enc_gallina Nat.shiftl_mul_pow2 Z.shiftl_mul_pow2; last by lia.
      rewrite Nat2Z.inj_add Nat2Z.inj_mul Nat2Z.inj_pow //.
    }
    iDestruct (khashfun_own_acc_lookup _ _ v' with "Hown") as "(Hkv&Hclo)".
    iDestruct (ghost_map_lookup with "[$] [$]") as %Hlook.
    eapply ghost_phys_dom_rev in Hlook; last by (split; eauto).
    iMod (spec_hashfun_prev with "H HK") as "(HK&H)".
    { rewrite Hlook. rewrite ?fin_to_nat_to_fin //. }
    { done. }
    iFrame.
    iModIntro.
    iSplitL "Hauth H".
    { iExists _, _, _. iFrame. eauto. }
    iApply "Hclo". eauto.
  Qed.

  (* Actually this is not true: if v is out of range it can be as if
     you're hashing a differnt value with some other key! *)
  Lemma wp_khashfun_out_of_range E f k m (v : Z) γ :
    (v < 0 ∨ MAX_VALS < v)%Z →
    {{{ keyed_hash_auth γ f ∗ khashfun_own γ k m }}}
      f #k #v @ E
    {{{ RET #false; keyed_hash_auth γ f ∗ khashfun_own γ k m }}}.
  Proof.
  Abort.

End keyed_hash.



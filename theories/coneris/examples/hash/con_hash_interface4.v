From clutch.coneris Require Import coneris.

Set Default Proof Using "Type*".

(** A concurrent interface for hash functions with presampling for individual keys *)
Class con_hash4 Σ `{!conerisGS Σ} := Con_Hash4
{
  (** * Operations *)
  init_con_hash : val;

  (** * Predicates *)
  conhashfun (γs : gname * gname * gname) (val_size : nat) (f : val) : iProp Σ;
  hashkey (γs : gname * gname * gname) (k : nat) (v : option nat) : iProp Σ;

  (** * General properties of the predicates *)
  #[global] hashkey_timeless γs k v :: Timeless (hashkey γs k v);
  #[global] conhashfun_persistent γs vs f :: Persistent (conhashfun γs vs f);
  #[global] hashkey_Some_persistent γs k v :: Persistent (hashkey γs k (Some v));

  hashkey_presample k (bad : gset nat) (ε εI εO: nonnegreal) γs val_size f :
    (∀ x, x ∈ bad → x < S val_size) →
    (εI * size bad + εO * (val_size + 1 - size bad) <= ε * (val_size + 1))%R →
    conhashfun γs val_size f -∗
    hashkey γs k None -∗
    ↯ ε -∗
    state_update ⊤ ⊤ (∃ (n : fin (S val_size)),
      ((⌜fin_to_nat n ∉ bad⌝ ∗ ↯ εO) ∨ (⌜fin_to_nat n ∈ bad⌝ ∗ ↯ εI)) ∗
      hashkey γs k (Some (fin_to_nat n)));

  conhash_init val_size max :
    {{{ True }}}
      init_con_hash #val_size #max
    {{{ γs conhash, RET conhash;
        conhashfun γs val_size conhash ∗
        ([∗ set] k ∈ (set_seq 0 (S max)), hashkey γs k None)  }}} ;

  wp_conhashfun_prev f (k n : nat) γs val_size :
    {{{ conhashfun γs val_size f ∗ hashkey γs k (Some n) }}}
      f #k
    {{{ RET #n; True }}}
}.

Section derived_lemmas.
  Context `{conerisGS Σ, !con_hash4 Σ}.

  Lemma wp_hash_lookup_safe k f γs val_size :
    {{{ hashkey γs k None ∗ conhashfun γs val_size f }}}
      f #k
    {{{ (v : nat), RET #v; ⌜(v ≤ val_size)%nat⌝ ∗ hashkey γs k (Some v) }}}.
  Proof.
    iIntros (Φ) "(HNone & #Hinv) HΦ".
    iMod (ec_zero) as "Herr".
    iApply state_update_pgl_wp.
    iMod (hashkey_presample _ ∅ nnreal_zero nnreal_zero nnreal_zero with "Hinv HNone [Herr]")
      as "(%v & _ & #Hkey)"; auto.
    - set_solver.
    - rewrite size_empty /=. lra.
    - iModIntro.
      wp_apply (wp_conhashfun_prev with "[-HΦ]"); auto.
      iIntros "_". iApply "HΦ". iFrame "#". iPureIntro.
      pose proof (fin_to_nat_lt v). lia.
  Qed.

  Lemma wp_hash_lookup_avoid_set k f γs (bad : gset nat)(ε εI εO:nonnegreal) val_size :
    (∀ x : nat, x ∈ bad → (x < S val_size)%nat) →
    (εI * (size bad) + εO * (val_size + 1 - size bad) <= ε * (val_size + 1))%R →
    {{{ ↯ ε ∗ hashkey γs k None ∗ conhashfun γs val_size f }}}
      f #k
    {{{ (v : nat), RET #v;
        ⌜(v ≤ val_size)%nat⌝ ∗
        ((⌜v ∈ bad⌝) ∗ ↯ εI  ∨ (⌜v ∉ bad⌝) ∗ ↯ εO) ∗
        hashkey γs k (Some v) }}}.
  Proof.
    iIntros (Hbad Hdistr Φ) "(Herr & Hnone & #Hinv) HΦ".
    iApply state_update_pgl_wp.
    iMod (hashkey_presample _ bad ε εI εO with "Hinv Hnone [Herr]")
      as "(%v & Hv & #Hhauth)"; auto.
    iModIntro.
    wp_apply (wp_conhashfun_prev with "[$]").
    iIntros "Hf".
    iApply "HΦ". iFrame.
    iSplit; [iPureIntro|].
    { pose proof (fin_to_nat_lt v). lia. }
    iDestruct "Hv" as "[?|?]"; auto.
  Qed.

End derived_lemmas.

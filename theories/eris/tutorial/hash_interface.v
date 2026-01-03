From clutch.eris Require Export eris.
From stdpp Require Export fin_maps.
Set Default Proof Using "Type*".


(** An interface for hash functions *)
Class hash_function Σ `{!erisGS Σ} := Hash_Function
{

  (** * Operations *)
  init_hash : val;

  (** * Predicates *)
  hashfun (val_size : nat) (f : val) (m : gmap nat nat): iProp Σ;

  (** * General properties of the predicates
  #[global] hashkey_timeless γs k v :: Timeless (hashkey γs k v);
  #[global] conhashfun_persistent γs vs f :: Persistent (hashfun γs vs f);
  #[global] hashkey_Some_persistent γs k v :: Persistent (hashkey γs k (Some v));
  *)


  hash_init_spec key_size val_size :
  {{{ True }}}
    init_hash #key_size #val_size
  {{{ h, RET h;
        hashfun val_size h ∅  }}} ;

  hash_query_spec_fresh (k : nat) (avoid : gset nat) (ε εI εO: R) val_size
    f (m : gmap nat nat) :
     m !! k = None ->
     (0 <= εI)%R ->
     (0 <= εO)%R ->
     (∀ x, x ∈ avoid → x < S val_size) →
     (εI * size avoid + εO * (val_size + 1 - size avoid) <= ε * (val_size + 1))%R →
     {{{ hashfun val_size f m ∗
           ↯ ε
     }}}
       f #k
       {{{ n, RET #n;
           ⌜ n < S val_size ⌝%nat ∗
                   hashfun val_size f (<[k := n]> m) ∗
        ((⌜n ∉ avoid⌝ ∗ ↯ εO) ∨ (⌜n ∈ avoid⌝ ∗ ↯ εI))
    }}} ;

  hash_query_spec_prev (k : nat) val_size (v :nat) f (m : gmap nat nat) :
  m !! k = Some v ->
  {{{ hashfun val_size f m
  }}}
    f #k
    {{{ RET #v; hashfun val_size f m }}}
}.

Section derived_lemmas.
  Context `{!erisGS Σ, !hash_function Σ}.

Lemma wp_insert_basic f val_size m (n : nat)  :
    m !! n = None →
    {{{ hashfun val_size f m }}}
      f #n
      {{{ (v : nat), RET #v; ⌜ (v < S val_size)%nat ⌝ ∗ hashfun val_size f (<[ n := v ]>m) }}}.
Proof.
  iIntros (Hlookup Φ) "Hhash HΦ".
  iMod (ec_zero) as "Herr".
  iApply (hash_query_spec_fresh n ∅ 0%R 0%R 0%R val_size with "[$]"); eauto.
  - lra.
  - lra.
  - intro x.
    rewrite elem_of_empty //.
  - rewrite size_empty /=.
    lra.
  - iModIntro.
    iIntros (n0) "(%Hsize & Hf & Hset)".
    iApply ("HΦ" with "[-]").
    by iFrame.
Qed.

End derived_lemmas.

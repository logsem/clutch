From clutch.eris Require Export eris.
From stdpp Require Export fin_maps.
Set Default Proof Using "Type*".


(**  * Hash Functions  *)

(** ** Hash interface *)

(** Here we construct an abstract interface for hash functions. This will allow
  us to work with hashes using a random oracle model, i.e. the first time we
  hash a key it will return a uniformly sampled value, and subsequent times will
  return the same value. Note that this is not how real world hashes work, but
  it is a common model to reason about hash-based data structures and algorithms.
  One can actually implement a data structure that behaves like this by using
  a map/dictionary whose values are sampled at random, but for the purpose of
  this tutorial we will work with the abstract interface.

  At the code level, the hash will be accessed through a function f, which is a
  value. Our logical view of the hash function will be given by a partial map m
  from keys to values. *)

Class hash_function Σ `{!erisGS Σ} := Hash_Function
{

  (** *** Operations *)
  init_hash : val;

  (** *** Predicates *)

  (** The hashfun predicate connects the code level function f with its abstract
     representation m. Here val_size is a bound on the codomain of the hash,
     i.e., the hash should return values in [0,...,val_size] *)

  hashfun (val_size : nat) (f : val) (m : gmap nat nat): iProp Σ;

  (** *** Properties *)

  (** All values must be within [0,...,val_size] *)

  hash_val_in_bd :
  ∀ vs f m k v,
    m !! k = Some v ->
    hashfun vs f m ⊢ ⌜ v < S vs ⌝;

  (** *** Specifications *)

  hash_init_spec val_size :
  {{{ True }}}
    init_hash #val_size
  {{{ h, RET h;
        hashfun val_size h ∅  }}} ;

  (** The key spec for working with hash functions is below. Here we are hashing
     a fresh key k, and we want its value v to fall outside of a set avoid.
     Instead of directly specifying that v∉avoid, we will distribute our current
     error budget ↯ε depending on whether v falls inside or outside avoid,
     giving ↯εI to the former and ↯εO to the latter.

     Since we assume that values for the hash are distributed uniformly, we will
     impose the condition

     (εI * size avoid + εO * (val_size + 1 - size avoid) <= ε * (val_size + 1))

     Note that:
       (1) The probability of falling in avoid is (size avoid / (val_size + 1))
       (2) The probability of falling outside of avoid is
           (val_size + 1 - size avoid) / (val_size + 1)

     Therefore the inequality above states that the ε is at least equal or
     larger to the expected amount of error credits we will have after hashing

     On returning, we will get a value n, an updated view on the hash, where the
     partial map now contains the key-value pair (k,n) and an amount of error
     credits depending on whether n ∈ avoid or n ∉ avoid. *)

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


   (** If we are hashing a previously hashed elem, then we simply return its
     assigned value, which is in the map *)

  hash_query_spec_prev (k : nat) val_size (v :nat) f (m : gmap nat nat) :
  m !! k = Some v ->
  {{{ hashfun val_size f m
  }}}
    f #k
    {{{ RET #v; hashfun val_size f m }}}
}.

Section derived_lemmas.
  Context `{!erisGS Σ, !hash_function Σ}.

(**  ** Derived lemmas about hash functions *)

(** We derive some lemmas that will allow us to work with the hash function.
   First, one can always query a fresh element without spending error credits,
   and then one gets no information about the value, besides that it is within
   range *)

Lemma hash_query_spec_fresh_basic (k : nat) val_size f m :
    m !! k = None →
    {{{ hashfun val_size f m }}}
      f #k
      {{{ (v : nat), RET #v; ⌜ (v < S val_size)%nat ⌝ ∗ hashfun val_size f (<[ k := v ]>m) }}}.
Proof.
  iIntros (Hlookup Φ) "Hhash HΦ".
  iMod (ec_zero) as "Herr".
  iApply (hash_query_spec_fresh k ∅ 0%R 0%R 0%R val_size with "[$]"); eauto.
  - real_solver.
  - real_solver.
  - intro x.
    rewrite elem_of_empty.
    intros F.
    exfalso.
    apply F.
  - rewrite size_empty.
    real_solver.
  - iModIntro.
    iIntros (n0) "(%Hsize & Hf & Hset)".
    iApply ("HΦ" with "[-]").
    by iFrame.
Qed.


(** Second, if one has enough error credits, one can avoid hashing a fresh
   element into a value in the avoid set *)


Lemma hash_query_spec_fresh_avoid_aux (k : nat) (avoid : gset nat) (ε : R) (val_size : nat) f m:
  m !! k = None →
  (∀ x, x ∈ avoid → x < S val_size) →
  (size avoid <= ε * (val_size + 1))%R →
  {{{ hashfun val_size f m ∗ ↯ ε }}}
    f #k
    {{{ (v : nat), RET #v; ⌜ (v < S val_size)%nat ⌝ ∗
                             hashfun val_size f (<[ k := v ]>m) ∗
                             ⌜ v ∉ avoid ⌝ }}}.
Proof.
  iIntros (Hlookup Hav Hε Φ) "(Hhash & Herr) HΦ".
  (** The key to this proof is the following step,
     where we assign ↯ 1 to the case where we sample
     an index in avoid and ↯ 0 otherwise.
   *)
  wp_apply (hash_query_spec_fresh  _ avoid
              _ 1 0 val_size _ m
             with "[$]"); auto.
  - real_solver.
  - real_solver.
  - real_solver.
  - iIntros (v) "(%Hv & Hhfw & Herr)".
     iDestruct "Herr" as "[(%Hvout & Herr) | (%Hvin & Herr)]".
     + iApply "HΦ".
       iFrame.
       iPureIntro.
       split; auto.
     + iPoseProof (ec_contradict with "[$Herr]") as "?"; [real_solver|].
       done.
Qed.

(** We can actually get rid of the hypothesis (∀ x, x ∈ avoid → x < S val_size)
    This is used to ensure we have the right multiplier for credits whenever we
    fall outside of the avoid set, but since we are giving 0 credits to that
    case it does not matter
 *)

Lemma hash_query_spec_fresh_avoid (k : nat) (avoid : gset nat) (ε : R) (val_size : nat) f m:
  m !! k = None →
  (size avoid <= ε * (val_size + 1))%R →
  {{{ hashfun val_size f m ∗ ↯ ε }}}
    f #k
    {{{ (v : nat), RET #v; ⌜ (v < S val_size)%nat ⌝ ∗
                           hashfun val_size f (<[ k := v ]>m) ∗
                           ⌜ v ∉ avoid ⌝ }}}.
Proof.
  iIntros (Hlookup Hε Φ) "(Hhash & Herr) HΦ".

  (** We first compute the intersection of avoid with with [0,...,val_size] to
     obtain a new set avoid' satisfying the premise of
     hash_query_spec_fresh_avoid_aux *)

  set (avoid' := avoid ∩ (set_seq 0 (val_size + 1))).
  wp_apply (hash_query_spec_fresh_avoid_aux _ avoid' _ val_size _ m
             with "[$]"); auto; rewrite /avoid'.
  (** The rest of the proof is mostly simple reasoning about sets *)
  - intros x Hx.
    rewrite elem_of_intersection in Hx.
    destruct Hx as [Hx1 Hx2].
    rewrite elem_of_set_seq in Hx2.
    nat_solver.
  - transitivity (size avoid); auto.
    apply le_INR.
    apply subseteq_size.
    set_solver.
  - iIntros (v) "(%Hv & Hhfw & %Hvout)".
    iApply "HΦ".
    iFrame.
    iPureIntro.
    split; auto.
    intros Hv2.
    apply Hvout.
    rewrite elem_of_intersection.
    split; auto.
    rewrite elem_of_set_seq.
    nat_solver.
Qed.

(** ** An example program *)

(** As a first use of our hash specifications, we will consider a simple
   example, where initialize a hash, hash two different integers, and check that
   their outputs are different *)

  Definition two_hash : expr :=
         let: "hf" := init_hash #7 in
         let: "v1" := "hf" #1 in
         let: "v2" := "hf" #2 in
         ("v1", "v2").

  Lemma two_hash_spec :
    {{{ ↯ (1/8) }}}
      two_hash
      {{{ v1 v2, RET (#v1,#v2) ; ⌜ v1 ≠ v2 ⌝ }}}.
  Proof.
    iIntros (Φ) "Herr HΦ".
    unfold two_hash.
    (** We first initialize the hash, with size 7 for values *)
    wp_apply (hash_init_spec 7); auto.
    iIntros (h) "Hhf".
    wp_pures.
    (** We now hash 1. The map is currently empty, and any
       result is valid at this point. Therefore, we do not
       need to spend any amount of error credits *)
    wp_apply (hash_query_spec_fresh_basic 1 with "[$]").
    {
      set_solver.
    }
    iIntros (v1) "(%Hv1 & Hhf)".
    wp_pures.
    (** We now hash 2. At this point, we want to avoid a collision with 1, that
       is, we want the result to not be v1. Since this is a singleton set, and
       the size of the value space is 8, we can spend ↯(1/8) to avoid it *)
    (* Exercise *)
    (* Admitted. *)

    (*  Sample solution: *)
    wp_apply (hash_query_spec_fresh_avoid 2 {[v1]} with "[$]").
    {
      set_solver.
    }
    - rewrite size_singleton /=.
      lra.
    - iIntros (v2) "(%Hv2 & Hhf & %Hnelem)".
      wp_pures.
      iApply "HΦ".
      iPureIntro.
      set_solver.
  Qed.




End derived_lemmas.

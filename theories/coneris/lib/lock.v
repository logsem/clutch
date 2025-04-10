From iris.base_logic.lib Require Export invariants.
From clutch.coneris Require Import coneris.
From clutch.con_prob_lang Require Import notation.
From iris.prelude Require Import options.
(** Taken from the Iris development *)
(** A general interface for a lock.

All parameters are implicit, since it is expected that there is only one
[heapGS_gen] in scope that could possibly apply.

Only one instance of this class should ever be in scope. To write a library that
is generic over the lock, just add a [`{!lock}] implicit parameter around the
code and [`{!lockG Σ}] around the proofs. To use a particular lock instance, use
[Local Existing Instance <lock instance>].

When writing an instance of this class, please take care not to shadow the class
projections (e.g., either use [Local Definition newlock] or avoid the name
[newlock] altogether), and do not register an instance -- just make it a
[Definition] that others can register later. *)
Class lock := Lock {
  (** * Operations *)
  newlock : val;
  acquire : val;
  release : val;
  (** * Ghost state *)
  (** The assumptions about [Σ] *)
  lockG : gFunctors → Type;
  (** [name] is used to associate [locked] with [is_lock] *)
  lock_name : Type;
  (** * Predicates *)
  (** No namespace [N] parameter because we only expose program specs, which
  anyway have the full mask. *)
  is_lock `{!conerisGS Σ} {L : lockG Σ} (γ: lock_name) (lock: val) (R: iProp Σ) : iProp Σ;
  locked `{!conerisGS Σ} {L : lockG Σ} (γ: lock_name) : iProp Σ;
  (** * General properties of the predicates *)
  #[global] is_lock_persistent `{!conerisGS Σ} {L : lockG Σ} γ lk R ::
    Persistent (is_lock (L:=L) γ lk R);
  is_lock_iff `{!conerisGS Σ} {L : lockG Σ} γ lk R1 R2 :
    is_lock (L:=L) γ lk R1 -∗ ▷ □ (R1 ∗-∗ R2) -∗ is_lock (L:=L) γ lk R2;
  #[global] locked_timeless `{!conerisGS Σ} {L : lockG Σ} γ ::
    Timeless (locked (L:=L) γ);
  locked_exclusive `{!conerisGS Σ} {L : lockG Σ} γ :
    locked (L:=L) γ -∗ locked (L:=L) γ -∗ False;
  (** * Program specs *)
  newlock_spec `{!conerisGS Σ} {L : lockG Σ} (R : iProp Σ):
    {{{ R }}} newlock #() {{{ lk γ, RET lk; is_lock (L:=L) γ lk R }}};
  acquire_spec `{!conerisGS Σ} {L : lockG Σ} γ lk R :
    {{{ is_lock (L:=L) γ lk R }}} acquire lk {{{ RET #(); locked (L:=L) γ ∗ R }}};
  release_spec `{!conerisGS Σ} {L : lockG Σ} γ lk R :
    {{{ is_lock (L:=L) γ lk R ∗ locked (L:=L) γ ∗ R }}} release lk {{{ RET #(); True }}}
}.

Global Arguments newlock : simpl never.
Global Arguments acquire : simpl never.
Global Arguments release : simpl never.
Global Arguments is_lock : simpl never.
Global Arguments locked : simpl never.

Existing Class lockG.
Global Hint Mode lockG + + : typeclass_instances.
Global Hint Extern 0 (lockG _) => progress simpl : typeclass_instances.

Global Instance is_lock_contractive `{!conerisGS Σ, !lock, !lockG Σ} γ lk :
  Contractive (is_lock γ lk).
Proof.
  apply (uPred.contractive_internal_eq (M:=iResUR Σ)).
  iIntros (P Q) "#HPQ". iApply prop_ext. iIntros "!>".
  iSplit; iIntros "H"; iApply (is_lock_iff with "H");
    iNext; iRewrite "HPQ"; auto.
Qed.

Global Instance is_lock_proper `{!conerisGS Σ, !lock, !lockG Σ} γ lk :
  Proper ((≡) ==> (≡)) (is_lock γ lk) := ne_proper _.

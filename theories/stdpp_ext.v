From Coq.ssr Require Export ssreflect.
From stdpp Require Import countable option.

Section option.

  Definition option_apply {A B} (f : A → B) (v : B) (mx : option A) :=
    match mx with Some x => f x | None => v end.

End option.

Section countable.
  Context `{Countable A}.

  (* a right partial inverse to encode  *)
  Definition encode_inv (p : positive) : option A :=
    a ← decode p;
    guard (encode a = p);
    mret a.

  Lemma encode_inv_encode a :
    encode_inv (encode a) = Some a.
  Proof.
    rewrite /encode_inv decode_encode /=.
    case_option_guard; done.
  Qed.

  Lemma encode_encode_inv (p : positive) :
    option_apply encode p (encode_inv p) = p.
  Proof.
    rewrite /encode_inv.
    destruct (decode _)=>//=.
    case_option_guard=>//=.
  Qed.

  Lemma encode_inv_Some n a :
    encode_inv n = Some a →
    encode a = n.
  Proof.
    intros Heq. specialize (encode_encode_inv n). rewrite Heq //.
  Qed.

  Lemma encode_inv_some_inj n n' a:
    encode_inv n = Some a →
    encode_inv n = encode_inv n' →
    n = n'.
  Proof.
    intros ? ?.
    transitivity (encode a).
    - by symmetry; apply encode_inv_Some.
    - apply encode_inv_Some. congruence.
  Qed.

  (* a right partial inverse to encode_nat  *)
  Definition encode_inv_nat (n : nat) : option A :=
    a ← decode_nat n;
    guard (encode_nat a = n);
    mret a.

  Lemma encode_inv_encode_nat a :
    encode_inv_nat (encode_nat a) = Some a.
  Proof.
    rewrite /encode_inv_nat decode_encode_nat /=.
    case_option_guard; done.
  Qed.

  Lemma encode_encode_inv_nat (n : nat) :
    option_apply encode_nat n (encode_inv_nat n) = n.
  Proof.
    rewrite /encode_inv_nat.
    destruct (decode_nat _)=>//=.
    case_option_guard=>//=.
  Qed.

  Lemma encode_inv_Some_nat n a :
    encode_inv_nat n = Some a →
    encode_nat a = n.
  Proof.
    intros Heq. specialize (encode_encode_inv_nat n). rewrite Heq //.
  Qed.

  Lemma encode_inv_nat_some_inj n n' a:
    encode_inv_nat n = Some a →
    encode_inv_nat n = encode_inv_nat n' →
    n = n'.
  Proof.
    intros Hn Heq.
    transitivity (encode_nat a).
    - by symmetry; apply encode_inv_Some_nat.
    - apply encode_inv_Some_nat. congruence.
  Qed.


End countable.

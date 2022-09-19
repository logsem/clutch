From stdpp Require Import countable.

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
    unfold encode_inv.
    rewrite decode_encode. simpl.
    case_option_guard; done.
  Qed.

  Lemma encode_encode_inv (p : positive) :
    from_option encode p (encode_inv p) = p.
  Proof.
    unfold encode_inv.
    destruct (decode _); try done; simpl.
    case_option_guard; done.
  Qed.

  Lemma encode_inv_Some n a :
    encode_inv n = Some a →
    encode a = n.
  Proof.
    intros Heq. specialize (encode_encode_inv n). by rewrite Heq.
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
    unfold encode_inv_nat.
    rewrite decode_encode_nat; simpl.
    case_option_guard; done.
  Qed.

  Lemma encode_encode_inv_nat (n : nat) :
    from_option encode_nat n (encode_inv_nat n) = n.
  Proof.
    unfold encode_inv_nat.
    destruct (decode_nat _); try done; simpl.
    by case_option_guard.
  Qed.

  Lemma encode_inv_Some_nat n a :
    encode_inv_nat n = Some a →
    encode_nat a = n.
  Proof.
    intros Heq. specialize (encode_encode_inv_nat n). by rewrite Heq.
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

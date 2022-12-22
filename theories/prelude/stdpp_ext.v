From stdpp Require Import countable fin_maps.

Section base.
  Global Instance negb_inj : Inj (=) (=) negb.
  Proof. intros [] []; auto. Qed.

  Global Instance negb_surj : Surj (=) negb.
  Proof. intros []; [exists false|exists true]; done. Qed.

  Lemma bool_fn_inj_1 (f : bool → bool) `{Inj bool bool (=) (=) f} b b' :
    f (negb b) = (negb b') → f b = b'.
  Proof.
    destruct b, b'; simpl.
    - destruct (f true) eqn: Heq; [done|].
      rewrite <-Heq at 2. intros; simplify_eq.
    - destruct (f true) eqn: Heq; [|done].
      rewrite <-Heq. intros; simplify_eq.
    - destruct (f false) eqn: Heq; [done|].
      rewrite <-Heq. intros; simplify_eq.
    - destruct (f false) eqn: Heq; [|done].
      rewrite <-Heq at 2. intros; simplify_eq.
  Qed.

  Lemma bool_fn_inj_2 (f : bool → bool) `{Inj bool bool (=) (=) f} b b' :
    f b = b' → f (negb b) = (negb b').
  Proof.
    intros. eapply bool_fn_inj_1; [done|]. by rewrite 2!negb_involutive.
  Qed.

  Class Bij {A B} (f : A → B) := {
    bij_inj :> Inj (=) (=) f;
    bij_surj :> Surj (=) f;
  }.

  Global Existing Instance bij_inj.
  Global Existing Instance bij_surj.

  Global Instance bij_id {A} : Bij (@id A).
  Proof. constructor; apply _. Qed.

  Global Instance bij_negb : Bij negb.
  Proof. constructor; apply _. Qed.
End base.

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

Section fin_maps.
  Context `{FinMap K M}.

  Lemma insert_inv {A} (m : M A) i x x' :
    <[i := x]>m = <[i := x']>m → x = x'.
  Proof.
    rewrite map_eq_iff.
    intros Heq. specialize (Heq i).
    rewrite 2!(lookup_insert _ i) in Heq.
    by simplify_option_eq.
  Qed.

  Lemma lookup_total_correct_2 `{!Inhabited A} (m : M A) i :
    m !! i = None → m !!! i = inhabitant.
  Proof. rewrite lookup_total_alt. by intros ->. Qed.

End fin_maps.

Section list.
  Context {A B : Type}.

  Lemma elem_of_list_prod l1 l2 (a : A) (b : B) :
    (a, b) ∈ list_prod l1 l2 ↔ a ∈ l1 ∧ b ∈ l2.
  Proof. rewrite !elem_of_list_In. apply in_prod_iff. Qed.

  Lemma elem_of_list_prod_1 l1 l2 (a : A) (b : B) :
    (a, b) ∈ list_prod l1 l2 → a ∈ l1 ∧ b ∈ l2.
  Proof. apply elem_of_list_prod. Qed.

  Lemma elem_of_list_prod_1_fst l1 l2 (a : A) (b : B) :
    (a, b) ∈ list_prod l1 l2 → a ∈ l1.
  Proof. apply elem_of_list_prod_1. Qed.

  Lemma elem_of_list_prod_1_snd l1 l2 (a : A) (b : B) :
    (a, b) ∈ list_prod l1 l2 → a ∈ l1.
  Proof. apply elem_of_list_prod_1. Qed.

  Lemma elem_of_list_prod_2 l1 l2 (a : A) (b : B) :
    a ∈ l1 ∧ b ∈ l2 → (a, b) ∈ list_prod l1 l2.
  Proof. apply elem_of_list_prod. Qed.

End list.

Tactic Notation "case_match" "in" ident(H) "eqn" ":" ident(Hd) :=
  match type of H with
  | context [ match ?x with _ => _ end ] => destruct x eqn:Hd
  | _ => fail "expected hypothesis to include a 'match'"
  end.

Tactic Notation "case_match" "in" ident(H) :=
  let Hf := fresh in case_match in H eqn:Hf.

Tactic Notation "case_bool_decide" "in" ident(H) "as" ident(Hd) :=
  match type of H with
  | context [@bool_decide ?P ?dec] =>
      destruct_decide (@bool_decide_reflect P dec) as Hd
  | _ => fail "expected hypothesis to include a 'bool_decide _'"
  end.
Tactic Notation "case_bool_decide" "in" ident(H) :=
  let Hfr := fresh in case_bool_decide in H as Hf.

Tactic Notation "case_bool_decide_and_destruct" "in" ident(H) :=
  let Hf := fresh in
  case_bool_decide in H as Hf;
  destruct_and? Hf;
  simplify_eq.

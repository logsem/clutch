From stdpp Require Import countable fin_maps finite.
From clutch.prelude Require Import classical.

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
    bij_inj :: Inj (=) (=) f;
    bij_surj :: Surj (=) f;
  }.

  Global Existing Instance bij_inj.
  Global Existing Instance bij_surj.

  (* Other instances should be declared with a priority penalty higher than 0. *)
  Global Instance bij_id {A} : Bij (@id A) | 0.
  Proof. constructor; apply _. Qed.

  Global Instance bij_negb : Bij negb | 1.
  Proof. constructor; apply _. Qed.

End base.

(** ** [nat_to_bool] *)
(* We take [0] to mean [false] and any other value to be [true] *)
Definition nat_to_bool (n : nat) : bool :=
  if bool_decide (n = 0) then false else true.

Lemma nat_to_bool_false n : nat_to_bool n = false → n = 0.
Proof. destruct n; naive_solver. Qed.
Lemma nat_to_bool_eq_0 : nat_to_bool 0 = false.
Proof. done. Qed.
Lemma nat_to_bool_neq_0 n : n ≠ 0 → nat_to_bool n = true.
Proof. destruct n; naive_solver. Qed.

Definition bool_to_nat (b : bool) := if b then 1 else 0.

Lemma bool_to_nat_to_bool b : nat_to_bool (bool_to_nat b) = b.
Proof. destruct b; naive_solver. Qed.
Lemma nat_to_bool_to_nat n : n ≤ 1 → bool_to_nat (nat_to_bool n) = n.
Proof. do 2 (destruct n; [naive_solver|]). lia. Qed.

Definition fin_to_bool (n : fin 2) : bool :=
  match n with
  | 0%fin => false
  | _ => true
  end.

Definition bool_to_fin (b : bool) := ((if b then 1%fin else 0%fin) : fin 2).

Lemma bool_to_fin_to_bool b : fin_to_bool (bool_to_fin b) = b.
Proof. destruct b; naive_solver. Qed.
Lemma fin_to_bool_to_fin n : bool_to_fin (fin_to_bool n) = n.
Proof.
  inv_fin n; [naive_solver|].
  intros n.
  inv_fin n; [naive_solver|].
  intros n.
  inv_fin n.
Qed.

Lemma bool_to_fin_to_nat_inv b :
  nat_to_bool (fin_to_nat (bool_to_fin b)) = b.
Proof. by destruct b. Qed.

Lemma fin_to_nat_to_bool_inv n :
  nat_to_bool (fin_to_nat n) = fin_to_bool n.
Proof.
  inv_fin n; [naive_solver|].
  intros n.
  inv_fin n; [naive_solver|].
  intros n.
  inv_fin n.
Qed.

Global Instance bool_to_fin_inj : Inj (=) (=) bool_to_fin.
Proof. by intros [] [] ?. Qed.
Global Instance bool_to_fin_surj : Surj (=) bool_to_fin.
Proof.
  intros n.
  inv_fin n; [by exists false|].
  intros n; inv_fin n; [by exists true|].
  intros n. inv_fin n.
Qed.

Global Instance fin_to_bool_inj : Inj (=) (=) fin_to_bool.
Proof.
  intros n m ?.
  inv_fin n; inv_fin m; try done.
  intros n m _.
  inv_fin n.
  - inv_fin m; [done|]. intros m. inv_fin m.
  - intros p. inv_fin p.
Qed.
Global Instance fin_to_bool_surj : Surj (=) fin_to_bool.
Proof. intros []; [by exists 1%fin|by exists 0%fin]. Qed.

(** ** [Z_to_bool] *)
(* We take [0] to mean [false] and any other value to be [true] *)
Definition Z_to_bool (z : Z) : bool :=
  if bool_decide (z = 0%Z) then false else true.

Lemma Z_to_bool_false z : Z_to_bool z = false → z = 0%Z.
Proof. destruct z; naive_solver. Qed.
Lemma Z_to_bool_eq_0 : Z_to_bool 0%Z = false.
Proof. done. Qed.
Lemma Z_to_bool_neq_0 z : z ≠ 0%Z → Z_to_bool z = true.
Proof. destruct z; naive_solver. Qed.
Lemma Z_to_bool_of_nat n : Z_to_bool (Z.of_nat n) = nat_to_bool n.
Proof. destruct n; naive_solver. Qed.

(* TODO: upstream *)
Global Instance sigT_eq_dec `{EqDecision A} (P : A → Type) `{!∀ x, EqDecision (P x)} :
  EqDecision { x : A & P x }.
Proof.
  intros [x Px] [y Py].
  destruct (decide (x = y)) as [->|]; [|right; naive_solver].
  destruct (decide (Px = Py)); [left|right]; naive_solver.
Defined.

Global Program Instance countable_sigT `{HA : EqDecision A, HCA : !Countable A} (P : A → Type)
        `{HDP : ∀ x, EqDecision (P x)} `{HCP : !∀ x, Countable (P x) } :
  Countable { x : A & P x } :=
  {| encode '(existT x y) := prod_encode (encode x) (encode y);
     decode p :=
       x ← prod_decode_fst p ≫= decode;
       y ← prod_decode_snd p ≫= decode;
       Some (existT x y) |}.
Next Obligation.
  intros ?????? [x y]; simpl.
  rewrite prod_decode_encode_fst, prod_decode_encode_snd; simpl.
  by do 2 (rewrite decode_encode; simpl).
Qed.

Notation "( x ; y )" := (existT x y) (at level 0, format "( x ;  '/  ' y )").

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

(* The lemmas about [Finite A] make use of the [Countable A] instance
   `[finite_countable] from std++ [finite.v]. For [fin N], for example, there
   already exists another instance. We give the highest priority ([0]) to
   [finite_countable] to be able to use the lemmas. *)
#[global] Existing Instance finite_countable | 0.

Lemma encode_nat_nat (n : nat) :
  encode_nat n = n.
Proof.
  unfold encode_nat, encode; simpl.
  unfold encode; simpl.
  case_match; lia.
Qed.

Lemma encode_inv_nat_Some_inj (n n' : nat) :
  encode_inv_nat n = Some n' → n = n'.
Proof.
  intros H%encode_inv_Some_nat.
  by rewrite encode_nat_nat in H.
Qed.

Lemma encode_inv_nat_None (n : nat) :
  ¬ (@encode_inv_nat nat _ _ n = None).
Proof. by rewrite <-(encode_nat_nat n), encode_inv_encode_nat. Qed.

Section finite.
  Context `{Finite A}.

  Lemma encode_inv_decode  (i : nat) :
    i < card A → ∃ a : A, encode_inv_nat i = Some a ∧ encode_nat a = i.
  Proof.
    intros (a & Hd & <-)%encode_decode.
    exists a.
    by rewrite encode_inv_encode_nat.
  Qed.

  Lemma encode_inv_decode_ge (i : nat) :
    (i ≥ card A)%nat → @encode_inv_nat A _ _ i = None.
  Proof.
    intros Hge. unfold encode_inv_nat.
    destruct (decode_nat i) eqn:Hd; [|done]; simpl.
    case_option_guard; [|done].
    pose proof (encode_lt_card a). lia.
  Qed.

  Lemma encode_nat_finite a n :
    encode_nat a = n ↔ enum A !! n = Some a.
  Proof.
    unfold encode_nat, encode; simpl.
    rewrite Nat2Pos.id; [|done].
    destruct (list_find_elem_of (a =.) (enum A) a) as [[i y] Hfind]; auto.
    { eapply elem_of_enum. }
    rewrite Hfind. simpl.
    eapply list_find_Some in Hfind as (? & -> & ?).
    split; [by intros <-|].
    intros Hn.
    eapply NoDup_alt; [|done|done].
    apply NoDup_enum.
  Qed.

  Lemma encode_inv_nat_finite n :
    encode_inv_nat n = enum A !! n.
  Proof.
    unfold encode_inv_nat.
    (* TODO this assert used to be computed by simpl before 8.18. *)
    assert ((decode_nat n) = (enum A !! pred (Pos.to_nat (Pos.of_nat (S n))))) as -> by reflexivity.
    rewrite Nat2Pos.id; [|done].
    destruct (decide (n < card A)%nat) as [Hlt | Hnlt%not_lt]; simpl.
    - destruct (encode_inv_decode n Hlt) as (? & Hdec & Henc).
      unfold encode_inv_nat, decode_nat, decode in Hdec.
      simpl in Hdec.
      rewrite Nat2Pos.id in Hdec; [|done].
      simpl in Hdec.
      rewrite Hdec. by apply encode_nat_finite in Henc.
    - destruct (enum A !! n) eqn:Henum; [|done].
      apply encode_nat_finite in Henum.
      simpl. by rewrite option_guard_True.
  Qed.

End finite.

(* The lemmas about [Finite A] make use of the [Countable A] instance
   `[finite_countable] from std++ [finite.v]. For [fin N], for example, there
   already exists another instance. We give the highest priority ([0]) to
   [finite_countable] to be able to use the lemmas. *)
#[export] Existing Instance finite_countable | 0.

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

Ltac destruct_match :=
  match goal with
  | |- context [ match ?x with _ => _ end ] => destruct x
  | H : context [ match ?x with _ => _ end ] |- _ => destruct x
  end.

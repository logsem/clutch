From stdpp Require Import countable fin_maps finite gmap.
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
    guard (encode a = p);;
    mret a.

  Lemma encode_inv_encode a :
    encode_inv (encode a) = Some a.
  Proof.
    unfold encode_inv.
    rewrite decode_encode. simpl.
    case_guard; done.
  Qed.

  Lemma encode_encode_inv (p : positive) :
    from_option encode p (encode_inv p) = p.
  Proof.
    unfold encode_inv.
    destruct (decode _); try done; simpl.
    case_guard; done.
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
    guard (encode_nat a = n);;
    mret a.

  Lemma encode_inv_encode_nat a :
    encode_inv_nat (encode_nat a) = Some a.
  Proof.
    unfold encode_inv_nat.
    rewrite decode_encode_nat; simpl.
    case_guard; done.
  Qed.

  Lemma encode_encode_inv_nat (n : nat) :
    from_option encode_nat n (encode_inv_nat n) = n.
  Proof.
    unfold encode_inv_nat.
    destruct (decode_nat _); try done; simpl.
    by case_guard.
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
    case_guard; [|done].
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

  Lemma fmap_inj (f:A -> B) (l1 l2: list A):
    Inj (=) (=) f -> f<$>l1=f<$>l2 -> l1 = l2.
  Proof.
    intros H.
    revert l2.
    induction l1.
    - intros ? K. simpl in *.
      by erewrite fmap_nil_inv.
    - intros l2 K.
      rewrite fmap_cons in K.
      destruct l2.
      + rewrite fmap_nil in K. simplify_eq.
      + rewrite fmap_cons in K.
        by simplify_eq.
  Qed.

End list.

Section gset.
  Context `{Countable A}.
  Lemma length_elements_size_gset (s:gset A): size (s) = length (elements s).
    done.
  Qed.
End gset.

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


(* (** * [gmultiset]  *) *)

(* Lemma gmultiset_difference_empty_l `{Countable A} (X : gmultiset A) : *)
(*   ∅ ∖ X = ∅. *)
(* Proof. multiset_solver. Qed. *)

(* Lemma gmultiset_difference_empty_r `{Countable A} (X : gmultiset A) : *)
(*   X ∖ ∅ = X. *)
(* Proof. multiset_solver. Qed. *)

(* Lemma gmultiset_difference_disj_union `{Countable A} (X Y Z : gmultiset A) : *)
(*   X ∖ (Y ⊎ Z)  = (X ∖ Y) ∖ Z. *)
(* Proof. multiset_solver. Qed. *)

(* Lemma gmultiset_difference_disj `{Countable A} (X Y : gmultiset A): *)
(*   X ## Y → X ∖ Y = X. *)
(* Proof. multiset_solver. Qed. *)

(* Lemma gmultiset_union_alt `{Countable A} (X Y : gmultiset A) : *)
(*   X ∪ Y = (X ∖ Y) ⊎ (Y ∖ X) ⊎ (X ∩ Y). *)
(* Proof. multiset_solver. Qed. *)

(* Lemma gmultiset_size_difference_singleton_le `{Countable A} (X : gmultiset A) x : *)
(*   size X - 1 ≤ size (X ∖ {[+ x +]}) ≤ size X. *)
(* Proof. *)
(*   destruct (decide (x ∈ X)) as [He|Hne]. *)
(*   - rewrite gmultiset_size_difference; [|multiset_solver]. *)
(*     rewrite gmultiset_size_singleton. lia. *)
(*   - rewrite gmultiset_difference_disj; [lia | multiset_solver]. *)
(* Qed. *)

(* Lemma gmultiset_size_difference_le `{Countable A} (X Y : gmultiset A) : *)
(*   size X - size Y ≤ size (X ∖ Y) ≤ size X. *)
(* Proof. *)
(*   induction Y using gmultiset_ind. *)
(*   { rewrite gmultiset_size_difference; [|multiset_solver]. lia. } *)
(*   rewrite gmultiset_disj_union_comm. *)
(*   rewrite gmultiset_difference_disj_union. *)
(*   pose proof (gmultiset_size_difference_singleton_le (X ∖ Y) x) as [? ?]. *)
(*   rewrite gmultiset_size_disj_union. *)
(*   rewrite gmultiset_size_singleton. *)
(*   lia. *)
(* Qed. *)

(* Lemma size_list_to_set_disj `{Countable T} (xs : list T) : *)
(*   size (list_to_set_disj xs : gmultiset _) = length xs. *)
(* Proof. *)
(*   induction xs. *)
(*   - rewrite list_to_set_disj_nil. done. *)
(*   - rewrite list_to_set_disj_cons. *)
(*     rewrite gmultiset_size_disj_union, gmultiset_size_singleton, IHxs. done. *)
(* Qed. *)

(* Lemma size_multiplicity_le `{Countable A} (X Y : gmultiset A) : *)
(*   (∀ z, multiplicity z X ≤ multiplicity z Y) → size X ≤ size Y. *)
(* Proof. intros ?. by eapply gmultiset_subseteq_size. Qed. *)


(** * list  *)
Fixpoint list_count `{Countable T} (x : T) (l : list T) : nat :=
  match l with
  | [] => 0
  | y :: l => (if decide (x = y) then 1%nat else 0%nat) + list_count x l
  end.

Fixpoint list_delete `{EqDecision A} (x : A) (l : list A) : list A :=
  match l with
  | [] => []
  | y :: l => if decide (x = y) then l else y :: list_delete x l
  end.

Lemma list_difference_app `{Countable T} (xs ys zs : list T) :
  list_difference (xs ++ ys) zs = list_difference xs zs ++ list_difference ys zs.
Proof.
  induction xs => /=; [done|].
  case_decide; [done|].
  by rewrite IHxs.
Qed.

Lemma list_difference_cons `{Countable T} (xs : list T) x :
  list_difference (x :: xs) [x] = list_difference xs [x].
Proof. simpl. case_decide; [done|]. set_solver. Qed.

Lemma list_count_not_elem_of  `{Countable T} (xs : list T) x :
  x ∉ xs → list_count x xs = 0%nat.
Proof.
  induction xs; [done|].
  intros [? ?]%not_elem_of_cons => /=.
  rewrite decide_False; [|done].
  by rewrite IHxs.
Qed.

Lemma list_delete_not_elem_of `{Countable T} x (xs : list T) :
  x ∉ xs → list_delete x xs = xs.
Proof.
  induction xs; [done|].
  intros [? ?]%not_elem_of_cons => /=.
  by rewrite decide_False, IHxs.
Qed.



Lemma list_count_hd `{Countable T} (xs : list T) x :
  list_count x (x :: xs) = (1 + list_count x xs)%nat.
Proof. simpl. rewrite decide_True; done. Qed.

Lemma list_count_hd_neq `{Countable T} (xs : list T) x y :
  x ≠ y → list_count x (y :: xs) = list_count x xs%nat.
Proof. intros => /=. by rewrite decide_False. Qed.

Lemma list_count_app `{Countable T} (xs ys : list T) x :
  list_count x (xs ++ ys) = (list_count x xs + list_count x ys)%nat.
Proof. induction xs => /=; [done|]. rewrite IHxs. lia. Qed.

Lemma list_count_elem_of `{Countable T} (xs : list T) x :
  x ∈ xs ↔ (list_count x xs > 0)%nat.
Proof.
  induction xs => /=.
  - split; lia || set_solver.
  - split.
    + intros [-> | ?]%elem_of_cons.
      * rewrite decide_True; [|done]. lia.
      * rewrite IHxs in H0. lia.
    + case_decide => ?; subst; [left|].
      right. apply IHxs. lia.
Qed.

Lemma list_count_filter_alt `{Countable T} `{!∀ a, Decision (P a)} (xs : list T) z :
  (list_count z (filter P xs) = if bool_decide (P z) then list_count z xs else 0)%nat.
Proof.
  induction xs => /=; [by case_bool_decide|].
  case_decide; case_bool_decide; subst. 
  - rewrite filter_cons_True, list_count_hd; [|done]. lia.
  - rewrite filter_cons_False; done.
  - destruct (decide (P a)).
    { rewrite filter_cons_True; [|done]. rewrite list_count_hd_neq; done.  }
    by rewrite filter_cons_False. 
  - destruct (decide (P a)).
    { by rewrite filter_cons_True, list_count_hd_neq. }
    by rewrite filter_cons_False.
Qed.

Lemma list_count_le_length `{Countable A} (xs : list A) (x : A) :
  list_count x xs ≤ length xs.
Proof. induction xs => /=; [done|]. case_decide; lia. Qed. 

#[global] Instance list_count_proper `{Countable T} (x : T) :
  Proper ((≡ₚ) ==> (=)) (list_count x).
Proof.
  intros xs xs' Hxs.
  induction xs in xs', Hxs |-*.
  { rewrite Permutation_nil_l in Hxs. rewrite <-Hxs. done. }
  apply Permutation_cons_inv_l in Hxs as (? & ? & -> & Hxs).
  rewrite list_count_app. simpl.
  rewrite (IHxs _ Hxs), list_count_app. lia.
Qed.

Lemma list_count_filter_split `{Countable A} P `{!∀ a, Decision (P a)} (xs : list A) (x : A) :
  (list_count x (filter P xs) = list_count x xs - list_count x (filter (λ a, ¬ P a) xs))%nat.
Proof.  
  rewrite <-(filter_app_complement P xs) at 2.
  rewrite list_count_app. lia.
Qed.

Lemma remove_dups_list_remove `{Countable T} x (xs : list T) :
  x ∈ remove_dups xs → x ∉ list_delete x (remove_dups xs).
Proof.
  induction xs => /=; [set_solver|].
  case_decide; [done|].
  intros [-> | ?]%elem_of_cons => /=.
  - rewrite decide_True; [|done]. intros ?. apply H0.
    rewrite <-elem_of_remove_dups. done.
  - case_decide.
    + subst. rewrite elem_of_remove_dups. done.
    + apply not_elem_of_cons. split; [done|]. by apply IHxs.
Qed.

Lemma filter_remove_dups `{Countable A} `{!∀ a, Decision (P a)} (zs : list A) :
  remove_dups (filter P zs) = filter P (remove_dups zs).
Proof.
  induction zs as [|x xs IH]; [done|].
  destruct (decide (P x)).
  - rewrite filter_cons_True; [|done]. 
    destruct (decide (x ∈ xs)) as [Hx | Hx].
    + simpl; case_decide as Hd.
      * by case_decide.
      * exfalso; apply Hd. by apply elem_of_list_filter.       
    + simpl; case_decide.
      * exfalso; apply Hx. by eapply elem_of_list_filter.
      * case_decide; [done|].
        by rewrite filter_cons_True, IH. 
  - rewrite filter_cons_False; [|done]. 
    destruct (decide (x ∈ xs)); simpl. 
    + by case_decide. 
    + case_decide; [done|]. by rewrite filter_cons_False.
Qed.

Lemma remove_dups_permute_swap `{Countable T} y x (l : list T) :
  remove_dups (x :: y :: l) ≡ₚ remove_dups (y :: x :: l).
Proof.
  apply NoDup_Permutation; [apply NoDup_remove_dups|apply NoDup_remove_dups|].
  intros ?. rewrite !elem_of_remove_dups.
  split; intros; set_solver.
Qed.

Lemma remove_dups_permute_cons `{Countable T} x (l l' : list T) :
  remove_dups l ≡ₚ remove_dups l' → remove_dups (x :: l) ≡ₚ remove_dups (x :: l').
Proof.
  intros Hl => /=.
  case_decide.
  - assert (x ∈ l').
    { rewrite <-elem_of_remove_dups, <-Hl, elem_of_remove_dups. done. }
    by case_decide.
  - assert (x ∉ l').
    { rewrite <-elem_of_remove_dups, <-Hl, elem_of_remove_dups. done. }
    case_decide; [done|].
    by f_equiv.
Qed.

Lemma remove_dups_fmap_permutation `{Countable T} (zs : list T) (f : T → T) :
  remove_dups (f <$> zs) ≡ₚ remove_dups (f <$> remove_dups zs).
Proof.
  apply NoDup_Permutation; [apply NoDup_remove_dups|apply NoDup_remove_dups|].
  intros ?. split.
  - rewrite elem_of_remove_dups, elem_of_list_fmap.
    intros (y & -> & Hy).
    rewrite elem_of_remove_dups, elem_of_list_fmap.
    eexists. split; [done|].
    by apply elem_of_remove_dups.
  - rewrite elem_of_remove_dups, elem_of_list_fmap.
    intros (y & -> & Hy).
    rewrite elem_of_remove_dups, elem_of_list_fmap.
    eexists. split; [done|].
    by apply elem_of_remove_dups.
Qed.

Lemma remove_dups_Permutation `{Countable T} (xs ys : list T) :
  Permutation xs ys → remove_dups xs ≡ₚ remove_dups ys.
Proof.
  revert xs ys.
  apply Permutation_ind_bis; intros.
  - done.
  - by apply remove_dups_permute_cons.
  - rewrite remove_dups_permute_swap. by do 2 apply remove_dups_permute_cons.
  - by etrans.
Qed.

#[global] Instance remove_dups_proper `{Countable A} :
  Proper ((≡ₚ) ==> (≡ₚ)) (remove_dups (A := A)).
Proof. intros ???. by apply remove_dups_Permutation. Qed.


(** * sum_list *)

Section list.
#[local] Open Scope Z.

Definition sum_list (X : list Z) : Z := foldr Z.add 0 X.
Definition sum_list_with `{Countable T} (f : T → Z) (X : list T) : Z := sum_list (f <$> X).

Lemma sum_list_with_add `{Countable T} (f f' : T → Z) (zs : list T) :
  sum_list_with (λ z, f z + f' z) zs = sum_list_with f zs + sum_list_with f' zs.
Proof.
  unfold sum_list_with, sum_list.
  induction zs; [done|].
  rewrite !fmap_cons. simpl. rewrite IHzs. lia.
Qed.

Lemma sum_list_with_sub `{Countable T} (f f' : T → Z) (zs : list T) :
  sum_list_with (λ z, f z - f' z) zs = sum_list_with f zs - sum_list_with f' zs.
Proof.
  unfold sum_list_with, sum_list.
  induction zs; [done|].
  rewrite !fmap_cons. simpl. rewrite IHzs. lia.
Qed.

Lemma sum_list_with_cons `{Countable T} (xs : list T) x (f : T → Z) :
  sum_list_with f (x :: xs) = f x + sum_list_with f xs.
Proof. done. Qed.

Lemma sum_list_with_nil `{Countable T} (xs : list T) (f : T → Z) :
  sum_list_with f [] = 0.
Proof. done. Qed.

Lemma sum_list_with_app `{Countable T} (xs ys : list T) (f : T → Z) :
  sum_list_with f (xs ++ ys) = sum_list_with f xs + sum_list_with f ys.
Proof.
  unfold sum_list_with, sum_list.
  rewrite Z.add_comm.
  rewrite fmap_app. rewrite foldr_app.
  rewrite <-foldr_comm_acc, ?Z.add_0_r.
  { done. }
  intros ??. lia.
Qed.

Lemma sum_list_with_ext `{Countable T} (zs : list T) f1 f2 :
  (∀ z, z ∈ zs → f1 z = f2 z) →
  sum_list_with f1 zs = sum_list_with f2 zs.
Proof.
  unfold sum_list_with, sum_list.
  induction zs => Hb; [simpl; lia|].
  rewrite 2!fmap_cons. simpl.
  rewrite Hb; [|left].
  rewrite IHzs. done.
  intros ??. apply Hb. by right.
Qed.

Lemma sum_list_with_0 `{Countable T} (xs : list T) :
  sum_list_with (λ _ : T, 0) xs = 0.
Proof. induction xs => /=; [done|]. rewrite sum_list_with_cons, IHxs. done. Qed.

Lemma sum_list_with_le `{Countable T} (zs : list T) f1 f2 :
  (∀ z, z ∈ zs → f1 z ≤ f2 z) →
  sum_list_with f1 zs ≤ sum_list_with f2 zs.
Proof.
  unfold sum_list_with, sum_list.
  induction zs => Hb; [simpl; lia|].
  rewrite 2!fmap_cons. simpl.
  apply Z.add_le_mono.
  { apply Hb. by left. }
  apply IHzs.
  intros ??. apply Hb. by right.
Qed.

Lemma sum_list_with_le_constant b (zs : list Z) f :
  (∀ z, z ∈ zs → 0 ≤ f z) →
  (∀ z, z ∈ zs → z ≤ b) →
  sum_list_with (λ z, z * f z) zs ≤ sum_list_with (λ z, b * f z) zs.
Proof.
  intros Hf Hb.
  apply sum_list_with_le.
  intros ??.
  specialize (Hf _ H).
  specialize (Hb _ H).
  by apply Z.mul_le_mono_nonneg_r.
Qed.

Lemma sum_list_with_pos `{Countable T} (ts : list T) (f : T → Z) :
  (∀ t, t ∈ ts → 0 ≤ f t) → 0 ≤ sum_list_with f ts.
Proof.
  intros ?.
  rewrite <-(sum_list_with_0 ts).
  by apply sum_list_with_le.
Qed.

Lemma sum_list_with_mul b (zs : list Z) f :
  sum_list_with (λ z, b * f z) zs = b * sum_list_with f zs.
Proof.
  unfold sum_list_with, sum_list.
  induction zs; [simpl; lia|].
  rewrite 2!fmap_cons. simpl.
  lia.
Qed.

Lemma sum_list_with_elem_of `{Countable T} (x : T) (xs : list T) (f : T → Z)  :
  x ∈ xs →
  sum_list_with f xs = f x + sum_list_with f (list_delete x xs).
Proof.
  intros (xs1 & ys & ->)%elem_of_list_split.
  induction xs1 => /=.
  - rewrite decide_True; done.
  - rewrite sum_list_with_cons.
    case_decide; subst; [done|].
    rewrite sum_list_with_cons.
    rewrite IHxs1. lia.
Qed.

Lemma sum_list_with_weaken f (xs ys zs us : list Z) :
  ys ## us →
  zs ## us →
  sum_list_with (λ z : Z, f z * Z.of_nat (list_count z (ys ++ xs ++ zs))) us =
  sum_list_with (λ z : Z, f z * Z.of_nat (list_count z xs)) us.
Proof.
  intros ??.
  apply sum_list_with_ext => z Hz.
  rewrite !list_count_app.
  rewrite list_count_not_elem_of; [|set_solver].
  rewrite (list_count_not_elem_of zs); [|set_solver].
  lia.
Qed.

Lemma sum_list_with_multiplicity (xs ys : list Z) f :
  sum_list_with f xs = sum_list_with (λ z, f z * Z.of_nat (list_count z xs)) (remove_dups (xs ++ ys)).
Proof.
  simpl.
  induction xs as [|x xs IH].
  { unfold sum_list_with, sum_list.
    induction ys as [|?? IH]=> /=; [done|].
    case_decide; [done|].
    rewrite fmap_cons, foldr_cons.
    simpl in IH.
    rewrite <-IH. lia. }
  simpl (sum_list _). simpl (remove_dups _).
  case_decide as Hel.
  - rewrite <-elem_of_remove_dups in Hel.
    rewrite (sum_list_with_elem_of x _ _ Hel).
    rewrite list_count_hd.
    rewrite Nat2Z.inj_add.
    rewrite Z.mul_add_distr_l, Z.mul_1_r.
    rewrite sum_list_with_cons.
    rewrite IH.
    rewrite (sum_list_with_elem_of x _ _ Hel).
    apply remove_dups_list_remove in Hel.
    rewrite <-(sum_list_with_weaken _ _ [x] []); [|set_solver|set_solver].
    rewrite Z.add_assoc. f_equal.
    apply sum_list_with_ext.
    intros ??. rewrite !list_count_app. simpl.
    lia.
  - rewrite !sum_list_with_cons.
    rewrite list_count_hd.
    rewrite Nat2Z.inj_add, Z.mul_add_distr_l. simpl. rewrite Z.mul_1_r.
    destruct (Nat.eq_0_gt_0_cases (list_count x xs)) as [->| He]; last first.
    { apply list_count_elem_of in He. set_solver. }
    rewrite Z.mul_0_r, Z.add_0_r.
    rewrite IH.
    f_equal.
    apply sum_list_with_ext.
    intros ?. rewrite elem_of_remove_dups => ?.
    case_decide; subst; [done|].
    lia.
Qed.

Lemma sum_list_multiplicity' (xs ys : list Z) :
  sum_list xs = sum_list_with (λ z, z * Z.of_nat (list_count z xs)) (remove_dups (xs ++ ys)).
Proof.
  pose proof (sum_list_with_multiplicity xs ys id). simpl in H. rewrite <-H.
  unfold sum_list_with. rewrite list_fmap_id. done.
Qed.

Lemma sum_list_multiplicity (xs : list Z) :
  sum_list xs = sum_list_with (λ z, z * Z.of_nat (list_count z xs)) (remove_dups xs).
Proof. rewrite (sum_list_multiplicity' xs []), app_nil_r. done. Qed.

Lemma sum_list_with_compose (zs : list Z) (f g : Z → Z) :
  sum_list_with (g ∘ f) zs = sum_list_with g (f <$> zs).
Proof. induction zs; [done|]. rewrite fmap_cons, !sum_list_with_cons, IHzs. done. Qed.

Lemma sum_list_with_split `{Countable T} (P : T → Prop) `{!∀ a, Decision (P a)} (zs : list T) (f : T → Z) :
  sum_list_with f zs = sum_list_with f (filter P zs) + sum_list_with f (filter (λ z, ¬ P z) zs).
Proof.
  induction zs; [done|].
  rewrite !filter_cons, !sum_list_with_cons.
  case_decide.
  - case_decide; [done|]. rewrite sum_list_with_cons, IHzs. lia.
  - rewrite decide_True; [|done]. rewrite sum_list_with_cons, IHzs. lia.
Qed.

Lemma elem_of_list_remove `{Countable T} x y (xs : list T) :
  x ∈ list_delete y (remove_dups xs) → x ≠ y.
Proof.
  induction xs in x, y |-* => /=; [set_solver|].
  case_decide => /=.
  - intros ?. by apply IHxs.
  - case_decide; subst.
    + intros ?. intros ->. by rewrite elem_of_remove_dups in H1.
    + intros [-> | ?]%elem_of_cons; [done|].
      by apply IHxs.
Qed.

Lemma list_remove_remove_dups `{Countable T} z (zs : list T) :
  list_delete z (remove_dups (z :: zs)) =
    if decide (z ∈ zs) then list_delete z (remove_dups zs) else remove_dups zs.
Proof.
  induction zs as [|x xs IH] => /=.
  { rewrite decide_True; done. }
  destruct (decide (z = x)) as [<- |].
  - rewrite decide_True; [|by left].
    (* TODO fix *)
    (* why does [rewrite decide_True] not work?! *)
    destruct (decide_rel elem_of z (z :: xs)); [|set_solver].
    by case_decide.
  - case_decide.
    + rewrite decide_True; [|set_solver].
      (* why does [rewrite decide_True] not work?! *)
      destruct (decide_rel elem_of z (z :: xs)); [|set_solver].
      destruct (decide_rel elem_of z (x :: xs)); [|set_solver].
      done.
    + rewrite decide_False; [|set_solver].
      destruct (decide_rel elem_of z (x :: xs)); [set_solver|].
      case_decide; simpl; rewrite decide_True; done.
Qed.

Lemma sum_list_with_Permutation `{Countable T} (f : T → Z) (xs ys : list T) :
  Permutation xs ys → sum_list_with f xs = sum_list_with f ys.
Proof.
  revert xs ys.
  apply Permutation_ind_bis; intros.
  - done.
  - rewrite !sum_list_with_cons. f_equal. auto.
  - rewrite !sum_list_with_cons, !Z.add_assoc, (Z.add_comm (f _)). f_equal. auto.
  - etrans; [apply H1|]. done.
Qed.

#[global] Instance sum_list_with_proper `{Countable T} (f : T → Z) :
  Proper ((≡ₚ) ==> (=)) (sum_list_with f).
Proof. intros ???. by apply sum_list_with_Permutation. Qed.

Lemma sum_difference_multiplicity (xs ys : list Z) :
  (∀ z, z ∈ xs ++ ys → 0 ≤ z) →
  sum_list xs - sum_list ys ≤
  sum_list_with (λ z, z * 0 `max` (Z.of_nat (list_count z xs) - Z.of_nat (list_count z ys))) (remove_dups (xs ++ ys)).
Proof.
  intros Hz.
  rewrite (sum_list_multiplicity' _ ys), (sum_list_multiplicity' _ xs).
  erewrite (sum_list_with_Permutation _ (remove_dups (ys ++ _))); last first.
  { apply remove_dups_Permutation, app_Permutation_comm. }
  rewrite <-sum_list_with_sub.
  eapply sum_list_with_le => z.
  rewrite elem_of_remove_dups => Hin.
  rewrite <-(Z.mul_sub_distr_l z).
  apply Z.mul_le_mono_nonneg_l; [by apply Hz|].
  lia.
Qed.

Lemma sum_difference_multiplicity' (b : Z) (xs ys : list Z) :
  (∀ z : Z, z ∈ xs ++ ys → 0 ≤ z ≤ b) →
  sum_list xs - sum_list ys ≤
  b * sum_list_with (λ z, 0 `max` (Z.of_nat (list_count z xs) - Z.of_nat (list_count z ys))) (remove_dups (xs ++ ys)).
Proof.
  intros Hb.
  etrans; [apply sum_difference_multiplicity|].
  { intros. by apply Hb. }
  etrans; [apply (sum_list_with_le_constant b)|].
  { lia. }
  { intros ? ?%(elem_of_remove_dups (_ ++ _)). by apply Hb. }
  rewrite sum_list_with_mul. done.
Qed.

Definition list_preimage `{!EqDecision A} (f : A → A) (zs : list A) (x : A) :=
  filter (λ z, x = f z) zs.

Lemma list_preimage_nil `{EqDecision T} (g : T → T) xs x :
  g x ∉ g <$> xs → list_preimage g xs (g x) = [].
Proof.
  unfold list_preimage => ?.
  induction xs; [done|].
  rewrite filter_cons_False; [|set_solver].
  rewrite IHxs; [done|]. set_solver.
Qed.

Lemma sum_list_map_list_preimage (g f : Z → Z) (zs : list Z) :
  sum_list_with f zs =
  sum_list_with (λ y : Z, sum_list_with f (list_preimage g zs y)) (remove_dups (g <$> zs)).
Proof.
  induction zs as [|x xs IH]; [done|].

  (* pull out the sum of [x] *)
  rewrite (sum_list_with_elem_of x); last first.
  { left. }
  simpl (list_delete _ _).
  rewrite decide_True; [|done].

  (* pull out the sum for the list_preimage of [g x] *)
  rewrite (sum_list_with_elem_of (g x) (remove_dups (g <$> _))) ;last first.
  { apply elem_of_remove_dups. set_solver. }

  (* split sum of list_preimage of [g x] into the part about [x] and sum of the rest *)
  rewrite (sum_list_with_split (λ z, z = x) (list_preimage _ _ _)).
  unfold list_preimage at 1.
  rewrite list_filter_filter.
  rewrite filter_cons_True; [|done].
  rewrite sum_list_with_cons.

  (* [z] is accounted for on both sides *)
  rewrite <-!Z.add_assoc. f_equal. rewrite !Z.add_assoc.

  (* putting the leftovers back together *)
  unfold list_preimage.
  rewrite list_filter_filter.
  rewrite filter_cons_False; [|by intros []].
  rewrite <-!list_filter_filter.
  rewrite <-(sum_list_with_split (λ z, z = x)).
  fold (list_preimage g xs (g x)).

  (* [x] does not contribute to the image sum anymore *)
  erewrite (sum_list_with_ext (list_delete _ _)); last first.
  { intros ? ?%elem_of_list_remove. rewrite filter_cons_False; done. }

  (* either we have duplicates of [g x] or not *)
  rewrite fmap_cons, list_remove_remove_dups.
  case_decide.
  - rewrite IH.
    erewrite sum_list_with_elem_of; [done|].
    by apply elem_of_remove_dups.
  - rewrite IH, list_preimage_nil; done.
Qed.

(** Triangle equality  *)
Lemma Z_abs_sum_le `{Countable T} (l : list T) (f : T → Z) :
  Z.abs (sum_list_with f l) <= sum_list_with (λ x, Z.abs (f x)) l.
Proof.
  induction l; [done|].
  rewrite !sum_list_with_cons.
  etrans; [apply Z.abs_triangle|].
  lia.
Qed.

Lemma elem_of_list_remove_filter `{Countable T} x y (xs : list T) `{!∀ a, Decision (P a)} :
  x ∈ list_delete y (filter P (remove_dups xs)) → x ≠ y.
Proof.
  induction xs in x, y |-* => /=; [set_solver|].
  case_decide => /=.
  - intros ?. by apply IHxs.
  - rewrite filter_cons.
    case_decide; subst; [|auto].
    simpl.
    case_decide; subst.
    + rewrite elem_of_list_filter.
      intros [? Hin] ->. rewrite elem_of_remove_dups in Hin. done.
    + intros [-> | ?]%elem_of_cons; [done|]. by apply IHxs.
Qed.

Lemma list_count_sum_list_preimage `{Countable A} (zs1 zs2 : list A) (f : A → A) z :
  Z.of_nat (list_count z (f <$> zs1)) =
    sum_list_with (λ z, Z.of_nat (list_count z zs1)) (list_preimage f (remove_dups (zs1 ++ zs2)) z).
Proof.
  unfold list_preimage.
  induction zs1 as [|x xs IH].
  { rewrite sum_list_with_0. done. }
  rewrite fmap_cons. simpl.
  case_decide.
  - case_decide.
    + rewrite (sum_list_with_elem_of x); last first.
      { apply elem_of_list_filter. split; [done|]. by apply elem_of_remove_dups. }
      rewrite decide_True; [|done].
      rewrite !Nat2Z.inj_add, <-Z.add_assoc.
      erewrite (sum_list_with_ext _ _ (λ z, Z.of_nat (list_count z xs))); last first.
      { intros ??.
        rewrite decide_False; [done|].
        by eapply elem_of_list_remove_filter. }
      rewrite IH.
      erewrite sum_list_with_elem_of; [done|].
      apply elem_of_list_filter. split; [done|].
      by apply elem_of_remove_dups.
    + rewrite filter_cons_True; [|done].
      rewrite sum_list_with_cons.
      rewrite decide_True; [|done].
      rewrite !Nat2Z.inj_add, <-Z.add_assoc.
      erewrite (sum_list_with_ext _ _ (λ z, Z.of_nat (list_count z xs))); last first.
      { intros ? [-> Hin]%elem_of_list_filter.
        rewrite decide_False; [done|].
        intros ->. rewrite elem_of_remove_dups in Hin. done. }
      rewrite (list_count_not_elem_of xs); [|set_solver].
      lia.
  - case_decide.
    + erewrite (sum_list_with_ext _ _ (λ z, Z.of_nat (list_count z xs))); last first.
      { intros ? [-> Hin]%elem_of_list_filter.
        rewrite decide_False; [done|].
        intros ->. rewrite elem_of_remove_dups in Hin. done. }
      lia.
    + rewrite filter_cons_False; [|done].
      erewrite (sum_list_with_ext _ _ (λ z, Z.of_nat (list_count z xs))); last first.
      { intros ? [-> Hin]%elem_of_list_filter.
        rewrite decide_False; [done|].
        intros ->. rewrite elem_of_remove_dups in Hin. done. }
      lia.
Qed.


End list.

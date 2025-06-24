From clutch Require Import eris.
From mathcomp Require Import fintype ssreflect.ssrAC.

Arguments le_S_n {_} {_} _.
Arguments Nat.le_trans {_} {_} {_} _ _.

Definition nat_tricho (n m : nat) : {n < m} + {n = m} + {n > m} := 
  match (gt_dec n m) with 
  | left pf => inright pf
  | right pf => inleft $ le_lt_eq_dec _ _ $ not_gt _ _ pf
  end.

Lemma nat_tricho_lt {n m : nat} (hlt : n < m) : nat_tricho n m = inleft (left hlt).
Proof.
  unfold nat_tricho.
  destruct (gt_dec n m) as [? | h_le]; first lia.
  destruct (le_lt_eq_dec n m (not_gt n m h_le)) as [hlt' | ?]; last lia.
  do 2 f_equal.
  apply ssrnat.lt_irrelevance.
Qed.

Lemma nat_tricho_eq {n m : nat} (heq : n = m) : nat_tricho n m = inleft (right heq).
Proof.
  unfold nat_tricho.
  subst m.
  destruct (gt_dec n n) as [? | h_le]; first lia.
  destruct (le_lt_eq_dec n n (not_gt n n h_le)) as [? | ?]; first lia.
  do 2 f_equal.
  apply Eqdep_dec.UIP_refl_nat.
Qed.

Lemma nat_tricho_gt {n m : nat} (hgt : n > m) : nat_tricho n m = inright hgt.
Proof.
  unfold nat_tricho.
  destruct (gt_dec n m) as [h_gt | ?]; last lia.
  f_equal.
  apply ssrnat.lt_irrelevance.
Qed.

Lemma not_0_gt {n : nat} : ¬ n < 0.
Proof Nat.nle_succ_0 n.

Lemma not_0_gt_eq {a b : nat} (a_eq_0 : a = 0) : ¬ b < a.
Proof let 'eq_refl := eq_sym a_eq_0 in not_0_gt.

Lemma leb_to_leq {a b : nat} : is_true (ssrnat.leq a b) -> a ≤ b.
Proof iffLR (Rcomplements.SSR_leq _ _).

Lemma leq_to_leb {a b : nat} : a ≤ b -> is_true (ssrnat.leq a b).
Proof iffRL (Rcomplements.SSR_leq _ _).

Definition mkOrdinal {a b : nat} (a_lt_b : a < b) : 'I_b := Ordinal (leq_to_leb a_lt_b).

Lemma option_map_some {A B : Type} (f : A -> B) (a : A) : Some (f a) = option_map f (Some a).
Proof eq_refl.


Definition upcast_ord {n} (ord : 'I_n) : 'I_(S n) :=
  let 'Ordinal v pf := ord in 
  Ordinal (m := v) (ssrnat.leqW pf).


Definition downcast_ord {n} (ord : 'I_(S n)) (ord_pos : 0 < ord): 'I_n :=
    match nat_of_ord ord as n0 return (nat_of_ord ord = n0) -> 'I_n with 
    | 0 => fun heq => False_rect _ $ not_0_gt_eq heq ord_pos
    | S v => fun heq => 
        Ordinal (m := v) (
          eq_ind 
            _ 
            (fun v => is_true (ssrnat.leq v n))
            (leq_ord ord) 
            _
            heq
          )
    end eq_refl.
Definition ord_succ {n} (ord : 'I_n) : 'I_(S n) :=
  let 'Ordinal v pf := ord in 
  Ordinal (leq_to_leb $ le_n_S _ _ (leb_to_leq pf)).
  
Lemma nat_of_ord_inj {n} {o1 o2 : 'I_n} (Heq : nat_of_ord o1 = nat_of_ord o2) : o1 = o2.
Proof.
  destruct o1, o2.
  simpl in Heq.
  destruct Heq.
  f_equal.
  apply proof_irrelevance.
Qed.

Definition transport {A B : Type} (Heq: A = B) : A -> B := λ a, let 'eq_refl := Heq in a.

Notation "Heq ▸ t" := (transport Heq t) (at level 65, right associativity).
Notation "Heq ▸ₛ t" := (transport (eq_sym Heq) t) (at level 65, right associativity).

Lemma UIP {A : Type} (e : A = A) : e = eq_refl.
Proof proof_irrelevance _ e eq_refl.

Lemma transport_refl {A : Type} (Heq : A = A) (a : A) : Heq ▸ a = a.
Proof.
  rewrite (UIP Heq) //.
Qed.

Lemma transport_sym_left {A B : Type} (Heq : A = B) (a : A) : Heq ▸ₛ Heq ▸ a = a.
Proof.
  by destruct Heq.
Qed.

Lemma transport_sym_right {A B : Type} (Heq : B = A) (a : A) : Heq ▸ Heq ▸ₛ a = a.
Proof.
  by destruct Heq.
Qed.

Lemma transport_inj {A B} {Heq: A = B} {a b : A} (cast_eq : Heq ▸ a = Heq ▸ b) : a = b.
Proof.
  destruct Heq.
  apply cast_eq.
Qed.

Lemma nat_of_ord_transport_map 
  {A B C : Type} (f : A -> B) (l : list A)
  (Heq1 : C = 'I_(length (map f l)))
  (Heq2 : C = 'I_(length l))
  (i : C) :
  nat_of_ord (Heq1 ▸ i) = nat_of_ord (Heq2 ▸ i).
Proof.
  destruct (map_length f l), (eq_sym Heq2).
  rewrite !transport_refl //.
Qed.


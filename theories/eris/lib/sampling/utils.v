From clutch.eris Require Import eris.

Local Open Scope R.
Local Ltac done ::= lia || lra || nra || real_solver || tactics.done || auto.
Ltac add_hint t := let n := fresh "hint" in have n := t.

Lemma INR_sub M N : (M >= N)%nat -> INR M - INR N = INR (M - N).
Proof.
  elim: M N.
  - case=> //.
  - move=> M IH [|N] Hge.
    + rewrite Nat.sub_0_r Rminus_0_r //.
    + rewrite -IH // !S_INR Rminus_plus_r_r //.
Qed.

Lemma INR_S_not_0 (n : nat) : 
  INR (S n) ≠ 0.
Proof.
  Set Printing Coercions.
  intros Heq.
  assert (S n ≠ 0)%nat as Heq' by lia.
  by apply Heq', INR_eq.
  Unset Printing Coercions. 
Qed.


Ltac simplra := simpl; lra.
Ltac find_contra :=
  solve
  [ contradiction
  | match goal with 
    | H : ¬ _ |- _ => exfalso; apply H; by eauto
    end ].
Ltac full_inv_fin :=
  repeat match goal with 
  | |- ∀ _, _ => intro
  | i : fin _ |- _   => inv_fin i
  end;
  try (reflexivity || find_contra).
Ltac extract_val_eq :=
  repeat match goal with 
  | H : #?n = #?m |- _ => injection H as H
  | H : Z.of_nat _ = Z.of_nat _ |- _ => apply Nat2Z.inj in H
  end.

Ltac simpl_expr :=
  repeat (
      match goal with 
      | |- context[(?v * (_ * /?v))] => 
            rewrite !Rmult_div_assoc Rmult_div_r

      | |- ?n * _ < ?n * _ => apply Rmult_lt_compat_l
      | |- ?n * _ <= ?n * _ => apply Rmult_le_compat_l
      | |- ?n * _ = ?n * _ => apply Rmult_eq_compat_l
      
      | |- _ < _ */?n => apply (Rmult_lt_reg_l n)
      | |- _ <= _ */?n => apply (Rmult_le_reg_l n)
      | |- _ = _ */?n => apply (Rmult_eq_reg_l n)

      | |- _ * /?n < _  => apply (Rmult_lt_reg_l n)
      | |- _ * /?n <= _  => apply (Rmult_le_reg_l n)
      | |- _ * /?n = _  => apply (Rmult_eq_reg_l n)
      end ||
      rewrite Rplus_0_l || rewrite Rplus_0_r ||
      rewrite Rmult_1_l || rewrite Rmult_1_r ||
      rewrite Rmult_0_l || rewrite Rmult_0_r ||
      rewrite Rdiv_1_l  || rewrite Rdiv_1_r ||
      rewrite Rdiv_def ||
      lra ||
      auto||
      solve[apply cond_nonneg] ||
      solve[apply pos_INR_S] ||
      solve[apply pos_INR] ||
      solve[apply le_INR; lia] ||
      solve[apply lt_INR; lia] ||
      solve[apply INR_S_not_0]
    ).


Lemma Rmult_le_1_le_r (r1 r2 : R) :
  0 <= r1 <= 1 -> 
  0 <= r2 ->
  0 <= r1 * r2 <= r2.
Proof.
  real_solver.
Qed.

Lemma Rmult_le_1_le_l (r1 r2 : R) :
  0 <= r1 <= 1 -> 
  0 <= r2 ->
  0 <= r2 * r1 <= r2.
Proof.
  real_solver.
Qed.


Lemma Rmult_le_1 (r1 r2 : R) :
  0 <= r1 <= 1 -> 
  0 <= r2 <= 1 ->
  0 <= r1 * r2 <= 1.
Proof.
  real_solver.
Qed.

Lemma Rpow_le_1 (r : R) (k : nat) :
  0 <= r <= 1 -> 
  0 <= r ^ k <= 1.
Proof.
  elim: k => // => n IH //=.
Qed.


Lemma ec_contradict_lt0 `{!erisGS Σ} (ε : R) : (ε < 0)%R -> ↯ ε ⊢ False.
Proof.
  iIntros "%ε_nonpos Herr".
  iPoseProof (ec_valid with "Herr") as "[%Hε _]" => //.
Qed.


Lemma foldr_plus_app (l1 l2 : list R) (acc : R) :
  foldr Rplus acc (l1 ++ l2) = foldr Rplus 0 l1 + foldr Rplus acc l2.
Proof.
  elim: l1 =>> //=.
Qed.


Lemma fmap_prop {A B : Type} (l : list A) (f : A -> B) (P1 : A -> Prop) (P2 : B -> Prop) :
  (∀ a, P1 a -> P2 (f a)) ->
  (∀ a, a ∈ l -> P1 a) ->
  ∀ b, b ∈ (f <$> l) -> P2 b.
Proof.
  move=> HPs.
  elim: l.
  - move=> _ b /= HinNil.
    by apply not_elem_of_nil in HinNil.
  - move=> a l IH Hforall /= b Hin.
    rewrite elem_of_cons in Hin.
    case: Hin.
    + move=> ->.
      apply HPs, Hforall, elem_of_list_here.
    + move=> Hin.
      apply IH => //.
      move=> a' Ha'.
      by apply Hforall, elem_of_list_further.
Qed.

Lemma forall_list_eq {A : Type} (l : list A) (a : A) :
  (∀ e, e ∈ l -> e = a) ->
  l = repeat a (length l).
Proof.
  add_hint @elem_of_list_here.
  add_hint @elem_of_list_further.
  elim: l => //=.
  move=> e l IH Hl.
  rewrite (Hl e) // -IH //.
Qed.

Lemma map_seq_if_lt {A : Type} (e1 e2 : A) (N : nat):
  (λ x, if bool_decide (x < N)%nat then e1 else e2) <$> seq 0 N = repeat e1 N.
Proof.
  set f := (λ x : nat, if bool_decide (x < N)%nat then e1 else e2).
  assert (Heq: ∀ e, e ∈ f <$> seq 0 N -> e = e1). {
    apply (fmap_prop _ f (λ n, n < N)%nat).
    - move=> a Ha /=.
      rewrite /f bool_decide_eq_true_2 //.
    - move=> a Ha.
      by apply elem_of_seq in Ha as [_ Ha].
  }
  replace N with (length (f <$> seq 0 N)) at 2 by rewrite fmap_length seq_length //.
  exact: forall_list_eq Heq.
Qed.

Lemma map_seq_if_ge {A : Type} (e1 e2 : A) (N L : nat):
  (λ x, if bool_decide (x < N)%nat then e1 else e2) <$> seq N L = repeat e2 L.
Proof.
  set f := (λ x : nat, if bool_decide (x < N)%nat then e1 else e2).
  assert (Heq: ∀ e, e ∈ f <$> seq N L -> e = e2). {
    apply (fmap_prop _ f (λ n, n >= N)%nat) => a Ha.
    - rewrite /f bool_decide_eq_false_2 //.
    - by apply elem_of_seq in Ha as [].
  }
  replace L with (length (f <$> seq N L)) at 2 by rewrite fmap_length seq_length //.
  exact: forall_list_eq Heq.
Qed.


Lemma foldr_plus_repeat (ε : R) (L : nat) :
  foldr Rplus 0 (repeat ε L) = ε * L.
Proof.
  elim: L =>> //.
  rewrite S_INR //=.
Qed.

Lemma SeriesC_case (N M : nat) (ε1 ε2 : R) :
  (N <= S M)%nat ->
  SeriesC (
    λ x : fin (S M), 
    if bool_decide (fin_to_nat x < N)%nat
    then ε2
    else ε1
  ) = (ε1 * (S M - N) + ε2 * N)%R.
Proof.
  move=> HNleM.
  rewrite SeriesC_finite_foldr -foldr_fmap.
  transitivity (
    foldr Rplus 0
    ((λ x : nat, if bool_decide (x < N)%nat then ε2 else ε1) ∘ fin_to_nat <$> enum (fin (S M)))
  ).
  { reflexivity. }
  rewrite list_fmap_compose fin.enum_fin_seq.
  assert (seq 0 (S M) = seq 0 N ++ seq N (S M - N)) as ->. 
  { replace (S M)%nat with (N + (S M - N))%nat at 1 by lia.
    apply seq_app. }
  rewrite fmap_app foldr_plus_app Rplus_comm.
  rewrite map_seq_if_ge map_seq_if_lt.
  rewrite !foldr_plus_repeat INR_sub //.
Qed.
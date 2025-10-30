From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt RInt_analysis AutoDerive.
From clutch.eris Require Import infinite_tape.
From clutch.eris.examples Require Import lazy_real max_lazy_real.
Set Default Proof Using "Type*".
#[local] Open Scope R.


Section Indicators.
Import Hierarchy.

Definition Iverson {T : Type} (P : T → Prop) : T → R :=
  fun t => if decide (P t) then 1 else 0.

Notation "⟦ x ⟧" := (Iverson x).

Lemma Iverson_True {T : Type} {P : T → Prop} {t : T} (H : P t) : ⟦ P ⟧ t = 1.
Proof. rewrite /Iverson; case_decide; [done | by intuition]. Qed.

Lemma Iverson_False {T : Type} {P : T → Prop} {t : T} (H : ¬ P t) : ⟦ P ⟧ t = 0.
Proof. rewrite /Iverson; case_decide; [by intuition | done]. Qed.

Lemma Iverson_add_neg {T : Type} {P : T → Prop} {t : T} :
  ⟦ P ⟧ t + ⟦ not ∘ P ⟧ t = 1.
Proof.
  rewrite /Iverson; case_decide; case_decide; try lra.
  all: simpl in H0; intuition.
Qed.

Lemma Iverson_nonneg {T : Type} {P : T → Prop} {t : T} : (0 <= ⟦ P ⟧ t)%R.
Proof. rewrite /Iverson; case_decide; lra. Qed.

Lemma Iverson_le_1 {T : Type} {P : T → Prop} {t : T} : (⟦ P ⟧ t <= 1)%R.
Proof. rewrite /Iverson; case_decide; lra. Qed.

Lemma SeriesC_Iverson_singleton {T} `{Countable T} {F : T → R} {P : T → Prop} (N0 : T)
    (HN0 : ∀ N, P N <-> N = N0) :
    SeriesC (fun n : T => Iverson P n * F n) = F N0.
Proof.
  rewrite -(SeriesC_singleton' N0 (F N0)).
  f_equal; apply functional_extensionality; intros n.
  case_bool_decide.
  { rewrite Iverson_True; [|rewrite HN0; done]. rewrite H0; lra. }
  { rewrite Iverson_False; [|rewrite HN0; done]. lra. }
Qed.

Lemma Iverson_mul_and {T : Type} {P Q : T → Prop} {t : T} :
  ⟦ P ⟧ t * ⟦ Q ⟧ t = ⟦ fun t => P t ∧ Q t ⟧ t.
Proof.
  rewrite /Iverson; case_decide; case_decide; case_decide.
  all: try lra.
  all: intuition.
Qed.


Lemma RInt_Iverson_ge {rx F} (Hrx : 0 <= rx <= 1) :
  RInt (λ x : R, Iverson (uncurry Rge) (x, rx) * F x) 0 1 =  RInt (λ x : R, F x) rx 1.
Proof. Admitted.

Lemma RInt_Iverson_ge' {rx F} (Hrx : 0 <= rx <= 1) :
  RInt (λ x : R, Iverson (fun x  => not (Rle x rx)) x * F x) 0 1 =  RInt (λ x : R, F x) rx 1.
Proof. Admitted.

Lemma RInt_Iverson_le {rx F} (Hrx : 0 <= rx <= 1) :
  RInt (λ x : R, Iverson (uncurry Rle) (x, rx) * F x) 0 1 =  RInt (λ x : R, F x) 0 rx.
Proof. Admitted.

Lemma RInt_Iverson_le'' {rx F} (Hrx : 0 <= rx <= 1) :
  RInt (λ x : R, Iverson (Rle x) rx * F x) 0 1 =  RInt (λ x : R, F x) 0 rx.
Proof. Admitted.

Lemma RInt_Iverson_ge'' {rx F} (Hrx : 0 <= rx <= 1) :
  RInt (λ x : R, Iverson (Rge x) rx * F x) 0 1 =  RInt (λ x : R, F x) rx 1.
Proof. Admitted.

Lemma RInt_Iverson_le''' {x} (Hx : 0 <= x <= 1) : RInt (Iverson (Rle x)) 0 1 = 1 - x.
Proof. Admitted.

Lemma RInt_Iverson_ge''' {x} (Hx : 0 <= x <= 1) : RInt (Iverson (Rge x)) 0 1 = x.
Proof. Admitted.


End Indicators.

Section Lib.
Import Hierarchy.
(* General analysis facts *)
  
Lemma RInt_add {F1 F2 : R → R} {a b : R} (H1 : ex_RInt F1 a b) (H2 : ex_RInt F2 a b) :
  RInt F1 a b  + RInt F2 a b = RInt (fun x => F1 x + F2 x) a b.
Proof. Admitted.

Lemma RInt_Rmult {F : R → R} {a b r : R} : r * RInt F a b = RInt (fun x => r * F x) a b.
Proof. Admitted.

Lemma RInt_Rmult' {F : R → R} {a b r : R} : (RInt F a b) * r = RInt (fun x => F x * r) a b.
Proof. Admitted.

Lemma ex_RInt_Rmult {F : R → R} {a b r : R} : ex_RInt F a b → ex_RInt (fun x => r * F x) a b.
Proof. Admitted.

Lemma ex_RInt_Rmult' {F : R → R} {a b r : R} : ex_RInt F a b → ex_RInt (fun x => F x * r) a b.
Proof. Admitted.

Lemma ex_RInt_pow {a b N} : ex_RInt (λ y : R, y ^ N) a b.
Proof. Admitted.

Lemma Rexp_nn {z} : 0 <= exp z.
Proof. Admitted.

Lemma Rexp_range {z : R} : z <= 0 -> 0 <= exp z <= 1.
Proof. Admitted.

Lemma ex_RInt_add' (f g : R → R) {h : R → R} {a b : R} (Ha : ex_RInt f a b) (Hb : ex_RInt g a b)
   (Hext : ∀ x, a <= x <= b → f x + g x = h x) : ex_RInt h a b.
Proof. Admitted. (* Check ex_RInt_plus. *)

Lemma ex_RInt_add  {f g : R → R} {a b : R} (Ha : ex_RInt f a b) (Hb : ex_RInt g a b) :
  ex_RInt (fun x => f x + g x) a b.
Proof. Admitted.

Lemma ex_RInt_Iverson_le {x a b}  : ex_RInt (Iverson (Rle x)) a b.
Proof. Admitted.

Lemma ex_RInt_Iverson_ge {x a b}  : ex_RInt (Iverson (Rge x)) a b.
Proof. Admitted.

Lemma ex_RInt_Iverson_eq {x a b}  : ex_RInt (Iverson (eq x)) a b.
Proof. Admitted.

Lemma ex_RInt_Iverson_le' {z a b}  : ex_RInt (Iverson (fun x : R => x <= z)) a b.
Proof. Admitted.

Lemma ex_RInt_Iverson_nle' {z a b}  : ex_RInt (Iverson (fun x : R => ¬ x <= z)) a b.
Proof. Admitted.

Lemma ex_RInt_Iverson_le_uncurry {rx} : ex_RInt (λ y : R, Iverson (uncurry Rle) (y, rx)) 0 1.
Proof. Admitted.

Lemma ex_RInt_Iverson_ge_uncurry {rx} : ex_RInt (λ y : R, Iverson (uncurry Rge) (y, rx)) 0 1.
Proof. Admitted.
(*
Lemma DominatedCvgTheorem {F : nat → R → R} {a b : R} (g : R → R)
  (Hdom : forall n x, Rmin a b <= x <= Rmax a b → 0 <= F n x <= g x)
  (Hint : ex_RInt g a b) :
  is_RInt (fun x => SeriesC (fun n => F n x)) a b (SeriesC (fun n => RInt (fun x => F n x) a b)).
Proof. Admitted.
*)


Lemma RInt_pow {a b N} : RInt (λ x : R, x ^ N) a b = b ^ (N + 1)%nat / (N + 1)%nat - a ^ (N + 1)%nat / (N + 1)%nat.
Proof. Admitted.


(* Arzela's Dominated Convergence theorem
Self-contained proof that does not use any measure theory: https://arxiv.org/pdf/1408.1439
Oh, never mind, The theorem presumes that the limit we're trying to prove exists and this cannot
be easily eliminated from the proof.

The monotone convergence theorem for Riemann integrals also assumes the limit is integrable.

In fact, even the Riemann version of the Dominated Convergence theorem has this problem!

Can I prove this for when F is (piecewise) uniformly continuous? ie. continuous, since [a, b] is compact.

Fubini's theorem gives a stronger condition: The set of discontinuities has measure 0.
Here the set of discontinuities is equal to at least every horizontal line (n parameter) plus any discontinuities
associated to the first parameter.

In any case, we are restricting the _continuity_ of the function F, not its integrability, which is stronger.


Proof. Admitted.

 *)


Definition Continuity2 (f : (R * R) -> R) (x y : R) : Prop :=
  filterlim f (locally (x, y)) (locally (f (x, y))).

Definition Discontinuities2 (f : R * R -> R) : R * R -> Prop :=
  fun '(x, y) => ¬ Continuity2 f x y.

(* A set is negligible if it can be covered by countably many balls of arbitrarily small total volume. *)
Definition Negligible (S : R * R -> Prop) : Prop :=
  ∀ (ε : posreal), ∃ (c : nat -> R * R) (r : nat -> nonnegreal),
    (SeriesC (fun n => r n * r n) < ε) /\
    (∀ x, S x -> ∃ n, ball (c n) (r n) x).

Theorem Negligible_Empty : Negligible (fun _ => False).
Proof.
  intro ε.
  exists (fun _ => (0, 0)), (fun _ => mknonnegreal 0 (Rle_refl 0)); constructor.
  { simpl. rewrite SeriesC_0; [apply cond_pos | ]. intros ?; lra. }
  intros ? [].
Qed.

(* Sets *)

Definition Icc (a b : R) : R -> Prop :=
  fun t => Rmin a b <= t <= Rmax a b.

Definition Ici (a : R) : R -> Prop :=
  fun t => a <= t.

Definition Iic (b : R) : R -> Prop :=
  fun t => t <= b.

Definition Iii : R -> Prop :=
  fun t => True.

Definition RII (X Y : R -> Prop) : R * R -> Prop :=
  fun '(tx, ty) => X tx /\ Y ty.

Definition On {T} (S U : T -> Prop) : Prop :=
  ∀ t, S t -> U t.

Definition Int {T} (S U : T -> Prop) : T -> Prop :=
  fun t => S t /\ U t.

Definition Bounded (f : R * R -> R) (M : R) : R * R -> Prop :=
  fun t => Rabs (f t) <= M.

(*
Definition NRtoRR (F : nat → R → R) : R → R → R :=
  fun x y => F (Rcomplements.floor1 x) y.
  (HC : Negligible (Int (RII (Icc xa xb) (Icc ya yb)) (Discontinuities2 f))) :
*)

(* Not 100% sure yet *)
Lemma FubiniNatR_ex {F : nat → R → R} {a b : R} (g : R → R)
  (Hcont : False) :
  ex_RInt (fun x => SeriesC (fun n => F n x)) a b.
Admitted.

End Lib.

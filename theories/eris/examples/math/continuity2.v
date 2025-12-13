From clutch.eris.examples.math Require Import prelude.
From clutch.eris Require Import infinite_tape.
Import Hierarchy.
Set Default Proof Using "Type*".
#[local] Open Scope R.

(** Definition and lemmas about 2D continuity.
Some of these facts could be used to state the generalized version of Fubini's theorem
(that Fubini's theorem holds when the set of 2D discontinuities is negligible)
*)

(** Two-dimensional continuity.
IMPORTANT: This definition is used in the axiomatization of Fubini's theorem. *)
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

Lemma Continuity2_swap (f : R * R → R) (x y : R) :
  Continuity2 (fun '(x', y') => f (y', x')) y x → Continuity2 f x y.
Proof.
  intros H P Hp.
  have H' := H P Hp.
  revert H'.
  rewrite /filtermap//=/locally//=.
  intros [e He].
  exists e.
  intros [zx zy] Hz.
  apply (He (zy, zx)).
  revert Hz.
  rewrite /ball//=/prod_ball//=.
  intuition.
Qed.

Lemma Continuity2_const {F : R * R → R} (v x y : R) :
  (∀ z, F z = v) →
  Continuity2 F x y.
Proof.
  rewrite /Continuity2.
  intros H.
  replace F with (fun (_ : R * R) => v); last by (apply functional_extensionality; intros; rewrite H).
  apply filterlim_const.
Qed.

Lemma Continuity2_continuous_fst
  {f : R * R → R_CompleteNormedModule} {x y : R} :
  Continuity2 f x y →
  Continuity.continuous (λ x', f (x', y)) x.
Proof.
  unfold Continuity2, Continuity.continuous.
  intros H2.
  apply (filterlim_comp _ _ _ (fun x' => (x', y)) f _ (locally (x, y))).
  2: apply H2.
  rewrite /filterlim/filter_le/filter_map//=.
  rewrite /filtermap//=.
  rewrite /locally//=.
  intros P [e He].
  exists e.
  intros z HZ.
  apply He.
  rewrite /ball//=.
  rewrite /prod_ball//=.
  split; try done.
  apply ball_center.
Qed.

Lemma Continuity2_continuous_snd
  {f : R * R → R_CompleteNormedModule} {x y : R} :
  Continuity2 f x y →
  Continuity.continuous (λ y', f (x, y')) y.
Proof.
  unfold Continuity2, Continuity.continuous.
  intros H2.
  apply (filterlim_comp _ _ _ (fun y' => (x, y')) f _ (locally (x, y))).
  2: apply H2.
  rewrite /filterlim/filter_le/filter_map//=.
  rewrite /filtermap//=.
  rewrite /locally//=.
  intros P [e He].
  exists e.
  intros z HZ.
  apply He.
  rewrite /ball//=.
  rewrite /prod_ball//=.
  split; try done.
  apply ball_center.
Qed.


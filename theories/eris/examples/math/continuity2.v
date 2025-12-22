From clutch.eris.examples.math Require Import prelude.
From clutch.eris Require Import infinite_tape.
Import Hierarchy.
Set Default Proof Using "Type*".
#[local] Open Scope R.

(** Definition and lemmas about 2D continuity.
NB. This is used to state Fubini's axiom. *)

(** 2D continuity *)
Definition Continuity2 (f : (R * R) -> R) (x y : R) : Prop :=
  filterlim f (locally (x, y)) (locally (f (x, y))).

Lemma Continuity2_continuity_2d_pt f x y:
  Continuity2 f x y <-> Continuity.continuity_2d_pt (curry f) x y.
Proof.
  split.
  - rewrite /Continuity2/Continuity.continuity_2d_pt.
    intros H eps.
    rewrite /filtermap//=/locally//= in H.
    rewrite /filterlim/=/filter_le/= /filtermap//= in H.
    pose (P:=(λ u, Rabs (u  - f (x, y)) < eps)).
    unshelve epose proof H P _ as [ep' H0].
    { exists eps.
      rewrite /P/=.
      rewrite /ball/=/AbsRing_ball/abs/=/minus/=/plus/opp/=/Rabs.
      intros. 
      repeat case_match; lra.
    }
    exists ep'.
    intros u v ? ?.
    unshelve epose proof H0 (u, v) _ as H3.
    { rewrite /ball/=/AbsRing_ball/prod_ball/=/ball/=/AbsRing_ball/abs/=/minus/=/plus/opp/=.
      unfold Rabs in *.
      repeat case_match; lra.
    }
    rewrite /P in H3.
    by rewrite /curry.
  - rewrite /Continuity2/Continuity.continuity_2d_pt.
    intros H P [eps H'].
    pose proof H eps as [delta H''].
    rewrite /filtermap.
    exists delta.
    intros [u v] H0.
    rewrite /ball/=/AbsRing_ball/prod_ball/=/ball/=/AbsRing_ball/abs/=/minus/=/plus/opp/= in H0.
    unshelve epose proof H'' u v _ _.
    + unfold Rabs in *; repeat case_match; lra.
    + unfold Rabs in *; repeat case_match; lra.
    + by apply H'.
Qed. 

(** The set of 2D discontinuities of a function *)
Definition Discontinuities2 (f : R * R -> R) : R * R -> Prop :=
  fun '(x, y) => ¬ Continuity2 f x y.

(** A Negligible set in 2D
The set can be covered by families of balls with arbitrarily small area. *)
Definition Negligible (S : R * R -> Prop) : Prop :=
  ∀ (ε : posreal), ∃ (c : nat -> R * R) (r : nat -> nonnegreal),
    (SeriesC (fun n => r n * r n) < ε) /\
    (∀ x, S x -> ∃ n, ball (c n) (r n) x).

(** The empty set is negligible *)
Theorem Negligible_Empty : Negligible (fun _ => False).
Proof.
  intro ε.
  exists (fun _ => (0, 0)), (fun _ => mknonnegreal 0 (Rle_refl 0)); constructor.
  { simpl. rewrite SeriesC_0; [apply cond_pos | ]. intros ?; lra. }
  intros ? [].
Qed.

(** 2D Continuity when arguments are exchanged *)
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

(** Constant functions are 2D continuous *)
Lemma Continuity2_const {F : R * R → R} (v x y : R) :
  (∀ z, F z = v) →
  Continuity2 F x y.
Proof.
  rewrite /Continuity2.
  intros H.
  replace F with (fun (_ : R * R) => v); last by (apply functional_extensionality; intros; rewrite H).
  apply filterlim_const.
Qed.

Lemma Continuity2_mult {F f1 f2: R * R → R} (x y : R) :
  Continuity2 f1 x y ->
  Continuity2 f2 x y ->
  (∀ z, F z = f1 z * f2 z) →
  Continuity2 F x y.
Proof.
  rewrite !Continuity2_continuity_2d_pt.
  intros H1 H2 H3.
  eapply Continuity.continuity_2d_pt_mult in H1; last apply H2.
  eapply Continuity.continuity_2d_pt_ext; last apply H1.
  intros. simpl.
  rewrite /curry.
  rewrite H3. lra.
Qed. 

(** 2D continuty projects to 1D continuity along a horizontal line *)
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

(** 2D continuty projects to 1D continuity along a vertical line *)
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

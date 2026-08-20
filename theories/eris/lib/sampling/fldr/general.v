From Coq Require Import Arith.PeanoNat Lists.List Reals Psatz Lia ZArith.
From clutch.eris Require Import eris.
From clutch.eris.lib Require Import list.
From clutch.eris.lib.sampling.fldr Require Import adequacy interface model distribution implementation list_total preprocessing loop.
From clutch.eris.lib.sampling Require Import utils distribution_adequacy distr_impl.

Import ListNotations.
#[local] Open Scope R.


Lemma fldr_sample_lim_exec_pointwise_general
    (ws : list nat) (Hws : admissible ws)
    (σ : state) (v : val) :
    lim_exec (fldr_sample ws fldr_unit_loc, σ) v = fldr_val_distr ws Hws v.
Proof.
  assert (Hprob :
      prob (lim_exec (fldr_sample ws fldr_unit_loc, σ))
        (λ w, bool_decide (v = w)) = fldr_val_distr ws Hws v).
  {
    unshelve eapply (@μ_impl_is_μ
      (fldr_val_distr ws Hws) (fldr_sample ws fldr_unit_loc) _
      adequacy.erisΣ).
    - iIntros (Σ erisGS0 ε D L Hε HD Hsum Φ) "Herr HΦ".
      wp_apply (twp_fldr_sample_adv_comp_general ws Hws D ε L with "Herr")
        as (j) "Herr"; try done.
      + rewrite <- Hsum.
        apply SeriesC_ext.
        intro x.
        apply Rmult_comm.
      + iApply ("HΦ" $! j).
        iExact "Herr".
    - apply adequacy.subG_erisGPreS.
      apply iprop.subG_refl.
  }
  rewrite (fldr_prob_singleton _ _) in Hprob.
  exact Hprob.
Qed.

Theorem fldr_sample_adequacy_general (ws : list nat) (Hws : admissible ws)
    (σ : state) (i : nat) (Hi : (i < length ws)%nat) :
    lim_exec (fldr_sample ws fldr_unit_loc, σ) #i =
      (INR (nth i ws 0%nat) / INR (weight_sum ws))%R.
Proof.
  rewrite (fldr_sample_lim_exec_pointwise_general ws Hws σ #i).
  rewrite (fldr_val_distr_nat ws Hws i).
  unfold target_mass.
  rewrite (proj2 (Nat.ltb_lt i (length ws)) Hi).
  reflexivity.
Qed.

Theorem fldr_sample_terminates_general
    (ws : list nat) (Hws : admissible ws)
    (σ : state) :
    SeriesC (lim_exec (fldr_sample ws fldr_unit_loc, σ)) = 1%R.
Proof.
  transitivity (SeriesC (fldr_val_distr ws Hws)).
  - apply SeriesC_ext.
    intro v.
    apply (fldr_sample_lim_exec_pointwise_general ws Hws σ v).
  - apply fldr_val_distr_mass.
Qed.

(** The single-outcome case: the [length ws = 1] guard returns [#0] with
    probability one, and [nth 0 ws 0 = weight_sum ws] so the ratio is 1. *)
Lemma single_outcome_weight (ws : list nat) (Hone : (length ws = 1)%nat) :
    nth 0 ws 0%nat = weight_sum ws.
Proof.
  destruct ws as [|w ws].
  - simpl in Hone. lia.
  - destruct ws as [|w' ws'].
    + simpl [weight_sum]; lia.
    + simpl in Hone. lia.
Qed.

Lemma fldr_sample_single_outcome (ws : list nat) (Hws : admissible ws)
    (Hone : (length ws = 1)%nat) (σ : state) :
    lim_exec (fldr_sample ws fldr_unit_loc, σ) #0 = 1%R.
Proof.
  rewrite (fldr_sample_adequacy_general ws Hws σ 0%nat).
  - rewrite (single_outcome_weight ws Hone).
    field.
    apply not_0_INR.
    pose proof (admissible_weight_sum_pos ws Hws) as Hsumpos.
    lia.
  - lia.
Qed.

(** * Regression: the generalisation strictly extends the old theorems.

    [[1]] and [[8]] are degenerate ([distribution.nondegenerate_not_one],
    [distribution.nondegenerate_not_eight]), so [fldr_sample_adequacy] and
    [fldr_sample_terminates] cannot be applied to them; the general theorems
    still decide them. *)

Example one_is_admissible : admissible [1%nat].
Proof. split; [discriminate|]. repeat constructor. Qed.

Example eight_is_admissible : admissible [8%nat].
Proof. split; [discriminate|]. constructor; [lia|constructor]. Qed.

Example three_two_one_admissible : admissible [3%nat; 2%nat; 1%nat].
Proof. split; [discriminate|]. repeat (constructor; [lia|]). constructor. Qed.

Example degenerate_one_covered (σ : state) :
  lim_exec (fldr_sample [1%nat] fldr_unit_loc, σ) #0 = 1%R
  /\ SeriesC (lim_exec (fldr_sample [1%nat] fldr_unit_loc, σ)) = 1%R
  /\ ~ nondegenerate [1%nat].
Proof.
  split; [|split].
  - rewrite (fldr_sample_adequacy_general [1%nat] one_is_admissible σ 0%nat).
    + simpl. lra.
    + simpl; lia.
  - apply (fldr_sample_terminates_general [1%nat] one_is_admissible σ).
  - exact nondegenerate_not_one.
Qed.

Example degenerate_eight_covered (σ : state) :
  lim_exec (fldr_sample [8%nat] fldr_unit_loc, σ) #0 = 1%R
  /\ SeriesC (lim_exec (fldr_sample [8%nat] fldr_unit_loc, σ)) = 1%R
  /\ ~ nondegenerate [8%nat].
Proof.
  split; [|split].
  - rewrite (fldr_sample_adequacy_general [8%nat] eight_is_admissible σ 0%nat).
    + simpl. lra.
    + simpl; lia.
  - apply (fldr_sample_terminates_general [8%nat] eight_is_admissible σ).
  - exact nondegenerate_not_eight.
Qed.

Example multi_outcome_covered (σ : state) :
  lim_exec (fldr_sample [3%nat; 2%nat; 1%nat] fldr_unit_loc, σ) #1 = (2/6)%R
  /\ SeriesC (lim_exec (fldr_sample [3%nat; 2%nat; 1%nat] fldr_unit_loc, σ)) = 1%R.
Proof.
  split.
  - rewrite (fldr_sample_adequacy_general _ three_two_one_admissible σ 1%nat).
    + simpl. lra.
    + simpl; lia.
  - apply (fldr_sample_terminates_general _ three_two_one_admissible σ).
Qed.
Print Assumptions fldr_sample_adequacy_general.
Print Assumptions fldr_sample_terminates_general.

(** The unconditional [distr_impl] instance is available from admissibility
    alone, including the degenerate singleton case. *)
Lemma fldr_instance_is_unconditional (ws : list nat) (Hws : admissible ws) :
    distr_impl (fldr_val_distr ws Hws).
Proof. apply _. Qed.

Example fldr_instance_covers_degenerate :
    distr_impl (fldr_val_distr [1%nat] one_is_admissible).
Proof. apply _. Qed.

Example fldr_instance_degenerate_is_not_nondegenerate :
    ~ nondegenerate [1%nat].
Proof. exact nondegenerate_not_one. Qed.

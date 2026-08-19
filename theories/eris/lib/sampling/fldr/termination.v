From Coq Require Import Arith.PeanoNat Lists.List Reals Psatz Lia ZArith.
From clutch.eris Require Import eris.
From clutch.eris.lib.sampling.fldr Require Import adequacy interface model distribution.
From clutch.eris.lib.sampling Require Import distribution_adequacy.

Import ListNotations.
#[local] Open Scope R.

Lemma fldr_sample_lim_exec_pointwise
    (ws : list nat) (Hws : admissible ws) (Hnd : nondegenerate ws)
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
      wp_apply (twp_fldr_sample_adv_comp ws Hws Hnd D ε L with "Herr")
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

(** [lim_exec] is a sub-distribution, so missing mass is exactly divergence;
    pointwise exactness at every value leaves no room for a diverging remainder. *)
Theorem fldr_sample_terminates
    (ws : list nat) (Hws : admissible ws) (Hnd : nondegenerate ws)
    (σ : state) :
    SeriesC (lim_exec (fldr_sample ws fldr_unit_loc, σ)) = 1%R.
Proof.
  transitivity (SeriesC (fldr_val_distr ws Hws)).
  - apply SeriesC_ext.
    intro v.
    apply (fldr_sample_lim_exec_pointwise ws Hws Hnd σ v).
  - apply fldr_val_distr_mass.
Qed.

Print Assumptions fldr_sample_adequacy.
Print Assumptions fldr_sample_terminates.

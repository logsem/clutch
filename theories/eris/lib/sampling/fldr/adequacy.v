From Coq Require Import Arith.PeanoNat Lists.List Reals Psatz Lia ZArith.
From clutch.eris Require Import eris.
From clutch.eris.lib.sampling Require Import utils distr_impl distribution_adequacy.
From clutch.eris.lib.sampling.fldr Require Import model distribution implementation interface.

Import ListNotations.
#[local] Open Scope R.

Section FldrImplementation.
  Context (ws : list nat) (Hws : admissible ws) (Hnd : nondegenerate ws).

  Instance fldr_impl : distr_impl (fldr_val_distr ws Hws).
  Proof using ws Hws Hnd.
    refine (MkDistrImpl (fldr_val_distr ws Hws)
              (fldr_sample ws) fldr_alloc loc
              (λ _ _ Δ l, fldr_own_tape ws Δ l)
              (λ _ _ Δ α, ⌜fldr_is_abs_loc Δ α⌝)%I
              fldr_unit_loc _ _ _ _).
    - iIntros (Σ erisGS0 D ε L ε_ge_0 D_bounds D_sum Φ) "Herr HΦ".
      wp_apply (twp_fldr_sample_adv_comp ws Hws Hnd D ε L with "Herr")
        as (i) "Herr"; try done.
      by iApply ("HΦ" $! i).
    - iIntros (Σ erisGS0 Φ) "_ HΦ".
      iApply (twp_fldr_sample_alloc ws).
      + iPureIntro; trivial.
      + iExact "HΦ".
    - iIntros (Σ erisGS0 e ε Δ l D L Φ e_not_val ε_ge_0 D_bounds D_sum)
        "(Herr & Htape & Hnext)".
      iApply (twp_fldr_sample_presample_adv_comp ws Hws Hnd e ε Δ l D L Φ
        e_not_val ε_ge_0 D_bounds D_sum).
      iFrame.
    - iIntros (Σ erisGS0 α Δ l v Φ) "Hpre HΦ".
      wp_apply (twp_fldr_sample_load ws Hws α Δ l v with "Hpre").
      by iApply "HΦ".
  Defined.
End FldrImplementation.

Theorem fldr_sample_adequacy
    (ws : list nat) (Hws : admissible ws) (Hnd : nondegenerate ws)
    (σ : state) (i : nat) (Hi : (i < length ws)%nat) :
    lim_exec (fldr_sample ws fldr_unit_loc, σ) #i =
      (INR (nth i ws 0%nat) / INR (weight_sum ws))%R.
Proof.
  assert (Hprob :
      prob (lim_exec (fldr_sample ws fldr_unit_loc, σ))
        (λ w, bool_decide (#i = w)) = fldr_val_distr ws Hws #i).
  {
    unshelve eapply (@μ_impl_is_μ
      (fldr_val_distr ws Hws) (fldr_sample ws fldr_unit_loc) _
      adequacy.erisΣ).
    - iIntros (Σ erisGS0 ε D L Hε HD Hsum Φ) "Herr HΦ".
      wp_apply (twp_fldr_sample_adv_comp ws Hws Hnd D ε L with "Herr")
        as (j) "Herr"; try done.
      + rewrite <- Hsum.
        apply SeriesC_ext.
        intro v.
        apply Rmult_comm.
      + iApply ("HΦ" $! j).
        iExact "Herr".
    - apply adequacy.subG_erisGPreS.
      apply iprop.subG_refl.
  }
  rewrite (fldr_prob_singleton _ _ ) in Hprob.
  rewrite (fldr_val_distr_nat ws Hws i) in Hprob.
  unfold target_mass in Hprob.
  rewrite (proj2 (Nat.ltb_lt i (length ws)) Hi) in Hprob.
  exact Hprob.
Qed.

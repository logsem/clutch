(** One-sided-exponential instantiation of the generic report-noisy-max library
    ([report_noisy_max_generic_lemmas]).  The ~700-line argmax + tape-state-step
    machinery is INHERITED; only the single per-draw coupling is exp-specific:

      - [Hdraw_exp] : the directional general-shift coupling.  This is ALREADY
                      the shape of [DPcoupl_exp_draw] (lib/exponential.v), since
                      the one-sided exponential natively supports an UPWARD shift
                      [z ↦ z + k] at cost [k'·ε] under [0 ≤ k+loc-loc' ≤ k'] — so
                      [Hdraw_exp] is a one-liner.

    Feeding it through the generic per-coordinate constructor
    [noise_map_correct_of_draw] yields the pivot, which instantiates the tape
    layer [hoare_couple_noise_list].  This file is the exp twin of
    [report_noisy_max_lemmas] — same shape, different noise. *)
From clutch.prob Require Import couplings_dp couplings differential_privacy distribution exponential.
From clutch.gen_diffpriv Require Import all.
From clutch.gen_diffpriv.lib Require Import exponential exponential_tapes.
From clutch.gen_prob_lang Require Import gwp.list families.
From clutch.gen_diffpriv.examples Require Export report_noisy_max_pure.
From clutch.gen_diffpriv.examples Require Import report_noisy_max_generic_lemmas.

(** [Hdraw] for the exponential: the single directional draw coupling.  This is
    literally [DPcoupl_exp_draw] (lib/exponential.v), which is ALREADY in the
    generic library's directional shape; [sf_sample exp_family (num,den,loc) =
    exp_rat num den loc] DEFINITIONALLY (since [exp_family = mkZNoise exp_rat
    exp_rat_mass]). *)
Fact Hdraw_exp (num den loc loc' k k' : Z) :
  (0 < IZR num / IZR den)%R → (0 ≤ k + loc - loc')%Z → (k + loc - loc' ≤ k')%Z →
  DPcoupl (exp_rat num den loc) (exp_rat num den loc')
          (λ z z', z + k = z')%Z (IZR k' * (IZR num / IZR den)) 0.
Proof.
  intros Hpos Hdir Hdist.
  exact (DPcoupl_exp_draw num den loc loc' k k' Hdir Hdist Hpos).
Qed.

Section exp.
  Context {S : Sig} `{!SampleIn exp_family S} `{!diffprivGS S Σ}.

  (** The exp report-noisy-max list coupling: [hoare_couple_noise_list] at
      [sample := exp_rat], with the pivot discharged per-coordinate via
      [noise_map_correct_of_draw … Hdraw_exp].  Since
      [exp_family = mkZNoise exp_rat exp_rat_mass] (families.v), the generic [↪N]
      tape views ARE the exp [↪E] views, so the statement is the exp one. *)
  Definition hoare_couple_exp_list :=
    hoare_couple_noise_list exp_rat exp_rat_mass
      (noise_map_correct_of_draw exp_rat exp_rat_mass Hdraw_exp)
      (S := S).

End exp.

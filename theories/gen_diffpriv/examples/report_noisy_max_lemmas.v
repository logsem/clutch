(** Discrete-Laplace instantiation of the generic report-noisy-max library
    ([report_noisy_max_generic_lemmas]).  The ~700-line argmax + tape-state-step
    machinery is INHERITED from the generic library; only the single per-draw
    coupling is Laplace-specific:

      - [Hdraw_laplace] : the directional general-shift coupling, i.e. exactly
                          [DPcoupl_laplace_draw] re-stated in the generic library's
                          shape (relation [z + k = z'], cost [IZR k' · ε]).

    Feeding it through the generic per-coordinate constructor
    [noise_map_correct_of_draw] yields the pivot [noise_map_correct_statement],
    which instantiates the tape layer [hoare_couple_noise_list].

    Re-exports the noise-independent pure lemmas ([report_noisy_max_pure]) so
    downstream clients (e.g. [report_noisy_max]) keep seeing [list_max_index_eq]
    etc. unchanged. *)
From clutch.prob Require Import couplings_dp couplings differential_privacy distribution.
From clutch.gen_diffpriv Require Import all.
From clutch.gen_diffpriv.lib Require Import laplace laplace_tapes.
From clutch.gen_prob_lang Require Import gwp.list families.
From clutch.gen_diffpriv.examples Require Export report_noisy_max_pure.
From clutch.gen_diffpriv.examples Require Import report_noisy_max_generic_lemmas.

(** [Hdraw] for Laplace: the single directional draw coupling.  This is just
    [DPcoupl_laplace_draw] (lib/laplace.v), whose [Z.abs (k+loc-loc') ≤ k']
    side-condition follows from [0 ≤ k+loc-loc' ≤ k'] by [lia], and whose
    [sf_sample laplace_family (num,den,loc) = laplace_rat num den loc]
    DEFINITIONALLY (since [laplace_family = mkZNoise laplace_rat laplace_rat_mass]). *)
Fact Hdraw_laplace (num den loc loc' k k' : Z) :
  (0 < IZR num / IZR den)%R → (0 ≤ k + loc - loc')%Z → (k + loc - loc' ≤ k')%Z →
  DPcoupl (laplace_rat num den loc) (laplace_rat num den loc')
          (λ z z', z + k = z')%Z (IZR k' * (IZR num / IZR den)) 0.
Proof.
  intros Hpos Hdir Hdist.
  apply (DPcoupl_laplace_draw num den loc loc' k k'); [lia | exact Hpos].
Qed.

Section laplace.
  Context {S : Sig} `{!SampleIn laplace_family S} `{!diffprivGS S Σ}.

  (** The Laplace report-noisy-max list coupling: the generic
      [hoare_couple_noise_list] at [sample := laplace_rat], with the pivot
      discharged per-coordinate via [noise_map_correct_of_draw … Hdraw_laplace].
      Since [laplace_family = mkZNoise laplace_rat laplace_rat_mass] (families.v),
      the generic [↪N] tape views ARE the Laplace [↪L] views, so the statement is
      the Laplace one verbatim. *)
  Definition hoare_couple_laplace_list :=
    hoare_couple_noise_list laplace_rat laplace_rat_mass
      (noise_map_correct_of_draw laplace_rat laplace_rat_mass Hdraw_laplace)
      (S := S).

End laplace.

(** One-sided-exponential instantiation of the generic report-noisy-max library
    ([report_noisy_max_generic_lemmas]).  The ~700-line argmax + tape-state-step
    machinery is INHERITED; only the two per-draw couplings are exp-specific:

      - [Hiso_exp]   : the 0-cost location isometry ([Mcoupl_exp_isometry]);
      - [Hshift_exp] : the +1 shift at cost [num/den], via the ONE-SIDED
                       [Mcoupl_exp] (k=1, k'=2) whose directionality [0 ≤ 1+loc-loc']
                       is satisfied because [dZ loc loc' ≤ 1] (so loc-loc' ≥ -1).

    The cost equals [num/den] exactly ([IZR 2 · num/(2·den)]).  This file is the
    exp twin of [report_noisy_max_lemmas] — same ~40 lines, different noise. *)
From clutch.prob Require Import couplings_dp couplings differential_privacy distribution exponential.
From clutch.gen_diffpriv Require Import all.
From clutch.gen_diffpriv.lib Require Import exponential exponential_tapes.
From clutch.gen_prob_lang Require Import gwp.list families.
From clutch.gen_diffpriv.examples Require Export report_noisy_max_pure.
From clutch.gen_diffpriv.examples Require Import report_noisy_max_generic_lemmas.

(** [Hiso] for the exponential: the 0-cost location isometry. *)
Fact Hiso_exp (num den loc loc' : Z) :
  Mcoupl (exp_rat num den loc) (exp_rat num den loc')
         (λ z z', z - z' = loc - loc')%Z 0.
Proof.
  rewrite /exp_rat. case_decide as H.
  - apply (Mcoupl_exp_isometry (mkposreal _ H) loc loc').
  - apply Mcoupl_dret; [done | lia].
Qed.

(** [Hshift] for the exponential: the +1 shift at cost [num/den].  Uses the
    one-sided [Mcoupl_exp] with k=1, k'=2; directionality [0 ≤ 1+loc-loc'] and
    bound [1+loc-loc' ≤ 2] both follow from [dZ loc loc' ≤ 1]. *)
Fact Hshift_exp (num den loc loc' : Z) :
  (0 < IZR num / IZR (2*den))%R → (dZ loc loc' <= 1)%R →
  DPcoupl (exp_rat num (2*den) loc) (exp_rat num (2*den) loc')
          (λ z z', z + 1 = z')%Z (IZR num / IZR den) 0.
Proof.
  intros Hproof Hd.
  apply dZ_bounded_cases in Hd. simpl in Hd.
  rewrite /exp_rat. case_decide as Hpos ; [|done].
  eapply DPcoupl_mono; [done|done|..]; last apply Mcoupl_to_DPcoupl;
    last eapply (Mcoupl_exp (mkposreal _ Hpos) loc loc' 1 2); try done.
  - (* cost: IZR 2 * (num/(2·den)) ≤ num/den  (equality) *)
    simpl. rewrite mult_IZR.
    replace (_/(_*_))%R with (/2 * (IZR num / IZR den))%R; last (rewrite Rdiv_mult_distr; lra).
    rewrite -Rmult_assoc.
    rewrite -{2}(Rmult_1_l (_/_)%R).
    apply Rmult_le_compat_r; [left; by apply ineq_convert | simpl; lra].
  - (* directionality 0 ≤ 1 + loc - loc' *) lia.
  - (* bound 1 + loc - loc' ≤ 2 *) lia.
Qed.

Section exp.
  Context {S : Sig} `{!SampleIn exp_family S} `{!diffprivGS S Σ}.

  (** The exp report-noisy-max list coupling: [hoare_couple_noise_list]
      instantiated at [sample := exp_rat].  Since
      [exp_family = mkZNoise exp_rat exp_rat_mass] (families.v), the generic [↪N]
      tape views ARE the exp [↪E] views, so the statement is the exp one. *)
  Definition hoare_couple_exp_list :=
    hoare_couple_noise_list exp_rat exp_rat_mass Hiso_exp Hshift_exp (S := S).

End exp.

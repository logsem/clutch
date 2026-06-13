(** Report-noisy-max (presampling) DP case study with ONE-SIDED EXPONENTIAL
    noise (the exponential mechanism), exp instantiation.

    The ~480-line implementation body (program + [rnm_init] + [rwp_list_map] +
    tape allocation + the [rnm_pres_diffpriv] proof) is INHERITED from the
    noise-generic [report_noisy_max_generic], parametric over the noise
    distribution [sample : Z → Z → Z → distr Z] and its list-presampling coupling
    [Hcouple].  This file is the THIN exponential instantiation: it pins
    [sample := exp_rat], [mass := exp_rat_mass] and discharges [Hcouple] with
    [hoare_couple_exp_list] (from [report_noisy_max_exp_lemmas]).  Since
    [exp_family = mkZNoise exp_rat exp_rat_mass] (families.v), the generic noise
    index/tape views ARE the exp ones definitionally, so no transport is needed
    and the public statements are preserved verbatim.

    See [report_noisy_max_pointwise] for the pointwise (coupling) variant. *)
From clutch.common Require Import inject.
From clutch.prob Require Import differential_privacy exponential.
From clutch.gen_diffpriv Require Import adequacy all.
From clutch.gen_diffpriv.lib Require Import exponential exponential_tapes.
From clutch.gen_prob_lang Require Import gwp.list inject families.
From clutch.gen_diffpriv.examples Require Import report_noisy_max_exp_lemmas report_noisy_max_generic.
From iris.prelude Require Import options.

Section rnme.
  Context {Sg : Sig} `{!SampleIn exp_family Sg} `{!diffprivGS Sg Σ}.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Sg)).

  (** The exp report-noisy-max program: the generic
      [report_noisy_max_presampling] pinned at [sample := exp_rat].  Because
      [exp_family = mkZNoise exp_rat exp_rat_mass], its sample index
      [sample_idx (D := mkZNoise exp_rat exp_rat_mass)] is the exp index
      [sample_idx (D := exp_family)] definitionally. *)
  Definition report_noisy_max_exp_presampling (num den : Z) : val :=
    report_noisy_max_presampling exp_rat exp_rat_mass (Sg := Sg) num den.

  (** The exp privacy proof: [report_noisy_max_generic.rnm_pres_diffpriv] with the
      exp list coupling [hoare_couple_exp_list] for [Hcouple]. *)
  Lemma rnm_exp_pres_diffpriv (Δ : Z) num den (evalQ : val) DB (dDB : Distance DB) (N : nat) K :
    (1 <= Δ)%Z →
    (0 < IZR num / IZR (2 * den))%R →
    (∀ i : Z, ⊢ hoare_sensitive Sg (evalQ #i) (IZR Δ) dDB dZ) →
    ∀ db db', (dDB db db' <= 1)%R →
                {{{ ↯m (IZR Δ * (IZR num / IZR den)) ∗
                    ⤇ fill K (report_noisy_max_exp_presampling num den evalQ #N (of_val (inject db'))) }}}
                  report_noisy_max_exp_presampling num den evalQ #N (of_val (inject db))
                  {{{ v, RET v ; ∃ (v' : val), ⤇ fill K v' ∗ ⌜ v = v' ⌝  }}}.
  Proof.
    apply (report_noisy_max_generic.rnm_pres_diffpriv
             exp_rat exp_rat_mass (Sg := Sg)
             (@hoare_couple_exp_list Sg _ _ _)).
  Qed.

End rnme.

Lemma rnm_exp_diffpriv_presampling (Sg : Sig) `{!SampleIn exp_family Sg} (Δ : Z) num den (evalQ : val) DB (dDB : Distance DB) (N : nat) :
  (1 <= Δ)%Z →
  (0 < IZR num / IZR (2 * den))%R →
  (0 <= IZR Δ * (IZR num / IZR den))%R →
  (∀ `{!diffprivGS Sg Σ}, ∀ i : Z, ⊢ hoare_sensitive Sg (evalQ #i) (IZR Δ) dDB dZ) → ∀ σ,
      diffpriv_pure
        dDB
        (λ db, lim_exec (δ := lang_markov (gen_lang Sg)) ((report_noisy_max_exp_presampling num den evalQ #N (inject db)), σ))
        (IZR Δ * (IZR num / IZR den)).
Proof.
  intros. apply diffpriv_approx_pure. apply DPcoupl_diffpriv.
  intros.
  eapply (wp_adequacy Sg diffprivΣ) => //.
  iIntros (?)"H1 H2".
  iDestruct (rnm_exp_pres_diffpriv with "[$H2 H1]") as "K"; try done.
  - by erewrite fill_empty.
  - iIntros.
    iApply "K".
    iNext. iIntros (?) "(%&?&%)".
    by iFrame.
Qed.

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
From Stdlib Require Import FunctionalExtensionality.
From clutch.common Require Import inject.
From clutch.prob Require Import differential_privacy exponential.
From clutch.gen_diffpriv Require Import adequacy all.
From clutch.gen_diffpriv.lib Require Import exponential exponential_tapes.
From clutch.gen_prob_lang Require Import gwp.list inject families znoise.
From clutch.gen_diffpriv.examples Require Import report_noisy_max_exp_lemmas report_noisy_max_generic report_noisy_max_idiomatic.
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
    report_noisy_max_generic.report_noisy_max_presampling exp_rat exp_rat_mass (Sg := Sg) num den.

  (** The IDIOMATIC exp report-noisy-max program: the generic one-pass
      direct-sampling [rnm_direct1] pinned at the exp family.  Because
      [exp_family = mkZNoise exp_rat exp_rat_mass], this is
      [rnm_direct1 (mkZNoise exp_rat exp_rat_mass) num den] definitionally — the
      [D := mkZNoise sample mass] expected by [rnm_idiomatic_lim_exec_eq]. *)
  Definition report_noisy_max_exp_idiomatic (num den : Z) : val :=
    report_noisy_max_idiomatic.rnm_direct1 exp_family num den.

  (** The exp privacy proof, now stated as the internal-DP notion
      [hoare_diffpriv_classic_at] with the range-carrying codomain
      [fin (Nat.max 1 N)]: [report_noisy_max_generic.rnm_pres_diffpriv] with the
      exp list coupling [hoare_couple_exp_list] for [Hcouple]. *)
  Lemma rnm_exp_pres_diffpriv (Δ : Z) (C : Z) num den (evalQ : val) DB (dDB : Distance DB) (N : nat) :
    (1 <= Δ)%Z →
    (1 <= C)%Z →
    (0 < IZR num / IZR (2 * den))%R →
    (∀ i : Z, ⊢ hoare_sensitive Sg (evalQ #i) (IZR Δ) dDB dZ) →
    ⊢ hoare_diffpriv_classic_at Sg (report_noisy_max_exp_presampling num den evalQ #N)
        (IZR C * (IZR Δ * (IZR num / IZR den))) 0 (IZR C) dDB (fin (Nat.max 1 N)).
  Proof.
    apply (report_noisy_max_generic.rnm_pres_diffpriv
             exp_rat exp_rat_mass (Sg := Sg)
             (@hoare_couple_exp_list Sg _ _ _)).
  Qed.

End rnme.

(** Group-privacy / k-adjacency adequacy corollary (exp).  As in the Laplace
    case, the unit-radius adjacency of [diffpriv_pure] is recovered by SCALING
    the metric by [C]; at [C := 1] this is the original statement verbatim. *)
Lemma rnm_exp_diffpriv_presampling (Sg : Sig) `{!SampleIn exp_family Sg} (Δ : Z) (C : Z) num den (evalQ : val) DB (dDB : Distance DB) (N : nat) :
  (1 <= Δ)%Z →
  (1 <= C)%Z →
  (0 < IZR num / IZR (2 * den))%R →
  (0 <= IZR C * (IZR Δ * (IZR num / IZR den)))%R →
  (∀ `{!diffprivGS Sg Σ}, ∀ i : Z, ⊢ hoare_sensitive Sg (evalQ #i) (IZR Δ) dDB dZ) → ∀ σ,
      diffpriv_pure
        (λ db db', (dDB db db' / IZR C)%R)
        (λ db, lim_exec (δ := lang_markov (gen_lang Sg)) ((report_noisy_max_exp_presampling num den evalQ #N (inject db)), σ))
        (IZR C * (IZR Δ * (IZR num / IZR den))).
Proof.
  intros HΔ HC ?? Hsens σ. apply diffpriv_approx_pure. apply DPcoupl_diffpriv.
  intros db db' Hadj.
  assert (0 < IZR C)%R by (apply IZR_lt; lia).
  assert (Hr : (dDB db db' <= IZR C)%R).
  { apply (Rmult_le_reg_r (/ IZR C)); first by apply Rinv_0_lt_compat.
    rewrite Rinv_r; last lra. exact Hadj. }
  eapply (wp_adequacy Sg diffprivΣ) => //.
  iIntros (?) "H1 H2 H3".
  (* [rnm_exp_pres_diffpriv] is now [hoare_diffpriv_classic_at]; specialise it at
     the empty evaluation context and the concrete adjacency [db,db'], then drive
     its Texan triple ([↯ 0] supplied by [H3]; the [↯m] credit is [H2]). *)
  iPoseProof (rnm_exp_pres_diffpriv Δ C num den evalQ DB dDB N HΔ HC ltac:(done) (Hsens _ _)) as "K".
  rewrite /hoare_diffpriv_classic_at.
  iApply ("K" $! [] db db' Hr with "[$H1 $H2 $H3]").
  iIntros "!>" (y) "rhs".
  rewrite fill_empty. iExists (inject y). by iFrame.
Qed.

(** ** Headline (exp): the IDIOMATIC (one-pass, no presampling tapes) exponential
    report-noisy-max is differentially private — EXACTLY
    [rnm_exp_diffpriv_presampling] but for the idiomatic program
    [report_noisy_max_exp_idiomatic] (i.e. [rnm_direct1]).  The proof is a pure
    transport: [diffpriv_pure] depends on the program only through the
    output-distribution family [λ db, lim_exec (prog … db)], and
    [rnm_idiomatic_lim_exec_eq] gives, pointwise in [db], the equality of the
    idiomatic and presampling families (at [sample := exp_rat],
    [mass := exp_rat_mass]).  Lifting that pointwise equality to a FUNCTION
    equality ([functional_extensionality]) rewrites the goal to exactly
    [rnm_exp_diffpriv_presampling], which we [apply]. *)
Lemma rnm_exp_diffpriv_idiomatic (Sg : Sig) `{!SampleIn exp_family Sg} (Δ : Z) (C : Z) num den (evalQ : val) DB (dDB : Distance DB) (N : nat) :
  (1 <= Δ)%Z →
  (1 <= C)%Z →
  (0 < IZR num / IZR (2 * den))%R →
  (0 <= IZR C * (IZR Δ * (IZR num / IZR den)))%R →
  (∀ `{!diffprivGS Sg Σ}, ∀ i : Z, ⊢ hoare_sensitive Sg (evalQ #i) (IZR Δ) dDB dZ) → ∀ σ,
      diffpriv_pure
        (λ db db', (dDB db db' / IZR C)%R)
        (λ db, lim_exec (δ := lang_markov (gen_lang Sg)) ((report_noisy_max_exp_idiomatic num den evalQ #N (inject db)), σ))
        (IZR C * (IZR Δ * (IZR num / IZR den))).
Proof.
  intros HΔ HC Hpos Hcost Hsens σ.
  (* The idiomatic and presampling output-distribution families AGREE pointwise
     (by [rnm_idiomatic_lim_exec_eq] at [sample := exp_rat]); lift to a function
     equality and rewrite to the presampling DP statement. *)
  assert (Hfam :
    (λ db : DB, lim_exec (δ := lang_markov (gen_lang Sg)) ((report_noisy_max_exp_idiomatic num den evalQ #N (inject db)), σ))
    = (λ db : DB, lim_exec (δ := lang_markov (gen_lang Sg)) ((report_noisy_max_exp_presampling num den evalQ #N (inject db)), σ))).
  { apply functional_extensionality => db.
    rewrite /report_noisy_max_exp_idiomatic /report_noisy_max_exp_presampling /exp_family.
    apply (rnm_idiomatic_lim_exec_eq Sg exp_rat exp_rat_mass
             Δ num den evalQ DB dDB N σ ltac:(lia)).
    intros ? i. apply Hsens. }
  rewrite Hfam.
  by apply (rnm_exp_diffpriv_presampling Sg Δ C num den evalQ DB dDB N).
Qed.

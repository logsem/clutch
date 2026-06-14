(** Report-noisy-max (presampling) DP case study, Laplace instantiation.

    The ~480-line implementation body (program + [rnm_init] + [rwp_list_map] +
    tape allocation + the [rnm_pres_diffpriv] proof) is INHERITED from the
    noise-generic [report_noisy_max_generic], parametric over the noise
    distribution [sample : Z → Z → Z → distr Z] and its list-presampling coupling
    [Hcouple].  This file is the THIN Laplace instantiation: it pins
    [sample := laplace_rat], [mass := laplace_rat_mass] and discharges [Hcouple]
    with [hoare_couple_laplace_list] (from [report_noisy_max_lemmas]).  Since
    [laplace_family = mkZNoise laplace_rat laplace_rat_mass] (families.v), the
    generic noise index/tape views ARE the Laplace ones definitionally, so no
    transport is needed and the public statements are preserved verbatim.

    See [report_noisy_max_pointwise] for the pointwise (coupling) variant. *)
From clutch.common Require Import inject.
From clutch.prob Require Import differential_privacy.
From clutch.gen_diffpriv Require Import adequacy all.
From clutch.gen_diffpriv.lib Require Import laplace laplace_tapes.
From clutch.gen_prob_lang Require Import gwp.list inject families.
From clutch.gen_diffpriv.examples Require Import report_noisy_max_lemmas report_noisy_max_generic.
From iris.prelude Require Import options.

Section rnm.
  Context {Sg : Sig} `{!SampleIn laplace_family Sg} `{!diffprivGS Sg Σ}.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Sg)).

  (** The Laplace report-noisy-max program: the generic
      [report_noisy_max_presampling] pinned at [sample := laplace_rat].  Because
      [laplace_family = mkZNoise laplace_rat laplace_rat_mass], its sample index
      [sample_idx (D := mkZNoise laplace_rat laplace_rat_mass)] is the Laplace
      index [sample_idx (D := laplace_family)] definitionally. *)
  Definition report_noisy_max_presampling (num den : Z) : val :=
    report_noisy_max_presampling laplace_rat laplace_rat_mass (Sg := Sg) num den.

  (** The Laplace privacy proof, now stated as the internal-DP notion
      [hoare_diffpriv_classic_at] with the range-carrying codomain
      [fin (Nat.max 1 N)]: [report_noisy_max_generic.rnm_pres_diffpriv] with the
      Laplace list coupling [hoare_couple_laplace_list] for [Hcouple]. *)
  Lemma rnm_pres_diffpriv (Δ : Z) (C : Z) num den (evalQ : val) DB (dDB : Distance DB) (N : nat) :
    (1 <= Δ)%Z →
    (1 <= C)%Z →
    (0 < IZR num / IZR (2 * den))%R →
    (∀ i : Z, ⊢ hoare_sensitive Sg (evalQ #i) (IZR Δ) dDB dZ) →
    ⊢ hoare_diffpriv_classic_at Sg (report_noisy_max_presampling num den evalQ #N)
        (IZR C * (IZR Δ * (IZR num / IZR den))) 0 (IZR C) dDB (fin (Nat.max 1 N)).
  Proof.
    apply (report_noisy_max_generic.rnm_pres_diffpriv
             laplace_rat laplace_rat_mass (Sg := Sg)
             (@hoare_couple_laplace_list Sg _ _ _)).
  Qed.

End rnm.

(** Group-privacy / k-adjacency adequacy corollary.  The unit-radius adjacency
    [dDB db db' <= 1] of [diffpriv_pure] is recovered by SCALING the metric by
    [C]: under [(dDB db db')/IZR C <= 1] (i.e. [dDB db db' <= IZR C]) RNM is
    private at the [C]-scaled cost [IZR C * (IZR Δ * (num/den))].  At [C := 1]
    this is the original [diffpriv_pure dDB … (IZR Δ * (num/den))] verbatim
    (since [x / IZR 1 = x] and [IZR 1 * y = y]). *)
Lemma rnm_diffpriv_presampling (Sg : Sig) `{!SampleIn laplace_family Sg} (Δ : Z) (C : Z) num den (evalQ : val) DB (dDB : Distance DB) (N : nat) :
  (1 <= Δ)%Z →
  (1 <= C)%Z →
  (0 < IZR num / IZR (2 * den))%R →
  (0 <= IZR C * (IZR Δ * (IZR num / IZR den)))%R →
  (∀ `{!diffprivGS Sg Σ}, ∀ i : Z, ⊢ hoare_sensitive Sg (evalQ #i) (IZR Δ) dDB dZ) → ∀ σ,
      diffpriv_pure
        (λ db db', (dDB db db' / IZR C)%R)
        (λ db, lim_exec (δ := lang_markov (gen_lang Sg)) ((report_noisy_max_presampling num den evalQ #N (inject db)), σ))
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
  (* [rnm_pres_diffpriv] is now [hoare_diffpriv_classic_at]; specialise it at the
     empty evaluation context and the concrete adjacency [db,db'], then drive its
     Texan triple ([↯ 0] supplied by [H3]; the [↯m] credit is [H2]). *)
  iPoseProof (rnm_pres_diffpriv Δ C num den evalQ DB dDB N HΔ HC ltac:(done) (Hsens _ _)) as "K".
  rewrite /hoare_diffpriv_classic_at.
  iApply ("K" $! [] db db' Hr with "[$H1 $H2 $H3]").
  iIntros "!>" (y) "rhs".
  rewrite fill_empty. iExists (inject y). by iFrame.
Qed.

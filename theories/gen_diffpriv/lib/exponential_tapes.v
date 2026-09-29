(** Tape-based one-sided-exponential library for the generic DP logic — the
    presampling (tape) analogue of [lib.exponential], mirroring
    [lib.laplace_tapes] family-for-family ([laplace_family] → [exp_family]):

      - surface program syntax [AllocTapeExp num den mean] and the typed tape
        views [α ↪E (num, den, mean; zs)] (impl) / [α ↪Eₛ (num, den, mean; zs)]
        (spec), both sugar over the generic tape map at [sample_idx];

      - the deterministic read [wp_exp_tape] / [wp_exp_tape_val] and allocator
        [wp_alloc_tape_exp];

      - the presampling coupling [wp_couple_tapes_exp], obtained by feeding the
        single exponential draw coupling [DPcoupl_exp_draw] into the generic
        state-step seam [wp_couple_tapes_family].

    Only the per-draw coupling obligation differs from [lib.laplace_tapes]: it
    carries the one-sided directionality [0 ≤ k+loc-loc' ≤ k'] of [Mcoupl_exp]
    instead of Laplace's symmetric [|k+loc-loc'| ≤ k']. *)
From iris.proofmode Require Import proofmode.
From clutch.prob Require Import differential_privacy distribution exponential couplings couplings_app couplings_dp.
From clutch.gen_diffpriv.lib Require Export exponential.
From clutch.gen_prob_lang.spec Require Import spec_ra.
From iris.prelude Require Import options.

Local Open Scope R.

(** [AllocTapeExp num den mean] allocates a fresh presampling tape for the
    exponential family at parameter [(num, den, mean)]. *)
Notation AllocTapeExp num den mean :=
  (AllocSampleTape (sample_idx (D := exp_family)) (Pair num (Pair den mean)))
  (only parsing).

(** Typed tape views over the generic tape predicate at index [sample_idx],
    parameter in explicit [PairV] value form (so the proof-mode tactics match a
    reduced [Sample] redex). *)
Notation "α ↪E ( num , den , mean ; zs )" :=
  ((α ↪ (sample_idx (D := exp_family),
           PairV (LitV (LitInt num)) (PairV (LitV (LitInt den)) (LitV (LitInt mean))),
           ((λ z : Z, LitV (LitInt z)) <$> zs)))%I)
  (at level 20, format "α  ↪E  ( num ,  den ,  mean ;  zs )") : bi_scope.

Notation "α ↪Eₛ ( num , den , mean ; zs )" :=
  ((α ↪ₛ (sample_idx (D := exp_family),
            PairV (LitV (LitInt num)) (PairV (LitV (LitInt den)) (LitV (LitInt mean))),
            ((λ z : Z, LitV (LitInt z)) <$> zs)))%I)
  (at level 20, format "α  ↪Eₛ  ( num ,  den ,  mean ;  zs )") : bi_scope.

Lemma exp_param_to_val (num den mean : Z) :
  sf_param_to_val exp_family (num, den, mean)
  = PairV (LitV (LitInt num)) (PairV (LitV (LitInt den)) (LitV (LitInt mean))).
Proof. reflexivity. Qed.

Lemma exp_sf_inj (z : Z) : sf_inj exp_family z = LitV (LitInt z).
Proof. reflexivity. Qed.

Section exp_tapes.
  Context {S : Sig} `{!SampleIn exp_family S} `{!diffprivGS S Σ}.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang S)).
  Local Notation lidx := (@sample_idx exp_family S _).

  (** Allocate a fresh exponential tape (empty). *)
  Lemma wp_alloc_tape_exp (num den mean : Z) E s :
    {{{ True }}}
      AllocTapeExp #num #den #mean @ s; E
    {{{ (α : loc), RET (LitV (LitLbl α)); α ↪E (num, den, mean; []) }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_pures.
    iApply (wp_alloc_sample_tape lidx
              (PairV (LitV (LitInt num)) (PairV (LitV (LitInt den)) (LitV (LitInt mean))))
              with "[//]").
    iIntros "!>" (α) "Hα". iApply "HΦ". iFrame.
  Qed.

  (** Read the head presampled outcome off a non-empty exponential tape
      (surface form, with the [Pair] parameter reduced by [wp_pures]). *)
  Lemma wp_exp_tape (num den mean z : Z) (zs : list Z) (α : loc) E s :
    {{{ ▷ α ↪E (num, den, mean; z :: zs) }}}
      Exp #num #den #mean (#lbl:α) @ s; E
    {{{ RET #z; α ↪E (num, den, mean; zs) }}}.
  Proof.
    iIntros (Φ) ">Hα HΦ".
    wp_pures.
    iApply (wp_sample_tape lidx
              (PairV (LitV (LitInt num)) (PairV (LitV (LitInt den)) (LitV (LitInt mean))))
              (LitV (LitInt z)) ((λ z0 : Z, LitV (LitInt z0)) <$> zs) α with "[Hα]").
    { iFrame. }
    iIntros "!> Hα". iApply "HΦ". iFrame.
  Qed.

  (** The reduced-form (value-parameter) exponential tape read — stated on the
      [Sample] redex with parameter already reduced to a [PairV] and the tape
      label as a value, i.e. the goal left after [wp_pures] reduces the [Exp]
      surface notation.  Mirrors [wp_laplace_tape_val]. *)
  Lemma wp_exp_tape_val (num den mean z : Z) (zs : list Z) (α : loc) E s :
    {{{ ▷ α ↪E (num, den, mean; z :: zs) }}}
      Sample lidx (Val (PairV (LitV (LitInt num))
                          (PairV (LitV (LitInt den)) (LitV (LitInt mean)))))
             (Val (LitV (LitLbl α))) @ s; E
    {{{ RET #z; α ↪E (num, den, mean; zs) }}}.
  Proof.
    iIntros (Φ) ">Hα HΦ".
    iApply (wp_sample_tape lidx
              (PairV (LitV (LitInt num)) (PairV (LitV (LitInt den)) (LitV (LitInt mean))))
              (LitV (LitInt z)) ((λ z0 : Z, LitV (LitInt z0)) <$> zs) α with "[Hα]").
    { iFrame. }
    iIntros "!> Hα". iApply "HΦ". iFrame.
  Qed.

  (** The presampling (tape) exponential coupling: advancing two exponential
      tapes with a shared draw shifts the spec draw by [k] at error [k'·ε],
      under the one-sided directionality [0 ≤ k+mean-mean' ≤ k'].  This is the
      generic [wp_couple_tapes_family] instantiated with [DPcoupl_exp_draw]. *)
  Lemma wp_couple_tapes_exp (mean mean' k k' : Z) α α' zs zs' e Φ
    (Hdir : (0 <= k + mean - mean')%Z)
    (Hdist : (k + mean - mean' <= k')%Z)
    (num den : Z) (ε ε' : R) E :
    IZR num / IZR den = ε →
    0 < IZR num / IZR den →
    ε' = (IZR k' * ε) →
    ▷ α ↪E (num, den, mean; zs) ∗ ▷ α' ↪Eₛ (num, den, mean'; zs') ∗ ↯m ε' -∗
    (∀ z, α ↪E (num, den, mean; zs ++ [z]) ∗ α' ↪Eₛ (num, den, mean'; zs' ++ [(z + k)%Z]) -∗
          WP e @ E {{ Φ }}) -∗
    WP e @ E {{ Φ }}.
  Proof.
    iIntros (Hε εpos Hε') "(Hα & Hα' & Hcred) HΦ".
    assert (0 <= ε')%R as Hε'pos.
    { subst ε'. apply Rmult_le_pos; [apply IZR_le; lia | lra]. }
    assert (DPcoupl (sf_sample exp_family (num, den, mean))
                    (sf_sample exp_family (num, den, mean'))
                    (λ z z' : Z, (z + k = z')%Z) ε' 0) as Hcpl.
    { rewrite Hε' -Hε. by apply (DPcoupl_exp_draw num den mean mean' k k' Hdir Hdist εpos). }
    iApply (wp_couple_tapes_family S exp_family (num, den, mean) (num, den, mean')
              α α' ((λ z : Z, LitV (LitInt z)) <$> zs) ((λ z : Z, LitV (LitInt z)) <$> zs')
              (λ z z', (z + k = z')%Z) e Φ ε' E Hε'pos Hcpl with "[Hα Hα' Hcred]").
    { rewrite !exp_param_to_val. iFrame. }
    iIntros (a a' Ha) "(Hα & Hα')".
    iEval (rewrite exp_param_to_val) in "Hα".
    iEval (rewrite exp_param_to_val) in "Hα'".
    iApply ("HΦ" $! a). rewrite Ha !fmap_app. iFrame.
  Qed.

End exp_tapes.

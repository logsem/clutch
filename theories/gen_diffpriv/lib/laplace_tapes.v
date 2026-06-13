(** Tape-based discrete-Laplace library for the generic DP logic.

    This adds the *presampling* (tape) interface for the Laplace family on top of
    [lib.laplace]:

      - surface program syntax [AllocTapeLaplace num den mean] and the typed tape
        views [α ↪L (num, den, mean; zs)] (impl) / [α ↪Lₛ (num, den, mean; zs)]
        (spec), both sugar over the *one* generic tape map at the family's index
        [sample_idx] (recovered from [SampleIn laplace_family S], never hardcoded);

      - the deterministic read [wp_laplace_tape] and allocator [wp_alloc_tape_laplace]
        (derived from the generic [wp_sample_tape] / [wp_alloc_sample_tape]);

      - the presampling coupling [wp_couple_tapes_laplace], obtained by feeding the
        single Laplace draw coupling [DPcoupl_laplace_draw] into the generic
        state-step seam [wp_couple_tapes_family].

    As with [lib.laplace], a client only provides [Definition Slap] +
    [SampleIn laplace_family Slap] and works in a [diffprivGS Slap]-development. *)
From iris.proofmode Require Import proofmode.
From clutch.prob Require Import differential_privacy distribution couplings couplings_app couplings_dp.
From clutch.gen_diffpriv.lib Require Export laplace.
From clutch.gen_prob_lang.spec Require Import spec_ra.
From iris.prelude Require Import options.

Local Open Scope R.

(** [AllocTapeLaplace num den mean] allocates a fresh presampling tape for the
    Laplace family at parameter [(num, den, mean)].  The family's index is read
    off the ambient [SampleIn laplace_family _] instance. *)
Notation AllocTapeLaplace num den mean :=
  (AllocSampleTape (sample_idx (D := laplace_family)) (Pair num (Pair den mean)))
  (only parsing).

(** Typed tape views: a Laplace tape holding presampled outcomes [zs : list Z],
    on the impl ([↪L]) and spec ([↪Lₛ]) tape maps respectively.  Both are sugar
    over the generic tape predicate at index [sample_idx].  The parameter is
    written in the *explicit* value form [PairV #num (PairV #den #mean)] — i.e.
    exactly the shape the proof-mode tactics read off a reduced [Sample] redex —
    so [wp_alloc_sample_tape]/[wp_sample_tape]/[tp_*] match it syntactically.
    (This form is definitionally [sf_param_to_val laplace_family (num,den,mean)];
    the bridge is [laplace_param_to_val] below, used inside the coupling rule.) *)
Notation "α ↪L ( num , den , mean ; zs )" :=
  ((α ↪ (sample_idx (D := laplace_family),
           PairV (LitV (LitInt num)) (PairV (LitV (LitInt den)) (LitV (LitInt mean))),
           ((λ z : Z, LitV (LitInt z)) <$> zs)))%I)
  (at level 20, format "α  ↪L  ( num ,  den ,  mean ;  zs )") : bi_scope.

Notation "α ↪Lₛ ( num , den , mean ; zs )" :=
  ((α ↪ₛ (sample_idx (D := laplace_family),
            PairV (LitV (LitInt num)) (PairV (LitV (LitInt den)) (LitV (LitInt mean))),
            ((λ z : Z, LitV (LitInt z)) <$> zs)))%I)
  (at level 20, format "α  ↪Lₛ  ( num ,  den ,  mean ;  zs )") : bi_scope.

(** The two representations of a Laplace parameter / outcome coincide
    definitionally; these reflexivity lemmas let us [rewrite] between the
    family-level form (produced by [wp_couple_tapes_family]) and the explicit
    value form (used by the tape views and proof-mode tactics). *)
Lemma laplace_param_to_val (num den mean : Z) :
  sf_param_to_val laplace_family (num, den, mean)
  = PairV (LitV (LitInt num)) (PairV (LitV (LitInt den)) (LitV (LitInt mean))).
Proof. reflexivity. Qed.

Lemma laplace_sf_inj (z : Z) : sf_inj laplace_family z = LitV (LitInt z).
Proof. reflexivity. Qed.

Section laplace_tapes.
  Context {S : Sig} `{!SampleIn laplace_family S} `{!diffprivGS S Σ}.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang S)).
  Local Notation lidx := (@sample_idx laplace_family S _).

  (** Allocate a fresh Laplace tape (empty).  The [Pair] parameter reduces by
      [wp_pures] to a value, then the generic allocator fires. *)
  Lemma wp_alloc_tape_laplace (num den mean : Z) E s :
    {{{ True }}}
      AllocTapeLaplace #num #den #mean @ s; E
    {{{ (α : loc), RET (LitV (LitLbl α)); α ↪L (num, den, mean; []) }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_pures.
    iApply (wp_alloc_sample_tape lidx
              (PairV (LitV (LitInt num)) (PairV (LitV (LitInt den)) (LitV (LitInt mean))))
              with "[//]").
    iIntros "!>" (α) "Hα". iApply "HΦ". iFrame.
  Qed.

  (** Read the head presampled outcome off a non-empty Laplace tape
      (deterministic).  The [Pair] parameter reduces by [wp_pures], then the
      generic [wp_sample_tape] fires. *)
  Lemma wp_laplace_tape (num den mean z : Z) (zs : list Z) (α : loc) E s :
    {{{ ▷ α ↪L (num, den, mean; z :: zs) }}}
      Laplace #num #den #mean (#lbl:α) @ s; E
    {{{ RET #z; α ↪L (num, den, mean; zs) }}}.
  Proof.
    iIntros (Φ) ">Hα HΦ".
    wp_pures.
    iApply (wp_sample_tape lidx
              (PairV (LitV (LitInt num)) (PairV (LitV (LitInt den)) (LitV (LitInt mean))))
              (LitV (LitInt z)) ((λ z0 : Z, LitV (LitInt z0)) <$> zs) α with "[Hα]").
    { iFrame. }
    iIntros "!> Hα". iApply "HΦ". iFrame.
  Qed.

  (** The presampling (tape) Laplace coupling: advancing two Laplace tapes with
      a shared draw shifts the spec draw by [k] at multiplicative error [|k'|·ε],
      provided the two means differ by at most [k'] after the shift.  This is the
      generic [wp_couple_tapes_family] instantiated with the single Laplace draw
      coupling [DPcoupl_laplace_draw] — at the index [sample_idx], so one rule
      serves every signature containing [laplace_family]. *)
  Lemma wp_couple_tapes_laplace (mean mean' k k' : Z) α α' zs zs' e Φ
    (Hdist : (Z.abs (k + mean - mean') <= k')%Z)
    (num den : Z) (ε ε' : R) E :
    IZR num / IZR den = ε →
    0 < IZR num / IZR den →
    ε' = (IZR k' * ε) →
    ▷ α ↪L (num, den, mean; zs) ∗ ▷ α' ↪Lₛ (num, den, mean'; zs') ∗ ↯m ε' -∗
    (∀ z, α ↪L (num, den, mean; zs ++ [z]) ∗ α' ↪Lₛ (num, den, mean'; zs' ++ [(z + k)%Z]) -∗
          WP e @ E {{ Φ }}) -∗
    WP e @ E {{ Φ }}.
  Proof.
    iIntros (Hε εpos Hε') "(Hα & Hα' & Hcred) HΦ".
    assert (0 <= ε')%R as Hε'pos.
    { subst ε'. apply Rmult_le_pos; [apply IZR_le; lia | lra]. }
    assert (DPcoupl (sf_sample laplace_family (num, den, mean))
                    (sf_sample laplace_family (num, den, mean'))
                    (λ z z' : Z, (z + k = z')%Z) ε' 0) as Hcpl.
    { rewrite Hε' -Hε. by apply (DPcoupl_laplace_draw num den mean mean' k k' Hdist εpos). }
    iApply (wp_couple_tapes_family S laplace_family (num, den, mean) (num, den, mean')
              α α' ((λ z : Z, LitV (LitInt z)) <$> zs) ((λ z : Z, LitV (LitInt z)) <$> zs')
              (λ z z', (z + k = z')%Z) e Φ ε' E Hε'pos Hcpl with "[Hα Hα' Hcred]").
    { rewrite !laplace_param_to_val. iFrame. }
    iIntros (a a' Ha) "(Hα & Hα')".
    iEval (rewrite laplace_param_to_val) in "Hα".
    iEval (rewrite laplace_param_to_val) in "Hα'".
    iApply ("HΦ" $! a). rewrite Ha !fmap_app. iFrame.
  Qed.

End laplace_tapes.

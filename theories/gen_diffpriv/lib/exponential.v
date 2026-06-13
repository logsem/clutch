(** Reusable one-sided-exponential-noise library for the generic DP logic — the
    exponential-mechanism analogue of [lib.laplace].

    Importing this file and providing a [SampleIn exp_family S] instance makes
    the [Exp] surface notation and the [wp_couple_exp] mechanism rule available
    at WHATEVER index the family occupies in [S] (recovered from [SampleIn] via
    [sample_idx], never hardcoded).  As with [lib.laplace], a client needs only:
      Definition Sexp : Sig := [...; exp_family; ...].
      #[global] Instance : SampleIn exp_family Sexp := ltac:(solve_SampleIn).
      Section foo. Context `{!diffprivGS Sexp Σ}.
    and then writes [Exp num den mean] in programs and applies [wp_couple_exp].

    The ONLY mathematical difference from the Laplace library is the per-draw
    coupling [DPcoupl_exp_draw]: the one-sided exponential supports the shift
    coupling [z' = z + k] only when the shift is *upward* enough to stay in the
    (one-sided) target support — [0 ≤ k + loc - loc'] — and the cost is then
    [(k+loc-loc')]-bounded, [k + loc - loc' ≤ k'] giving cost [k'·ε].  Contrast
    Laplace (two-sided): it needs only [|k+loc-loc'| ≤ k'] and no directionality.
    This directionality is exactly what makes it the exponential mechanism. *)
From iris.proofmode Require Import proofmode.
From clutch.prob Require Import differential_privacy distribution exponential couplings couplings_app couplings_dp.
From clutch.gen_diffpriv Require Export primitive_laws coupling_rules proofmode.
From clutch.gen_prob_lang Require Export families.
From iris.prelude Require Import options.

Local Open Scope R.

(** [Exp num den mean tape] samples the one-sided exponential family at
    parameter [(num, den, mean)] using sample tape [tape] ([#()] for a direct,
    tape-less sample).  Same 4-argument surface form as [Laplace]; the family's
    index in the ambient signature is recovered from [SampleIn exp_family _]. *)
Notation Exp num den mean tape :=
  (Sample (sample_idx (D := exp_family)) (Pair num (Pair den mean)) tape)
  (only parsing).

Section exponential.
  Context {S : Sig} `{!SampleIn exp_family S} `{!diffprivGS S Σ}.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang S)).
  (* the family's index in [S], recovered from the [SampleIn] instance *)
  Local Notation lidx := (@sample_idx exp_family S _).

  (** The core one-sided-exponential draw coupling, on the family's outcome type
      [Z]: shifting the location by [k] couples [z ↦ z + k] at cost [k'·ε] when
      the shift is upward into the target support ([0 ≤ k+loc-loc']) and bounded
      ([k+loc-loc' ≤ k']).  Family-level fact (independent of [S]), discharged by
      the reusable [Mcoupl_exp]. *)
  Lemma DPcoupl_exp_draw (num den loc loc' k k' : Z)
    (Hdir : (0 <= k + loc - loc')%Z)
    (Hdist : (k + loc - loc' <= k')%Z)
    (Hpos : (0 < IZR num / IZR den)%R) :
    DPcoupl (sf_sample exp_family (num, den, loc))
            (sf_sample exp_family (num, den, loc'))
            (λ z z', (z + k = z')%Z) (IZR k' * (IZR num / IZR den)) 0.
  Proof.
    simpl. rewrite /exp_rat.
    destruct (decide (0 < IZR num / IZR den)) as [εpos | nε]; [|lra].
    apply Mcoupl_to_DPcoupl.
    by apply (Mcoupl_exp (mkposreal _ εpos) loc loc' k k' Hdir Hdist).
  Qed.

  (** The one-sided exponential mechanism at the WP level: sampling at location
      [loc] (impl) vs [loc'] (spec) couples to outputs that agree after shifting
      the spec by [k], at multiplicative error [k'·ε], under the one-sided
      directionality.  Obtained by instantiating the GENERIC prog-couple seam
      [wp_couple_sample_gen] with [DPcoupl_exp_draw] at index [sample_idx]. *)
  Lemma wp_couple_exp (loc loc' k k' : Z)
    (Hdir : (0 <= k + loc - loc')%Z)
    (Hdist : (k + loc - loc' <= k')%Z)
    (num den : Z) (ε ε' : R) K E :
    IZR num / IZR den = ε →
    0 < IZR num / IZR den →
    ε' = (IZR k' * ε) →
    {{{ ⤇ fill K (Sample lidx
                    (Val (PairV (LitV (LitInt num))
                            (PairV (LitV (LitInt den)) (LitV (LitInt loc')))))
                    (Val (LitV LitUnit))) ∗ ↯m ε' }}}
      Sample lidx
        (Val (PairV (LitV (LitInt num))
                (PairV (LitV (LitInt den)) (LitV (LitInt loc)))))
        (Val (LitV LitUnit)) @ E
      {{{ (z : Z), RET #z; ⤇ fill K #(z + k) }}}.
  Proof.
    iIntros (Hε εpos Hε' Φ) "(Hr & Hε) HΦ".
    iApply (wp_couple_sample_gen S lidx
              (sf_param_to_val exp_family (num, den, loc))
              (sf_param_to_val exp_family (num, den, loc'))
              (dmap (sf_inj exp_family) (sf_sample exp_family (num, den, loc)))
              (dmap (sf_inj exp_family) (sf_sample exp_family (num, den, loc')))
              (λ v v', ∃ z : Z, v = #z ∧ v' = #(z + k)) K E ε'
              (sig_sample_at exp_family S (num, den, loc))
              (sig_sample_at exp_family S (num, den, loc')) _ with "[$Hr $Hε]").
    { iIntros "!>" (v v') "(Hspec & %HR)". destruct HR as (z & -> & ->).
      iApply ("HΦ" $! z with "Hspec"). }
    (* the single DP obligation: lift the exponential draw coupling through sf_inj *)
    Unshelve.
    apply DPcoupl_map; [subst ε'; apply Rmult_le_pos; [apply IZR_le; lia | lra] | lra | ].
    eapply (DPcoupl_mono _ _ _ _ (λ z z', (z + k = z')%Z) _ ε' ε' 0 0);
      [ intros; reflexivity
      | intros; reflexivity
      | intros z z' Hzz'; exists z; split; [done | by rewrite Hzz']
      | lra | lra
      | subst ε'; rewrite -Hε; by apply DPcoupl_exp_draw ].
  Qed.

  (** The surface-form exponential coupling rule, stated on the [Exp] notation
      (with the [(num,den,loc)] parameter as an un-reduced [Pair]). *)
  Lemma hoare_couple_exp (loc loc' k k' : Z)
    (Hdir : (0 <= k + loc - loc')%Z)
    (Hdist : (k + loc - loc' <= k')%Z)
    (num den : Z) (ε ε' : R) K E :
    IZR num / IZR den = ε →
    0 < IZR num / IZR den →
    ε' = (IZR k' * ε) →
    {{{ ⤇ fill K (Exp #num #den #loc' #()) ∗ ↯m ε' }}}
      Exp #num #den #loc #() @ E
      {{{ (z : Z), RET #z; ⤇ fill K #(z + k) }}}.
  Proof.
    iIntros (Hε εpos Hε' Φ) "(Hr & Hε) HΦ".
    wp_pures. tp_pures.
    iApply (wp_couple_exp loc loc' k k' Hdir Hdist num den ε ε' K E Hε εpos Hε'
              with "[$Hr $Hε]").
    iApply "HΦ".
  Qed.

  (** The exact (error-free) coupling: identical locations couple perfectly
      along the diagonal at zero cost (the reflexive coupling [ARcoupl_eq]
      lifted to [DPcoupl]).  No directionality needed here ([k = 0]). *)
  Lemma hoare_couple_exp_exact (loc num den : Z) K E :
    {{{ ⤇ fill K (Exp #num #den #loc #()) }}}
      Exp #num #den #loc #() @ E
      {{{ (z : Z), RET #z; ⤇ fill K #z }}}.
  Proof.
    iIntros (Φ) "Hr HΦ".
    wp_pures. tp_pures.
    iMod ecm_zero as "Hε".
    iApply (wp_couple_sample_gen S lidx
              (sf_param_to_val exp_family (num, den, loc))
              (sf_param_to_val exp_family (num, den, loc))
              (dmap (sf_inj exp_family) (sf_sample exp_family (num, den, loc)))
              (dmap (sf_inj exp_family) (sf_sample exp_family (num, den, loc)))
              (λ v v', ∃ z : Z, v = #z ∧ v' = #z) K E 0
              (sig_sample_at exp_family S (num, den, loc))
              (sig_sample_at exp_family S (num, den, loc)) _ with "[$Hr $Hε]").
    { iIntros "!>" (v v') "(Hspec & %HR)". destruct HR as (z & -> & ->).
      iApply ("HΦ" $! z with "Hspec"). }
    (* the reflexive coupling of the exponential draw, lifted through sf_inj *)
    Unshelve.
    apply (DPcoupl_map (sf_inj exp_family) (sf_inj exp_family)
             (sf_sample exp_family (num, den, loc)) (sf_sample exp_family (num, den, loc))
             (λ v v', ∃ z : Z, v = #z ∧ v' = #z) 0 0); [lra | lra | ].
    eapply (DPcoupl_mono (sf_sample exp_family (num, den, loc))
              (sf_sample exp_family (num, den, loc))
              (sf_sample exp_family (num, den, loc))
              (sf_sample exp_family (num, den, loc))
              (=) (λ a a', ∃ z : Z, sf_inj exp_family a = #z ∧ sf_inj exp_family a' = #z)
              0 0 0 0);
      [ intros; reflexivity | intros; reflexivity
      | intros a a' ->; by exists a' | lra | lra
      | apply ARcoupl_to_DPcoupl, ARcoupl_eq ].
  Qed.

End exponential.

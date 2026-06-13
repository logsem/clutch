(** Reusable discrete-Laplace library for the generic DP logic.

    Importing this file and providing a [SampleIn laplace_family S] instance
    makes the [Laplace] surface notation and the [wp_couple_laplace] mechanism
    rule available at WHATEVER index the family occupies in the signature [S] —
    the index is recovered from the [SampleIn] instance via [sample_idx], never
    hardcoded.  No per-development canonical-structure or [spec_updateGS]
    boilerplate is required: the WP elaborates through the ∀S canonical chain
    (pinned by the in-context [diffprivGS]) and the spec layer resolves through
    the [diffprivGS_spec_updateGS] instance.

    A client development therefore needs only:
      Definition Slap : Sig := [...; laplace_family; ...].
      #[global] Instance : SampleIn laplace_family Slap := ltac:(solve_SampleIn).
      Section foo. Context `{!diffprivGS Slap Σ}.
    and then writes [Laplace num den mean] in programs and applies
    [wp_couple_laplace] in proofs. *)
From iris.proofmode Require Import proofmode.
From clutch.prob Require Import differential_privacy distribution couplings_dp.
(* re-export the client-facing layer so [Require Import laplace] alone provides
   the WP rules, coupling seams, proof-mode tactics, notation and families *)
From clutch.gen_diffpriv Require Export primitive_laws coupling_rules proofmode.
From clutch.gen_prob_lang Require Export families.
From iris.prelude Require Import options.

Local Open Scope R.

(** [Laplace num den mean] samples the Laplace family at parameter
    [(num, den, mean)].  The family's position in the ambient signature is
    recovered from the [SampleIn laplace_family _] instance — NOT hardcoded. *)
Notation Laplace num den mean :=
  (Sample (sample_idx (D := laplace_family)) (Pair num (Pair den mean))
          (Val (LitV LitUnit))) (only parsing).

Section laplace.
  Context {S : Sig} `{!SampleIn laplace_family S} `{!diffprivGS S Σ}.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang S)).
  (* the family's index in [S], recovered from the [SampleIn] instance *)
  Local Notation lidx := (@sample_idx laplace_family S _).

  (** The core Laplace draw coupling, on the family's outcome type [Z]:
      shifting the location by [k] costs [|k'| · ε] error when the two locations
      differ by at most [k'].  Family-level fact (independent of [S]),
      discharged by the reusable [Mcoupl_laplace]. *)
  Lemma DPcoupl_laplace_draw (num den loc loc' k k' : Z)
    (Hdist : (Z.abs (k + loc - loc') <= k')%Z)
    (Hpos : (0 < IZR num / IZR den)%R) :
    DPcoupl (sf_sample laplace_family (num, den, loc))
            (sf_sample laplace_family (num, den, loc'))
            (λ z z', (z + k = z')%Z) (IZR k' * (IZR num / IZR den)) 0.
  Proof.
    simpl. rewrite /laplace_rat.
    destruct (decide (0 < IZR num / IZR den)) as [εpos | nε]; [|lra].
    apply Mcoupl_to_DPcoupl.
    by apply (Mcoupl_laplace (mkposreal _ εpos) loc loc' k k' Hdist).
  Qed.

  (** The Laplace mechanism is ε-DP at the WP level: sampling at location [loc]
      (impl) vs [loc'] (spec) couples to outputs that agree after shifting the
      spec by [k], at multiplicative error [|k'|·ε].  Obtained by instantiating
      the GENERIC prog-couple seam [wp_couple_sample_gen] with the single Laplace
      draw coupling [DPcoupl_laplace_draw] — at the index [sample_idx], so this
      one rule serves every signature containing [laplace_family]. *)
  Lemma wp_couple_laplace (loc loc' k k' : Z)
    (Hdist : (Z.abs (k + loc - loc') <= k')%Z)
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
              (sf_param_to_val laplace_family (num, den, loc))
              (sf_param_to_val laplace_family (num, den, loc'))
              (dmap (sf_inj laplace_family) (sf_sample laplace_family (num, den, loc)))
              (dmap (sf_inj laplace_family) (sf_sample laplace_family (num, den, loc')))
              (λ v v', ∃ z : Z, v = #z ∧ v' = #(z + k)) K E ε'
              (sig_sample_at laplace_family S (num, den, loc))
              (sig_sample_at laplace_family S (num, den, loc')) _ with "[$Hr $Hε]").
    { iIntros "!>" (v v') "(Hspec & %HR)". destruct HR as (z & -> & ->).
      iApply ("HΦ" $! z with "Hspec"). }
    (* the single DP obligation: lift the Laplace draw coupling through sf_inj *)
    Unshelve.
    apply DPcoupl_map; [subst ε'; apply Rmult_le_pos; [apply IZR_le; lia | lra] | lra | ].
    eapply (DPcoupl_mono _ _ _ _ (λ z z', (z + k = z')%Z) _ ε' ε' 0 0);
      [ intros; reflexivity
      | intros; reflexivity
      | intros z z' Hzz'; exists z; split; [done | by rewrite Hzz']
      | lra | lra
      | subst ε'; rewrite -Hε; by apply DPcoupl_laplace_draw ].
  Qed.

End laplace.

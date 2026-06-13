(** A differential-privacy example on the GENERIC language: the Laplace
    mechanism is ε-DP.  Demonstrates that instantiating the generic
    coupling seam [wp_couple_sample_gen] for the Laplace family (one
    [DPcoupl] obligation, discharged by the reusable [Mcoupl_laplace]) is all
    that is needed to run a real DP proof — no per-distribution re-clone of
    the program logic. *)
From iris.proofmode Require Import proofmode environments coq_tactics ltac_tactics reduction.
From clutch.prob Require Import differential_privacy distribution couplings_dp.
From clutch.gen_diffpriv Require Import primitive_laws coupling_rules proofmode adequacy.
From clutch.gen_prob_lang Require Import families.
From iris.prelude Require Import options.

Local Open Scope R.

(** The signature: a single Laplace family. *)
Definition Slap : Sig := [laplace_family].
#[global] Instance SampleIn_laplace : SampleIn laplace_family Slap.
Proof. refine {| sample_idx := 0 |}. reflexivity. Defined.

(** Surface sugar: [Laplace num den loc] samples from the Laplace family at
    parameter [(num, den, loc)] (encoded as the pair value). *)
Notation Laplace num den loc :=
  (Sample 0 (Pair num (Pair den loc)) (Val (LitV LitUnit))) (only parsing).

Section laplace.
  Context `{!diffprivGS Slap Σ}.
  Canonical Structure gen_ectxi_lang_lap := gen_ectxi_lang Slap.
  Canonical Structure gen_ectx_lang_lap := gen_ectx_lang Slap.
  Canonical Structure gen_lang_lap := gen_lang Slap.
  Canonical Structure gen_markov_lap := lang_markov (gen_lang Slap).
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Slap)).
  #[local] Existing Instance spec_rules_spec_updateGS.
  #[local] Instance spec_updateGS_lap : spec_updateGS gen_markov_lap Σ :=
    spec_rules_spec_updateGS Slap.

  (** The core Laplace draw coupling, on the family's outcome type [Z]:
      shifting the location by [k] costs [|k'| · ε] error when the two locations
      differ by at most [k']. Discharged by the reusable [Mcoupl_laplace]. *)
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

  (** The Laplace mechanism is ε-DP at the WP level: sampling from the Laplace
      family at location [loc] (impl) vs [loc'] (spec) couples to outputs that
      agree after shifting the spec by [k], at multiplicative error [|k'|·ε].
      This per-family rule is obtained by instantiating the GENERIC prog-couple
      seam [wp_couple_sample_gen] with the single Laplace draw coupling
      [DPcoupl_laplace_draw] — no re-clone of the program logic. *)
  Lemma wp_couple_laplace (loc loc' k k' : Z)
    (Hdist : (Z.abs (k + loc - loc') <= k')%Z)
    (num den : Z) (ε ε' : R) K E :
    IZR num / IZR den = ε →
    0 < IZR num / IZR den →
    ε' = (IZR k' * ε) →
    {{{ ⤇ fill K (Sample 0 (Val (PairV (LitV (LitInt num)) (PairV (LitV (LitInt den)) (LitV (LitInt loc'))))) (Val (LitV LitUnit))) ∗ ↯m ε' }}}
      Sample 0 (Val (PairV (LitV (LitInt num)) (PairV (LitV (LitInt den)) (LitV (LitInt loc))))) (Val (LitV LitUnit)) @ E
      {{{ (z : Z), RET #z; ⤇ fill K #(z + k) }}}.
  Proof.
    iIntros (Hε εpos Hε' Φ) "(Hr & Hε) HΦ".
    assert (Hss : sig_sample Slap 0 (sf_param_to_val laplace_family (num, den, loc))
                  = Some (dmap (sf_inj laplace_family) (sf_sample laplace_family (num, den, loc))))
      by exact (sig_sample_at laplace_family Slap (num, den, loc)).
    assert (Hss' : sig_sample Slap 0 (sf_param_to_val laplace_family (num, den, loc'))
                   = Some (dmap (sf_inj laplace_family) (sf_sample laplace_family (num, den, loc'))))
      by exact (sig_sample_at laplace_family Slap (num, den, loc')).
    iApply (wp_couple_sample_gen Slap 0
              (sf_param_to_val laplace_family (num, den, loc))
              (sf_param_to_val laplace_family (num, den, loc'))
              (dmap (sf_inj laplace_family) (sf_sample laplace_family (num, den, loc)))
              (dmap (sf_inj laplace_family) (sf_sample laplace_family (num, den, loc')))
              (λ v v', ∃ z : Z, v = #z ∧ v' = #(z + k)) K E ε'
              Hss Hss' _ with "[$Hr $Hε]").
    { (* the continuation *)
      iIntros "!>" (v v') "(Hspec & %HR)". destruct HR as (z & -> & ->).
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

  (** Parity check: the STANDARD [wp_pures] now reduces pure redexes — the
      [gen_diffpriv.proofmode] [gwp_get_sig] override reads [Slap] off the
      [diffprivGS] hypothesis, so no [_gen] variant is needed. *)
  Lemma wp_pure_test (z : Z) E (Φ : val → iProp Σ) : Φ #z -∗ WP ((λ: "x", "x")%V #z) @ E {{ Φ }}.
  Proof. iIntros "H". wp_pures. iApply "H". Qed.

  (** The full λ-program differential-privacy statement: the one-line Laplace
      mechanism [λ loc, Laplace(num/den, loc)] is ε-DP for 1-sensitive inputs
      (|loc − loc'| ≤ 1).  This is the end-to-end usability target — it is proved
      with the STANDARD proof-mode tactics ([wp_pures] on the implementation,
      [tp_pures] on the specification, [iApply] of the per-family coupling rule),
      exactly as one writes a [prob_lang] proof.  No [_gen] tactic variants, no
      manual signature threading: the [gen_diffpriv.proofmode] [gwp_get_sig] /
      [tp_get_sig] overrides recover the signature [Slap] automatically.  This is
      the parity demonstration: porting a real DP case study costs the same as
      it did before generalisation. *)
  Lemma wp_laplace_diffpriv (loc loc' num den : Z) (ε : R) K E :
    IZR num / IZR den = ε →
    0 < IZR num / IZR den →
    (Z.abs (loc - loc') <= 1)%Z →
    {{{ ⤇ fill K ((λ: "l", Laplace #num #den "l")%V #loc') ∗ ↯m ε }}}
      (λ: "l", Laplace #num #den "l")%V #loc @ E
    {{{ (z : Z), RET #z; ⤇ fill K #z }}}.
  Proof.
    iIntros (Hε εpos Hsens Φ) "(Hr & Hε) HΦ".
    wp_pures.
    tp_pures.
    (* reduce to the single Laplace draw; couple with shift [k = 0] at
       sensitivity [k' = 1], so the cost is [|1|·ε = ε] *)
    iApply (wp_couple_laplace loc loc' 0%Z 1%Z _ num den ε ε K E Hε εpos _ with "[$Hr $Hε]").
    iModIntro. iIntros (z) "Hr".
    replace (z + 0)%Z with z by lia.
    iApply ("HΦ" with "Hr").
    Unshelve.
    - (* the [k=0] shift respects 1-sensitivity *)
      replace (0 + loc - loc')%Z with (loc - loc')%Z by lia. exact Hsens.
    - (* the multiplicative error: [ε = |1|·ε] *)
      simpl; lra.
  Qed.

End laplace.

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
From clutch.gen_prob_lang.spec Require Import spec_tactics.
From clutch.gen_prob_lang Require Import tactics wp_tactics notation lang.
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

(** A signature-pinning [wp_pures]: the generic [wp_pures] cannot infer the
    distribution signature [S] for the ∀S [PureExec] instances (S lives in the
    [Wp] instance, not the syntax).  This variant reads [S] off the in-context
    [diffprivGS S _] hypothesis and passes it positionally to
    [tac_wp_pure_later]. *)
Ltac wp_pure_gen :=
  iStartProof;
  lazymatch goal with
  | _ : diffprivGS ?S _ |- envs_entails _ (wp ?a ?E ?e ?Q) =>
      let e' := eval simpl in e in
      reshape_expr e' ltac:(fun K eredex =>
        eapply (tac_wp_pure_later S _ _ _ E K eredex);
        [ tc_solve | try (split_and?; reflexivity) ; try done | tc_solve | simpl ])
  end.
Ltac wp_pures_gen := iStartProof; repeat (wp_pure_gen; []).

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

  (* diagnostic: does wp_pures reduce a lambda application here? *)
  (** Sanity check that the signature-pinned [wp_pures_gen] reduces pure redexes
      (a λ-application) — the impl-side reduction needed by full DP programs. *)
  Lemma wp_pure_test (z : Z) E (Φ : val → iProp Σ) : Φ #z -∗ WP ((λ: "x", "x")%V #z) @ E {{ Φ }}.
  Proof. iIntros "H". wp_pures_gen. iApply (wp_value' (Λ := gen_lang Slap)). iApply "H". Qed.

End laplace.

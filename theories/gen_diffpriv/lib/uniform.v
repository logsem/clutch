(** Reusable uniform-sampling library for the generic DP logic.

    Importing this file and providing a [SampleIn uniform_family S] instance makes
    the [Uniform] surface notation and the [wp_couple_uniform] mechanism rule
    available at WHATEVER index the family occupies in the signature [S] — the
    index is recovered from the [SampleIn] instance via [sample_idx], never
    hardcoded (mirroring [lib/laplace.v]).

    The headline content is the 0-cost SHIFT coupling: two uniform draws on
    [{0,…,N}] couple exactly (no [ε], no [δ]) with the spec output equal to the
    impl output rotated by [k] mod [N+1].  This is the foundation on which the
    δ-bearing collision-avoidance variants (deferred to the crypto port) build.

    A client development therefore needs only:
      Definition Suni : Sig := [...; uniform_family; ...].
      #[global] Instance : SampleIn uniform_family Suni := ltac:(solve_SampleIn).
      Section foo. Context `{!diffprivGS Suni Σ}.
    and then writes [Uniform #N #()] in programs and applies [wp_couple_uniform]
    in proofs. *)
From Stdlib Require Import ZArith.
From iris.proofmode Require Import proofmode.
From clutch.prob Require Import differential_privacy distribution couplings couplings_app couplings_dp.
(* re-export the client-facing layer so [Require Import uniform] alone provides
   the WP rules, coupling seams, proof-mode tactics, notation and families. *)
From clutch.gen_diffpriv Require Export primitive_laws coupling_rules proofmode diffpriv_rules.
From clutch.gen_prob_lang Require Export families.
From iris.prelude Require Import options.

Local Open Scope R.

(** [Uniform N tape] samples the uniform family at parameter [N] (a [Z] literal,
    the inclusive bound) using sample tape [tape] ([#()] for a direct, tape-less
    sample).  The family's index in the ambient signature is recovered from the
    [SampleIn uniform_family _] instance — NOT hardcoded. *)
Notation Uniform N tape :=
  (Sample (sample_idx (D := uniform_family)) N tape)
  (only parsing).

(** Value-form of [Uniform] (direct, tape-less): the bound already reduced to a
    [LitV (LitInt _)], as it appears AFTER [wp_pures]/[tp_pures].  The coupling
    rules below are stated on [UniformV] so their preconditions match
    post-reduction goals; the [couple_uniform] tactic relies on this shape. *)
Notation UniformV N :=
  (Sample (sample_idx (D := uniform_family))
     (Val (LitV (LitInt N))) (Val (LitV LitUnit)))
  (only parsing).

Section uniform.
  Context {Sg : Sig} `{!SampleIn uniform_family Sg} `{!diffprivGS Sg Σ}.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Sg)).
  (* the family's index in [Sg], recovered from the [SampleIn] instance *)
  Local Notation uidx := (@sample_idx uniform_family Sg _).

  (** The core uniform draw shift coupling, on the family's outcome type [Z]:
      shifting the draw by [k] couples the two draws EXACTLY (cost [(0,0)]), with
      the spec output equal to the impl output rotated by [k] mod [N+1] (and the
      impl output recorded in range [0,N]).  Family-level fact (independent of
      [Sg]), discharged by the reusable [DPcoupl_dunifP_shift]. *)
  Lemma DPcoupl_uniform_draw (N : nat) (k : Z) :
    DPcoupl (sf_sample uniform_family N)
            (sf_sample uniform_family N)
            (λ z z', z' = (z + k) `mod` Z.of_nat (S N) ∧ 0 <= z <= Z.of_nat N)%Z 0 0.
  Proof. simpl. apply DPcoupl_dunifP_shift. Qed.

  (** The uniform-shift mechanism at the WP level: sampling at bound [z] (impl)
      vs the same bound [z] (spec), both [Z] literals [#z] with [0 ≤ z], couples
      to outputs related by the cyclic shift [out' = (out + k) mod (z+1)], at ZERO
      cost (no [↯m], no [↯]).  Obtained by instantiating the generic prog-couple
      seam [wp_couple_sample_gen] with [DPcoupl_uniform_draw] — at the recovered
      index [uidx], so this one rule serves every signature containing
      [uniform_family]. *)
  Lemma wp_couple_uniform (z k : Z) K E :
    (0 <= z)%Z →
    {{{ ⤇ fill K (Sample uidx (Val (LitV (LitInt z))) (Val (LitV LitUnit))) }}}
      Sample uidx (Val (LitV (LitInt z))) (Val (LitV LitUnit)) @ E
      {{{ (out : Z), RET #out;
          ⤇ fill K #((out + k) `mod` (z + 1))%Z ∗ ⌜(0 <= out <= z)%Z⌝ }}}.
  Proof.
    iIntros (Hz Φ) "Hr HΦ".
    iMod ecm_zero as "Hε".
    (* [z = Z.of_nat (Z.to_nat z)] under [0 ≤ z], so the value param [#z] equals
       [sf_param_to_val uniform_family (Z.to_nat z)]; rewrite the WHOLE goal to
       [N] so the program subject matches the [wp_couple_sample_gen] rule. *)
    set (N := Z.to_nat z).
    assert (HzN : z = Z.of_nat N) by (subst N; rewrite Z2Nat.id //).
    rewrite HzN.
    assert (Hbound : (Z.of_nat (S N) = Z.of_nat N + 1)%Z) by (rewrite Nat2Z.inj_succ; lia).
    iApply (wp_couple_sample_gen Sg uidx
              (sf_param_to_val uniform_family N)
              (sf_param_to_val uniform_family N)
              (dmap (sf_inj uniform_family) (sf_sample uniform_family N))
              (dmap (sf_inj uniform_family) (sf_sample uniform_family N))
              (λ v v', ∃ out : Z, v = #out ∧ v' = #((out + k) `mod` (Z.of_nat N + 1))%Z
                                  ∧ (0 <= out <= Z.of_nat N)%Z) K E 0
              (sig_sample_at uniform_family Sg N)
              (sig_sample_at uniform_family Sg N) _ with "[Hr Hε]").
    { (* the param value [#N] matches [sf_param_to_val uniform_family N] *)
      simpl. iFrame. }
    { iIntros "!>" (v v') "(Hspec & %HR)".
      destruct HR as (out & -> & -> & Hb). iApply ("HΦ" $! out with "[$Hspec //]"). }
    (* the single DP obligation: lift the uniform draw coupling through sf_inj *)
    Unshelve.
    apply DPcoupl_map; [lra | lra | ].
    eapply (DPcoupl_mono _ _ _ _
              (λ z0 z', z' = (z0 + k) `mod` Z.of_nat (S N) ∧ 0 <= z0 <= Z.of_nat N)%Z
              _ 0 0 0 0).
    - intros; reflexivity.
    - intros; reflexivity.
    - intros x y (Hxy & Hrange). exists x. simpl.
      split; [reflexivity|]. rewrite Hxy Hbound. split; [reflexivity | exact Hrange].
    - lra.
    - lra.
    - apply DPcoupl_uniform_draw.
  Qed.

End uniform.

(** [couple_uniform k with "[…]"] — the ergonomic coupling step.  It reduces the
    bound to a [LitV (LitInt _)] literal ([wp_pures]/[tp_pures]), focuses the
    [Sample] on both sides ([wp_bind]/[tp_bind]), and applies the value-form
    [wp_couple_uniform] inferring [z/K/E] from the goal — the author supplies only
    the privacy choice [k] (cyclic shift) and the resource pattern.  The single
    side-condition ([0 ≤ z], the bound's nonnegativity) is auto-discharged best
    effort ([lia]/[done]); the postcondition continuation is the single remaining
    goal.  Mirrors [couple_laplace]. *)
Tactic Notation "couple_uniform" uconstr(k) "with" constr(pat) :=
  wp_pures; tp_pures;
  wp_bind (Sample _ _ _); tp_bind (Sample _ _ _);
  (* [unshelve] (the tactical) turns the goal THIS [iApply] shelves — only the
     [0 ≤ z] side-condition — into a regular front goal, without globally
     un-shelving unrelated goals the way the [Unshelve] command would. *)
  unshelve (iApply (wp_couple_uniform _ k _ _ _ with pat));
  (* best-effort discharge of [0 ≤ z]; the postcondition continuation is the
     single goal left *)
  try first [ lia | done | (simpl; lia) ].

Section uniform_canary.
  Context {Sg : Sig} `{!SampleIn uniform_family Sg} `{!diffprivGS Sg Σ}.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Sg)).

  (** CANARY: two surface-form [Uniform #N #()] draws couple, at zero cost, with
      the spec output the impl output cyclically shifted by [k] mod [N+1] — driven
      entirely by the [couple_uniform] tactic.  Stated over the [Uniform] notation
      (i.e. [expr], with an un-reduced bound) so it exercises the surface path a
      program takes; demonstrates the convenience layer end to end. *)
  Lemma wp_uniform_shift_canary (N k : Z) K E :
    (0 <= N)%Z →
    {{{ ⤇ fill K (Uniform #N #()) }}}
      Uniform #N #() @ E
      {{{ (out : Z), RET #out;
          ⤇ fill K #((out + k) `mod` (N + 1))%Z ∗ ⌜(0 <= out <= N)%Z⌝ }}}.
  Proof.
    iIntros (HN Φ) "Hr HΦ".
    (* the whole proof is one ergonomic coupling step: [couple_uniform] reduces
       the bound, focuses the [Sample]s, applies [wp_couple_uniform], discharges
       the [0 ≤ N] side-condition, and unifies the postcondition with [HΦ]. *)
    couple_uniform k with "[$Hr]".
  Qed.

End uniform_canary.

(** [wp_*] proof-mode tactic instances for the generic DP weakest precondition.
    Ported from [diffpriv/proofmode]; provides the base/bind/pure [GwpTactics]
    instances at [gen_lang Sg], enough for [wp_pures]/[wp_bind].  (The heap
    instance needs the [↦∗] array layer from [derived_laws]; the sampling tape
    tactic class is deferred — relational sampling goes through coupling rules.) *)
From clutch.diffpriv Require Import weakestpre lifting.
From clutch.gen_diffpriv Require Import primitive_laws model.
From clutch.gen_diffpriv Require Export derived_laws.
From clutch.gen_prob_lang Require Export wp_tactics.
From clutch.gen_prob_lang.spec Require Export spec_tactics.
From clutch.gen_prob_lang Require Export tactics notation lang.
From clutch.gen_prob_lang Require Import class_instances.
From iris.prelude Require Import options.

Section gen_proofmode.
  Context (Sg : Sig).
  Context `{!diffprivGS Sg Σ}.

  #[global] Program Instance diffpriv_wptactics_base : GwpTacticsBase Σ unit wp.
  Next Obligation. intros. by apply wp_value. Qed.
  Next Obligation. intros. by apply wp_fupd. Qed.

  #[global] Program Instance diffpriv_wptactics_bind : GwpTacticsBind Sg Σ unit wp.
  Next Obligation. intros. by apply wp_bind. Qed.

  #[global] Program Instance diffpriv_wptactics_pure : GwpTacticsPure Sg Σ unit true wp.
  Next Obligation. intros. by eapply wp_pure_step_later. Qed.

  #[global] Program Instance diffpriv_wptactics_heap : GwpTacticsHeap Σ unit true wp :=
    Build_GwpTacticsHeap _ _ _ _ (λ l q v, (l ↦{q} v)%I) (λ l q vs, (l ↦∗{q} vs)%I) _ _ _ _.
  Next Obligation. intros. by apply wp_alloc. Qed.
  Next Obligation. intros. by apply wp_allocN. Qed.
  Next Obligation. intros. by apply wp_deref. Qed.
  Next Obligation. intros. by apply wp_store. Qed.

  (** Sample-tape tactic instance: enables [wp_alloc_sample_tape]/[wp_sample_tape]
      on the *raw* generic tape predicate [l ↪ (i, pv, xs)].  As in [prob_lang]'s
      [GwpTacticsTapes] instance, the fractional argument is ignored (reading the
      head consumes it, so the deterministic-read rules require full ownership);
      the obligations are discharged directly from [wp_alloc_sample_tape] and
      [wp_sample_tape]. *)
  #[global] Program Instance diffpriv_wptactics_sample_tape : GwpTacticsSampleTape Σ unit true wp :=
    Build_GwpTacticsSampleTape _ _ _ _ (λ l _q i pv xs, (l ↪ (i, pv, xs))%I) _ _.
  Next Obligation. intros. by apply wp_alloc_sample_tape. Qed.
  Next Obligation. intros. by apply wp_sample_tape. Qed.

End gen_proofmode.

(** ** Signature-resolution overrides for usability parity.

    The distribution signature [S] lives in the [Wp]/[spec_update] instance, not
    in the (signature-independent) [expr]/[val] syntax, so the generic
    [wp_pure]/[tp_pure] machinery cannot recover it by unification — leaving the
    [S]-parametric [PureExec] instance unresolvable.  Both tactic families route
    [S] through an overridable hook ([gwp_get_sig] / [tp_get_sig]); here we
    redefine those hooks (globally, via [::=], so the effect is independent of
    later [Import] order) to read [S] off the in-context [diffprivGS S _]
    hypothesis.  After this, the *standard* [wp_pures]/[tp_pures] and every
    derived tactic ([wp_rec], [tp_load], …) work verbatim in any
    [diffprivGS]-development — achieving tactic parity with [prob_lang]. *)

Ltac gwp_get_sig k ::=
  lazymatch goal with
  | _ : diffprivGS ?S _ |- _ => k S
  | _ : diffprivRGS ?S _ |- _ => k S
  | _ => k open_constr:(_)
  end.

Ltac tp_get_sig k ::=
  lazymatch goal with
  | |- environments.envs_entails _
         (@spec_update.spec_update (lang_markov (gen_lang ?S)) _ _ _ _ _ _) => k S
  | _ : diffprivGS ?S _ |- _ => k S
  | _ : diffprivRGS ?S _ |- _ => k S
  end.

(** ** Shared skeleton for the noise-family coupling tactics

    The per-family convenience tactics ([couple_laplace] / [couple_exp] /
    [couple_trunc_laplace] and their [_apply] variants in [lib.laplace] /
    [lib.exponential] / [lib.trunc_laplace]) all share the same skeleton, which
    varies on only two axes: whether to focus the [Sample] on both sides first
    ([couple_bind]), and which best-effort side-condition battery to run after
    the [unshelve (iApply (wp_couple_X …))] step.  The two batteries below are
    family-agnostic; each library adds only a thin [couple_*_iapply] wrapping its
    own coupling-rule [iApply], then assembles the bundled and apply-only tactics
    from these shared pieces.  See [lib.laplace] for the full design rationale. *)

(** [couple_bind] — the shared leading focus run by the bundled [couple_X]
    tactics: reduce the [Pair] params to a [PairV] tree ([wp_pures]/[tp_pures])
    and focus the [Sample] on both sides ([wp_bind]/[tp_bind]).  SKIPPED by the
    [couple_X_apply] variants, whose caller has already focused both sides (and
    may interleave setup between the bind and the apply). *)
Ltac couple_bind :=
  wp_pures; tp_pures;
  wp_bind (Sample _ _ _); tp_bind (Sample _ _ _).

(** [couple_discharge] — the shared best-effort battery for the bundled
    [couple_X] tactics, covering BOTH the exact-cost (framed credit, pattern
    [\"[$Hr $Hε]\"]) and the non-exact cost (routed credit, pattern [\"[$Hr Hε]\"])
    regimes — which one you get is chosen by the caller's resource pattern, not by
    a separate tactic.  It pins the equational/regime side-conditions (by
    [reflexivity] / [apply Zabs_ind; lia] / [lia] / [simpl; lra]) and closes
    genuine [Prop] hypotheses via the [|- R => fail]-guarded [assumption].  The
    guard is the crux: it stops [assumption] from instantiating a bare real-valued
    value-evar ([ε]/[ε']) with an in-context distance bound [c : R] at the routed
    (cost) sites, where the residual [↯m (k'·ε)] credit goal — an [iProp] that
    none of these first-order tactics fire on — survives for the caller's
    [ecm_eq]/[ecm_weaken] reconciliation. *)
Ltac couple_discharge :=
  try first
    [ reflexivity
    | (apply Zabs_ind; lia)
    | (match goal with |- R => fail 1 | _ => assumption end)
    | lia
    | (simpl; lra) ].

(** [couple_discharge_apply] — the slimmer battery for the apply-only
    [couple_X_apply] variants.  Same guarded shape as [couple_discharge] but
    WITHOUT the [simpl; lra] framed-[Hε'] closer: the interleaved sites that drive
    the apply variant hand-write their own residual closers (e.g. [ecm_eq] / [lra]
    / [iFrame] bullets), so the battery must LEAVE those real-valued goals for the
    caller rather than greedily discharge them — closing them here would shift the
    caller's bullet alignment.  This is the one per-family-variant difference that
    resists folding into a single battery. *)
Ltac couple_discharge_apply :=
  try first
    [ (apply Zabs_ind; lia)
    | reflexivity
    | (match goal with |- R => fail 1 | _ => assumption end)
    | lia ].

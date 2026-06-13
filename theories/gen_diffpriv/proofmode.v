(** [wp_*] proof-mode tactic instances for the generic DP weakest precondition.
    Ported from [diffpriv/proofmode]; provides the base/bind/pure [GwpTactics]
    instances at [gen_lang Sg], enough for [wp_pures]/[wp_bind].  (The heap
    instance needs the [↦∗] array layer from [derived_laws]; the sampling tape
    tactic class is deferred — relational sampling goes through coupling rules.) *)
From clutch.diffpriv Require Import weakestpre lifting.
From clutch.gen_diffpriv Require Import primitive_laws.
From clutch.gen_diffpriv Require Export derived_laws.
From clutch.gen_prob_lang Require Export wp_tactics.
From clutch.gen_prob_lang.spec Require Export spec_tactics.
From clutch.gen_prob_lang Require Export tactics notation lang.
From clutch.gen_prob_lang Require Import class_instances.
From iris.prelude Require Import options.

Section gen_proofmode.
  Context (Sg : Sig).
  Canonical Structure gen_ectxi_lang_pm := gen_ectxi_lang Sg.
  Canonical Structure gen_ectx_lang_pm := gen_ectx_lang Sg.
  Canonical Structure gen_lang_pm := gen_lang Sg.
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
  | _ => k open_constr:(_)
  end.

Ltac tp_get_sig k ::=
  lazymatch goal with
  | |- environments.envs_entails _
         (@spec_update.spec_update (lang_markov (gen_lang ?S)) _ _ _ _ _ _) => k S
  | _ : diffprivGS ?S _ |- _ => k S
  end.

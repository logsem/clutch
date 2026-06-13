(** [wp_*] proof-mode tactic instances for the generic DP weakest precondition.
    Ported from [diffpriv/proofmode]; provides the base/bind/pure [GwpTactics]
    instances at [gen_lang Sg], enough for [wp_pures]/[wp_bind].  (The heap
    instance needs the [↦∗] array layer from [derived_laws]; the sampling tape
    tactic class is deferred — relational sampling goes through coupling rules.) *)
From clutch.diffpriv Require Import weakestpre lifting.
From clutch.gen_diffpriv Require Import primitive_laws.
From clutch.gen_prob_lang Require Export wp_tactics.
From clutch.gen_prob_lang Require Import class_instances tactics notation lang.
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

End gen_proofmode.

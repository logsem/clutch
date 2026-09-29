(** Reusable "value computes a decidable predicate" spec witnesses for the
    generic DP logic.

    A private query is typically [release ∘ aggregate ∘ filter], where the
    FILTER step is driven by a runtime predicate VALUE [vpred] that is meant to
    compute some Coq-level decidable predicate [pred].  Reasoning about such a
    query needs a Hoare-triple witness that [vpred] really decides [pred] on
    BOTH the implementation side (the standard WP triple) and the SPEC side (the
    [gwp_spec]-indexed [G]-triple, so the [gwp]-based list ADT can run on the
    spec program too).

    This pair of triples was duplicated verbatim across
    [examples.adaptive_count], [examples.privacy_filter] (as
    [is_predicate]/[is_spec_predicate]/[is_predicate_list]) and bundled into one
    conjunction in [examples.composition_demo] (as [decides_pred]).  This file
    factors them out ONCE:

      - [is_predicate pred vpred]      — the impl-side WP triple;
      - [is_spec_predicate pred vpred] — the [gwp_spec] spec-side twin;
      - [is_predicate_list l v]        — the list lifting (a [list (A → bool)]
                                          paired pointwise with an injected
                                          [val] list, carrying both triples).

    The [gwp_spec] referenced here is the SHARED spec-side [GenWp] instance from
    [gen_prob_lang.spec.spec_rules]; an in-context [diffprivGS Sg Σ] supplies the
    [specG_prob_lang]/[invGS_gen] it needs.  A client therefore needs only:
      From clutch.gen_diffpriv.lib Require Import predicate_spec.
      Section foo. Context {Sg : Sig} `{!diffprivGS Sg Σ}.
    and then [is_predicate], [is_spec_predicate] and [is_predicate_list] are
    available at the same implicit arguments as the original local copies. *)
From clutch.common Require Import inject.
From clutch.gen_diffpriv Require Export adequacy all.
From clutch.gen_prob_lang Require Export inject families.
From clutch.gen_prob_lang.spec Require Export spec_ra spec_rules.
From clutch.gen_prob_lang.gwp Require Export gen_weakestpre arith list.
From iris.prelude Require Import options.

Section predicate_spec.
  Context {Sg : Sig} `{!diffprivGS Sg Σ}.

  (** [vpred] computes [pred] on the IMPLEMENTATION side: applied to an injected
      argument [inject x] it returns the injected boolean [inject (pred x)]. *)
  Definition is_predicate {A} `[Inject A val] (pred : A -> bool) (vpred : val) : iProp Σ :=
    ∀ x, {{{ True }}} vpred (inject x) {{{ w, RET w; ⌜w = (inject (pred x))⌝ }}}.

  (** The SPEC-side twin: the same statement, but as a [gwp_spec]-indexed
      [G]-triple, so the [gwp]-based list operators can run on the spec program. *)
  Definition is_spec_predicate {A} `[Inject A val] (pred : A -> bool) (vpred : val) : iProp Σ :=
    ∀ x, G{{{ True }}} vpred (inject x) @ gwp_spec (Sg:=Sg) ; ⊤ {{{ w, RET w; ⌜w = (inject (pred x))⌝ }}}.

  (** List lifting: a list of predicates [l] paired pointwise with an injected
      [val] list [v], carrying both the impl and the spec triple for each pair. *)
  Fixpoint is_predicate_list {A} `[Inject A val] (l : list (A -> bool)) (v : val) : iProp Σ :=
    match l with
    | [] => ⌜v = NONEV⌝
    | pred::l' => ∃ vpred vl',
    ⌜v = SOMEV (vpred, vl')⌝
     ∗ is_predicate pred vpred ∗ is_spec_predicate pred vpred ∗ is_predicate_list l' vl' end.

End predicate_spec.

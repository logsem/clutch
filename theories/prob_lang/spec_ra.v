(** We define the resources required to interpret the specification
    configuration. *)
From Coq Require Import Reals.
From iris.algebra Require Import auth excl frac agree gmap.
From iris.base_logic.lib Require Import invariants ghost_map.
From iris.prelude Require Import options.
From iris.proofmode Require Import proofmode.
From self.program_logic Require Import exec.
From self.prob_lang Require Import lang.

Definition specN := nroot .@ "spec".

(* We will through [spec_interp] tie the exact state (both heap and tapes) to a
   fragmental view that lives in [spec_ctx]; from here we will give meaning to
   the usual [spec] resource and points-to connectivs *)
Definition progUR : ucmra := optionUR (exclR exprO).
Definition cfgO : ofe := leibnizO cfg.
Definition cfgUR : ucmra := optionUR (exclR cfgO).

(** The CMRA for the spec [cfg]. *)
Class specGS Σ := CfgSG {
  (* the instances we need for [spec_interp] *)
  specGS_interp_inG :> inG Σ (authUR cfgUR);
  specGS_interp_name : gname;

  (* the instances we need for [spec_ctx] *)
  specGS_prog_inG :> inG Σ (authR progUR);
  specGS_prog_name : gname;

  specGS_heap :> ghost_mapG Σ loc val;
  specGS_tapes :> ghost_mapG Σ loc tape;
  specGS_heap_name : gname;
  specGS_tapes_name : gname;
}.

Section resources.
  Context `{!specGS Σ}.

  Definition spec_interp_auth (ρ : cfg) : iProp Σ :=
    own specGS_interp_name (● (Excl' ρ : cfgUR)).
  Definition spec_interp_frag (ρ : cfg) : iProp Σ :=
    own specGS_interp_name (◯ (Excl' ρ : cfgUR)).

  Lemma spec_interp_auth_frag_agree ρ ρ' :
    spec_interp_auth ρ -∗ spec_interp_frag ρ' -∗ ⌜ρ = ρ'⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as
      %[Hexcl ?]%auth_both_valid_discrete.
    rewrite Excl_included in Hexcl.
    by apply leibniz_equiv in Hexcl.
  Qed.

  Definition spec_prog_auth (e : expr) : iProp Σ :=
    own specGS_prog_name (● (Excl' e : progUR)).
  Definition spec_prog_frag (e : expr) : iProp Σ :=
    own specGS_prog_name (◯ (Excl' e : progUR)).

  Lemma spec_prog_auth_frag_agree ρ ρ' :
    spec_prog_auth ρ -∗ spec_prog_frag ρ' -∗ ⌜ρ = ρ'⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as
      %[Hexcl ?]%auth_both_valid_discrete.
    rewrite Excl_included in Hexcl.
    by apply leibniz_equiv in Hexcl.
  Qed.

  Definition spec_heap_auth `{specGS Σ} :=
    @ghost_map_auth _ _ _ _ _ specGS_heap specGS_heap_name 1.
  Definition spec_tapes_auth `{specGS Σ} :=
    @ghost_map_auth _ _ _ _ _ specGS_tapes specGS_tapes_name 1.

End resources.

(** Spec program  *)
Notation " ⤇ e" := (spec_prog_frag e) (at level 20) : bi_scope.

(** Spec heap *)
Notation "l ↦ₛ{ dq } v" := (@ghost_map_elem _ _ _ _ _ specGS_heap specGS_heap_name l dq v)
  (at level 20, format "l  ↦ₛ{ dq }  v") : bi_scope.
Notation "l ↦ₛ□ v" := (l ↦ₛ{ DfracDiscarded } v)%I
  (at level 20, format "l  ↦ₛ□  v") : bi_scope.
Notation "l ↦ₛ{# q } v" := (l ↦ₛ{ DfracOwn q } v)%I
  (at level 20, format "l  ↦ₛ{# q }  v") : bi_scope.
Notation "l ↦ₛ v" := (l ↦ₛ{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↦ₛ  v") : bi_scope.

(** Spec tapes *)
Notation "l ↪ₛ{ dq } v" := (@ghost_map_elem _ _ _ _ _ specGS_tapes specGS_tapes_name l dq v)
  (at level 20, format "l  ↪ₛ{ dq }  v") : bi_scope.
Notation "l ↪ₛ□ v" := (l ↪ₛ{ DfracDiscarded } v)%I
  (at level 20, format "l  ↪ₛ□  v") : bi_scope.
Notation "l ↪ₛ{# q } v" := (l ↪ₛ{ DfracOwn q } v)%I
  (at level 20, format "l  ↪ₛ{# q }  v") : bi_scope.
Notation "l ↪ₛ v" := (l ↪ₛ{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↪ₛ  v") : bi_scope.

Section spec_ctx.
  Context `{!invGS_gen HasNoLc Σ, !specGS Σ}.

  Definition spec_inv : iProp Σ :=
    (∃ ξ ρ e σ,
        spec_interp_frag ρ ∗
        ⌜exec ξ ρ (e, σ) = 1%R⌝ ∗
        spec_prog_auth e ∗
        spec_heap_auth σ.(heap) ∗
        spec_tapes_auth σ.(tapes))%I.

  Definition spec_ctx : iProp Σ :=
    inv specN spec_inv.

  Global Instance spec_ctx_persistent : Persistent spec_ctx.
  Proof. apply _. Qed.
End spec_ctx.

(* PGH: originally used with autosubst; might be undeeded. *)
Ltac iAsimpl :=
  repeat match goal with
  | |- context [ (⤇ ?e)%I ] => progress (
    let e' := fresh in evar (e':expr);
    assert (e = e') as ->; [unfold e'; reflexivity|];
    unfold e'; clear e')
  | |- context [ WP ?e @ _ {{ _ }}%I ] => progress (
    let e' := fresh in evar (e':expr);
    assert (e = e') as ->; [unfold e'; reflexivity|];
    unfold e'; clear e')
    end.

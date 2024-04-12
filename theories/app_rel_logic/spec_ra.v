(** We define the resources required to interpret the specification
    configuration. *)
From Coq Require Import Reals.
From iris.algebra Require Import auth excl.
From iris.base_logic.lib Require Import invariants ghost_map.
From iris.prelude Require Import options.
From iris.proofmode Require Import proofmode.
From clutch.common Require Import language ectxi_language spec.
From clutch.prob_lang Require Import locations lang.

(* Definition specN := nroot .@ "spec". *)

(* We will through [spec_interp] tie the exact state (both heap and tapes) to a
   fragmental view that lives in [spec_ctx]; from here we will give meaning to
   the usual [spec] resource and points-to connectivs *)
Definition progUR : ucmra := optionUR (exclR exprO).
(* Definition cfgO : ofe := prodO exprO stateO. *)
(* Definition cfgUR : ucmra := optionUR (exclR cfgO). *)

(** The CMRA for the spec [cfg]. *)
Class specGS Σ := CfgSG {
  (* the instances we need for [spec_interp] *)
  (* specGS_interp_inG :: inG Σ (authUR cfgUR); *)
  (* specGS_interp_name : gname; *)

  (* the instances we need for [spec_ctx] *)
  specGS_prog_inG :: inG Σ (authR progUR);
  specGS_prog_name : gname;

  specGS_heap :: ghost_mapG Σ loc val;
  specGS_tapes :: ghost_mapG Σ loc tape;
  specGS_heap_name : gname;
  specGS_tapes_name : gname;
}.

Section resources.
  Context `{!specGS Σ}.
  Definition spec_prog_auth e :=
    own specGS_prog_name (● (Excl' e : progUR)).
  Definition spec_heap_auth `{specGS Σ} :=
    @ghost_map_auth _ _ _ _ _ specGS_heap specGS_heap_name 1.
  Definition spec_tapes_auth `{specGS Σ} :=
    @ghost_map_auth _ _ _ _ _ specGS_tapes specGS_tapes_name 1.

  Definition spec_interp_auth (ρ : cfg) : iProp Σ :=
    spec_prog_auth (ρ.1) ∗
    spec_heap_auth (ρ.2.(heap)) ∗
    spec_tapes_auth (ρ.2.(tapes))
  .

  Definition spec_prog_frag (e : expr) : iProp Σ :=
    own specGS_prog_name (◯ (Excl' e : progUR)).

  Definition spec_heap_frag (l : loc) v dq: iProp Σ := 
    (@ghost_map_elem _ _ _ _ _ specGS_heap specGS_heap_name l dq v).

  Definition spec_tapes_frag (l : loc) v dq: iProp Σ := 
    (@ghost_map_elem _ _ _ _ _ specGS_tapes specGS_tapes_name l dq v).
  
  (* Definition spec_interp_frag (ρ : cfg) : iProp Σ := *)
  (*   own specGS_interp_name (◯ (Excl' ρ : cfgUR)). *)

  Lemma spec_interp_auth_frag_agree_expr e1 σ1 e2  :
    spec_interp_auth (e1, σ1) -∗ spec_prog_frag e2 -∗ ⌜e1 = e2⌝.
  Proof.
    iIntros "[Ha _] Hf".
    iDestruct (own_valid_2 with "Ha Hf") as
      %[Hexcl ?]%auth_both_valid_discrete.
    rewrite Excl_included in Hexcl.
    by apply leibniz_equiv in Hexcl.
  Qed.

  Lemma spec_interp_update_expr e1 σ1 e2 e3 :
    spec_interp_auth (e1, σ1) -∗ spec_prog_frag e2 ==∗ spec_interp_auth (e3, σ1) ∗ spec_prog_frag e3.
  Proof.
    iIntros "Ha Hf".
    iDestruct (spec_interp_auth_frag_agree_expr with "Ha Hf") as %->.
    iDestruct "Ha" as "[Ha Hb]".
    iMod (own_update_2 with "Ha Hf") as "[Ha Hf]".
    { by eapply auth_update, option_local_update,
        (exclusive_local_update _ (Excl e3)). }
    by iFrame.
  Qed.

  Lemma spec_interp_auth_frag_lookup_heap e1 σ1 l v dq:
    spec_interp_auth (e1, σ1) -∗ spec_heap_frag l v dq -∗ ⌜σ1.(heap)!!l=Some v⌝.
  Proof.
    iIntros "(_&H&_) H'/=".
    iApply (ghost_map_lookup with "H H'").
  Qed.

  Lemma spec_interp_auth_frag_lookup_tapes e1 σ1 l v dq:
    spec_interp_auth (e1, σ1) -∗ spec_tapes_frag l v dq -∗ ⌜σ1.(tapes)!!l=Some v⌝.
  Proof.
    iIntros "(_&_&H) H'/=".
    iApply (ghost_map_lookup with "H H'").
  Qed.

  Lemma spec_interp_auth_frag_update_heap e1 σ1 l v w:
    spec_interp_auth (e1, σ1) -∗ spec_heap_frag l v (DfracOwn 1) ==∗
    spec_interp_auth (e1, state_upd_heap <[l:=w]> σ1) ∗ spec_heap_frag l w (DfracOwn 1).
  Proof.
    iIntros "(?&H&?) H'/=". destruct σ1.
    iMod (ghost_map_update with "H H'") as "?". simpl.
    iModIntro. iFrame. simpl. iFrame.
  Qed.

  Lemma spec_interp_auth_frag_update_tapes e1 σ1 l v w:
    spec_interp_auth (e1, σ1) -∗ spec_tapes_frag l v (DfracOwn 1) ==∗
    spec_interp_auth (e1, state_upd_tapes <[l:=w]> σ1) ∗ spec_tapes_frag l w (DfracOwn 1).
  Proof.
    iIntros "(?&?&H) H'/=". destruct σ1.
    iMod (ghost_map_update with "H H'") as "?". simpl.
    iModIntro. iFrame. simpl. iFrame.
  Qed.

  Definition spec_auth_spec : spec _ _ := Spec spec_interp_auth.

  (* Definition spec_prog_auth (e : expr) : iProp Σ := *)
  (*   own specGS_prog_name (● (Excl' e : progUR)). *)
  (* Definition spec_prog_frag (e : expr) : iProp Σ := *)
  (*   own specGS_prog_name (◯ (Excl' e : progUR)). *)

  (* Lemma spec_prog_auth_frag_agree e e' : *)
  (*   spec_prog_auth e -∗ spec_prog_frag e' -∗ ⌜e = e'⌝. *)
  (* Proof. *)
  (*   iIntros "Ha Hf". *)
  (*   iDestruct (own_valid_2 with "Ha Hf") as *)
  (*     %[Hexcl ?]%auth_both_valid_discrete. *)
  (*   rewrite Excl_included in Hexcl. *)
  (*   by apply leibniz_equiv in Hexcl. *)
  (* Qed. *)

  (* Lemma spec_prog_update e'' e e' : *)
  (*   spec_prog_auth e -∗ spec_prog_frag e' ==∗ spec_prog_auth e'' ∗ spec_prog_frag e''. *)
  (* Proof. *)
  (*   iIntros "Ha Hf". *)
  (*   iDestruct (spec_prog_auth_frag_agree with "Ha Hf") as %->. *)
  (*   iMod (own_update_2 with "Ha Hf") as "[Ha Hf]". *)
  (*   { by eapply auth_update, option_local_update, *)
  (*     (exclusive_local_update _ (Excl e'')). } *)
  (*   by iFrame. *)
  (* Qed. *)

  (* Definition spec_heap_auth `{specGS Σ} := *)
  (*   @ghost_map_auth _ _ _ _ _ specGS_heap specGS_heap_name 1. *)
  (* Definition spec_tapes_auth `{specGS Σ} := *)
  (*   @ghost_map_auth _ _ _ _ _ specGS_tapes specGS_tapes_name 1. *)

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
  

(* Section spec_ctx. *)
(*   Context `{!invGS_gen HasNoLc Σ, !specGS Σ}. *)

(*   Definition spec_inv : iProp Σ := *)
(*     (∃ ρ e σ n, *)
(*         spec_interp_frag ρ ∗ *)
(*         ⌜pexec n ρ (e, σ) = 1%R⌝ ∗ *)
(*         spec_prog_auth e ∗ *)
(*         spec_heap_auth σ.(heap) ∗ *)
(*         spec_tapes_auth σ.(tapes))%I. *)

(*   Definition spec_ctx : iProp Σ := *)
(*     inv specN spec_inv. *)

(*   Global Instance spec_ctx_persistent : Persistent spec_ctx. *)
(*   Proof. apply _. Qed. *)

(*   Definition refines_right K (e : expr) := (spec_ctx ∗ ⤇ fill K e)%I. *)

(*   Lemma refines_right_bind K' K e : *)
(*     refines_right K' (fill K e) ≡ refines_right (K ++ K') e. *)
(*   Proof. rewrite /refines_right /=. by rewrite fill_app. Qed. *)

(* End spec_ctx. *)

(* Ltac iAsimpl := *)
(*   repeat match goal with *)
(*   | |- context [ (⤇ ?e)%I ] => progress ( *)
(*     let e' := fresh in evar (e':expr); *)
(*     assert (e = e') as ->; [unfold e'; reflexivity|]; *)
(*     unfold e'; clear e') *)
(*   | |- context [ WP ?e @ _ {{ _ }}%I ] => progress ( *)
(*     let e' := fresh in evar (e':expr); *)
(*     assert (e = e') as ->; [unfold e'; reflexivity|]; *)
(*     unfold e'; clear e') *)
(*     end. *)

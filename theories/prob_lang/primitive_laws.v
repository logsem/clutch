(** This file proves the basic laws of the ProbLang weakest precondition by
    applying the lifting lemmas. *)
From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Export ghost_map.
From self.program_logic Require Export weakestpre.
From self.program_logic Require Import ectx_lifting.
From self.prob_lang Require Export class_instances spec_ra.
From self.prob_lang Require Import tactics notation.
From iris.prelude Require Import options.

Class clutchGS Σ := HeapG {
  clutchGS_invG : invGS_gen HasNoLc Σ;
  (* CMRA for the state *)
  clutchGS_heap : ghost_mapG Σ loc val;
  clutchGS_tapes : ghost_mapG Σ loc (nat * list nat);
  (* ghost names for the state *)
  clutchGS_heap_name : gname;
  clutchGS_tapes_name : gname;
  (* CMRA and ghost name for the spec *)
  clutchGS_spec :> specGS Σ;
}.

Definition heap_auth `{clutchGS Σ} :=
  @ghost_map_auth _ _ _ _ _ clutchGS_heap clutchGS_heap_name.
Definition tapes_auth `{clutchGS Σ} :=
  @ghost_map_auth _ _ _ _ _ clutchGS_tapes clutchGS_tapes_name.

Definition valid_tapes (t : gmap loc tape) : Prop :=
  map_Forall (λ _ '(b, ns), Forall (λ n, n ≤ b) ns) t.

Lemma valid_tapes_insert_fresh t n :
  valid_tapes t →
  valid_tapes (<[fresh_loc t:=(n, [])]> t).
Proof.
  rewrite /valid_tapes. intros Ht.
  rewrite map_Forall_insert; [auto|].
  apply not_elem_of_dom, fresh_loc_is_fresh.
Qed.

Lemma valid_tapes_consume t b n ns α :
  valid_tapes t →
  t !! α = Some (b, n :: ns) →
  valid_tapes (<[α:=(b, ns)]> t).
Proof.
  rewrite /valid_tapes.
  intros Ht Hα.
  apply map_Forall_insert_2; [|done].
  suff: (Forall (λ m, m ≤ b) (n :: ns)).
  { rewrite Forall_cons. by intros []. }
  eapply (map_Forall_lookup_1 _ _ _ _ Ht Hα).
Qed.

Lemma valid_tapes_leq t α b n ns :
  valid_tapes t →
  t !! α = Some (b, n :: ns) →
  n ≤ b.
Proof.
  rewrite /valid_tapes.
  intros Ht Hα.
  eapply (Forall_cons (λ n, n ≤ b) _ ns).
  apply (map_Forall_lookup_1 _ _ _ _ Ht Hα).
Qed.

Global Instance clutchGS_irisGS `{!clutchGS Σ} : irisGS prob_lang Σ := {
  iris_invGS := clutchGS_invG;
  state_interp σ := (heap_auth 1 σ.(heap) ∗ tapes_auth 1 σ.(tapes) ∗ ⌜valid_tapes σ.(tapes)⌝)%I;
  spec_interp ρ := spec_interp_auth ρ;
}.

(** Heap *)
Notation "l ↦{ dq } v" := (@ghost_map_elem _ _ _ _ _ clutchGS_heap clutchGS_heap_name l dq v)
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Notation "l ↦□ v" := (l ↦{ DfracDiscarded } v)%I
  (at level 20, format "l  ↦□  v") : bi_scope.
Notation "l ↦{# q } v" := (l ↦{ DfracOwn q } v)%I
  (at level 20, format "l  ↦{# q }  v") : bi_scope.
Notation "l ↦ v" := (l ↦{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↦  v") : bi_scope.

(** Tapes *)
Notation "l ↪{ dq } v" := (@ghost_map_elem _ _ _ _ _ clutchGS_tapes clutchGS_tapes_name l dq v)
  (at level 20, format "l  ↪{ dq }  v") : bi_scope.
Notation "l ↪□ v" := (l ↪{ DfracDiscarded } v)%I
  (at level 20, format "l  ↪□  v") : bi_scope.
Notation "l ↪{# q } v" := (l ↪{ DfracOwn q } v)%I
  (at level 20, format "l  ↪{# q }  v") : bi_scope.
Notation "l ↪ v" := (l ↪{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↪  v") : bi_scope.

Notation "l ↪b bs" := (l ↪ (1, bool_to_nat <$> bs))%I
  (at level 20, format "l  ↪b  bs") : bi_scope.

Section lifting.
Context `{!clutchGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : val → iProp Σ.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types l : loc.

(** Recursive functions: we do not use this lemmas as it is easier to use Löb *)
(* induction directly, but this demonstrates that we can state the expected *)
(* reasoning principle for recursive functions, without any visible ▷. *)
Lemma wp_rec_löb E f x e Φ Ψ :
  □ ( □ (∀ v, Ψ v -∗ WP (rec: f x := e)%V v @ E {{ Φ }}) -∗
     ∀ v, Ψ v -∗ WP (subst' x v (subst' f (rec: f x := e) e)) @ E {{ Φ }}) -∗
  ∀ v, Ψ v -∗ WP (rec: f x := e)%V v @ E {{ Φ }}.
Proof.
  iIntros "#Hrec". iLöb as "IH". iIntros (v) "HΨ".
  iApply lifting.wp_pure_step_later; first done.
  iNext. iApply ("Hrec" with "[] HΨ"). iIntros "!>" (w) "HΨ".
  iApply ("IH" with "HΨ").
Qed.

(** Heap *)
Lemma wp_alloc E v :
  {{{ True }}} Alloc (Val v) @ E {{{ l, RET LitV (LitLoc l); l ↦ v }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "[Hh Ht] !#".
  iSplit; [by eauto with head_step|].
  iIntros "!> /=" (e2 σ2 Hs); inv_head_step.
  iMod ((ghost_map_insert (fresh_loc σ1.(heap)) v) with "Hh") as "[$ Hl]".
  { apply not_elem_of_dom, fresh_loc_is_fresh. }
  iIntros "!>". iFrame. by iApply "HΦ".
Qed.

Lemma wp_load E l dq v :
  {{{ ▷ l ↦{dq} v }}} Load (Val $ LitV $ LitLoc l) @ E {{{ RET v; l ↦{dq} v }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "[Hh Ht] !#".
  iDestruct (ghost_map_lookup with "Hh Hl") as %?.
  iSplit; [by eauto with head_step|].
  iIntros "!> /=" (e2 σ2 Hs); inv_head_step.
  iFrame. iModIntro. by iApply "HΦ".
Qed.

Lemma wp_store E l v' v :
  {{{ ▷ l ↦ v' }}} Store (Val $ LitV (LitLoc l)) (Val v) @ E
  {{{ RET LitV LitUnit; l ↦ v }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "[Hh Ht] !#".
  iDestruct (ghost_map_lookup with "Hh Hl") as %?.
  iSplit; [by eauto with head_step|].
  iIntros "!> /=" (e2 σ2 Hs); inv_head_step.
  iMod (ghost_map_update with "Hh Hl") as "[$ Hl]".
  iFrame. iModIntro. by iApply "HΦ".
Qed.

(** Tapes  *)
Lemma wp_alloc_tape E (n : nat) :
  {{{ True }}} AllocTape #n @ E {{{ α, RET LitV (LitLbl α); α ↪ (n, []) }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "(Hh & Ht & %Hvalid) !# /=".
  iSplit; [by eauto with head_step|].
  iIntros "!>" (e2 σ2 Hs); inv_head_step.
  iMod (ghost_map_insert (fresh_loc σ1.(tapes)) with "Ht") as "[$ Hl]".
  { apply not_elem_of_dom, fresh_loc_is_fresh. }
  rewrite Nat2Z.id.
  iFrame. iModIntro.
  iSplitR; [|by iApply "HΦ"].
  iPureIntro.
  by apply valid_tapes_insert_fresh.
Qed.

Lemma wp_rand E (n : nat) :
  {{{ True }}} Rand (Val $ LitV $ LitInt n) @ E
  {{{ m, RET LitV (LitInt m); ⌜m ≤ n⌝ }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "Hσ !#".
  iSplit; [by eauto with head_step|].
  simpl.
  iIntros "!>" (e2 σ2 Hs).
  inv_head_step.
  iFrame. iApply "HΦ".
  auto with lia.
Qed.

Lemma wp_rand_tape E α (b n : nat) ns  :
  {{{ ▷ α ↪ (b, n :: ns) }}} Rand (Val $ LitV $ LitLbl α) @ E
  {{{ RET LitV (LitInt n); ⌜n ≤ b⌝ ∗ α ↪ (b, ns) }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "(Hh & Ht & %Hvalid) !#".
  iDestruct (ghost_map_lookup with "Ht Hl") as %?.
  iSplit; [by eauto with head_step|].
  simpl.
  iIntros "!>" (e2 σ2 Hs).
  inv_head_step.
  iMod (ghost_map_update with "Ht Hl") as "[$ Hl]".
  iFrame. iModIntro.
  assert (n ≤ b) as Hnb by by eapply valid_tapes_leq.
  iSplitR; [|iApply "HΦ"; eauto].
  iPureIntro.
  by eapply valid_tapes_consume.
Qed.

Lemma wp_rand_tape_empty E α (b : nat) :
  {{{ ▷ α ↪ (b, []) }}} Rand (Val $ LitV $ LitLbl α) @ E
  {{{ n, RET LitV (LitInt n); ⌜n ≤ b⌝ ∗ α ↪ (b, []) }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "(Hh & Ht & Hvalid) !#".
  iDestruct (ghost_map_lookup with "Ht Hl") as %?.
  iSplit; [by eauto with head_step|].
  simpl.
  iIntros "!>" (e2 σ2 Hs).
  inv_head_step.
  iFrame.
  iModIntro. iApply ("HΦ" with "[$Hl //]").
Qed.

(** * Simple derived laws *)
Lemma wp_alloc_tape_bool E (n : nat) :
  {{{ True }}} AllocTapeB @ E {{{ α, RET LitV (LitLbl α); α ↪b [] }}}.
Proof. iIntros (Φ) "_ HΦ". by iApply wp_alloc_tape. Qed. 

Lemma wp_flip E :
  {{{ True }}} flip @ E {{{ b, RET LitV (LitBool b); True }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  replace (UnOp ZtoBOp (rand #1%nat))
    with (fill ([UnOpCtx ZtoBOp]) (rand #1%nat)); [|done].
  iApply wp_bind.
  iApply (wp_rand with "[//]").
  iIntros "!>" (??) "/=".
  iApply wp_pure_step_later; [done|].
  iApply wp_value. by iApply "HΦ".
Qed.

Lemma wp_flip_tape E α b bs :
  {{{ ▷ α ↪b (b :: bs) }}} flipL (Val $ LitV $ LitLbl α) @ E
  {{{ RET LitV (LitBool b); α ↪b bs }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  replace (UnOp ZtoBOp (rand #lbl:α))
    with (fill ([UnOpCtx ZtoBOp]) (rand #lbl:α)); [|done].
  iApply wp_bind.
  iApply (wp_rand_tape with "Hl").
  iIntros "!> [% Hl] /=".
  iApply wp_pure_step_later; [done|].
  iApply wp_value.
  rewrite Z_to_bool_of_nat.
  rewrite bool_to_nat_to_bool.
  by iApply "HΦ".
Qed.

Lemma wp_flip_tape_empty E α :
  {{{ ▷ α ↪b [] }}} flipL (Val $ LitV $ LitLbl α) @ E
  {{{ b, RET LitV (LitBool b); α ↪b [] }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  replace (UnOp ZtoBOp (rand #lbl:α))
    with (fill ([UnOpCtx ZtoBOp]) (rand #lbl:α)); [|done].
  iApply wp_bind.
  iApply (wp_rand_tape_empty with "Hl").
  iIntros "!>" (n) "[% Hl] /=".
  iApply wp_pure_step_later; [done|].
  iApply wp_value.
  by iApply "HΦ".
Qed.

End lifting.

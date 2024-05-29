(** Resources required to track a [ProbLang] spec configuration. *)
From Coq Require Import Reals.
From iris.algebra Require Import auth excl.
From iris.base_logic.lib Require Import invariants ghost_map.
From iris.prelude Require Import options.
From iris.proofmode Require Import proofmode.
From self.common Require Import language ectxi_language.
From self.prob_lang Require Import locations lang.

Definition progUR : ucmra := optionUR (exclR exprO).
Definition cfgO : ofe := prodO exprO stateO.

(** The CMRA for the spec [cfg]. *)
Class specGS Σ := SpecGS {
  #[local] specGS_prog_inG :: inG Σ (authR progUR);
  specGS_prog_name : gname;

  #[local] specGS_heap :: ghost_mapG Σ loc val;
  #[local] specGS_tapes :: ghost_mapG Σ loc tape;

  specGS_heap_name : gname;
  specGS_tapes_name : gname;                      
}.

Class specGpreS Σ := SpecGPreS {
  specGpreS_prog_inG :: inG Σ (authR progUR);
  specGpreS_heap :: ghost_mapG Σ loc val;
  specGpreS_tapes :: ghost_mapG Σ loc tape;
}.

Definition specΣ : gFunctors :=
  #[ghost_mapΣ loc val;
    ghost_mapΣ loc tape;
    GFunctor (authUR progUR)].
#[global] Instance subG_selfGPreS {Σ} : subG specΣ Σ → specGpreS Σ.
Proof. solve_inG. Qed.

Section resources.
  Context `{!specGS Σ}.
  Definition spec_prog_auth e :=
    own specGS_prog_name (● (Excl' e : progUR)).
  Definition spec_heap_auth `{specGS Σ} :=
    @ghost_map_auth _ _ _ _ _ specGS_heap specGS_heap_name 1.
  Definition spec_tapes_auth `{specGS Σ} :=
    @ghost_map_auth _ _ _ _ _ specGS_tapes specGS_tapes_name 1.

  Definition spec_auth (ρ : cfg) : iProp Σ :=
    spec_prog_auth (ρ.1) ∗
    spec_heap_auth (ρ.2.(heap)) ∗
    spec_tapes_auth (ρ.2.(tapes)).

  Definition spec_prog_frag (e : expr) : iProp Σ :=
    own specGS_prog_name (◯ (Excl' e : progUR)).

  Definition spec_heap_frag (l : loc) v dq: iProp Σ :=
    (@ghost_map_elem _ _ _ _ _ specGS_heap specGS_heap_name l dq v).

  Definition spec_tapes_frag (l : loc) v dq: iProp Σ :=
    (@ghost_map_elem _ _ _ _ _ specGS_tapes specGS_tapes_name l dq v).
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

Section theory.
  Context `{!specGS Σ}.

  Lemma spec_auth_prog_agree e1 σ1 e2  :
    spec_auth (e1, σ1) -∗ ⤇ e2 -∗ ⌜e1 = e2⌝.
  Proof.
    iIntros "[Ha _] Hf".
    iDestruct (own_valid_2 with "Ha Hf") as
      %[Hexcl ?]%auth_both_valid_discrete.
    rewrite Excl_included in Hexcl.
    by apply leibniz_equiv in Hexcl.
  Qed.

  Lemma spec_update_prog e3 e1 σ1 e2 :
    spec_auth (e1, σ1) -∗ ⤇ e2 ==∗ spec_auth (e3, σ1) ∗ ⤇ e3.
  Proof.
    iIntros "Ha Hf".
    iDestruct (spec_auth_prog_agree with "Ha Hf") as %->.
    iDestruct "Ha" as "[Ha Hb]".
    iMod (own_update_2 with "Ha Hf") as "[Ha Hf]".
    { by eapply auth_update, option_local_update,
        (exclusive_local_update _ (Excl e3)). }
    by iFrame.
  Qed.

  (** Heap *)

  Lemma spec_auth_lookup_heap e1 σ1 l v dq:
    spec_auth (e1, σ1) -∗ l ↦ₛ{dq} v -∗ ⌜σ1.(heap) !! l = Some v⌝.
  Proof. iIntros "(_&H&_) H'/=". iApply (ghost_map_lookup with "H H'"). Qed.

  Lemma spec_auth_heap_alloc e σ v :
    spec_auth (e, σ) ==∗
    spec_auth (e, state_upd_heap <[ fresh_loc σ.(heap) := v ]> σ) ∗ fresh_loc σ.(heap) ↦ₛ v.
  Proof.
    iIntros "(? & Hheap & ?) /=".
    iMod (ghost_map_insert (fresh_loc σ.(heap)) with "Hheap") as "[Hheap Hl]".
    { apply not_elem_of_dom, fresh_loc_is_fresh. }
    by iFrame.
  Qed.

  Lemma spec_auth_update_heap w e1 σ1 l v :
    spec_auth (e1, σ1) -∗ l ↦ₛ{#1} v ==∗
    spec_auth (e1, state_upd_heap <[l:=w]> σ1) ∗ l ↦ₛ{#1} w.
  Proof.
    iIntros "(?&H&?) H' /=".
    iMod (ghost_map_update with "H H'") as "?".
    iModIntro. by iFrame.
  Qed.

  (** Tapes *)

  Lemma spec_auth_lookup_tape e1 σ1 l v dq :
    spec_auth (e1, σ1) -∗ l ↪ₛ{dq} v -∗ ⌜σ1.(tapes) !! l = Some v⌝.
  Proof. iIntros "(_&_&H) H'/=". iApply (ghost_map_lookup with "H H'"). Qed.

  Lemma spec_auth_update_tape w e1 σ1 l v :
    spec_auth (e1, σ1) -∗ l ↪ₛ{#1} v ==∗
    spec_auth (e1, state_upd_tapes <[l:=w]> σ1) ∗ l ↪ₛ{#1} w.
  Proof.
    iIntros "(?&?&H) H'/=".
    iMod (ghost_map_update with "H H'") as "?".
    iModIntro. by iFrame.
  Qed.

  Lemma spec_auth_tape_alloc e σ N :
    spec_auth (e, σ) ==∗
    spec_auth (e, state_upd_tapes <[fresh_loc σ.(tapes) := (N; [])]> σ) ∗ fresh_loc σ.(tapes) ↪ₛ (N; []).
  Proof.
    iIntros "(? & ? & Htapes) /=".
    iMod (ghost_map_insert (fresh_loc σ.(tapes)) with "Htapes") as "[H Hl]".
    { apply not_elem_of_dom, fresh_loc_is_fresh. }
    by iFrame.
  Qed.

End theory.

Lemma spec_ra_init e σ `{specGpreS Σ} :
  ⊢ |==> ∃ _ : specGS Σ,
      spec_auth (e, σ) ∗ ⤇ e ∗ ([∗ map] l ↦ v ∈ σ.(heap), l ↦ₛ v) ∗ ([∗ map] α ↦ t ∈ σ.(tapes), α ↪ₛ t).
Proof.
  iMod (own_alloc ((● (Excl' e)) ⋅ (◯ (Excl' e)))) as "(%γp & Hprog_auth & Hprog_frag)".
  { by apply auth_both_valid_discrete. }
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh Hls]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht Hαs]]".
  iExists (SpecGS _ _ γp _ _ γH γT).
  by iFrame.
Qed.

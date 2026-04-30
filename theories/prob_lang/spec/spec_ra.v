(** Resources required to track a [ProbLang] spec configuration. *)
From Stdlib Require Import Reals.
From iris.algebra Require Import auth excl.
From iris.base_logic.lib Require Import invariants ghost_map.
From iris.prelude Require Import options.
From iris.proofmode Require Import proofmode.
From clutch.base_logic Require Export spec_update.
From clutch.common Require Import language ectxi_language.
From clutch.prob_lang Require Import lang.

Definition progUR : ucmra := optionUR (exclR exprO).
Definition cfgO : ofe := prodO exprO stateO.

(** The CMRA for the spec [cfg]. *)
Class specG_prob_lang Σ := SpecGS {
  #[local] specG_prob_lang_prog_inG :: inG Σ (authR progUR);
  specG_prob_lang_prog_name : gname;

  #[local] specG_prob_lang_heap :: ghost_mapG Σ loc val;
  #[local] specG_prob_lang_tapes :: ghost_mapG Σ loc tape;
  #[local] specG_prob_lang_tapes_laplace :: ghost_mapG Σ loc tape_laplace;

  specG_prob_lang_heap_name : gname;
  specG_prob_lang_tapes_name : gname;                      
  specG_prob_lang_tapes_laplace_name : gname;
}.

Class specGpreS Σ := SpecGPreS {
  specGpreS_prog_inG :: inG Σ (authR progUR);
  specGpreS_heap :: ghost_mapG Σ loc val;
  specGpreS_tapes :: ghost_mapG Σ loc tape;
  specGpreS_tapes_laplace :: ghost_mapG Σ loc tape_laplace;
}.

Definition specΣ : gFunctors :=
  #[ghost_mapΣ loc val;
    ghost_mapΣ loc tape;
    ghost_mapΣ loc tape_laplace;
    GFunctor (authUR progUR)].
#[global] Instance subG_clutchGPreS {Σ} : subG specΣ Σ → specGpreS Σ.
Proof. solve_inG. Qed.

Section resources.
  Context `{!specG_prob_lang Σ}.
  Definition spec_prog_auth e :=
    own specG_prob_lang_prog_name (● (Excl' e : progUR)).
  Definition spec_heap_auth `{specG_prob_lang Σ} :=
    @ghost_map_auth _ _ _ _ _ specG_prob_lang_heap specG_prob_lang_heap_name (DfracOwn 1).
  Definition spec_tapes_auth `{specG_prob_lang Σ} :=
    @ghost_map_auth _ _ _ _ _ specG_prob_lang_tapes specG_prob_lang_tapes_name (DfracOwn 1).
  Definition spec_tapes_laplace_auth `{specG_prob_lang Σ} :=
    @ghost_map_auth _ _ _ _ _ specG_prob_lang_tapes_laplace specG_prob_lang_tapes_laplace_name (DfracOwn 1).

  Definition spec_auth (ρ : cfg) : iProp Σ :=
    spec_prog_auth (ρ.1) ∗
    spec_heap_auth (ρ.2.(heap)) ∗
    spec_tapes_auth (ρ.2.(tapes)) ∗
    spec_tapes_laplace_auth (ρ.2.(tapes_laplace)).

  Definition spec_prog_frag (e : expr) : iProp Σ :=
    own specG_prob_lang_prog_name (◯ (Excl' e : progUR)).

  Definition spec_heap_frag (l : loc) v dq: iProp Σ :=
    (@ghost_map_elem _ _ _ _ _ specG_prob_lang_heap specG_prob_lang_heap_name l dq v).

  Definition spec_tapes_frag (l : loc) v dq: iProp Σ :=
    (@ghost_map_elem _ _ _ _ _ specG_prob_lang_tapes specG_prob_lang_tapes_name l dq v).

  Definition spec_tapes_laplace_frag (l : loc) v dq: iProp Σ :=
    (@ghost_map_elem _ _ _ _ _ specG_prob_lang_tapes_laplace specG_prob_lang_tapes_laplace_name l dq v).
End resources.


(** Spec program  *)
Notation " ⤇ e" := (spec_prog_frag e) (at level 20) : bi_scope.

(** Spec heap *)
Notation "l ↦ₛ{ dq } v" := (@ghost_map_elem _ _ _ _ _ specG_prob_lang_heap specG_prob_lang_heap_name l dq v)
  (at level 20, format "l  ↦ₛ{ dq }  v") : bi_scope.
Notation "l ↦ₛ□ v" := (l ↦ₛ{ DfracDiscarded } v)%I
  (at level 20, format "l  ↦ₛ□  v") : bi_scope.
Notation "l ↦ₛ{# q } v" := (l ↦ₛ{ DfracOwn q } v)%I
  (at level 20, format "l  ↦ₛ{# q }  v") : bi_scope.
Notation "l ↦ₛ v" := (l ↦ₛ{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↦ₛ  v") : bi_scope.

(** Spec tapes *)
Notation "l ↪ₛ{ dq } v" := (@ghost_map_elem _ _ _ _ _ specG_prob_lang_tapes specG_prob_lang_tapes_name l dq v)
  (at level 20, format "l  ↪ₛ{ dq }  v") : bi_scope.
Notation "l ↪ₛ□ v" := (l ↪ₛ{ DfracDiscarded } v)%I
  (at level 20, format "l  ↪ₛ□  v") : bi_scope.
Notation "l ↪ₛ{# q } v" := (l ↪ₛ{ DfracOwn q } v)%I
  (at level 20, format "l  ↪ₛ{# q }  v") : bi_scope.
Notation "l ↪ₛ v" := (l ↪ₛ{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↪ₛ  v") : bi_scope.

(** Spec Laplace tapes *)
Notation "l ↪Lₛ{ dq } v" := (@ghost_map_elem _ _ _ _ _ specG_prob_lang_tapes_laplace specG_prob_lang_tapes_laplace_name l dq v)
  (at level 20, format "l  ↪Lₛ{ dq }  v") : bi_scope.
Notation "l ↪Lₛ□ v" := (l ↪Lₛ{ DfracDiscarded } v)%I
  (at level 20, format "l  ↪Lₛ□  v") : bi_scope.
Notation "l ↪Lₛ{# q } v" := (l ↪Lₛ{ DfracOwn q } v)%I
  (at level 20, format "l  ↪Lₛ{# q }  v") : bi_scope.
Notation "l ↪Lₛ v" := (l ↪Lₛ{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↪Lₛ  v") : bi_scope.

Notation "l ↪Lₛ ( num , den , mean ; xs )" := (l ↪Lₛ (Tape_Laplace num den mean xs))%I
  (at level 20, format "l  ↪Lₛ  ( num , den , mean ;  xs )") : bi_scope.

Section theory.
  Context `{!specG_prob_lang Σ}.

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
  Proof. iIntros "(_&_&H&_) H'/=". iApply (ghost_map_lookup with "H H'"). Qed.

  Lemma spec_auth_update_tape w e1 σ1 l v :
    spec_auth (e1, σ1) -∗ l ↪ₛ{#1} v ==∗
    spec_auth (e1, state_upd_tapes <[l:=w]> σ1) ∗ l ↪ₛ{#1} w.
  Proof.
    iIntros "(?&?&H&?) H'/=".
    iMod (ghost_map_update with "H H'") as "?".
    iModIntro. by iFrame.
  Qed.

  Lemma spec_auth_tape_alloc e σ N :
    spec_auth (e, σ) ==∗
    spec_auth (e, state_upd_tapes <[fresh_loc σ.(tapes) := (N; [])]> σ) ∗ fresh_loc σ.(tapes) ↪ₛ (N; []).
  Proof.
    iIntros "(? & ? & Htapes & ?) /=".
    iMod (ghost_map_insert (fresh_loc σ.(tapes)) with "Htapes") as "[H Hl]".
    { apply not_elem_of_dom, fresh_loc_is_fresh. }
    by iFrame.
  Qed.

  (** Laplace Tapes *)

  Lemma spec_auth_lookup_tape_laplace e1 σ1 l v dq :
    spec_auth (e1, σ1) -∗ l ↪Lₛ{dq} v -∗ ⌜σ1.(tapes_laplace) !! l = Some v⌝.
  Proof. iIntros "(_&_&_&H) H'/=". iApply (ghost_map_lookup with "H H'"). Qed.

  Lemma spec_auth_update_tape_laplace w e1 σ1 l v :
    spec_auth (e1, σ1) -∗ l ↪Lₛ{#1} v ==∗
    spec_auth (e1, state_upd_tapes_laplace <[l:=w]> σ1) ∗ l ↪Lₛ{#1} w.
  Proof.
    iIntros "(?&?&?&H) H'/=".
    iMod (ghost_map_update with "H H'") as "?".
    iModIntro. by iFrame.
  Qed.

  Lemma spec_auth_tape_laplace_alloc e σ num den mean :
    spec_auth (e, σ) ==∗
    spec_auth (e, state_upd_tapes_laplace <[fresh_loc σ.(tapes_laplace) := (Tape_Laplace num den mean [])]> σ) ∗ fresh_loc σ.(tapes_laplace) ↪Lₛ (num, den, mean; []).
  Proof.
    iIntros "(? & ? & ?&Htapes) /=".
    iMod (ghost_map_insert (fresh_loc σ.(tapes_laplace)) with "Htapes") as "[H Hl]".
    { apply not_elem_of_dom, fresh_loc_is_fresh. }
    by iFrame.
  Qed.

End theory.

Lemma spec_ra_init e σ `{specGpreS Σ} :
  ⊢ |==> ∃ _ : specG_prob_lang Σ,
      spec_auth (e, σ) ∗ ⤇ e ∗ ([∗ map] l ↦ v ∈ σ.(heap), l ↦ₛ v) ∗ ([∗ map] α ↦ t ∈ σ.(tapes), α ↪ₛ t) ∗ ([∗ map] α ↦ t ∈ σ.(tapes_laplace), α ↪Lₛ t).
Proof.
  iMod (own_alloc ((● (Excl' e)) ⋅ (◯ (Excl' e)))) as "(%γp & Hprog_auth & Hprog_frag)".
  { by apply auth_both_valid_discrete. }
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh Hls]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht Hαs]]".
  iMod (ghost_map_alloc σ.(tapes_laplace)) as "[%γTL [Htl Hαs']]".
  iExists (SpecGS _ _ γp _ _ _ γH γT γTL).
  by iFrame.
Qed.

(** Tapes containing natural numbers defined as a wrapper over backend tapes *)
Definition nat_spec_tape `{specG_prob_lang Σ} l (N : nat) (ns : list nat) : iProp Σ :=
  ∃ (fs : list (fin (S N))), ⌜fin_to_nat <$> fs = ns⌝ ∗ l ↪ₛ (N; fs).

Notation "l ↪ₛN ( M ; ns )" := (nat_spec_tape l M ns)%I
       (at level 20, format "l ↪ₛN ( M ; ns )") : bi_scope.

Section spec_tape_interface.
  Context `{!specG_prob_lang Σ}.

  (** Helper lemmas to go back and forth between the user-level representation
      of tapes (using nat) and the backend (using fin) *)

  Lemma spec_tapeN_to_empty l M :
    (l ↪ₛN ( M ; [] ) -∗ l ↪ₛ ( M ; [] )).
  Proof.
    iIntros "Hl".
    iDestruct "Hl" as (?) "(%Hmap & Hl')".
    by destruct (fmap_nil_inv _ _ Hmap).
  Qed.


  Lemma empty_to_spec_tapeN l M :
    (l ↪ₛ ( M ; [] ) -∗ l ↪ₛN ( M ; [] )).
  Proof.
    iIntros "Hl".
    iExists []. auto.
  Qed.

  Lemma read_spec_tape_head l M n ns :
    (l ↪ₛN ( M ; n :: ns ) -∗
      ∃ x xs, l ↪ₛ ( M ; x :: xs ) ∗ ⌜ fin_to_nat x = n ⌝ ∗
              ( l ↪ₛ ( M ; xs ) -∗l ↪ₛN ( M ; ns ) )).
  Proof.
    iIntros "Hl".
    iDestruct "Hl" as (xss) "(%Hmap & Hl')".
    destruct (fmap_cons_inv _ _ _ _ Hmap) as (x&xs&->&Hxs&->).
    iExists x, xs.
    iFrame.
    iSplit; auto.
    iIntros.
    iExists xs; auto.
  Qed.

End spec_tape_interface.



#[global] Instance spec_rules_spec_updateGS `{!specG_prob_lang Σ} :
  spec_updateGS (lang_markov prob_lang) Σ := Spec_updateGS spec_auth.

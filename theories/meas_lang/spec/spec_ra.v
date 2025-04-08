(** Resources required to track a [MeasLang] spec configuration. *)
From Coq Require Import Reals.
From iris.algebra Require Import auth excl.
From iris.base_logic.lib Require Import invariants ghost_map.
From iris.prelude Require Import options.
From iris.proofmode Require Import proofmode.
From clutch.meas_lang Require Export meas_spec_update.
From clutch.meas_lang Require Import language ectxi_language.
From clutch.meas_lang Require Import lang.
From mathcomp.analysis Require Import measure.

Local Open Scope classical_set_scope.

Definition progUR : ucmra := optionUR (exclR (leibnizO (@Measurable.sort _ expr))).
(* Definition cfgO : ofe := prodO expr state. *)

(** The CMRA for the spec [cfg]. *)
Class specG_meas_lang (Σ : gFunctors) := SpecGS {
  #[local] specG_meas_lang_prog_inG :: inG Σ (authR progUR);
  specG_meas_lang_prog_name : gname;

  #[local] specG_meas_lang_heap :: ghost_mapG Σ <<discr loc>> val;
  #[local] specG_meas_lang_tapes :: ghost_mapG Σ <<discr loc>> btape;
  #[local] specG_meas_lang_utapes :: ghost_mapG Σ <<discr loc>> utape;

  specG_meas_lang_heap_name : gname;
  specG_meas_lang_tapes_name : gname;
  specG_meas_lang_utapes_name : gname;
}.

Class specGpreS Σ := SpecGPreS {
  specGpreS_prog_inG :: inG Σ (authR progUR);
  specGpreS_heap :: ghost_mapG Σ <<discr loc>> val;
  specGpreS_tapes :: ghost_mapG Σ <<discr loc>> btape;
  specGpreS_utapes :: ghost_mapG Σ <<discr loc>> utape;
}.

Definition specΣ : gFunctors :=
  #[ghost_mapΣ <<discr loc>> val;
    ghost_mapΣ <<discr loc>> btape;
    ghost_mapΣ <<discr loc>> utape;
    GFunctor (authUR progUR)].
#[global] Instance subG_clutchGPreS {Σ} : subG specΣ Σ → specGpreS Σ.
Proof. solve_inG. Qed.

Section resources.
  Context `{!specG_meas_lang Σ}.
  Definition spec_prog_auth (e : expr) :=
    own specG_meas_lang_prog_name (● (Excl' e : progUR)).
  Definition spec_heap_auth `{specG_meas_lang Σ} :=
    @ghost_map_auth _ _ _ _ _ specG_meas_lang_heap specG_meas_lang_heap_name 1.
  Definition spec_tapes_auth `{specG_meas_lang Σ} :=
    @ghost_map_auth _ _ _ _ _ specG_meas_lang_tapes specG_meas_lang_tapes_name 1.
  Definition spec_utapes_auth `{specG_meas_lang Σ} :=
    @ghost_map_auth _ _ _ _ _ specG_meas_lang_utapes specG_meas_lang_utapes_name 1.

  Definition spec_auth (ρ : cfg) : iProp Σ :=
    spec_prog_auth (ρ.1) ∗
    spec_heap_auth (heap ρ.2) ∗
    spec_tapes_auth (tapes ρ.2) ∗
    spec_utapes_auth (utapes ρ.2).

  Definition spec_prog_frag (e : expr) : iProp Σ :=
    own specG_meas_lang_prog_name (◯ (Excl' e : progUR)).
  
  Definition spec_heap_frag (l : loc) v dq: iProp Σ :=
    (@ghost_map_elem _ _ _ _ _ specG_meas_lang_heap specG_meas_lang_heap_name l dq v).

  Definition spec_tapes_frag (l : loc) v dq: iProp Σ :=
    (@ghost_map_elem _ _ _ _ _ specG_meas_lang_tapes specG_meas_lang_tapes_name l dq v).

  Definition spec_utapes_frag (l : loc) v dq: iProp Σ :=
    (@ghost_map_elem _ _ _ _ _ specG_meas_lang_utapes specG_meas_lang_utapes_name l dq v).

End resources.

(** Spec program  *)
Notation " ⤇ e" := (spec_prog_frag e) (at level 20) : bi_scope.

(** Spec heap *)
Notation "l ↦ₛ{ dq } v" := (@ghost_map_elem _ _ _ _ _ specG_meas_lang_heap specG_meas_lang_heap_name l dq v)
  (at level 20, format "l  ↦ₛ{ dq }  v") : bi_scope.
Notation "l ↦ₛ□ v" := (l ↦ₛ{ DfracDiscarded } v)%I
  (at level 20, format "l  ↦ₛ□  v") : bi_scope.
Notation "l ↦ₛ{# q } v" := (l ↦ₛ{ DfracOwn q } v)%I
  (at level 20, format "l  ↦ₛ{# q }  v") : bi_scope.
Notation "l ↦ₛ v" := (l ↦ₛ{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↦ₛ  v") : bi_scope.

(** Spec tapes *)
Notation "l ↪ₛ{ dq } v" := (@ghost_map_elem _ _ _ _ _ specG_meas_lang_tapes specG_meas_lang_tapes_name l dq v)
  (at level 20, format "l  ↪ₛ{ dq }  v") : bi_scope.
Notation "l ↪ₛ□ v" := (l ↪ₛ{ DfracDiscarded } v)%I
  (at level 20, format "l  ↪ₛ□  v") : bi_scope.
Notation "l ↪ₛ{# q } v" := (l ↪ₛ{ DfracOwn q } v)%I
  (at level 20, format "l  ↪ₛ{# q }  v") : bi_scope.
Notation "l ↪ₛ v" := (l ↪ₛ{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↪ₛ  v") : bi_scope.

(** Spec utapes *)
Notation "l ↪ℝₛ{ dq } v" := (@ghost_map_elem _ _ _ _ _ specG_meas_lang_utapes specG_meas_lang_utapes_name l dq v)
  (at level 20, format "l  ↪ℝₛ{ dq }  v") : bi_scope.
Notation "l ↪ℝₛ□ v" := (l ↪ℝₛ{ DfracDiscarded } v)%I
  (at level 20, format "l  ↪ℝₛ□  v") : bi_scope.
Notation "l ↪ℝₛ{# q } v" := (l ↪ℝₛ{ DfracOwn q } v)%I
  (at level 20, format "l  ↪ℝₛ{# q }  v") : bi_scope.
Notation "l ↪ℝₛ v" := (l ↪ℝₛ{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↪ℝₛ  v") : bi_scope.

Section theory.
  Context `{!specG_meas_lang Σ}.

  Lemma spec_auth_prog_agree (e1 : expr) (σ1 : state) (e2 : expr) :
    spec_auth (e1, σ1) -∗ ⤇ e2 -∗ ⌜e1 = e2⌝.
  Proof.
    iIntros "[Ha _] Hf".
    iDestruct (own_valid_2 with "Ha Hf") as
      %[Hexcl ?]%auth_both_valid_discrete.
    rewrite Excl_included in Hexcl.
    by apply leibniz_equiv in Hexcl.
  Qed.

  Lemma spec_update_prog (e3 e1 : expr) (σ1 : state) (e2 : expr) :
    spec_auth (e1, σ1) -∗ ⤇ e2 ==∗ spec_auth (e3, σ1) ∗ ⤇ e3.
  Proof.
    iIntros "Ha Hf".
    iDestruct (spec_auth_prog_agree with "Ha Hf") as %->.
    iDestruct "Ha" as "[Ha Hb]".
    iMod (own_update_2 with "Ha Hf") as "[Ha Hf]".
    { eapply auth_update, @option_local_update.
      eapply (exclusive_local_update).
      admit. }
    (*
      eapply (exclusive_local_update _ (Excl e3)).
      done. } *)
    rewrite /spec_auth//=.
    (* iFrame is super slow for some reason *)
    iSplitR "Hf".
    { iModIntro.
      iDestruct "Hb" as "[Hb1 [Hb2 Hb3]]".
      iSplitL "Ha"; first by unfold spec_prog_auth; iApply "Ha".
      iSplitL "Hb1"; first by iApply "Hb1".
      iSplitL "Hb2"; first by iApply "Hb2".
      by iApply "Hb3". }
    by iApply "Hf".
  Admitted.

  (** Heap *)

  Lemma spec_auth_lookup_heap e1 σ1 l v dq:
    spec_auth (e1, σ1) -∗ l ↦ₛ{dq} v -∗ ⌜heap σ1 !! l = Some v⌝.
  Proof. iIntros "(_&H&_) H'/=". iApply (ghost_map_lookup with "H H'"). Qed.

  Lemma spec_auth_heap_alloc e σ v :
    spec_auth (e, σ) ==∗
    spec_auth (e, state_upd_heap <[ state.fresh (heap σ) := v ]> σ) ∗ state.fresh (heap σ) ↦ₛ v.
  Proof.
    iIntros "(H1 & Hheap & H2 & H3) /=".
    iMod (ghost_map_insert (state.fresh (heap σ)) with "Hheap") as "[Hheap Hl]".
    { apply not_elem_of_dom.
      admit. (* fresh_loc_is_fresh. *) }
    iModIntro.
    iSplitR "Hl".
    { rewrite /spec_auth//=.
      iSplitL "H1"; first by iApply "H1".
      iSplitL "Hheap"; first by iApply "Hheap".
      iSplitL "H2"; first by iApply "H2".
      by iApply "H3". }
    by iApply "Hl".
  Admitted.

  Lemma spec_auth_update_heap w e1 σ1 l v :
    spec_auth (e1, σ1) -∗ l ↦ₛ{#1} v ==∗
    spec_auth (e1, state_upd_heap <[l:=w]> σ1) ∗ l ↦ₛ{#1} w.
  Proof.
    iIntros "(H1&H&H2&H3) H' /=".
    iMod (ghost_map_update with "H H'") as "(H4&H5)".
    iModIntro.
    iSplitR "H5".
    { rewrite /spec_auth//=.
      iSplitL "H1"; first by iApply "H1".
      iSplitL "H4"; first by iApply "H4".
      iSplitL "H2"; first by iApply "H2".
      by iApply "H3". }
    by iApply "H5".
   Qed.

  (** Tapes *)
  Lemma spec_auth_lookup_tape (e1 : expr) (σ1 : state) (l : loc) v dq :
    spec_auth (e1, σ1) -∗ l ↪ₛ{dq} v -∗ ⌜(tapes σ1) !! l = Some v⌝.
  Proof.
    iIntros "(H1&H2&H&H3) H'/=".
    iApply (@ghost_map_lookup with "[H]").
    { by rewrite /ghost_map_auth//=. }
    by iApply "H'".
  Qed.

  Lemma spec_auth_update_tape w (e1 : expr) (σ1 : state) (l : loc) v :
    spec_auth (e1, σ1) -∗ l ↪ₛ{#1} v ==∗
    spec_auth (e1, state_upd_tapes <[l:=w]> σ1) ∗ l ↪ₛ{#1} w.
  Proof.
    iIntros "(H1&H2&H&H3) H'/=".
    iMod (ghost_map_update with "H H'") as "(H4&H5)".
    iModIntro.
    iSplitR "H5"; last by iApply "H5".
    iSplitL "H1"; first by iApply "H1".
    iSplitL "H2"; first by iApply "H2".
    iSplitL "H4"; first by iApply "H4".
    by iApply "H3".
  Qed.

  Lemma spec_auth_tape_alloc (e : expr) (σ : state) N :
    spec_auth (e, σ) ==∗
    spec_auth (e, state_upd_tapes <[state.fresh (tapes σ) := (N, emptyTape)]> σ) ∗ state.fresh (tapes σ) ↪ₛ (N, emptyTape).
  Proof.
    iIntros "(H1 & H2 & Htapes & H3) /=".
    iMod (ghost_map_insert (state.fresh (tapes σ)) with "Htapes") as "[H Hl]".
    { apply not_elem_of_dom. admit. }
    iModIntro.
    iSplitR "Hl"; last by iApply "Hl".
    iSplitL "H1"; first by iApply "H1".
    iSplitL "H2"; first by iApply "H2".
    iSplitL "H"; first by iApply "H".
    by iApply "H3".
  Admitted.


  (** UTapes *)
  Lemma spec_auth_lookup_utape (e1 : expr) (σ1 : state) (l : loc) v dq :
    spec_auth (e1, σ1) -∗ l ↪ℝₛ{dq} v -∗ ⌜(utapes σ1) !! l = Some v⌝.
  Proof.
    iIntros "(H1&H2&H3&H) H'/=".
    iApply (@ghost_map_lookup with "[H]").
    { by rewrite /ghost_map_auth//=. }
    by iApply "H'".
  Qed.

  Lemma spec_auth_update_utape w (e1 : expr) (σ1 : state) (l : loc) v :
    spec_auth (e1, σ1) -∗ l ↪ℝₛ{#1} v ==∗
    spec_auth (e1, state_upd_utapes <[l:=w]> σ1) ∗ l ↪ℝₛ{#1} w.
  Proof.
    iIntros "(H1&H2&H3&H) H'/=".
    iMod (ghost_map_update with "H H'") as "(H4&H5)".
    iModIntro.
    iSplitR "H5"; last by iApply "H5".
    iSplitL "H1"; first by iApply "H1".
    iSplitL "H2"; first by iApply "H2".
    iSplitL "H3"; first by iApply "H3".
    by iApply "H4".
  Qed.

  Lemma spec_auth_utape_alloc (e : expr) (σ : state) :
    spec_auth (e, σ) ==∗
    spec_auth (e, state_upd_utapes <[state.fresh (utapes σ) := emptyTape]> σ) ∗ state.fresh (utapes σ) ↪ℝₛ emptyTape.
  Proof.
    iIntros "(H1 & H2 & H3 & Htapes) /=".
    iMod (ghost_map_insert (state.fresh (utapes σ)) with "Htapes") as "[H Hl]".
    { apply not_elem_of_dom. admit. }
    iModIntro.
    iSplitR "Hl"; last by iApply "Hl".
    iSplitL "H1"; first by iApply "H1".
    iSplitL "H2"; first by iApply "H2".
    iSplitL "H3"; first by iApply "H3".
    by iApply "H".
  Admitted.

End theory.


Lemma spec_ra_init e σ `{specGpreS Σ} :
  ⊢ |==> ∃ _ : specG_meas_lang Σ,
      spec_auth (e, σ) ∗ ⤇ e ∗ ([∗ map] l ↦ v ∈ (heap σ), l ↦ₛ v) ∗ ([∗ map] α ↦ t ∈ (tapes σ), α ↪ₛ t) ∗ ([∗ map] α ↦ t ∈ (utapes σ), α ↪ℝₛ t).
Proof. Admitted.
(*
  iMod (own_alloc ((● (Excl' e)) ⋅ (◯ (Excl' e)))) as "(%γp & Hprog_auth & Hprog_frag)".
  { by apply auth_both_valid_discrete. }
  iMod (ghost_map_alloc (heap σ)) as "[%γH [Hh Hls]]".
  iMod (ghost_map_alloc (tapes σ)) as "[%γT [Ht Hαs]]".
  iMod (ghost_map_alloc (utapes σ)) as "[%γU [Hu HαUs]]".
  iExists (SpecGS _ _ γp _ _ _ γH γT γU).
  iModIntro.
  rewrite /spec_auth//=.
  iSplitL "Hprog_auth Hh Ht Hu".
  { iSplitL "Hprog_auth"; first by iApply "Hprog_auth".
    iSplitL "Hh"; first by iApply "Hh".
    iSplitL "Ht"; first by iApply "Ht".
    by iApply "Hu". }
  iSplitL "Hprog_frag"; first by iApply "Hprog_frag".
  iSplitL "Hls"; first by iApply "Hls".
  iSplitL "Hαs"; first by iApply "Hαs".
  by iApply "HαUs".
Qed. *)


(** No nat spec tapes *)

(* Tapes containing natural numbers defined as a wrapper over backend tapes
Definition nat_spec_tape `{specG_prob_lang Σ} l (N : nat) (ns : list nat) : iProp Σ :=
  ∃ (fs : list (fin (S N))), ⌜fin_to_nat <$> fs = ns⌝ ∗ l ↪ₛ (N; fs).

Notation "l ↪ₛN ( M ; ns )" := (nat_spec_tape l M ns)%I
       (at level 20, format "l ↪ₛN ( M ; ns )") : bi_scope.
Section spec_tape_interface.
  Context `{!specG_meas_lang Σ}.

  (* Helper lemmas to go back and forth between the user-level representation
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

*)


(*
(* FIXME: I feel like this is wrong... *)
#[global] Instance spec_rules_spec_updateGS `{!specG_meas_lang Σ} :
  meas_spec_updateGS (meas_lang_markov meas_lang) Σ := MeasSpec_updateGS spec_auth.
*)


(*
#[global] Instance spec_rules_spec_updateGS `{!specG_prob_lang Σ} :
  spec_updateGS (lang_markov prob_lang) Σ := Spec_updateGS spec_auth.
*)

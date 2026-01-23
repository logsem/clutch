(** Resources required to track a [ProbEffLang] spec configuration. *)
From Stdlib Require Import Reals.
From iris.algebra Require Import auth excl.
From iris.bi Require Export fractional.
From iris.base_logic.lib Require Import invariants ghost_map.
From iris.prelude Require Import options.
From iris.proofmode Require Import proofmode.
From clutch.base_logic Require Export spec_update.

From clutch.common Require Import locations language.
From clutch.prob_eff_lang.probblaze Require Import syntax semantics.

Definition progUR : ucmra := optionUR (exclR syntax.exprO). (* TODO: fix imports to find exprO from syntax *)
Definition cfgO : ofe := prodO syntax.exprO syntax.stateO.

(** The CMRA for the spec [cfg]. *)
Class specG_blaze_prob_lang Σ := SpecGS {
  #[local] specG_blaze_prob_lang_prog_inG :: inG Σ (authR progUR);
  specG_blaze_prob_lang_prog_name : gname;

  #[local] specG_blaze_prob_lang_heap :: ghost_mapG Σ loc syntax.val;
  #[local] specG_blaze_prob_lang_tapes :: ghost_mapG Σ loc tape;
  #[local] specG_blaze_prob_lang_labels :: ghost_mapG Σ label unit;

  specG_blaze_prob_lang_heap_name : gname;
  specG_blaze_prob_lang_tapes_name : gname;
  specG_blaze_prob_lang_labels_name : gname
}.

Class specGpreS Σ := SpecGPreS {
  specGpreS_prog_inG :: inG Σ (authR progUR);
  specGpreS_heap :: ghost_mapG Σ loc syntax.val;
  specGpreS_tapes :: ghost_mapG Σ loc tape;
  specGpreS_labels :: ghost_mapG Σ label unit
}.

Definition specΣ : gFunctors :=
  #[ghost_mapΣ loc syntax.val;
    ghost_mapΣ loc tape;
    ghost_mapΣ label unit;
    GFunctor (authUR progUR)].
#[global] Instance subG_clutchGPreS {Σ} : subG specΣ Σ → specGpreS Σ.
Proof. solve_inG. Qed.

Section resources.
  Context `{!specG_blaze_prob_lang Σ}.
  Definition spec_prog_auth e :=
    own specG_blaze_prob_lang_prog_name (● (Excl' e : progUR)).
  Definition spec_heap_auth `{specG_blaze_prob_lang Σ} :=
    @ghost_map_auth _ _ _ _ _ specG_blaze_prob_lang_heap specG_blaze_prob_lang_heap_name 1.
  Definition spec_tapes_auth `{specG_blaze_prob_lang Σ} :=
    @ghost_map_auth _ _ _ _ _ specG_blaze_prob_lang_tapes specG_blaze_prob_lang_tapes_name 1.
  Definition spec_labels_auth `{specG_blaze_prob_lang Σ} :=
    ghost_map_auth specG_blaze_prob_lang_labels_name 1.


  (* TODO: figure out if this belongs to state_rules or spec_ra *)
  Definition past_labels (l : label) : list label :=
    imap (λ l' _, Label l') (replicate (label_car l)%nat ()).

  
  Definition to_labels (l : label) : gmap label () :=
    let kv_pair l := (l, ()) in
    list_to_map (kv_pair <$> past_labels l).
  
  Definition spec_auth (ρ : (syntax.expr * syntax.state)) : iProp Σ :=
    spec_prog_auth (ρ.1) ∗
    spec_heap_auth (ρ.2.(heap)) ∗
    spec_tapes_auth (ρ.2.(tapes)) ∗
    spec_labels_auth (to_labels ρ.2.(next_label)).

  Definition spec_prog_frag (e : syntax.expr) : iProp Σ :=
    own specG_blaze_prob_lang_prog_name (◯ (Excl' e : progUR)).

  Definition spec_heap_frag (l : loc) v dq: iProp Σ :=
    (@ghost_map_elem _ _ _ _ _ specG_blaze_prob_lang_heap specG_blaze_prob_lang_heap_name l dq v).

  Definition spec_tapes_frag (l : loc) v dq: iProp Σ :=
    (@ghost_map_elem _ _ _ _ _ specG_blaze_prob_lang_tapes specG_blaze_prob_lang_tapes_name l dq v).

  Definition spec_labels_frag (l : label) dq : iProp Σ :=
    ghost_map_elem specG_blaze_prob_lang_labels_name l dq ().
  
End resources.

(** Spec program  *)
Notation " ⤇ e" := (spec_prog_frag e) (at level 20) : bi_scope.

(** Spec heap *)
Notation "l ↦ₛ{ dq } v" := (@ghost_map_elem _ _ _ _ _ specG_blaze_prob_lang_heap specG_blaze_prob_lang_heap_name l dq v)
  (at level 20, format "l  ↦ₛ{ dq }  v") : bi_scope.
Notation "l ↦ₛ□ v" := (l ↦ₛ{ DfracDiscarded } v)%I
  (at level 20, format "l  ↦ₛ□  v") : bi_scope.
Notation "l ↦ₛ{# q } v" := (l ↦ₛ{ DfracOwn q } v)%I
  (at level 20, format "l  ↦ₛ{# q }  v") : bi_scope.
Notation "l ↦ₛ v" := (l ↦ₛ{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↦ₛ  v") : bi_scope.

(** Spec tapes *)
Notation "l ↪ₛ{ dq } v" := (@ghost_map_elem _ _ _ _ _ specG_blaze_prob_lang_tapes specG_blaze_prob_lang_tapes_name l dq v)
  (at level 20, format "l  ↪ₛ{ dq }  v") : bi_scope.
Notation "l ↪ₛ□ v" := (l ↪ₛ{ DfracDiscarded } v)%I
  (at level 20, format "l  ↪ₛ□  v") : bi_scope.
Notation "l ↪ₛ{# q } v" := (l ↪ₛ{ DfracOwn q } v)%I
  (at level 20, format "l  ↪ₛ{# q }  v") : bi_scope.
Notation "l ↪ₛ v" := (l ↪ₛ{ DfracOwn 1 } v)%I
                       (at level 20, format "l  ↪ₛ  v") : bi_scope.


Definition unshotₛ `{specG_blaze_prob_lang Σ} (r : loc) := (r ↦ₛ LitV (LitBool true))%I.

Section theory.
  Context `{!specG_blaze_prob_lang Σ}.

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
    iIntros "(? & ? & Htapes&?) /=".
    iMod (ghost_map_insert (fresh_loc σ.(tapes)) with "Htapes") as "[H Hl]".
    { apply not_elem_of_dom, fresh_loc_is_fresh. }
    by iFrame.
  Qed.

  (** Labels **)
  (* consider removing these rules *)

  Lemma Excl_expr_included (e e' : syntax.expr) : Excl' e ≼ Excl' e' → e = e'.
  Proof. by rewrite Excl_included; apply leibniz_equiv. Qed.

  Global Instance spec_label_fractional l : Fractional (λ q, spec_labels_frag l (DfracOwn q))%I.
  Proof. apply _. Qed.

  Global Instance spec_label_as_fractional l q :
    AsFractional (spec_labels_frag l (DfracOwn q)) (λ q', spec_labels_frag l (DfracOwn q'))%I q.
  Proof. apply _. Qed.

  Global Instance frame_spec_label p l q1 q2 q :
    FrameFractionalQp q1 q2 q →
    Frame p (spec_labels_frag l (DfracOwn q1)) (spec_labels_frag l (DfracOwn q2)) (spec_labels_frag l (DfracOwn q)) | 5.
  Proof. apply: frame_fractional. Qed.

  Global Instance spec_label_combine_sep_gives dq1 dq2 l :
    CombineSepGives (spec_labels_frag l dq1) (spec_labels_frag l dq2) ⌜ ✓ (dq1 ⋅ dq2) ⌝.
  Proof.
    rewrite /CombineSepGives. iIntros "[H1 H2]".
    iCombine "H1 H2" gives %[? _]. eauto.
  Qed.

  Lemma spec_label_combine dq1 dq2 l :
    spec_labels_frag l dq1 -∗ spec_labels_frag l dq2 -∗ spec_labels_frag l (dq1 ⋅ dq2).
  Proof.
    iIntros "Hl1 Hl2". by iCombine "Hl1 Hl2" as "$".
  Qed.

  Global Instance spec_label_combine_as dq1 dq2 l :
    CombineSepAs (spec_labels_frag l dq1) (spec_labels_frag l dq2) (spec_labels_frag l (dq1 ⋅ dq2)) | 60.
  Proof.
    rewrite /CombineSepAs. iIntros "[H1 H2]".
    iDestruct (spec_label_combine with "H1 H2") as "$".
  Qed.

  Lemma spec_label_valid dq l : spec_labels_frag l dq -∗ ⌜ ✓ dq ⌝.
  Proof. apply ghost_map_elem_valid. Qed.

  Lemma spec_label_valid_2 dq1 dq2 l :
    spec_labels_frag l dq1 -∗ spec_labels_frag l dq2 -∗ ⌜ ✓ (dq1 ⋅ dq2) ⌝.
  Proof. iIntros "H1 H2". by iCombine "H1 H2" gives %?. Qed.

  Lemma spec_label_frac_ne dq1 dq2 l1 l2 :
    ¬ ✓(dq1 ⋅ dq2) → spec_labels_frag l1 dq1 -∗ spec_labels_frag l2 dq2 -∗ ⌜ l1 ≠ l2 ⌝.
  Proof. apply ghost_map_elem_frac_ne. Qed.

  Lemma spec_label_ne dq2 l1 l2 :
    spec_labels_frag l1 (DfracOwn 1) -∗ spec_labels_frag l2 dq2 -∗ ⌜ l1 ≠ l2 ⌝.
  Proof. apply ghost_map_elem_ne. Qed.

  Lemma spec_label_persist dq l : spec_labels_frag l dq ==∗ spec_labels_frag l DfracDiscarded.
  Proof. apply ghost_map_elem_persist. Qed.
End theory.
  
Lemma spec_ra_init e σ `{specGpreS Σ} :
  ⊢ |==> ∃ _ : specG_blaze_prob_lang Σ,
      spec_auth (e, σ) ∗ ⤇ e ∗ ([∗ map] l ↦ v ∈ σ.(heap), l ↦ₛ v) ∗ ([∗ map] α ↦ t ∈ σ.(tapes), α ↪ₛ t).
Proof.
  iMod (own_alloc ((● (Excl' e)) ⋅ (◯ (Excl' e)))) as "(%γp & Hprog_auth & Hprog_frag)".
  { by apply auth_both_valid_discrete. }
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh Hls]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht Hαs]]".
  iMod (ghost_map_alloc (to_labels σ.(next_label))) as (γlabels) "[Hlabels _]".
  iExists (SpecGS _ _ γp _ _ _ γH γT γlabels).
  by iFrame.
Qed.

(** Tapes containing natural numbers defined as a wrapper over backend tapes *)
Definition nat_spec_tape `{specG_blaze_prob_lang Σ} l (N : nat) (ns : list nat) : iProp Σ :=
  ∃ (fs : list (fin (S N))), ⌜fin_to_nat <$> fs = ns⌝ ∗ l ↪ₛ (N; fs).

Notation "l ↪ₛN ( M ; ns )" := (nat_spec_tape l M ns)%I
                                 (at level 20, format "l ↪ₛN ( M ; ns )") : bi_scope.

Section spec_tape_interface.
  Context `{!specG_blaze_prob_lang Σ}.

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

#[global] Instance spec_rules_spec_updateGS `{!specG_blaze_prob_lang Σ} :
  spec_updateGS (lang_markov blaze_prob_lang) Σ := Spec_updateGS spec_auth.

(** Resources required to track a [ProbLang] spec configuration. *)
From Stdlib Require Import Reals.
From iris.algebra Require Import auth excl gmap.
From iris.base_logic.lib Require Import invariants ghost_map.
From iris.prelude Require Import options.
From iris.proofmode Require Import proofmode.
From clutch.common Require Import con_language con_ectxi_language.
From clutch.con_prob_lang Require Import lang.


(** The CMRA for the spec [cfg]. *)
Class specG_con_prob_lang Σ := SpecGS {
  #[local] specG_con_prob_lang_prog :: ghost_mapG Σ nat expr;
  specG_con_prob_lang_prog_name : gname;

  #[local] specG_con_prob_lang_heap :: ghost_mapG Σ loc val;
  #[local] specG_con_prob_lang_tapes :: ghost_mapG Σ loc tape;

  specG_con_prob_lang_heap_name : gname;
  specG_con_prob_lang_tapes_name : gname;                      
}.

Class specGpreS Σ := SpecGPreS {
  specGpreS_prog_inG :: ghost_mapG Σ nat expr;
  specGpreS_heap :: ghost_mapG Σ loc val;
  specGpreS_tapes :: ghost_mapG Σ loc tape;
}.

Definition specΣ : gFunctors :=
  #[ghost_mapΣ loc val;
    ghost_mapΣ loc tape;
    ghost_mapΣ nat expr].
#[global] Instance subG_clutchGPreS {Σ} : subG specΣ Σ → specGpreS Σ.
Proof. solve_inG. Qed.

Definition to_tpool (tp : list expr) :gmap nat expr:= (map_seq 0 tp).
Lemma tpool_lookup tp j : to_tpool tp !! j = tp !! j.
Proof.
  unfold to_tpool. 
  by rewrite lookup_map_seq_0.
Qed.
Lemma to_tpool_insert tp j e :
  j < length tp →
  to_tpool (<[j:=e]> tp) = <[j:=e]> (to_tpool tp).
Proof.
  intros. apply: map_eq=> i. destruct (decide (i = j)) as [->|].
  - by rewrite tpool_lookup lookup_insert_eq list_lookup_insert_eq.
  - rewrite tpool_lookup lookup_insert_ne // list_lookup_insert_ne //.
    by rewrite tpool_lookup.
Qed.

Lemma to_tpool_app tp e :
  <[length tp:=e]> (to_tpool (tp)) = (to_tpool (tp++[e])).
Proof.
  intros. apply: map_eq=> i. destruct (decide (i = length tp)) as [->|].
  - rewrite lookup_insert_eq tpool_lookup lookup_app_r; last done.
    by rewrite Nat.sub_diag.
  - rewrite tpool_lookup lookup_insert_ne //.
    destruct (decide (i < length tp)).
    + by rewrite tpool_lookup lookup_app_l.
    + rewrite tpool_lookup !lookup_ge_None_2; first done.
      * rewrite length_app; simpl; lia.
      * lia.
Qed.

Section resources.
  Context `{!specG_con_prob_lang Σ}.
  Definition spec_prog_auth :=
    @ghost_map_auth _ _ _ _ _ specG_con_prob_lang_prog specG_con_prob_lang_prog_name (DfracOwn 1).
  Definition spec_heap_auth :=
    @ghost_map_auth _ _ _ _ _ specG_con_prob_lang_heap specG_con_prob_lang_heap_name (DfracOwn 1).
  Definition spec_tapes_auth  :=
    @ghost_map_auth _ _ _ _ _ specG_con_prob_lang_tapes specG_con_prob_lang_tapes_name (DfracOwn 1).

  Definition spec_auth (ρ : cfg) : iProp Σ :=
    spec_prog_auth (to_tpool ρ.1) ∗
    spec_heap_auth (ρ.2.(heap)) ∗
    spec_tapes_auth (ρ.2.(tapes)).

  Definition spec_prog_frag (j:nat) (e : expr) : iProp Σ :=
    (@ghost_map_elem _ _ _ _ _ specG_con_prob_lang_prog specG_con_prob_lang_prog_name j (DfracOwn 1) e).

  Definition spec_heap_frag (l : loc) v dq: iProp Σ :=
    (@ghost_map_elem _ _ _ _ _ specG_con_prob_lang_heap specG_con_prob_lang_heap_name l dq v).

  Definition spec_tapes_frag (l : loc) v dq: iProp Σ :=
    (@ghost_map_elem _ _ _ _ _ specG_con_prob_lang_tapes specG_con_prob_lang_tapes_name l dq v).
End resources.


(** Spec program  *)
Notation " j ⤇ e" := (spec_prog_frag j e) (at level 20) : bi_scope.

(** Spec heap *)
Notation "l ↦ₛ{ dq } v" := (@ghost_map_elem _ _ _ _ _ specG_con_prob_lang_heap specG_con_prob_lang_heap_name l dq v)
  (at level 20, format "l  ↦ₛ{ dq }  v") : bi_scope.
Notation "l ↦ₛ□ v" := (l ↦ₛ{ DfracDiscarded } v)%I
  (at level 20, format "l  ↦ₛ□  v") : bi_scope.
Notation "l ↦ₛ{# q } v" := (l ↦ₛ{ DfracOwn q } v)%I
  (at level 20, format "l  ↦ₛ{# q }  v") : bi_scope.
Notation "l ↦ₛ v" := (l ↦ₛ{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↦ₛ  v") : bi_scope.

(** Spec tapes *)
Notation "l ↪ₛ{ dq } v" := (@ghost_map_elem _ _ _ _ _ specG_con_prob_lang_tapes specG_con_prob_lang_tapes_name l dq v)
  (at level 20, format "l  ↪ₛ{ dq }  v") : bi_scope.
Notation "l ↪ₛ□ v" := (l ↪ₛ{ DfracDiscarded } v)%I
  (at level 20, format "l  ↪ₛ□  v") : bi_scope.
Notation "l ↪ₛ{# q } v" := (l ↪ₛ{ DfracOwn q } v)%I
  (at level 20, format "l  ↪ₛ{# q }  v") : bi_scope.
Notation "l ↪ₛ v" := (l ↪ₛ{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↪ₛ  v") : bi_scope.

Section theory.
  Context `{!specG_con_prob_lang Σ}.


  Lemma spec_auth_prog_agree es σ j e  :
    spec_auth (es, σ) -∗ j ⤇ e -∗ ⌜es!!j=Some e⌝.
  Proof.
    iIntros "[Ha _] Hf". simpl.
    iDestruct (ghost_map_lookup with "Ha Hf") as "<-".
    iPureIntro.
    by rewrite tpool_lookup. 
  Qed.

  
  Lemma spec_auth_prog_length es σ j e  :
    spec_auth (es, σ) -∗ j ⤇ e -∗ ⌜j<length es⌝.
  Proof.
    iIntros.
    iDestruct (spec_auth_prog_agree with "[$][$]") as "%".
    iPureIntro. by eapply lookup_lt_Some.
  Qed.

  Lemma spec_update_prog es σ j e e':
    spec_auth (es, σ) -∗ j ⤇ e ==∗ spec_auth (<[j:=e']>es, σ) ∗ j ⤇ e'.
  Proof.
    iIntros "[Ha ?] Hf".
    iDestruct (spec_auth_prog_length with "[$][$]") as "%".
    iMod (ghost_map_update with "Ha Hf") as "[??]". iFrame.
    iModIntro.
    by rewrite to_tpool_insert.
  Qed.

  Lemma spec_fork_prog es σ e :
    spec_auth (es, σ) ==∗ spec_auth (es++[e], σ) ∗ ∃ j, j ⤇ e.
  Proof.
    iIntros "[Ha ?]".
    iMod (ghost_map_insert with "Ha") as "[??]".
    { rewrite tpool_lookup. by apply lookup_ge_None_2. }
    rewrite to_tpool_app. by iFrame.
  Qed.

  
  (** Heap *)

  Lemma spec_auth_lookup_heap e1 σ1 l v dq:
    spec_auth (e1, σ1) -∗ l ↦ₛ{dq} v -∗ ⌜σ1.(heap) !! l = Some v⌝.
  Proof. iIntros "(_&H&_) H'/=".
         iApply (ghost_map_lookup with "H H'"). Qed.

  Lemma spec_auth_heap_alloc e σ v :
    spec_auth (e, σ) ==∗
    spec_auth (e, state_upd_heap <[ fresh_loc σ.(heap) := v ]> σ) ∗ fresh_loc σ.(heap) ↦ₛ v.
  Proof.
    iIntros "(? & Hheap &?) /=".
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
  Proof. iIntros "(?&?&H) H'/=".
         iApply (ghost_map_lookup with "[H] H'").
         iFrame.
  Qed.

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

Lemma spec_ra_init es σ `{specGpreS Σ} :
  ⊢ |==> ∃ _ : specG_con_prob_lang Σ,
      spec_auth (es, σ) ∗ ([∗ map] n↦e ∈ (to_tpool es), n ⤇ e) ∗ ([∗ map] l ↦ v ∈ σ.(heap), l ↦ₛ v) ∗ ([∗ map] α ↦ t ∈ σ.(tapes), α ↪ₛ t).
Proof.
  iMod (ghost_map_alloc (to_tpool es)) as "[%γE [He Hes]]".
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh Hls]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht Hαs]]".
  iExists (SpecGS _ _ γE _ _ γH γT).
  by iFrame.
Qed.

(** Tapes containing natural numbers defined as a wrapper over backend tapes *)
Definition nat_spec_tape `{specG_con_prob_lang Σ} l (N : nat) (ns : list nat) : iProp Σ :=
  ∃ (fs : list (fin (S N))), ⌜fin_to_nat <$> fs = ns⌝ ∗ l ↪ₛ (N; fs).

Notation "l ↪ₛN ( M ; ns )" := (nat_spec_tape l M ns)%I
       (at level 20, format "l ↪ₛN ( M ; ns )") : bi_scope.

Section spec_tape_interface.
  Context `{!specG_con_prob_lang Σ}.

  (** Helper lemmas to go back and forth between the user-level representation *)
(*       of tapes (using nat) and the backend (using fin) *)

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
  
  Lemma spec_tapeN_tapeN_contradict l N M ns ms:
    l ↪ₛN ( N;ns ) -∗ l↪ₛN (M;ms) -∗ False.
  Proof.
    iIntros "(%&<-&H1) (%&<-&H2)".
    by iDestruct (ghost_map_elem_ne with "[$][$]") as "%".
  Qed.


End spec_tape_interface.



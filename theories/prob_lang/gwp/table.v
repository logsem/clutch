From iris.base_logic.lib Require Import fancy_updates.
From stdpp Require Import list fin_maps gmap.
From clutch.prob_lang.gwp Require Export gen_weakestpre linked_list.
Set Default Proof Using "Type*".

(* TODO: move and upstream *)
Lemma list_to_map_list_insert `{Countable K} {V} i (k : K) (v v' : V) xs :
  NoDup xs.*1 →
  xs !! i = Some (k, v') →
  list_to_map (<[i:=(k, v)]> xs) = <[k:=v]> (list_to_map (M := gmap K V) xs).
Proof.
  induction xs as [|[k' w] xs IH] in i, k, v, v' |-*; [done|].
  rewrite lookup_cons. destruct i => /=.
  - intros ? [= -> <-]. rewrite insert_insert. done.
  - intros [Hk' Hxs]%NoDup_cons Hlook => /=.
    assert (k ≠ k').
    { intros <-. apply Hk'. apply elem_of_list_fmap.
      eexists (k, v'). split; [done|].
      by eapply elem_of_list_lookup_2. }
    rewrite insert_commute; [|done].
    by setoid_rewrite IH.
Qed.

Lemma NoDup_fst_list_alter_pair {K V} (xs : list (K * V)) k v w i :
  xs !! i = Some (k, w) →
  NoDup xs.*1 →
  NoDup (alter (λ _ : K * V, (k, v)) i xs).*1.
Proof.
  induction xs as [|[k' w'] xs IH] in i, k, v, w |-*; [done|].
  rewrite lookup_cons. destruct i => /=.
  { by intros [= -> ->]. }
  rewrite !NoDup_cons.
  intros Hlook [Hk' Hxs].
  split; [|by eapply IH].
  rewrite elem_of_list_fmap.
  intros ([k'' w''] & ? & H). simplify_eq/=.
  apply elem_of_list_lookup_1 in H as (j &?).
  eapply Hk'. apply elem_of_list_fmap.
  (* Why is this necessary? *)
  replace list_alter with
    (alter (Alter := (list_alter (A := K * V)))) in H; [|done].
  destruct (decide (i = j)) as [<-|].
  - rewrite list_lookup_alter Hlook in H. simplify_eq/=.
    eexists (_, _). split; [done|]. apply elem_of_list_lookup. eauto.
  - rewrite list_lookup_alter_ne in H; [|done].
    eexists (_, _). split; [done|]. apply elem_of_list_lookup. eauto.
Qed.

Module Table.

  Definition empty : val := λ: <>, ref (LinkedList.empty #()).

  Definition insert : val :=
    λ: "key" "value" "m",
      let: "l" := !"m" in
      let: "test" := λ: "p", Fst "p" = "key" in
      match: LinkedList.find "l" "test" with
        NONE =>
          "m" <- LinkedList.insert "l" ("key", "value")
      | SOME "r" =>
          let: "idx" := Fst "r" in
          LinkedList.alter "l" (λ: <>, ("key", "value")) "idx"
      end.

  Definition lookup : val :=
    λ: "key" "m",
      let: "l" := !"m" in
      let: "test" := λ: "p", Fst "p" = "key" in
      let: "res" := LinkedList.find "l" "test" in
      match: "res" with
        NONE => NONE
      | SOME "p" =>
          let, ("i", ("k", "v")) := "p" in
          SOME "v"
      end.

End Table.

Section Table.
  Context `{invGS_gen hlc Σ} `{g : !GenWp Σ}.

  #[local] Notation "l G↦ dq v" := (gwp_pointsto g l dq v)
    (at level 20, dq custom dfrac at level 1, format "l  G↦ dq  v") : bi_scope.

  Context `[Countable K, !Inject K val].
  Context `[V : Type, !Inject V val].

  Implicit Types (k : K).

  Import Table.

  Definition is_table (d : val) (m : gmap K V) : iProp Σ :=
    ∃ (l1 l2 : loc) (xs : list (K * V)),
      ⌜d = #l1⌝ ∗ ⌜m = list_to_map xs⌝ ∗ ⌜NoDup (fst <$> xs)⌝ ∗
      l1 G↦ #l2 ∗ is_linked_list (g := g) l2 xs.

  #[global] Instance is_linked_list_Timeless d m :
    Timeless (is_table d m).
  Proof. apply _. Qed.

  Lemma gwp_table_empty E :
    G{{{ True }}}
      empty #() @ g; E
    {{{ d, RET d; is_table d ∅ }}}.
  Proof.
    iIntros (Ψ) "_ HΨ".
    gwp_rec.
    gwp_apply gwp_linked_list_empty; [done|].
    iIntros (l) "Hl".
    gwp_alloc l' as "Hl'".
    iModIntro. iApply "HΨ".
    iFrame. iPureIntro.
    do 2 (split; [done|]). constructor.
  Qed.

  Lemma gwp_table_insert (k : K) v d m E :
    val_is_unboxed (inject k) →
    G{{{ is_table d m }}}
      insert (inject k) (inject v) d @ g; E
    {{{ RET #(); is_table d (<[ k := v ]> m) }}}.
  Proof.
    iIntros (? Ψ) "Hm HΨ".
    rewrite /insert. gwp_pures.
    iDestruct "Hm" as (??? -> -> ?) "[Hl1 Hl2]".
    gwp_load.
    gwp_pures.
    set (test := (λ '(k', v), k = k') : K * V → Prop).
    gwp_apply (gwp_linked_list_find _ _ _ _ test with "[] Hl2").
    { iIntros ([k' w] ?) "!# _ H". gwp_pures.
      case_bool_decide; simplify_eq/=.
      - rewrite bool_decide_eq_true_2 //. by iApply "H".
      - rewrite bool_decide_eq_false_2; [|intros ?; simplify_eq]. by iApply "H". }
    iIntros "Hl2".
    destruct (list_find test xs) as [(idx & [k' v']) |] eqn:Hfind.
    - gwp_pures.
      gwp_apply (gwp_linked_list_alter _ _ _ (λ _, (k, v)) with "[] Hl2").
      { iIntros ([] ?) "!# _ H". gwp_pures. iModIntro. by iApply "H". }
      iIntros "Hl2". iApply "HΨ".
      iFrame. iPureIntro.
      rewrite /test in Hfind.
      apply list_find_Some in Hfind as (? & <- & _).
      split; [done|]. split.
      + pose proof (list_insert_alter xs idx (k, v)) as Halt.
        rewrite /alter in Halt. rewrite -Halt.
        by erewrite list_to_map_list_insert.
      + by eapply NoDup_fst_list_alter_pair.
    - gwp_pures.
      gwp_apply (gwp_linked_list_insert (k, v) with "Hl2").
      iIntros (l2') "Hl2'". gwp_store.
      iModIntro. iApply "HΨ". iFrame. iPureIntro.
      rewrite list_to_map_cons /=.
      do 2 (split; [done|]).
      apply list_find_None in Hfind.
      apply NoDup_cons.
      split; [|done].
      intros ([]&?&?)%elem_of_list_fmap.
      simplify_eq/=.
      eapply Forall_forall in Hfind; [|done].
      simpl in Hfind. contradiction.
  Qed.

  Lemma gwp_table_lookup (k : K) d m E :
    val_is_unboxed (inject k) →
    G{{{ is_table d m }}}
      lookup (inject k) d @ g; E
    {{{ RET (inject (m !! k)); is_table d m }}}.
  Proof.
    iIntros (? Ψ) "Hm HΨ".
    iDestruct "Hm" as (??? -> -> ?) "[Hl1 Hl2]".
    rewrite /lookup. gwp_pures.
    gwp_load. gwp_pures.
    gwp_apply (gwp_linked_list_find _ _ _ _ (λ '(k', v), k = k') with "[] Hl2").
    { iIntros ([k' v] ?) "!> _ HΨ". gwp_pures. iModIntro.
      destruct (decide (k = k')) as [<-|].
      - rewrite !bool_decide_eq_true_2 //. by iApply "HΨ".
      - rewrite !bool_decide_eq_false_2 //; [|intros [=]; simplify_eq].
        by iApply "HΨ". }
    iIntros "Hl2".
    destruct (list_find _ xs) as [(i & [k' v']) | ] eqn:Heq.
    - gwp_pures. iModIntro.
      assert (list_to_map xs !! k = Some v') as ->.
      { apply list_find_Some in Heq as (?%elem_of_list_lookup_2 & <- & _).
        by erewrite elem_of_list_to_map_1. }
      iApply "HΨ". by iFrame.
    - gwp_pures. iModIntro.
      assert (list_to_map xs !! k = None) as ->.
      { apply not_elem_of_list_to_map_1.
        intros ([] & ? &?)%elem_of_list_fmap; simplify_eq/=.
        eapply list_find_None, Forall_forall in Heq; [|done].
        simpl in Heq. contradiction. }
      iApply "HΨ". by iFrame.
  Qed.

End Table.

(** * library for linkedlist specific for hashmap *)
From tachis.tachis Require Export expected_time_credits ert_weakestpre problang_wp proofmode
  derived_laws cost_models ert_rules.
From tachis.prob_lang Require Import notation tactics metatheory lang.
From iris.proofmode Require Export proofmode.
From Coq Require Export Reals Psatz.
From Coquelicot Require Export Hierarchy.
Require Import Lra.
From tachis.tachis.examples.hashmap Require Export map.

Set Default Proof Using "Type*".

Section list_code.
  Context `{!tachisGS Σ CostTick}.

  Fixpoint isList (l : val) (xs : list nat) : iProp Σ :=
    match xs with
    | [] => ⌜l = NONEV⌝
    | x :: xs => ∃ (hd : loc) l', ⌜l = SOMEV #hd⌝ ∗ hd ↦ (#x, l')%V ∗ isList l' xs
  end.

  Definition insert : val :=
  rec: "insert" "l" "x" :=
    match: "l" with
      NONE => SOME (ref ("x", NONEV))
    | SOME "p" =>
        let: "v" := !"p" in
        tick (#1) ;;
        let: "h" := Fst ("v") in
        let: "t" := Snd ("v") in
        if: "h" = "x" then SOME "p"
        else
          "p" <- ("h", "insert" "t" "x");;
          SOME "p"
    end.

  Lemma wp_insert_new (l : val) (x:nat) (xs : list nat) E:
    x∉xs -> 
    {{{isList l xs ∗ ⧖ (length xs) }}}
      insert l #x @E
      {{{l, RET l; isList l (xs ++ x::[])}}}.
  Proof.
    revert xs l.
    induction xs.
    all: simpl.
    - iIntros (l Hnotin Φ) "[% _] HΦ".
      subst. rewrite /insert.
      wp_pures.
      wp_alloc l as "Hl". wp_pures.
      iModIntro.
      iApply "HΦ".
      iExists _, _. iFrame. done.
    - iIntros (l Hnotin Φ) "[(%&%&->&H1&H2)Hx] HΦ".
      rewrite /insert.
      wp_pures.
      wp_load. iIntros "H1". wp_pures.
      iAssert (⧖ (length xs + 1))%I with "[Hx]" as "Hx".
      { iApply (etc_irrel with "[$]"). case_match; simpl; lra. }
      wp_pure; last first.
      + do 8 wp_pure. rewrite -/insert.
        wp_pure. case_bool_decide.
        { set_solver. }
        wp_pures.
        wp_apply (IHxs with "[$H2 Hx]").
        { set_solver. }
        { iApply etc_irrel; last done. lra. }
        iIntros (l) "Hl".
        wp_pures. wp_store. iIntros "H1".
        wp_pures. iModIntro. iApply "HΦ".
        iExists _, _. iFrame. done.
      + assert (0<=length xs)%R; last lra.
        apply pos_INR.
  Qed.

  Lemma wp_insert_old (l : val) (x:nat) (xs : list nat) E:
    x∈xs -> 
    {{{isList l xs ∗ ⧖ (length xs) }}}
      insert l #x@E
      {{{l, RET l; isList l (xs)}}}.
  Proof.
    revert xs l.
    induction xs.
    all: simpl.
    - iIntros (l Hin Φ) "[% _] HΦ".
      set_solver.
    - iIntros (l Hin Φ) "[(%&%&->&H1&H2)Hx] HΦ".
      rewrite /insert.
      wp_pures.
      wp_load. iIntros "H1". wp_pures.
      iAssert (⧖ (length xs + 1))%I with "[Hx]" as "Hx".
      { iApply (etc_irrel with "[$]"). case_match; simpl; lra. }
      wp_pure; last first.
      + do 8 wp_pure. rewrite -/insert.
        wp_pure. case_bool_decide.
        * inversion H. apply Nat2Z.inj' in H1. subst.
          wp_pures. iModIntro. iApply "HΦ".
          iExists _, _. iFrame. done.
        * wp_pures.
          wp_apply (IHxs with "[$H2 Hx]").
          { set_solver. }
          { iApply etc_irrel; last done. lra. }
          iIntros (l) "Hl".
          wp_pures. wp_store. iIntros "H1".
          wp_pures. iModIntro. iApply "HΦ".
          iExists _, _. iFrame. done.
      + assert (0<=length xs)%R; last lra.
        apply pos_INR.
  Qed.

  Lemma wp_insert_general (l : val) (x:nat) (xs : list nat) E:
    {{{isList l xs ∗ ⧖ (length xs) }}}
      insert l #x @E
      {{{l, RET l; ∃ xs', isList l (xs') ∗ ⌜length xs<=length xs'<=1+length xs⌝}}}.
  Proof.
    pose proof ExcludedMiddle (x∈xs) as [|].
    - iIntros (?) "[??] HΦ". wp_apply (wp_insert_old with "[$]"); first done.
      iIntros. iApply "HΦ". iExists _. iFrame. iPureIntro.
      lia.
    - iIntros (?) "[??]HΦ".  wp_apply (wp_insert_new with "[$]"); first done.
      iIntros. iApply "HΦ". iExists _. iFrame. iPureIntro.
      rewrite app_length. simpl. lia.
  Qed.

  Definition lookup : val :=
  rec: "lookup" "l" "x" :=
    match: "l" with
      NONE => #false
    | SOME "p" =>
        let: "v" := !"p" in
        tick (#1) ;;
        let: "h" := Fst ("v") in
        let: "t" := Snd ("v") in
        if: "h" = "x" then #true
        else
          "lookup" "t" "x"
    end.

  Lemma wp_lookup_notin (l : val) (x:nat) (xs : list nat) E:
    x∉xs -> 
    {{{isList l xs ∗ ⧖ (length xs) }}}
      lookup l #x@E
      {{{ RET #false; isList l (xs)}}}.
  Proof.
    revert xs l.
    induction xs.
    all: simpl.
    - iIntros (l Hnotin Φ) "[% _] HΦ".
      subst. rewrite /lookup.
      wp_pures.
      iApply "HΦ". iFrame. done.
    - iIntros (l Hnotin Φ) "[(%&%&->&H1&H2)Hx] HΦ".
      rewrite /lookup.
      wp_pures.
      wp_load. iIntros "H1". wp_pures.
      iAssert (⧖ (length xs + 1))%I with "[Hx]" as "Hx".
      { iApply (etc_irrel with "[$]"). case_match; simpl; lra. }
      wp_pure; last first.
      + do 8 wp_pure. rewrite -/lookup.
        wp_pure. case_bool_decide.
        { set_solver. }
        wp_pures.
        wp_apply (IHxs with "[$H2 Hx]").
        { set_solver. }
        { iApply etc_irrel; last done. lra. }
        iIntros "Hl".
        iApply "HΦ".
        iExists _, _. iFrame. done.
      + assert (0<=length xs)%R; last lra.
        apply pos_INR.
  Qed.

  Lemma wp_lookup_in (l : val) (x:nat) (xs : list nat) E:
    x∈xs -> 
    {{{isList l xs ∗ ⧖ (length xs) }}}
      lookup l #x @E
      {{{ RET #true; isList l (xs)}}}.
  Proof.
    revert xs l.
    induction xs.
    all: simpl.
    - iIntros (l Hin Φ) "[% _] HΦ". set_solver.
    - iIntros (l Hin Φ) "[(%&%&->&H1&H2)Hx] HΦ".
      rewrite /lookup.
      wp_pures.
      wp_load. iIntros "H1". wp_pures.
      iAssert (⧖ (length xs + 1))%I with "[Hx]" as "Hx".
      { iApply (etc_irrel with "[$]"). case_match; simpl; lra. }
      wp_pure; last first.
      + do 8 wp_pure. rewrite -/lookup.
        wp_pure. case_bool_decide.
        * inversion H. apply Nat2Z.inj' in H1. subst.
          wp_pures. iModIntro. iApply "HΦ".
          iExists _, _. iFrame. done.
        * wp_pures. wp_apply (IHxs with "[$H2 Hx]").
          { set_solver. }
          { iApply etc_irrel; last done. lra. }
          iIntros "Hl". iApply "HΦ".
          iExists _,_; iFrame. done.
      + assert (0<=length xs)%R; last lra.
        apply pos_INR.
  Qed.

  Lemma wp_lookup_general (l : val) (x:nat) (xs : list nat) E:
    {{{isList l xs ∗ ⧖ (length xs) }}}
      lookup l #x @ E
      {{{(b:bool), RET #b; isList l (xs) ∗ ⌜if b then x∈ xs else x∉ xs⌝}}}.
  Proof.
    pose proof ExcludedMiddle (x∈xs) as [|].
    - iIntros (?) "[??] HΦ". wp_apply (wp_lookup_in with "[$]"); first done.
      iIntros. iApply "HΦ". iFrame. done. 
    - iIntros (?) "[??]HΦ".  wp_apply (wp_lookup_notin with "[$]"); first done.
      iIntros. iApply "HΦ". by iFrame. 
  Qed.

End list_code.

From Coq Require Import Reals Psatz.
From clutch.prob_lang Require Import lang notation.
From clutch.caliper Require Import primitive_laws proofmode adequacy.
From clutch.caliper.examples Require Import lazy_real.

(** A [treap] is a Binary Search Tree (BST) with two attributes at each node,
    [key] and [priority]. The [priority] attribute is a value sampled uniformly
    at random at insertion time.

    A treap maintains two invariants:

      1. It is always sorted according to [key] (left subtree is smaller, right
         subtree is greater), i.e. inorder traversal of the nodes is the same as
         the sorted order of the keys.

      2. It is heap-ordered (max heap order): the [priority] for any non-leaf
         node must be greater than or equal to the priority of its children.

   This ensures that, with high probability, the height is O(log n). *)

(** We will use the [lazy_real.v] construction for (lazily) sampling priorities.
    This ensures that no collisions will occur. As a result, termination of the
    insertion procedure both relies on induction in the tree height but also on
    the fact that comparing to lazily sampled reals almost-surely terminates.
    Worst case, one insertion into a tree [t] will have to make [height(t)]
    priority comparisons to rebalance the tree and maintain the max heap order
    invariant. *)

(** A binary (search) tree  *)
Inductive tree (K : Type) : Type :=
| leaf
| node (key : K) (left right : tree K).

Arguments leaf {_}.
Arguments node {_}.

(** For our termination proof, we don't really care about properties of the tree
    other than its height. This is to ensure that we have enough "fuel" left for
    comparing [lazy_real]s. *)
Section bst.
  Context {K : Type}.

  Fixpoint bst_height (t : tree K) : nat :=
    match t with
    | leaf => 0
    | node _ l r => 1 + bst_height l + bst_height r
    end.

  (** If [T1], [T2] and [T3] are subtrees of the tree rooted with [y]
      (on left side) or [x] (on right side)

                y                               x
               / \     Right Rotation          / \
              x  T3    – – – – – – – >       T1  y
             / \       < - - - - - - -          / \
            T1 T2     Left Rotation           T2  T3
   *)
  Definition bst_rotate_left (x : tree K) : tree K :=
    match x with
    | node xkey T1 (node ykey T2 T3) => node ykey (node xkey T1 T2) T3
    | _ => x
    end.

  Definition bst_rotate_right (y : tree K) : tree K :=
    match y with
    | node ykey (node xkey T1 T2) T3 => node xkey T1 (node ykey T2 T3)
    | _ => y
    end.

End bst.

(** We represent treaps as an option of a reference to a 4-tuple [(key,
    priority, left, right)]. *)

Definition get_key : val :=
  λ: "node", Fst (Fst (Fst !"node")).
Definition get_priority : val :=
  λ: "node", Snd (Fst (Fst !"node")).
Definition get_left : val :=
  λ: "node", Snd (Fst !"node").
Definition get_right : val :=
  λ: "node", Snd !"node".

Definition set_left : val :=
  λ: "node" "new_left",
    let, ("key", "priority", "left", "right") := !"node" in
    "node" <- ("key", "priority", "new_left", "right").
Definition set_right : val :=
  λ: "node" "new_right",
    let, ("key", "priority", "left", "right") := !"node" in
    "node" <- ("key", "priority", "left", "new_right").

Definition rotate_right : val :=
  λ: "root",
    let:m "y" := "root" in
    match: get_left "y" with
    | NONE => "root"
    | SOME "x" =>
        let: "T2" := get_right "x" in
        set_right "x" (SOME "y");;
        set_left "y" "T2";;
        SOME "x"
    end.

Definition rotate_left : val :=
  λ: "root",
    let:m "x" := "root" in
    match: get_right "x" with
    | NONE => "root"
    | SOME "y" =>
        let: "T2" := get_left "y" in
        set_left "y" (SOME "x");;
        set_right "x" "T2";;
        SOME "y"
    end.

Definition new_node : val :=
  λ: "key", SOME (ref ("key", lazy_real.init #(), NONEV, NONEV)).

Definition unSOME : val :=
  λ: "m", match: "m" with | NONE => #() #() | SOME "v" => "v" end.

(** To insert a new key [x] into a treap, generate a random priority [y] for
    [x]. Binary search for [x] in the tree, and create a new node at the leaf
    position where the binary search determines a node for [x] should exist.
    Then, as long as [x] is not the root of the tree and has a larger priority
    number than its parent [z], perform a tree rotation that reverses the
    parent-child relation between [x] and [z]. *)
Definition insert : val :=
  rec: "insert" "root" "key" :=
    match: "root" with
    | NONE => new_node "key"
    | SOME "r" =>
        let, ("rkey", "rpriority", "rleft", "rright") := !"r" in

        if: "key" = "rkey" then "root"

        else if: "key" < "rkey" then

          (* Insert in left subtree *)
          let: "new_left" := "insert" "rleft" "key" in
          set_left "r" "new_left";;

          (* Rebalance relative to priority  *)
          if: lazy_real.cmp (get_priority (unSOME "new_left")) "rpriority" = #1 then
            rotate_right "root"
          else "root"

        else

          (* Insert in right subtree *)
          let: "new_right" := "insert" "rright" "key" in
          set_right "r" "new_right";;

          (* Rebalance relative to priority  *)
          if: lazy_real.cmp (get_priority (unSOME "new_right")) "rpriority" = #1 then
            rotate_left "root"
          else "root"
    end.

Section spec.
  Context `{!caliperG lazy_real.model Σ}.

  Fixpoint is_treap (v : val) (t : tree Z) : iProp Σ :=
    match t with
    | leaf => ⌜v = NONEV⌝
    | node k l r =>
        ∃ (ℓ : loc) (p vl vr : val) (ps : list _),
          ⌜v = SOMEV #ℓ⌝ ∗ ℓ ↦ (#k, p, vl, vr)%V ∗ lazy_no ps p ∗
          is_treap vl l ∗ is_treap vr r
  end.

  Lemma wp_new_node (k : Z) E :
    ⟨⟨⟨ True ⟩⟩⟩
      new_node #k @ E
    ⟨⟨⟨ v, RET v; is_treap v (node k leaf leaf) ⟩⟩⟩.
  Proof.
    iIntros (?) "_ H". rewrite /new_node.
    wp_pures.
    wp_apply rwp_init; [done|].
    iIntros (v) "Hp".
    wp_alloc l as "Hl".
    wp_pures.
    iModIntro.
    iApply "H".
    simpl.
    iExists _, _, _, _, _.
    iFrame. done.
  Qed.

  Lemma wp_rotate_right v t E :
    ⟨⟨⟨ is_treap v t ⟩⟩⟩
      rotate_right v @ E
    ⟨⟨⟨ v, RET v; is_treap v (bst_rotate_right t) ⟩⟩⟩.
  Proof.
    iIntros (Ψ) "Ht HΨ". wp_rec.
    destruct t as [|ykey l T3].
    { iDestruct "Ht" as %->. wp_pures. by iApply "HΨ". }
    iSimpl in "Ht".
    iDestruct "Ht" as (ℓ p vl vr ps) "(-> & Hℓ & Hp & Hl & Hr)".
    wp_pures.
    rewrite /get_left; wp_load; wp_pures.
    destruct l as [|xkey T1 T2].
    { iDestruct "Hl" as %->. wp_pures. iApply "HΨ".
      iModIntro. simpl. iExists _, _, _, _, _. by iFrame. }
    iSimpl in "Hl".
    iDestruct "Hl" as (ℓx px vlx vrx psx) "(-> & Hℓx & Hpx & Hlx & Hrx)".
    wp_pures.
    rewrite /get_right; wp_load; wp_pures.
    rewrite /set_right; wp_load; wp_pures; wp_store.
    rewrite /set_left; wp_load; wp_pures; wp_store; wp_pures.
    iApply "HΨ".
    iModIntro. simpl. iFrame. auto. 
  Qed.

  Lemma wp_rotate_left v t E :
    ⟨⟨⟨ is_treap v t ⟩⟩⟩
      rotate_left v @ E
    ⟨⟨⟨ v, RET v; is_treap v (bst_rotate_left t) ⟩⟩⟩.
  Proof.
    iIntros (Ψ) "Ht HΨ". wp_rec.
    destruct t as [|xkey T1 r].
    { iDestruct "Ht" as %->. wp_pures. by iApply "HΨ". }
    iSimpl in "Ht".
    iDestruct "Ht" as (ℓ p vl vr ps) "(-> & Hℓ & Hp & Hl & Hr)".
    wp_pures.
    rewrite /get_right; wp_load; wp_pures.
    destruct r as [|ykey T2 T3].
    { iDestruct "Hr" as %->. wp_pures. iApply "HΨ".
      iModIntro. simpl. iExists _, _, _, _, _. by iFrame. }
    iSimpl in "Hr".
    iDestruct "Hr" as (ℓy py vly vry psy) "(-> & Hℓy & Hpy & Hly & Hry)".
    wp_pures.
    rewrite /get_left; wp_load; wp_pures.
    rewrite /set_left; wp_load; wp_pures; wp_store.
    rewrite /set_right; wp_load; wp_pures; wp_store; wp_pures.
    iApply "HΨ".
    iModIntro. simpl. iExists _, _, _, _, _. iFrame. auto. 
  Qed.

  Lemma wp_insert v t E (z : Z) N :
    bst_height t ≤ N →
    ⟨⟨⟨ is_treap v t ∗ cmps N ⟩⟩⟩
      insert v #z @ E
    ⟨⟨⟨ k l r M w, RET w;
        is_treap w (node k l r) ∗ ⌜bst_height t ≤ bst_height (node k l r) ≤ bst_height t + 1⌝ ∗
        cmps M ∗ ⌜N - bst_height t ≤ M⌝ ⟩⟩⟩.
  Proof.
    iInduction t as [|k l r] "IH" forall (v N);
      iIntros (Hheight Ψ) "(Ht & Hcmps) HΨ".
    - iSimpl in "Ht". iDestruct "Ht" as %->.
      rewrite /insert. wp_pures.
      wp_apply wp_new_node; [done|].
      iIntros (t) "Ht".
      iApply ("HΨ" $! z leaf leaf).
      iFrame. simpl in *.
      iSplit; iPureIntro; lia.
    - rewrite {3}/insert. wp_pures; rewrite -/insert.
      iSimpl in "Ht".
      iDestruct "Ht" as (ℓ p vl vr ps) "(-> & Hℓ & Hp & Hl & Hr)".
      wp_pures. wp_load; wp_pures.

      case_bool_decide; wp_pures.
      { iApply ("HΨ" $! _ l t1). iModIntro. iFrame.
        iSplit; auto with lia. }
      simpl in Hheight.

      case_bool_decide; wp_pures.
      + wp_apply ("IH" $! _ N with "[] [$]").
        { iPureIntro. lia. }
        iIntros (k1 l1 r1 M vl') "(Hvl' & % & Hcmps & %)".
        wp_pures.
        rewrite /set_left; wp_load; wp_store; wp_pures.
        iSimpl in "Hvl'".
        iDestruct "Hvl'" as (ℓy py vly vry psy) "(-> & Hℓy & Hpy & Hly & Hry)".
        rewrite /unSOME /get_priority; wp_load; wp_pures.
        wp_apply (rwp_cmp with "[$]"); [lia|].
        iIntros (c z1 z2) "(Hz1 & Hz2 & Hcmps)".
        wp_pures.
        case_bool_decide; wp_pures.
        * wp_apply (wp_rotate_right _ (node _ (node _  _ _) _) with "[-HΨ Hcmps]").
          { simpl. 
            iFrame "Hℓ Hz2".
            iSplit; [done|].
            iFrame "Hℓy Hz1".
            by iFrame. }
          iIntros (w) "Hw".
          iApply "HΨ". iFrame.
          simpl in *.
          iSplit; iPureIntro; lia.
        * iApply ("HΨ" $! _ (node _ l1 r1) t1).
          iFrame "Hcmps".
          iModIntro. iSplitL.
          { iExists _, _, _, _, _. rewrite -/is_treap.
            iSplit; [done|]. iFrame "Hℓ Hz2 Hr".
            iExists _, _, _, _, _.
            iSplit; [done|]. iFrame. }
          simpl in *.
          iSplit; iPureIntro; lia.
      + wp_apply ("IH1" $! _ N with "[] [$]").
        { iPureIntro. lia. }
        iIntros (k1 l1 r1 M vl') "(Hvl' & % & Hcmps & %)".
        wp_pures.
        rewrite /set_right; wp_load; wp_store; wp_pures.
        iSimpl in "Hvl'".
        iDestruct "Hvl'" as (ℓy py vly vry psy) "(-> & Hℓy & Hpy & Hly & Hry)".
        rewrite /unSOME /get_priority; wp_load; wp_pures.
        wp_apply (rwp_cmp with "[$]"); [lia|].
        iIntros (c z1 z2) "(Hz1 & Hz2 & Hcmps)".
        wp_pures.
        case_bool_decide; wp_pures.
        * wp_apply (wp_rotate_left _ (node _ _ (node _ _ _)) with "[-HΨ Hcmps]").
          { simpl. iExists _, _, _, _, _.
            iSplit; [done|]. iFrame "Hℓ Hz2 Hl".
            iExists _, _, _, _, _.
            iSplit; [done|]. iFrame "Hℓy". iFrame. }
          iIntros (w) "Hw".
          iApply "HΨ". iFrame.
          simpl in *.
          iSplit; iPureIntro; lia.
        * iApply ("HΨ" $! _ l (node _ l1 r1)). iFrame.
          iModIntro. iSplit; [auto|].
          simpl in *.
          iSplit; iPureIntro; try lia.
  Qed.

End spec.

Definition new_treap : val :=
  λ: <>, ref NONEV.

Definition insert_treap : val :=
  λ: "t" "k", "t" <- insert !"t" "k".

Definition runner : expr :=
  let: "t" := new_treap #() in
  insert_treap "t" #3;;
  insert_treap "t" #2;;
  insert_treap "t" #5.

Section runner_spec.
  Context `{!caliperG lazy_real.model Σ}.

  Definition treap (l : loc) (t : tree Z) : iProp Σ :=
    ∃ v, l ↦ v ∗ is_treap v t.

  Lemma wp_new_treap E :
    ⟨⟨⟨ True ⟩⟩⟩
      new_treap #() @ E
    ⟨⟨⟨ l, RET #l; treap l leaf ⟩⟩⟩.
  Proof.
    iIntros (?) "_ H". rewrite /new_treap.
    wp_pures.
    wp_alloc l as "Hl".
    iModIntro.
    iApply "H".
    iExists _.
    by iFrame.
  Qed.

  Lemma wp_insert_treap l t (k : Z) E N :
    bst_height t ≤ N →
    ⟨⟨⟨ treap l t ∗ cmps N ⟩⟩⟩
      insert_treap #l #k @ E
    ⟨⟨⟨ t' M, RET #();
        treap l t' ∗ ⌜bst_height t ≤ bst_height t' ≤ bst_height t + 1⌝ ∗
        cmps M ∗ ⌜N - bst_height t ≤ M⌝
    ⟩⟩⟩.
  Proof.
    iIntros (??) "[(%v & Hl & Ht) Hcmps] H". rewrite /insert_treap.
    wp_pures. wp_load.
    wp_apply (wp_insert with "[$]"); [done|].
    iIntros (?????) "(Ht & % & Hcmps & %)".
    wp_store. iModIntro.
    iApply "H". iFrame. auto. 
  Qed.

  Lemma wp_runner :
    ⟨⟨⟨ cmps 3 ⟩⟩⟩
      runner
    ⟨⟨⟨ v, RET v; True ⟩⟩⟩.
  Proof.
    iIntros (Ψ) "Hcmps HΨ". rewrite /runner.
    wp_apply wp_new_treap; [done|].
    iIntros (v) "Ht".
    wp_pures.
    wp_apply (wp_insert_treap with "[$Ht $Hcmps]"); [simpl; lia|].
    iIntros (??) "/= (Ht & % & Hcmps & %)".
    wp_pures.
    wp_apply (wp_insert_treap with "[$Ht $Hcmps]"); [simpl; lia|].
    iIntros (??) "/= (Ht & % & Hcmps & %)".
    wp_pures.
    wp_apply (wp_insert_treap with "[$Ht $Hcmps]"); [simpl; lia|].
    iIntros (??) "/= (Ht & % & Hcmps & %)".
    by iApply "HΨ".
  Qed.

End runner_spec.

Notation σ₀ := {| heap := ∅; tapes := ∅ |}.
Notation almost_surely_terminates ρ := (SeriesC (lim_exec ρ) = 1%R).

Theorem runner_terminates :
  almost_surely_terminates (runner, σ₀).
Proof.
  eapply Rle_antisym; [done|].
  transitivity (SeriesC (lim_exec ((true, true, 3%nat) : mstate model))).
  { by rewrite iter_two_coins_terminates. }
  eapply (rwp_soundness_mass (δ := model) (tprΣ model)).
  iIntros (?) "Ha".
  wp_apply (wp_runner with "[Ha]"); [|done].
  iExists _, _. eauto with lia.
Qed.


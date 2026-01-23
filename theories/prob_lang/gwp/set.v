From stdpp Require Import strings list pretty gmap.
From iris.base_logic.lib Require Import fancy_updates.
From clutch.prob_lang Require Export gwp.list.

Definition set_empty : val := λ: <>, [].

Definition set_add : val :=
  λ: "x" "s",
    if: list_mem "x" "s"
    then  "s"
    else  "x" :: "s".

Notation "{[ x ]}" := (set_add x (set_empty #())) (at level 1, format "{[ x ]}") : expr_scope.

Notation "{[ x ; y ; .. ; z ]}" :=
  (set_add x (set_add y .. (set_add z (set_empty #())) ..)) : expr_scope.

Definition set_mem := list_mem.

Definition set_iter := list_iter.

Definition set_foldl := list_fold.

Definition set_forall := list_forall.

Definition set_cardinal := list_length.

Definition set_subseteq : val :=
  λ: "x" "y", list_forall (λ: "e", set_mem "e" "y") "x".

Definition set_equal : val :=
  λ: "x" "y", (set_subseteq "x" "y") && (set_subseteq "y" "x").

Set Default Proof Using "Type".

Section set_specs.
  Context `{invGS_gen hlc Σ} `{g : !GenWp Σ}.
  Context `[Countable A, !Inject A val].

  Implicit Types x : A.

  Definition is_set (X : gset A) (v : val) : Prop :=
    ∃ (l : list A), is_list l v ∧ X = list_to_set l ∧ NoDup l ∧ set_Forall (λ a, val_is_unboxed (inject a)) X .

  Lemma gwp_set_empty s E :
    G{{{ True }}}
      set_empty #() @ s; E
    {{{ v, RET v; ⌜is_set ∅ v⌝}}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    gwp_rec. gwp_pures.
    iModIntro. iApply "HΦ".
    iPureIntro.
    exists [].
    do 2 (split; [done|]).
    split; [by apply NoDup_nil|].
    apply set_Forall_empty.
  Qed.

  Lemma gwp_set_add x X v s E :
    val_is_unboxed (inject x) →
    G{{{ ⌜is_set X v⌝ }}}
      set_add (inject x) v @ s; E
    {{{ v, RET v; ⌜is_set ({[ x ]} ∪ X) v⌝}}}.
  Proof.
    iIntros (? Φ (l & ? & -> & Hdup & Hunbox)) "HΦ".
    gwp_rec; gwp_pures.
    gwp_apply (gwp_list_mem with "[//]"); [done|].
    iIntros ([] Hb); gwp_if.
    - iApply "HΦ". iPureIntro.
      exists l. set_solver.
    - gwp_apply (gwp_list_cons with "[//]").
      iIntros (v' Hv').
      iApply "HΦ". iPureIntro.
      eexists (_ :: _).
      repeat split; try set_solver.
      apply NoDup_cons.
      destruct Hb; set_solver.
  Qed.

  Lemma gwp_set_mem x X v s E :
    val_is_unboxed (inject x) →
    G{{{ ⌜is_set X v⌝ }}}
      set_mem (inject x) v @ s; E
    {{{ (b : bool), RET #b; ⌜if b then x ∈ X else x ∉ X⌝ }}}.
  Proof.
    iIntros (? Φ (l & ? & -> & ?)) "HΦ".
    iApply (gwp_list_mem with "[//]"); [done|].
    iIntros ([] Hb); iApply "HΦ"; iPureIntro.
    { set_solver. }
    destruct Hb; set_solver.
  Qed.

  Lemma gwp_set_mem_elem_of x X v s E :
    val_is_unboxed (inject x) →
    x ∈ X →
    G{{{ ⌜is_set X v⌝ }}}
      set_mem (inject x) v @ s; E
    {{{ RET #true; True }}}.
  Proof.
    iIntros (?? Φ (l & ? & -> & ?)) "HΦ".
    iApply (gwp_list_mem with "[//]"); [done|].
    iIntros ([] Hb); last first.
    { destruct Hb; set_solver. }
    by iApply "HΦ".
  Qed.

  (* Lemma gwp_set_iter Φ1 Φ2 Ψ P (X : gset A) v handler s E : *)
  (*   (∀ (x : A) (X' : gset A), *)
  (*      G{{{ ⌜x ∈ X⌝ ∗ P ∗ Ψ X' ∗ Φ1 x }}} *)
  (*        (Val handler) $x @ s; E *)
  (*      {{{v, RET v; P ∗ Ψ (X' ∪ {[x]}) ∗ Φ2 x }}}) -∗ *)
  (*   G{{{ ⌜is_set X v⌝ ∗ P ∗ Ψ ∅ ∗ [∗ set] x ∈ X, Φ1 x }}} *)
  (*     set_iter (Val handler) (Val v) @ s; E *)
  (*   {{{ RET #(); P ∗ Ψ X ∗ [∗ set] x ∈ X, Φ2 x }}}. *)
  (* Proof. *)
  (*   iIntros "#Hhandler". *)
  (*   iIntros "!#" (Ξ) "(%HX & HP & HΨ & HΦ1) HΞ". *)
  (*   destruct HX as (l & ? & -> & Hdup). *)
  (*   rewrite !big_sepS_list_to_set //. *)
  (*   rewrite /set_iter. *)
  (*   gwp_apply (gwp_list_iter_invariant Φ1 Φ2 (λ l, Ψ (list_to_set l)) P *)
  (*               with "[] [$HP $HΦ1 $HΨ //]"); [|done]. *)
  (*   iIntros (a l') "!#". iIntros (Ξ') "([%l'' %] & HP & HΨ & HΦ1) HΞ' ". *)
  (*   gwp_apply ("Hhandler" $! a (list_to_set l') *)
  (*               with "[-HΞ']"); last first. *)
  (*   { rewrite list_to_set_app_L /= union_empty_r_L //. } *)
  (*   iFrame. iPureIntro. set_solver. *)
  (* Qed. *)

  (* Lemma gwp_set_foldl P Φ Ψ ip handler (X : gset A) acc v : *)
  (*   (∀ (a : A) acc Xacc, *)
  (*       {{{ P Xacc acc ∗ Φ a }}} *)
  (*         (Val handler) (Val acc) $a @ s; E *)
  (*       {{{v, RET v; P (Xacc ∪ {[a]}) v ∗ Ψ a }}}) -∗ *)
  (*   {{{ ⌜is_set X v⌝ ∗ P ∅ acc ∗ [∗ set] a ∈ X, Φ a }}} *)
  (*     set_foldl handler acc v @ s; E *)
  (*   {{{v, RET v; P X v ∗ [∗ set] a ∈ X, Ψ a }}}. *)
  (* Proof. *)
  (*   iIntros "#Hhandler !#" (Ξ) "(%HX & HP & HΦ) HΞ". *)
  (*   destruct HX as (l & ? & -> & Hdup). *)
  (*   rewrite !big_sepS_list_to_set // /set_fold. *)
  (*   gwp_apply (gwp_list_fold (λ l v, P (list_to_set l) v) Φ Ψ with "[] [$HP $HΦ //]"). *)
  (*   { iIntros (????) "!#". iIntros (Ξ') "(% & HP & HΦ) HΞ'". *)
  (*     gwp_apply ("Hhandler" with "[$HP $HΦ]"). *)
  (*     rewrite list_to_set_app_L /= union_empty_r_L //. } *)
  (*   iIntros (?) "[? ?]". *)
  (*   iApply "HΞ". iFrame. *)
  (*   rewrite big_sepS_list_to_set //. *)
  (* Qed. *)

  (* Lemma gwp_set_subseteq X Y v w s E : *)
  (*   G{{{ ⌜is_set X v⌝ ∗ ⌜is_set Y w⌝}}} *)
  (*     set_subseteq v w @ s; E *)
  (*   {{{ (b : bool), RET #b; ⌜if b then X ⊆ Y else X ⊈ Y⌝ }}}. *)
  (* Proof. *)
  (*   iIntros (Φ) "[%HX %HY] HΦ". *)
  (*   destruct HX as (Xl & ? & -> & ? & ?). *)
  (*   rewrite /set_subseteq. gwp_pures. *)
  (*   gwp_apply (gwp_list_forall (λ x, ⌜x ∈ Y⌝) (λ x, ⌜x ∉ Y⌝) with "[] [//]")%I. *)
  (*   { iIntros (?? Ψ) "!#". iIntros "HΨ". *)
  (*     gwp_pures. gwp_apply (gwp_set_mem with "[//]"). *)
  (*     iIntros ([] ?); by iApply "HΨ". } *)
  (*   iIntros ([]) "Hb". *)
  (*   - iApply "HΦ". *)
  (*     rewrite elem_of_subseteq. *)
  (*     iIntros (x Hx%elem_of_list_to_set). *)
  (*     rewrite big_sepL_elem_of //. *)
  (*   - iApply "HΦ". iDestruct "Hb" as (x) "[% %]". *)
  (*     iPureIntro; set_solver. *)
  (* Qed. *)

  (* Lemma gwp_set_equal ip X Y xv yv: *)
  (*   {{{ ⌜is_set X xv⌝ ∗ ⌜is_set Y yv⌝}}} *)
  (*     set_equal (Val xv) (Val yv) @ s; E *)
  (*   {{{ (b : bool), RET #b; ⌜if b then X = Y else X ≠ Y⌝ }}}. *)
  (* Proof. *)
  (*   iIntros (Φ) "[%HX %HY] HΦ". *)
  (*   rewrite /set_equal. gwp_pures. *)
  (*   gwp_apply (gwp_set_subseteq); [auto|]. *)
  (*   iIntros ([] ?); gwp_if; last first. *)
  (*   { iApply "HΦ". iPureIntro; set_solver. } *)
  (*   gwp_apply (gwp_set_subseteq); [auto|]. *)
  (*   iIntros ([] ?); iApply "HΦ"; iPureIntro; set_solver. *)
  (* Qed. *)

  (* Lemma gwp_set_forall Φ Ψ ip X xv (fv : val) : *)
  (*   (∀ (a : A), *)
  (*       {{{ True }}} *)
  (*         fv $a @ s; E *)
  (*       {{{ (b : bool), RET #b; if b then Φ a else Ψ a }}}) -∗ *)
  (*   {{{ ⌜is_set X xv⌝ }}} *)
  (*     list_forall fv xv @ s; E *)
  (*   {{{ (b : bool), RET #b; if b then [∗ set] x ∈ X, Φ x else ∃ x, ⌜x ∈ X⌝ ∗ Ψ x }}}. *)
  (* Proof. *)
  (*   iIntros "#Hfv !#" (Ξ (?&?&->&?)) "HΞ". *)
  (*   gwp_apply (gwp_list_forall with "[//] [//]"). *)
  (*   iIntros ([]) "Hb"; iApply "HΞ". *)
  (*   { rewrite  big_sepS_list_to_set //. } *)
  (*   iDestruct "Hb" as (?) "[% ?]". *)
  (*   iExists _. rewrite elem_of_list_to_set. eauto. *)
  (* Qed. *)

  (* Lemma gwp_set_cardinal ip X xv  : *)
  (*   {{{ ⌜is_set X xv⌝ }}} *)
  (*     set_cardinal xv @ s; E *)
  (*   {{{ RET #(size X); True }}}. *)
  (* Proof. *)
  (*   iIntros (Φ (?&?&->&?)) "HΦ". *)
  (*   rewrite /set_cardinal. *)
  (*   gwp_apply gwp_list_length; [done|]. *)
  (*   iIntros (n ->). *)
  (*   rewrite list_to_set_size //. *)
  (*   by iApply "HΦ". *)
  (* Qed. *)

End set_specs.

Global Arguments gwp_set_empty {_ _ _ _} _ {_ _ _}.

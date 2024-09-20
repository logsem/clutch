(** This file proves the basic laws of the ProbLang weakest precondition by
    applying the lifting lemmas. *)
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth excl.
From iris.base_logic.lib Require Export ghost_map.
From clutch.base_logic Require Export error_credits.
From clutch.coneris Require Export weakestpre ectx_lifting.
From clutch.con_prob_lang Require Export class_instances.
From clutch.con_prob_lang Require Import tactics lang notation.
From iris.prelude Require Import options.

Class conerisGS Σ := HeapG {
  conerisGS_invG : invGS_gen HasNoLc Σ;
  (* CMRA for the state *)
  conerisGS_heap : ghost_mapG Σ loc val;
  conerisGS_tapes : ghost_mapG Σ loc tape;
  (* ghost names for the state *)
  conerisGS_heap_name : gname;
  conerisGS_tapes_name : gname;
  (* CMRA and ghost name for the error *)
  conerisGS_error :: ecGS Σ;
}.


Definition progUR : ucmra := optionUR (exclR exprO).
Definition partial_cfgO : ofe := prodO exprO stateO.
Definition partial_cfgUR : ucmra := optionUR (exclR partial_cfgO).

Definition heap_auth `{conerisGS Σ} :=
  @ghost_map_auth _ _ _ _ _ conerisGS_heap conerisGS_heap_name.
Definition tapes_auth `{conerisGS Σ} :=
  @ghost_map_auth _ _ _ _ _ conerisGS_tapes conerisGS_tapes_name.


Global Instance conerisGS_conerisWpGS `{!conerisGS Σ} : conerisWpGS con_prob_lang Σ := {
  conerisWpGS_invGS := conerisGS_invG;
    state_interp σ := (heap_auth 1 σ.(heap) ∗ tapes_auth 1 σ.(tapes))%I;
    fork_post := (λ _, True%I);
    err_interp ε := (ec_supply ε);
    
}.

(** Heap *)
Notation "l ↦{ dq } v" := (@ghost_map_elem _ _ _ _ _ conerisGS_heap conerisGS_heap_name l dq v)
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Notation "l ↦□ v" := (l ↦{ DfracDiscarded } v)%I
  (at level 20, format "l  ↦□  v") : bi_scope.
Notation "l ↦{# q } v" := (l ↦{ DfracOwn q } v)%I
  (at level 20, format "l  ↦{# q }  v") : bi_scope.
Notation "l ↦ v" := (l ↦{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↦  v") : bi_scope.

(** Tapes *)
Notation "l ↪{ dq } v" := (@ghost_map_elem _ _ _ _ _ conerisGS_tapes conerisGS_tapes_name l dq (v : tape))
  (at level 20, format "l  ↪{ dq }  v") : bi_scope.
Notation "l ↪□ v" := (l ↪{ DfracDiscarded } v)%I
  (at level 20, format "l  ↪□  v") : bi_scope.
Notation "l ↪{# q } v" := (l ↪{ DfracOwn q } v)%I
  (at level 20, format "l  ↪{# q }  v") : bi_scope.
Notation "l ↪ v" := (l ↪{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↪  v") : bi_scope.

(** User-level tapes *)
Definition nat_tape `{conerisGS Σ} l (N : nat) (ns : list nat) : iProp Σ :=
  ∃ (fs : list (fin (S N))), ⌜fin_to_nat <$> fs = ns⌝ ∗ l ↪ (N; fs).

Notation "l ↪N ( M ; ns )" := (nat_tape l M ns)%I
  (at level 20, format "l  ↪N  ( M ;  ns )") : bi_scope.

Section tape_interface.
  Context `{!conerisGS Σ}.

  (** Helper lemmas to go back and forth between the user-level representation
      of tapes (using nat) and the backend (using fin) *)

  Lemma tapeN_to_empty l M :
    (l ↪N ( M ; [] ) -∗ l ↪ ( M ; [] )).
  Proof.
    iIntros "Hl".
    iDestruct "Hl" as (?) "(%Hmap & Hl')".
    by destruct (fmap_nil_inv _ _ Hmap).
  Qed.


  Lemma empty_to_tapeN l M :
    (l ↪ ( M ; [] ) -∗ l ↪N ( M ; [] )).
  Proof.
    iIntros "Hl".
    iExists []. auto.
  Qed.

  Lemma tapeN_tapeN_contradict l N M ns ms:
    l ↪N ( N;ns ) -∗ l↪N (M;ms) -∗ False.
  Proof.
    iIntros "(%&<-&H1) (%&<-&H2)".
    by iDestruct (ghost_map_elem_ne with "[$][$]") as "%".
  Qed.

  Lemma read_tape_head l M n ns :
    (l ↪N ( M ; n :: ns ) -∗
      ∃ x xs, l ↪ ( M ; x :: xs ) ∗ ⌜ fin_to_nat x = n ⌝ ∗
        ( l ↪ ( M ; xs ) -∗l ↪N ( M ; ns ) )).
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

  Lemma tapeN_lookup α N ns m: 
    tapes_auth 1 m -∗ α ↪N (N; ns) -∗ ⌜∃ ns', m!!α = Some (N; ns') /\ fin_to_nat <$> ns' = ns⌝.
  Proof.
    iIntros "? (%&%&?)".
    iDestruct (ghost_map_lookup with "[$][$]") as "%".
    iPureIntro. naive_solver.
  Qed.

  Lemma tapeN_update_append α N ns m (x : fin (S N)):
    tapes_auth 1 m -∗ α ↪N (N; fin_to_nat <$> ns) ==∗ tapes_auth 1 (<[α:=(N; ns ++ [x])]> m) ∗ α ↪N (N; (fin_to_nat <$> ns) ++ [fin_to_nat x]).
  Proof.
    iIntros "? (%&%&?)".
    iMod (ghost_map_update with "[$][$]") as "[??]".
    iFrame.
    by rewrite fmap_app.
  Qed. 

  Lemma tapeN_update_append' α N m (ns ns':list (fin (S N))):
    tapes_auth 1 m -∗ α ↪N (N; fin_to_nat <$> ns) ==∗ tapes_auth 1 (<[α:=(N; ns ++ ns')]> m) ∗ α ↪N (N; (fin_to_nat <$> ns) ++ (fin_to_nat <$> ns')).
  Proof.
    iIntros "? (%&%&?)".
    iMod (ghost_map_update with "[$][$]") as "[??]".
    iFrame.
    by rewrite fmap_app.
  Qed. 
  
  (*
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
*)

End tape_interface.



Section lifting.
Context `{!conerisGS Σ}.
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

Lemma wp_alloc E v s :
  {{{ True }}} Alloc (Val v) @ s; E {{{ l, RET LitV (LitLoc l); l ↦ v }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "[Hh Ht] !#".
  solve_red.
  iIntros "!> /=" (e2 σ2 efs Hs); inv_head_step.
  iMod ((ghost_map_insert (fresh_loc σ1.(heap)) v) with "Hh") as "[? Hl]".
  { apply not_elem_of_dom, fresh_loc_is_fresh. }
  iFrame.
  rewrite map_union_empty -insert_union_singleton_l.
  iFrame.
  iIntros "!>". iSplit; [by iApply "HΦ"|done].
Qed.

Lemma wp_allocN_seq (N : nat) (z : Z) E v s:
  TCEq N (Z.to_nat z) →
  (0 < N)%Z →
  {{{ True }}}
    AllocN (Val $ LitV $ LitInt $ z) (Val v) @ s; E
                                                    {{{ l, RET LitV (LitLoc l); [∗ list] i ∈ seq 0 N, (l +ₗ (i : nat)) ↦ v }}}.
Proof.
  iIntros (-> Hn Φ) "_ HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "[Hh Ht] !#".
  iSplit.
  { iPureIntro.
    rewrite /head_reducible.
    eexists.
    apply head_step_support_equiv_rel.
    econstructor; eauto.
    lia.
  }
  iIntros "!> /=" (e2 σ2 efs Hs); inv_head_step.
  iMod ((ghost_map_insert_big _ _ with "Hh")) as "[$ Hl]".
  iIntros "!>". iFrame. iSplitL; last done.
  iApply "HΦ".
  iInduction (H) as [ | ?] "IH" forall (σ1).
  - simpl.
    iSplit; auto.
    rewrite map_union_empty.
    rewrite loc_add_0.
    by rewrite big_sepM_singleton.
  - rewrite seq_S.
    rewrite heap_array_replicate_S_end.
    iPoseProof (big_sepM_union _ _ _ _ with "Hl") as "[H1 H2]".
    iApply big_sepL_app.
    iSplitL "H1".
    + iApply "IH".
      { iPureIntro. lia. }
      iApply "H1".
    + simpl. iSplit; auto.
      by rewrite big_sepM_singleton.
      Unshelve.
      {
        apply heap_array_map_disjoint.
        intros.
        apply not_elem_of_dom_1.
        by apply fresh_loc_offset_is_fresh.
      }
      apply heap_array_map_disjoint.
      intros.
      apply not_elem_of_dom_1.
      rewrite dom_singleton.
      apply not_elem_of_singleton_2.
      intros H2.
      apply loc_add_inj in H2.
      rewrite replicate_length in H1.
      lia.
Qed.

Lemma wp_load E l dq v s :
  {{{ ▷ l ↦{dq} v }}} Load (Val $ LitV $ LitLoc l) @ s; E {{{ RET v; l ↦{dq} v }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "[Hh Ht] !#".
  iDestruct (ghost_map_lookup with "Hh Hl") as %?.
  solve_red.
  iIntros "!> /=" (e2 σ2 efs Hs); inv_head_step.
  iFrame. iModIntro. iSplitL; last done. by iApply "HΦ".
Qed.

Lemma wp_store E l v' v s :
  {{{ ▷ l ↦ v' }}} Store (Val $ LitV (LitLoc l)) (Val v) @ s; E
  {{{ RET LitV LitUnit; l ↦ v }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "[Hh Ht] !#".
  iDestruct (ghost_map_lookup with "Hh Hl") as %?.
  solve_red.
  iIntros "!> /=" (e2 σ2 efs Hs); inv_head_step.
  iMod (ghost_map_update with "Hh Hl") as "[$ Hl]".
  iFrame. iModIntro. iSplitL; last done. by iApply "HΦ".
Qed.

Lemma wp_rand (N : nat) (z : Z) E s :
  TCEq N (Z.to_nat z) →
  {{{ True }}} rand #z @ s; E {{{ (n : fin (S N)), RET #n; True }}}.
Proof.
  iIntros (-> Φ) "_ HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "Hσ !#".
  solve_red.
  iIntros "!>" (e2 σ2 efs Hs).
  inv_head_step.
  iFrame.
  iSplitL; last done. by iApply ("HΦ" $! x) .
Qed.


(** Tapes  *)
Lemma wp_alloc_tape N z E s :
  TCEq N (Z.to_nat z) →
  {{{ True }}} alloc #z @ s; E {{{ α, RET #lbl:α; α ↪N (N; []) }}}.
Proof.
  iIntros (-> Φ) "_ HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "(Hh & Ht) !# /=".
  solve_red.
  iIntros "!>" (e2 σ2 efs Hs); inv_head_step.
  iMod (ghost_map_insert (fresh_loc σ1.(tapes)) with "Ht") as "[$ Hl]".
  { apply not_elem_of_dom, fresh_loc_is_fresh. }
  iFrame. iModIntro.
  iSplitL; last done.
  iApply "HΦ".
  iExists []; auto.
Qed.

Lemma wp_rand_tape N α n ns z E s :
  TCEq N (Z.to_nat z) →
  {{{ ▷ α ↪N (N; n :: ns) }}}
    rand(#lbl:α) #z @ s; E
  {{{ RET #(LitInt n); α ↪N (N; ns) ∗ ⌜n <= N⌝ }}}.
Proof.
  iIntros (-> Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "(Hh & Ht) !#".
  iDestruct (read_tape_head with "Hl") as (x xs) "(Hl&<-&Hret)".
  iDestruct (ghost_map_lookup with "Ht Hl") as %?.
  solve_red.
  iIntros "!>" (e2 σ2 efs Hs).
  inv_head_step.
  iMod (ghost_map_update with "Ht Hl") as "[$ Hl]".
  iFrame. iModIntro.
  iSplitL; last done.
  iApply "HΦ".
  iSplit; first by iApply "Hret".
  iPureIntro.
  pose proof (fin_to_nat_lt x); lia.
Qed.

Lemma wp_rand_tape_empty N z α E s :
  TCEq N (Z.to_nat z) →
  {{{ ▷ α ↪N (N; []) }}}
    rand(#lbl:α) #z @ s; E
  {{{ (n : nat), RET #(LitInt n); α ↪N (N; []) ∗ ⌜n <= N⌝ }}}.
Proof.
  iIntros (-> Φ) ">Hl HΦ".
  iPoseProof (tapeN_to_empty with "Hl") as "Hl".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "(Hh & Ht) !#".
  iDestruct (ghost_map_lookup with "Ht Hl") as %?.
  solve_red.
  iIntros "!>" (e2 σ2 efs Hs).
  inv_head_step.
  iFrame.
  iModIntro. iSplitL; last done.
  iApply ("HΦ" with "[$Hl]").
  iSplit; auto.
  iPureIntro.
  pose proof (fin_to_nat_lt x); lia.
Qed.

Lemma wp_rand_tape_wrong_bound N M z α E ns s :
  TCEq N (Z.to_nat z) →
  N ≠ M →
  {{{ ▷ α ↪N (M; ns) }}}
    rand(#lbl:α) #z @ s; E
  {{{ (n : nat), RET #(LitInt n); α ↪N (M; ns) ∗ ⌜n <= N⌝ }}}.
Proof.
  iIntros (-> ? Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "(Hh & Ht) !#".
  iDestruct "Hl" as (?) "(?&Hl)".
  iDestruct (ghost_map_lookup with "Ht Hl") as %?.
  solve_red.
  iIntros "!>" (e2 σ2 efs Hs).
  inv_head_step.
  iFrame.
  iModIntro.
  iSplitL; last done.
  iApply ("HΦ").
  iFrame.
  iPureIntro.
  pose proof (fin_to_nat_lt x); lia.
Qed.

Lemma wp_fork s E e Φ :
  ▷ WP e @ s; ⊤ {{ _, True }} -∗ ▷ Φ (LitV LitUnit) -∗ WP Fork e @ s; E {{ Φ }}.
Proof.
  iIntros "He HΦ". iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "(Hh & Ht) !#". solve_red.
  iIntros "!>" (e2 σ2 efs Hs).
  inv_head_step. by iFrame. 
Qed.

(* Concurrency *)
Lemma wp_cmpxchg_fail s E (v v1 v2: val) l dq :
  vals_compare_safe v v1 ->
  v ≠ v1 ->
  {{{ ▷ l ↦{dq} v }}}
    CmpXchg #l v1 v2 @ s; E
   {{{ RET (v, #false)%V; l ↦{dq} v }}}.
Proof.
  iIntros (?? Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "[Hh Ht] !#".
  iDestruct (ghost_map_lookup with "Hh Hl") as %?.
  solve_red.
  iIntros "!> /=" (e2 σ2 efs Hs); inv_head_step.
  iFrame. iSplitL; last done.
  by iApply "HΦ".
Qed.


Lemma wp_cmpxchg_suc s E (v v1 v2: val) l :
  vals_compare_safe v v1 ->
  v = v1 ->
  {{{ ▷ l ↦ v }}}
    CmpXchg #l v1 v2 @ s; E
   {{{ RET (v, #true)%V; l ↦ v2 }}}.
Proof.
  iIntros (? ? Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "[Hh Ht] !#".
  iDestruct (ghost_map_lookup with "Hh Hl") as %?.
  solve_red.
  iIntros "!> /=" (e2 σ2 efs Hs); inv_head_step.
  iMod (ghost_map_update with "Hh Hl") as "[$ Hl]".
  iFrame. iModIntro. iSplitL; last done. by iApply "HΦ".
Qed.

Lemma wp_xchg s E (v1 v2: val) l :
  {{{ ▷ l ↦ v1 }}}
    Xchg #l v2 @ s; E
   {{{ RET v1; l ↦ v2 }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "[Hh Ht] !#".
  iDestruct (ghost_map_lookup with "Hh Hl") as %?.
  solve_red.
  iIntros "!> /=" (e2 σ2 efs Hs); inv_head_step.
  iMod (ghost_map_update with "Hh Hl") as "[$ Hl]".
  iFrame. iModIntro. iSplitL; last done. by iApply "HΦ".
Qed.


Lemma wp_faa s E (i1 i2: Z) l :
  {{{ ▷ l ↦ #i1 }}}
    FAA #l #i2 @ s; E
   {{{ RET #i1; l ↦ #(i1+i2)%Z }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "[Hh Ht] !#".
  iDestruct (ghost_map_lookup with "Hh Hl") as %?.
  solve_red.
  iIntros "!> /=" (e2 σ2 efs Hs); inv_head_step.
  iMod (ghost_map_update with "Hh Hl") as "[$ Hl]".
  iFrame. iModIntro. iSplitL; last done. by iApply "HΦ".
Qed.


  
End lifting.

Global Hint Extern 0 (TCEq _ (Z.to_nat _ )) => rewrite Nat2Z.id : typeclass_instances.

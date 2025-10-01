(** This file proves the basic laws of the ProbLang weakest precondition by
    applying the lifting lemmas. *)
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth excl.
From iris.base_logic.lib Require Export ghost_map.
From iris.algebra Require Import gmap_view.
From clutch.base_logic Require Export error_credits.
From clutch.eris Require Export weakestpre ectx_lifting.
From clutch.prob_lang2 Require Export class_instances.
From clutch.prob_lang2 Require Import tactics lang notation.
From iris.prelude Require Import options.

(*
Class tapeG Σ (N K V : Type) `{Countable N} := GhostMapG {
  #[local] tape_inG :: inG Σ (gmap_viewR N (agreeR (K -d> leibnizO V)));
}.

Definition tapeΣ (N K V : Type) `{Countable N} : gFunctors :=
  #[ GFunctor (gmap_viewR N (agreeR (K -d> leibnizO V))) ].

Global Instance subG_tapeΣ Σ (N K V : Type) `{Countable N} :
  subG (tapeΣ N K V) Σ → tapeG Σ N K V.
Proof. solve_inG. Qed.
*)

Class tapeG Σ := GhostMapG {
  #[local] tape_inG :: inG Σ (gmap_viewR loc (agreeR (leibnizO tape)));
}.

Definition tapeΣ : gFunctors :=
  #[ GFunctor (gmap_viewR loc (agreeR (leibnizO tape))) ].

Global Instance subG_tapeΣ Σ :
  subG tapeΣ Σ → tapeG Σ.
Proof. solve_inG. Qed.


Class erisGS Σ := HeapG {
  erisGS_invG : invGS_gen HasNoLc Σ;
  (* CMRA for the state *)
  erisGS_heap : ghost_mapG Σ loc val;
  (* CMRA for the tapes. *)
  erisGS_tapes : tapeG Σ;
  (* ghost names for the state *)
  erisGS_heap_name : gname;
  erisGS_tapes_name : gname;
  (* CMRA and ghost name for the error *)
  erisGS_error :: ecGS Σ;
}.

Definition progUR : ucmra := optionUR (exclR exprO).
Definition cfgO : ofe := prodO exprO stateO.
Definition cfgUR : ucmra := optionUR (exclR cfgO).

Definition heap_auth `{erisGS Σ} :=
  @ghost_map_auth _ _ _ _ _ erisGS_heap erisGS_heap_name.

Definition tapes_auth `{erisGS Σ} (q : dfrac) m :=
  @own Σ _ (erisGS_tapes.(tape_inG)) erisGS_tapes_name
    (gmap_view_auth (V:=agreeR $ leibnizO tape) q m).

Definition tapes_frag `{erisGS Σ} (q : dfrac) (k : loc) (v : agreeR $ leibnizO tape) :=
  @own Σ _ (erisGS_tapes.(tape_inG)) erisGS_tapes_name (gmap_view_frag k q v).

Global Instance erisGS_erisWpGS `{!erisGS Σ} : erisWpGS prob_lang Σ := {
  erisWpGS_invGS := erisGS_invG;
  state_interp σ := (heap_auth 1 σ.(heap) ∗ tapes_auth (DfracOwn 1) (to_agree <$> σ.(tapes)))%I;
  err_interp ε := (ec_supply ε);
}.

(** Heap *)
Notation "l ↦{ dq } v" := (@ghost_map_elem _ _ _ _ _ erisGS_heap erisGS_heap_name l dq v)
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Notation "l ↦□ v" := (l ↦{ DfracDiscarded } v)%I
  (at level 20, format "l  ↦□  v") : bi_scope.
Notation "l ↦{# q } v" := (l ↦{ DfracOwn q } v)%I
  (at level 20, format "l  ↦{# q }  v") : bi_scope.
Notation "l ↦ v" := (l ↦{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↦  v") : bi_scope.

(** Tapes *)
Notation "l ↪{ dq } v" := (tapes_frag dq l (to_agree v))
  (at level 20, format "l  ↪{ dq }  v") : bi_scope.
Notation "l ↪□ v" := (l ↪{ DfracDiscarded } v)%I
  (at level 20, format "l  ↪□  v") : bi_scope.
Notation "l ↪{# q } v" := (l ↪{ DfracOwn q } v)%I
  (at level 20, format "l  ↪{# q }  v") : bi_scope.
Notation "l ↪ v" := (l ↪{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↪  v") : bi_scope.


Section namespace_lemmas.
  Context `{erisGS Σ}.
  Implicit Types (k : loc) (v : tape) (dq : dfrac).
  Implicit Types (m : gmap loc tape).

  Lemma tapes_insert {m} k v:
     m !! k = None →
     ⊢ tapes_auth (DfracOwn 1) (to_agree <$> m) ==∗
     tapes_auth (DfracOwn 1) (to_agree <$> <[k := v]> m) ∗ k ↪{DfracOwn 1} v.
  Proof.
    intros Hm.
    rewrite -own_op.
    iApply own_update.
    rewrite fmap_insert.
    apply: gmap_view_alloc; [ |done|done].
    rewrite lookup_fmap Hm //.
  Qed.

  Lemma tapes_lookup {m k v} :
    tapes_auth (DfracOwn 1) (to_agree <$> m) -∗ (k ↪{DfracOwn 1} v) -∗ ⌜m !! k = Some v⌝.
  Proof.
    iIntros "Hauth Hel".
    iCombine "Hauth Hel" gives
      %(av' & _ & _ & Hav' & _ & Hincl)%gmap_view_both_dfrac_valid_discrete_total.
    iPureIntro.
    apply lookup_fmap_Some in Hav' as [v' [<- Hv']].
    apply to_agree_included_L in Hincl.
    by rewrite Hincl.
  Qed.

  Lemma tapes_update {m k v} w :
    tapes_auth (DfracOwn 1) (to_agree <$> m) -∗ k ↪{DfracOwn 1} v ==∗
    tapes_auth (DfracOwn 1) (to_agree <$> <[k := w]> m) ∗ k ↪{DfracOwn 1} w.
  Proof.
    iApply bi.wand_intro_r. rewrite -!own_op.
    iApply own_update. rewrite fmap_insert. apply: gmap_view_replace; done.
  Qed.

End namespace_lemmas.

Section pre_namespace_lemmas.
  Context `{inG Σ (gmap_viewR loc (agreeR (leibnizO tape)))}.
  Implicit Types (k : loc) (v : tape) (dq : dfrac).
  Implicit Types (m : gmap loc tape).

  Lemma tapes_alloc m :
    ⊢ |==> ∃ γ, own γ (gmap_view_auth (V:=agreeR $ leibnizO tape) (DfracOwn 1) (to_agree <$> m)) ∗
           [∗ map] k ↦ v ∈ m,
              (@own Σ _ _ γ (gmap_view_frag (V:=agreeR $ leibnizO tape) k (DfracOwn 1) (to_agree v))).
  Proof.
    iMod (own_alloc_strong (gmap_view_auth (V:=agreeR $ leibnizO tape) (DfracOwn 1) ∅) (fun _ => True))
      as (γ) "[% Hauth]".
    { exact pred_infinite_True. }
    { by apply gmap_view_auth_valid. }
    iExists γ.
    iMod (own_update with "[Hauth]") as "Hauth'".
    2: iApply "Hauth".
    { eapply (gmap_view_alloc_big _ (to_agree <$> m) (DfracOwn 1)).
      { apply map_disjoint_empty_r. }
      { done. }
      { by apply map_Forall_fmap. }
    }
    iModIntro.
    rewrite own_op; iDestruct "Hauth'" as "[Ha1 Ha2]".
    rewrite right_id -big_opM_own_1 big_opM_fmap.
    iFrame.
  Qed.

End pre_namespace_lemmas.


Section lifting.
Context `{!erisGS Σ}.
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
  iSplitR; [iPureIntro |].
  { eexists _; eapply head_step_support_equiv_rel; constructor; eauto. }
  iIntros "!> /=" (e2 σ2 Hs); inv_head_step.
  iMod ((ghost_map_insert (fresh_loc σ1.(heap)) v) with "Hh") as "[? Hl]".
  { apply not_elem_of_dom, fresh_loc_is_fresh. }
  iFrame.
  rewrite map_union_empty -insert_union_singleton_l.
  iFrame.
  iIntros "!>". by iApply "HΦ".
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
  iIntros "!> /=" (e2 σ2 Hs); inv_head_step.
  iMod ((ghost_map_insert_big _ _ with "Hh")) as "[$ Hl]".
  iIntros "!>". iFrame.
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

(* TODO: All the admits left are from solve_red; debug me *)

Lemma wp_load E l dq v s :
  {{{ ▷ l ↦{dq} v }}} Load (Val $ LitV $ LitLoc l) @ s; E {{{ RET v; l ↦{dq} v }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "[Hh Ht] !#".
  iDestruct (ghost_map_lookup with "Hh Hl") as %?.
  iSplitR; [iPureIntro |].
  { eexists _; eapply head_step_support_equiv_rel; constructor; eauto. }
  iIntros "!> /=" (e2 σ2 Hs); inv_head_step.
  iFrame. iModIntro. by iApply "HΦ".
Qed.

Lemma wp_store E l v' v s :
  {{{ ▷ l ↦ v' }}} Store (Val $ LitV (LitLoc l)) (Val v) @ s; E
  {{{ RET LitV LitUnit; l ↦ v }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "[Hh Ht] !#".
  iDestruct (ghost_map_lookup with "Hh Hl") as %?.
  iSplitR; [iPureIntro |].
  { eexists _; eapply head_step_support_equiv_rel. eapply StoreS; exact H. }
  iIntros "!> /=" (e2 σ2 Hs); inv_head_step.
  iMod (ghost_map_update with "Hh Hl") as "[$ Hl]".
  iFrame. iModIntro. by iApply "HΦ".
Qed.

Lemma wp_rand (N : nat) (z : Z) E s :
  TCEq N (Z.to_nat z) →
  {{{ True }}} rand #z @ s; E {{{ (n : fin (S N)), RET #n; True }}}.
Proof.
  iIntros (-> Φ) "_ HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "Hσ !#".
  iSplitR; [iPureIntro |].
  { eexists _; eapply head_step_support_equiv_rel; constructor; eauto. }
  iIntros "!>" (e2 σ2 Hs).
  inv_head_step.
  iFrame.
  by iApply ("HΦ" $! x).
  Unshelve. exact Fin.F1.
Qed.

(** Tapes  *)
Lemma wp_alloc_tape N z E s :
  TCEq N (Z.to_nat z) →
  {{{ True }}} alloc #z @ s; E {{{ α, RET #lbl:α; α ↪ (N; []) }}}.
Proof.
  iIntros (-> Φ) "_ HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "(Hh & Ht) !# /=".
  iSplitR; [iPureIntro |].
  { eexists _; eapply head_step_support_equiv_rel; constructor; eauto. }
  iIntros "!>" (e2 σ2 Hs); inv_head_step.
  iMod (tapes_insert (fresh_loc (σ1.(tapes))) with "Ht") as "[$ Hl]".
  { apply not_elem_of_dom, fresh_loc_is_fresh. }
  iFrame. iModIntro.
  by iApply "HΦ".
Qed.

Lemma wp_rand_tape N α n ns z E s :
  TCEq N (Z.to_nat z) →
  {{{ ▷ α ↪ (N; n :: ns) }}} rand(#lbl:α) #z @ s; E {{{ RET #(LitInt n); α ↪ (N; ns) }}}.
Proof.
  iIntros (-> Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "(Hh & Ht) !#".
  iDestruct (tapes_lookup with "Ht Hl") as %?.
  iSplitR; [iPureIntro |].
  { eexists _; eapply head_step_support_equiv_rel; constructor; eauto. }
  iIntros "!>" (e2 σ2 Hs).
  inv_head_step.
  iMod (tapes_update with "Ht Hl") as "[$ Hl]".
  iFrame. iModIntro.
  by iApply "HΦ".
Qed.

Lemma wp_rand_tape_empty N z α E s :
  TCEq N (Z.to_nat z) →
  {{{ ▷ α ↪ (N; []) }}} rand(#lbl:α) #z @ s; E {{{ (n : fin (S N)), RET #(LitInt n); α ↪ (N; []) }}}.
Proof.
  iIntros (-> Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "(Hh & Ht) !#".
  iDestruct (tapes_lookup with "Ht Hl") as %?.
  iSplitR; [iPureIntro |].
  { eexists _; eapply head_step_support_equiv_rel; constructor; last exact H. done. }
  iIntros "!>" (e2 σ2 Hs).
  inv_head_step.
  iFrame.
  iModIntro. iApply ("HΦ" with "[$Hl //]").
  Unshelve. exact Fin.F1.
Qed.

Lemma wp_rand_tape_wrong_bound N M z α E ns s :
  TCEq N (Z.to_nat z) →
  N ≠ M →
  {{{ ▷ α ↪ (M; ns) }}} rand(#lbl:α) #z @ s; E {{{ (n : fin (S N)), RET #(LitInt n); α ↪ (M; ns) }}}.
Proof.
  iIntros (-> ? Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "(Hh & Ht) !#".
  iDestruct (tapes_lookup with "Ht Hl") as %?.
  iSplitR; [iPureIntro |].
  { eexists _; eapply head_step_support_equiv_rel.
    eapply RandTapeOtherS.
    - reflexivity.
    - exact H0.
    - exact H.
  }
  iIntros "!>" (e2 σ2 Hs).
  inv_head_step.
  iFrame.
  iModIntro.
  iApply ("HΦ" with "[$Hl //]").
  Unshelve. exact Fin.F1.
Qed.

End lifting.

Global Hint Extern 0 (TCEq _ (Z.to_nat _ )) => rewrite Nat2Z.id : typeclass_instances.

(** This file proves the basic laws of the ProbLang weakest precondition by
    applying the lifting lemmas. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export ghost_map.
From clutch.base_logic Require Export error_credits.
From clutch.paris Require Export app_weakestpre ectx_lifting.
From clutch.prob_lang Require Export class_instances.
From clutch.prob_lang Require Import tactics lang notation metatheory.
From clutch.prob_lang.spec Require Export spec_ra spec_rules.
From iris.prelude Require Import options.

Class parisGS Σ := HeapG {
  parisGS_invG : invGS_gen HasNoLc Σ;
  (* CMRA for the state *)
  parisGS_heap : ghost_mapG Σ loc val;
  parisGS_tapes : ghost_mapG Σ loc tape;
  (* ghost names for the state *)
  parisGS_heap_name : gname;
  parisGS_tapes_name : gname;
  (* CMRA and ghost name for the spec *)
  parisGS_spec :: specG_prob_lang Σ;
  (* CMRA and ghost name for the error *)
  parisGS_error :: ecGS Σ;
}.

Class parisGpreS Σ := ParisGpreS {
  parisGpreS_iris  :: invGpreS Σ;
  parisGpreS_heap  :: ghost_mapG Σ loc val;
  parisGpreS_tapes :: ghost_mapG Σ loc tape;
  parisGpreS_spcec :: specGpreS Σ;
  parisGpreS_err   :: ecGpreS Σ;
}.

Definition parisΣ : gFunctors :=
  #[invΣ;
    ghost_mapΣ loc val;
    ghost_mapΣ loc tape;
    specΣ;
    ecΣ].
Global Instance subG_parisGPreS {Σ} : subG parisΣ Σ → parisGpreS Σ.
Proof. solve_inG. Qed.

Definition heap_auth `{parisGS Σ} :=
  @ghost_map_auth _ _ _ _ _ parisGS_heap parisGS_heap_name.
Definition tapes_auth `{parisGS Σ} :=
  @ghost_map_auth _ _ _ _ _ parisGS_tapes parisGS_tapes_name.

Global Instance parisGS_irisGS `{!parisGS Σ} : parisWpGS prob_lang Σ := {
  parisWpGS_invGS := parisGS_invG;
  state_interp σ := (heap_auth 1 σ.(heap) ∗ tapes_auth 1 σ.(tapes))%I;
  err_interp := ec_supply;
}.

(** Heap *)
Notation "l ↦{ dq } v" := (@ghost_map_elem _ _ _ _ _ parisGS_heap parisGS_heap_name l dq v)
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Notation "l ↦□ v" := (l ↦{ DfracDiscarded } v)%I
  (at level 20, format "l  ↦□  v") : bi_scope.
Notation "l ↦{# q } v" := (l ↦{ DfracOwn q } v)%I
  (at level 20, format "l  ↦{# q }  v") : bi_scope.
Notation "l ↦ v" := (l ↦{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↦  v") : bi_scope.

(** Tapes *)
Notation "l ↪{ dq } v" := (@ghost_map_elem _ _ tape _ _ parisGS_tapes parisGS_tapes_name l dq v)
  (at level 20, format "l  ↪{ dq }  v") : bi_scope.
Notation "l ↪□ v" := (l ↪{ DfracDiscarded } v)%I
  (at level 20, format "l  ↪□  v") : bi_scope.
Notation "l ↪{# q } v" := (l ↪{ DfracOwn q } v)%I
  (at level 20, format "l  ↪{# q }  v") : bi_scope.
Notation "l ↪ v" := (l ↪{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↪  v") : bi_scope.

Section lifting.
Context `{!parisGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : val → iProp Σ.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types l : loc.

(** Recursive functions: we do not use this lemma as it is easier to use Löb
    induction directly, but this demonstrates that we can state the expected
    reasoning principle for recursive functions, without any visible ▷. *)

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
  iIntros "!> /=" (e2 σ2 Hs); inv_head_step.
  iMod ((ghost_map_insert (fresh_loc σ1.(heap)) v) with "Hh") as "[? Hl]".
  { apply not_elem_of_dom, fresh_loc_is_fresh. }
  iFrame.
  rewrite map_union_empty -insert_union_singleton_l.
  iFrame.
  iIntros "!>". by iApply "HΦ".
Qed.

Lemma wp_allocN_seq (N : nat) (z : Z) E v s :
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

Lemma wp_load E l dq v s :
  {{{ ▷ l ↦{dq} v }}} Load (Val $ LitV $ LitLoc l) @ s; E {{{ RET v; l ↦{dq} v }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "[Hh Ht] !#".
  iDestruct (ghost_map_lookup with "Hh Hl") as %?.
  solve_red.
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
  solve_red.
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
  solve_red.
  iIntros "!>" (e2 σ2 Hs).
  inv_head_step.
  iFrame.
  by iApply ("HΦ" $! x) .
Qed.

Lemma wp_rand (N : nat) (z : Z) E s :
  TCEq N (Z.to_nat z) →
  {{{ True }}} rand #z @ s; E {{{ (n : fin (S N)), RET #n; True }}}.
Proof.
  iIntros (-> Φ) "_ HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "Hσ !#".
  solve_red.
  iIntros "!>" (e2 σ2 Hs).
  inv_head_step.
  iFrame.
  by iApply ("HΦ" $! x) .
Qed.

(** Tapes  *)
Lemma wp_alloc_tape N z E s :
  TCEq N (Z.to_nat z) →
  {{{ True }}} alloc #z @ s; E {{{ α, RET #lbl:α; α ↪ (N; []) }}}.
Proof.
  iIntros (-> Φ) "_ HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "(Hh & Ht) !# /=".
  solve_red.
  iIntros "!>" (e2 σ2 Hs); inv_head_step.
  iMod (ghost_map_insert (fresh_loc σ1.(tapes)) with "Ht") as "[$ Hl]".
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
  iDestruct (ghost_map_lookup with "Ht Hl") as %?.
  solve_red.
  iIntros "!>" (e2 σ2 Hs).
  inv_head_step.
  iMod (ghost_map_update with "Ht Hl") as "[$ Hl]".
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
  iDestruct (ghost_map_lookup with "Ht Hl") as %?.
  solve_red.
  iIntros "!>" (e2 σ2 Hs).
  inv_head_step.
  iFrame.
  iModIntro. iApply ("HΦ" with "[$Hl //]").
Qed.

Lemma wp_rand_tape_wrong_bound N M z α E ns s :
  TCEq N (Z.to_nat z) →
  N ≠ M →
  {{{ ▷ α ↪ (M; ns) }}} rand(#lbl:α) #z @ s; E {{{ (n : fin (S N)), RET #(LitInt n); α ↪ (M; ns) }}}.
Proof.
  iIntros (-> ? Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "(Hh & Ht) !#".
  iDestruct (ghost_map_lookup with "Ht Hl") as %?.
  solve_red.
  iIntros "!>" (e2 σ2 Hs).
  inv_head_step.
  iFrame.
  iModIntro.
  iApply ("HΦ" with "[$Hl //]").
Qed.

(** spec [rand] *)
Lemma wp_rand_r N z E e K Φ :
  TCEq N (Z.to_nat z) →
  ⤇ fill K (rand #z) ∗
  (∀ n : fin (S N), ⤇ fill K #n -∗ WP e @ E {{ Φ }})
  ⊢ WP e @ E {{ Φ }}.
Proof.
  iIntros (->) "(Hj & Hwp)".
  iApply wp_lift_step_spec_couple.
  iIntros (σ1 e1' σ1' ε1) "(Hσ & Hs & Hε)".
  iDestruct (spec_auth_prog_agree with "Hs Hj") as %->.
  iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".
  iApply spec_coupl_step; [solve_red|].
  rewrite fill_dmap //=.
  iIntros (e2' σ2' ([? ? ]&?&Hs)%dmap_pos).
  simplify_eq/=.
  rewrite head_prim_step_eq // in Hs.
  inv_head_step.
  iApply spec_coupl_ret.
  iMod (spec_update_prog (fill K #_) with "Hs Hj") as "[$ Hj]".
  iFrame. iModIntro.
  iMod "Hclose" as "_"; iModIntro.
  by iApply "Hwp".
Qed.

(** spec [rand(α)] with empty tape  *)
Lemma wp_rand_empty_r N z E e K α Φ :
  TCEq N (Z.to_nat z) →
  ⤇ fill K (rand(#lbl:α) #z) ∗ α ↪ₛ (N; []) ∗
  (∀ n : fin (S N), (α ↪ₛ (N; []) ∗ ⤇ fill K #n) -∗ WP e @ E {{ Φ }})
  ⊢ WP e @ E {{ Φ }}.
Proof.
  iIntros (->) "(Hj & Hα & Hwp)".
  iApply wp_lift_step_spec_couple.
  iIntros (σ1 e1' σ1' ε1) "(Hσ & Hs & Hε)".
  iDestruct (spec_auth_prog_agree with "Hs Hj") as %->.
  iDestruct (spec_auth_lookup_tape with "Hs Hα") as %?.
  iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".
  iApply spec_coupl_step; [solve_red|].
  rewrite fill_dmap //=.
  iIntros (e2' σ2' ([? ? ]&?&Hs)%dmap_pos).
  simplify_eq/=.
  rewrite head_prim_step_eq // in Hs.
  inv_head_step.
  iApply spec_coupl_ret.
  iMod (spec_update_prog (fill K #_) with "Hs Hj") as "[$ Hj]".
  iFrame. iModIntro.
  iMod "Hclose" as "_"; iModIntro.
  iApply "Hwp".
  iFrame.
Qed.

(** spec [rand(α)] with wrong tape  *)
Lemma wp_rand_wrong_tape_r N M z E e K α Φ ns :
  TCEq N (Z.to_nat z) →
  N ≠ M →
  ⤇ fill K (rand(#lbl:α) #z) ∗ α ↪ₛ (M; ns) ∗
  (∀ (n : fin (S N)), (α ↪ₛ (M; ns) ∗ ⤇ fill K #n) -∗ WP e @ E {{ Φ }})
  ⊢ WP e @ E {{ Φ }}.
Proof.
  iIntros (-> ?) "(Hj & Hα & Hwp)".
  iApply wp_lift_step_spec_couple.
  iIntros (σ1 e1' σ1' ε1) "(Hσ & Hs & Hε)".
  iDestruct (spec_auth_prog_agree with "Hs Hj") as %->.
  iDestruct (spec_auth_lookup_tape with "Hs Hα") as %?.
  iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".
  iApply spec_coupl_step; [solve_red|].
  rewrite fill_dmap //=.
  iIntros (e2' σ2' ([? ? ]&?&Hs)%dmap_pos).
  simplify_eq/=.
  rewrite head_prim_step_eq // in Hs.
  inv_head_step.
  iApply spec_coupl_ret.
  iMod (spec_update_prog (fill K #_) with "Hs Hj") as "[$ Hj]".
  iFrame. iModIntro.
  iMod "Hclose" as "_"; iModIntro.
  iApply "Hwp".
  iFrame.
Qed.

End lifting.

Global Hint Extern 0 (TCEq _ (Z.to_nat _ )) => rewrite Nat2Z.id : typeclass_instances.

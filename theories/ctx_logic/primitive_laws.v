(** This file proves the basic laws of the Clutch weakest precondition for ProbLang by applying the
    lifting lemmas. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export ghost_map.
From clutch.ctx_logic Require Export weakestpre.
From clutch.ctx_logic Require Import lifting ectx_lifting.
From clutch.prob_lang Require Export class_instances.
From clutch.prob_lang.spec Require Export spec_ra spec_rules.
From clutch.prob_lang Require Import tactics lang notation metatheory.
From iris.prelude Require Import options.

Class clutchGS Σ := HeapG {
  clutchGS_invG : invGS_gen HasNoLc Σ;
  (* CMRA for the state *)
  clutchGS_heap : ghost_mapG Σ loc val;
  clutchGS_tapes : ghost_mapG Σ loc tape;
  (* ghost names for the state *)
  clutchGS_heap_name : gname;
  clutchGS_tapes_name : gname;
  (* spec resources *)
  clutchGS_spec :: specGS Σ;
}.

Class clutchGpreS Σ := ClutchGpreS {
  clutchGpreS_iris  :: invGpreS Σ;
  clutchGpreS_heap  :: ghost_mapG Σ loc val;
  clutchGpreS_tapes :: ghost_mapG Σ loc tape;
  clutchGpreS_spec  :: specGpreS Σ;
}.

Definition clutchΣ : gFunctors :=
  #[invΣ;
    ghost_mapΣ loc val;
    ghost_mapΣ loc tape;
    specΣ].
Global Instance subG_clutchGPreS {Σ} : subG clutchΣ Σ → clutchGpreS Σ.
Proof. solve_inG. Qed.

Definition heap_auth `{clutchGS Σ} :=
  @ghost_map_auth _ _ _ _ _ clutchGS_heap clutchGS_heap_name.
Definition tapes_auth `{clutchGS Σ} :=
  @ghost_map_auth _ _ _ _ _ clutchGS_tapes clutchGS_tapes_name.

#[global] Instance clutchGS_clutchWpGS `{!clutchGS Σ} : clutchWpGS prob_lang Σ := {
  clutchWpGS_invGS := clutchGS_invG;
  clutchWpGS_spec_updateGS := spec_rules_spec_updateGS;
  state_interp σ := (heap_auth 1 σ.(heap) ∗ tapes_auth 1 σ.(tapes))%I;
}.

(** Heap *)
Notation "l ↦{ dq } v" := (@ghost_map_elem _ _ _ _ _ clutchGS_heap clutchGS_heap_name l dq v)
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Notation "l ↦□ v" := (l ↦{ DfracDiscarded } v)%I
  (at level 20, format "l  ↦□  v") : bi_scope.
Notation "l ↦{# q } v" := (l ↦{ DfracOwn q } v)%I
  (at level 20, format "l  ↦{# q }  v") : bi_scope.
Notation "l ↦ v" := (l ↦{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↦  v") : bi_scope.

(** Tapes *)
Notation "l ↪{ dq } v" := (@ghost_map_elem _ _ tape _ _ clutchGS_tapes clutchGS_tapes_name l dq v)
  (at level 20, format "l  ↪{ dq }  v") : bi_scope.
Notation "l ↪□ v" := (l ↪{ DfracDiscarded } v)%I
  (at level 20, format "l  ↪□  v") : bi_scope.
Notation "l ↪{# q } v" := (l ↪{ DfracOwn q } v)%I
  (at level 20, format "l  ↪{# q }  v") : bi_scope.
Notation "l ↪ v" := (l ↪{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↪  v") : bi_scope.

Section primitive_laws.
Context `{!clutchGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : val → iProp Σ.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types l : loc.

(** Recursive functions: we do not use this lemma as it is easier to use Löb *)
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
  {{{ ▷ α ↪ (N; n :: ns) }}} rand(#lbl: α) #z @ s; E {{{ RET #n; α ↪ (N; ns) }}}.
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
  {{{ ▷ α ↪ (N; []) }}} rand(#lbl:α) #z @ s; E {{{ (n : fin (S N)), RET #n; α ↪ (N; []) }}}.
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
  {{{ ▷ α ↪ (M; ns) }}} rand(#lbl:α) #z @ s; E {{{ (n : fin (S N)), RET #n; α ↪ (M; ns) }}}.
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

(** Spec probabilistic [rand] *)
Lemma wp_rand_r N z E e K Φ :
  TCEq N (Z.to_nat z) →
  ⤇ fill K (rand #z) ∗
  (∀ n : fin (S N), ⤇ fill K #n -∗ WP e @ E {{ Φ }})
  ⊢ WP e @ E {{ Φ }}.
Proof.
  iIntros (->) "(Hj & Hwp)".
  iApply wp_lift_step_spec_couple.
  iIntros (σ1 e1' σ1') "[Hσ Hs]".
  iDestruct (spec_auth_prog_agree with "Hs Hj") as %->.
  iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".
  iApply spec_coupl_steps.
  iExists (λ σ2 '(e2', σ2'), ∃ n : fin (S _), σ2 = σ1 ∧ (e2', σ2') = (fill K #n, σ1')), 1.
  iSplit; [iPureIntro|].
  { rewrite pexec_1 step_or_final_no_final; last first.
    { apply reducible_not_final. solve_red. }
    rewrite -(dret_id_right (dret σ1)).
    rewrite /= fill_dmap //.
    eapply Rcoupl_dbind => /=; [|by eapply Rcoupl_rand_r].
    intros [e2 σ2] (e2' & σ2') (? & -> & [= -> ->]).
    apply Rcoupl_dret=>/=. eauto. }
  iIntros (σ2 e2' σ2' (n & -> & [= -> ->])).
  iMod (spec_update_prog (fill K #n) with "Hs Hj") as "[$ Hj]".
  iFrame. iModIntro.
  iMod "Hclose" as "_"; iModIntro.
  by iApply "Hwp".
Qed.

(** RHS [rand(α)] with empty tape  *)
Lemma wp_rand_empty_r N z E e K α Φ :
  TCEq N (Z.to_nat z) →
  ⤇ fill K (rand(#lbl:α) #z) ∗ α ↪ₛ (N; []) ∗
  (∀ n : fin (S N), (α ↪ₛ (N; []) ∗ ⤇ fill K #n) -∗ WP e @ E {{ Φ }})
  ⊢ WP e @ E {{ Φ }}.
Proof.
  iIntros (->) "(Hj & Hα & Hwp)".
  iApply wp_lift_step_spec_couple.
  iIntros (σ1 e1' σ1') "[Hσ Hs]".
  iDestruct (spec_auth_prog_agree with "Hs Hj") as %->.
  iDestruct (spec_auth_lookup_tape with "Hs Hα") as %?.
  iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".
  iApply spec_coupl_steps.
  iExists (λ σ2 '(e2', σ2'), ∃ n : fin (S _), σ2 = σ1 ∧ (e2', σ2') = (fill K #n, σ1')), 1.
  iSplit; [iPureIntro|].
  { rewrite pexec_1 step_or_final_no_final; last first.
    { apply reducible_not_final. solve_red. }
    rewrite -(dret_id_right (dret σ1)).
    rewrite /= fill_dmap //.
    eapply Rcoupl_dbind => /=; [|by eapply Rcoupl_rand_empty_r].
    intros [e2 σ2] (e2' & σ2') (? & -> & [= -> ->]).
    apply Rcoupl_dret=>/=. eauto. }
  iIntros (σ2 e2' σ2' (n & -> & [= -> ->])).
  iMod (spec_update_prog (fill K #n) with "Hs Hj") as "[$ Hj]".
  iFrame. iModIntro.
  iMod "Hclose" as "_"; iModIntro.
  by iApply ("Hwp" with "[$]").
Qed.

(** RHS [rand(α)] with wrong tape  *)
Lemma wp_rand_wrong_tape_r N M z E e K α Φ ns :
  TCEq N (Z.to_nat z) →
  N ≠ M →
  ⤇ fill K (rand(#lbl:α) #z) ∗ α ↪ₛ (M; ns) ∗
  (∀ (n : fin (S N)), (α ↪ₛ (M; ns) ∗ ⤇ fill K #n) -∗ WP e @ E {{ Φ }})
  ⊢ WP e @ E {{ Φ }}.
Proof.
  iIntros (-> ?) "(Hj & Hα & Hwp)".
  iApply wp_lift_step_spec_couple.
  iIntros (σ1 e1' σ1') "[Hσ Hs]".
  iDestruct (spec_auth_prog_agree with "Hs Hj") as %->.
  iDestruct (spec_auth_lookup_tape with "Hs Hα") as %?.
  iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".
  iApply spec_coupl_steps.
  iExists (λ σ2 '(e2', σ2'), ∃ n : fin (S _), σ2 = σ1 ∧ (e2', σ2') = (fill K #n, σ1')), 1.
  iSplit; [iPureIntro|].
  { rewrite pexec_1 step_or_final_no_final; last first.
    { apply reducible_not_final. solve_red. }
    rewrite -(dret_id_right (dret σ1)).
    rewrite /= fill_dmap //.
    eapply Rcoupl_dbind => /=; [|by eapply Rcoupl_rand_wrong_r].
    intros [e2 σ2] (e2' & σ2') (? & -> & [= -> ->]).
    apply Rcoupl_dret=>/=. eauto. }
  iIntros (σ2 e2' σ2' (n & -> & [= -> ->])).
  iMod (spec_update_prog (fill K #n) with "Hs Hj") as "[$ Hj]".
  iFrame. iModIntro.
  iMod "Hclose" as "_"; iModIntro.
  by iApply ("Hwp" with "[$]").
Qed.

End primitive_laws.

#[global] Hint Extern 0 (TCEq _ (Z.to_nat _ )) => rewrite Nat2Z.id : typeclass_instances.

(** [tc_solve] does not realize that the [spec_updateGS] instances are the same but the [apply:]
    tactic does... *)
#[global] Hint Extern 0
  (ElimModal _ _ _ (spec_update _ _) _ (WP _ @ _ {{ _ }}) (WP _ @ _ {{ _ }})) =>
  apply: elim_modal_spec_update_wp : typeclass_instances.

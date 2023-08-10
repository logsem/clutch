From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Import fancy_updates ghost_map.

From clutch.tpr Require Import weakestpre spec ectx_lifting.
From clutch.prob_lang Require Export class_instances.
From clutch.prob_lang Require Import tactics lang notation.

Class tprGpreS A Σ := TprGpreS {
  tprGpre_iris  :> invGpreS Σ;
  tprGpre_heap  :> ghost_mapG Σ loc val;
  tprGpre_tapes :> ghost_mapG Σ loc tape;
  tpr_spec      :> specPreG A Σ;
}.

Definition tprΣ A: gFunctors :=
  #[invΣ;
    ghost_mapΣ loc val;
    ghost_mapΣ loc tape;
    specΣ A].
Global Instance subG_tprGPreS {A Σ} : subG (tprΣ A) Σ → tprGpreS A Σ.
Proof. solve_inG. Qed.

Class tprG A Σ := TprG {
  tprG_invG :> invGS_gen HasNoLc Σ;
  tprG_heap  : ghost_mapG Σ loc val;
  tprG_tapes : ghost_mapG Σ loc tape;
  tprG_heap_name : gname;
  tprG_tapes_name : gname;
  tprG_specG :> specG A Σ;
}.

Definition heap_auth `{tprG Σ} :=
  @ghost_map_auth _ _ _ _ _ tprG_heap tprG_heap_name.
Definition tapes_auth `{tprG Σ} :=
  @ghost_map_auth _ _ _ _ _ tprG_tapes tprG_tapes_name.

Global Instance tprG_tprwpG `{!tprG A Σ} : tprwpG prob_lang Σ := {
  iris_invGS := _;
  state_interp σ := (heap_auth 1 σ.(heap) ∗ tapes_auth 1 σ.(tapes))%I;
}.

(** Heap *)
Notation "l ↦{ dq } v" := (@ghost_map_elem _ _ _ _ _ tprG_heap tprG_heap_name l dq v)
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Notation "l ↦□ v" := (l ↦{ DfracDiscarded } v)%I
  (at level 20, format "l  ↦□  v") : bi_scope.
Notation "l ↦{# q } v" := (l ↦{ DfracOwn q } v)%I
  (at level 20, format "l  ↦{# q }  v") : bi_scope.
Notation "l ↦ v" := (l ↦{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↦  v") : bi_scope.

(** Tapes *)
Notation "l ↪{ dq } v" := (@ghost_map_elem _ _ _ _ _ tprG_tapes tprG_tapes_name l dq (v : tape))
  (at level 20, format "l  ↪{ dq }  v") : bi_scope.
Notation "l ↪□ v" := (l ↪{ DfracDiscarded } v)%I
  (at level 20, format "l  ↪□  v") : bi_scope.
Notation "l ↪{# q } v" := (l ↪{ DfracOwn q } v)%I
  (at level 20, format "l  ↪{# q }  v") : bi_scope.
Notation "l ↪ v" := (l ↪{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↪  v") : bi_scope.

Section rwp.
  Context  `{markov A B} `{!tprG A Σ}.

  (** * RSWP  *)
  Lemma rswp_alloc k E v :
    ⟨⟨⟨ True ⟩⟩⟩ ref v at k @ E ⟨⟨⟨ l, RET #l; l ↦ v ⟩⟩⟩.
  Proof.
    iIntros (Φ) "_ HΦ".
    iApply rswp_lift_atomic_head_step.
    iIntros (σ1) "[Hh Ht] !# !>".
    iSplit; [by eauto with head_step|].
    iIntros (e2 σ2 Hs); inv_head_step.
    iMod ((ghost_map_insert (fresh_loc σ1.(heap)) v) with "Hh") as "[$ Hl]".
    { apply not_elem_of_dom, fresh_loc_is_fresh. }
    iIntros "!>". iFrame. by iApply "HΦ".
  Qed.

  Lemma rswp_load k E l q v :
    ⟨⟨⟨ ▷ l ↦{q} v ⟩⟩⟩ ! #l at k @ E ⟨⟨⟨ RET v; l ↦{q} v ⟩⟩⟩.
  Proof.
    iIntros (Φ) ">Hl HΦ". iApply rswp_lift_atomic_head_step.
    iIntros (σ1) "[Hh Ht] !> !>".
    iDestruct (ghost_map_lookup with "Hh Hl") as %?.
    iSplit; [by eauto with head_step|].
    iIntros (v2 σ2 Hstep); inv_head_step.
    iModIntro. iFrame. by iApply "HΦ".
  Qed.

  Lemma rswp_store k E l v' v :
    ⟨⟨⟨ ▷ l ↦ v' ⟩⟩⟩ #l <- v at k @ E ⟨⟨⟨ RET #(); l ↦ v ⟩⟩⟩.
  Proof.
    iIntros (Φ) ">Hl HΦ".
    iApply rswp_lift_atomic_head_step.
    iIntros (σ1) "[Hh Ht] !>".
    iDestruct (ghost_map_lookup with "Hh Hl") as %?.
    iSplit; [by eauto with head_step|].
    iIntros "!> /=" (e2 σ2 Hs); inv_head_step.
    iMod (ghost_map_update with "Hh Hl") as "[$ Hl]".
    iFrame. iModIntro. by iApply "HΦ".
  Qed.

  Lemma rswp_rand (N : nat) (z : Z) k E :
    TCEq N (Z.to_nat z) →
    ⟨⟨⟨ True ⟩⟩⟩ rand #z from #() at k @ E ⟨⟨⟨ (n : fin (S N)), RET #n; True ⟩⟩⟩.
  Proof.
    iIntros (-> Φ) "_ HΦ".
    iApply rswp_lift_atomic_head_step.
    iIntros (σ1) "Hσ !#".
    iSplit; [eauto with head_step|].
    Unshelve.
    2 : { apply 0%fin . }
    iIntros "!>" (e2 σ2 Hs).
    inv_head_step.
    iFrame.
    by iApply ("HΦ" $! x) .
  Qed.

  (** * RWP  *)
  Lemma rwp_alloc E v :
    ⟨⟨⟨ True ⟩⟩⟩ ref v @ E ⟨⟨⟨ l, RET #l; l ↦ v ⟩⟩⟩.
  Proof.
    iIntros (Φ) "H HΦ".
    iApply rwp_no_step; [done|].
    by iApply (rswp_alloc with "H HΦ").
  Qed.

  Lemma rwp_load E l q v :
    ⟨⟨⟨ ▷ l ↦{q} v ⟩⟩⟩ ! #l @ E ⟨⟨⟨ RET v; l ↦{q} v ⟩⟩⟩.
  Proof.
    iIntros (Φ) "H HΦ".
    iApply rwp_no_step; [done|].
    by iApply (rswp_load with "H HΦ").
  Qed.

  Lemma rwp_store E l v' v :
    ⟨⟨⟨ ▷ l ↦ v' ⟩⟩⟩ #l <- v @ E ⟨⟨⟨ RET #(); l ↦ v ⟩⟩⟩.
  Proof.
    iIntros (Φ) "H HΦ".
    iApply rwp_no_step; [done|].
    by iApply (rswp_store with "H HΦ").
  Qed.

  Lemma rwp_rand (N : nat) (z : Z) E :
    TCEq N (Z.to_nat z) →
    ⟨⟨⟨ True ⟩⟩⟩ rand #z from #() @ E ⟨⟨⟨ (n : fin (S N)), RET #n; True ⟩⟩⟩.
  Proof.
    iIntros (? Φ) "H HΦ".
    iApply rwp_no_step; [done|].
    by iApply (rswp_rand with "H HΦ").
  Qed.

End rwp.

Section coupl.
  Context `{markov A B} `{!tprG A Σ}.

  Lemma rwp_couple (N : nat) (z : Z) E R a1 :
    TCEq N (Z.to_nat z) →
    Rcoupl (dunifP N) (step a1) R →
    ⟨⟨⟨ specF a1 ⟩⟩⟩ rand #z from #() @ E ⟨⟨⟨ (n : fin (S N)) a2, RET #n; specF a2 ∗ ⌜R n a2⌝ ⟩⟩⟩.
  Proof.
    iIntros (-> ? Φ) "Ha HΦ".
    iApply rwp_lift_step_fupd_coupl; [done|].
    iIntros (σ1 a) "[Hσ1 HaA]".
    iDestruct (spec_auth_agree with "HaA Ha") as %->.
    iApply fupd_mask_intro; [set_solver|].
    iIntros "Hclose".
    assert (head_reducible (rand #z from #()) σ1) as hr.
    { eexists (_, _).
      apply head_step_support_equiv_rel.
      by eapply (RandNoTapeS _ _ 0%fin). }
    iApply rwp_coupl_steps.
    iExists (λ '(e2, σ2) a2, ∃ (n : fin _), e2 = Val #n ∧ σ2 = σ1 ∧ R n a2).
    iSplit.
    { iPureIntro. by apply head_prim_reducible. }
    iSplit.
    { iPureIntro. simpl.
      rewrite head_prim_step_eq //=.
      rewrite -(dret_id_right (step _)).
      eapply Rcoupl_dbind; [|done].
      intros n a2 HR.
      apply Rcoupl_dret. eauto. }
    iIntros ([? ?] a2) "[%n (-> & -> & %)] !> !> !>".
    iMod (spec_auth_update a2 with "HaA Ha") as "[HaA Ha]".
    iMod "Hclose" as "_".
    iModIntro.
    iFrame.
    iApply rwp_value.
    iApply "HΦ". by iFrame.
  Qed.
End coupl.

Global Hint Extern 0 (TCEq _ (Z.to_nat _ )) => rewrite Nat2Z.id : typeclass_instances.

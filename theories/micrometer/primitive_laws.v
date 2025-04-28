(** This file proves the basic laws of the ProbLang weakest precondition by
    applying the lifting lemmas. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export ghost_map.
From clutch.base_logic Require Export error_credits.
From clutch.micrometer Require Export app_weakestpre ectx_lifting.
From clutch.meas_lang Require Export class_instances meas_spec_update.
From clutch.meas_lang Require Import tactics lang notation metatheory tapes.
From clutch.meas_lang.spec Require Export spec_ra spec_rules spec_tactics.
From mathcomp.analysis Require Import measure.
From mathcomp Require Import classical_sets.

From iris.prelude Require Import options.

Local Open Scope classical_set_scope.

Class micrometerGS Σ := HeapG {
  micrometerGS_invG : invGS_gen HasNoLc Σ;
  (* CMRA for the state *)
  micrometerGS_heap : ghost_mapG Σ <<discr loc>> val;
  micrometerGS_tapes : ghost_mapG Σ <<discr loc>> btape;
  micrometerGS_utapes : ghost_mapG Σ <<discr loc>> utape;
  (* ghost names for the state *)
  micrometerGS_heap_name : gname;
  micrometerGS_tapes_name : gname;
  micrometerGS_utapes_name : gname;
  (* CMRA and ghost name for the spec *)
  micrometerGS_spec :: specG_meas_lang Σ;
  (* CMRA and ghost name for the error *)
  micrometerGS_error :: ecGS Σ;
}.


Class micrometerGpreS Σ := MicrometerGpreS {
  micrometerGpreS_iris   :: invGpreS Σ;
  micrometerGpreS_heap   :: ghost_mapG Σ <<discr loc>> val;
  micrometerGpreS_tapes  :: ghost_mapG Σ <<discr loc>> btape;
  micrometerGpreS_utapes :: ghost_mapG Σ <<discr loc>> utape;
  micrometerGpreS_spcec  :: specGpreS Σ;
  micrometerGpreS_err    :: ecGpreS Σ;
}.

Definition micrometerΣ : gFunctors :=
  #[invΣ;
    ghost_mapΣ <<discr loc>> val;
    ghost_mapΣ <<discr loc>> btape;
    ghost_mapΣ <<discr loc>> utape;
    specΣ;
    ecΣ].
Global Instance subG_micrometerGPreS {Σ} : subG micrometerΣ Σ → micrometerGpreS Σ.
Proof. solve_inG. Qed.

Definition heap_auth `{micrometerGS Σ} :=
  @ghost_map_auth _ _ _ _ _ micrometerGS_heap micrometerGS_heap_name.
Definition btapes_auth `{micrometerGS Σ} :=
  @ghost_map_auth _ _ _ _ _ micrometerGS_tapes micrometerGS_tapes_name.
Definition utapes_auth `{micrometerGS Σ} :=
  @ghost_map_auth _ _ _ _ _ micrometerGS_utapes micrometerGS_utapes_name.

(* meas_spec_updateGS (meas_lang_markov meas_lang) Σ *)



Global Instance micrometerGS_irisGS `{!micrometerGS Σ} : micrometerWpGS meas_lang Σ := {
  micrometerWpGS_invGS := micrometerGS_invG;
  state_interp σ :=
      (heap_auth 1 (heap σ) ∗ btapes_auth 1 (tapes σ) ∗ utapes_auth 1 (utapes σ))%I;
  err_interp := ec_supply;
}.

(** Heap *)
Notation "l ↦{ dq } v" := (@ghost_map_elem _ _ _ _ _ micrometerGS_heap micrometerGS_heap_name l dq v)
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Notation "l ↦□ v" := (l ↦{ DfracDiscarded } v)%I
  (at level 20, format "l  ↦□  v") : bi_scope.
Notation "l ↦{# q } v" := (l ↦{ DfracOwn q } v)%I
  (at level 20, format "l  ↦{# q }  v") : bi_scope.
Notation "l ↦ v" := (l ↦{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↦  v") : bi_scope.

(** Tapes *)
Notation "l ↪{ dq } v" := (@ghost_map_elem _ _ tape _ _ micrometerGS_tapes micrometerGS_tapes_name l dq v)
  (at level 20, format "l  ↪{ dq }  v") : bi_scope.
Notation "l ↪□ v" := (l ↪{ DfracDiscarded } v)%I
  (at level 20, format "l  ↪□  v") : bi_scope.
Notation "l ↪{# q } v" := (l ↪{ DfracOwn q } v)%I
  (at level 20, format "l  ↪{# q }  v") : bi_scope.
Notation "l ↪ v" := (l ↪{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↪  v") : bi_scope.

(** UTapes *)
Notation "l ↪ℝ{ dq } v" := (@ghost_map_elem _ _ tape _ _ micrometerGS_tapes micrometerGS_tapes_name l dq v)
  (at level 20, format "l  ↪ℝ{ dq }  v") : bi_scope.
Notation "l ↪ℝ□ v" := (l ↪ℝ{ DfracDiscarded } v)%I
  (at level 20, format "l  ↪ℝ□  v") : bi_scope.
Notation "l ↪ℝ{# q } v" := (l ↪ℝ{ DfracOwn q } v)%I
  (at level 20, format "l  ↪ℝ{# q }  v") : bi_scope.
Notation "l ↪ℝ v" := (l ↪ℝ{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↪ℝ  v") : bi_scope.
(*


(** User-level tapes *)
Definition nat_tape `{micrometerGS Σ} l (N : nat) (ns : list nat) : iProp Σ :=
  ∃ (fs : list (fin (S N))), ⌜fin_to_nat <$> fs = ns⌝ ∗ l ↪ (N; fs).

Notation "l ↪N ( M ; ns )" := (nat_tape l M ns)%I
  (at level 20, format "l  ↪N  ( M ;  ns )") : bi_scope.

Definition nat_spec_tape `{micrometerGS Σ} l (N : nat) (ns : list nat) : iProp Σ :=
  ∃ (fs : list (fin (S N))), ⌜fin_to_nat <$> fs = ns⌝ ∗ l ↪ₛ (N; fs).

Notation "l ↪ₛN ( M ; ns )" := (nat_spec_tape l M ns)%I
       (at level 20, format "l ↪ₛN ( M ; ns )") : bi_scope. *)

Section tape_interface.
  Context `{!micrometerGS Σ}.

  (*
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
  Qed. *)

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
Context `{!micrometerGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : val → iProp Σ.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types l : loc.

(** Recursive functions: we do not use this lemma as it is easier to use Löb
    induction directly, but this demonstrates that we can state the expected
    reasoning principle for recursive functions, without any visible ▷. *)


Lemma wp_rec_löb E f (x : <<discr binders.binder>>) e Φ Ψ :
  □ ( □ (∀ v, Ψ v -∗ WP (AppC (ValC (RecVC f x e)) (ValC v) : meas_lang.language.expr meas_lang) @ E {{ Φ }}) -∗
     ∀ v, Ψ v -∗
          let e' : meas_lang.language.expr meas_lang := (substU' (x, (v, (substU' (f, ((RecVC f x e), e)))))) in
          WP e' @ E {{ Φ }}) -∗
  ∀ v, Ψ v -∗
       let e' : meas_lang.language.expr meas_lang := AppC (ValC (RecVU ((f, x), e))) (ValC v) in
       WP e' @ E {{ Φ }}.
Proof.
  iIntros "#Hrec". iLöb as "IH". iIntros (v) "HΨ".
  iApply (@lifting.wp_pure_step_later _ _ _ _ _ _ _ _ _ 1).
  { unfold PureExec.
    admit. (* rec ctor? *) }
  { admit. (* Should reduce under no hypotheses *) }
  iNext. iApply ("Hrec" with "[] HΨ"). iIntros "!>" (w) "HΨ".
  iApply ("IH" with "HΨ").
Admitted.

Local Open Scope classical_set_scope.

(** Heap *)
Lemma wp_alloc E v s :
  {{{ True }}}
    (AllocC (ValC v) : meas_lang.language.expr meas_lang) @ s; E
  {{{ l, RET (LitVC (LitLocC l) : meas_lang.language.val meas_lang); l ↦ v }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  iApply wp_lift_atomic_head_step; [done|];  simpl.
  iIntros (σ1) "[Hh [Ht Hu]] !#".
  iSplitR.
  { iPureIntro. (* solve_red *) admit. }
  iApply EXSM_ret.
  { rewrite prod1.
    apply measurableX; [ by apply expr_meas_singleton | by apply state_meas_singleton ]. }
  iIntros "!> //=".

  iMod (ghost_map_insert (γ:=micrometerGS_heap_name) (heap (state_upd_heap <[state.fresh (heap σ1):=v]> σ1)) with "[Hh]") as "[Hl ?]".
  2: {
    unfold heap_auth.
    admit. (* iApply "Hh". *) }
  1: admit.
  (* { apply not_elem_of_dom, fresh_loc_is_fresh. } *)
  (* ?? *)
Admitted.
(*

  iFrame.
  rewrite map_union_empty -insert_union_singleton_l.
  iFrame.
  iIntros "!>". by iApply "HΦ".
Qed. *)

(*
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
*)

Lemma wp_load E l dq v s :
  {{{ ▷ l ↦{dq} v }}} (Load (Val $ LitV $ LitLoc l) : meas_lang.language.expr meas_lang) @ s; E {{{ RET (v : val); l ↦{dq} v }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  simpl.
  iIntros (σ1) "[Hh Ht] !#".
  iDestruct (ghost_map_lookup with "Hh Hl") as %?.
  iSplitR.
  { admit. (* solve_red. *) }
  iExists [set (ValC v, σ1)].
  iSplitR. {
    iPureIntro.
    rewrite prod1.
    by apply measurableX; [apply expr_meas_singleton | apply state_meas_singleton]. }
  iSplitR. {
    rewrite H.
    iPureIntro.
    apply gRetMass1Inv.
    { rewrite prod1.
      by apply measurableX; [apply expr_meas_singleton | apply state_meas_singleton]. }
    { by rewrite //=. }
  }
  simpl.
  iIntros (ρ ->) "!> _ //=".
  iModIntro.
  iSplitL "Hh Ht".
  { iSplitL "Hh"; done. }
  iApply "HΦ".
  iAssumption.
Admitted.

Lemma wp_store E l v' v s :
  {{{ ▷ l ↦ v' }}} (Store (Val $ LitV (LitLoc l)) (Val v) : meas_lang.language.expr meas_lang) @ s; E
  {{{ RET (LitV LitUnit : val) ; l ↦ v }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  simpl.
  iIntros (σ1) "[Hh Ht] !#".
  iDestruct (ghost_map_lookup with "Hh Hl") as %?.
  iSplitR. { (* solve_red *) admit. }
  iExists [set (Val (LitVU ()%V), state_upd_heap <[l:=v]> σ1)].
  iSplitR. {
    iPureIntro.
    rewrite prod1.
    by apply (measurableX (T1:=expr)); [apply expr_meas_singleton | apply state_meas_singleton]. }
  iSplitR. { rewrite H; iPureIntro; apply gRetMass1Inv.
    { rewrite prod1.
      by apply (measurableX (T1:=expr)); [apply expr_meas_singleton | apply state_meas_singleton]. }
    { by rewrite //=. }
  }
  iIntros (? ->) "!> /= _".
  iMod (ghost_map_update with "Hh Hl") as "[$ Hl]".
  iModIntro.
  iSplitR "HΦ Hl"; [done|].
  iApply "HΦ".
  iAssumption.
Admitted.

Lemma wp_rand (N : nat) (z : Z) E s :
  TCEq N (Z.to_nat z) →
  {{{ True }}} (rand (Val (LitV (LitInt z))) : meas_lang.language.expr meas_lang) @ s; E {{{ (n : nat), RET (#(LitInt $ Z.of_nat n) : val); ⌜n <= N⌝ }}}.
Proof.
  iIntros (-> Φ) "_ HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  simpl.
  iIntros (σ1) "Hσ !#".
  iSplitR. { (* red *) admit. }


(*
  iIntros "!>" (e2 σ2 Hs).
  inv_head_step.
  iFrame.
  iApply ("HΦ" $! x).
  iPureIntro.
  pose proof (fin_to_nat_lt x); lia.
Qed. *) Admitted.


(** Tapes  *)

(*
Lemma wp_alloc_tape N z E s :
  TCEq N (Z.to_nat z) →
  {{{ True }}} (alloc (Val (LitV (LitInt z))) :  meas_lang.language.expr meas_lang)@ s; E {{{ α, RET #lbl:α; α ↪N (N; []) }}}.
Proof.
  iIntros (-> Φ) "_ HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "(Hh & Ht) !# /=".
  solve_red.
  iIntros "!>" (e2 σ2 Hs); inv_head_step.
  iMod (ghost_map_insert (fresh_loc σ1.(tapes)) with "Ht") as "[$ Hl]".
  { apply not_elem_of_dom, fresh_loc_is_fresh. }
  iFrame. iModIntro.
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
  iIntros "!>" (e2 σ2 Hs).
  inv_head_step.
  iMod (ghost_map_update with "Ht Hl") as "[$ Hl]".
  iFrame. iModIntro.
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
  iIntros "!>" (e2 σ2 Hs).
  inv_head_step.
  iFrame.
  iModIntro. iApply ("HΦ" with "[$Hl]").
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
  iIntros "!>" (e2 σ2 Hs).
  inv_head_step.
  iFrame.
  iModIntro.
  iApply ("HΦ").
  iFrame.
  iPureIntro.
  pose proof (fin_to_nat_lt x); lia.
Qed.

(** spec [rand] *)
Lemma wp_rand_r N z E e K Φ :
  TCEq N (Z.to_nat z) →
  ⤇ fill K (rand #z) ∗
  (∀ n : nat, ⤇ fill K #n -∗ ⌜ n <= N ⌝ -∗ WP e @ E {{ Φ }})
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
  iApply ("Hwp" with "Hj").
  iPureIntro.
  pose proof (fin_to_nat_lt x); lia.
Qed.

(** This is just a wrapper for tp_alloctape that works with nats
    TODO : Make into tactic *)
Lemma wp_alloc_tape_r N z E e K Φ :
  TCEq N (Z.to_nat z) →
  ⤇ fill K (alloc #z) ∗
    (∀ α, ⤇ fill K #lbl:α -∗ α ↪ₛN (N; []) -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
Proof.
  iIntros (->) "(Hj & Hwp)".
  tp_alloctape as α "Hα".
  iApply ("Hwp" with "Hj").
  iFrame.
  iPureIntro.
  auto.
Qed.

(** spec [rand(α)] with empty tape  *)
Lemma wp_rand_empty_r N z E e K α Φ :
  TCEq N (Z.to_nat z) →
  ⤇ fill K (rand(#lbl:α) #z) ∗ α ↪ₛN (N; []) ∗
  (∀ n : nat, (α ↪ₛN (N; []) ∗ ⤇ fill K #n) -∗ ⌜ n <= N ⌝ -∗ WP e @ E {{ Φ }})
  ⊢ WP e @ E {{ Φ }}.
Proof.
  iIntros (->) "(Hj & Hα & Hwp)".
  iApply wp_lift_step_spec_couple.
  iIntros (σ1 e1' σ1' ε1) "(Hσ & Hs & Hε)".
  iPoseProof (spec_tapeN_to_empty with "Hα") as "Hα".
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
  iApply ("Hwp" with "[Hα Hj]");
   first by iFrame; auto.
  iPureIntro.
  pose proof (fin_to_nat_lt x); lia.
Qed.


(** This is just a wrapper for tp_rand that works with nats
    TODO: Make into tactic *)
Lemma wp_rand_tape_r N z E e K α Φ n ns :
  TCEq N (Z.to_nat z) →
  ⤇ fill K (rand(#lbl:α) #z) ∗ α ↪ₛN (N; n::ns) ∗
    ((α ↪ₛN (N; ns) ∗ ⤇ fill K #n) -∗ ⌜ n <= N ⌝ -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
Proof.
  iIntros (Heq) "(Hj & Hα & Hwp)".
  iDestruct (read_spec_tape_head with "Hα") as (x xs) "(Hl&<-&Hret)".
  tp_rand.
  iDestruct ("Hret" with "Hl") as "Hret".
  iApply ("Hwp" with "[$]").
  iPureIntro.
  pose proof (fin_to_nat_lt x); lia.
Qed.


  (** spec [rand(α)] with wrong tape  *)
  Lemma wp_rand_wrong_tape_r N M z E e K α Φ ns :
    TCEq N (Z.to_nat z) →
    N ≠ M →
    ⤇ fill K (rand(#lbl:α) #z) ∗ α ↪ₛN (M; ns) ∗
      (∀ (n : nat), (α ↪ₛN (M; ns) ∗ ⤇ fill K #n) -∗ ⌜ n <= N ⌝ -∗ WP e @ E {{ Φ }})
      ⊢ WP e @ E {{ Φ }}.
Proof.
  iIntros (-> ?) "(Hj & Hα & Hwp)".
  iApply wp_lift_step_spec_couple.
  iIntros (σ1 e1' σ1' ε1) "(Hσ & Hs & Hε)".
  iDestruct "Hα" as (?) "(%&Hα)".
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
  iApply ("Hwp" with "[-]"); first by iFrame.
  iPureIntro.
  pose proof (fin_to_nat_lt x); lia.
Qed.

*)
End lifting.

Global Hint Extern 0 (TCEq _ (Z.to_nat _ )) => rewrite Nat2Z.id : typeclass_instances.

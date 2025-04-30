(** This file proves the basic laws of the ProbLang weakest precondition by
    applying the lifting lemmas. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export ghost_map.
From clutch.base_logic Require Export error_credits_mult.
From clutch.diffpriv Require Export weakestpre ectx_lifting.
From clutch.prob_lang Require Export class_instances.
From clutch.prob_lang Require Import tactics lang notation metatheory.
From clutch.prob_lang.spec Require Export spec_ra spec_rules spec_tactics.
From iris.prelude Require Import options.

Class diffprivGS Σ := HeapG {
  diffprivGS_invG : invGS_gen HasNoLc Σ;
  (* CMRA for the state *)
  diffprivGS_heap : ghost_mapG Σ loc val;
  diffprivGS_tapes : ghost_mapG Σ loc tape;
  (* ghost names for the state *)
  diffprivGS_heap_name : gname;
  diffprivGS_tapes_name : gname;
  (* CMRA and ghost name for the spec *)
  diffprivGS_spec :: specG_prob_lang Σ;
  (* CMRA and ghost name for the error *)
  diffprivGS_error :: ecGS Σ;
}.

Class diffprivGpreS Σ := DiffprivGpreS {
  diffprivGpreS_iris  :: invGpreS Σ;
  diffprivGpreS_heap  :: ghost_mapG Σ loc val;
  diffprivGpreS_tapes :: ghost_mapG Σ loc tape;
  diffprivGpreS_spcec :: specGpreS Σ;
  diffprivGpreS_err   :: ecGpreS Σ;
}.

Definition diffprivΣ : gFunctors :=
  #[invΣ;
    ghost_mapΣ loc val;
    ghost_mapΣ loc tape;
    specΣ;
    ecΣ].
Global Instance subG_diffprivGPreS {Σ} : subG diffprivΣ Σ → diffprivGpreS Σ.
Proof. solve_inG. Qed.

Definition heap_auth `{diffprivGS Σ} :=
  @ghost_map_auth _ _ _ _ _ diffprivGS_heap diffprivGS_heap_name.
Definition tapes_auth `{diffprivGS Σ} :=
  @ghost_map_auth _ _ _ _ _ diffprivGS_tapes diffprivGS_tapes_name.

Global Instance diffprivGS_irisGS `{!diffprivGS Σ} : diffprivWpGS prob_lang Σ := {
  diffprivWpGS_invGS := diffprivGS_invG;
  state_interp σ := (heap_auth 1 σ.(heap) ∗ tapes_auth 1 σ.(tapes))%I;
  err_interp := ec_supply;
}.

(** Heap *)
Notation "l ↦{ dq } v" := (@ghost_map_elem _ _ _ _ _ diffprivGS_heap diffprivGS_heap_name l dq v)
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Notation "l ↦□ v" := (l ↦{ DfracDiscarded } v)%I
  (at level 20, format "l  ↦□  v") : bi_scope.
Notation "l ↦{# q } v" := (l ↦{ DfracOwn q } v)%I
  (at level 20, format "l  ↦{# q }  v") : bi_scope.
Notation "l ↦ v" := (l ↦{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↦  v") : bi_scope.

(** Tapes *)
Notation "l ↪{ dq } v" := (@ghost_map_elem _ _ tape _ _ diffprivGS_tapes diffprivGS_tapes_name l dq v)
  (at level 20, format "l  ↪{ dq }  v") : bi_scope.
Notation "l ↪□ v" := (l ↪{ DfracDiscarded } v)%I
  (at level 20, format "l  ↪□  v") : bi_scope.
Notation "l ↪{# q } v" := (l ↪{ DfracOwn q } v)%I
  (at level 20, format "l  ↪{# q }  v") : bi_scope.
Notation "l ↪ v" := (l ↪{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↪  v") : bi_scope.

(** User-level tapes *)
Definition nat_tape `{diffprivGS Σ} l (N : nat) (ns : list nat) : iProp Σ :=
  ∃ (fs : list (fin (S N))), ⌜fin_to_nat <$> fs = ns⌝ ∗ l ↪ (N; fs).

Notation "l ↪N ( M ; ns )" := (nat_tape l M ns)%I
  (at level 20, format "l  ↪N  ( M ;  ns )") : bi_scope.

(*
Definition nat_spec_tape `{diffprivGS Σ} l (N : nat) (ns : list nat) : iProp Σ :=
  ∃ (fs : list (fin (S N))), ⌜fin_to_nat <$> fs = ns⌝ ∗ l ↪ₛ (N; fs).

Notation "l ↪ₛN ( M ; ns )" := (nat_spec_tape l M ns)%I
       (at level 20, format "l ↪ₛN ( M ; ns )") : bi_scope.
*)

Section tape_interface.
  Context `{!diffprivGS Σ}.

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
Context `{!diffprivGS Σ}.
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
  {{{ True }}} rand #z @ s; E {{{ (n : nat), RET #n; ⌜n <= N⌝ }}}.
Proof.
  iIntros (-> Φ) "_ HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "Hσ !#".
  solve_red.
  iIntros "!>" (e2 σ2 Hs).
  inv_head_step.
  iFrame.
  iApply ("HΦ" $! x).
  iPureIntro.
  pose proof (fin_to_nat_lt x); lia.
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

End lifting.

Global Hint Extern 0 (TCEq _ (Z.to_nat _ )) => rewrite Nat2Z.id : typeclass_instances.

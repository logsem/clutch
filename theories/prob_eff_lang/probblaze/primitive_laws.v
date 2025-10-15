(** This file proves the basic laws of the ProbLang weakest precondition by
    applying the lifting lemmas. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export ghost_map.
From clutch.common Require Import locations.
From clutch.base_logic Require Export error_credits.
From clutch.approxis Require Export app_weakestpre ectx_lifting.
From clutch.prob_eff_lang.probblaze Require Import syntax semantics notation.
From clutch.prob_eff_lang.probblaze Require Export spec_ra class_instances ectx_lifting.
From iris.prelude Require Import options.

Class probblazeGS Σ := HeapG {
    probblazeGS_invG : invGS_gen HasNoLc Σ;
  (* CMRA for the state *)
  probblazeGS_heap : ghost_mapG Σ loc syntax.val;
  probblazeGS_tapes : ghost_mapG Σ loc tape;
  probblazeGS_labels : ghost_mapG Σ label unit;
  (* ghost names for the state *)
  probblazeGS_heap_name : gname;
  probblazeGS_tapes_name : gname;
  probblazeGS_labels_name : gname;
  (* CMRA and ghost name for the spec *)
  probblazeGS_spec :: specG_blaze_prob_lang Σ;
  (* CMRA and ghost name for the error *)
  probblazeGS_error :: ecGS Σ;
}.

Class probblazeGpreS Σ := ProbblazeGpreS {
  probblazeGpreS_iris  :: invGpreS Σ;
  probblazeGpreS_heap  :: ghost_mapG Σ loc syntax.val;
  probblazeGpreS_tapes :: ghost_mapG Σ loc tape;
  probblazeGpreS_labels :: ghost_mapG Σ label unit;                            
  probblazeGpreS_spec :: specGpreS Σ;
  probblaGpreS_err   :: ecGpreS Σ;
}.

Definition probblazeΣ : gFunctors :=
  #[invΣ;
    ghost_mapΣ loc syntax.val;
    ghost_mapΣ loc tape;
    ghost_mapΣ label unit;
    specΣ;
    ecΣ].
Global Instance subG_probblazeGPreS {Σ} : subG probblazeΣ Σ → probblazeGpreS Σ.
Proof. solve_inG. Qed.

Definition past_labels (l : label) : list label :=
  imap (λ l' _, Label l') (replicate (label_car l)%nat ()).

Definition to_labels (l : label) : gmap label () :=
  let kv_pair l := (l, ()) in
  list_to_map (kv_pair <$> past_labels l).


Section past_labels.

  Local Open Scope nat.

  Lemma past_labels_succ l :
    past_labels (label_succ l) = past_labels l ++ [l].
  Proof.
    rewrite /past_labels /label_succ.
    destruct l as [n].
    rewrite replicate_S_end.
    by rewrite imap_app //= replicate_length Nat.add_0_r.
  Qed.

  Lemma NoDup_past_labels l : NoDup (past_labels l).
  Proof.
    destruct l as [n].
    induction n as [|n IH].
    - rewrite /past_labels //=.
      by apply NoDup_nil.
    - rewrite (past_labels_succ (Label n)).
      rewrite NoDup_app.
      split; [done|].
      split; [|apply NoDup_singleton].
      intros l Hl.
      rewrite elem_of_list_lookup in Hl.
      destruct Hl as [i Hl].
      rewrite list_lookup_imap_Some in Hl.
      destruct Hl as [() [Hi ->]].
      rewrite lookup_replicate in Hi.
      destruct Hi as [_ Hi]. simpl in Hi.
      rewrite elem_of_list_singleton.
      inversion 1.
      apply (Nat.lt_irrefl n).
      by rewrite H1 in Hi.
  Qed.

  Lemma lookup_past_labels_Some l i :
    i < label_car l → past_labels l !! i = Some (Label i).
  Proof.
    rewrite /past_labels list_lookup_imap_Some.
    intros Hi. exists (). split; [|done].
    rewrite lookup_replicate. by split.
  Qed.

  Lemma lookup_past_labels_None l i :
    i ≥ label_car l → past_labels l !! i = None.
  Proof.
    intros Hi.
    apply lookup_ge_None_2.
    by rewrite imap_length replicate_length.
  Qed.

  Lemma elem_of_past_labels l l' :
    label_car l < label_car l' → l ∈ past_labels l'.
  Proof.
    intros Hl.
    rewrite elem_of_list_lookup.
    exists (label_car l).
    destruct l as [n].
    by apply lookup_past_labels_Some.
  Qed.

  Lemma not_elem_of_past_labels l l' :
    label_car l ≥ label_car l' → l ∉ past_labels l'.
  Proof.
    rewrite elem_of_list_lookup.
    intros Hl [i Hlkp].
    case (le_gt_dec (label_car l') i).
    - intros Hl'.
      rewrite (lookup_past_labels_None l' i) in Hlkp; [|done].
      by inversion Hlkp.
    - intros Hl'.
      rewrite (lookup_past_labels_Some l' i) in Hlkp; [|done].
      inversion Hlkp.
      simplify_eq.
      simpl in Hl.
      apply (Nat.lt_irrefl i).
      by apply (Nat.lt_le_trans _ (label_car l')).
  Qed.

End past_labels.

Section to_labels.

  Local Open Scope nat_scope.

  Lemma lookup_to_labels_None l l' :
    label_car l' ≤ label_car l →
    (to_labels l') !! l = None.
  Proof.
    intros Hl.
    rewrite /to_labels.
    rewrite -not_elem_of_list_to_map.
    rewrite -list_fmap_compose.
    rewrite elem_of_list_fmap.
    intros [l'' [Heq Hin]].
    simpl in Heq.
    rewrite -Heq in Hin.
    by apply (not_elem_of_past_labels l l').
  Qed.

  Lemma lookup_to_labels_Some l l' :
    label_car l < label_car l' →
    (to_labels l') !! l = Some ().
  Proof.
    intros Hl.
    rewrite /to_labels.
    apply (elem_of_list_to_map_1 (_ <$> past_labels l') l).
    - rewrite -list_fmap_compose //=.
      by apply NoDup_fmap_2; [intros ??|apply NoDup_past_labels].
    - rewrite elem_of_list_fmap.
      exists l. split; [done|].
      by apply elem_of_past_labels.
  Qed.

  Lemma to_labels_succ l :
    to_labels (label_succ l) = <[l := ()]> (to_labels l).
  Proof.
    rewrite /to_labels past_labels_succ fmap_app list_to_map_app //=.
    rewrite insert_empty map_union_comm.
    - by rewrite -insert_union_singleton_l.
    - rewrite map_disjoint_singleton_r.
      by apply lookup_to_labels_None.
  Qed.

End to_labels.


Definition heap_auth `{probblazeGS Σ} :=
  @ghost_map_auth _ _ _ _ _ probblazeGS_heap probblazeGS_heap_name.
Definition tapes_auth `{probblazeGS Σ} :=
  @ghost_map_auth _ _ _ _ _ probblazeGS_tapes probblazeGS_tapes_name.
Definition labels_auth `{probblazeGS Σ} :=
  @ghost_map_auth _ _ _ _ _ probblazeGS_labels probblazeGS_labels_name.

Global Instance probblazeGS_irisGS `{!probblazeGS Σ} : approxisWpGS blaze_prob_lang Σ := {
  approxisWpGS_invGS := probblazeGS_invG;
  state_interp σ := (heap_auth 1 σ.(heap) ∗ tapes_auth 1 σ.(tapes) ∗ labels_auth 1 (to_labels (next_label σ)))%I;
  err_interp := ec_supply;
  }.

(** Labels *)
Local Definition is_label `{probblazeGS Σ} (l : label) (dq : dfrac) : iProp Σ :=
  @ghost_map_elem _ _ _ _ _ probblazeGS_labels probblazeGS_labels_name l dq ().

(** Heap *)
Notation "l ↦{ dq } v" := (@ghost_map_elem _ _ _ _ _ probblazeGS_heap probblazeGS_heap_name l dq v)
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Notation "l ↦□ v" := (l ↦{ DfracDiscarded } v)%I
  (at level 20, format "l  ↦□  v") : bi_scope.
Notation "l ↦{# q } v" := (l ↦{ DfracOwn q } v)%I
  (at level 20, format "l  ↦{# q }  v") : bi_scope.
Notation "l ↦ v" := (l ↦{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↦  v") : bi_scope.

(** Tapes *)
Notation "l ↪{ dq } v" := (@ghost_map_elem _ _ tape _ _ probblazeGS_tapes probblazeGS_tapes_name l dq v)
  (at level 20, format "l  ↪{ dq }  v") : bi_scope.
Notation "l ↪□ v" := (l ↪{ DfracDiscarded } v)%I
  (at level 20, format "l  ↪□  v") : bi_scope.
Notation "l ↪{# q } v" := (l ↪{ DfracOwn q } v)%I
  (at level 20, format "l  ↪{# q }  v") : bi_scope.
Notation "l ↪ v" := (l ↪{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↪  v") : bi_scope.

(** User-level tapes *)
Definition nat_tape `{probblazeGS Σ} l (N : nat) (ns : list nat) : iProp Σ :=
  ∃ (fs : list (fin (S N))), ⌜fin_to_nat <$> fs = ns⌝ ∗ l ↪ (N; fs).

Notation "l ↪N ( M ; ns )" := (nat_tape l M ns)%I
  (at level 20, format "l  ↪N  ( M ;  ns )") : bi_scope.

Section tape_interface.
  Context `{!probblazeGS Σ}.

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

End tape_interface.

Section lifting.
Context `{!probblazeGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : syntax.val → iProp Σ.
Implicit Types σ : syntax.state.
Implicit Types v : syntax.val.
Implicit Types l : loc.
Implicit Types ℓ : label.

(** Recursive functions: we do not use this lemma as it is easier to use Löb
    induction directly, but this demonstrates that we can state the expected
    reasoning principle for recursive functions, without any visible ▷. *)

Lemma wp_rec_löb E f x e Φ Ψ :
  □ ( □ (∀ v, Ψ v -∗ WP (rec: f x := e)%V v @ E {{ Φ }}) -∗
     ∀ v, Ψ v -∗ WP (val_subst' x v (val_subst' f (rec: f x := e) e)) @ E {{ Φ }}) -∗
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
  iSplit. { iPureIntro. eexists. apply head_step_support_equiv_rel. constructor; eauto. } (* implement solve_red *)
  iIntros "!>" (e2 σ2 Hs); simplify_eq; inv_head_step.
  iMod ((ghost_map_insert (fresh_loc σ1.(heap)) v) with "Hh") as "[? Hl]".
  { apply not_elem_of_dom, fresh_loc_is_fresh. }
  iFrame.
  rewrite map_union_empty -insert_union_singleton_l.
  iFrame.
  iIntros "!>". by iApply "HΦ".
Qed.

Lemma heap_array_app l vs1 vs2 : heap_array l (vs1 ++ vs2) = (heap_array l vs1) ∪ (heap_array (l +ₗ (length vs1)) vs2) .
Proof.
  revert l.
  induction vs1; intro l.
  - simpl.
    rewrite map_empty_union loc_add_0 //.
  - rewrite -app_comm_cons /= IHvs1.
    rewrite map_union_assoc.
    do 2 f_equiv.
    rewrite Nat2Z.inj_succ /=.
    rewrite /Z.succ
      Z.add_comm
      loc_add_assoc //.
Qed.


Lemma heap_array_replicate_S_end l v n :
  heap_array l (replicate (S n) v) = heap_array l (replicate n v) ∪ {[l +ₗ n:= v]}.
Proof.
  induction n.
  - simpl.
    rewrite map_union_empty.
    rewrite map_empty_union.
    by rewrite loc_add_0.
  - rewrite replicate_S_end
     heap_array_app
     IHn /=.
    rewrite map_union_empty replicate_length //.
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
  iIntros "!>" (e2 σ2 Hs); simplify_eq; inv_head_step.
  iMod ((ghost_map_insert_big _ _ with "Hh")) as "[$ Hl]".
  iIntros "!>". iFrame.
  iApply "HΦ".
  iInduction (H0) as [ | ?] "IH" forall (σ1).
  - simpl.
    iSplit; auto.
    rewrite map_union_empty.
    rewrite loc_add_0.
    by rewrite big_sepM_singleton.
  - rewrite seq_S. do 2rewrite Nat2Z.id.
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
  iSplit. { iPureIntro. eexists. apply head_step_support_equiv_rel. constructor; eauto. } (* implement solve_red *)
  iIntros "!>" (e2 σ2 Hs); inv_head_step.
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
  iSplit. { iPureIntro. eexists. apply head_step_support_equiv_rel. econstructor; eauto. } (* implement solve_red *)
  iIntros "!>" (e2 σ2 Hs); inv_head_step.
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
  iSplit. { iPureIntro. eexists. apply head_step_support_equiv_rel. constructor; eauto. } (* implement solve_red *)
  iIntros "!>" (e2 σ2 Hs).
  inv_head_step.
  iFrame.
  iApply ("HΦ" $! x).
  iPureIntro.
  pose proof (fin_to_nat_lt x). apply le_INR. lia.
  Unshelve. apply Fin.F1.
Qed.

(** Tapes  *)
Lemma wp_alloc_tape N z E s :
  TCEq N (Z.to_nat z) →
  {{{ True }}} alloc #z @ s; E {{{ α, RET #lbl:α; α ↪N (N; []) }}}.
Proof.
  iIntros (-> Φ) "_ HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "(Hh & Ht & Hlab) !#".
  iSplit. { iPureIntro. eexists. apply head_step_support_equiv_rel. constructor; eauto. } (* implement solve_red *)
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
  iIntros (σ1) "(Hh & Ht & Hlab) !#".
  iDestruct (read_tape_head with "Hl") as (x xs) "(Hl&<-&Hret)".
  iDestruct (ghost_map_lookup with "Ht Hl") as %?.
  iSplit. { iPureIntro. eexists. apply head_step_support_equiv_rel. constructor; eauto. } (* implement solve_red *)
  iIntros "!>" (e2 σ2 Hs).
  inv_head_step.
  iMod (ghost_map_update with "Ht Hl") as "[$ Hl]".
  iFrame. iModIntro.
  iApply "HΦ".
  iSplit; first by iApply "Hret".
  iPureIntro.
  pose proof (fin_to_nat_lt x). apply le_INR. lia.
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
  iIntros (σ1) "(Hh & Ht & Hlab) !#".
  iDestruct (ghost_map_lookup with "Ht Hl") as %?.
  iSplit. { iPureIntro. eexists. apply head_step_support_equiv_rel. apply RandTapeEmptyS; eauto. } (* implement solve_red *)
  iIntros "!>" (e2 σ2 Hs).
  inv_head_step.
  iFrame.
  iModIntro. iApply ("HΦ" with "[$Hl]").
  iSplit; auto.
  iPureIntro.
  pose proof (fin_to_nat_lt x); apply le_INR; lia.
  Unshelve. apply Fin.F1.
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
  iIntros (σ1) "(Hh & Ht & Hlab) !#".
  iDestruct "Hl" as (?) "(?&Hl)".
  iDestruct (ghost_map_lookup with "Ht Hl") as %?.
  iSplit. { iPureIntro. eexists. apply head_step_support_equiv_rel. eapply RandTapeOtherS; eauto. } (* implement solve_red *)
  iIntros "!>" (e2 σ2 Hs).
  inv_head_step.
  iFrame.
  iModIntro.
  iApply ("HΦ").
  iFrame.
  iPureIntro.
  pose proof (fin_to_nat_lt x); apply le_INR; lia.
  Unshelve. apply Fin.F1.
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
  iApply spec_coupl_step.
  { eexists. simpl. unfold semantics.prim_step.
    setoid_rewrite head_reducible_decomp_ctx;
      [|done| eexists; apply head_step_support_equiv_rel; unshelve econstructor; eauto using Fin.F1].
    apply dmap_pos. eexists. split; last first.
    - apply head_step_support_equiv_rel. unshelve econstructor; eauto using Fin.F1.
    - done. Unshelve. done.}
  iIntros (e2' σ2' Hstep). simpl in Hstep.
  rewrite semantics.fill_dmap in Hstep; eauto.
  apply dmap_pos in Hstep as ([? ?]&?&Hs).
  simplify_eq/=. 
  setoid_rewrite head_prim_step_eq in Hs. 2 : { eexists. apply head_step_support_equiv_rel. unshelve constructor; eauto using Fin.F1. }
  inv_head_step.
  iApply spec_coupl_ret.
  iMod (spec_update_prog (fill K #_) with "Hs Hj") as "[$ Hj]".
  iFrame. iModIntro.
  iMod "Hclose" as "_"; iModIntro.
  iApply ("Hwp" with "Hj").
  iPureIntro.
  pose proof (fin_to_nat_lt x); apply le_INR; lia.
Qed.

(** This is just a wrapper for tp_alloctape that works with nats
    TODO : Make into tactic *)
(* Lemma wp_alloc_tape_r N z E e K Φ :
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
   Qed. *)

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
  iApply spec_coupl_step.
   { eexists. simpl. unfold semantics.prim_step. 
     setoid_rewrite head_reducible_decomp_ctx;
      [|done| eexists; apply head_step_support_equiv_rel; unshelve apply RandTapeEmptyS; first exact (Z.to_nat z); eauto using Fin.F1].
    apply dmap_pos. eexists. split; last first.
    - apply head_step_support_equiv_rel. unshelve apply RandTapeEmptyS; first exact (Z.to_nat z); eauto using Fin.F1.
    - done. }
  setoid_rewrite semantics.fill_dmap; eauto.
  iIntros (e2' σ2' ([? ? ]&?&Hs)%dmap_pos).
  simplify_eq/=.
  setoid_rewrite head_prim_step_eq in Hs. 2 : { eexists. apply head_step_support_equiv_rel. unshelve apply RandTapeEmptyS; eauto using Fin.F1. }
  inv_head_step.
  iApply spec_coupl_ret.
  iMod (spec_update_prog (fill K #_) with "Hs Hj") as "[$ Hj]".
  iFrame. iModIntro.
  iMod "Hclose" as "_"; iModIntro.
  iApply ("Hwp" with "[Hα Hj]");
   first by iFrame; auto.
  iPureIntro.
  pose proof (fin_to_nat_lt x); apply le_INR; lia.
Qed.


(** This is just a wrapper for tp_rand that works with nats
    TODO: Make into tactic *)
(* Lemma wp_rand_tape_r N z E e K α Φ n ns :
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
   Qed. *)


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
  iApply spec_coupl_step.
   { eexists. simpl. unfold semantics.prim_step. 
     setoid_rewrite head_reducible_decomp_ctx;
      [|done| eexists; apply head_step_support_equiv_rel; unshelve eapply RandTapeOtherS; first exact (Z.to_nat z); eauto using Fin.F1].
    apply dmap_pos. eexists. split; last first.
    - apply head_step_support_equiv_rel. unshelve eapply RandTapeOtherS; first exact (Z.to_nat z); eauto using Fin.F1.
    - done. }
  setoid_rewrite semantics.fill_dmap; eauto.
  iIntros (e2' σ2' ([? ? ]&?&Hs)%dmap_pos).
  simplify_eq/=.
  setoid_rewrite head_prim_step_eq in Hs.
  2: { eexists; apply head_step_support_equiv_rel; unshelve eapply RandTapeOtherS; first exact (Z.to_nat z); eauto using Fin.F1. }
  inv_head_step.
  iApply spec_coupl_ret.
  iMod (spec_update_prog (fill K #_) with "Hs Hj") as "[$ Hj]".
  iFrame. iModIntro.
  iMod "Hclose" as "_"; iModIntro.
  iApply ("Hwp" with "[-]"); first by iFrame.
  iPureIntro.
  pose proof (fin_to_nat_lt x); apply le_INR; lia.
Qed.

(** Effect allocation *)

Global Instance is_label_timeless ℓ dq : Timeless (is_label ℓ dq).
Proof. apply _. Qed.

Global Instance is_label_fractional ℓ : Fractional (λ q, is_label ℓ (DfracOwn q))%I.
Proof. apply _. Qed.

Global Instance is_label_as_fractional ℓ q :
  AsFractional (is_label ℓ (DfracOwn q)) (λ q, is_label ℓ (DfracOwn q))%I q.
Proof. apply _. Qed.

Global Instance is_label_persistent ℓ  : Persistent (is_label ℓ DfracDiscarded).
Proof. apply _. Qed.

Global Instance is_label_combine_sep_gives ℓ dq1 dq2 :
  CombineSepGives (is_label ℓ dq1)  (is_label ℓ dq2) ⌜ ✓ (dq1 ⋅ dq2) ⌝.
Proof.
  rewrite /CombineSepGives. iIntros "[H1 H2]".
  iCombine "H1 H2" gives %[? _]. eauto.
Qed.

Lemma is_label_combine ℓ dq1 dq2 :
  is_label ℓ dq1 -∗ is_label ℓ dq2 -∗ is_label ℓ (dq1 ⋅ dq2).
Proof.
  iIntros "Hl1 Hl2". by iCombine "Hl1 Hl2" as "$".
Qed.

Global Instance is_label_combine_as ℓ dq1 dq2 :
  CombineSepAs (is_label ℓ dq1) (is_label ℓ dq2) (is_label ℓ (dq1 ⋅ dq2)) | 60.
Proof.
  rewrite /CombineSepAs. iIntros "[H1 H2]".
  iDestruct (is_label_combine with "H1 H2") as "$".
Qed.

Lemma is_label_valid ℓ dq : is_label ℓ dq -∗ ⌜ ✓ dq ⌝.
Proof. apply ghost_map_elem_valid. Qed.

Lemma is_label_valid_2 ℓ dq1 dq2 :
  is_label ℓ dq1 -∗ is_label ℓ dq2 -∗ ⌜ ✓ (dq1 ⋅ dq2) ⌝.
Proof. iIntros "H1 H2". by iCombine "H1 H2" gives %?. Qed.

Lemma is_label_frac_ne ℓ1 ℓ2 dq1 dq2 :
  ¬ ✓(dq1 ⋅ dq2) → is_label ℓ1 dq1 -∗ is_label ℓ2 dq2 -∗ ⌜ ℓ1 ≠ ℓ2 ⌝.
Proof. apply ghost_map_elem_frac_ne. Qed.

Lemma is_label_ne ℓ1 ℓ2 dq2:
  is_label ℓ1 (DfracOwn 1) -∗ is_label ℓ2 dq2 -∗ ⌜ ℓ1 ≠ ℓ2 ⌝.
Proof. apply ghost_map_elem_ne. Qed.

Lemma is_label_persist ℓ dq : is_label ℓ dq ==∗ is_label ℓ DfracDiscarded.
Proof. apply ghost_map_elem_persist. Qed.

Global Instance frame_is_label p ℓ q1 q2 q :
  FrameFractionalQp q1 q2 q →
  Frame p
    (is_label ℓ (DfracOwn q1))
    (is_label ℓ (DfracOwn q2))
    (is_label ℓ (DfracOwn q)) | 5.
Proof. apply: frame_fractional. Qed.

Lemma wp_effect E Φ s e :
  ▷ (∀ ℓ, is_label ℓ (DfracOwn 1) ={E}=∗ WP lbl_subst s ℓ e @ E {{ Φ }}) -∗
  WP Effect s e @ E {{ Φ }}.
Proof.
  iIntros "HΦ". iApply wp_lift_head_step; first done.
  iIntros (σ1) "[Hh [Ht Hlabs]]". iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
  iSplit. { iPureIntro. exists ((lbl_subst s (next_label σ1) e), state_upd_next_label label_succ σ1 ). apply head_step_support_equiv_rel. by apply EffectS. }
  iIntros "!>" (e2 σ2 Hs).
  inv_head_step.
  iFrame.
  iMod (ghost_map_insert (next_label σ1) () with "Hlabs") as "[Hlabs Hl]".
  { by apply lookup_to_labels_None.}
  iMod "Hclose".
  iMod ("HΦ" with "[$Hl]") as "HΦ".
  iModIntro. rewrite to_labels_succ. iFrame.
Qed.

End lifting.

Global Hint Extern 0 (TCEq _ (Z.to_nat _ )) => rewrite Nat2Z.id : typeclass_instances.

(** This file proves the basic laws of the ConProbLang weakest precondition by
    applying the lifting lemmas. *)
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth excl.
From iris.base_logic.lib Require Export ghost_map.
From clutch.base_logic Require Export error_credits.
From clutch.elton Require Export weakestpre ectx_lifting pupd.
From clutch.delay_prob_lang Require Export class_instances.
From clutch.delay_prob_lang Require Import tactics lang notation urn_subst.
From iris.prelude Require Import options.

Class eltonGS Σ := HeapG {
  eltonGS_invG : invGS_gen HasNoLc Σ;
  (* CMRA for the state *)
  eltonGS_heap : ghost_mapG Σ loc val;
  eltonGS_urns : ghost_mapG Σ loc urn;
  (* ghost names for the state *)
  eltonGS_heap_name : gname;
  eltonGS_urns_name : gname;
  (* CMRA and ghost name for the error *)
  eltonGS_error :: ecGS Σ;
}.


Definition progUR : ucmra := optionUR (exclR exprO).
Definition cfgO : ofe := prodO exprO stateO.
Definition cfgUR : ucmra := optionUR (exclR cfgO).

Definition heap_auth `{eltonGS Σ} :=
  @ghost_map_auth _ _ _ _ _ eltonGS_heap eltonGS_heap_name.
Definition urns_auth `{eltonGS Σ} :=
  @ghost_map_auth _ _ _ _ _ eltonGS_urns eltonGS_urns_name.


Global Instance eltonGS_eltonWpGS `{!eltonGS Σ} : eltonWpGS d_prob_lang Σ := {
  eltonWpGS_invGS := eltonGS_invG;
    state_interp σ := (heap_auth 1 σ.(heap) ∗ urns_auth 1 σ.(urns))%I;
    err_interp ε := (ec_supply ε);
    
}.

(** Heap *)
Notation "l ↦{ dq } v" := (@ghost_map_elem _ _ _ _ _ eltonGS_heap eltonGS_heap_name l dq v)
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Notation "l ↦□ v" := (l ↦{ DfracDiscarded } v)%I
  (at level 20, format "l  ↦□  v") : bi_scope.
Notation "l ↦{# q } v" := (l ↦{ DfracOwn q } v)%I
  (at level 20, format "l  ↦{# q }  v") : bi_scope.
Notation "l ↦ v" := (l ↦{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↦  v") : bi_scope.

(** Urns *)
Notation "l ↪{ dq } v" := (@ghost_map_elem _ _ _ _ _ eltonGS_urns eltonGS_urns_name l dq v)
  (at level 20, format "l  ↪{ dq }  v") : bi_scope.
Notation "l ↪□ v" := (l ↪{ DfracDiscarded } v)%I
  (at level 20, format "l  ↪□  v") : bi_scope.
Notation "l ↪{# q } v" := (l ↪{ DfracOwn q } v)%I
  (at level 20, format "l  ↪{# q }  v") : bi_scope.
Notation "l ↪ v" := (l ↪{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↪  v") : bi_scope.

(* (** User-level tapes *) *)
(* Definition nat_tape `{eltonGS Σ} l (N : nat) (ns : list nat) : iProp Σ := *)
(*   ∃ (fs : list (fin (S N))), ⌜fin_to_nat <$> fs = ns⌝ ∗ l ↪ (N; fs). *)

(* Notation "l ↪N ( M ; ns )" := (nat_tape l M ns)%I *)
(*   (at level 20, format "l  ↪N  ( M ;  ns )") : bi_scope. *)

(* Section tape_interface. *)
(*   Context `{!eltonGS Σ}. *)

(*   (** Helper lemmas to go back and forth between the user-level representation *)
(*       of tapes (using nat) and the backend (using fin) *) *)

(*   Lemma tapeN_to_empty l M : *)
(*     (l ↪N ( M ; [] ) -∗ l ↪ ( M ; [] )). *)
(*   Proof. *)
(*     iIntros "Hl". *)
(*     iDestruct "Hl" as (?) "(%Hmap & Hl')". *)
(*     by destruct (fmap_nil_inv _ _ Hmap). *)
(*   Qed. *)


(*   Lemma empty_to_tapeN l M : *)
(*     (l ↪ ( M ; [] ) -∗ l ↪N ( M ; [] )). *)
(*   Proof. *)
(*     iIntros "Hl". *)
(*     iExists []. auto. *)
(*   Qed. *)

(*   Lemma tapeN_tapeN_contradict l N M ns ms: *)
(*     l ↪N ( N;ns ) -∗ l↪N (M;ms) -∗ False. *)
(*   Proof. *)
(*     iIntros "(%&<-&H1) (%&<-&H2)". *)
(*     by iDestruct (ghost_map_elem_ne with "[$][$]") as "%". *)
(*   Qed. *)

(*   Lemma read_tape_head l M n ns : *)
(*     (l ↪N ( M ; n :: ns ) -∗ *)
(*       ∃ x xs, l ↪ ( M ; x :: xs ) ∗ ⌜ fin_to_nat x = n ⌝ ∗ *)
(*         ( l ↪ ( M ; xs ) -∗l ↪N ( M ; ns ) )). *)
(*   Proof. *)
(*     iIntros "Hl". *)
(*     iDestruct "Hl" as (xss) "(%Hmap & Hl')". *)
(*     destruct (fmap_cons_inv _ _ _ _ Hmap) as (x&xs&->&Hxs&->). *)
(*     iExists x, xs. *)
(*     iFrame. *)
(*     iSplit; auto. *)
(*     iIntros. *)
(*     iExists xs; auto. *)
(*   Qed. *)

(*   Lemma tapeN_lookup α N ns m:  *)
(*     tapes_auth 1 m -∗ α ↪N (N; ns) -∗ ⌜∃ ns', m!!α = Some (N; ns') /\ fin_to_nat <$> ns' = ns⌝. *)
(*   Proof. *)
(*     iIntros "? (%&%&?)". *)
(*     iDestruct (ghost_map_lookup with "[$][$]") as "%". *)
(*     iPureIntro. naive_solver. *)
(*   Qed. *)

(*   Lemma tapeN_update_append α N ns m (x : fin (S N)): *)
(*     tapes_auth 1 m -∗ α ↪N (N; fin_to_nat <$> ns) ==∗ tapes_auth 1 (<[α:=(N; ns ++ [x])]> m) ∗ α ↪N (N; (fin_to_nat <$> ns) ++ [fin_to_nat x]). *)
(*   Proof. *)
(*     iIntros "? (%&%&?)". *)
(*     iMod (ghost_map_update with "[$][$]") as "[??]". *)
(*     iFrame. *)
(*     by rewrite fmap_app. *)
(*   Qed.  *)

(*   Lemma tapeN_update_append' α N m (ns ns':list (fin (S N))): *)
(*     tapes_auth 1 m -∗ α ↪N (N; fin_to_nat <$> ns) ==∗ tapes_auth 1 (<[α:=(N; ns ++ ns')]> m) ∗ α ↪N (N; (fin_to_nat <$> ns) ++ (fin_to_nat <$> ns')). *)
(*   Proof. *)
(*     iIntros "? (%&%&?)". *)
(*     iMod (ghost_map_update with "[$][$]") as "[??]". *)
(*     iFrame. *)
(*     by rewrite fmap_app. *)
(*   Qed.  *)
  
(*   Lemma tapeN_ineq α N ns: *)
(*     α↪N (N; ns) -∗ ⌜Forall (λ n, n<=N)%nat ns⌝. *)
(*   Proof. *)
(*     iIntros "(% & <- & H)". *)
(*     iPureIntro. *)
(*     eapply Forall_impl. *)
(*     - apply fin.fin_forall_leq. *)
(*     - simpl. intros. *)
(*       lia. *)
(*   Qed. *)

(*   Lemma hocap_tapes_notin α N ns m (f:(nat*list nat)-> nat) g: *)
(*     α ↪N (N; ns) -∗ ([∗ map] α0↦t ∈ m, α0 ↪N (f t; g t)) -∗ ⌜m!!α=None ⌝. *)
(*   Proof. *)
(*     destruct (m!!α) eqn:Heqn; last by iIntros. *)
(*     iIntros "Hα Hmap". *)
(*     iDestruct (big_sepM_lookup with "[$]") as "?"; first done. *)
(*     iExFalso. *)
(*     iApply (tapeN_tapeN_contradict with "[$][$]"). *)
(*   Qed. *)
          
(*   (* *)
(*   Lemma spec_tapeN_to_empty l M : *)
(*     (l ↪ₛN ( M ; [] ) -∗ l ↪ₛ ( M ; [] )). *)
(*   Proof. *)
(*     iIntros "Hl". *)
(*     iDestruct "Hl" as (?) "(%Hmap & Hl')". *)
(*     by destruct (fmap_nil_inv _ _ Hmap). *)
(*   Qed. *)


(*   Lemma empty_to_spec_tapeN l M : *)
(*     (l ↪ₛ ( M ; [] ) -∗ l ↪ₛN ( M ; [] )). *)
(*   Proof. *)
(*     iIntros "Hl". *)
(*     iExists []. auto. *)
(*   Qed. *)

(*   Lemma read_spec_tape_head l M n ns : *)
(*     (l ↪ₛN ( M ; n :: ns ) -∗ *)
(*       ∃ x xs, l ↪ₛ ( M ; x :: xs ) ∗ ⌜ fin_to_nat x = n ⌝ ∗ *)
(*               ( l ↪ₛ ( M ; xs ) -∗l ↪ₛN ( M ; ns ) )). *)
(*   Proof. *)
(*     iIntros "Hl". *)
(*     iDestruct "Hl" as (xss) "(%Hmap & Hl')". *)
(*     destruct (fmap_cons_inv _ _ _ _ Hmap) as (x&xs&->&Hxs&->). *)
(*     iExists x, xs. *)
(*     iFrame. *)
(*     iSplit; auto. *)
(*     iIntros. *)
(*     iExists xs; auto. *)
(*   Qed. *)
(* *) *)

(* End tape_interface. *)



Section lifting.
Context `{!eltonGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : val → iProp Σ.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types l : loc.

Lemma pupd_epsilon_err E:
  ⊢ pupd E E (∃ ε, ⌜(0<ε)%R⌝ ∗ ↯ ε)%I.
Proof.
  rewrite pupd_unseal/pupd_def.
  iIntros (?? ε) "(Hstate& Herr)".
  iApply fupd_mask_intro; first set_solver.
  iIntros "Hclose".
  iApply state_step_coupl_ampl.
  iIntros (ε' ?).
  destruct (decide (ε'<1)%R); last first.
  { iApply state_step_coupl_ret_err_ge_1.
    simpl in *. lra.
  }
  iApply state_step_coupl_ret.
  assert (ε<=ε')%R as H'; first (simpl; lra).
  pose (diff :=((ε' - ε) H')%NNR).
  replace (ε') with (ε + diff)%NNR; last (apply nnreal_ext; rewrite /diff; simpl; lra).
  iMod (ec_supply_increase _ diff with "[$]") as "[??]".
  { rewrite /diff. simpl. simpl in *. lra. }
  iFrame. iMod "Hclose". iPureIntro.
  rewrite /diff.
  simpl.
  split; first done.
  lra.
Qed.

Lemma pupd_resolve_urn s ε (ε2 : _ -> nonnegreal) l E:
  s ≠ ∅ ->
 (SeriesC (λ x, if bool_decide (x ∈ elements s) then ε2 x else 0)/ size s <= ε)%R ->
  (exists r, forall ρ, (ε2 ρ <= r)%R) ->
  ↯ ε -∗ l ↪ urn_unif s -∗
  pupd E E (∃ x,
        ↯ (ε2 x) ∗ l↪ urn_unif {[x]} ∗ ⌜x ∈ s⌝
    )%I.
Proof.
  rewrite pupd_unseal/pupd_def.
  iIntros (Hs Hineq [r Hbound]) "Herr Hl".
  iIntros (?[] ε') "([Hs Hu]& Herr')".
  iDestruct (ghost_map_lookup with "Hu [$]") as %?.
  iDestruct (ec_supply_ec_inv with "[$][$]") as %(x&x'& -> & He).
  iApply fupd_mask_intro; first set_solver.
  iIntros "Hclose".
  iApply state_step_coupl_rec_complete_split.
  pose (ε2' := λ x,  (ε2 x + x')%NNR ).
  assert (∀ x, 0<=ε2' x)%R as Hnnr; first (intros; apply cond_nonneg). 
  iExists _,_, (λ x, mknonnegreal _ (Hnnr x)).
  iSplit; first done.
  iSplit; first done.
  iSplit.
  { iPureIntro.
    exists ( (r+x'))%R.
    simpl. intros.
    rewrite /ε2'.
    real_solver.
  }
  assert (size s > 0)%R.
  { apply Rlt_gt.
    apply lt_0_INR.
    destruct (size _) eqn :Hn; last lia.
    exfalso.
    apply Hs.
    rewrite size_empty_iff in Hn.
    set_solver.
  }
  iSplit; first iPureIntro.
  { simpl.
    rewrite Rcomplements.Rle_div_l; last lra.
    rewrite Rcomplements.Rle_div_l in Hineq; last lra.
    rewrite Rmult_plus_distr_r.
    rewrite He.
    etrans; last (apply Rplus_le_compat_r; exact).
    replace (size _) with (length (elements s)) by done.
    rewrite -SeriesC_list_2; last apply NoDup_elements.
    right.
    rewrite -SeriesC_plus; [|apply ex_seriesC_list..].
    apply SeriesC_ext.
    intros.
    case_bool_decide; simpl; lra.
  }
  iIntros (x0 Hx0).
  iMod (ec_supply_decrease with "Herr' Herr") as (????) "Hε2".
  iModIntro.
  destruct (Rlt_decision ((ε2 (x0)) + nonneg x' )%R 1%R) as [Hdec|Hdec]; last first.
  { apply Rnot_lt_ge, Rge_le in Hdec.
    by iApply state_step_coupl_ret_err_ge_1.
  }
  iApply state_step_coupl_ret.
  iMod (ghost_map_update with "Hu Hl") as "[$ Hl]".
  rename select ((_+_)%NNR = _) into H1. apply (f_equal nonneg) in H1.
  unshelve iMod (ec_supply_increase _ (mknonnegreal (ε2 (x0)) _) with "[Hε2]") as "[Hε2 Hcr]"; first done.
  { simpl. done. }
  { simpl in *. lra. }
  { iApply ec_supply_eq; [|done]. simplify_eq. lra. }
  iFrame.
  subst.
  iMod "Hclose".
  iModIntro. iSplit; last done.
  iApply ec_supply_eq; [|done]. simplify_eq. simpl. simpl in *. lra.
Qed.

(** Recursive functions: we do not use this lemmas as it is easier to use Löb *)
(* induction directly, but this demonstrates that we can state the expected *)
(* reasoning principle for recursive functions, without any visible ▷. *)

Lemma wp_value_promotion v v' P Φ s E:
  is_simple_val v' = true ->
  (rupd (λ x, x=v') P v)-∗
    (P -∗ WP (Val v') @ s; E {{ Φ }}) -∗
    WP (Val v) @ s; E {{ Φ }}.
Proof.
  iIntros (H) "H1 H2".
  iApply state_step_coupl_wp.
  iIntros (??) "[??]".
  iApply fupd_mask_intro; first set_solver.
  iIntros "Hclose".
  iApply state_step_coupl_value_promote.
  iExists [], v, v', P.
  simpl.
  repeat iSplit; last iFrame; first done.
  { rewrite rupd_unseal/rupd_def.
    iDestruct ("H1" with "[$]") as  "[%K ?]".
    iPureIntro.
    intros ? H'.
    apply K in H'. by destruct!/=.
  }
  iFrame.
  iIntros "HP".
  iApply state_step_coupl_ret.
  iFrame.
  iModIntro.
  iMod "Hclose".
  by iApply "H2".
Qed. 

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
      rewrite length_replicate in H1.
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

(* Should also implement a version where the argument may be a thunk *)
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
  rename select (fin _) into x.
  rename select (_>0)%R into Hx.
  epose proof (urn_subst_equal_epsilon_unique _ _ z _ _) as H'.
  rewrite H' in x Hx *.
  iFrame.
  by iApply ("HΦ" $! x) .
  Unshelve.
  4:{ done. }
  done. 
Qed.

Lemma wp_drand_thunk (N : nat) (z : Z) v E s P :
  TCEq N (Z.to_nat z) →
  {{{ (rupd (λ v,v= #N) P v)}}} drand v @ s; E {{{ l, RET LitV (LitLbl l); P ∗ l ↪ (urn_unif $ list_to_set (Z.of_nat <$> (seq 0 (S N)))) }}}.
Proof.
  iIntros (-> Φ) "Hrupd HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  rewrite rupd_unseal/rupd_def.
  iIntros (σ1) "Hσ !#".
  iDestruct ("Hrupd" with "[$]") as "[% [HP [Hs Hu]]]".
  iSplit.
  { iPureIntro.
    econstructor.
    simpl.
    destruct (urns_f_distr_witness (urns σ1)) as [f Hf].
    apply H in Hf as H'.
    destruct H' as [? [H' ->]].
    case_match; simpl in *; simplify_eq; repeat setoid_rewrite bind_Some in H'; destruct!/=; last first.
    case_match; last first.
    - exfalso.
      setoid_rewrite bind_Some in H.
      rename select (¬ _) into Hcontra.
      apply Hcontra.
      eexists _.
      intros ? H2.
      apply H in H2.
      by destruct!/=.
    - erewrite urn_subst_equal_epsilon_unique; first solve_distr.
      intros ? H2.
      apply H in H2.
      setoid_rewrite bind_Some in H2. by destruct!/=.
  }
  iIntros "!>" (e2 σ2 Hs).
  inv_head_step.
  iFrame.
  iMod (ghost_map_insert (fresh_loc σ1.(urns)) with "Hu") as "[$ Hl]".
  { apply not_elem_of_dom, fresh_loc_is_fresh. }
  iModIntro.
  iApply "HΦ".
  iFrame.
  rewrite (urn_subst_equal_epsilon_unique _ _ (Z.to_nat z) _ _); last first.
  { intros ? H2.
    apply H in H2.
    setoid_rewrite bind_Some in H2. by destruct!/=.
  }
  rewrite Nat2Z.id.
  rewrite Nat.add_1_r. iFrame. 
Qed.

(* (** Tapes  *) *)
(* Lemma wp_alloc_tape N z E s : *)
(*   TCEq N (Z.to_nat z) → *)
(*   {{{ True }}} alloc #z @ s; E {{{ α, RET #lbl:α; α ↪N (N; []) }}}. *)
(* Proof. *)
(*   iIntros (-> Φ) "_ HΦ". *)
(*   iApply wp_lift_atomic_head_step; [done|]. *)
(*   iIntros (σ1) "(Hh & Ht) !# /=". *)
(*   solve_red. *)
(*   iIntros "!>" (e2 σ2 efs Hs); inv_head_step. *)
(*   iMod (ghost_map_insert (fresh_loc σ1.(tapes)) with "Ht") as "[$ Hl]". *)
(*   { apply not_elem_of_dom, fresh_loc_is_fresh. } *)
(*   iFrame. iModIntro. *)
(*   iSplitL; last done. *)
(*   iApply "HΦ". *)
(*   iExists []; auto. *)
(* Qed. *)

(* Lemma wp_rand_tape N α n ns z E s : *)
(*   TCEq N (Z.to_nat z) → *)
(*   {{{ ▷ α ↪N (N; n :: ns) }}} *)
(*     rand(#lbl:α) #z @ s; E *)
(*   {{{ RET #(LitInt n); α ↪N (N; ns) ∗ ⌜n <= N⌝ }}}. *)
(* Proof. *)
(*   iIntros (-> Φ) ">Hl HΦ". *)
(*   iApply wp_lift_atomic_head_step; [done|]. *)
(*   iIntros (σ1) "(Hh & Ht) !#". *)
(*   iDestruct (read_tape_head with "Hl") as (x xs) "(Hl&<-&Hret)". *)
(*   iDestruct (ghost_map_lookup with "Ht Hl") as %?. *)
(*   solve_red. *)
(*   iIntros "!>" (e2 σ2 efs Hs). *)
(*   inv_head_step. *)
(*   iMod (ghost_map_update with "Ht Hl") as "[$ Hl]". *)
(*   iFrame. iModIntro. *)
(*   iSplitL; last done. *)
(*   iApply "HΦ". *)
(*   iSplit; first by iApply "Hret". *)
(*   iPureIntro. *)
(*   pose proof (fin_to_nat_lt x); lia. *)
(* Qed. *)

(* Lemma wp_rand_tape_empty N z α E s : *)
(*   TCEq N (Z.to_nat z) → *)
(*   {{{ ▷ α ↪N (N; []) }}} *)
(*     rand(#lbl:α) #z @ s; E *)
(*   {{{ (n : nat), RET #(LitInt n); α ↪N (N; []) ∗ ⌜n <= N⌝ }}}. *)
(* Proof. *)
(*   iIntros (-> Φ) ">Hl HΦ". *)
(*   iPoseProof (tapeN_to_empty with "Hl") as "Hl". *)
(*   iApply wp_lift_atomic_head_step; [done|]. *)
(*   iIntros (σ1) "(Hh & Ht) !#". *)
(*   iDestruct (ghost_map_lookup with "Ht Hl") as %?. *)
(*   solve_red. *)
(*   iIntros "!>" (e2 σ2 efs Hs). *)
(*   inv_head_step. *)
(*   iFrame. *)
(*   iModIntro. iSplitL; last done. *)
(*   iApply ("HΦ" with "[$Hl]"). *)
(*   iSplit; auto. *)
(*   iPureIntro. *)
(*   pose proof (fin_to_nat_lt x); lia. *)
(* Qed. *)

(* Lemma wp_rand_tape_wrong_bound N M z α E ns s : *)
(*   TCEq N (Z.to_nat z) → *)
(*   N ≠ M → *)
(*   {{{ ▷ α ↪N (M; ns) }}} *)
(*     rand(#lbl:α) #z @ s; E *)
(*   {{{ (n : nat), RET #(LitInt n); α ↪N (M; ns) ∗ ⌜n <= N⌝ }}}. *)
(* Proof. *)
(*   iIntros (-> ? Φ) ">Hl HΦ". *)
(*   iApply wp_lift_atomic_head_step; [done|]. *)
(*   iIntros (σ1) "(Hh & Ht) !#". *)
(*   iDestruct "Hl" as (?) "(?&Hl)". *)
(*   iDestruct (ghost_map_lookup with "Ht Hl") as %?. *)
(*   solve_red. *)
(*   iIntros "!>" (e2 σ2 efs Hs). *)
(*   inv_head_step. *)
(*   iFrame. *)
(*   iModIntro. *)
(*   iSplitL; last done. *)
(*   iApply ("HΦ"). *)
(*   iFrame. *)
(*   iPureIntro. *)
(*   pose proof (fin_to_nat_lt x); lia. *)
(* Qed. *)

(* Lemma wp_fork s E e Φ : *)
(*   ▷ WP e @ s; ⊤ {{ _, True }} -∗ ▷ Φ (LitV LitUnit) -∗ WP Fork e @ s; E {{ Φ }}. *)
(* Proof. *)
(*   iIntros "He HΦ". iApply wp_lift_atomic_head_step; [done|]. *)
(*   iIntros (σ1) "(Hh & Ht) !#". solve_red. *)
(*   iIntros "!>" (e2 σ2 efs Hs). *)
(*   inv_head_step. by iFrame.  *)
(* Qed. *)
  
End lifting.

Global Hint Extern 0 (TCEq _ (Z.to_nat _ )) => rewrite Nat2Z.id : typeclass_instances.

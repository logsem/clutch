(** This file proves the basic laws of the ProbLang weakest precondition by
    applying the lifting lemmas. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export ghost_map.
From clutch.base_logic Require Export error_credits.
From clutch.prelude Require Import tactics.
From clutch.foxtrot Require Export weakestpre pupd ectx_lifting.
From clutch.foxtrot Require Import oscheduler full_info.
From clutch.con_prob_lang Require Export class_instances.
From clutch.con_prob_lang Require Import tactics lang notation metatheory erasure.
From clutch.con_prob_lang.spec Require Export spec_ra.
From iris.prelude Require Import options.

Class foxtrotGS Σ := HeapG {
  foxtrotGS_invG : invGS_gen HasNoLc Σ;
  (* CMRA for the state *)
  foxtrotGS_heap : ghost_mapG Σ loc val;
  foxtrotGS_tapes : ghost_mapG Σ loc tape;
  (* ghost names for the state *)
  foxtrotGS_heap_name : gname;
  foxtrotGS_tapes_name : gname;
  (* CMRA and ghost name for the spec *)
  foxtrotGS_spec :: specG_con_prob_lang Σ;
  (* CMRA and ghost name for the error *)
  foxtrotGS_error :: ecGS Σ;
}.

Class foxtrotGpreS Σ := FoxtrotGpreS {
  foxtrotGpreS_iris  :: invGpreS Σ;
  foxtrotGpreS_heap  :: ghost_mapG Σ loc val;
  foxtrotGpreS_tapes :: ghost_mapG Σ loc tape;
  foxtrotGpreS_spec :: specGpreS Σ;
  foxtrotGpreS_err   :: ecGpreS Σ;
}.

Definition foxtrotΣ : gFunctors :=
  #[invΣ;
    ghost_mapΣ loc val;
    ghost_mapΣ loc tape;
    specΣ;
    ecΣ].
Global Instance subG_foxtrotGPreS {Σ} : subG foxtrotΣ Σ → foxtrotGpreS Σ.
Proof. solve_inG. Qed.

Definition heap_auth `{foxtrotGS Σ} :=
  @ghost_map_auth _ _ _ _ _ foxtrotGS_heap foxtrotGS_heap_name.
Definition tapes_auth `{foxtrotGS Σ} :=
  @ghost_map_auth _ _ _ _ _ foxtrotGS_tapes foxtrotGS_tapes_name.

Global Instance foxtrotGS_irisGS `{!foxtrotGS Σ} : foxtrotWpGS con_prob_lang Σ := {
  foxtrotWpGS_invGS := foxtrotGS_invG;
  state_interp σ := (heap_auth 1 σ.(heap) ∗ tapes_auth 1 σ.(tapes))%I;
  spec_interp ρ := spec_auth ρ;
  fork_post v :=  True%I;
  err_interp := ec_supply;
}.

(** Heap *)
Notation "l ↦{ dq } v" := (@ghost_map_elem _ _ _ _ _ foxtrotGS_heap foxtrotGS_heap_name l dq v)
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Notation "l ↦□ v" := (l ↦{ DfracDiscarded } v)%I
  (at level 20, format "l  ↦□  v") : bi_scope.
Notation "l ↦{# q } v" := (l ↦{ DfracOwn q } v)%I
  (at level 20, format "l  ↦{# q }  v") : bi_scope.
Notation "l ↦ v" := (l ↦{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↦  v") : bi_scope.

(** Tapes *)
Notation "l ↪{ dq } v" := (@ghost_map_elem _ _ tape _ _ foxtrotGS_tapes foxtrotGS_tapes_name l dq v)
  (at level 20, format "l  ↪{ dq }  v") : bi_scope.
Notation "l ↪□ v" := (l ↪{ DfracDiscarded } v)%I
  (at level 20, format "l  ↪□  v") : bi_scope.
Notation "l ↪{# q } v" := (l ↪{ DfracOwn q } v)%I
  (at level 20, format "l  ↪{# q }  v") : bi_scope.
Notation "l ↪ v" := (l ↪{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↪  v") : bi_scope.

(** User-level tapes *)
Definition nat_tape `{foxtrotGS Σ} l (N : nat) (ns : list nat) : iProp Σ :=
  ∃ (fs : list (fin (S N))), ⌜fin_to_nat <$> fs = ns⌝ ∗ l ↪ (N; fs).

Notation "l ↪N ( M ; ns )" := (nat_tape l M ns)%I
  (at level 20, format "l  ↪N  ( M ;  ns )") : bi_scope.

Section tape_interface.
  Context `{!foxtrotGS Σ}.

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
  Context `{!foxtrotGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ Ψ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types v : val.
  Implicit Types l : loc.

  Lemma pupd_epsilon_err E:
    ⊢ pupd E E (∃ ε, ⌜(0<ε)%R⌝ ∗ ↯ ε)%I.
  Proof.
    rewrite pupd_unseal/pupd_def.
    iIntros (?? ε) "(Hstate&?& Herr)".
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose".
    iApply spec_coupl_amplify.
    iIntros (ε' ?).
    destruct (decide (ε'<1)%R); last first.
    { iApply spec_coupl_ret_err_ge_1.
      simpl in *. lra.
    }
    iApply spec_coupl_ret.
    assert (ε<=ε')%R as H'; first (simpl; lra).
    pose (diff :=((ε' - ε) H')%NNR).
    replace (ε') with (ε + diff)%NNR; last (apply nnreal_ext; rewrite /diff; simpl; lra).
    iMod (ec_supply_increase _ diff with "[$]") as "[??]".
    { rewrite /diff. simpl. simpl in *. lra. }
    iFrame. iMod "Hclose". iPureIntro.
    rewrite /diff.
    simpl.
    lra.
  Qed.

  Lemma pupd_presample (N : nat) E ns α:
    α ↪N (N;ns) ⊢
    pupd E E (∃ (n:nat), α↪N (N; ns ++ [n]) ∗ ⌜(n<=N)%nat⌝).
  Proof. 
    rewrite pupd_unseal/pupd_def.
    iIntros "Hα" (σ ρ1 ε1) "([? Ht]&?&?)".
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose".
    iDestruct "Hα" as "(%&%&?)".
    iDestruct (ghost_map_lookup with "Ht [$]") as %?.
    iApply spec_coupl_rec.
    iExists _, (state_step σ α), (full_info_cons_osch (λ ρ, dmap (λ n, length (ρ.1) + fin_to_nat n)%nat (dunifP N)) (λ _, full_info_inhabitant)), 0%NNR, (λ _, ε1), ε1.
    repeat iSplit.
    - iPureIntro. by eapply state_step_sch_erasable.
    - done.
    - iPureIntro. rewrite Rplus_0_l.
      rewrite Expval_const; last done.
      trans (ε1 * 1)%R; last (simpl; lra).
      by apply Rmult_le_compat.
    - rewrite full_info_cons_osch_lim_exec/state_step.
      rewrite bool_decide_eq_true_2; last first.
      { rewrite elem_of_dom. naive_solver. }
      setoid_rewrite lookup_total_correct; last done.
      Local Opaque full_info_lift_osch.
      simpl.
      replace 0%R with (0+0)%R by lra.
      rewrite /dmap.
      iPureIntro.
      eapply ARcoupl_dbind; [lra|lra| |]; last first.
      { rewrite -{1}(dret_id_right (dunifP _)).
        replace 0%R with (0+0)%R by lra.
        eapply ARcoupl_dbind; [lra|lra|..]; last first.
        - apply ARcoupl_eq.
        - instantiate(1:=(λ x y, y=length ρ1.1 + x)). intros. subst.
          by apply ARcoupl_dret.
      }
      simpl. intros; subst.
      rewrite -{1}(dret_id_right (dret _)).
      replace 0%R with (0+0)%R by lra.
      eapply ARcoupl_dbind; [lra|lra|..]; last first.
      + rewrite /step'.
        instantiate (1:= λ x y, x=(state_upd_tapes <[α:=(N; fs ++ [a])]> σ)/\y=ρ1).
        destruct ρ1.
        simpl.
        rewrite lookup_ge_None_2; last lia.
        by apply ARcoupl_dret.
      + simpl.
        intros. destruct!/=.
        rewrite full_info_lift_osch_lim_exec full_info_inhabitant_lim_exec.
        rewrite dmap_dret. rewrite app_nil_r.
        instantiate (1 := λ x y, exists (a:fin (S N)), x = (state_upd_tapes <[α:=(N; fs ++ [a])]> σ)
                                                  /\ y = ([(cfg_to_cfg' ρ1, length ρ1.1 + a)], ρ1)).
        apply ARcoupl_dret; naive_solver.
    - iPureIntro. intros ?????[a?] [a' ?]. destruct!/=.
      assert (a=a') as ->.
      { apply fin_to_nat_inj. lia. }
      naive_solver.
    - simpl.
      iIntros (??? (x&?&?)).
      simplify_eq.
      iApply spec_coupl_ret.
      iMod (ghost_map_update with "Ht [$]") as "(?&?)".
      iModIntro.
      iMod "Hclose".
      iModIntro.
      iFrame. iPureIntro.
      simpl.
      eexists _.
      rewrite fmap_app. split; first f_equal.
      pose proof fin_to_nat_lt x. lia.
  Qed. 

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
    iIntros "!> /=" (e2 σ2 efs Hs); inv_head_step.
    iMod ((ghost_map_insert (fresh_loc σ1.(heap)) v) with "Hh") as "[? Hl]".
    { apply not_elem_of_dom, fresh_loc_is_fresh. }
    iFrame.
    rewrite map_union_empty -insert_union_singleton_l.
    iFrame.
    iIntros "!>". iSplitL; last done. by iApply "HΦ".
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
    iFrame. iModIntro. iSplit; last done. by iApply "HΦ".
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
    {{{ True }}} rand #z @ s; E {{{ (n : nat), RET #n; ⌜n <= N⌝ }}}.
  Proof.
    iIntros (-> Φ) "_ HΦ".
    iApply wp_lift_atomic_head_step; [done|].
    iIntros (σ1) "Hσ !#".
    solve_red.
    iIntros "!>" (e2 σ2 efs Hs).
    inv_head_step.
    iFrame.
    iSplitL; last done.
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
    iModIntro. iSplit; last done. iApply ("HΦ" with "[$Hl]").
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

  (** Concurrency *)
  
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


  (** spec *)
  Lemma pupd_step_pure (P: Prop) n e e' j K E:
    P →
    PureExec P n e e' →
    j ⤇ fill K e ⊢ pupd E E (j ⤇ fill K e').
  Proof.
    intros H1 H2.
    apply H2 in H1.
    clear H2.
    revert e e' H1.
    iInduction n as [|n] "IH".
    - simpl. iIntros (?? H). inversion H; subst.
      iIntros. 
      by iFrame.
    - iIntros (?? H). inversion H as [|? ??? H']. subst.
      iIntros "H".
      iAssert (pupd E E (j⤇ fill K y))%I with "[H]" as ">H"; last by iApply "IH".
      rewrite pupd_unseal/pupd_def.
      iIntros (?[??]?) "(?&?&?)".
      iDestruct (spec_auth_prog_agree with "[$][$]") as "%".
      iApply fupd_mask_intro; first set_solver.
      iIntros "Hclose".
      iApply (spec_coupl_step_r_adv _ _ _ _ (_,_) with "[-]").
      + eapply pure_step_safe. eapply pure_step_ctx; last done.
        apply con_ectx_lang_ctx.
      + done.
      + instantiate (1:=(λ _, ε1)%NNR).
        by eexists ε1%R.
      + right.
        rewrite Expval_const; last done.
        instantiate (1:=0%NNR).
        erewrite Rplus_0_l.
        rewrite prim_step_mass; last first.
        { eapply pure_step_safe. eapply pure_step_ctx; last done.
          apply _. }
        by rewrite Rmult_1_r.
      + eapply pure_step_det in H' as H''.
        setoid_rewrite fill_prim_step_dbind; last first.
        { simpl. erewrite val_stuck; try done. erewrite H''. lra. }
        instantiate (2:= λ '(e', σ', efs), e' = fill K y /\ σ' = s /\ efs = []).
        simpl in *.
        apply pmf_1_eq_dret in H''. rewrite H''.
        rewrite dmap_dret.
        apply pgl_dret. naive_solver.
      + iIntros (???) "[(%&%&%) %K']".
        subst.
        iMod (spec_update_prog with "[$][$]") as "[??]".
        iModIntro.
        rewrite app_nil_r. simpl.
        iApply spec_coupl_ret. iFrame. by iMod "Hclose".
        Unshelve. done.
  Qed.
  
  (** Alloc, load, and store *)
  Lemma pupd_alloc E K e v j :
    IntoVal e v →
    j ⤇ fill K (ref e) ⊢ pupd E E (∃ l, j ⤇ fill K (#l) ∗ l ↦ₛ v).
  Proof.
    iIntros (<-) "HK".
    rewrite pupd_unseal/pupd_def.
    iIntros (σ1 [] ε1) "(H1 & H2 & H3)".
    iDestruct (spec_auth_prog_agree with "[$][$]") as "%".
    iMod (spec_auth_heap_alloc with "[$]") as "[Hs Hl]".
    iMod (spec_update_prog with "[$][$]") as "[HK Hs]".
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose".
    iApply spec_coupl_step_r; [|done|..].
    - apply reducible_fill. apply head_prim_reducible. solve_red.
    - instantiate (2:=0%NNR). instantiate (1:= ε1). simpl.
      lra.
    - simpl.
      rewrite fill_dmap //=.
      rewrite head_prim_step_eq//.
      simpl.
      rewrite dmap_dret/=.
      apply pgl_dret.
      rewrite /prim_step/=.
      instantiate (2:= λ x, x = (fill K #(fresh_loc (heap s)), state_upd_heap_N (fresh_loc (heap s)) (Z.to_nat 1) v s, [])).
      naive_solver.
    - iIntros (???) "%".
      destruct!/=.
      iApply spec_coupl_ret.
      iModIntro.
      iMod "Hclose".
      iFrame. rewrite state_upd_heap_singleton.
      rewrite app_nil_r. by iFrame.
  Qed.
  
  Lemma pupd_load E K l q v j:
    j ⤇ fill K (!#l) ∗ l ↦ₛ{q} v
    ⊢ pupd E E (j ⤇ fill K (of_val v) ∗ l ↦ₛ{q} v).
  Proof.
    iIntros "[HK HL]".
    rewrite pupd_unseal/pupd_def.
    iIntros (σ1 [] ε1) "(H1 & H2 & H3)".
    iDestruct (spec_auth_prog_agree with "[$][$]") as "%".
    iDestruct (spec_auth_lookup_heap with "[$][$]") as "%".
    iMod (spec_update_prog with "[$][$]") as "[HK Hs]".
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose".
    iApply spec_coupl_step_r; [|done|..].
    - apply reducible_fill. apply head_prim_reducible. solve_red.
    - instantiate (2:=0%NNR). instantiate (1:= ε1). simpl.
      lra.
    - simpl.
      rewrite fill_dmap //=.
      rewrite head_prim_step_eq//.
      simpl.
      case_match; last done.
      rewrite dmap_dret/=.
      apply pgl_dret.
      rewrite /prim_step/=.
      simplify_eq.
      instantiate (2:= λ x, x =(fill K v, s, [])).
      naive_solver.
    - iIntros (???) "%".
      destruct!/=.
      iApply spec_coupl_ret.
      iModIntro.
      iMod "Hclose".
      iFrame. 
      rewrite app_nil_r. by iFrame.
  Qed.

  Lemma pupd_store E K l v' e v j:
    IntoVal e v →
    j ⤇ fill K (#l <- e) ∗ l ↦ₛ v'
    ⊢ pupd E E (j ⤇ fill K #() ∗ l ↦ₛ v).
  Proof.
    iIntros (<-) "[HK HL]".
    rewrite pupd_unseal/pupd_def.
    iIntros (σ1 [] ε1) "(H1 & H2 & H3)".
    iDestruct (spec_auth_prog_agree with "[$][$]") as "%".
    iDestruct (spec_auth_lookup_heap with "[$][$]") as "%".
    iMod (spec_auth_update_heap with "[$][$]") as "[??]".
    iMod (spec_update_prog with "[$][$]") as "[HK Hs]".
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose".
    iApply spec_coupl_step_r; [|done|..].
    - apply reducible_fill. apply head_prim_reducible. solve_red.
    - instantiate (2:=0%NNR). instantiate (1:= ε1). simpl.
      lra.
    - simpl.
      rewrite fill_dmap //=.
      rewrite head_prim_step_eq//.
      simpl.
      case_match; last done.
      rewrite dmap_dret/=.
      apply pgl_dret.
      rewrite /prim_step/=.
      simplify_eq.
      instantiate (2:= λ x, x =(fill K #(), state_upd_heap <[l:=v]> s, [])).
      naive_solver.
    - iIntros (???) "%".
      destruct!/=.
      iApply spec_coupl_ret.
      iModIntro.
      iMod "Hclose".
      iFrame. 
      rewrite app_nil_r. by iFrame.
  Qed.

  (* TODO: prove adv comp version *)
  Lemma pupd_rand j K N z E:
    TCEq N (Z.to_nat z) →
    j⤇ fill K (rand #z) -∗
    pupd E E (∃ (n:nat), j⤇ fill K #n ∗ ⌜(n<=N)%nat⌝).
  Proof.
    iIntros (->) "HK".
    rewrite pupd_unseal/pupd_def.
    iIntros (σ1 [] ε1) "(H1 & H2 & H3)".
    iDestruct (spec_auth_prog_agree with "[$][$]") as "%".
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose".
    iApply spec_coupl_step_r; [|done|..].
    - apply reducible_fill. apply head_prim_reducible. solve_red.
    - instantiate (2:=0%NNR). instantiate (1:= ε1). simpl.
      lra.
    - simpl.
      rewrite fill_dmap //=.
      rewrite head_prim_step_eq//.
      simpl.
      rewrite dmap_comp.
      rewrite /dmap.
      replace 0%R with (0+0)%R; last lra.
      eapply pgl_dbind; last first.
      + by apply pgl_trivial.
      + simpl.
        intros a ?. apply pgl_dret.
        split; last done.
        instantiate (1:= λ x, ∃ (n:nat), x =(fill K #n, s, []) /\ (n<=Z.to_nat z)%nat ).
        simpl. eexists _; split; first done.
        pose proof fin_to_nat_lt a. lia.
      + done.
      + done. 
    - simpl. iIntros (???) "%".
      destruct!/=.
      iMod (spec_update_prog with "[$][$]") as "[HK Hs]".
      iApply spec_coupl_ret.
      iModIntro.
      iMod "Hclose".
      rewrite app_nil_r.
      by iFrame.
  Qed.

  (* technically not used since presampling on the right is not allowed*)
  Lemma pupd_rand_tape j K N z E n ns α:
    TCEq N (Z.to_nat z) →
    j⤇ fill K (rand(#lbl:α) #z) -∗
    α ↪ₛN (N; n::ns) -∗
    pupd E E (j⤇ fill K #n ∗ α ↪ₛN (N; ns)).
  Proof.
    iIntros (->) "HK Htape".
    rewrite pupd_unseal/pupd_def.
    iIntros (σ1 [?[]] ε1) "(H1 & H2 & H3)".
    iDestruct (spec_auth_prog_agree with "[$][$]") as "%".
    iDestruct "H2" as "[Hb [Ha H2]]".
    simpl.
    iDestruct "Htape" as "(%&%&Htape)".
    iDestruct (ghost_map_lookup with "H2 Htape") as %H1.
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose".
    destruct fs; first simplify_eq.
    iApply spec_coupl_step_r; [|done|..].
    - apply reducible_fill. simpl. apply head_prim_reducible.
      rewrite /head_reducible.
      simpl.
      rewrite H1. case_bool_decide; last done.
      eexists _.
      rewrite dret_1_1; [lra|done].
    - instantiate (2:=0%NNR). instantiate (1:= ε1). simpl.
      lra.
    - simpl in *.
      instantiate (2 := (λ '(e', σ', efs), e' = fill K _ /\ σ' = {| heap := _ ; tapes := <[α:=(Z.to_nat z; _)]> _ |} /\ efs = [])).
      instantiate (1:= <[α:=(Z.to_nat z; _)]> _).
      rewrite fill_dmap //=.
      erewrite head_prim_step_eq; last first.
      { rewrite /head_reducible.
      simpl.
      rewrite H1. case_bool_decide; last done.
      eexists _.
      rewrite dret_1_1; [lra|done]. }
      simpl.
      rewrite H1. case_bool_decide; last done.
      rewrite dmap_dret.
      apply pgl_dret.
      repeat case_match. simpl in *. by simplify_eq. 
    - simpl. iIntros (???) "%".
      destruct!/=.
      iMod (ghost_map_update with "[$H2][$Htape]") as "[H2 Htape]".
      iMod (spec_update_prog with "[H2 Ha Hb][$HK]") as "[HK Hs]".
      { iSplitL "Hb"; first done.
        instantiate (1:= {| heap := _; tapes := _ |}).
        simpl.
        iFrame. }
      iApply spec_coupl_ret.
      iModIntro.
      iMod "Hclose".
      iFrame. 
      rewrite app_nil_r.
      by iFrame.
  Qed. 


  Lemma pupd_fork E K e j:
    j ⤇ fill K (Fork e)
    ⊢ pupd E E (j ⤇ fill K #() ∗ ∃ k, k ⤇ e).
  Proof.
    iIntros "HK".
    rewrite pupd_unseal/pupd_def.
    iIntros (σ1 [] ε1) "(H1 & H2 & H3)".
    iDestruct (spec_auth_prog_agree with "[$][$]") as "%".
    iMod (spec_update_prog with "[$][$]") as "[HK Hs]".
    iMod (spec_fork_prog with "[$]") as "[??]".    
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose".
    iApply spec_coupl_step_r; [|done|..].
    - apply reducible_fill. apply head_prim_reducible. solve_red.
    - instantiate (2:=0%NNR). instantiate (1:= ε1). simpl.
      lra.
    - simpl.
      rewrite fill_dmap //=.
      rewrite head_prim_step_eq//.
      simpl.
      rewrite dmap_dret/=.
      apply pgl_dret.
      instantiate (2:= λ x, x =(fill K #(), s, [e])).
      naive_solver.
    - iIntros (???) "%".
      destruct!/=.
      iApply spec_coupl_ret.
      iModIntro.
      iMod "Hclose".
      by iFrame.
  Qed.

  Lemma pupd_cmpxchg_fail E K l q v v1 v2 j:
    vals_compare_safe v v1 ->
    v ≠ v1 ->
    j ⤇ fill K (CmpXchg #l v1 v2) ∗ l ↦ₛ{q} v
    ⊢ pupd E E (j ⤇ fill K (v, #false)%V ∗ l ↦ₛ{q} v).
  Proof.
    iIntros (??) "[HK HL]".
    rewrite pupd_unseal/pupd_def.
    iIntros (σ1 [] ε1) "(H1 & H2 & H3)".
    iDestruct (spec_auth_prog_agree with "[$][$]") as "%".
    iDestruct (spec_auth_lookup_heap with "[$][$]") as "%".
    iMod (spec_update_prog with "[$][$]") as "[HK Hs]".
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose".
    iApply spec_coupl_step_r; [|done|..].
    - apply reducible_fill. apply head_prim_reducible. solve_red.
    - instantiate (2:=0%NNR). instantiate (1:= ε1). simpl.
      lra.
    - simpl.
      rewrite fill_dmap //=.
      rewrite head_prim_step_eq//.
      simpl.
      case_match; last done.
      simplify_eq.
      case_match; last done.
      rewrite bool_decide_eq_false_2; last done.
      rewrite dmap_dret/=.
      apply pgl_dret.
      rewrite /prim_step/=.
      simplify_eq.
      instantiate (2:= λ x, x =(fill K (v, #false)%V, s, [])).
      naive_solver.
    - iIntros (???) "%".
      destruct!/=.
      iApply spec_coupl_ret.
      iModIntro.
      iMod "Hclose".
      iFrame. 
      rewrite app_nil_r. by iFrame.
  Qed.
    
  Lemma pupd_cmpxchg_suc E K l v v1 v2 j:
    vals_compare_safe v v1 ->
    v = v1 ->
    j ⤇ fill K (CmpXchg #l v1 v2) ∗ l ↦ₛ v
    ⊢ pupd E E (j ⤇ fill K (v, #true)%V ∗ l ↦ₛ v2).
  Proof.
    iIntros (??) "[HK HL]".
    rewrite pupd_unseal/pupd_def.
    iIntros (σ1 [] ε1) "(H1 & H2 & H3)".
    iDestruct (spec_auth_prog_agree with "[$][$]") as "%".
    iDestruct (spec_auth_lookup_heap with "[$][$]") as "%".
    iMod (spec_auth_update_heap with "[$][$]") as "[??]".
    iMod (spec_update_prog with "[$][$]") as "[HK Hs]".
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose".
    iApply spec_coupl_step_r; [|done|..].
    - apply reducible_fill. apply head_prim_reducible. solve_red.
    - instantiate (2:=0%NNR). instantiate (1:= ε1). simpl.
      lra.
    - simpl.
      rewrite fill_dmap //=.
      rewrite head_prim_step_eq//.
      simpl.
      case_match; last done.
      simplify_eq.
      case_match; last done.
      rewrite bool_decide_eq_true_2; last done.
      rewrite dmap_dret/=.
      apply pgl_dret.
      rewrite /prim_step/=.
      simplify_eq.
      instantiate (2:= λ x, x =(fill K (v, #true)%V, state_upd_heap <[l:=v2]> s, [])).
      naive_solver.
    - iIntros (???) "%".
      destruct!/=.
      iApply spec_coupl_ret.
      iModIntro.
      iMod "Hclose".
      iFrame. 
      rewrite app_nil_r. by iFrame.
  Qed. 

  Lemma pupd_xchg E K l v1 v2 j:
    j ⤇ fill K (Xchg #l v2) ∗ l ↦ₛ v1
    ⊢ pupd E E (j ⤇ fill K v1 ∗ l ↦ₛ v2).
  Proof.
    iIntros "[HK HL]".
    rewrite pupd_unseal/pupd_def.
    iIntros (σ1 [] ε1) "(H1 & H2 & H3)".
    iDestruct (spec_auth_prog_agree with "[$][$]") as "%".
    iDestruct (spec_auth_lookup_heap with "[$][$]") as "%".
    iMod (spec_auth_update_heap with "[$][$]") as "[??]".
    iMod (spec_update_prog with "[$][$]") as "[HK Hs]".
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose".
    iApply spec_coupl_step_r; [|done|..].
    - apply reducible_fill. apply head_prim_reducible. solve_red.
    - instantiate (2:=0%NNR). instantiate (1:= ε1). simpl.
      lra.
    - simpl.
      rewrite fill_dmap //=.
      rewrite head_prim_step_eq//.
      simpl.
      case_match; last done.
      simplify_eq.
      rewrite dmap_dret/=.
      apply pgl_dret.
      rewrite /prim_step/=.
      simplify_eq.
      instantiate (2:= λ x, x =(fill K v1, state_upd_heap <[l:=v2]> s, [])).
      naive_solver.
    - iIntros (???) "%".
      destruct!/=.
      iApply spec_coupl_ret.
      iModIntro.
      iMod "Hclose".
      iFrame. 
      rewrite app_nil_r. by iFrame.
  Qed.

  Lemma pupd_faa E K l (i1 i2:Z) j:
    j ⤇ fill K (FAA #l #i2) ∗ l ↦ₛ #i1
    ⊢ pupd E E (j ⤇ fill K #i1 ∗ l ↦ₛ #(i1+i2)%Z).
  Proof.
    iIntros "[HK HL]".
    rewrite pupd_unseal/pupd_def.
    iIntros (σ1 [] ε1) "(H1 & H2 & H3)".
    iDestruct (spec_auth_prog_agree with "[$][$]") as "%".
    iDestruct (spec_auth_lookup_heap with "[$][$]") as "%".
    iMod (spec_auth_update_heap with "[$][$]") as "[??]".
    iMod (spec_update_prog with "[$][$]") as "[HK Hs]".
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose".
    iApply spec_coupl_step_r; [|done|..].
    - apply reducible_fill. apply head_prim_reducible. solve_red.
    - instantiate (2:=0%NNR). instantiate (1:= ε1). simpl.
      lra.
    - simpl.
      rewrite fill_dmap //=.
      rewrite head_prim_step_eq//.
      simpl.
      case_match; last done.
      simplify_eq.
      rewrite dmap_dret/=.
      apply pgl_dret.
      rewrite /prim_step/=.
      simplify_eq.
      instantiate (2:= λ x, x =(fill K #i1, state_upd_heap <[l:=#(i1 + i2)]> s, [])).
      naive_solver.
    - iIntros (???) "%".
      destruct!/=.
      iApply spec_coupl_ret.
      iModIntro.
      iMod "Hclose".
      iFrame. 
      rewrite app_nil_r. by iFrame.
  Qed.

  Lemma pupd_alloc_tape E K j z N :
    TCEq N (Z.to_nat z)->
    j ⤇ fill K (alloc #z)
    ⊢ pupd E E (∃ α, α ↪ₛN (N; []) ∗ j⤇ fill K #lbl:α).
  Proof. 
    iIntros (->) "HK".
    rewrite pupd_unseal/pupd_def.
    iIntros (σ1 [] ε1) "(H1 & H2 & H3)".
    iDestruct (spec_auth_prog_agree with "[$][$]") as "%".
    iMod (spec_auth_tape_alloc with "[$]") as "[Hs Hl]".
    iMod (spec_update_prog with "[$][$]") as "[HK Hs]".
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose".
    iApply spec_coupl_step_r; [|done|..].
    - apply reducible_fill. apply head_prim_reducible. solve_red.
    - instantiate (2:=0%NNR). instantiate (1:= ε1). simpl.
      lra.
    - simpl.
      rewrite fill_dmap //=.
      rewrite head_prim_step_eq//.
      simpl.
      rewrite dmap_dret/=.
      apply pgl_dret.
      rewrite /prim_step/=.
      instantiate (2:= λ x, x = (fill K #lbl:(fresh_loc (tapes s)), state_upd_tapes <[fresh_loc (tapes s):=(Z.to_nat z; [])]> s,
     [])).
      naive_solver.
    - iIntros (???) "%".
      destruct!/=.
      iApply spec_coupl_ret.
      iModIntro.
      iMod "Hclose".
      iFrame. 
      rewrite app_nil_r. by iFrame.
  Qed. 
          
  (* (** spec [rand] *) *)
  (* Lemma wp_rand_r N z E e K Φ : *)
  (*   TCEq N (Z.to_nat z) → *)
  (*   ⤇ fill K (rand #z) ∗ *)
  (*   (∀ n : nat, ⤇ fill K #n -∗ ⌜ n <= N ⌝ -∗ WP e @ E {{ Φ }}) *)
  (*   ⊢ WP e @ E {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros (->) "(Hj & Hwp)". *)
  (*   iApply wp_lift_step_spec_couple. *)
  (*   iIntros (σ1 e1' σ1' ε1) "(Hσ & Hs & Hε)". *)
  (*   iDestruct (spec_auth_prog_agree with "Hs Hj") as %->. *)
  (*   iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose". *)
  (*   iApply spec_coupl_step; [solve_red|]. *)
  (*   rewrite fill_dmap //=. *)
  (*   iIntros (e2' σ2' ([? ? ]&?&Hs)%dmap_pos). *)
  (*   simplify_eq/=. *)
  (*   rewrite head_prim_step_eq // in Hs. *)
  (*   inv_head_step. *)
  (*   iApply spec_coupl_ret. *)
  (*   iMod (spec_update_prog (fill K #_) with "Hs Hj") as "[$ Hj]". *)
  (*   iFrame. iModIntro. *)
  (*   iMod "Hclose" as "_"; iModIntro. *)
  (*   iApply ("Hwp" with "Hj"). *)
  (*   iPureIntro. *)
  (*   pose proof (fin_to_nat_lt x); lia. *)
  (* Qed. *)

  (* (** This is just a wrapper for tp_alloctape that works with nats *)
  (*   TODO : Make into tactic *) *)
  (* Lemma wp_alloc_tape_r N z E e K Φ : *)
  (*   TCEq N (Z.to_nat z) → *)
  (*   ⤇ fill K (alloc #z) ∗ *)
  (*   (∀ α, ⤇ fill K #lbl:α -∗ α ↪ₛN (N; []) -∗ WP e @ E {{ Φ }}) *)
  (*   ⊢ WP e @ E {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros (->) "(Hj & Hwp)". *)
  (*   tp_alloctape as α "Hα". *)
  (*   iApply ("Hwp" with "Hj"). *)
  (*   iFrame. *)
  (*   iPureIntro. *)
  (*   auto. *)
  (* Qed. *)

  (* (** spec [rand(α)] with empty tape  *) *)
  (* Lemma wp_rand_empty_r N z E e K α Φ : *)
  (*   TCEq N (Z.to_nat z) → *)
  (*   ⤇ fill K (rand(#lbl:α) #z) ∗ α ↪ₛN (N; []) ∗ *)
  (*   (∀ n : nat, (α ↪ₛN (N; []) ∗ ⤇ fill K #n) -∗ ⌜ n <= N ⌝ -∗ WP e @ E {{ Φ }}) *)
  (*   ⊢ WP e @ E {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros (->) "(Hj & Hα & Hwp)". *)
  (*   iApply wp_lift_step_spec_couple. *)
  (*   iIntros (σ1 e1' σ1' ε1) "(Hσ & Hs & Hε)". *)
  (*   iPoseProof (spec_tapeN_to_empty with "Hα") as "Hα". *)
  (*   iDestruct (spec_auth_prog_agree with "Hs Hj") as %->. *)
  (*   iDestruct (spec_auth_lookup_tape with "Hs Hα") as %?. *)
  (*   iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose". *)
  (*   iApply spec_coupl_step; [solve_red|]. *)
  (*   rewrite fill_dmap //=. *)
  (*   iIntros (e2' σ2' ([? ? ]&?&Hs)%dmap_pos). *)
  (*   simplify_eq/=. *)
  (*   rewrite head_prim_step_eq // in Hs. *)
  (*   inv_head_step. *)
  (*   iApply spec_coupl_ret. *)
  (*   iMod (spec_update_prog (fill K #_) with "Hs Hj") as "[$ Hj]". *)
  (*   iFrame. iModIntro. *)
  (*   iMod "Hclose" as "_"; iModIntro. *)
  (*   iApply ("Hwp" with "[Hα Hj]"); *)
  (*     first by iFrame; auto. *)
  (*   iPureIntro. *)
  (*   pose proof (fin_to_nat_lt x); lia. *)
  (* Qed. *)


  (* (** This is just a wrapper for tp_rand that works with nats *)
  (*   TODO: Make into tactic *) *)
  (* Lemma wp_rand_tape_r N z E e K α Φ n ns : *)
  (*   TCEq N (Z.to_nat z) → *)
  (*   ⤇ fill K (rand(#lbl:α) #z) ∗ α ↪ₛN (N; n::ns) ∗ *)
  (*   ((α ↪ₛN (N; ns) ∗ ⤇ fill K #n) -∗ ⌜ n <= N ⌝ -∗ WP e @ E {{ Φ }}) *)
  (*   ⊢ WP e @ E {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros (Heq) "(Hj & Hα & Hwp)". *)
  (*   iDestruct (read_spec_tape_head with "Hα") as (x xs) "(Hl&<-&Hret)". *)
  (*   tp_rand. *)
  (*   iDestruct ("Hret" with "Hl") as "Hret". *)
  (*   iApply ("Hwp" with "[$]"). *)
  (*   iPureIntro. *)
  (*   pose proof (fin_to_nat_lt x); lia. *)
  (* Qed. *)


  (* (** spec [rand(α)] with wrong tape  *) *)
  (* Lemma wp_rand_wrong_tape_r N M z E e K α Φ ns : *)
  (*   TCEq N (Z.to_nat z) → *)
  (*   N ≠ M → *)
  (*   ⤇ fill K (rand(#lbl:α) #z) ∗ α ↪ₛN (M; ns) ∗ *)
  (*   (∀ (n : nat), (α ↪ₛN (M; ns) ∗ ⤇ fill K #n) -∗ ⌜ n <= N ⌝ -∗ WP e @ E {{ Φ }}) *)
  (*   ⊢ WP e @ E {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros (-> ?) "(Hj & Hα & Hwp)". *)
  (*   iApply wp_lift_step_spec_couple. *)
  (*   iIntros (σ1 e1' σ1' ε1) "(Hσ & Hs & Hε)". *)
  (*   iDestruct "Hα" as (?) "(%&Hα)". *)
  (*   iDestruct (spec_auth_prog_agree with "Hs Hj") as %->. *)
  (*   iDestruct (spec_auth_lookup_tape with "Hs Hα") as %?. *)
  (*   iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose". *)
  (*   iApply spec_coupl_step; [solve_red|]. *)
  (*   rewrite fill_dmap //=. *)
  (*   iIntros (e2' σ2' ([? ? ]&?&Hs)%dmap_pos). *)
  (*   simplify_eq/=. *)
  (*   rewrite head_prim_step_eq // in Hs. *)
  (*   inv_head_step. *)
  (*   iApply spec_coupl_ret. *)
  (*   iMod (spec_update_prog (fill K #_) with "Hs Hj") as "[$ Hj]". *)
  (*   iFrame. iModIntro. *)
  (*   iMod "Hclose" as "_"; iModIntro. *)
  (*   iApply ("Hwp" with "[-]"); first by iFrame. *)
  (*   iPureIntro. *)
  (*   pose proof (fin_to_nat_lt x); lia. *)
  (* Qed. *)

End lifting.

Global Hint Extern 0 (TCEq _ (Z.to_nat _ )) => rewrite Nat2Z.id : typeclass_instances.

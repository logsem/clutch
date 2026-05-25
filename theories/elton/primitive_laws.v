(** This file proves the basic laws of the delayProbLang weakest precondition by
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



Section lifting.
  Context `{!eltonGS Σ}.

  Global Instance rupd_timeless P Q v {_:Timeless Q}: Timeless (rupd P Q v).
  Proof.
    rewrite rupd_unseal/rupd_def.
    apply _.
  Qed. 
  
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : val → iProp Σ.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types l : loc.

Lemma pupd_epsilon_err E:
  ⊢ pupd E E (∃ ε, ⌜(0<ε)%R⌝ ∗ ↯ ε)%I.
Proof.
  rewrite pupd_unseal/pupd_def.
  iApply fupd_mask_intro; first set_solver.
  iIntros "Hclose".
  iIntros (?? ε) "(Hstate& Herr)".
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
  iFrame. iMod "Hclose".
  iApply fupd_mask_intro; first set_solver.
  iIntros "Hclose'".
  iSplit; first done.
  iMod "Hclose'".
  iPureIntro.
  rewrite /diff.
  simpl.
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
  iApply fupd_mask_intro; first set_solver.
  iIntros "Hclose".
  iIntros (?[] ε') "([Hs Hu]& Herr')".
  iDestruct (ghost_map_lookup with "Hu [$]") as %?.
  iDestruct (ec_supply_ec_inv with "[$][$]") as %(x&x'& -> & He).
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
  iModIntro.
  iSplitL "Hε2".
  - iApply ec_supply_eq; [|done]. simplify_eq. simpl. simpl in *. lra.
  - iSplit; first done.
    iMod "Hclose". by iPureIntro.
Qed.


Lemma pupd_resolve_urn_avoid s l E x' :
  s≠∅ ->
  ↯(1/size s) -∗
  l ↪ urn_unif s -∗
  pupd E E (∃ x, l ↪urn_unif {[x]} ∗ ⌜ x≠ x' ⌝).
Proof.
  iIntros (Hneq) "Herr Hl".
  iMod (pupd_resolve_urn _ _ (λ x, if bool_decide (x=x')%Z then nnreal_one else nnreal_zero)%R with "[$][$]") as "H"; try done.
  - trans ((SeriesC (λ x, if bool_decide (x=x') then nnreal_one else nnreal_zero))/size s)%R.
    + rewrite !Rdiv_def. apply Rmult_le_compat_r.
      { rewrite -Rdiv_1_l. apply Rdiv_INR_ge_0. }
      apply SeriesC_le.
      * intros. do 2 case_bool_decide; simpl; lra.
      * apply ex_seriesC_singleton.
    + by rewrite SeriesC_singleton.
  - exists 1. intros. case_bool_decide; simpl; lra.
  - iDestruct ("H") as "(%&Herr&Hl&%)".
    case_bool_decide; first (by iDestruct (ec_contradict with "[$]") as "[]").
    by iFrame.
Qed. 
  
  
Lemma pupd_partial_resolve_urn s ε (ε2 : _ -> nonnegreal) l E lis:
  s ≠ ∅ ->
  ⋃ lis = s ->
  NoDup lis ->
  ∅ ∉ lis ->
  (∀ x y, x∈ lis -> y ∈ lis -> ∀ z, z ∈ x -> z ∈ y -> x=y) ->
 (SeriesC (λ x, if bool_decide (x ∈ lis) then ε2 x * size x else 0)/ size s <= ε)%R ->
  (exists r, forall ρ, (ε2 ρ <= r)%R) ->
  ↯ ε -∗ l ↪ urn_unif s -∗
  pupd E E (∃ s',
        ↯ (ε2 s') ∗ l↪ urn_unif s' ∗ ⌜s' ∈ lis⌝
    )%I.
Proof.
  rewrite pupd_unseal/pupd_def.
  iIntros (Hs Hunion Hnodup Hnonempty Hdisjoint Hineq [r Hbound]) "Herr Hl".
  iApply fupd_mask_intro; first set_solver.
  iIntros "Hclose".
  iIntros (?[] ε') "([Hs Hu]& Herr')".
  iDestruct (ghost_map_lookup with "Hu [$]") as %?.
  iDestruct (ec_supply_ec_inv with "[$][$]") as %(x&x'& -> & He).
  iApply state_step_coupl_rec_partial_split.
  pose (ε2' := λ x,  (ε2 x + x')%NNR ).
  assert (∀ x, 0<=ε2' x)%R as Hnnr; first (intros; apply cond_nonneg).
  iExists _,_, (λ x, mknonnegreal _ (Hnnr x)), lis.
  iSplit; first done.
  iSplit; first done.
  iSplit; first done.
  iSplit; first done.
  iSplit; first done.
  iSplit; first done.
  iSplit.
  { iPureIntro.
    exists ( (r+x'))%R.
    simpl. intros.
    rewrite /ε2'.
    real_solver.
  }
  iSplit; first iPureIntro.
  { simpl.
    setoid_rewrite Rmult_plus_distr_r.
    erewrite (SeriesC_ext _ (λ x0, (if bool_decide (x0 ∈ lis) then ε2 x0 * size x0 else 0)+if bool_decide (x0 ∈ lis) then x' * size x0 else 0)%R); last (intros; case_bool_decide; simpl; lra).
    rewrite SeriesC_plus; try apply ex_seriesC_list.
    rewrite Rdiv_plus_distr.
    apply Rplus_le_compat; first lra.
    rewrite SeriesC_list; last done.
    cut ((∀ lis', NoDup lis' ->  (∀ x y : gset Z, x ∈ lis' → y ∈ lis' → ∀ z : Z, z ∈ x → z ∈ y → x = y)->foldr (Rplus ∘ λ a : gset Z, x' * size a) 0 lis' = x'* size (⋃ lis')) )%R.
    - intros H'. rewrite H'; try done.
      rewrite Hunion. rewrite Rmult_div_l; first done.
      apply not_0_INR.
      rewrite size_non_empty_iff.
      by rewrite leibniz_equiv_iff.
    - clear.
      intros l.
      induction l as [|hd tl IHl]; first rewrite size_empty/=; first lra.
      intros Hnodup Hdisjoint.
      simpl.
      repeat setoid_rewrite elem_of_cons in Hdisjoint.
      rewrite IHl.
      + rewrite size_union; first simpl.
        * rewrite plus_INR. lra.
        * intros y ?. rewrite elem_of_union_list.
          intros (y' &?&?).
          assert (hd =y') as ->; first naive_solver.
          apply NoDup_cons in Hnodup. naive_solver.
      + apply NoDup_cons in Hnodup. naive_solver.
      + intros. naive_solver.
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
  rename select ((_+_)%NNR = _) into H'. apply (f_equal nonneg) in H'.
  unshelve iMod (ec_supply_increase _ (mknonnegreal (ε2 (x0)) _) with "[Hε2]") as "[Hε2 Hcr]"; first done.
  { simpl. done. }
  { simpl in *. lra. }
  { iApply ec_supply_eq; [|done]. simplify_eq. lra. }
  iFrame.
  subst.
  iModIntro.
  iSplitL "Hε2".
  - iApply ec_supply_eq; [|done]. simplify_eq. simpl. simpl in *. lra.
  - iSplit; first done.
    iMod "Hclose". by iPureIntro.
Qed. 

Lemma pupd_partial_resolve_urn_avoid s n l E m:
  s≠ ∅ ->
  (1<=n)%nat ->
  (n<=size s)%nat ->
  ↯ (n/size s) -∗
  l ↪ urn_unif s -∗
  pupd E E (∃ s', ↯ ((n-1)%nat/(size s')%nat) ∗ l ↪ urn_unif s' ∗ ⌜s' ⊆ s⌝ ∗ ⌜size s-1<=size s'⌝ ∗ ⌜m∉ s'⌝).
Proof.
  intros Hempty Hineq Hineq'.
  apply Nat.lt_eq_cases in Hineq' as [|]; last first.
  { subst.
    iIntros "H".
    iDestruct (ec_contradict with "[$]") as "[]".
    rewrite Rdiv_diag; first done.
    replace 0%R with (INR 0) by done.
    apply not_INR.
    rewrite size_non_empty_iff.
    set_solver. }
  iIntros "Herr Hl".
  destruct (decide (m∈s)); last first.
  { iModIntro.
    iFrame.
    repeat iSplit.
    - iApply (ec_weaken with "[$]").
      split.
      + apply Rcomplements.Rdiv_le_0_compat.
        * apply pos_INR.
        * apply lt_0_INR.
          lia.
      + rewrite Rcomplements.Rle_div_l; last first.
        { apply Rlt_gt. apply lt_0_INR; lia. }
        rewrite -Rmult_div_swap.
        rewrite -Rcomplements.Rle_div_r; last first.
        { apply Rlt_gt. apply lt_0_INR; lia. }
        rewrite !minus_INR; try lia.
        replace (INR 1) with 1%R by done.
        assert (-size s <= -n)%R; real_solver.
    - done.
    - iPureIntro; lia.
    - done. 
  }
  assert (0<= (n-1)%nat/(size s -1)%nat)%R as err_ineq.
  { apply Rcomplements.Rdiv_le_0_compat.
    * apply pos_INR.
    * apply lt_0_INR.
      lia.
  }
  iMod (pupd_partial_resolve_urn _ _ (λ x, if bool_decide (x=({[m]} : gset _)) then nnreal_one else mknonnegreal _ err_ineq) _ _ (({[m]} ::(s∖{[m]}) ::[]): list (gset _)) with "[$Herr] [$]")%Z as "H'".
  - done.
  - simpl.
    rewrite union_empty_r_L.
    rewrite -union_difference_L; first done.
    set_solver.
  - repeat setoid_rewrite NoDup_cons.
    repeat split; last by apply NoDup_nil.
    + set_unfold.
       intros ?. destruct!/=. set_solver.
    + set_solver.
  - set_unfold.
    intros ?.
    destruct!/=.
    rename select (_=_∖_) into Hcontra.
    apply (f_equal size) in Hcontra.
    rewrite size_empty size_difference in Hcontra; last set_solver.
    rewrite size_singleton in Hcontra. lia.
  - intros.
    set_unfold.
    destruct!/=; set_solver.
  - rewrite SeriesC_list; last first.
    { repeat setoid_rewrite NoDup_cons.
      repeat split; last by apply NoDup_nil.
      - set_unfold.
        intros ?. destruct!/=. set_solver.
      - set_solver. }
    Local Opaque size.
    simpl.
    rewrite bool_decide_eq_true_2; last done.
    rewrite Rmult_1_l size_singleton.
    rewrite bool_decide_eq_false_2; last set_solver.
    rewrite Rplus_0_r.
    simpl.
    rewrite size_difference; last set_solver.

    (* replace (_-_+_) with tries' by lia. *)
    rewrite !Rdiv_def.
    apply Rmult_le_compat_r.
    + rewrite -Rdiv_1_l.
      apply Rdiv_INR_ge_0.
    + rewrite size_singleton.
      (* rewrite plus_INR. *)
      simpl.
      rewrite Rmult_assoc.
      rewrite (Rmult_comm (/ _)%R).
      rewrite minus_INR. 2: lia.
      assert ((size s - 1)%nat */(size s -1)%nat=1)%R as -> ; simpl ; last lra.
      rewrite -Rdiv_def.
      rewrite Rdiv_diag; first done.
      rewrite minus_INR; last lia.
      simpl.
      assert (INR (size s) ≠ 1)%R; last lra.
      replace 1%R with (INR 1) by done.
      apply not_INR. lia.
  - eexists (Rmax _ _).
    intros.
    case_bool_decide.
    + apply Rmax_l.
    + apply Rmax_r.
  - iDestruct "H'" as "(%&Herr&Hurn &%h3)".
    set_unfold in h3.
    destruct!/=.
    + rewrite bool_decide_eq_true_2; last done.
      by iDestruct (ec_contradict with "[$]") as "[]".
    + rewrite bool_decide_eq_false_2; last set_solver.
      simpl.
      iFrame.
      iModIntro.
      rewrite size_difference; last set_solver.
      rewrite size_singleton.
      iFrame. 
      iPureIntro.
      repeat split.
      * set_solver.
      * lia. 
      * set_solver.
Qed. 
  
Lemma wp_value_promotion (v v': val) P Φ s E:
  (rupd (λ x, x=v') P v)-∗
    (P -∗ WP (Val (v')) @ s; E {{ Φ }}) -∗
    WP (Val (v)) @ s; E {{ Φ }}.
Proof.
  iIntros "H1 H2".
  iApply state_step_coupl_wp.
  iApply fupd_mask_intro; first set_solver.
  iIntros "Hclose".
  iIntros (??) "[??]".
  iApply state_step_coupl_value_promote.
  iExists [], (v), (v').
  simpl.
  repeat iSplit; last iFrame; first done.
  { rewrite rupd_unseal/rupd_def.
    iDestruct ("H1" with "[$]") as  "[%K ?]".
    iPureIntro.
    intros ? H'.
    apply K in H' as (?&H&?). subst.
    by rewrite H.
  }
  rewrite rupd_unseal/rupd_def.
  iDestruct ("H1" with "[$]") as "[_ [HP Hstate]]".
  iFrame.
  iApply state_step_coupl_ret.
  iFrame.
  iModIntro.
  iMod "Hclose".
  by iApply "H2".
Qed. 


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
  iIntros "!> /=" (e2 σ2 Hs); inv_head_step.
  erewrite urn_subst_equal_epsilon_unique; last done.
  iMod ((ghost_map_insert (fresh_loc σ1.(heap)) v) with "Hh") as "[? Hl]".
  { apply not_elem_of_dom, fresh_loc_is_fresh. }
  iFrame.
  simpl.
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
  erewrite urn_subst_equal_epsilon_unique; last done.
  clear.
  iInduction (Z.to_nat z) as [ | ?] "IH" forall (σ1); first done.
  rewrite seq_S.
  rewrite heap_array_replicate_S_end.
  iPoseProof (big_sepM_union _ _ _ _ with "Hl") as "[H1 H2]".
  iApply big_sepL_app.
  iSplitL "H1".
  + by iApply "IH".
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
      apply loc_add_inj in H2. subst.
      rename select (_<_)%Z into H1.
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
  rename select (_!!(epsilon _)=_) into H1.
  erewrite urn_subst_equal_epsilon_unique' in H1; last done.
  simplify_eq.
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
  rename select (_!!(epsilon _)=_) into H1.
  erewrite urn_subst_equal_epsilon_unique' in H1; last done.
  erewrite urn_subst_equal_epsilon_unique'; last done.
  simplify_eq.
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

Lemma wp_drand_thunk (N : nat) (z : Z) (v:val) E s P :
  TCEq N (Z.to_nat z) →
  {{{ (rupd (λ v ,v= (LitV $ LitInt N)) P v)}}} drand  v @ s; E {{{ l, RET LitV (LitLbl l); P ∗ l ↪ (urn_unif $ list_to_set (Z.of_nat <$> (seq 0 (S N)))) }}}.
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
    case_match; simpl in *; simplify_eq; repeat setoid_rewrite bind_Some in H'; destruct!/=.
    case_match; last first. 
    { exfalso. rename select (¬ _) into Hcontra.
      apply Hcontra.
      eexists _.
      intros ? H2. apply H in H2.
      setoid_rewrite bind_Some in H2. by destruct!/=. 
    }
    erewrite urn_subst_equal_epsilon_unique; first solve_distr.
    intros ? H2.
    apply H in H2.
    setoid_rewrite bind_Some in H2.
    by destruct!/=.
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
    setoid_rewrite bind_Some in H2.
    by destruct!/=.
  }
  rewrite Nat2Z.id.
  rewrite Nat.add_1_r. iFrame. 
Qed.
  
End lifting.

Global Hint Extern 0 (TCEq _ (Z.to_nat _ )) => rewrite Nat2Z.id : typeclass_instances.

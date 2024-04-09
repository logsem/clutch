(** * Coupling rules  *)
From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext.
From clutch.app_rel_logic Require Import lifting ectx_lifting.
From clutch.prob_lang Require Import lang notation tactics metatheory.
From clutch.app_rel_logic Require Export primitive_laws spec_rules.

Section rules.
  Context `{!app_clutchGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types v : val.
  Implicit Types l : loc.
  Implicit Types ε : nonnegreal.

  Lemma wp_couple_tapes (N M : nat) E e α αₛ ns nsₛ Φ (ε : nonnegreal) :
    to_val e = None →
    (∀ σ1, reducible (e, σ1)) →
    nclose specN ⊆ E →
    (N <= M)%R →
    (((S M - S N) / S M) = ε)%R →
    spec_ctx ∗
    ▷ α ↪ (N; ns) ∗ ▷ αₛ ↪ₛ (M; nsₛ) ∗
    € ε ∗
    (∀ (n : fin (S N)) (m : fin (S M)),
        ⌜(fin_to_nat n = m)⌝ →
        α ↪ (N; ns ++ [n]) ∗ αₛ ↪ₛ (M; nsₛ ++ [m]) -∗
        WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (He Hred ? NMpos NMε) "(#Hinv & >Hα & >Hαₛ & Hε & Hwp)".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)".
    iInv specN as (ρ' e0' σ0' n_spec_steps) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_interp_auth_frag_agree with "Hauth2 Hspec0") as %<-.
    iDestruct (ghost_map_lookup with "Htapes Hαₛ") as %?.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iSplitR ; [done|].
    (* Get up to speed with the spec resource (tracked in spec_ctx) *)
    iApply exec_coupl_det_r; [done|].
    (* split ε_now into ε + (ε_now - ε) *)
    iDestruct (ec_supply_bound with "Hε2 Hε") as %Hle.
    set (ε' := nnreal_minus ε_now ε Hle ).
    replace ε_now with (nnreal_plus ε ε'); last first.
    { apply nnreal_ext; simpl; lra. }
    (* Do a coupled [state_step] on both sides  *)
    iApply (exec_coupl_state_steps α αₛ).
    { rewrite /= /get_active.
      apply elem_of_list_In, in_prod;
        apply elem_of_list_In, elem_of_elements, elem_of_dom; auto. }
    iExists _.
    iSplit.
    { iPureIntro.
      eapply ARcoupl_state_state ; eauto.
    }
    iIntros (σ2 σ2' (n & m & nm & ? & ?)).
    (* Update our resources *)
    iMod (spec_interp_update (e0', (state_upd_tapes <[αₛ:=(M; nsₛ ++ [m]) : tape]> σ0'))
           with "Hauth2 Hspec0") as "[Hauth2 Hspec0]".
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?%lookup_total_correct.
    iDestruct (ghost_map_lookup with "Htapes Hαₛ") as %?%lookup_total_correct.
    simplify_map_eq.
    iMod (ghost_map_update ((N; ns ++ [n]) : tape) with "Ht1 Hα") as "[Ht1 Hα]".
    iMod (ghost_map_update ((M; nsₛ ++ [m]) : tape) with "Htapes Hαₛ") as "[Htapes Hαₛ]".
    (* Update Hε2 *)
    iMod (ec_decrease_supply with "Hε2 Hε") as "Hε2".
    (* Close the [spec_ctx] invariant again, so the assumption can access all invariants *)
    iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hauth Hheap Hspec0 Htapes]") as "_".
    { iModIntro. rewrite /spec_inv.
      iExists _, _, (state_upd_tapes _ _), 0. simpl.
      iFrame. rewrite pexec_O dret_1_1 //. }
    (* Our [WP] assumption with the updated resources now suffices to prove the goal *)
    iSpecialize ("Hwp" $! n m nm with "[$Hα $Hαₛ]").
    rewrite !wp_unfold /wp_pre /= He.
    iMod ("Hwp" $! (state_upd_tapes <[α:=(N; ns ++ [n]) : tape]> _)
           with "[$Hh1 $Hauth2 $Ht1 $Hε2]") as "[Hred Hwp]".
    iModIntro. done.
  Qed.

  Lemma wp_couple_tapes_rev (N M : nat) E e α αₛ ns nsₛ Φ (ε : nonnegreal) :
    to_val e = None →
    (∀ σ1, reducible (e, σ1)) →
    nclose specN ⊆ E →
    (M <= N)%R →
    (((S N - S M) / S N) = ε)%R →
    spec_ctx ∗
    ▷ α ↪ (N; ns) ∗ ▷ αₛ ↪ₛ (M; nsₛ) ∗
    € ε ∗
    (∀ (n : fin (S N)) (m : fin (S M)),
        ⌜(fin_to_nat n = m)⌝ →
        α ↪ (N; ns ++ [n]) ∗ αₛ ↪ₛ (M; nsₛ ++ [m]) -∗
        WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (He Hred ? NMpos NMε) "(#Hinv & >Hα & >Hαₛ & Hε & Hwp)".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)".
    iInv specN as (ρ' e0' σ0' n_spec_steps) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_interp_auth_frag_agree with "Hauth2 Hspec0") as %<-.
    iDestruct (ghost_map_lookup with "Htapes Hαₛ") as %?.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iSplitR ; [done|].
    (* Get up to speed with the spec resource (tracked in spec_ctx) *)
    iApply exec_coupl_det_r; [done|].
    (* split ε_now into ε + (ε_now - ε) *)
    iDestruct (ec_supply_bound with "Hε2 Hε") as %Hle.
    set (ε' := nnreal_minus ε_now ε Hle ).
    replace ε_now with (nnreal_plus ε ε'); last first.
    { apply nnreal_ext; simpl; lra. }
    (* Do a coupled [state_step] on both sides  *)
    iApply (exec_coupl_state_steps α αₛ).
    { rewrite /= /get_active.
      apply elem_of_list_In, in_prod;
        apply elem_of_list_In, elem_of_elements, elem_of_dom; auto. }
    iExists _.
    iSplit.
    { iPureIntro.
      eapply ARcoupl_state_state_rev ; eauto.
    }
    iIntros (σ2 σ2' (n & m & nm & ? & ?)).
    (* Update our resources *)
    iMod (spec_interp_update (e0', (state_upd_tapes <[αₛ:=(M; nsₛ ++ [m]) : tape]> σ0'))
           with "Hauth2 Hspec0") as "[Hauth2 Hspec0]".
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?%lookup_total_correct.
    iDestruct (ghost_map_lookup with "Htapes Hαₛ") as %?%lookup_total_correct.
    simplify_map_eq.
    iMod (ghost_map_update ((N; ns ++ [n]) : tape) with "Ht1 Hα") as "[Ht1 Hα]".
    iMod (ghost_map_update ((M; nsₛ ++ [m]) : tape) with "Htapes Hαₛ") as "[Htapes Hαₛ]".
    (* Update Hε2 *)
    iMod (ec_decrease_supply with "Hε2 Hε") as "Hε2".
    (* Close the [spec_ctx] invariant again, so the assumption can access all invariants *)
    iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hauth Hheap Hspec0 Htapes]") as "_".
    { iModIntro. rewrite /spec_inv.
      iExists _, _, (state_upd_tapes _ _), 0. simpl.
      iFrame. rewrite pexec_O dret_1_1 //. }
    (* Our [WP] assumption with the updated resources now suffices to prove the goal *)
    iSpecialize ("Hwp" $! n m nm with "[$Hα $Hαₛ]").
    rewrite !wp_unfold /wp_pre /= He.
    iMod ("Hwp" $! (state_upd_tapes <[α:=(N; ns ++ [n]) : tape]> _)
           with "[$Hh1 $Hauth2 $Ht1 $Hε2]") as "[Hred Hwp]".
    iModIntro. done.
  Qed.

  Lemma wp_rand_avoid_l {N : nat} (t : fin (S N)) (z : Z) ε E :
    TCEq N (Z.to_nat z) →
    TCEq ε (nnreal_div (nnreal_nat 1) (nnreal_nat (S N))) →
    nclose specN ⊆ E →
    spec_ctx ⊢
    {{{ € ε }}}
      rand #z @ E
      {{{ (n : fin (S N)), RET #n; ⌜ n ≠ t ⌝ }}}.
  Proof.
    iIntros (Nz Nε ?) "#Hinv %Φ !> Hε Hwp".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)".
    iInv specN as (ρ' e0' σ0' n_spec_steps) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_interp_auth_frag_agree with "Hauth2 Hspec0") as %<-.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iSplit.
    { iPureIntro. eapply head_prim_reducible; eauto with head_step. }
    (* Get up to speed with the spec resource (tracked in spec_ctx) *)
    iApply exec_coupl_det_r; [done|].
    iDestruct (ec_supply_bound with "Hε2 Hε") as %Hle.
    set (ε' := nnreal_minus ε_now ε Hle ).
    replace ε_now with (nnreal_plus ε ε'); last first.
    1: apply nnreal_ext ; simpl ; lra.
    iApply (exec_coupl_prim_step_l).
    iExists _.
    iSplit.
    { iPureIntro. eapply head_prim_reducible; eauto with head_step. }
    iSplit.
    { iPureIntro.
      eapply (wp_couple_rand_no_coll_l _ _ _ _ t) ; eauto.
      - apply lt_0_INR. lia.
      - rewrite Nε. simpl. lra.
      - by rewrite Nz.
    }
    iIntros (? (n & -> & nt & ?)).
    (* Update our resources *)
    iMod (spec_interp_update (e0', σ0')
           with "Hauth2 Hspec0") as "[Hauth2 Hspec0]".
    simplify_map_eq.
    (* Update Hε2 *)
    iMod (ec_decrease_supply with "Hε2 Hε") as "Hε2".
    (* Close the [spec_ctx] invariant again, so the assumption can access all invariants *)
    iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hauth Hheap Hspec0 Htapes]") as "_".
    { iModIntro. rewrite /spec_inv.
      iExists _, _, _, 0. simpl.
      iFrame. rewrite pexec_O dret_1_1 //. }
    (* Our [WP] assumption with the updated resources now suffices to prove the goal *)
    iSpecialize ("Hwp" $! n with "[]"). 1: easy.
    rewrite !wp_unfold /wp_pre /=.
    iFrame. iApply fupd_mask_intro. 1: easy. iIntros "hclose". iModIntro.
    iMod "hclose". done.
  Qed.

  Lemma wp_couple_avoid_r {N : nat} (t : fin (S N)) (z : Z) K e ε E Φ:
    to_val e = None →
    (∀ σ1, reducible (e, σ1)) →
    TCEq N (Z.to_nat z) →
    TCEq ε (nnreal_div (nnreal_nat 1) (nnreal_nat (S N))) →
    nclose specN ⊆ E →
    refines_right K (rand #z) ∗
    € ε ∗
    (∀ (n : fin (S N)),
       refines_right K #n -∗ ⌜n≠t⌝-∗
        WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (Htv Hred Nz Nε Hspec) "([#Hinv  HK] & Hε & Hwp)". 
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)".
    iInv specN as (ρ' e0' σ0' n_spec_steps) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_interp_auth_frag_agree with "Hauth2 Hspec0") as %<-.
    iDestruct (spec_prog_auth_frag_agree with "Hauth HK") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iSplit; first done.
    (* Get up to speed with the spec resource (tracked in spec_ctx) *)
    iApply exec_coupl_det_r; [done|].
    iDestruct (ec_supply_bound with "Hε2 Hε") as %Hle.
    set (ε' := nnreal_minus ε_now ε Hle ).
    replace ε_now with (nnreal_plus ε ε'); last first.
    1: apply nnreal_ext ; simpl ; lra.
    iApply exec_coupl_exec_r.
    iExists (λ ρ2 ρₛ,
             ∃ n : fin (S N), ρ2 = (e ,σ1) ∧ ρₛ = (fill K #n, σ0') ∧ n ≠ t), 1.
    iSplit.
    - rewrite pexec_1 step_or_final_no_final /=.
      + rewrite fill_dmap //.
        rewrite -(dmap_id (dret _)). iPureIntro.
        rewrite /dmap /=. 
        replace ε with (nnreal_plus ε nnreal_zero); last first.
        { apply nnreal_ext; simpl; lra. }
        eapply ARcoupl_dbind; last first.
        * apply (wp_couple_rand_no_coll_r _ _ _ _ t); eauto.
          -- apply lt_0_INR. lia.
          -- rewrite Nε. simpl.  rewrite Nz. lra.
          -- rewrite Nz. done.
        * intros [] [] (b & ? & ?).
          apply ARcoupl_dret.
          simplify_eq. simpl. naive_solver.
        * simpl; lra.
        * apply cond_nonneg.
      + by apply to_final_None_2, fill_not_val.
    - iIntros (??) "(% &_&[%He %])". simplify_eq.
      iMod (spec_interp_update (fill K #(n), σ0') with "Hauth2 Hspec0") as "[Hauth2 Hspec0]".
      iMod (spec_prog_update (fill K #(n))  with "Hauth HK") as "[Hauth HK]".
      iMod (ec_decrease_supply with "Hε2 Hε") as "Hε2".
      iMod "Hclose'" as "_".
      iMod ("Hclose" with "[Hauth Hheap Hspec0 Htapes]") as "_".
      { iModIntro. rewrite /spec_inv.
        iExists _, _, _, 0. simpl.
        iFrame. rewrite pexec_O dret_1_1 //. }
    (* Our [WP] assumption with the updated resources now suffices to prove the goal *)
      iSpecialize ("Hwp" $! n with "[HK][]").
      { iSplit; by iFrame. }
      { done. }
      rewrite !wp_unfold /wp_pre /=.
      iFrame. rewrite Htv. iMod ("Hwp" with "[$]") as "(%&?)".
      iModIntro. iFrame.
  Qed.

  (** * rand(unit, N) ~ rand(unit, M) coupling, N <= M, under inj *)
  Lemma wp_couple_rand_rand_inj (N M : nat)  (f:nat -> nat) z w K E Φ (ε : nonnegreal) :
    (forall n, n < S N -> f n < S M) ->
    (forall n1 n2, n1 < S N -> n2 < S N -> f n1 = f n2 -> n1 = n2) ->
    TCEq N (Z.to_nat z) →
    TCEq M (Z.to_nat w) →
    nclose specN ⊆ E →
    (N <= M)%R ->
    (((S M - S N) / S M) = ε)%R →
    refines_right K (rand #w) ∗
    € ε ∗
    ▷ (∀ (n : fin (S N)), 
        refines_right K #(f n)  -∗ WP (Val #n) @ E {{ Φ }})
    ⊢ WP rand #z @ E {{ Φ }}.
  Proof.
    iIntros (Hdom Hinj).
    set g := (λ m : fin (S N), Fin.of_nat_lt (Hdom m (fin_to_nat_lt m))).
    iIntros (-> -> ? HNM Hε) "([#Hinv Hr ] & Hε & Hwp)".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)".
    iInv specN as (ρ' e0' σ0' m) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_prog_auth_frag_agree with "Hauth Hr") as %->.
    iDestruct (spec_interp_auth_frag_agree with "Hauth2 Hspec0") as %<-.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iSplit.
    { iPureIntro. eapply head_prim_reducible; eauto with head_step. }
    iDestruct (ec_supply_bound with "Hε2 Hε") as %Hle.
    set (ε' := nnreal_minus ε_now ε Hle ).
    replace ε_now with (nnreal_plus ε ε'); last first.
    { apply nnreal_ext; simpl; lra. }
    iApply exec_coupl_det_r; [done|].
    iApply exec_coupl_prim_steps.
    iExists (λ '(e2, σ2) '(e2', σ2'),
        ∃ (n : fin _),
        (e2, σ2) = (Val #(n), σ1) ∧ (e2', σ2') = (fill K #(g n), σ0')).
    iSplit.
    { iPureIntro. eapply head_prim_reducible; eauto with head_step. }
    iSplit.
    { iPureIntro. simpl.
      rewrite fill_dmap // -(dret_id_right (prim_step _ _)) /=.
      rewrite /dmap /=.
      replace ε with (nnreal_plus ε nnreal_zero); last first.
      { apply nnreal_ext; simpl; lra. }
      eapply ARcoupl_dbind.
      1,2:apply cond_nonneg.
      2:eapply (ARcoupl_rand_rand_inj _ _ g); eauto.
      simpl.
      intros [] [] (b & ? & ?).
      apply ARcoupl_dret.
      simplify_eq. simpl. eauto. } 
    iIntros ([] [] (b & b' & Hbb')).
    simplify_eq.
    iMod (spec_interp_update (fill K #(g b), σ0') with "Hauth2 Hspec0") as "[Hauth2 Hspec0]".
    iMod (spec_prog_update (fill K #(g b))  with "Hauth Hr") as "[Hauth Hr]".
    iMod (ec_decrease_supply with "Hε2 Hε") as "Hε2".
    do 2 iModIntro.
    iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hauth Hheap Hspec0 Htapes]") as "_".
    { iModIntro. rewrite /spec_inv.
      iExists _, _, _, 0. simpl.
      iFrame. rewrite pexec_O dret_1_1 //. }
    iModIntro. iFrame.
    iApply "Hwp"; eauto.
    iSplit; try done.
    rewrite /g. by rewrite fin_to_nat_to_fin.
    Unshelve.
    intros m1 m2 Heq.
    assert (fin_to_nat (g m1) = f (fin_to_nat m1)) as H1.
    {
      rewrite /g fin_to_nat_to_fin //.
    }
    assert (fin_to_nat (g m2) = f (fin_to_nat m2)) as H2.
    {
      rewrite /g fin_to_nat_to_fin //.
    }
    apply fin_to_nat_inj.
    apply Hinj.
    - apply fin_to_nat_lt.
    - apply fin_to_nat_lt.
    - rewrite -H1.
      rewrite -H2.
      by f_equal.
  Qed.
  

  (** * rand(unit, N) ~ rand(unit, M) coupling, N <= M, under equality *)
  Lemma wp_couple_rand_rand_leq (N M : nat) z w K E Φ (ε : nonnegreal) :
    TCEq N (Z.to_nat z) →
    TCEq M (Z.to_nat w) →
    nclose specN ⊆ E →
    (N <= M)%R ->
    (((S M - S N) / S M) = ε)%R →
    refines_right K (rand #w) ∗
    € ε ∗
    ▷ (∀ (n : fin (S N)) (m : fin (S M)),
        ⌜(fin_to_nat n = m)⌝ →
        refines_right K #m  -∗ WP (Val #n) @ E {{ Φ }})
    ⊢ WP rand #z @ E {{ Φ }}.
  Proof.
    iIntros (-> -> ? HNM Hε) "([#Hinv Hr ] & Hε & Hwp)".
    iApply wp_couple_rand_rand_inj; [| |done|done|done|..].
    - instantiate (1:=(λ x,x)). apply INR_le in HNM. intros. lia.
    - intros; lia.
    - iFrame. iSplitR; first done.
      assert (∀ x:fin (S(Z.to_nat z)), x<S(Z.to_nat w)) as T.
      { apply INR_le in HNM. intros. pose proof fin_to_nat_lt x. lia. }
      iModIntro. iIntros. iApply ("Hwp" $! n (nat_to_fin (T n))).
      + iPureIntro.
        by rewrite fin_to_nat_to_fin.
      + rewrite fin_to_nat_to_fin. iFrame.
  Qed.


  (** * rand(unit, N) ~ rand(unit, M) coupling, M <= N, along an injection *)
  Lemma wp_couple_rand_rand_rev_inj (N M : nat) (f : nat -> nat) z w K E Φ (ε : nonnegreal) :
    (forall n, n < S M -> f n < S N) ->
    (forall n1 n2, n1 < S M -> n2 < S M -> f n1 = f n2 -> n1 = n2) ->
    TCEq N (Z.to_nat z) →
    TCEq M (Z.to_nat w) →
    nclose specN ⊆ E →
    (M <= N)%R ->
    (((S N - S M) / S N) = ε)%R →
    refines_right K (rand #w) ∗
    € ε ∗
    ▷ (∀ (m : fin (S M)),
        refines_right K #m  -∗ WP (Val #(f m)) @ E {{ Φ }})
    ⊢ WP rand #z @ E {{ Φ }}.
  Proof.
    iIntros (Hdom Hinj).
    set g := (λ m : fin (S M), Fin.of_nat_lt (Hdom m (fin_to_nat_lt m))).
    iIntros (-> -> ? HNM Hε) "([#Hinv Hr ] & Hε & Hwp)".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)".
    iInv specN as (ρ' e0' σ0' m) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_prog_auth_frag_agree with "Hauth Hr") as %->.
    iDestruct (spec_interp_auth_frag_agree with "Hauth2 Hspec0") as %<-.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iSplit.
    { iPureIntro. apply head_prim_reducible.
      eexists (Val #0%fin, σ1).
      apply head_step_support_equiv_rel.
      by eapply (RandNoTapeS _ _ 0%fin). }
    iDestruct (ec_supply_bound with "Hε2 Hε") as %Hle.
    set (ε' := nnreal_minus ε_now ε Hle ).
    replace ε_now with (nnreal_plus ε ε'); last first.
    { apply nnreal_ext; simpl; lra. }
    iApply exec_coupl_det_r; [done|].
    iApply exec_coupl_prim_steps.
    iExists (λ '(e2, σ2) '(e2', σ2'),
        ∃ (m : fin _),
        (e2, σ2) = (Val #(g m), σ1) ∧ (e2', σ2') = (fill K #m, σ0')).
    iSplit.
    { iPureIntro. eapply head_prim_reducible; eauto with head_step. }
    iSplit.
    { iPureIntro. simpl.
      rewrite fill_dmap // -(dret_id_right (prim_step _ _)) /=.
      rewrite /dmap /=.
      replace ε with (nnreal_plus ε nnreal_zero); last first.
      { apply nnreal_ext; simpl; lra. }
      eapply ARcoupl_dbind.
      1,2:apply cond_nonneg.
      2:eapply (ARcoupl_rand_rand_rev_inj _ _ g); eauto.
      intros [] [] (b & [=] & [=])=>/=.
      apply ARcoupl_dret.
      simplify_eq. eauto. }
    iIntros ([] [] (b & [= -> ->] & [= -> ->])).
    simplify_eq.
    iMod (spec_interp_update (fill K #b, σ0') with "Hauth2 Hspec0") as "[Hauth2 Hspec0]".
    iMod (spec_prog_update (fill K #b)  with "Hauth Hr") as "[Hauth Hr]".
    iMod (ec_decrease_supply with "Hε2 Hε") as "Hε2".
    do 2 iModIntro.
    iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hauth Hheap Hspec0 Htapes]") as "_".
    { iModIntro. rewrite /spec_inv.
      iExists _, _, _, 0. simpl.
      iFrame. rewrite pexec_O dret_1_1 //. }
    iModIntro. iFrame.
    assert (#(g b) = #(f b)) as ->.
    {
      f_equal.
      rewrite /g fin_to_nat_to_fin //.
    }
    iApply "Hwp"; eauto.
    iSplit; done.
    Unshelve.
    (* TODO: Is there a cleaner way? *)
    intros m1 m2 Heq.
    assert (fin_to_nat (g m1) = f (fin_to_nat m1)) as H1.
    {
      rewrite /g fin_to_nat_to_fin //.
    }
    assert (fin_to_nat (g m2) = f (fin_to_nat m2)) as H2.
    {
      rewrite /g fin_to_nat_to_fin //.
    }
    apply fin_to_nat_inj.
    apply Hinj.
    - apply fin_to_nat_lt.
    - apply fin_to_nat_lt.
    - rewrite -H1.
      rewrite -H2.
      by f_equal.
  Qed.





  (** * rand(unit, N) ~ rand(unit, M) coupling, N <= M, under equality *)
  Lemma wp_couple_rand_rand_rev_leq (N M : nat) z w K E Φ (ε : nonnegreal) :
    TCEq N (Z.to_nat z) →
    TCEq M (Z.to_nat w) →
    nclose specN ⊆ E →
    (M <= N)%R ->
    (((S N - S M) / S N) = ε)%R →
    refines_right K (rand #w) ∗
    € ε ∗
    ▷ (∀ (n : fin (S N)) (m : fin (S M)),
        ⌜(fin_to_nat n = m)⌝ →
        refines_right K #m  -∗ WP (Val #n) @ E {{ Φ }})
    ⊢ WP rand #z @ E {{ Φ }}.
  Proof.
    iIntros (-> -> ? HNM Hε) "([#Hinv Hr ] & Hε & Hwp)".
    iApply wp_couple_rand_rand_rev_inj; [| |done|done|done|..].
    - instantiate (1:=(λ x,x)). apply INR_le in HNM. intros. lia.
    - intros; lia.
    - iFrame. iSplitR; first done.
      assert (∀ x:fin (S(Z.to_nat w)), x<S(Z.to_nat z)) as T.
      { apply INR_le in HNM. intros. pose proof fin_to_nat_lt x. lia. }
      iModIntro. iIntros. replace (fin_to_nat m) with (fin_to_nat (nat_to_fin (T m))).
      + iApply "Hwp"; by rewrite fin_to_nat_to_fin.
      + by rewrite fin_to_nat_to_fin.
  Qed.

End rules.

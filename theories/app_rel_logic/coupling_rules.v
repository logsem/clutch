(** * Coupling rules  *)
From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext.
From clutch.app_rel_logic Require Import lifting ectx_lifting.
From clutch.prob_lang Require Import lang notation tactics metatheory erasure.
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

  (** Copied from weakest_pre since this only holds for problang
      since state steps are erasable only in problang atm
*)
  Lemma exec_coupl_state_steps α α' e1 σ1 e1' σ1' Z (ε ε' : nonnegreal) :
    (α, α') ∈ list_prod (get_active σ1) (get_active σ1') →
    (∃ R, ⌜ARcoupl (state_step σ1 α) (state_step σ1' α') R ε⌝ ∗
          (∀ σ2 σ2', ⌜R σ2 σ2'⌝ ={∅}=∗ exec_coupl e1 σ2 e1' σ2' Z ε'))
    ⊢ exec_coupl e1 σ1 e1' σ1' Z (nnreal_plus ε ε').
  Proof.
    iIntros (?) "(%&[% H])".
    iApply exec_coupl_big_state_steps.
    iExists R2, (state_step σ1 α), (state_step σ1' α').
    apply elem_of_list_prod_1 in H. destruct H as [H1 H2].
    rewrite /get_active in H1. rewrite elem_of_elements in H1.
    rewrite elem_of_dom in H1. destruct H1.
    rewrite /get_active in H2. rewrite elem_of_elements in H2.
    rewrite elem_of_dom in H2. destruct H2.
    repeat iSplit; try done.
    - iPureIntro. by eapply state_step_erasable. 
    - iPureIntro. by eapply state_step_erasable.
  Qed.

  Lemma wp_couple_tapes (N M : nat) E e α αₛ ns nsₛ Φ (ε : nonnegreal) :
    to_val e = None →
    (∀ σ1, reducible (e, σ1)) →
    (N <= M)%R →
    (((S M - S N) / S M) = ε)%R →
    ▷ α ↪ (N; ns) ∗ ▷ αₛ ↪ₛ (M; nsₛ) ∗
    € ε ∗
    (∀ (n : fin (S N)) (m : fin (S M)),
        ⌜(fin_to_nat n = m)⌝ →
        α ↪ (N; ns ++ [n]) ∗ αₛ ↪ₛ (M; nsₛ ++ [m]) -∗
        WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (He Hred NMpos NMε) "(>Hα & >Hαₛ & Hε & Hwp)".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)".
    iDestruct "Hauth2" as "(HK&Hh2&Ht2)/=".
    iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
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
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?%lookup_total_correct.
    iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?%lookup_total_correct.
    simplify_map_eq.
    iMod (ghost_map_update ((N; ns ++ [n]) : tape) with "Ht1 Hα") as "[Ht1 Hα]".
    iMod (ghost_map_update ((M; nsₛ ++ [m]) : tape) with "Ht2 Hαₛ") as "[Ht2 Hαₛ]".
    (* Update Hε2 *)
    iMod (ec_decrease_supply with "Hε2 Hε") as "Hε2".
    iMod "Hclose'" as "_".
    (* Our [WP] assumption with the updated resources now suffices to prove the goal *)
    iSpecialize ("Hwp" $! n m nm with "[$Hα $Hαₛ]").
    rewrite !wp_unfold /wp_pre /= He.
    iMod ("Hwp" $! (state_upd_tapes <[α:=(N; ns ++ [n]) : tape]> _) _ (state_upd_tapes _ _)
           with "[$Hh1 $Ht1 $Hε2 $HK $Hh2 Ht2]") as "Hwp"; done.
  Qed.
    

  Lemma wp_couple_tapes_rev (N M : nat) E e α αₛ ns nsₛ Φ (ε : nonnegreal) :
    to_val e = None →
    (∀ σ1, reducible (e, σ1)) →
    (M <= N)%R →
    (((S N - S M) / S N) = ε)%R →
    ▷ α ↪ (N; ns) ∗ ▷ αₛ ↪ₛ (M; nsₛ) ∗
    € ε ∗
    (∀ (n : fin (S N)) (m : fin (S M)),
        ⌜(fin_to_nat n = m)⌝ →
        α ↪ (N; ns ++ [n]) ∗ αₛ ↪ₛ (M; nsₛ ++ [m]) -∗
        WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (He Hred NMpos NMε) "( >Hα & >Hαₛ & Hε & Hwp)".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)".
    iDestruct "Hauth2" as "(HK&Hh2&Ht2)".
    iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
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
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?%lookup_total_correct.
    iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?%lookup_total_correct.
    simplify_map_eq.
    iMod (ghost_map_update ((N; ns ++ [n]) : tape) with "Ht1 Hα") as "[Ht1 Hα]".
    iMod (ghost_map_update ((M; nsₛ ++ [m]) : tape) with "Ht2 Hαₛ") as "[Ht2 Hαₛ]".
    (* Update Hε2 *)
    iMod (ec_decrease_supply with "Hε2 Hε") as "Hε2".
    (* Close the [spec_ctx] invariant again, so the assumption can access all invariants *)
    iMod "Hclose'" as "_".
    (* Our [WP] assumption with the updated resources now suffices to prove the goal *)
    iSpecialize ("Hwp" $! n m nm with "[$Hα $Hαₛ]").
    rewrite !wp_unfold /wp_pre /= He.
    iMod ("Hwp" $! (state_upd_tapes <[α:=(N; ns ++ [n]) : tape]> _) _ (state_upd_tapes _ _)
           with "[$Hh1 $Ht1 $Hε2 $HK $Hh2 Ht2]") as "Hwp"; done.
  Qed.

  Lemma wp_rand_avoid_l {N : nat} (t : fin (S N)) (z : Z) ε E :
    TCEq N (Z.to_nat z) →
    TCEq ε (nnreal_div (nnreal_nat 1) (nnreal_nat (S N))) ->
    ⊢
    {{{ € ε }}}
      rand #z @ E
      {{{ (n : fin (S N)), RET #n; ⌜ n ≠ t ⌝ }}}.
  Proof.
    iIntros (Nz Nε) "%Φ !> Hε Hwp".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)".
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
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
    simplify_map_eq.
    (* Update Hε2 *)
    iMod (ec_decrease_supply with "Hε2 Hε") as "Hε2".
    (* Close the [spec_ctx] invariant again, so the assumption can access all invariants *)
    iMod "Hclose'" as "_".
    (* Our [WP] assumption with the updated resources now suffices to prove the goal *)
    iSpecialize ("Hwp" $! n with "[]"). 1: easy.
    rewrite !wp_unfold /wp_pre /=.
    iFrame. iApply fupd_mask_intro. 1: easy. iIntros "hclose". iModIntro.
    iMod "hclose". done.
  Qed.

  Lemma wp_rand_avoid_r {N : nat} (t : fin (S N)) (z : Z) K e ε E Φ:
    to_val e = None →
    (∀ σ1, reducible (e, σ1)) →
    TCEq N (Z.to_nat z) →
    TCEq ε (nnreal_div (nnreal_nat 1) (nnreal_nat (S N))) →
    ⤇ fill K (rand #z) ∗
    € ε ∗
    (∀ (n : fin (S N)),
       ⤇ fill K #n -∗ ⌜n≠t⌝-∗
        WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (Htv Hred Nz Nε) "(HK & Hε & Hwp)". 
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)".
    iDestruct (spec_interp_auth_frag_agree_expr with "Hauth2 HK") as "->".
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iDestruct (ec_supply_bound with "Hε2 Hε") as %Hle.
    set (ε' := nnreal_minus ε_now ε Hle ).
    replace ε_now with (nnreal_plus ε ε'); last first.
    1: apply nnreal_ext ; simpl ; lra.
    iApply exec_coupl_exec_r.
    iExists (λ ρ2 ρₛ,
             ∃ n : fin (S N), ρ2 = (e ,σ1) ∧ ρₛ = (fill K #n, σ1') ∧ n ≠ t), 1.
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
      iMod (spec_interp_update_expr _ _ _ (fill K #(n)) with "Hauth2 HK") as "[Hauth2 HK]".
      iMod (ec_decrease_supply with "Hε2 Hε") as "Hε2".
      iMod "Hclose'" as "_".
      iSpecialize ("Hwp" $! n with "[$HK][]").
      { done. }
      rewrite !wp_unfold /wp_pre /=.
      iFrame. rewrite Htv. iMod ("Hwp" with "[$]").
      iModIntro. iFrame.
  Qed.

  (** * rand(unit, N) ~ rand(unit, M) coupling, N <= M, under inj *)
  Lemma wp_couple_rand_rand_inj (N M : nat)  (f:nat -> nat) z w K E Φ (ε : nonnegreal) :
    (forall n, n < S N -> f n < S M) ->
    (forall n1 n2, n1 < S N -> n2 < S N -> f n1 = f n2 -> n1 = n2) ->
    TCEq N (Z.to_nat z) →
    TCEq M (Z.to_nat w) →
    (N <= M)%R ->
    (((S M - S N) / S M) = ε)%R →
    ⤇ fill K (rand #w) ∗
    € ε ∗
    ▷ (∀ (n : fin (S N)), 
        ⤇ fill K #(f n)  -∗ WP (Val #n) @ E {{ Φ }})
    ⊢ WP rand #z @ E {{ Φ }}.
  Proof.
    iIntros (Hdom Hinj).
    set g := (λ m : fin (S N), Fin.of_nat_lt (Hdom m (fin_to_nat_lt m))).
    iIntros (-> -> HNM Hε) "( Hr  & Hε & Hwp)".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)".
    iDestruct (spec_interp_auth_frag_agree_expr with "Hauth2 Hr") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iDestruct (ec_supply_bound with "Hε2 Hε") as %Hle.
    set (ε' := nnreal_minus ε_now ε Hle ).
    replace ε_now with (nnreal_plus ε ε'); last first.
    { apply nnreal_ext; simpl; lra. }
    (* iApply exec_coupl_det_r; [done|]. *)
    iApply exec_coupl_prim_steps.
    iExists (λ '(e2, σ2) '(e2', σ2'),
        ∃ (n : fin _),
        (e2, σ2) = (Val #(n), σ1) ∧ (e2', σ2') = (fill K #(g n), σ1')).
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
    iMod (spec_interp_update_expr _ _ _  (fill K #(g b)) with "Hauth2 Hr") as "[Hauth2 Hspec0]".
    iMod (ec_decrease_supply with "Hε2 Hε") as "Hε2".
    do 2 iModIntro.
    iMod "Hclose'" as "_".
    iModIntro. iFrame.
    iApply "Hwp"; eauto.    
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
    (N <= M)%R ->
    (((S M - S N) / S M) = ε)%R →
    ⤇ fill K (rand #w) ∗
    € ε ∗
    ▷ (∀ (n : fin (S N)) (m : fin (S M)),
        ⌜(fin_to_nat n = m)⌝ →
        ⤇ fill K #m  -∗ WP (Val #n) @ E {{ Φ }})
    ⊢ WP rand #z @ E {{ Φ }}.
  Proof.
    iIntros (-> ->  HNM Hε) "(Hr & Hε & Hwp)".
    iApply wp_couple_rand_rand_inj; [| |done|done|..].
    - instantiate (1:=(λ x,x)). apply INR_le in HNM. intros. lia.
    - intros; lia.
    - iFrame. 
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
    (M <= N)%R ->
    (((S N - S M) / S N) = ε)%R →
    ⤇ fill K (rand #w) ∗
    € ε ∗
    ▷ (∀ (m : fin (S M)),
        ⤇ fill K #m  -∗ WP (Val #(f m)) @ E {{ Φ }})
    ⊢ WP rand #z @ E {{ Φ }}.
  Proof.
    iIntros (Hdom Hinj).
    set g := (λ m : fin (S M), Fin.of_nat_lt (Hdom m (fin_to_nat_lt m))).
    iIntros (-> -> HNM Hε) "(Hr & Hε & Hwp)".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)".
    iDestruct (spec_interp_auth_frag_agree_expr with "Hauth2 Hr") as %-> .
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iDestruct (ec_supply_bound with "Hε2 Hε") as %Hle.
    set (ε' := nnreal_minus ε_now ε Hle ).
    replace ε_now with (nnreal_plus ε ε'); last first.
    { apply nnreal_ext; simpl; lra. }
    (* iApply exec_coupl_det_r; [done|]. *)
    iApply exec_coupl_prim_steps.
    iExists (λ '(e2, σ2) '(e2', σ2'),
        ∃ (m : fin _),
        (e2, σ2) = (Val #(g m), σ1) ∧ (e2', σ2') = (fill K #m, σ1')).
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
    iMod (spec_interp_update_expr _ _ _ (fill K #b) with "Hauth2 Hr") as "[Hauth2 Hspec0]".
    iMod (ec_decrease_supply with "Hε2 Hε") as "Hε2".
    do 2 iModIntro.
    iMod "Hclose'" as "_".
    iModIntro. iFrame.
    assert (#(g b) = #(f b)) as ->.
    {
      f_equal.
      rewrite /g fin_to_nat_to_fin //.
    }
    iApply "Hwp"; eauto.
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
    (M <= N)%R ->
    (((S N - S M) / S N) = ε)%R →
    ⤇ fill K (rand #w) ∗
    € ε ∗
    ▷ (∀ (n : fin (S N)) (m : fin (S M)),
        ⌜(fin_to_nat n = m)⌝ →
        ⤇ fill K #m  -∗ WP (Val #n) @ E {{ Φ }})
    ⊢ WP rand #z @ E {{ Φ }}.
  Proof.
    iIntros (-> -> HNM Hε) "(Hr & Hε & Hwp)".
    iApply wp_couple_rand_rand_rev_inj; [| |done|done|..].
    - instantiate (1:=(λ x,x)). apply INR_le in HNM. intros. lia.
    - intros; lia.
    - iFrame.
      assert (∀ x:fin (S(Z.to_nat w)), x<S(Z.to_nat z)) as T.
      { apply INR_le in HNM. intros. pose proof fin_to_nat_lt x. lia. }
      iModIntro. iIntros. replace (fin_to_nat m) with (fin_to_nat (nat_to_fin (T m))).
      + iApply "Hwp"; by rewrite fin_to_nat_to_fin.
      + by rewrite fin_to_nat_to_fin.
  Qed.

End rules.

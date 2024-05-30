(** * Coupling rules  *)
From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext.
From clutch.paris Require Import lifting ectx_lifting.
From clutch.prob_lang Require Import lang notation tactics metatheory erasure.
From clutch.paris Require Export primitive_laws.

Section rules.
  Context `{!parisGS Σ}.
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
    iIntros (He NMpos NMε) "(>Hα & >Hαₛ & Hε & Hwp)".
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
    iIntros (He NMpos NMε) "( >Hα & >Hαₛ & Hε & Hwp)".
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
    TCEq N (Z.to_nat z) →
    TCEq ε (nnreal_div (nnreal_nat 1) (nnreal_nat (S N))) →
    ⤇ fill K (rand #z) ∗
    € ε ∗
    (∀ (n : fin (S N)),
       ⤇ fill K #n -∗ ⌜n≠t⌝-∗
        WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (Htv Nz Nε) "(HK & Hε & Hwp)".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)".
    iDestruct (spec_auth_prog_agree with "Hauth2 HK") as "->".
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
      iMod (spec_update_prog (fill K #(n)) with "Hauth2 HK") as "[Hauth2 HK]".
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
    iDestruct (spec_auth_prog_agree with "Hauth2 Hr") as %->.
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
    iMod (spec_update_prog (fill K #(g b)) with "Hauth2 Hr") as "[Hauth2 Hspec0]".
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
    iDestruct (spec_auth_prog_agree with "Hauth2 Hr") as %-> .
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
    iMod (spec_update_prog (fill K #b) with "Hauth2 Hr") as "[Hauth2 Hspec0]".
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

  (** * fragmented state rand N ~ state rand M, N>=M, under injective function from M to N*)
  Lemma wp_couple_fragmented_rand_rand_inj  (M N:nat) (f:fin(S M) -> fin (S N)) (Hinj: Inj (=) (=) f) ns nsₛ α αₛ e E Φ:
    (M<=N)%R ->
    to_val e = None ->
    ▷ α ↪ (N; ns) ∗ ▷ αₛ ↪ₛ (M; nsₛ) ∗
    (∀ (n : fin (S N)),
       if bool_decide(∃ m, f m = n) then
         ∀ m,
       α ↪ (N; ns ++ [n]) ∗ αₛ ↪ₛ (M; nsₛ ++ [m]) ∗ ⌜f m = n⌝ -∗
       WP e @ E {{ Φ }}
     else
       α ↪ (N; ns ++ [n]) ∗ αₛ ↪ₛ (M; nsₛ) -∗
       WP e @ E {{ Φ }}
    )
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (Hineq Hval) "(>Hα & >Hαₛ & Hwp)".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)".
    iDestruct "Hauth2" as "(HK&Hh2&Ht2)/=".
    iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?.
    simplify_map_eq.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    replace (ε_now) with (0+ε_now)%NNR; last (apply nnreal_ext; simpl; lra).
    iApply exec_coupl_big_state_steps.
    iExists _, _, _.
    repeat iSplit.
    - iPureIntro. apply ARcoupl_exact. apply Rcoupl_fragmented_rand_rand_inj.
      all: exact.
    - iPureIntro. by eapply state_step_erasable.
    - iPureIntro. apply erasable_dbind_predicate.
      + apply dunifP_mass.
      + by eapply state_step_erasable.
      + apply dret_erasable.
    - simpl. iIntros (??[n H']).
      case_bool_decide as H1.
      * destruct H' as (m&?&?&?).
        destruct H1 as [m' <-].
        assert (m' = m) as -> by (by apply Hinj).
        iMod (ghost_map_update ((N; ns ++ [f m]) : tape) with "Ht1 Hα") as "[Ht1 Hα]".
        iMod (ghost_map_update ((M; nsₛ ++ [m]) : tape) with "Ht2 Hαₛ") as "[Ht2 Hαₛ]".
        iMod "Hclose'" as "_".
        iSpecialize ("Hwp" $! (f m)).
        rewrite bool_decide_eq_true_2; last naive_solver.
        iSpecialize ("Hwp" $! (m)).
        rewrite !wp_unfold/wp_pre/=Hval.
        iDestruct ("Hwp" with "[$Hα $Hαₛ]") as "Hwp"; first done.
        iMod ("Hwp" $! (state_upd_tapes <[α:=(N; ns ++ [f m]) : tape]> _) _ (state_upd_tapes <[αₛ:=(M; nsₛ ++ [m]) : tape]> _) with "[$]"). subst.
        iModIntro. replace (0+_)%NNR with ε_now; first iFrame.
        apply nnreal_ext; simpl; lra.
      * destruct H' as [??]. simplify_eq.
        iMod (ghost_map_update ((N; ns ++ [n]) : tape) with "Ht1 Hα") as "[Ht1 Hα]".
        iMod "Hclose'" as "_".
        iSpecialize ("Hwp" $! n).
        rewrite bool_decide_eq_false_2; last done.
        rewrite !wp_unfold/wp_pre/=Hval.
        iDestruct ("Hwp" with "[$]") as "Hwp".
        iMod ("Hwp" $! (state_upd_tapes <[α:=(N; ns ++ [n]) : tape]> _) _ with "[$]").
        iModIntro. replace (0+_)%NNR with ε_now; first iFrame.
        apply nnreal_ext; simpl; lra.
    Qed.

  (** * fragmented state rand N ~ state rand M, N>=M, under equality*)
  Lemma wp_couple_fragmented_rand_rand_leq (M N:nat) ns nsₛ α αₛ e E Φ:
    (M<=N)%R ->
    to_val e = None ->
    ▷ α ↪ (N; ns) ∗ ▷ αₛ ↪ₛ (M; nsₛ) ∗
    (∀ (n : fin (S N)),
       match lt_dec (fin_to_nat n) (S M) with
       | left Hproof =>
           α ↪ (N; ns ++ [n]) ∗ αₛ ↪ₛ (M; nsₛ ++ [nat_to_fin Hproof]) -∗
           WP e @ E {{ Φ }}
       | _ =>
           α ↪ (N; ns ++ [n]) ∗ αₛ ↪ₛ (M; nsₛ) -∗
           WP e @ E {{ Φ }}
       end
    )
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (Hineq Hval) "(>Hα & >Hαₛ & Hwp)".
    assert (∀ x : fin(S M), fin_to_nat x < S N)%nat as H.
    { intros. pose proof fin_to_nat_lt x. apply INR_le in Hineq. lia. }
    pose (f := λ x, (nat_to_fin (H x))).
    assert (Inj (eq) (eq) f) as Hinj.
    { rewrite /f. intros ?? H0. apply (f_equal fin_to_nat) in H0. rewrite !fin_to_nat_to_fin in H0.
      by apply fin_to_nat_inj.
    }
    iApply (wp_couple_fragmented_rand_rand_inj _ _ f with "[$Hα $Hαₛ Hwp]"); try done.
    iIntros (n).
    case_bool_decide as H1.
    - destruct H1 as [n' <-].
      iIntros (?) "(?&?&%Hid)".
      apply Hinj in Hid as ->.
      iSpecialize ("Hwp" $! (f n')).
      case_match eqn:H'; last first.
      { exfalso.
        cut (f n' < S M)%nat; first lia.
        rewrite /f. rewrite fin_to_nat_to_fin.
        apply fin_to_nat_lt.
      }
      replace (nat_to_fin l) with (n').
      { iApply "Hwp". iFrame. }
      apply fin_to_nat_inj. rewrite fin_to_nat_to_fin. by rewrite /f fin_to_nat_to_fin.
    - iSpecialize ("Hwp" $! n).
      case_match; last iFrame.
      exfalso. apply H1. exists (nat_to_fin l). rewrite /f.
      apply fin_to_nat_inj. by rewrite !fin_to_nat_to_fin.
  Qed.

  (** * fragmented state rand N ~ state rand M, M>=N, under injective function from N to M*)
  Lemma wp_couple_fragmented_rand_rand_inj_rev  (M N:nat) (f:fin(S N) -> fin (S M)) (Hinj: Inj (=) (=) f) ns nsₛ α αₛ e E Φ:
    (N<=M)%R ->
    to_val e = None ->
    ▷ α ↪ (N; ns) ∗ ▷ αₛ ↪ₛ (M; nsₛ) ∗
    (∀ (m : fin (S M)),
       if bool_decide(∃ n, f n = m) then
         ∀ n,
       α ↪ (N; ns ++ [n]) ∗ αₛ ↪ₛ (M; nsₛ ++ [m]) ∗ ⌜f n = m⌝ -∗
       WP e @ E {{ Φ }}
     else
       α ↪ (N; ns) ∗ αₛ ↪ₛ (M; nsₛ++[m]) -∗
       WP e @ E {{ Φ }}
    )
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (Hineq Hval) "(>Hα & >Hαₛ & Hwp)".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)".
    iDestruct "Hauth2" as "(HK&Hh2&Ht2)/=".
    iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?.
    simplify_map_eq.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    replace (ε_now) with (0+ε_now)%NNR; last (apply nnreal_ext; simpl; lra).
    iApply exec_coupl_big_state_steps.
    iExists _, _, _.
    repeat iSplit.
    - iPureIntro. apply ARcoupl_exact. apply Rcoupl_swap, Rcoupl_fragmented_rand_rand_inj.
      all: exact.
    - iPureIntro. apply erasable_dbind_predicate.
      + apply dunifP_mass.
      + by eapply state_step_erasable.
      + apply dret_erasable.
    - iPureIntro. by eapply state_step_erasable.
    - simpl. iIntros (??[m H']).
      case_bool_decide as H1.
      * destruct H' as (n&?&?&?).
        destruct H1 as [n' <-].
        assert (n' = n) as -> by (by apply Hinj).
        iMod (ghost_map_update ((N; ns ++ [n]) : tape) with "Ht1 Hα") as "[Ht1 Hα]".
        iMod (ghost_map_update ((M; nsₛ ++ [f n]) : tape) with "Ht2 Hαₛ") as "[Ht2 Hαₛ]".
        iMod "Hclose'" as "_".
        iSpecialize ("Hwp" $! (f n)).
        rewrite bool_decide_eq_true_2; last naive_solver.
        iSpecialize ("Hwp" $! (n)).
        rewrite !wp_unfold/wp_pre/=Hval.
        iDestruct ("Hwp" with "[$Hα $Hαₛ]") as "Hwp"; first done.
        iMod ("Hwp" $! (state_upd_tapes <[α:=(N; ns ++ [n]) : tape]> _) _ (state_upd_tapes <[αₛ:=(M; nsₛ ++ [f n]) : tape]> _) with "[$]"). subst.
        iModIntro. replace (0+_)%NNR with ε_now; first iFrame.
        apply nnreal_ext; simpl; lra.
      * destruct H' as [??]. simplify_eq.
        iMod (ghost_map_update ((M; nsₛ ++ [m]) : tape) with "Ht2 Hαₛ") as "[Ht2 Hαₛ]".
        iMod "Hclose'" as "_".
        iSpecialize ("Hwp" $! m).
        rewrite bool_decide_eq_false_2; last done.
        rewrite !wp_unfold/wp_pre/=Hval.
        iDestruct ("Hwp" with "[$]") as "Hwp".
        iMod ("Hwp" $! _ _ (state_upd_tapes <[αₛ:=(M; nsₛ ++ [m]) : tape]> _) with "[$]").
        iModIntro. replace (0+_)%NNR with ε_now; first iFrame.
        apply nnreal_ext; simpl; lra.
  Qed.

  (** * fragmented state rand N ~ state rand M, M>=N, under injective function from N to M
      But with errors for rejection sampling! *)
  Lemma wp_couple_fragmented_rand_rand_inj_rev'  (M N:nat) (f:fin(S N) -> fin (S M)) (Hinj: Inj (=) (=) f) ns nsₛ α αₛ e E Φ ε:
    (N<M)%R ->
    to_val e = None ->
    ▷ α ↪ (N; ns) ∗ ▷ αₛ ↪ₛ (M; nsₛ) ∗ € ε ∗
    (∀ (m : fin (S M)),
       if bool_decide(∃ n, f n = m) then
         ∀ n,
       α ↪ (N; ns ++ [n]) ∗ αₛ ↪ₛ (M; nsₛ ++ [m]) ∗ ⌜f n = m⌝ -∗
       WP e @ E {{ Φ }}
     else
       ∀ (ε':nonnegreal),
       ⌜(nonneg ε' = (S M) / (S M - S N) * ε)%R⌝ ∗
       α ↪ (N; ns) ∗ αₛ ↪ₛ (M; nsₛ++[m]) ∗ € ε' -∗
       WP e @ E {{ Φ }}
    )
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (Hineq Hval) "(>Hα & >Hαₛ & Hε & Hwp)".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)".
    iDestruct "Hauth2" as "(HK&Hh2&Ht2)".
    iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %H.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iDestruct (ec_supply_bound with "[$][$]") as "%Hle".
    replace (ε_now)%NNR with (0+ε_now)%NNR at 2 by (apply nnreal_ext; simpl; lra).
    iApply exec_coupl_big_state_steps_adv_RHS.
    (** distribute errors such that if it is in domain f, get ε_now - ε, otherwise ε_now + S N/(S M - S N) ε*)
    set (ε_now1 := nnreal_minus ε_now ε Hle).
    set (ε_now2 :=  (ε_now + ε * nnreal_nat (S N) / nnreal_nat (S M - S N))%NNR).
    set (E2 σ:=if bool_decide (∃ x, σ = state_upd_tapes <[αₛ:=(M; nsₛ ++ [f x])]> σ1')
                               then ε_now1
                               else ε_now2
        ).
    iExists _, _, _, E2.
    repeat iSplit.
    - iPureIntro. apply ARcoupl_exact. apply Rcoupl_swap, Rcoupl_fragmented_rand_rand_inj.
      all: try exact.
      lra.
    - iPureIntro. exists (Rmax ε_now1 ε_now2).
      intros. rewrite /E2. case_bool_decide; split; try apply cond_nonneg.
      + apply Rmax_l.
      + apply Rmax_r.
    - iPureIntro. simpl in H. simpl. erewrite state_step_unfold; last done.
      erewrite (SeriesC_ext _
                  (λ b : state,
                     if bool_decide (b ∈ (λ x, state_upd_tapes <[αₛ:=(M; nsₛ ++ [x])]> σ1') <$> (fin_enum (S M)))
                     then /(S M) * E2 b
                     else 0
                  )%R); last first.
      { intros n.
        case_bool_decide as H1; last first.
        { apply Rmult_eq_0_compat_r.  rewrite /dmap/dbind/dbind_pmf/pmf/=.
          apply SeriesC_0. intros. apply Rmult_eq_0_compat_l.
          rewrite /dret_pmf. case_bool_decide; last lra.
          subst. exfalso. apply H1. erewrite elem_of_list_fmap.
          exists x; split; first done. replace (fin_enum (S M)) with (enum (fin (S M))) by done.
          apply elem_of_enum.
        }
        rewrite elem_of_list_fmap in H1. destruct H1 as [y [-> ?]].
        apply Rmult_eq_compat_r. rewrite /dmap/dbind/dbind_pmf/pmf/=.
        rewrite SeriesC_scal_l.
        replace (SeriesC _) with 1%R; first lra.
        symmetry.
        rewrite /dret_pmf.
        erewrite (SeriesC_ext _ (λ x, if bool_decide (x = y) then 1 else 0))%R;
          first apply SeriesC_singleton.
        intros.
        case_bool_decide as H2.
        - apply state_upd_tapes_same in H2. simplify_eq.
          case_bool_decide; done.
        - case_bool_decide; last done.
          subst. done. }
      trans (SeriesC (λ x, if bool_decide (∃ y, f y = x) then / S M * ε_now1 else / S M * ε_now2))%R.
    (** here i simplify the seriesc*)
      + set (h σ := match (ClassicalEpsilon.excluded_middle_informative
                             (∃ x, σ = state_upd_tapes <[αₛ:=(M; nsₛ ++ [x])]> σ1')
                          ) with
                    | left Hproof => Some (epsilon Hproof)
                    | _ => None
                    end
            ).
        etrans; last eapply (SeriesC_le_inj _ h).
        * apply Req_le_sym. apply SeriesC_ext. (** should be ok *)
          intros s. rewrite /h. case_match eqn:Heqn; last first.
          { rewrite bool_decide_eq_false_2; first (simpl;lra).
            erewrite elem_of_list_fmap.
            intros [? [->?]]. apply n.
            naive_solver.
          }
          pose proof epsilon_correct _ e0 as H'.
          rewrite bool_decide_eq_true_2; last first.
          { destruct e0 as [x ?]. subst. rewrite elem_of_list_fmap.
            eexists _. split; first done.
            replace (fin_enum _) with (enum (fin (S M))) by done.
            apply elem_of_enum. }
          rewrite !S_INR.
          rewrite /E2.
          simpl in *. subst.
          case_bool_decide as H1.
          -- rewrite bool_decide_eq_true_2.
             { rewrite /ε_now1. simpl; lra. }
             destruct H1 as [y ?]. exists y. rewrite H1. done.
          -- rewrite bool_decide_eq_false_2.
             { rewrite /ε_now2; simpl; lra. }
             intros [x H2].
             apply H1. rewrite H' in H2. apply state_upd_tapes_same in H2. simplify_eq.
             naive_solver.
        * intros. case_bool_decide; apply Rmult_le_pos; try apply cond_nonneg.
          all: rewrite <-Rdiv_1_l; apply Rcomplements.Rdiv_le_0_compat; try lra.
          all: apply pos_INR_S.
        * intros n1 n2 m. rewrite /h. case_match eqn:H1; case_match eqn:H2; try done.
          intros.
          pose proof epsilon_correct _ e0.
          pose proof epsilon_correct _ e1. simpl in *. simplify_eq.
          rewrite H5 H6. by repeat f_equal.
        * apply ex_seriesC_finite.
      + eset (diff:=elements (((list_to_set (enum (fin(S M)))):gset _ )∖ ((list_to_set(f<$>enum (fin(S N)))):gset _))).
        erewrite (SeriesC_ext _
                    (λ x : fin (S M), (if bool_decide (x ∈ f<$> enum (fin(S N))) then / S M * ε_now1 else 0%R) +
                                      if bool_decide (x ∈ diff ) then / S M * ε_now2 else 0%R
                 ))%R; last first.
        { (** annoying lemma again *)
          intros n. rewrite /diff.
          case_bool_decide as H1.
          - destruct H1 as [? H1]. rewrite bool_decide_eq_true_2; last first.
            + subst. apply elem_of_list_fmap_1. apply elem_of_enum.
            + subst. rewrite bool_decide_eq_false_2; first lra.
              rewrite elem_of_elements.
              rewrite not_elem_of_difference; right.
              rewrite elem_of_list_to_set. apply elem_of_list_fmap_1; apply elem_of_enum.
          - rewrite bool_decide_eq_false_2; last first.
            { rewrite elem_of_list_fmap. intros [?[??]].
              subst. apply H1. naive_solver. }
            rewrite bool_decide_eq_true_2; first lra.
            rewrite elem_of_elements. rewrite elem_of_difference.
            split; rewrite elem_of_list_to_set; first apply elem_of_enum.
            rewrite elem_of_list_fmap. intros [?[??]].
            subst. apply H1. naive_solver.
        }
        rewrite SeriesC_plus; try apply ex_seriesC_finite.
        rewrite !SeriesC_list_2; last first.
        { apply NoDup_fmap_2; [done|apply NoDup_enum]. }
        { rewrite /diff. eapply NoDup_elements. }
        rewrite fmap_length. rewrite fin.length_enum_fin.
        rewrite /diff.
        replace (length _) with (S M - S N); last first.
        { erewrite <-size_list_to_set; last apply NoDup_elements.
          erewrite list_to_set_elements.
          rewrite size_difference.
          - rewrite !size_list_to_set; [|apply NoDup_fmap; [auto|apply NoDup_enum]|apply NoDup_enum]; auto.
            rewrite fmap_length.
            rewrite !fin.length_enum_fin. done.
          - intros ??. apply elem_of_list_to_set. apply elem_of_enum.
        }
        rewrite /ε_now1 /ε_now2. simpl. rewrite -/(INR (S N)) -/(INR (S M)). rewrite !S_INR.
        rewrite !Rmult_assoc.
        rewrite minus_INR; last (apply INR_le; lra).
        cut ((N+1)/ (M + 1) * ε_now - (N+1)/(M+1) *ε+
               (M-N)/ (M + 1) * ε_now + ((N + 1)/(M+1) * ((M-N)/ (M - N))) * ε <= ε_now)%R; first lra.
        rewrite Rdiv_diag; last lra.
        cut ((N + 1) / (M + 1) * ε_now+ (M - N) / (M + 1) * ε_now <= ε_now)%R; first lra.
        cut ((M + 1) / (M + 1) * ε_now <= ε_now)%R; first lra.
        rewrite Rdiv_diag; first lra.
        pose proof pos_INR M. lra.
    - iPureIntro. apply erasable_dbind_predicate.
      + apply dunifP_mass.
      + by eapply state_step_erasable.
      + apply dret_erasable.
    - iPureIntro. by eapply state_step_erasable.
    - iIntros (??[m H']).
      case_bool_decide as H1.
      * destruct H' as (n&?&?&?).
        destruct H1 as [n' <-].
        assert (n' = n) as -> by (by apply Hinj).
        iMod (ghost_map_update ((N; ns ++ [n]) : tape) with "Ht1 Hα") as "[Ht1 Hα]".
        iMod (ghost_map_update ((M; nsₛ ++ [f n]) : tape) with "Ht2 Hαₛ") as "[Ht2 Hαₛ]".
        iMod "Hclose'" as "_".
        iSpecialize ("Hwp" $! (f n)).
        rewrite bool_decide_eq_true_2; last naive_solver.
        iSpecialize ("Hwp" $! (n)).
        rewrite !wp_unfold/wp_pre/=Hval.
        iDestruct ("Hwp" with "[$Hα $Hαₛ]") as "Hwp"; first done.
        replace (ε_now) with (ε + ε_now1)%NNR; last first.
        { apply nnreal_ext. simpl. lra. }
        iMod (ec_decrease_supply with "[$][$]") as "Hε2".
        iMod ("Hwp" $! (state_upd_tapes <[α:=(N; ns ++ [n]) : tape]> _) _ (state_upd_tapes <[αₛ:=(M; nsₛ ++ [f n]) : tape]> _) with "[$]"). subst.
        iModIntro.
        replace (E2 (state_upd_tapes <[αₛ:=(M; nsₛ ++ [f n])]> σ1')) with ε_now1; first by iApply exec_stutter_free.
        rewrite /E2. rewrite bool_decide_eq_true_2; first done.
        naive_solver.
      * destruct H' as [??]. simplify_eq.
        iMod (ghost_map_update ((M; nsₛ ++ [m]) : tape) with "Ht2 Hαₛ") as "[Ht2 Hαₛ]".
        iMod "Hclose'" as "_".
        iSpecialize ("Hwp" $! m).
        rewrite bool_decide_eq_false_2; last done.
        rewrite !S_INR. simpl.
        replace (E2 _) with (ε_now2); last first.
        { rewrite /E2. rewrite bool_decide_eq_false_2; first done.
          intros [? H2]. apply state_upd_tapes_same in H2. simplify_eq. naive_solver.
        }
        destruct (Rle_or_lt 1 ε_now2).
        { iApply fupd_mask_intro; first set_solver.
          iIntros. iApply exec_stutter_spend. done.
        }
        iMod (ec_increase_supply _ (ε * nnreal_nat (S N) / nnreal_nat (S M - S N))%NNR with "[$Hε2]") as "[Hsupply Hε']".
        { iPureIntro. eapply Rle_lt_trans; last exact. by rewrite /ε_now2. }
        iCombine "Hε Hε'" as "Hε".
        iDestruct ("Hwp" with "[$Hα $Hαₛ $Hε]") as "Hwp".
        { (** annoying maths *)
          iPureIntro. simpl. rewrite -/(INR (S N)). rewrite S_INR.
          replace (INR M + 1 - (INR N + 1))%R with (INR M - INR N)%R by lra.
          rewrite -{1}(Rmult_1_l (nonneg ε)).
          rewrite Rmult_assoc (Rmult_comm (nonneg ε)).
          rewrite -Rmult_plus_distr_r. apply Rmult_eq_compat_r.
          rewrite Rdiv_def. replace (1)%R with ((INR M - INR N)*/(INR M - INR N))%R at 1; last first.
          { apply Rinv_r. lra. }
          rewrite minus_INR; last (apply INR_le; lra).
          rewrite -Rmult_plus_distr_r. lra.
        }
        rewrite !wp_unfold/wp_pre/=Hval.
        iMod ("Hwp" $! _ _ (state_upd_tapes <[αₛ:=(M; nsₛ ++ [m]) : tape]> _) with "[$]").
        iModIntro. iApply exec_stutter_free. rewrite /ε_now2. done.
        Unshelve.
        -- apply gset_fin_set.
  Qed.

  Lemma wp_couple_fragmented_rand_rand_leq_rev'  (M N:nat)  ns nsₛ α αₛ e E Φ ε:
    (N<M)%R ->
    to_val e = None ->
    ▷ α ↪ (N; ns) ∗ ▷ αₛ ↪ₛ (M; nsₛ) ∗ € ε ∗
    (∀ (m : fin (S M)),
       match lt_dec (fin_to_nat m) (S N) with
       | left Hproof =>
           α ↪ (N; ns ++ [nat_to_fin Hproof]) ∗ αₛ ↪ₛ (M; nsₛ ++ [m])  -∗
           WP e @ E {{ Φ }}
       | _ =>
           ∀ (ε':nonnegreal),
       ⌜(nonneg ε' = (S M) / (S M - S N) * ε)%R⌝ ∗
       α ↪ (N; ns) ∗ αₛ ↪ₛ (M; nsₛ++[m]) ∗ € ε' -∗
       WP e @ E {{ Φ }}
     end
    )
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (Hineq Hval) "(>Hα & >Hαₛ & Hε & Hwp)".
    assert (∀ x : fin(S N), fin_to_nat x < S M)%nat as H.
    { intros. pose proof fin_to_nat_lt x. apply INR_lt in Hineq. lia. }
    pose (f := λ x, (nat_to_fin (H x))).
    assert (Inj (eq) (eq) f) as Hinj.
    { rewrite /f. intros ?? H0. apply (f_equal fin_to_nat) in H0. rewrite !fin_to_nat_to_fin in H0.
      by apply fin_to_nat_inj.
    }
    iApply (wp_couple_fragmented_rand_rand_inj_rev' _ _ f with "[$Hα $Hαₛ $Hε Hwp]"); try done.
    iIntros (n).
    case_bool_decide as H1.
    - destruct H1 as [n' <-].
      iIntros (?) "(?&?&%Hid)".
      apply Hinj in Hid as ->.
      iSpecialize ("Hwp" $! (f n')).
      case_match eqn:H'; last first.
      { exfalso.
        cut (f n' < S N)%nat; first lia.
        rewrite /f. rewrite fin_to_nat_to_fin.
        apply fin_to_nat_lt.
      }
      replace (nat_to_fin l) with (n').
      { iApply "Hwp". iFrame. }
      apply fin_to_nat_inj. rewrite fin_to_nat_to_fin. by rewrite /f fin_to_nat_to_fin.
    - iSpecialize ("Hwp" $! n).
      case_match; last iFrame.
      exfalso. apply H1. exists (nat_to_fin l). rewrite /f.
      apply fin_to_nat_inj. by rewrite !fin_to_nat_to_fin.
  Qed.

  (** couplings between prim step and state steps*)
  Lemma wp_couple_tape_rand N f `{Bij (fin (S N)) (fin (S N)) f} K E α z ns Φ e :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    ▷ α ↪ (N; ns) ∗ ⤇ fill K  (rand #z) ∗
    (∀ n : fin (S N), α ↪ (N; ns ++ [n]) ∗ ⤇ fill K  #(f n) -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (-> He) "(>Hα & Hj & Hwp)".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1' ε) "[[Hh1 Ht1] [Hauth2 Herr]]".
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?.
    iDestruct (spec_auth_prog_agree with "Hauth2 Hj") as %-> .
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    replace (ε) with (0+ε)%NNR by (apply nnreal_ext; simpl; lra).
    iApply (exec_coupl_state_prim α).
    { rewrite /= /get_active. apply elem_of_elements, elem_of_dom; eauto. }
    iExists
      (λ σ2 '(e2', σ2'),
        ∃ n, σ2 = state_upd_tapes <[α := (_; ns ++ [n]) : tape]> σ1
             ∧ (e2', σ2') = (fill K #(f n), σ1')).
    iSplit.
    { iPureIntro.
      apply ARcoupl_exact.
      rewrite /= -(dret_id_right (state_step _ _)) fill_dmap //.
      eapply Rcoupl_dbind => /=; last first.
      { eapply Rcoupl_pos_R. by eapply Rcoupl_state_rand. }
      intros σ2 (e2' & σ2') ((b & -> & ->) & ? & ?).
      apply Rcoupl_dret=>/=. eauto. }
    iIntros (σ2 e2' σ2' (b & -> & [= -> ->])).
    iMod (spec_update_prog (fill K #(f b)) with "Hauth2 Hj") as "[Hauth2 Hspec0]".
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?%lookup_total_correct.
    iMod (ghost_map_update ((_; ns ++ [b]) : tape) with "Ht1 Hα") as "[Ht1 Hα]".
    iMod "Hclose'" as "_".
    iSpecialize ("Hwp" with "[$]").
    rewrite !wp_unfold /wp_pre /= He.
    iMod ("Hwp" $! (state_upd_tapes <[α:=(_; ns ++ [b]) : tape]> σ1)
           with "[$Hh1 $Hauth2 $Ht1 $Herr]") as "Hwp".
    replace (_+_)%NNR with (ε) by (apply nnreal_ext; simpl; lra).
    done.
  Qed.

  (** * rand(unit, N) ~ state_step(α', N) coupling *)
  Lemma wp_couple_rand_tape N f `{Bij (fin (S N)) (fin (S N)) f} z E α ns Φ :
    TCEq N (Z.to_nat z) →
    ▷ α ↪ₛ (N; ns) ∗
    ▷ (∀ n : fin (S N), α ↪ₛ (N; ns ++ [f n]) -∗ Φ #n)
    ⊢ WP rand #z @ E {{ Φ }}.
  Proof.
    iIntros (->) "(>Hαs & Hwp)".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1' ε) "[[Hh1 Ht1] [Hauth2 Herr]]".
    iDestruct (spec_auth_lookup_tape with "Hauth2 Hαs") as %?.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    replace (ε) with (0+ε)%NNR at 2 by (apply nnreal_ext; simpl; lra).
    iApply (exec_coupl_prim_state α).
    { rewrite /= /get_active. apply elem_of_elements, elem_of_dom; eauto. }
    iExists _. iSplit.
    { iPureIntro. eapply head_prim_reducible; eauto with head_step. }
    iSplit.
    { iPureIntro. apply ARcoupl_exact. by eapply (Rcoupl_rand_state _ f). }
    iIntros (e2 σ2 σ2' (b & [=-> ->] & ->)).
    iMod (spec_auth_update_tape (_; ns ++ [f b]) with "Hauth2 Hαs") as "[Htapes Hαs]".
    do 2 iModIntro.
    iMod "Hclose'" as "_".
    iSpecialize ("Hwp" $! b with "[$Hαs]").
    iFrame.
    iModIntro.
    by iApply wp_value.
  Qed.

  (** This lemma is special because we directly use prim step prim step case.
      we need this if LHS is just a simple rand, and it reduces to a value immediately
   *)
  Lemma wp_couple_rand_rand_lbl N f `{Bij (fin (S N)) (fin (S N)) f} z K E α Φ :
    TCEq N (Z.to_nat z) →
    α ↪ₛ (N; []) ∗  ⤇ fill K (rand(#lbl:α) #z) ∗
    ▷ (∀ n : fin (S N), α ↪ₛ (N; []) ∗  ⤇ fill K #(f n) -∗ Φ #n)
    ⊢ WP rand #z @ E {{ Φ }}.
  Proof.
    iIntros (->) "(Hα & Hspec & Hwp)".
    iMod ec_zero as "Hε".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1' ε) "((Hh1 & Ht1) & Hauth2 & Hε2)".
    iDestruct (spec_auth_prog_agree with "Hauth2 Hspec") as %-> .
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    replace (ε) with (0+ε)%NNR at 2 by (apply nnreal_ext; simpl; lra).
    iApply exec_coupl_prim_steps.
    iExists (λ '(e2, σ2) '(e2', σ2'),
               ∃ (m : fin _),
                 (e2, σ2) = (Val #(m), σ1) ∧ (e2', σ2') = (fill K #(f m), σ1')).
    iSplit.
    { iPureIntro. eapply head_prim_reducible; eauto with head_step. }
    iSplit.
    { simpl.
      iDestruct (spec_auth_lookup_tape with "Hauth2 Hα") as %H0.
      erewrite prim_step_empty_tape; last done.
      iPureIntro. simpl.
      rewrite fill_dmap // -(dret_id_right (prim_step _ _)) /=.
      rewrite /dmap /=.
      replace (0)%R with (0+0)%R by lra.
      eapply ARcoupl_dbind; [done|done|..]; last first.
      - replace 0%R with (nonneg 0%NNR); last by simpl.
        apply (ARcoupl_rand_rand_inj _ _ f); try done.
        rewrite Rminus_diag. rewrite Rdiv_0_l. by simpl.
      - simpl. intros a b [? [-> ->]]. apply ARcoupl_dret. simpl.
        naive_solver.
    }
    iIntros ([] [] (b & [= -> ->] & [= -> ->])).
    simplify_eq.
    iMod (spec_update_prog (fill K #(f b)) with "Hauth2 Hspec") as "[Hauth2 Hspec0]".
    do 2 iModIntro.
    iMod "Hclose'" as "_".
    iModIntro. iFrame.
    iApply wp_value.
    iApply "Hwp"; eauto. iFrame.
  Qed.


End rules.

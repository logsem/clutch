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
    (∀ σ1, reducible e σ1) →
    nclose specN ⊆ E →
    (N <= M)%R →
    (((S M - S N) / S N) = ε)%R →
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
      iFrame. rewrite exec_O dret_1_1 //. }
    (* Our [WP] assumption with the updated resources now suffices to prove the goal *)
    iSpecialize ("Hwp" $! n m nm with "[$Hα $Hαₛ]").
    rewrite !wp_unfold /wp_pre /= He.
    iMod ("Hwp" $! (state_upd_tapes <[α:=(N; ns ++ [n]) : tape]> _)
           with "[$Hh1 $Hauth2 $Ht1 $Hε2]") as "[Hred Hwp]".
    iModIntro. done.
  Qed.

  Lemma wp_couple_tapes_rev (N M : nat) E e α αₛ ns nsₛ Φ (ε : nonnegreal) :
    to_val e = None →
    (∀ σ1, reducible e σ1) →
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
      iFrame. rewrite exec_O dret_1_1 //. }
    (* Our [WP] assumption with the updated resources now suffices to prove the goal *)
    iSpecialize ("Hwp" $! n m nm with "[$Hα $Hαₛ]").
    rewrite !wp_unfold /wp_pre /= He.
    iMod ("Hwp" $! (state_upd_tapes <[α:=(N; ns ++ [n]) : tape]> _)
           with "[$Hh1 $Hauth2 $Ht1 $Hε2]") as "[Hred Hwp]".
    iModIntro. done.
  Qed.

  Lemma wp_couple_no_coll_rand K N z E (x : Fin.t N) Φ ε :
    nclose specN ⊆ E →
    (0 < S N)%R →
    ((1 / S N) = ε)%R →
    N = Z.to_nat z →
    € ε ∗
    refines_right K (rand #z from #()) ∗
    (∀ (n : fin (S N)),
        ⌜(fin_to_nat n ≠ x)⌝ →
        refines_right K #n -∗
        WP (let: "x" := of_val #(fin_to_nat x) in "x") @ E {{ Φ }})
    ⊢ WP (let: "x" := of_val #(fin_to_nat x) in "x") @ E {{ Φ }}.
  Proof.
    iIntros (? Npos Nε Nz) "(Hε & [#Hinv Hj] &  Hwp)".
    iApply wp_lift_step_fupd_couple ; [done|].
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)".
    iInv specN as (ρ' e0' σ0' n_spec_steps) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_interp_auth_frag_agree with "Hauth2 Hspec0") as %<-.
    (* iDestruct (ghost_map_lookup with "Htapes Hαₛ") as %?. *)
    (* iDestruct (ghost_map_lookup with "Ht1 Hα") as %?. *)
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iSplitR. { (* iPureIntro. *)
               (* replace (#() ;; #x)%E with (fill [AppLCtx #()] (λ:<>, #x))%E by auto. *)
               (* apply head_prim_fill_reducible. *)
               (* eexists (_, _). *)
               (* apply head_step_support_equiv_rel. *)
               (* eapply RecS. *) admit. }
    (* Get up to speed with the spec resource (tracked in spec_ctx) *)
    iApply exec_coupl_det_r; [done|].
    (* split ε_now into ε + (ε_now - ε) *)
    iDestruct (ec_supply_bound with "Hε2 Hε") as %Hle.
    set (ε' := nnreal_minus ε_now ε Hle ).
    replace ε_now with (nnreal_plus ε ε') by (apply nnreal_ext; simpl; lra).
    iDestruct (spec_prog_auth_frag_agree with "Hauth Hj") as %->.
    From clutch.rel_logic Require Import proofmode.
    (* wp_bind #x. *)
    set (e := (let: "x" := #x in "x")%E).
    (* Unset Printing Notations. Set Printing Coercions. *)
    replace e with (fill [AppRCtx (λ:"x", "x")] (Val #x))%E by reflexivity.
    (* Do a coupled [state_step] on both sides  *)
    iApply (exec_coupl_exec_r).
  Abort.

  Lemma wp_couple_rand_no_coll K N z E (x : Fin.t N) Φ ε :
    nclose specN ⊆ E →
    (0 < S N)%R →
    ((1 / S N) = ε)%R →
    N = Z.to_nat z →
    € ε ∗
    refines_right K #x ∗
    (∀ (n : fin (S N)),
        ⌜(fin_to_nat n ≠ x)⌝ →
        refines_right K #x -∗
        WP (Val #n) @ E {{ Φ }})
    ⊢ WP (rand #z from #()) @ E {{ Φ }}.
  Proof.
    iIntros (? Npos Nε Nz) "(Hε & [#Hinv Hj] &  Hwp)".
    iApply wp_lift_step_fupd_couple ; [done|].
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)".
    iInv specN as (ρ' e0' σ0' n_spec_steps) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_interp_auth_frag_agree with "Hauth2 Hspec0") as %<-.
    (* iDestruct (ghost_map_lookup with "Htapes Hαₛ") as %?. *)
    (* iDestruct (ghost_map_lookup with "Ht1 Hα") as %?. *)
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iSplitR. { (* iPureIntro. *)
               (* replace (#() ;; #x)%E with (fill [AppLCtx #()] (λ:<>, #x))%E by auto. *)
               (* apply head_prim_fill_reducible. *)
               (* eexists (_, _). *)
               (* apply head_step_support_equiv_rel. *)
               (* eapply RecS. *) admit. }
    (* Get up to speed with the spec resource (tracked in spec_ctx) *)
    iApply exec_coupl_det_r; [done|].
    (* split ε_now into ε + (ε_now - ε) *)
    iDestruct (ec_supply_bound with "Hε2 Hε") as %Hle.
    set (ε' := nnreal_minus ε_now ε Hle ).
    replace ε_now with (nnreal_plus ε ε') by (apply nnreal_ext; simpl; lra).
    iDestruct (spec_prog_auth_frag_agree with "Hauth Hj") as %->.
    From clutch.rel_logic Require Import proofmode.
    (* wp_bind #x. *)
    set (e := (let: "x" := #x in "x")%E).
    (* Unset Printing Notations. Set Printing Coercions. *)
    replace e with (fill [AppRCtx (λ:"x", "x")] (Val #x))%E by reflexivity.
    (* Do a coupled [state_step] on both sides  *)
    iApply (exec_coupl_exec_r).

  Abort.

  (** * rand(unit, N) ~ rand(unit, M) coupling, N <= M, under equality *)
  Lemma wp_couple_rand_rand_leq (N M : nat) z w K E Φ (ε : nonnegreal) :
    TCEq N (Z.to_nat z) →
    TCEq M (Z.to_nat w) →
    nclose specN ⊆ E →
    (N <= M)%R ->
    (((S M - S N) / S N) = ε)%R →
    refines_right K (rand #w from #()) ∗
    € ε ∗
    ▷ (∀ (n : fin (S N)) (m : fin (S M)),
        ⌜(fin_to_nat n = m)⌝ →
        refines_right K #m  -∗ WP (Val #n) @ E {{ Φ }})
    ⊢ WP rand #z from #() @ E {{ Φ }}.
  Proof.
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
        ∃ (n : fin _) (m : fin _),
        (fin_to_nat n = m) ∧
        (e2, σ2) = (Val #n, σ1) ∧ (e2', σ2') = (fill K #m, σ0')).
    iSplit.
    { iPureIntro. apply head_prim_reducible.
      eexists (Val #0%fin, σ1).
      apply head_step_support_equiv_rel.
      by eapply (RandNoTapeS _ _ 0%fin). }
    iSplit.
    { iPureIntro. simpl.
      rewrite fill_dmap // -(dret_id_right (prim_step _ _)) /=.
      rewrite /dmap /=.
      replace ε with (nnreal_plus ε nnreal_zero); last first.
      { apply nnreal_ext; simpl; lra. }
      eapply ARcoupl_dbind.
      1,2:apply cond_nonneg.
      2:eapply ARcoupl_rand_rand; eauto.
      intros [] [] (b & ? & ? & [=] & [=])=>/=.
      apply ARcoupl_dret.
      simplify_eq. eauto. }
    iIntros ([] [] (b & b' & Hbb' & [= -> ->] & [= -> ->])).
    simplify_eq.
    iMod (spec_interp_update (fill K #b', σ0') with "Hauth2 Hspec0") as "[Hauth2 Hspec0]".
    iMod (spec_prog_update (fill K #b')  with "Hauth Hr") as "[Hauth Hr]".
    iMod (ec_decrease_supply with "Hε2 Hε") as "Hε2".
    do 2 iModIntro.
    iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hauth Hheap Hspec0 Htapes]") as "_".
    { iModIntro. rewrite /spec_inv.
      iExists _, _, _, 0. simpl.
      iFrame. rewrite exec_O dret_1_1 //. }
    iModIntro. iFrame.
    iApply "Hwp"; eauto.
    iSplit; done.
  Qed.


  (** * rand(unit, N) ~ rand(unit, M) coupling, M <= N, along an injection *)
  Lemma wp_couple_rand_rand_rev_inj (N M : nat) f `{Inj (fin (S M)) (fin (S N)) (=) (=) f } z w K E Φ (ε : nonnegreal) :
    TCEq N (Z.to_nat z) →
    TCEq M (Z.to_nat w) →
    nclose specN ⊆ E →
    (M <= N)%R ->
    (((S N - S M) / S N) = ε)%R →
    refines_right K (rand #w from #()) ∗
    € ε ∗
    ▷ (∀ (m : fin (S M)),
        refines_right K #m  -∗ WP (Val #(f m)) @ E {{ Φ }})
    ⊢ WP rand #z from #() @ E {{ Φ }}.
  Proof.
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
        (e2, σ2) = (Val #(f m), σ1) ∧ (e2', σ2') = (fill K #m, σ0')).
    iSplit.
    { iPureIntro. apply head_prim_reducible.
      eexists (Val #0%fin, σ1).
      apply head_step_support_equiv_rel.
      by eapply (RandNoTapeS _ _ 0%fin). }
    iSplit.
    { iPureIntro. simpl.
      rewrite fill_dmap // -(dret_id_right (prim_step _ _)) /=.
      rewrite /dmap /=.
      replace ε with (nnreal_plus ε nnreal_zero); last first.
      { apply nnreal_ext; simpl; lra. }
      eapply ARcoupl_dbind.
      1,2:apply cond_nonneg.
      2:eapply ARcoupl_rand_rand_rev_inj; eauto.
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
      iFrame. rewrite exec_O dret_1_1 //. }
    iModIntro. iFrame.
    iApply "Hwp"; eauto.
    iSplit; done.
  Qed.





End rules.

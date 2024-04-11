(** Rules for updating the specification program. *)
From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext.
From clutch.app_rel_logic Require Import lifting ectx_lifting.
From clutch.prob_lang Require Import lang notation tactics metatheory exec_lang.
From clutch.app_rel_logic Require Export spec_ra.
From clutch.app_rel_logic Require Export app_weakestpre primitive_laws.

Section rules.
  Context `{!app_clutchGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types v : val.
  Implicit Types l : loc.

  (** Pure reductions *)
  Lemma step_pure E K e e' (P : Prop) n:
    P →
    PureExec P n e e' →
    ⤇ fill K e ⊢ spec_update E (⤇ fill K e').
  Proof.
    iIntros (HP Hex) "HK". 
    rewrite /spec_update.
    iIntros ([??]) "Hs".
    iDestruct (spec_interp_auth_frag_agree_expr with "[$][$]") as "->".
    iMod (spec_interp_update _ _ _ (fill K e') with "[$][$]") as "[HK Hs]".
    iModIntro. iExists _, n. iFrame. iPureIntro.
    epose proof (exec_PureExec_ctx (fill K) P 0%nat _ _ _ _ s HP Hex _). done.
    Unshelve.
    rewrite pexec_O. by apply dret_1_1.
  Qed.
    
  (** Alloc, load, and store *)
  Lemma step_alloc E K e v :
    IntoVal e v →
    ⤇ fill K (ref e) ⊢ spec_update E (∃ l,  ⤇ fill K (#l) ∗ l ↦ₛ v).
  Proof.
    iIntros (<-) "HK". rewrite /spec_update.
    iIntros ([? σ]) "Hs".
    iDestruct (spec_interp_auth_frag_agree_expr with "[$][$]") as "->".
    set (l := fresh_loc σ.(heap)).
    iMod (spec_interp_update _ _ _ (fill K #l) with "[$][$]") as "[HK Hs]".
    iDestruct "HK" as "(HK&Hheap&Htapes)".
    iMod (ghost_map_insert l v with "[$]") as "[Hheap Hl]".
    { apply not_elem_of_dom, fresh_loc_is_fresh. }
    iModIntro. iExists (fill K #l, state_upd_heap <[l:=v]> σ), 1.
    iFrame.
    iSplit; last first.
    { iExists _. iFrame. }
    iPureIntro.
    eapply exec_det_step_ctx; [apply _| |]; last first.
    { simpl. rewrite pexec_O. by apply dret_1_1. }
    subst l. solve_step. apply dret_1_1.
    rewrite state_upd_heap_singleton. done. 
  Qed.

  Lemma step_load E K l q v:
    ⤇ fill K (!#l) ∗ l ↦ₛ{q} v
    ⊢ spec_update E (⤇ fill K (of_val v) ∗ l ↦ₛ{q} v).
  Proof.
    iIntros "[HK Hl]". rewrite /spec_update.
    iIntros ([? σ]) "Hs".
    iDestruct (spec_interp_auth_frag_agree_expr with "[$][$]") as "->".
    iMod (spec_interp_update _ _ _ (fill K v) with "[$][$]") as "[Hauth Hj]".
    iDestruct "Hauth" as "(HK&Hheap&Htapes)".
    iDestruct (ghost_map_lookup with "Hheap Hl") as %?.
    iModIntro. iExists _, _. iFrame.
    iPureIntro. 
    eapply exec_det_step_ctx; [apply _| |]; last first.
    { simpl. erewrite pexec_O. by apply dret_1_1. }
    solve_step.
    Qed. 

  Lemma step_store E K l v' e v:
    IntoVal e v →
    ⤇ fill K (#l <- e) ∗ l ↦ₛ v'
    ⊢ spec_update E (⤇ fill K #() ∗ l ↦ₛ v).
  Proof.
    iIntros (<-) "[HK Hl]". rewrite /spec_update.
    iIntros ([? σ]) "Hs".
    iDestruct (spec_interp_auth_frag_agree_expr with "[$][$]") as "->".
    iMod (spec_interp_update _ _ _ (fill K #()) with "[$][$]") as "[Hauth Hj]".
    iDestruct "Hauth" as "(HK&Hheap&Htapes)".
    iDestruct (ghost_map_lookup with "Hheap Hl") as %?.
    iMod (ghost_map_update v with "Hheap Hl") as "[Hheap Hl]".
    iModIntro. iExists (fill K #(), state_upd_heap <[l:=v]> σ), _.
    iFrame.
    iPureIntro.
    eapply exec_det_step_ctx; [apply _| |]; last first.
    { simpl. erewrite pexec_O. by apply dret_1_1. }
    solve_step.
  Qed.

  (** AllocTape and Rand (non-empty tape)  *)
  Lemma step_alloctape E K N z :
    TCEq N (Z.to_nat z) →
    ⤇ fill K (alloc #z) ⊢ spec_update E (∃ l, ⤇ fill K (#lbl: l) ∗ l ↪ₛ (N; [])).
  Proof.
    iIntros (->) "HK". rewrite /spec_update.
    iIntros ([? σ]) "Hs".
    iDestruct (spec_interp_auth_frag_agree_expr with "[$][$]") as "->".
    iMod (spec_interp_update _ _ _(fill K #(LitLbl (fresh_loc σ.(tapes)))) with "[$] [$]") as "[Hauth Hj]".
    iDestruct "Hauth" as "(HK&Hheap&Htapes)".
    iMod (ghost_map_insert (fresh_loc σ.(tapes)) ((_; []) : tape) with "Htapes") as "[Htapes Hl]".
    { apply not_elem_of_dom, fresh_loc_is_fresh. }
    iModIntro. iExists (fill K #lbl:(fresh_loc (tapes σ)), (state_upd_tapes <[fresh_loc σ.(tapes):=_]> σ)), 1.
    iFrame.
    iSplit; last first.
    { iExists _. iFrame. }
    iPureIntro.
    eapply exec_det_step_ctx; [apply _| |]; last first.
    { simpl. rewrite pexec_O. by apply dret_1_1. }
    solve_step. apply dret_1_1. done. 
  Qed.


  Lemma step_rand E K l N z n ns :
    TCEq N (Z.to_nat z) →
    ⤇ fill K (rand(#lbl:l) #z) ∗ l ↪ₛ (N; n :: ns)
    ⊢ spec_update E (⤇ fill K #n ∗ l ↪ₛ (N; ns)).
  Proof.
    iIntros (->) "[HK Hl]".
    rewrite /spec_update.
    iIntros ([? σ]) "Hs".
    iDestruct (spec_interp_auth_frag_agree_expr with "[$][$]") as "->".
    iMod (spec_interp_update _ _ _(fill K #n) with "[$] [$]") as "[Hauth Hj]".
    iDestruct "Hauth" as "(HK&Hheap&Htapes)".
    iDestruct (ghost_map_lookup with "Htapes Hl") as %?.
    iMod (ghost_map_update ((_; ns) : tape) with "Htapes Hl") as "[Htapes Hl]".
    iModIntro. iExists (fill K #n, (state_upd_tapes <[l:=_]> σ)), 1.
    iFrame.
    iPureIntro.
    eapply exec_det_step_ctx; [apply _| |]; last first.
    { simpl. rewrite pexec_O. by apply dret_1_1. }
    solve_step. case_bool_decide; last lia. apply dret_1_1. done. 
  Qed.    
    


  (* TODO: Can we get this as a lifting of the corresponding exact relational rule? *)

  (** RHS [rand] *)
  Lemma wp_rand_r N z E e K Φ :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (∀ σ1, reducible (e, σ1)) →
    ⤇ fill K (rand #z) ∗
    (∀ n : fin (S N), ⤇ fill K #n -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (-> He Hred) "( Hj & Hwp)".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1' ε) "[[Hh1 Ht1] [Hauth2 Herr]]".
    iDestruct (spec_interp_auth_frag_agree_expr with "[$][$]") as "->".
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    replace (ε) with (nnreal_plus nnreal_zero ε)
      by by apply nnreal_ext => /=; lra.
    iApply (exec_coupl_exec_r).
    iExists (λ _ '(e2', σ2'), ∃ n : fin (S (Z.to_nat z)), (e2', σ2') = (fill K #n, σ1')), 1.
    iSplit.
    { iPureIntro.
      rewrite pexec_1.
      replace nnreal_zero with (nnreal_plus nnreal_zero nnreal_zero)
                               by by apply nnreal_ext => /= ; lra.
      rewrite step_or_final_no_final /=; [|by apply to_final_None_2, fill_not_val].
      rewrite -(dret_id_right (dret _)) fill_dmap //.
      eapply ARcoupl_dbind => /=.
      1,2: simpl ; lra.
      2: by eapply ARcoupl_rand_r.
      intros [e2 σ2] (e2' & σ2') (? & [= -> ->] & [= -> ->]).
      apply ARcoupl_dret => /=. eauto. }
    iIntros (σ2 e2' (n & [= -> ->])).
    iMod (spec_interp_update _ _ _ (fill K #n) with "Hauth2 Hj") as "[Hspec Hspec0]".
    simpl.                      (*     simplify_map_eq. *)
    iMod "Hclose'" as "_".
    (* iMod ("Hclose" with "[Hauth Hheap Hspec0 Htapes]") as "_". *)
    (* { iModIntro. rewrite /spec_inv. *)
    (*   iExists _, _, _, 0. simpl. *)
    (*   iFrame. rewrite pexec_O dret_1_1 //. } *)
    iSpecialize ("Hwp" with "Hspec0").
    rewrite !wp_unfold /wp_pre /= He.
    iMod ("Hwp" $! _ with "[$Hh1 $Hspec $Ht1 $Herr]") as "Hwp".
    replace (nnreal_plus nnreal_zero ε) with (ε)
      by by apply nnreal_ext => /= ; lra.
    iModIntro.
    done.
  Qed.

  (** RHS [rand(α)] with empty tape  *)
  Lemma wp_rand_empty_r N z E e K α Φ :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (∀ σ1, reducible (e, σ1)) →
    ⤇ fill K (rand(#lbl:α) #z) ∗ α ↪ₛ (N; []) ∗
    ((α ↪ₛ (N; []) ∗ ∃ n : fin (S N), ⤇ fill K #n) -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (-> He Hred HE) "(#Hinv & Hj & Hα & Hwp)".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1' ε) "[[Hh1 Ht1] [Hauth2 Herr]]".
    iInv specN as (ρ' e0' σ0' m) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_interp_auth_frag_agree with "Hauth2 Hspec0") as %<-.
    iDestruct (ghost_map_lookup with "Htapes Hα") as %Hαsome.
    iDestruct (spec_prog_auth_frag_agree with "Hauth Hj") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    replace (ε) with (nnreal_plus nnreal_zero ε)
      by by apply nnreal_ext => /=; lra.
    iApply exec_coupl_det_r; [done|].
    (* Do a (trivially) coupled [prim_step] on the right *)
    iApply (exec_coupl_exec_r).
    iExists (λ _ '(e2', σ2'), ∃ n : fin (S _), (e2', σ2') = (fill K #n, σ0')), 1.
    iSplit.
    { iPureIntro.
      rewrite pexec_1.
      replace nnreal_zero with (nnreal_plus nnreal_zero nnreal_zero)
                               by by apply nnreal_ext => /= ; lra.
      rewrite step_or_final_no_final /=; [|by apply to_final_None_2, fill_not_val].
      rewrite -(dret_id_right (dret _)) fill_dmap //.
      eapply ARcoupl_dbind => /=.
      1,2: simpl; lra.
      2: by eapply ARcoupl_rand_empty_r.
      intros [e2 σ2] (e2' & σ2') (? & [= -> ->] & [= -> ->]).
      apply ARcoupl_dret=>/=. eauto. }
    iIntros (σ2 e2' (n & [= -> ->])).
    iMod (spec_interp_update (fill K #n, σ0') with "Hauth2 Hspec0") as "[Hspec Hspec0]".
    iMod (spec_prog_update (fill K #n) with "Hauth Hj") as "[Hauth Hj]".
    simplify_map_eq.
    iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hauth Hheap Hspec0 Htapes]") as "_".
    { iModIntro. rewrite /spec_inv.
      iExists _, _, _, 0. simpl.
      iFrame. rewrite pexec_O dret_1_1 //. }
    iSpecialize ("Hwp" with "[$Hα $Hinv Hj]"); [eauto|].
    rewrite !wp_unfold /wp_pre /= He.
    iMod ("Hwp" $! _ with "[$Hh1 $Hspec $Ht1 $Herr]") as "Hwp".
    replace (nnreal_plus nnreal_zero ε) with (ε)
      by by apply nnreal_ext => /= ; lra.
    iModIntro.
    done.
  Qed.

    (** RHS [rand(α)] with wrong tape  *)
  Lemma wp_rand_wrong_tape_r N M z E e K α Φ ns :
    TCEq N (Z.to_nat z) →
    N ≠ M →
    to_val e = None →
    (∀ σ1, reducible (e, σ1)) →
    nclose specN ⊆ E →
    spec_ctx ∗ ⤇ fill K (rand(#lbl:α) #z) ∗ α ↪ₛ (M; ns) ∗
    ((α ↪ₛ (M; ns) ∗ spec_ctx ∗ ∃ n : fin (S N), ⤇ fill K #n) -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (-> Hneq He Hred HE) "(#Hinv & Hj & Hα & Hwp)".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1' ε) "[[Hh1 Ht1] [Hauth2 Herr]]".
    iInv specN as (ρ' e0' σ0' m) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_interp_auth_frag_agree with "Hauth2 Hspec0") as %<-.
    iDestruct (ghost_map_lookup with "Htapes Hα") as %Hαsome.
    iDestruct (spec_prog_auth_frag_agree with "Hauth Hj") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    replace (ε) with (nnreal_plus nnreal_zero ε)
      by by apply nnreal_ext => /=; lra.
    iApply exec_coupl_det_r; [done|].
    (* Do a (trivially) coupled [prim_step] on the right *)
    iApply (exec_coupl_exec_r).
    iExists (λ _ '(e2', σ2'), ∃ n : fin (S _), (e2', σ2') = (fill K #n, σ0')), 1.
    iSplit.
    { iPureIntro.
      rewrite pexec_1.
      replace nnreal_zero with (nnreal_plus nnreal_zero nnreal_zero)
                               by by apply nnreal_ext => /= ; lra.
      rewrite step_or_final_no_final /=; [|by apply to_final_None_2, fill_not_val].
      rewrite -(dret_id_right (dret _)) fill_dmap //.
      eapply ARcoupl_dbind => /=.
      1,2: simpl; lra.
      2: by eapply ARcoupl_rand_wrong_r.
      intros [e2 σ2] (e2' & σ2') (? & [= -> ->] & [= -> ->]).
      apply ARcoupl_dret=>/=. eauto.
    }
    iIntros (σ2 e2' (n & [= -> ->])).
    iMod (spec_interp_update (fill K #n, σ0') with "Hauth2 Hspec0") as "[Hspec Hspec0]".
    iMod (spec_prog_update (fill K #n) with "Hauth Hj") as "[Hauth Hj]".
    simplify_map_eq.
    iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hauth Hheap Hspec0 Htapes]") as "_".
    { iModIntro. rewrite /spec_inv.
      iExists _, _, _, 0. simpl.
      iFrame. rewrite pexec_O dret_1_1 //. }
    iSpecialize ("Hwp" with "[$Hα $Hinv Hj]"); [eauto|].
    rewrite !wp_unfold /wp_pre /= He.
    iMod ("Hwp" $! _ with "[$Hh1 $Hspec $Ht1 $Herr]") as "Hwp".
    replace (nnreal_plus nnreal_zero ε) with (ε)
      by by apply nnreal_ext => /= ; lra.
    iModIntro.
    done.
  Qed.

  (** * Corollaries about [refines_right]  *)
  Lemma refines_right_alloctape E K N z :
    TCEq N (Z.to_nat z) →
    nclose specN ⊆ E →
    refines_right K (alloc #z) ⊢ |={E}=> ∃ l, refines_right K (#lbl: l) ∗ l ↪ₛ (N; []).
  Proof.
    iIntros (??) "(?&?)".
    iMod (step_alloctape with "[$]") as (l) "(?&?)"; [done|].
    iExists _; by iFrame.
  Qed.

  Lemma refines_right_rand E K l N z n ns :
    TCEq N (Z.to_nat z) →
    nclose specN ⊆ E →
    l ↪ₛ (N; n :: ns) ∗
    refines_right K (rand(#lbl:l) #z ) ⊢ |={E}=> refines_right K #n ∗ l ↪ₛ (N; ns).
  Proof.
    iIntros (??) "(?&?&?)".
    iMod (step_rand with "[$]") as "(?&?&?)"; [done|].
    iModIntro; iFrame.
  Qed.

  Lemma refines_right_bind K' K e :
    refines_right K' (fill K e) ≡ refines_right (K ++ K') e.
  Proof. rewrite /refines_right /=. by rewrite fill_app. Qed.

End rules.

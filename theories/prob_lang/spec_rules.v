(** Rules for updating the specification program. *)
From stdpp Require Import namespaces.
From self.prelude Require Import stdpp_ext.
From iris.proofmode Require Import proofmode.
From self.program_logic Require Import language ectx_language exec weakestpre lifting.
From self.prob_lang Require Import locations notation tactics primitive_laws spec_ra metatheory lang.

Section rules.
  Context `{!clutchGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types v : val.
  Implicit Types l : loc.

  (** Pure reductions *)
  Lemma step_pure E K e e' (P : Prop) n :
    P →
    PureExec P n e e' →
    nclose specN ⊆ E →
    spec_ctx ∗ ⤇ fill K e ={E}=∗ spec_ctx ∗ ⤇ fill K e'.
  Proof.
    iIntros (HP Hex ?) "[#Hspec Hj]". iFrame "Hspec".
    iInv specN as (ρ e0 σ0 m) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_prog_auth_frag_agree with "Hauth Hj") as %->.
    iMod (spec_prog_update (fill K e') with "Hauth Hj") as "[Hauth Hj]".
    iFrame "Hj". iApply "Hclose". iNext.
    iExists _, _, _, (m + n).
    iFrame.
    iPureIntro.
    by eapply (exec_PureExec_ctx (fill K) P).
  Qed.

  (** Alloc, load, and store *)
  Lemma step_alloc E K e v :
    IntoVal e v →
    nclose specN ⊆ E →
    spec_ctx ∗ ⤇ fill K (ref e) ={E}=∗ ∃ l, spec_ctx ∗ ⤇ fill K (#l) ∗ l ↦ₛ v.
  Proof.
    iIntros (<-?) "[#Hinv Hj]". iFrame "Hinv".
    iInv specN as (ρ e σ m) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_prog_auth_frag_agree with "Hauth Hj") as %->.
    set (l := fresh_loc σ.(heap)).
    iMod (spec_prog_update (fill K #l) with "Hauth Hj") as "[Hauth Hj]".
    iMod (ghost_map_insert l v with "Hheap") as "[Hheap Hl]".
    { apply not_elem_of_dom, fresh_loc_is_fresh. }
    iExists l. iFrame. iMod ("Hclose" with "[-]"); [|done].
    iModIntro. rewrite /spec_inv.
    iExists _, _, (state_upd_heap <[l:=v]> σ), _.
    iFrame. iPureIntro.
    eapply exec_det_step_ctx; [apply _| |done].
    subst l.
    solve_step.
  Qed.

  Lemma step_load E K l q v:
    nclose specN ⊆ E →
    spec_ctx ∗ ⤇ fill K (!#l) ∗ l ↦ₛ{q} v
    ={E}=∗ spec_ctx ∗ ⤇ fill K (of_val v) ∗ l ↦ₛ{q} v.
  Proof.
    iIntros (?) "(#Hinv & Hj & Hl)". iFrame "Hinv".
    iInv specN as (ρ e σ m) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_prog_auth_frag_agree with "Hauth Hj") as %->.
    iMod (spec_prog_update (fill K v) with "Hauth Hj") as "[Hauth Hj]".
    iDestruct (ghost_map_lookup with "Hheap Hl") as %?.
    iFrame. iMod ("Hclose" with "[-]"); [|done].
    iModIntro. iExists _, _, _, _.
    iFrame. iPureIntro.
    eapply exec_det_step_ctx; [apply _| |done].
    solve_step.
  Qed.

  Lemma step_store E K l v' e v:
    IntoVal e v →
    nclose specN ⊆ E →
    spec_ctx ∗ ⤇ fill K (#l <- e) ∗ l ↦ₛ v'
    ={E}=∗ spec_ctx ∗ ⤇ fill K #() ∗ l ↦ₛ v.
  Proof.
    iIntros (<-?) "(#Hinv & Hj & Hl)". iFrame "Hinv".
    iInv specN as (ρ e σ m) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_prog_auth_frag_agree with "Hauth Hj") as %->.
    iMod (spec_prog_update (fill K #()) with "Hauth Hj") as "[Hauth Hj]".
    iDestruct (ghost_map_lookup with "Hheap Hl") as %?.
    iMod (ghost_map_update v with "Hheap Hl") as "[Hheap Hl]".
    iFrame. iMod ("Hclose" with "[-]"); [|done].
    iModIntro. iExists _, _, (state_upd_heap <[l:=v]> σ), _.
    iFrame. iPureIntro.
    eapply exec_det_step_ctx; [apply _| |done].
    solve_step.
  Qed.

  (** AllocTape and Rand (non-empty tape)  *)
  Lemma step_alloctape E K N z :
    TCEq N (Z.to_nat z) →
    nclose specN ⊆ E →
    spec_ctx ∗ ⤇ fill K (alloc #z) ={E}=∗ ∃ l, spec_ctx ∗ ⤇ fill K (#lbl: l) ∗ l ↪ₛ (N; []).
  Proof.
    iIntros (-> ?) "[#Hinv Hj]". iFrame "Hinv".
    iInv specN as (ρ e σ m) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_prog_auth_frag_agree with "Hauth Hj") as %->.
    iMod (spec_prog_update (fill K #(LitLbl (fresh_loc σ.(tapes)))) with "Hauth Hj") as "[Hauth Hj]".
    iMod (ghost_map_insert (fresh_loc σ.(tapes)) ((_; []) : tape) with "Htapes") as "[Htapes Hl]".
    { apply not_elem_of_dom, fresh_loc_is_fresh. }
    iExists (fresh_loc σ.(tapes)).
    iFrame. iMod ("Hclose" with "[-]"); [|done].
    iModIntro.
    iExists _, _, (state_upd_tapes <[fresh_loc σ.(tapes):=_]> σ), _.
    iFrame. iPureIntro.
    eapply exec_det_step_ctx; [apply _| |done].
    (* TODO: fix tactic *)
    solve_step.
    by apply dret_1_1.
  Qed.

  Lemma step_rand E K l N z n ns :
    TCEq N (Z.to_nat z) →
    nclose specN ⊆ E →
    spec_ctx ∗ ⤇ fill K (rand #z from #lbl:l) ∗ l ↪ₛ (N; n :: ns)
    ={E}=∗ spec_ctx ∗ ⤇ fill K #n ∗ l ↪ₛ (N; ns).
  Proof.
    iIntros (-> ?) "(#Hinv & Hj & Hl)". iFrame "Hinv".
    iInv specN as (ρ e σ m) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_prog_auth_frag_agree with "Hauth Hj") as %->.
    iMod (spec_prog_update (fill K #n) with "Hauth Hj") as "[Hauth Hj]".
    iDestruct (ghost_map_lookup with "Htapes Hl") as %?.
    iMod (ghost_map_update ((_; ns) : tape) with "Htapes Hl") as "[Htapes Hl]".
    iFrame. iMod ("Hclose" with "[-]"); [|done].
    iModIntro. iExists _, _, (state_upd_tapes <[l:=_]> σ), _.
    iFrame. iPureIntro.
    eapply exec_det_step_ctx; [apply _| |done].
    (* TODO: fix tactic *)
    solve_step.
    rewrite bool_decide_eq_true_2 //.
    by apply dret_1_1.
  Qed.


  (** * RHS [rand(α)] with empty tape  *)
  Lemma wp_rand_empty_r N z E e K α Φ :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    nclose specN ⊆ E →
    spec_ctx ∗ ⤇ fill K (rand #z from #lbl:α) ∗ α ↪ₛ (N; []) ∗
    ((α ↪ₛ (N; []) ∗ spec_ctx ∗ ∃ n : fin (S N), ⤇ fill K #n) -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (-> He HE) "(#Hinv & Hj & Hα & Hwp)".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1') "[[Hh1 Ht1] Hauth2]".
    iInv specN as (ρ' e0' σ0' m) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_interp_auth_frag_agree with "Hauth2 Hspec0") as %<-.
    iDestruct (ghost_map_lookup with "Htapes Hα") as %Hαsome.
    iDestruct (spec_prog_auth_frag_agree with "Hauth Hj") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iApply exec_coupl_det_r; [done|].
    (* Do a (trivially) coupled [prim_step] on the right *)
    iApply (exec_coupl_exec_r).
    iExists (λ _ '(e2', σ2'), ∃ n : fin (S _), (e2', σ2') = (fill K #n, σ0')), 1.
    iSplit.
    { iPureIntro.
      rewrite exec_1.
      rewrite prim_step_or_val_no_val /=; [|by apply fill_not_val].
      rewrite -(dret_id_right (dret _)) fill_dmap //.
      eapply Rcoupl_dbind => /=; [|by eapply Rcoupl_rand_empty_r].
      intros [e2 σ2] (e2' & σ2') (? & [= -> ->] & [= -> ->]).
      apply Rcoupl_dret=>/=. eauto. }
    iIntros (σ2 e2' (n & [= -> ->])).
    iMod (spec_interp_update (fill K #n, σ0') with "Hauth2 Hspec0") as "[Hspec Hspec0]".
    iMod (spec_prog_update (fill K #n) with "Hauth Hj") as "[Hauth Hj]".
    simplify_map_eq.
    iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hauth Hheap Hspec0 Htapes]") as "_".
    { iModIntro. rewrite /spec_inv.
      iExists _, _, _, 0. simpl.
      iFrame. rewrite exec_O dret_1_1 //. }
    iSpecialize ("Hwp" with "[$Hα $Hinv Hj]"); [eauto|].
    rewrite !wp_unfold /wp_pre /= He.
    by iMod ("Hwp" $! _ with "[$Hh1 $Hspec $Ht1]") as "Hwp".
  Qed.

    (** * RHS [rand(α)] with wrong tape  *)
  Lemma wp_rand_wrong_tape_r N M z E e K α Φ ns :
    TCEq N (Z.to_nat z) →
    N ≠ M →
    to_val e = None →
    nclose specN ⊆ E →
    spec_ctx ∗ ⤇ fill K (rand #z from #lbl:α) ∗ α ↪ₛ (M; ns) ∗
    ((α ↪ₛ (M; ns) ∗ spec_ctx ∗ ∃ n : fin (S N), ⤇ fill K #n) -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (-> ? He HE) "(#Hinv & Hj & Hα & Hwp)".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1') "[[Hh1 Ht1] Hauth2]".
    iInv specN as (ρ' e0' σ0' m) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_interp_auth_frag_agree with "Hauth2 Hspec0") as %<-.
    iDestruct (ghost_map_lookup with "Htapes Hα") as %Hαsome.
    iDestruct (spec_prog_auth_frag_agree with "Hauth Hj") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iApply exec_coupl_det_r; [done|].
    (* Do a (trivially) coupled [prim_step] on the right *)
    iApply (exec_coupl_exec_r).
    iExists (λ _ '(e2', σ2'), ∃ n : fin (S _), (e2', σ2') = (fill K #n, σ0')), 1.
    iSplit.
    { iPureIntro.
      rewrite exec_1.
      rewrite prim_step_or_val_no_val /=; [|by apply fill_not_val].
      rewrite -(dret_id_right (dret _)) fill_dmap //.
      eapply Rcoupl_dbind => /=; [|by eapply Rcoupl_rand_wrong_r].
      intros [e2 σ2] (e2' & σ2') (? & [= -> ->] & [= -> ->]).
      apply Rcoupl_dret=>/=. eauto. }
    iIntros (σ2 e2' (n & [= -> ->])).
    iMod (spec_interp_update (fill K #n, σ0') with "Hauth2 Hspec0") as "[Hspec Hspec0]".
    iMod (spec_prog_update (fill K #n) with "Hauth Hj") as "[Hauth Hj]".
    simplify_map_eq.
    iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hauth Hheap Hspec0 Htapes]") as "_".
    { iModIntro. rewrite /spec_inv.
      iExists _, _, _, 0. simpl.
      iFrame. rewrite exec_O dret_1_1 //. }
    iSpecialize ("Hwp" with "[$Hα $Hinv Hj]"); [eauto|].
    rewrite !wp_unfold /wp_pre /= He.
    by iMod ("Hwp" $! _ with "[$Hh1 $Hspec $Ht1]") as "Hwp".
  Qed.

  (** * Corollaries about [refines_right]  *)
  Lemma refines_right_alloctape E K N z :
    TCEq N (Z.to_nat z) →
    nclose specN ⊆ E →
    refines_right K (alloc #z) ={E}=∗ ∃ l, refines_right K (#lbl: l) ∗ l ↪ₛ (N; []).
  Proof.
    iIntros (??) "(?&?)".
    iMod (step_alloctape with "[$]") as (l) "(?&?)"; [done|].
    iExists _; by iFrame.
  Qed.

  Lemma refines_right_rand E K l N z n ns :
    TCEq N (Z.to_nat z) →
    nclose specN ⊆ E →
    l ↪ₛ (N; n :: ns) -∗
    refines_right K (rand #z from #lbl:l) ={E}=∗ refines_right K #n ∗ l ↪ₛ (N; ns).
  Proof.
    iIntros (??) "? (?&?)".
    iMod (step_rand with "[$]") as "(?&?&?)"; [done|].
    iModIntro; iFrame.
  Qed.

  (* This is extremely similar to wp_flip_empty_r. *)
  Lemma wp_flipU_r E e K Φ :
    to_val e = None →
    nclose specN ⊆ E →
    spec_ctx ∗ ⤇ fill K (flip #()) ∗
    ((spec_ctx ∗ ∃ b : bool, ⤇ fill K #b) -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (He HE) "(#Hinv & Hj & Hwp)".
    (* Idea: Perform a [prim_step] on the right, via FlipTapeEmptyS. *)
    (* We do not want to execute a [prim_step] on the left. We merely rely on
    the fact that we *could* step (because to_val e = None) in order to appeal
    to [Hwp]. *)
    iApply lifting.wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1') "[[Hh1 Ht1] Hspec]".
    iInv specN as (ρ' e0' σ0' n) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_interp_auth_frag_agree with "Hspec Hspec0") as %<-.
    iDestruct (spec_prog_auth_frag_agree with "Hauth Hj") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iApply exec_coupl_det_r; [done|].
    (* Do a coupled [prim_step] on the right *)
    iApply (exec_coupl_exec_r).
    iExists (λ _ '(e2', σ2'), ∃ (b : bool), (e2', σ2') = (fill K #b, σ0')).
    iExists 1.
    iSplit.
    { iPureIntro.
      rewrite /exec /=.
      rewrite dret_id_right.
      rewrite /prim_step_or_val /=.
      rewrite fill_not_val //.
      rewrite fill_prim_step_dbind //.
      replace (dret _) with (dbind dret (dret (e, σ1))) by now rewrite dret_id_right.
      unshelve eapply Rcoupl_dbind ; simpl.
      1: exact (λ ρ2 ρ2', ∃ b : bool, ρ2 = (e, σ1) /\ ρ2' = (Val #b, σ0')).
      { intros ? (e' & s') (b & ? & HH).
        apply Rcoupl_dret. rewrite /fill_lift /=. exists b. by inversion HH. }
      apply Rcoupl_flipU_r => //.
    }
    iIntros (σ2 e2' (b & [= -> ->])).
    iMod (spec_interp_update (fill K #b, σ0') with "Hspec Hspec0") as "[Hspec Hspec0]".
    iMod (spec_prog_update (fill K #b) with "Hauth Hj") as "[Hauth Hj]".
    simplify_map_eq.
    iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hauth Hheap Hspec0 Htapes]") as "_".
    { iModIntro. rewrite /spec_inv.
      iExists _, _, _, 0. simpl.
      iFrame. rewrite exec_O dret_1_1 //. }
    iSpecialize ("Hwp" with "[Hj]").
    { iSplitR. 1: done. iExists _. iFrame. }
    rewrite !wp_unfold /wp_pre /= He.
    iMod ("Hwp" $! _ with "[$Hh1 $Hspec Ht1]") as "Hwp"; [done|].
    iModIntro. done.
  Qed.

  Corollary wp_flipU_r' E e K Φ :
    to_val e = None →
    nclose specN ⊆ E →
    spec_ctx ∗ ⤇ fill K (flip #()) ∗
    (∀ b : bool, ((spec_ctx ∗ ⤇ fill K #b) -∗ WP e @ E {{ Φ }}))
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (??) "(#Hs & Hp & Hwp)".
    iApply (wp_flipU_r _ _ K) => //.
    iFrame. iFrame "Hs". iIntros "[_ H]". iDestruct "H" as "[%b Hb]".
    iApply "Hwp". iFrame. iAssumption.
  Qed.

End rules.

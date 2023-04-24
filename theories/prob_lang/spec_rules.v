(** Rules for updating the specification program. *)
From Coq Require Import Reals.
From stdpp Require Import namespaces.
From self.prelude Require Import stdpp_ext.
From iris.algebra Require Import auth excl frac agree gmap list.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import proofmode.
From self.program_logic Require Import ectx_lifting.
From self.prob_lang Require Export lang notation tactics primitive_laws spec_ra metatheory.

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

  Lemma step_allocBooltape E K :
    nclose specN ⊆ E →
    spec_ctx ∗ ⤇ fill K allocBool ={E}=∗ ∃ l, spec_ctx ∗ ⤇ fill K (#lbl: l) ∗ l ↪ₛb [].
  Proof. by apply step_alloctape. Qed.

  Lemma step_flip E K l (b : bool) bs :
    nclose specN ⊆ E →
    spec_ctx ∗ ⤇ fill K (flip #lbl:l) ∗ l ↪ₛb (b :: bs)
    ={E}=∗ spec_ctx ∗ ⤇ fill K #(LitBool b) ∗ l ↪ₛb bs.
  Proof.
    iIntros (?) "(#Hinv & Hj & Hl)".
    replace (fill K (flip #lbl:l)) with
      (fill ([UnOpCtx ZtoBOp] ++ K) (rand #1%nat from #lbl:l)); [|done].
    iMod (step_rand with "[$Hinv $Hj $Hl]") as "(_ & Hj & Hl) /="; [done|].
    iMod (step_pure with "[$Hinv $Hj]") as "[_ Hj]"; [done|done|].
    rewrite Z_to_bool_of_nat bool_to_fin_to_nat_inv.
    by iFrame "Hinv Hl".
  Qed.

  (** * RHS [rand(α)] with empty tape  *)
  Lemma wp_rand_empty_r N z E e K α Φ :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    nclose specN ⊆ E →
    spec_ctx ∗ ⤇ fill K (rand #z from #lbl:α) ∗ α ↪ₛ (N; []) ∗
    ((α ↪ₛ (N; []) ∗ spec_ctx ∗ ∃ n, ⤇ fill K #n) -∗ WP e @ E {{ Φ }})
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

  Lemma refines_right_flip E K l b bs :
    nclose specN ⊆ E →
    l ↪ₛb (b :: bs) -∗
    refines_right K (flip #lbl:l) ={E}=∗ refines_right K #(LitBool b) ∗ l ↪ₛb bs.
  Proof.
    iIntros (?) "? (?&?)".
    iMod (step_flip with "[$]") as "(?&?&?)"; first done.
    iModIntro; iFrame.
  Qed.

  (** * Coupling rules  *)
  (* TODO: can we factor out a lemma to avoid duplication in all the coupling lemmas? *)

  (** * state_step(α, N) ~ state_step(α', N) coupling *)
  Lemma wp_couple_tapes N f `{Bij (fin (S N)) (fin (S N)) f} E e α αₛ ns nsₛ Φ :
    to_val e = None →
    nclose specN ⊆ E →
    spec_ctx ∗ αₛ ↪ₛ (N; nsₛ) ∗ α ↪ (N; ns) ∗
    ((∃ n, αₛ ↪ₛ (N; nsₛ ++ [f n]) ∗ α ↪ (N; ns ++ [n])) -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (He ?) "(#Hinv & Hαs & Hα & Hwp)".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1') "[[Hh1 Ht1] Hauth2]".
    iInv specN as (ρ' e0' σ0' m) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_interp_auth_frag_agree with "Hauth2 Hspec0") as %<-.
    iDestruct (ghost_map_lookup with "Htapes Hαs") as %?.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    (* Get up to speed with the spec resource (tracked in spec_ctx) *)
    iApply exec_coupl_det_r; [done|].
    (* Do a coupled [state_step] on both sides  *)
    iApply (exec_coupl_state_steps α αₛ).
    { rewrite /= /get_active.
      apply elem_of_list_In, in_prod;
        apply elem_of_list_In, elem_of_elements, elem_of_dom; auto. }
    iExists _.
    iSplit.
    { iPureIntro. by eapply Rcoupl_pos_R, (Rcoupl_state_state _ f). }
    iIntros (σ2 σ2' ((b & -> & ->) & ? & ?)).
    (* Update our resources *)
    iMod (spec_interp_update (e0', (state_upd_tapes <[αₛ:=(N; nsₛ ++ [f b]) : tape]> σ0'))
           with "Hauth2 Hspec0") as "[Hauth2 Hspec0]".
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?%lookup_total_correct.
    iDestruct (ghost_map_lookup with "Htapes Hαs") as %?%lookup_total_correct.
    simplify_map_eq.
    iMod (ghost_map_update ((N; ns ++ [b]) : tape) with "Ht1 Hα") as "[Ht1 Hα]".
    iMod (ghost_map_update ((N; nsₛ ++ [f b]) : tape) with "Htapes Hαs") as "[Htapes Hαs]".
    (* Close the [spec_ctx] invariant again, so the assumption can access all invariants *)
    iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hauth Hheap Hspec0 Htapes]") as "_".
    { iModIntro. rewrite /spec_inv.
      iExists _, _, (state_upd_tapes _ _), 0. simpl.
      iFrame. rewrite exec_O dret_1_1 //. }
    (* Our [WP] assumption with the updated resources now suffices to prove the goal *)
    iSpecialize ("Hwp" with "[Hα Hαs]").
    { iExists _. iFrame; auto. }
    rewrite !wp_unfold /wp_pre /= He.
    iMod ("Hwp" $! (state_upd_tapes <[α:=(N; ns ++ [b]) : tape]> _)
           with "[$Hh1 $Hauth2 $Ht1]") as "Hwp".
    iModIntro. done.
  Qed.

  Corollary wp_couple_tapes_eq N E e α αₛ ns nsₛ Φ :
    to_val e = None →
    nclose specN ⊆ E →
    spec_ctx ∗ αₛ ↪ₛ (N; nsₛ) ∗ α ↪ (N; ns) ∗
    ((∃ n, αₛ ↪ₛ (N; nsₛ ++ [n]) ∗ α ↪ (N; ns ++ [n])) -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof. by eapply (wp_couple_tapes _ (Datatypes.id)). Qed.

  Lemma wp_couple_tapesN_eq m E N e α αₛ ns nsₛ Φ :
    to_val e = None →
    nclose specN ⊆ E →
    spec_ctx ∗ αₛ ↪ₛ (N; nsₛ) ∗ α ↪ (N; ns) ∗
    ((∃ ns', ⌜length ns' = m ⌝ ∗ αₛ ↪ₛ (N; nsₛ ++ ns') ∗ α ↪ (N; ns ++ ns')) -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (??).
    iInduction m as [| m] "IH" forall (ns nsₛ).
    - iIntros "(#Hctx&Hα&Hαₛ&Hwp)".
      iApply "Hwp".
      iExists [].
      iSplit; [done|].
      rewrite 2!app_nil_r.
      iFrame.
    - iIntros "(#Hctx&Hα&Hαₛ&Hwp)".
      iApply "IH". iFrame "Hα Hαₛ Hctx".
      iDestruct 1 as (ns' Hlen) "(Hα&Hαₛ)".
      iApply wp_couple_tapes_eq; [done|done|].
      iFrame "Hα Hαₛ Hctx".
      iDestruct 1 as (n) "(Hα&Hαₛ)".
      iApply "Hwp".
      iExists (ns' ++ [n]).
      rewrite 2!app_assoc. iFrame.
      iPureIntro.
      rewrite app_length Hlen /=.
      lia.
  Qed.

  (** * state_step(α, N) ~ rand(unit, N) coupling *)
  Lemma wp_couple_tape_rand N f `{Bij (fin (S N)) (fin (S N)) f} K E α z ns Φ e :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    nclose specN ⊆ E →
    spec_ctx ∗ α ↪ (N; ns) ∗ ⤇ fill K (rand #z from #()) ∗
    (∀ n, α ↪ (N; ns ++ [n]) ∗ ⤇ fill K #(f n) -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (-> He ?) "(#Hinv & Hα & Hj & Hwp)".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1') "[[Hh1 Ht1] Hauth2]".
    iInv specN as (ρ' e0' σ0' m) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_interp_auth_frag_agree with "Hauth2 Hspec0") as %<-.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?.
    iDestruct (spec_prog_auth_frag_agree with "Hauth Hj") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iApply exec_coupl_det_r; [done|].
    iApply (exec_coupl_state_prim α).
    { rewrite /= /get_active. apply elem_of_elements, elem_of_dom; eauto. }
    iExists
      (λ σ2 '(e2', σ2'),
        ∃ n, σ2 = state_upd_tapes <[α := (_; ns ++ [n]) : tape]> σ1
             ∧ (e2', σ2') = (fill K #(f n), σ0')).
    iSplit.
    { iPureIntro.
      rewrite /= -(dret_id_right (state_step _ _)) fill_dmap //.
      eapply Rcoupl_dbind => /=; last first.
      { eapply Rcoupl_pos_R. by eapply Rcoupl_state_rand. }
      intros σ2 (e2' & σ2') ((b & -> & ->) & ? & ?).
      apply Rcoupl_dret=>/=. eauto. }
    iIntros (σ2 e2' σ2' (b & -> & [= -> ->])).
    iMod (spec_interp_update (fill K #(f b), σ0') with "Hauth2 Hspec0") as "[Hauth2 Hspec0]".
    iMod (spec_prog_update (fill K #(f b)) with "Hauth Hj") as "[Hauth Hj]".
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?%lookup_total_correct.
    iMod (ghost_map_update ((_; ns ++ [b]) : tape) with "Ht1 Hα") as "[Ht1 Hα]".
    iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hauth Hheap Hspec0 Htapes]") as "_".
    { iModIntro. rewrite /spec_inv.
      iExists _, _, _, 0. simpl.
      iFrame. rewrite exec_O dret_1_1 //. }
    iSpecialize ("Hwp" with "[$Hα $Hj]").
    rewrite !wp_unfold /wp_pre /= He.
    iMod ("Hwp" $! (state_upd_tapes <[α:=(_; ns ++ [b]) : tape]> σ1)
           with "[$Hh1 $Hauth2 $Ht1]") as "Hwp".
    done.
  Qed.

  Corollary wp_couple_tape_rand_eq N K E α z ns Φ e :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    nclose specN ⊆ E →
    spec_ctx ∗ α ↪ (N; ns) ∗ ⤇ fill K (rand #z from #()) ∗
    (∀ n, α ↪ (N; ns ++ [n]) ∗ ⤇ fill K #n -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof. apply (wp_couple_tape_rand _ Datatypes.id). Qed.

  (** * rand(unit, N) ~ state_step(α', N) coupling *)
  Lemma wp_couple_rand_tape N f `{Bij (fin (S N)) (fin (S N)) f} z E α ns Φ :
    TCEq N (Z.to_nat z) →
    nclose specN ⊆ E →
    spec_ctx ∗ α ↪ₛ (N; ns) ∗
    (∀ n, α ↪ₛ (N; ns ++ [f n]) -∗ Φ #n)
    ⊢ WP rand #z from #() @ E {{ Φ }}.
  Proof.
    iIntros (-> He) "(#Hinv & Hαs & Hwp)".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1') "[[Hh1 Ht1] Hauth2]".
    iInv specN as (ρ' e0' σ0' m) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_interp_auth_frag_agree with "Hauth2 Hspec0") as %<-.
    iDestruct (ghost_map_lookup with "Htapes Hαs") as %?.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iApply exec_coupl_det_r; [done|].
    iApply (exec_coupl_prim_state α).
    { rewrite /= /get_active. apply elem_of_elements, elem_of_dom; eauto. }
    iExists _.
    iSplit.
    { iPureIntro. apply head_prim_reducible.
      eexists (Val #0%fin, σ1).
      apply head_step_support_equiv_rel.
      by eapply (RandNoTapeS _ _ 0%fin). }
    iSplit.
    { iPureIntro. by eapply (Rcoupl_rand_state _ f). }
    iIntros (e2 σ2 σ2' (b & [=-> ->] & ->)).
    iMod (spec_interp_update (e0', state_upd_tapes <[α:=(_; ns ++ [f b]) : tape]> σ0')
           with "Hauth2 Hspec0") as "[Hauth2 Hspec0]".
    iDestruct (ghost_map_lookup with "Htapes Hαs") as %?%lookup_total_correct.
    iMod (ghost_map_update ((_; ns ++ [f b]) : tape) with "Htapes Hαs") as "[Htapes Hαs]".
    do 2 iModIntro.
    iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hauth Hheap Hspec0 Htapes]") as "_".
    { iModIntro. rewrite /spec_inv.
      iExists _, _, (state_upd_tapes _ _), 0. simpl.
      iFrame. rewrite exec_O dret_1_1 //. }
    iSpecialize ("Hwp" $! b with "[$Hαs]").
    iFrame.
    iModIntro.
    by iApply wp_value.
  Qed.

  Corollary wp_couple_rand_tape_eq E α N z ns Φ :
    TCEq N (Z.to_nat z) →
    nclose specN ⊆ E →
    spec_ctx ∗ α ↪ₛ (N; ns) ∗
    (∀ n, α ↪ₛ (N; ns ++ [n]) -∗ Φ #n)
    ⊢ WP rand #z from #() @ E {{ Φ }}.
  Proof. apply (wp_couple_rand_tape _ Datatypes.id). Qed.

  (** * rand(α, N) ~ rand(unit, N) coupling *)
  Lemma wp_couple_rand_lbl_rand N f `{Bij (fin (S N)) (fin (S N)) f} z K E α Φ :
    TCEq N (Z.to_nat z) →
    nclose specN ⊆ E →
    spec_ctx ∗ α ↪ (N; []) ∗ ⤇ fill K (rand #z from #()) ∗
    (∀ n, α ↪ (N; []) ∗ ⤇ fill K #(f n) -∗ Φ #n)
    ⊢ WP rand #z from #lbl:α @ E {{ Φ }}.
  Proof.
    iIntros (??) "(#Hinv & Hα & Hr & HΦ)".
    iApply wp_couple_tape_rand => //.
    iFrame "Hinv". iFrame => /=.
    iIntros (n) "(Hα & Hr)".
    iApply (wp_rand_tape with "Hα").
    iIntros "!> Hα".
    iApply ("HΦ" with "[$]").
  Qed.

  Corollary wp_couple_rand_lbl_rand_eq N z K E α Φ :
    TCEq N (Z.to_nat z) →
    nclose specN ⊆ E →
    spec_ctx ∗ α ↪ (N; []) ∗ ⤇ fill K (rand #z from #()) ∗
    (∀ (n : fin (S N)), α ↪ (N; []) ∗ ⤇ fill K #n -∗ Φ #n)
    ⊢ WP rand #z from #lbl:α @ E {{ Φ }}.
  Proof. apply (wp_couple_rand_lbl_rand _ Datatypes.id). Qed.

  (** * rand(unit, N) ~ rand(α, N) coupling *)
  Lemma wp_couple_rand_rand_lbl N f `{Bij (fin (S N)) (fin (S N)) f} z K E α Φ :
    TCEq N (Z.to_nat z) →
    nclose specN ⊆ E →
    spec_ctx ∗ α ↪ₛ (N; []) ∗ ⤇ fill K (rand #z from #lbl:α) ∗
    (∀ n, α ↪ₛ (N; []) ∗ ⤇ fill K #(f n) -∗ Φ #n)
    ⊢ WP rand #z from #() @ E {{ Φ }}.
  Proof.
    iIntros (??) "(#Hinv & Hα & Hr & Hwp)".
    iApply wp_fupd.
    iApply wp_couple_rand_tape => //.
    iFrame "Hinv". iFrame => /=.
    iIntros (n) "Hα".
    iMod (step_rand with "[$]") as "(_ & Hr & Hα)"; [done|].
    iModIntro.
    iApply ("Hwp" with "[$]").
  Qed.

  Lemma wp_couple_rand_rand_lbl_eq N z K E α Φ :
    TCEq N (Z.to_nat z) →
    nclose specN ⊆ E →
    spec_ctx ∗ α ↪ₛ (N; []) ∗ ⤇ fill K (rand #z from #lbl:α) ∗
    (∀ (n : fin (S N)), α ↪ₛ (N; []) ∗ ⤇ fill K #n -∗ Φ #n)
    ⊢ WP rand #z from #() @ E {{ Φ }}.
  Proof. apply (wp_couple_rand_rand_lbl _ Datatypes.id). Qed.

  (** * rand(unit, N) ~ rand(unit, N) coupling *)
  Lemma wp_couple_rand_rand N f `{Bij (fin (S N)) (fin (S N)) f} z K E Φ :
    TCEq N (Z.to_nat z) →
    nclose specN ⊆ E →
    spec_ctx ∗ ⤇ fill K (rand #z from #()) ∗
    (∀ n, ⤇ fill K #(f n) -∗ Φ #n)
    ⊢ WP rand #z from #() @ E {{ Φ }}.
  Proof.
    iIntros (-> ?) "(#Hinv & Hr & Hwp)".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1') "[[Hh1 Ht1] Hauth2]".
    iInv specN as (ρ' e0' σ0' m) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_prog_auth_frag_agree with "Hauth Hr") as %->.
    iDestruct (spec_interp_auth_frag_agree with "Hauth2 Hspec0") as %<-.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iApply exec_coupl_det_r; [done|].
    iApply exec_coupl_prim_steps.
    iExists
      (λ '(e2, σ2) '(e2', σ2'),
        ∃ (n : fin _), (e2, σ2) = (Val #n, σ1) ∧ (e2', σ2') = (fill K #(f n), σ0')).
    iSplit.
    { iPureIntro. apply head_prim_reducible.
      eexists (Val #0%fin, σ1).
      apply head_step_support_equiv_rel.
      by eapply (RandNoTapeS _ _ 0%fin). }
    iSplit.
    { iPureIntro. simpl.
      rewrite fill_dmap // -(dret_id_right (prim_step _ _)) /=.
      eapply Rcoupl_map.
      eapply Rcoupl_impl; [|by apply (Rcoupl_rand_rand _ f)].
      intros [] [] (b & [=] & [=])=>/=.
      simplify_eq. eauto. }
    iIntros ([] [] (b & [= -> ->] & [= -> ->])).
    iMod (spec_interp_update (fill K #(f b), σ0') with "Hauth2 Hspec0") as "[Hauth2 Hspec0]".
    iMod (spec_prog_update (fill K #(f b)) with "Hauth Hr") as "[Hauth Hr]".
    do 2 iModIntro.
    iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hauth Hheap Hspec0 Htapes]") as "_".
    { iModIntro. rewrite /spec_inv.
      iExists _, _, _, 0. simpl.
      iFrame. rewrite exec_O dret_1_1 //. }
    iModIntro. iFrame.
    iApply wp_value.
    iApply ("Hwp" with "[$]").
  Qed.

  Lemma wp_couple_rand_rand_eq N z K E Φ :
    TCEq N (Z.to_nat z) →
    nclose specN ⊆ E →
    spec_ctx ∗ ⤇ fill K (rand #z from #()) ∗
    (∀ n : fin (S N), ⤇ fill K #n -∗ Φ #n)
    ⊢ WP rand #z from #() @ E {{ Φ }}.
  Proof. apply (wp_couple_rand_rand _ Datatypes.id). Qed.

End rules.

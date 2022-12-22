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
  Context `{!prelocGS Σ}.
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

  (** AllocTape and flip (non-empty tape)  *)
  Lemma step_alloctape E K :
    nclose specN ⊆ E →
    spec_ctx ∗ ⤇ fill K alloc ={E}=∗ ∃ l, spec_ctx ∗ ⤇ fill K (#lbl: l) ∗ l ↪ₛ [].
  Proof.
    iIntros (?) "[#Hinv Hj]". iFrame "Hinv".
    iInv specN as (ρ e σ m) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_prog_auth_frag_agree with "Hauth Hj") as %->.
    set (l := fresh_loc σ.(tapes)).
    iMod (spec_prog_update (fill K #(LitLbl l)) with "Hauth Hj") as "[Hauth Hj]".
    iMod (ghost_map_insert l [] with "Htapes") as "[Htapes Hl]".
    { apply not_elem_of_dom, fresh_loc_is_fresh. }
    iExists l. iFrame. iMod ("Hclose" with "[-]"); [|done].
    iModIntro.
    iExists _, _, (state_upd_tapes <[l:=[]]> σ), _.
    iFrame. iPureIntro.
    eapply exec_det_step_ctx; [apply _| |done].
    solve_step.
  Qed.

  (* TODO: should this go here or not? *)
  Lemma refines_right_alloctape E K :
    nclose specN ⊆ E →
    refines_right K alloc ={E}=∗ ∃ l, refines_right K (#lbl: l) ∗ l ↪ₛ [].
  Proof.
    iIntros (?) "(?&?)".
    iMod (step_alloctape with "[$]") as (l) "(?&?)"; first done.
    iExists _; by iFrame.
  Qed.

  Lemma step_flip E K l b bs :
    nclose specN ⊆ E →
    spec_ctx ∗ ⤇ fill K (flip #lbl:l) ∗ l ↪ₛ (b :: bs)
    ={E}=∗ spec_ctx ∗ ⤇ fill K #b ∗ l ↪ₛ bs.
  Proof.
    iIntros (?) "(#Hinv & Hj & Hl)". iFrame "Hinv".
    iInv specN as (ρ e σ m) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_prog_auth_frag_agree with "Hauth Hj") as %->.
    iMod (spec_prog_update (fill K #b) with "Hauth Hj") as "[Hauth Hj]".
    iDestruct (ghost_map_lookup with "Htapes Hl") as %?.
    iMod (ghost_map_update bs with "Htapes Hl") as "[Htapes Hl]".
    iFrame. iMod ("Hclose" with "[-]"); [|done].
    iModIntro. iExists _, _, (state_upd_tapes <[l:=bs]> σ), _.
    iFrame. iPureIntro.
    eapply exec_det_step_ctx; [apply _| |done].
    simpl.
    (* TODO: more clever [solve_step] tactic? *)
    rewrite head_prim_step_eq; [|eauto with head_step].
    rewrite /pmf /=. simplify_map_eq.
    rewrite bool_decide_eq_true_2 //.
  Qed.

  (* TODO: should this go here or not? *)
  Lemma refines_right_flip E K l b bs :
    nclose specN ⊆ E →
    l ↪ₛ (b :: bs) -∗
    refines_right K (flip #lbl:l) ={E}=∗ refines_right K (#b) ∗ l ↪ₛ bs.
  Proof.
    iIntros (?) "? (?&?)".
    iMod (step_flip with "[$]") as "(?&?&?)"; first done.
    iModIntro; iFrame.
  Qed.

  Lemma wp_couple_tapes_gen f `{Inj bool bool (=) (=) f, Surj bool bool (=) f} E e α αₛ bs bsₛ Φ :
    to_val e = None →
    nclose specN ⊆ E →
    spec_ctx ∗ αₛ ↪ₛ bsₛ ∗ α ↪ bs ∗
    ((∃ b, αₛ ↪ₛ (bsₛ ++ [f b]) ∗ α ↪ (bs ++ [b])) -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (He ?) "(#Hinv & Hαs & Hα & Hwp)".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1') "[[Hh1 Ht1] Hspec]".
    iInv specN as (ρ' e0' σ0' n) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_interp_auth_frag_agree with "Hspec Hspec0") as %<-.
    iDestruct (ghost_map_lookup with "Htapes Hαs") as %?.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    (* Get up to speed with the spec resource (tracked in spec_ctx) *)
    iApply exec_coupl_det_r; [done|].
    (* Do a coupled [state_step] on both sides  *)
    iApply (exec_coupl_state_steps α αₛ).
    { rewrite /= /get_active.
      apply elem_of_list_In, in_prod;
        apply elem_of_list_In, elem_of_elements, elem_of_dom; eauto. }
    iExists _.
    iSplit.
    { iPureIntro. eapply Rcoupl_pos_R, (Rcoupl_state_step f); by apply elem_of_dom. }
    iIntros (σ2 σ2' ((b & -> & ->) & ? & ?)).
    (* Update our resources *)
    iMod (spec_interp_update (e0', (state_upd_tapes <[αₛ:=tapes σ0' !!! αₛ ++ [f b]]> σ0'))
           with "Hspec Hspec0") as "[Hspec Hspec0]".
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?%lookup_total_correct.
    iDestruct (ghost_map_lookup with "Htapes Hαs") as %?%lookup_total_correct.
    simplify_map_eq.
    iMod (ghost_map_update (tapes σ1 !!! α ++ [b]) with "Ht1 Hα") as "[Ht1 Hα]".
    iMod (ghost_map_update (tapes σ0' !!! αₛ ++ [f b]) with "Htapes Hαs") as "[Htapes Hαs]".
    (* Close the [spec_ctx] invariant again, so the assumption can access all invariants  *)
    iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hauth Hheap Hspec0 Htapes]") as "_".
    { iModIntro. rewrite /spec_inv.
      iExists _, _, (state_upd_tapes _ _), 0. simpl.
      iFrame. rewrite exec_O dret_1_1 //. }
    (* Our [WP] assumption with the updated resources now suffices to prove the goal *)
    iSpecialize ("Hwp" with "[Hα Hαs]").
    { iExists _. iFrame. }
    rewrite !wp_unfold /wp_pre /= He.
    iMod ("Hwp" $! (state_upd_tapes _ _) with "[$Hh1 $Hspec Ht1]") as "Hwp"; [done|].
    iModIntro. done.
  Qed.

  Lemma wp_couple_tapes E e α αₛ bs bsₛ Φ :
    to_val e = None →
    nclose specN ⊆ E →
    spec_ctx ∗ αₛ ↪ₛ bsₛ ∗ α ↪ bs ∗
    ((∃ b, αₛ ↪ₛ (bsₛ ++ [b]) ∗ α ↪ (bs ++ [b])) -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof. apply (wp_couple_tapes_gen (Datatypes.id)). Qed.

  Lemma wp_couple_tapes_neg E e α αₛ bs bsₛ Φ :
    to_val e = None →
    nclose specN ⊆ E →
    spec_ctx ∗ αₛ ↪ₛ bsₛ ∗ α ↪ bs ∗
    ((∃ b, αₛ ↪ₛ (bsₛ ++ [negb b]) ∗ α ↪ (bs ++ [b])) -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof. apply (wp_couple_tapes_gen negb). Qed.

  (* TODO: requires adding a case to exec_coupl_pre *)
  Lemma wp_couple_tape_flip K E α bs Φ e :
    to_val e = None →
    nclose specN ⊆ E →
    spec_ctx ∗ α ↪ bs ∗ ⤇ fill K (flip #()) ∗
    (∀ (b : bool), α ↪ (bs ++ [b]) ∗ ⤇ fill K #b -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
  Admitted.

  (* TODO: requires adding a case to exec_coupl_pre *)
  Lemma wp_couple_flip_tape E α bs Φ :
    nclose specN ⊆ E →
    spec_ctx ∗ α ↪ₛ bs ∗
    (∀ (b : bool), α ↪ₛ (bs ++ [b]) -∗ Φ #b)
    ⊢ WP flip #() @ E {{ Φ }}.
  Proof.
  Admitted.

  Lemma wp_couple_flips_l K E α Φ :
    nclose specN ⊆ E →
    spec_ctx ∗ α ↪ [] ∗ ⤇ fill K (flip #()) ∗
    (∀ (b : bool), α ↪ [] ∗ ⤇ fill K #b -∗ WP (Val #b) @ E {{ Φ }})
    ⊢ WP flip #lbl:α @ E {{ Φ }}.
  Proof.
    iIntros (?) "(#Hinv & Hα & Hr & Hwp)".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1') "[[Hh1 Ht1] Hspec]".
    iInv specN as (ρ' e0' σ0' n) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_prog_auth_frag_agree with "Hauth Hr") as %->.
    iDestruct (spec_interp_auth_frag_agree with "Hspec Hspec0") as %<-.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %Hα.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iApply exec_coupl_det_r; [done|].
    iApply exec_coupl_prim_steps.
    iExists
      (λ '(e2, σ2) '(e2', σ2'),
        ∃ (b : bool), (e2, σ2) = (Val #b, σ1) ∧ (e2', σ2') = (fill K #b, σ0')).
    iSplit.
    { iPureIntro. apply head_prim_reducible.
      eexists (Val #true, σ1).
      rewrite /pmf /= Hα bool_decide_eq_true_2 //. lra. }
    iSplit.
    { iPureIntro. simpl.
      rewrite fill_dmap // -(dret_id_right (prim_step _ _)) /=.
      eapply Rcoupl_map.
      eapply Rcoupl_impl; [|by apply Rcoupl_flip_flip_l].
      intros [] [] [? [=]]=>/=; simplify_eq; eauto. }
    iIntros ([] [] (b & [=] & [=])); simplify_eq.
    iMod (spec_interp_update (fill K #b, σ0') with "Hspec Hspec0") as "[Hspec Hspec0]".
    iMod (spec_prog_update (fill K #b) with "Hauth Hr") as "[Hauth Hr]".
    do 2 iModIntro.
    iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hauth Hheap Hspec0 Htapes]") as "_".
    { iModIntro. rewrite /spec_inv.
      iExists _, _, _, 0. simpl.
      iFrame. rewrite exec_O dret_1_1 //. }
    iModIntro. iFrame.
    iApply ("Hwp" with "[$]").
  Qed.

  Lemma wp_couple_flips_r K E α Φ :
    nclose specN ⊆ E →
    spec_ctx ∗ α ↪ₛ [] ∗ ⤇ fill K (flip #lbl:α) ∗
    (∀ (b : bool), α ↪ₛ [] ∗ ⤇ fill K #b -∗ WP (Val #b) @ E {{ Φ }})
    ⊢ WP flip #() @ E {{ Φ }}.
  Proof.
    iIntros (?) "(#Hinv & Hα & Hr & Hwp)".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1') "[[Hh1 Ht1] Hspec]".
    iInv specN as (ρ' e0' σ0' n) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_prog_auth_frag_agree with "Hauth Hr") as %->.
    iDestruct (spec_interp_auth_frag_agree with "Hspec Hspec0") as %<-.
    iDestruct (ghost_map_lookup with "Htapes Hα") as %Hα.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iApply exec_coupl_det_r; [done|].
    iApply exec_coupl_prim_steps.
    iExists
      (λ '(e2, σ2) '(e2', σ2'),
        ∃ (b : bool), (e2, σ2) = (Val #b, σ1) ∧ (e2', σ2') = (fill K #b, σ0')).
    iSplit.
    { iPureIntro. apply head_prim_reducible.
      eexists (Val #true, σ1).
      rewrite /pmf /= bool_decide_eq_true_2 //. lra. }
    iSplit.
    { iPureIntro. simpl.
      rewrite fill_dmap // -(dret_id_right (prim_step _ _)) /=.
      eapply Rcoupl_map.
      eapply Rcoupl_impl; [|by apply Rcoupl_flip_flip_r].
      intros [] [] [? [=]]=>/=; simplify_eq; eauto. }
    iIntros ([] [] (b & [=] & [=])); simplify_eq.
    iMod (spec_interp_update (fill K #b, σ0') with "Hspec Hspec0") as "[Hspec Hspec0]".
    iMod (spec_prog_update (fill K #b) with "Hauth Hr") as "[Hauth Hr]".
    do 2 iModIntro.
    iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hauth Hheap Hspec0 Htapes]") as "_".
    { iModIntro. rewrite /spec_inv.
      iExists _, _, _, 0. simpl.
      iFrame. rewrite exec_O dret_1_1 //. }
    iModIntro. iFrame.
    iApply ("Hwp" with "[$]").
  Qed.

  Lemma wp_couple_flips_lr K E Φ :
    nclose specN ⊆ E →
    spec_ctx ∗ ⤇ fill K (flip #()) ∗
    (∀ (b : bool), ⤇ fill K #b -∗ WP (Val #b) @ E {{ Φ }})
    ⊢ WP flip #() @ E {{ Φ }}.
  Proof.
    iIntros (?) "(#Hinv & Hr & Hwp)".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1') "[[Hh1 Ht1] Hspec]".
    iInv specN as (ρ' e0' σ0' n) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_prog_auth_frag_agree with "Hauth Hr") as %->.
    iDestruct (spec_interp_auth_frag_agree with "Hspec Hspec0") as %<-.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iApply exec_coupl_det_r; [done|].
    iApply exec_coupl_prim_steps.
    iExists
      (λ '(e2, σ2) '(e2', σ2'),
        ∃ (b : bool), (e2, σ2) = (Val #b, σ1) ∧ (e2', σ2') = (fill K #b, σ0')).
    iSplit.
    { iPureIntro. apply head_prim_reducible.
      eexists (Val #true, σ1).
      rewrite /pmf /= bool_decide_eq_true_2 //. lra. }
    iSplit.
    { iPureIntro. simpl.
      rewrite fill_dmap // -(dret_id_right (prim_step _ _)) /=.
      eapply Rcoupl_map.
      eapply Rcoupl_impl; [|by apply Rcoupl_flip_flip_lr].
      intros [] [] [? [=]]=>/=; simplify_eq; eauto. }
    iIntros ([] [] (b & [=] & [=])); simplify_eq.
    iMod (spec_interp_update (fill K #b, σ0') with "Hspec Hspec0") as "[Hspec Hspec0]".
    iMod (spec_prog_update (fill K #b) with "Hauth Hr") as "[Hauth Hr]".
    do 2 iModIntro.
    iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hauth Hheap Hspec0 Htapes]") as "_".
    { iModIntro. rewrite /spec_inv.
      iExists _, _, _, 0. simpl.
      iFrame. rewrite exec_O dret_1_1 //. }
    iModIntro. iFrame.
    iApply ("Hwp" with "[$]").
  Qed.

End rules.

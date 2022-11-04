(** Rules for updating the specification program. *)
From Coq Require Import Reals.
From stdpp Require Import namespaces.
From self.prelude Require Import stdpp_ext.
From iris.algebra Require Import auth excl frac agree gmap list.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import proofmode.
From self.program_logic Require Import ectx_lifting.
From self.prob_lang Require Export lang notation tactics primitive_laws spec_ra exec_prob_lang.

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
    iInv specN as (ξ ρ e0 σ0) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_prog_auth_frag_agree with "Hauth Hj") as %->.
    iMod (spec_prog_update (fill K e') with "Hauth Hj") as "[Hauth Hj]".
    iFrame "Hj". iApply "Hclose". iNext.
    edestruct (exec_PureExec_ctx (fill K) P) as [ξ' Hexec']; [done|done|].
    iExists (ξ ++ ξ'), _, _, _.
    iFrame. by erewrite Hexec'.
  Qed.

  (** Alloc, load, and store *)
  Lemma step_alloc E K e v :
    IntoVal e v →
    nclose specN ⊆ E →
    spec_ctx ∗ ⤇ fill K (ref e) ={E}=∗ ∃ l, spec_ctx ∗ ⤇ fill K (#l) ∗ l ↦ₛ v.
  Proof.
    iIntros (<-?) "[#Hinv Hj]". iFrame "Hinv".
    iInv specN as (ξ ρ e σ) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_prog_auth_frag_agree with "Hauth Hj") as %->.
    set (l := fresh_loc σ.(heap)).
    iMod (spec_prog_update (fill K #l) with "Hauth Hj") as "[Hauth Hj]".
    iMod (ghost_map_insert l v with "Hheap") as "[Hheap Hl]".
    { apply not_elem_of_dom, fresh_loc_is_fresh. }
    iExists l. iFrame. iMod ("Hclose" with "[-]"); [|done].
    iModIntro. rewrite /spec_inv.
    iExists (ξ ++ prim_step_sch (_, _)), _, _, (state_upd_heap <[l:=v]> σ).
    iFrame. erewrite exec_det_step_ctx; [done|apply _|].
    solve_step.
  Qed.

  Lemma step_load E K l q v:
    nclose specN ⊆ E →
    spec_ctx ∗ ⤇ fill K (!#l) ∗ l ↦ₛ{q} v
    ={E}=∗ spec_ctx ∗ ⤇ fill K (of_val v) ∗ l ↦ₛ{q} v.
  Proof.
    iIntros (?) "(#Hinv & Hj & Hl)". iFrame "Hinv".
    iInv specN as (ξ ρ e σ) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_prog_auth_frag_agree with "Hauth Hj") as %->.
    iMod (spec_prog_update (fill K v) with "Hauth Hj") as "[Hauth Hj]".
    iDestruct (ghost_map_lookup with "Hheap Hl") as %?.
    iFrame. iMod ("Hclose" with "[-]"); [|done].
    iModIntro. iExists (ξ ++ prim_step_sch (_, _)), _, _, _.
    iFrame. erewrite exec_det_step_ctx; [done|apply _|].
    solve_step.
  Qed.

  Lemma step_store E K l v' e v:
    IntoVal e v →
    nclose specN ⊆ E →
    spec_ctx ∗ ⤇ fill K (#l <- e) ∗ l ↦ₛ v'
    ={E}=∗ spec_ctx ∗ ⤇ fill K #() ∗ l ↦ₛ v.
  Proof.
    iIntros (<-?) "(#Hinv & Hj & Hl)". iFrame "Hinv".
    iInv specN as (ξ ρ e σ) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_prog_auth_frag_agree with "Hauth Hj") as %->.
    iMod (spec_prog_update (fill K #()) with "Hauth Hj") as "[Hauth Hj]".
    iDestruct (ghost_map_lookup with "Hheap Hl") as %?.
    iMod (ghost_map_update v with "Hheap Hl") as "[Hheap Hl]".
    iFrame. iMod ("Hclose" with "[-]"); [|done].
    iModIntro. iExists (ξ ++ prim_step_sch (_, _)), _, _, (state_upd_heap <[l:=v]> σ).
    iFrame. erewrite exec_det_step_ctx; [done|apply _|].
    solve_step.
  Qed.

  (** AllocTape and flip (non-empty tape)  *)
  Lemma step_alloctape E K :
    nclose specN ⊆ E →
    spec_ctx ∗ ⤇ fill K alloc ={E}=∗ ∃ l, spec_ctx ∗ ⤇ fill K (#lbl: l) ∗ l ↪ₛ [].
  Proof.
    iIntros (?) "[#Hinv Hj]". iFrame "Hinv".
    iInv specN as (ξ ρ e σ) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_prog_auth_frag_agree with "Hauth Hj") as %->.
    set (l := fresh_loc σ.(tapes)).
    iMod (spec_prog_update (fill K #(LitLbl l)) with "Hauth Hj") as "[Hauth Hj]".
    iMod (ghost_map_insert l [] with "Htapes") as "[Htapes Hl]".
    { apply not_elem_of_dom, fresh_loc_is_fresh. }
    iExists l. iFrame. iMod ("Hclose" with "[-]"); [|done].
    iModIntro.
    iExists (ξ ++ prim_step_sch (_, _)), _, _, (state_upd_tapes <[l:=[]]> σ).
    iFrame. erewrite exec_det_step_ctx; [done|apply _|].
    solve_step.
  Qed.

  Lemma step_flip E K l b bs :
    nclose specN ⊆ E →
    spec_ctx ∗ ⤇ fill K (flip #lbl:l) ∗ l ↪ₛ (b :: bs)
    ={E}=∗ spec_ctx ∗ ⤇ fill K #b ∗ l ↪ₛ bs.
  Proof.
    iIntros (?) "(#Hinv & Hj & Hl)". iFrame "Hinv".
    iInv specN as (ξ ρ e σ) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_prog_auth_frag_agree with "Hauth Hj") as %->.
    iMod (spec_prog_update (fill K #b) with "Hauth Hj") as "[Hauth Hj]".
    iDestruct (ghost_map_lookup with "Htapes Hl") as %?.
    iMod (ghost_map_update bs with "Htapes Hl") as "[Htapes Hl]".
    iFrame. iMod ("Hclose" with "[-]"); [|done].
    iModIntro. iExists (ξ ++ prim_step_sch (_, _)), _, _, (state_upd_tapes <[l:=bs]> σ).
    iFrame. erewrite exec_det_step_ctx; [done|apply _|].
    simpl.
    (* TODO: more clever [solve_step] tactic? *)
    rewrite head_prim_step_eq; [|eauto with head_step].
    rewrite /pmf /=. simplify_map_eq.
    rewrite bool_decide_eq_true_2 //.
  Qed.

  Lemma wp_couple_tapes E e e' α αₛ bs bsₛ Φ :
    pure_step e e' →
    nclose specN ⊆ E →
    spec_ctx ∗ αₛ ↪ₛ bsₛ ∗ α ↪ bs ∗
    ((∃ b, αₛ ↪ₛ (bsₛ ++ [b]) ∗ α ↪ (bs ++ [b])) -∗ WP e' @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (Hpstep ?) "(#Hinv & Hαs & Hα & Hwp)".
    assert (to_val e = None) as Hv.
    { eapply (reducible_not_val _ inhabitant), Hpstep. }
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ [eₛ σₛ]) "[[Hh1 Ht1] Hρ]".
    iInv specN as (ξₛ ρ' e2 σ2) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_interp_auth_frag_agree with "Hρ Hspec0") as %<-.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iSplit.
    { iPureIntro; eapply Hpstep. }
    iExists _, _, _. iSplit.
    { iPureIntro. apply state_prim_step_sch_wf. rewrite Hv //. }
    iSplit.
    { iPureIntro. eapply Rcoupl_exec_det_prefix_r; [done|]. by eapply (state_prim_state_coupl α αₛ). }
    iIntros (e3 σ3 [e4 σ4] (?&?& [b [=]])); simplify_eq.
    iIntros "!> !>". rewrite /state_interp /spec_interp /=.
    iMod (spec_interp_update (e2, _) with "Hρ Hspec0") as "[Hρ Hspec0]".
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?%lookup_total_correct.
    iDestruct (ghost_map_lookup with "Htapes Hαs") as %?%lookup_total_correct.
    simplify_map_eq.
    iMod (ghost_map_update (tapes σ !!! α ++ [b]) with "Ht1 Hα") as "[Ht1 Hα]".
    iFrame.
    iMod (ghost_map_update (tapes σ2 !!! αₛ ++ [b]) with "Htapes Hαs") as "[Htapes Hαs]".
    iMod "Hclose'". iMod ("Hclose" with "[Hauth Hheap Hspec0 Htapes]") as "_"; last first.
    { iModIntro. iApply "Hwp". iExists b. iFrame. }
    iModIntro. rewrite /spec_inv.
    iExists [], _, _, (state_upd_tapes _ _). simpl.
    iFrame. rewrite exec_nil dret_1 //.
Qed.

End rules.

(** Rules for updating the specification program. *)
From stdpp Require Import namespaces.
From iris.algebra Require Import auth excl frac agree gmap list.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import proofmode.
From self.prob_lang Require Export lang notation tactics primitive_laws spec_ra.

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

End rules.

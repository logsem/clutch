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

  Lemma wp_couple_tapes E e α αₛ bs bsₛ Φ :
    to_val e = None →
    nclose specN ⊆ E →
    spec_ctx ∗ αₛ ↪ₛ bsₛ ∗ α ↪ bs ∗
    ((∃ b, αₛ ↪ₛ (bsₛ ++ [b]) ∗ α ↪ (bs ++ [b])) -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (He ?) "(#Hinv & Hαs & Hα & Hwp)".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1') "[[Hh1 Ht1] Hspec]".
    iInv specN as (ξₛ ρ' e0' σ0') ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_interp_auth_frag_agree with "Hspec Hspec0") as %<-.

    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".





    (* We pick schedulers and a coupling that adds a bit to both sides *)

    iExists _, _, _. iSplit.
    { iPureIntro.
      eapply Rcoupl_exec_state_det_prefix_r; [done|].
      eapply Rcoupl_pos_R.
      apply (Rcoupl_exec_exec_state_steps _ _ _ α αₛ). }
    simpl.
    iIntros (σ2 e2' σ2' ([-> [b [= -> ->]]] & H1 & H1' )).

    (* Just some extra information in case it's useful (probably isn't...) *)
    rewrite dret_id_right in H1.
    rewrite exec_singleton exec_fn_unfold /= in H1'.

    (* We update our resources *)
    iMod (spec_interp_update (e0', _) with "Hspec Hspec0") as "[Hspec Hspec0]".
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?%lookup_total_correct.
    iDestruct (ghost_map_lookup with "Htapes Hαs") as %?%lookup_total_correct.
    simplify_map_eq.
    iMod (ghost_map_update (tapes σ1 !!! α ++ [b]) with "Ht1 Hα") as "[Ht1 Hα]".
    iFrame.
    iMod (ghost_map_update (tapes σ0' !!! αₛ ++ [b]) with "Htapes Hαs") as "[Htapes Hαs]".

    (* We close the [spec_ctx] invariant again, so the assumption can access all invariants  *)
    iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hauth Hheap Hspec0 Htapes]") as "_".
    { iModIntro. rewrite /spec_inv. iExists [], _, _, (state_upd_tapes _ _). simpl.
      iFrame. rewrite exec_nil dret_1 //. }

    (* We can now specialize our assumption with the updated resources *)
    iSpecialize ("Hwp" with "[Hα Hαs]").
    { iExists _. iFrame. }
    rewrite !wp_unfold /wp_pre /= He.
    iMod ("Hwp" $! (state_upd_tapes _ _) with "[$Hh1 $Hspec Ht1]") as "[% (% & % & %Hcpl & Hwp)]"; [done|].

    (* The pure Coq-level theorem doing what we want to do is
      [exec_coupl_state_prim] in [program_logic/exec.v] (the conclusion should
      be phrased slighlty differently to match the current formulation in the
      WP, though, but the right intermediate arguments are in the proof) *)

    (* Let's try fetching an inhabitant of [Hcpl] - We wrap it in [Rcoupl_pos_R]
      for now just to get some extra information, in case it might be
      useful... *)
    pose proof (Rcoupl_pos_R _ _ _ Hcpl) as Hcpl'.
    eapply Rcoupl_inhabited_l in Hcpl' as [σ2 [[e2' σ2'] (?&?&?)]]; [|apply exec_state_inhabited].

    (* We now have something to plug in to ["Hwp"] *)
    iMod ("Hwp" with "[//]") as "[%Hred (%ζ2 & %ξ2 & %S & %HcplS & Hcont)]".
    iModIntro. iSplit.
    { iPureIntro. by eapply exec_state_reducible. }

    (* The"final" scheduler is the one that combines the schedulers given
      from the two couplings [Hcpl] and [HcplS] *)
    iExists (ζ1 ++ ζ2), (ξ1 ++ ξ2), S.
    iSplit; [|done].
    iPureIntro.
    rewrite exec_state_app exec_app.
    rewrite -dbind_assoc.
    (* the [dbind_assoc] rewrite for some reason unfolded [exec_state] -- will
       mark it [simpl never] *)
    assert (∀ a, foldlM (λ σ f, state_step σ (f σ)) a ζ2 = exec_state ζ2 a) as Heq by done.
    setoid_rewrite Heq.

    (* Now we apply the [Rcoupl_bind] rule, but this requires us to prove the
       the "continuation coupling" for all things that satisfy [R2] ...*)
    eapply Rcoupl_bind; [|done].
    intros σ3 ρ HR.

    (* But now we're stuck, because we only proved it for the inhabitant we
       extracted (see [HcplS]) — so this is obviously not the right approach *)



 Admitted.


End rules.

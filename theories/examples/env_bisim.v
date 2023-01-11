(* Example taken from Sangiorgi and Vignudelli's "Environmental Bisimulations
   for Probabilistic Higher-order Languages".

NB: This example was mentioned as open problem in Aleš's thesis.
 *)

From stdpp Require Import namespaces.
From iris.base_logic Require Import invariants na_invariants.
From self.prob_lang Require Import notation proofmode primitive_laws spec_rules.
From self.logrel Require Import model rel_rules rel_tactics.
From self.typing Require Import soundness.
From self.prelude Require Import base.
Set Default Proof Using "Type*".

(* A diverging term. *)
Definition Ω : expr := rec: "Ω" "v" := "Ω" "v".

(* We'll have to think about where exactly the tape allocation should happen
   once we get to the proof. *)
Definition pchoice e1 e2 : expr :=
  if: flip "α" then e1 else e2.

Infix "⊕" := pchoice (at level 80) : expr_scope.

Definition M : expr :=
  if: !"x" = #0 then "x" <- #1 ;; #true else Ω #().

Definition N : expr :=
  if: !"x" = #0 then "x" <- #1 ;; #false else Ω #().

Definition H : expr :=
  let: "x" := ref #0 in
  let: "α" := #() in
  (λ:<>, M ⊕ N).

Definition H_with_tape : expr :=
  let: "x" := ref #0 in
  let: "α" := alloc in
  (λ:<>, M ⊕ N).

Definition K : expr :=
  let: "x" := ref #0 in
  let: "α" := #() in
  (λ:<>, M) ⊕ (λ:<>, N).

Section proofs.
  Context `{!prelogrelGS Σ}.

  Definition bisimN := nroot.@"bisim".

  Lemma H_with_tape_K_rel :
    ⊢ REL H_with_tape << K : lrel_unit → lrel_bool.
  Proof.
    rewrite /H_with_tape /K.
    rel_alloc_l x as "x". rel_alloc_r y as "y".
    rel_pures_l. rel_pures_r.
    rel_alloctape_l α as "α".
    rel_bind_r (flip _)%E.
    iApply (refines_couple_tape_flip with "[$α x y]"); [done|].
    iIntros (b) "α /=".
    rel_pures_l. rel_pures_r.
    set (P := ((α ↪ [b] ∗ x ↦ #0 ∗ y ↦ₛ #0) ∨ (α ↪ [] ∗ x ↦ #1 ∗ y ↦ₛ #1))%I).
    iApply (refines_na_alloc P bisimN).
    iSplitL. 1: iModIntro ; iLeft ; iFrame.
    iIntros "#Hinv".
    destruct b.
    (* Both cases are proven in *exactly* the same way. *)
    - rel_pures_r.
      rel_arrow_val.
      iIntros (??) "_".
      iApply (refines_na_inv with "[$Hinv]") ; [done|].
      iIntros "[[(α & x & y) | (α & x & y)] Hclose]".
      all: rel_pures_l ; rel_pures_r.
      + rel_flip_l. rel_pures_l. rel_load_r. rel_load_l. rel_pures_l. rel_pures_r.
        rel_store_l. rel_store_r. rel_pures_l. rel_pures_r.
        iApply (refines_na_close with "[- $Hclose]").
        iSplitL; [|rel_values].
        iRight. iModIntro. iFrame.
      + rel_load_r. rel_pures_r.
        rel_apply_l refines_flip_empty_l.
        iFrame. iIntros (b) "α".
        destruct b.
        (* Both cases are proven in *exactly* the same way. *)
        * rel_pures_l. rel_load_l. rel_pures_l.
          iApply (refines_na_close with "[- $Hclose]"). iSplitL.
          1: { iModIntro. iRight. iFrame. }
          rewrite refines_eq /refines_def.
          iIntros (?) "??".
          iLöb as "HH".
          wp_rec.
          now iApply ("HH" with "[$]").
        * rel_pures_l. rel_load_l. rel_pures_l.
          iApply (refines_na_close with "[- $Hclose]"). iSplitL.
          1: iModIntro ; iRight ; iFrame.
          rewrite refines_eq /refines_def.
          iIntros (?) "??".
          iLöb as "HH".
          wp_rec.
          now iApply ("HH" with "[$]").
    - rel_pures_r.
      rel_arrow_val.
      iIntros (??) "_".
      iApply (refines_na_inv with "[$Hinv]") ; [done|].
      iIntros "[[(α & x & y) | (α & x & y)] Hclose]".
      all: rel_pures_l ; rel_pures_r.
      + rel_flip_l. rel_pures_l. rel_load_r. rel_load_l. rel_pures_l. rel_pures_r.
        rel_store_l. rel_store_r. rel_pures_l. rel_pures_r.
        iApply (refines_na_close with "[- $Hclose]").
        iSplitL; [|rel_values].
        iRight. iModIntro. iFrame.
      + rel_load_r. rel_pures_r.
        rel_apply_l refines_flip_empty_l.
        iFrame. iIntros (b) "α".
        destruct b.
        (* Both cases are proven in *exactly* the same way. *)
        * rel_pures_l. rel_load_l. rel_pures_l.
          iApply (refines_na_close with "[- $Hclose]"). iSplitL.
          1: { iModIntro. iRight. iFrame. }
          rewrite refines_eq /refines_def.
          iIntros (?) "??".
          iLöb as "HH".
          wp_rec.
          now iApply ("HH" with "[$]").
        * rel_pures_l. rel_load_l. rel_pures_l.
          iApply (refines_na_close with "[- $Hclose]"). iSplitL.
          1: iModIntro ; iRight ; iFrame.
          rewrite refines_eq /refines_def.
          iIntros (?) "??".
          iLöb as "HH".
          wp_rec.
          now iApply ("HH" with "[$]").
  Qed.

  Lemma H_H_with_tape_rel :
    ⊢ REL H << H_with_tape : lrel_unit → lrel_bool.
  Proof.
    rewrite /H_with_tape /H.
    rel_alloc_l x as "x". rel_alloc_r y as "y".
    rel_pures_l. rel_pures_r.
    rel_alloctape_r α as "α".
    rel_pures_r.
    set (P := ((α ↪ₛ [] ∗ x ↦ #0 ∗ y ↦ₛ #0) ∨ (α ↪ₛ [] ∗ x ↦ #1 ∗ y ↦ₛ #1))%I).
    iApply (refines_na_alloc P bisimN).
    iSplitL. 1: iModIntro ; iLeft ; iFrame.
    iIntros "#Hinv".
    rel_arrow_val.
    iIntros (??) "_".
    iApply (refines_na_inv with "[$Hinv]") ; [done|].
    iIntros "[[(α & x & y) | (α & x & y)] Hclose]".
    all: rel_pures_l ; rel_pures_r.
    + rel_bind_l (Flip _). rel_bind_r (Flip _).
      rel_apply_l refines_couple_flips_r.
      iFrame ; iIntros (b) "α".
      destruct b.
      * rel_pures_l. rel_pures_r. rel_load_l. rel_load_r. rel_pures_l. rel_pures_r.
        rel_store_l. rel_store_r. rel_pures_l. rel_pures_r.
        iApply (refines_na_close with "[- $Hclose]").
        iSplitL; [|rel_values].
        iRight ; iModIntro ; iFrame.
      * rel_pures_l. rel_pures_r. rel_load_l. rel_load_r. rel_pures_l. rel_pures_r.
        rel_store_l. rel_store_r. rel_pures_l. rel_pures_r.
        iApply (refines_na_close with "[- $Hclose]").
        iSplitL; [|rel_values].
        iRight ; iModIntro ; iFrame.
    + rel_bind_l (Flip _). rel_bind_r (Flip _).
      rel_apply_l refines_couple_flips_r.
      iFrame ; iIntros (b) "α".
      destruct b.
      * rel_pures_l. rel_pures_r. rel_load_l. rel_load_r. rel_pures_l. rel_pures_r.
        iApply (refines_na_close with "[- $Hclose]"). iSplitL.
        1: iModIntro ; iRight ; iFrame.
        rewrite refines_eq /refines_def.
        iIntros (?) "??".
        iLöb as "HH".
        wp_rec.
        now iApply ("HH" with "[$]").
      * rel_pures_l. rel_pures_r. rel_load_l. rel_load_r. rel_pures_l. rel_pures_r.
        iApply (refines_na_close with "[- $Hclose]"). iSplitL.
        1: iModIntro ; iRight ; iFrame.
        rewrite refines_eq /refines_def.
        iIntros (?) "??".
        iLöb as "HH".
        wp_rec.
        now iApply ("HH" with "[$]").
  Qed.


  (* TODO: what should this say exactly? *)
  (* wp_couple_tape_flip is similar. *)
  Lemma wp_flip_empty_r E e K α Φ :
    to_val e = None →
    nclose specN ⊆ E →
    spec_ctx ∗ ⤇ fill K (flip #lbl:α) ∗ α ↪ₛ [] ∗
    ((α ↪ₛ [] ∗ spec_ctx ∗ ∃ b : bool, ⤇ fill K #b) -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (He ?) "(#Hinv & Hj & Hα & Hwp)".
    (* Perform a [prim_step] on the right, via FlipTapeEmptyS. *)
    (* We do not want to execute a [prim_step] on the left. We merely rely on
    the fact that we *could* step (because to_val e = None) in order to appeal
    to [Hwp]. *)
    iApply lifting.wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1') "[[Hh1 Ht1] Hspec]".
    iInv specN as (ρ' e0' σ0' n) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_interp_auth_frag_agree with "Hspec Hspec0") as %<-.
    iDestruct (ghost_map_lookup with "Htapes Hα") as %?.
    iDestruct (spec_prog_auth_frag_agree with "Hauth Hj") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    (* Get up to speed with the spec resource (tracked in spec_ctx) *)
    iApply exec_coupl_det_r; [done|].
    (* Do a coupled [prim_step] on the right *)
    iApply (exec_coupl_exec_r).
    iExists (λ σ2 '(e2', σ2'), ∃ (b : bool), (e2', σ2') = (fill K #b, σ0')).
    iExists 1.
    iSplit.
    { iPureIntro.
      rewrite /exec. simpl.
      rewrite dret_id_right.
      rewrite /prim_step_or_val /=.
      (* TODO should be provably equal to None instead of admit. *)
      destruct (to_val (fill K (flip #lbl:α))) eqn:Hval. 1: admit.
      rewrite fill_prim_step_dbind //.
      set (ρ' :=
(@dret
       (prod (ofe_car (self.program_logic.language.exprO prob_lang))
          (ofe_car (self.program_logic.language.stateO prob_lang)))
       (@prod_eq_dec (ofe_car (self.program_logic.language.exprO prob_lang))
          expr_eq_dec
          (ofe_car (self.program_logic.language.stateO prob_lang))
          state_eq_dec)
       (@prod_countable
          (ofe_car (self.program_logic.language.exprO prob_lang)) expr_eq_dec
          expr_countable
          (ofe_car (self.program_logic.language.stateO prob_lang))
          state_eq_dec state_countable)
       (@pair (ofe_car (self.program_logic.language.exprO prob_lang))
          (ofe_car (self.program_logic.language.stateO prob_lang)) e σ1))).
      rewrite -(dret_id_right ρ').
      eapply Rcoupl_dbind => /=; last first.
      Unshelve.
      3: {
        simpl.
        exact (λ _ '(e', s'), ∃ b : bool, (fill K e', s') = (fill K #b, σ0')).
      }
      2:{
        intros ? (e' & s') H.
        apply Rcoupl_dret. rewrite /fill_lift. simpl. assumption.
      }
      simpl.
      subst ρ'.
      unfold prim_step. simpl. rewrite decomp_unfold. simpl.
      unfold fill_lift. simpl. unfold dmap.
      replace (λ a : expr * state, dret (let '(e0, σ) := a in (e0, σ)))
        with
        (λ a : expr * state, dret a).
      2: { extensionality a. destruct a. done. }
      rewrite dret_id_right.
      unfold head_step. unfold head_step_pmf. simpl.
      Fail rewrite H1.
      set (F := (λ '(lhs, rhs), match rhs with
                              | (Val #(LitBool b), σ2) =>
                                  if bool_decide (σ0' = σ2) &&
                                       bool_decide (lhs = (e, σ1))
                                  then 0.5%R else 0%R
                              | _ => 0%R end)).
      unshelve econstructor.
      {
        unshelve econstructor.
        - exact F.
        - admit.
          (* subst F. intros. simpl. destruct a. destruct p0. destruct e0; try lra. *)
          (* destruct v; try lra. destruct l; try lra. *)
          (* destruct (bool_decide (σ0' = s) && bool_decide (p = (e, σ1))) eqn:H. *)
          (* all: rewrite H; lra. *)
        - admit.
        - admit.
      }
      simpl.
      constructor ; last first.
      - intros (? & e' & s') H. simpl.
        simpl in H.
        (* not sure why H doesn't simplify. maybe the evars created by the
        admit's from above? anyhow, it should amount to this: *)
        assert (F (p, (e', s')) > 0)%R by admit.
        unfold F in H2.
        destruct e' ; try (apply Rgt_irrefl in H2 ; done).
        destruct v ; try (apply Rgt_irrefl in H2 ; done).
        destruct l ; try (apply Rgt_irrefl in H2 ; done).
        exists b.
        destruct (bool_decide (σ0' = s')) eqn:HH.
        ++ destruct (bool_decide (p = (e, σ1))) eqn:HH'.
           ** apply bool_decide_eq_true_1 in HH.
              rewrite HH.
              reflexivity.
           ** rewrite HH' in H2. simpl in H2.
              apply Rgt_irrefl in H2. done.
        ++ simpl in H2. apply Rgt_irrefl in H2. done.
      - econstructor.
        all: admit.
    }
    iIntros (σ2 e2' (b & [= -> ->])).
    iMod (spec_interp_update (fill K #b, σ0') with "Hspec Hspec0") as "[Hspec Hspec0]".
    iMod (spec_prog_update (fill K #b) with "Hauth Hj") as "[Hauth Hj]".
    (* iDestruct (ghost_map_lookup with "Ht1 Hα") as %?%lookup_total_correct. *)
    simplify_map_eq.
    (* iMod (ghost_map_update (tapes σ1 !!! α ++ [b]) with "Ht1 Hα") as "[Ht1 Hα]". *)
    iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hauth Hheap Hspec0 Htapes]") as "_".
    { iModIntro. rewrite /spec_inv.
      iExists _, _, _, 0. simpl.
      iFrame. rewrite exec_O dret_1_1 //. }
    iSpecialize ("Hwp" with "[Hα Hj]").
    { iFrame. iSplitR. 1: done. iExists _. iFrame. }
    rewrite !wp_unfold /wp_pre /= He.
    iMod ("Hwp" $! _ with "[$Hh1 $Hspec Ht1]") as "Hwp"; [done|].
    iModIntro. done.
  Admitted.

  Lemma refines_flip_empty_r K E α A e :
    to_val e = None →
    α ↪ₛ [] ∗
      (∀ (b : bool), α ↪ₛ [] -∗ REL e << fill K (Val #b) @ E : A)
    ⊢ REL e << fill K (flip #lbl:α) @ E : A.
  Proof.
    iIntros (ev) "[Hα H]".
    rewrite refines_eq /refines_def.
    iIntros (K2) "[#Hs Hspec] Hnais /=".
    wp_apply wp_flip_empty_r ; auto.
    iFrame. iSplitR. 1: iAssumption.
    unfold refines_right.
    rewrite -fill_app. iFrame.
    iIntros "(α & _ & %b & Hb)".
    rewrite fill_app.
    by iApply ("H" $! _ with "[$α] [$Hs $Hb]").
  Qed.

  Lemma K_H_with_tape_rel :
    ⊢ REL K << H_with_tape : lrel_unit → lrel_bool.
  Proof.
    rewrite /H_with_tape /K.
    rel_alloc_l x as "x". rel_alloc_r y as "y".
    rel_pures_l. rel_pures_r.
    rel_alloctape_r α as "α".
    rel_bind_l (flip _)%E.
    iApply (refines_couple_flip_tape with "[$α x y]").
    iIntros (b) "α /=".
    rel_pures_l. rel_pures_r.
    set (P := ((α ↪ₛ [b] ∗ x ↦ #0 ∗ y ↦ₛ #0) ∨ (α ↪ₛ [] ∗ x ↦ #1 ∗ y ↦ₛ #1))%I).
    iApply (refines_na_alloc P bisimN).
    iSplitL. 1: iModIntro ; iLeft ; iFrame.
    iIntros "#Hinv".
    destruct b.
    (* Both cases are proven in *exactly* the same way. *)
    - rel_pures_l.
      rel_arrow_val.
      iIntros (??) "_".
      iApply (refines_na_inv with "[$Hinv]") ; [done|].
      iIntros "[[(α & x & y) | (α & x & y)] Hclose]".
      all: rel_pures_l ; rel_pures_r.
      + rel_flip_r. rel_pures_r. rel_load_r. rel_load_l. rel_pures_l. rel_pures_r.
        rel_store_l. rel_store_r. rel_pures_l. rel_pures_r.
        iApply (refines_na_close with "[- $Hclose]").
        iSplitL; [|rel_values].
        iRight. iModIntro. iFrame.
      + rel_load_l.
        rel_apply_r refines_flip_empty_r. 1: auto.
        iFrame. iIntros (b) "α". rel_pures_l.
        destruct b.
        (* Both cases are proven in *exactly* the same way. *)
        all: rel_pures_r ; rel_load_r ; rel_pures_r ;
          iApply (refines_na_close with "[- $Hclose]") ; iSplitL ;
          [iModIntro ; iRight ; iFrame|] ;
          rewrite refines_eq /refines_def ; iIntros (?) "??" ;
          iLöb as "HH" ; wp_rec ; now iApply ("HH" with "[$]").
    - rel_pures_l.
      rel_arrow_val.
      iIntros (??) "_".
      iApply (refines_na_inv with "[$Hinv]") ; [done|].
      iIntros "[[(α & x & y) | (α & x & y)] Hclose]".
      all: rel_pures_l ; rel_pures_r.
      + rel_flip_r. rel_pures_r. rel_load_r. rel_load_l. rel_pures_l. rel_pures_r.
        rel_store_l. rel_store_r. rel_pures_l. rel_pures_r.
        iApply (refines_na_close with "[- $Hclose]").
        iSplitL; [|rel_values].
        iRight. iModIntro. iFrame.
      + rel_load_l.
        rel_apply_r refines_flip_empty_r. 1: auto.
        iFrame. iIntros (b) "α". rel_pures_l.
        destruct b.
        (* Both cases are proven in *exactly* the same way. *)
        all: rel_pures_r ; rel_load_r ; rel_pures_r ;
          iApply (refines_na_close with "[- $Hclose]") ; iSplitL ;
          [iModIntro ; iRight ; iFrame|] ;
          rewrite refines_eq /refines_def ; iIntros (?) "??" ;
          iLöb as "HH" ; wp_rec ; now iApply ("HH" with "[$]").
  Qed.

  Lemma H_with_tape_H_rel :
    ⊢ REL H_with_tape << H : lrel_unit → lrel_bool.
  Proof.
    rewrite /H_with_tape /H.
    rel_alloc_l x as "x". rel_alloc_r y as "y".
    rel_pures_l. rel_pures_r.
    rel_alloctape_l α as "α".
    rel_pures_r.
    set (P := ((α ↪ [] ∗ x ↦ #0 ∗ y ↦ₛ #0) ∨ (α ↪ [] ∗ x ↦ #1 ∗ y ↦ₛ #1))%I).
    iApply (refines_na_alloc P bisimN).
    iSplitL. 1: iModIntro ; iLeft ; iFrame.
    iIntros "#Hinv".
    rel_arrow_val.
    iIntros (??) "_".
    iApply (refines_na_inv with "[$Hinv]") ; [done|].
    iIntros "[[(α & x & y) | (α & x & y)] Hclose]".
    all: rel_pures_l ; rel_pures_r.
    + rel_bind_l (Flip _). rel_bind_r (Flip _).
      rel_apply_l refines_couple_flips_l.
      iFrame ; iIntros (b) "α".
      destruct b ;
        rel_pures_l ; rel_pures_r ; rel_load_l ; rel_load_r ; rel_pures_l ; rel_pures_r ;
        rel_store_l ; rel_store_r ; rel_pures_l ; rel_pures_r ;
        iApply (refines_na_close with "[- $Hclose]").
      all: iSplitL; [|rel_values] ;
        iRight ; iModIntro ; iFrame.
    + rel_bind_l (Flip _). rel_bind_r (Flip _).
      rel_apply_l refines_couple_flips_l.
      iFrame ; iIntros (b) "α".
      destruct b ;
        rel_pures_l ; rel_pures_r ; rel_load_l ; rel_load_r ; rel_pures_l ; rel_pures_r ;
        iApply (refines_na_close with "[- $Hclose]").
        all: iSplitL ; [iModIntro ; iRight ; iFrame|] ;
          rewrite refines_eq /refines_def ; iIntros (?) "??" ;
          iLöb as "HH" ; wp_rec ; now iApply ("HH" with "[$]").
  Qed.

End proofs.

Theorem H_K_refinement :
  ∅ ⊨ H ≤ctx≤ K : () → TBool.
Proof.
  eapply ctx_refines_transitive.
  - eapply (refines_sound prelogrelΣ).
    intros. simpl. apply: H_H_with_tape_rel.
  - eapply (refines_sound prelogrelΣ).
    intros. apply: H_with_tape_K_rel.
Qed.

Theorem K_H_refinement :
  ∅ ⊨ K ≤ctx≤ H : () → TBool.
Proof.
  eapply ctx_refines_transitive.
  - eapply (refines_sound prelogrelΣ).
    intros. simpl. apply: K_H_with_tape_rel.
  - eapply (refines_sound prelogrelΣ).
    intros. apply: H_with_tape_H_rel.
Qed.

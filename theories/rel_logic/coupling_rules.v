(** * Coupling rules  *)
From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext.
From clutch.program_logic Require Import lifting ectx_lifting. 
From clutch.prob_lang Require Import lang notation tactics metatheory.
From clutch.rel_logic Require Export primitive_laws spec_ra spec_rules. 

(* TODO: can we factor out a clever lemma to avoid duplication in all the
   coupling lemmas? *)
Section rules.
  Context `{!clutchGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types v : val.
  Implicit Types l : loc.

  (** * state_step(α, N) ~ state_step(α', N) coupling *)
  Lemma wp_couple_tapes N f `{Bij (fin (S N)) (fin (S N)) f} E e α αₛ ns nsₛ Φ :
    to_val e = None →
    nclose specN ⊆ E →
    spec_ctx ∗ ▷ αₛ ↪ₛ (N; nsₛ) ∗ ▷ α ↪ (N; ns) ∗
    (∀ n : fin (S N), αₛ ↪ₛ (N; nsₛ ++ [f n]) ∗ α ↪ (N; ns ++ [n]) -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (He ?) "(#Hinv & >Hαs & >Hα & Hwp)".
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
    iSpecialize ("Hwp" with "[$Hα $Hαs]").
    rewrite !wp_unfold /wp_pre /= He.
    iMod ("Hwp" $! (state_upd_tapes <[α:=(N; ns ++ [b]) : tape]> _)
           with "[$Hh1 $Hauth2 $Ht1]") as "Hwp".
    iModIntro. done.
  Qed.

  Lemma wp_couple_tapes_gen n1 n2 (R : fin (S n1) → fin (S n2) → Prop) E e α αₛ zs zsₛ Φ :
    to_val e = None →
    nclose specN ⊆ E →
    Rcoupl (dunif (S n1)) (dunif (S n2)) R →
    spec_ctx ∗ ▷ αₛ ↪ₛ (n2; zsₛ) ∗ ▷ α ↪ (n1; zs) ∗
    (∀ z1 z2, ⌜R z1 z2⌝ ∗ αₛ ↪ₛ (n2; zsₛ ++ [z2]) ∗ α ↪ (n1; zs ++ [z1]) -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (He ? Hcoupl) "(#Hinv & >Hαs & >Hα & Hwp)".
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
        apply elem_of_list_In, elem_of_elements, elem_of_dom; eauto. }
    iExists _.
    iSplit.
    { iPureIntro.
      eapply Rcoupl_pos_R, (Rcoupl_state_step_gen _ _ R); eauto.
    }
    iIntros (σ2 σ2' ((a & b & Hab & -> & ->) & ? & ?)).
    (* Update our resources *)
    iMod (spec_interp_update (e0', (state_upd_tapes <[αₛ:=(n2; zsₛ ++ [b]) : tape]> σ0'))
           with "Hauth2 Hspec0") as "[Hauth2 Hspec0]".
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?%lookup_total_correct.
    iDestruct (ghost_map_lookup with "Htapes Hαs") as %?%lookup_total_correct.
    simplify_map_eq.
    iMod (ghost_map_update ((n1; zs ++ [a]) : tape) with "Ht1 Hα") as "[Ht1 Hα]".
    iMod (ghost_map_update ((n2; zsₛ ++ [b]) : tape) with "Htapes Hαs") as "[Htapes Hαs]".
    (* Close the [spec_ctx] invariant again, so the assumption can access all invariants  *)
    iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hauth Hheap Hspec0 Htapes]") as "_".
    { iModIntro. rewrite /spec_inv.
      iExists _, _, (state_upd_tapes _ _), 0. simpl.
      iFrame. rewrite exec_O dret_1_1 //; iSplit; auto. }
    (* Our [WP] assumption with the updated resources now suffices to prove the goal *)
    iSpecialize ("Hwp" with "[$Hα $Hαs //]").
    rewrite !wp_unfold /wp_pre /= He.
    iMod ("Hwp" $! (state_upd_tapes <[α:=(n1; zs ++ [a]) : tape]> _) with "[$Hh1 $Hauth2 Ht1]") as "Hwp"; auto.
  Qed.

  Lemma wp_couple_tapes_eq N E e α αₛ ns nsₛ Φ :
    to_val e = None →
    nclose specN ⊆ E →
    spec_ctx ∗ ▷ αₛ ↪ₛ (N; nsₛ) ∗ ▷ α ↪ (N; ns) ∗
    (∀ n : fin (S N), αₛ ↪ₛ (N; nsₛ ++ [n]) ∗ α ↪ (N; ns ++ [n]) -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof. by eapply (wp_couple_tapes _ (Datatypes.id)). Qed.

  Lemma wp_couple_tapesN_eq m E N e α αₛ ns nsₛ Φ :
    to_val e = None →
    nclose specN ⊆ E →
    spec_ctx ∗ ▷ αₛ ↪ₛ (N; nsₛ) ∗ ▷ α ↪ (N; ns) ∗
    (∀ ns', ⌜length ns' = m ⌝ ∗ αₛ ↪ₛ (N; nsₛ ++ ns') ∗ α ↪ (N; ns ++ ns') -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (??).
    iInduction m as [| m] "IH" forall (ns nsₛ).
    - iIntros "(#Hctx & >Hα & >Hαₛ & Hwp)".
      iApply ("Hwp" $! []).
      rewrite 2!app_nil_r.
      by iFrame. 
    - iIntros "(#Hctx & >Hα & >Hαₛ & Hwp)".
      iApply "IH". iFrame "Hα Hαₛ Hctx".
      iIntros (?) "(%Hlen & Hα & Hαₛ)".
      iApply wp_couple_tapes_eq; [done|done|].
      iFrame "Hα Hαₛ Hctx".
      iIntros (n) "(Hα&Hαₛ)".
      iApply ("Hwp" $! (_ ++ [_])).
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
    ▷ α ↪ (N; ns) ∗ refines_right K (rand #z from #()) ∗
    (∀ n : fin (S N), α ↪ (N; ns ++ [n]) ∗ refines_right K #(f n) -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (-> He ?) "(>Hα & [#Hinv Hj] & Hwp)".
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
    iSpecialize ("Hwp" with "[$]").
    rewrite !wp_unfold /wp_pre /= He.
    iMod ("Hwp" $! (state_upd_tapes <[α:=(_; ns ++ [b]) : tape]> σ1)
           with "[$Hh1 $Hauth2 $Ht1]") as "Hwp".
    done.
  Qed.

  Lemma wp_couple_tape_rand_eq N K E α z ns Φ e :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    nclose specN ⊆ E →
    ▷ α ↪ (N; ns) ∗ refines_right K (rand #z from #()) ∗
    (∀ n : fin (S N), α ↪ (N; ns ++ [n]) ∗ refines_right K #n -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof. apply (wp_couple_tape_rand _ Datatypes.id). Qed.

  (** * rand(unit, N) ~ state_step(α', N) coupling *)
  Lemma wp_couple_rand_tape N f `{Bij (fin (S N)) (fin (S N)) f} z E α ns Φ :
    TCEq N (Z.to_nat z) →
    nclose specN ⊆ E →
    spec_ctx ∗ ▷ α ↪ₛ (N; ns) ∗
    ▷ (∀ n : fin (S N), α ↪ₛ (N; ns ++ [f n]) -∗ Φ #n)
    ⊢ WP rand #z from #() @ E {{ Φ }}.
  Proof.
    iIntros (-> He) "(#Hinv & >Hαs & Hwp)".
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

  Lemma wp_couple_rand_tape_eq E α N z ns Φ :
    TCEq N (Z.to_nat z) →
    nclose specN ⊆ E →
    spec_ctx ∗ ▷ α ↪ₛ (N; ns) ∗
    ▷ (∀ n : fin (S N), α ↪ₛ (N; ns ++ [n]) -∗ Φ #n)
    ⊢ WP rand #z from #() @ E {{ Φ }}.
  Proof. apply (wp_couple_rand_tape _ Datatypes.id). Qed.

  (** * rand(α, N) ~ rand(unit, N) coupling *)
  Lemma wp_couple_rand_lbl_rand N f `{Bij (fin (S N)) (fin (S N)) f} z K E α Φ :
    TCEq N (Z.to_nat z) →
    nclose specN ⊆ E →
    ▷ α ↪ (N; []) ∗ refines_right K (rand #z from #()) ∗
    ▷ (∀ n : fin (S N), α ↪ (N; []) ∗ refines_right K #(f n) -∗ Φ #n)
    ⊢ WP rand #z from #lbl:α @ E {{ Φ }}.
  Proof.
    iIntros (??) "(>Hα & [#Hinv Hr] & HΦ)".
    iApply wp_couple_tape_rand => //.
    iFrame "Hinv". iFrame => /=.
    iIntros (n) "(Hα & Hr)".
    iApply (wp_rand_tape with "Hα").
    iIntros "!> Hα".
    iApply ("HΦ" with "[$]").
  Qed.

  Lemma wp_couple_rand_lbl_rand_eq N z K E α Φ :
    TCEq N (Z.to_nat z) →
    nclose specN ⊆ E →
    ▷ α ↪ (N; []) ∗ refines_right K (rand #z from #()) ∗
    ▷ (∀ n : fin (S N), α ↪ (N; []) ∗ refines_right K #n -∗ Φ #n)
    ⊢ WP rand #z from #lbl:α @ E {{ Φ }}.
  Proof. apply (wp_couple_rand_lbl_rand _ Datatypes.id). Qed.

  (** * rand(unit, N) ~ rand(α, N) coupling *)
  Lemma wp_couple_rand_rand_lbl N f `{Bij (fin (S N)) (fin (S N)) f} z K E α Φ :
    TCEq N (Z.to_nat z) →
    nclose specN ⊆ E →
    ▷ α ↪ₛ (N; []) ∗ refines_right K (rand #z from #lbl:α) ∗
    ▷ (∀ n : fin (S N), α ↪ₛ (N; []) ∗ refines_right K #(f n) -∗ Φ #n)
    ⊢ WP rand #z from #() @ E {{ Φ }}.
  Proof.
    iIntros (??) "(Hα & [#Hinv Hr] & Hwp)".
    iApply wp_fupd.
    iApply wp_couple_rand_tape => //.
    iFrame "Hinv". iFrame => /=.
    iIntros "!>" (n) "Hα".
    iMod (step_rand with "[$]") as "(_ & Hr & Hα)"; [done|].
    iModIntro.
    iApply ("Hwp" with "[$]").
  Qed.

  Lemma wp_couple_rand_rand_lbl_eq N z K E α Φ :
    TCEq N (Z.to_nat z) →
    nclose specN ⊆ E →
    ▷ α ↪ₛ (N; []) ∗ refines_right K (rand #z from #lbl:α) ∗
    ▷ (∀ (n : fin (S N)), α ↪ₛ (N; []) ∗ refines_right K #n -∗ Φ #n)
    ⊢ WP rand #z from #() @ E {{ Φ }}.
  Proof. apply (wp_couple_rand_rand_lbl _ Datatypes.id). Qed.

  (** * rand(unit, N) ~ rand(unit, N) coupling *)
  Lemma wp_couple_rand_rand N f `{Bij (fin (S N)) (fin (S N)) f} z K E Φ :
    TCEq N (Z.to_nat z) →
    nclose specN ⊆ E →
    refines_right K (rand #z from #()) ∗
    ▷ (∀ n : fin (S N), refines_right K #(f n) -∗ Φ #n)
    ⊢ WP rand #z from #() @ E {{ Φ }}.
  Proof.
    iIntros (-> ?) "([#Hinv Hr] & Hwp)".
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
      eapply Rcoupl_dmap.
      eapply Rcoupl_mono; [by apply (Rcoupl_rand_rand _ f)|].
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
    refines_right K (rand #z from #()) ∗
    ▷ (∀ n : fin (S N), refines_right K #n -∗ Φ #n)
    ⊢ WP rand #z from #() @ E {{ Φ }}.
  Proof. apply (wp_couple_rand_rand _ Datatypes.id). Qed.

    (** * rand(α, N) ~ rand(α, N) coupling *)
  Lemma wp_couple_rand_lbl_rand_lbl N f `{Bij (fin (S N)) (fin (S N)) f} z K E α α' Φ :
    TCEq N (Z.to_nat z) →
    nclose specN ⊆ E →
    ▷ α ↪ (N; []) ∗ ▷ α' ↪ₛ (N; []) ∗ refines_right K (rand #z from #lbl:α') ∗
    ▷ (∀ n : fin (S N), α ↪ (N; []) ∗ α' ↪ₛ (N; []) ∗ refines_right K #(f n) -∗ Φ #n)
    ⊢ WP rand #z from #lbl:α @ E {{ Φ }}.
  Proof.
    iIntros (??) "(>Hα & >Hαs & [#Hinv Hr] & Hwp)".
    iApply wp_couple_tapes; [done|done|].
    iFrame "Hinv Hα Hαs".
    iIntros (n) "(Hαs & Hα) /=".
    iMod (step_rand with "[$Hr $Hinv $Hαs]") as "(_ & Hr & Hαs)"; [done|].
    iApply (wp_rand_tape with "Hα").
    iIntros "!> Hα".
    iApply ("Hwp" with "[$]").
  Qed.

  Lemma wp_couple_rand_lbl_rand_lbl_eq N z K E α α' Φ :
    TCEq N (Z.to_nat z) →
    nclose specN ⊆ E →
    ▷ α ↪ (N; []) ∗ ▷ α' ↪ₛ (N; []) ∗ refines_right K (rand #z from #lbl:α') ∗
    ▷ (∀ n : fin (S N), α ↪ (N; []) ∗ α' ↪ₛ (N; []) ∗ refines_right K #n -∗ Φ #n)
    ⊢ WP rand #z from #lbl:α @ E {{ Φ }}.
  Proof. apply (wp_couple_rand_lbl_rand_lbl _ Datatypes.id). Qed.

  (** * rand(α, N) ~ rand(α, N) wrong bound coupling *)
  Lemma wp_couple_rand_lbl_rand_lbl_wrong N M f `{Bij (fin (S N)) (fin (S N)) f}
    z K E α α' Φ xs ys :
    TCEq N (Z.to_nat z) →
    N ≠ M →
    nclose specN ⊆ E →
    ▷ α ↪ (M; xs) ∗ ▷ α' ↪ₛ (M; ys) ∗ refines_right K (rand #z from #lbl:α') ∗
    ▷ (∀ n : fin (S N), α ↪ (M; xs) ∗ α' ↪ₛ (M; ys) ∗ refines_right K #(f n) -∗ Φ #n)
    ⊢ WP rand #z from #lbl:α @ E {{ Φ }}.
  Proof.
    iIntros (-> ??) "(>Hα & >Hαs & [#Hinv Hr] & Hwp)".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1') "[[Hh1 Ht1] Hauth2]".
    iInv specN as (ρ' e0' σ0' m) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_prog_auth_frag_agree with "Hauth Hr") as %->.
    iDestruct (spec_interp_auth_frag_agree with "Hauth2 Hspec0") as %<-.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?.
    iDestruct (ghost_map_lookup with "Htapes Hαs") as %?.
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
      by eapply RandTapeOtherS. }
    iSplit.
    { iPureIntro. simpl.
      rewrite fill_dmap // -(dret_id_right (prim_step _ _)) /=.
      eapply Rcoupl_dmap.
      eapply Rcoupl_mono; [by eapply (Rcoupl_rand_lbl_rand_lbl_wrong _ _ f)|].
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

  (** * rand(α, N) ~ rand(N) wrong bound coupling *)
  Lemma wp_couple_rand_lbl_rand_wrong N M f `{Bij (fin (S N)) (fin (S N)) f} z K E α Φ xs :
    TCEq N (Z.to_nat z) →
    N ≠ M →
    nclose specN ⊆ E →
    ▷ α ↪ (M; xs) ∗ refines_right K (rand #z from #()) ∗
    ▷ (∀ n : fin (S N), α ↪ (M; xs) ∗ refines_right K #(f n) -∗ Φ #n)
    ⊢ WP rand #z from #lbl:α @ E {{ Φ }}.
  Proof.
    iIntros (-> ??) "(>Hα & [#Hinv Hr] & Hwp)".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1') "[[Hh1 Ht1] Hauth2]".
    iInv specN as (ρ' e0' σ0' m) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_prog_auth_frag_agree with "Hauth Hr") as %->.
    iDestruct (spec_interp_auth_frag_agree with "Hauth2 Hspec0") as %<-.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?.
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
      by eapply RandTapeOtherS. }
    iSplit.
    { iPureIntro. simpl.
      rewrite fill_dmap // -(dret_id_right (prim_step _ _)) /=.
      eapply Rcoupl_dmap.
      eapply Rcoupl_mono; [by eapply (Rcoupl_rand_lbl_rand_wrong _ _ f)|].
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

  (** * rand(N) ~ rand(α, N) wrong bound coupling *)
  Lemma wp_couple_rand_rand_lbl_wrong N M f `{Bij (fin (S N)) (fin (S N)) f} z K E α Φ ys :
    TCEq N (Z.to_nat z) →
    N ≠ M →
    nclose specN ⊆ E →
    ▷ α ↪ₛ (M; ys) ∗ refines_right K (rand #z from #lbl:α) ∗
    ▷ (∀ n : fin (S N), α ↪ₛ (M; ys) ∗ refines_right K #(f n) -∗ Φ #n)
    ⊢ WP rand #z from #() @ E {{ Φ }}.
  Proof.
    iIntros (-> ??) "(> Hα & [#Hinv Hr] & Hwp)".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1') "[[Hh1 Ht1] Hauth2]".
    iInv specN as (ρ' e0' σ0' m) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_prog_auth_frag_agree with "Hauth Hr") as %->.
    iDestruct (spec_interp_auth_frag_agree with "Hauth2 Hspec0") as %<-.
    iDestruct (ghost_map_lookup with "Htapes Hα") as %?.
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
      by eapply RandNoTapeS. }
    iSplit.
    { iPureIntro. simpl.
      rewrite fill_dmap // -(dret_id_right (prim_step _ _)) /=.
      eapply Rcoupl_dmap.
      eapply Rcoupl_mono; [by eapply (Rcoupl_rand_rand_lbl_wrong _ _ f)|].
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

End rules.

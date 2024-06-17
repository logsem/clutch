(** * Coupling rules  *)
From stdpp Require Import namespaces gmap mapset.
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext.
From clutch.prob_lang Require Import lang notation tactics metatheory erasure.
From clutch.clutch Require Import lifting ectx_lifting.
From clutch.clutch Require Export weakestpre primitive_laws.

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
    ▷ αₛ ↪ₛ (N; nsₛ) ∗ ▷ α ↪ (N; ns) ∗
    (∀ n : fin (S N), αₛ ↪ₛ (N; nsₛ ++ [f n]) ∗ α ↪ (N; ns ++ [n]) -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros "(>Hαs & >Hα & Hwp)".
    iApply wp_lift_step_spec_couple.
    iIntros (σ1 e1' σ1') "[[Hh Ht] Hs]".
    iDestruct (ghost_map_lookup with "Ht Hα") as %?.
    iDestruct (spec_auth_lookup_tape with "Hs Hαs") as %?.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".
    iApply spec_coupl_erasables.
    iExists _, (state_step σ1 α), (state_step σ1' αₛ).
    iSplit; [iPureIntro|].
    { by eapply Rcoupl_pos_R, (Rcoupl_state_state _ f). }
    do 2 (iSplit; [iPureIntro; by eapply state_step_erasable|]).
    iIntros (σ2 σ2' ((b & -> & ->) & ? & ?)).
    iFrame.
    iMod (ghost_map_update with "Ht Hα") as "[$ Hα]".
    iMod (spec_auth_update_tape with "Hs Hαs") as "[$ Hαs]".
    iModIntro.
    iMod "Hclose" as "_"; iModIntro.
    by iApply ("Hwp" with "[$]").
  Qed.

  Lemma wp_couple_tapes_rel n1 n2 (R : fin (S n1) → fin (S n2) → Prop) E e α αₛ zs zsₛ Φ :
    Rcoupl (dunif (S n1)) (dunif (S n2)) R →
    ▷ αₛ ↪ₛ (n2; zsₛ) ∗ ▷ α ↪ (n1; zs) ∗
    (∀ z1 z2, ⌜R z1 z2⌝ ∗ αₛ ↪ₛ (n2; zsₛ ++ [z2]) ∗ α ↪ (n1; zs ++ [z1]) -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (?) "(>Hαs & >Hα & Hwp)".
    iApply wp_lift_step_spec_couple.
    iIntros (σ1 e1' σ1') "[[Hh Ht] Hs]".
    iDestruct (ghost_map_lookup with "Ht Hα") as %?.
    iDestruct (spec_auth_lookup_tape with "Hs Hαs") as %?.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".
    iApply spec_coupl_erasables.
    iExists _, (state_step σ1 α), (state_step σ1' αₛ).
    iSplit; [iPureIntro|].
    { by eapply Rcoupl_pos_R, (Rcoupl_state_step_gen _ _ R). }
    do 2 (iSplit; [iPureIntro; by eapply state_step_erasable|]).
    iIntros (σ2 σ2' ((? & ? & ? & -> & ->) & ? & ?)).
    iFrame.
    iMod (ghost_map_update with "Ht Hα") as "[$ Hα]".
    iMod (spec_auth_update_tape with "Hs Hαs") as "[$ Hαs]".
    iModIntro.
    iMod "Hclose" as "_"; iModIntro.
    iApply ("Hwp" with "[-]"). by iFrame.
  Qed.

  Lemma wp_couple_tapes_eq N E e α αₛ ns nsₛ Φ :
    ▷ αₛ ↪ₛ (N; nsₛ) ∗ ▷ α ↪ (N; ns) ∗
    (∀ n : fin (S N), αₛ ↪ₛ (N; nsₛ ++ [n]) ∗ α ↪ (N; ns ++ [n]) -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof. by eapply (wp_couple_tapes _ (Datatypes.id)). Qed.

  Lemma wp_couple_tapesN_eq m E N e α αₛ ns nsₛ Φ :
    ▷ αₛ ↪ₛ (N; nsₛ) ∗ ▷ α ↪ (N; ns) ∗
    (∀ ns', ⌜length ns' = m ⌝ ∗ αₛ ↪ₛ (N; nsₛ ++ ns') ∗ α ↪ (N; ns ++ ns') -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iInduction m as [| m] "IH" forall (ns nsₛ).
    - iIntros "(>Hα & >Hαₛ & Hwp)".
      iApply ("Hwp" $! []).
      rewrite 2!app_nil_r.
      by iFrame.
    - iIntros "(>Hα & >Hαₛ & Hwp)".
      iApply "IH". iFrame "Hα Hαₛ".
      iIntros (?) "(%Hlen & Hα & Hαₛ)".
      iApply wp_couple_tapes_eq.
      iFrame "Hα Hαₛ".
      iIntros (n) "(Hα & Hαₛ)".
      iApply ("Hwp" $! (_ ++ [_])).
      rewrite 2!app_assoc. iFrame.
      iPureIntro.
      rewrite app_length Hlen /=.
      lia.
  Qed.

  (** * state_step(α, N) ~ rand(N) coupling *)
  Lemma wp_couple_tape_rand N f `{Bij (fin (S N)) (fin (S N)) f} K E α z ns Φ e :
    TCEq N (Z.to_nat z) →
    ▷ α ↪ (N; ns) ∗ ⤇ fill K (rand #z) ∗
    (∀ n : fin (S N), α ↪ (N; ns ++ [n]) ∗ ⤇ fill K #(f n) -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (->) "(>Hα & Hj & Hwp)".
    iApply wp_lift_step_spec_couple.
    iIntros (σ1 e1' σ1') "[[Hh Ht] Hs]".
    iDestruct (ghost_map_lookup with "Ht Hα") as %?.
    iDestruct (spec_auth_prog_agree with "Hs Hj") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".
    iApply spec_coupl_erasable_steps.
    iExists (λ σ2 '(e2', σ2'),
        ∃ n, σ2 = state_upd_tapes <[α := (_; ns ++ [n]) : tape]> σ1
             ∧ (e2', σ2') = (fill K #(f n), σ1')), 1, (state_step σ1 α).
    iSplit; [iPureIntro|].
    { rewrite pexec_1 step_or_final_no_final; last first.
      { apply reducible_not_final. solve_red. }
      rewrite -(dret_id_right (state_step _ _)) /= fill_dmap //.
      eapply Rcoupl_dbind => /=; last first.
      { eapply Rcoupl_pos_R. by eapply Rcoupl_state_rand. }
      intros σ2 (e2' & σ2') ((b & -> & ->) & ? & ?).
      apply Rcoupl_dret=>/=. eauto. }
    iSplit; [iPureIntro; by eapply state_step_erasable|].
    iIntros (σ2 e2' σ2' (b & -> & [= -> ->])).
    iFrame.
    iMod (ghost_map_update with "Ht Hα") as "[$ Hα]".
    iMod (spec_update_prog with "Hs Hj") as "[$ Hj]".
    iModIntro; iMod "Hclose" as "_"; iModIntro.
    by iApply ("Hwp" with "[$]").
  Qed.

  Lemma wp_couple_tape_rand_eq N K E α z ns Φ e :
    TCEq N (Z.to_nat z) →
    ▷ α ↪ (N; ns) ∗ ⤇ fill K (rand #z) ∗
    (∀ n : fin (S N), α ↪ (N; ns ++ [n]) ∗ ⤇ fill K #n -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof. apply (wp_couple_tape_rand _ Datatypes.id). Qed.

  (** * rand(N) ~ state_step(α', N) coupling *)
  Lemma wp_couple_rand_tape N f `{Bij (fin (S N)) (fin (S N)) f} z E α ns :
    TCEq N (Z.to_nat z) →
    {{{ ▷ α ↪ₛ (N; ns) }}}
      rand #z @ E
    {{{ (n : fin (S N)), RET #n; α ↪ₛ (N; ns ++ [f n]) }}}.
  Proof.
    iIntros (Hz Ψ) ">Hαs HΨ".
    iApply wp_lift_step_prog_couple; [done|].
    iIntros (σ1 e1' σ1') "[Hσ Hs]".
    iDestruct (spec_auth_lookup_tape with "Hs Hαs") as %?.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".
    simpl in *.
    rewrite /prog_coupl.
    iExists (λ ρ2 ρ2', ∃ (n : fin (S N)),
                ρ2 = (Val #n, σ1) ∧
                ρ2' = (e1', state_upd_tapes <[α := (N; ns ++ [f n]) : tape]> σ1')),
      0, (state_step σ1' α).
    setoid_rewrite pexec_O.
    iSplit; [iPureIntro|].
    { eapply head_prim_reducible; eauto with head_step. }
    iSplit; [iPureIntro|].
    { rewrite /= -(dret_id_right (prim_step _ _)) /=.
      eapply Rcoupl_dbind; last first.
      { eapply (Rcoupl_rand_state _ f) => //. rewrite Hz //. }
      intros [] ? (?& [= -> ->] & ->).
      eapply Rcoupl_dret. eauto. }
    iSplit; [iPureIntro|].
    { by eapply state_step_erasable. }
    iIntros (e2 σ e2' σ2' (n & [= -> ->] & [= -> ->])).
    iMod (spec_auth_update_tape with "Hs Hαs") as "[$ Hαs]".
    iFrame "Hσ".
    iIntros "!> !>".
    iMod "Hclose" as "_".
    iApply wp_value.
    by iApply "HΨ".
  Qed.

  Lemma wp_couple_rand_tape_eq E α N z ns :
    TCEq N (Z.to_nat z) →
    {{{ ▷ α ↪ₛ (N; ns) }}}
      rand #z @ E
    {{{ (n : fin (S N)), RET #n; α ↪ₛ (N; ns ++ [n]) }}}.
  Proof. apply (wp_couple_rand_tape _ Datatypes.id). Qed.

  (** * rand(α, N) ~ rand(N) coupling *)
  Lemma wp_couple_rand_lbl_rand N f `{Bij (fin (S N)) (fin (S N)) f} z K E α :
    TCEq N (Z.to_nat z) →
    {{{ ▷ α ↪ (N; []) ∗ ⤇ fill K (rand #z) }}}
      rand(#lbl:α) #z @ E
    {{{ (n : fin (S N)), RET #n;  α ↪ (N; []) ∗ ⤇ fill K #(f n) }}}.
  Proof.
    iIntros (? Ψ) "(>Hα & Hj) HΨ".
    iApply wp_couple_tape_rand => //.
    iFrame => /=.
    iIntros (n) "(Hα & Hr)".
    iApply (wp_rand_tape with "Hα").
    iIntros "!> Hα".
    iApply ("HΨ" with "[$]").
  Qed.

  Lemma wp_couple_rand_lbl_rand_eq N z K E α :
    TCEq N (Z.to_nat z) →
    {{{ ▷ α ↪ (N; []) ∗ ⤇ fill K (rand #z) }}}
      rand(#lbl:α) #z @ E
    {{{ (n : fin (S N)), RET #n; α ↪ (N; []) ∗ ⤇ fill K #n }}}.
  Proof. apply (wp_couple_rand_lbl_rand _ Datatypes.id). Qed.

  (** * rand(N) ~ rand(α, N) coupling *)
  Lemma wp_couple_rand_rand_lbl N f `{Bij (fin (S N)) (fin (S N)) f} z K E α :
    TCEq N (Z.to_nat z) →
    {{{ ▷ α ↪ₛ (N; []) ∗ ⤇ fill K (rand(#lbl:α) #z) }}}
      rand #z @ E
    {{{ (n : fin (S N)), RET #n; α ↪ₛ (N; []) ∗ ⤇ fill K #(f n) }}}.
  Proof.
    iIntros (? Ψ) "(Hα & Hr) HΨ".
    iApply wp_spec_update.
    iApply (wp_couple_rand_tape with "Hα").
    iIntros "!>" (n) "Hα /=".
    iMod (step_rand with "[$Hr $Hα]") as "[? ?]".
    by iApply ("HΨ" with "[$]").
  Qed.
  Lemma wp_couple_rand_rand_lbl_eq N z K E α :
    TCEq N (Z.to_nat z) →
    {{{ ▷ α ↪ₛ (N; []) ∗ ⤇ fill K (rand(#lbl:α) #z) }}}
      rand #z @ E
    {{{ (n : fin (S N)), RET #n; α ↪ₛ (N; []) ∗ ⤇ fill K #n }}}.
  Proof. apply (wp_couple_rand_rand_lbl _ Datatypes.id). Qed.

  (** * rand(N) ~ rand(N) coupling *)
  Lemma wp_couple_rand_rand N f `{Bij (fin (S N)) (fin (S N)) f} z K E :
    TCEq N (Z.to_nat z) →
    {{{ ⤇ fill K (rand #z) }}}
      rand #z @ E
    {{{ (n : fin (S N)), RET #n; ⤇ fill K #(f n) }}}.
  Proof.
    iIntros (-> Ψ) "Hr HΨ".
    iApply wp_lift_step_prog_couple; [done|].
    iIntros (σ1 e1' σ1') "[Hσ Hs] /=".
    iDestruct (spec_auth_prog_agree with "Hs Hr") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".
    iApply prog_coupl_prim_steps.
    iExists (λ '(e2, σ2) '(e2', σ2'),
              ∃ (n : fin _), (e2, σ2) = (Val #n, σ1) ∧
                             (e2', σ2') = (fill K #(f n), σ1')).
    iSplit; [iPureIntro|].
    { eapply head_prim_reducible; eauto with head_step. }
    iSplit; [iPureIntro|].
    { rewrite /= fill_dmap //.
      rewrite /= -(dret_id_right (prim_step _ _)) /=.
      eapply Rcoupl_dmap.
      eapply Rcoupl_mono; [by apply (Rcoupl_rand_rand _ f)|].
      intros [] [] (b & [=] & [=])=>/=.
      simplify_eq. eauto. }
    iIntros (e2 σ2 e2' σ2' (b & [= -> ->] & [= -> ->])) "!>".
    iMod (spec_update_prog with "Hs Hr") as "[$ Hr]".
    iMod "Hclose" as "_".
    iFrame.
    iApply wp_value.
    by iApply "HΨ".
  Qed.

  Lemma wp_couple_rand_rand_eq N z K E :
    TCEq N (Z.to_nat z) →
    {{{ ⤇ fill K (rand #z) }}}
      rand #z @ E
    {{{ (n : fin (S N)), RET #n; ⤇ fill K #n }}}.
  Proof. apply (wp_couple_rand_rand _ Datatypes.id). Qed.

    (** * rand(α, N) ~ rand(α, N) coupling *)
  Lemma wp_couple_rand_lbl_rand_lbl N f `{Bij (fin (S N)) (fin (S N)) f} z K E α α' :
    TCEq N (Z.to_nat z) →
    {{{ ▷ α ↪ (N; []) ∗ ▷ α' ↪ₛ (N; []) ∗ ⤇ fill K (rand(#lbl:α') #z) }}}
      rand(#lbl:α) #z @ E
    {{{ (n : fin (S N)), RET #n; α ↪ (N; []) ∗ α' ↪ₛ (N; []) ∗ ⤇ fill K #(f n) }}}.
  Proof.
    iIntros (??) "(>Hα & >Hαs & Hr) HΨ".
    iApply wp_couple_tapes. iFrame.
    iIntros (n) "(Hαs & Hα) /=".
    iMod (step_rand with "[$Hr $Hαs]") as "[? ?]".
    iApply (wp_rand_tape with "Hα").
    iIntros "!> Hα".
    iApply ("HΨ" with "[$]").
  Qed.

  Lemma wp_couple_rand_lbl_rand_lbl_eq N z K E α α' :
    TCEq N (Z.to_nat z) →
    {{{ ▷ α ↪ (N; []) ∗ ▷ α' ↪ₛ (N; []) ∗ ⤇ fill K (rand(#lbl:α') #z) }}}
      rand(#lbl:α) #z @ E
    {{{ (n : fin (S N)), RET #n; α ↪ (N; []) ∗ α' ↪ₛ (N; []) ∗ ⤇ fill K #n }}}.
  Proof. apply (wp_couple_rand_lbl_rand_lbl _ Datatypes.id). Qed.

  (** * rand(α, N) ~ rand(α, N) wrong bound coupling *)
  Lemma wp_couple_rand_lbl_rand_lbl_wrong N M f `{Bij (fin (S N)) (fin (S N)) f} z K E α α' xs ys :
    TCEq N (Z.to_nat z) →
    N ≠ M →
    {{{ ▷ α ↪ (M; xs) ∗ ▷ α' ↪ₛ (M; ys) ∗ ⤇ fill K (rand(#lbl:α') #z) }}}
      rand(#lbl:α) #z @ E
    {{{ (n : fin (S N)), RET #n; α ↪ (M; xs) ∗ α' ↪ₛ (M; ys) ∗ ⤇ fill K #(f n) }}}.
  Proof.
    iIntros (-> ? Ψ) "(>Hα & >Hαs & Hr) Hwp".
    iApply wp_lift_step_prog_couple; [done|].
    iIntros (σ1 e1' σ1') "[[Hh Ht] Hs]".
    iDestruct (ghost_map_lookup with "Ht Hα") as %?.
    iDestruct (spec_auth_lookup_tape with "Hs Hαs") as %?.
    iDestruct (spec_auth_prog_agree with "Hs Hr") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".
    iApply prog_coupl_prim_steps.
    iExists
      (λ ρ2 ρ2',
        ∃ (n : fin _), ρ2 = (Val #n, σ1) ∧ ρ2' = (fill K #(f n), σ1')).
    iSplit; [iPureIntro|].
    { eapply head_prim_reducible; eauto with head_step. }
    iSplit; [iPureIntro|].
    { rewrite /= fill_dmap //.
      rewrite -(dret_id_right (prim_step _ _)) /=.
      apply Rcoupl_dmap.
      eapply Rcoupl_mono; [by eapply (Rcoupl_rand_lbl_rand_lbl_wrong _ _ f)|].
      intros [] [] (b & [=] & [=])=>/=.
      simplify_eq. eauto. }
    iIntros (e2 σ2 e2' σ2' (b & [= -> ->] & [= -> ->])) "!>".
    iMod (spec_update_prog with "Hs Hr") as "[$ Hr]".
    iFrame.
    iMod "Hclose" as "_".
    iApply wp_value.
    by iApply ("Hwp" with "[$]").
  Qed.

  (** * rand(α, N) ~ rand(N) wrong bound coupling *)
  Lemma wp_couple_rand_lbl_rand_wrong N M f `{Bij (fin (S N)) (fin (S N)) f} z K E α xs :
    TCEq N (Z.to_nat z) →
    N ≠ M →
    {{{ ▷ α ↪ (M; xs) ∗ ⤇ fill K (rand #z) }}}
      rand(#lbl:α) #z @ E
    {{{ (n : fin (S N)), RET #n; α ↪ (M; xs) ∗ ⤇ fill K #(f n) }}}.
  Proof.
    iIntros (-> ? Ψ) "(>Hα & Hr) Hwp".
    iApply wp_lift_step_prog_couple; [done|].
    iIntros (σ1 e1' σ1') "[[Hh Ht] Hs]".
    iDestruct (ghost_map_lookup with "Ht Hα") as %?.
    iDestruct (spec_auth_prog_agree with "Hs Hr") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".
    iApply prog_coupl_prim_steps.
    iExists
      (λ ρ2 ρ2',
        ∃ (n : fin _), ρ2 = (Val #n, σ1) ∧ ρ2' = (fill K #(f n), σ1')).
    iSplit; [iPureIntro|].
    { eapply head_prim_reducible; eauto with head_step. }
    iSplit; [iPureIntro|].
    { rewrite /= fill_dmap //.
      rewrite -(dret_id_right (prim_step _ _)) /=.
      apply Rcoupl_dmap.
      eapply Rcoupl_mono; [by eapply (Rcoupl_rand_lbl_rand_wrong _ _ f)|].
      intros [] [] (b & [=] & [=])=>/=.
      simplify_eq. eauto. }
    iIntros (e2 σ2 e2' σ2' (b & [= -> ->] & [= -> ->])) "!>".
    iMod (spec_update_prog with "Hs Hr") as "[$ Hr]".
    iFrame.
    iMod "Hclose" as "_".
    iApply wp_value.
    by iApply ("Hwp" with "[$]").
  Qed.

  (** * rand(N) ~ rand(α, N) wrong bound coupling *)
  Lemma wp_couple_rand_rand_lbl_wrong N M f `{Bij (fin (S N)) (fin (S N)) f} z K E α ys :
    TCEq N (Z.to_nat z) →
    N ≠ M →
    {{{ ▷ α ↪ₛ (M; ys) ∗ ⤇ fill K (rand(#lbl:α) #z) }}}
      rand #z @ E
    {{{ (n : fin (S N)), RET #n; α ↪ₛ (M; ys) ∗ ⤇ fill K #(f n) }}}.
  Proof.
    iIntros (-> ? Ψ) "(>Hαs & Hr) Hwp".
    iApply wp_lift_step_prog_couple; [done|].
    iIntros (σ1 e1' σ1') "[Hσ Hs]".
    iDestruct (spec_auth_lookup_tape with "Hs Hαs") as %?.
    iDestruct (spec_auth_prog_agree with "Hs Hr") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".
    iApply prog_coupl_prim_steps.
    iExists
      (λ ρ2 ρ2',
        ∃ (n : fin _), ρ2 = (Val #n, σ1) ∧ ρ2' = (fill K #(f n), σ1')).
    iSplit; [iPureIntro|].
    { eapply head_prim_reducible; eauto with head_step. }
    iSplit; [iPureIntro|].
    { rewrite /= fill_dmap //.
      rewrite -(dret_id_right (prim_step _ _)) /=.
      apply Rcoupl_dmap.
      eapply Rcoupl_mono; [by eapply (Rcoupl_rand_rand_lbl_wrong _ _ f)|].
      intros [] [] (b & [=] & [=])=>/=.
      simplify_eq. eauto. }
    iIntros (e2 σ2 e2' σ2' (b & [= -> ->] & [= -> ->])) "!>".
    iMod (spec_update_prog with "Hs Hr") as "[$ Hr]".
    iFrame.
    iMod "Hclose" as "_".
    iApply wp_value.
    by iApply ("Hwp" with "[$]").
  Qed.

  (** test for coupling *)
  Lemma wp_couple_1_3 e E α1 α2 αₛ ns1 ns2 nsₛ Φ:
    (∀ σ1, state_interp σ1 ={E}=∗ ⌜reducible (e, σ1)⌝ ∗ state_interp σ1) ∗
    ▷ αₛ ↪ₛ (3; nsₛ) ∗ ▷ α1 ↪ (1; ns1) ∗ ▷ α2 ↪ (1; ns2)∗
    (∀ x y z, αₛ ↪ₛ (3; nsₛ ++ [z]) ∗
              α1 ↪ (1; ns1 ++ [x]) ∗
              α2 ↪ (1; ns2 ++ [y]) ∗
              ⌜(2*fin_to_nat x + fin_to_nat y = fin_to_nat z)%nat⌝ -∗
              WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros "(Hred & >Hαs & >Hα1 & >Hα2 & Hwp)".
    iApply wp_lift_step_spec_couple.
    iIntros (σ1 e1' σ1') "[[Hh1 Ht1] Hs]".
    iDestruct ("Hred" with "[$]") as ">[%Hr [Hh1 Ht1]]".
    iDestruct (ghost_map_lookup with "Ht1 Hα1") as %H1.
    iDestruct (ghost_map_lookup with "Ht1 Hα2") as %H2.
    iDestruct (ghost_map_elem_ne with "Hα1 Hα2") as %?.
    iDestruct (spec_auth_lookup_tape with "Hs Hαs") as %?.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".
    iApply spec_coupl_erasables.
    iExists _, _, _.
    iSplit; [iPureIntro|].
    { by eapply Rcoupl_state_1_3. }
    iSplit; [iPureIntro|].
    { eapply erasable_dbind.
      - by eapply state_step_erasable.
      - intros ? K. rewrite state_step_support_equiv_rel in K.
        cut (∃ (l : list(fin (2))), tapes σ' !! α2 = Some (1%nat; l)).
        + elim. intros. by eapply state_step_erasable.
        + inversion K as [??????H3 Ha Hb Hc]; simplify_eq.
          rewrite lookup_total_alt in Ha.
          rewrite H1 /= in Ha. simplify_eq.
          eexists. rewrite /state_upd_tapes /= lookup_insert_Some.
          naive_solver. }
    iSplit; [iPureIntro|].
    { by eapply state_step_erasable. }
    iIntros (σ2 σ2' (x & y & z & -> & -> & ?)) "!>".
    iMod (ghost_map_update ((1; ns1 ++ [x]) : tape) with "Ht1 Hα1") as "[Ht1 Hα1]".
    iMod (ghost_map_update ((1; ns2 ++ [y]) : tape) with "Ht1 Hα2") as "[$ Hα2]".
    iMod (spec_auth_update_tape with "Hs Hαs") as "[$ Hαs]".
    iFrame "Hh1".
    iMod "Hclose" as "_".
    iApply "Hwp". by iFrame.
  Qed.

End rules.

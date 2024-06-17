From clutch.paris Require Import adequacy.
From clutch.paris Require Export paris.
Set Default Proof Using "Type*".
Open Scope R.

Section rejection_sampler.
  Context {N M:nat}.
  (** Changing from M<=N to M<N, because we want to reject the case where N=M
      otherwise, the maths gets ugly
      Luckily, when N=M, the refinement becomes trivial
   *)
  Context {Hineq: (M < N)%nat}.

  Local Lemma NM1: 1 < (S N / (S N - S M)).
  Proof.
    rewrite !S_INR.
    apply lt_INR in Hineq.
    apply Rcomplements.Rlt_div_r; [lra|].
    rewrite Rmult_1_l.
    pose proof pos_INR M. lra.
  Qed.
  Local Hint Resolve NM1:core.

  Local Lemma NMpos : 0 < (S N / (S N - S M)).
  Proof. pose proof NM1; lra. Qed.

  Local Hint Resolve NMpos:core.

  Definition rejection_sampler_prog: val :=
    rec: "f" "_" :=
      let: "x" := rand #N in
      if: ("x" ≤ #M) then "x"
      else "f" #().

  Definition rejection_sampler_prog_annotated: expr :=
    let: "α" := alloc #N in
    (rec: "f" "_" :=
      let: "x" := rand("α") #N  in
      if: ("x" ≤ #M) then "x"
      else "f" #()).

  Definition simpl_sampler_prog: val :=
    λ: "_", rand #M.

  Definition simpl_sampler_prog_annotated: expr :=
    let: "α" := alloc #M in
    λ: "_", rand("α") #M.

  Context `{!parisGS Σ}.

  Lemma wp_rejection_simpl:
    {{{ ⤇ simpl_sampler_prog_annotated #() }}}
      rejection_sampler_prog_annotated #()
    {{{ (v : val), RET v; ⤇ v }}}.
  Proof.
    iIntros (?) "Hspec H".
    rewrite /simpl_sampler_prog_annotated /rejection_sampler_prog_annotated.
    wp_apply (wp_alloc_tape); [done|].
    iIntros (α) "Hα".
    tp_alloctape as αₛ "Hαₛ".
    tp_pures. do 3 wp_pure.
    iLöb as "IH" forall "Hspec Hα Hαₛ".
    wp_pures.
    wp_apply (wp_couple_fragmented_rand_rand_leq M N); try (done || lia).

    rewrite Nat2Z.id. iFrame.
    iIntros (n).
    case_match eqn:Heqn.
    - iIntros "[Hα Hαₛ]".
      simpl.
      wp_apply (wp_rand_tape with "[$]").
      iIntros "Hα".
      wp_pures.
      rewrite bool_decide_eq_true_2; last lia.
      tp_rand.
      wp_pures.
      iModIntro.
      iApply "H".
      rewrite fin_to_nat_to_fin //.
    - iIntros "[Hα Hαₛ]".
      simpl.
      wp_apply (wp_rand_tape with "[$]").
      iIntros "Hα".
      wp_pures.
      rewrite bool_decide_eq_false_2; last lia.
      wp_pure.
      wp_apply ("IH" with "[$][$][$][$]").
  Qed.

  Definition rejection_sampler_prog_annotated' αₛ : val :=
    (rec: "f" "_" :=
      let: "x" := rand(#lbl:αₛ) #N  in
      if: ("x" ≤ #M) then "x"
      else "f" #()).

  Lemma wp_simpl_rejection_ind_aux (ε : R) α αₛ:
    0 < ε →
    ⤇ rejection_sampler_prog_annotated' αₛ #() -∗
    ↯ ε -∗ α ↪ (M; []) -∗ αₛ ↪ₛ (N; []) -∗
    (∀ (ε' : R), ⌜ε' = ((S N / (S N - S M)) * ε)%R⌝ -∗
                         ⤇ rejection_sampler_prog_annotated' αₛ #() -∗
                         ↯ ε' -∗ α ↪ (M; []) -∗ αₛ ↪ₛ (N; []) -∗
                         WP rand(#lbl:α) #M {{ v, ∃ v' : val, ⤇ v' ∗ ⌜v = v'⌝ }}) -∗
    WP rand(#lbl:α) #M {{ v, ∃ v' : val, ⤇ v' ∗ ⌜v = v'⌝ }}.
  Proof.
    iIntros (Hpos) "Hspec Hε Hα Hαₛ Hcnt".
    rewrite {1}/rejection_sampler_prog_annotated'.
    tp_pures.
    tp_bind (rand(#lbl:_) _)%E.
    assert (0 <= ε) as Hε by lra.
    set ε' := mknonnegreal _ Hε.
    replace ε with ε'.(nonneg); [|done].
    wp_apply (wp_couple_fragmented_rand_rand_leq_rev'
               with "[$Hε $Hα $Hαₛ Hspec Hcnt]"); [done|done|].
    iIntros (m). case_match eqn:Heqn.
    - simpl. iIntros "[Hα Hαₛ]".
      tp_rand.
      tp_pures. case_bool_decide; last lia.
      tp_pures.
      wp_apply (wp_rand_tape with "[$]").
      iIntros. iExists _. iFrame.
      iPureIntro.
      f_equal. by rewrite fin_to_nat_to_fin.
    - iIntros (ε'') "(% & Hα & Hαₛ & Hε)".
      simpl.
      tp_rand.
      tp_pures.
      case_bool_decide; first lia.
      tp_pure.
      iApply ("Hcnt" $! ε'' with "[][$][$][$][$]").
      by simplify_eq.
  Qed.

  Lemma wp_simpl_rejection (ε : R):
    0 < ε →
    ⤇ rejection_sampler_prog_annotated #() -∗
    ↯ ε -∗ WP simpl_sampler_prog_annotated #() {{ v, ∃ v' : val, ⤇ v' ∗ ⌜v = v'⌝ }}.
  Proof.
    iIntros (Hpos) "Hspec Hε".
    rewrite /simpl_sampler_prog_annotated/rejection_sampler_prog_annotated.
    wp_apply (wp_alloc_tape); first done.
    iIntros (α) "Hα".
    tp_alloctape as αₛ "Hαₛ".
    do 3 tp_pure.
    wp_pures. rewrite Nat2Z.id.
    iRevert "Hα Hαₛ Hspec".
    iApply (ec_ind_amp _ (S N / (S N - S M)) with "[] Hε"); [done|real_solver|].
    iIntros "!#" (??) "#IH ????".
    iApply (wp_simpl_rejection_ind_aux with "[$][$][$][$]"); [done|].
    iIntros (? H1) "? Hε ? ?". subst.
    by iApply ("IH" with "[Hε][$][$][$]").
  Qed.

  Lemma wp_rejection_sampler_prog :
    ⤇ rejection_sampler_prog_annotated #() -∗
    WP rejection_sampler_prog #() {{ v, ∃ v' : val, ⤇ v' ∗ ⌜v = v'⌝ }}.
  Proof.
    iIntros "Hspec".
    rewrite /rejection_sampler_prog_annotated.
    tp_alloctape as α "Hα".
    do 3 tp_pure.
    iLöb as "IH" forall "Hspec Hα".
    rewrite /rejection_sampler_prog.
    wp_pures. tp_pures.
    wp_apply (wp_couple_rand_tape with "Hα").
    iIntros (n) "Hα". simpl.
    tp_pures.
    tp_bind (rand(_) _)%E.
    iMod (step_rand with "[$]") as "[Hspec Hα]".
    simpl.
    tp_pures. wp_pures.
    case_bool_decide.
    - tp_pures. wp_pures.
      iModIntro. iExists _. iFrame. done.
    - tp_pure. wp_pure.
      iApply ("IH" with "[$] [$]").
  Qed.

  Lemma wp_simpl_sampler_prog_annotated :
    ⤇ simpl_sampler_prog #() -∗
    WP simpl_sampler_prog_annotated #() {{ v, ∃ v' : val, ⤇ v' ∗ ⌜v = v'⌝ }}.
  Proof.
    iIntros "Hspec".
    rewrite /simpl_sampler_prog_annotated.
    rewrite /simpl_sampler_prog.
    wp_apply wp_alloc_tape; [done|].
    iIntros (α) "Hα".
    tp_pures. wp_pures.
    tp_bind (rand (_))%E.
    wp_apply (wp_couple_tape_rand with "[$Hα $Hspec]").
    iIntros (x) "[Hα Hspec]".
    simpl.
    wp_apply (wp_rand_tape with "[$]").
    iIntros. iExists _. iFrame. done.
  Qed.

  Lemma wp_rejection_sampler_prog_prog_annotated :
    ⤇ rejection_sampler_prog #() -∗
    WP rejection_sampler_prog_annotated #() {{ v, ∃ v' : val, ⤇ v' ∗ ⌜v = v'⌝ }}.
  Proof.
    iIntros "Hspec".
    rewrite /rejection_sampler_prog_annotated.
    wp_apply (wp_alloc_tape); first done.
    iIntros (α) "Hα".
    do 3 wp_pure.
    iLöb as "IH" forall "Hspec Hα".
    rewrite /rejection_sampler_prog.
    tp_pures. wp_pures.
    tp_bind (rand (_))%E.
    wp_apply (wp_couple_tape_rand with "[$Hα $Hspec]").
    iIntros (x) "[Hα Hspec]".
    simpl.
    wp_apply (wp_rand_tape with "[$]").
    iIntros.
    tp_pures; wp_pures.
    case_bool_decide.
    - tp_pures; wp_pures.
      iExists _. iFrame. done.
    - tp_pure. wp_pure.
      by iApply ("IH" with "[$][$]").
  Qed.

  Lemma wp_simpl_sampler_prog_prog_annotated :
    ⤇ simpl_sampler_prog_annotated #() -∗
    WP simpl_sampler_prog #() {{ v, ∃ v' : val, ⤇ v' ∗ ⌜v = v'⌝ }}.
  Proof.
    iIntros "Hspec".
    rewrite /simpl_sampler_prog_annotated.
    rewrite /simpl_sampler_prog.
    tp_alloctape as α "Hα".
    wp_pures. tp_pures.
    wp_apply (wp_couple_rand_rand_lbl _ _ _ [] with "[$]").
    rewrite Nat2Z.id.
    iIntros (?) "[Hα Hspec]".
    eauto.
  Qed.

End rejection_sampler.


Lemma ARcoupl_rejection_sampler_simpl (N M:nat) (Hineq : (M < N)%nat) σ:
  ARcoupl
    (lim_exec (@rejection_sampler_prog N M #(), σ))
    (lim_exec (@simpl_sampler_prog M #(), σ))
    (=) 0.
Proof.
  replace 0 with (0+0) by lra.
  eapply ARcoupl_eq_trans_l ; [done|done| |].
  { eapply (wp_adequacy parisΣ _ _ _ σ); [done|].
    iIntros (?) "? _".
    by iApply (@wp_rejection_sampler_prog _ _ Hineq). }

  replace 0 with (0+0) by lra.
  eapply (ARcoupl_eq_trans_r _ );
    [done|done| |]; last first.
  { eapply (wp_adequacy parisΣ _ _ σ); [done|].
    iIntros (?) "? _".
    by iApply (@wp_simpl_sampler_prog_annotated _ _ Hineq). }

  eapply (wp_adequacy parisΣ); [done|].
  iIntros (?) "? _".
  wp_apply (@wp_rejection_simpl _ _ Hineq with "[$]").
  eauto.
Qed.

Lemma ARcoupl_simpl_rejection_sampler (N M:nat) (Hineq : (M < N)%nat) σ:
  ARcoupl
    (lim_exec (@simpl_sampler_prog M #(), σ))
    (lim_exec (@rejection_sampler_prog N M #(), σ))
    (=) 0.
Proof.
  replace 0 with (0+0) by lra.
  eapply (ARcoupl_eq_trans_r); [done|done|..]; last first.
  { eapply (wp_adequacy parisΣ _ _ σ); [done|].
    iIntros (?) "? _".
    by iApply (@wp_rejection_sampler_prog_prog_annotated _ _ Hineq). }

  replace 0 with (0+0) by lra.
  eapply (ARcoupl_eq_trans_r); [done|done|..].
  { eapply (wp_adequacy parisΣ _ _ _ σ); [done|].
    iIntros (?) "? _".
    by iApply (@wp_simpl_sampler_prog_prog_annotated _ _ Hineq). }

  apply (wp_adequacy_error_lim parisΣ); [done|].
  iIntros.
  by wp_apply (@wp_simpl_rejection _ _ Hineq with "[$][$]").
Qed.

From clutch.approxis Require Import adequacy.
From clutch.approxis Require Export approxis.


From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.

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

  Context `{!approxisGS Σ}.


Tactic Notation "my_wp_alloctape" ident(l) "as" constr(H) :=
  let Htmp := iFresh in
  let finish _ :=
    first [intros l | fail 1 "wp_alloctape:" l "not fresh"];
    pm_reduce;
    lazymatch goal with
    | |- False => fail 1 "wp_alloc:" H "not fresh"
    | _ => iDestructHyp Htmp as H; wp_finish
    end in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
      let process_single _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_wp_alloctape _ _ _ Htmp K))
          |fail 1 "wp_alloc: cannot find 'AllocTape' in" e];
        [ idtac
        | tc_solve
        |finish ()]
      in process_single ()
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
      let process_single _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_wp_alloctape _ _ _ Htmp K))
          |fail 1 "wp_alloc: cannot find 'AllocTape' in" e];
        [tc_solve
        |finish ()]
      in process_single ()
  | _ => fail "wp_alloc: not a 'wp'"
  end.


Tactic Notation "my_wp_randtape" "as" constr(H) :=
  let Htmp := iFresh in
  let solve_wptac_mapsto_tape _ :=
    let l := match goal with |- _ = Some (_, (wptac_mapsto_tape ?l _ _ (_ :: _))%I) => l end in
    iAssumptionCore || fail "wp_load: cannot find" l "↦ ?" in
  let finish _ :=
    pm_reduce;
    lazymatch goal with
    | |- False => fail 1 "wp_alloc:" H "not fresh"
    | _ => iDestructHyp Htmp as H; wp_finish
    end in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_rand_tape _ _ _ _ Htmp K))
      |fail 1 "wp_load: cannot find 'Rand' in" e];
    [ | tc_solve | solve_wptac_mapsto_tape () | finish () ]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_rand_tape _ _ _ _ Htmp K))
      |fail 1 "wp_load: cannot find 'Rand' in" e];
    [idtac
    |tc_solve
    |solve_wptac_mapsto_tape ()
    |wp_finish]
  | _ => fail "wp_load: not a 'wp'"
  end.


Tactic Notation "my_tp_randnat" "as" constr(H) :=
  let finish _ :=
        ((iIntros H; tp_normalise) || fail 1 "tp_alloctape:" H "not correct intro pattern") in
  iStartProof;
  eapply tac_tp_randnat;
  [tc_solve || fail "tp_rand: cannot eliminate modality in the goal"
  | (* postpone solving [TCEq ...] until after the tape has been unified *)
  |iAssumptionCore || fail "tp_rand: cannot find the RHS"
  |tp_bind_helper
  |iAssumptionCore || fail "tp_rand: cannot find '? ↪ₛ ?'"
  |simpl; reflexivity || fail "tp_rand: this should not happen"
  |pm_reduce (* new goal *)];
  [tc_solve || fail "tp_rand: cannot convert bound to a natural number"
  | finish () ].


Tactic Notation "my_tp_allocnattape" ident(l) "as"  constr(H) :=
  let finish _ :=
    first [intros l | fail 1 "tp_allocnattape:" l "not fresh"];
    eexists; split;
    [ reduction.pm_reflexivity
    | (iIntros H; tp_normalise) || fail 1 "tp_alloctape:" H "not correct intro pattern" ] in
  iStartProof;
  eapply (tac_tp_allocnattape);
  [tc_solve || fail "tp_allocnattape: cannot eliminate modality in the goal"
  | (* postpone solving [TCEq ...] *)
  |iAssumptionCore || fail "tp_allocnattape: cannot find the RHS"
  |tp_bind_helper
  | ];
  [try tc_solve |
  | finish () ].

Lemma wp_rejection_simpl:
  {{{ ⤇ simpl_sampler_prog_annotated #() }}}
    rejection_sampler_prog_annotated #()
    {{{ (v : val), RET v; ⤇ v }}}.
Proof.
  iIntros (?) "Hspec H".
  rewrite /simpl_sampler_prog_annotated /rejection_sampler_prog_annotated.
  wp_alloctape α as "Hα".
  tp_allocnattape αs as "Hαₛ".
  tp_pures. do 3 wp_pure.
  iLöb as "IH" forall "Hspec Hα Hαₛ".
  wp_pures.
  wp_apply (wp_couple_fragmented_rand_rand_leq M N); try (done || lia).
  iFrame.
  iIntros (n).
  case_match eqn:Heqn.
  - iIntros "% [Hα [Hαₛ %]]".
    simpl.
    wp_randtape as "%".
    wp_pures.
    rewrite bool_decide_eq_true_2; last lia.
    (* tp_rand. *)
    tp_randnat.
    wp_pures.
    iModIntro.
    by iApply "H".
  - iIntros "% [Hα [Hαₛ %]]".
    simpl.
    wp_randtape as "%".
    wp_pures.
    apply bool_decide_eq_false_1 in Heqn.
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
    ↯ ε -∗ α ↪N (M; []) -∗ αₛ ↪ₛN (N; []) -∗
    (∀ (ε' : R), ⌜ε' = ((S N / (S N - S M)) * ε)%R⌝ -∗
                         ⤇ rejection_sampler_prog_annotated' αₛ #() -∗
                         ↯ ε' -∗ α ↪N (M; []) -∗ αₛ ↪ₛN (N; []) -∗
                         WP rand(#lbl:α) #M {{ v, ∃ v' : val, ⤇ v' ∗ ⌜v = v'⌝ }}) -∗
    WP rand(#lbl:α) #M {{ v, ∃ v' : val, ⤇ v' ∗ ⌜v = v'⌝ }}.
  Proof.
    iIntros (Hpos) "Hspec Hε Hα Hαₛ Hcnt".
    rewrite {1}/rejection_sampler_prog_annotated'.
    tp_pures.
    assert (0 <= ε) as Hε by lra.
    set ε' := mknonnegreal _ Hε.
    replace ε with ε'.(nonneg); [|done].
    wp_apply (wp_couple_fragmented_rand_rand_leq_rev'
               with "[$Hε $Hα $Hαₛ Hspec Hcnt]"); [done|done|].
    iIntros (m) "%". case_match eqn:Heqn.
    - iIntros "[Hα [Hαₛ %]]".
      (* tp_rand. *)
      tp_randnat.
      apply bool_decide_eq_true_1 in Heqn.
      tp_pures. case_bool_decide; last lia.
      tp_pures.
      wp_randtape.
      iExists _. iFrame.
      iPureIntro. done.
    - iIntros (ε'') "(% & Hα & Hαₛ & Hε & %)".
      iSimpl in "Hspec".
      (* tp_rand. *)
      tp_randnat.
      tp_pures.
      apply bool_decide_eq_false_1 in Heqn.
      case_bool_decide; first by (exfalso ; lia).
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
    wp_alloctape α as "Hα".
    tp_allocnattape αₛ as "Hαₛ".
    do 3 tp_pure.
    wp_pures.
    iRevert "Hα Hαₛ Hspec".
    iApply (ec_ind_amp _ (S N / (S N - S M)) with "[] Hε"); [done| |].
    { apply NM1. }
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
    tp_allocnattape α as "Hα".
    do 3 tp_pure.
    iLöb as "IH" forall "Hspec Hα".
    rewrite /rejection_sampler_prog.
    wp_pures. tp_pures.
    wp_apply (wp_couple_rand_tape with "Hα"); first done.
    iIntros (n) "(Hα&?)". simpl.
    tp_pures.
    tp_randnat.
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
    wp_alloctape α as "Hα".
    tp_pures. wp_pures.
    tp_bind (rand (_))%E.
    wp_apply (wp_couple_tape_rand with "[$Hα $Hspec]"); first done.
    iIntros (x) "[Hα [Hspec %]]".
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
    wp_alloctape α as "Hα".
    do 3 wp_pure.
    iLöb as "IH" forall "Hspec Hα".
    rewrite /rejection_sampler_prog.
    tp_pures. wp_pures.
    tp_bind (rand (_))%E.
    wp_apply (wp_couple_tape_rand with "[$Hα $Hspec]"); first done.
    iIntros (x) "[Hα [Hspec %]]".
    simpl.
    wp_randtape.
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
    tp_allocnattape α as "Hα".
    wp_pures. tp_pures.
    wp_apply (wp_couple_rand_rand_lbl _ _ _ [] with "[$]"); first done.
    iIntros (?) "[Hα [Hspec %]]".
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
  { eapply (wp_adequacy approxisΣ _ _ _ σ); [done|].
    iIntros (?) "? _".
    by iApply (@wp_rejection_sampler_prog _ _ Hineq). }

  replace 0 with (0+0) by lra.
  eapply (ARcoupl_eq_trans_r _ );
    [done|done| |]; last first.
  { eapply (wp_adequacy approxisΣ _ _ σ); [done|].
    iIntros (?) "? _".
    by iApply (@wp_simpl_sampler_prog_annotated _ _ Hineq). }

  eapply (wp_adequacy approxisΣ); [done|].
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
  { eapply (wp_adequacy approxisΣ _ _ σ); [done|].
    iIntros (?) "? _".
    by iApply (@wp_rejection_sampler_prog_prog_annotated _ _ Hineq). }

  replace 0 with (0+0) by lra.
  eapply (ARcoupl_eq_trans_r); [done|done|..].
  { eapply (wp_adequacy approxisΣ _ _ _ σ); [done|].
    iIntros (?) "? _".
    by iApply (@wp_simpl_sampler_prog_prog_annotated _ _ Hineq). }

  apply (wp_adequacy_error_lim approxisΣ); [done|].
  iIntros.
  by wp_apply (@wp_simpl_rejection _ _ Hineq with "[$][$]").
Qed.

Lemma rejection_sampler_correct N M (Hineq : (M<N)%nat) σ:
  (lim_exec (@rejection_sampler_prog N M #(), σ)) =
  (lim_exec (@simpl_sampler_prog M #(), σ)).
Proof.
  apply ARcoupl_antisym.
  - by apply ARcoupl_rejection_sampler_simpl.
  - by apply ARcoupl_simpl_rejection_sampler.
Qed.

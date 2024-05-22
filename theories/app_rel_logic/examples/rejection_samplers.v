From clutch.app_rel_logic Require Import adequacy.
From clutch.app_rel_logic Require Export paris.
Set Default Proof Using "Type*".
Open Scope R.

Section rejection_sampler.
  Context `{!parisGS Σ}.
  Context {N M:nat}.
  (** Changing from M<=N to M<N, because we want to reject the case where N=M 
      otherwise, the maths gets ugly
      Luckily, when N=M, the refinement becomes trivial
   *)
  Context {Hineq: M<N}.
  
  
  Local Lemma NM1: 1<(S N / (S N - S M)).
  Proof.
    rewrite !S_INR.
    apply Rcomplements.Rlt_div_r; first lra.
    rewrite Rmult_1_l.
    pose proof pos_INR M. lra.
  Qed.
  Local Hint Resolve NM1:core.
  
  Local Lemma NMpos: 0<(S N / (S N - S M)).
  Proof.
    pose proof NM1; lra.
  Qed.
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

  Lemma wp_rejection_simpl:
    ⤇ simpl_sampler_prog_annotated #() -∗
    € (0%NNR) -∗ WP rejection_sampler_prog_annotated #() {{ v, ∃ v' : val, ⤇ v' ∗ ⌜v = v'⌝ }}.
  Proof.
    iIntros "Hspec Herr".
    rewrite /simpl_sampler_prog_annotated /rejection_sampler_prog_annotated.
    wp_apply (wp_alloc_tape); first done.
    iIntros (α) "Hα".
    tp_alloctape as αₛ "Hαₛ".
    tp_pures. do 3 wp_pure.
    iLöb as "IH" forall "Hspec Herr Hα Hαₛ".
    wp_pures.
    wp_apply (wp_couple_fragmented_rand_rand_leq M N); try (done||lra).
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
      iExists _. iFrame.
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


  Lemma wp_simpl_rejection_ind_aux (ε:nonnegreal) α αₛ:
    (0%NNR < ε)%R ->
    ⤇ (rec: "f" "_" := let: "x" := rand(#lbl:αₛ) #N in if: "x" ≤ #M then "x" else "f" #())%V #() -∗
    € ε -∗ α ↪ (M; []) -∗ αₛ ↪ₛ (N; []) -∗
    ( ∀ (ε':nonnegreal), ⌜(nonneg ε' = (S N / (S N - S M)) * ε)%R⌝ -∗
                         ⤇ (rec: "f" "_" := let: "x" := rand(#lbl:αₛ) #N in if: "x" ≤ #M then "x" else "f" #())%V #() -∗
                         € ε' -∗ α ↪ (M; []) -∗ αₛ ↪ₛ (N; []) -∗
                         WP rand(#lbl:α) #M {{ v, ∃ v' : val, ⤇ v' ∗ ⌜v = v'⌝ }}
    ) -∗ WP rand(#lbl:α) #M {{ v, ∃ v' : val, ⤇ v' ∗ ⌜v = v'⌝ }}.
  Proof.
    iIntros (Hpos) "Hspec Hε Hα Hαₛ IH".
    tp_pures.
    tp_bind (rand(#lbl:_) _)%E.
    wp_apply wp_couple_fragmented_rand_rand_leq_rev'; last iFrame; [lra|done|..].
    iIntros (m). case_match eqn:Heqn.
    - simpl. iIntros "[Hα Hαₛ]".
      tp_rand.
      tp_pures. case_bool_decide; last lia.
      tp_pures.
      wp_apply (wp_rand_tape with "[$]").
      iIntros. iExists _. iFrame.
      iPureIntro.
      f_equal. by rewrite fin_to_nat_to_fin.
    - iIntros (ε') "(% & Hα & Hαₛ & Hε)".
      simpl.
      tp_rand.
      tp_pures.
      case_bool_decide; first lia.
      tp_pure.
      iApply ("IH" $! ε' with "[][$][$][$][$]"). done.
  Qed.
  
  Lemma wp_simpl_rejection (ε:nonnegreal):
    (0%NNR < ε)%R -> ⤇ rejection_sampler_prog_annotated #() -∗
    € ε -∗ WP simpl_sampler_prog_annotated #() {{ v, ∃ v' : val, ⤇ v' ∗ ⌜v = v'⌝ }}.
  Proof.
    iIntros (Hpos) "Hspec Hε".
    rewrite /simpl_sampler_prog_annotated/rejection_sampler_prog_annotated.
    wp_apply (wp_alloc_tape); first done.
    iIntros (α) "Hα".
    tp_alloctape as αₛ "Hαₛ".
    do 3 tp_pure.
    wp_pures. rewrite Nat2Z.id.
    iRevert "Hα Hαₛ Hspec".
    pose proof ec_ind_amp as H.
    iApply H; [| | |iFrame]; last first.
    - iModIntro. iIntros (??) "#IH ????". iApply (wp_simpl_rejection_ind_aux with "[$][$][$][$]").
      + done.
      + iIntros (? H1) "? Hε ? ?". iApply ("IH" with "[Hε][$][$][$]").
        iApply ec_spend_irrel; last done.
        instantiate (1 := mknonnegreal _ _).
        simpl. done.
    - done.
    - done.
      Unshelve.
      apply Rcomplements.Rdiv_le_0_compat.
      + apply pos_INR.
      + apply Rlt_0_minus. rewrite !S_INR. lra.
  Qed.

End rejection_sampler.


Lemma ARcoupl_rejection_sampler_simpl (N M:nat) (Hineq : M<N) σ:
  ARcoupl (lim_exec (@rejection_sampler_prog N M #(), σ))
    (lim_exec (@simpl_sampler_prog M #(), σ)) eq 0%NNR.
Proof.
  assert (parisGpreS parisΣ).
  { apply subG_parisGPreS. eapply subG_refl. }
  replace 0%NNR with (0+0)%NNR by (apply nnreal_ext; simpl; lra).
  eapply (ARcoupl_eq_trans_l _ (lim_exec(@rejection_sampler_prog_annotated N M #(), σ))); [done|done|..].
  { eapply wp_aRcoupl_lim; first done.
    iIntros (?) "Hspec Herr".
    rewrite /rejection_sampler_prog_annotated.
    rewrite /rejection_sampler_prog.
    tp_alloctape as α "Hα".
    do 3 tp_pure. 
    iLöb as "IH" forall "Hspec Hα Herr".
    wp_pures. tp_pures.
    wp_apply (wp_couple_rand_tape with "[$Hα Herr Hspec]").
    iIntros "!> %n Hα". simpl.
    tp_bind (rand(_) _)%E.
    (* TODO: why is this instance not be infered??? *)
    pose proof elim_modal_spec_update_wp.
    iMod (step_rand with "[$]") as "[Hspec Hα]".
    simpl.
    tp_pures. wp_pures.
    case_bool_decide.
    - tp_pures. wp_pures.
      iModIntro. iExists _. iFrame. done.
    - tp_pure. wp_pure. iApply ("IH" with "[$][$][$]").
  }
  replace 0%NNR with (0+0)%NNR by (apply nnreal_ext; simpl; lra).
  eapply (ARcoupl_eq_trans_r _ (lim_exec(@simpl_sampler_prog_annotated M #(), σ))); [done|done|..]; last first.
  { eapply wp_aRcoupl_lim; first done.
    iIntros (?) "Hspec Herr".
    rewrite /simpl_sampler_prog_annotated.
    rewrite /simpl_sampler_prog.
    wp_apply (wp_alloc_tape); first done.
    iIntros (α) "Hα".
    tp_pures. wp_pures.
    tp_bind (rand (_))%E.
    wp_apply (wp_couple_tape_rand with "[$Hα $Hspec Herr]"); [done|].
    iIntros (x) "[Hα Hspec]".
    simpl.
    wp_apply (wp_rand_tape with "[$]").
    iIntros. iExists _. iFrame. done.
  }
  eapply wp_aRcoupl_lim; first done.
  iIntros. wp_apply (wp_rejection_simpl with "[$]"). done.
  Unshelve.
  done.
Qed.


Lemma ARcoupl_simpl_rejection_sampler (N M:nat) (Hineq : M<N) σ:
  ARcoupl (lim_exec (@simpl_sampler_prog M #(), σ))
    (lim_exec (@rejection_sampler_prog N M #(), σ))
    eq 0%NNR.
Proof.
  assert (parisGpreS parisΣ).
  { apply subG_parisGPreS. eapply subG_refl. }
  replace 0%NNR with (0+0)%NNR by (apply nnreal_ext; simpl; lra).
  eapply (ARcoupl_eq_trans_r _ (lim_exec(@rejection_sampler_prog_annotated N M #(), σ))); [done|done|..]; last first.
  { (* rejection sampler annotated <= rejection sampler *)
    eapply wp_aRcoupl_lim; first done.
    iIntros (?) "Hspec Herr".
    rewrite /rejection_sampler_prog_annotated.
    rewrite /rejection_sampler_prog.
    wp_apply (wp_alloc_tape); first done.
    iIntros (α) "Hα".
    do 3 wp_pure.
    iLöb as "IH" forall "Hspec Herr Hα".
    tp_pures. wp_pures.
    tp_bind (rand (_))%E.
    wp_apply (wp_couple_tape_rand with "[$Hα $Hspec Herr]"); [done|].
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
  }
  replace 0%NNR with (0+0)%NNR by (apply nnreal_ext; simpl; lra).
  eapply (ARcoupl_eq_trans_r _ (lim_exec(@simpl_sampler_prog_annotated M #(), σ))); [done|done|..].
  { (* simpl <= simple annotated *)
    eapply wp_aRcoupl_lim; first done.
    iIntros (?) "Hspec Herr".
    rewrite /simpl_sampler_prog_annotated.
    rewrite /simpl_sampler_prog.
    tp_alloctape as α "Hα".
    wp_pures. tp_pures.
    iApply (wp_bind (λ x, fill [] x)).
    wp_apply (wp_couple_rand_rand_lbl _ _ _ []).
    rewrite Nat2Z.id. iFrame.
    iIntros "!> % [Hα Hspec]".
    simpl. wp_pures. iModIntro. iExists _. iFrame.
    done.
  }
  eapply wp_ARcoupl_epsilon_lim; first done.
  iIntros.
  wp_apply (wp_simpl_rejection with "[$][$]").
  done.
  Unshelve.
  all: done.
Qed.

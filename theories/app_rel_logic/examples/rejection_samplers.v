From clutch.app_rel_logic Require Import adequacy.
From clutch.app_rel_logic Require Export app_clutch.
Set Default Proof Using "Type*".
Open Scope R.

Section rejection_sampler.
  Context `{!app_clutchGS Σ}.
  Context {N M:nat}.
  Context {Hineq: M<=N}.

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
    wp_apply (wp_couple_fragmented_rand_rand_leq M N); try done.
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

End rejection_sampler.


Lemma ARcoupl_rejection_sampler_simpl (N M:nat) (Hineq : M<=N) σ:
  ARcoupl (lim_exec (@rejection_sampler_prog N M #(), σ))
    (lim_exec (@simpl_sampler_prog M #(), σ)) eq 0%NNR.
Proof.
  assert (app_clutchGpreS app_clutchΣ).
  { apply subG_app_clutchGPreS. eapply subG_refl. }
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


Lemma ARcoupl_simpl_rejection_sampler (N M:nat) (Hineq : M<=N) σ:
  ARcoupl (lim_exec (@simpl_sampler_prog M #(), σ))
    (lim_exec (@rejection_sampler_prog N M #(), σ))
    eq 0%NNR.
Proof.
  assert (app_clutchGpreS app_clutchΣ).
  { apply subG_app_clutchGPreS. eapply subG_refl. }
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
    iApply (wp_bind (λ x, x)).
    wp_apply (wp_couple_rand_rand_lbl _ _ _ []).
    rewrite Nat2Z.id. iFrame.
    iIntros "!> % [Hα Hspec]".
    simpl. wp_pures. iModIntro. iExists _. iFrame.
    done.
  }
  eapply wp_ARcoupl_epsilon_lim; first done.
  iIntros.
  admit.
Admitted.

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
    do 2 tp_pure.
    iLöb as "IH" forall "Hspec Hα Herr".
    wp_pures. tp_pures.
    (* need couple tapes and state steps urgh*)
    admit.
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
    (* need couple tapes and state steps*)
    admit. }
  eapply wp_aRcoupl_lim; first done.
  iIntros. wp_apply (wp_rejection_simpl with "[$]"). done.
  Admitted.

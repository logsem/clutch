From Coq Require Import Reals Psatz.
From clutch.prob_lang Require Import lang notation.
From clutch.tpref_logic Require Import weakestpre spec primitive_laws proofmode adequacy.
From clutch.prob Require Import distribution markov.
From clutch.tpref_logic.examples Require Import flip.
#[local] Open Scope R.

(** A geometric random walk in which every step is a geometric random walk *)
Inductive state :=
| q0 | q1 | qf.

#[export] Instance state_dec : EqDecision state.
Proof. solve_decision. Defined.
#[export] Program Instance state_finite : Finite state := {| enum := [q0; q1; qf] |}.
Next Obligation.
  do 2 (constructor; [set_solver|]). apply NoDup_singleton.
Qed.
Next Obligation. intros []; set_solver. Qed.

Definition mstep (s : state) : distr state :=
  match s with
  | q0 => b ← fair_coin; dret (if b then qf else q1)
  | q1 => b ← fair_coin; dret (if b then q0 else q1)
  | qf => dzero
  end.

Definition mto_final (s : state) : option state :=
  match s with qf => Some qf | _ => None end.

Definition model_mixin : MarkovMixin mstep mto_final.
Proof. constructor. by intros [] [] []; simplify_eq=>/=. Qed.

Canonical Structure random_walk_nested : markov := Markov _ _ model_mixin.

#[global] Program Instance rw_nested_rsm :
  rsm (λ s, match s with | q0 => 2 | q1 => 3 | qf => 0 end) (1 / 2).
Next Obligation. simpl. real_solver. Qed.
Next Obligation. lra. Qed.
Next Obligation.
  simpl; intros [] Hf=>/=.
  - rewrite dbind_det; [done|apply fair_coin_mass|].
    intros. apply dret_mass.
  - rewrite dbind_det; [done|apply fair_coin_mass|].
    intros. apply dret_mass.
  - exfalso. eauto.
Qed.
Next Obligation.
  simpl. intros [] ?; [lra..|]. eauto.
Qed.
Next Obligation.
  intros a Hf. simpl.
   apply (ex_seriesC_le _ (λ a', step a a' * 3)); [|by apply ex_seriesC_scal_r].
  intros []; real_solver.
Qed.
Next Obligation.
  intros [] Hf => /=; [| |exfalso; eauto].
  - rewrite Expval_dbind.
    + rewrite Expval_fair_coin 2!Expval_dret. lra.
    + intros []; lra.
    + apply ex_seriesC_finite.
  - rewrite Expval_dbind.
    + rewrite Expval_fair_coin 2!Expval_dret. lra.
    + intros []; lra.
    + apply ex_seriesC_finite.
Qed.

Lemma random_walk_nested_terminates :
  SeriesC (lim_exec q0) = 1.
Proof. eapply rsm_term_limexec. Qed.

(** A random generator for a list of list of Booleans *)
Definition listgen : val :=
  rec: "listgen" "f" :=
    if: flip then NONE else
      let: "h" := "f" #() in
      let: "t" := "listgen" "f" in
      SOME ("h", "t").

Definition listgen_list_bool : expr :=
  listgen (λ: <>, listgen (λ: <>, flip))%E.

Lemma Rcoupl_mstep q :
  ¬ is_final q →
  Rcoupl
    fair_coin (mstep q)
    (λ b s,
      match q with
      | q0 => s = if b then qf else q1
      | q1 => s = if b then q0 else q1
      | _ => False
      end).
Proof.
  intros ?.
  rewrite -{1}(dret_id_right fair_coin).
  destruct q; [| |exfalso; eauto]; simpl.
  - eapply Rcoupl_dbind; [|eapply Rcoupl_eq].
    intros ? [] ->; by eapply Rcoupl_dret.
  - eapply Rcoupl_dbind; [|eapply Rcoupl_eq].
    intros ? [] ->; by eapply Rcoupl_dret.
Qed.

Section specs.
  Context `{!tprG random_walk_nested Σ}.

  Lemma wp_listgen1 E :
    ⟨⟨⟨ specF q1 ⟩⟩⟩
      listgen (λ: <>, flip)%V @ E
    ⟨⟨⟨ v, RET v; specF q0 ⟩⟩⟩.
  Proof.
    iLöb as "IH".
    iIntros (Ψ) "Hspec HΨ".
    rewrite /listgen.
    wp_pures; rewrite -/flip -/listgen.
    wp_apply (rwp_couple_flip with "Hspec").
    { apply Rcoupl_mstep. eauto. }
    iIntros ([] s) "[Hspec %]"; subst.
    { wp_pures. iModIntro. iApply "HΨ". eauto. }
    wp_pures.
    wp_apply rwp_flip; [done|].
    iIntros (b) "_".
    wp_pures.
    wp_apply ("IH" with "Hspec").
    iIntros (v) "Hspec".
    wp_pures.
    iModIntro.
    by iApply "HΨ".
  Qed.

  Lemma wp_listgen2 E :
    ⟨⟨⟨ specF q0 ⟩⟩⟩
      listgen (λ: <>, listgen (λ: <>, flip)%V)%V @ E
    ⟨⟨⟨ v, RET v; specF qf ⟩⟩⟩.
  Proof.
    iLöb as "IH".
    iIntros (Ψ) "Hspec HΨ".
    rewrite /listgen.
    wp_pures; rewrite -/flip -/listgen.
    wp_apply (rwp_couple_flip with "Hspec").
    { eapply Rcoupl_mstep. eauto. }
    iIntros ([] s) "[Hspec ->]".
    { wp_pures. iModIntro. iApply "HΨ". eauto. }
    do 2 wp_pure _.
    wp_apply (wp_listgen1 with "Hspec").
    iIntros (v) "Hspec".
    wp_pures.
    wp_apply ("IH" with "Hspec").
    iIntros (w) "Hspec".
    wp_pures.
    iModIntro.
    by iApply "HΨ".
  Qed.

End specs.

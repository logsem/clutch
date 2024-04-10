From Coq Require Import Reals Psatz.
From clutch.prob_lang Require Import lang notation.
From clutch.tpref_logic Require Import weakestpre primitive_laws proofmode adequacy.
From clutch.prob Require Import distribution markov.
From clutch.tpref_logic.examples Require Import flip.
#[local] Open Scope R.

(** A random list generator *)
Definition listgen : val :=
  rec: "listgen" "f" :=
    if: flip then NONE else
      let: "h" := "f" #() in
      let: "t" := "listgen" "f" in
      SOME ("h", "t").

(** A random generator for a list of list of Booleans *)
Definition listgen_list_bool : expr :=
  listgen (λ: <>, listgen (λ: <>, flip)%V)%V.

(** [listgen_list_bool] corresponds to a geometric random walk in which every
    step is a geometric random walk.  *)
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

(** The model almost-surely terminates *)
#[export] Program Instance rw_nested_rsm :
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
  intros a Hf. apply ex_seriesC_finite.
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

(** With the [random_walk_nested] model we can prove termination of
    [listgen_list_bool] in a fairly straightforward but ad-hoc way.  *)
Section specs_random_walk_nested.
  Context `{!tprG random_walk_nested Σ}.

  Lemma wp_listgen_flip :
    ⟨⟨⟨ specF q1 ⟩⟩⟩
      listgen (λ: <>, flip)%V
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

  Lemma wp_listgen_list_bool :
    ⟨⟨⟨ specF q0 ⟩⟩⟩
      listgen (λ: <>, listgen (λ: <>, flip)%V)%V
    ⟨⟨⟨ v, RET v; specF qf ⟩⟩⟩.
  Proof.
    iLöb as "IH".
    iIntros (Ψ) "Hspec HΨ".
    rewrite /listgen_list_bool /listgen.
    wp_pures; rewrite -/flip -/listgen.
    wp_apply (rwp_couple_flip with "Hspec").
    { eapply Rcoupl_mstep. eauto. }
    iIntros ([] s) "[Hspec ->]".
    { wp_pures. iModIntro. iApply "HΨ". eauto. }
    wp_pures.
    wp_apply (wp_listgen_flip with "Hspec").
    iIntros (v) "Hspec".
    wp_pures.
    wp_apply ("IH" with "Hspec").
    iIntros (w) "Hspec".
    wp_pures.
    iModIntro.
    by iApply "HΨ".
  Qed.

End specs_random_walk_nested.

(** Ideally, we'd like to have a single spec for [listgen] that is expressive
    enough to prove termination of [listgen_list_bool] by applying it
    twice. However, it seems like we need a more general model construction to
    do this: Both [wp_listgen_flip] and [wp_listgen_list_bool] are specs of
    [listgen] (for particular choices of the generator [f]) but
    [wp_listgen_list_bool] always takes the model to the final state [qf]
    whereas [wp_listgen_flip] doesn't. However [q0] is actually the "final"
    state of the inner random walk so morally the specs are in fact the
    same. What we seem to need is something akin to a recursive Markov chain. *)
Notation initial := (inl false).
Notation final := (inl true).
Notation inner m := (inr m).

Section nested_model.
  Context (δ : markov) (m0 : mstate δ).

  Definition nested_state : Type := bool + mstate δ.

  Definition nested_step (s : nested_state) : distr nested_state :=
    match s with
    | initial =>
        b ← fair_coin; dret (if b then final else inner m0)
    | final => dzero
    | inner m =>
        match to_final m with
        | None => m' ← step m; dret (inner m')
        | Some _ => dret initial
        end
    end.

  Definition nested_to_final (s : nested_state) : option () :=
    if s is final then Some () else None.

  Definition nested_mixin : MarkovMixin nested_step nested_to_final.
  Proof. constructor. intros [[]|] [] [[]|]; simplify_eq=>//=. Qed.

  Canonical Structure nested_markov : markov := Markov _ _ nested_mixin.

  #[export] Program Instance nested_rsm `{!rsm (δ := δ) h ϵ} :
    rsm (λ (s : mstate nested_markov),
        match s with
        | initial => h m0 + 4 * ϵ
        | final => 0
        | inner m => h m + h m0 + 6 * ϵ
        end)%R ϵ.
  Next Obligation.
    intros h ϵ Hrsm.
    pose proof (rsm_nneg m0); pose proof rsm_eps_pos.
    intros [[] | m] => /=; [done|lra|].
    pose proof (rsm_nneg m). lra.
  Qed.
  Next Obligation. intros; apply rsm_eps_pos. Qed.
  Next Obligation.
    intros h ϵ Hrsm [[]|] Hf => /=.
    - exfalso. eauto.
    - rewrite dbind_det; [done|apply fair_coin_mass|].
      intros. apply dret_mass.
    - case_match; [rewrite dret_mass //|].
      rewrite dbind_mass.
      setoid_rewrite dret_mass.
      setoid_rewrite Rmult_1_r.
      apply rsm_step_total. eauto.
  Qed.
  Next Obligation.
    intros h ϵ Hrsm.
    pose proof (rsm_nneg m0); pose proof rsm_eps_pos.
    intros [[] | m] => /= ?; [eauto|lra|].
    pose proof (rsm_nneg m). lra.
  Qed.
  Next Obligation.
    intros h ϵ Hrsm [[] | m] => /= ?.
    - eapply ex_seriesC_ext; [|eapply ex_seriesC_0].
      intros [[]|] => /=; rewrite dzero_0; lra.
    - eapply ex_expval_fair_coin_dbind. intros b. eapply ex_expval_dret.
    - case_match; [eapply ex_expval_dret|].
      assert (Hf : ¬ is_final m) by eauto.
      pose proof (rsm_nneg m0); pose proof rsm_eps_pos.
      eapply ex_expval_dbind.
      + intros [[]|]; [lra..|]. pose proof (rsm_nneg m1). lra.
      + rewrite /ex_expval.
        setoid_rewrite Expval_dret.
        setoid_rewrite Rmult_plus_distr_l.
        eapply ex_seriesC_plus; [|by eapply ex_seriesC_scal_r].
        setoid_rewrite Rmult_plus_distr_l.
        eapply ex_seriesC_plus; [|by eapply ex_seriesC_scal_r].
        by eapply rsm_int.
      + intros a. eapply ex_expval_dret.
  Qed.
  Next Obligation.
    intros h ϵ Hrsm [[] | m] => /= ?;
      pose proof (rsm_nneg m0); pose proof rsm_eps_pos.
    - exfalso; eauto.
    - rewrite Expval_dbind.
      + rewrite Expval_fair_coin 2!Expval_dret. lra.
      + intros [[]| m] => /=; [lra..|]. pose proof (rsm_nneg m). lra.
      + eapply ex_expval_fair_coin_dbind => b. eapply ex_expval_dret.
    - case_match.
      + rewrite Expval_dret. pose proof (rsm_nneg m).
        lra.
      + rewrite Expval_dbind.
        * rewrite {1}/Expval.
          erewrite SeriesC_ext; last first.
          { intros ?. rewrite Expval_dret //. }
          setoid_rewrite Rmult_plus_distr_l at 1.
          assert (Hf : ¬ is_final m) by eauto.
          rewrite SeriesC_plus; last first.
          { by eapply ex_seriesC_scal_r. }
          { setoid_rewrite Rmult_plus_distr_l.
            eapply ex_seriesC_plus; [by eapply rsm_int|].
            by eapply ex_seriesC_scal_r. }
          setoid_rewrite Rmult_plus_distr_l.
          rewrite SeriesC_plus; last first.
          { by eapply ex_seriesC_scal_r. }
          { by eapply rsm_int. }
          pose proof (rsm_dec m Hf) as Hdec.
          rewrite /Expval in Hdec.
          rewrite 2!SeriesC_scal_r.
          rewrite rsm_step_total //.
          lra.
        * intros [[]|]; [lra..|]. pose proof (rsm_nneg m1). lra.
        * eapply ex_expval_dbind.
          { intros [[]|]; [lra..|]. pose proof (rsm_nneg m1). lra. }
          { eapply ex_seriesC_ext.
            { intros ?. rewrite Expval_dret //. }
            setoid_rewrite Rmult_plus_distr_l.
            eapply ex_seriesC_plus; [|by eapply ex_seriesC_scal_r].
            setoid_rewrite Rmult_plus_distr_l.
            eapply ex_seriesC_plus; [|by eapply ex_seriesC_scal_r].
            eapply rsm_int. eauto. }
          intros s. eapply ex_expval_dret.
  Qed.

End nested_model.

Lemma Rcoupl_nested_step_initial δ m0 :
  Rcoupl
    fair_coin
    (nested_step δ m0 initial)
    (λ b s, s = if b then final else inner m0).
Proof.
  rewrite /nested_step /=.
  rewrite -{1}(dret_id_right fair_coin).
  eapply Rcoupl_dbind; [|eapply Rcoupl_eq].
  intros ? [] ->; by eapply Rcoupl_dret.
Qed.

Section nested_ho_spec.
  Context {δ : markov} {m0 : mstate δ} `{!tprG (nested_markov δ m0) Σ}.

  Lemma spec_restart m E :
    is_final m →
    specF (inner m) -∗ spec_updateN 1 E (specF initial).
  Proof.
    iIntros ([mf Hm]) "Hspec". iIntros (s) "Hs".
    iDestruct (spec_auth_agree with "Hs Hspec") as %->.
    iExists initial.
    iMod (spec_auth_update with "Hs Hspec") as "[$ $]".
    iModIntro. iPureIntro.
    rewrite stepN_Sn /=.
    rewrite Hm.
    rewrite dret_id_left /=.
    by apply dret_1.
  Qed.

  Lemma wp_listgen (f : val) :
    ⟨⟨⟨ specF (inner m0) ⟩⟩⟩
      f #()
    ⟨⟨⟨ m v, RET v; specF (inner m) ∗ ⌜is_final m⌝ ⟩⟩⟩ -∗
    ⟨⟨⟨ specF initial ⟩⟩⟩
      listgen f
    ⟨⟨⟨ v, RET v; specF final ⟩⟩⟩.
  Proof.
    iIntros "#Hf".
    iLöb as "IH".
    iIntros (Ψ) "!# Hspec HΨ".
    rewrite /listgen.
    wp_pures; rewrite -/flip -/listgen.
    wp_apply (rwp_couple_flip with "Hspec").
    { apply Rcoupl_nested_step_initial. }
    iIntros ([] s) "[Hspec ->]".
    - wp_pures. iModIntro. by iApply "HΨ".
    - wp_pures.
      wp_apply ("Hf" with "Hspec").
      iIntros (m s) "[Hspec %]".
      wp_pures.
      iApply rwp_spec_steps'.
      iSplitR "Hspec"; [|by iApply (spec_restart with "Hspec")].
      iIntros "Hspec !>".
      wp_apply ("IH" with "Hspec").
      iIntros (?) "Hspec".
      wp_pures. iModIntro.
      by iApply "HΨ".
  Qed.

End nested_ho_spec.

(** Trivial one-point Markov chain  *)
Definition unit_markov_mixin : MarkovMixin (λ _ : (), dzero) (λ _, Some ()).
Proof. constructor. by intros [] [] []; simplify_eq=>/=. Qed.

Canonical Structure unit_markov : markov := Markov _ _ unit_markov_mixin.

Section listgen_flip'.
  Context `{tprG (nested_markov unit_markov ()) Σ}.

  Lemma wp_listgen_flip' :
    ⟨⟨⟨ specF initial ⟩⟩⟩
      listgen (λ: <>, flip)%V
    ⟨⟨⟨ v, RET v; specF final ⟩⟩⟩.
  Proof.
    iIntros (Ψ1) "Hspec HΨ1 /=".
    wp_apply (wp_listgen with "[] Hspec"); [|done].
    iIntros (Ψ2) "!# Hspec HΨ2 /=".
    wp_pures.
    wp_apply rwp_flip; [done|].
    iIntros (b) "_".
    iApply "HΨ2". iFrame.
    eauto.
  Qed.
End listgen_flip'.

Section listgen_listgen_flip_spec.

  Definition model : markov :=
    nested_markov (nested_markov unit_markov ()) initial.

  Context `{tprG model Σ}.

  Lemma wp_listgen_list_bool' :
    ⟨⟨⟨ specF initial ⟩⟩⟩
      listgen (λ: <>, listgen (λ: <>, flip)%V)%V
    ⟨⟨⟨ v, RET v; specF final ⟩⟩⟩.
  Proof.
    iIntros (Ψ1) "Hspec HΨ1 /=".
    wp_apply (wp_listgen with "[] Hspec"); [|done].
    iIntros (Ψ2) "!# Hspec HΨ2 /=".
    wp_pures.

    wp_apply (wp_listgen with "[] [Hspec]").

    (* Hmm.... *)
  Abort.

End listgen_listgen_flip_spec.

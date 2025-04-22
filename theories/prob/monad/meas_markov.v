Set Warnings "-hiding-delimiting-key".
From HB Require Import structures.
From Coq Require Import Logic.ClassicalEpsilon Psatz Logic.FunctionalExtensionality Program.Wf Reals.
From mathcomp Require Import ssrbool all_algebra eqtype choice boolp classical_sets.
From iris.prelude Require Import options.
From iris.algebra Require Import ofe.
From Coq.ssr Require Import ssreflect ssrfun.
From clutch.bi Require Import weakestpre.
From mathcomp.analysis Require Import reals measure ereal Rstruct lebesgue_integral sequences.
From clutch.prob.monad Require Export giry lim couplings_app.
From clutch.prelude Require Import classical.
Set Warnings "hiding-delimiting-key".
(*From Coq Require Import Reals Psatz.
From Coquelicot Require Import Rcomplements Rbar Lim_seq.
From clutch.prob Require Import distribution couplings couplings_app mdp.
*)
Set Default Proof Using "Type*".

(** * Markov Chains *)
Section meas_markov_mixin.
  Context {mstate_disp mstate_ret_disp : measure_display}.
  Context {mstate : measurableType mstate_disp}.
  Context {mstate_ret : measurableType mstate_ret_disp}.
  Context (step : mstate → giryM mstate).
  Context (to_final : mstate → option mstate_ret).

  Record MeasMarkovMixin := {
    mixin_step_meas : measurable_fun setT step;
    mixin_to_final_meas : measurable_fun setT to_final;
    mixin_to_final_is_final a :
      is_Some (to_final a) → is_zero (step a);
  }.
End meas_markov_mixin.

Structure meas_markov := MeasMarkov {
  mstate_disp : measure_display;
  mstate_ret_disp : measure_display;
  mstate : measurableType mstate_disp ;
  mstate_ret : measurableType mstate_ret_disp ;
  step     : mstate → giryM mstate;
  to_final : mstate → option mstate_ret;
  markov_mixin : MeasMarkovMixin step to_final;
}.

#[global] Arguments MeasMarkov {_ _ _ _} _ _ _.
#[global] Arguments step {_}.
#[global] Arguments to_final {_}.

(*
Definition markov_mdp_mixin (m : markov):
  MdpMixin (λ (x:()) s, m.(step) s) (m.(to_final)).
Proof.
  constructor.
  intros.
  by apply markov_mixin.
Qed.

Canonical Structure markov_mdp (m : markov) := Mdp _ _ (markov_mdp_mixin m).
*)

Section is_final.
  Context {δ : meas_markov}.
  Implicit Types a : mstate δ.
  Implicit Types b : mstate_ret δ.

  Lemma step_meas : measurable_fun setT (@step δ).
  Proof. apply markov_mixin. Qed.

  Lemma to_final_meas : measurable_fun setT (@to_final δ).
  Proof. apply markov_mixin. Qed.

  Lemma to_final_is_final a :
    is_Some (to_final a) → is_zero (step a).
  Proof. apply markov_mixin. Qed.

  Definition is_final a := is_Some (to_final a).

  Lemma to_final_None a : ¬ is_final a ↔ to_final a = None.
  Proof. rewrite eq_None_not_Some //. Qed.

  Lemma to_final_None_1 a : ¬ is_final a → to_final a = None.
  Proof. apply to_final_None. Qed.

  Lemma to_final_None_2 a : to_final a = None → ¬ is_final a.
  Proof. apply to_final_None. Qed.

  Lemma to_final_Some a : is_final a ↔ ∃ b, to_final a = Some b.
  Proof. done. Qed.

  Lemma to_final_Some_1 a : is_final a → ∃ b, to_final a = Some b.
  Proof. done. Qed.

  Lemma to_final_Some_2 a b : to_final a = Some b → is_final a.
  Proof. intros. eexists _; by apply H.  Qed.

  Lemma is_final_dzero a : is_final a → is_zero (step a).
  Proof.
    intros Hf.
    apply to_final_is_final.
    by rewrite //.
  Qed.

  (*
  #[global] Instance is_final_dec a : Decision (is_final a).
  Proof. rewrite /is_final. apply _. Qed.
   *)
End is_final.

#[global] Hint Immediate to_final_Some_2 to_final_None_2 to_final_None_1: core.


Section reducible.
  Context {δ : meas_markov}.
  Implicit Types a : mstate δ.

  Definition reducible a := ¬ is_zero (step a).
  Definition irreducible a := is_zero (step a).
  Definition stuck a := ¬ is_final a ∧ irreducible a.
  Definition not_stuck a := is_final a ∨ reducible a.

  Lemma not_reducible a  : ¬ reducible a ↔ irreducible a.
  Proof.
    unfold reducible, irreducible. split.
    { by apply classical.NNP_P. }
    { by apply classical.P_NNP. }
  Qed.

  Lemma reducible_not_final a :
    reducible a → ¬ is_final a.
  Proof. move=> H ?. apply H. by apply is_final_dzero. Qed.

  Lemma is_final_irreducible a : is_final a → irreducible a.
  Proof.
    intros ?.
    rewrite /irreducible.
    apply is_final_dzero.
    by rewrite //.
  Qed.

  Lemma not_not_stuck a : ¬ not_stuck a ↔ stuck a.
  Proof.
    rewrite /stuck /not_stuck -not_reducible.
    destruct (decide (is_final a)); naive_solver.
  Qed.

  (* Delete me *)
  Lemma irreducible_dzero a :
    irreducible a → is_zero (step a).
  Proof. done. Qed.

  Lemma reducible_not_stuck a :
    reducible a → not_stuck a.
  Proof. intros. by right. Qed.

  Lemma mass_pos_reducible a :
    (0 < mass (step a) (measurableT))%E → reducible a.
  Proof. 
    rewrite /reducible /is_zero /not /measure_eq.
    intros. 
    assert (mass (step a) (measurableT) = 0)%E.
    {
      rewrite /mass. 
      rewrite (eq_measure_integral gZero). 
      2 : { intros. apply H0; auto. }
      rewrite (eq_measure_integral mzero). 
      2 : { intros. apply gZero_eval; auto. }
      apply integral_measure_zero.
    }
    rewrite H1 lte_fin in H. 
    apply (elimT (RltbP 0 0)) in H. lra.
  Qed.


End reducible.

Section markov.
  Context {δ : meas_markov}.
  Implicit Types a : mstate δ.
  Implicit Types b : mstate_ret δ.



  Lemma const_meas_fun {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2} (a : T2):
    measurable_fun setT (fun _ : T1 => a).
  Proof.
    move => _ A HA.
    rewrite /preimage setTI.
    destruct (pselect (A a)) as [Ha | Ha]; 
    erewrite (eq_set (Q := fun _ => _) _).
    { apply: measurableT. }
    { apply: measurable0. }
    Unshelve. 
    { intros. rewrite propeqE. tauto. }
    { intros. rewrite propeqE. tauto. }
  Qed.

  (** * Strict partial evaluation *)
  Program Definition stepN (n : nat) a : giryM (mstate δ) :=
    gIter n step a.

  Lemma stepN_meas (n : nat) : measurable_fun setT (stepN n).
  Proof. by apply gIter_meas_fun, step_meas. Qed.

  Lemma stepN_0 : stepN 0 = gRet.
  Proof. done. Qed.

  Lemma stepN_Sn a n :
    stepN (S n) a = gBind' (stepN n) (step a) .
  Proof. done. Qed.

  Lemma stepN_1 a :
    stepN 1 a ≡μ step a.
  Proof. 
    by rewrite stepN_Sn stepN_0 (gBind'_meas_rw gRet_meas_fun) gBind_gRet. 
  Qed.

  Lemma stepN_plus a (n m : nat) :
    stepN (n + m) a ≡μ gBind' (stepN m) (stepN n a) . 
  Proof. 
    apply gIter_plus, step_meas.
  Qed.

  (*
    Generalize these ones to eval on sets?

  Lemma stepN_Sn_inv n a0 a2 :
    stepN (S n) a0 a2 > 0 →
    ∃ a1, step a0 a1 > 0 ∧ stepN n a1 a2 > 0.
  Proof. intros (?&?&?)%dbind_pos. eauto. Qed.

  Lemma stepN_det_steps n m a1 a2 :
    stepN n a1 a2 = 1 →
    stepN n a1 ≫= stepN m = stepN m a2.
  Proof. intros ->%pmf_1_eq_dret. rewrite dret_id_left //. Qed.
*)

  Lemma stepN_is_det_trans n m a1 a2 a3 :
    is_det a2 (stepN n a1) →
    is_det a3 (stepN m a2) →
    is_det a3 (stepN (n + m) a1).
  Proof.
    rewrite /is_det stepN_plus (gBind'_meas_rw (stepN_meas _)).
    intros. by rewrite H gRet_gBind.
  Qed.


  (** * Non-strict partial evaluation *)
  Definition step_or_final a : giryM (mstate δ) :=
    match to_final a with
    | Some _ => gRet a
    | None => step a
    end.

  Definition step_or_final' a : giryM (mstate δ) := 
    if (isSome \o to_final) a then gRet a else step a.

  Lemma step_or_final'_eq: step_or_final = step_or_final'.
  Proof.
    apply functional_extensionality. intros.
    rewrite /step_or_final /step_or_final' /comp.
    destruct (to_final x); auto.
  Qed.

  Lemma isSome_is_none {A : Type} (a : option A) : isSome a = false ↔ a = None.
  Proof.
    rewrite /isSome. split; destruct a; auto; intros; inversion H.
  Qed.

  Lemma is_final_meas_fun: measurable_fun setT (isSome \o (to_final : mstate δ -> _)).
  Proof.
    apply measurableT_comp.
    { 
      apply (measurable_fun_bool false).
      rewrite setTI /preimage. 
      erewrite (eq_set _).
      apply option_cov_None_meas_set.
      Unshelve. 
      intros. 
      rewrite propeqE /option_cov_None. simpl. 
      rewrite /isSome. split; destruct x; auto; intros; inversion H.
    }
    { apply to_final_meas. }
  Qed.

  Lemma step_or_final_meas : measurable_fun setT step_or_final.
  Proof. 
    rewrite step_or_final'_eq.
    unfold step_or_final'.
    eapply (measurable_fun_if measurableT is_final_meas_fun (g := gRet) (h := step)); apply (measurable_funS measurableT).
    { apply subsetT. }
    { apply gRet_meas_fun. }
    { apply subsetT. }
    { apply step_meas. }
  Qed.

  Lemma step_or_final_no_final a :
    ¬ is_final a → step_or_final a = step a.
  Proof. rewrite /step_or_final /is_final /= -eq_None_not_Some. by intros ->. Qed.

  Lemma step_or_final_is_final a :
    is_final a → step_or_final a = gRet a.
  Proof. rewrite /step_or_final /=. by intros [? ->]. Qed.

  Definition pexec (n : nat) a : giryM (mstate δ) := gIter n step_or_final a.

  Lemma pexec_meas (n : nat) : measurable_fun setT (pexec n).
  Proof. 
    apply gIter_meas_fun, step_or_final_meas.
  Qed.

  Lemma pexec_O a :
    pexec 0 a = gRet a.
  Proof. done. Qed.


  Lemma pexec_Sn a n :
    pexec (S n) a = gBind' (pexec n) (step_or_final a).
  Proof. done. Qed.

  Lemma pexec_plus ρ n m :
    pexec (n + m) ρ ≡μ gBind' (pexec m) (pexec n ρ).
  Proof.
    apply gIter_plus, step_or_final_meas.
  Qed.

  Lemma pexec_1 a :
    pexec 1 a ≡μ step_or_final a.
  Proof. 
    rewrite /pexec//=.
    rewrite (gBind'_meas_rw gRet_meas_fun).
    apply gBind_gRet.
  Qed.

  Lemma pexec_Sn_r a n :
    pexec (S n) a ≡μ gBind' step_or_final (pexec n a).
  Proof.
    assert (S n = n + 1)%nat as ->; try lia.
    rewrite pexec_plus.
    rewrite !(gBind'_meas_rw (pexec_meas _)).
    rewrite !(gBind'_meas_rw step_or_final_meas).
    apply gBind_equiv.
    apply pexec_1.
  Qed.

  Lemma pexec_is_final n a :
    is_final a → pexec n a ≡μ gRet a.
  Proof.
    intros ?.
    induction n.
    { by rewrite pexec_O //. }
    { 
      rewrite pexec_Sn.
      rewrite -step_or_final_is_final; auto.
      rewrite (gBind'_meas_rw (pexec_meas _)).
      rewrite /step_or_final. 
      rewrite /is_final in H. destruct (to_final a); try by inversion H.
      by rewrite gRet_gBind. 
    }

  Qed.

  Lemma pexec_no_final a n :
    ¬ is_final a →
    pexec (S n) a = gBind' (pexec n) (step a).
  Proof. intros. rewrite pexec_Sn step_or_final_no_final //. Qed.

  Lemma pexec_det_step n a1 a2 a0 :
    is_det a2 (step a1) →
    is_det a1 (pexec n a0) →
    is_det a2 (pexec (S n) a0).
  Proof.
    rewrite /is_det pexec_Sn_r.
    rewrite (gBind'_meas_rw step_or_final_meas).
    intros H H1. rewrite -H H1 gRet_gBind /step_or_final. 
    case_match; auto.
    exfalso.
    apply (@gRet_not_zero _ _ a2).
    rewrite -H. apply is_final_dzero; by rewrite /is_final H0.
  Qed.

  Lemma pexec_det_steps n m a1 a2 :
    is_det a2 (pexec n a1) →
    gBind (pexec_meas m) (pexec n a1) ≡μ pexec m a2.
  Proof. 
    rewrite /is_det. intros. by rewrite H gRet_gBind.
  Qed.


  Lemma stepN_le_pexec n x : giryM_le (stepN n x) (pexec n x).
  Proof.
    apply gIter_giryM_le.
    { apply step_meas. }
    { apply step_or_final_meas. }
    move => a s Hs.
    destruct (decide (is_final a)).
    { 
      rewrite to_final_is_final; auto.
      rewrite gZero_eval; auto.
    }
    rewrite step_or_final_no_final //.
  Qed.

  Lemma stepN_pexec_det n x y:
    is_det y (stepN n x) → is_det y (pexec n x).
  Proof.
    unfold is_det.
    intros.
    apply giryM_le_is_det.
    erewrite giryM_le_proper.
    { apply stepN_le_pexec. }
    { by rewrite -H. }
    auto.
  Qed.

(*

    apply iterM_mono => a a'.
    destruct (decide (is_final y)).
    { rewrite to_final_is_final.

    - rewrite to_final_is_final //.
    - rewrite step_or_final_no_final //.
  Qed.
*)

  (** * Stratified evaluation to a final state *)
  Fixpoint exec (n : nat) (a : mstate δ) {struct n} : giryM (mstate_ret δ) :=
    match to_final a, n with
      | Some b, _ => gRet b
      | None, 0 => gZero
      | None, S n => gBind' (exec n) (step a)
    end.

  Lemma exec_unfold (n : nat) :
    exec n = λ a,
      match to_final a, n with
      | Some b, _ => gRet b
      | None, 0 => gZero
      | None, S n => gBind' (exec n) (step a)
      end.
  Proof. by destruct n. Qed.

  Definition exec_0' a := if (isSome \o to_final) a then ((gRet \o 𝜋_Some_v) \o to_final) a else (fun _ => gZero) a.

  Lemma exec_0'_eq: exec 0 = exec_0'.
  Proof.
    apply functional_extensionality.
    intros a.
    rewrite /exec /exec_0'.
    simpl.
    destruct (to_final a); auto.
  Qed.

  Definition exec_Sn' n a := if (isSome \o to_final) a then ((gRet \o 𝜋_Some_v) \o to_final) a else (gBind' (exec n) \o step) a.

  Lemma exec_Sn'_eq n : exec (S n) = exec_Sn' n.
  Proof.
    apply functional_extensionality.
    intros a.
    rewrite /exec_Sn'.
    simpl.
    destruct (to_final a); auto.
  Qed.

  Local Open Scope classic.

  Lemma exec'_true_meas : measurable_fun ((isSome \o to_final) @^-1` [set true]) ((gRet \o 𝜋_Some_v) \o (to_final : mstate δ -> _)).
  Proof.
    assert ([set x | isSome x = true] = (option_cov_Some (T := mstate_ret δ))). {
      apply eq_set.
      intros. rewrite propeqE /option_cov_Some. simpl. 
      rewrite /isSome. split; intros.
      { destruct x; inversion H. exists s; auto. }
      { destruct H. rewrite H. auto. }
    }
    apply (measurable_comp (F := [set x | isSome x = true])).
    { 
      rewrite H.
      apply option_cov_Some_meas_set. 
    }
    { 
      unfold preimage. simpl.     
      unfold subset. simpl. intros.
      destruct H0. by subst t.
    }
    {
      apply measurableT_comp. { apply gRet_meas_fun. }
      rewrite H. apply 𝜋_Some_v_meas_fun.
      apply None. 
    }
    {
      apply (measurable_funS measurableT).
      { apply subsetT. }
      { apply to_final_meas. }
    }
  Qed.

  Lemma exec_meas_fun (n : nat) : measurable_fun setT (exec n).
  Proof. 
    induction n.
    {
      rewrite exec_0'_eq.
      apply (measurable_fun_if measurableT).
      { apply is_final_meas_fun. }
      { rewrite setTI. apply exec'_true_meas. }
      { 
        apply (measurable_funS measurableT). { apply subsetT. }
        apply (const_meas_fun gZero).
      }
    }
    {
      rewrite exec_Sn'_eq.
      apply (measurable_fun_if measurableT).
      { apply is_final_meas_fun. }
      { rewrite setTI. apply exec'_true_meas. }
      { apply (measurable_funS measurableT). { apply subsetT. }
        apply measurableT_comp.
        { apply (gBind'_meas_fun IHn). }
        { apply step_meas. }
      }
    }
  Qed.

  Lemma exec_is_final a b n :
    to_final a = Some b → exec n a = gRet b.
  Proof. destruct n; simpl; by intros ->. Qed.

  Lemma exec_Sn a n :
    exec (S n) a ≡μ gBind' (exec n) (step_or_final a).
  Proof.
    rewrite /step_or_final /=.
    case_match; [|done]. 
    rewrite gBind'_meas_rw. { apply exec_meas_fun. }
    intros.
    rewrite gRet_gBind /exec. 
    by erewrite exec_is_final.
  Qed.

  Lemma exec_plus a n1 n2 :
    exec (n1 + n2) a ≡μ gBind' (exec n2) (pexec n1 a).
  Proof.
    rewrite !gBind'_meas_rw. { apply exec_meas_fun. }
    intros.
    revert a. induction n1.
    { 
      intro a. rewrite pexec_O gRet_gBind //.
    }
    { 
      intro a. replace ((S n1 + n2)%nat) with ((S (n1 + n2))); auto.
      rewrite exec_Sn pexec_Sn. 
      intros.
      rewrite !gBind'_meas_rw. { apply exec_meas_fun. } { apply pexec_meas. }
      intros.
      rewrite gBind_assoc.
      by rewrite gBind_equiv. 
    }
  Qed.
  
  (*
  Lemma exec_pexec_relate a n:
    exec n a = pexec n a ≫=
                 (λ e, match to_final e with
                             | Some b => dret b
                             | _ => dzero
                       end).
  Proof.
    revert a.
    induction n; intros a.
    - simpl. rewrite pexec_O.
      rewrite dret_id_left'.
      done.
    - simpl. rewrite pexec_Sn.
      rewrite -dbind_assoc'.
      case_match eqn:H.
      + rewrite step_or_final_is_final; last by eapply to_final_Some_2.
        rewrite dret_id_left'.
        rewrite pexec_is_final; last by eapply to_final_Some_2.
        rewrite dret_id_left'. rewrite H. done.
      + rewrite step_or_final_no_final; last by eapply to_final_None_2.
        apply dbind_ext_right. done.
  Qed.
  *)

  Lemma exec_mono a n :
    giryM_le (exec n a) (exec (S n) a).
  Proof.
    intros.
    move : a.
    induction n.
    {
      move => a v Hv.
      rewrite /=. 
      case_match; auto.
      rewrite gZero_eval //.
    }
    move => a v Hv.
    do 2 (rewrite exec_Sn; auto).
    do 2 rewrite (gBind'_meas_rw (exec_meas_fun _)).
    apply gBind_giryM_le; auto.
    apply giryM_le_refl.
  Qed.

  Lemma exec_mono' ρ n m  :
    n ≤ m → 
    giryM_le (exec n ρ) (exec m ρ).
  Proof.
    intros. 
    remember (m - n).
    revert n m H Heqn0.
    induction n0. 
    {
      intros.
      replace m with n. 2: lia.
      apply giryM_le_refl.
    }
    intros.
    replace m with (S (n0 + n)). 2: lia. 
    eapply giryM_le_trans.
    { eapply (IHn0 _ (n0+n)); lia. }
    apply exec_mono.
  Qed.

  Lemma exec_mono_term a b n m :
    (mass' (exec n a) setT = 1)%E →
    n ≤ m →
    exec m a ≡μ exec n a.
  Proof.
    intros Hv Hleq.
    move => s Hm.
    apply @order.Order.le_anti.
    apply andb_true_iff.
    split.
    2: by apply exec_mono'.
    destruct (decide (exec m a s <= exec n a s)%E); auto.
    rewrite /mass' !extern_if_eq /mass !(integral_cst _ measurableT 1) !mul1e // in Hv.
    assert (exec m a [set: mstate_ret δ] = 1%E).
    {
      apply @order.Order.le_anti.
      rewrite sprobability_setT -Hv exec_mono' //.
    }
    assert (false); auto.
    rewrite -(order.Order.POrderTheory.lt_irreflexive (1: \bar R)%E); auto. 
    assert (exec n a [set: mstate_ret δ] < exec m a [set: mstate_ret δ])%E.
    2: by rewrite Hv H in H0. 
    specialize (measurableC Hm) as Hm'.
    replace (exec n a _) with (exec n a s + exec n a (~` s))%E.
    2: {
      rewrite -measureU; auto. 
      2: apply subsets_disjoint, subset_refl.
      by rewrite setUv.
    }
    replace (exec m a _) with (exec m a s + exec m a (~` s))%E.
    2: {
      rewrite -measureU; auto. 
      2: apply subsets_disjoint, subset_refl.
      by rewrite setUv.
    }
    apply (lte_leD (eval_is_fin_num (exec n a) Hm')).
    2: apply exec_mono'; auto.
    rewrite order.Order.TotalTheory.ltNge.
    destruct (exec m a s <= exec n a s)%E eqn : Hle.
    {
      exfalso.
      by apply n0.
    }
    by rewrite Hle.
  Qed.



  Lemma exec_O_not_final a :
    ¬ is_final a →
    exec 0 a = gZero.
  Proof. intros ?%to_final_None_1 =>/=; by case_match. Qed.

  Lemma exec_Sn_not_final a n :
    ¬ is_final a →
    exec (S n) a ≡μ gBind' (exec n) (step a).
  Proof. by intros ?; rewrite exec_Sn step_or_final_no_final //. Qed.


  (*
    NOTE 1:
    Before proving this (and adding singleton measurability to the meas_markov interface,
     see if it's stated correctly.

     It is only used in this file.
     Downstream, aside from dependencies in MDP which are ignored.
       - mdp; ignored
       - pexec_exec_det
         - pexec_exec_det_neg
           - lim_exec_det_final
         - lim_exec_det_final
       - exec_pexec_val_neq_le
         - pexec_exec_det_neg
           - lim_exec_det_final

      So don't port:
        - pexec_exec_le_final
        - pexec_exec_det
        - pexec_exec_det_neg
        - exec_pexec_val_neq_le
      Until it's need arises in lim_exec_det_final.
   *)

  (*

  NOTE 1
  Lemma pexec_exec_le_final n a a' b :
    to_final a' = Some b →
    le_ereal (pexec n a [set a']) (exec n a [set b]).
  Proof.
    intros Hb.
    revert a. induction n; intros a.
    { rewrite pexec_O.
      destruct (decide (a = a')) as [->|].
      { erewrite exec_is_final; [|done].
        admit. } (* rewrite !dret_1_1 //. *)
      { (* rewrite dret_0 //. *) admit. }
    }
    { rewrite exec_Sn; last admit.
      rewrite pexec_Sn.
      destruct (decide (is_final a)).
      { rewrite step_or_final_is_final //.
        admit.
        (* rewrite 2!dret_id_left -/exec.
        apply IHn. *) }
      { rewrite step_or_final_no_final //.
        admit.
        (*
        rewrite /pmf /= /dbind_pmf.
        eapply SeriesC_le.
        * intros a''. split; [by apply Rmult_le_pos|].
          by apply Rmult_le_compat.
        * eapply pmf_ex_seriesC_mult_fn.
          exists 1. by intros ρ. *)
      }
  Admitted.
 *)

  (*
  NOTE 1
  Lemma pexec_exec_det n a a' b :
    to_final a' = Some b →
    pexec n a [set a'] = (1)%E → exec n a [set b] = (1)%E.
  Proof.
    intros Hf.
    pose proof (pexec_exec_le_final n a a' b Hf).
    (* pose proof (pmf_le_1 (exec n a) b). *)
  Qed. *)

  (*

  NOTE 1
  Lemma exec_pexec_val_neq_le n m a a' b b' :
    to_final a' = Some b' →
    b ≠ b' → exec m a b + pexec n a a' <= 1.
  Proof.
    intros Hf Hneq.
    etrans; [by apply Rplus_le_compat_l, pexec_exec_le_final|].
    etrans; [apply Rplus_le_compat_l, (exec_mono' _ n (n `max` m)), Nat.le_max_l|].
    etrans; [apply Rplus_le_compat_r, (exec_mono' _ m (n `max` m)), Nat.le_max_r|].
    etrans; [|apply (pmf_SeriesC (exec (n `max` m) a))].
    by apply pmf_plus_neq_SeriesC.
  Qed.

  NOTE 1
  Lemma pexec_exec_det_neg n m a a' b b' :
    to_final a' = Some b' →
    pexec n a a' = 1 →
    b ≠ b' →
    exec m a b = 0.
  Proof.
    intros Hf Hexec Hv.
    pose proof (exec_pexec_val_neq_le n m a a' b b' Hf Hv) as Hle.
    rewrite Hexec in Hle.
    pose proof (pmf_pos (exec m a) b).
    lra.
  Qed.
*)


(*
  Sup_seq -> limn_esup (fun n => μ n S).

  Lemma is_finite_Sup_seq_exec a b :
    is_finite (Sup_seq (λ n, exec n a b)).
  Proof.
    apply (Rbar_le_sandwich 0 1).
    - by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
    - by apply upper_bound_ge_sup=>/=.
  Qed.

  Lemma is_finite_Sup_seq_SeriesC_exec a :
    is_finite (Sup_seq (λ n, SeriesC (exec n a))).
  Proof.
    apply (Rbar_le_sandwich 0 1).
    - by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
    - by apply upper_bound_ge_sup=>/=.
  Qed.

*)

  (** * Full evaluation (limit of stratification) *)

  Definition lim_exec (a : mstate δ) : giryM (mstate_ret δ) :=
    limit_measure (fun n => exec n a).

  (* Definition lim_exec (a : mstate δ) : distr (mstate_ret δ) := lim_distr (λ n, exec n a) (exec_mono a). *)

  Lemma lim_exec_unfold a (b : set _) :
    lim_exec a b = limn_esup (λ n, (exec n a) b).
  Proof. by rewrite /lim_exec. Qed.

  (* Search measurable setT. *)

  Lemma lim_exec_Sup_seq (a : mstate δ) :
    mass' (lim_exec a) setT = limn_esup (λ n, mass' (exec n a) setT).
  Proof. Admitted.
  (*
    erewrite SeriesC_ext; last first.
    { intros ?. rewrite lim_exec_unfold //. }
    erewrite MCT_seriesC; eauto.
    - intros. apply exec_mono.
    - intros. by eapply SeriesC_correct.
    - rewrite (Rbar_le_sandwich 0 1).
      + apply Sup_seq_correct.
      + by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
      + by apply upper_bound_ge_sup=>/=.
  Qed. *)

  Lemma lim_exec_step (a : mstate δ) :
    lim_exec a ≡μ gBind' lim_exec (step_or_final a).
  Proof. Admitted.
(*
  Proof.
   apply distr_ext.
   intro b.
   rewrite {2}/pmf /= /dbind_pmf.
   rewrite lim_exec_unfold.
   setoid_rewrite lim_exec_unfold.
   assert
     (SeriesC (λ a', step_or_final a a' * Sup_seq (λ n, exec n a' b)) =
      SeriesC (λ a', Sup_seq (λ n, step_or_final a a' * exec n a' b))) as ->.
   { apply SeriesC_ext; intro b'.
     apply eq_rbar_finite.
     rewrite rmult_finite.
     rewrite (rbar_finite_real_eq).
     - rewrite -Sup_seq_scal_l //.
     - apply (Rbar_le_sandwich 0 1).
       + by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
       + by apply upper_bound_ge_sup=>/=. }
   rewrite (MCT_seriesC _ (λ n, exec (S n) a b) (lim_exec a b)) //.
   - intros. by apply Rmult_le_pos.
   - intros.
     apply Rmult_le_compat; [done|done|done|].
     apply exec_mono.
   - intros a'.
     exists (step_or_final a a').
     intros n.
     rewrite <- Rmult_1_r. by apply Rmult_le_compat_l.
   - intro n.
     rewrite exec_Sn.
     rewrite {3}/pmf/=/dbind_pmf.
     apply SeriesC_correct.
     apply (ex_seriesC_le _ (step_or_final a)); [|done].
     intros a'. split.
     + by apply Rmult_le_pos.
     + rewrite <- Rmult_1_r. by apply Rmult_le_compat_l.
   - rewrite lim_exec_unfold.
     rewrite mon_sup_succ.
     + rewrite (Rbar_le_sandwich 0 1).
       * apply Sup_seq_correct.
       * by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
       * by apply upper_bound_ge_sup=>/=.
     + intro; apply exec_mono.
  Qed.
*)

  Lemma lim_exec_pexec n a :
    lim_exec a ≡μ gBind' lim_exec (pexec n a).
  Proof.
    move : a.
    induction n; intro a.
    { rewrite pexec_O. (* Check gret_id_left. *)
      (* dret_id_left //. *) admit. }
    { rewrite pexec_Sn.
      (* -dbind_assoc/=.
      rewrite lim_exec_step.
      apply dbind_eq; [|done].
      intros ??. apply IHn. *) Admitted.

  Lemma lim_exec_det_final n a a' b :
    to_final a' = Some b →
    is_det a' (pexec n a) →
    lim_exec a ≡μ gRet b.
  Proof.
    intros Hb Hpe.
    intros b' Hb'.
    rewrite lim_exec_unfold.
    rewrite /gRet.
    rewrite /dirac//=/dirac//=/numfun.indic.
    destruct (ExcludedMiddle (b' b)).
    { rewrite (mem_set H) //=.
      admit. }
    { rewrite (memNset H) //=.
      (* Rewrite by constant sequence... *)
      admit. }
  Admitted.
(*
    rewrite {2}/pmf /= /dret_pmf.
    case_bool_decide; simplify_eq.
    - apply Rle_antisym.
      + apply finite_rbar_le; [eapply is_finite_Sup_seq_exec|].
        by apply upper_bound_ge_sup=>/=.
      + apply rbar_le_finite; [eapply is_finite_Sup_seq_exec|].
        apply (Sup_seq_minor_le _ _ n)=>/=.
        by erewrite pexec_exec_det.
    - rewrite -(sup_seq_const 0).
      f_equal. apply Sup_seq_ext=> m.
      f_equal. by eapply pexec_exec_det_neg.
  Qed. *)

  Lemma lim_exec_final a b :
    to_final a = Some b →
    lim_exec a ≡μ gRet b.
  Proof.
    intros ???.
    erewrite (lim_exec_det_final 0%nat); [done| done | |done].
    rewrite pexec_O.
    apply is_det_dret.
  Qed.

  Lemma lim_exec_not_final a :
    ¬ is_final a →
    lim_exec a ≡μ gBind' lim_exec (step a).
  Proof.
    intros Hn. rewrite lim_exec_step step_or_final_no_final //.
  Qed.

  Lemma lim_exec_leq a (b : set _) (H : measurable b) (r : R) :
    (∀ n, (exec n a b <= EFin r)%E) →
    (lim_exec a b <= EFin r)%E.
  Proof.
    intro Hexec.
    rewrite lim_exec_unfold.
  Admitted.
  (*
    apply finite_rbar_le; [apply is_finite_Sup_seq_exec|].
    by apply upper_bound_ge_sup=>/=.
  Qed. *)

  Lemma lim_exec_leq_mass  a r :
    (∀ n, mass' (exec n a) setT <= EFin r)%E →
    (mass' (lim_exec a) setT <= EFin r)%E.
  Proof. Admitted.
  (*
    intro Hm.
    erewrite SeriesC_ext; last first.
    { intros. rewrite lim_exec_unfold //. }
    erewrite (MCT_seriesC _ (λ n, SeriesC (exec n a)) (Sup_seq (λ n, SeriesC (exec n a)))); eauto.
    - apply finite_rbar_le; [apply is_finite_Sup_seq_SeriesC_exec|].
      by apply upper_bound_ge_sup.
    - apply exec_mono.
    - intros. by apply SeriesC_correct.
    - rewrite (Rbar_le_sandwich 0 1).
      + apply (Sup_seq_correct (λ n, SeriesC (exec n a))).
      + by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
      + by apply upper_bound_ge_sup=>/=.
  Qed. *)

  (*
  No need to port now

  Lemma lim_exec_term n a :
    SeriesC (exec n a) = 1 →
    lim_exec a = exec n a.
  Proof.
    intro Hv.
    apply distr_ext=> b.
    rewrite lim_exec_unfold.
    apply Rle_antisym.
    - apply finite_rbar_le; [apply is_finite_Sup_seq_exec|].
      rewrite -/pmf.
      apply upper_bound_ge_sup.
      intros n'.
      destruct (decide (n <= n')) as [|?%Rnot_le_lt].
      + right. apply exec_mono_term; [done|]. by apply INR_le.
      + apply exec_mono'. apply INR_le. by left.
    - apply rbar_le_finite; [apply is_finite_Sup_seq_exec|].
      apply (sup_is_upper_bound (λ m, exec m a b) n).
  Qed.
  *)

  (*
  No need to port now

  Lemma lim_exec_pos a b :
    lim_exec a b > 0 → ∃ n, exec n a b > 0.
  Proof.
    intros.
    apply Classical_Pred_Type.not_all_not_ex.
    intros H'.
    assert (lim_exec a b <= 0); [|lra].
    apply lim_exec_leq => n.
    by apply Rnot_gt_le.
  Qed.
   *)

  (*
  No need to port now

  Lemma lim_exec_continuous_prob a ϕ r :
    (∀ n, prob (exec n a) ϕ <= r) →
    prob (lim_exec a) ϕ <= r.
  Proof.
    intro Hm.
    rewrite /prob.
    erewrite SeriesC_ext; last first.
    { intro; rewrite lim_exec_unfold; auto. }
    assert
      (forall v, (if ϕ v then real (Sup_seq (λ n0 : nat, exec n0 a v)) else 0) =
                 (real (Sup_seq (λ n0 : nat, if ϕ v then exec n0 a v else 0)))) as Haux.
    { intro v.
      destruct (ϕ v); auto.
      rewrite sup_seq_const //.
    }
    assert
      (is_finite (Sup_seq (λ n0 : nat, SeriesC (λ v, if ϕ v then exec n0 a v else 0)))) as Hfin.
    {
      apply (Rbar_le_sandwich 0 1).
      + apply (Sup_seq_minor_le _ _ 0%nat); simpl.
        apply SeriesC_ge_0'.
        intro v; destruct (ϕ v); auto.
        lra.
      + apply upper_bound_ge_sup; intro; simpl; auto.
        apply (Rle_trans _ (SeriesC (exec n a))); auto.
        apply (SeriesC_le _ (exec n a)); auto.
        intro v; destruct (ϕ v); real_solver.
    }
    erewrite SeriesC_ext; last first.
    {
      intro; rewrite Haux //.
    }
    erewrite (MCT_seriesC _ (λ n, SeriesC (λ v, if ϕ v then exec n a v else 0))
                (Sup_seq (λ n0 : nat, SeriesC (λ v, if ϕ v then exec n0 a v else 0))));
      auto.
    - apply finite_rbar_le; auto.
      apply upper_bound_ge_sup; auto.
    - intros n v.
      destruct (ϕ v); auto.
      lra.
    - intros n v.
      destruct (ϕ v); [ apply exec_mono | lra].
    - intro v; destruct (ϕ v); exists 1; intro; auto; lra.
    - intros n.
      apply SeriesC_correct; auto.
      apply (ex_seriesC_le _ (exec n a)); auto.
      intro v; destruct (ϕ v); real_solver.
    - rewrite (Rbar_le_sandwich 0 1); auto.
      + apply (Sup_seq_correct (λ n0 : nat, SeriesC (λ v, if ϕ v then exec n0 a v else 0))).
      + apply (Sup_seq_minor_le _ _ 0%nat); simpl; auto.
        apply SeriesC_ge_0'.
        intro v; destruct (ϕ v); real_solver.
      + apply upper_bound_ge_sup; intro; simpl; auto.
        apply (Rle_trans _ (SeriesC (exec n a))); auto.
        apply (SeriesC_le _ (exec n a)); auto.
        intro v; destruct (ϕ v); real_solver.
  Qed.

**)
End markov.
#[global] Arguments pexec {_} _ _ : simpl never.

(** Approximate couplings  *)
Section ARcoupl.
  Context {δ : meas_markov}.


  Lemma lim_exec_ARcoupl {d} {B : measurableType d} (a : mstate δ) (μ2 : giryM B) φ (ε : R) (D : \bar R) :
    (0 <= EFin ε)%E →
    (0 <= D)%E →
    (∀ n, ARcoupl_meas (exec n a) μ2 φ ε D) →
    ARcoupl_meas (lim_exec a) μ2 φ ε D.
  Proof.
    (*
    intros Hε Hn.
    assert (∀ a', Rbar.is_finite
                   (Lim_seq.Sup_seq (λ n, Rbar.Finite (exec n a a')))) as Hfin.
    { intro a'.
      apply (is_finite_bounded 0 1).
      - apply (Lim_seq.Sup_seq_minor_le _ _ 0); simpl.
        case_match; auto.
      - by apply upper_bound_ge_sup; intro; simpl. }
    intros f g Hf Hg Hfg.
    rewrite {1}/lim_exec.
    setoid_rewrite lim_distr_pmf at 1.
    transitivity (Rbar.real (Lim_seq.Sup_seq
                               (λ n, Rbar.Finite (SeriesC (λ v, exec n a v * f v))))).
    - right.
      setoid_rewrite (rbar_scal_r); [|done].
      setoid_rewrite <- Sup_seq_scal_r; [|apply Hf].
      simpl.
      eapply MCT_seriesC.
      + intros. real_solver.
      + intros. apply Rmult_le_compat_r; [apply Hf | apply exec_mono].
      + intros; exists 1; intros. real_solver.
      + intro n. apply SeriesC_correct.
        apply (ex_seriesC_le _ (exec n a)); auto.
        intros; real_solver.
      + rewrite rbar_finite_real_eq.
        { apply Lim_seq.Sup_seq_correct. }
        apply (is_finite_bounded 0 1).
        * apply (Lim_seq.Sup_seq_minor_le _ _ 0); simpl.
          apply SeriesC_ge_0' => ?. case_match; real_solver.
        * apply upper_bound_ge_sup; intro; simpl.
          etrans.
          { apply (SeriesC_le _ (exec n a)); [|done]. real_solver. }
          done.
    - apply Rbar_le_fin'.
      { apply Rplus_le_le_0_compat; [|done].
        apply SeriesC_ge_0'. real_solver. }
      apply upper_bound_ge_sup.
      intro; simpl. auto.
      by eapply Hn.
      *)
  Admitted.
End ARcoupl.

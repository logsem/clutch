From Coq Require Import Reals Psatz.
From Coquelicot Require Import Rcomplements Rbar Lim_seq.
From clutch.prob Require Import distribution couplings couplings_app.
Set Default Proof Using "Type*".

(** * Markov decision process *)
Section mdp_mixin.
  Context `{Countable mdpstate, Countable mdpstate_ret, Countable mdpaction}.
  Context (step : mdpaction -> mdpstate → distr mdpstate).
  Context (to_final : mdpstate → option mdpstate_ret).

  Record MdpMixin := {
    mixin_to_final_is_final a :
      is_Some (to_final a) → ∀ ac a', step ac a a' = 0;
  }.
End mdp_mixin.

Structure mdp := Mdp {
  mdpstate : Type;
  mdpstate_ret : Type;
  mdpaction : Type;
                     
  mdpstate_eqdec : EqDecision mdpstate;
  mdpstate_count : Countable mdpstate;
  mdpstate_ret_eqdec : EqDecision mdpstate_ret;
  mdpstate_ret_count : Countable mdpstate_ret;
  mdpaction_eqdec : EqDecision mdpaction;
  mdpaction_count : Countable mdpaction;

  step     : mdpaction -> mdpstate → distr mdpstate;
  to_final : mdpstate → option mdpstate_ret;

  mdp_mixin : MdpMixin step to_final;
}.
#[global] Arguments Mdp {_ _ _ _ _ _ _ _ _} _ _ _.
#[global] Arguments step {_}.
#[global] Arguments to_final {_}.

#[global] Existing Instance mdpstate_eqdec.
#[global] Existing Instance mdpstate_count.
#[global] Existing Instance mdpstate_ret_eqdec.
#[global] Existing Instance mdpstate_ret_count.
#[global] Existing Instance mdpaction_eqdec.
#[global] Existing Instance mdpaction_count.

Section scheduler.
  Context {δ : mdp}.
  Context `{Hsch_state: Countable sch_state}.
  Record scheduler:= {
      scheduler_f :> (sch_state * mdpstate δ) -> distr (sch_state * mdpaction δ)
    }.
  Definition scheduler_int_state_f (s:scheduler) ρ := lmarg (s ρ).
  Definition scheduler_action_f (s:scheduler) ρ := rmarg (s ρ).

  
  Section is_final.
    Implicit Types a : mdpstate δ.
    Implicit Types b : mdpstate_ret δ.

    Lemma to_final_is_final a :
      is_Some (to_final a) → ∀ ac a', step ac a a' = 0.
    Proof. apply mdp_mixin. Qed.

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
    Proof. intros. by eexists. Qed.

    Lemma is_final_dzero a ac : is_final a → step ac a = dzero.
    Proof.
      intros Hf.
      apply distr_ext=> a'.
      rewrite to_final_is_final //.
    Qed.

    #[global] Instance is_final_dec a : Decision (is_final a).
    Proof. rewrite /is_final. apply _. Qed.
    
  End is_final.


  (** Everything below is dependent on an instance of a scheduler (and an mdp) 0*)
  Context (sch:scheduler).

  
  Section reducible.
    Implicit Types ρ : sch_state * mdpstate δ.

    Definition reducible ρ := ∃ ac a', scheduler_action_f sch ρ ac > 0 /\ step ac ρ.2 a' > 0.
    Definition irreducible ρ := ∀ ac a', scheduler_action_f sch ρ ac = 0 \/ step ac ρ.2 a' = 0.
    Definition stuck a := ¬ is_final a.2 ∧ irreducible a.
    Definition not_stuck a := is_final a.2 ∨ reducible a.

    Lemma not_reducible a  : ¬ reducible a ↔ irreducible a.
    Proof.
      rewrite /reducible /irreducible. split.
      - intros H ac a'.
        apply (not_exists_forall_not _ _) with ac in H.
        apply (not_exists_forall_not _ _) with a' in H.
        apply not_and_or_not in H as [|].
        + left. pose proof pmf_pos (scheduler_action_f sch a) ac.
          lra.
        + right. pose proof pmf_pos (step ac a.2) a'.
          lra.
      - intros H [x[x'[]]]. 
        specialize (H x x') as [|]; lra.
    Qed.

    Lemma reducible_not_final a :
      reducible a → ¬ is_final a.2.
    Proof. move => [] a' /[swap] /is_final_dzero -> []?[]??. inv_distr. Qed.

    Lemma is_final_irreducible a : is_final a.2 → irreducible a.
    Proof. intros ??. rewrite is_final_dzero //. naive_solver. Qed.

    Lemma not_not_stuck a : ¬ not_stuck a ↔ stuck a.
    Proof.
      rewrite /stuck /not_stuck -not_reducible.
      destruct (decide (is_final a.2)); naive_solver.
    Qed.

    (* Lemma irreducible_dzero a ac: *)
    (*   irreducible a → step ac a = dzero. *)
    (* Proof. *)
    (*   intros Hirr%not_reducible. apply dzero_ext=> a'. *)
    (*   destruct (decide (step ac a a' = 0)); [done|]. *)
    (*   exfalso. eapply Hirr. *)
    (*   exists ac, a'. *)
    (*   pose proof (pmf_le_1 (step ac a) a'). *)
    (*   pose proof (pmf_pos (step ac a) a'). *)
    (*   lra. *)
    (* Qed. *)

    Lemma reducible_not_stuck a :
      reducible a → not_stuck a.
    Proof. intros. by right. Qed.

    (* Lemma mass_pos_reducible a ac : *)
    (*   SeriesC (step ac a) > 0 → reducible a. *)
    (* Proof. intros [??]%SeriesC_gtz_ex; try done. *)
    (*        rewrite /reducible. naive_solver. *)
    (* Qed. *)

    (* Lemma reducible_mass_pos a ac : *)
    (*   reducible a → SeriesC (step ac a.2) > 0. *)
    (* Proof. *)
    (*   intros [a' [Ha []]]. *)
    (*   eapply Rlt_le_trans; [done|]. *)
    (*   apply pmf_le_SeriesC. *)
    (* Qed. *)
  End reducible.

  Section step.
    (* sch_step takes a strict step and returns the whole configuration, including the sch state *)
    Definition sch_step (ρ:sch_state*mdpstate δ) : distr(sch_state*mdpstate δ) :=
      sch ρ ≫= (λ '(sch_σ', mdp_a), dmap (λ mdp_σ', (sch_σ', mdp_σ')) (step mdp_a ρ.2)).

    Definition sch_stepN (n:nat) p := iterM n sch_step p.

    Lemma sch_stepN_O :
      sch_stepN 0 = dret.
    Proof. done. Qed.

    Lemma sch_stepN_Sn a n :
      sch_stepN (S n) a = sch_step a ≫= sch_stepN n.
    Proof. done. Qed.

    Lemma sch_stepN_1 a :
      sch_stepN 1 a = sch_step a.
    Proof. rewrite sch_stepN_Sn sch_stepN_O dret_id_right //. Qed.

    Lemma sch_stepN_plus a (n m : nat) :
      sch_stepN (n + m) a = sch_stepN n a ≫= sch_stepN m.
    Proof. apply iterM_plus. Qed.

    Lemma sch_stepN_Sn_inv n a0 a2 :
      sch_stepN (S n) a0 a2 > 0 →
      ∃ a1, sch_step a0 a1 > 0 ∧ sch_stepN n a1 a2 > 0.
    Proof. intros (?&?&?)%dbind_pos. eauto. Qed.

    Lemma sch_stepN_det_steps n m a1 a2 :
      sch_stepN n a1 a2 = 1 →
      sch_stepN n a1 ≫= sch_stepN m = sch_stepN m a2.
    Proof. intros ->%pmf_1_eq_dret. rewrite dret_id_left //. Qed.

    Lemma sch_stepN_det_trans n m a1 a2 a3 :
      sch_stepN n a1 a2 = 1 →
      sch_stepN m a2 a3 = 1 →
      sch_stepN (n + m) a1 a3 = 1.
    Proof.
      rewrite sch_stepN_plus.
      intros ->%pmf_1_eq_dret.
      replace (dret a2 ≫= _)
        with (sch_stepN m a2); [|by rewrite dret_id_left].
      intros ->%pmf_1_eq_dret.
      by apply dret_1.
    Qed.

    (* sch_step_or_final does a non-strict step, and returns whole configuration *)
    Definition sch_step_or_final a :=
      match to_final a.2 with
      | Some _ => dret a
      | None => sch_step a
      end.

    Definition sch_pexec (n:nat) p := iterM n sch_step_or_final p.

    Lemma sch_pexec_O a :
      sch_pexec 0 a = dret a.
    Proof. done. Qed.

    Lemma sch_pexec_Sn a n :
      sch_pexec (S n) a = sch_step_or_final a ≫= sch_pexec n.
    Proof. done. Qed.

    Lemma sch_pexec_plus ρ n m :
      sch_pexec (n + m) ρ = sch_pexec n ρ ≫= sch_pexec m.
    Proof. rewrite /sch_pexec iterM_plus //.  Qed.

    Lemma sch_pexec_1 :
      sch_pexec 1 = sch_step_or_final.
    Proof.
      extensionality a.
      rewrite sch_pexec_Sn /sch_pexec /= dret_id_right //.
    Qed.

    Lemma sch_pexec_Sn_r a n :
      sch_pexec (S n) a = sch_pexec n a ≫= sch_step_or_final.
    Proof.
      assert (S n = n + 1)%nat as -> by lia.
      rewrite sch_pexec_plus sch_pexec_1 //.
    Qed.

    (* Lemma sch_pexec_is_final n a : *)
    (*   is_final a → sch_pexec n a = dret a. *)
    (* Proof. *)
    (*   intros ?. *)
    (*   induction n. *)
    (*   - rewrite pexec_O //. *)
    (*   - rewrite pexec_Sn step_or_final_is_final //. *)
    (*     rewrite dret_id_left -IHn //. *)
    (* Qed. *)

    (* Lemma pexec_no_final a n : *)
    (*   ¬ is_final a → *)
    (*   pexec (S n) a = step a ≫= pexec n. *)
    (* Proof. intros. rewrite pexec_Sn step_or_final_no_final //. Qed. *)

    (* Lemma sch_pexec_det_step n a1 a2 a0 : *)
    (*   sch_step a1 a2 = 1 → *)
    (*   sch_pexec n a0 a1 = 1 → *)
    (*   sch_pexec (S n) a0 a2 = 1. *)
    (* Proof. *)
    (*   rewrite sch_pexec_Sn_r. *)
    (*   intros Hs ->%pmf_1_eq_dret. *)
    (*   rewrite dret_id_left /=. *)
    (*   case_match; [|done]. *)
    (*   assert (sch_step a1 a2 = 0) as Hns; [by eapply to_final_is_final|]. *)
    (*   lra. *)
    (* Qed. *)

    Lemma sch_pexec_det_steps n m a1 a2 :
      sch_pexec n a1 a2 = 1 →
      sch_pexec n a1 ≫= sch_pexec m = sch_pexec m a2.
    Proof. intros ->%pmf_1_eq_dret. rewrite dret_id_left //. Qed.

    (* Lemma sch_stepN_pexec_det n x y: *)
    (*   sch_stepN n x y = 1 → sch_pexec n x y = 1. *)
    (* Proof. *)
    (*   rewrite /sch_stepN /sch_pexec. *)
    (*   intros H'. *)
    (*   apply Rle_antisym; [done|]. *)
    (*   rewrite -H'. *)
    (*   apply iterM_mono => a a'. *)
    (*   destruct (decide (is_final a)). *)
    (*   - rewrite to_final_is_final //. *)
    (*   - rewrite step_or_final_no_final //. *)
    (* Qed. *)

    (* exec takes non-strict steps and returns the final mstate_ret,
     in a language setting, that's the value
     *)

    Fixpoint sch_exec (n:nat) (ρ : sch_state * mdpstate δ) {struct n} : distr (mdpstate_ret δ) :=
      let '(sch_σ, mdp_σ) := ρ in
      match to_final mdp_σ, n with
      | Some b, _ => dret b
      | None, 0 => dzero
      | None, S n => sch_step ρ ≫= sch_exec n
      end.

    Lemma sch_exec_is_final a b c n :
      to_final a = Some b → sch_exec n (c, a) = dret b.
    Proof. destruct n; simpl; by intros ->. Qed.

    Lemma sch_exec_Sn a n :
      sch_exec (S n) a = sch_step_or_final a ≫= sch_exec n.
    Proof.
      rewrite /sch_step_or_final /=.
      destruct a. simpl.
      case_match; [|done].
      rewrite dret_id_left -/sch_exec.
      by erewrite sch_exec_is_final.
    Qed.
    
    Lemma sch_exec_mono a n v :
      sch_exec n a v <= sch_exec (S n) a v.
    Proof.
      apply refRcoupl_eq_elim.
      move : a.
      induction n.
      - intros [].
        apply refRcoupl_from_leq.
        intros b. rewrite /distr_le /=.
        by case_match.
      - intros []; do 2 rewrite sch_exec_Sn.
        eapply refRcoupl_dbind; [|apply refRcoupl_eq_refl].
        by intros ? ? ->.
    Qed.
    
    (** * TODO: lemmas for sch_exec *)

    (** * Full evaluation (limit of stratification) *)
    Definition sch_lim_exec (ρ : sch_state * mdpstate δ) : distr (mdpstate_ret δ) :=
      lim_distr (λ n, sch_exec n ρ) (sch_exec_mono ρ).
    
  End step.

End scheduler.

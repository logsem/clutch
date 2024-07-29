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
  Context `{Countable sch_state}.
  Record scheduler:= {
      scheduler_f :> sch_state -> mdpstate δ -> distr (sch_state * mdpaction δ)
    }.
  Definition scheduler_int_state_f (s:scheduler) i e := lmarg (s i e).
  Definition scheduler_action_f (s:scheduler) i e := rmarg (s i e).

  Context (sch:scheduler).
  (* sch_step takes a strict step and returns the whole configuration, including the sch state *)
  Definition sch_step (p:sch_state*mdpstate δ) : distr(sch_state*mdpstate δ) :=
    let '(sch_σ, mdp_σ) := p in
    sch sch_σ mdp_σ ≫= (λ '(sch_σ', mdp_a), dmap (λ mdp_σ', (sch_σ', mdp_σ')) (step mdp_a mdp_σ)).

  Definition sch_stepN (n:nat) p := iterM n sch_step p.

  (** * TODO: Lemmas for sch_stepN *)

  (* sch_step_or_final does a non-strict step, and returns whole configuration *)
  Definition sch_step_or_final a :=
    match to_final a.2 with
    | Some _ => dret a
    | None => sch_step a
    end.

  Definition sch_pexec (n:nat) p := iterM n sch_step_or_final p.

  (** * TODO: Lemmas for pexec *)

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
  

End scheduler.

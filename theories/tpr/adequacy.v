From Coq Require Export Reals Psatz.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Import fancy_updates ghost_map.
From iris.bi Require Export fixpoint big_op.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.bi Require Import weakestpre.
From clutch.program_logic Require Import tpr_weakestpre.
From clutch.prob_lang Require Import lang.
From clutch.prob Require Import couplings distribution.

Section spec_exec.
  Context `{spec A Σ}.
 
  Fixpoint spec_exec (n : nat) (a : A) {struct n} : distr A :=
    match bool_decide (spec_final a), n with
      | true, _ => dret a
      | false, 0 => dzero
      | false, S n => spec_step a ≫= spec_exec n
    end.

  Lemma spec_exec_mon a n a' :
    spec_exec n a a' <= spec_exec (S n) a a'.
  Proof.
    apply refRcoupl_eq_elim.
    move : a.
    induction n.
    - intros.
      apply refRcoupl_from_leq.
      intros w. rewrite /distr_le /=.
      by case_match.
    - intros. simpl.
      case_bool_decide.
      + by apply refRcoupl_dret.
      + eapply refRcoupl_dbind; [|apply refRcoupl_eq_refl].
        intros ? ? ->. apply IHn.
  Qed.
  
End spec_exec.   


Section adequacy.
  Context `{!irisGS prob_lang Σ} `{spec A Σ}.

  (* TODO: some resource for tracking [a] in the post condition *)
  Theorem wp_refRcoupl_step_fupdN (e : expr) (σ : state) (a : A) (n : nat) (φ : val → A → Prop)  :
    state_interp σ ∗ spec_interp a ∗ RWP e ⟨⟨ v, ∃ (a : A), ⌜spec_final a⌝ ∗ ⌜φ v a⌝ ⟩⟩ ⊢ 
    |={⊤,∅}=> |={∅}▷=>^n ⌜lim_exec_val (e, σ) ≿ spec_exec n a : φ⌝.
  Proof.
    Admitted. 

End adequacy.    

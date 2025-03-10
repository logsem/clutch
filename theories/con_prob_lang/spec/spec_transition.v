From Coq Require Import Reals Psatz.
From clutch.con_prob_lang Require Import lang.
From clutch.common Require Export con_language.
From clutch.prob Require Export distribution.

Set Default Proof Using "Type*".

Section spec_transition.
  Definition spec_transition_compress (ρ: cfg con_prob_lang) (μ : distr nat)
    (f: nat -> cfg con_prob_lang -> distr (cfg con_prob_lang)) 
    : distr (cfg con_prob_lang) :=
    (μ ≫= (λ tid, (dbind (λ ρ', f tid ρ') (step tid ρ)))).

  Inductive spec_transition (ρ:cfg con_prob_lang) : distr (cfg con_prob_lang) ->  Prop :=
  | spec_transition_dret : spec_transition ρ (dret ρ)
  | spec_transition_step (μ : distr nat)
      (f: nat -> cfg con_prob_lang -> distr (cfg con_prob_lang)):
    (∀ (tid:nat), (μ tid > 0)%R -> 
                (forall ρ', step tid ρ ρ' > 0 -> spec_transition ρ' (f tid ρ'))) ->
    spec_transition ρ (spec_transition_compress ρ μ f )
  .

  Lemma spec_transition_step' ρ μ μ1 f :
    μ=spec_transition_compress ρ μ1 f ->
    (∀ (tid:nat), (μ1 tid > 0)%R -> 
                (forall ρ', step tid ρ ρ' > 0 -> spec_transition ρ' (f tid ρ'))) ->
    spec_transition ρ μ.
  Proof.
    intros -> ?.
    by apply spec_transition_step.
  Qed.

  Lemma spec_transition_bind ρ μ f:
    spec_transition ρ μ ->
    (∀ ρ', (μ ρ'> 0)%R -> spec_transition ρ' (f ρ')) ->
    spec_transition ρ (μ≫=f).
  Proof.
    intros H.
    revert f.
    induction H as [|H μ f IH1 IH2].
    - intros. rewrite dret_id_left.
      apply H. solve_distr.
    - intros f' Hf'.
      rewrite /spec_transition_compress.
      rewrite -!dbind_assoc.
      eapply (spec_transition_step' _ _ μ).
      + rewrite /spec_transition_compress.
        apply dbind_ext_right.
        intros. by rewrite -dbind_assoc.
      + simpl. intros. apply IH2; try done.
        intros. apply Hf'.
        rewrite /spec_transition_compress.
        apply dbind_pos. eexists _; split; last done.
        apply dbind_pos. eexists _; by split.
  Qed.
End spec_transition.

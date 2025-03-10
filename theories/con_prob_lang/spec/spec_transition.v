From Coq Require Import Reals Psatz.
From clutch.con_prob_lang Require Import lang.
From clutch.common Require Export con_language.
From clutch.prob Require Export distribution.

Set Default Proof Using "Type*".

Section spec_transition.
  Definition spec_transition_compress (ρ: cfg con_prob_lang) (μ : distr (option nat))
    (f: nat -> cfg con_prob_lang -> distr (cfg con_prob_lang)) (μ' : distr (cfg con_prob_lang))
    : distr (cfg con_prob_lang) :=
    (μ ≫= (λ (o:option nat),
             match o with
             | Some tid => (dbind (λ ρ', f tid ρ') (step tid ρ))
             | None => μ'
             end
    )).

  Inductive spec_transition (ρ:cfg con_prob_lang) : distr (cfg con_prob_lang) ->  Prop :=
  | spec_transition_dret : spec_transition ρ (dret ρ)
  | spec_transition_bind (μ : distr (option nat))
      (f: nat -> cfg con_prob_lang -> distr (cfg con_prob_lang)) (μ' : distr (cfg con_prob_lang)):
    (∀ (tid:nat), (μ (Some tid) > 0)%R -> 
                (forall ρ', step tid ρ ρ' > 0 -> spec_transition ρ' (f tid ρ'))) ->
    ((μ None > 0)%R -> spec_transition ρ μ') ->
    spec_transition ρ (spec_transition_compress ρ μ f μ')
  .

  Lemma spec_transition_bind' ρ μ μ1 f μ2 :
    μ=spec_transition_compress ρ μ1 f μ2 ->
    (∀ (tid:nat), (μ1 (Some tid) > 0)%R -> 
                (forall ρ', step tid ρ ρ' > 0 -> spec_transition ρ' (f tid ρ'))) ->
    ((μ1 None > 0)%R -> spec_transition ρ μ2) ->
    spec_transition ρ μ.
  Proof.
    intros -> ??.
    by apply spec_transition_bind.
  Qed.
End spec_transition.

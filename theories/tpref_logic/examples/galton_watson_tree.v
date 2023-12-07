From Coq Require Import Reals Psatz.
From clutch.prob_lang Require Import lang notation.
From clutch.tpref_logic Require Import weakestpre spec primitive_laws proofmode adequacy.
From clutch.prob Require Import distribution markov.

Section galton_watson_model.
  Context (μ : distr nat).

  Definition gw_step (n : nat) : distr nat :=
    if n is 0 then dzero
    else m ← μ; dret (n - 1 + m)%nat.

  Definition gw_to_final (n : nat) : option nat :=
    if n is 0 then Some 0%nat else None.

  Definition gw_mixin : MarkovMixin gw_step gw_to_final.
  Proof. constructor. by intros [] [] []; simplify_eq=>/=. Qed.

  Canonical Structure gw_walk : markov := Markov _ _ gw_mixin.

End galton_watson_model.

From iris.proofmode Require Import base proofmode.
From iris.bi Require Export weakestpre fixpoint big_op.
From iris.base_logic.lib Require Import ghost_map invariants fancy_updates.
From iris.algebra Require Import excl.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.delay_prob_lang Require Import notation.
From clutch.common Require Export language.
From clutch.base_logic Require Import error_credits.
From clutch.elton Require Import weakestpre primitive_laws.
From clutch.prob Require Import distribution.
Import uPred.

Fixpoint distr_urns_f (m:list(loc*urn)) : distr (gmap loc nat) :=
  match m with
  | [] => dret ∅
  | (k, u) :: rest =>
      let l:=elements u in
      if bool_decide (l=[]) then distr_urns_f rest
      else let x := distr_urns_f rest in
           x ≫= (λ m, dunifP (size u+1)%nat ≫=
                        (λ n, match l!!(fin_to_nat n) with
                              | Some num =>dret (<[k:=num]> m)
                              | None => dzero (* impossible *)
                              end
             ))
  end.



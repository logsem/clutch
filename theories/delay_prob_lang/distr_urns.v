From clutch.prelude Require Export stdpp_ext tactics.
From clutch.delay_prob_lang Require Import lang notation.
From clutch.prob Require Export distribution.

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

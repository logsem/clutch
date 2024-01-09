From clutch.ub_logic Require Export ub_weakestpre.

Import uPred.

(** * The total weakest precondition *)
Definition ub_twp_pre `{!irisGS Λ Σ}
  (wp : coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
    coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
  match to_val e1 with
  | Some v => |={E}=> Φ v
  | None => ∀ σ1 ε,
      state_interp σ1 ∗ err_interp ε ={E,∅}=∗
      exec_ub e1 σ1 (λ ε2 '(e2, σ2),
        |={∅,E}=> state_interp σ2 ∗ err_interp ε2 ∗ wp E e2 Φ) ε
end%I.


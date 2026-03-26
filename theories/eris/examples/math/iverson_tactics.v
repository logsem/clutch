From clutch.eris.examples.math Require Import prelude iverson.
From clutch.eris Require Import infinite_tape.

Import Hierarchy.
Set Default Proof Using "Type*".
#[local] Open Scope R.

(** * Iverson Bracket Tactics

    Automation for simplifying Iverson bracket expressions.
    Handles common patterns:
    - Rewriting [Iverson_True]/[Iverson_False] with side-condition discharge
    - Cleaning up [Rmult_1_l], [Rmult_0_l], [Rplus_0_l], [Rplus_0_r] after rewriting
    - Proving non-negativity of Iverson-weighted terms
*)

(** Simplify a single Iverson bracket applied to a concrete value.
    Tries [Iverson_True] then [Iverson_False], discharging side conditions
    with [intuition], [done], or [simpl; intuition]. *)
Ltac solve_iverson_side :=
  first [ done
        | cbv; tauto
        | cbv; done
        | tauto
        | lia
        | lra
        | simpl; lia
        | simpl; lra
        | intuition done
        | intuition lia
        | intuition lra ].

(** Simplify a single Iverson bracket applied to a concrete value.
    Uses [assert] + [rewrite] to fully commit only when the side condition
    is provable. *)
Ltac iverson_simp1 :=
  match goal with
  | |- context [ Iverson ?P ?t ] =>
    let H := fresh "HIv" in
    first [
      assert (H : P t) by solve_iverson_side;
      rewrite (Iverson_True H); clear H
    |
      assert (H : ¬ P t) by solve_iverson_side;
      rewrite (Iverson_False H); clear H
    ]
  end.

Ltac arith_iverson :=
  repeat (first [ rewrite Rmult_0_l
                | rewrite Rmult_1_l
                | rewrite Rplus_0_l
                | rewrite Rplus_0_r
                | rewrite Rmult_0_r ]).

(** Repeatedly simplify all Iverson brackets in the goal, then clean up
    trivial arithmetic ([0*x], [1*x], [x+0], [0+x]). *)
Ltac simp_iverson :=
  repeat iverson_simp1;
  arith_iverson.

(** Prove [0 <= Iverson P t * x] when [0 <= x]. *)
Lemma Iverson_Rmult_nonneg {T} {P : T -> Prop} {t : T} {x : R} (Hx : 0 <= x) :
  0 <= Iverson P t * x.
Proof. apply Rmult_le_pos; [apply Iverson_nonneg | exact Hx]. Qed.

(** Prove [0 <= x * Iverson P t] when [0 <= x]. *)
Lemma Iverson_Rmult_nonneg' {T} {P : T -> Prop} {t : T} {x : R} (Hx : 0 <= x) :
  0 <= x * Iverson P t.
Proof. apply Rmult_le_pos; [exact Hx | apply Iverson_nonneg]. Qed.

(** Solve goals of the form [0 <= Iverson _ _ * _] or [0 <= _ * Iverson _ _]. *)
Ltac iverson_nonneg :=
  first [ apply Iverson_Rmult_nonneg; auto
        | apply Iverson_Rmult_nonneg'; auto
        | apply Iverson_nonneg ].

(** Solve goals of the form [0 <= A + B] where each summand involves Iverson brackets. *)
Ltac iverson_sum_nonneg :=
  apply Rplus_le_le_0_compat; iverson_nonneg.

(** An implementation of Papadimitriou's randomized algorithm for 2-SAT in
    ProbLang.

    Papadimitriou's algorithm is the following random walk:

      1. Pick an arbitrary (here, uniformly random) initial assignment of the
         [n] propositional variables.
      2. Repeat for at most [iter] steps:
           - If the assignment satisfies every clause, return [true].
           - Otherwise, pick the first unsatisfied clause [(l1, l2)], choose
             one of its two literals uniformly at random, and flip the
             corresponding variable in the assignment.
      3. If we run out of iterations without finding a satisfying assignment,
         return [false].

    Representation:
      - The candidate assignment is a mutable array of booleans of length [n].
      - A literal is a pair [(b, i)] where [b : bool] indicates whether the
        variable is negated and [i] is the index of the variable in the
        assignment array.
      - A 2-clause is a pair [(l1, l2)] of literals.
      - A formula is a [list] of 2-clauses (using the list encoding from
        [clutch.eris.lib.list]).
*)

From clutch.eris Require Import eris.
From clutch.eris.lib Require Import list array.

Set Default Proof Using "Type*".

(** [lang_negb] is the program-level boolean negation. *)
Definition lang_negb : val :=
  λ: "b", if: "b" then #false else #true.

(** [eval_lit a lit] looks up the variable referenced by literal [lit] in the
    assignment array [a] and returns its (possibly negated) value. *)
Definition eval_lit : val :=
  λ: "a" "lit",
    let, ("b", "i") := "lit" in
    let: "v" := !("a" +ₗ "i") in
    if: "b" then lang_negb "v" else "v".

(** [eval_clause a c] evaluates the 2-clause [c = (l1, l2)] under the
    assignment in [a]. It short-circuits on the first satisfied literal. *)
Definition eval_clause : val :=
  λ: "a" "c",
    let, ("l1", "l2") := "c" in
    if: eval_lit "a" "l1" then #true else eval_lit "a" "l2".

(** [find_unsat a cls] traverses the formula [cls] and returns [SOME c] for
    the first clause [c] not satisfied by [a], or [NONE] if [a] satisfies
    every clause in [cls]. *)
Definition find_unsat : val :=
  rec: "find_unsat" "a" "cls" :=
    match: "cls" with
      NONE => NONE
    | SOME "p" =>
        let, ("c", "t") := "p" in
        if: eval_clause "a" "c" then "find_unsat" "a" "t"
        else SOME "c"
    end.

(** [flip_random_var a c] selects one of the two literals of clause [c]
    uniformly at random and flips the value of its variable in [a]. *)
Definition flip_random_var : val :=
  λ: "a" "c",
    let, ("l1", "l2") := "c" in
    let: "lit" := (if: rand #1 = #0 then "l1" else "l2") in
    let: "i" := Snd "lit" in
    let: "v" := !("a" +ₗ "i") in
    ("a" +ₗ "i") <- lang_negb "v".

(** [papa_loop a cls iter] performs at most [iter] random-walk steps on the
    assignment array [a] for the formula [cls]. It returns [#true] as soon as
    the current assignment satisfies every clause, and [#false] if it exhausts
    its iteration budget. The array [a] is mutated in place. *)
Definition papa_loop : val :=
  rec: "loop" "a" "cls" "iter" :=
    match: find_unsat "a" "cls" with
      NONE => #true
    | SOME "c" =>
        if: "iter" ≤ #0 then #false
        else
          flip_random_var "a" "c" ;;
          "loop" "a" "cls" ("iter" - #1)
    end.

Definition init_rand : val :=
  λ: "n", array_init "n" (λ: "x", rand #1 = #0).

(** [papa_2sat n cls iter] runs Papadimitriou's algorithm on the formula
    [cls] over [n] variables for at most [iter] steps. It returns a pair
    [(sat, a)] where [sat : bool] indicates whether a satisfying assignment
    was found and [a] is the (location of the) final candidate assignment. *)
Definition papa_2sat : val :=
  λ: "n" "cls" "iter",
    let: "a" := init_rand "n" in
    let: "sat" := papa_loop "a" "cls" "iter" in
    ("sat", "a").

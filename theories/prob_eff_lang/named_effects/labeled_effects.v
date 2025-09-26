(* labeled_effects.v *)

From iris.proofmode Require Import base tactics classes.
From clutch.prob_eff_lang          Require Import weakestpre notation tactics
                                   shallow_handler.

Set Default Proof Using "Type".


(** * Implementation. *)

Section implementation.

Definition effect : val := λ: <>, Alloc #().

Definition perform : val := λ: "l" "v", do:("l", "v").

Definition shandle : val := rec: "shandle" "l" "client" "h" "r" :=
  TryWith ("client" #())
  (* Effect branch: *)
    (λ: "args" "k",
      let: "l'" := Fst "args" in
      let: "v"  := Snd "args" in
      if: "l" = "l'" then
        "h" "v" "k"
      else
        let: "y" := (do: "args") in
        "shandle" "l" (λ: <>, "k" "y") "h" "r")
  (* Return branch: *)
    (λ: "res", "r" "res").

Definition handle (n : expr) : expr := rec: "handle" "client" "h" "r" :=
  shandle n "client"
  (* Effect branch: *)
    (λ: "v" "k",
      "h" "v" (λ: "w", "handle" (λ: <>, "k" "w") "h" "r"))
  (* Return branch: *)
    (λ: "res", "r" "res").

End implementation.

From clutch.eris Require Export eris error_rules.
From Coquelicot Require Import Series.
Require Import Lra.

Section golden_toss.
  Context `{!erisGS Σ}.

  (* Example from:
   * https://conferences.au.dk/fileadmin/conferences/2025/confest/ChristophMatheja_QESTFORMATS.pdf 
   * p.4
   *)
  Definition golden_toss_tape : expr :=
    rec: "toss" "a" "α" :=
      let: "x" := rand("α") #1 in
      if: ("x" = #1) 
        then #()
        else "toss" #() "α" ;; "toss" #() "α" ;; "toss" #() "α".
  
  Definition prog_tape : expr :=
    let: "α" := alloc #1 in
    golden_toss_tape #() "α".

  Definition golden_toss : val :=
    rec: "toss" "a" :=
      let: "x" := rand #1 in
      if: ("x" = #1) 
        then #()
        else "toss" #() ;; "toss" #() ;; "toss" #().
  
  Definition prog : expr :=
    golden_toss #().

  (* make termination probability of `toss` to be `x` 
   * then we have `x = 1/2 ( 1 + x^3 )` which has 3 roots:
   * 1, φ - 1, and -φ (where φ = (sqrt 5 + 1) / 2 is the golden ratio)
   * 1 and -φ are obviously not the right answer, so the termination probability
   * is φ - 1
   *)

  (* φ' = 1 - (φ - 1) = 2 - φ = (3 - sqrt 5) / 2 *)
  Definition φ' : R := (3 - sqrt 5) / 2.

  Lemma golden_toss_spec E :
    ⊢ ↯ (φ') -∗ WP prog @ E [{ _, True%I }].
  Proof.
  Abort.


End golden_toss.

From clutch.eris Require Import eris tutorial.eris_rules.
From clutch.eris.tutorial Require Import eris_rules.

(* ###################################################################### *)
(** * Geometric distribution *)

Section geometric_total.
  Context `{!erisGS Σ}.

  (** Before, we have mentioned that we are working with a partial correctness
       version of Eris. That is, we consider non-termination as a valid
       behavior. In particular a diverging program satisfies any specification.
       Let's show this more concretely *)

  Definition loop : val :=
    rec: "loop" "n" := if: rand #0 = #0 then "loop" "n" else #42.


  Lemma loop_false :
    {{{ True }}} loop #() {{{ m, RET #m; False }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    iLöb as "IH".
    (** There is a later modality in front of our IH *)
    (** Let's take a single execution step *)
    unfold loop.
    wp_pure.
    (** Two things have happened. First, the program has taken an execution
        Second, the ▷ in front of our IH has been removed.
        We continue the execution *)
    wp_apply (wp_rand_nat); auto.
    iIntros (n) "%Hn".
    inversion Hn; [|nat_solver].
    do 2 wp_pure.
    (** We now apply the IH and conclude *)
    iApply "IH".
    iModIntro.
    iApply "HΦ".
  Qed.


  (** Eris defines a second total correctness version of the logic.

      Triples for total correctness use the syntax

             [[{ P }]] e [[{ v, RET #v; Q }]]

   *)


  (** Recall the definition of the geometric process *)

  Definition geometric : val :=
    rec: "geo" "n" :=
      if: rand #2 = #0 then #0 else "geo" "n" + #1.

  (** Let's show that it terminates with probability 1. *)

  (** We will use "error induction": 

         ⌜ 0 < ε ⌝ ∗ ⌜ ε < ε' ⌝ ∗ (↯ ε' -∗ P) ∗ ↯ ε ⊢ P
        ---------------------------------------------------
                              ↯ ε ⊢ P

   *)

  Lemma geo_nonneg_pos_err (ε : R) :
    [[{ ⌜0 < ε⌝%R ∗ ↯ ε }]] geometric #() [[{ m, RET #m; ⌜0 ≤ m⌝%Z }]].
  Proof.
    iIntros (Φ) "(%Hε & Herr)".
    (**  Error induction can be used through the rule [ec_induction],
         setting ε' := 3/2 *)
    iRevert (Φ).
    iApply (ec_induction ε ((3/2)*ε)); auto.
    { real_solver. }
    iIntros "(IH & Herr)".
    iIntros (Φ) "HΦ".
    wp_lam.

    set (F (n:nat) := if bool_decide (n=0) then 0%R else ((3/2)*ε)%R).
    wp_apply (twp_rand_exp F 2 with "Herr").
    { intro n.
      unfold F.
      real_solver. }
    { unfold F.
      simpl.
      real_solver. }
    iIntros (n) "[%Hn Herr]".
    unfold F.
    destruct n.
    - (** The case n=0 does not make any recursive call, so we can conclude
          by symbolic execution *)
      wp_pures. by iApply ("HΦ").
    - do 2 wp_pure.
      (** The case 1 <= n calls #geometric recursively *)
      wp_bind (geometric #()).
      simpl.
      (** Note that now, we have amplified our error credits to [3/2 * ε],
          so we have enough credits to apply IH *)
      iApply ("IH" with "Herr [HΦ]").
      iIntros (m) "%Hm".
      wp_pures.
      iApply "HΦ".
      iPureIntro.
      real_solver.
  Qed.

  (** But where do we get the error credits [↯ε]?

      The logic allows us to produce an arbitrarily small ↯ε 
      "out of thin air". 

   *)

  (**  We can use this principle to prove the final spec *)
  Lemma geo_nonneg :
    [[{ True }]] geometric #() [[{ m, RET #m; ⌜0 ≤ m⌝%Z }]].
  Proof.
    iIntros (Φ) "_ HΦ".
    (** A positive amount of error credits can be obtained with [twp_err_pos]  *)
    iApply twp_err_pos; auto.
    iIntros (ε) "%Hε Herr".
    (** We can now use the specification proven above *)
    iApply (geo_nonneg_pos_err with "[$Herr]"); auto.
  Qed.

End geometric_total.

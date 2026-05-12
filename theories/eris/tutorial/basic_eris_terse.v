From clutch.eris Require Import eris tutorial.eris_rules.
From clutch.eris.tutorial Require Import eris_rules basic.

(* ###################################################################### *)
(** * Eris *)

Section eris_introduction.
  Context {Σ : gFunctors}.
  Context {Heris : erisGS Σ}.

  (** Error credits can be combined. xx *)
  Lemma error_credit_split :
    ↯ (1/4 + 1/4) ⊢ ↯ (1/4) ∗ ↯ (1/4).
  Proof.
  Abort.

  (** Error credits can be combined. xx *)
  Lemma error_credit_combine :
    ↯ (1/4) ∗ ↯ (1/4) ⊢ ↯ (1/2).
  Proof.
  Abort.

  (** If we own [↯ ε] and [1 <= ε] then we can prove [False]! xx *)
  Lemma error_credit_False ε :
    (1 <= ε)%R →
    ↯ ε ⊢ False.
  Proof.
  Abort.

  (** Exercise:
      If we can combine enough error credits to get above 1, any conclusion follows.
      xx *)
  Lemma error_credit_accumulate P Q :
    ↯ (2/3) ∗ (P -∗ ↯ (1/2)) -∗ P -∗ Q.
  Proof.
  Abort.

  (** The programming language [ProbLang] we consider in this tutorial has a
      single probabilistic connective [rand #N]. The expression [rand #N]
      evalautes uniformly at random to a value in the set [{0, 1, ..., N}]. For
      example, the expression [rand #1] corresponds to a coin flip, reducing
      with probability [1/2] to either [0] or [1]. *)
  Lemma wp_coin_flip :
    {{{ True }}} rand #1 {{{ (n : nat), RET #n; ⌜n = 0 ∨ n = 1⌝ }}}.
  Proof.
    iIntros "%Φ HP HΦ".
    (* xx *)
    wp_apply wp_rand.
  Abort.

  (** Let's try another example: The expression [rand #2] samples uniformly from
      the set [{0, 1, 2}]. The program therefore returns [false] with probability
      [1/3], and [true] with probability [2/3]. xx *)
  Definition unif_3_eq : expr :=
    if: rand #2 = #0 then #false else #true.

  (** Let's write a spec using error credits that captures this idea. xx *)
  Lemma wp_unif_3 :
    {{{ ↯ (1 / 3) }}} unif_3_eq {{{ (b : bool), RET #b; ⌜b = true⌝ }}}.
  Proof.
    iIntros (Φ) "Hε HΦ".
    unfold unif_3_eq.
    (** Here we apply [wp_rand_err] that allows us "spend" [1 / (N + 1)] error
        credits to avoid a concrete outcome in the range [0..N]. We choose [0]
        to be the outcome we want to avoid. xx *)
    wp_apply (wp_rand_err 0 with "[Hε]").
    { iApply (ec_eq with "Hε"). simpl. real_solver. }
  Abort.

  (** For proving tight bounds, [wp_rand_err] is not always enough.  *)
  Definition twoflip : expr :=
    if: rand #1 = #1 then #true
    else
      if: rand #1 = #1 then #true
      else #false.

  (** Notice how in the [twoflip] program, the program returns [false] with
      probability [1/4]. However, to "avoid" this erroneous outcome, we need
      [1/2] error credits. As such, we need to "scale" the initial error budget
      using expectation-preserving composition via [wp_rand_exp] *)
  Lemma wp_twoflip :
    {{{ ↯ (1 / 4) }}} twoflip {{{ (b : bool), RET #b; ⌜b = true⌝ }}}.
  Proof.
    iIntros (Φ) "Hε HΦ".
    unfold twoflip.
    set (F (n : nat) := if bool_decide (n = 1) then 0%R else (1/2)%R).
    (* We perform the first sampling, and distribute ε according to F. xx *)
    wp_apply (wp_rand_exp F with "Hε").
    { intros n. unfold F. real_solver. }
    { unfold F. simpl. real_solver. }

  Abort.

  (** Eris is a partial correctness logic. *)

  Definition loop : val :=
    rec: "loop" "n" := if: rand #0 = #0 then "loop" "n" else #42.


  Lemma loop_false :
    {{{ True }}} loop #() {{{ m, RET #m; False }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    (** We use "Löb induction" to reason about recursion. *)
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

End eris_introduction.

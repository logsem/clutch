From clutch.prob_lang Require Import notation.
From clutch.eris Require Import error_rules.

Notation "# l" := (LitV l%nat%V%stdpp) (at level 8, format "# l").

(** This file collects useful rules for the tutorial. For a more detailed view
    of the rules of Eris, see the [theories/eris/] folder *)
Section rules.
  Context `{!erisGS Σ}.

(** The basic sampling rule essentially acts as a nondeterministic choice,
    no credits are used and the only information we get is that the output
    x is in the range [0...N] *)
Lemma wp_rand_nat (N : nat) E Φ :
  ▷ (∀ x : nat, ⌜x < S N⌝ -∗ Φ #x) -∗
  WP rand #N @ E {{ Φ }}.
Proof.
  iIntros "HΦ".
  iApply clutch.eris.primitive_laws.wp_rand_nat; auto.
Qed.

(** We have a rule for spending ↯(1/(N+1)) to avoid one concrete outcome in the
    range [0..N]. Note that this rule can actually be derived from the more
    general wp_rand_exp_nat, that is below *)
Lemma wp_rand_err_nat (m : nat) (N : nat) E Φ :
  ↯ (1 / (N + 1)) -∗
  ▷ (∀ x : nat, ⌜x ≤ N ∧ x ≠ m⌝ -∗ Φ #x) -∗
  WP rand #N @ E {{ Φ }}.
Proof.
  iIntros "Herr HΦ".
  iApply clutch.eris.error_rules.wp_rand_err_nat; auto.
  rewrite /Rdiv Rmult_1_l.
  iFrame.
Qed.

(** Finally we present the rule for general expectation-preserving composition.
    The user needs to provide ↯ ε1, and gets to choose a credit distribution
    function ε2, as long as (1) it's codomain is the real interval [0,1] and (2)
    it's expected value is no more than ε1. After sampling, we will get a
    natural number n in the range [0..N], and ↯ (ε2 n) error credits. *)
Lemma wp_rand_exp_nat (N : nat) (ε1 : R) (ε2 : nat → R) E Φ :
  (∀ n, (0 <= ε2 n <= 1)%R) →
  (foldr Rplus 0 (ε2 <$> seq 0 (S N)) <= (S N) * ε1 )%R →
  ↯ ε1 -∗
  ▷ (∀ (n : nat), ⌜n ≤ N⌝ ∗ ↯ (ε2 n) -∗ Φ #n) -∗
  WP rand #N @ E {{ Φ }}.
Proof.
   iIntros (Hbd HS) "Herr HΦ".
   iApply (clutch.eris.error_rules.wp_rand_exp_nat with "Herr"); auto.
   rewrite
     (SeriesC_ext _ (λ n : nat, 1 / S N * (if bool_decide (n ≤ N) then ε2 n else 0))%R);
     last first.
   {
     intros n.
     case_bool_decide; real_solver.
   }
   rewrite SeriesC_scal_l.
   rewrite SeriesC_nat_bounded_to_foldr'.
   rewrite Rmult_comm.
   rewrite Rmult_div_assoc Rmult_1_r.
   apply Rcomplements.Rle_div_l.
   - real_solver.
   - real_solver.
Qed.

End rules.

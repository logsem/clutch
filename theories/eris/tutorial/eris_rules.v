From stdpp Require Import namespaces finite.
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext.
From clutch.prob_lang Require Import notation tactics metatheory.
From clutch.prob_lang Require Import lang.
From clutch.eris Require Import lifting proofmode ectx_lifting primitive_laws seq_amplification.
From clutch.eris Require Import total_lifting total_ectx_lifting total_primitive_laws error_rules.

(** This file collects useful rules for the tutorial. For a more detailed
    view of the rules of Eris, see the theories/eris/ folder
 *)


Section rules.
  Context `{!erisGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types v : val.
  Implicit Types l : loc.

Lemma wp_rand_nat (N : nat) E Φ :
  (∀ x : nat, ⌜x < S N⌝ -∗ Φ #x) -∗
  WP rand #N @ E {{ Φ }}.
Proof.
  iIntros "HΦ".
  iApply clutch.eris.primitive_laws.wp_rand_nat; auto.
Qed.


Lemma wp_rand_err_nat (N : nat) (m : nat) E Φ :
  ↯ (1 / (N+1)) -∗
  (∀ x : nat, ⌜(x ≤ N) /\ x ≠ m⌝ -∗ Φ #x) -∗
  WP rand #N @ E {{ Φ }}.
Proof.
  iIntros "Herr HΦ".
  iApply clutch.eris.error_rules.wp_rand_err_nat; auto.
  rewrite /Rdiv Rmult_1_l.
  iFrame.
Qed.

Lemma wp_rand_exp_nat (N : nat) (ε1 : R) (ε2 : nat -> R) E Φ :
  (∀ n, (0 <= ε2 n <= 1)%R) →
  (foldr (Rplus ∘ ε2) 0 (seq 0 (S N)) <= (S N) * ε1 )%R →
  ↯ ε1 -∗ (∀ (n : nat), ⌜ n <= N ⌝ ∗ ↯ (ε2 n) -∗ Φ #n) -∗
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

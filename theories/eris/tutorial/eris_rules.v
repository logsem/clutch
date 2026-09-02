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
Lemma wp_rand (N : nat) E Φ :
  ▷ (∀ x : nat, ⌜x < S N⌝ -∗ Φ #x) -∗
  WP rand #N @ E {{ Φ }}.
Proof.
  iIntros "HΦ".
  iApply clutch.eris.primitive_laws.wp_rand_nat; auto.
Qed.

(** We have a rule for spending ↯(1/(N+1)) to avoid one concrete outcome in the
    range [0..N]. Note that this rule can actually be derived from the more
    general wp_rand_exp_nat, that is below *)
Lemma wp_rand_err (m : nat) (N : nat) E Φ :
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
    function ε2, as long as (1) it's codomain is the non-negative reals and (2)
    it's expected value is no more than ε1. After sampling, we will get a
    natural number n in the range [0..N], and ↯ (ε2 n) error credits. *)
Lemma wp_rand_exp (ε2 : nat → R) (N : nat) (ε1 : R) E Φ :
  (∀ n, (0 <= ε2 n)%R) →
  (foldr Rplus 0 (ε2 <$> seq 0 (S N)) <= (S N) * ε1 )%R →
  ↯ ε1 -∗
  ▷ (∀ (n : nat), ⌜n ≤ N⌝ ∗ ↯ (ε2 n) -∗ Φ #n) -∗
  WP rand #N @ E {{ Φ }}.
Proof.
   iIntros (Hbd HS) "Herr HΦ".
   set (F (n : nat) := Rmin (ε2 n) 1).
   iApply (clutch.eris.error_rules.wp_rand_exp_nat _ _ _ F with "Herr"); auto.
   {
     intros n.
     rewrite /F; split.
     - apply Rmin_glb; real_solver.
     - apply Rmin_r.
   }
   {
     etransitivity.
     - rewrite /F.
       apply (SeriesC_le _
               (λ n : nat, 1 / S N * (if bool_decide (n ≤ N) then ε2 n else 0))%R).
       + intros n; split.
         * case_bool_decide; [|real_solver].
           apply Rmult_le_pos.
           ** real_solver.
           ** apply Rmin_glb; real_solver.
         * case_bool_decide.
           ** apply Rmult_le_compat_l; [real_solver|].
              apply Rmin_l.
           ** real_solver.
       + apply ex_seriesC_scal_l.
         apply ex_seriesC_nat_bounded.
     - rewrite SeriesC_scal_l.
       rewrite SeriesC_nat_bounded_to_foldr'.
       rewrite Rmult_comm.
       rewrite Rmult_div_assoc Rmult_1_r.
       apply Rcomplements.Rle_div_l; real_solver.
   }
   iModIntro.
   iIntros (n) "(%Hn & Herr)".
   iApply "HΦ".
   iSplit; auto.
   destruct (decide (1 <= F n)%R) as [HFn|HFn].
   + iExFalso.
     iApply (ec_contradict with "Herr"); auto.
   + iApply (ec_weaken with "Herr").
     split; auto.
     rewrite /F.
     rewrite /F in HFn.
     apply Rnot_le_gt, Rgt_lt in HFn.
     revert HFn.
     eapply (Rmin_case_strong); real_solver.
Qed.

(** Below we have the total WP version of the rules above. Note
    the lack of a later [▷] in all of the premises *)

Lemma twp_rand (N : nat) E Φ :
  (∀ x : nat, ⌜x < S N⌝ -∗ Φ #x) -∗
  WP rand #N @ E [{ Φ }].
Proof.
  iIntros "HΦ".
  iApply clutch.eris.total_primitive_laws.twp_rand_nat; auto.
Qed.

Lemma twp_rand_err (m : nat) (N : nat) E Φ :
  ↯ (1 / (N + 1)) -∗
  (∀ x : nat, ⌜x ≤ N ∧ x ≠ m⌝ -∗ Φ #x) -∗
  WP rand #N @ E [{ Φ }].
Proof.
  iIntros "Herr HΦ".
  iApply clutch.eris.error_rules.twp_rand_err_nat; auto.
  rewrite /Rdiv Rmult_1_l.
  iFrame.
Qed.


Lemma twp_rand_exp (ε2 : nat → R) (N : nat) (ε1 : R) E Φ :
  (∀ n, (0 <= ε2 n)%R) →
  (foldr Rplus 0 (ε2 <$> seq 0 (S N)) <= (S N) * ε1 )%R →
  ↯ ε1 -∗
  (∀ (n : nat), ⌜n ≤ N⌝ ∗ ↯ (ε2 n) -∗ Φ #n) -∗
  WP rand #N @ E [{ Φ }].
Proof.
   iIntros (Hbd HS) "Herr HΦ".
   set (F (n : nat) := Rmin (ε2 n) 1).
   iApply (clutch.eris.error_rules.twp_rand_exp_nat _ _ _ F with "Herr"); auto.
   {
     intros n.
     rewrite /F; split.
     - apply Rmin_glb; real_solver.
     - apply Rmin_r.
   }
   {
     etransitivity.
     - rewrite /F.
       apply (SeriesC_le _
               (λ n : nat, 1 / S N * (if bool_decide (n ≤ N) then ε2 n else 0))%R).
       + intros n; split.
         * case_bool_decide; [|real_solver].
           apply Rmult_le_pos.
           ** real_solver.
           ** apply Rmin_glb; real_solver.
         * case_bool_decide.
           ** apply Rmult_le_compat_l; [real_solver|].
              apply Rmin_l.
           ** real_solver.
       + apply ex_seriesC_scal_l.
         apply ex_seriesC_nat_bounded.
     - rewrite SeriesC_scal_l.
       rewrite SeriesC_nat_bounded_to_foldr'.
       rewrite Rmult_comm.
       rewrite Rmult_div_assoc Rmult_1_r.
       apply Rcomplements.Rle_div_l; real_solver.
   }
   iIntros (n) "(%Hn & Herr)".
   iApply "HΦ".
   iSplit; auto.
   destruct (decide (1 <= F n)%R) as [HFn|HFn].
   + iExFalso.
     iApply (ec_contradict with "Herr"); auto.
   + iApply (ec_weaken with "Herr").
     split; auto.
     rewrite /F.
     rewrite /F in HFn.
     apply Rnot_le_gt, Rgt_lt in HFn.
     revert HFn.
     eapply (Rmin_case_strong); real_solver.
Qed.

(** The error induction rule *)

Lemma ec_induction (ε ε' : R) P :
    (0 < ε)%R →
    (ε < ε')%R →
    ((↯ ε' -∗ P) ∗ ↯ ε ⊢ P) ->
    (↯ ε ⊢ P).
Proof.
  iIntros (Hε Hε' IH1) "Herr".
  set (k := (ε'/ε)%R).
  iApply (ec_ind_simpl_external ε k); auto.
  {
    rewrite /k.
    rewrite -Rcomplements.Rlt_div_r; real_solver.
  }
  iIntros "(IH2 & Herr)".
  iApply IH1.
  iFrame.
  iIntros "Herr".
  iApply ("IH2" with "[Herr]").
  iApply (ec_eq with "Herr").
  rewrite /k.
  rewrite -Rmult_div_swap.
  rewrite Rmult_div_l; real_solver.
Qed.

(** Rules to obtain positive error credits *)

Lemma twp_err_pos e s E Φ :
  to_val e = None ->
  (∀ ε, ⌜ (0 < ε)%R ⌝ -∗ ↯ (ε) -∗ WP e @ s; E [{ Φ }] )
    ⊢ WP e @ s; E [{ Φ }].
Proof.
    iIntros (?) "?".
    iApply clutch.eris.error_rules.twp_err_pos; auto.
Qed.


Lemma wp_err_pos e E Φ :
  to_val e = None ->
  (∀ ε, ⌜ (0 < ε)%R ⌝ -∗ ↯ (ε) -∗ WP e @ E {{ Φ }} )
    ⊢ WP e @ E {{ Φ }}.
Proof.
  iIntros (?) "?".
  iApply clutch.eris.error_rules.wp_err_pos; auto.
Qed.

End rules.

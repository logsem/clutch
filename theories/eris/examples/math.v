Require Export clutch.eris.examples.math.axioms.
Require Export clutch.eris.examples.math.continuity2.
Require Export clutch.eris.examples.math.iverson.
Require Export clutch.eris.examples.math.integrals.
Require Export clutch.eris.examples.math.exp.
Require Export clutch.eris.examples.math.sets.
Require Export clutch.eris.examples.math.series.
Require Export clutch.eris.examples.math.limit_exchanges.
Require Export clutch.eris.examples.math.improper.
Require Export clutch.eris.examples.math.derived_fubini.
Require Export clutch.eris.examples.math.piecewise.


Require Import clutch.eris.examples.math.prelude.
From clutch.eris Require Import infinite_tape.
Import Hierarchy.
Set Default Proof Using "Type*".
#[local] Open Scope R.

(** Helper: Decompose RInt F 0 (S N) into sum of unit intervals *)
Lemma RInt_decompose_nat (F : R → R) (N : nat) :
  (∀ k : nat, (k <= N)%nat → ex_RInt F (INR k) (INR k + 1)) →
  ex_RInt F 0 (INR (S N)) →
  RInt F 0 (INR (S N)) = sum_n (fun k => RInt F (INR k) (INR k + 1)) N.
Proof.
  intros Hex_k Hex_total.
  induction N as [|N IH].
  { rewrite sum_O. simpl. f_equal. lra. }
  rewrite sum_Sn.
  rewrite -(RInt_Chasles F 0 (S N) (S (S N))).
  3: { apply Hex_k. lia. }
  - f_equal.
    apply IH.
    { intros k Hk. apply Hex_k. lia. }
    apply (ex_RInt_Chasles_1 F 0 (S N) (S (S N))).
    all: cycle 1.
    + exact Hex_total.
    + rewrite ?S_INR. split; try lra.
      apply Rplus_le_le_0_compat; try lra.
      apply pos_INR.
  - apply (ex_RInt_Chasles_1 F 0 (S N) (S (S N))).
    + rewrite ?S_INR. split; try lra.
      apply Rplus_le_le_0_compat; try lra.
      apply pos_INR.
    + exact Hex_total.
Qed.

(** Key lemma: If a function converges as x→∞, then the discrete sequence f(S n) also converges *)
Lemma continuous_to_discrete_limit {f : R → R} {L : R} :
  filterlim f (Rbar_locally Rbar.p_infty) (locally L) →
  filterlim (λ n : nat, f (INR (S n))) eventually (locally L).
Proof.
  intro Hcont.
  unfold filterlim in *.
  unfold filter_le in *.
  intros P HP.
  unfold filtermap in *.
  specialize (Hcont P HP).
  unfold Rbar_locally in Hcont.
  destruct Hcont as [M HM].
  unfold eventually.
  exists (Z.to_nat (up M)).
  intros n Hn.
  apply HM.
  have HupM : M < IZR (up M) by apply archimed.
  apply Rlt_le_trans with (r2 := IZR (up M)).
  { apply HupM. }
  destruct (Z_le_gt_dec 0 (up M)) as [Hpos | Hneg].
  { rewrite <-(Z2Nat.id (up M)); [|done]. rewrite <-INR_IZR_INZ. apply le_INR. lia. }
  { apply Rle_trans with (r2 := 0). { have : IZR (up M) < IZR 0 by (apply IZR_lt; lia). simpl in *. lra. } apply pos_INR. }
Qed.

(** Step 1: The improper integral equals the series of proper integrals over unit intervals *)
Lemma RInt_gen_as_series (F : R → R) :
  ex_RInt_gen F (at_point 0) (Rbar_locally Rbar.p_infty) →
  (∀ b : R, ex_RInt F 0 b) →
  (∀ k : nat, ex_RInt F (INR k) (INR k + 1)) →
  RInt_gen F (at_point 0) (Rbar_locally Rbar.p_infty) =
  SeriesC (fun k => RInt F (INR k) (INR k + 1)).
Proof.
  intros Hex_gen Hex_b Hex_k.
  rewrite (filterlim_RInt_gen Hex_b).
  symmetry.
  rewrite SeriesC_nat.
  apply Filterlim_Series.
  { unfold Lim_seq.ex_lim_seq.
    exists (Rbar.Finite (iota (λ IF : R, filterlim (λ b : R, RInt F 0 b) (Rbar_locally Rbar.p_infty) (locally IF)))).
    unfold Lim_seq.is_lim_seq.
    apply seq_lift.
    replace (@sum_n R_AbelianMonoid (fun k : nat => @RInt R_CompleteNormedModule F (INR k) (Rplus (INR k) (IZR (Zpos xH)))))
      with (λ M : nat, RInt F 0 (S M)).
    2: { apply functional_extensionality. intro M. symmetry.
         rewrite RInt_decompose_nat; try done. }
    have Hcont : filterlim (λ b : R, RInt F 0 b) (Rbar_locally Rbar.p_infty)
      (locally (iota (λ IF : R, filterlim (λ b : R, RInt F 0 b) (Rbar_locally Rbar.p_infty) (locally IF)))).
    { rewrite -(filterlim_RInt_gen Hex_b). apply filterlim_is_RInt_gen. { apply Hex_b. } apply RInt_gen_correct. apply Hex_gen. }
    apply (continuous_to_discrete_limit Hcont).
  }
  have Hcont : filterlim (λ b : R, RInt F 0 b) (Rbar_locally Rbar.p_infty)
    (locally (iota (λ IF : R, filterlim (λ b : R, RInt F 0 b) (Rbar_locally Rbar.p_infty) (locally IF)))).
  { rewrite -(filterlim_RInt_gen Hex_b). apply filterlim_is_RInt_gen. { apply Hex_b. } apply RInt_gen_correct. apply Hex_gen. }
  have Heq : (λ M : nat, sum_n (λ n : nat, RInt F n (n + 1)) M) = (λ M : nat, RInt F 0 (S M)).
  { apply functional_extensionality. intro M. symmetry. apply RInt_decompose_nat. { intros ??. apply Hex_k. } apply Hex_b. }
  rewrite Heq.
  apply (continuous_to_discrete_limit Hcont).
Qed.

(** Derivation lemmas for simplifying RInt_sep hypotheses *)

(** Hypothesis 3 is derivable from Hypothesis 2 *)
Lemma ex_RInt_unit_intervals_from_all (F : R → R) :
  (∀ b : R, ex_RInt F 0 b) →
  (∀ k : nat, ex_RInt F (INR k) (INR k + 1)).
Proof.
  intros Hex_b k.
  apply (ex_RInt_Chasles_2 F 0 k (k + 1)).
  { split. { apply pos_INR. } lra. }
  apply Hex_b.
Qed.

(** Hypothesis 4 is derivable from Hypothesis 3 *)
Lemma ex_RInt_shift_from_interval (F : R → R) :
  (∀ k : nat, ex_RInt F (INR k) (INR k + 1)) →
  (∀ k : nat, ex_RInt (fun x => F (x + INR k)) 0 1).
Proof.
  intros Hex_k k.
  have Hcomp := ex_RInt_comp_lin F 1 k 0 1.
  apply ex_RInt_ext with (f := (λ y : R, scal 1 (F (1 * y + k)))).
  { intros x Hx. rewrite /scal//=/mult//= Rmult_1_l. f_equal. lra. }
  apply Hcomp.
  have -> : 1 * 0 + k = k by lra.
  have -> : 1 * 1 + k = k + 1 by lra.
  apply Hex_k.
Qed.

(** Step 2 helper: Change of variables for translation *)
Lemma RInt_translation (F : R → R) (k : nat) :
  ex_RInt F (INR k) (INR k + 1) →
  ex_RInt (fun x => F (x + INR k)) 0 1 →
  RInt F (INR k) (INR k + 1) = RInt (fun x => F (x + INR k)) 0 1.
Proof.
  intros Hex_F Hex_shift.
  symmetry.
  have Hsimp : (λ x : R, F (x + k)) = λ y : R, scal 1 (F (1 * y + k)).
  { apply functional_extensionality.  intros x.
    rewrite /scal//=/mult//= Rmult_1_l.
    f_equal.
    lra.
  }
  rewrite Hsimp.
  rewrite (RInt_comp_lin F 1 k 0 1).
  { f_equal; lra. }
  have Heq : 1 * 0 + k = k by lra.
  have Heq2 : 1 * 1 + k = k + 1 by lra.
  rewrite Heq Heq2. apply Hex_F.
Qed.

Theorem RInt_sep (F : R → R) (UB : nat → R) :
  ex_RInt_gen F (at_point 0) (Rbar_locally Rbar.p_infty) →
  (∀ b : R, ex_RInt F 0 b) →
  ex_seriesC UB →
  (∀ x n, 0 < x < 1 → 0 <= F (x + INR n)) →
  (∀ x n, 0 < x < 1 → Rabs (F (x + INR n)) <= UB n) →
  RInt_gen F (at_point 0) (Rbar_locally Rbar.p_infty) =
  RInt (fun x => SeriesC (fun (k : nat) => F (x + k))) 0 1.
Proof.
  intros Hex_gen Hex_b HexU Hnn Hub.

  (* Derive the redundant hypotheses *)
  have Hex_k : ∀ k : nat, ex_RInt F (INR k) (INR k + 1).
  { apply ex_RInt_unit_intervals_from_all. apply Hex_b. }
  have Hex_shift : ∀ k : nat, ex_RInt (fun x => F (x + INR k)) 0 1.
  { apply ex_RInt_shift_from_interval. apply Hex_k. }

  (* Now proceed with the three-step proof *)
  rewrite (RInt_gen_as_series F Hex_gen Hex_b Hex_k).
  rewrite (SeriesC_ext _ (fun k => RInt (fun x => F (x + INR k)) 0 1)).
  2: { intro k. symmetry. rewrite RInt_translation; try done. }
  symmetry.
  rewrite (FubiniIntegralSeriesC_Strong UB); try done.
  lra.
Qed.

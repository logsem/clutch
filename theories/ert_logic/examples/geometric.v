(** * Simple Geometric Example *)
From clutch.prob_lang Require Import lang notation tactics metatheory.
From clutch.ert_logic Require Export expected_time_credits ert_weakestpre problang_wp proofmode
  derived_laws cost_models ert_rules.
From iris.proofmode Require Export proofmode.
From Coquelicot Require Export Hierarchy.

From Coq Require Export Reals Psatz.
Require Import Lra.

(* Simple example: Flip until heads, expectation should be constant *)

Definition geo
  := (rec: "g" "_" :=
        if: ((rand #1) = #0)%E
          then #()
          else ("g" #()))%V.

Section proofs.
  Context `{!ert_clutchGS Σ Costapp}.
  Lemma wp_geo E:
    {{{ ⧖ (2) }}}
      geo #()@E
      {{{RET #(); True}}}.
  Proof.
    iIntros (Φ) "Hx HΦ".
    iLöb as "IH" forall (Φ) "Hx HΦ".
    rewrite /geo. 
    wp_pures. simpl. replace (2-1) with 1; last (simpl;lra).
    wp_apply (wp_couple_rand_adv_comp' _ _ _ _ _
                (λ x, if (bool_decide (# (fin_to_nat x) = # 0))
                          then 0
                      else 2) with "[$]").
    - intros; case_bool_decide; lra.
    - simpl. rewrite SeriesC_finite_foldr.
      simpl. lra.
    - iIntros (n) "Hx". wp_pure.
      { case_bool_decide; lra. }
      case_bool_decide; simpl; wp_pure.
      + iModIntro. iApply "HΦ". done.
      + replace (2-_-_) with 2; last (simpl;lra). iApply ("IH" with "[$]"). done.
  Qed.
      
      
    
  
End proofs.

(* Defining these as paramaters until we decide what counts as a tick *)

(* Definition tc_val := (nnreal_nat 1). *)
(* Definition tc_recurse := (nnreal_nat 1). *)
(* Definition tc_sample := (nnreal_nat 1). *)
(* Definition tc_if := (nnreal_nat 1). *)

(* Definition tc_spec : nonnegreal := ((nnreal_nat 2) * tc_if + tc_val + tc_recurse)%NNR. *)

(* Definition tc_distr (s : fin 2) : nonnegreal *)
(*   := if fin_to_bool s *)
(*       then (tc_if + tc_val)%NNR *)
(*       else (tc_if + tc_recurse + tc_spec)%NNR. *)

(* Lemma tc_distr_mean : (SeriesC tc_distr) = nonneg ((nnreal_nat 2) * tc_spec)%NNR. *)
(* Proof. rewrite SeriesC_fin2 /=. lra. Qed. *)

(* Check ⧖ tc_spec -∗ (WP geo #() @ _ {{ fun _ => ⌜True ⌝ }})%I. *)

(* Proof:
    Use Lob induction.
    Start: ⧖ X
    - step (rand #1) with advanced composition on (⧖ X)
    amplify using X = (1/2) (tc_if + tc_val) + (1/2) (tc_if + tc_recurse + X)
    Case #0: ⧖ tc_if + tc_val
      - step if statement
      ⧖ tc_val
      - step return of a value
      ⧖ 0
    Case #1:
      ⧖ tc_if + tc_recurse + X
      - step if statement
      ⧖ tc_recurse + X
      - step to allow function application
      ⧖ X
      - Apply induction hypothesis

    Solving,
    X = (1/2) (tc_if + tc_val) + (1/2) (tc_if + tc_recurse + X)
    2X = (tc_if + tc_val) + (tc_if + tc_recurse + X)
    X = tc_if + tc_val + tc_if + tc_recurse
 *)

From Coq Require Export Reals Psatz.
From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Export fancy_updates.
From iris.algebra Require Import big_op.
From iris.bi Require Export weakestpre fixpoint big_op.
From iris.prelude Require Import options.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Export ghost_map.

From self.prob Require Export couplings distribution.
From self.program_logic Require Export language exec weakestpre.
From self.prob_lang Require Export lang.
From self.prob_lang Require Export class_instances spec_ra.
From self.prob_lang Require Import tactics notation.

Import uPred.

Local Open Scope R.

Section helper_lemma.

  Context `{!irisGS prob_lang Σ}.

  Definition pure_eq (ρ1 ρ2 : cfg) := (ρ1.1 = ρ2.1) /\ (ρ1.2.(heap) = ρ2.2.(heap)).

  Lemma foo_helper_1 (m : nat) (e1 : expr) (σ1 : state) (e1' : expr) (σ1' : state) (R: cfg -> cfg -> Prop):
    Rcoupl (prim_step e1 σ1) (prim_step e1' σ1') R ->
    (forall ρ2 ρ2', R ρ2 ρ2' -> ∃ n : nat, refRcoupl (prim_exec ρ2 m) (prim_exec ρ2' n) pure_eq)
    -> ∃ n : nat, refRcoupl (prim_exec (e1, σ1) (S m)) (prim_exec (e1', σ1') n) pure_eq.
  Proof.
    intros (μ & ((HμL & HμR) & HμSupp)) Hcont.
    assert (exists n, ∀ ρ2 ρ2' : cfg, μ (ρ2, ρ2') > 0 → refRcoupl (prim_exec ρ2 m) (prim_exec ρ2' n) pure_eq) as (n & Hn).
    (* Somehow use finiteness of the support? *)
    { admit. }
    exists (S n).
    rewrite /prim_exec /=.
    case_match; case_match.
    + specialize (Hn (e1, σ1) (e1', σ1')).
      assert (μ (e1, σ1, (e1', σ1')) > 0) as Haux; [admit | ].
      specialize (Hn Haux).
      destruct m; destruct n;
      rewrite /prim_exec in Hn.
  Admitted.

  Lemma foo (e1 : expr) (σ1 : state) (e1' : expr) (σ1' : state) (m : nat) :
    exec_coupl e1 σ1 e1' σ1'
               (λ '(e2, σ2) '(e2', σ2'), ∃ n, ⌜refRcoupl (prim_exec (e2, σ2) m) (prim_exec (e2', σ2') n) pure_eq⌝)%I ⊢@{iProp Σ}
    (∃ n, ⌜refRcoupl (prim_exec (e1, σ1) (S m) ) (prim_exec (e1', σ1') n) pure_eq⌝).
  Proof.
    rewrite /exec_coupl /exec_coupl'.
    iPoseProof (least_fixpoint_iter
                  (exec_coupl_pre
                     (λ '(e2, σ2) '(e2', σ2'), ∃ n : nat, ⌜refRcoupl (prim_exec (e2, σ2) m) (prim_exec (e2', σ2') n) pure_eq⌝)%I)
                  (λ '((e1, σ1), (e1', σ1')), ∃ n : nat, ⌜refRcoupl (prim_exec (e1, σ1) (S m)) (prim_exec (e1', σ1') n) pure_eq⌝)%I) as "H".
    iIntros "Hbi".
    iSpecialize ("H" with "[]").
    + iModIntro. iIntros ((ρ2&ρ2')).
      destruct ρ2 as (e2, σ2).
      destruct ρ2' as (e2', σ2').
      rewrite /exec_coupl_pre.
      iIntros "[Hpp| [Hpr| [Hrp| Hss]]]".
      ++ iDestruct "Hpp" as (R2 HR2) "Hpp".
         destruct HR2 as (μ & ((HμL & HμR) & HμSupp)).
Admitted.


End helper_lemma.


Theorem wp_adequacy `{!invGpreS Σ} e σ e' σ' n s :
  (∀ `{Hinv : invG Σ},
     (|={⊤}=>
        state_interp σ ∗ spec_interp_auth (e', σ') ∗
        WP e @ s; ⊤ {{ v, ⤇ v }})%I) →
  ∃ m, refRcoupl (prim_exec (e, σ) n) (prim_exec (e', σ') m) pure_eq.

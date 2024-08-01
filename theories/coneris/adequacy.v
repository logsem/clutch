From iris.proofmode Require Import base proofmode.
From iris.bi Require Export weakestpre fixpoint big_op.
From iris.base_logic.lib Require Import ghost_map invariants fancy_updates.
From iris.algebra Require Import excl.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.con_prob_lang Require Import erasure notation.
From clutch.common Require Export con_language sch_erasable.
From clutch.base_logic Require Import error_credits.
From clutch.coneris Require Import weakestpre primitive_laws.
From clutch.prob Require Import distribution.
Import uPred.

Notation con_prob_lang_mdp := (con_lang_mdp con_prob_lang).

Section adequacy.
  Context `{!conerisGS Σ}.
End adequacy.

Class conerisGpreS Σ := ConerisGpreS {
  conerisGpreS_iris  :: invGpreS Σ;
  conerisGpreS_heap  :: ghost_mapG Σ loc val;
  conerisGpreS_tapes :: ghost_mapG Σ loc tape;
  conerisGpreS_err   :: ecGpreS Σ;
}.

Definition conerisΣ : gFunctors :=
  #[invΣ; ghost_mapΣ loc val;
    ghost_mapΣ loc tape;
    GFunctor (authR nonnegrealUR)].
Global Instance subG_conerisGPreS {Σ} : subG conerisΣ Σ → conerisGpreS Σ.
Proof. solve_inG. Qed.

Theorem wp_pgl Σ `{conerisGpreS Σ} `{Countable sch_int_state} (ζ : sch_int_state) n
  (e : expr) (σ : state) (ε : R) (sch: scheduler con_prob_lang_mdp sch_int_state) φ :
  0 <= ε →
  (∀ `{conerisGS Σ}, ⊢ ↯ ε -∗ WP e {{ v, ⌜φ v⌝ }}) →
  pgl (sch_exec sch n (ζ, ([e], σ))) φ ε.
Proof.
Admitted.

Lemma pgl_closed_lim `{Countable sch_int_state} (ζ : sch_int_state) (e : expr) (σ : state) (ε : R)
  (sch: scheduler con_prob_lang_mdp sch_int_state) φ :
  (∀ n, pgl (sch_exec sch n (ζ, ([e], σ))) φ ε) →
  pgl (sch_lim_exec sch (ζ, ([e], σ))) φ ε .
Proof. intros Hn. by apply sch_lim_exec_continuous_prob. Qed.

Theorem wp_pgl_lim Σ `{conerisGpreS Σ} `{Countable sch_int_state} (ζ : sch_int_state)
  (e : expr) (σ : state) (ε : R) (sch: scheduler con_prob_lang_mdp sch_int_state) φ :
  0 <= ε →
  (∀ `{conerisGS Σ}, ⊢ ↯ ε -∗ WP e {{ v, ⌜φ v⌝ }}) →
  pgl (sch_lim_exec sch (ζ, ([e], σ))) φ ε.
Proof.
  intros.
  apply pgl_closed_lim.
  intros.
  by eapply wp_pgl.
Qed.

(* TODO limit stronger adequacy*)

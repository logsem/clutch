(** * Batch Sampling *)
From clutch.ert_logic Require Export expected_time_credits ert_weakestpre problang_wp proofmode
  derived_laws cost_models ert_rules.
From clutch.prob_lang Require Import notation tactics metatheory lang.
From iris.proofmode Require Export proofmode.
From Coq Require Export Reals Psatz.
From Coquelicot Require Export Hierarchy.
Require Import Lra.

Set Default Proof Using "Type*".

Definition sample
  := (rec: "g" "_" :=
        let: "result" := (rand #1) + #2 * (rand #1) in
        if: ("result" < #3)%E
          then "result"
        else ("g" #()))%V.

Section proof1.
  Context `{!ert_clutchGS Σ CostRand}.
  Lemma wp_geo E:
    {{{ ⧖ (8/3) }}}
      sample #()@E
      {{{RET #(); True}}}.
  Proof.
    iIntros (Φ) "Hx HΦ".
    iLöb as "IH" forall (Φ) "Hx HΦ".
    rewrite /sample.
    wp_pures. simpl.
    wp_apply (wp_couple_rand_adv_comp with "[Hx]").
  Admitted.
    
End proof1.

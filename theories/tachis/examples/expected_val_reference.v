From clutch.prob_lang Require Import lang notation tactics metatheory.
From clutch.tachis Require Export adequacy expected_time_credits ert_weakestpre problang_wp proofmode
  derived_laws cost_models ert_rules.
From iris.proofmode Require Export proofmode.
From Coquelicot Require Import Rbar.
Set Default Proof Using "Type*".
Open Scope R.

(** * Lohse & Garg 2024, Section 7 *)
Section loc_cost.

  Definition toss l : expr := if: rand #1 = #1 then #()
                              else l <- !l + #1.

  Lemma wp_op_ert `{!tachisGS Σ CostTick} :
    {{{ ⧖ (1/2) }}}
      let: "l" := ref #0 in toss "l";; tick (! "l")
    {{{ RET #(); True }}}.
  Proof with (try iIntros ; wp_pures).
    iIntros (Φ) "n HΦ".
    wp_alloc...
    iSpecialize ("HΦ" $! I).
    wp_apply (wp_couple_rand_adv_comp' _ _ _ _ _
                (λ x, if bool_decide (x = 1%fin) then 0 else 1)%R with "n").
    1: intros ; case_bool_decide ; lra.
    1: { rewrite SeriesC_finite_foldr /=. lra. }
    repeat (try iIntros (n) ; inv_fin n)...
    - wp_load... wp_store... wp_load ; iIntros. by wp_pure_cost.
    - wp_load ; iIntros. by wp_pure_cost.
  Qed.

End loc_cost.

Fact op_ert : ∀ σ,
    @lim_ERT CostTick ((let: "l" := ref #0 in toss "l";; tick (! "l"))%E, σ) <= (1/2)%NNR.
Proof.
  intros.
  eapply (wp_ERT_lim CostTick tachisΣ _ _ _ (λ _, True)).
  iIntros (?) "tc". by iApply (wp_op_ert with "[$tc]").
Qed.

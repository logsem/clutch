(** * Coupling rules  *)
From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext fin tactics.
From clutch.common Require Import con_language con_ectx_language con_ectxi_language.
From clutch.foxtrot Require Import lifting ectx_lifting.
From clutch.con_prob_lang Require Import lang notation tactics metatheory erasure.
From clutch.foxtrot Require Export primitive_laws oscheduler full_info proofmode.

Section rules.
  Context `{!foxtrotGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types v : val.
  Implicit Types l : loc.

  #[local] Open Scope R.

  (** spec [rand] *)
  (** TODO make more general rules when needed*)
  Lemma tp_rand_r_err N z E K j m:
    TCEq N (Z.to_nat z) →
    j ⤇ fill K (rand #z) -∗
    ↯ (/ (N + 1)%nat)-∗
    pupd E E (∃ n, ⌜(n<=N)%nat⌝ ∗ ⌜n≠m⌝ ∗ j ⤇ fill K #n).
  Proof.
    iIntros (Heq) "Hspec Herr".
    rewrite pupd_unseal/pupd_def.
    iIntros (σ1 [] ε1) "(H1 & H2 & H3)".
    iDestruct (spec_auth_prog_agree with "[$][$]") as "%".
    iDestruct (ec_supply_ec_inv with "[$][$]") as %(x&x'& -> & He).
    iApply fupd_mask_intro; first set_solver.
    assert (0 <= / (N + 1)%nat).
    { rewrite -Rdiv_1_l.
      apply Rdiv_INR_ge_0.
    }
    iIntros "Hclose".
    iApply spec_coupl_step_r; [|done|..].
    - apply reducible_fill. apply head_prim_reducible. solve_red.
    - simpl; done. 
    - simpl.
      rewrite fill_dmap //=.
      rewrite head_prim_step_eq//.
      simpl.
      rewrite -Heq.
      rewrite dmap_comp.
      rewrite /dmap.
      rewrite He.
      replace (/ _) with ((/ (N+1)%nat) + 0)%R; last (simpl; lra).
      eapply pgl_dbind; last first.
      + rewrite -Rdiv_1_l. replace (INR _) with (INR N + 1)%R; first apply (ub_unif_err_nat _ m).
        by rewrite plus_INR. 
      + simpl. intros a ?. apply pgl_dret; split; last done.
        instantiate (1:=λ x, ∃ (m':nat), x= (fill K #m', s, []) /\ m'≠m/\m' ≤ N).
        eexists _. repeat split; try done.
        pose proof fin_to_nat_lt a. lia.
      + done.
      + done. 
    - iIntros (???) "%".
      destruct!/=.
      iMod (ec_supply_decrease with "[$][$]") as (????) "Hdec".
      iMod (spec_update_prog with "[$][$]") as "[HK Hs]".
      iModIntro.
      iApply spec_coupl_ret.
      iMod "Hclose".
      iModIntro.
      iFrame.
      rewrite app_nil_r. iFrame.
      iSplit; try done.
      iApply ec_supply_eq; [|done].
      simplify_eq. lra.
  Qed. 
End rules.

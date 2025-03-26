From clutch.eris Require Import eris.
From clutch.eris.lib.sampling Require Import utils.
From clutch.eris.lib.sampling Require Import bernoulli.
#[local] Open Scope R.

Section Geometric.
  #[local] Ltac done ::= 
    solve[lia || lra || nra || real_solver || tactics.done || auto].

  Context `{!erisGS Σ}.
  Definition geometric : val :=
    rec: "geometric" "N" "M" :=
    if: bernoulli "N" "M" = #1 then #0 else 
    #1 + "geometric" "N" "M"
  .
  
  Lemma geometric_spec (N M k : nat) (Hlt : (N <= M)%nat) (p := N / (S M)) :
  [[{↯ (1 - (((1 - p)^k) * p))%R }]]
    geometric #N #M
  [[{RET #k; True}]].
  Proof.
    assert (0 <= p <= 1)%R as Hp. {
      split; subst p; simpl_expr.
    }
    induction k.
    - iIntros "%Φ Herr HΦ".
      rewrite /geometric Rmult_1_l.
      wp_pures.
      wp_apply (bernoulli_success_spec_simple with "Herr") as "%v ->".
      wp_pures.
      by iApply "HΦ".
    - iIntros "%Φ Herr HΦ".
      rewrite /geometric.
      wp_pures.
      fold geometric.
      replace (1 - (1 - p)^(S k) * p) with ((1 - p) * (1 - (1 - p)^k * p) + p) by rewrite //=.
      wp_apply (twp_bernoulli_scale _ _ _ (1 - (1 - p) ^ k * p) 1 with "Herr") as "%n [[-> Herr] | [-> Herr]]";
      fold p; try done; last solve[cred_contra].
      { apply error_credits.Rle_0_le_minus.
        assert (0 <= ((1 - p) ^ k) <= 1)%R. {
          apply Rpow_le_1; lra.
        }
        by apply Rmult_le_1. }
      wp_pures.
      wp_apply (IHk with "Herr") as "_".
      wp_pures.
      rewrite Z.add_1_l -Nat2Z.inj_succ.
      by iApply "HΦ".
  Qed.

End Geometric.

From clutch.eris Require Import eris.
From clutch.eris.lib.sampling Require Import utils.
From clutch.eris.lib.sampling Require Import bernoulli.
Local Open Scope R.



Section Geometric.
  Local Ltac done ::= 
  lia || lra || nra || real_solver || tactics.done || auto.

  Context `{!erisGS Σ}.
  Definition geometric : val :=
    rec: "geometric" "N" "M" :=
    if: bernoulli "N" "M" = #1 then #0 else 
    #1 + "geometric" "N" "M"
  .
About twp_rand_err_amp.
  Lemma geometric_spec (N M k : nat) (Hlt : (N <= M)%nat) (p := N / (S M)) :
  [[{↯ (1 - (((1 - p)^k) * p))%R }]]
    geometric #N #M
  [[{RET #k; True}]].
  Proof.
    (* move=> p.
    set (p := ((INR N) / (INR (S M)))%R).
    assert (0 <= p <= 1)%R as Hp. {
      split; subst p; simpl_expr.
    }
    induction k.
    - iIntros "%Φ Herr HΦ".
      rewrite /geometric Rmult_1_l.
      wp_pures.
      wp_apply (bernoulli_succes_spec with "Herr") as "%v ->".
      wp_pures.
      by iApply "HΦ".
    - iIntros "%Φ Herr HΦ".
      rewrite /geometric.
      wp_pures.
      fold geometric.
      simpl pow.
      iPoseProof (ec_split ((1 - (1 - p) * (1 - p) ^ k * p) - p) p with "[Herr]")%R as "[Herr Herr']".
      { rewrite -Rminus_plus_distr.
        apply error_credits.Rle_0_le_minus, Rcomplements.Rle_minus_r.
        rewrite -{3}(Rmult_1_r (1 - p)) Rmult_assoc.
        simpl_expr.
        assert (0 <= ((1 - p) ^ k) <= 1)%R. {
          apply Rpow_le_1; lra.
        }
        by apply Rmult_le_1. }
      { lra. }
      { iApply (ec_eq with "Herr") => //. }
      wp_apply (bernoulli_failure_spec with "Herr'") as "%v ->"; wp_pures.
      wp_bind (geometric _ _).
      iApply (IHk with "[Herr]").
      { (* Difficult to prove given that it's false *)
        admit. }
      iIntros "_".
      wp_pures.
      rewrite /= Z.add_1_l -Nat2Z.inj_succ.
      by iApply "HΦ". *)
  Abort.


End Geometric.
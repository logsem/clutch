From iris.base_logic.lib Require Import fancy_updates.
From clutch.common Require Import inject.
From clutch.prob_lang Require Export lang notation gwp.gen_weakestpre.

Module Arith.
  
Definition max : val :=
  λ: "n" "m",
    if: "m" ≤ "n" then "n" else "m".

Definition min : val :=
  λ: "n" "m",
    if: "n" ≤ "m" then "n" else "m".

End Arith. 

#[local] Open Scope Z.

Section Z_theory.
  Context `{invGS_gen hlc Σ} (g : GenWp Σ).

  Lemma gwp_max (z1 z2 : Z) Φ E :
    Φ #(z1 `max` z2) -∗
    GWP Arith.max #z1 #z2 @ g ; E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    gwp_rec. gwp_pures.
    case_bool_decide; simplify_eq; gwp_pures.
    - rewrite Z.max_l //.
    - rewrite Z.max_r //. lia.
  Qed.

  Lemma gwp_min (z1 z2 : Z) E Φ :
    Φ #(z1 `min` z2) -∗
    GWP Arith.min #z1 #z2 @ g ; E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    gwp_rec. gwp_pures.
    case_bool_decide; simplify_eq; gwp_pures.
    - rewrite Z.min_l //.
    - rewrite Z.min_r //. lia.
  Qed.

End Z_theory.

From clutch.foxtrot Require Import foxtrot nodet diverge.

Definition prog : expr :=
  let: "n" := nodet #() in
  if: rand "n"=#0
  then diverge #()
  else #().


Lemma prog_refines_unit :
  ∅ ⊨ prog ≤ctx≤ #() : TUnit.
Proof.
  apply (refines_sound foxtrotRΣ).
  iIntros (??).
  unfold_rel.
  iIntros (K j) "Hspec".
  rewrite /prog.
  wp_apply (wp_nodet); first done.
  iIntros (?) "_".
  wp_pures.
  wp_apply wp_rand; first done.
  iIntros.
  wp_pures.
  case_bool_decide.
  - wp_pures. wp_apply (wp_diverge); first done.
    by iIntros.
  - wp_pure. by iFrame.
Qed.

Lemma unit_refines_prog :
  ∅ ⊨ #() ≤ctx≤ prog : TUnit.
Proof.
  apply (refines_sound foxtrotRΣ).
  iIntros (??).
  unfold_rel.
  iIntros (K j) "Hspec".
  rewrite /prog.
  iMod (pupd_epsilon_err) as "(%ε & %Hpos &Herr)".
  apply archimed_cor1 in Hpos as (N&Hineq&Hpos').
  assert (/(S N)< ε)%R as Hineq'.
  { etrans; last exact.
    apply Rinv_0_lt_contravar.
    - by apply lt_0_INR.
    - apply lt_INR. lia.
  }
  iDestruct (ec_weaken with "[$]") as "Herr".
  { split; last (left; apply Hineq').
    rewrite -Rdiv_1_l.
    apply Rdiv_INR_ge_0.
  }
  tp_bind j (nodet #()).
  iMod (tp_nodet _ _ _ N with "[$]") as "Hspec".
  Local Opaque INR.
  simpl.
  tp_pures j.
  tp_bind j (rand _)%E.
  iMod (tp_rand_r_err _ _ _ _ _ 0 with "[$][Herr]") as "(%&%&%&Hspec)".
  { iApply ec_eq; last done.
    by rewrite S_INR plus_INR.
  }
  simpl.
  tp_pures j.
  - solve_vals_compare_safe.
  - rewrite bool_decide_eq_false_2; last first.
    { intros ?. simplify_eq. lia. }
    tp_pures j.
    wp_pures.
    by iFrame.
Qed.   

Lemma prog_eq_unit :
  ∅ ⊨ prog =ctx= #() : TUnit.
Proof.
  split; [apply prog_refines_unit|apply unit_refines_prog].
Qed. 
  
  



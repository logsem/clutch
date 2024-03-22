From clutch.prob_lang Require Import lang notation tactics metatheory.
From clutch.ert_logic Require Export expected_time_credits ert_weakestpre problang_wp proofmode
  derived_laws cost_models ert_rules.
From iris.proofmode Require Export proofmode.
Set Default Proof Using "Type*".

(* TODO: move *)
Lemma Rmult_pos_nat r (n : nat) :
  (0 <= r)%R →
  (0 <= r * n)%R.
Proof. intros. eapply Rmult_le_pos; [done|]. apply pos_INR. Qed.

Hint Resolve Rmult_pos_nat : real.

#[local] Notation "'while' e1 'do' e2 'end'" :=
  ((rec: "loop" <> := (if: e1 then e2 ;; "loop" #() else #()))%V #())%E
    (e1, e2 at level 200) : expr_scope.

(** [Kaminski 2019, Section 7.1]  *)
(** while ( x > 0 ) { { x := x − 1 } [1/2] { skip } } *)
Definition loop1 (l : loc) : expr :=
  while (#0 < !#l) do
    if: rand #1 = #0 then
      #l <- !#l - #1
    else #()
  end.

Section loop1.
  Context `{!ert_clutchGS Σ Cost1}.

  Lemma wp_loop1 (l : loc) (n : nat) :
    {{{ ⧖ (4 + 21 * n) ∗ l ↦ #n }}}
      loop1 l
    {{{ RET #(); True }}}.
  Proof.
    iLöb as "IH" forall (n).
    iIntros (Ψ) "[Hc Hl] HΨ".
    rewrite {2}/loop1.
    iDestruct (etc_split with "Hc") as "[Hc Hn]";
      eauto with real.
    wp_pure with "Hc".
    iChip "Hc" as "H1".
    wp_apply (wp_load with "[H1 $Hl]").
    { rewrite bool_decide_eq_false_2 //=. }
    iIntros "Hl".
    wp_pure with "Hc".
    case_bool_decide as Hlt;
      wp_pure with "Hc"; last first.
    { by iApply "HΨ". }
    iClear "Hc".
    destruct n.
    { rewrite Nat2Z.inj_0 // in Hlt. }
    rewrite !S_INR.
    wp_apply (wp_couple_rand_adv_comp' _ _ _ _ _
                (λ x, if bool_decide (x = 0%fin)
                      then 11 + 21 * n
                      else 8  + 21 * (n + 1))%R with "Hn").
    { intros x. case_bool_decide.
      - assert (0 <= 21 * n)%R; [|lra]. eauto with real.
      - assert (0 <= 21 * (n + 1))%R; [|lra].
        eapply Rmult_le_pos; eauto with real. }
    { rewrite [cost _]/= !S_INR SeriesC_finite_foldr /=. lra. }
    iIntros (b) "Hc".
    inv_fin b; [|intros b].
    - rewrite bool_decide_eq_true_2 //.
      assert (11 + 21 * n = 7 + (4 + 21 * n))%R as -> by lra.
      iDestruct (etc_split with "Hc") as "[Hc Hn]"; [lra| |].
      { assert (0 <= 15 * n)%R; [|lra]. eauto with real. }
      wp_pure with "Hc".
      wp_pure with "Hc".
      iChip "Hc" as "H1".
      wp_apply (wp_load with "[H1 $Hl]").
      { rewrite bool_decide_eq_false_2 //=. }
      iIntros "Hl".
      wp_pure with "Hc".
      iChip "Hc" as "H1".
      wp_apply (wp_store with "[H1 $Hl]").
      { rewrite bool_decide_eq_false_2 //=. }
      iIntros "Hl".
      wp_pure with "Hc".
      replace #(S n - 1) with #n by (do 3 f_equal; lia).
      wp_pure with "Hc".
      wp_apply ("IH" with "[$Hn $Hl] HΨ").
    - rewrite /=.
      assert (8 + 21 * (n + 1) = 4 + (4 + 21 * (n + 1)))%R as -> by lra.
      iDestruct (etc_split with "Hc") as "[Hc Hn]"; [lra| |].
      { assert (0 <= 21 * n)%R; [|lra]. eauto with real. }
      wp_pures with "Hc".
      rewrite -Nat.add_1_r.
      iApply ("IH" $! (n + 1) with "[Hn $Hl] HΨ").
      iApply (etc_irrel with "Hn").
      rewrite plus_INR INR_1 //.
  Qed.

End loop1.

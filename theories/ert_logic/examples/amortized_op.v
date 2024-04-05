From tachis.prob_lang Require Import lang notation tactics metatheory.
From tachis.ert_logic Require Export expected_time_credits ert_weakestpre problang_wp proofmode
  derived_laws cost_models ert_rules.
From iris.proofmode Require Export proofmode.
Set Default Proof Using "Type*".

#[local] Notation "'[['  e1  ']]'  '[1/2]'  '[['  e2  ']]'" :=
  (if: rand #1 = #0 then e1 else e2)%E
    (e1, e2 at level 200) : expr_scope.

(** * Batz. et al 2023 (POPL 2023), Example 5.7 *)
Section op.

  Variable (l : loc).

  Definition op : expr :=
    [[ tick (! #l) ]] [1/2] [[ #l <- #0 ]];;
    #l <- !#l + #1.

  Context `{!ert_tachisGS Σ CostTick}.

  (** The ERT is fairly easy to determine as [n / 2] *)
  Lemma wp_op_ert (n : nat) :
    {{{ ⧖ (n / 2) ∗ l ↦ #n }}}
      op
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Ψ) "[Hc Hl] HΨ". rewrite /op.
    wp_apply (wp_couple_rand_adv_comp' _ _ _ _ _
                (λ x, if bool_decide (x = 0%fin)
                      then n else 0)%R with "Hc").
    { intros. case_bool_decide; eauto with real. }
    { rewrite SeriesC_finite_foldr /=. lra. }
    iIntros (b) "Hc".
    wp_pure.
    inv_fin b; [|intros b]; simpl.
    - wp_pures.
      wp_load; iIntros "Hl".
      wp_pure_cost.
      { rewrite Nat2Z.id //. }
      wp_pures.
      wp_load; iIntros "Hl".
      wp_pures.
      wp_store; iIntros "Hl".
      by iApply "HΨ".
    - wp_pures.
      wp_store; iIntros "Hl".
      wp_pures.
      wp_load; iIntros "Hl".
      wp_pures.
      wp_store; iIntros "Hl".
      by iApply "HΨ".
  Qed.

  (** However (as discussed in the paper), obtaining the ERT of repeated invocations of [op] solely
      using their ERT calculus would have been hard. For example,

        [op;; op]

      has ERT [3n / 4 + 1 / 4] and

        [op;; op;; op]

      has ERT [7n / 8 + 5 / 8] and so on. The pattern is not very obvious. Instead, the paper
      develops an amortized ERT predicate which is annotated with a potential function [π]. Using
      this, they show that [op] has *amortized* constant cost [1] and thus [op^n] has cost [n].

      Using time credits we can do this amortized reasoning for free! *)
  Definition π : iProp Σ := ∃ (n : nat), l ↦ #n ∗ ⧖ n.

  Lemma wp_op_aert :
    {{{ ⧖ 1 ∗ π }}}
      op
    {{{ RET #(); π }}}.
  Proof.
    iIntros (Ψ) "(Hc & (%n & Hl & Hn)) HΨ". rewrite /op.
    iCombine "Hn Hc" as "Hc".
    assert (0 <= n)%R by eauto with real.
    wp_apply (wp_couple_rand_adv_comp' _ _ _ _ _
                (λ x, if bool_decide (x = 0%fin)
                      then 2 * n + 1
                      else 1)%R with "Hc").
    { intros. case_bool_decide; lra. }
    { rewrite SeriesC_finite_foldr /=. lra. }
    iIntros (b) "Hc".
    wp_pure.
    inv_fin b; [|intros b]; simpl.
    - wp_pures.
      wp_load; iIntros "Hl".
      wp_pure_cost; rewrite Nat2Z.id; [lra|].
      wp_pures.
      wp_load; iIntros "Hl".
      wp_pures.
      wp_store; iIntros "Hl".
      iApply "HΨ".
      iExists (n + 1).
      rewrite Nat2Z.inj_add // plus_INR INR_1.
      iFrame.
      iApply (etc_irrel with "Hc"); lra.
    - wp_pures.
      wp_store; iIntros "Hl".
      wp_pures.
      wp_load; iIntros "Hl".
      wp_pures.
      wp_store; iIntros "Hl".
      iApply "HΨ".
      iExists 1. iFrame.
  Qed.

  (** Using the amortized spec for [op], it's straightforwad to show a specification for [n]
      invocations of [op] *)

  Definition repeat_n : val :=
    rec: "repeat" "n" "f" :=
      if: "n" = #0 then #() else "f" "n";; "repeat" ("n" - #1) "f".

  Lemma wp_repeat_n (P : nat → iProp Σ) (f : val) (n : nat) :
    (∀ (m : nat),
        {{{ P (S m) }}}
          f #(S m)
       {{{ RET #(); P m }}}) -∗
    {{{ P n }}}
      repeat_n #n f
    {{{ RET #(); P 0 }}}.
  Proof.
    iIntros "#Hf".
    iInduction n as [|n] "IH"; iIntros (Ψ) "!# HP HΨ".
    { wp_rec. wp_pures. by iApply ("HΨ" with "[$HP]"). }
    wp_rec; wp_pures.
    wp_apply ("Hf" with "HP").
    iIntros "HP".
    wp_pures.
    replace #(S n - 1) with #n by (do 2 f_equal; lia).
    by wp_apply ("IH" with "HP").
  Qed.

  (** If [l] is [m] then the ERT of [n] repetitions of [op] is [n + m] *)
  Lemma wp_op_n_aert (n m : nat) :
    {{{ ⧖ (n + m) ∗ l ↦ #m }}}
      repeat_n #n (λ: <>, op)%V
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Ψ) "[Hc Hl] HΨ".
    iDestruct (etc_split with "Hc") as "[Hn Hm]";
      eauto with real.
    iAssert π with "[Hl Hm]" as "Hπ".
    { iExists m. iFrame. }
    wp_apply (wp_repeat_n (λ n, π ∗ ⧖ n)%I
               with "[] [$Hn $Hπ]"); last first; clear.
    { iIntros. by iApply "HΨ". }
    iIntros (m Ψ) "!# [Hπ Hm] HΨ".
    iDestruct (etc_nat_Sn with "Hm") as "[H1 Hm]".
    wp_pures.
    wp_apply (wp_op_aert with "[$Hπ $H1]").
    iIntros "Hπ".
    iApply "HΨ".
    iFrame.
  Qed.

End op.

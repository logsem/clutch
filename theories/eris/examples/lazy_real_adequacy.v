From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt RInt_analysis AutoDerive RInt_gen.
From clutch.eris Require Import infinite_tape.
From clutch.eris.examples Require Import lazy_real max_lazy_real real_decr_trial.
From clutch.eris.examples Require Import math.
Import Hierarchy.
Set Default Proof Using "Type*".
#[local] Open Scope R.

(* We prove the simple adequacy statement of samplers e that returns a distribution of lazy reals *)
(* we compare to see whether the lazy real <= (x)/(2^y) *)
(* We have the inequality (x)<2^y *)
Definition pow2 : val :=
  rec: "pow2" "y":=
    if: "y"≤#0%nat then #(1%nat) else #2 * ("pow2" ("y"-#1)).

Definition is_zero : val :=
  (rec: "f" "α" "l" :=
     let, ("z", "l'") := get_chunk "α" "l" in
     if: "z" = #0 then "f" "α" "l'" else #false)%V.

Definition is_smaller_prog_aux : val :=
  (rec: "f" "α" "l" "x" "y" :=
     if: "y"=#0 then is_zero "α" "l"
     else
       let, ("z", "l'") := get_chunk "α" "l" in
       let: "y'" := "y" - #1 in 
       let: "p" := pow2 "y'" in
       if: "x"<"p"
       then (* first digit of (x)/(2^y) is 0*)
         if: "z"=#1 then #false
         else "f" "α" "l'" "x" "y'"
       else (* first digit of (x)/(2^y) is 1*)
         if: "z"=#0 then #true
         else "f" "α" "l'" ("x"-"p") "y'"
  )%V.

Definition is_smaller_prog : val :=
  λ: "l" "x" "y",
    let, ("α", "l'") := "l" in is_smaller_prog_aux "f" "x" "y" "α" "l'"
.

Local Lemma ineq_lemma (x y:nat): (x<2^y)%nat -> 0<=(x/2^y)%nat <=1.
Proof.
  replace 1 with (INR 1) by done. replace 0 with (INR 0) by done. split.
    - apply le_INR. lia. 
    - apply le_INR. apply Nat.Div0.div_le_upper_bound. lia.
Qed.

Section adequacy.
  Context `{!erisGS Σ}.
  
  Lemma wp_pow2 (n:nat):
    {{{ True }}}
      pow2 #n
      {{{(x:nat), RET (#x); ⌜x = (2^n)%nat⌝ }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    iLöb as "IH" forall (Φ n).
    rewrite /pow2.
    wp_pures. rewrite -/pow2.
    case_bool_decide; wp_pures.
    - iModIntro. iApply "HΦ".
      assert (n = 0)%nat by lia.
      simplify_eq. done.
    - replace (Z.of_nat n - 1)%Z with (Z.of_nat (n-1)); last first.
      + rewrite Nat2Z.inj_sub; first lia.
        destruct n; last lia. done.
      + wp_apply ("IH").
        iIntros (x) "%".
        wp_pures.
        iModIntro.
        replace (_*_)%Z with (Z.of_nat (2*x)); last first.
        * rewrite Nat2Z.inj_mul. f_equal.
        * iApply "HΦ". iPureIntro. subst.
          rewrite -PeanoNat.Nat.pow_succ_r'. f_equal.
          destruct n; try done. lia.
  Qed.

  Lemma wp_e x y μ e:
    (∀ x, 0<=μ x)->
    ex_RInt μ 0 1 ->
    (x<2^y)%nat ->
    (∀ (F : R -> R), (⌜∃ M, ∀ x , 0 <= F x <= M⌝) -∗
       ↯ (RInt (fun (x:R) => μ x * F x) 0 1)%R -∗
       WP e {{ l, ∃ r : R,  lazy_real l r ∗ ↯(F r) }}) -∗
    ↯ (RInt μ (x / 2 ^ y)%nat 1) -∗
    WP e {{ l, ∃ r : R,  lazy_real l r ∗ ↯(if (bool_decide (r<=(x/2^y)%nat)%R) then 0 else 1)%R }}.
  Proof.
    iIntros (Hpos Hex Hineq) "Hwp Herr".
    iApply "Hwp".
    - iPureIntro.
      exists 1. intros; case_bool_decide; lra.
    - iApply (ec_eq with "[$]").
      etrans; first (rewrite -RInt_Iverson_ge'; first done).
      + by apply ineq_lemma.
      + apply: ex_RInt_Chasles_2; first by apply ineq_lemma. done.
      + apply RInt_ext.
        intros.
        rewrite Rmult_comm. f_equal.
        rewrite /Iverson.
        case_match; case_bool_decide; lra.
  Qed. 
  
  Lemma wp_is_smaller_prog x y μ e:
    (∀ x, 0<=μ x)->
    ex_RInt μ 0 1 ->
    (x<2^y)%nat ->
    (∀ (F : R -> R), (⌜∃ M, ∀ x , 0 <= F x <= M⌝) -∗
       ↯ (RInt (fun (x:R) => μ x * F x) 0 1)%R -∗
       WP e {{ l, ∃ r : R,  lazy_real l r ∗ ↯(F r) }}) -∗
    ↯ (RInt μ (x / 2 ^ y)%nat 1) -∗
    WP is_smaller_prog e #x #y {{ v, ⌜v = #true⌝ }}.
  Proof.
    iIntros (Hpos Hex Hineq) "Hwp Herr".
    rewrite /is_smaller_prog.
    wp_bind e.
    wp_apply (pgl_wp_wand with "[-]"); first by iApply (wp_e with "[Hwp][$]").
    simpl.
    iIntros (?) "(%&Hl&Herr)".
    rewrite /lazy_real.
    iDestruct "Hl" as "(%&%&%&->&->&H)".
    wp_pures.
    case_bool_decide; last by iDestruct (ec_contradict with "[$]") as "[]".
  Admitted.
  
End adequacy.

Theorem wp_pgl_lim Σ `{erisGpreS Σ} (e : expr) (σ : state) (μ : R -> R):
  (∀ x, 0<=μ x)->
  ex_RInt μ 0 1 ->
  (∀ `{erisGS Σ} (F : R -> R) (Hnn : ∃ M, ∀ x , 0 <= F x <= M),
      ↯ (RInt (fun (x:R) => μ x * F x) 0 1)%R ⊢
     WP e {{ l, ∃ r : R,  lazy_real l r ∗ ↯(F r) }}) →
  ∀ (x y:nat), (x<2^y)%nat ->
  pgl (lim_exec (is_smaller_prog e #x #y, σ)) (λ x, x=#true) (RInt μ (x/2^y)%nat 1).
Proof.
  intros Hpos Hbound Hwp x y Hineq.
  apply ineq_lemma in Hineq as Hineq'.
  eapply (wp_pgl_lim Σ).
  { apply RInt_ge_0; first naive_solver.
    - by apply: ex_RInt_Chasles_2.
    - intros; apply Hpos.
  }
  iIntros (?) "Herr".
  iPoseProof (wp_is_smaller_prog with "[][$]") as "$"; [done..|].
  iIntros (? H2) "Herr".
  by iApply Hwp.
Qed. 
  

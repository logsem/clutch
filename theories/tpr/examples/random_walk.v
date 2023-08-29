From Coq Require Import Reals Psatz.
From Coq.Reals Require Import Rfunctions.
From Coquelicot Require Import Lim_seq Rbar Hierarchy.
From clutch.prelude Require Import stdpp_ext.
From clutch.prob Require Import distribution markov.

Definition step (b : bool) :=
  if b then fair_coin else dzero.

Definition to_final (b : bool) : option bool :=
  if b then None else Some false.

Definition random_walk_mixin : MarkovMixin step to_final.
Proof. constructor. by intros [] [] []; simplify_eq=>/=. Qed.

Canonical Structure random_walk : markov := Markov step to_final random_walk_mixin.

Lemma exec_random_walk n :
  SeriesC (exec n true) = 1 - (1/2)^n.
Proof.
  induction n.
  { rewrite Rminus_eq_0 /= dzero_mass //. }
  rewrite exec_Sn_not_final; [|by eapply to_final_None].
  rewrite /markov.step /=.
  rewrite fair_coin_dbind_mass.
  rewrite IHn.
  erewrite exec_is_final; [|done].
  rewrite dret_mass.
  lra.
Qed.

Lemma random_walk_terminates :
  SeriesC (lim_exec true) = 1.
Proof.
  apply (MCT_seriesC _ (λ n, SeriesC (exec n true))); last first.
  - simpl. setoid_rewrite exec_random_walk.
    intros ϵ. split.
    + intros n. trans 1.
      * apply Rminus_gt_0_lt.
        assert (1 - (1 - (1 / 2) ^ n) = (1 / 2) ^ n) as -> by lra.
        apply pow_lt. lra.
      * rewrite -{1}(Rplus_0_r 1).
        apply Rplus_lt_compat_l, cond_pos.
    + assert (∃ n, (1 / 2) ^ n < ϵ) as [n Hn].
      { case: (pow_lt_1_zero (1/2) _ ϵ (cond_pos ϵ)).
        { apply Rabs_def1; lra. }
        intros n Hn. exists n.
        specialize (Hn n (Nat.le_refl _)).
        by apply Rabs_def2 in Hn as [? ?]. }
      exists n. lra.
  - intros. by eapply SeriesC_correct.
  - eauto.
  - intros. eapply exec_mono.
  - eauto.
Qed.

From iris.proofmode Require Import coq_tactics ltac_tactics reduction proofmode.
From clutch.tpr Require Import weakestpre spec lifting ectx_lifting.
From clutch.prob_lang Require Export class_instances.
From clutch.prob_lang Require Import tactics lang notation.
From clutch.tpr Require Import primitive_laws proofmode adequacy.
From clutch.lib Require Import flip conversion.

Definition while (cond body : expr) : expr :=
  (rec: "loop" <> := (if: cond then body ;; "loop" #() else #())) #().

Notation "'while' e1 'do' e2 'end'" := (while e1 e2)
   (e1, e2 at level 200) : expr_scope.

Definition prog_random_walk : expr :=
  let: "c" := ref #true in
  while !"c" do "c" <- flip end.

(* TODO: generalize *)
Lemma Rcoupl_dunifP_1_coin `{Countable A} (μ : distr A) R :
  Rcoupl fair_coin μ R →
  Rcoupl (dunifP 1) μ (λ n a, R (fin_to_bool n) a).
Proof.
  intros Hcpl.
  assert (dunifP 1 = dmap bool_to_fin fair_coin) as ->.
  { apply distr_ext=>n.
    (* TODO: use some nicer lemma *)
    rewrite /pmf/= /dbind_pmf SeriesC_bool.
    rewrite /pmf/= /fair_coin_pmf /dret_pmf.
    inv_fin n; simpl; [lra|]=> n.
    inv_fin n; simpl; [lra|].
    inversion 1. }
  rewrite -(dret_id_right μ).
  apply Rcoupl_dmap.
  assert ((λ (a : bool) (a' : A), R (fin_to_bool (bool_to_fin a)) a') = R) as ->; [|done].
  extensionality b.
  rewrite bool_to_fin_to_bool //.
Qed.

Section coupl.
  Context `{!tprG δ Σ}.

  Lemma rwp_couple_flip E R a1 :
    Rcoupl fair_coin (step a1) R →
    {{{ specF a1 }}} flip @ E {{{ (b : bool) a2, RET #b; specF a2 ∗ ⌜R b a2⌝  }}}.
  Proof.
    iIntros (? Φ) "Ha HΦ". rewrite /flip/flipL.
    wp_pures.
    wp_apply (rwp_couple with "Ha"); [by eapply Rcoupl_dunifP_1_coin|].
    iIntros (n a2) "[Ha %HR]". rewrite /int_to_bool.
    wp_pures.
    case_bool_decide; wp_pures.
    - iApply "HΦ". iFrame. inv_fin n; eauto.
    - iApply ("HΦ"). iFrame. inv_fin n; eauto.
  Qed.

End coupl.

Section fair_coins.
  Variable (f : bool → bool).
  Context `{Inj bool bool (=) (=) f, Surj bool bool (=) f}.

  Definition fair_coins_pmf (bs : bool * bool) : R :=
    if bool_decide (bs.1 = f bs.2) then 0.5%R else 0.

  Program Definition fair_coins : distr (bool * bool) :=
    MkDistr fair_coins_pmf _ _ _.
  Next Obligation.
    rewrite /fair_coins_pmf.
    intros [[] []]; simpl; case_bool_decide; lra.
  Qed.
  Next Obligation.
    rewrite /fair_coins_pmf.
    destruct (f true) eqn:Hf1.
    - assert (f false = false) as Hf2.
      { destruct (f false) eqn:Hf2; [|done]. rewrite -Hf1 in Hf2. simplify_eq. }
      apply (ex_seriesC_ext (λ bs, (if bool_decide (bs = (true, true)) then 0.5 else 0) +
                                   (if bool_decide (bs = (false, false)) then 0.5 else 0)))%R.
      { intros [[] []]; simpl; rewrite ?Hf1 ?Hf2 /=; lra. }
      eapply ex_seriesC_plus; eapply ex_seriesC_singleton.
    - assert (f false = true) as Hf2.
      { destruct (f false) eqn:Hf2; [done|]. rewrite -Hf2 in Hf1. simplify_eq. }
      apply (ex_seriesC_ext (λ bs, (if bool_decide (bs = (true, false)) then 0.5 else 0) +
                                   (if bool_decide (bs = (false, true)) then 0.5 else 0)))%R.
      { intros [[] []]; simpl; rewrite ?Hf1 ?Hf2 /=; lra. }
      eapply ex_seriesC_plus; eapply ex_seriesC_singleton.
  Qed.
  Next Obligation.
    rewrite /fair_coins_pmf.
    destruct (f true) eqn:Hf1.
    - assert (f false = false) as Hf2.
      { destruct (f false) eqn:Hf2; [|done]. rewrite -Hf1 in Hf2. simplify_eq. }
      rewrite (SeriesC_ext _ (λ bs, (if bool_decide (bs = (true, true)) then 0.5 else 0) +
                                     if bool_decide (bs = (false, false)) then 0.5 else 0))%R; last first.
      { intros [[] []]; simpl; rewrite ?Hf1 ?Hf2 /=; lra. }
      erewrite SeriesC_plus; [|eapply ex_seriesC_singleton..].
      rewrite 2!SeriesC_singleton. lra.
    - assert (f false = true) as Hf2.
      { destruct (f false) eqn:Hf2; [done|]. rewrite -Hf2 in Hf1. simplify_eq. }
      rewrite (SeriesC_ext _ (λ bs, (if bool_decide (bs = (true, false)) then 0.5 else 0) +
                                     if bool_decide (bs = (false, true)) then 0.5 else 0))%R; last first.
      { intros [[] []]; simpl; rewrite ?Hf1 ?Hf2 /=; lra. }
      erewrite SeriesC_plus; [|eapply ex_seriesC_singleton..].
      rewrite 2!SeriesC_singleton. lra.
  Qed.
End fair_coins.

Definition f_inv {A B} f `{Surj A B (=) f} : B → A := λ b, epsilon (surj f b).

Lemma f_inv_cancel_r {A B} f `{Surj A B (=) f} b :
  f (f_inv f b) = b.
Proof. rewrite /f_inv /= (epsilon_correct _ (surj f b)) //. Qed.

Lemma f_inv_cancel_l {A B} f `{Inj A B (=) (=) f, Surj A B (=) f} b :
  f_inv f (f b) = b.
Proof. apply (inj f), (epsilon_correct _ (surj f (f b))). Qed.


Lemma Rcoupl_fair_coin f `{Bij bool bool f} :
  Rcoupl fair_coin fair_coin (λ b b', b = f b').
Proof.
  exists (fair_coins f). repeat split.
  - eapply distr_ext=> b.
    rewrite lmarg_pmf /pmf /= /fair_coins_pmf /fair_coin_pmf /=.
    rewrite (SeriesC_ext _ (λ b', if bool_decide (b' = f_inv f b) then 0.5 else 0))%R.
    { rewrite SeriesC_singleton //. }
    intros b'. case_bool_decide as Heq.
    + rewrite bool_decide_eq_true_2 //.
      rewrite Heq f_inv_cancel_l //.
    + rewrite bool_decide_eq_false_2 //.
      intros [= ->]. apply Heq. rewrite f_inv_cancel_r //.
  - eapply distr_ext=> b.
    rewrite rmarg_pmf /pmf /= /fair_coins_pmf /fair_coin_pmf /=.
    rewrite SeriesC_singleton //.
  - intros []. rewrite /pmf /= /fair_coins_pmf /=.
    case_bool_decide; [done|lra].
Qed.

Section random_walk.
  Context `{!tprG random_walk Σ}.

  Lemma random_walk_ref :
    ⟨⟨⟨ specF true ⟩⟩⟩ prog_random_walk ⟨⟨⟨ RET #(); specF false ⟩⟩⟩.
  Proof.
    rewrite /prog_random_walk.
    iIntros (Φ) "Ha HΦ".
    wp_alloc l as "Hl".
    do 3 wp_pure _.
    iLöb as "IH".
    wp_pures.
    wp_load.
    wp_pures.
    wp_apply (rwp_couple_flip _ (=) with "Ha").
    { simpl. apply Rcoupl_fair_coin. apply _. }
    iIntros (b a2) "[Ha <-]".
    wp_store.
    destruct b.
    - wp_apply ("IH" with "Ha HΦ Hl").
    - wp_pures. wp_load. wp_pures. by iApply "HΦ".
  Qed.

End random_walk.

Notation σ₀ := {| heap := ∅; tapes := ∅ |}.
Notation almost_surely_terminates ρ := (SeriesC (lim_exec_val ρ) = 1%R).

Theorem prog_random_walk_terminates :
  almost_surely_terminates (prog_random_walk, σ₀).
Proof.
  eapply Rle_antisym; [done|].
  transitivity (SeriesC (lim_exec true)).
  { by rewrite random_walk_terminates. }
  eapply (wp_refRcoupl_mass (tprΣ bool)).
  iIntros (?) "Ha".
  wp_apply (random_walk_ref with "Ha").
  iIntros "Ha".
  iExists _. iFrame.
  iPureIntro.
  by eapply to_final_Some_2.
Qed.

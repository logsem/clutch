From clutch.prob Require Export countable_sum countable_distribution countable_couplings.
From Coq Require Import Reals Psatz.
From Coq.ssr Require Import ssreflect.
From Coquelicot Require Import Rcomplements Rbar Series Lim_seq Hierarchy.
From stdpp Require Export countable finite.
From Coq.Logic Require Import ClassicalEpsilon.
From clutch.prelude Require Export base stdpp_ext Reals_ext Coquelicot_ext Series_ext classical uniform_list NNRbar.
From clutch.common Require Export language erasable.
From clutch.prob_lang Require Import erasure.

Open Scope R.

Section conv_comb.

  Context (A : Type).
  
  Record conv_comb := MkConvComb {
    ccr :> A -> cdistr A -> Prop; 
    ccr_cdret : ∀ a, ccr a (cdret a);
    ccr_cdbind : ∀ μ f a, 
      ccr a μ -> (∀ a', ccr a' (f a')) -> ccr a (cdbind f μ)
  }.

End conv_comb.

Section real_cc.
  
  Program Definition real_cc : conv_comb R := MkConvComb _ (λ x d, ex_seriesCS (λ a, d a * a) ∧ SeriesCS (λ a, d a * a) = x) _ _.
  Next Obligation.
    move => a //=.
    assert (∀ a0, cdret a a0 * a0 = if bool_decide (a0 = a) then a else 0). 
    { intros. rewrite cdret_pmf_unfold. real_solver. }
    econstructor.
    - eapply (ex_seriesCS_ext (λ a0, if bool_decide (a0 = a) then a else 0)) => //=.
      eapply ex_seriesCS_singleton.
    - erewrite (SeriesCS_ext _ (λ a0, if bool_decide (a0 = a) then a else 0)) => //=.
      eapply SeriesCS_singleton.
  Qed.
  Next Obligation.
    simpl. intros ??? (?&?) ?.
    econstructor; last first.

    - erewrite (SeriesCS_ext _ (fun x => SeriesCS (λ a0 : R, μ a0 * f a0 x) * x));
      last by intros; rewrite cdbind_unfold_pmf.
      erewrite (SeriesCS_ext _ (fun x => SeriesCS (λ a0 : R, μ a0 * (f a0 x * x))));
      last by intros; rewrite -SeriesCS_scal_r; apply SeriesCS_ext; real_solver.
      
  Admitted.

End real_cc.

Section nnr_cc.
  
  Program Definition nnr_cc : conv_comb nonnegreal := MkConvComb _ (λ x d, ex_seriesCS (λ a, d a * a) ∧ SeriesCS (λ a, d a * a) = x) _ _.
  Next Obligation.
    move => a //=.
    Locate nnreal_zero.
    assert (∀ a0, cdret a a0 * a0 = if bool_decide (a0 = a) then a else nnreal_zero). 
    { intros. rewrite cdret_pmf_unfold. real_solver. }
    econstructor.
    - eapply (ex_seriesCS_ext (λ a0, if bool_decide (a0 = a) then nonneg a else 0)); first by intros; rewrite cdret_pmf_unfold; real_solver.
      eapply ex_seriesCS_singleton.
    - erewrite (SeriesCS_ext _ (λ a0, if bool_decide (a0 = a) then nonneg a else 0)); last by intros; rewrite cdret_pmf_unfold; real_solver.
      eapply SeriesCS_singleton.
  Qed.
  Next Obligation.
    (* simpl. intros ??? (?&?) ?.
    econstructor; last first.

    - erewrite (SeriesCS_ext _ (fun x => SeriesCS (λ a0 : R, μ a0 * f a0 x) * x));
      last by intros; rewrite cdbind_unfold_pmf.
      erewrite (SeriesCS_ext _ (fun x => SeriesCS (λ a0 : R, μ a0 * (f a0 x * x))));
      last by intros; rewrite -SeriesCS_scal_r; apply SeriesCS_ext; real_solver.
       *)
  Admitted.

End nnr_cc.

Section prog_cc.

  Context {Λ : language}.

  Inductive pexec_rel : (cfg Λ) -> (cdistr (cfg Λ)) -> Prop := 
  | exec_rel_stepN n ρ : pexec_rel ρ (pexec n ρ)
  | exec_rel_erasable e σ μ : erasable μ σ -> pexec_rel (e, σ) (dmap (pair e) μ)
  | exec_rel_rec μ f ρ : pexec_rel ρ μ -> (∀ ρ', pexec_rel ρ' (f ρ')) -> pexec_rel ρ (cdbind f μ)
  .

  Program Definition prog_cc : conv_comb (cfg Λ) := MkConvComb _ pexec_rel _ _.
  Next Obligation.
    intros. replace (cdret a) with (distr_cdistr (pexec 0 a)); first by apply exec_rel_stepN.
    by rewrite pexec_O cdret_dret.
  Qed.
  Next Obligation. 
    by econstructor. 
  Qed.

End prog_cc.
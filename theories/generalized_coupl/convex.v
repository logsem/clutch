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
      ccr a μ -> (∀ a', ccr a' (f a')) -> ccr a (cdbind f μ);
    ccr_convex : ∀ {B} (μ : cdistr B) f a, 
      (∀ x, ccr a (f x)) -> ccr a (cdbind f μ)
  }.

End conv_comb.

#[global] Hint Resolve ccr_cdret : core.

Section real_cc.
  
  Program Definition real_cc : conv_comb R := MkConvComb _ (λ x d, ex_seriesCS (λ a, d a * a) ∧ SeriesCS (λ a, d a * a) = x) _ _ _.
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
  Next Obligation.

  Admitted.

End real_cc.

Section nnr_cc.
  
  Program Definition nnr_cc : conv_comb nonnegreal := MkConvComb _ (λ x d, ex_seriesCS (λ a, d a * a) ∧ SeriesCS (λ a, d a * a) = x) _ _ _.
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
  Next Obligation.
  Admitted.

End nnr_cc.

Section prog_cc.

  Context {Λ : language}.

  Inductive pexec_rel : (cfg Λ) -> (cdistr (cfg Λ)) -> Prop := 
  | exec_rel_stepN n ρ : pexec_rel ρ (pexec n ρ)
  | exec_rel_erasable e σ μ : erasable μ σ -> pexec_rel (e, σ) (dmap (pair e) μ)
  | exec_rel_bind μ f ρ : pexec_rel ρ μ -> (∀ ρ', pexec_rel ρ' (f ρ')) -> pexec_rel ρ (cdbind f μ)
  | exec_rel_rec μ f ρ : pexec_rel ρ μ -> (∀ ρ', pexec_rel ρ' (f ρ')) -> pexec_rel ρ (cdbind f μ)
  .

  Program Definition prog_cc : conv_comb (cfg Λ) := MkConvComb _ pexec_rel _ _ _.
  Next Obligation.
    intros. replace (cdret a) with (distr_cdistr (pexec 0 a)); first by apply exec_rel_stepN.
    by rewrite pexec_O cdret_dret.
  Qed.
  Next Obligation. 
    by econstructor. 
  Qed.
  Next Obligation.
    intros.
  Admitted.

End prog_cc.

Section prod_cc.
  Context {A B : Type}.

  Variables (ca : conv_comb A) (cb : conv_comb B).

  Definition prod_cc_rel (a : A) (b : B) μ η := ca a μ ∧ cb b η.

  Program Definition prod_cc : conv_comb (A * B) := MkConvComb _ (λ p d, prod_cc_rel p.1 p.2 (cdbind (λ x, cdret $ fst x) d) (cdbind (λ x, cdret $ snd x) d)) _ _ _.
  Next Obligation.
    move => [a b] //=.
    rewrite /prod_cc_rel. split.
    - have -> : cdbind (λ x : A * B, cdret x.1) (cdret (a, b)) = cdret a.
      { apply cdistr_ext => a'.
        rewrite cdbind_unfold_pmf.
        erewrite (SeriesCS_ext _ (λ x : A * B, if bool_decide (x = (a, b)) then cdret a a' else 0)).
        - apply SeriesCS_singleton.
        - intros [a'' b'']. rewrite cdret_pmf_unfold. real_solver. }
      apply ccr_cdret.
    - have -> : cdbind (λ x : A * B, cdret x.2) (cdret (a, b)) = cdret b.
      { apply cdistr_ext => b'.
        rewrite cdbind_unfold_pmf.
        erewrite (SeriesCS_ext _ (λ x : A * B, if bool_decide (x = (a, b)) then cdret b b' else 0)).
        - apply SeriesCS_singleton.
        - intros [a'' b'']. rewrite cdret_pmf_unfold. real_solver. }
      apply ccr_cdret.
  Qed.
  Next Obligation.
    rewrite /prod_cc_rel.
    move => μ f [a b] //= [Ha Hb] Hc.
    (* Both marginals of [cdbind f μ] equal [cdbind (λ x, marginal(f x)) μ]
       by monad associativity / Fubini (cdistr_double_swap). *)
    have Hfst : cdbind (λ x : A * B, cdret x.1) (cdbind f μ) =
                cdbind (λ x : A * B, cdbind (λ y : A * B, cdret y.1) (f x)) μ.
    { admit. (* cdistr_double_swap + SeriesCS_scal_r *) }
    have Hsnd : cdbind (λ x : A * B, cdret x.2) (cdbind f μ) =
                cdbind (λ x : A * B, cdbind (λ y : A * B, cdret y.2) (f x)) μ.
    { admit. }
    split.
    - rewrite Hfst.
      replace (cdbind (λ x : A * B, cdbind (λ y : A * B, cdret y.1) (f x)) μ) with
        (cdbind (λ a'',
                   cdbind (λ b'', cdbind (λ y : A * B, cdret y.1) (f (a'', b'')))
                          (cdbind (λ x : A * B, cdret x.2) μ))
               (cdbind (λ x : A * B, cdret x.1) μ)); last first.
      { admit. (* distribution equality: requires disintegration of μ *) }
      apply (ccr_cdbind _ ca (cdbind (λ x : A * B, cdret x.1) μ) _ a Ha).
      intro a''. apply (ccr_convex _ ca (cdbind (λ x : A * B, cdret x.2) μ) _ a'').
      intro b''. exact (proj1 (Hc (a'', b''))).
    - rewrite Hsnd.
      replace (cdbind (λ x : A * B, cdbind (λ y : A * B, cdret y.2) (f x)) μ) with
        (cdbind (λ b'',
                   cdbind (λ a'', cdbind (λ y : A * B, cdret y.2) (f (a'', b'')))
                          (cdbind (λ x : A * B, cdret x.1) μ))
               (cdbind (λ x : A * B, cdret x.2) μ)); last first.
      { admit. (* distribution equality: requires disintegration of μ *) }
      apply (ccr_cdbind _ cb (cdbind (λ x : A * B, cdret x.2) μ) _ b Hb).
      intro b''. apply (ccr_convex _ cb (cdbind (λ x : A * B, cdret x.1) μ) _ b'').
      intro a''. exact (proj2 (Hc (a'', b''))).
  Admitted.
  Next Obligation.
    rewrite /prod_cc_rel.
    intros C μ f [a b] Hc => //=.
    have Hfst : cdbind (λ x : A * B, cdret x.1) (cdbind f μ) =
                cdbind (λ x : C, cdbind (λ y : A * B, cdret y.1) (f x)) μ.
    { admit. (* cdistr_double_swap + SeriesCS_scal_r *) }
    have Hsnd : cdbind (λ x : A * B, cdret x.2) (cdbind f μ) =
                cdbind (λ x : C, cdbind (λ y : A * B, cdret y.2) (f x)) μ.
    { admit. }
    split.
    - rewrite Hfst.
      apply (ccr_convex _ _ μ _ a).
      intro x. exact (proj1 (Hc x)).
    - rewrite Hsnd.
      apply (ccr_convex _ _ μ _ b).
      intro x. exact (proj2 (Hc x)).
  Admitted.

End prod_cc.
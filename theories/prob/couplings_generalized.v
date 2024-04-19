(** Generalized exact couplings *)
(** Exact couplings  *)
From Coq Require Import Reals Psatz.
From Coquelicot Require Import Rcomplements.
From stdpp Require Export countable.

From clutch.prelude Require Import base Coquelicot_ext Reals_ext stdpp_ext classical.
From clutch.prob Require Export countable_sum distribution couplings.

Local Open Scope R.
Section coupl_generalized.
  Context `{Countable A, Countable B}.
  Context (μ1:distr A) (μ2: distr B).

  Program Definition distr_scal1 (μ:distr(A*B)):= distr_scal (SeriesC μ1) (lmarg μ) _.
  Next Obligation.
    intros; split; auto.
    real_solver.
  Qed.
  
  Program Definition distr_scal2 (μ:distr(A*B)):= distr_scal (SeriesC μ2) (rmarg μ) _.
  Next Obligation.
    intros; split; auto.
    real_solver.
  Qed.

  Lemma distr_scal1_pmf μ x: distr_scal1 μ x = (SeriesC μ1) * lmarg μ x.
  Proof.
    done.
  Qed.
  Lemma distr_scal2_pmf μ x: distr_scal2 μ x = (SeriesC μ2) * rmarg μ x.
  Proof.
    done.
  Qed.
  
  Definition is_gencoupl (μ:distr(A*B)) :=
    distr_scal1 (μ) = μ1 /\ distr_scal2 (μ) = μ2.

  Definition ex_gencoupl := ∃ (μ : distr (A * B)), is_gencoupl μ.
End coupl_generalized.

Section Rgencoupl.
  Context `{Countable A, Countable B}.
  Context (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop).

  Definition is_Rgencoupl (μ : distr (A * B)) :=
    is_gencoupl μ1 μ2 μ ∧ ∀ (p : A * B), μ p > 0 → R p.1 p.2.

  Definition Rgencoupl := ∃ (μ : distr (A * B)), is_Rgencoupl μ.
End Rgencoupl.
  
Section ex_gencoupl.
  Context `{Countable A, Countable B}.
  Lemma ex_gencoupl_dbind `{Countable A', Countable B'} (f : A → distr A') (g : B → distr B')
    (μ1 : distr A) (μ2 : distr B) :
    (∀ a b, ex_gencoupl (f a) (g b)) → ex_gencoupl μ1 μ2 → ex_gencoupl (μ1 ≫= f) (μ2 ≫= g).
  Proof.
    intros Hfg (μ & Hμ).
    rewrite /ex_gencoupl in Hfg.
    assert (∀ (p : A * B), ∃ μ : distr (A' * B'), is_gencoupl (f p.1) (g p.2) μ) as Hfg'; [done|].
    apply ClassicalEpsilon.choice in Hfg' as (Ch & HCh).
    rewrite /ex_gencoupl.
    exists (dbind Ch μ); split.
    + apply distr_ext; intro a'.
      rewrite distr_scal1_pmf.
      rewrite lmarg_pmf.
      rewrite /pmf/=/dbind_pmf.
      rewrite <-distr_double_swap_lmarg.
      setoid_rewrite SeriesC_scal_l.
      assert (∀ p , SeriesC (f p.1) * SeriesC (λ b' : B', Ch p (a', b')) = f p.1 a') as Heq2.
      { intros (a & b).
        specialize (HCh (a, b)) as (HChL & HChR). simpl.
        rewrite -{2}HChL.
        rewrite distr_scal1_pmf. simpl.
        rewrite lmarg_pmf //.
      }
      destruct Hμ as [Hμ1 Hμ2].
  (*       rewrite lmarg_pmf //. } *)
  (*     rewrite (SeriesC_ext _ _ Heq2). *)
  (*     rewrite fubini_pos_seriesC_prod_lr. *)
  (*     2: { simpl; intros; by apply Rmult_le_pos. } *)
  (*     2: { apply (ex_seriesC_le _ μ); [|done]. *)
  (*          intros; split; [by apply Rmult_le_pos|]. *)
  (*          rewrite -{2}(Rmult_1_r (μ n)). *)
  (*          by apply Rmult_le_compat. } *)
  (*     rewrite /dbind_pmf. *)
  (*     rewrite /pmf/=/dbind_pmf.  rewrite /lmarg_pmf. *)
  (*     rewrite /lmarg. *)
  (*     rewrite {2}/pmf/=. rewrite !/dbind_pmf. *)
  (*     rewrite /lmarg_pmf. *)
  (*     rewrite /dbind_pmf. *)
  (*     erewrite (SeriesC_ext (λ _, _*_)); last first. *)
  (*     { intros. by rewrite /pmf/= /dbind_pmf. } *)
  (*     rewrite /dret_pmf. *)
      
  (*     rewrite <- distr_double_swap_lmarg. *)
  (*     setoid_rewrite SeriesC_scal_l. *)
  (*     assert (∀ p , μ p * SeriesC (λ b' : B', Ch p (a', b')) = μ p * f p.1 a') as Heq2. *)
  (*     { intros (a & b). *)
  (*       specialize (HCh (a, b)) as (HChL & HChR). *)
  (*       rewrite -HChL. *)
  (*       rewrite lmarg_pmf //. } *)
  (*     rewrite (SeriesC_ext _ _ Heq2). *)
  (*     rewrite fubini_pos_seriesC_prod_lr. *)
  (*     2: { simpl; intros; by apply Rmult_le_pos. } *)
  (*     2: { apply (ex_seriesC_le _ μ); [|done]. *)
  (*          intros; split; [by apply Rmult_le_pos|]. *)
  (*          rewrite -{2}(Rmult_1_r (μ n)). *)
  (*          by apply Rmult_le_compat. } *)
  (*     assert (∀ a : A, SeriesC (λ b : B, μ (a, b) * f (a, b).1 a') *)
  (*              = SeriesC (λ b : B, μ (a, b) ) * f a a') as Heq3. *)
  (*     { intro a; simpl; apply SeriesC_scal_r. } *)
  (*     rewrite (SeriesC_ext _ _ Heq3). *)
  (*     assert (∀ a, SeriesC (λ b : B, μ (a, b)) = μ1 a) as Heq4. *)
  (*     { intro a. *)
  (*       destruct Hμ as (Hμ1 & Hμ2). *)
  (*       rewrite <- Hμ1. *)
  (*       rewrite lmarg_pmf //. } *)
  (*     apply SeriesC_ext. *)
  (*     intro a. rewrite Heq4 //. *)
  (*   (* The second half is esentially the same as the first, can it be proven somehow by symmetry? *) *)
  (*   + apply distr_ext; intro b'. *)
  (*     rewrite rmarg_pmf. *)
  (*     rewrite {1 2}/pmf/=/dbind_pmf. *)
  (*     rewrite <- distr_double_swap_rmarg. *)
  (*     setoid_rewrite SeriesC_scal_l. *)
  (*     assert (∀ p , μ p * SeriesC (λ a' : A', Ch p (a', b')) = μ p * g p.2 b') as Heq2. *)
  (*     { intros (a & b). *)
  (*       specialize (HCh (a, b)) as (HChL & HChR). *)
  (*       rewrite <- HChR. *)
  (*       rewrite rmarg_pmf //. } *)
  (*     rewrite (SeriesC_ext _ _ Heq2). *)
  (*     rewrite fubini_pos_seriesC_prod_rl //. *)
  (*     2:{ simpl; intros; by apply Rmult_le_pos. } *)
  (*     2:{ apply (ex_seriesC_le _ μ); [|done]. *)
  (*         intros; split; [by apply Rmult_le_pos|]. *)
  (*         rewrite -{2}(Rmult_1_r (μ _)). *)
  (*         by apply Rmult_le_compat. } *)
  (*     assert (∀ b : B, SeriesC (λ a : A, μ (a, b) * g (a, b).2 b') *)
  (*              = SeriesC (λ a : A, μ (a, b) ) * g b b') as Heq3. *)
  (*     { intro b; simpl; apply SeriesC_scal_r. } *)
  (*     rewrite (SeriesC_ext _ _ Heq3). *)
  (*     assert (∀ b, SeriesC (λ a : A, μ (a, b)) = μ2 b) as Heq4. *)
  (*     { intro b. *)
  (*       destruct Hμ as (Hμ1 & Hμ2). *)
  (*       rewrite -Hμ2 rmarg_pmf //. } *)
  (*     apply SeriesC_ext. *)
  (*     intro b. rewrite Heq4 //. *)
      (* Qed. *)
  Admitted.
End ex_gencoupl.

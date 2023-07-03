From Coq Require Import Reals Psatz.
From Coq.ssr Require Import ssreflect ssrfun.
From Coquelicot Require Import Rcomplements Lim_seq Rbar.
From stdpp Require Export countable.
From clutch.prelude Require Export base Coquelicot_ext Reals_ext stdpp_ext.
From clutch.prob Require Export countable_sum distribution.

Open Scope R.

Section relations.

  Context `{Countable A, Countable B}.
  Context (R : A -> B -> Prop) (P : A → Prop).
  Context (dec_R : forall a b, Decision (R a b)).
  Context (dec_P : forall a, Decision (P a)).

  Global Instance rel_img_dec : forall b, Decision (exists a, P a /\ R a b).
  Proof.
    intro.
    apply make_decision.
  Defined.

End relations.

Section couplings.
  Context `{Countable A, Countable B, Countable A', Countable B'}.
  Context (μ1 : distr A) (μ2 : distr B) (S : A -> B -> Prop).


  Definition Rcoupl :=
    forall (f: A → R) (g: B -> R),
    (forall a, 0 <= f a <= 1) ->
    (forall b, 0 <= g b <= 1) ->
    (forall a b, S a b -> f a <= g b) ->
    SeriesC (λ a, μ1 a * f a) <= SeriesC (λ b, μ2 b * g b).

End couplings.

Section couplings_theory.
  Context `{Countable A, Countable B, Countable A', Countable B'}.

  Lemma Rcoupl_dret (a : A) (b : B) (R : A → B → Prop) :
    R a b → Rcoupl (dret a) (dret b) R.
  Proof.
    intro HR.
    intros f g Hf Hg Hfg.
    assert (SeriesC (λ a0 : A, dret a a0 * f a0) = f a) as ->.
    { rewrite <-(SeriesC_singleton a (f a)).
      apply SeriesC_ext. rewrite /pmf/=/dret_pmf. real_solver.
    }
    assert (SeriesC (λ b0 : B, dret b b0 * g b0) = g b) as ->.
    { rewrite <-(SeriesC_singleton b (g b)).
      apply SeriesC_ext. rewrite /pmf/=/dret_pmf. real_solver.
    }
    auto.
  Qed.


  Lemma Rcoupl_dbind (f : A → distr A') (g : B → distr B')
    (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) (S : A' → B' → Prop) :
      (∀ a b, R a b → Rcoupl (f a) (g b) S) → Rcoupl μ1 μ2 R → Rcoupl (dbind f μ1) (dbind g μ2) S.
  Proof.
    intros Hcoup_fg Hcoup_R h1 h2 Hh1pos Hh2pos Hh1h2S.
    rewrite /Rcoupl in Hcoup_R.
    rewrite /Rcoupl in Hcoup_fg.
    rewrite /pmf/=/dbind_pmf.
    setoid_rewrite <- SeriesC_scal_r.

    rewrite <-(fubini_pos_seriesC (λ '(a,x), μ1 x * f x a * h1 a)).
    - assert (SeriesC (λ b : A, SeriesC (λ a : A', μ1 b * f b a * h1 a)) =
             SeriesC (λ b : A, μ1 b * SeriesC (λ a : A', f b a * h1 a))) as ->.
    {
      apply SeriesC_ext; intro.
      rewrite <- SeriesC_scal_l.
      apply SeriesC_ext; real_solver.
    }
    rewrite <-(fubini_pos_seriesC (λ '(b,x), μ2 x * g x b * h2 b)).
    2:{
      intros b' b.
      specialize (Hh2pos b').
      real_solver.
    }
    2:{
      intro b'.
      specialize (Hh2pos b').
      apply (ex_seriesC_le _ μ2); auto.
      intro b; split.
      - apply Rmult_le_pos.
        + real_solver.
        + real_solver.
      - rewrite <- Rmult_1_r.
        rewrite Rmult_assoc.
        apply Rmult_le_compat_l; auto.
        rewrite <- Rmult_1_r.
        apply Rmult_le_compat; real_solver.
       }
    2:{
      setoid_rewrite SeriesC_scal_r.
      apply (ex_seriesC_le _ (λ a : B', SeriesC (λ b : B, μ2 b * g b a))); auto.
      - intros b'; specialize (Hh2pos b'); split.
        + apply Rmult_le_pos; [ | lra].
          apply (pmf_pos ((dbind g μ2)) b').
        + rewrite <- Rmult_1_r.
          apply Rmult_le_compat_l; auto.
          * apply SeriesC_ge_0'. real_solver.
          * real_solver.
      - apply (pmf_ex_seriesC (dbind g μ2)).
    }
    assert (SeriesC (λ b : B, SeriesC (λ a : B', μ2 b * g b a * h2 a))
            = SeriesC (λ b : B, μ2 b * SeriesC (λ a : B', g b a * h2 a))) as ->.
    {
      apply SeriesC_ext; intro.
      rewrite <- SeriesC_scal_l.
      apply SeriesC_ext; real_solver.
    }
    apply Hcoup_R.
    + intro; split.
      * apply SeriesC_ge_0'; intro a'.
        specialize (Hh1pos a'); real_solver.
      * apply (Rle_trans _ (SeriesC (f a))); auto.
        apply SeriesC_le; auto.
        intro a'.
        specialize (Hh1pos a'); real_solver.
    + intro; split.
      * apply SeriesC_ge_0'; intro b'.
        specialize (Hh2pos b'); real_solver.
      * apply (Rle_trans _ (SeriesC (g b))); auto.
        apply SeriesC_le; auto.
        intro b'.
        specialize (Hh2pos b'); real_solver.
    + intros a b Rab.
      apply Hcoup_fg; auto.
    - intros a' a.
      specialize (Hh1pos a'); real_solver.
    - intro a'.
      specialize (Hh1pos a').
      apply (ex_seriesC_le _ μ1); auto.
      intro a; split.
      + apply Rmult_le_pos.
        * real_solver.
        * real_solver.
      + rewrite <- Rmult_1_r.
        rewrite Rmult_assoc.
        apply Rmult_le_compat_l; auto.
        rewrite <- Rmult_1_r.
        apply Rmult_le_compat; real_solver.
    - setoid_rewrite SeriesC_scal_r.
      apply (ex_seriesC_le _ (λ a : A', SeriesC (λ x : A, μ1 x * f x a))); auto.
      + intros a'; specialize (Hh1pos a'); split.
        * apply Rmult_le_pos; [ | lra].
          apply (pmf_pos ((dbind f μ1)) a').
        * rewrite <- Rmult_1_r.
          apply Rmult_le_compat_l; auto.
          -- apply SeriesC_ge_0'. real_solver.
          -- real_solver.
      + apply (pmf_ex_seriesC (dbind f μ1)).
Qed.



  Lemma Rcoupl_mass_leq (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) :
    Rcoupl μ1 μ2 R → SeriesC μ1 <= SeriesC μ2.
  Proof.
    intros Hcoupl.
    rewrite /Rcoupl in Hcoupl.
    rewrite -(Rmult_1_r (SeriesC μ1)).
    rewrite -(Rmult_1_r (SeriesC μ2)).
    do 2 rewrite -SeriesC_scal_r.
    apply Hcoupl; intros; lra.
  Qed.


  Lemma Rcoupl_eq (μ1 : distr A) :
    Rcoupl μ1 μ1 (=).
  Proof.
    intros f g Hf Hg Hfg.
    apply SeriesC_le.
    - intro a; specialize (Hf a); specialize (Hg a); real_solver.
    - apply (ex_seriesC_le _ μ1); auto.
      intro a; specialize (Hg a); real_solver.
  Qed.

(*
  Lemma coupl_sym (μ1 : distr A) (μ2 : distr B) :
    coupl μ1 μ2 -> coupl μ2 μ1.
  Proof.
    intros (μ & HμL & HμR).
    exists (dmap (λ '(a, b), (b, a)) μ); split; apply distr_ext.
    + intro b.
      rewrite <- HμR.
      rewrite lmarg_pmf rmarg_pmf.
      apply SeriesC_ext; intro a.
      simpl.
      rewrite {1}/pmf /= /dbind_pmf /=.
      rewrite {2}/pmf /= /dret_pmf /=.
      assert (∀ a0, μ a0 * (if bool_decide ((b, a) = (let '(a1, b0) := a0 in (b0, a1))) then 1 else 0)
                    = if bool_decide ((a, b) = a0 ) then μ (a, b) else 0) as Heq1.
      { intros (a' & b').
        case_bool_decide; case_bool_decide; simplify_eq; try lra.
      }
      rewrite (SeriesC_ext _ _ Heq1).
      apply SeriesC_singleton'.
    + intro a.
      rewrite <- HμL.
      rewrite lmarg_pmf rmarg_pmf.
      apply SeriesC_ext; intro b.
      simpl.
      rewrite {1}/pmf /= /dbind_pmf /=.
      rewrite {2}/pmf /= /dret_pmf /=.
      assert (∀ a0, μ a0 * (if bool_decide ((b, a) = (let '(a1, b0) := a0 in (b0, a1))) then 1 else 0)
                    = if bool_decide ((a, b) = a0 ) then μ (a, b) else 0) as Heq1.
      { intros (a' & b').
        case_bool_decide; case_bool_decide; simplify_eq; try lra. }
      rewrite (SeriesC_ext _ _ Heq1).
      apply SeriesC_singleton'.
  Qed.

  Lemma coupl_dbind (f : A → distr A') (g : B → distr B') (μ1 : distr A) (μ2 : distr B) :
    (∀ a b, coupl (f a) (g b)) → coupl μ1 μ2 → coupl (dbind f μ1) (dbind g μ2).
  Proof.
    intros Hfg (μ & Hμ).
    rewrite /coupl in Hfg.
    assert (∀ (p : A * B), ∃ μ : distr (A' * B'), isCoupl (f p.1) (g p.2) μ) as Hfg'; auto.
    pose proof (Choice (A * B) (distr (A' * B')) _ Hfg') as Ch.
    rewrite /coupl.
    destruct Ch as (Ch & HCh).
    exists (dbind Ch μ); split.
    + apply distr_ext; intro a'.
      rewrite lmarg_pmf.
      rewrite {1 2}/pmf/=/dbind_pmf.
      rewrite <- distr_double_swap_lmarg.
      setoid_rewrite SeriesC_scal_l.
      assert (∀ p , μ p * SeriesC (λ b' : B', Ch p (a', b')) = μ p * f p.1 a') as Heq2.
      { intros (a & b).
        specialize (HCh (a, b)) as (HChL & HChR).
        rewrite <- HChL.
        rewrite lmarg_pmf.
        auto.
      }
      rewrite (SeriesC_ext _ _ Heq2).
      rewrite fubini_pos_seriesC_prod_lr; auto.
      2:{simpl; intros; apply Rmult_le_pos; auto. }
      2:{apply (ex_seriesC_le _ μ); auto.
         intros; split; [apply Rmult_le_pos; auto | ].
         rewrite <- Rmult_1_r; apply Rmult_le_compat; auto.
         apply Rle_refl.
      }
      assert (∀ a : A, SeriesC (λ b : B, μ (a, b) * f (a, b).1 a')
               = SeriesC (λ b : B, μ (a, b) ) * f a a') as Heq3.
      {
        intro a; simpl; apply SeriesC_scal_r.
      }
      rewrite (SeriesC_ext _ _ Heq3).
      assert (∀ a, SeriesC (λ b : B, μ (a, b)) = μ1 a) as Heq4.
      {
        intro a.
        destruct Hμ as (Hμ1 & Hμ2).
        rewrite <- Hμ1;
        rewrite lmarg_pmf; auto.
      }
      apply SeriesC_ext.
      intro a.
      rewrite (Heq4 a); auto.
    (* The second half is esentially the same as the first, can it be proven somehow by symmetry? *)
    + apply distr_ext; intro b'.
      rewrite rmarg_pmf.
      rewrite {1 2}/pmf/=/dbind_pmf.
      rewrite <- distr_double_swap_rmarg.
      setoid_rewrite SeriesC_scal_l.
      assert (∀ p , μ p * SeriesC (λ a' : A', Ch p (a', b')) = μ p * g p.2 b') as Heq2.
      { intros (a & b).
        specialize (HCh (a, b)) as (HChL & HChR).
        rewrite <- HChR.
        rewrite rmarg_pmf.
        auto.
      }
      rewrite (SeriesC_ext _ _ Heq2).
      rewrite fubini_pos_seriesC_prod_rl; auto.
      2:{simpl; intros; apply Rmult_le_pos; auto. }
      2:{apply (ex_seriesC_le _ μ); auto.
         intros; split; [apply Rmult_le_pos; auto | ].
         rewrite <- Rmult_1_r; apply Rmult_le_compat; auto.
         apply Rle_refl.
      }
      assert (∀ b : B, SeriesC (λ a : A, μ (a, b) * g (a, b).2 b')
               = SeriesC (λ a : A, μ (a, b) ) * g b b') as Heq3.
      {
        intro b; simpl; apply SeriesC_scal_r.
      }
      rewrite (SeriesC_ext _ _ Heq3).
      assert (∀ b, SeriesC (λ a : A, μ (a, b)) = μ2 b) as Heq4.
      {
        intro b.
        destruct Hμ as (Hμ1 & Hμ2).
        rewrite <- Hμ2;
        rewrite rmarg_pmf; auto.
      }
      apply SeriesC_ext.
      intro b.
      rewrite (Heq4 b); auto.
  Qed.


  Lemma Rcoupl_dbind (f : A → distr A') (g : B → distr B')
    (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) (S : A' → B' → Prop) :
      (∀ a b, R a b → Rcoupl (f a) (g b) S) → Rcoupl μ1 μ2 R → Rcoupl (dbind f μ1) (dbind g μ2) S.
  Proof.
    intros Hfg (μ & HμC & HμS).
    rewrite /Rcoupl /isRcoupl in Hfg.
    (* First we rewrite Hfg to be able to use Choice *)
    assert (∀ p, ∃ μ', R p.1 p.2 →
                       (isCoupl (f p.1) (g p.2) μ' ∧ (∀ q : A' * B', μ' q > 0 → S q.1 q.2)))
      as Hfg'; auto.
    {
      intro p.
      specialize (HμS p).
      specialize (Hfg p.1 p.2).
      pose proof (ExcludedMiddle (R p.1 p.2)) as H3; destruct H3 as [HR | HnR].
      + specialize (Hfg HR).
        destruct Hfg as (μ' & Hμ'1 & Hμ'2).
        exists μ'; auto.
      + exists dzero; intro ; done.
    }
    pose proof (Choice (A * B) (distr (A' * B')) _ Hfg') as (Ch & HCh).
    rewrite /Rcoupl /isRcoupl.
    exists (dbind Ch μ); split; try split.
 (* To prove that the first marginal coincides is a matter of rearranging the sums and using the
    fact that μ and (Ch p) are couplings *)
    + apply distr_ext; intro a'.
      rewrite lmarg_pmf.
      rewrite {1 2}/pmf/=/dbind_pmf.
      rewrite <- distr_double_swap_lmarg.
      setoid_rewrite SeriesC_scal_l.
      erewrite (SeriesC_ext _ (λ p, μ p * f p.1 a')); last first.
      { intros (a & b).
        destruct (Rtotal_order (μ (a, b)) 0) as [Hlt | [Heqz | Hgt]].
        - pose proof (pmf_pos μ (a, b)); lra.
        - rewrite Heqz; lra.
        - specialize (HCh (a, b) (HμS (a, b) Hgt )) as ((HChL & HChR) & HChS).
          rewrite -HChL lmarg_pmf //=. }
      rewrite fubini_pos_seriesC_prod_lr; auto.
      2:{simpl; intros; apply Rmult_le_pos; auto. }
      2:{apply (ex_seriesC_le _ μ); auto.
         intros; split; [apply Rmult_le_pos; auto | ].
         rewrite <- Rmult_1_r; apply Rmult_le_compat; auto.
         apply Rle_refl.
      }
      erewrite (SeriesC_ext _ (λ a, SeriesC (λ b : B, μ (a, b) ) * f a a'));
      [ | intro a; simpl; apply SeriesC_scal_r ].
      erewrite (SeriesC_ext _ (λ a, (μ1 a) * f a a')); auto.
      intro a.
      destruct HμC as (Hμ1 & Hμ2).
      rewrite <- Hμ1;
      rewrite lmarg_pmf; auto.
    (* The second half is esentially the same as the first, can it be proven somehow by symmetry? *)
    + apply distr_ext; intro b'.
      rewrite rmarg_pmf.
      rewrite {1 2}/pmf/=/dbind_pmf.
      rewrite <- distr_double_swap_rmarg.
      setoid_rewrite SeriesC_scal_l.
      erewrite (SeriesC_ext _ (λ p, μ p * g p.2 b')); last first.
      {intros (a & b);
        destruct (Rtotal_order (μ (a, b)) 0) as [Hlt | [Heqz | Hgt]];
        [ pose proof (pmf_pos μ (a, b)); lra | rewrite Heqz; lra |
        specialize (HCh (a, b) (HμS (a, b) Hgt)) as ((HChL & HChR) & HChS);
        rewrite -HChR rmarg_pmf //=].
       }
      rewrite fubini_pos_seriesC_prod_rl; auto.
      2:{simpl; intros; apply Rmult_le_pos; auto. }
      2:{apply (ex_seriesC_le _ μ); auto.
         intros; split; [apply Rmult_le_pos; auto | ].
         rewrite <- Rmult_1_r; apply Rmult_le_compat; auto.
         apply Rle_refl.
      }
      erewrite (SeriesC_ext _ (λ b, SeriesC (λ a : A, μ (a, b) ) * g b b'));
      [ | intro b; simpl; apply SeriesC_scal_r].
      erewrite (SeriesC_ext _ (λ b, (μ2 b) * g b b')); auto.
      intro b.
      destruct HμC as (Hμ1 & Hμ2).
      rewrite <- Hμ2;
      rewrite rmarg_pmf; auto.
    + intros (a' & b') H3; simpl.
      pose proof (dbind_pos Ch μ (a', b')) as (H4 & H5).
      specialize (H4 H3) as ((a0, b0) & H7 & H8).
      specialize (HCh (a0, b0) (HμS (a0, b0) H8)) as (HCh1 & HCh2).
      specialize (HCh2 (a', b') H7).
      done.
  Qed.
*)

  Lemma Rcoupl_eq_elim (μ1 μ2 : distr A) :
    Rcoupl μ1 μ2 (=) → forall a, μ1 a <= μ2 a.
  Proof.
    intros Hcoupl a.
    rewrite /Rcoupl in Hcoupl.
    rewrite -(SeriesC_singleton a (μ1 a)).
    rewrite -(SeriesC_singleton a (μ2 a)).
    assert (SeriesC (λ n : A, if bool_decide (n = a) then μ1 a else 0)
           = SeriesC (λ n : A, μ1 n * (if bool_decide (n = a) then 1 else 0))) as ->.
    {
      apply SeriesC_ext; real_solver.
    }
    assert (SeriesC (λ n : A, if bool_decide (n = a) then μ2 a else 0)
           = SeriesC (λ n : A, μ2 n * (if bool_decide (n = a) then 1 else 0))) as ->.
    {
      apply SeriesC_ext; real_solver.
    }
    apply Hcoupl; real_solver.
  Qed.

  (*
  Lemma Rcoupl_eq_sym (μ1 μ2: distr A) :
    Rcoupl μ1 μ2 eq → Rcoupl μ2 μ1 eq.
  Proof.
    intros Hc.
    apply Rcoupl_eq_elim in Hc as ->; auto.
    apply Rcoupl_eq.
  Qed.

  Lemma Rcoupl_eq_trans (μ1 μ2 μ3 : distr A) :
    Rcoupl μ1 μ2 eq → Rcoupl μ2 μ3 eq → Rcoupl μ1 μ3 eq.
  Proof. by intros ->%Rcoupl_eq_elim ?. Qed.

  Lemma Rcoupl_weaken (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) (S : A → B → Prop):
    Rcoupl μ1 μ2 R → (∀ a b, R a b -> S a b) → Rcoupl μ1 μ2 S.
  Proof.
    intros [μ [[HμL HμR] HμSupp]] Hwk.
    exists μ; split; [split | ]; auto.
  Qed.
  Definition Rcoupl_impl μ1 μ2 R S H RC := Rcoupl_weaken μ1 μ2 R S RC H.

  Lemma Rcoupl_inhabited_l (μ1 : distr A) (μ2 : distr B) R :
    Rcoupl μ1 μ2 R →
    SeriesC μ1 > 0 →
    ∃ a b, R a b.
  Proof.
    intros [μ [Hcpl HR]] Hz.
    assert (SeriesC μ > 0) as Hsup by by erewrite isCoupl_mass_l.
    apply SeriesC_gtz_ex in Hsup as [[a b] Hμ]; [|done].
    eauto.
  Qed.

  Lemma Rcoupl_inhabited_r (μ1 : distr A) (μ2 : distr B) R :
    Rcoupl μ1 μ2 R →
    SeriesC μ2 > 0 →
    ∃ a b, R a b.
  Proof.
    intros [μ [Hcpl HR]] Hz.
    assert (SeriesC μ > 0) as Hsup by by erewrite isCoupl_mass_r.
    apply SeriesC_gtz_ex in Hsup as [[a b] Hμ]; [|done].
    eauto.
  Qed.
 *)

End couplings_theory.

(* TODO: cleanup *)
Section Rcoupl.
  Context `{Countable A, Countable B}.
  Variable (μ1 : distr A) (μ2 : distr B).

  Lemma Rcoupl_trivial :
    SeriesC μ1 = 1 ->
    SeriesC μ2 = 1 ->
    Rcoupl μ1 μ2 (λ _ _, True).
  Proof.
    intros Hμ1 Hμ2 f g Hf Hg Hfg.
    destruct (LubC_correct f) as [H1 H2].
    destruct (GlbC_correct g) as [H3 H4].
    apply (Rle_trans _ (SeriesC (λ a : A, μ1 a * (real (LubC f))))).
    {
      apply SeriesC_le'; auto.
      - intro a.
        apply Rmult_le_compat_l; auto.
        apply rbar_le_finite; auto.
        apply (Rbar_le_sandwich (f a) 1); auto.
        apply H2; auto.
        intro; apply Hf.
      - apply (ex_seriesC_le _ μ1); auto.
        intro a; specialize (Hf a); real_solver.
      - apply ex_seriesC_scal_r; auto.
    }
    rewrite SeriesC_scal_r Hμ1 -Hμ2 -SeriesC_scal_r.
    apply (Rle_trans _ (SeriesC (λ b : B, μ2 b * (real (GlbC g))))).
    {
      (* We step form LubC f to Glb here because it is easier if
         we have an inhabitant of B *)
      apply SeriesC_le'; auto.
      - intro b.
        apply Rmult_le_compat_l; auto.
        apply rbar_le_finite; auto.
        + apply (Rbar_le_sandwich 0 (g b)); auto.
          apply H4; auto.
          apply Hg.
        + apply H4.
          intro b'.
          destruct (LubC f) eqn:Hlub.
          * rewrite <- Hlub; simpl.
            apply finite_rbar_le; auto.
            { apply is_finite_correct; eauto. }
            rewrite Hlub.
            apply H2; intro.
            apply Hfg; auto.
          * apply Hg.
          * apply Hg.
      - apply ex_seriesC_scal_r; auto.
      - apply ex_seriesC_scal_r; auto.
    }
    apply SeriesC_le'; auto.
    - intro b.
      apply Rmult_le_compat_l; auto.
      apply finite_rbar_le.
      + apply (Rbar_le_sandwich 0 (g b)); auto.
        apply H4.
        apply Hg.
      + apply H3.
    - apply ex_seriesC_scal_r; auto.
    - apply (ex_seriesC_le _ μ2); auto.
      intro b; specialize (Hg b); real_solver.
  Qed.

  Lemma Rcoupl_pos_R R :
    Rcoupl μ1 μ2 R → Rcoupl μ1 μ2 (λ a b, R a b ∧ μ1 a > 0 ∧ μ2 b > 0).
  Proof.
    intros Hμ1μ2 f g Hf Hg Hfg.
    assert (SeriesC (λ a : A, μ1 a * f a) =
           SeriesC (λ a : A, μ1 a * (if bool_decide (μ1 a > 0) then f a else 0))) as ->.
    { apply SeriesC_ext; intro a.
      case_bool_decide; auto.
      assert (0 <= μ1 a); auto.
      assert (μ1 a = 0); nra.
    }
    assert (SeriesC (λ b : B, μ2 b * g b) =
           SeriesC (λ b : B, μ2 b * (if bool_decide (μ2 b > 0) then g b else 1))) as ->.
    { apply SeriesC_ext; intro b.
      case_bool_decide; auto.
      assert (0 <= μ2 b); auto.
      assert (μ2 b = 0); nra.
    }
    apply Hμ1μ2; auto.
    - intro a; specialize (Hf a); real_solver.
    - intro b; specialize (Hg b); real_solver.
    - intros a b Rab.
      specialize (Hf a).
      specialize (Hg b).
      specialize (Hfg a b).
      real_solver.
  Qed.

End Rcoupl.

Lemma Rcoupl_dzero_dzero `{Countable A, Countable B} (R : A → B → Prop) :
  Rcoupl dzero dzero R.
Proof.
  intros f g Hf Hg HR.
  rewrite /pmf/=.
  do 2 rewrite SeriesC_scal_l; lra.
Qed.

Lemma Rcoupl_dzero_r_inv `{Countable A, Countable B} μ1 (R : A → B → Prop) :
  Rcoupl μ1 dzero R → μ1 = dzero.
Proof.
  intros Hz%Rcoupl_mass_leq.
  apply SeriesC_zero_dzero.
  rewrite dzero_mass in Hz.
  assert (0 <= SeriesC μ1); auto.
  lra.
Qed.

(*
Lemma Rcoupl_dzero_l_inv `{Countable A, Countable B} μ2 (R : A → B → Prop) :
  Rcoupl dzero μ2 R → μ2 = dzero.
Proof.
  intros Hz%Rcoupl_mass_eq.
  apply SeriesC_zero_dzero.
  rewrite -Hz SeriesC_0 //.
Qed.
*)

Lemma Rcoupl_map `{Countable A, Countable B, Countable A', Countable B'}
  (f : A → A') (g : B → B') (μ1 : distr A) (μ2 : distr B) (R : A' → B' → Prop) :
  Rcoupl μ1 μ2 (λ a a', R (f a) (g a')) → Rcoupl (dmap f μ1) (dmap g μ2) R.
Proof.
  intros Hcoupl. rewrite /dmap.
  eapply (Rcoupl_dbind _ _ _ _ (λ (a : A) (a' : B), R (f a) (g a'))); auto.
  intros a b Hab.
  apply (Rcoupl_dret (f a) (g b) R Hab).
Qed.

(* I think this should be true, maybe it can be proven through Strassens theorem, but
  I don't see how to do it directly *)
(*
  Lemma Rcoupl_from_mapL `{Countable A, Countable B, Countable A', Countable B'}:
    forall (f : A → A') (μ1 : distr A) (μ2 : distr B) (R : A' → B → Prop),
      Rcoupl (dmap f μ1) μ2 R -> Rcoupl μ1 μ2 (λ a b, R (f a) b).
  Proof.
    intros f μ1 μ2 R (μ & ((HμL & HμR) & HμSup)).
    eexists (dprod μ1 μ2).
    split; [split | ].

    eexists (MkDistr (λ '(a, b), μ (f a , g b)) _ _ _).

  Qed.
 *)

(* TODO: move somewhere else *)
Definition f_inv {A B} f `{Surj A B (=) f} : B → A := λ b, epsilon (surj f b).

Lemma f_inv_cancel_r {A B} f `{Surj A B (=) f} b :
  f (f_inv f b) = b.
Proof. rewrite /f_inv /= (epsilon_correct _ (surj f b)) //. Qed.

Lemma f_inv_cancel_l {A B} f `{Inj A B (=) (=) f, Surj A B (=) f} b :
  f_inv f (f b) = b.
Proof. apply (inj f), (epsilon_correct _ (surj f (f b))). Qed.

Lemma Rcoupl_dunif (N : nat) f `{Bij (fin N) (fin N) f} :
  Rcoupl (dunif N) (dunif N) (λ n m, m = f n).
Proof.
  intros g h Hg Hh Hgh.
  (* This proog requires a lemma for rearranging the SeriesC:
     SeriesC (λ a : fin N, dunif N a * g a) = SeriesC (λ a : fin N, dunif N (f a) * g (f a))
  *)
Admitted.

Lemma Rcoupl_dunif_leq (N M : nat):
  (N <= M) -> Rcoupl (dunif N) (dunif M) (λ n m, n <= m).
Proof.
Admitted.


(* Lemma Rcoupl_fair_conv_comb `{Countable A, Countable B} *)
(*   f `{Inj bool bool (=) (=) f, Surj bool bool (=) f} *)
(*   (S : A → B → Prop) (μ1 μ2 : distr A) (μ1' μ2' : distr B) : *)
(*   (∀ a, Rcoupl (if f a then μ1 else μ2) (if a then μ1' else μ2') S) → *)
(*   Rcoupl (fair_conv_comb μ1 μ2) (fair_conv_comb μ1' μ2') S. *)
(* Proof. *)
(*   intros HS. rewrite /fair_conv_comb. *)
(*   eapply Rcoupl_dbind; [|apply (Rcoupl_fair_coin f)]. *)
(*   simpl. intros a b ->. *)
(*   done. *)
(* Qed. *)

(* Lemma Rcoupl_fair_conv_comb_id `{Countable A, Countable B} (S : A → B → Prop) *)
(*   (μ1 μ2 : distr A) (μ1' μ2' : distr B) : *)
(*   Rcoupl μ1 μ1' S → *)
(*   Rcoupl μ2 μ2' S → *)
(*   Rcoupl (fair_conv_comb μ1 μ2) (fair_conv_comb μ1' μ2') S. *)
(* Proof. *)
(*   intros HS1 HS2. *)
(*   eapply (Rcoupl_fair_conv_comb id). *)
(*   intros []; (eapply Rcoupl_impl; [|done]); eauto. *)
(* Qed. *)

(* Lemma Rcoupl_fair_conv_comb_neg `{Countable A, Countable B} (S : A → B → Prop) *)
(*   (μ1 μ2 : distr A) (μ1' μ2' : distr B) : *)
(*   Rcoupl μ1 μ2' S → *)
(*   Rcoupl μ2 μ1' S → *)
(*   Rcoupl (fair_conv_comb μ1 μ2) (fair_conv_comb μ1' μ2') S. *)
(* Proof. *)
(*   intros HS1 HS2. *)
(*   eapply (Rcoupl_fair_conv_comb negb). *)
(*   intros []; (eapply Rcoupl_impl; [|done]); eauto. *)
(* Qed. *)

(* This is a lemma about convex combinations, but it is easier to prove with couplings
     TODO: find a better place to put it in *)
(* Lemma fair_conv_comb_dbind `{Countable A, Countable B} (μ1 μ2 : distr A) (f : A -> distr B) : *)
(*   dbind f (fair_conv_comb μ1 μ2) = fair_conv_comb (dbind f μ1) (dbind f μ2). *)
(* Proof. *)
(*   rewrite /fair_conv_comb -dbind_assoc. *)
(*   apply Rcoupl_eq_elim. *)
(*   eapply (Rcoupl_dbind _ _ _ _ (=)); [ | apply Rcoupl_eq]. *)
(*   intros b1 b2 ->. *)
(*   destruct b2; apply Rcoupl_eq. *)
(* Qed. *)


Section Rcoupl_strength.
  Context `{Countable A, Countable B, Countable D, Countable E}.

  Variable (μ1 : distr A) (μ2 : distr B).

  Lemma Rcoupl_strength_l (R : A → B → Prop) (d : D)  :
    Rcoupl μ1 μ2 R →
    Rcoupl (strength_l d μ1) μ2 (λ '(d', a) b, d' = d ∧ R a b).
  Proof.
    rewrite /strength_l /dmap.
    intros Hcpl.
    rewrite -(dret_id_right μ2).
    eapply Rcoupl_dbind; [|done].
    intros. by apply Rcoupl_dret.
  Qed.

  Lemma Rcoupl_strength (R : A → B → Prop) (d : D) (e : E) :
    Rcoupl μ1 μ2 R →
    Rcoupl (strength_l d μ1) (strength_l e μ2)
      (λ '(d', a) '(e', b), d' = d ∧ e' = e ∧ R a b).
  Proof.
    rewrite /strength_l /dmap.
    eapply Rcoupl_dbind.
    intros. by apply Rcoupl_dret.
  Qed.

End Rcoupl_strength.

Section ref_couplings_theory.
  Context `{Countable A, Countable B}.

  Lemma Rcoupl_from_leq (μ1 μ2 : distr A) :
    (∀ a, μ1 a <= μ2 a) -> Rcoupl μ1 μ2 (=).
  Proof.
    intros Hleq f g Hf Hg Hfg.
    apply SeriesC_le; last first.
    { apply (ex_seriesC_le _ μ2); auto.
      intro a; specialize (Hg a); real_solver.
    }
    intro a.
    specialize (Hf a);
    specialize (Hg a);
    specialize (Hfg a).
    real_solver.
  Qed.

  Lemma Rcoupl_eq_trans (μ1 μ2 μ3 : distr A):
    Rcoupl μ1 μ2 (=) → Rcoupl μ2 μ3 (=) → Rcoupl μ1 μ3 (=).
  Proof.
    intros H12 H23 f g Hf Hg Hfg.
    eapply (Rle_trans); [eapply H12 | eapply H23]; eauto.
    intros ??->; lra.
  Qed.

  Lemma Rcoupl_eq_Rcoupl_unfoldl (μ1 μ2 μ3 : distr A) R :
    Rcoupl μ1 μ2 (=) → Rcoupl μ2 μ3 R → Rcoupl μ1 μ3 R.
  Proof.
    intros H12 H23 f g Hf Hg Hfg.
    apply (Rle_trans _ (SeriesC (λ a : A, μ2 a * f a))); [apply H12 | apply H23]; auto.
    intros ??->; lra.
  Qed.

  Lemma refRcoupl_eq_refRcoupl_unfoldr (μ1 μ2 μ3 : distr A) R :
    Rcoupl μ1 μ2 R → Rcoupl μ2 μ3 (=) → Rcoupl μ1 μ3 R.
  Proof.
    intros H12 H23 f g Hf Hg Hfg.
    apply (Rle_trans _ (SeriesC (λ a : A, μ2 a * g a))); [apply H12 | apply H23]; auto.
    intros ??->; lra.
  Qed.

  Lemma Rcoupl_weaken (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) (S : A → B → Prop):
      (∀ a b, R a b -> S a b) → Rcoupl μ1 μ2 R → Rcoupl μ1 μ2 S.
  Proof.
    intros Hwk H12 f g Hf Hg Hfg.
    apply H12; auto.
  Qed.

End ref_couplings_theory.

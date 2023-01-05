From Coq Require Import Reals Psatz.
From Coq.ssr Require Import ssreflect ssrfun.
From Coquelicot Require Import Rcomplements Rbar Series Lim_seq Hierarchy.
From stdpp Require Export countable.
From self.prelude Require Export base Coquelicot_ext Reals_ext.
From self.prob Require Export countable_sum double distribution.

Open Scope R.

Section couplings.
  Context `{Countable A, Countable B, Countable A', Countable B'}.
  Context (μ1 : distr A) (μ2 : distr B) (R : A -> B -> Prop) (S : A' → B' → Prop).

  Definition isCoupl (μ : distr (A * B)) : Prop :=
    lmarg μ = μ1 ∧ rmarg μ = μ2.

  Definition coupl :=
    ∃ (μ : distr (A * B)), isCoupl μ.

  Definition isRcoupl (μ : distr (A * B)) : Prop :=
    isCoupl μ ∧ (∀ (p : A * B), (μ p > 0) -> R (fst p) (snd p)).

  Definition Rcoupl :=
    ∃ (μ : distr (A * B)), isRcoupl μ.

  Lemma isRcoupl_isCoupl μ : isRcoupl μ -> isCoupl μ.
  Proof.
    intro C; destruct C; auto.
  Qed.

  Lemma isCoupl_mass_l μ : isCoupl μ -> SeriesC μ = SeriesC μ1.
  Proof.
    intro Hμ.
    destruct Hμ as (Hμl & Hμr).
    rewrite <- Hμl.
    rewrite /lmarg.
    rewrite <- dmap_mass.
    auto.
  Qed.

  Lemma isCoupl_mass_r μ : isCoupl μ -> SeriesC μ = SeriesC μ2.
  Proof.
    intro Hμ.
    destruct Hμ as (Hμl & Hμr).
    rewrite <- Hμr.
    rewrite /rmarg.
    rewrite <- dmap_mass.
    auto.
  Qed.

  Lemma isCoupl_mass_eq μ : isCoupl μ -> SeriesC μ1 = SeriesC μ2.
  Proof.
    intro Hμ.
    rewrite <- (isCoupl_mass_l μ); auto.
    rewrite <- (isCoupl_mass_r μ); auto.
  Qed.

End couplings.

Section couplings_theory.
  Context `{Countable A, Countable B, Countable A', Countable B'}.

  Lemma isCoupl_dret (a : A) (b : B) :
    isCoupl (dret a) (dret b) (dret (a, b)).
  Proof.
    split; [rewrite /lmarg dmap_dret // |rewrite /rmarg dmap_dret //].
  Qed.

  Lemma coupl_dret (a : A) (b : B) :
    coupl (dret a) (dret b).
  Proof.
    exists (dret (a, b)).
    apply isCoupl_dret.
  Qed.

  Lemma isRcoupl_dret (a : A) (b : B) (R : A → B → Prop) :
    R a b → isRcoupl (dret a) (dret b) R (dret (a, b)).
  Proof.
    split; [apply isCoupl_dret |].
    intro p.
    rewrite /pmf /= /dret_pmf /=.
    case_bool_decide as Hp; [rewrite Hp //| lra].
  Qed.

  Lemma Rcoupl_dret (a : A) (b : B) (R : A → B → Prop) :
    R a b → Rcoupl (dret a) (dret b) R.
  Proof.
    exists (dret (a, b)).
    apply isRcoupl_dret.
    auto.
  Qed.

  Lemma Rcoupl_mass_eq (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) :
    Rcoupl μ1 μ2 R → SeriesC μ1 = SeriesC μ2.
  Proof. intros (?&?&?). by eapply isCoupl_mass_eq. Qed.

  (* Lemma isCoupl_dret_inv (a : A) (b : B) (μ : distr (A*B)) : *)
  (*   isCoupl (dret a) (dret b) μ -> μ = dret ( (a,b)). *)
  (* Proof. *)

  (* Lemma Rcoupl_dret_inv (a : A) (b : B) (R : A → B → Prop) : *)
  (*   Rcoupl (dret a) (dret b) R -> R a b. *)
  (* Proof. *)
  (*   intros (μ & (HμC & HμS)). *)
  (*   apply (isCoupl_dret_inv a b) in HμC. *)
  (*   apply (HμS (a, b)). *)
  (*   rewrite HμC. *)
  (*   rewrite /pmf/=/dret_pmf. *)
  (*   case_bool_decide; simplify_eq; auto. lra. *)
  (* Qed. *)

  Lemma Rcoupl_eq (μ1 : distr A) :
    Rcoupl μ1 μ1 (=).
  Proof.
    exists (ddiag μ1); split; [split | ].
    + apply distr_ext.
      intro a.
      rewrite lmarg_pmf.
      rewrite {1}/pmf/=/dbind_pmf/=.
      rewrite SeriesC_singleton'; auto.
    + apply distr_ext.
      intro a.
      rewrite rmarg_pmf.
      rewrite {1}/pmf/=/dbind_pmf/=.
      (* TODO: Need lemma to rewrite these singletons *)
      rewrite (SeriesC_ext _ (λ a0 : A, if bool_decide (a0 = a) then μ1 a else 0));
      [rewrite SeriesC_singleton; auto | ].
      intro a'; case_bool_decide; simplify_eq; auto.
    + intros (a1 & a2) Hpos; simpl.
      rewrite /pmf/= in Hpos.
      case_bool_decide; simplify_eq; auto; lra.
  Qed.

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
      simpl.
      unfold dbind_pmf.
      rewrite (SeriesC_double_swap (λ '(b, a), μ a * Ch a (a', b))).
      assert (∀ b, SeriesC (λ a : B', μ b * Ch b (a', a)) = μ b * SeriesC (λ a : B', Ch b (a', a))) as Heq1.
      {
        intro b; apply SeriesC_scal_l.
      }
      rewrite (SeriesC_ext _ _ Heq1).
      assert (∀ p , μ p * SeriesC (λ b' : B', Ch p (a', b')) = μ p * f p.1 a') as Heq2.
      { intros (a & b).
        specialize (HCh (a, b)) as (HChL & HChR).
        rewrite <- HChL.
        rewrite lmarg_pmf.
        auto.
      }
      rewrite (SeriesC_ext _ _ Heq2).
      rewrite SeriesC_double_prod_lr.
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
      simpl.
      unfold dbind_pmf.
      rewrite (SeriesC_double_swap (λ '(a, a0), μ a0 * Ch a0 (a, b'))).
      assert (∀ p, SeriesC (λ a : A', μ p * Ch p (a, b')) = μ p * SeriesC (λ a : A', Ch p (a, b'))) as Heq1.
      {
        intro p; apply SeriesC_scal_l.
      }
      rewrite (SeriesC_ext _ _ Heq1).
      assert (∀ p , μ p * SeriesC (λ a' : A', Ch p (a', b')) = μ p * g p.2 b') as Heq2.
      { intros (a & b).
        specialize (HCh (a, b)) as (HChL & HChR).
        rewrite <- HChR.
        rewrite rmarg_pmf.
        auto.
      }
      rewrite (SeriesC_ext _ _ Heq2).
      rewrite SeriesC_double_prod_rl.
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
      rewrite lmarg_pmf /= /dbind_pmf
       (SeriesC_double_swap (λ '(b, a), μ a * Ch a (a', b))).
      erewrite (SeriesC_ext _ (λ b, μ b * SeriesC (λ a : B', Ch b (a', a))) );
      [ | intro p; apply SeriesC_scal_l].
      erewrite (SeriesC_ext _ (λ p, μ p * f p.1 a')); last first.
      { intros (a & b).
        destruct (Rtotal_order (μ (a, b)) 0) as [Hlt | [Heqz | Hgt]].
        - pose proof (pmf_pos μ (a, b)); lra.
        - rewrite Heqz; lra.
        - specialize (HCh (a, b) (HμS (a, b) Hgt )) as ((HChL & HChR) & HChS).
          rewrite -HChL lmarg_pmf //=. }
      rewrite SeriesC_double_prod_lr.
      erewrite (SeriesC_ext _ (λ a, SeriesC (λ b : B, μ (a, b) ) * f a a'));
      [ | intro a; simpl; apply SeriesC_scal_r ].
      erewrite (SeriesC_ext _ (λ a, (μ1 a) * f a a')); auto.
      intro a.
      destruct HμC as (Hμ1 & Hμ2).
      rewrite <- Hμ1;
      rewrite lmarg_pmf; auto.
    (* The second half is esentially the same as the first, can it be proven somehow by symmetry? *)
    + apply distr_ext; intro b'.
      rewrite rmarg_pmf /= /dbind_pmf
      (SeriesC_double_swap (λ '(a, a0), μ a0 * Ch a0 (a, b'))).
      erewrite (SeriesC_ext _ (λ b, μ b * SeriesC (λ a : A', Ch b (a, b'))) );
      [ | intro p; apply SeriesC_scal_l].
      erewrite (SeriesC_ext _ (λ p, μ p * g p.2 b')); last first.
      {intros (a & b);
        destruct (Rtotal_order (μ (a, b)) 0) as [Hlt | [Heqz | Hgt]];
        [ pose proof (pmf_pos μ (a, b)); lra | rewrite Heqz; lra |
        specialize (HCh (a, b) (HμS (a, b) Hgt)) as ((HChL & HChR) & HChS);
        rewrite -HChR rmarg_pmf //=].
       }
      rewrite SeriesC_double_prod_rl.
      erewrite (SeriesC_ext _ (λ b, SeriesC (λ a : A, μ (a, b) ) * g b b'));
      [ | intro b; simpl; apply SeriesC_scal_r].
      erewrite (SeriesC_ext _ (λ b, (μ2 b) * g b b')); auto.
      intro b.
      destruct HμC as (Hμ1 & Hμ2).
      rewrite <- Hμ2;
      rewrite rmarg_pmf; auto.
    + intros (a' & b') H3; simpl.
      pose proof (dbind_pos_support Ch μ (a', b')) as (H4 & H5).
      specialize (H4 H3) as ((a0, b0) & H7 & H8).
      specialize (HCh (a0, b0) (HμS (a0, b0) H8)) as (HCh1 & HCh2).
      specialize (HCh2 (a', b') H7).
      done.
  Qed.

  Lemma Rcoupl_eq_elim (μ1 μ2 : distr A) :
    Rcoupl μ1 μ2 (=) → μ1 = μ2.
  Proof.
    intros (μ & (HμL & HμR) & HμS).
    rewrite <- HμL, <- HμR.
    apply distr_ext.
    intro a1.
    rewrite lmarg_pmf rmarg_pmf.
    apply SeriesC_ext.
    intro a2.
    specialize (HμS (a1, a2)) as HμS12.
    specialize (HμS (a2, a1)) as HμS21.
    simpl in HμS12.
    simpl in HμS21.
    pose proof (Rtotal_order (μ (a1, a2)) (μ (a2, a1))) as [Hlt | [Heq | Hgt]]; auto.
    + pose proof (pmf_pos μ (a1, a2)).
      assert (μ (a2, a1) > 0) as H'; try lra.
      specialize (HμS21 H'); destruct HμS21; auto.
    + pose proof (pmf_pos μ (a2, a1)).
      assert (μ (a1, a2) > 0) as H'; try lra.
      specialize (HμS12 H'); destruct HμS12; auto.
  Qed.

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
    (∀ a b, R a b -> S a b) → Rcoupl μ1 μ2 R → Rcoupl μ1 μ2 S.
  Proof.
    intros Hwk [μ [[HμL HμR] HμSupp]].
    exists μ; split; [split | ]; auto.
  Qed.

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
    intros Hμ1 Hμ2.
    exists (dprod μ1 μ2). split; [|done].
    split; [apply lmarg_dprod|apply rmarg_dprod]; done.
  Qed.

  Lemma Rcoupl_pos_R R :
    Rcoupl μ1 μ2 R → Rcoupl μ1 μ2 (λ a b, R a b ∧ μ1 a > 0 ∧ μ2 b > 0).
  Proof.
    intros [μ [[Hμ1 Hμ2] HR]].
    exists μ. split; [done|].
    intros [a b] Hρ. split; [auto|].
    rewrite -Hμ1 -Hμ2.
    rewrite 2!dmap_pos.
    split; eauto.
  Qed.

  Lemma Rcoupl_impl (R T : A → B → Prop) :
    (∀ a b, T a b → R a b) →
    Rcoupl μ1 μ2 T →
    Rcoupl μ1 μ2 R.
  Proof.
    intros Himpl [μ [Hcpl HT]].
    eexists μ. split; [done|].
    intros ? ?%HT. eauto.
  Qed.

End Rcoupl.

Lemma Rcoupl_dzero_r_inv `{Countable A, Countable B} μ1 (R : A → B → Prop) :
  Rcoupl μ1 dzero R → μ1 = dzero.
Proof.
  intros Hz%Rcoupl_mass_eq.
  apply SeriesC_zero_dzero.
  rewrite Hz SeriesC_0 //.
Qed.

Lemma Rcoupl_dzero_l_inv `{Countable A, Countable B} μ2 (R : A → B → Prop) :
  Rcoupl dzero μ2 R → μ2 = dzero.
Proof.
  intros Hz%Rcoupl_mass_eq.
  apply SeriesC_zero_dzero.
  rewrite -Hz SeriesC_0 //.
Qed.

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

Lemma Rcoupl_fair_coin f `{Inj bool bool (=) (=) f, Surj bool bool (=) f} :
  Rcoupl fair_coin fair_coin (λ b b', b = f b').
Proof.
  exists (fair_coins f). repeat split.
  - eapply distr_ext=> b.
    rewrite lmarg_pmf /pmf /= /fair_coins_pmf /fair_coin_pmf /=.
    rewrite (SeriesC_ext _ (λ b', if bool_decide (b' = f_inv f b) then 0.5 else 0)).
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

Lemma Rcoupl_fair_conv_comb `{Countable A, Countable B}
  f `{Inj bool bool (=) (=) f, Surj bool bool (=) f}
  (S : A → B → Prop) (μ1 μ2 : distr A) (μ1' μ2' : distr B) :
  (∀ a, Rcoupl (if f a then μ1 else μ2) (if a then μ1' else μ2') S) →
  Rcoupl (fair_conv_comb μ1 μ2) (fair_conv_comb μ1' μ2') S.
Proof.
  intros HS. rewrite /fair_conv_comb.
  eapply Rcoupl_dbind; [|apply (Rcoupl_fair_coin f)].
  simpl. intros a b ->.
  done.
Qed.

Lemma Rcoupl_fair_conv_comb_id `{Countable A, Countable B} (S : A → B → Prop)
  (μ1 μ2 : distr A) (μ1' μ2' : distr B) :
  Rcoupl μ1 μ1' S →
  Rcoupl μ2 μ2' S →
  Rcoupl (fair_conv_comb μ1 μ2) (fair_conv_comb μ1' μ2') S.
Proof.
  intros HS1 HS2.
  eapply (Rcoupl_fair_conv_comb id).
  intros []; (eapply Rcoupl_impl; [|done]); eauto.
Qed.

Lemma Rcoupl_fair_conv_comb_neg `{Countable A, Countable B} (S : A → B → Prop)
  (μ1 μ2 : distr A) (μ1' μ2' : distr B) :
  Rcoupl μ1 μ2' S →
  Rcoupl μ2 μ1' S →
  Rcoupl (fair_conv_comb μ1 μ2) (fair_conv_comb μ1' μ2') S.
Proof.
  intros HS1 HS2.
  eapply (Rcoupl_fair_conv_comb negb).
  intros []; (eapply Rcoupl_impl; [|done]); eauto.
Qed.

(* This is a lemma about convex combinations, but it is easier to prove with couplings
     TODO: find a better place to put it in *)
Lemma fair_conv_comb_dbind `{Countable A, Countable B} (μ1 μ2 : distr A) (f : A -> distr B) :
  dbind f (fair_conv_comb μ1 μ2) = fair_conv_comb (dbind f μ1) (dbind f μ2).
Proof.
  rewrite /fair_conv_comb -dbind_assoc.
  apply Rcoupl_eq_elim.
  eapply (Rcoupl_dbind _ _ _ _ (=)); [ | apply Rcoupl_eq].
  intros b1 b2 ->.
  destruct b2; apply Rcoupl_eq.
Qed.

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

Section refinement_couplings.
  Context `{Countable A, Countable B, Countable A', Countable B'}.
  Context (μ1 : distr A) (μ2 : distr B) (R : A -> B -> Prop) (S : A' → B' → Prop).

  Definition isRefCoupl (μ : distr (A * B)) : Prop :=
    lmarg μ = μ1 /\ (∀ (b : B), rmarg μ b <= μ2 b).

  Definition refCoupl :=
    ∃ (μ : distr (A * B)), isRefCoupl μ.

  Definition isRefRcoupl (μ : distr (A * B)) : Prop :=
    isRefCoupl μ ∧ (forall (p : A * B), (μ p > 0) -> R (fst p) (snd p)).

  Definition refRcoupl :=
    ∃ (μ : distr (A * B)), isRefRcoupl μ.


  Lemma isRefCoupl_mass_l μ : isRefCoupl μ -> SeriesC μ = SeriesC μ1.
  Proof.
    intro Hμ.
    destruct Hμ as (Hμl & Hμr).
    rewrite <- Hμl.
    rewrite /lmarg.
    rewrite <- dmap_mass.
    auto.
  Qed.

  Lemma isRefCoupl_mass_r μ : isRefCoupl μ -> SeriesC μ <= SeriesC μ2.
  Proof.
    intro Hμ.
    destruct Hμ as (Hμl & Hμr).
    rewrite (dmap_mass μ snd).
    apply SeriesC_le; auto.
  Qed.

  Lemma isRefCoupl_mass_eq μ : isRefCoupl μ -> SeriesC μ1 <= SeriesC μ2.
  Proof.
    intro Hμ.
    rewrite <- (isRefCoupl_mass_l μ); auto.
    apply (isRefCoupl_mass_r μ); auto.
  Qed.

End refinement_couplings.

Section ref_couplings_theory.

Context `{Countable A, Countable B}.


  Lemma refRcoupl_mass_eq (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) :
    refRcoupl μ1 μ2 R → SeriesC μ1 <= SeriesC μ2.
  Proof. intros (?&?&?). by eapply isRefCoupl_mass_eq. Qed.



  Lemma refRcoupl_eq_elim (μ1 μ2 : distr A) :
    refRcoupl μ1 μ2 (=) → (∀ a, μ1 a <= μ2 a).
  Proof.
    intros (μ & (HμL & HμR) & HμS) a.
    eapply (Rle_Transitive _ (rmarg μ a) _); auto.
    rewrite <- HμL.
    rewrite lmarg_pmf rmarg_pmf.
    eapply SeriesC_le.
    { intro .  specialize (HμS (a,n)). simpl in HμS.
      destruct (Rtotal_order (μ (a,n)) 0) as [? | [? | H3]];
      [ pose proof (pmf_pos μ (a, n)); lra |
       pose proof (pmf_pos μ (n, a)); lra |
      pose proof (HμS H3); simplify_eq; lra ].
    }
    apply ex_seriesC_rmarg.
  Qed.

  Lemma refRcoupl_from_leq (μ1 μ2 : distr A) :
    (∀ a, μ1 a <= μ2 a) -> refRcoupl μ1 μ2 (=).
  Proof.
    intro Hleq.
    exists (ddiag μ1). split;[ split  | ].
    + apply distr_ext; intro a.
      rewrite lmarg_pmf {2}/pmf/=.
      rewrite SeriesC_singleton'; auto.
    + intro a.
      rewrite ddiag_rmarg.
      auto.
    + intros p Hp.
      rewrite ddiag_pmf in Hp.
      case_bool_decide; auto; lra.
  Qed.


  Lemma refRcoupl_eq_refl (μ1 : distr A):
    refRcoupl μ1 μ1 (=).
  Proof.
    apply refRcoupl_from_leq.
    intro a.
    apply Rle_refl.
  Qed.

  Lemma refRcoupl_eq_trans (μ1 μ2 μ3 : distr A):
    refRcoupl μ1 μ2 (=) → refRcoupl μ2 μ3 (=) → refRcoupl μ1 μ3 (=).
  Proof.
    intros H12 H23.
    pose proof (refRcoupl_eq_elim _ _ H12) as H12'.
    pose proof (refRcoupl_eq_elim _ _ H23) as H23'.
    apply refRcoupl_from_leq.
    intros; eapply Rle_trans; eauto.
  Qed.

  Lemma refRcoupl_eq_refRcoupl_unfoldl (μ1 μ2 μ3 : distr A) R :
    Rcoupl μ1 μ2 (=) → refRcoupl μ2 μ3 R → refRcoupl μ1 μ3 R.
  Proof. by intros ->%Rcoupl_eq_elim ?. Qed.

  Lemma refRcoupl_eq_refRcoupl_unfoldr (μ1 μ2 μ3 : distr A) R :
    refRcoupl μ1 μ2 R → Rcoupl μ2 μ3 (=) → refRcoupl μ1 μ3 R.
  Proof. by intros ? <-%Rcoupl_eq_elim. Qed.

  Lemma isRefCoupl_dret (a : A) (b : B) :
    isRefCoupl (dret a) (dret b) (dret (a, b)).
  Proof.
    split; [rewrite /lmarg dmap_dret // | rewrite /rmarg dmap_dret //].
  Qed.

  Lemma refCoupl_dret (a : A) (b : B) :
    refCoupl (dret a) (dret b).
  Proof.
    exists (dret (a, b)).
    apply isRefCoupl_dret.
  Qed.

  Lemma Rcoupl_refRcoupl (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) :
    Rcoupl μ1 μ2 R → refRcoupl μ1 μ2 R.
  Proof.
    rewrite /refRcoupl /Rcoupl.
    intros (μ & ((HμL & HμR) & HμSupp)).
    exists μ.
    split; auto.
    split; auto.
    intro.
    rewrite HμR; lra.
  Qed.

  Lemma refRcoupl_dret a b (R : A → B → Prop) :
    R a b → refRcoupl (dret a) (dret b) R.
  Proof.
    intros HR.
    eexists. split; [eapply isRefCoupl_dret|].
    intros [] [=<- <-]%dret_pos. done.
  Qed.

  Context `{Countable A', Countable B'}.

  Lemma refRcoupl_dbind (f : A → distr A') (g : B → distr B') (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) (S : A' → B' → Prop) :
    (∀ a b, R a b → refRcoupl (f a) (g b) S) → refRcoupl μ1 μ2 R → refRcoupl (dbind f μ1) (dbind g μ2) S.
  Proof.
    intros Hfg (μ & HμC & HμS).
    rewrite /Rcoupl /isRcoupl in Hfg.
    (* First we rewrite Hfg to be able to use Choice *)
    assert (∀ p, ∃ μ' , R p.1 p.2 → (isRefCoupl (f p.1) (g p.2) μ' ∧
                (∀ q : A' * B', μ' q > 0 → S q.1 q.2))) as Hfg'.
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
      rewrite lmarg_pmf /= /dbind_pmf
       (SeriesC_double_swap (λ '(b, a), μ a * Ch a (a', b))).
      erewrite (SeriesC_ext _ (λ b, μ b * SeriesC (λ a : B', Ch b (a', a))) );
      [ | intro p; apply SeriesC_scal_l].
      erewrite (SeriesC_ext _ (λ p, μ p * f p.1 a')); last first.
      { intros (a & b).
        destruct (Rtotal_order (μ (a, b)) 0) as [Hlt | [Heqz | Hgt]].
        + pose proof (pmf_pos μ (a, b)); lra.
        + rewrite Heqz; lra.
        + specialize (HCh (a, b) (HμS (a, b) Hgt )) as ((HChL & HChR) & HChS).
          rewrite -HChL lmarg_pmf //=. }
      rewrite SeriesC_double_prod_lr.
      erewrite (SeriesC_ext _ (λ a, SeriesC (λ b : B, μ (a, b) ) * f a a'));
      [ | intro a; simpl; apply SeriesC_scal_r ].
      erewrite (SeriesC_ext _ (λ a, (μ1 a) * f a a')); auto.
      intro a.
      destruct HμC as (Hμ1 & Hμ2).
      rewrite <- Hμ1;
      rewrite lmarg_pmf; auto.
    + intro b'.
      rewrite rmarg_pmf /dbind_pmf.
      rewrite (SeriesC_double_swap (λ '(a, a0), μ a0 * Ch a0 (a, b'))).
      erewrite (SeriesC_ext _ (λ b, μ b * SeriesC (λ a : A', Ch b (a, b'))) );
      [ | intro p; apply SeriesC_scal_l].
      apply (Rle_trans _ (SeriesC (λ p, μ p * g p.2 b')) _).
      {
        apply SeriesC_le; [ | ]; last first.
        + apply (ex_seriesC_le _ μ); auto.
          intros; split.
          ++ apply Rmult_le_pos; auto.
          ++ rewrite <- Rmult_1_r.
             apply Rmult_le_compat_l; auto.
        + intros (a & b); split; [ apply Rmult_le_pos; auto | ].
        {
          assert (SeriesC (λ a0 : A', Ch (a, b) (a0, b')) = rmarg (Ch (a, b)) b') as ->;
          [rewrite rmarg_pmf; auto | apply pmf_pos].
        }
        destruct (Rtotal_order (μ (a, b)) 0) as [Hlt | [Heqz | Hgt]].
        ++ pose proof (pmf_pos μ (a, b)); lra.
        ++ rewrite Heqz; lra.
        ++ specialize (HCh (a, b) (HμS (a, b) Hgt )) as ((HChL & HChR) & HChS).
          specialize (HChR b').
          rewrite (rmarg_pmf (Ch (a, b))) in HChR.
          apply Rmult_le_compat_l; auto.
      }
      rewrite {3}/pmf /= /dbind_pmf /=.
      rewrite SeriesC_double_prod_rl /=.
      apply SeriesC_le; [ | ]; last first.
      {
        apply (ex_seriesC_le _ μ2); auto.
        intros; split.
        + apply Rmult_le_pos; auto.
        + rewrite <- Rmult_1_r.
          apply Rmult_le_compat_l; auto.
      }
      intro b; split.
      ++ rewrite SeriesC_scal_r.
         apply Rmult_le_pos ; auto.
         assert (SeriesC (λ x : A, μ (x, b)) = rmarg μ b ) as -> ; [rewrite rmarg_pmf | apply pmf_pos ]; auto.
      ++ destruct HμC as [HμCL HμCR].
         rewrite SeriesC_scal_r.
         apply Rmult_le_compat_r; auto.
         specialize (HμCR b).
         rewrite rmarg_pmf in HμCR; auto.
    + intros (a' & b') H3; simpl.
      pose proof (dbind_pos_support Ch μ (a', b')) as (H4 & H5).
      specialize (H4 H3) as ((a0, b0) & H7 & H8).
      specialize (HCh (a0, b0) (HμS (a0, b0) H8)) as (HCh1 & HCh2).
      specialize (HCh2 (a', b') H7).
      done.
  Qed.

  Lemma refRcoupl_dzero (μ : distr B) (R: A → B → Prop):
    refRcoupl dzero μ R.
  Proof.
    exists dzero; split; try split.
    + rewrite /lmarg dmap_dzero; done.
    + intro a.
      rewrite rmarg_pmf {1}/pmf/=.
      rewrite SeriesC_0; auto.
    + rewrite /pmf/=; intros; lra.
  Qed.

  Lemma refRcoupl_weaken (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) (S : A → B → Prop):
      (∀ a b, R a b -> S a b) → refRcoupl μ1 μ2 R → refRcoupl μ1 μ2 S.
  Proof.
    intros Hwk [μ [[HμL HμR] HμSupp]].
    exists μ; split; [split | ]; auto.
  Qed.


  Lemma refRcoupl_trivial (μ1 :distr A) (μ2 :distr B):
    SeriesC μ1 <= SeriesC μ2 ->
    refRcoupl μ1 μ2 (λ _ _, True).
  Proof.
    intros Hμ.
    pose proof (pmf_SeriesC_ge_0 μ1) as H3.
    destruct (Rlt_or_le 0 (SeriesC μ1)); last first.
    + destruct H3 ; try lra.
      rewrite (SeriesC_zero_dzero μ1); [ | apply Rle_antisym; auto].
      apply refRcoupl_dzero.
    + assert (0 < SeriesC μ2); [apply (Rlt_le_trans _ (SeriesC μ1)) | ]; auto.
      eexists (distr_scal (/(SeriesC μ2)) (dprod μ1 μ2) _).
    Unshelve.
    2:{
      split; auto.
      - left; apply Rinv_0_lt_compat; auto.
      - rewrite dprod_mass.
        rewrite Rmult_comm Rmult_assoc.
        rewrite Rinv_r; auto; try lra.
        rewrite Rmult_1_r.
        apply pmf_SeriesC.
    }
    split; [|done].
    split.
    ++ apply distr_ext. intro a.
      rewrite lmarg_pmf
       SeriesC_scal_l
       -lmarg_pmf
       lmarg_dprod_pmf
       -Rmult_comm
       Rmult_assoc
       Rinv_r; lra.
    ++ intro b.
      rewrite rmarg_pmf
       SeriesC_scal_l
       -rmarg_pmf
       rmarg_dprod_pmf
       -Rmult_comm
       Rmult_assoc.
      assert (μ2 b = μ2 b * 1) as Hrw; [rewrite Rmult_1_r; auto | ].
      rewrite {2}Hrw.
      apply (Rmult_le_compat_l); auto; try lra.
      apply (Rdiv_le_1 (SeriesC μ1) (SeriesC μ2)) ; try lra.
  Qed.


End ref_couplings_theory.

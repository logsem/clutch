(** Exact couplings  *)
From mathcomp Require Import all_ssreflect classical_sets boolp functions.
From clutch.prelude Require Import classical.
From mathcomp.algebra Require Import ssralg ssrnum interval.
From mathcomp.analysis Require Import ereal measure lebesgue_measure lebesgue_integral ftc probability sequences function_spaces.
From clutch.prob.monad Require Import prelude giry.
From stdpp Require Import base.
From Coq Require Import Reals.
Require Import mathcomp.reals_stdlib.Rstruct.
Require Import mathcomp.reals.reals.
From HB Require Import structures.



Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Default Proof Using "Type".

(*
Local Open Scope classical_set_scope.

Notation RR := ((R : realType) : measurableType _).
 *)

Section couplings.
  Local Open Scope classical_set_scope.

  Context {dA dB} `{A : measurableType dA} `{B : measurableType dB}.
  Context (μ1 : giryM A) (μ2 : giryM B) (S : A -> B -> Prop) (ε : R) (δ : \bar R).


  Definition ARcoupl_meas : Prop :=
    forall (f : A -> \bar R) (Hmf : measurable_fun setT f) (Hfge0 : forall (a : A), (0 <= f a)%E) (Hfle1 : forall (a : A), (f a <= 1)%E)
      (g : B -> \bar R) (Hmg : measurable_fun setT g) (Hgge0 : forall (b : B), (0 <= g b)%E) (Hgle1 : forall (b : B), (g b <= 1)%E),
      (forall (a : A) (b : B), S a b -> (f a <= g b)%E) ->
      (\int[μ1]_(x in setT) f x <= ( δ + (expR ε)%:E* \int[μ2]_(x in setT) g x))%E.

End couplings.

Global Instance integral_proper {d} {T : measurableType d} f :
  Proper (measure_eq ==> eq) (fun (μ : giryM T) => \int[μ]_(x in setT) f x)%E.
Proof.
  intros μ1 μ1' H.
  eapply eq_measure_integral.
  intros S HS ?.
  by apply H.
Qed.

Section couplings_theory.
  Local Open Scope classical_set_scope.
  Local Open Scope ring_scope.
  Local Open Scope ereal_scope.
  Context {dA1 dB1 dA2 dB2}
    `{A1 : measurableType dA1} `{B1 : measurableType dB1}
    `{A2 : measurableType dA2} `{B2 : measurableType dB2}.

  Lemma ARcoupl_meas_proper_pre {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2} S ε δ :
    Proper (measure_eq ==> measure_eq ==> impl) (fun (μ1 : giryM T1) (μ2 : giryM T2) => ARcoupl_meas μ1 μ2 S ε δ).
  Proof.
    intros μ1 μ1' H1 μ2 μ2' H2.
    intros Hcoupl f Hfm Hfp Hf1 g Hgm Hgp Hg1 Hle.
    symmetry in H1, H2.
    rewrite (integral_proper _ H1).
    rewrite (integral_proper _ H2).
    by apply Hcoupl.
  Qed.

  Global Instance ARcoupl_meas_proper {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2} S ε δ :
    Proper (measure_eq ==> measure_eq ==> eq) (fun (μ1 : giryM T1) (μ2 : giryM T2) => ARcoupl_meas μ1 μ2 S ε δ).
  Proof.
    intros μ1 μ1' H1 μ2 μ2' H2.
    apply propext; split; apply ARcoupl_meas_proper_pre; done.
  Qed.

  (* TODO: Fix notation scoping for ε <= ε', etc *)

  Lemma ARcoupl_meas_mono (μ1 μ1': giryM A1) (μ2 μ2': giryM B1) S S' (ε ε': R) (δ δ': \bar R) :
    (μ1 ≡μ μ1') ->
    (μ2 ≡μ μ2') ->
    (∀ x y, S x y -> S' x y) ->
    (Order.le ε ε') ->
    (δ <= δ') ->
    ARcoupl_meas μ1 μ2 S ε δ ->
    ARcoupl_meas μ1' μ2' S' ε' δ'.
  Proof.
    intros Hμ1 Hμ2 HR Hε Hδ Hcoupl f Hmf Hfge0 Hfle1 g Hmg Hgge0 Hgle1 Hfg.
    specialize (Hcoupl f Hmf Hfge0 Hfle1 g Hmg Hgge0 Hgle1).
    rewrite (eq_measure_integral μ1); last first.
    {
      intros ???.
      symmetry.
      by apply Hμ1.
    }
    rewrite (eq_measure_integral μ2); last first.
    {
      intros ???.
      symmetry.
      by apply Hμ2.
    }
    eapply (Order.le_trans).
    {
      apply Hcoupl; auto.
    }
    eapply (@Order.le_trans _ _ (δ + (expR ε')%:E * \int[μ2]_x g x)).
    {
      apply (leeD2l δ).
      apply (@lee_pmul _ (expR ε)%:E); auto.
      apply exp.expR_ge0.
      apply integral_ge0; auto.
      rewrite lee_fin
        exp.ler_expR //.
    }
    apply (leeD2r ((expR ε')%:E * \int[μ2]_x g x)); auto.
 Qed.

  Lemma ARcoupl_meas_1 (μ1 : giryM A1) (μ2 : giryM B1) S (ε : R) (δ : \bar R) :
    (1 <= δ) -> ARcoupl_meas μ1 μ2 S ε δ.
  Proof.
    intros Hδ f Hmf Hfge0 Hfle1 g Hmg Hgge0 Hgle1 Hfg.
    apply (@Order.le_trans _ _ ((\int[μ1]_x cst 1 x)%E)).
    {
      apply ge0_le_integral; auto.
    }
    rewrite integral_cst; auto.
    rewrite mul1e.
    have Hμ1 : (μ1 [set: A1] <= 1)%E by apply sprobability_setT.
    apply (@Order.le_trans _ _ (1%E)); auto.
    have Hg : (0 <= (expR ε)%:E * \int[μ2]_x g x)%E.
    {
      apply mule_ge0.
      apply exp.expR_ge0.
      apply integral_ge0; auto.
    }
    apply (lee_paddr Hg); auto.
 Qed.


  Lemma ARcoupl_meas_mon_grading (μ1 : giryM A1) (μ2 : giryM B1) (S : A1 → B1 → Prop) ε1 ε2 δ1 δ2 :
    (Order.le ε1 ε2) ->
    (δ1 <= δ2) ->
    ARcoupl_meas μ1 μ2 S ε1 δ1 ->
    ARcoupl_meas μ1 μ2 S ε2 δ2.
  Proof.
    intros Hε Hδ Hcoupl.
    eapply ARcoupl_meas_mono; eauto.
  Qed.



  Lemma ARcoupl_meas_dret (a : A1) (b : B1) (S : A1 → B1 → Prop) ε δ :
    (Order.le (GRing.zero) ε) ->
    0 <= δ →
    S a b →
    ARcoupl_meas (gRet a) (gRet b) S ε δ.
  Proof.
    intros Hε Hδ HS f Hmf Hfge0 Hfle1 g Hmg Hgge0 Hgle1 Hfg.
    rewrite gRetInt_rw; auto.
    rewrite gRetInt_rw; auto.
    specialize (Hfg _ _ HS).
    have Hfg' : (f a <= (expR ε)%:E * g b).
    {
      rewrite -(mul1e (f a)).
      apply (@lee_pmul _ _ (expR ε)%:E); auto.
      rewrite -exp.expR0.
      rewrite lee_fin
        exp.ler_expR //.
    }
    apply (lee_paddl Hδ Hfg').
  Qed.


  (* The hypothesis (0 ≤ δ1) is not really needed, I just kept it for symmetry *)
  Lemma ARcoupl_meas_dbind (f : A1 → giryM A2) (Hf : measurable_fun setT f) (g : B1 → giryM B2) (Hg : measurable_fun setT g)
    (μ1 : giryM A1) (μ2 : giryM B1) (S : A1 → B1 → Prop) (T : A2 → B2 → Prop) ε1 ε2 δ1 δ2 :
    (0 <= δ1) -> (0 <= δ2) -> (δ2 \is a fin_num) ->
    (∀ a b, S a b → ARcoupl_meas (f a) (g b) T ε2 δ2) →
    ARcoupl_meas μ1 μ2 S ε1 δ1 →
    ARcoupl_meas (gBind Hf μ1) (gBind Hg μ2) T (ε1 + ε2) (δ1 + δ2)%E.
  Proof.
    intros Hδ1 Hδ2 Hδ2fin Hcoup_fg Hcoup_S.
    intros h1 Hmh1 Hh1ge0 Hh1le1.
    intros h2 Hmh2 Hh2ge0 Hh2le1.
    intros Hh1h2.
    rewrite gBindInt_rw; auto.
    rewrite gBindInt_rw; auto.
    set (a := fun (x:A1) => maxe ((\int[f x]_y h1 y) - δ2)%E 0%:E).
    have Hh1measInt : measurable_fun setT (λ x : A1, (\int[f x]_y h1 y)%E).
    {
      pose proof (gBindInt_meas_fun μ1 Hf Hmh1) as Haux.
      eapply eq_measurable_fun; eauto.
      intros ??.
      rewrite /gInt //.
    }
    have Hameas : (measurable_fun setT a).
    {
      rewrite /a.
      apply measurable_maxe; auto.
      apply emeasurable_funD; auto.
    }
    have Ha_ge0 : (forall x, (0 <= a x)%E).
    {
      intros x.
      rewrite /a.
      rewrite Order.TotalTheory.le_max.
      rewrite lee_fin
        Order.le_refl
        orb_true_r //.
    }
    have Ha_le1 : (forall x, (a x <= 1)%E).
    {
      intros x.
      rewrite /a.
      rewrite Order.TotalTheory.ge_max.
      rewrite lee_fin
       Num.Theory.ler01
       andb_true_r.
      rewrite leeBlDl //.
      apply (@Order.le_trans _ _ ((\int[f x]_y cst 1 y)%E));
        [apply ge0_le_integral; auto |].
      rewrite integral_cst; auto.
      rewrite mul1e.
      have Hμ1 : (f x [set: A2] <= 1)%E by apply sprobability_setT.
      apply (@Order.le_trans _ _ (1%E)); auto.
      apply (lee_paddl Hδ2); auto.
    }

    set (b := fun (x:B1) => mine ((expR ε2)%:E * \int[g x]_y h2 y)%E 1%:E).
    have Hh2measInt : measurable_fun setT (λ x : B1, (\int[g x]_y h2 y)%E).
    {
      pose proof (gBindInt_meas_fun μ2 Hg Hmh2) as Haux.
      eapply eq_measurable_fun; eauto.
      intros ??.
      rewrite /gInt //.
    }
    have Hbmeas : (measurable_fun setT b).
    {
      rewrite /b.
      apply measurable_mine; auto.
      apply measurable_funeM; auto.
    }
    have Hb_ge0 : (forall x, (0 <= b x)%E).
    {
      intros x.
      rewrite /b.
      rewrite Order.TotalTheory.le_min /=.
      rewrite lee_fin /= Num.Theory.ler01 andb_true_r.
      apply (@mule_ge0 _ (expR ε2)%:E); auto.
      apply exp.expR_ge0.
      apply integral_ge0; auto.
    }
    have Hb_le1 : (forall x, (b x <= 1)%E).
    {
      intros x.
      rewrite /b.
      rewrite Order.TotalTheory.ge_min Order.le_refl orb_true_r //.
    }

    have HS_ab : (∀ (a0 : A1) (b0 : B1), S a0 b0 → (a a0 <= b b0)%E).
    {
      intros a0 b0 Ha0b0.
      rewrite /a /b.
      rewrite Order.TotalTheory.le_min.
      rewrite Order.TotalTheory.ge_max.
      rewrite Order.TotalTheory.ge_max.
      rewrite lee_fin Num.Theory.ler01 andb_true_r.
      rewrite (@mule_ge0 _ (expR ε2)%:E); auto.
      2:apply exp.expR_ge0.
      2:apply integral_ge0; auto.
      rewrite andb_true_r.
      rewrite leeBlDl //.
      rewrite Hcoup_fg; auto.
      rewrite andb_true_l.
      rewrite leeBlDl //.
      rewrite lee_paddl; auto.
      apply (@Order.le_trans _ _ ((\int[f a0]_y cst 1 y)%E));
        [apply ge0_le_integral; auto |].
      rewrite integral_cst; auto.
      rewrite mul1e.
      apply sprobability_setT.
    }


    (* Now, we can instantiate Hcoup_S with a, b  *)
    specialize (Hcoup_S a Hameas Ha_ge0 Ha_le1 b Hbmeas Hb_ge0 Hb_le1 HS_ab).
    rewrite (GRing.addrC δ1 δ2).
    rewrite exp.expRD.
    rewrite EFinM.
    rewrite -muleA.
    rewrite -ge0_integralZl; auto.
    2: {intros; apply integral_ge0; auto. }
    2: {apply exp.expR_ge0. }
    eapply (@Order.le_trans _ _ (δ2 + δ1 + (expR ε1)%:E * \int[μ2]_x b x)); last first.
    {
      apply (@leeD2l _ (δ2 + δ1)).
      rewrite lee_pmul2l; auto; last first.
      apply exp.expR_gt0.
      apply ge0_le_integral; auto.
      intros x ?.
      apply (@mule_ge0 _ (expR ε2)%:E); auto.
      apply exp.expR_ge0.
      apply integral_ge0; auto.
      apply measurable_funeM; auto.
      intros b0 Hb0.
      rewrite /b/=.
      rewrite Order.TotalTheory.ge_min
                Order.le_refl
                orb_true_l //.
    }
    eapply (@Order.le_trans _ _ (δ2 + \int[μ1]_x a x)); last first.
    {
      rewrite -GRing.addrA.
      apply (@leeD2l _ δ2); auto.
    }
    eapply (@Order.le_trans _ _ (\int[μ1]_x cst δ2 x + \int[μ1]_x a x)%E); last first.
    {
      apply (@leeD2r _ (\int[μ1]_x a x)%E).
      rewrite integral_cst; auto.
      rewrite muleC.
      apply (@gee_pMl _ (μ1 [set: A1]) δ2); auto.
      have Haux : (`|μ1 [set: A1]| <= 1)%E.
      {
        rewrite gee0_abs.
        apply sprobability_setT.
        apply measure_ge0.
      }
      rewrite fin_num_abs.
      eapply Order.POrderTheory.le_lt_trans; eauto.
      apply ltry.
      apply sprobability_setT.
    }
    rewrite -ge0_integralD; auto.
    apply ge0_le_integral; auto.
    {
      intros ??.
      apply integral_ge0; auto.
    }
    {
      intros x ?.
      simpl.
      apply (@adde_ge0 _ δ2 (a x)); auto.
    }
    {
      apply emeasurable_funD; auto.
    }
    intros x ?.
    rewrite /a /=.
    rewrite adde_maxr.
    rewrite GRing.addrC.
    rewrite subeK //.
    rewrite Order.TotalTheory.le_max
      Order.le_refl
      orb_true_l //.
  Qed.


  Lemma ARcoupl_meas_dbind_exp_l (f : A1 → giryM A2) (Hf : measurable_fun setT f) (g : B1 → giryM B2) (Hg : measurable_fun setT g)
    (μ1 : giryM A1) (μ2 : giryM B1) (S : A1 → B1 → Prop) (T : A2 → B2 → Prop) δ1 (Δ2 : A1 -> \bar R) (HΔ2 : measurable_fun setT Δ2) ε1 ε2 :
    (0 <= δ1) -> (forall a, 0 <= Δ2 a) -> (forall a, (Δ2 a) \is a fin_num) ->
    (∀ a b, S a b → ARcoupl_meas (f a) (g b) T ε2 (Δ2 a)) →
    ARcoupl_meas μ1 μ2 S ε1 δ1 →
    ARcoupl_meas (gBind Hf μ1) (gBind Hg μ2) T (GRing.add ε1 ε2) (δ1 + \int[μ1]_a Δ2 a).
  Proof.
    intros Hδ1 Hδ2 Hδ2fin Hcoup_fg Hcoup_S.
    intros h1 Hmh1 Hh1ge0 Hh1le1.
    intros h2 Hmh2 Hh2ge0 Hh2le1.
    intros Hh1h2.
    rewrite gBindInt_rw; auto.
    rewrite gBindInt_rw; auto.
    set (a := fun (x:A1) => maxe ((\int[f x]_y h1 y) - Δ2(x))%E 0%:E).
    have Hh1measInt : measurable_fun setT (λ x : A1, (\int[f x]_y h1 y)%E).
    {
      pose proof (gBindInt_meas_fun μ1 Hf Hmh1) as Haux.
      eapply eq_measurable_fun.
      intros ??.
      rewrite /gInt //.
      auto.
    }
    have Hameas : (measurable_fun setT a).
    {
      rewrite /a.
      apply measurable_maxe; auto.
      apply emeasurable_funB; auto.
    }
    have Ha_ge0 : (forall x, (0 <= a x)%E).
    {
      intros x.
      rewrite /a.
      rewrite Order.TotalTheory.le_max.
      rewrite lee_fin
        Order.le_refl
        orb_true_r //.
    }
    have Ha_le1 : (forall x, (a x <= 1)%E).
    {
      intros x.
      rewrite /a.
      rewrite Order.TotalTheory.ge_max.
      rewrite lee_fin
       Num.Theory.ler01
       andb_true_r.
      rewrite leeBlDl //.
      apply (@Order.le_trans _ _ ((\int[f x]_y cst 1 y)%E));
        [apply ge0_le_integral; auto |].
      rewrite integral_cst; auto.
      rewrite mul1e.
      have Hμ1 : (f x [set: A2] <= 1)%E by apply sprobability_setT.
      apply (@Order.le_trans _ _ (1%E)); auto.
      apply (lee_paddl (Hδ2 x)); auto.
    }

    set (b := fun (x:B1) => mine ((expR ε2)%:E * \int[g x]_y h2 y)%E 1%:E).
    have Hh2measInt : measurable_fun setT (λ x : B1, (\int[g x]_y h2 y)%E).
    {
      pose proof (gBindInt_meas_fun μ2 Hg Hmh2) as Haux.
      eapply eq_measurable_fun.
      intros ??.
      rewrite /gInt //.
      auto.
    }
    have Hbmeas : (measurable_fun setT b).
    {
      rewrite /b.
      apply measurable_mine; auto.
      apply measurable_funeM; auto.
    }
    have Hb_ge0 : (forall x, (0 <= b x)%E).
    {
      intros x.
      rewrite /b.
      rewrite Order.TotalTheory.le_min /=.
      rewrite lee_fin /= Num.Theory.ler01 andb_true_r.
      apply (@mule_ge0 _ (expR ε2)%:E); auto.
      apply exp.expR_ge0.
      apply integral_ge0; auto.
    }
    have Hb_le1 : (forall x, (b x <= 1)%E).
    {
      intros x.
      rewrite /b.
      rewrite Order.TotalTheory.ge_min Order.le_refl orb_true_r //.
    }

    have HS_ab : (∀ (a0 : A1) (b0 : B1), S a0 b0 → (a a0 <= b b0)%E).
    {
      intros a0 b0 Ha0b0.
      rewrite /a /b.
      rewrite Order.TotalTheory.le_min.
      rewrite Order.TotalTheory.ge_max.
      rewrite Order.TotalTheory.ge_max.
      rewrite lee_fin Num.Theory.ler01 andb_true_r.
      rewrite (@mule_ge0 _ (expR ε2)%:E); auto.
      2:apply exp.expR_ge0.
      2:apply integral_ge0; auto.
      rewrite andb_true_r.
      rewrite leeBlDl //.
      rewrite Hcoup_fg; auto.
      rewrite andb_true_l.
      rewrite leeBlDl //.
      rewrite lee_paddl; auto.
      apply (@Order.le_trans _ _ ((\int[f a0]_y cst 1 y)%E));
        [apply ge0_le_integral; auto |].
      rewrite integral_cst; auto.
      rewrite mul1e.
      apply sprobability_setT.
    }

    (* Now, we can instantiate Hcoup_S with a, b  *)

    specialize (Hcoup_S a Hameas Ha_ge0 Ha_le1 b Hbmeas Hb_ge0 Hb_le1 HS_ab).
    rewrite (GRing.addrC δ1).
    rewrite exp.expRD.
    rewrite EFinM.
    rewrite -muleA.
    rewrite -ge0_integralZl; auto.
    2: {intros; apply integral_ge0; auto. }
    2: {apply exp.expR_ge0. }
    eapply (@Order.le_trans _ _
              (\int[μ1]_a0 Δ2 a0 + δ1 + (expR ε1)%:E * \int[μ2]_x b x)); last first.
    {
      apply (@leeD2l _ (\int[μ1]_a0 Δ2 a0 + δ1)).
      rewrite lee_pmul2l; auto; last first.
      apply exp.expR_gt0.
      apply ge0_le_integral; auto.
      intros x ?.
      apply (@mule_ge0 _ (expR ε2)%:E); auto.
      apply exp.expR_ge0.
      apply integral_ge0; auto.
      apply measurable_funeM; auto.
      intros b0 Hb0.
      rewrite /b/=.
      rewrite Order.TotalTheory.ge_min
                Order.le_refl
                orb_true_l //.
    }
    eapply (@Order.le_trans _ _ (\int[μ1]_a0 Δ2 a0 + \int[μ1]_x a x)); last first.
    {
      rewrite -GRing.addrA.
      apply (@leeD2l _ (\int[μ1]_a0 Δ2 a0)); auto.
    }
    rewrite -ge0_integralD; auto.
    apply ge0_le_integral; auto.
    {
      intros ??.
      apply integral_ge0; auto.
    }
    {
      intros x ?.
      simpl.
      apply (@adde_ge0 _ (Δ2 x) (a x)); auto.
    }
    {
      apply emeasurable_funD; auto.
    }
    intros x ?.
    rewrite /a /=.
    rewrite adde_maxr.
    rewrite GRing.addrC.
    rewrite subeK //.
    rewrite Order.TotalTheory.le_max
      Order.le_refl
      orb_true_l //.
  Qed.


  Lemma ARcoupl_meas_dbind_exp_r (f : A1 → giryM A2) (Hf : measurable_fun setT f) (g : B1 → giryM B2) (Hg : measurable_fun setT g)
    (μ1 : giryM A1) (μ2 : giryM B1) (S : A1 → B1 → Prop) (T : A2 → B2 → Prop) δ1 (Δ2 : B1 -> \bar R) (HΔ2 : measurable_fun setT Δ2) ε1 ε2 :
    (0 <= δ1) -> (forall b, 0 <= Δ2 b) -> (forall b, (Δ2 b) \is a fin_num) ->
    (∀ a b, S a b → ARcoupl_meas (f a) (g b) T ε2 (Δ2 b)) →
    ARcoupl_meas μ1 μ2 S ε1 δ1 →
    ARcoupl_meas (gBind Hf μ1) (gBind Hg μ2) T (GRing.add ε1 ε2) (δ1 + (expR ε1)%:E * \int[μ2]_b Δ2 b).
  Proof.
    intros Hδ1 Hδ2 Hδ2fin Hcoup_fg Hcoup_S.
    intros h1 Hmh1 Hh1ge0 Hh1le1.
    intros h2 Hmh2 Hh2ge0 Hh2le1.
    intros Hh1h2.
    rewrite gBindInt_rw; auto.
    rewrite gBindInt_rw; auto.
    set (a := fun (x:A1) => (\int[f x]_y h1 y)%E).
    have Hameas : (measurable_fun setT a).
    {
      pose proof (gBindInt_meas_fun μ1 Hf Hmh1) as Haux.
      eapply eq_measurable_fun.
      intros ??.
      rewrite /gInt //.
      auto.
    }

    have Ha_ge0 : (forall x, (0 <= a x)%E).
    {
      intros x.
      rewrite /a.
      apply integral_ge0; auto.
    }
    have Hh1_int_le1 : (forall x, \int[f x]_y h1 y <= 1).
    {
      intro x.
      apply (@Order.le_trans _ _ ((\int[f x]_y cst 1 y)%E));
        [apply ge0_le_integral; auto |].
      rewrite integral_cst; auto.
      rewrite mul1e.
      apply sprobability_setT.
    }
    have Ha_le1 : (forall x, (a x <= 1)%E); [rewrite /a // |].

    set (b := fun (x:B1) => mine (Δ2(x) + (expR ε2)%:E * (\int[g x]_y h2 y))%E 1%:E).
    have Hh2measInt : measurable_fun setT (λ x : B1, (\int[g x]_y h2 y)%E).
    {
      pose proof (gBindInt_meas_fun μ2 Hg Hmh2) as Haux.
      eapply eq_measurable_fun.
      intros ??.
      rewrite /gInt //.
      auto.
    }
    have Hbmeas : (measurable_fun setT b).
    {
      rewrite /b.
      apply measurable_mine; auto.
      apply emeasurable_funD; auto.
      apply measurable_funeM; auto.
    }
    have Hb_ge0 : (forall x, (0 <= b x)%E).
    {
      intros x.
      rewrite /b.
      rewrite Order.TotalTheory.le_min /=.
      rewrite lee_fin /= Num.Theory.ler01 andb_true_r.
      apply (@adde_ge0 _ (Δ2 x)); auto.
      apply (@mule_ge0 _ (expR ε2)%:E); auto.
      apply exp.expR_ge0.
      apply integral_ge0; auto.
    }
    have Hb_le1 : (forall x, (b x <= 1)%E).
    {
      intros x.
      rewrite /b.
      rewrite Order.TotalTheory.ge_min Order.le_refl orb_true_r //.
    }

    have HS_ab : (∀ (a0 : A1) (b0 : B1), S a0 b0 → (a a0 <= b b0)%E).
    {
      intros a0 b0 Ha0b0.
      rewrite /a /b.
      rewrite Order.TotalTheory.le_min.
      rewrite Hh1_int_le1 andb_true_r //.
      apply Hcoup_fg; auto.
    }

    (* Now, we can instantiate Hcoup_S with a, b  *)
    specialize (Hcoup_S a Hameas Ha_ge0 Ha_le1 b Hbmeas Hb_ge0 Hb_le1 HS_ab).

    eapply (@Order.le_trans _ _ (δ1 + (expR ε1)%:E * \int[μ2]_x b x)); auto.
    rewrite -GRing.addrA.
    apply (@leeD2l _ δ1).
    rewrite exp.expRD EFinM -muleA.
    rewrite -ge0_muleDr; auto.
    2: {apply integral_ge0; auto. }
    2: {
      apply (@mule_ge0 _ (expR ε2)%:E); auto.
      apply exp.expR_ge0.
      apply integral_ge0; auto.
      intros; apply integral_ge0; auto.
    }
    rewrite lee_pmul2l; auto.
    2:{ apply exp.expR_gt0. }
    rewrite -ge0_integralZl; auto.
    rewrite -ge0_integralD; auto; last first.
    {
      apply measurable_funeM; auto.
    }
    {
      intros.
      apply (@mule_ge0 _ (expR ε2)%:E); auto.
      apply exp.expR_ge0.
      apply integral_ge0; auto.
    }
    apply ge0_le_integral; auto.
    {
      intros x ?.
      apply (@adde_ge0 _ (Δ2 x)); auto.
      apply (@mule_ge0 _ (expR ε2)%:E); auto.
      apply exp.expR_ge0.
      apply integral_ge0; auto.
    }
    {
      apply emeasurable_funD; auto.
      apply measurable_funeM; auto.
    }
    {
      intros x ?.
      rewrite /b /=.
      rewrite Order.TotalTheory.ge_min
        Order.le_refl
        orb_true_l //.
    }
    {
      intros.
      apply integral_ge0; auto.
    }
    apply exp.expR_ge0.
  Qed.



  Lemma ARcoupl_meas_dbind_exp_r_eps0 (f : A1 → giryM A2) (Hf : measurable_fun setT f) (g : B1 → giryM B2) (Hg : measurable_fun setT g)
    (μ1 : giryM A1) (μ2 : giryM B1) (S : A1 → B1 → Prop) (T : A2 → B2 → Prop) δ1 (Δ2 : B1 -> \bar R) (HΔ2 : measurable_fun setT Δ2) :
    (0 <= δ1) -> (forall b, 0 <= Δ2 b) -> (forall b, (Δ2 b) \is a fin_num) ->
    (∀ a b, S a b → ARcoupl_meas (f a) (g b) T GRing.zero (Δ2 b)) →
    ARcoupl_meas μ1 μ2 S GRing.zero δ1 →
    ARcoupl_meas (gBind Hf μ1) (gBind Hg μ2) T GRing.zero (δ1 + \int[μ2]_b Δ2 b).
  Proof.
    intros Hδ1 Hδ2 Hδ2fin Hcoup_fg Hcoup_S.
    pose proof (ARcoupl_meas_dbind_exp_r Hf Hg HΔ2 Hδ1 Hδ2 Hδ2fin Hcoup_fg Hcoup_S) as Haux.
    rewrite exp.expR0 GRing.add0r mul1e in Haux.
    auto.
  Qed.


  Lemma ARcoupl_meas_mass_leq (μ1 : giryM A1) (μ2 : giryM B1) (S : A1 → B1 → Prop) ε δ :
    ARcoupl_meas μ1 μ2 S ε δ → μ1 [set: A1] <= (expR ε)%:E * μ2 [set: B1] + δ.
  Proof.
    intros Hcoupl.
    rewrite /ARcoupl_meas in Hcoupl.
    rewrite -(mul1e (μ1 [set: A1])).
    rewrite -(mul1e (μ2 [set: B1])).
    rewrite -integral_cst; auto.
    rewrite -integral_cst; auto.
    rewrite GRing.addrC.
    apply Hcoupl; auto.
  Qed.


  Lemma ARcoupl_meas_eq (μ1 : giryM A1) :
    ARcoupl_meas μ1 μ1 (=) GRing.zero 0.
  Proof.
    intros f Hfmeas Hfge0 Hfle1 g Hgmeas Hgge0 Hgle1 Hfg.
    rewrite GRing.add0r.
    rewrite exp.expR0 mul1e.
    apply ge0_le_integral; auto.
  Qed.


  Lemma ARcoupl_meas_eq_elim (μ1 μ2 : giryM A1) ε δ :
    ARcoupl_meas μ1 μ2 (=) ε δ → forall (S : set A1), (dA1.-measurable S) -> μ1 S <= (expR ε)%:E * μ2 S + δ.
  Proof.
    intros Hcoupl S HSmeas.
    rewrite GRing.addrC.
    rewrite -(mul1e (μ1 S)).
    rewrite -(mul1e (μ2 S)).
    rewrite -integral_cst; auto.
    rewrite -integral_cst; auto.
    rewrite integral_mkcond.
    rewrite (@integral_mkcond _ _ _ μ2).
    apply Hcoupl; auto.
    {
      apply (measurable_restrictT (@cst A1 (\bar R) 1)); auto.
    }
    {
      intros.
      apply (@numfun.erestrict_ge0 _ _ S (@cst A1 (\bar R) 1)); auto.
    }
    {
      rewrite /patch.
      intros a.
      case (a \in S); simpl; auto.
    }
    {
      apply (measurable_restrictT (@cst A1 (\bar R) 1)); auto.
    }
    {
      intros.
      apply (@numfun.erestrict_ge0 _ _ S (@cst A1 (\bar R) 1)); auto.
    }
    {
      rewrite /patch.
      intros b.
      case (b \in S); simpl; auto.
    }
    intros ? ? ->; auto.
  Qed.


End couplings_theory.

(* TODO: cleanup *)
Section ARcoupl_meas.


  Local Open Scope classical_set_scope.
  Local Open Scope ring_scope.
  Local Open Scope ereal_scope.

  Context {dA dB}
    `{A : measurableType dA} `{B : measurableType dB}.

  Variable (μ1 : giryM A) (μ2 : giryM B).



  Lemma ARcoupl_meas_trivial :
    μ1 [set: A] = 1 ->
    μ2 [set: B] = 1 ->
    ARcoupl_meas μ1 μ2 (λ _ _, True) GRing.zero 0.
  Proof.
    intros Hμ1 Hμ2 f Hfm Hfge0 Hfle1 g Hgm Hgge0 Hgle1 Hfg.
    rewrite exp.expR0 mul1e.
    rewrite GRing.add0r.
    set (ubf := ereal_sup (range f)).
    set (lbg := ereal_inf (range g)).
    apply (@Order.le_trans _ _ ubf).
    {
      rewrite -(mule1 ubf) -Hμ1.
      rewrite -integral_cst; auto.
      rewrite /ubf.
      apply ge0_le_integral; auto.
      - intros a ? ; simpl.
        apply ereal_sup_le.
        exists (f a); auto.
      - intros a ? ; simpl.
        apply ereal_sup_le.
        exists (f a); auto.
    }
    apply (@Order.le_trans _ _ lbg).
    {
      rewrite /ubf /lbg.
      apply lb_ereal_inf.
      apply lbP.
      intros y [b Hb <-].
      apply ub_ereal_sup.
      apply ubP.
      intros x [a Ha <-].
      auto.
    }
    rewrite -(mule1 lbg) -Hμ2.
    rewrite -integral_cst; auto.
    rewrite /lbg.
    apply ge0_le_integral; auto.
    - intros b ? ; simpl.
      apply lb_ereal_inf, lbP.
      intros y [? ? <-]; auto.
    - intros b ? ; simpl.
      apply ereal_inf_le.
      exists (g b); auto.
  Qed.

  Lemma ARcoupl_meas_preserve (t : A -> B) (Hmt : measurable_fun setT t) :
    (*
       This condition is precisely measure preservation,
       i.e. forall S, measurable S -> μ2 S = μ1 (f @^-1` A)
     *)
    (forall (S : set B), measurable S -> μ2 S = pushforward μ1 Hmt S) ->
    ARcoupl_meas μ1 μ2 (λ n m, m = t n) GRing.zero 0.
  Proof.
    intros Hpres f Hfm Hfge0 Hfle1 g Hgm Hgge0 Hgle1 Hfg.
    rewrite exp.expR0 mul1e.
    rewrite GRing.add0r.
    rewrite (@eq_measure_integral _ _ _ _ (pushforward μ1 Hmt) μ2); last first.
    {
      intros ? ? ?.
      apply Hpres.
      auto.
    }
    rewrite ge0_integral_pushforward; auto.
    apply ge0_le_integral; auto.
    { rewrite <- (setTI (preimage _ _)). by apply Hmt. }
    { intros. rewrite /ssrfun.comp. apply Hgge0. }
    { apply measurableT_comp; auto. }
    { intros. by apply Hfg. }
    { apply @in_setP. intros. apply Hgge0. }
  Qed.

  Lemma ARcoupl_meas_preserve_mZl (t : A -> B) (Hmt : measurable_fun setT t)
    (Z : set A) (HZ: measurable Z):
    (*
       This condition is precisely measure preservation,
       i.e. forall S, measurable S -> μ2 S = μ1 (f @^-1` A)
     *)
    (forall (S : set B), measurable S -> μ2 S = pushforward μ1 Hmt S) ->
    (μ1 Z = 0) ->
    ARcoupl_meas μ1 μ2 (λ n m, (n \notin Z) /\ m = t n) GRing.zero 0.
  Proof.
    intros Hpres Hμ1Z f Hfm Hfge0 Hfle1 g Hgm Hgge0 Hgle1 Hfg.
    rewrite exp.expR0 mul1e.
    rewrite GRing.add0r.
    rewrite (negligible_integral HZ); auto.
    2:{
      pose proof (finite_measure_integrable_cst μ1 1).
      eapply (le_integrable _ _ _ H); eauto.
      Unshelve.
      auto.
      auto.
      intros; simpl; auto.
      rewrite gee0_abs // Num.Theory.normr1 //.
    }
    rewrite setTD.
    - rewrite integral_mkcond.
      rewrite (@eq_measure_integral _ _ _ _ (pushforward μ1 Hmt) μ2); last first.
    {
      intros ? ? ?.
      apply Hpres.
      auto.
    }
    have HmfrestrZ : measurable_fun [set: A] (f \_ (~` Z)).
    {
      apply measurable_restrict; auto.
      apply measurableC; auto.
      apply measurable_fun_setI1; auto.
      apply measurableC; auto.
    }
    rewrite ge0_integral_pushforward; auto; last first.
    { admit. }
(*
    apply ge0_le_integral; auto.
    {
      intros x ?.
      rewrite /patch /=.
      case (x \in ~`Z); simpl; auto.
    }
    {
      intros; simpl; auto.
    }
    {
      apply measurableT_comp; auto.
    }
    intros x ?.
    rewrite /patch /=.
    case (x \in ~`Z) eqn:Htx ; simpl; auto.
    apply Hfg.
    split; auto.
    rewrite -in_setC Htx //.
 Qed.
*)
    Admitted.


Local Open Scope classical_set_scope.


Lemma ARcoupl_meas_pos_R R' ε δ (SA : set A) (SB : set B) (HA : measurable SA) (HB : measurable SB) :
  μ1 SA = 1 -> μ2 SB = 1 -> ARcoupl_meas μ1 μ2 R' ε δ → ARcoupl_meas μ1 μ2 (λ a b, R' a b ∧ SA a ∧ SB b) ε δ.
Proof.
  intros HSA HSB Hμ1μ2 f Hf Hfg0 Hfl1 g Hg Hgg0 Hgl1 Hfg.

  (* Split the integrals into S and ~` S *)
  have R1: forall d (T : measurableType d) (μ : giryM T) (S : set T) (HS : measurable S) (h : T -> \bar R)
             (Hh : measurable_fun setT h) (Hhp : ∀ x : T, (~` S `|` S) x → 0 <= h x),
             \int[μ]_x h x = (\int[μ]_(x in ~` S) h x) + (\int[μ]_(x in S) h x).
  { intros. rewrite -(setvU S) ge0_integral_setU; try done.
    { by apply measurableC. }
    { by rewrite setvU. }
    { by rewrite /disj_set; rewrite setICl; apply eq_refl. }
  }
  rewrite (R1 _ _ _ SA) //.
  rewrite (R1 _ _ _ SB) //.

  (* Integrals on ~` S are 0 *)
  have L1 : forall d (T : measurableType d) (μ : giryM T) (S : set T) (HS : measurable S) (h : T -> \bar R)
              (Hm : measurable_fun setT h)(Hh0 : ∀ b : T, 0 <= h b) (Hh : ∀ b : T, h b <= 1),
      μ S = 1 -> (\int[μ]_(x in ~` S) h x) = 0.
  { (* Integral is bounded above by integral of cst 1, which is 0, and below by integral of cst 0
       Can be simplified if there's a "integral over set w/ measure 0 is 0" lemma somewhere (can't find it)
     *)
    intros.
    apply le_anti_ereal; apply /andP; split.
    { eapply le_trans_ereal.
      { eapply (@ge0_le_integral _ _ _ _ _ _ _ (cst 1)); try done.
        apply @mathcomp_measurable_fun_restiction_setT; try done.
        by apply measurableC. }
      { rewrite integral_cst.
        { (* Need that the measure of a comeplement is bounded above by 1 - the measure of the set *)
          rewrite //= subprobability_1_setC; try done.
          by rewrite //= GRing.mulr0. }
        { by eapply @measurableC. }
      }
    }
    { eapply le_trans_ereal.
      { have -> : 0 = \int[μ]_(x in ~` S) (cst 0) x.
        { rewrite integral_cst //=; first by rewrite mul0e.
          by apply measurableC. }
        { eapply (@ge0_le_integral _ _ _ _ _ _ (cst 0)); try done.
          { apply @mathcomp_measurable_fun_restiction_setT; try done.
            by apply measurableC. }
          { by rewrite /cst//=. }
        }
      }
      apply ge0_le_integral; try done.
      { by apply measurableC. }
      { apply @mathcomp_measurable_fun_restiction_setT; try done. by apply measurableC. }
      { apply @mathcomp_measurable_fun_restiction_setT; try done. by apply measurableC. }
    }
  }
  rewrite L1; try done.
  rewrite L1; try done.
  rewrite GRing.add0r GRing.add0r.

  (* Change the left integral to the restriction of f *)
  rewrite (integral_mkcond SA).

  (* Change the right integral to the patch of g to 1 outside SB *)
  pose g' := patch (fun _ => 1) SB g.
  have Hg'M : measurable_fun [set: B] g'.
  { (* Same argument as if_in... refactor? *)
    rewrite -(setvU SB).
    apply <- measurable_funU; try done; first split.
    { eapply (@mathcomp_measurable_fun_ext _ _ _ _ _ _ (cst 1)); try done.
      intros b Hb.
      have Hb' : ¬ (SB b). { by rewrite /setC//= in Hb. }
      rewrite /g'/patch (memNset Hb').
      rewrite /cst//=.
    }
    { eapply (@mathcomp_measurable_fun_ext _ _ _ _ _ _ g); try done.
      { apply @mathcomp_measurable_fun_restiction_setT; try done. }
      intros b Hb.
      by rewrite /g'/patch (mem_set Hb).
    }
    by apply measurableC.
  }
  have Hg'g0 : ∀ b : B, 0 <= g' b.
  { intro b. case (ExcludedMiddle (SB b)); intros Hb.
    { by rewrite /g'/restrict/patch (mem_set Hb). }
    { by rewrite /g'/restrict/patch (memNset Hb). }
  }
  have Hg'l1 : ∀ a : B, g' a <= 1.
  { intro b. case (ExcludedMiddle (SB b)); intros Hb.
    { by rewrite /g'/restrict/patch (mem_set Hb). }
    { by rewrite /g'/restrict/patch (memNset Hb). }
  }

  (* Lemmas I'll need soon *)
  have HxM : measurable_fun [set: B] (g \_ SB).
  { apply @mathcomp_restriction_is_measurable; try done.
    apply @mathcomp_measurable_fun_restiction_setT; try done. }
  have Hxg0 : ∀ x : B, 0 <= (g \_ SB) x.
  { intro b. case (ExcludedMiddle (SB b)); intros Hb.
    { by rewrite /g'/restrict/patch (mem_set Hb). }
    { by rewrite /g'/restrict/patch (memNset Hb). }
  }
  have Hxl1 : ∀ b : B, (g \_ SB) b <= 1.
  { intro b. case (ExcludedMiddle (SB b)); intros Hb.
    { by rewrite /g'/restrict/patch (mem_set Hb). }
    { by rewrite /g'/restrict/patch (memNset Hb). }
  }

  have -> : \int[μ2]_(x in SB) g x = \int[μ2]_x g' x.
  { rewrite (integral_mkcond SB).
    (* Split the integrals into SB abs SB' *)
    rewrite (R1 _ _ _ SB) //.
    rewrite (R1 _ _ _ SB) //; first last.
    (* Integrals outside SB are zero *)
    rewrite L1; try done. rewrite GRing.add0r.
    rewrite L1; try done. rewrite GRing.add0r.
    (* On this set, the functions are equal *)
    apply eq_integral.
    apply in_setP.
    intros b Hb.
    rewrite /g'/restrict/patch.
    case (ExcludedMiddle (SB b)); intros HBin.
    { by rewrite (mem_set HBin) //=. }
    { by rewrite (memNset HBin) //=. }
  }

  pose f' := (f \_ SA).
  have Hf'M : measurable_fun [set: A] f'.
  { apply @mathcomp_restriction_is_measurable; try done.
    apply @mathcomp_measurable_fun_restiction_setT; try done. }
  have Hf'g0 : ∀ x : A, 0 <= f' x.
  { intro b. case (ExcludedMiddle (SA b)); intros Hb.
    { by rewrite /f'/restrict/patch (mem_set Hb). }
    { by rewrite /f'/restrict/patch (memNset Hb). }
  }
  have Hf'l1 : ∀ b : A, f' b <= 1.
  { intro b. case (ExcludedMiddle (SA b)); intros Hb.
    { by rewrite /f'/restrict/patch (mem_set Hb). }
    { by rewrite /f'/restrict/patch (memNset Hb). }
  }

  (* Reduced inequality *)
  have Lfg : (∀ (a : A) (b : B), R' a b → f' a <= g' b).
  { intros a b HR.
    case (ExcludedMiddle (SA a)); intros Ha;
    case (ExcludedMiddle (SB b)); intros Hb.
    { rewrite /f'/g'/restrict/patch (mem_set Ha) (mem_set Hb).
      by apply Hfg. }
    { rewrite /f'/g'/restrict/patch (mem_set Ha) (memNset Hb).
      done. }
    { rewrite /f'/g'/restrict/patch (memNset Ha) (mem_set Hb).
      by rewrite /point//=. }
    { rewrite /f'/g'/restrict/patch (memNset Ha) (memNset Hb).
      by rewrite /point//=. }
  }

  (* Finish *)
  eapply (Hμ1μ2 _ Hf'M Hf'g0 Hf'l1 _ Hg'M Hg'g0 Hg'l1 Lfg).
  Unshelve. all: try done; by apply measurableC.
Qed.

End ARcoupl_meas.



(*
Section ARcoupl_unif.

  Local Open Scope ring_scope.
  Local Open Scope ereal_scope.
  Local Open Scope classical_set_scope.

  (* Axioms about Lebesgue integrals over an interval, should be provable with change of variables *)
  Axiom leb_integral_cov_scale_ge0 :
    forall a b k (f : R -> \bar R),
      (a < b)%R ->
      (0 <= k)%R ->
      (measurable_fun setT f) ->
      (forall x, 0 <= (f x)) ->
      \int[lebesgue_measure]_(x in `[a, b]) (fun x => f (k*x)%R ) x = (1/k) * \int[lebesgue_measure]_(x in `[(k*a)%R, (k*b)%R]) f x.


  Axiom leb_integral_cov_scale_le0 :
    forall (a b : R) k f,
      (a < b)%R ->
      (k <= 0) ->
      (measurable_fun setT f) ->
      (forall x, 0 <= f x)%E ->
      \int[lebesgue_measure]_(x in `[a, b]) (fun x => f (k * x)) x = -(1/k) * \int[lebesgue_measure]_(x in `[(k*a)%R, (k*b)%R]) f x.

  Axiom leb_integral_cov_shift :
    forall (a b : R) d f,
      (a < b)%R ->
      (measurable_fun setT f) ->
      (forall x, 0 <= f x)%E ->
      \int[lebesgue_measure]_(x in `[a, b]) (fun x => f (x + d)) x = -(1/k) * \int[lebesgue_measure]_(x in `[(a+d)%R, (b+d)%R]) f x.


  Lemma ARcoupl_meas_unif_rev (a b : R) (Hab : Order.lt a b) :
     ARcoupl_meas (uniform_prob Hab) (uniform_prob Hab) (fun n m => m = GRing.add (GRing.add a b) (GRing.opp n) ) GRing.zero 0.
  Proof.
    intros f Hfm Hfge0 Hfle1 g Hgm Hgge0 Hgle1 Hfg.
    rewrite integral_uniform; auto.
    rewrite integral_uniform; auto.
    rewrite GRing.add0r.
    rewrite exp.expR0.
    rewrite mul1e.
    rewrite Rintegration_by_parts.
    rewrite integral_itv_bndo_bndc.

    Search patch.
   eapply (ARcoupl_meas_preserve).
   intros S ?.
   Search ocitv.
   Unshelve.
   Set Printing All.
*)

Section ARcoupl.

Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope classical_set_scope.

Context {d1 d2} {A : measurableType d1} {B : measurableType d2}.

Lemma ARcoupl_dzero_dzero (R : A → B → Prop) :
  ARcoupl_meas gZero gZero R 0 0.
Proof.
  intros f ? ? ? g ? ? ? HR.
  rewrite /gZero.
  rewrite integral_measure_zero.
  rewrite add0e.
  rewrite exp.expR0.
  rewrite mul1e.
  rewrite integral_measure_zero.
  done.
Qed.

Lemma ARcoupl_dzero_r_inv μ1 (R : A → B → Prop) :
  ARcoupl_meas μ1 gZero R 0 0 → μ1 ≡μ gZero.
Proof.
  intros Hz%ARcoupl_meas_mass_leq.
  intros S HS.
  rewrite /gZero//=/mzero//= in Hz.
  rewrite /gZero//=/mzero//=.
  rewrite adde0 in Hz.
  rewrite mule0 in Hz.
  eapply subset_measure0; [done | by eapply @measurableT | by rewrite /subset//= | ].
  apply le_anti_ereal; apply /andP; split.
  { unfold Order.le in Hz. by apply Hz. }
  { have X := measure_ge0 μ1 setT. unfold Order.le in X. by apply X. }
Qed.

Lemma ARcoupl_dzero (μ : giryM B) (R: A → B → Prop) (ε : nonnegreal) :
  (0 <= ε)%R ->
  ARcoupl_meas gZero μ R 0 (EFin (nonneg ε)).
Proof.
  intros Hleq f Hfm Hflb Hfub g Hgm Hglb Hgub HR.
  rewrite /gZero.
  rewrite exp.expR0.
  rewrite integral_measure_zero.
  rewrite mul1e.
  eapply @adde_ge0.
  { apply (Coq.ssr.ssrbool.introT (RlebP _ _)).
    by apply Hleq. }
  apply integral_ge0.
  intros x _.
  by apply Hglb.
Qed.

(*
Lemma Rcoupl_dzero_l_inv `{Countable A, Countable B} μ2 (R : A → B → Prop) :
  Rcoupl dzero μ2 R → μ2 = dzero.
Proof.
  intros Hz%Rcoupl_mass_eq.
  apply SeriesC_zero_dzero.
  rewrite -Hz SeriesC_0 //.
Qed.

Lemma ARcoupl_map `{Countable A, Countable B, Countable A', Countable B'}
  (f : A → A') (g : B → B') (μ1 : distr A) (μ2 : distr B) (R : A' → B' → Prop) ε :
  (0 <= ε) ->
  ARcoupl μ1 μ2 (λ a a', R (f a) (g a')) ε → ARcoupl (dmap f μ1) (dmap g μ2) R ε.
Proof.
  intros Hleq Hcoupl. rewrite /dmap.
  rewrite -(Rplus_0_r ε).
  eapply (ARcoupl_dbind _ _ _ _ (λ (a : A) (a' : B), R (f a) (g a')) _ ε 0); auto; [lra |].
  intros a b Hab.
  by eapply ARcoupl_dret.
Qed.

Lemma ARcoupl_eq_trans_l `{Countable A, Countable B} μ1 μ2 μ3 (R: A → B → Prop) ε1 ε2 :
  (0 <= ε1) ->
  (0 <= ε2) ->
  ARcoupl μ1 μ2 (=) ε1 ->
  ARcoupl μ2 μ3 R ε2 ->
  ARcoupl μ1 μ3 R (ε1 + ε2).
Proof.
  intros Hleq1 Hleq2 Heq HR f g Hf Hg Hfg.
  specialize (HR f g Hf Hg Hfg).
  eapply Rle_trans; [apply Heq | ]; auto.
  - intros ? ? ->; lra.
  - rewrite (Rplus_comm ε1) -Rplus_assoc.
    apply Rplus_le_compat_r; auto.
Qed.

Lemma ARcoupl_eq_trans_r `{Countable A, Countable B} μ1 μ2 μ3 (R: A → B → Prop) ε1 ε2 :
  (0 <= ε1) ->
  (0 <= ε2) ->
  ARcoupl μ1 μ2 R ε1 ->
  ARcoupl μ2 μ3 (=) ε2 ->
  ARcoupl μ1 μ3 R (ε1 + ε2).
Proof.
  intros Hleq1 Hleq2 HR Heq f g Hf Hg Hfg.
  specialize (HR f g Hf Hg Hfg).
  eapply Rle_trans; eauto.
  rewrite (Rplus_comm ε1) -Rplus_assoc.
  apply Rplus_le_compat_r.
  apply Heq; eauto.
  intros; simplify_eq; lra.
Qed.

(* Maybe this can be generalized, but for now I only need this version *)
Lemma ARcoupl_from_eq_Rcoupl `{Countable A} (μ1 μ2 : distr A) ε :
  (0 <= ε) ->
  Rcoupl μ1 μ2 (=) ->
  ARcoupl μ1 μ2 (=) ε.
Proof.
  intros Hε Hcpl.
  rewrite (Rcoupl_eq_elim μ1 μ2); auto.
  apply (ARcoupl_mon_grading _ _ _ 0); auto.
  apply ARcoupl_eq.
Qed.


Lemma ARcoupl_dunif (N : nat) f `{Bij (fin N) (fin N) f} :
  ARcoupl (dunif N) (dunif N) (λ n m, m = f n) 0.
Proof.
  intros g h Hg Hh Hgh.
  rewrite !SeriesC_finite_foldr.
  rewrite Rplus_0_r.
  assert (exists l : list (fin N),
             foldr (Rplus ∘ (λ a : fin N, dunif N a * g a)) 0 (enum (fin N))
             <= foldr (Rplus ∘ (λ b : fin N, if bool_decide (b ∈ l) then dunif N b * h b else 0)) 0 (enum (fin N))) as [l H1]; last first.
  - etrans; first exact. remember (enum (fin N)) as n eqn:Heqn. clear Heqn H1.
    induction n.
    + done.
    + simpl. case_bool_decide; try lra.
      assert (0<=dunif N a * h a); last lra.
      apply Rmult_le_pos; [done|apply Hh].
  - remember (enum (fin N)) as n eqn:Heqn. rewrite {2}Heqn.
    assert (NoDup n) as Hnd.
    { subst. apply NoDup_enum. }
    clear Heqn.
    cut (
        foldr (Rplus ∘ (λ a : fin N, dunif N a * g a)) 0 n <=
          foldr (Rplus ∘ (λ b : fin N, if bool_decide (b ∈ f<$>n) then dunif N b * h b else 0)) 0
            (enum (fin N))).
    { intros. eexists _. done. }
    revert Hnd.
    induction n.
    + intros. clear. simpl. induction (fin_enum N); first done. simpl. lra.
    + intros Hnd. rewrite NoDup_cons in Hnd. destruct Hnd as [Hnd1 Hnd2].
      specialize (IHn Hnd2).
      simpl.
      trans (foldr (Rplus ∘ (λ b : fin N, if bool_decide (b = f a) then dunif N b * h b else 0)) 0
               (fin_enum N) + foldr (Rplus ∘ (λ b : fin N, if bool_decide (b ∈ f<$>n) then dunif N b * h b else 0)) 0 (fin_enum N)).
      * apply Rplus_le_compat; last done.
        trans (dunif N (f a) * h (f a)).
        { apply Rmult_le_compat; naive_solver. }
        clear IHn Hnd1 Hnd2.
        assert (f a ∈ fin_enum N).
        { replace (fin_enum _) with (enum (fin N)); last done.
          apply elem_of_enum.
        }
        apply elem_of_list_split in H0.
        destruct H0 as [?[? ->]].
        induction x.
        -- simpl. case_bool_decide; last done.
           apply Rle_plus_l; first lra.
           induction x0; simpl; first lra.
           case_bool_decide; try lra.
           apply Rplus_le_le_0_compat; last lra.
           apply Rmult_le_pos; naive_solver.
        -- simpl. assert (0<=if (bool_decide (a0 = f a)) then dunif N a0 * h a0 else 0); last lra.
           case_bool_decide; last lra.
           apply Rmult_le_pos; naive_solver.
      * induction (fin_enum N); first (simpl; lra).
        simpl.
        repeat case_bool_decide; subst.
        -- apply elem_of_list_fmap_2_inj in H1; first done. by destruct H.
        -- set_solver.
        -- lra.
        -- set_solver.
        -- lra.
        -- set_solver.
        -- set_solver.
        -- lra.
Qed.

Lemma ARcoupl_Bij (N : nat) f `{Bij (fin N) (fin N) f} (ε:nonnegreal):
  ARcoupl (dunif N) (dunif N) (λ n m, m = f n) ε <->
    ARcoupl (dmap f (dunif N)) (dmap id (dunif N)) (=) ε.
Proof.
  split; intros H1.
  - apply ARcoupl_map; first apply cond_nonneg.
    eapply ARcoupl_mono; last done; naive_solver.
  - rewrite dmap_id in H1.
    replace (nonneg ε) with (0+nonneg ε); last lra.
    eapply ARcoupl_eq_trans_r; [done|apply cond_nonneg| |done].
    erewrite <-(dmap_id (dunif N)) at 1.
    apply ARcoupl_map; first done.
    eapply ARcoupl_mono; last apply (ARcoupl_dunif _ id); naive_solver.
Qed.


Lemma ARcoupl_dunif_leq_inj (N M : nat) h `{Inj (fin N) (fin M) (=) (=) h}:
  (0 < N <= M) -> ARcoupl (dunif N) (dunif M) (λ n m, m = h n) ((M-N)/M).
Proof.
  intros Hleq f g Hg Hf Hfg.
  etrans; last first.
  { apply Rplus_le_compat_r.
    eapply (SeriesC_filter_leq _ (λ b, ∃ a, b = h a)).
    - intros. rewrite dunif_pmf. apply Rmult_le_pos.
      + rewrite -Rdiv_1_l. apply Rdiv_le_0_compat; lra.
      + naive_solver.
    - apply ex_seriesC_finite.
  }
  simpl.
  etrans; last first.
  { apply Rplus_le_compat_r.
    pose (hsome := λ x, Some (h x)).
    eapply (SeriesC_le_inj _ hsome).
    - intros. case_bool_decide; last lra.
      intros. rewrite dunif_pmf. apply Rmult_le_pos.
      + rewrite -Rdiv_1_l. apply Rdiv_le_0_compat; lra.
      + naive_solver.
    - rewrite /hsome. naive_solver.
    - apply ex_seriesC_finite.
  } simpl.
  etrans; last first.
  { apply Rplus_le_compat_l.
    instantiate (1:= SeriesC (λ x: fin N, (M-N)/(M*N))).
    rewrite SeriesC_finite_mass fin_card Rmult_div_assoc.
    rewrite (Rmult_comm N (M-N)). rewrite !Rdiv_def Rmult_assoc.
    apply Rmult_le_compat_l; first lra.
    rewrite -(Rdiv_1_l M). rewrite -Rdiv_def- Rle_div_r; last lra.
    apply Req_le_sym. rewrite Rdiv_mult_distr !Rdiv_def.
    rewrite (Rmult_assoc N) (Rmult_comm (/ M)) -Rmult_assoc.
    rewrite Rmult_inv_r; last lra.
    rewrite Rmult_1_l. rewrite Rmult_comm Rmult_inv_r; lra.
  }
  rewrite -SeriesC_plus; [|apply ex_seriesC_finite|apply ex_seriesC_finite].
  apply SeriesC_le; last apply ex_seriesC_finite.
  intros. case_bool_decide; last first.
  { exfalso. naive_solver. }
  split.
  - intros. rewrite dunif_pmf. apply Rmult_le_pos.
    + rewrite -Rdiv_1_l. apply Rdiv_le_0_compat; lra.
    + naive_solver.
  - intros. rewrite !dunif_pmf.
    etrans.
    { apply Rmult_le_compat_l.
      - rewrite -Rdiv_1_l. apply Rdiv_le_0_compat; lra.
      - apply Hfg. reflexivity.
    }
    cut ((/ N - / M)* g (h n) <=  (M - N) / (M * N)); first lra.
    trans ((/ N - / M)*1).
    + apply Rmult_le_compat_l; last naive_solver.
      rewrite -Rminus_le_0. apply Rinv_le_contravar; lra.
    + rewrite Rmult_1_r.
      cut (/ N - / M <= M / (M * N) - N/ (M*N)); first lra.
      cut (/N = M/(M*N)/\ /M=N/(M*N)); first lra.
      split.
      * rewrite -Rdiv_1_l. erewrite <-Rdiv_mult_l_l.
        -- f_equal. lra.
        -- lra.
      * rewrite -Rdiv_1_l. erewrite <-Rdiv_mult_l_r.
        -- f_equal. lra.
        -- lra.
Qed.

Lemma ARcoupl_dunif_leq (N M : nat):
  (0 < N <= M) -> ARcoupl (dunif N) (dunif M) (λ n m, fin_to_nat n = m) ((M-N)/M).
Proof.
  intros Hleq f g Hf Hg Hfg.
  assert (∀ x:fin N, (fin_to_nat x < M)%nat) as Hineq.
  { intros x. pose proof fin_to_nat_lt x. destruct Hleq as [? H1].
    apply INR_le in H1. lia. }
  eapply (ARcoupl_dunif_leq_inj _ _ (λ x:fin N, nat_to_fin (Hineq x))); try done.
  intros. apply Hfg.
  subst. by rewrite fin_to_nat_to_fin.
  Unshelve.
  intros ?? H. apply (f_equal fin_to_nat) in H.
  rewrite !fin_to_nat_to_fin in H.
  by apply fin_to_nat_inj.
Qed.

(* Note the asymmetry on the error wrt to the previous lemma *)
Lemma ARcoupl_dunif_leq_rev_inj (N M : nat) h `{Inj (fin M) (fin N) (=) (=) h}:
  (0 < M <= N) -> ARcoupl (dunif N) (dunif M) (λ n m, n = h m) ((N-M)/N).
Proof.
  intros Hleq f g Hf Hg Hfg.
  rewrite /pmf/=.
  do 2 rewrite SeriesC_scal_l.
  rewrite Rmult_comm.
  apply Rle_div_r.
  - apply Rlt_gt.
    apply Rinv_0_lt_compat; lra.
  - rewrite /Rdiv Rinv_inv Rmult_plus_distr_r.
    rewrite (Rmult_assoc (N-M)) Rinv_l; [ | lra].
    rewrite Rmult_1_r Rplus_comm.
    assert (SeriesC f <= SeriesC g + (N - M)) as Haux.
    { erewrite (SeriesC_split_pred _ (λ x, (bool_decide (∃ y, x= h y)))); [|naive_solver|apply ex_seriesC_finite].
      apply Rplus_le_compat.
      - apply SeriesC_filter_finite_1'; try done.
        destruct Hleq. split; [apply INR_lt|by apply INR_le].
        by simpl.
      - trans (SeriesC (λ a : fin (N-M), 1)); last first.
        + rewrite SeriesC_finite_mass fin_card Rmult_1_r minus_INR; try lra. apply INR_le. naive_solver.
        + etrans; first apply SeriesC_filter_finite_2; try done.
          * destruct Hleq. split; [apply INR_lt|by apply INR_le].
            by simpl.
          * rewrite SeriesC_finite_mass. rewrite fin_card. lra.
    }
    apply (Rle_trans _ (SeriesC g + (N - M))); auto.
    rewrite Rplus_comm.
    apply Rplus_le_compat_l.
    assert (0<=SeriesC g) as Hpos.
    { apply SeriesC_ge_0'. naive_solver. }
    rewrite Rmult_comm (Rmult_comm (/M)).
    rewrite -Rdiv_def Rmult_div_assoc.
    rewrite -Rle_div_r; last lra.
    rewrite Rmult_comm.
    apply Rmult_le_compat_r; lra.
Qed.

Lemma ARcoupl_dunif_leq_rev (N M : nat) :
  (0 < M <= N) -> ARcoupl (dunif N) (dunif M) (λ n m, fin_to_nat n = m) ((N-M)/N).
Proof.
  intros Hleq f g Hf Hg Hfg.
  assert (∀ x:fin M, (fin_to_nat x < N)%nat) as Hineq.
  { intros x. pose proof fin_to_nat_lt x. destruct Hleq as [? H1].
    apply INR_le in H1. lia. }
  eapply (ARcoupl_dunif_leq_rev_inj _ _ (λ x:fin M, nat_to_fin (Hineq x))); try done.
  intros. apply Hfg.
  subst. by rewrite fin_to_nat_to_fin.
  Unshelve.
  intros ?? H. apply (f_equal fin_to_nat) in H.
  rewrite !fin_to_nat_to_fin in H.
  by apply fin_to_nat_inj.
Qed.


Lemma ARcoupl_dunif_no_coll_l `{Countable A} (v : A) (N : nat) (x : fin N) :
  (0 < N ) -> ARcoupl (dunif N) (dret v) (λ m n, m ≠ x ∧ n = v) (1/N).
Proof with try (by apply ex_seriesC_finite) ; auto ; try done.
  intros Hleq f g Hf Hg Hfg.
  rewrite /pmf/=/dret_pmf.
  assert (∀ b, 0 <= g b) by apply Hg.
  assert (∀ b, g b <= 1) by apply Hg.
  assert (∀ a, 0 <= f a) by apply Hf.
  assert (∀ a, f a <= 1) by apply Hf.
  assert (0 <= / N) by (left ; apply Rinv_0_lt_compat ; lra).
  assert (forall n, 0 <= / N * f n).
  { intros ; apply Rmult_le_pos... }
  setoid_rewrite (SeriesC_ext _ (λ b, (if bool_decide (b = v) then g v else 0))) at 1; last first.
  { intro ; case_bool_decide ; simplify_eq ; real_solver. }
  transitivity (SeriesC (λ a : fin N, if bool_decide (a = x) then 1 / N else / N * f a )).
  { apply SeriesC_le...
    intros ; case_bool_decide ; split...
    rewrite -(Rmult_1_r (1/N)).
    apply Rmult_le_compat... nra. }
  rewrite (SeriesC_split_elem _ x)...
  - rewrite Rplus_comm.
    apply Rplus_le_compat.
    + etrans.
      * apply (SeriesC_finite_bound _ (/ N * g v)).
        intros; split.
        -- case_bool_decide; [|lra].
           rewrite bool_decide_eq_false_2...
        -- case_bool_decide.
           2: apply Rmult_le_pos...
           rewrite bool_decide_eq_false_2...
           apply Rmult_le_compat_l...
      * rewrite SeriesC_singleton fin_card.
        rewrite -Rmult_assoc Rinv_r ; lra.
    + etrans ; [ | right; apply (SeriesC_singleton x (1/N))].
      right ; apply SeriesC_ext => n.
      by case_bool_decide.
  - intro ; case_bool_decide... lra.
Qed.

Corollary ARcoupl_dunif_no_coll_l' (N : nat) (x : fin N) :
  (0 < N ) -> ARcoupl (dunif N) (dret x) (λ m n, m ≠ x ∧ n = x) (1/N).
Proof.
  apply ARcoupl_dunif_no_coll_l.
Qed.

Lemma ARcoupl_dunif_no_coll_r `{Countable A} (v : A) (N : nat) (x : fin N) :
  (0 < N ) -> ARcoupl (dret v) (dunif N) (λ m n, m = v ∧ n ≠ x) (1/N).
Proof with try (by apply ex_seriesC_finite) ; auto ; try done.
  intros Hleq f g Hf Hg Hfg.
  rewrite /pmf/=/dret_pmf.
  assert (∀ b, 0 <= g b) by apply Hg.
  assert (∀ b, g b <= 1) by apply Hg.
  assert (∀ a, 0 <= f a) by apply Hf.
  assert (∀ a, f a <= 1) by apply Hf.
  assert (0 <= / N) by (left ; apply Rinv_0_lt_compat ; lra).
  assert (forall n, 0 <= / N * f n).
  { intros ; apply Rmult_le_pos... }
  assert (forall a, 0 <= / N * g a).
  { intros ; apply Rmult_le_pos... }
  setoid_rewrite (SeriesC_ext _ (λ a, (if bool_decide (a = v) then f v else 0))) ; last first.
  { intro ; case_bool_decide ; simplify_eq ; real_solver. }
  transitivity (SeriesC (λ n : fin N, if bool_decide (n = x) then 0 else / N * g n) + 1/N) ; last first.
  { apply Rplus_le_compat...
    apply SeriesC_le...
    intros n.
    case_bool_decide... }
  rewrite -(SeriesC_singleton x (1 / N)).
  rewrite -SeriesC_plus...
  transitivity (SeriesC (λ _ : fin N, / N * f v)).
  + rewrite SeriesC_finite_mass SeriesC_singleton fin_card.
    rewrite -Rmult_assoc Rinv_r ; lra.
  + apply SeriesC_le...
    intros ; split...
    case_bool_decide.
    * rewrite Rplus_0_l -(Rmult_1_r (1/N)).
      apply Rmult_le_compat... nra.
    * rewrite Rplus_0_r. apply Rmult_le_compat_l...
Qed.

Corollary ARcoupl_dunif_no_coll_r' (N : nat) (x : fin N) :
  (0 < N) -> ARcoupl (dret x) (dunif N) (λ m n, m = x ∧ n ≠ x) (1/N).
Proof.
  eapply ARcoupl_dunif_no_coll_r.
Qed.

Lemma UB_to_ARcoupl `{Countable A, Countable B} (μ1 : distr A) (P : A -> Prop) (ε : R) :
  pgl μ1 P ε ->
  ARcoupl μ1 (dret tt) (λ a _, P a) ε.
Proof.
  rewrite /pgl /prob.
  intros Hub f g Hf Hg Hfg.
  rewrite SeriesC_finite_foldr; simpl.
  rewrite dret_1_1; last done.
  rewrite Rmult_1_l Rplus_0_r.
  remember ((λ a:A, negb (bool_decide (P a)))) as q.
  rewrite (SeriesC_split_pred _ q).
  - rewrite Rplus_comm.
    apply Rplus_le_compat.
    + trans (SeriesC (λ a : A, if q a then 0 else μ1 a * g ())).
      * apply SeriesC_le; first subst.
        -- intros. case_bool_decide; simpl; try lra.
           split.
           ++ apply Rmult_le_pos; naive_solver.
           ++ apply Rmult_le_compat_l; auto.
        -- eapply (ex_seriesC_ext (λ a : A, if bool_decide (P a) then μ1 a * g () else 0)); last eapply ex_seriesC_filter_pos.
           ++ intros. subst. repeat case_bool_decide; done.
           ++ intros; apply Rmult_le_pos; naive_solver.
           ++ apply ex_seriesC_scal_r. done.
      * trans (SeriesC (λ a, μ1 a * g ())).
        -- apply SeriesC_le; last by apply ex_seriesC_scal_r.
           intros. subst. case_bool_decide; simpl; split; try lra.
           all: apply Rmult_le_pos; naive_solver.
        -- rewrite SeriesC_scal_r. etrans; first apply Rmult_le_compat_r; auto.
           ++ naive_solver.
           ++ lra.
    + etrans; last exact.
      apply SeriesC_le.
      * subst. intros. case_bool_decide; simpl; try lra.
        split.
        -- apply Rmult_le_pos; naive_solver.
        -- rewrite <- Rmult_1_r. apply Rmult_le_compat; naive_solver.
      * apply ex_seriesC_filter_bool_pos; auto.
  - intros. apply Rmult_le_pos; naive_solver.
  - apply pmf_ex_seriesC_mult_fn. naive_solver.
Qed.

Lemma ARcoupl_to_UB `{Countable A, Countable B} (μ1 : distr A) (μ2 : distr B) (P : A -> Prop) (ε : R) :
  ARcoupl μ1 μ2 (λ a _, P a) ε -> pgl μ1 P ε.
Proof.
  rewrite /ARcoupl/pgl/prob.
  intros Har.
  eset (λ a:A, if bool_decide (P a) then 0 else 1) as f.
  eset (λ b:B, 0) as g.
  specialize (Har f g).
  replace (ε) with (SeriesC (λ b, μ2 b * g b) + ε).
  { etrans; last apply Har.
    - apply SeriesC_le; last apply pmf_ex_seriesC_mult_fn.
      + intros. rewrite /f. repeat case_bool_decide; try done; simpl; split; try lra.
        done.
      + exists 1. rewrite /f. intros; case_match; lra.
    - intros. rewrite /f. case_match; lra.
    - rewrite /g. intros; lra.
    - intros. rewrite /f/g. case_match; first done.
      apply bool_decide_eq_false in H2. done. }
  rewrite /g.
  rewrite SeriesC_scal_r. lra.
Qed.

Lemma up_to_bad_lhs `{Countable A, Countable B} (μ1 : distr A) (μ2 : distr B) (P : A -> Prop) (Q : A → B → Prop) (ε ε' : R) :
  ARcoupl μ1 μ2 (λ a b, P a -> Q a b) ε ->
  pgl μ1 P ε' ->
  ARcoupl μ1 μ2 Q (ε + ε').
Proof.
  intros Hcpl Hub f g Hf Hg Hfg.
  set (P' := λ a, bool_decide (P a)).
  set (f' := λ a, if bool_decide (P a) then f a else 0).
  (* epose proof (Hub P' _) as Haux. *)
  (* Unshelve. *)
  (* 2:{ *)
  (*   intros a Ha; rewrite /P'. *)
  (*   case_bool_decide; auto. *)
  (* } *)
  (* rewrite /prob in Haux. *)
  rewrite -Rplus_assoc.
  eapply Rle_trans; [ | by apply Rplus_le_compat_l].
  eapply Rle_trans; last first.
  - eapply Rplus_le_compat_r.
    eapply (Hcpl f' g); auto.
    + intro a; specialize (Hf a).
      rewrite /f'; real_solver.
    + intros a b HPQ; rewrite /f'.
      case_bool_decide; [apply Hfg; auto | apply Hg ].
  - rewrite /f' /P' -SeriesC_plus.
    + apply SeriesC_le.
      * intro a; specialize (Hf a); split; [real_solver |].
        case_bool_decide; simpl; [lra | ].
        rewrite Rmult_0_r Rplus_0_l.
        real_solver.
      * apply (ex_seriesC_le _ (λ x, (μ1 x)*2)); [ | apply ex_seriesC_scal_r; auto].
        intro a; specialize (Hf a); split.
        -- case_bool_decide; simpl.
           ++ rewrite Rplus_0_r. real_solver.
           ++ rewrite Rmult_0_r Rplus_0_l //.
        -- case_bool_decide; simpl.
           ++ rewrite Rplus_0_r. real_solver.
           ++ rewrite Rmult_0_r Rplus_0_l //.
              rewrite <- Rmult_1_r at 1.
              real_solver.
    + apply (ex_seriesC_le _ μ1); auto.
      intro a; specialize (Hf a); real_solver.
    + apply (ex_seriesC_le _ μ1); auto.
      intro a; specialize (Hf a); real_solver.
Qed.


Lemma up_to_bad_rhs `{Countable A, Countable B} (μ1 : distr A) (μ2 : distr B) (P : B -> Prop) (Q : A → B → Prop) (ε ε' : R) :
  ARcoupl μ1 μ2 (λ a b, P b -> Q a b) ε ->
  pgl μ2 P ε' ->
  ARcoupl μ1 μ2 Q (ε + ε').
Proof.
  intros Hcpl Hub f g Hf Hg Hfg.
  set (P' := λ a, bool_decide (P a)).
  set (g' := λ a, if bool_decide (P a) then g a else 0).
  rewrite -Rplus_assoc.
  eapply Rle_trans; [ | by apply Rplus_le_compat_l].
  clear Hub.

  rewrite Rplus_assoc (Rplus_comm ε) -Rplus_assoc.
  rewrite -SeriesC_plus.
  2,3: apply (ex_seriesC_le _ (λ b : B, μ2 b)) => // ; real_solver.
  unfold ARcoupl in Hcpl.
  trans (SeriesC (λ b : B, μ2 b * g b + μ2 b * (if negb (bool_decide (P b)) then 1 else 0)) + ε) ; [|(right ; f_equal ; series)].
  setoid_rewrite <-Rmult_plus_distr_l.
  trans (SeriesC
           (λ b : B, μ2 b * Rmin 1 (g b + (if negb (bool_decide (P b)) then 1 else 0))) + ε).
  2:{ apply Rplus_le_compat_r. apply SeriesC_le.
      2:{
        eapply (ex_seriesC_le _ (λ b : B, μ2 b * (1 + 1))).
        2: apply ex_seriesC_scal_r => //.
        intros b. assert (0 <= g b) by real_solver.
        repeat real_solver_partial.
        all: apply Rplus_le_compat ; real_solver.
      }
      intros b.
      assert (0 <= g b /\ (g b <= 1)) by real_solver.
      repeat real_solver_partial.
      - rewrite Rmin_right ; real_solver.
      - rewrite Rmin_right ; real_solver.
      - rewrite Rmin_left ; real_solver.
      - rewrite Rmin_left ; real_solver.
  }
  apply Hcpl.
  1: real_solver.
  - intros b ; assert (0 <= g b /\ (g b <= 1)) by real_solver.
    repeat real_solver_partial.
    + rewrite Rmin_right ; real_solver.
    + rewrite Rmin_right ; real_solver.
    + rewrite Rmin_left ; real_solver.
    + rewrite Rmin_left ; real_solver.
  - repeat real_solver_partial.
    + rewrite Rplus_0_r. trans (g b). 1: eauto. rewrite Rmin_right. 1: lra. real_solver.
    + rewrite Rmin_left. 2: assert (0 <= g b) by real_solver ; real_solver.
      real_solver.
Qed.


Lemma ARcoupl_refRcoupl `{Countable A, Countable B}
  μ1 μ2 (ψ : A → B → Prop) : refRcoupl μ1 μ2 ψ -> ARcoupl μ1 μ2 ψ 0.
Proof.
  intros (μ&(<-&Hrm)&Hs).
  setoid_rewrite rmarg_pmf in Hrm.
  intros f g Hf Hg Hfg.
  rewrite Rplus_0_r.
  setoid_rewrite lmarg_pmf.
  etrans; last first.
  {
    apply SeriesC_le.
    - split; last first.
      + apply Rmult_le_compat_r; [apply Hg | apply Hrm].
      + simpl. apply Rmult_le_pos; [ | apply Hg].
        by apply SeriesC_ge_0'.
    - eapply ex_seriesC_le ; [ | eapply (pmf_ex_seriesC μ2)].
      intros; split.
      * apply Rmult_le_pos; auto. apply Hg.
      * rewrite <- Rmult_1_r.
        apply Rmult_le_compat_l; auto. apply Hg.
  }
  setoid_rewrite <- SeriesC_scal_r.
  rewrite (fubini_pos_seriesC (λ '(a,n), Rmult (μ (a, n)) (g n))).
  - apply SeriesC_le.
    + intro a; split.
      * apply SeriesC_ge_0'.
        intro.
        apply Rmult_le_pos; auto. apply Hf.
      * apply SeriesC_le.
        ** intro b; split.
           *** apply Rmult_le_pos; auto.
               apply Hf.
           *** destruct (decide ((μ(a,b) > 0)%R)) as [H3 | H4].
               **** apply Hs, Hfg in H3.
                    by apply Rmult_le_compat_l.
               **** apply Rnot_gt_le in H4.
                    replace (μ(a,b)) with 0%R; [ lra | by apply Rle_antisym].
        ** eapply ex_seriesC_le; [ | eapply (ex_seriesC_lmarg μ); eauto ].
           intros; split.
           *** apply Rmult_le_pos; auto.
               apply Hg.
           *** rewrite <- Rmult_1_r.
               apply Rmult_le_compat_l; auto.
               apply Hg.
    + eapply ex_seriesC_le; [ | eapply (fubini_pos_ex_seriesC_prod_ex_lr μ)]; eauto.
      * intro; simpl.
        split.
        ** apply SeriesC_ge_0'.
           intro; apply Rmult_le_pos; auto.
           apply Hg.
        ** apply SeriesC_le.
           *** intro; split.
               **** apply Rmult_le_pos; auto. apply Hg.
               **** rewrite <- Rmult_1_r.
                    apply Rmult_le_compat_l; eauto; eapply Hg.
           *** apply ex_seriesC_lmarg; auto.
  - intros; apply Rmult_le_pos; auto. apply Hg.
  - intros a.
    eapply ex_seriesC_le; [ | unshelve eapply (ex_seriesC_lmarg μ _ a) ]; eauto.
    intros. split.
    + apply Rmult_le_pos; auto. apply Hg.
    + rewrite <- Rmult_1_r. apply Rmult_le_compat_l; auto; apply Hg.
  - eapply ex_seriesC_le; [ | eapply (fubini_pos_ex_seriesC_prod_ex_lr μ)]; eauto.
    + intro; simpl.
      split.
      * apply SeriesC_ge_0'.
        intro; apply Rmult_le_pos; auto.
        apply Hg.
      * apply SeriesC_le.
        ** intro; split.
           *** apply Rmult_le_pos; auto. apply Hg.
           *** rewrite <- Rmult_1_r.
               apply Rmult_le_compat_l; eauto; eapply Hg.
        ** apply ex_seriesC_lmarg; auto.
Qed.

Lemma ARcoupl_exact `{Countable A, Countable B}
  μ1 μ2 (ψ : A → B → Prop) : Rcoupl μ1 μ2 ψ → ARcoupl μ1 μ2 ψ 0.
Proof.
  intros ; by eapply ARcoupl_refRcoupl, Rcoupl_refRcoupl.
Qed.

Lemma ARcoupl_limit `{Countable A, Countable B} μ1 μ2 ε (ψ : A -> B -> Prop):
  (forall ε', ε' > ε -> ARcoupl μ1 μ2 ψ ε') -> ARcoupl μ1 μ2 ψ ε.
Proof.
  rewrite /ARcoupl.
  intros Hlimit. intros.
  apply real_le_limit.
  intros. rewrite Rle_minus_l.
  rewrite Rplus_assoc.
  apply Hlimit; try done.
  lra.
Qed.

Lemma ARcoupl_antisym `{Countable A} (μ1 μ2: distr A):
  ARcoupl μ1 μ2 eq 0 -> ARcoupl μ2 μ1 eq 0 ->
  μ1 = μ2.
Proof.
  intros H1 H2.
  apply distr_ext.
  intros a.
  pose proof (ARcoupl_eq_elim _ _ _ H1 a).
  pose proof (ARcoupl_eq_elim _ _ _ H2 a). lra.
Qed. 
  
Lemma ARcoupl_tight `{Countable A} (μ1 μ2 : distr A) ε:
  ARcoupl μ1 μ2 eq ε <-> SeriesC (λ x, if bool_decide (μ2 x <= μ1 x) then μ1 x - μ2 x else 0) <= ε.
Proof.
  split.
  - rewrite /ARcoupl.
    set (f:=λ x, if bool_decide (μ2 x <= μ1 x) then 1 else 0).
    intros Hcoupl.
    assert (∀ x, 0<=f x <=1).
    { intros. rewrite /f. case_bool_decide; lra. }
    eassert (SeriesC _ <= SeriesC _ + _) as H'.
    { apply (Hcoupl f f); naive_solver. }
    rewrite Rplus_comm -Rle_minus_l in H'.
    etrans; last exact.
    rewrite Rle_minus_r.
    apply Req_le.
    rewrite -SeriesC_plus; last first.
    + apply pmf_ex_seriesC_mult_fn. naive_solver.
    + apply ex_seriesC_le with μ1; last done.
      intros. case_bool_decide; try done.
      split; first lra.
      by apply Rminus_le_0_compat.
    + apply SeriesC_ext.
      intros. rewrite /f.
      case_bool_decide; lra.
  - intros HseriesC f g Hf Hg Hfg.
    rewrite Rplus_comm -Rle_minus_l.
    etrans; last exact.
    rewrite Rle_minus_l. 
    rewrite -SeriesC_plus; last first.
    + apply pmf_ex_seriesC_mult_fn. naive_solver.
    + apply ex_seriesC_le with μ1; last done.
      intros. case_bool_decide; try done.
      split; first lra.
      by apply Rminus_le_0_compat.
    + apply SeriesC_le.
      * intros n. split.
        { apply Rmult_le_pos; naive_solver. }
        case_bool_decide.
        -- assert (f n <= g n) by naive_solver.
           rewrite -Rle_minus_l.
           trans (μ1 n * f n - μ2 n * f n).
           ++ apply Ropp_le_cancel. rewrite !Ropp_minus_distr.
              apply Rplus_le_compat_r.
              apply Rmult_le_compat_l; [done|lra].
           ++ rewrite -Rmult_minus_distr_r.
              rewrite -{2}(Rmult_1_r (_-_)).
              apply Rmult_le_compat_l; last naive_solver.
              lra.
        -- trans (μ1 n * g n).
           ++ apply Rmult_le_compat_l; [done|naive_solver].
           ++ rewrite Rplus_0_l. apply Rmult_le_compat_r; [naive_solver|lra].
      * apply ex_seriesC_le with (λ x, μ1 x + μ2 x); last first.
        { by apply ex_seriesC_plus. }
        intros; split; case_bool_decide.
        -- trans (μ1 n - μ2 n); first lra.
           apply Rplus_le_0_compat.
           apply Rmult_le_pos; naive_solver.
        -- rewrite Rplus_0_l. apply Rmult_le_pos; naive_solver.
        -- trans (μ1 n).
           ++ cut (μ1 n + μ2 n * g n <= μ1 n + μ2 n*1); first lra.
              apply Rplus_le_compat_l.
              apply Rmult_le_compat_l; [done|naive_solver].
           ++ by apply Rplus_le_0_compat.
        -- trans (μ2 n * 1).
           ++ rewrite Rplus_0_l.
              apply Rmult_le_compat_l; [done|naive_solver].
           ++ rewrite Rmult_1_r.
              rewrite Rplus_comm.
              by apply Rplus_le_0_compat.
Qed.
                 
Lemma ARcoupl_swap `{Countable A} (μ1 μ2 : distr A) ε:
  SeriesC μ2 <= SeriesC μ1 -> (ARcoupl μ1 μ2 eq ε -> ARcoupl μ2 μ1 eq ε).
Proof.
  intros Heq.
  rewrite !ARcoupl_tight.
  intros; etrans; last exact.
  cut (SeriesC (λ x : A, if bool_decide (μ1 x <= μ2 x) then μ2 x - μ1 x else 0) + SeriesC μ1<=
         SeriesC (λ x : A, if bool_decide (μ2 x <= μ1 x) then μ1 x - μ2 x else 0) + SeriesC μ2).
  { intros. lra. }
  rewrite -!SeriesC_plus; last first; try done.
  - apply ex_seriesC_le with (μ2); last done.
    intros; case_bool_decide; split; try (lra||done).
    apply Rminus_le_0_compat. done.
  - apply ex_seriesC_le with (μ1); last done.
    intros; case_bool_decide; split; try (lra||done).
    apply Rminus_le_0_compat. done.
  - apply SeriesC_le; last first.
    + apply ex_seriesC_le with (λ x, μ1 x+ μ2 x); last first.
      * by apply ex_seriesC_plus.
      * intros n.
        pose proof pmf_pos μ1 n.
        pose proof pmf_pos μ2 n.
        intros; case_bool_decide; lra.
    + intros.
      pose proof pmf_pos μ1 n.
      pose proof pmf_pos μ2 n.
      intros; repeat case_bool_decide; lra.
Qed.

Lemma ARcoupl_symmetric `{Countable A} (μ1 μ2 : distr A) ε:
  SeriesC μ1 = SeriesC μ2 -> (ARcoupl μ1 μ2 eq ε <-> ARcoupl μ2 μ1 eq ε).
Proof.
  intros; split; intros; apply ARcoupl_swap; (lra||naive_solver).
Qed.
  
Lemma ARcoupl_dunif_avoid N (l:list (fin N)):
  NoDup l->
  ARcoupl (dunif N) (dunif N) (λ x y, x∉l /\ x=y) (length l/N).
Proof.
  intros Hl.
  cut (∀ ε, ARcoupl (dunif N) (ssd (λ x, bool_decide(x∉l)) (dunif N)) (=) ε ->
            ARcoupl (dunif N) (dunif N) (λ x y, x∉l /\ x=y) ε).
  {
    intros H.
    apply H.
    apply ARcoupl_tight.
    rewrite (SeriesC_ext _ (λ x, if bool_decide(x∈l) then 1/(N) else 0)).
    - rewrite SeriesC_list_2; [lra|done].
    - intros.
      rewrite bool_decide_eq_true_2; last first.
      { rewrite /ssd/ssd_pmf/pmf/=. case_bool_decide; try lra.
        rewrite -Rdiv_1_l.
        apply Rdiv_INR_ge_0.
      }
      rewrite /ssd/ssd_pmf{2}/pmf.
      case_bool_decide.
      + rewrite bool_decide_eq_false_2; last done.
        lra.
      + rewrite bool_decide_eq_true_2; last done.
        rewrite dunif_pmf. lra.
  }
  intros ε Hcoupl f g Hf Hg Hfg.
  pose (g':=λ x, if bool_decide (x∈l) then 1 else g x).
  assert (∀ b, 0<=g' b <=1).
  { rewrite /g'. intros. case_bool_decide; try lra. naive_solver. }
  epose proof Hcoupl f g' _ _ _.
  etrans; first exact.
  apply Rplus_le_compat_r.
  apply SeriesC_le; last apply pmf_ex_seriesC_mult_fn; last naive_solver.
  intros n; split.
  - apply Rmult_le_pos; naive_solver.
  - rewrite /g'.
    rewrite /ssd/ssd_pmf{1}/pmf.
    case_bool_decide.
    + by rewrite bool_decide_eq_false_2.
    + rewrite Rmult_0_l.
      apply Rmult_le_pos; naive_solver.
    Unshelve.
    all: try done.
    intros ?? ->.
    rewrite /g'.
    case_bool_decide; naive_solver.
Qed.
    
*)

End ARcoupl.

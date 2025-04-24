(** Axioms of a the Giry Monad type (a sigma algebra for subdistributions) *)
From mathcomp Require Import all_ssreflect all_algebra boolp classical_sets functions.
From mathcomp.analysis Require Import reals ereal measure lebesgue_measure lebesgue_integral Rstruct.
From clutch.prob.monad Require Export prelude tactics.
From clutch.prelude Require Import classical.
Import Coq.Relations.Relation_Definitions.
Require Import Coq.micromega.Lra.
From Coq Require Import Classes.Morphisms Reals Classes.RelationPairs.
From stdpp Require Import base tactics.
From HB Require Import structures.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Set Default Proof Using "Type".

Section giryM_def.
  Local Open Scope classical_set_scope.
  Context `{d : measure_display} (T : measurableType d).

  Definition giryM : Type := @subprobability d T R.

  Definition gEval (S : set T) (μ : giryM) := μ S.
  Definition gEvalPreImg (S : set T) := (preimage_class setT (gEval S) measurable).

  Definition giry_measurable := <<s \bigcup_(S in measurable) (gEvalPreImg S)>>.

  (*  Axiom giry_measurable : set (set giryM). *)
  Lemma giry_measurable0 : giry_measurable set0.
    Proof.
      apply sigma_algebra0.
  Qed.

  Lemma giry_measurableC : forall (S : set giryM),
    giry_measurable S -> giry_measurable (~` S).
  Proof.
    intros ? ?.
    rewrite -setTD.
    apply sigma_algebraCD.
    auto.
  Qed.

 Lemma giry_measurableU : forall (A : sequences.sequence (set giryM)),
    (forall i : nat, giry_measurable (A i)) -> giry_measurable (\bigcup_i A i).
 Proof.
   apply sigma_algebra_bigcup.
 Qed.

  Definition giry_display : measure_display.
  Proof. by constructor. Qed.

  Lemma mzero_setT : (@mzero d T R setT <= 1)%E.
  Proof. by rewrite /mzero/=. Qed.

  HB.instance Definition _ := gen_eqMixin giryM.
  HB.instance Definition _ := gen_choiceMixin giryM.
  HB.instance Definition _ := Measure_isSubProbability.Build _ _ _ (@mzero d T R) mzero_setT.
  HB.instance Definition _ := isPointed.Build giryM mzero.
  HB.instance Definition _ :=
    @isMeasurable.Build giry_display giryM giry_measurable
      giry_measurable0 giry_measurableC giry_measurableU.

End giryM_def.



Definition measure_eq `{d : measure_display} {T : measurableType d} : relation (giryM T) :=
  fun μ1 μ2 => forall (S : set T), measurable S -> μ1 S = μ2 S.
Notation "x ≡μ y" := (measure_eq x y) (at level 70).
Global Hint Extern 0 (_ ≡μ _) => reflexivity : core.
Global Hint Extern 0 (_ ≡μ _) => symmetry; assumption : core.

Instance equivalence_measure_eq `{d : measure_display} {T : measurableType d} :
  Equivalence (@measure_eq d T).
Proof.
  constructor.
  - done.
  - rewrite /Symmetric.
    intros ? ? H ? ?.
    by rewrite H //=.
  - intros ? ? ? H0 H1 ? ?.
    by rewrite H0 //= H1 //=.
Qed.

Section giry_eval.
  Local Open Scope classical_set_scope.
  Context `{d : measure_display} {T : measurableType d}.

  (* TODO: Make hint *)
  Lemma gEval_meas_fun : forall (S : set T) (H : d.-measurable S), measurable_fun setT (gEval S).
  Proof.
    intros S HmS.
    simpl.
    eapply (@measurability giry_display _ (giryM T) _ setT (gEval S)).
    {
      rewrite smallest_id; auto.
      simpl.
      apply sigma_algebra_measurable.
    }
    rewrite /giry_display.-measurable /= /giry_measurable /=.
    eapply subset_trans; [  | apply sub_gen_smallest].
    eapply subset_trans; [  | apply bigcup_sup]; eauto.
    rewrite /gEvalPreImg.
    apply subset_refl.
  Qed.

  (*
  Lemma gEval_eval : forall (S : set T) (H : d.-measurable S) (μ : giryM T), gEval H μ = μ S.
  *)

End giry_eval.


Section giry_integral.
  Local Open Scope classical_set_scope.
  Local Open Scope ereal_scope.
  Context `{d : measure_display} {T : measurableType d}.

  Definition gInt (f : T -> \bar R) (μ : giryM T) := (\int[μ]_x f x).

  (* TODO: Check if additional conditions on f are needed *)
  Lemma gInt_meas_fun : forall (f : T -> \bar R) (Hmf : measurable_fun setT f) (Hfge0 : forall x, 0 <= f x),
      measurable_fun setT (gInt f).
    Proof.
      (*
        The idea is to reconstruct f from simple functions, then use
        measurability of gEval. See "Codensity and the Giry monad", Avery

        TODO: The proof could be cleaner
       *)
      intros f Hmf Hfge0.
      rewrite /gInt.

      have HTmeas : d.-measurable [set: T]; auto.
      have Hfge0' : (forall t, [set: T] t -> 0 <= f t); auto.

      (* f is the limit of a monotone sequence of simple functions *)
      pose proof (approximation HTmeas Hmf Hfge0') as [g [Hgmono Hgconv]].

      set gE := (fun n => EFin \o (g n)).
      have HgEmeas : (forall n : nat, measurable_fun [set: T] (gE n)).
      {
        intro.
        rewrite /gE /=.
        apply EFin_measurable_fun; auto.
      }
      have HgEge0: (forall (n : nat) (x : T), [set: T] x -> 0 <= gE n x).
      {
        intros.
        rewrite /gE /= //.
        apply g.
      }
      have HgEmono : (forall x: T, [set: T] x -> {homo gE^~ x : n m / (Order.le n m) >-> n <= m}).
      {
        intros x Hx n m Hnm.
        apply lee_tofin.
        pose (lefP _ _ (Hgmono n m Hnm)); auto.
      }

      (* By MCT, limit of the integrals of g_n is the integral of the limit of g_n *)
      have Hcvg := (cvg_monotone_convergence _ HgEmeas HgEge0 HgEmono).

      set gEInt := (fun n => (fun μ => \int[μ]_x (gE n) x )).
      have HgEIntmeas : (forall n : nat, measurable_fun [set: giryM T] (gEInt n)).
      {
        intro n.
        rewrite /gEInt /gE /=.
        eapply eq_measurable_fun.
        intros μ Hμ.
        rewrite integralT_nnsfun sintegralE //.
        apply emeasurable_fun_fsum; auto.
        intros r.
        have Hrmeas : d.-measurable (preimage (g n) (set1 r)); auto.
        apply (measurable_funeM (r%:E)).
        have : measurable_fun [set: giryM T] (fun x : giryM T => x (g n @^-1` [set r])); auto.
        eapply eq_measurable_fun.
        intros ? ?.
        auto.
        apply gEval_meas_fun; auto.
      }
      (* The μ ↦ int[mu] lim g_n is measurable if every μ ↦ int[mu] g_n is measurable *)
      apply (emeasurable_fun_cvg _ (fun (μ : giryM T) => \int[μ]_x f x) HgEIntmeas).
      intros μ Hμ.
      rewrite /gEInt /=.
      erewrite (eq_integral _ f); [apply (Hcvg μ HTmeas) |].
      intros x Hx.
      have HxT : [set: T] x; [auto |].
      specialize (Hgconv x HxT).
      rewrite (topology.cvg_unique _
                 Hgconv (topology.cvgP _ Hgconv)) //.
   Qed.

  (*
  Axiom gInt_eval : forall (f : T -> \bar R) (H : measurable_fun setT f) (μ : giryM T), gInt H μ = (\int[μ]_x f x).
  *)

End giry_integral.

Section giry_cod_meas.
  Local Open Scope classical_set_scope.

  (* TODO: Either move this lemma to a more accessible location, or integrate within
     the proof below *)
  Local Lemma measurability_aux d d' (aT : measurableType d) (rT : measurableType d')
    (f : aT -> rT) (G : set (set rT)) :
    @measurable _ rT = <<s G >> -> ( forall (S : set rT), G S -> @measurable _ aT (f @^-1` S)) ->
    measurable_fun setT f.
  Proof.
    intros HG S.
    eapply measurability; eauto.
    rewrite /preimage_class.
    apply image_subP.
    intros ??.
    rewrite setTI; auto.
  Qed.

  (* Adapted from mathlib induction_on_inter *)
  (* TODO: Clean up proof, move lemma, change premises to use setX_closed like notations *)
  Local Lemma dynkin_induction d {T : measurableType d} (G : set (set T)) (P : (set T) -> Prop) :
    @measurable _ T = <<s G >> ->
    setI_closed G ->
    (P setT) ->
    (forall S, G S -> P S) ->
    (forall S, measurable S -> P S -> P (setC S)) ->
    (forall F : sequences.sequence (set T),
        (forall n, measurable (F n)) ->
        trivIset setT F ->
        (forall n, P (F n)) -> P (\bigcup_k F k)) ->
    (forall S, <<s G >> S -> P S).
  Proof.
    intros HG HIclosed HsetT Hgen HsetC Hbigcup S HGS.
    have HmS : measurable S; [ rewrite HG // |].
    have Haux : <<s G >> `<=` [set S : (set T) | measurable S /\ P S].
    {
      apply lambda_system_subset; auto.
      apply (dynkin_lambda_system ([set S0 | measurable S0 /\ P S0])).
      split; auto.
      - split; auto.
      - intros ?[??].
        split; auto.
        apply measurableC; auto.
      - intros ?? Hm.
        split; auto.
        apply bigcup_measurable; auto.
        intros k Hk.
        apply Hm; auto.
        apply Hbigcup; auto.
        apply Hm.
        apply Hm.
        intros ??.
        split; auto.
        rewrite HG //.
        apply sub_gen_smallest; auto.
      intros ??. apply subsetT.
    }
    apply Haux.
    rewrite -HG //.
  Qed.

  Lemma giryM_cod_meas_fun `{d1 : measure_display} `{d2 : measure_display}
    `{T1 : measurableType d1} `{T2 : measurableType d2}
    (f : T1 -> giryM T2) :
    (forall (S : set T2) (HmS : measurable S), measurable_fun setT (fun t => f t S)) ->
    measurable_fun setT f.
  Proof.
    intros HS.
    eapply measurability_aux.
    {
      rewrite /giry_display.-measurable /= /giry_measurable.
      auto.
    }
    simpl.
    intros S [U HU1 HU2].
    specialize (HS U HU1).
    rewrite /gEvalPreImg /preimage_class in HU2.
    destruct HU2 as [B HB <-].
    specialize (HS measurableT B HB).
    rewrite setTI.
    rewrite -comp_preimage.
    eapply eq_measurable; eauto.
    rewrite setTI /gEval /= //.
  Qed.

  (*
  Lemma giryM_cod_meas_fun_gen `{d1 : measure_display} `{d2 : measure_display}
    `{T1 : measurableType d1} `{T2 : measurableType d2}
    (f : T1 -> giryM T2) (G : set (set T2))
    (S0 : set T2) (HG : d2.-measurable = <<s G >> )(Hms : d2.-measurable S0) :
    (forall (S : set T2) (HmS : G S ), measurable_fun setT (fun t => f t S)) ->
    measurable_fun setT f.
  Proof.
    intros HS.
    apply giryM_cod_meas_fun.
    eapply (@measurability_aux _ _ _ _ _ (\bigcup_(S in G) gEvalPreImg S)).
    {
      rewrite /giry_display.-measurable /= /giry_measurable HG.
      apply seteqP; split; [|apply sub_sigma_algebra2, bigcup_subset, sub_gen_smallest].
      apply lambda_system_subset; auto.
      - rewrite /setI_closed.
        intros A B [S1 HGS1 HS1] [S2 HGS2 HS2].
        exists (S1 `&` S2). admit.
        rewrite /gEvalPreImg /preimage_class.
        eexists.
    }
    intros S [? ? H].
    rewrite /gEvalPreImg /preimage_class in H.
    destruct H as [B HB <-].
    specialize (HS x H0 B HB).
    rewrite setTI.
    rewrite -comp_preimage.
    eapply eq_measurable; eauto.
    rewrite setTI /gEval /= //.

  Admitted.
  *)

  (*
  Lemma giryM_cod_prod_meas_fun `{d : measure_display} `{T: measurableType d}
    `{d1 : measure_display} `{d2 : measure_display}
    `{T1 : measurableType d1} `{T2 : measurableType d2}
    (f: T -> giryM (T1 * T2)%type) :
    (forall (S1 : set T1) (S2 : set T2) (HmS1 : d1.-measurable S1) (HmS2 : d2.-measurable S2),
        measurable_fun setT (fun t : T => (f t) (S1 `*` S2))) ->
    measurable_fun setT f.
  Proof.
    intros HI.
    eapply giryM_cod_meas_fun.
    rewrite measurable_prod_measurableType.
    apply dynkin_induction.
    - intros A B [A1 HA1 [A2 HA2 <-]] [B1 HB1 [B2 HB2 <-]].
      exists (A1 `&` B1); auto.
      apply measurable_setI; auto.
      exists (A2 `&` B2); auto.
      apply measurable_setI; auto.
      rewrite setXI //.
    - rewrite -setXTT.
      apply HI; auto.
    - intros S [A HA [B HB <-]].
      apply HI; auto.
    - intros S HS.


    eapply (dynkin_induction _ _ _ _ _ HmS). auto.

    eapply (@measurability_aux _ _ _ _ _ (\bigcup_(S in [set A `*` B | A in d1.-measurable & B in d2.-measurable]) gEvalPreImg S)).
    {
      rewrite /giry_display.-measurable /= /giry_measurable.
      rewrite measurable_prod_measurableType.
      apply seteqP; split; [|apply sub_sigma_algebra2, bigcup_subset, sub_gen_smallest].
      apply lambda_system_subset; auto.
      - rewrite /setI_closed.
        intros A B HA HB.
        admit.
      - apply g_sigma_algebra_lambda_system.
        intros ??.
        apply subsetT.
      - apply bigcup_sub.
        intros W HW.
        rewrite /smallest.
      - intros ??; apply subsetT.
    }
    simpl.
    intros S [U [W1 HW1 [W2 HW2 <-]] HU2].
    specialize (HS W1 W2 HW1 HW2).
    rewrite /gEvalPreImg /preimage_class in HU2.
    destruct HU2 as [B HB <-].
    specialize (HS measurableT B HB).
    rewrite setTI.
    rewrite -comp_preimage.
    eapply eq_measurable; eauto.
    rewrite setTI /gEval /= //.
  Admitted.
  *)

End giry_cod_meas.

Section giry_map.
    Local Open Scope classical_set_scope.
    Context `{d1 : measure_display} `{d2 : measure_display}.
  Context {T1 : measurableType d1} {T2 : measurableType d2}.

  Variables (f : T1 -> T2) (Hmf : measurable_fun setT f) (μ1 : giryM T1).

  Definition gMap_ev := pushforward μ1 Hmf.

  Let gMap0 : gMap_ev set0 = 0%E.
  Proof.
    rewrite /gMap_ev measure0 //.
  Qed.

  Let gMap_ge0 A : (0 <= gMap_ev A)%E.
  Proof.
    rewrite /gMap_ev measure_ge0 //.
  Qed.

  Let gMap_semi_sigma_additive : semi_sigma_additive (gMap_ev).
  Proof.
    rewrite /gMap_ev.
    apply measure_semi_sigma_additive.
  Qed.

  Let gMap_setT : (gMap_ev setT <= 1)%E.
  Proof.
    rewrite /gMap_ev /pushforward /=.
    apply sprobability_setT.
  Qed.


  HB.instance Definition _ := isMeasure.Build d2 T2 R gMap_ev gMap0 gMap_ge0 gMap_semi_sigma_additive.
  HB.instance Definition _ := Measure_isSubProbability.Build _ _ _ gMap_ev gMap_setT.

  Definition gMap : giryM T2 := gMap_ev.

End giry_map.

Section giry_map_meas.


  Local Open Scope classical_set_scope.
  Local Open Scope ereal_scope.
  Context `{d1 : measure_display} `{d2 : measure_display}.
  Context {T1 : measurableType d1} {T2 : measurableType d2}.



  Lemma gMap_to_int : forall (f : T1 -> T2) (H : measurable_fun setT f) (μ1 : giryM T1) (S : set T2) (HmS : measurable S),
      (gMap H μ1 S = \int[μ1]_x (numfun.indic S (f x))%:E)%E.
  Proof.
    intros f Hmf μ1 S HmS.
    rewrite /gMap /gMap_ev.
    rewrite -{1}(setIT S).
    rewrite -(integral_indic (pushforward μ1 Hmf)); auto.
    rewrite ge0_integral_pushforward; auto.
    apply EFin_measurable_fun.
    apply measurable_indic; auto.
    intros y.
    rewrite /numfun.indic.
    case: (y \in S); auto.
  Qed.





  Lemma gMap_meas_fun : forall (f : T1 -> T2) (H : measurable_fun setT f), measurable_fun setT (gMap H).
  Proof.
    intros f Hmf.
    rewrite /gMap.
    apply (@giryM_cod_meas_fun _ _ (giryM T1)); simpl.
    intros S HmS.
    rewrite /gMap_ev /pushforward /=.
    apply gEval_meas_fun.
    rewrite -(setTI (f @^-1` S)).
    apply Hmf; auto.
  Qed.


  Lemma gMap_proper : forall (f : T1 -> T2) (H : measurable_fun setT f), (Proper (measure_eq ==> measure_eq) (gMap H)).
  Proof.
    intros.
    intros ?? Hrw ??.
    rewrite /= /gMap_ev /pushforward /=.
    rewrite Hrw //.
    rewrite -(setTI (f @^-1` S)).
    apply H; auto.
  Qed.


  Lemma gMapInt (f : T1 -> T2) (Hmf : measurable_fun setT f) (μ : giryM T1)
    (h : T2 -> \bar R) (Hmh : measurable_fun setT h) (Hpos : forall x, 0 <= h x):
    gInt h (gMap Hmf μ) = gInt (h \o f) μ.
  Proof.
    rewrite /gInt.
    have Haux : (forall S, d2.-measurable S -> S `<=` [set : T2] -> gMap Hmf μ S = pushforward μ Hmf S); auto.
    erewrite (eq_measure_integral _ Haux).
    rewrite ge0_integral_pushforward; auto.
  Qed.

  (* Axiom gMap : forall (f : T1 -> T2), measurable_fun setT f -> (giryM T1 -> giryM T2).
  Axiom gMap_meas_fun : forall (f : T1 -> T2) (H : measurable_fun setT f), measurable_fun setT (gMap H).
  Axiom gMap_proper : forall (f : T1 -> T2) (H : measurable_fun setT f), (Proper (measure_eq ==> measure_eq) (gMap H)). *)

  Global Existing Instance gMap_proper.


End giry_map_meas.

Section giry_ret.

  Local Open Scope classical_set_scope.
  Local Open Scope ring_scope.
  Local Open Scope ereal_scope.
  Context `{d : measure_display} {T : measurableType d}.


  Definition gRet (x:T) : giryM T := (dirac^~ R x)%R.

  Lemma gRet_meas_fun : measurable_fun setT gRet.
  Proof.
    rewrite /gRet /dirac.
    apply giryM_cod_meas_fun; simpl.
    intros S HmS.
    rewrite /dirac.
    apply EFin_measurable_fun.
    apply measurable_indic; auto.
  Qed.


  Lemma gRetInt (x : T) (h : T -> \bar R) (H : measurable_fun setT h):
      gInt h (gRet x) = h x.
  Proof.
    rewrite /gInt.
    have Haux : (forall S, d.-measurable S -> S `<=` [set : T] -> gRet x S = dirac x S); auto.
    erewrite (eq_measure_integral _ Haux).
    rewrite integral_dirac; auto.
    rewrite diracT mul1e //.
  Qed.

  Lemma gRetInt_rw (x : T) (h : T -> \bar R) (H : measurable_fun setT h):
      \int[gRet x]_x h x = h x.
  Proof.
    apply gRetInt; auto.
  Qed.

  Lemma gRetMass1Inv {x : T} {S : set T} (HS : measurable S) : gRet x S = 1 <-> S x.
  Proof.
    rewrite /gRet/dirac//=/dirac//=/numfun.indic//=.
    case (ExcludedMiddle (S x)); intro H.
    { by rewrite mem_set. }
    { rewrite memNset; [|done].
      rewrite //=.
      split; move=>K; last done.
      exfalso.
      rewrite /GRing.one//=/GRing.natmul//=/GRing.zero//= in K.
      inversion K.
      lra.
    }
  Qed.

  Lemma gRetMass0Inv (S : set T) (a : T) (HS : measurable S):
    ¬ S a ↔ (gRet a) S = 0.
  Proof.
    split; intros.
    { 
      rewrite /gRet /GRing.zero //=. 
      rewrite diracE.
      rewrite memNset; auto.
    }
    move => Hc.
    apply gRetMass1Inv in Hc; auto.
    rewrite Hc in H. inversion H.
    by apply R1_neq_R0.
  Qed.
  (*
  Axiom gRet : T -> giryM T.
  Axiom gRet_meas_fun : measurable_fun setT gRet.
  *)
  (** Use bool_decide or as_bool? *)
  (* Axiom gRet_eval : forall S x (H: d.-measurable S), gRet x S = if (S x) then 1%E else 0%E. *)



End giry_ret.


Section giry_join.
  Local Open Scope classical_set_scope.
  Local Open Scope ereal_scope.
  Context `{d : measure_display} {T : measurableType d}.
  Variable (M : giryM (giryM T)).

  Definition gJoin_ev (S : set T) := gInt (gEval S) M.

  Let gJoin0 : gJoin_ev set0 = 0%E.
  Proof.
    rewrite /gJoin_ev /gEval.
    apply integral0_eq.
    auto.
  Qed.

  Let gJoin_ge0 A : (0 <= gJoin_ev A)%E.
  Proof.
    rewrite /gJoin_ev.
    apply integral_ge0.
    auto.
  Qed.

  (* TODO: Cleaner proof? *)
  Let gJoin_semi_sigma_additive : semi_sigma_additive (gJoin_ev).
  Proof.
    rewrite /gJoin_ev /gInt.
    rewrite /gEval /=.
    intros F HF HFTriv HcupF.
    have Hμ : (forall (μ : giryM T), semi_sigma_additive μ).
    {
      intros; auto.
      apply measure_semi_sigma_additive.
    }
    eapply topology.cvg_trans.
    {
      erewrite topology.eq_cvg; last first.
      intros ?.
      rewrite -ge0_integral_sum; auto.
      intros.
      apply gEval_meas_fun; auto.
      auto.
    }
    eapply topology.cvg_trans.
    {
      apply cvg_monotone_convergence; auto.
      {
        intros n.
        apply emeasurable_fun_sum.
        intros.
        apply gEval_meas_fun; auto.
      }
      {
        intros n ? ?.
        rewrite sume_ge0; auto.
      }
      intros ? ?.
      intros ? ? ?.
      rewrite sequences.ereal_nondecreasing_series //.
    }
    apply topology.close_cvgxx.
    rewrite topology.closeE; auto.
    f_equal.
    apply functional_extensionality.
    intros μ.
    simpl.
    rewrite /semi_sigma_additive in Hμ.
    specialize (Hμ μ F HF HFTriv HcupF).
    apply topology.cvg_lim; auto.
    apply topology.eventually_filter.
  Qed.

  (* TODO: Cleaner proof? *)
  Let gJoin_setT : (gJoin_ev setT <= 1)%E.
  Proof.
    rewrite /gJoin_ev.
    apply (@Order.le_trans _ _ (1%:E * (M setT))); last first.
    {
      rewrite mul1e.
      apply sprobability_setT.
    }
    eapply Order.le_trans; last first.
    {
      apply (@integral_le_bound _ _ R M _ (gEval setT) 1); auto.
      apply gEval_meas_fun; auto.
      apply (aeW M).
      intros ??.
      rewrite gee0_abs; auto.
      rewrite /gEval.
      apply (@sprobability_setT d T R x).
    }
    apply ge0_le_integral; auto.
    apply gEval_meas_fun; auto.
    intros; apply abse_ge0.
    apply (@measurableT_comp _ _ _ _ _ _ abse).
    apply abse_measurable.
    apply gEval_meas_fun; auto.
    intros ??.
    rewrite gee0_abs; auto.
  Qed.

  (*
  Axiom gJoin : giryM (giryM T) -> giryM T.
  Axiom gJoin_meas_fun : measurable_fun setT gJoin.
  Axiom gJoin_proper : (Proper (measure_eq ==> measure_eq) gJoin).
  *)

  HB.instance Definition _ := isMeasure.Build d _ R gJoin_ev gJoin0 gJoin_ge0 gJoin_semi_sigma_additive.
  HB.instance Definition _ := Measure_isSubProbability.Build _ _ _ gJoin_ev gJoin_setT.

  Definition gJoin : giryM T := gJoin_ev.

End giry_join.


Section giry_join_meas_fun.
  Local Open Scope classical_set_scope.
  Local Open Scope ereal_scope.
  Context `{d : measure_display} {T : measurableType d}.


  Lemma gJoin_meas_fun : measurable_fun setT (@gJoin d T).
  Proof.
    apply (@giryM_cod_meas_fun _ _ (giryM (giryM T))); simpl.
    rewrite /gJoin_ev.
    intros S HmS.
    eapply (@gInt_meas_fun _ _ (gEval S)).
    Unshelve.
    apply gEval_meas_fun; auto.
    auto.
  Qed.

  Lemma gJoin_proper : (Proper (measure_eq ==> measure_eq) (@gJoin d T)).
  Proof.
    intros ?? Hrw ??.
    rewrite /= /gJoin_ev.
    apply eq_measure_integral.
    intros ???.
    apply Hrw.
    auto.
  Qed.

  (* TODO: Messy proof, cleanup *)
  Lemma gJoinSInt (M : giryM (giryM T)) (h : {nnsfun T >-> R} )  (Hmh : measurable_fun setT h) :
    sintegral (gJoin M) h = \int[M]_μ sintegral μ h.
  Proof.
    etransitivity; last first.
    {
      eapply eq_integral.
      intros μ Hμ.
      rewrite sintegralE.
      auto.
    }
    simpl.
    rewrite ge0_integral_fsum; auto; last first.
    {
      intros ???.
      apply nnsfun_mulemu_ge0.
    }
    {
      intros ?.
      apply measurable_funeM.
      apply gEval_meas_fun; auto.
    }
    rewrite sintegralE /=.
    have Heq: forall x, (x%:E * gJoin_ev M (h @^-1` [set x]))%E = (\int[M]_μ (x%:E * μ (h @^-1` [set x])))%E.
    {
      intro x.
      rewrite integralZl; auto.
      eapply le_integrable; last first.
      apply (finite_measure_integrable_cst _ 1).
      intros μ ?.
      simpl.
      rewrite Num.Theory.normr1.
      rewrite gee0_abs.
      eapply Order.le_trans; [ | apply (@sprobability_setT _ _ _ μ)].
      apply le_measure; auto.
      rewrite in_setE.
      apply measurable_sfunP.
      apply measurable_set1.
      rewrite in_setE.
      auto.
      apply subsetT.
      rewrite measure_ge0 //.
      apply gEval_meas_fun; auto.
      auto.
      }
    f_equal.
    apply fsbigop.eq_finite_support.
    intros r Hr; auto.
    apply functional_extensionality; auto.
    intros.
    rewrite Heq //.
  Qed.

  (* TODO: Messy proof, cleanup *)
  Lemma gJoinInt (M : giryM (giryM T))
    (h : T -> \bar R) (Hmh : measurable_fun setT h) (Hpos : forall x, 0 <= h x):
    gInt h (gJoin M) = gInt (fun (μ : giryM T) => \int[μ]_x h x) M.
  Proof.

    have HTmeas : d.-measurable [set: T]; auto.
    have Hhge0' : (forall t, [set: T] t -> 0 <= h t); auto.
    pose proof (approximation HTmeas Hmh Hhge0') as [g [Hgmono Hgconv]].

    set gE := (fun n => EFin \o (g n)).
    have HgEmeas : (forall n : nat, measurable_fun [set: T] (gE n)).
    {
      intro.
      rewrite /gE /=.
      apply EFin_measurable_fun; auto.
    }
    have HgEge0: (forall (n : nat) (x : T), [set: T] x -> 0 <= gE n x).
    {
      intros.
      rewrite /gE /= //.
      apply g.
    }
    have HgEmono : (forall x: T, [set: T] x -> {homo gE^~ x : n m / (Order.le n m) >-> n <= m}).
    {
      intros x Hx n m Hnm.
      apply lee_tofin.
      pose (lefP _ _ (Hgmono n m Hnm)); auto.
    }

    (* By MCT, limit of the integrals of g_n is the integral of the limit of g_n *)
    have Hcvg := (monotone_convergence _ _ HgEmeas HgEge0 HgEmono).
    rewrite /gInt.
    (* TODO: Fix failing inference? *)
    have Hgconv' : forall x : T,
        [set: T] x ->
        h x = (topology.lim (topology.fmap (EFin \o (fun x0 : nat => g x0 x)) (@topology.nbhs nat (topology.topology_set_system__canonical__topology_Filtered nat) topology.eventually))).
    {
      intros x Hx.
      specialize (Hgconv x Hx).
      pose (Hgconv2 := topology.cvgP _ Hgconv).
      rewrite (topology.cvg_unique _ Hgconv Hgconv2); auto.
    }

    have Hcvg' :
      forall t : measure T RbaseSymbolsImpl_R__canonical__reals_Real,
        d.-measurable [set: T] ->
        \int[t]_x h x =
          topology.lim (topology.fmap (fun n : nat => \int[t]_x gE n x) (@topology.nbhs nat (topology.topology_set_system__canonical__topology_Filtered nat) topology.eventually)).
    {
      intros ??.
      rewrite -Hcvg; auto.
      apply eq_integral => x Hx.
      rewrite Hgconv'; auto.
      apply set_mem; auto.
    }
    rewrite Hcvg'; auto.
    have ->: (fun n : nat => \int[gJoin M]_x gE n x) = (fun n : nat => \int[M]_μ \int[μ]_x gE n x).
    {
      apply functional_extensionality.
      intros n.
      rewrite integralT_nnsfun.
      rewrite gJoinSInt.
      apply eq_integral.
      intros ??.
      rewrite integralT_nnsfun //.
      auto.
    }
    erewrite (@eq_integral _ _ _ M _ _ (fun μ => \int[μ]_x h x)); last first.
    {
      intros ??. rewrite Hcvg' //.
    }
    rewrite monotone_convergence; auto.
    {
      intros n.
      eapply (gInt_meas_fun (HgEmeas n)); auto.
      intros.
      apply HgEge0; auto.
      apply set_mem.
      apply in_setT.
    }
    {
      intros.
      apply integral_ge0; auto.
    }
    {
      intros ?????.
      apply ge0_le_integral; auto.
      intros ??; auto.
      apply HgEmono; auto.
    }
  Qed.


  Global Existing Instance gJoin_proper.

End giry_join_meas_fun.

Section giry_bind.
  Local Open Scope classical_set_scope.
  Context `{d1 : measure_display} `{d2 : measure_display}.
  Context {T1 : measurableType d1} {T2 : measurableType d2}.

  Definition gBind (f : T1 -> giryM T2) (H : measurable_fun setT f) : giryM T1 -> giryM T2 :=
    gJoin \o (gMap H).


  Lemma gBind_meas_fun (f : T1 -> giryM T2) (H : measurable_fun setT f) :  measurable_fun setT (gBind H).
  Proof.
    eapply (@measurable_comp _ _ _ _ _ _ setT).
    { by eapply @measurableT. }
    { by apply subsetT. }
    { by apply gJoin_meas_fun. }
    { by apply gMap_meas_fun. }
  Qed.

  Global Instance gBind_proper (f : T1 -> giryM T2) (H : measurable_fun setT f) : Proper (measure_eq ==> measure_eq) (gBind H).
  Proof.
    intros x y H'.
    rewrite /gBind.
    intros S HS.
    rewrite /ssrfun.comp.
    apply gJoin_proper; [|done].
    by apply gMap_proper.
  Qed.
  

End giry_bind.


Section giry_bind_meas_fun.
  Local Open Scope classical_set_scope.
  Local Open Scope ereal_scope.
  Context `{d1 : measure_display} `{d2 : measure_display}.
  Context {T1 : measurableType d1} {T2 : measurableType d2}.


  Lemma gBindInt_meas_fun (μ : giryM T1) (f : T1 -> giryM T2) (H : measurable_fun setT f)
    (h : T2 -> \bar R) (mh : measurable_fun setT h) (Hhge0 : forall x, 0 <= h x) :
      measurable_fun setT (fun x => gInt h (f x)).
  Proof.
    eapply (@measurable_comp _ _ _ _ _ _ setT _ _ f).
    { by eapply @measurableT. }
    { by apply subsetT. }
    { by apply gInt_meas_fun. }
    { by apply H. }
  Qed.

  Lemma gBindInt :
    forall (μ : giryM T1) (f : T1 -> giryM T2) (H : measurable_fun setT f) (h : T2 -> \bar R) (mh : measurable_fun setT h) (Hhge0 : forall x, 0 <= h x),
      gInt h (gBind H μ) = gInt (fun x => gInt h (f x)) μ.
  Proof.
    intros ??????.
    rewrite /gBind /=.
    rewrite gJoinInt; auto.
    rewrite gMapInt; auto.
    apply gInt_meas_fun; auto.
    intros.
    apply integral_ge0; auto.
  Qed.

  Lemma gBindInt_rw (μ : giryM T1) (f : T1 -> giryM T2) (H : measurable_fun setT f) (h : T2 -> \bar R) (mh : measurable_fun setT h) (Hhge0 : forall x, 0 <= h x) :
    \int[gBind H μ]_y h y = \int[μ]_x \int[f x]_y  h y.
  Proof.
    apply gBindInt; auto.
  Qed.

  Lemma gBindEval_rw (μ : giryM T1) (f : T1 -> giryM T2) (H : measurable_fun setT f)
    (S : set T2) (HS : measurable S) :
    gBind H μ S = \int[μ]_x (f x S).
  Proof.
    rewrite /gBind /= /gJoin_ev gMapInt; auto.
    by apply gEval_meas_fun.
  Qed.

End giry_bind_meas_fun.

Section giry_monad.
  Local Open Scope classical_set_scope.
  Local Open Scope ereal_scope.
  Context `{d1 : measure_display} `{d2 : measure_display} `{d3 : measure_display}.
  Context {T1 : measurableType d1} {T2 : measurableType d2} {T3 : measurableType d3}.

  Lemma gJoin_assoc : forall (x : giryM (giryM (giryM T1))),
      (gJoin \o (gMap gJoin_meas_fun)) x ≡μ (gJoin \o gJoin) x.
  Proof.
    intros μ S HmS.
    rewrite /= /gJoin_ev.
    rewrite gMapInt //.
    rewrite gJoinInt //.
    all: apply gEval_meas_fun; auto.
  Qed.


  Lemma gJoin_id1 : forall (x : giryM T1),
      (gJoin \o (gMap gRet_meas_fun)) x ≡μ (gJoin \o gRet) x.
  Proof.
    intros μ S HmS.
    rewrite /= /gJoin_ev; simpl.
    rewrite gMapInt; auto; [|apply gEval_meas_fun; auto].
    rewrite gRetInt; auto; [|apply gEval_meas_fun; auto].
    rewrite /gInt /gEval /gRet /= /dirac.
    rewrite integral_indic; auto.
    rewrite setIT //.
  Qed.

  Lemma gJoin_id2 : forall (x : giryM (giryM T1)) (f : T1 -> T2) (H : measurable_fun setT f),
      (gJoin \o gMap (gMap_meas_fun H)) x ≡μ (gMap H \o gJoin) x.
  Proof.
    intros μ f Hmf S HmS.
    rewrite /= /gJoin_ev; simpl.
    rewrite gMapInt; auto.
    apply gEval_meas_fun; auto.
  Qed.

  Theorem gBind_id_left (f : T1 -> giryM T2) (a : T1) (HMF : measurable_fun setT f):
    gBind HMF (gRet a) ≡μ f a.
  Proof.
    intros S HS.
    rewrite gBindEval_rw; [|done].
    rewrite gRetInt_rw; [done|].
    have -> : (λ x : T1, f x S) = (gEval S) \o f.
    { by apply functional_extensionality; intro x; rewrite /gEval//=. }
    eapply measurable_comp; [| | by apply (gEval_meas_fun HS) | done ].
    { by apply @measurableT. }
    { by rewrite //=. }
  Qed.

  Theorem gBind_id_right (μ : giryM T1) :
    gBind gRet_meas_fun μ ≡μ μ.
  Proof.
    intros S HS.
    rewrite gBindEval_rw; [|done].
    rewrite /gRet//=/dirac//=.
    rewrite integral_indic; [| done | done ].
    by rewrite setIT.
  Qed.


End giry_monad.

Section giry_zero.
  Local Open Scope classical_set_scope.

  Section giry_zero_def.
    Context `{d1 : measure_display} {T1 : measurableType d1}.
    Definition gZero := mzero : giryM T1.
    Lemma gZero_eval : forall S (H: d1.-measurable S), gZero S = (0% E).
    Proof.
      intros ??.
      rewrite /gZero/mzero //.
    Qed.
  End giry_zero_def.

  Context `{d1 : measure_display} `{d2 : measure_display} {T1 : measurableType d1} {T2 : measurableType d2}.

  Lemma gZero_map : forall (f : T1 -> T2) (H : measurable_fun setT f),
    gMap H gZero ≡μ (gZero : giryM T2).
  Proof.
    intros f H S HmS.
    rewrite /=/gMap_ev /mzero //.
  Qed.

End giry_zero.

Section giry_external_map.
  Local Open Scope classical_set_scope.
  Context `{d1 : measure_display} `{d2 : measure_display}.
  Context {T1 : measurableType d1} {T2 : measurableType d2}.

  Definition gMap' (f : T1 -> T2) : giryM T1 -> giryM T2 :=
    extern_if (cst gZero) (fun h : measurable_fun setT f => gMap h).

  Lemma gMap'_meas_fun (f : T1 -> T2) (H : measurable_fun setT f) : measurable_fun setT (gMap' f).
  Proof. by rewrite /gMap' extern_if_eq; apply gMap_meas_fun. Qed.

  Global Instance gMap'_proper : Proper (eq ==> measure_eq ==> measure_eq) gMap'.
  Proof.
    intros f ? <-.
    destruct (ExcludedMiddle (measurable_fun setT f)) as [E|E].
    { by rewrite /gMap' extern_if_eq; apply gMap_proper. }
    { by rewrite /gMap' extern_if_neq. }
  Qed.

  Lemma gMap'_gMap (f : T1 -> T2) (H: measurable_fun setT f) μ : gMap' f μ ≡μ gMap H μ.
  Proof. rewrite /gMap'. by rewrite extern_if_eq. Qed.
    
End giry_external_map.

Section giry_external_map_lemmas.
  Lemma gMap'_id {d} {T : measurableType d} (μ: giryM T) :
    gMap' (λ x, x) μ ≡μ μ.
  Proof. by unshelve rewrite gMap'_gMap. Qed.
End giry_external_map_lemmas.

Section giry_external_bind.
  Local Open Scope classical_set_scope.
  Context `{d1 : measure_display} `{d2 : measure_display}.
  Context {T1 : measurableType d1} {T2 : measurableType d2}.

  Definition gBind' (f : T1 -> giryM T2) : giryM T1 -> giryM T2 :=
    gJoin \o (gMap' f).

  Lemma gBind'_meas_fun (f : T1 -> giryM T2) (H : measurable_fun setT f) : measurable_fun setT (gBind' f).
  Proof. by rewrite /gBind'/gMap' extern_if_eq; apply gBind_meas_fun. Qed.



  Lemma gBind'_meas_rw: ∀ {f : T1 -> giryM T2} (H : measurable_fun setT f),
    gBind' f = gBind H.
  Proof.
    intros. 
    by rewrite /gBind' /gMap' (extern_if_eq H) /gBind.
  Qed.


End giry_external_bind.


Section giry_prod.
  Local Open Scope classical_set_scope.
  Context `{d1 : measure_display} `{d2 : measure_display}.
  Context {T1 : measurableType d1} {T2 : measurableType d2}.
  Variable (μ12 : giryM T1 * giryM T2).

  (* https://en.wikipedia.org/wiki/Giry_monad#Product_distributions  *)
  Definition gProd_ev  (S : set (T1 * T2)) := product_measure1 μ12.1 μ12.2 S.


  Let gProd0 : gProd_ev set0 = 0%E.
  Proof.
    rewrite /gProd_ev.
    auto.
  Qed.

  Let gProd_ge0 A : (0 <= gProd_ev A)%E.
  Proof.
    rewrite /gProd_ev.
    auto.
  Qed.

  Let gProd_semi_sigma_additive : semi_sigma_additive (gProd_ev).
  Proof.
    rewrite /gProd_ev /=.
    apply measure_semi_sigma_additive.
  Qed.

  Let gProd_setT : (gProd_ev setT <= 1)%E.
  Proof.
    rewrite /gProd_ev.
    rewrite -setXTT.
    rewrite product_measure1E; auto.
    eapply (@Order.le_trans _ _ (1*1)%E); [ | rewrite mul1e; auto].
    apply (@lee_pmul _ (μ12.1 setT) 1 (μ12.2 setT) 1); auto.
    apply (@sprobability_setT d1 T1 _ μ12.1).
    apply (@sprobability_setT d2 T2 _ μ12.2).
  Qed.


  HB.instance Definition _ := isMeasure.Build _ _ R gProd_ev gProd0 gProd_ge0 gProd_semi_sigma_additive.
  HB.instance Definition _ := Measure_isSubProbability.Build _ _ _ gProd_ev gProd_setT.
  Definition gProd : giryM (T1*T2)%type := gProd_ev.

  (*  gBind' (fun v1 => gBind' (gRet \o (pair v1)) (snd μ)) (fst μ). *)


End giry_prod.


Section giry_prod_meas_fun.
  Local Open Scope classical_set_scope.
  Context `{d1 : measure_display} `{d2 : measure_display}.
  Context {T1 : measurableType d1} {T2 : measurableType d2}.

  (* Somehow this isn't a mathlib lemma ?? *)
  Local Lemma measurable_setI `{d : measure_display} `{T: measurableType d}
  (A B : set T) (HA : d.-measurable A) (HB : d.-measurable B) :
    d.-measurable (A `&` B).
  Proof.
    rewrite -(setCK (A `&` B)).
    rewrite setCI.
    apply measurableC.
    rewrite -bigcup2E.
    apply bigcup_measurable.
    intros i ?.
    simpl.
    case (i == 0). apply measurableC; auto.
    case (i == 1). apply measurableC; auto.
    apply measurable0.
  Qed.


  (* TODO: Clean up, maybe move elsewhere *)
  Lemma subprobability_prod_setC
    (P : giryM T1 * giryM T2) (A : set (prod T1 T2)) :
    measurable A ->
    (product_measure1 P.1 P.2) (~` A) =
      ((product_measure1 P.1 P.2) [set: T1 * T2] - (product_measure1 P.1 P.2) A)%E.
  Proof.
  move=> mA.
  rewrite  -(setvU A) measureU ?addeK ?setICl//.
  - simpl.
    rewrite ge0_fin_numE //.
    apply (@Order.POrderTheory.le_lt_trans _ _ (((product_measure1 P.1 P.2) setT))).
    rewrite le_measure; auto.
    apply mem_set; auto.
    apply mem_set; auto.
    apply subsetT.
    apply (@Order.POrderTheory.le_lt_trans _ _ 1%E); auto.
    rewrite -(mul1e 1).
    rewrite -setXTT product_measure1E; auto.
    apply (@lee_pmul _ (P.1 setT)); auto.
    apply sprobability_setT.
    apply sprobability_setT.
    apply (ltry (GRing.one R)).
  - exact: measurableC.
  Qed.

  (*
     See "A synthetic approach to Markov kernels, conditional
     independence and theorems on sufficient statistics", Fritz

     TODO: Clean up proof
   *)
  Lemma gProd_meas_fun : measurable_fun setT (@gProd d1 d2 T1 T2).
  Proof.
    simpl.
    apply (@giryM_cod_meas_fun _ _ _ _ gProd).

    rewrite measurable_prod_measurableType; simpl.
    rewrite /gProd_ev.
    apply dynkin_induction; simpl.
    - rewrite measurable_prod_measurableType //.
    - intros A B [A1 HA1 [A2 HA2 <-]] [B1 HB1 [B2 HB2 <-]].
      exists (A1 `&` B1); auto.
      apply measurable_setI; auto.
      exists (A2 `&` B2); auto.
      apply measurable_setI; auto.
      rewrite setXI //.
    - eapply eq_measurable_fun; [intros ??; rewrite -setXTT product_measure1E // |].
      apply emeasurable_funM.
      apply (@measurableT_comp _ _ _ _ _ _ (gEval _) _ fst).
      apply gEval_meas_fun; auto.
      apply (@measurable_fst _ _ (giryM T1) (giryM T2)).

      apply (@measurableT_comp _ _ _ _ _ _ (gEval _) _ snd).
      apply gEval_meas_fun; auto.
      apply (@measurable_snd _ _ (giryM T1) (giryM T2)).
    - intros S [A HA [B HB <-]].
      eapply eq_measurable_fun; [intros ??; rewrite product_measure1E // |].
      apply emeasurable_funM.
      apply (@measurableT_comp _ _ _ _ _ _ (gEval _) _ fst).
      apply gEval_meas_fun; auto.
      apply (@measurable_fst _ _ (giryM T1) (giryM T2)).

      apply (@measurableT_comp _ _ _ _ _ _ (gEval _) _ snd).
      apply gEval_meas_fun; auto.
      apply (@measurable_snd _ _ (giryM T1) (giryM T2)).
    - intros S HmS HS.
      eapply (eq_measurable_fun).
        intros ??. simpl in x. rewrite (subprobability_prod_setC x).
        rewrite -setXTT product_measure1E; auto.
        auto.
      apply emeasurable_funB; auto; simpl.
      apply emeasurable_funM.
      apply (@measurableT_comp _ _ _ _ _ _ (gEval _) _ fst).
      apply gEval_meas_fun; auto.
      apply (@measurable_fst _ _ (giryM T1) (giryM T2)).

      apply (@measurableT_comp _ _ _ _ _ _ (gEval _) _ snd).
      apply gEval_meas_fun; auto.
      apply (@measurable_snd _ _ (giryM T1) (giryM T2)).

    - intros F HmF HF Hn.
      eapply eq_measurable_fun.
        intros ??.
        rewrite measure_semi_bigcup; auto.
        apply bigcup_measurable; auto.
        simpl.
        apply ge0_emeasurable_fun_sum; auto.
  Qed.

  Lemma gProd_proper  :
    (Proper ((measure_eq * measure_eq) ==> measure_eq) (@gProd d1 d2 T1 T2)).
  Proof.
    intros [g1 g2][g1' g2'].
    rewrite /gProd/gProd_ev/=.
    intros K. destruct K as [K1 K2].
    intros ??. simpl.
    rewrite /gProd_ev/=.
    assert (g1 ≡μ g1') as H1.
    { intros S' HS'.
      by specialize (K1 (S') HS'). 
    }
    assert (g2 ≡μ g2') as H2.
    { intros S' HS'.
      by specialize (K2 (S') HS'). 
    }
    rewrite /product_measure1.
    etrans.
    apply: (eq_measure_integral ).
    { intros ???. by apply H1. }
    apply eq_integral.
    intros x ?.
    simpl.
    apply H2.
    by apply (measurable_xsection R).
  Qed.

End giry_prod_meas_fun.


Section giry_prod_int.
  Local Open Scope classical_set_scope.
  Local Open Scope ereal_scope.
  Context `{d1 : measure_display} `{d2 : measure_display}.
  Context {T1 : measurableType d1} {T2 : measurableType d2}.

  Lemma gProdInt1 (μ1 : giryM T1) (μ2 : giryM T2)
    (h : (T1 * T2)%type -> \bar R) (Hmh : measurable_fun setT h) (Hpos : forall x, 0 <= h x):
    gInt h (gProd (μ1, μ2)) = gInt (fun x => gInt (fun y => h (x, y)) μ2 ) μ1.
  Proof.
    rewrite /gInt/=/gProd_ev/=.
    rewrite fubini_tonelli1; auto.
  Qed.

  Lemma gProdInt2 (μ1 : giryM T1) (μ2 : giryM T2)
    (h : (T1 * T2)%type -> \bar R) (Hmh : measurable_fun setT h) (Hpos : forall x, 0 <= h x):
    gInt h (gProd (μ1, μ2)) = gInt (fun y => gInt (fun x => h (x, y)) μ1 ) μ2.
  Proof.
    rewrite /gInt/=/gProd_ev/=.
    rewrite fubini_tonelli2; auto.
  Qed.

End giry_prod_int.

Section giry_iterM.
  Local Open Scope classical_set_scope.
  Context {d} {T : measurableType d}.

  Fixpoint gIter (n : nat) (f : T -> giryM T) : T -> giryM T
    := match n with
         O => gRet
       | (S n) => fun a => gBind' (gIter n f) (f a)
       end.

  Lemma giryM_iterN_zero (f : T -> giryM T) : gIter 0 f = gRet.
  Proof. done. Qed.

  (*
  Lemma giryM_iterN_S_rev_eq n (f : T -> giryM T) :
    (fun a => giryM_bind_external (f a) (giryM_iterN n f)) = (ssrfun.comp (giryM_bind_external^~ f) (giryM_iterN n f)).
  Proof.
  Admitted.
  (*
    apply functional_extensionality.
    intro a.
    rewrite /ssrfun.comp//=.
    induction n.
    { rewrite giryM_iterN_zero. admit. }
    simpl.
    rewrite IHn.
    *)

  Lemma giryM_iterN_S_rev n (f : T -> giryM T) :
    giryM_iterN (S n) f = ssrfun.comp (giryM_bind_external^~ f) (giryM_iterN n f).
  Proof. by rewrite <- giryM_iterN_S_rev_eq. Qed.
*)

  Lemma gIter_meas_fun (f : T -> giryM T) (HF : measurable_fun setT f) :
      forall n, measurable_fun setT (gIter n f).
  Proof.
    induction n.
    { by rewrite giryM_iterN_zero; apply gRet_meas_fun. }
    { simpl.
      assert ((fun a : T => gBind' (gIter n f) (f a)) = ((gBind' (gIter n f ))\o f)) as Hrewrite.
      { by apply functional_extensionality_dep. }
      rewrite Hrewrite.
      eapply measurable_comp; [| |by apply gBind'_meas_fun|done]; last first.
      - done.
      - eapply @measurableT.
    }
  Qed.

End giry_iterM.


Section giry_is_zero.
  Local Open Scope classical_set_scope.
  Context {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}.

  Definition is_zero {d} {T : measurableType d} (s : giryM T) : Prop := s ≡μ gZero.
  
  Global Instance is_zero_Proper {d} {T:measurableType d}:
    Proper (measure_eq ==> iff) (@is_zero d T).
  Proof. intros ?? ?. rewrite !/is_zero. by rewrite H. Qed.

  Lemma is_zero_gMap' (m : giryM T1) (f : T1 -> T2) (H : measurable_fun setT f) : is_zero m -> is_zero (gMap' f m).
  Proof.
    unfold is_zero; move=>->.
    rewrite /gMap' extern_if_eq.
    by apply gZero_map.
  Qed.

  Lemma gMap'_is_zero (m : giryM T1) (f : T1 -> T2) (H : measurable_fun setT f) : is_zero (gMap' f m) -> is_zero m.
  Proof.
    intros Hzero s Hms. rewrite gZero_eval; last done.
    unshelve rewrite gMap'_gMap in Hzero; first done.
    assert (gMap H m setT = 0%E) as Hzero'.
    { rewrite Hzero; last done.
      by apply gZero_eval. }
    assert (m setT =0%E) as Hzero2 by done.
    eapply subset_measure0; last done; try naive_solver.
    apply subsetT.
  Qed.

End giry_is_zero.

Section giry_is_prob.
  Local Open Scope classical_set_scope.

  Definition is_prob  {d} {T : measurableType d} (s : giryM T) : Prop := s [set: T] = 1%E.
  
  Global Instance is_prob_Proper {d} {T:measurableType d}:
    Proper (measure_eq ==> iff) (is_prob (T:=T)).
  Proof. intros ??. rewrite /is_prob. by intros ->. Qed. 

  Lemma is_prob_gRet {d} {T : measurableType d} (x:T) : is_prob (gRet x).
  Proof.
    apply probability_setT.
  Qed.

  Lemma is_prob_gMap {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2} (a:T1) (μ : giryM T1) (f : T1 -> T2) (H : measurable_fun setT f):
    is_prob μ <-> is_prob (gMap H μ).
  Proof. done. Qed.
    
End giry_is_prob.

Section giry_has_support_in.
  Local Open Scope classical_set_scope.
  Context {d} {T : measurableType d}.

  Definition mass (μ : giryM T) (S : set T) (_ : d.-measurable S) : \bar R :=
    (\int[μ]_(x in S) 1)%E.

  (* This may be redundant due to the behavior of \int on non-measurable sets, but we should
     fix it to zero for when we axiomatize. *)
  Definition mass' (μ : giryM T) (S : set T) : \bar R :=
    extern_if 0%E (fun (h : d.-measurable S) => mass μ h).
  
  Lemma mass'_subset (μ : giryM T) (S1 S2 : set T):
    d.-measurable S1 -> d.-measurable S2 -> S1 `<=` S2 -> (mass' μ S1 <= mass' μ S2)%E.
  Proof.
    rewrite /mass'.
    intros ?? H1.
    rewrite !extern_if_eq.
    rewrite /mass.
    by apply ge0_subset_integral.
  Qed.

  Definition has_support_in (μ : giryM T) (S : set T) : Prop := mass' μ S = mass' μ setT.

  Lemma has_support_in_subset (μ : giryM T) (S1 S2 : set T) :
    d.-measurable S1 -> d.-measurable S2 -> S1 `<=` S2 -> has_support_in μ S1 -> has_support_in μ S2.
  Proof.
    rewrite /has_support_in.
    intros ?? H1 H2.
    unshelve epose proof @mass'_subset μ S1 S2 _ _ H1; try done.
    epose proof @mass'_subset μ S2 ([set:T]) _ _ _; try done.
    (* sandwich of extended R? *)
    
  Admitted.

  Global Instance mass_proper : Proper (measure_eq ==> eq ==> eq) mass'.
  Proof.
    intros x y Hxy ? S ->.
    rewrite /mass'.
    case (ExcludedMiddle (measurable S)); move=> HS; last by rewrite !extern_if_neq.
    rewrite !extern_if_eq.
    rewrite /mass.
    apply eq_measure_integral.
    move=> A MA ?.
    by apply Hxy.
  Qed.

End giry_has_support_in.




Section giry_is_det.
  Local Open Scope classical_set_scope.
  Context {d} {T : measurableType d}.

  Definition is_det (t : T) (μ : giryM T) : Prop :=
    μ ≡μ gRet t.
  
  Global Instance is_det_Proper :
    Proper (eq ==> measure_eq ==> iff) (is_det).
  Proof. intros ???? ? H'. subst.
         rewrite /is_det. by rewrite H'.
  Qed.
  
  Lemma is_det_dret (a : T) : is_det a (gRet a).
  Proof. by move=>??. Qed.

  Lemma is_det_has_support_in {a : T} {μ : giryM T} (MS : forall x : T, measurable [set x]) :
    is_det a μ -> has_support_in μ [set a].
  Proof.
    rewrite /is_det.
    move=>H.
    rewrite /has_support_in.
    setoid_rewrite H.
    rewrite /mass'.
    do 2 rewrite extern_if_eq.
    rewrite /mass gRetInt_rw; [|done].
    rewrite integral_cst; [|done].
    rewrite /dirac//=/dirac//=/numfun.indic.
    rewrite mem_set //=.
    by rewrite mul1e.
  Qed.

End giry_is_det.

Section is_det_lemmas.
  Context {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}.
  
  Lemma is_det_gMap (a:T1) (μ : giryM T1) (f : T1 -> T2) (H : measurable_fun setT f):
    is_det a μ -> is_det (f a) (gMap' f μ).
  Proof.
    unshelve rewrite gMap'_gMap; first done.
    rewrite /is_det. intros ->.
    done.
  Qed.

End is_det_lemmas.

Section le_giry.
  Local Open Scope classical_set_scope.
  Local Open Scope ereal_scope.

  Lemma eval_le_1 {d} {T : measurableType d} (μ : giryM T) (S : set T) (HS : measurable S):
    μ S <= 1.
  Proof.
    erewrite @order.Order.le_trans.
    2:{
      apply le_measure.
      3: apply subsetT.
      2: {
        apply mem_set.
        apply (measurableT (s := T)).
      }
      by apply mem_set.
    }
    2: apply sprobability_setT.
    auto.
  Qed.

  Lemma eval_is_fin_num {d} {T : measurableType d} (μ : giryM T) (S : set T) (HS : measurable S):
    (μ S) \is a fin_num.
  Proof.
    rewrite fin_real; auto.
    erewrite (@order.Order.POrderTheory.lt_le_trans).
    3: apply measure_ge0.
    2: apply ltNy0.
    erewrite (@order.Order.POrderTheory.le_lt_trans).
    2: by apply eval_le_1.
    2: {
      simpl.
      apply (ltry 1%R).
    }
    auto.
  Qed.

  Definition giryM_le {d} {T : measurableType d} (μ1 μ2: giryM T) := 
    ∀ s, measurable s -> (μ1 s <= μ2 s).
  
  Lemma giryM_le_zero {d} {T : measurableType d} (μ : giryM T):
    giryM_le gZero μ.
  Proof.
    move => s Hs.
    by rewrite gZero_eval.
  Qed.

  Lemma giryM_le_refl {d} {T : measurableType d} (μ : giryM T):
    giryM_le μ μ.
  Proof.
    rewrite /giryM_le //.
  Qed.

  Global Instance giryM_le_proper {d} {T : measurableType d}: 
    Proper ((measure_eq (T:=T)) ==> (measure_eq (T:=T)) ==> eq) giryM_le.
  Proof.
    intros x y H0 μ1 μ2 H1.
    unfold measure_eq in *.
    apply propext.
    split.
    {
      move => H s Hs.
      rewrite -H0; auto. 
      rewrite -H1; auto.
    }
    {
      move => H s Hs.
      rewrite H0; auto. 
      rewrite H1; auto.
    }
  Qed.

  Lemma giryM_le_trans {d} {T : measurableType d} (μ1 μ2 μ3 : giryM T):
    giryM_le μ1 μ2 -> giryM_le μ2 μ3 -> giryM_le μ1 μ3.
  Proof.
    move => H1 H2 s Hs.
    eapply @order.Order.le_trans.
    { by apply H1. }
    { by apply H2. }
  Qed.

  Lemma giryM_le_antisym {d} {T : measurableType d} (μ1 μ2 : giryM T):
    giryM_le μ1 μ2 -> giryM_le μ2 μ1 -> μ1 ≡μ μ2.
  Proof.
    move => H1 H2 s Hs.
    eapply @order.Order.le_anti.
    rewrite H1; auto.
    rewrite H2; auto.
  Qed.

  Lemma gBind_giryM_le {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2} (μ1 μ2: giryM T1) (f g : T1 -> giryM T2) (Hf : measurable_fun setT f) (Hg: measurable_fun setT g):
    giryM_le μ1 μ2 ->
    (∀ a, giryM_le (f a) (g a)) ->
    giryM_le (gBind Hf μ1) (gBind Hg μ2).
  Proof.
    move => H1 H2 s Hs.
    rewrite !gBindEval_rw; auto.
    (*
    \int[μ1]_x (f x s) <= \int[μ2]_x (g x s) -(monotonicity)-> ...
    *)
  Admitted.

  Lemma gIter_giryM_le {d} {T : measurableType d} (f g : T -> giryM T) (Hf : measurable_fun setT f) (Hg: measurable_fun setT g) n a:
    (∀ a, giryM_le (f a) (g a)) -> 
    giryM_le (gIter n f a) (gIter n g a).
  Proof.
    revert a. induction n.
    {
      intros.
      rewrite /gIter. 
      apply giryM_le_refl.
    }
    intros.
    simpl. rewrite !gBind'_meas_rw; try apply gIter_meas_fun; try assumption.
    intros.
    apply gBind_giryM_le; auto.
  Qed.

  Lemma giryM_le_is_det {d} {T : measurableType d} (μ : giryM T) a : 
    giryM_le (gRet a) μ ->
    is_det a μ.
  Proof.
    move => H s Hs.
    destruct (pselect (s a)).
    {
      apply gRetMass1Inv in s0 as Hs0; auto.
      apply @order.Order.le_anti. 
      rewrite H; auto.
      rewrite Hs0.
      by rewrite eval_le_1.
    }
    replace (gRet a s) with (0 : \bar R). 2 : {
      symmetry. by apply gRetMass0Inv.
    }
    assert ((~` s) a); auto.
    assert (measurable (~` s)). { by apply measurableC. }
    assert (μ (~`s) = 1). {
      apply gRetMass1Inv in H0 as Hs0; auto.
      apply @order.Order.le_anti. 
      rewrite -Hs0 H; auto.
      rewrite Hs0.
      by rewrite eval_le_1.
    }
    assert (μ (~`s) + μ s = 1)%E. {
      rewrite -measureU; auto.
      2: apply disjoints_subset, subset_refl.
      rewrite setvU. 
      simpl.
      apply @order.Order.le_anti.
      specialize (H setT measurableT).
      assert (gRet a setT = 1) as Hrt. {
        rewrite gRetMass1Inv //.
      }
      rewrite Hrt in H. 
      by rewrite eval_le_1.
    }
    apply (f_equal (fun x => x - μ(~`s))) in H3.
    rewrite H2 in H3. 
    rewrite GRing.addrC GRing.addrA (GRing.addrC _ 1)%E in H3.
    rewrite -!EFinB -!RminusE !Rminus_diag add0e in H3.
    simpl in H3.
    by rewrite H3.
  Qed.
End le_giry.


(* Should eventually be moved to and completed within giry.v *)
Section AdditionalMonadLaws.
  Local Open Scope classical_set_scope.
  Local Open Scope ereal_scope.

  Lemma gMap_gRet: ∀ {d1 d2: measure_display} {T1 : measurableType d1} {T2 : measurableType d2} (t : T1) (f : T1 -> giryM T2) (H : measurable_fun setT f),
    gMap H (gRet t) ≡μ gRet (f t).
  Proof.
    intros. intros S HS.
    rewrite gMap_to_int; [|done].
    rewrite gRetInt_rw; [done |].
    have -> : (λ x : T1, (numfun.indic S (f x))%:E) =
              EFin \o (numfun.indic S) \o f.
    { intros. done. }
    eapply (@measurable_comp); [ by eapply @measurableT | by rewrite //= | | done ].
    (* Stupid *)
  Admitted.

  Lemma gret_id_left: ∀ {d1 : measure_display} {T1 : measurableType d1} (x : giryM T1),
    (gJoin \o gRet) x ≡μ x.
  Proof.
    intros. intros S HS.
    rewrite //= /gJoin_ev.
    rewrite gRetInt; [done|].
    by apply gEval_meas_fun.
  Qed.

  Lemma gRet_gBind: ∀ {d1 d2: measure_display} {T1 : measurableType d1} {T2 : measurableType d2} (t : T1) (f : T1 -> giryM T2) (H : measurable_fun setT f),
      gBind H (gRet t) ≡μ f t.
  Proof.
    intros.
    rewrite /gBind. simpl. rewrite gMap_gRet.
    replace (gJoin (gRet (f t))) with ((gJoin \o gRet) (f t)); auto.
    by rewrite gret_id_left.
  Qed.

  Lemma gBind_gRet: ∀ {d1 : measure_display} {T1 : measurableType d1} (t : giryM T1),
    gBind gRet_meas_fun t ≡μ t.
  Proof.
    intros.
    by rewrite /gBind gJoin_id1 gret_id_left.
  Qed.

  Lemma gBind_equiv: ∀ {d1 d2 : measure_display} {T1 : measurableType d1} {T2 : measurableType d2}
    [f f' : T1 → giryM T2] {H : measurable_fun setT f} {H' : measurable_fun setT f'} {p : giryM T1},
      (∀ a : T1, f a ≡μ f' a) -> gBind H p ≡μ gBind H' p.
  Proof.
    intros.
  Admitted.

  Lemma gBind_assoc_help: ∀ {d1 d2 d3: measure_display} {T1 : measurableType d1} {T2 : measurableType d2} {T3 : measurableType d3}
    {f : T1 -> giryM T2} {g : T2 -> giryM T3} (Hf : measurable_fun setT f) (Hg : measurable_fun setT g),
      measurable_fun setT ((gBind Hg) \o f).
  Proof.
    intros.
    apply measurableT_comp; auto.
    apply gBind_meas_fun.
  Qed.

  Lemma gBind_assoc: ∀ {d1 d2 d3: measure_display} {T1 : measurableType d1} {T2 : measurableType d2} {T3 : measurableType d3}
    {f : T1 -> giryM T2} {g : T2 -> giryM T3} {Hf : measurable_fun setT f} {Hg : measurable_fun setT g} (p : giryM T1),
      gBind Hg (gBind Hf p) ≡μ gBind (gBind_assoc_help Hf Hg) p.
  Proof.

  Admitted.

  Lemma gIter_plus {d1 : measure_display} {T1 : measurableType d1} (f : T1 → giryM T1) {H : measurable_fun setT f} (t : T1) (n m : nat) :
    gIter (n + m) f t ≡μ gBind' (gIter m f) (gIter n f t).
  Proof.
    rewrite (gBind'_meas_rw (gIter_meas_fun _ _)).
    revert t. induction n; intros.
    { rewrite gRet_gBind //. }
    simpl. rewrite !(gBind'_meas_rw (gIter_meas_fun _ _)).
    admit.
  Admitted.

  Global Instance is_det_proper {d} {T : measurableType d}:
    Proper (eq ==> (measure_eq (T:=T)) ==> eq) is_det.
  Proof.
    intros x y H0 μ1 μ2 H1.
    unfold is_det, has_support_in, mass'.
    subst x.
    rewrite /mass.
    apply propext; split;
    by move =><-.
  Qed.

  Lemma is_det_eq_meas_lem {d} {T : measurableType d} {t : T} {μ1 μ2 : giryM T}:
    μ1 ≡μ μ2 -> is_det t μ1 -> is_det t μ2.
  Proof.
    rewrite /is_det.
    intros H H1.
    rewrite -H1.
    by rewrite H.
  Qed.

  Lemma is_det_eq_meas {d} {T : measurableType d} {t : T} {μ1 μ2 : giryM T}:
    μ1 ≡μ μ2 -> is_det t μ1 ↔ is_det t μ2.
  Proof. intros ?; split; move=>?; eapply @is_det_eq_meas_lem; done. Qed.

  Lemma gRet_not_zero {d} {T : measurableType d} (a : T):
    ¬ is_zero (gRet a).
  Proof.
    rewrite /is_zero/measure_eq//=.
    intro H.
    apply R1_neq_R0.
    have H' : d.-measurable [set: T] by eapply @measurableT.
    specialize H with setT. apply H in H'.
    rewrite /mzero//=/dirac/=/numfun.indic//=/mzero//= in H'.
    rewrite mem_set in H'; [|done].
    rewrite //= in H'.
    inversion H'.
    done.
  Qed.

End AdditionalMonadLaws.

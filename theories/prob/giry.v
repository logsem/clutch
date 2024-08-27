(** Measures and probabilitiy from mathcomp-analysis *)

From mathcomp Require Import all_ssreflect all_algebra finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
From mathcomp.analysis Require Import reals ereal signed (* topology *) normedtype esum numfun measure lebesgue_measure lebesgue_integral.
From HB Require Import structures.

From clutch.prob.monad Require Export types.

Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Default Proof Using "Type".

(*

  (* Lemmas for for section 6 *)

  Lemma measurable_if_pushfowrard_subset {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2} (f : T1 -> T2) :
        (d2.-measurable  `<=` [set s : set T2 | d1.-measurable ( f@^-1` s )]) -> (measurable_fun setT f). Proof.
    intro HS.
    rewrite /measurable_fun.
    rewrite /subset in HS.
    intros X Y HY.
    specialize (HS Y HY).
    simpl in HS.
    rewrite setTI.
    apply HS.
  Qed.

  (** ********** 6. Measurability of (T₁ -> giryM T₂) functions *)

  (* FIXME: move *)
  Definition measurable_evaluations {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2} (f : T1 -> giryM T2) : Prop
    := forall (S : set T2), d2.-measurable S -> (@measurable_fun _ _ _ borelER setT (f ^~ S)).

  Section giry_measurable_characterization.
    Context {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}.
    Variable (f : T1 -> giryM T2).

    (* Check (f ^~ _ : T1 -> borelER). *)

    Lemma measurable_evals_if_measurable : measurable_fun setT f -> measurable_evaluations f.
    Proof using Type.
      intros Hm.
      rewrite /measurable_evaluations.
      intros S HS.
      replace (fun x : T1 => f x S) with ((@^~ S) \o f); last by apply functional_extensionality.

      apply (@measurable_comp _ _ _ _ _ _ setT (@^~ S : giryM T2 -> borelER)); auto.
      { apply subsetT. }
      apply (@giryM_eval_def_measurable _ _ _ HS).
    Qed.

    Lemma measurable_if_measurable_evals : measurable_evaluations f -> measurable_fun setT f.
    Proof.
      intro Hm.
      rewrite /measurable_evaluations/measurable_fun/= in Hm.

      apply (@measurable_if_pushfowrard_subset _ _ _ _ f).
      rewrite {1}/measurable/=.
      apply smallest_sub.
      { rewrite /sigma_algebra.
        constructor.
        - rewrite /= preimage_set0.
          apply measurable0.
        - intros ?.
          simpl.
          intro HA.
          rewrite setTD.
          rewrite -preimage_setC.
          apply measurableC.
          apply HA.
        - simpl.
          intros S MS.
          rewrite preimage_bigcup.
          apply bigcup_measurable.
          intros k _.
          apply MS.
      }
      rewrite /giry_subbase/subset/=.
      intros X [Y [HY HX]].

      have G1 : d1.-measurable [set: T1] by auto.
      specialize (Hm Y HY G1).
      rewrite /salgebraType/= in Hm.
      clear G1.

      rewrite /preimage_class_of_measures/preimage_class/= in HX.
      destruct HX as [B HB HBf].
      rewrite setTI in HBf.

      specialize (Hm B HB).
      rewrite setTI in Hm.

      rewrite <- HBf.
      rewrite <- comp_preimage.
      simpl.

      have HF : (fun x : T1 => f x Y) = ((SubProbability.sort (R:=R))^~ Y \o f).
      { apply functional_extensionality.
        intro x.
        by simpl.
      }

      rewrite HF in Hm.
      apply Hm.
    Qed.

    Lemma measurable_evals_iff_measurable : measurable_evaluations f <-> measurable_fun setT f.
    Proof using Type. split; [apply measurable_if_measurable_evals | apply measurable_evals_if_measurable]. Qed.

    (* Probably want to use measurable_evaluations as a builder for measuable_fun now, so I can
       instansiate THAT and get the measurable fun hierarchy bit automatically (by this lemma) *)

    (* I don't think we ever care about measruable_evaluations as a class (still useful as a lemma
       so I won't add a mixin + factory going the other direction )*)

    (* FIXME: Needs to be done outside of a section. Uncomment below (it works) and reorganize. *)


(*
HB.factory Record GiryMeasurableEvals {R : realType} {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2} (f : T1 -> giryM R T2) := { meas_evaluationsP : measurable_evaluations f }.

HB.builders Context R d1 d2 T1 T2 f of @GiryMeasurableEvals R d1 d2 T1 T2 f.
  Lemma measurable_subproof: measurable_fun setT f.
  Proof. apply measurable_evals_iff_measurable, meas_evaluationsP. Qed.

  HB.instance Definition _ :=
      isMeasurableMap.Build _ _ T1 (giryM R T2) f measurable_subproof.

HB.end.
*)

  End giry_measurable_characterization.





  (* FIXME: Expose alias to measurable function, not giryM_ret *)
  (* ie. giryM_ret_def, giryM_ret_aux, and giryM_ret *)

  (* TODO: Can this link into the STDPP monad interface? What do we do in probability already? *)
  (* Seems that the answer is no, this would cement that (eg. map only works with measurable functions). *)

  (** ********** 4. Monad return  *)

  Section giry_ret.
    (* FIXME: Seal the version it doesn't know is measurable *)
    Context {d} {T : measurableType d}.

    Local Definition giryM_ret_def : T -> giryM T := fun t0 => @dirac _ T t0 _.

    Local Lemma giry_ret_measurable : @measurable_fun _ _ T (giryM T) setT giryM_ret_def.
    Proof using Type.
      apply measurable_evals_iff_measurable.
      rewrite /measurable_evaluations.
      intros S SMeas.
      rewrite /measurable_fun/= .
      intros ? Y HY.
      (* NOTE: Since its using 'measurable, it seems that Borel or Lebesgue doesn't matter here.  *)
      remember (fun x : T => (\d_x)%R S) as f.
      rewrite /dirac in Heqf.
      have W : f = (comp EFin (indic S)).
      { apply functional_extensionality. intro. by rewrite Heqf/=. }
      rewrite W.
      rewrite setTI.
      rewrite comp_preimage.
      rewrite preimage_indic.
      remember (in_mem GRing.zero (mem (preimage EFin Y))) as B1; rewrite -HeqB1.
      remember (in_mem (GRing.one R) (mem (preimage EFin Y))) as B2; rewrite -HeqB2.
      destruct B1; destruct B2; simpl.
      - apply H.
      - apply measurableC, SMeas.
      - apply SMeas.
      - apply measurable0.
    Qed.

    HB.instance Definition _ :=
      isMeasurableMap.Build _ _ T (giryM T) giryM_ret_def giry_ret_measurable.

  End giry_ret.

  (* FIXME: This is the interface that should be used *)
  Definition giryM_ret {d} {T : measurableType d} : measurable_map T (giryM T) := giryM_ret_def.
  Lemma giryM_ret_aux {d} {T : measurableType d} (t : T) : giryM_ret t = dirac t.
  Proof using Type. auto. Qed.

  (* CHECK: Arguments to infer seem good *)
  (* Check giryM_ret _. *)
  (* TODO: Make some notation *)

  Section giry_ret_laws.
    (* TODO: Port laws from prob here *)
    Context {d} {T : measurableType d}.
  End giry_ret_laws.


  (** ********** 6. Expectations over the Giry Monad *)
  Section giryM_integrate_laws.
    (* TODO: Port laws from prob here *)
    Context {d} {T : measurableType d}.

    (* FIXME: Not sure if measurable_map is the right type to use here *)
    Definition giryM_integrate_def (f : measurable_map T (\bar R)) : giryM T -> \bar R
      := fun μ => (\int[μ]_x (f x))%E.

    Lemma giry_meas_integrate (f : measurable_map T (\bar R)) (Hf : forall x : T, (0%R <= f x)%E) :
      @measurable_fun _ _ (giryM T) (\bar R) setT (giryM_integrate_def f).
    Proof.
      rewrite /giryM_integrate_def.
      rewrite /=/salgebraType.


      (* The approximation lemma for f that corresponds roughly to the mathlib limits *)
      have HMT : d.-measurable [set: T] by [].
      have X : forall μ : measure T R,
       (\int[μ]_x f x)%E =
       @topology.lim (@constructive_ereal_extended__canonical__topology_Nbhs R)
         (@topology.fmap nat \bar R
            (@sintegral T R μ \o
               (fun x : nat =>
                @nnsfun_approx d T R [set: T] HMT f (@measurable_mapP d default_measure_display T \bar R f) x))
            (@topology.nbhs nat (topology.topology_set_system__canonical__topology_Filtered nat) topology.eventually)).
      { intro μ.
        refine (@nd_ge0_integral_lim d T R μ f (nnsfun_approx HMT (@measurable_mapP _ _ _ _ f)) Hf _ _).
        - intro x.
          intros n1 n2 Hle.
          have HR := (@nd_nnsfun_approx d T R setT HMT f (@measurable_mapP _ _ _ _ f)) n1 n2 Hle.
          by apply (asboolW HR).
        - intro x.
          refine (@cvg_nnsfun_approx d T R setT HMT f (@measurable_mapP _ _ _ _ f) _ x _).
          - intros ? ?.
            by apply Hf.
          - by simpl.
      }
      have Hr1 :
       (fun μ : giryType T => (\int[μ]_x f x)%E) =
       (fun μ => @topology.lim (@constructive_ereal_extended__canonical__topology_Nbhs R)
         (@topology.fmap nat \bar R
            (@sintegral T R μ \o
               (fun x : nat =>
                @nnsfun_approx d T R [set: T] HMT f (@measurable_mapP d default_measure_display T \bar R f) x))
            (@topology.nbhs nat (topology.topology_set_system__canonical__topology_Filtered nat) topology.eventually))).
      { apply functional_extensionality.
        intro x.
        apply (X x).
      }
      rewrite Hr1.
      clear Hr1.
      clear X.

      (* This is a related measurable function *)
      (* Check @ge0_emeasurable_fun_sum d T R setT. (* This sum is over T.*) *)

      (* This one could actually be applied, if we can do the right rewrites to the sum? *)
      (* Reduces the problem to proving measurablility at evey approximation level *)
      have h_seq (i : nat) (μ : giryM T) : \bar R.
      { admit.  }

      (* Check @ge0_emeasurable_fun_sum _ (giryM T) R setT h_seq _. *)



      have Questionable : forall μ : giryType T,
           (topology.lim
             (topology.fmap (sintegral μ \o (fun x : nat => nnsfun_approx HMT measurable_mapP x))
                (@topology.nbhs nat (topology.topology_set_system__canonical__topology_Filtered nat) topology.eventually)))
        =
             (topology.lim
               (topology.fmap (fun n : nat => (\sum_(0 <= i < n) h_seq i μ)%R)
                  (@topology.nbhs nat (topology.topology_set_system__canonical__topology_Filtered nat) topology.eventually))).
      { intros AAAA. (* ???? *)
        simpl.
        intro μ.

        (* Rewriting sintegral *)
        have X1 : (comp (sintegral μ) (fun x : nat => nnsfun_approx HMT measurable_mapP x)) =
                  (fun x : nat => (sintegral μ (nnsfun_approx HMT measurable_mapP x))).
        { intros What1 What2. rewrite /comp. apply functional_extensionality. intro x. simpl. admit. }
        erewrite X1. Unshelve. 2: apply AAAA. (* ???? *)
        clear X1.
        have X2 : forall n : nat,
          sintegral μ (nnsfun_approx HMT measurable_mapP n)
          =
            (\sum_(x <- finite_support 0 [set r | 0 < r]
                (fun x : join_Num_POrderedZmodule_between_GRing_Nmodule_and_Order_POrder R =>
                 (x%:E * μ (nnsfun_approx HMT measurable_mapP n @^-1` [set x]))%E))
      (x%:E * μ (nnsfun_approx HMT measurable_mapP n @^-1` [set x]))%E)%R.
        { intros What1 What2 What3.
          intro n.

          rewrite (@sintegralEnnsfun _ _ R μ (nnsfun_approx HMT measurable_mapP n)).
          simpl.
          admit.
        }
      rewrite (functional_extensionality _ _ (X2 AAAA AAAA AAAA)).
      clear X2.
      simpl.
      f_equal.
      f_equal.
      apply functional_extensionality.
      intro n.
      simpl.

      (* have Strange : forall z, h_seq z μ = (z%:E * μ (nnsfun_approx HMT measurable_mapP n @^-1` [set z]))%R.  *)

      (* FIXME: Next step-- is this provable? *)
      (* Check [set r | 0 < r].
      Check index_iota 0 n. *)

      (* Aside from coercion hell, we should be able to define
         h_seq = (x%:E * μ (nnsfun_approx HMT measurable_mapP n @^-1` [set x])) *)
      (* I think that some of this could be avoided by just picking a single RealType? I see these weird
       types join_Num_POrderedZmodule_between_GRing_Nmodule_and_Order_POrder so think it originates from
       some inference related to coercions. Plus, it's weird that I can't use the type that's displayed
       for sintegralEnnsfun... that "finite support" magically pops up when I declare it using the type
       from sintegralEnnsfun  *)
      admit.
      }
      rewrite (functional_extensionality _ _ (Questionable _)).
      clear Questionable.

      refine (@ge0_emeasurable_fun_sum _ (giryM T) R setT h_seq _ _).
      - (* Probably doable for sane h_seq *)
        admit.

      (* Need to prove h_seq is measurable *)
      (* mult. measurable is measurable *)
      (* measure ofnnsfun_approx is measurable? *)
      (* - Regardless of a lemma for this, there should be a lemma for finite sums, which that is. *)
      (* Then I just need measuring a set is measurable, which is giryM_eval_def_measurable? Or something like that. *)

      Restart.






      have H1 : (forall x : T, [set: T] x -> (0%R <= f x)%E) by admit.
      have H2 : d.-measurable [set: T] by admit.
      (*

      Check @is_cvg_sintegral d T R.

      Search (topology.lim (topology.fmap _ _) = _).

      Check @emeasurable_fun_cvg _ (giryM T) R setT _
        (fun μ : giryType T =>
           topology.lim
             (topology.fmap (sintegral μ \o (fun x : nat => nnsfun_approx _ measurable_mapP x))
                (@topology.nbhs nat (topology.topology_set_system__canonical__topology_Filtered nat) topology.eventually))).
      (* Maybe, but this is not my main approach. *)


      (* I want to pull terms through that limit to eventually get to the limit of approximations of f. *)
      (* f x is the limit of approximations evaluated at x *)
      Check @cvg_nnsfun_approx d T R setT H2 f (@measurable_mapP _ _ _ _ f) H1.
      (* Search topology.lim topology.cvg_to. *)

      Search measurable_fun topology.lim.
      *)



      (* Check sequences.congr_lim. (* Only aesthetically useful *) *)

      (* Relate cvg_lim to lim *)
      (* Check topology.cvg_lim. *)

      (* Approximations converge to the limit *)
      (* Check is_cvg_sintegral. (* Limit of sintegral *) *)

      (* Check approximation. (* Use on Hypothesis. *) *)

      (* Can I turn the lim thing into a cvg_to problem? *)


      (* Can I simplify the sintegral? *)
      (* Check sintegralEnnsfun. (* Turn integral into sum *)
      Search topology.fmap (_ \o _).
      Check fun μ => @sintegralE d T R _. *)
      (* (μ \o (fun x : nat => nnsfun_approx HMT measurable_mapP x)). *)


      (* Check topology.fmap_comp (sintegral _) (fun x : nat => nnsfun_approx _ measurable_mapP x). *)

      (* Search topology.lim topology.fmap topology.eventually.
      Search topology.lim sintegral.

      Search topology.fmap sintegral.
      Search measurable_fun. *)




      (* I don't know if I can do much more with measurable_fun? Maybe MCT? since it's about th emeasurability of a limit? *)
      (* Locate cvg_monotone_convergence. *)

      (* Search measurable_fun.
      rewrite /measurable_fun.
      intros _.
      intros B HB.
      rewrite setTI.
       *)


(* What is this stuff. Why did I save it.
measurable_fun_esups:
measurable_fun_limn_esup:
measurableT_comp:
measurable_fun_sups:
measurable_comp:
measurable_fun_limn_sup:
*)

      (* Search measurable_fun topology.lim. *)
      rewrite /sintegral/=.
      (**)

    Admitted.

    HB.instance Definition _ (f : measurable_map T (\bar R)) (Hf : forall x : T, (0%R <= f x)%E):=
      isMeasurableMap.Build _ _ (giryM T) (\bar R) (giryM_integrate_def f) (giry_meas_integrate Hf).

  End giryM_integrate_laws.


  (* FIXME: Seal above definitions *)
  (* Might need to add nonnegative functions into the hierarchy (or internalize into a \bar R wrapper?)*)
  (*
  Definition giryM_integrate {d} {T : measurableType d} (f : measurable_map T (\bar R)) (Hf : forall x : T, (0%R <= f x)%E) : measurable_map (giryM T) (\bar R)
    := (@giryM_integrate_def f ).
  Lemma giryM_integrate_aux {d} {T : measurableType d} (f : measurable_map T (\bar R)) :
    forall μ, (giryM_integrate f μ = \int[μ]_x (f x))%E.
  Proof using Type. done. Qed.
   *)


  (* TODO: Mcmp_aux / seal *)

  (** ********** ?. Constant is measurable_map *)
  Section MeasurableMap_const.
    Context {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}.

    Lemma Mcst_def_measurable (t : T2):
      @measurable_fun _ _ T1 T2 setT (cst t).
    Proof using Type. apply measurable_cst. Qed.


    HB.instance Definition _ (t : T2) :=
      isMeasurableMap.Build _ _ T1 T2 (cst t) (Mcst_def_measurable t).
  End MeasurableMap_const.



  (** ********** 7. Monad map  *)

  Section giryM_map_definition.
    Context {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2}.

    Lemma pushforward_setT (f : measurable_map T1 T2) (m : giryM T1) : (pushforward m (@measurable_mapP _ _ _ _ f) setT <= 1)%E.
    Proof using Type. rewrite /pushforward preimage_setT. apply sprobability_setT. Qed.

    HB.instance Definition _ (f : measurable_map T1 T2) (m : giryM T1) := Measure_isSubProbability.Build _ _ _ (pushforward m (@measurable_mapP _ _ _ _ f)) (pushforward_setT f m).

    Definition giryM_map_def (f : measurable_map T1 T2) (m : giryM T1) : giryM T2 := pushforward m (@measurable_mapP _ _ _ _ f).

    Lemma giryM_map_def_is_measurable (f : measurable_map T1 T2) : @measurable_fun _ _ (giryM T1) (giryM T2) setT (giryM_map_def f).
    Proof.
      apply measurable_if_measurable_evals.
      rewrite /measurable_evaluations.
      (* Check pushforward. *)

      intros S HS.
      apply measurable_if_pushfowrard_subset.
      intros Y HY.
      simpl.

      (*

      have HM := @measurable_mapP _ _ _ _ f.
      apply measurable_if_pushfowrard_subset.
      rewrite /giryM_map_def.
      intros S SM.
      simpl.
      rewrite /pushforward.
      simpl.*)


      (* rewrite /giryM_map_def/measurable_fun.
      intros ? Y YMeas.
      rewrite setTI.
      rewrite /pushforward.
      rewrite /preimage.*)
    Admitted.

    HB.instance Definition _ (f : measurable_map T1 T2) :=
      isMeasurableMap.Build _ _ (giryM T1) (giryM T2) (giryM_map_def f) (giryM_map_def_is_measurable f).

  End giryM_map_definition.


  (* FIXME: Seal above definitions *)
  Definition giryM_map {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2} (f : measurable_map T1 T2) :
      measurable_map (giryM T1) (giryM T2)
    := giryM_map_def f.
  Lemma giryM_map_aux {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2} (f : measurable_map T1 T2) :
    forall μ, giryM_map f μ = pushforward μ  (@measurable_mapP _ _ _ _ f).
  Proof. done. Qed.


  Section giry_map_laws.
    (* TODO: Port laws from prob here *)
    Context {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}.

    Lemma giryM_map_zero (f : measurable_map T1 T2) : giryM_map f mzero = mzero.
    Proof.
      rewrite giryM_map_aux/mzero/pushforward.
      (* functional_extensionality doesn't work... weird *)
    Admitted.

    Lemma giryM_map_cst (μ : giryM T1) (k : T2) : giryM_map (cst k) μ = giryM_ret k .
    Proof.
      rewrite giryM_map_aux.
      rewrite /pushforward.
      rewrite giryM_ret_aux.

      (* Defining a specific version of cst that is a measurable function (Mcst, like Mcmp) might fix this *)

      (* Weird that I can't apply functional extensionality *)
      have H : (fun A : set T2 => μ (cst k @^-1` A)) = (fun A : set T2 => ((\1_A k)%:E)).
      { apply functional_extensionality.
        intro A.
        rewrite preimage_cst.
        rewrite /indic.
        destruct (k \in A).
        - simpl.
          admit.
        - simpl.
          admit.
      }
      rewrite H.
      clear H.
      rewrite /dirac.
      Fail reflexivity.
      (* ???? *)
      (* This whole proof is haunted *)
    Admitted.

    Lemma giryM_map_integrate (g : measurable_map T2 (\bar R)) (h : measurable_map T1 T2) (μ : giryM T1):
      (\int[giryM_map h μ]_x g x  = \int[μ]_x g (h x))%E.
    Proof.
      rewrite giryM_map_aux.
      rewrite integral_pushforward.
      (* Can this be weakened to include negative g? *)
      - simpl.
        reflexivity.
      - admit.
      - admit.
    Admitted.
  End giry_map_laws.



  (** ********** 8. Monad join *)


  Section giryM_join_definition.
    Context {d} {T : measurableType d}.

    Definition giryM_join_def {d} {T : measurableType d} (m : giryM (giryM T)) : (set T -> \bar R)
      := (fun S => \int[m]_μ (μ S))%E.

    (* For the proofs,
        I don't know if there's any way to reuse the measurability of evaluation functions to do this. *)

    Section giryM_join_measure_def.
      Context (m : giryM (giryM T)).

      Definition giryM_join0 : giryM_join_def m set0 = 0%E.
      Proof.
        rewrite /giryM_join_def.
        have X1 : (\int[m]_μ μ set0)%E  = ((integral m setT (cst GRing.zero)))%E.
        { f_equal.
          apply functional_extensionality.
          intro μ.
          by rewrite measure0.
        }
        rewrite X1.
        rewrite integral_cst.
        - by rewrite (mul0e _).
        - rewrite /=.
          by apply (@measurableT _ (salgebraType _)).
      Qed.

      Definition giryM_join_ge0 A : (0 <= giryM_join_def m A)%E.
      Proof.
        rewrite /giryM_join_def.
        apply integral_ge0.
        intros μ _.
        apply (measure_ge0 μ A).
      Qed.

      Definition giryM_join_semi_additive : semi_sigma_additive (giryM_join_def m).
      Proof.
        (* Search semi_sigma_additive.
        Search sigma_additive.
        Search additive. *)
        rewrite /semi_sigma_additive.
        intros F Fmeas Htriv_int HFunion_meas.
        rewrite /giryM_join_def.
        (* Search integral bigcup. (* Seems like the limit we want *) *)

        (* Check (integral_bigcup Htriv_int Fmeas).
        (* Search topology.cvg_to topology.lim.
        Search (topology.cvg_to _ (topology.nbhs _)) topology.lim. *) *)

      Admitted.

      HB.instance Definition _
        := isMeasure.Build _ _ _
             (giryM_join_def m)
             giryM_join0
             giryM_join_ge0
             giryM_join_semi_additive.

      Lemma giryM_join_setT : (giryM_join_def m setT <= 1)%E.
      Proof.
        rewrite /giryM_join_def.
        have H : (\int[m]_μ μ [set: T] <= \int[m]_μ 1)%E.
        { (* Search integral (_ <= _)%E. *)
          apply ge0_le_integral.
          - by [].
          - intros ? ?; by [].
          - simpl.
            admit.
          - intros ? ?; by [].
          - admit.
          - intros ? ?.
            (* Because of subprobability *)
            admit.  }

      (* Now I just need that the measure of m is at most 1,
         Also true because of subprobability. *)
      Admitted.

      HB.instance Definition _ :=  Measure_isSubProbability.Build _ _ _ (giryM_join_def m) giryM_join_setT.

    End giryM_join_measure_def.

    Definition giryM_join_def' : giryM (giryM T) -> (giryM T) := giryM_join_def.

    Lemma giryM_join_def'_measurable : @measurable_fun _ _ (giryM (giryM T)) (giryM T) setT giryM_join_def'.
    Proof.

    Admitted.

    HB.instance Definition _ :=
      isMeasurableMap.Build _ _ (giryM (giryM T)) (giryM T) giryM_join_def' giryM_join_def'_measurable.

  End giryM_join_definition.


  (* FIXME: Seal above defs *)
  Definition giryM_join {d} {T : measurableType d} : measurable_map (giryM (giryM T)) (giryM T) := giryM_join_def'.
  Lemma giryM_join_aux {d} {T : measurableType d} (m : giryM (giryM T)) :
    forall S, (giryM_join m S = \int[m]_μ (μ S))%E.
  Proof. done. Qed.



  Section giryM_join_laws.
    (* TODO: Port laws from prob here *)
    Context {d} {T : measurableType d}.
    Context {d2} {T2 : measurableType d2}.

    Lemma giryM_join_zero : giryM_join mzero = (mzero : giryM T).
    Proof.
      apply giryM_ext.
      apply functional_extensionality.
      intro S.
      rewrite /mzero.
      (* Odd that it doesn't reduce mzero? *)
      simpl.


    Admitted.

    (* lintegral_join *)
    Lemma giryM_join_integrate (m : giryM (giryM T)) (f : T -> \bar R) (Hf : forall x : T, (0%R <= f x)%E)
      (mf : measurable_fun setT f) :
      (\int[giryM_join m]_x (f x) = \int[m]_μ (\int[μ]_x f x))%E.
    Proof.
      have HTmeas : d.-measurable [set: T] by [].

      (* Rewrite integral over (giryM_join M) to limit. *)
      erewrite nd_ge0_integral_lim; first last.
      - intro x.
        apply (@cvg_nnsfun_approx _ _ _ setT HTmeas _ mf).
        - intros. apply Hf.
        - by simpl.
      - intros x n' m' Hle.
        (* Check (@nd_nnsfun_approx _ _ _ _ _ _ _ n' m' Hle). *)
        (* Need to turn the %R comparison into %O)*)
        admit.
      - apply Hf.

      (* Rewrite integral over μ to limit, under the RHS integral. *)
      have Setoid1 : forall g h, g = h -> (\int[m]_μ g μ)%E = (\int[m]_μ (h μ))%E.
      { intros. f_equal. apply functional_extensionality. intros. by rewrite H. }

      erewrite Setoid1; last first.
      { apply functional_extensionality.
        move=> y.
        erewrite nd_ge0_integral_lim.
        - reflexivity.
        - apply Hf.
        - (* See above admit *)
          admit.
        - intro x.
          apply (@cvg_nnsfun_approx _ _ _ setT HTmeas _ mf).
          - intros. apply Hf.
          - by simpl.
      }

    (* Rewrite the sintegral of nnsfun_approx into a sum *)
    rewrite topology.fmap_comp.

    have Setoid2 : forall S, forall g h, g = h  -> (topology.fmap g S) = (topology.fmap h S).
    { intros ? ? ? ? ? H. by rewrite H. }
    erewrite Setoid2; last first.
    - apply functional_extensionality.
      apply (sintegralE _).  (* FIXME: Possible issue down the road: sintegralE vs sintegralET *)

    under eq_integral=> ? _ do rewrite topology.fmap_comp.

    (* Evaluate the giryM_join on the LHS into an integral *)
    erewrite
      (Setoid2 _ _ _ _
         (fun f' => (bigop.body GRing.zero
                    (finite_support GRing.zero (image setT (fun i : T => f' i))
                       (fun x : R => _))
                    _ ))); last first.
    - (* What a nightmare, there has to be a better way to rewrite under the integral sign *)
      (* Look for an example in mathcomp analysis source *)
      apply functional_extensionality.
      intro f'.
      f_equal.
      apply functional_extensionality.
      intro x.
      f_equal.
      rewrite /giryM_join.
      rewrite /giryM_join_def'.
      simpl.
      rewrite /giryM_join_def.
      done.
    simpl.
    rewrite -topology.fmap_comp.

    under eq_integral=> ? _ do rewrite -topology.fmap_comp.

    rewrite (@monotone_convergence _ (giryM T) R m setT _ _ _ _ _); first last.
    - (* Sequence is monotone *)
      (* Unset Printing Notations. *)
      intros μ _.
      (* Check nd_nnsfun_approx.
      (* Search homomorphism_2 bigop.body. *) *)

      (* Might need to do this directly.. I can't find any relevant theorems for this type of sum *)
      (* Surely this proof was done somewhere else so I'm confident it's possible. *)
      intros x y Hle.
      admit.
    - (* Sequence is nonnegative *)
      intros n μ _.
      simpl.
      (* Search 0%R (_ <= _)%E "sum". *)
      (* None of the relevant theorems work, but something will. *)
      admit.
    - (* Sequence is pointwise measurable *)
      intros n.
      apply emeasurable_fun_fsum. (* Measurability of finite sums *)
      { (* Sum is finite *)  admit. }
      intro range_element.
      (* Seems to be no lemmas that mul measurable is measurable in ENNR, only R *)
      admit.
    - (* ⊤ is measurable *)
      admit.


    (* Pointwise equality between limits *)
    f_equal.
    f_equal.
    rewrite /comp.
    apply functional_extensionality.
    intro n.

    (* Exchange finite sum with integral on the RHS (LHS seems harder) *)
    rewrite ge0_integral_fsum; first last.
    - (* Range of approximation is finite *)
      admit.
    - (* Argument is nonnegative *)
      intros n' μ _.
      admit.
    - (* Argument is pointwise measurable. *)
      admit.
    - (* ⊤ is measurable *)
      admit.


    f_equal.
    - (* The index sets are the same *)
      (* As predicted, it's way easier do prove this down here *)
      f_equal.
      apply functional_extensionality.
      intro x.
      rewrite /giryM_join_def.
      (* Scalar multiplication *)
      admit.
    - (* The bodies are the same *)
      apply functional_extensionality.
      intro x.
      f_equal.
      (* Scalar multiplication *)
      admit.
    Admitted.


    Lemma giryM_join_map_map (mf : measurable_map T T2) (m : giryM (giryM T)) :
      giryM_join (giryM_map (giryM_map mf) m) = giryM_map mf (giryM_join m).
    Proof.
      apply giryM_ext.
      apply functional_extensionality.
      intro S.
      rewrite giryM_join_aux.
      rewrite giryM_map_aux.
      rewrite giryM_map_aux.
      (* rewrite giryM_join_integrate. *)
    Admitted.

    Lemma giryM_join_map_join (m : giryM (giryM (giryM T))) :
      giryM_join (giryM_map giryM_join m) = giryM_join (giryM_join m).
    Proof. Admitted.

    Lemma giryM_join_map_ret (μ : (giryM T)) :
      giryM_join (giryM_map giryM_ret μ) = μ.
    Proof. Admitted.

    Lemma giryM_join_ret (μ : (giryM T)) :
      giryM_join (giryM_ret μ) = μ.
    Proof. Admitted.
  End giryM_join_laws.


  (** ********** ?. Composition of Measurable Maps (move up) *)

  (* FIXME: What is Coq's default composition operator? Make an instance for that. *)

  Section MeasurableMap_cmp.
    Context {d1 d2 d3} {T1 : measurableType d1} {T2 : measurableType d2} {T3 : measurableType d3}.

    Lemma cmp_measurable (f : measurable_map T2 T3) (g : measurable_map T1 T2) :
      @measurable_fun _ _ T1 T3 setT (comp f g).
    Proof.
      apply (@measurable_comp _ _ _ _ _ _ setT).
      - (* Search measurable setT. *)
        (* Annoying *)
        admit.
      - apply subsetT.
      - apply measurable_mapP.
      - apply measurable_mapP.
    Admitted.

    HB.instance Definition _ (f : measurable_map T2 T3) (g : measurable_map T1 T2) :=
      isMeasurableMap.Build _ _ T1 T3 (comp f g) (cmp_measurable f g).

  End MeasurableMap_cmp.

  Definition Mcmp {d1 d2 d3} {T1 : measurableType d1} {T2 : measurableType d2} {T3 : measurableType d3}
    (f : measurable_map T2 T3) (g : measurable_map T1 T2) : measurable_map T1 T3
    := comp f g.


  (** ********** 8. Monad bind *)

  Definition giryM_bind {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}
                        (f : measurable_map T1 (giryM T2)) : measurable_map (giryM T1) (giryM T2)
    := Mcmp giryM_join (giryM_map f).

  Section giryM_bind_laws.
    (* TODO: Port laws from prob here *)
    Context {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}.
    Context {f : measurable_map T1 (giryM T2)}.

    Lemma giryM_bind_0_l : giryM_bind f mzero = mzero.
    Proof using Type.
      rewrite /giryM_bind.
      rewrite /Mcmp/comp.
      (* FIXME *)
      Opaque giryM_join.
      Opaque giryM_map.
      simpl.
      Transparent giryM_join.
      Transparent giryM_map.
      rewrite giryM_map_zero.
      apply giryM_join_zero.
    Qed.

    (* FIXME: make it so that I don't have to annotate giryM T2 here? *)
    Lemma giryM_bind_0_r (μ : giryM T1) : giryM_bind (cst (mzero : giryM T2)) μ = mzero.
    Proof using Type.
      rewrite /giryM_bind.
      rewrite /Mcmp/comp.
      (* FIXME *)
      Opaque giryM_join.
      Opaque giryM_map.
      simpl.
      Transparent giryM_join.
      Transparent giryM_map.
      rewrite giryM_map_cst.
      by rewrite giryM_join_ret.
    Qed.

    Lemma giryM_bind_measurable : measurable_fun setT (giryM_bind f).
    Proof using Type.
      rewrite /giryM_bind.
      rewrite /Mcmp/comp.
      (* FIXME *)
      Opaque giryM_join.
      Opaque giryM_map.
      simpl.
      Transparent giryM_join.
      Transparent giryM_map.
      apply cmp_measurable.
    Qed.

    Lemma giryM_bind_eval (m : giryM T1) (s : set T2) (HS : measurable s) :
      (giryM_bind f m s = \int[m]_x f x s)%E.
    Proof. Admitted.

    Lemma giryM_bind_integrate (m : giryM T1) (g : T2 -> \bar R) (mg : measurable_fun setT g) :
      (\int[giryM_bind f m]_x g x = \int[m]_a (\int[f a]_x g x))%E.
    Proof. Admitted.

    Lemma giryM_bind_ret_l t : giryM_bind f (giryM_ret t) = f t.
    Proof. Admitted.

    Lemma giryM_bind_ret_r (m : giryM T1) : giryM_bind giryM_ret m = m.
    Proof. Admitted.


    Context {d3} {T3 : measurableType d3} (g : measurable_map T2 (giryM T3)).

    Lemma giryM_bind_bind (m : giryM T1) :
      giryM_bind g (giryM_bind f m) = giryM_bind (comp (giryM_bind g) f) m.
    Proof.
      (* Probably Mcmp *)
      rewrite /giryM_bind.
    Admitted.

    (* Make identity a measurable_map *)
    (* Lemma giryM_join_bind (m : giryM (giryM T1)) :
      giryM_join m = giryM_bind (fun x => x) m. *)

  End giryM_bind_laws.

End giry.
*)

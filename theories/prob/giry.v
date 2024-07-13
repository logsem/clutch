(** Measures and probabilitiy from mathcomp-analysis *)

From mathcomp Require Import all_ssreflect all_algebra finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
From mathcomp.analysis Require Import reals ereal signed (* topology *) normedtype esum numfun measure lebesgue_measure lebesgue_integral.
From HB Require Import structures.

Import Coq.Logic.FunctionalExtensionality.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**   Summary

      giryType T              Type of points in the giry sigma algebra on T, namely, subdistributions on T
      giryM T                 Measurable space on giryType (measures)

      T.-giry                 Display for the giry sigma algebra on T
      T.-giry.-measurable     Measurability in the giry sigma algebra on T

      Monad operations, each respects subdistribution structure on giryM
        giryM_ret
        giryM_map
        giryM_join
        giryM_bind


    CITE: Mathlib
*)

Reserved Notation "T .-giry" (at level 1, format "T .-giry").
Reserved Notation "T .-giry.-measurable"
 (at level 2, format "T .-giry.-measurable").



(** ********** 0. Define HB structure for measurable functions *)
(* This is very close to isMeasurableFun, but the codomain is not a realType. *)
(* Odd that they don't have this in the Hierarchy already? *)
(* The reason we want this is to avoid carrying around measurability requirements everywhere *)


HB.mixin Record isMeasurableMap d1 d2 (T1 : measurableType d1) (T2 : measurableType d2)
  (f : T1 -> T2) := {
  measurable_mapP : measurable_fun setT f
}.

#[short(type=measurable_map)]
HB.structure Definition MeasurableMap {d1} {d2} T1 T2 :=
  {f of @isMeasurableMap d1 d2 T1 T2 f}.


(* FIXME: Builder for measurableFun to RealType? Or does this go automatically?  *)


Section measurability_lemmas.
  Context {d1} {T1 : measurableType d1}.
  Context {d2} {T2 : measurableType d2}.

  (* Lemma measurability_image : forall S1 : set T1, forall S2 : set T2,
    d1.-measurable S1 -> d2.-measurable S2 ->  *)

End measurability_lemmas.


Section giry.
  Context (R : realType). (* FIXME: rather annoying to not infer this from context *)
  Local Open Scope classical_set_scope.

  (* FIXME: Are these the same? Or is 'measurable derived from the Lebesgue measure? Would that be an issue? *)
  (* 'measurable breaks when I remove the import to lebesgue_measure *)
  Definition ereal_borel_subbase : set (set \bar R) := [set N | exists x, ereal_nbhs x N].

  Definition ereal_borel_sets : set (set \bar R) := <<s [set N | exists x, ereal_nbhs x N]>>.
  Definition ereal_meas_sets : set (set \bar R) := 'measurable.

  Definition giryType {d} T : Type := @subprobability d T R.

  (** ********** 1. Define the measurable sets of a giry sigma algebra *)
  Section giry_space.
    Variable (d : measure_display) (T : measurableType d).

    (* #[log] *)
    HB.instance Definition _ := gen_eqMixin (giryType T).
    HB.instance Definition _ := gen_choiceMixin (giryType T).

    Lemma mzero_setT : (@mzero d T R setT <= 1)%E.
    Proof using Type. by rewrite /mzero/=. Qed.

    HB.instance Definition _ := Measure_isSubProbability.Build _ _ _ (@mzero d T R) mzero_setT.

    HB.instance Definition _ := isPointed.Build (giryType T) mzero.

    Definition preimage_class_of_measures (S : set T) : set (set (giryType T)) :=
      @preimage_class (giryType T)
        (\bar R)                  (* Range type *)
        setT                      (* Domain set *)
        (fun μ => μ S)              (* Evaluation function *)
        ereal_borel_sets           (* Range sets*).

    Definition giry_subbase : set (set (giryType T))
      := [set C | exists (S : set T) (_ : measurable S), preimage_class_of_measures S C].

    Definition giry_measurable : set (set (giryType T)) := <<s giry_subbase>>.


  End giry_space.



  Definition giryM_display {d} {T} := sigma_display (@giry_subbase d T).

  Definition giryM {d} (T : measurableType d) : measurableType giryM_display
    := [the measurableType _ of salgebraType (@giry_subbase _ T)].

  Notation "T .-giry" := (@giryM_display _ T) : measure_display_scope.
  Notation "T .-giry.-measurable" := (measurable : set (set (giryM T))) : classical_set_scope.



  Definition borelER_display := sigma_display ereal_borel_subbase.
  Definition borelER : measurableType borelER_display
    := [the measurableType _ of salgebraType ereal_borel_subbase].

  Check measurability.

  (** ********** 2. Test: Examples of measuring sets *)
  Section giry_space_example.
    Context {d : measure_display} (T : measurableType d).

    (* Example: Measuring sets in the Giry space *)
    Example test_giry_measures_0 : T.-giry.-measurable (set0 : set (giryM T)).
    Proof using Type. simpl. apply measurable0. Qed.

    Example test_giry_measures_T : T.-giry.-measurable [set: giryM T].
    Proof using Type. rewrite /=. apply (@measurableT _ (salgebraType _)). Qed.

    (* giryM is also a measurable type, so can be nested. *)
    Example test_giry_measures_0' : (giryM T).-giry.-measurable (set0 : set (giryM (giryM T))).
    Proof using Type. simpl. apply measurable0. Qed.

  End giry_space_example.




  (** ********** 3. Test: Examples of integration *)

  Section giry_integral_example.
    Context {d : measure_display} (T : measurableType d).

    Variable (μ_target : giryM T).  (* Some point in the space of measures on T*)

    (* The dirac measure using that point *)
    Example giry_ret_μ : giryM (giryM T) := @dirac _ _ μ_target _.

    Example int_zero_over_dirac : (\int[giry_ret_μ]_x cst 0%:E x)%E = 0%:E.
    Proof using Type. apply integral0. Qed.

    Example int_one_over_dirac : (\int[giry_ret_μ]_x cst 1%:E x)%E = 1%:E.
    Proof using Type.
      rewrite integral_cst /=.
      - by rewrite diracT mul1e.
      - rewrite -setC0.
        apply (@measurableC _ (giryM _)).
        by apply measurable0.
    Qed.
  End giry_integral_example.





  (** ********** 5. Measurability of evaluation maps *)
  Section giryM_eval.
    Context {d} {T : measurableType d}.

    Local Definition giryM_eval_def (S : set T) (HS : d.-measurable S) : giryM T -> borelER := (fun μ => μ S).

    Check measurable_fun.



    (* Evaluation functions are measurable maps *)

    (* FIXME: do we actually use Borel \bar R anywhere here? *)

    (* Yes, first line, to apply the comap lemma. Maybe a more general comap lemma can avoid this. *)

    Local Lemma giryM_eval_def_measurable (S : set T) (HS : d.-measurable S) : @measurable_fun _ _ (giryM T) borelER setT (giryM_eval_def HS).
    Proof using Type.
      apply (@measurability _ _ _ _ _ (giryM_eval_def HS) ereal_borel_subbase); first by simpl.
      rewrite /T.-giry.-measurable/=.
      rewrite {2}/giry_subbase/=.
      apply  (@subset_trans _ (giry_subbase (T:=T))); last by apply sub_gen_smallest.
      rewrite /subset/=.
      intros X.
      rewrite /preimage_class/=.
      intros [Y HY <-].
      rewrite {1}/giry_subbase/=.
      exists S, HS.
      rewrite /preimage_class_of_measures/preimage_class/=.
      exists Y.
      { apply sub_gen_smallest.
        rewrite /ereal_borel_subbase/= in HY.
        done. }
      done.
    Qed.

    HB.instance Definition _ (S : set T) (HS : d.-measurable S) :=
      isMeasurableMap.Build _ _ (giryM T) borelER (giryM_eval_def HS) (giryM_eval_def_measurable HS).

  End giryM_eval.

  (* FIXME: This is the interface that should be used (seal the other?) *)

  Definition giryM_eval {d} {T : measurableType d} (S : set T) (HS : d.-measurable S) : measurable_map (giryM T) borelER
    := (giryM_eval_def HS).
  Lemma giryM_eval_aux {d} {T : measurableType d} (S : set T) (HS : d.-measurable S) :
    forall μ, giryM_eval HS μ = μ S.
  Proof using Type. done. Qed.



  (* Lemmas for for section 6 *)

  Lemma measurable_if_pushfowrard_subset {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2} (f : T1 -> T2) :
        (d2.-measurable  `<=` [set s : set T2 | d1.-measurable ( f@^-1` s )]) -> (measurable_fun setT f).
  Proof using Type.
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

    Check (f ^~ _ : T1 -> borelER).

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
    Proof using Type.
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
  Check giryM_ret _.
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

    (* measurable_lintegral *)
    (*  -> lintegral_bind *)
    (*    -> bind_bind *)
    (*  -> measurable_join  *)
    (* Taking expectaiton is measurable *)
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
      Check @ge0_emeasurable_fun_sum d T R setT. (* This sum is over T.*)

      (* This one could actually be applied, if we can do the right rewrites to the sum? *)
      (* Reduces the problem to proving measurablility at evey approximation level *)
      have h_seq (i : nat) (μ : giryM T) : \bar R.
      { admit.  }


      Check @ge0_emeasurable_fun_sum _ (giryM T) R setT h_seq _.


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
      Check [set r | 0 < r].
      Check index_iota 0 n.

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




      Check sequences.congr_lim. (* Only aesthetically useful *)

      (* Relate cvg_lim to lim *)
      Check topology.cvg_lim.

      (* Approximations converge to the limit *)
      Check is_cvg_sintegral. (* Limit of sintegral *)

      Check approximation. (* Use on Hypothesis. *)

      (* Can I turn the lim thing into a cvg_to problem? *)


      (* Can I simplify the sintegral? *)
      Check sintegralEnnsfun. (* Turn integral into sum *)
      Search topology.fmap (_ \o _).
      Check fun μ => @sintegralE d T R _.
      (* (μ \o (fun x : nat => nnsfun_approx HMT measurable_mapP x)). *)


      Check topology.fmap_comp (sintegral _) (fun x : nat => nnsfun_approx _ measurable_mapP x).

      Search topology.lim topology.fmap topology.eventually.
      Search topology.lim sintegral.

      Search topology.fmap sintegral.
      Search measurable_fun.




      (* I don't know if I can do much more with measurable_fun? Maybe MCT? since it's about th emeasurability of a limit? *)
      Locate cvg_monotone_convergence.

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

      Search measurable_fun topology.lim.
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





  (** ********** 7. Monad map  *)

  Section giryM_map_definition.
    Context {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2}.

    Lemma pushforward_setT (f : measurable_map T1 T2) (m : giryM T1) : (pushforward m (@measurable_mapP _ _ _ _ f) setT <= 1)%E.
    Proof using Type. rewrite /pushforward preimage_setT. apply sprobability_setT. Qed.

    HB.instance Definition _ (f : measurable_map T1 T2) (m : giryM T1) := Measure_isSubProbability.Build _ _ _ (pushforward m (@measurable_mapP _ _ _ _ f)) (pushforward_setT f m).

    Definition giryM_map_def (f : measurable_map T1 T2) (m : giryM T1) : giryM T2 := pushforward m (@measurable_mapP _ _ _ _ f).

    Lemma giryM_map_def_is_measurable (f : measurable_map T1 T2) : @measurable_fun _ _ (giryM T1) (giryM T2) setT (giryM_map_def f).
    Proof. Admitted.

    HB.instance Definition _ (f : measurable_map T1 T2) :=
      isMeasurableMap.Build _ _ (giryM T1) (giryM T2) (giryM_map_def f) (giryM_map_def_is_measurable f).

  End giryM_map_definition.


  (* FIXME: Seal above definitions *)
  Definition giryM_map {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2} (f : measurable_map T1 T2) :
      measurable_map (giryM T1) (giryM T2)
    := giryM_map_def f.
  Lemma giryM_map_aux {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2} (f : measurable_map T1 T2) :
    forall μ, giryM_map f μ = pushforward μ  (@measurable_mapP _ _ _ _ f).
  Proof using Type. done. Qed.


  Section giry_map_laws.
    (* TODO: Port laws from prob here *)
    Context {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}.
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
      Proof using Type.
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
      Proof using Type.
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
        Search integral bigcup. (* Seems like the limit we want *)

        Check (integral_bigcup Htriv_int Fmeas).
        Search topology.cvg_to topology.lim.
        Search (topology.cvg_to _ (topology.nbhs _)) topology.lim.

      Admitted.

      HB.instance Definition _
        := isMeasure.Build _ _ _
             (giryM_join_def m)
             giryM_join0
             giryM_join_ge0
             giryM_join_semi_additive.

      Lemma giryM_join_setT : (giryM_join_def m setT <= 1)%E.
      Proof. (* Does this need any additional assumptions? *) Admitted.

      HB.instance Definition _ :=  Measure_isSubProbability.Build _ _ _ (giryM_join_def m) giryM_join_setT.

    End giryM_join_measure_def.

    Definition giryM_join_def' : giryM (giryM T) -> (giryM T) := giryM_join_def.

    Lemma giryM_join_def'_measurable : @measurable_fun _ _ (giryM (giryM T)) (giryM T) setT giryM_join_def'.
    Proof. Admitted.

    HB.instance Definition _ :=
      isMeasurableMap.Build _ _ (giryM (giryM T)) (giryM T) giryM_join_def' giryM_join_def'_measurable.

  End giryM_join_definition.


  (* FIXME: Seal above defs *)
  Definition giryM_join {d} {T : measurableType d} : measurable_map (giryM (giryM T)) (giryM T) := giryM_join_def'.
  Lemma giryM_join_aux {d} {T : measurableType d} (m : giryM (giryM T)) :
    forall S, (giryM_join m S = \int[m]_μ (μ S))%E.
  Proof using Type. done. Qed.



  Section giryM_join_laws.
    (* TODO: Port laws from prob here *)
    Context {d} {T : measurableType d}.
    Context {d2} {T2 : measurableType d2}.

    Lemma giryM_join_zero : giryM_join mzero = (mzero : giryM T).
    Proof.
      simpl.
      rewrite /giryM_join_def'.
      rewrite /salgebraType.
      rewrite /giryType.
      (* How to I compare for equality? *)
      HB.about SubProbability.
      Search subprobability.

      (* Lol maybe this will work *)
      (* f_equal *)

    Admitted.

    (* lintegral_join *)
    Lemma giryM_join_integrate (m : giryM (giryM T)) (f : T -> \bar R) (Hf : forall x : T, (0%R <= f x)%E)
      (mf : measurable_fun setT f) :
      (\int[giryM_join m]_x (f x) = \int[m]_μ (\int[μ]_x f x))%E.
    Proof.
      have HTmeas : d.-measurable [set: T] by admit.

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
        intro y.
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
    (*Check (sintegral (giryM_join m)).
    Check (functional_extensionality _ _ (sintegralEnnsfun (giryM_join m))).
    Locate sintegralEnnsfun.
    have Hext := (functional_extensionality _ _ (sintegralEnnsfun (giryM_join m))). *)
    have Setoid2 : forall S, forall g h, g = h  -> (topology.fmap g S) = (topology.fmap h S).
    { intros ? ? ? ? ? H. by rewrite H. }
    erewrite Setoid2; last first.
    - apply functional_extensionality.
      apply (sintegralE _).  (* FIXME: Possible issue down the road: sintegralE vs sintegralET *)
    erewrite Setoid1; last first.
    { apply functional_extensionality.
      intro y.
      rewrite topology.fmap_comp.
      erewrite Setoid2.
      - reflexivity.
      - apply functional_extensionality.
        apply (sintegralE _). (* See sintegral comment above *)
    }
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

    Search finite_support esum.
    Search esum topology.lim.
    Check nneseries_esum.

    (* Want the LHS to be of the form
        topology.lim
          (topology.fmap
            (fun n : nat => (\sum_(0 <= i < n | P i) a i)%R)
            (topology.nbhs topology.eventually))
     *)
    (* nat -> (... R ...) *)
    Check  ((fun f' : T -> R =>
         (\sum_(x <- finite_support 0 (range f') (fun x : R => (x%:E * giryM_join_def m (f' @^-1` [set x]))%E))
             (x%:E * \int[m]_μ μ (f' @^-1` [set x]))%E)%R) \o (fun x : nat => nnsfun_approx HTmeas mf x)).

    have approx_func : nat -> R := (fun _ => 0%R).
    erewrite (Setoid2 _ _ _ _ (fun n => _)); last first.
    - apply functional_extensionality.
      intro n.
      simpl.
      (* What should the value of approx_func be? *)
      (* Get the i'th value of (range (nnsfun_approx HTmeas mf n))
         Map it through (nnsfun_approx HTmeas mf n @^-1`...)
         What is that? Is it just nnsfun_approx ... i* 2^-n? *)
      have A :
        (finite_support 0 (range (nnsfun_approx HTmeas mf n)) (fun x : R => (x%:E * giryM_join_def m (nnsfun_approx HTmeas mf n @^-1` [set x]))%E))%E =
        ([seq approx_func i | i <- (index_iota 0 n)] : seq R).
      { admit.  }
      rewrite A.

      clear A.
      erewrite (@big_map _ _ _ _ _ approx_func (index_iota 0 n) (fun _ => true) _).
      reflexivity.
    (* Great, now we should be able to exchange the limit?*)
    Check @nneseries_esum _ _ (fun _ => true). (* Err... maybe not. Unless the limit is inside the esum definition? *)
    Check sequences.nneseries_sum.
    (* This looks closer, but that inner sum is strange. Maybe check out the proof?  *)

    Search (topology.lim (topology.fmap _ _)) "sum".

    Check esum_fset. (* sum -> esum, but have to do above? *)
    (* rewrite esum_fset. *)
    Admitted.


    Lemma giryM_join_map_map (mf : measurable_map T T2) (m : giryM (giryM T)) :
      giryM_join (giryM_map (giryM_map mf) m) = giryM_map mf (giryM_join m).
    Proof. Admitted.

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

    Definition Mcmp_def (f : measurable_map T2 T3) (g : measurable_map T1 T2) : T1 -> T3
      := fun x => f (g (x)).

    Lemma Mcmp_def_measurable (f : measurable_map T2 T3) (g : measurable_map T1 T2) :
      @measurable_fun _ _ T1 T3 setT (Mcmp_def f g).
    Proof. Admitted.

    HB.instance Definition _ (f : measurable_map T2 T3) (g : measurable_map T1 T2) :=
      isMeasurableMap.Build _ _ T1 T3 (Mcmp_def f g) (Mcmp_def_measurable f g).

  End MeasurableMap_cmp.

  Definition Mcmp {d1 d2 d3} {T1 : measurableType d1} {T2 : measurableType d2} {T3 : measurableType d3}
    (f : measurable_map T2 T3) (g : measurable_map T1 T2) : measurable_map T1 T3
    := Mcmp_def f g.

  (* TODO: Mcmp_aux / seal *)

  (** ********** ?. Constant is measurable_map *)
  Section MeasurableMap_const.
    Context {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}.

    Lemma Mcst_def_measurable (t : T2):
      @measurable_fun _ _ T1 T2 setT (cst t).
    Proof. Admitted.

    HB.instance Definition _ (t : T2) :=
      isMeasurableMap.Build _ _ T1 T2 (cst t) (Mcst_def_measurable t).
  End MeasurableMap_const.

  (*
  (** ********** ?. Id is measurable_map *)
  Section MeasurableMap_id.
    Context {d1} {T1 : measurableType d1}.

    Lemma Mid_def_measurable :
      @measurable_fun _ _ T1 T1 setT (id : T1 -> T1).
    Proof. Admitted.

    HB.instance Definition _ :=
      isMeasurableMap.Build _ _ T1 T1 (@id T1 ) Mid_def_measurable.
  End MeasurableMap_const.
   *)


  (** ********** 8. Monad bind *)

(*
  Definition giryM_bind {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}
                        (f : measurable_map T1 (giryM T2)) (m : giryM T1) : giryM T2
    := giryM_join (giryM_map f m).
*)

  Definition giryM_bind {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}
                        (f : measurable_map T1 (giryM T2)) : measurable_map (giryM T1) (giryM T2)
    := Mcmp giryM_join (giryM_map f).

  (* No need to prove measurability! *)


  Section giryM_bind_laws.
    (* TODO: Port laws from prob here *)
    Context {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}.
    Context {f : measurable_map T1 (giryM T2)}.


    (* TODO: Port these equations *)
    Lemma giryM_bind_0_l : giryM_bind f mzero = mzero.
    Proof. Admitted.

    (* FIXME: make it so that I don't have to annotate giryM T2 here? *)
    Lemma giryM_bind_0_r (μ : giryM T1) : giryM_bind (cst (mzero : giryM T2)) μ = mzero.
    Proof. Admitted.

    (* Check (giryM_bind f). *)
    Lemma giryM_bind_measurable : measurable_fun setT (giryM_bind f).
    Proof. Admitted.

    Lemma giryM_bind_eval (m : giryM T1) (s : set T2) (HS : measurable s) :
      (giryM_bind f m s = \int[m]_x f x s)%E.
    Proof. Admitted.

    Lemma giryM_bind_integrate (m : giryM T1) (g : T2 -> \bar R) (mg : measurable_fun setT g) :
      (\int[giryM_bind f m]_x g x = \int[m]_a (\int[f a]_x g x))%E.
    Proof. Admitted.

    (* This is a mess ... put it into a fresh namespace? *)
    Lemma giryM_bind_bind {d3} {T3 : measurableType d3} (g : T2 -> giryM T3) (mg : measurable_fun setT g) (m : giryM T1) : True.
    Proof. Admitted.

    Lemma giryM_bind_ret_l t : giryM_bind f (giryM_ret t) = f t.
    Proof. Admitted.

    Lemma giryM_bind_ret_r (m : giryM T1) : giryM_bind giryM_ret m = m.
    Proof. Admitted.

  End giryM_bind_laws.

End giry.

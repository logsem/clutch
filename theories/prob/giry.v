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
    Proof using d. by rewrite /mzero/=. Qed.

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
    Proof using d. simpl. apply measurable0. Qed.

    Example test_giry_measures_T : T.-giry.-measurable [set: giryM T].
    Proof using d. rewrite /=. apply (@measurableT _ (salgebraType _)). Qed.

    (* giryM is also a measurable type, so can be nested. *)
    Example test_giry_measures_0' : (giryM T).-giry.-measurable (set0 : set (giryM (giryM T))).
    Proof using d. simpl. apply measurable0. Qed.

  End giry_space_example.




  (** ********** 3. Test: Examples of integration *)

  Section giry_integral_example.
    Context {d : measure_display} (T : measurableType d).

    Variable (μ_target : giryM T).  (* Some point in the space of measures on T*)

    (* The dirac measure using that point *)
    Example giry_ret_μ : giryM (giryM T) := @dirac _ _ μ_target _.

    Example int_zero_over_dirac : (\int[giry_ret_μ]_x cst 0%:E x)%E = 0%:E.
    Proof using d. apply integral0. Qed.

    Example int_one_over_dirac : (\int[giry_ret_μ]_x cst 1%:E x)%E = 1%:E.
    Proof using d.
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
    Proof.
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
  Proof using R. done. Qed.




  (** ********** 6. Measurability of (T₁ -> giryM T₂) functions *)

  (* FIXME: move *)
  Definition measurable_evaluations {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2} (f : T1 -> giryM T2) : Prop
    := forall (S : set T2), d2.-measurable S -> (@measurable_fun _ _ _ borelER setT (f ^~ S)).



  Section giry_measurable_characterization.
    Context {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}.
    Variable (f : T1 -> giryM T2).

    Check (f ^~ _ : T1 -> borelER).

    Lemma measurable_evals_if_measurable : measurable_fun setT f -> measurable_evaluations f.
    Proof.
      intros Hm.
      rewrite /measurable_evaluations.
      intros S HS.
      replace (fun x : T1 => f x S) with ((@^~ S) \o f); last by apply functional_extensionality.

      apply (@measurable_comp _ _ _ _ _ _ setT (@^~ S : giryM T2 -> borelER)); auto.
      { apply subsetT. }
      apply (@giryM_eval_def_measurable _ _ _ HS).
    Qed.

    Lemma measurable_if_measurable_evals : measurable_evaluations f -> measurable_fun setT f.
    Proof. Admitted.

    Lemma measurable_evals_iff_measurable : measurable_evaluations f <-> measurable_fun setT f.
    Proof. split; [apply measurable_if_measurable_evals | apply measurable_evals_if_measurable]. Qed.

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
    Proof.
      (* rewrite /measurable_fun. intros H Y HY. *)
      (* The preimage is the set [s | giryM_ret s ∈ Y] *)
      (* In principle this could be any subset of T, somehow the measurability of
         Y has to eliminate this possibility. *)


      (* Enough to work in a subbasis *)
      apply (@measurability _ _ _ _ _ giryM_ret_def (@giry_subbase _ T)); first by simpl.
      rewrite /subset; intros X HX.
      rewrite /preimage_class/= in HX.
      rewrite /salgebraType in HX.
      destruct HX as [Z HZ <-].
      rewrite setTI.

      rewrite /giry_subbase/= in HZ.
      destruct HZ as [S [HS HSZ]].
      rewrite /preimage_class_of_measures/= in HSZ.

      (* Z is a set of subprobability distributions on T.
         S is a set of T
         S is measurable in T.
         Z is measurable in (giryM T).

        giry_subbase Z tells me very little about Z
         measurable_measure (mathlib) characterizes measurable functions into the monad by their
         evaluations. So unfolding down one more layer is (probably) necessary using this line.

        Consequence: Probaby best to try applying the lemma you declared and then immediately forgot about.

       *)
      simpl in *.
      rewrite /preimage_class/= in HSZ.
      destruct HSZ as [SR HSBorel <-].
      rewrite setTI.

      (* SR is a borel set in (\bar R).
         ( ... ^~ S @^-1` SR) is the set of all subprobabilility measures which evaluate S to something in SR
         (giryM_ret_def @^-1 ... SR ) is the set of all elements of T whose dirac measure
            evaluates S to something in SR.

          For any (t : T), t ∈ S <-> dirac t S = 1
          (0 ∈ SR) / (t ∈ S) :        Says nothing
          (0 ∈ SR) / (t not ∈ S) :    t ∈ (... @^-1 ...)
          (1 ∈ SR) / (t ∈ S) :        t ∈ (... @^-1 ...)
          (1 ∈ SR) / (t not ∈ S) :    Says nothing

          Neither -> t not∈ (... @^-1 ...).

          Can I peel back one level of unfolding and eliminate the explicit R borel set reasoning?
            (see above for answer)
       *)


      rewrite /ereal_borel_sets/= in HSBorel.

      (* Check sigma_algebra_preimage_classE. *)
      simpl.
      rewrite /measurable/=.
    Restart.
      (* Attempt 2 *)

      apply measurable_evals_iff_measurable.
      rewrite /measurable_evaluations.
      intros S SMeas.
      (* Now we're proving a T → \bar R function is measurable... better. *)
      (* This should be easy to characterize since S is measurable. Just depends on
         if 0 or 1 is in the real set. *)

      rewrite /measurable_fun/= .
      intros ? Y HY.
      (* NOTE: Since its using 'measurable, it seems that Borel or Lebesgue doesn't matter here. (assuming qed)*)
      remember (fun x : T => (\d_x)%R S) as f.
      rewrite <- (preimage_range f).
      rewrite -preimage_setI.

      (* Probably silly to work in this order *)
      replace (range f) with ([set 0%:E; 1%:E] : set \bar R) by admit.
      (* Split it into (f @^-1 ({1} & Y)) U (f^-1 ({0} & Y))
          Then I can simplify each thing easier (maybe). *)
      rewrite setIUl.
      rewrite preimage_setU.
      do 2 rewrite set1I.

      (* Now we're looking decent. Figure out how to use LEM and complete. *)
    Admitted.

    HB.instance Definition _ :=
      isMeasurableMap.Build _ _ T (giryM T) giryM_ret_def giry_ret_measurable.

  End giry_ret.

  (* FIXME: This is the interface that should be used *)
  Definition giryM_ret {d} {T : measurableType d} : measurable_map T (giryM T) := giryM_ret_def.
  Lemma giryM_ret_aux {d} {T : measurableType d} (t : T) : giryM_ret t = dirac t.
  Proof using R. auto. Qed.

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

    (* Taking expectaiton is measurable *)
    Lemma giry_meas_integrate f : @measurable_fun _ _ (giryM T) (\bar R) setT (giryM_integrate_def f).
    Proof. Admitted.

    HB.instance Definition _ (f : measurable_map T (\bar R)) :=
      isMeasurableMap.Build _ _ (giryM T) (\bar R) (giryM_integrate_def f) (giry_meas_integrate f).

  End giryM_integrate_laws.


  (* FIXME: Seal above definitions *)
  Definition giryM_integrate {d} {T : measurableType d} (f : measurable_map T (\bar R)) : measurable_map (giryM T) (\bar R)
    := (giryM_integrate_def f).
  Lemma giryM_integrate_aux {d} {T : measurableType d} (f : measurable_map T (\bar R)) :
    forall μ, (giryM_integrate f μ = \int[μ]_x (f x))%E.
  Proof using R. done. Qed.






  (** ********** 7. Monad map  *)

  Section giryM_map_definition.
    Context {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2}.

    Lemma pushforward_setT (f : measurable_map T1 T2) (m : giryM T1) : (pushforward m (@measurable_mapP _ _ _ _ f) setT <= 1)%E.
    Proof. (* Does this need any additional assumptions? *) Admitted.

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
  Proof using R. done. Qed.


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
      Proof. Admitted.

      Definition giryM_join_ge0 A : (0 <= giryM_join_def m A)%E.
      Proof. Admitted.

      Definition giryM_join_semi_additive : semi_sigma_additive (giryM_join_def m).
      Proof. Admitted.

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
  Proof using R. done. Qed.



  Section giryM_join_laws.
    (* TODO: Port laws from prob here *)
    Context {d} {T : measurableType d}.

    Lemma giryM_join_zero : giryM_join mzero = (mzero : giryM T).
    Proof. Admitted.

    (* FIXME: measurable_fun usage *)
    Lemma giryM_join_integrate (m : giryM (giryM T)) (f : T -> \bar R) (mf : measurable_fun setT f) :
      (\int[giryM_join m]_x (f x) = \int[m]_μ (\int[μ]_x f x))%E.
    Proof. Admitted.


    (* join_map_map *)
    (* join_map_join *)
    (* join_map_dirac *)
    (* join_dirac *)

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
    Context {f : T1 -> giryM T2} (mf : measurable_fun setT f).


    (* FIXME: Make a measurable_map instance for mzero and cst *)
    (*
    Lemma giryM_bind_0_l : giryM_bind mzero mf = mzero.
    Proof. Admitted.

    (* FIXME: make it so that I don't have to annotate giryM T2 here? *)
    Lemma giryM_bind_0_r (μ : giryM T1) : giryM_bind μ (measurable_cst (mzero : giryM T2)) = mzero.
    Proof. Admitted.

    Lemma giryM_bind_measurable : measurable_fun setT (giryM_bind^~ mf).
    Proof. Admitted.

    Lemma giryM_bind_eval (m : giryM T1) (s : set T2) (HS : measurable s) :
      (giryM_bind m mf s = \int[m]_x f x s)%E.
    Proof. Admitted.

    Lemma giryM_bind_integrate (m : giryM T1) (g : T2 -> \bar R) (mg : measurable_fun setT g) :
      (\int[giryM_bind m mf]_x g x = \int[m]_a (\int[f a]_x g x))%E.
    Proof. Admitted.


    (* This is a mess ... put it into a fresh namespace *)
    Lemma giryM_bind_bind {d3} {T3 : measurableType d3} (g : T2 -> giryM T3) (mg : measurable_fun setT g) (m : giryM T1) : True.
    Proof. Admitted.

    Lemma giryM_bind_ret_l t : giryM_bind (giryM_ret t) mf = f t.
    Proof. Admitted.


    Lemma giryM_bind_ret_r (m : giryM T1) : giryM_bind m (giry_ret_measurable : measurable_fun _ _) = m.
    Proof. Admitted.


     *)

    (* Other monad laws? *)

    (* join_eq_bind *)

  End giryM_bind_laws.

End giry.

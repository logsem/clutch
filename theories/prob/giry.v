(** Measures and probabilitiy from mathcomp-analysis *)

From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp.analysis Require Import ereal reals lebesgue_measure measure lebesgue_integral.
From HB Require Import structures.

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

*)


Reserved Notation "T .-giry" (at level 1, format "T .-giry").
Reserved Notation "T .-giry.-measurable"
 (at level 2, format "T .-giry.-measurable").

Section giry.
  Context (R : realType).
  Local Open Scope classical_set_scope.

  (* FIXME: Are these the same? Or is 'measurable derived from the Lebesgue measure? Would that be an issue? *)
  (* 'measurable breaks when I remove the import to lebesgue_measure *)
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
        ereal_meas_sets           (* Range sets*).

    Definition giry_subbase : set (set (giryType T))
      := [set C | exists (S : set T) (_ : measurable S), preimage_class_of_measures S C].

    Definition giry_measurable : set (set (giryType T)) := <<s giry_subbase>>.

  End giry_space.





  Definition giryM_display {d} {T} := sigma_display (@giry_subbase d T).

  Definition giryM {d} (T : measurableType d) : measurableType giryM_display
    := salgebraType (@giry_subbase _ T).

  Notation "T .-giry" := (@giryM_display _ T) : measure_display_scope.
  Notation "T .-giry.-measurable" := (measurable : set (set (giryM T))) : classical_set_scope.




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




  (** ********** 4. Monad return  *)

  Definition giryM_ret {d} {T : measurableType d} : T -> giryM T
    := fun t0 => @dirac _ T t0 _.

  Section giry_ret_laws.
    (* TODO: Port laws from prob here *)
    Context {d} {T : measurableType d}.

    (* Return is a measurable function *)
    Lemma giry_ret_measurable : @measurable_fun _ _ T (giryM T) setT giryM_ret.
    Proof. Admitted.

  End giry_ret_laws.





  (** ********** 5. Measurability of (T₁ -> giryM T₂) functions *)

  Definition giryM_Peval {d} {T : measurableType d} : set T -> giryM T -> \bar R
    := fun s => (fun μ => μ s).

  (* Evaluation functions are measurable *)
  Lemma giryM_Peval_measurable {d} {T : measurableType d} (S : set T) :
    d.-measurable S -> @measurable_fun _ _ (giryM T) (\bar R) setT (giryM_Peval S).
  Proof.
    intro Hmeas_s.
    rewrite /measurable_fun /=.
    intros Hmeas_T U Hmeas_U.
  Admitted.

  Section giry_measurable_characterization.
    Context {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}.
    Variable (f : T1 -> giryM T2).

    Lemma measurable_evals_imply_measurable :
      (forall S : set T2, d2.-measurable S -> @measurable_fun _ _ T1 (\bar R) setT (fun μ => (f μ) S)).
    Proof. Admitted.

    Lemma giry_measurable_fun_char :
      (forall S : set T2, d2.-measurable S <-> @measurable_fun _ _ T1 (\bar R) setT (fun μ => (f μ) S)).
    Proof. Admitted.

  End giry_measurable_characterization.





  (** ********** 6. Expectations over the Giry Monad *)

  Definition giryM_integrate {d} {T : measurableType d} (f : T -> \bar R) (_ : measurable_fun setT f)
      : giryM T -> \bar R
    := fun μ => (\int[μ]_x (f x))%E.

  Section giryM_integrate_laws.
    (* TODO: Port laws from prob here *)
    Context {d} {T : measurableType d} (f : T -> \bar R) (Hf : measurable_fun setT f).

    (* Taking expectaiton is measurable *)
    Lemma giry_meas_integrate : @measurable_fun _ _ (giryM T) _ setT (giryM_integrate Hf).
    Proof. Admitted.

  End giryM_integrate_laws.





  (** ********** 7. Monad map  *)

  Section giryM_map_definition.
    Context {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2}.
    Variables (f : T1 -> T2) (m : giryM T1) (mf : measurable_fun setT f).


    Lemma pushforward_setT : (pushforward m mf setT <= 1)%E.
    Proof. (* Does this need any additional assumptions? *) Admitted.

    HB.instance Definition _ := Measure_isSubProbability.Build _ _ _ (pushforward m mf) pushforward_setT.

    Definition giryM_map : giryM T2 := pushforward m mf.

  End giryM_map_definition.

  Section giry_map_laws.
    (* TODO: Port laws from prob here *)
    Context {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}.
  End giry_map_laws.





  (** ********** 8. Monad join *)

  Definition giryM_join {d} {T : measurableType d} (m : giryM (giryM T)) : (set T -> \bar R)
    := (fun S => \int[m]_μ (μ S))%E.

  Section giryM_join_definition.

    (* For the proofs,
        I don't know if there's any way to reuse the measurability of evaluation functions to do this. *)
    Context {d} {T : measurableType d}.
    Variables (m : giryM (giryM T)).

    Definition giryM_join0 : giryM_join m set0 = 0%E.
    Proof. Admitted.

    Definition giryM_join_ge0 A : (0 <= giryM_join m A)%E.
    Proof. Admitted.

    Definition giryM_join_semi_additive : semi_sigma_additive (giryM_join m).
    Proof. Admitted.

    HB.instance Definition _
      := isMeasure.Build _ _ _
           (giryM_join m)
           giryM_join0
           giryM_join_ge0
           giryM_join_semi_additive.

    Lemma giryM_join_setT : (giryM_join m setT <= 1)%E.
    Proof. (* Does this need any additional assumptions? *) Admitted.

    HB.instance Definition _ := Measure_isSubProbability.Build _ _ _ (giryM_join m) giryM_join_setT.

  End giryM_join_definition.

  Section giryM_join_laws.
    (* TODO: Port laws from prob here *)
    Context {d} {T : measurableType d}.
  End giryM_join_laws.





  (** ********** 8. Monad bind *)

  Definition giryM_bind {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}
                       (f : T1 -> giryM T2) (m : giryM T1) (mf : measurable_fun setT f) : giryM T2
    := giryM_join (giryM_map m mf).

  Section giryM_bind_laws.
    (* TODO: Port laws from prob here *)
    Context {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}.
  End giryM_bind_laws.

End giry.

(** Definition of the Giry Monad type (a sigma algebra for subdistributions) *)

#[warning="-notation-incompatible-prefix"] From mathcomp Require Import all_boot all_algebra finmap.
#[warning="-notation-incompatible-prefix"] From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
From mathcomp.reals Require Import reals signed.
From mathcomp.analysis Require Import ereal normedtype esum numfun measure lebesgue_measure lebesgue_integral.
From HB Require Import structures.

From Stdlib.Logic Require Import FunctionalExtensionality.
From Stdlib.Relations Require Import Relation_Definitions.
From Stdlib.Classes Require Import RelationClasses.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Default Proof Using "Type".

(**   Summary

      Types for measurable functions
        measurable_map T1 T2    Type of measurable functions from T1 to T2

      Types of the Giry Monad
        giryType T              Type of points in the giry sigma algebra on T, namely, subdistributions on T
        giryM T                 measurableType of (giryType T)
        T.-giry                 Display for the giry sigma algebra on T
        T.-giry.-measurable     Measurability in the giry sigma algebra on T

      Discrete Spaces
        <<discr T>>             measurableType for discrete space on T

 *)

(*
Reserved Notation "T .-giry" (at level 1, format "T .-giry").
Reserved Notation "T .-giry.-measurable"
 (at level 2, format "T .-giry.-measurable").
*)


(** ********** Measurable Functions ********** **)
(* Adding measurable functions to the hierarchy allows us to avoid
   excessive proofs of measurability. *)
HB.mixin Record isMeasurableMap d1 d2 (T1 : measurableType d1) (T2 : measurableType d2)
  (f : T1 -> T2) := {
  measurable_mapP : measurable_fun setT f
}.


(** Use the type (measurableMap T1 T2) for any measurable map *)
#[short(type=measurable_map)]
HB.structure Definition MeasurableMap {d1} {d2} T1 T2 :=
  {f of @isMeasurableMap d1 d2 T1 T2 f}.


(* FIXME: Builder for measurableFun to RealType? Or does this go automatically?  *)


Section measurability_lemmas.
  Context {d1} {T1 : measurableType d1}.
  Context {d2} {T2 : measurableType d2}.

  Local Open Scope classical_set_scope.

  (* Weak extensionality: The functions are equal pointwise *)
  Lemma measurable_map_ext (m1 m2 : measurable_map T1 T2) (H : forall t : T1, m1 t = m2 t) : m1 = m2.
  Proof.
    apply functional_extensionality in H.
    (* move: m1 m2 H => [x [[y] [+ [[+]]] +]]. *)
    move: m1 m2 H => [x [[+]]] [y [[+]]] /= Hxy.
    intros w v.
  Admitted.

  (* Lemma measurability_image : forall S1 : set T1, forall S2 : set T2,
    d1.-measurable S1 -> d2.-measurable S2 ->  *)

End measurability_lemmas.

(*
(** ********** Borel space on extended Reals ********** **)
Section ereal_borel.
  Context `{R : realType}.

  (* Standard Borel space on the extended reals *)
  Definition ereal_borel_subbase : set (set \bar R) := [set N | exists x, ereal_nbhs x N].
  Definition ereal_borel_sets : set (set \bar R) := <<s ereal_borel_subbase>>.

  (** Use the type borelER for the Borel space of extended Reals *)
  Definition borelER_display := sigma_display ereal_borel_subbase.
  Definition borelER : measurableType borelER_display
    := [the measurableType _ of salgebraType ereal_borel_subbase].
End ereal_borel.
*)




(** ********** Giry Monad ********** **)

Section giry_space.
  (** Define a measurable space over (giryType T) *)
  Context `{R : realType} `{d : measure_display} (T : measurableType d).
  Local Open Scope classical_set_scope.

  (* Type of points in the Giry monad *)
  Definition giryType {d} T : Type := @subprobability d T R.

  HB.instance Definition _ := gen_eqMixin (giryType T).
  HB.instance Definition _ := gen_choiceMixin (giryType T).

  Lemma mzero_setT : (@mzero d T R setT <= 1)%E.
  Proof. by rewrite /mzero/=. Qed.

  HB.instance Definition _ := Measure_isSubProbability.Build _ _ _ (@mzero d T R) mzero_setT.

  HB.instance Definition _ := isPointed.Build (giryType T) mzero.

  Definition preimage_class_of_measures (S : set T) : set (set (giryType T)) :=
    @preimage_class (giryType T)
      (\bar R)                  (* Range type *)
      setT                      (* Domain set *)
      (fun μ => μ S)              (* Evaluation function *)
      'measurable               (* Range sets *).

  Definition giry_subbase : set (set (giryType T))
    := [set C | exists (S : set T) (_ : measurable S), preimage_class_of_measures S C].

  Definition giry_measurable : set (set (giryType T)) := <<s giry_subbase>>.
End giry_space.

Definition giryM_display `{R : realType} `{d : measure_display} `{T : measurableType d} :=
  sigma_display (@giry_subbase R d T).
Global Arguments giryM_display {_} {_} {_}.

(** Use giryM for any Giry Monad type *)
Definition giryM (R : realType) (d : measure_display) (T : measurableType d) : measurableType giryM_display :=
  [the measurableType _ of salgebraType (@giry_subbase R d T)].
Global Arguments giryM {_} {_} _.


(** Relation defeining measure equality *)
(* Local Open Scope classical_set_scope. *)

Definition measure_eq `{R : realType} `{d : measure_display} {T : measurableType d} : relation (@giryM R d T) :=
  fun μ1 μ2 => forall (S : set T), measurable S -> μ1 S = μ2 S.
Notation "x ≡μ y" := (measure_eq x y) (at level 70).
Global Hint Extern 0 (_ ≡μ _) => reflexivity : core.
Global Hint Extern 0 (_ ≡μ _) => symmetry; assumption : core.

Instance equivalence_measure_eq `{R : realType} `{d : measure_display} {T : measurableType d} :
  Equivalence (@measure_eq R d T).
Proof.
  constructor.
  - done.
  - rewrite /Symmetric.
    intros ? ? H ? ?.
    by rewrite H //=.
  - intros ? ? ? H0 H1 ? ?.
    by rewrite H0 //= H1 //=.
Qed.



Section giry_lemmas.
  Context `{R : realType} `{d : measure_display} {T : measurableType d}.
  Notation giryM := (giryM (R := R)).

  Local Open Scope classical_set_scope.

  Lemma giryM_ext (μ1 μ2 : giryM T) (H : forall S : set T, μ1 S = μ2 S) : μ1 = μ2.
  Proof.
    apply functional_extensionality in H.
    move: H.
    move: μ1 μ2 => [x [[x1] x2 [x3] [x4] [x5 [x6]] [x7]]] [y [[+] + [+] [+] [+ [+]] [+]]] /= xy.
    rewrite -{}xy => y1 y2 y3 y4 y5 y6 y7.
    f_equal.
    by rewrite
      (_ : x1 = y1)//
      (_ : x2 = y2)//
      (_ : x3 = y3)//
      (_ : x4 = y4)//
      (_ : x5 = y5)//
      (_ : x6 = y6)//
      (_ : x7 = y7)//.
  Qed.


  Lemma base_eval_measurable {d1} {T1 : measurableType d1} (S : set T1) (HS : measurable S):
    measurable_fun [set: giryM T1] ((SubProbability.sort (R:=R))^~ S).
  Proof.
    (* Breaks w/ new mathcomp-analysis *)
  Admitted.
  (*
    eapply (@measurability _ _ _ _ _ _ 'measurable).
    { rewrite /measurable/=.
      symmetry.
      rewrite smallest_id.
      - done.
      - constructor.
        - by apply emeasurable0.
        - intros ??.
          rewrite setTD.
          by apply emeasurableC.
        - by apply bigcupT_emeasurable.
    }
    rewrite /measurable/=.
    rewrite {2}/giry_subbase/=.
    apply  (@subset_trans _ (giry_subbase (T:=T1))); last by apply sub_gen_smallest.
    rewrite /subset/=.
    intros X.
    rewrite /preimage_class/=.
    intros [Y HY <-].
    rewrite {1}/giry_subbase/=.
    exists S, HS.
    rewrite /preimage_class_of_measures/preimage_class/=.
    exists Y.
    - done.
    - by rewrite setTI.
  Qed.
   *)

End giry_lemmas.



(* Notation is useless without inference for R

Section giryNotation.
  Notation "T .-giry" := (@giryM_display _ T) : measure_display_scope.
  Notation "T .-giry.-measurable" := ((@measurable _ (giryM T)) : set (set (giryM T))) : classical_set_scope.
End giryNotation.
*)


Reserved Notation "'<<discr' G '>>'"
  (at level 2, format "'<<discr'  G  '>>'").


Section discrete_space.
  Local Open Scope classical_set_scope.

  (* Type of points in a discrete space *)
  Definition discrType (T : Type) : Type := T.

  Section discr_salgebra_instance.
    Variables (T: pointedType).
    Definition inhab : discrType T := (@point T).

    Definition discr_meas : set (set (discrType T)) := [set: set (discrType T)].

    Lemma discr_meas0 : discr_meas set0.
    Proof. by []. Qed.

    Lemma discr_measC X : discr_meas X -> discr_meas (~` X).
    Proof. by []. Qed.

    Lemma discr_measU (F : sequences.sequence (set T)) : (forall i, discr_meas (F i)) -> discr_meas (\bigcup_i F i).
    Proof. by []. Qed.

    HB.instance Definition _ := gen_eqMixin (discrType T).
    HB.instance Definition _ := gen_choiceMixin (discrType T).
    HB.instance Definition _ := isPointed.Build (discrType T) inhab.
    HB.instance Definition _:= @isMeasurable.Build default_measure_display (discrType T) discr_meas
                                 discr_meas0 discr_measC discr_measU.
  End discr_salgebra_instance.

End discrete_space.

Notation "'<<discr' G '>>'" := (discrType G) : classical_set_scope.

Section fin_pointed.
  Local Open Scope ereal_scope.
  Local Open Scope classical_set_scope.
  Context {R : realType}.
  Variable (m : nat).

  (* The finite type of > 0 elements is pointed *)
  Program Definition Ism_inhabitant : 'I_(S m). eapply (@Ordinal _), leqnn. Defined.

  HB.instance Definition _ := gen_eqMixin ('I_m).
  HB.instance Definition _ := gen_choiceMixin ('I_m).
  HB.instance Definition _ N := isPointed.Build ('I_(S m)) Ism_inhabitant.
End fin_pointed.

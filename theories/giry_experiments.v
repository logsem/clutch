(** Measures and probabilitiy from mathcomp-analysis *)

Require Import Rdefinitions Raxioms RIneq Rbasic_fun Zwf.
Require Import Epsilon FunctionalExtensionality Ranalysis1 Rsqrt_def.
Require Import Rtrigo1 Reals.
From mathcomp Require Import all_ssreflect ssralg poly mxpoly ssrnum.
From mathcomp Require Import all_ssreflect ssralg ssrnum matrix interval.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import all_ssreflect ssralg ssrnum finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop .
From mathcomp Require Import all_ssreflect all_algebra finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import fsbigop cardinality set_interval.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg poly ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality.
From mathcomp Require Import boolp classical_sets functions.
From HB Require Import structures.

From mathcomp.analysis Require Import constructive_ereal ereal reals landau Rstruct topology function_spaces cantor.
From mathcomp.analysis Require Import prodnormedzmodule normedtype realfun sequences exp trigo nsatz_realtype esum.
From mathcomp.analysis Require Import real_interval lebesgue_measure lebesgue_stieltjes_measure forms derive measure numfun lebesgue_integral.
From mathcomp.analysis Require Import ftc hoelder probability summability signed itv convex charge kernel.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.






(** Johanes Hotzel already tried to define the Giry monad, though therey's no too much there *)

Section stolen_giry_monad_attempt.

(* Stolen https://github.com/math-comp/analysis/pull/1177/commits/32261c68d93041da910fd2fe2afd810c7a783ff8 *)
Context d (T : measurableType d) {R : realType} (y : T). (* y is unused... *)
Definition ret (x : T) (A : set T) := @dirac d T x R A.
Definition bind (mu : probability T R) (f : T -> probability T R) :=
  fun (A : set T) => (\int[mu]_x f x A)%E.

Lemma bindT mu f : bind mu f setT = 1%E.
Proof.
rewrite /bind.
under eq_integral => x _ do rewrite probability_setT.
Admitted.

Fail HB.instance Definition _ mu f :=
  Measure_isProbability.Build _ _ _ (bind mu f) (bindT mu f).

Lemma giry_left_id (mu : probability T R) (f : T -> probability T R) (x : T) : bind (ret x) f = f x.
Proof.
rewrite /bind/ret/=.
Admitted.
Lemma giry_right_id (mu : probability T R) A: bind mu (fun x => ret x) A = mu A.
Proof.
rewrite /bind/ret/=.
Admitted.
(* Lemma giry_assoc (mu : probability T R) f g A : bind (bind mu f) g = bind mu (fun x => bind (f x) g).
Admitted. *)

End stolen_giry_monad_attempt.










(** My Giry attempt *)

Section giry.
  Context d (T : measurableType d) (R : realType).
  Local Open Scope classical_set_scope.

  (* Generic definitions for the type of measures on T *)

  Definition giry_display : measure_display.
  Proof using d. exact. Qed.

  Definition giryType := @measure d T R.

  #[log]
  HB.instance Definition _ := gen_eqMixin giryType.
  #[log]
  HB.instance Definition _ := gen_choiceMixin giryType.
  #[log]
  HB.instance Definition _ := isPointed.Build giryType mzero.

  Definition ereal_borel_sets : set (set \bar R) := <<s [set N | exists x, ereal_nbhs x N]>>.

  (* Definition borel_sigma_algebra : sigma_algebra [set: \bar R] ereal_borel_sets
    := smallest_sigma_algebra [set: \bar R] ereal_borel_subbase. *)

  (* Err... there is already a measurable type?
     This is a function (set (set R)) -> (set (set \bar R)), use this to lift? Are we already using it to lift?
     Check emeasurable.
   *)

  Definition preimage_class_of_measures (S : set T) : set (set giryType) :=
          @preimage_class
            giryType
            (\bar R)                  (* Range type *)
            setT                      (* Domain set *)
            (fun 𝜇 => 𝜇 S)              (* Evaluation function *)
            ereal_borel_sets          (* Range sets*).

  Definition giry_subbase : set (set giryType)
    := [set C | exists (S : set T) (_ : measurable S), preimage_class_of_measures S C].

  Definition giry_measurable : set (set giryType) := <<s giry_subbase>>.

  #[log]
  HB.instance Definition _ := Pointed.on (salgebraType giry_subbase).


  Check (salgebraType giry_subbase).      (* Type of generated sigma algebra? *)
  Check (sigma_display giry_subbase).     (* Display of generated sigma algebra? *)
  Check (salgebraType giry_subbase : measurableType (sigma_display giry_subbase)).
  (* The salgebraType is measurable (finally)*)

  Check (measurable : set (set (salgebraType giry_subbase))) .
  Check (giry_subbase.-sigma.-measurable set0).

  Example test_meas_0 : (giry_subbase.-sigma.-measurable set0).
  Proof using d.
    (* HB.about SemiRingOfSets. *)
    (* Unset Printing Notations. *)
    (* Locate measurable0. *)
    (* Works (this is a very good sign) *)
    (* apply isMeasurable.measurable0. *)
    apply measurable0.
  Qed.

  Example test_meas_top : (giry_subbase.-sigma.-measurable (setT : set giryType)).
  Proof using d. rewrite -setC0. apply measurableC, measurable0. Qed.


  (* Now let's put some measure on this space (something simple like Dirac of some fixed measure or something) *)


  Definition 𝜇_target : giryType. Admitted.

  Definition giry_ret_𝜇
    := @dirac
          (sigma_display giry_subbase)
          (salgebraType giry_subbase)
          (𝜇_target : giryType)
          R.
  Check giry_ret_𝜇.


  Example int_zero_over_dirac : (\int[giry_ret_𝜇]_x cst 0%:E x)%E = 0%:E.
  Proof using d. apply integral0. Qed.

  Example int_one_over_dirac : (\int[giry_ret_𝜇]_x cst 1%:E x)%E = 1%:E.
  Proof using d.
    rewrite integral_cst /=.
    - by rewrite diracT mul1e.
    - rewrite -setC0.
      apply (@measurableC _ (salgebraType giry_subbase)).
      apply measurable0.
  Qed.

End giry.















Section simple.
  (* Excercise: Formalize some simple constructions for measures, measurable functions. *)

  (* Formalize the trivial sigma algebra on a subspace of the set of all elements of a type *)

  Definition MyTrivAlgebraType {T} (Sp : set T) := T.

  Definition MyTrivDisplay {T} : (set T) -> measure_display.
  Proof. exact. Qed.

  Section MyTrivAlgebraInstance.
    Variables (T : pointedType) (Sp : set T).


    Fail HB.about MyTrivAlgebraType.
    Fail HB.about T.
    (* So this needs MyTrivAlgebraType to be a pointedType (makes sense) *)
    HB.instance Definition _ := Pointed.on (MyTrivAlgebraType Sp).
    HB.about MyTrivAlgebraType. (* Now it has choice, pointed, and equality *)

    Definition MyTrivAlgebraMeasurable : set (set T) := setU [set set0] [set Sp].

    Lemma MyTrivAlgebra0 : MyTrivAlgebraMeasurable set0.
    Proof. rewrite /MyTrivAlgebraMeasurable /=. by left. Qed.

    Lemma MyTrivAlgebraC : forall (A : set T),
      MyTrivAlgebraMeasurable A -> MyTrivAlgebraMeasurable (~` A)%classic.
    Proof.
      move=> A.
      case=>->.
      (* This is wrong! The compliments will take it over [set: T] not Sp.  *)
      (* I'm going to admit it for now, to see if this type is what the HierarchyBuilder
         wants. If so, I need to change the type, if not, I need to change the lemma. *)
    Admitted.

    Lemma MyTrivAlgebra_bigcup :
        forall F : sequence (set T),
        (forall i : nat, MyTrivAlgebraMeasurable (F i)) ->
        MyTrivAlgebraMeasurable (\bigcup_i F i)%classic.
    Proof.
      move=> F HF.
      Locate bigcup_measurable.
      (* Uhh... I should be able to do induction over this? How do they do it in mathcomp analysis *)
    Admitted.



    HB.about isMeasurable.Build.

    HB.instance Definition _ :=
      @isMeasurable.Build
        (MyTrivDisplay Sp)
        (MyTrivAlgebraType Sp)
        MyTrivAlgebraMeasurable
        MyTrivAlgebra0
        MyTrivAlgebraC
        MyTrivAlgebra_bigcup.

    (* Nice! *)


    HB.about isMeasurable.


  End MyTrivAlgebraInstance.




End simple.



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



  (* Ok now we can do some giry-specfic stuff. For one, every evaluation function should be measurable. *)

  Check measurable_fun.


  (* measurable functions (between measure spaces) are _not_ part of the hierarchy, but measurable
     functions to reals _are_. *)



  (*preimage_class_measurable_fun : measurability of funcitons generated by preimage classses *)

  (* Need measurability w/ extended bases (eg. meas. from <<G>> implies meas. from <<G U ..>>)*)

  (* This? *)
  Check measurability.

  (* Okay and the second issue is that I'm taking preimage classes not necessarily from the right place. *)

  HB.about isMeasurableFun.
  Check  measurable_funP.
  (* This seems to imply that there's a cannonical _measurable_ instance on RealTypes, which I would
     very much like to use when defining my Giry sigma algebra. In fact, it would be necessary to get
     measurable_fun isntance I could actually use for taking integrals. *)


  HB.about realType.

  Check  @measurable_funP.

  (* Err... a measure is a function to an extended real type. *)

  (* Eventually I'll want to integrate whatever functions I call measurable *)
  (* So I need to see if (measurable_fun Giry... R∞) is enough for that or if I need to extend
     their integration theory to include extended functions. *)


  (* So the issue is, I'm wondering if a function with range \bar R can be integrable.

      Are there any other situations this might have come up? Fubini's theorem perhaps?

      Aha! It does come up in Fubini. So somewhere in there is a way to take an integral of an extended function.
   *)

  (* Actually wait, am I being stupid? The integrals I wrote above had ranges in ereals, so it's definitely possible*)
  (* Why did coq think that those functions were integrable? Did it think that they were measurable? How so? To R or \bar R? *)


  (* For fubini, they take
     Variables (f : X * Y -> \bar R) (f0 : forall xy, 0 <= f xy).
     Hypothesis mf : measurable_fun setT f.

      In particular, the range of f and g are \bar R and they have this explicit measurable_fun hypothesis,
     they don't get measurablility from the Hierarchy

   *)

  (* The ``section integral`` has f, g : T -> \bar R

      ... and nothing else? what?

   *)

  (* Well I suppose that's not too bad *)


  (* See Rintegral to look for canonical definition of measure space on R *)

  (* See @integrable *)

  (* Okay interesting. So in measure theory "integrable" does mean that both the positive and negative
     parts of a function have finite integral. However, the integral in mathcomp-analysis doesn't seem to
     define it this way, and it leads me to think that they're making a choice of how to define \infty - \infty *)

  (* I wonder what the lean version does. By this definition, the evaluation map _shouldn't_ be integrable on
     all sets for all measures... so then wheat is it's integral? *)

  (* I guess since theyre all positive functions, it's fine to define the integral of a function which
      takes values at \infty to be \infty... so we can reuse this version of the integral only if
        \infty - \infty = \infty
    *)

  Compute (+oo - +oo)%E.

  (* Dammit *)

  (* Err... so is this an issue? If I take the integral of a measure, I should be able to prove that the
     negative part is always zero, right? *)


  (* AFTER LUNCH: try it. Plug a measure into the thing they use to restrict to negatives and see if you get 0 *)



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



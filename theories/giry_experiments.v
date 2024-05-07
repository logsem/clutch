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




Reserved Notation "T .-giry" (at level 1, format "T .-giry").
Reserved Notation "T .-giry.-measurable"
 (at level 2, format "G .-giry.-measurable").





(** modifiedfrom pushforward *)
(* After some reflection, this seems like it will be useless. I wanted to define the join by a pushforward
   of the "evaluation function", but unfortunately, the "evaluation function" is not a function (it is
   a set-function). *)
Section pullback.

  Local Open Scope classical_set_scope.

  Definition pullback d1 d2 (T1 : measurableType d1) (T2 : measurableType d2)
    (R : realFieldType) (m : set T2 -> \bar R) (f : T1 -> T2)
    of measurable_fun setT f := fun A => m (f @` A).
  Arguments pullback {d1 d2 T1 T2 R} m {f}.


  Section pullback_measure.
    Local Open Scope ereal_scope.
    Context d d' (T1 : measurableType d) (T2 : measurableType d') (R : realFieldType).


    Variables (m : measure T2 R) (f : T1 -> T2).
    Hypothesis mf : measurable_fun setT f.      (* If we can prove that ... is measurable, we should be able to pull
                                                   the measure on \bar R back to a measure on the Giry sigma algebra *)

    Let pullback0: pullback m mf set0 = 0.
    Proof. by rewrite /pullback image_set0 measure0. Defined.

    Let pullback_ge0 A : 0 <= pullback m mf A.
    Proof. apply: measure_ge0. Defined.

    Lemma pullback_sigma_additive : semi_sigma_additive (pullback m mf).
    Proof. Admitted.

    HB.instance Definition _ :=
      isMeasure.Build _ _ _
          (pullback m mf)
          pullback0
          pullback_ge0
          pullback_sigma_additive.

  End pullback_measure.
End pullback.




(** My Giry attempt *)

Section giry.
  Context (R : realType).
  Local Open Scope classical_set_scope.

  (*
      (giryType T)            Type of points in the giry sigma algebra on T, namely, measures on T
      (giryM T)               Measurable space on giryType (measures)
                                - An element of this type is a measure on T
      (T.-giry)               Display for the giry sigma algebra on T
      (T.-giry.-measurable)   Measurability in the giry sigma algebra on T
   *)


  (* FIXME: There has to be a standard version in the lirbaray, see below *)
  Definition ereal_borel_sets : set (set \bar R) := <<s [set N | exists x, ereal_nbhs x N]>>.


  (** Construction of the Giry sigma algebra *)

  Definition giry_display {d} {T : measurableType d} : measure_display.
  Proof using R. exact. Qed.

  (* Alias for underlying type we will build a giry sigma algebra on *)
  Definition giryType {d} (T : measurableType d) : Type := @measure d T R.

  (* Define the measurable sets of a giry sigma algebra *)
  Section giry_space.
    Variable (d : measure_display) (T : measurableType d).

    (* #[log] *)
    HB.instance Definition _ := gen_eqMixin (giryType T).
    (* #[log] *)
    HB.instance Definition _ := gen_choiceMixin (giryType T).
    (* #[log] *)
    HB.instance Definition _ := isPointed.Build (giryType T) mzero.

    Definition preimage_class_of_measures (S : set T) : set (set (giryType T)) :=
      @preimage_class (giryType T)
        (\bar R)                  (* Range type *)
        setT                      (* Domain set *)
        (fun 𝜇 => 𝜇 S)              (* Evaluation function *)
        ereal_borel_sets          (* Range sets*).

    Definition giry_subbase : set (set (giryType T))
      := [set C | exists (S : set T) (_ : measurable S), preimage_class_of_measures S C].

    Definition giry_measurable : set (set (giryType T)) := <<s giry_subbase>>.

    #[log]
    HB.instance Definition _ := Pointed.on (salgebraType giry_subbase).
  End giry_space.

  (* Measurable type for giryM aliases *)
  Definition giryM_display {d} {T} := sigma_display (@giry_subbase d T).
  Definition giryM {d} (T : measurableType d) : measurableType giryM_display
    := salgebraType (@giry_subbase _ T).

  Notation "T .-giry" := (@giryM_display _ T) : measure_display_scope.
  Notation "T .-giry.-measurable" :=
    (measurable : set (set (giryM T))) : classical_set_scope.


  Section giry_space_example.
    Context {d : measure_display} (T : measurableType d).

    (* Example: Measuring sets in the Giry space *)
    Example test_giry_measures_0 : T.-giry.-measurable (set0 : set (giryM T)).
    Proof using d. simpl. apply measurable0. Qed.

    Example test_giry_measures_T : T.-giry.-measurable [set: giryM T].
    Proof using d.
      simpl.
      Fail apply measurableT.
    Abort.

    (* giryM is also a measurable type, so can be nested. *)
    Example test_giry_measures_0' : (giryM T).-giry.-measurable (set0 : set (giryM (giryM T))).
    Proof using d. simpl. apply measurable0. Qed.

  End giry_space_example.


  (** Basic examples *)

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
        apply measurable0.
    Qed.

  End giry_integral_example.




  (** Monadic return *)
  Definition giryM_ret {d} {T : measurableType d} : T -> giryM T
    := fun t0 => @dirac _ T t0 _.

  Section giry_ret_laws.
    (* TODO: Port laws from prob here *)
    Context {d} {T : measurableType d}.

    Lemma giry_ret_measurable : @measurable_fun _ _ T (giryM T) setT giryM_ret.
    Proof. Admitted.


  End giry_ret_laws.



  (** Characterizing measurable functions in terms of evaluation functions *)

  Definition giryM_Peval {d} {T : measurableType d} : set T -> giryM T -> \bar R
    := fun s => (fun μ => μ s).

  (* Evaluation functions are measurable *)
  Lemma giryM_Peval_measurable {d} {T : measurableType d} (S : set T) :
    d.-measurable S -> @measurable_fun _ _ (giryM T) _ setT (giryM_Peval S).
  (*                                                 ^
                                                    What is this field?? *)
  Proof.
    intro Hmeas_s.
    rewrite /measurable_fun /=.
    intros Hmeas_T U Hmeas_U.
    (* What is 'measurable???'*)
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


  (** Expectations in the Giry monad *)

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





  (** Mapping in the Giry monad *)

  Definition giryM_map {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}
                       (f : T1 -> T2) (m : giryM T1) (mf : measurable_fun setT f) : giryM T2
    := pushforward m mf.


  Section giry_map_laws.
    (* TODO: Port laws from prob here *)
    Context {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}.
  End giry_map_laws.



  (** Monadic join *)

  Definition giryM_join {d} {T : measurableType d} (m : giryM (giryM T)) : (set T -> \bar R)
    := (fun S => \int[m]_μ (μ S))%E.

  Section giryM_join_measure.

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

  End giryM_join_measure.



  Section giryM_join_laws.
    (* TODO: Port laws from prob here *)
    Context {d} {T : measurableType d}.
  End giryM_join_laws.


  (** Monadic bind *)

  Definition girym_bind {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}
                       (f : T1 -> giryM T2) (m : giryM T1) (mf : measurable_fun setT f) : giryM T2
    := giryM_join (giryM_map m mf).

  Section giryM_bind_laws.
    (* TODO: Port laws from prob here *)
    Context {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}.
  End giryM_bind_laws.









  (** BELOW IS NOT CLEANED *)






  (** (Ignore) Trying to understand integrability *)

  (* See Rintegral to look for canonical definition of measure space on R? *)

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


  (* Todo: try it. Plug a measure into the thing they use to restrict to negatives and see if you get 0 *)
  (* See how integrability is used... if it's just for lemmas then that's probably OK. *)
  (* If this "negative is always zero" thing turns out, then we can use the "unsafe" integral w/ no consequence *)
  (* See which lemmas are used in the proof of Fubini *)

  HB.about measure.

  Check funeneg.

  (* Check forall (mu : measure T R), mu _ = _. *)
  (*
      Definition integral mu D f (g := f \_ D) :=
      nnintegral mu (g ^\+) - nnintegral mu (g ^\-).

    So I think the strategy is to prove lemmas about funeneg and the opposite, then show that
    we can use nnintegral instead of integral for measures

    This is the notion of measurability that we want? Actually wait... what are we doing again?
  *)

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



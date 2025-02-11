(** Definition of the Giry Monad type (a sigma algebra for subdistributions) *)

From mathcomp Require Import all_ssreflect all_algebra finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
From mathcomp.analysis Require Import reals ereal signed normedtype esum numfun measure lebesgue_measure lebesgue_integral.
From HB Require Import structures.

Import Coq.Logic.FunctionalExtensionality.
Import Coq.Relations.Relation_Definitions.
Import Coq.Classes.RelationClasses.

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


(*
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
*)


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


(*


(** ********** Giry Monad ********** **)

Section giry_space.
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

  (*
  Definition preimage_class_of_measures (S : set T) : set (set (giryType T)) :=
    @preimage_class (giryType T)
      (\bar R)                  (* Range type *)
      setT                      (* Domain set *)
      (fun μ => μ S)              (* Evaluation function *)
      'measurable               (* Range sets *).

  Definition giry_subbase : set (set (giryType T))
    := [set C | exists (S : set T) (_ : measurable S), preimage_class_of_measures S C].
  *)

  Axiom giry_subbase : set (set (giryType T)).

  Definition giry_measurable : set (set (giryType T)) := <<s giry_subbase>>.

End giry_space.

Definition giryM_display `{R : realType} `{d : measure_display} `{T : measurableType d} :=
  sigma_display (@giry_subbase R d T).
Global Arguments giryM_display {_} {_} {_}.

(** Use giryM for any Giry Monad type *)
Definition giryM (R : realType) (d : measure_display) (T : measurableType d) : measurableType giryM_display :=
  [the measurableType _ of g_sigma_algebraType (@giry_subbase R d T)].
Global Arguments giryM {_} {_} _.


(** Relation defeining measure equality *)
(* Local Open Scope classical_set_scope. *)
*)

(*


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

  Definition base_eval_internal {d1} {T1 : measurableType d1} (S : set T1) (HS : measurable S) :
      giryM T1 -> \bar R :=
    fun μ => μ S.
  Axiom base_eval_meas : forall {d1} {T1 : measurableType d1} (S : set T1) (HS : measurable S),
    measurable_fun setT (base_eval_internal HS).

  (* External
  Definition eval {d1} {T1 : measurableType d1} (S : set T1) :
  *)



  (*
  Lemma base_eval_measurable {d1} {T1 : measurableType d1} (S : set T1) (HS : measurable S):
    measurable_fun [set: giryM T1] ((SubProbability.sort (R:=R))^~ S).
  Proof.
    eapply @measurability.
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

*)

(*
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
    HB.instance Definition _ := @isMeasurable.Build default_measure_display (discrType T) discr_meas
                                 discr_meas0 discr_measC discr_measU.
  End discr_salgebra_instance.

End discrete_space.

Notation "'<<discr' G '>>'" := (discrType G) : classical_set_scope.




(*


Section discrete_space_of_maps.

  Local Open Scope classical_set_scope.

  Context {d1 d2 : measure_display}.
  Context (T1 : measurableType d1).
  Context (T2 : measurableType d2).

  (** Bundled: a measurable map equipped with the set it's measurable out of. *)
  Structure MeasurableMap (dom : set T1) : Type := {
      mf_car :> T1 -> T2;
      dom_meas : d1.-measurable dom;
      f_meas : measurable_fun dom mf_car
  }.

  Definition MeasurableMapT : Type := @MeasurableMap setT.

  Program Definition MeasurableMapT_mk (f : T1 -> T2) (Hf : measurable_fun setT f) : MeasurableMapT :=
    {| mf_car := f ; dom_meas := _; f_meas := Hf |}.
  Next Obligation. intros. by eapply @measurableT. Qed.

  Program Definition MeasurableMapT_default : MeasurableMapT :=
    @MeasurableMapT_mk (cst point) _.
  Next Obligation. intros. by apply measurable_cst. Qed.

  HB.instance Definition _ := gen_eqMixin MeasurableMapT.
  HB.instance Definition _ := gen_choiceMixin MeasurableMapT.
  HB.instance Definition _ := isPointed.Build MeasurableMapT MeasurableMapT_default.

  (*  Check ((<<discr (MeasurableMapT)>>) : measurableType _) . *)

  Definition lift (f : T1 -> T2) (H : measurable_fun setT f) : T1 -> <<discr MeasurableMapT>> :=
    cst (@MeasurableMapT_mk f H).

  (* What do we need for this to be measurable? *)
  Lemma lift_meas (f : T1 -> T2) (H : measurable_fun setT f) : measurable_fun setT (@lift f H).
  Proof.
    unfold lift.
    apply measurable_cst.
  Qed.

  (*
    unfold MeasurableMapT_mk.
    unfold measurable_fun.
    simpl.
    intros _ Y HY.
    rewrite /preimage//=.
    rewrite setTI.
    (* It's either set0 or setT becuase the choice to t doesn't matter (proof irrelevance) *)
  Admitted.
*)


End discrete_space_of_maps.

*)





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

(* MS on Option *)
(* noval (measurable fun ) *)

Section Option.

Local Open Scope classical_set_scope.

Context {d1} {T1 : measurableType d1}.

Definition option_S : Type := option (set T1).
Definition option_T : Type := option T1.
Definition option_ST (k : option_S) : set option_T :=
  match k with
  | None => [set None]
  | Some s => image Some s
  end.
Definition option_ML : set option_S :=
  fun k =>
    match k with
    | None => True
    | Some s => d1.-measurable s
    end.

Definition option_cyl : set (set option_T) := image option_ML option_ST.

HB.instance Definition _ := gen_eqMixin option_T.
HB.instance Definition _ := gen_choiceMixin option_T.
HB.instance Definition _ := isPointed.Build option_T None.

(* FIXME: Remove *)
 Lemma option_meas_obligation :
  forall A : set option_T, <<s option_cyl>> A -> <<s option_cyl >> (~` A).
Proof. eapply sigma_algebraC. Qed.

HB.instance Definition _ := @isMeasurable.Build
  (sigma_display option_cyl)
  (option T1)
  <<s option_cyl>>
  (@sigma_algebra0 _ setT option_cyl)
  option_meas_obligation
  (@sigma_algebra_bigcup _ setT option_cyl).

End Option.

Lemma Some_measurable {d1} {T : measurableType d1} : measurable_fun setT (Some : T -> option T).
Proof.
  eapply measurability; first done.
  rewrite /preimage_class/subset//=.
  intros ? [? [x ? <-] <-].
  rewrite setTI/preimage//=.
  unfold option_ML in H.
  destruct x; rewrite //=.
  { admit. }
  { admit. }
Admitted.
Hint Resolve Some_measurable : measlang.

(* Shapes? *)

Definition 𝜋_Some_v {d1} {T : measurableType d1} (k : option T) : T := match k with | Some v => v | _ => point end.
Definition option_cov_Some {d1} {T : measurableType d1} : set (option T) := [set e | exists x, e = Some x].
Definition option_cov_None {d1} {T : measurableType d1} : set (option T) := [set e | e = None].
Lemma option_cov_Some_meas {d1} {T : measurableType d1} : measurable (option_cov_Some : set (option T)).
Proof. Admitted.
Hint Resolve option_cov_Some_meas : measlang.
Lemma option_cov_None_meas {d1} {T : measurableType d1} : measurable (option_cov_None : set (option T)).
Proof. Admitted.
Hint Resolve option_cov_None_meas : measlang.
Lemma 𝜋_Some_v_meas {d1} {T : measurableType d1} (k : option T) : measurable_fun (option_cov_Some : set (option T)) 𝜋_Some_v.
Proof. Admitted.
Hint Resolve 𝜋_Some_v_meas : measlang.

Section List.

Local Open Scope classical_set_scope.

Context {d1} {T1 : measurableType d1}.

Definition list_S : Type := list (set T1).
Definition list_T : Type := list T1.
Fixpoint list_ST (k : list_S) : set list_T :=
  match k with
  | [::] => [set [::]]
  | (s :: xs) => image2 s (list_ST xs) (fun x y => x :: y)
  end.
Fixpoint list_ML (k : list_S) : Prop :=
    match k with
    | [::] => True
    | (s :: xs) => d1.-measurable s /\ list_ML xs
    end.

Definition list_cyl : set (set list_T) := image list_ML list_ST.

HB.instance Definition _ := gen_eqMixin (list T1).
HB.instance Definition _ := gen_choiceMixin (list T1).
HB.instance Definition _ := isPointed.Build (list T1) [::].

(* FIXME: Remove *)
 Lemma list_meas_obligation :
  forall A : set list_T, <<s list_cyl>> A -> <<s list_cyl >> (~` A).
Proof. eapply sigma_algebraC. Qed.

HB.instance Definition _ := @isMeasurable.Build
  (sigma_display list_cyl)
  (list T1)
  <<s list_cyl>>
  (@sigma_algebra0 _ setT list_cyl)
  list_meas_obligation
  (@sigma_algebra_bigcup _ setT list_cyl).
End List.

Definition consU {d1} {T : measurableType d1} : (T * list T)%type -> list T := uncurry List.cons.

Lemma cons_measurable {d1} {T : measurableType d1} : measurable_fun setT (consU : (T * list T)%type -> list T).
Proof. Admitted.
Hint Resolve cons_measurable : measlang.

(* Shapes? *)

Definition 𝜋_cons_v {d1} {T : measurableType d1} (k : list T) : T := match k with | (v :: _) => v | _ => point end.
Definition 𝜋_cons_vs {d1} {T : measurableType d1} (k : list T) : list T := match k with | (_ :: v) => v | _ => point end.
Definition list_cov_cons {d1} {T : measurableType d1} : set (list T) := [set e | exists x y, e = x :: y].
Definition list_cov_empty {d1} {T : measurableType d1} : set (list T) := [set e | e = [::]].
Lemma list_cov_cons_meas {d1} {T : measurableType d1} : measurable (list_cov_cons : set (list T)).
Proof. Admitted.
Hint Resolve list_cov_cons_meas : measlang.
Lemma list_cov_empty_meas {d1} {T : measurableType d1} : measurable (list_cov_empty : set (list T)).
Proof. Admitted.
Hint Resolve list_cov_empty_meas : measlang.
Lemma 𝜋_cons_v_meas {d1} {T : measurableType d1} (k : list T) : measurable_fun (list_cov_cons : set (list T)) 𝜋_cons_v.
Proof. Admitted.
Hint Resolve 𝜋_cons_v_meas : measlang.
Lemma 𝜋_cons_vs_meas {d1} {T : measurableType d1} (k : list T) : measurable_fun (list_cov_cons : set (list T)) 𝜋_cons_vs.
Proof. Admitted.
Hint Resolve 𝜋_cons_vs_meas : measlang.

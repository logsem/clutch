(* TODO cleanup imports *)
Set Warnings "hiding-delimiting-key".
From HB Require Import structures.
From Coq Require Import Logic.ClassicalEpsilon Psatz.
From stdpp Require Import base numbers binders strings gmap.
From mathcomp Require Import functions.
From mathcomp.analysis Require Import reals measure itv lebesgue_measure probability.
From mathcomp Require Import ssrbool all_algebra eqtype choice boolp fintype.
From iris.algebra Require Export ofe.
From clutch.prelude Require Export stdpp_ext.
From clutch.common Require Export locations.
From clutch.meas_lang Require Import ectxi_language ectx_language.
From Coq Require Export Reals.
From clutch.prob.monad Require Export giry prelude.
From mathcomp.analysis Require Export Rstruct.
From mathcomp Require Import classical_sets.
Import Coq.Logic.FunctionalExtensionality.
From clutch.prelude Require Import classical.
From clutch.meas_lang.lang Require Export prelude. (* types constructors shapes cover projections. **)
Set Warnings "hiding-delimiting-key".

Set Default Proof Using "Type*".

Section seq_measure.
  Local Open Scope classical_set_scope.
  (** Measurable functions out of nat *)
  Context {d} {T : measurableType d}.

  Definition nf : Type := nat -> T.

  HB.instance Definition _ := gen_eqMixin nf.
  HB.instance Definition _ := gen_choiceMixin nf.
  HB.instance Definition _ := isPointed.Build nf (cst point).

  Definition nf_generators : set (set nf) :=
    (\bigcup_i (preimage_class setT (fun f => f i) measurable)).

  Definition nf_measurable : set (set nf) := <<s nf_generators>>.

  Lemma nf_meas0 : nf_measurable set0.
  Proof. by apply sigma_algebra0. Qed.

  Lemma nf_measC X : (nf_measurable X) -> nf_measurable (~` X).
  Proof. by apply sigma_algebraC. Qed.

  Lemma nf_measU (F : sequences.sequence (set nf)) : (forall i, nf_measurable (F i)) -> nf_measurable (\bigcup_i F i).
  Proof. by apply sigma_algebra_bigcup. Qed.

  HB.instance Definition _ :=
    @isMeasurable.Build (sigma_display nf_measurable) nf nf_measurable nf_meas0 nf_measC nf_measU.

  Definition nf_eval (i : nat) : nf -> T := (fun f : nf => f i).

  Lemma nf_eval_measurable (i : nat) : measurable_fun setT (nf_eval i).
  Proof.
    intros _ Y HY.
    rewrite /nf_measurable.
    suffices H : nf_generators ([set: tapes_nf__canonical__measure_SigmaRing] `&` nf_eval i @^-1` Y).
    { by apply ((@sub_gen_smallest _ _ nf_generators) _ H). }
    exists i; [done|].
    rewrite /nf_eval.
    rewrite /preimage_class//=.
    exists Y; [done|].
    rewrite setTI.
    done.
  Qed.

  (* The uncurry is measurable becuase nat is discrete and countable *)
  Definition nf_evalC : (nat * nf)%type -> T := uncurry nf_eval.
  Lemma nf_evalC_measurable : measurable_fun setT nf_evalC.
  Proof. by apply (@uncurry_nat_measurable _ _ _ _ nf_eval), nf_eval_measurable. Qed.

  Definition nf_update (i : nat) : (T * nf)%type -> nf :=
    (fun x => (fun n => if (n =? i) then (fst x) else ((ssrfun.comp (nf_eval n) snd) x))).

  Lemma nf_update_measurable (i : nat) : measurable_fun setT (nf_update i).
  Proof.
    eapply @measurability; [done|].
    rewrite //=/nf_update/subset/preimage_class//=.
    intro S.
    rewrite /nf_generators/preimage_class//=.
    move=> [S' [k _ +]].
    rewrite setTI//=; move=>[S'' HS'' +].
    rewrite setTI//=; move=><-<-//=.
    rewrite <-comp_preimage; rewrite /ssrfun.comp//=.
    destruct (k =? i); rewrite //=.
    { have -> : ((λ x : T * nf, x.1) @^-1` S'') = (setT `&` fst @^-1` S'').
      { rewrite /setI/preimage/cst//=.
        apply /predeqP =>[y] /=.
        by intuition. }
      by eapply @measurable_fst. }
    { have -> : ((λ x : T * nf, nf_eval k x.2) @^-1` S'') = ((ssrfun.comp (nf_eval k) snd) @^-1` S'').
      { by rewrite /ssrfun.comp/preimage//=. }
      rewrite <-(setTI (preimage _ _)).
      by eapply (measurable_comp _ _ (nf_eval_measurable k) (measurable_snd) _ HS'').
      Unshelve.
      { by eapply @measurableT. }
      { by simpl. }
      { by eapply @measurableT. }
    }
  Qed.


  Definition nf_updateC : (nat * (T * nf))%type -> nf := uncurry nf_update.
  Lemma nf_updateC_measurable : measurable_fun setT nf_updateC.
  Proof. by apply (@uncurry_nat_measurable _ _ _ _ nf_update), nf_update_measurable. Qed.

End seq_measure.




(**  General lemmas about tapes *)

Definition tape_content_t (A : Type) : Type := nat -> option A.

Record tape (A : Type) : Type := {
  tape_position : nat;
  tape_contents : tape_content_t A
}.

Definition emptyTapeContents {A : Type} : tape_content_t A := fun _ => None.

Definition emptyTape {A : Type} : tape A :=
  {| tape_position := 0 ;
     tape_contents := emptyTapeContents
  |}.

(* History lookup: look through absolute history *)
Global Instance tape_content_lookup {A} : Lookup nat A (tape_content_t A) := fun i => fun h => h i.

(**  Specialize tapes to btapes and utapes, construct siga algebra *)
Section tapes_algebra.
  Local Open Scope classical_set_scope.


  (* Tapes in the computable fragment *)
  Record pre_btape : Type := {
      btape_tape :> tape nat;
      btape_bound : nat
  }.

  (* Tapes of real numbers *)
 Definition pre_utape : Type := tape R.


  (* FIXME: move *)
  Definition image4 {TA TB TC TD rT} (A : set TA) (B : set TB) (C : set TC) (D : set TD) (f : TA -> TB -> TC -> TD -> rT) :=
    [set z | exists2 x, A x & exists2 y, B y & exists2 w, C w & exists2 v, D v & f x y w v = z].
  Arguments image4 _ _ _ _ _ _ _ _ _ /.

  Definition btape_basis_emp : set (set pre_btape) :=
    let bound_set : set nat := setT in
    let pos_set : set nat := setT in

    (* The set of all btapes such that
       - the bound is b
       - the position is p
       - the content is empty *)
    let construct b p :=
      [set {| btape_tape := {| tape_position := p; tape_contents := (fun _ => None) |} ;
              btape_bound := b |}] in
    image2 bound_set pos_set construct.

  Program Definition btape_basis_full : set (set pre_btape) :=
    let bound_set : set nat := setT in
    let pos_set   : set nat := setT in
    let index_set : set nat := setT in
    let value_set : set nat := setT in

    (* The set of all btapes such that
       - the bound is b
       - the position is p
       - the content at index i is set to the value v *)
    let construct b p i v :=
      (fun bt =>
         exists contents,
           bt = {| btape_tape := {| tape_position := p; tape_contents := contents |}; btape_bound := b|} /\
           contents !! i = Some v) in

    image4 bound_set pos_set index_set value_set construct.

  Definition btape_basis := btape_basis_emp `|` btape_basis_full.

  HB.instance Definition _ := gen_eqMixin pre_btape.
  HB.instance Definition _ := gen_choiceMixin pre_btape.
  HB.instance Definition _ := isPointed.Build pre_btape {| btape_tape := emptyTape ; btape_bound := 0 |}.

  Local Lemma btape_meas_obligation : ∀ A : set pre_btape, <<s btape_basis>> A → <<s btape_basis>> (~` A).
  Proof. eapply sigma_algebraC. Qed.

  HB.instance Definition _ := @isMeasurable.Build
    (sigma_display btape_basis)
    pre_btape
    <<s btape_basis>>
    (@sigma_algebra0 _ setT btape_basis)
    btape_meas_obligation
    (@sigma_algebra_bigcup _ setT btape_basis).


  Definition utape_basis_emp : set (set pre_utape) :=
    let pos_set : set nat := setT in

    (* The set of all utapes such that
       - the position is p
       - the content is empty *)
    let construct p :=
      [set {| tape_position := p; tape_contents := (fun _ => None) |}] in
    image pos_set construct.

  (* FIXME: This should not return a singleton! *)
  Definition utape_basis_full : set (set pre_utape) :=
    let pos_set   : set nat := setT in
    let index_set : set nat := setT in
    let value_set : set (set (R : realType)) := 'measurable in

    (* The set of all utapes such that
       - the position is p
       - the content at position i is set to some value in set_of_v *)
    let construct p i set_of_v :=
        (fun ut =>
           exists contents r,
             ut = {| tape_position := p; tape_contents := contents |} /\
             contents !! i = Some r /\
             set_of_v r) in
    image3 pos_set index_set value_set construct.

  Definition utape_basis : set (set pre_utape) := utape_basis_emp `|` utape_basis_full.

  HB.instance Definition _ := gen_eqMixin pre_utape.
  HB.instance Definition _ := gen_choiceMixin pre_utape.
  HB.instance Definition _ := isPointed.Build pre_utape emptyTape.

  Local Lemma utape_meas_obligation : ∀ A : set pre_utape, <<s utape_basis>> A → <<s utape_basis>> (~` A).
  Proof. eapply sigma_algebraC. Qed.

  HB.instance Definition _ := @isMeasurable.Build
    (sigma_display utape_basis)
    pre_utape
    <<s utape_basis>>
    (@sigma_algebra0 _ setT utape_basis)
    utape_meas_obligation
    (@sigma_algebra_bigcup _ setT utape_basis).


  (* User-facing types *)
  Definition btape : measurableType btape_basis.-sigma := pre_btape.
  Definition utape : measurableType utape_basis.-sigma := pre_utape.

End tapes_algebra.


(* btape and utape definitions *)

(* All values of the tape are within the tape bound *)
Definition btape_inbounds (t : btape): Prop :=
  forall n : nat,
    tape_contents _ t n = None \/
    exists v : nat, tape_contents _ t n = Some v /\ v < btape_bound t.

(* All tape values prior to state have been determined *)
Definition tape_history_deterministic {A} (t : tape A) : Prop :=
  forall i : nat, i < tape_position _ t -> exists v : A, tape_contents _ t i = Some v.

(* Tape lookup: look relative to current index. t !! 0  will be the next sample. *)
Global Instance tape_rel_lookup {A} : Lookup nat A (tape A) := fun i => fun t => (tape_contents _ t (i + tape_position _ t)).

Definition tape_content_update_unsafe {A} (i : nat) (v : option A) (h : tape_content_t A) : tape_content_t A
  := fun i' => if i' =? i then v else h i'.

Global Instance tape_content_insert {A} : Insert nat (option A) (tape_content_t A) := tape_content_update_unsafe.

Definition tapeUpdateUnsafe {A} (i : nat) (v : option A) (t : tape A) : tape A :=
  {| tape_position := tape_position _ t;
     tape_contents := <[ (i + tape_position _ t) := v ]> (tape_contents _ t)
  |}.

Global Instance tape_insert {A} : Insert nat (option A) (tape A) := tapeUpdateUnsafe.

Program Definition tapeAdvance {A} (t : tape A) : tape A
  := {| tape_position := 1 + tape_position _ t; tape_contents := tape_contents _ t |}.

(* Advance the tape by 1, returning an updated tape and the first sample on the tape. *)
Program Definition tapeNext {A} (t : tape A) (H : isSome (t !! 0)) : A * (tape A)
  := match (t !! 0) with
     | None => _
     | Some v =>
         (v,
          {| tape_position := 1 + tape_position _ t;
             tape_contents := tape_contents _ t |})
     end.
Next Obligation. by move=>/= ? ? H1 H2; symmetry in H2; rewrite H2//= in H1. Defined.

(* Representation predicates for common tape structures *)

Definition tapeHasPrefix {A} (t : tape A) (l : list A) : Prop
  := forall i : nat, i < length l -> t !! i = l !! i.

Definition tapeEmptyAfter {A} (t : tape A) (b : nat) : Prop
  := forall i : nat, i >= b -> t !! i = None.


(* Tapes a la base clutch *)
Definition isFiniteTape (t : btape) (l : list nat) : Prop
  :=   tapeHasPrefix t l
     /\ tapeEmptyAfter t (length l)
     /\ btape_inbounds t
     /\ tape_history_deterministic t.


(* TODO: realIsBinarySequence (cannonical form w/ 0-termination on dyadic numbers) *)

Definition tapeHasInfinitePrefix {A} (t : tape A) (f : nat -> A) : Prop
  := forall i : nat, t !! i = Some (f i).

(* TODO: tapeIsRealInRange (l : R) ... := bound = 1, tapeHasInfinitePrefic *)
(* tapeOfReal ... ?*)

(* Tape with "Junk" prefix *)
Definition tapeHasEventually {A} (t : tape A) (l : list A) : Prop
  := exists offset: nat, forall i : nat, i < length l -> t !! (i + offset) = l !! i.

Global Instance tape_inhabited {A} : Inhabited (tape A) := populate emptyTape.
Global Instance tapes_lookup_total {A} : LookupTotal loc (tape A) (gmap loc (tape A)).
Proof. apply map_lookup_total. Defined.
Global Instance tapes_insert {A} : Insert loc (tape A) (gmap loc (tape A)).
Proof. apply map_insert. Defined.

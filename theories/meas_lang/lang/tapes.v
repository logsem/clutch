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
  Hint Resolve nf_eval_measurable : measlang.

  (* The uncurry is measurable becuase nat is discrete and countable *)
  Definition nf_evalC : (nat * nf)%type -> T := uncurry nf_eval.
  Lemma nf_evalC_measurable : measurable_fun setT nf_evalC.
  Proof. by apply (@uncurry_nat_measurable _ _ _ _ nf_eval), nf_eval_measurable. Qed.
  Hint Resolve nf_evalC_measurable : measlang.

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
  Hint Resolve nf_update_measurable : measlang.

  Definition nf_updateC : (nat * (T * nf))%type -> nf := uncurry nf_update.
  Lemma nf_updateC_measurable : measurable_fun setT nf_updateC.
  Proof. by apply (@uncurry_nat_measurable _ _ _ _ nf_update), nf_update_measurable. Qed.
  Hint Resolve nf_updateC_measurable : measlang.

End seq_measure.

Global Arguments nf {_} _.

Section tapes.
  Local Open Scope classical_set_scope.

  (**  General lemmas about tapes *)

  Context {d} {A : measurableType d}.

  Definition tape : Type := (nat * nf (option A))%type.

  Definition tape_position : tape -> nat := fst.
  Lemma tape_positon_meas : measurable_fun setT tape_position.
  Proof. unfold tape_position. by eauto with measlang. Qed.
  Hint Resolve tape_positon_meas : measlang.

  Definition tape_contents : tape -> nf (option A) := snd.
  Lemma tape_contents_meas : measurable_fun setT tape_contents.
  Proof. unfold tape_contents. by eauto with measlang. Qed.
  Hint Resolve tape_contents_meas : measlang.

  Definition emptyTapeContents  : nf (option A) := cst None.

  Definition emptyTape : tape := (0, emptyTapeContents).

  (* History lookup: look through absolute history *)
  (** Don't use lookup if you expect the function to be measurable in the index! *)
  Global Instance tape_content_lookup : Lookup nat A tape := fun i => (ssrfun.comp (nf_eval i) tape_contents).

  Definition shiftTape (f : nat -> nat) : tape -> tape :=
    mProd (ssrfun.comp f tape_position) tape_contents.

  Lemma shiftTape_meas (f : nat -> nat) : measurable_fun setT (shiftTape f).
  Proof.
    mcrunch_prod.
    { eapply measurable_comp; first by eapply @measurableT.
      all: simpl; by eauto with measlang. }
    by eauto with measlang.
  Qed.
  Hint Resolve shiftTape_meas : measlang.

  Definition tapeAdvance : tape -> tape := shiftTape (Nat.succ).
  Lemma tapeAdvance_meas : measurable_fun setT tapeAdvance.
  Proof. by eauto with measlang. Qed.
  Hint Resolve tapeAdvance_meas : measlang.

End tapes.

Global Arguments tape {_} _.

Local Open Scope classical_set_scope.

(** Tape + bound *)
Definition btape : Type := (nat * (tape <<discr Z>>))%type.

Definition btape_position : btape -> nat := ssrfun.comp fst snd.
Lemma btape_positon_meas : measurable_fun setT btape_position.
Proof.
  eapply measurable_comp; first by eapply @measurableT.
  { by simpl. }
  { by eauto with measlang. }
  { by eauto with measlang. }
Qed.
Hint Resolve btape_positon_meas : measlang.

Definition btape_contents : btape -> nf (option <<discr Z>>) := ssrfun.comp snd snd.
Lemma btape_contents_meas : measurable_fun setT btape_contents.
Proof.
  eapply measurable_comp; first by eapply @measurableT.
  { by simpl. }
  { by eauto with measlang. }
  { by eauto with measlang. }
Qed.
Hint Resolve btape_contents_meas : measlang.

Definition btape_bound : btape -> nat := fst.
Lemma btape_bound_meas : measurable_fun setT btape_bound.
Proof. unfold btape_bound; by eauto with measlang. Qed.
Hint Resolve btape_bound_meas : measlang.


(** Tape of real numbers *)
Definition utape `{R : realType} := tape R.




(* btape and utape definitions *)

(* All values of the tape are within the tape bound *)
Definition btape_inbounds (t : btape): Prop :=
  forall n : nat,
    btape_contents t n = None \/
    exists v : Z, btape_contents t n = Some v /\ (v < btape_bound t)%Z.

(* All tape values prior to state have been determined *)
Definition tape_history_deterministic {d} {A : measurableType d} (t : tape A) : Prop :=
  forall i : nat, i < tape_position t -> exists v : A, tape_contents t i = Some v.

(* Tape lookup: look relative to current index. t !! 0  will be the next sample.
Global Instance tape_rel_lookup {A} : Lookup nat A (tape A) :=
  fun i => fun t => (tape_contents _ t (i + tape_position _ t)).
*)

(*
Global Instance tape_content_insert {A} : Insert nat (option A) (tape_content_t A) := tape_content_update_unsafe.

Definition tapeUpdateUnsafe {A} (i : nat) (v : option A) (t : tape A) : tape A :=
  {| tape_position := tape_position _ t;
     tape_contents := <[ (i + tape_position _ t) := v ]> (tape_contents _ t)
  |}.

Global Instance tape_insert {A} : Insert nat (option A) (tape A) := tapeUpdateUnsafe.
*)

(*
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
*)




(*
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
*)

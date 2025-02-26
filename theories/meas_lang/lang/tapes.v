Set Warnings "hiding-delimiting-key".
From HB Require Import structures.
From Coq Require Export ssrfun.
From stdpp Require Import binders.
From mathcomp Require Import eqtype choice boolp functions classical_sets.
From mathcomp.analysis Require Import reals measure lebesgue_measure sequences.
From clutch.common Require Export locations.
From clutch.meas_lang.lang Require Export prelude.
Set Warnings "hiding-delimiting-key".

Set Default Proof Using "Type*".

Local Open Scope classical_set_scope.

(** Sigma algebra on sequences *)

Section sequence_measure.
  Context {d} {T : measurableType d}.

  HB.instance Definition _ := gen_eqMixin T^nat.
  HB.instance Definition _ := gen_choiceMixin T^nat.
  HB.instance Definition _ := isPointed.Build T^nat (cst point).

  Definition sequence_generators : set (set T^nat) :=
    \bigcup_i (preimage_class setT (fun f => f i) measurable).

  Definition sequence_measurable : set (set T^nat) := <<s sequence_generators>>.

  Lemma sequence_meas0 : sequence_measurable set0.
  Proof. by apply sigma_algebra0. Qed.

  Lemma sequence_measC X : (sequence_measurable X) -> sequence_measurable (~` X).
  Proof. by apply sigma_algebraC. Qed.

  Lemma sequence_measU (F : sequence (set T^nat)) : (forall i, sequence_measurable (F i)) -> sequence_measurable (\bigcup_i F i).
  Proof. by apply sigma_algebra_bigcup. Qed.

  HB.instance Definition _ :=
    @isMeasurable.Build (sigma_display sequence_measurable) T^nat
      sequence_measurable sequence_meas0 sequence_measC sequence_measU.

  Definition sequence_eval (i : nat) : T^nat -> T := fun f => f i.

  Lemma sequence_eval_measurable (i : nat) : measurable_fun setT (sequence_eval i).
  Proof.
    intros _ Y HY.
    rewrite /sequence_measurable.
    suffices H : sequence_generators (setT `&` sequence_eval i @^-1` Y).
    { by apply ((@sub_gen_smallest _ _ sequence_generators) _ H). }
    exists i; [done|].
    rewrite /sequence_eval.
    rewrite /preimage_class//=.
    exists Y; [done|].
    rewrite setTI.
    done.
  Qed.
  Hint Resolve sequence_eval_measurable : measlang.

  (* The uncurry is measurable becuase nat is discrete and countable *)
  Definition sequence_evalC : (nat * T^nat)%type -> T := uncurry sequence_eval.
  Lemma sequence_evalC_measurable : measurable_fun setT sequence_evalC.
  Proof. by apply (@uncurry_nat_measurable _ _ _ _ sequence_eval), sequence_eval_measurable. Qed.
  Hint Resolve sequence_evalC_measurable : measlang.

  Definition sequence_update (i : nat) : (T * T^nat)%type -> T^nat :=
    fun x n =>
      if (n =? i)
        then fst x
        else ((sequence_eval n) \o snd) x.

  Lemma sequence_update_measurable (i : nat) : measurable_fun setT (sequence_update i).
  Proof.
    eapply @measurability; [done|].
    rewrite //=/sequence_update/subset/preimage_class//=.
    intro S.
    rewrite /sequence_generators/preimage_class//=.
    move=> [S' [k _ +]].
    rewrite setTI//=; move=>[S'' HS'' +].
    rewrite setTI//=; move=><-<-//=.
    rewrite <-comp_preimage; rewrite /ssrfun.comp//=.
    destruct (k =? i); rewrite //=.
    { have -> : ((λ x : T * sequence T, x.1) @^-1` S'') = (setT `&` fst @^-1` S'').
      { rewrite /setI/preimage/cst//=.
        apply /predeqP =>[y] /=.
        by intuition. }
      by eapply @measurable_fst. }
    { have -> : ((λ x : T * sequence T, sequence_eval k x.2) @^-1` S'') = ((ssrfun.comp (sequence_eval k) snd) @^-1` S'').
      { by rewrite /ssrfun.comp/preimage//=. }
      rewrite <-(setTI (preimage _ _)).
      by eapply (measurable_comp _ _ (sequence_eval_measurable k) (measurable_snd) _ HS'').
      Unshelve.
      { by eapply @measurableT. }
      { by simpl. }
      { by eapply @measurableT. }
    }
  Qed.
  Hint Resolve sequence_update_measurable : measlang.

  Definition sequence_updateC : (nat * (T * T^nat))%type -> T^nat := uncurry sequence_update.
  Lemma sequence_updateC_measurable : measurable_fun setT sequence_updateC.
  Proof. by apply (@uncurry_nat_measurable _ _ _ _ sequence_update), sequence_update_measurable. Qed.
  Hint Resolve sequence_updateC_measurable : measlang.

End sequence_measure.

Section tapes.
  Local Open Scope classical_set_scope.

  (**  General lemmas about tapes *)

  Context {d} {A : measurableType d}.

  Definition tape : Type := (nat * (option A)^nat)%type.

  Definition tape_position : tape -> nat := fst.
  Lemma tape_positon_meas : measurable_fun setT tape_position.
  Proof. unfold tape_position. by eauto with measlang. Qed.
  Hint Resolve tape_positon_meas : measlang.

  Definition tape_contents : tape -> (option A)^nat := snd.
  Lemma tape_contents_meas : measurable_fun setT tape_contents.
  Proof. unfold tape_contents. by eauto with measlang. Qed.
  Hint Resolve tape_contents_meas : measlang.

  Definition emptyTapeContents : (option A)^nat := cst None.

  Definition emptyTape : tape := (0, emptyTapeContents).

  (* History lookup: look through absolute history *)
  (** Don't use lookup if you expect the function to be measurable in the index! *)
  Global Instance tape_content_lookup : Lookup nat A tape := fun i => ((sequence_eval i) \o tape_contents).

  Definition shiftTape (f : nat -> nat) : tape -> tape :=
    (f \o tape_position) △ tape_contents.

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

Definition btape_contents : btape -> sequence (option <<discr Z>>) := snd \o snd.
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
Definition utape := tape ((R : realType) : measurableType _).


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

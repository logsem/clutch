(* TODO cleanup imports *)
Set Warnings "-hiding-delimiting-key".
From HB Require Import structures.
From Coq Require Import Logic.ClassicalEpsilon Psatz.
From stdpp Require Import base numbers binders strings gmap fin_maps.
From mathcomp Require Import functions.
From mathcomp.analysis Require Import reals measure itv lebesgue_measure probability.
From mathcomp Require Import ssrbool all_algebra eqtype choice boolp fintype.
From iris.algebra Require Export ofe.
From clutch.prelude Require Export stdpp_ext.
From clutch.common Require Export locations.
From clutch.meas_lang Require Import ectxi_language ectx_language.
From Coq Require Export Reals.
From clutch.prob.monad Require Export giry.
From mathcomp.analysis Require Export Rstruct.
From mathcomp Require Import classical_sets.
Import Coq.Logic.FunctionalExtensionality.
From clutch.prelude Require Import classical.
From clutch.meas_lang.lang Require Export prelude types constructors shapes cover projections tapes.
Set Warnings "hiding-delimiting-key".

Local Open Scope classical_set_scope.

Set Default Proof Using "Type*".

Section heapdom.
  Context {d} {T : measurableType d}.

  (**  Measure space on sets  *)

  Structure MeasHeapDom := { v : set T }.

  HB.instance Definition _ := gen_eqMixin MeasHeapDom.
  HB.instance Definition _ := gen_choiceMixin MeasHeapDom.
  HB.instance Definition _ := isPointed.Build MeasHeapDom {| v := set0 |}.

  (* Generated by singleton sets, so all countable (and finite) sets are measurable. *)
  Definition measheapdom_generators :=
    [set [set (Build_MeasHeapDom x)] | x in measurable ].

  Definition measheapdom_measurable := <<s measheapdom_generators>>.

  Lemma mhd_meas0 : measheapdom_measurable set0.
  Proof. by apply sigma_algebra0. Qed.

  Lemma mhd_measC X : (measheapdom_measurable  X) -> measheapdom_measurable  (~` X).
  Proof. by apply sigma_algebraC. Qed.

  Lemma mhd_measU (F : sequences.sequence (set MeasHeapDom)) : (forall i,measheapdom_measurable  (F i)) -> measheapdom_measurable (\bigcup_i F i).
  Proof. by apply sigma_algebra_bigcup. Qed.

  HB.instance Definition _ :=
    @isMeasurable.Build (sigma_display measheapdom_measurable) MeasHeapDom
      measheapdom_measurable mhd_meas0 mhd_measC mhd_measU.
End heapdom.

Section hp_measure.
  Local Open Scope classical_set_scope.
  (** Measurable functions out of <<discr loc>> (TODO: Generalize with the seq_measure).
      Will need to pick the right Countable class so that it works with the shapes proof
      but also the countability part of the measurability argument.

      Also will need to deal with the fact that nat does not have a <<discr _>> strucutre,
      which messes up my typeclasses for SA's generated by singletons.
   *)
  Context {d} {T : measurableType d}.

  Definition hp : Type := <<discr loc>> -> T.

  HB.instance Definition _ := gen_eqMixin hp.
  HB.instance Definition _ := gen_choiceMixin hp.
  HB.instance Definition _ := isPointed.Build hp (cst point).

  Definition hp_generators : set (set hp) :=
    (\bigcup_i (preimage_class setT (fun f => f i) measurable)).

  Definition hp_measurable : set (set hp) := <<s hp_generators>>.

  Lemma hp_meas0 : hp_measurable set0.
  Proof. by apply sigma_algebra0. Qed.

  Lemma hp_measC X : (hp_measurable X) -> hp_measurable (~` X).
  Proof. by apply sigma_algebraC. Qed.

  Lemma hp_measU (F : sequences.sequence (set hp)) : (forall i, hp_measurable (F i)) -> hp_measurable (\bigcup_i F i).
  Proof. by apply sigma_algebra_bigcup. Qed.

  HB.instance Definition _ :=
    @isMeasurable.Build (sigma_display hp_measurable) hp hp_measurable hp_meas0 hp_measC hp_measU.

  Definition hp_eval (i : <<discr loc>>) : hp -> T := fun f => f i.

  Lemma hp_eval_meas_fun (i : <<discr loc>>) : measurable_fun setT (hp_eval i).
  Proof.
    intros _ Y HY.
    rewrite /hp_measurable.
    suffices H : hp_generators (setT `&` hp_eval i @^-1` Y).
    { by apply ((@sub_gen_smallest _ _ hp_generators) _ H). }
    exists i; [done|].
    rewrite /hp_eval.
    rewrite /preimage_class//=.
    exists Y; [done|].
    rewrite setTI.
    done.
  Qed.
  Hint Resolve hp_eval_meas_fun : measlang.


  Lemma uncurry_loc_measurable {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}
          (f : <<discr loc>> -> T1 -> T2) (Hf : forall i, measurable_fun setT (f i)) :
        measurable_fun setT (uncurry f).
   Proof using T d.
    intros _ Y HY.
    have -> : ((uncurry f) @^-1` Y) = \bigcup_i ((setX [set loc_enum i] ((f $ loc_enum i) @^-1` Y)) : set (<<discr loc>> * _)%type).
    { rewrite /uncurry/preimage/setX//=.
      apply /predeqP =>[[l ]] /=.
      split.
      { intros H.
        destruct (loc_enum_surj l) as [i Hi].
        exists i; [done|].
        by rewrite Hi //=. }
      { move=>[x ?]//=. by move=>[-> ?]//=. }
    }
    rewrite setTI.
    apply bigcup_measurable.
    intros i ?.
    apply measurableX.
    { by rewrite /measurable//=. }
    rewrite <-(setTI (preimage _ _)).
    by eapply (Hf _ _ Y HY).
    Unshelve. by apply @measurableT.
  Qed.


  (* The uncurry is measurable becuase nat is discrete and countable *)
  Definition hp_evalC : (<<discr loc>> * hp)%type -> T := uncurry hp_eval.
  Lemma hp_evalC_meas_fun : measurable_fun setT hp_evalC.
  Proof. by apply (@uncurry_loc_measurable _ _ _ _ hp_eval), hp_eval_meas_fun. Qed.
  Hint Resolve hp_evalC_meas_fun : measlang.

  Definition hp_update (i : <<discr loc>>) : (T * hp)%type -> hp :=
    fun x n =>
      if (decide (n = i))
        then fst x
        else ((hp_eval n) \o snd) x.

  Lemma hp_update_meas_fun (i : <<discr loc>>) : measurable_fun setT (hp_update i).
  Proof.
    eapply @measurability; [done|].
    rewrite //=/hp_update/subset/preimage_class//=.
    intro S.
    rewrite /hp_generators/preimage_class//=.
    move=> [S' [k _ +]].
    rewrite setTI//=; move=>[S'' HS'' +].
    rewrite setTI//=; move=><-<-//=.
    rewrite <-comp_preimage; rewrite /ssrfun.comp//=.
    destruct (decide (k = i)); rewrite //=.
    { have -> : ((λ x : T * hp, x.1) @^-1` S'') = (setT `&` fst @^-1` S'').
      { rewrite /setI/preimage/cst//=.
        apply /predeqP =>[y] /=.
        by intuition. }
      by eapply @measurable_fst. }
    { have -> : ((λ x : T * hp, hp_eval k x.2) @^-1` S'') = ((ssrfun.comp (hp_eval k) snd) @^-1` S'').
      { by rewrite /ssrfun.comp/preimage//=. }
      rewrite <-(setTI (preimage _ _)).
      by eapply (measurable_comp _ _ (hp_eval_meas_fun k) (measurable_snd) _ HS'').
      Unshelve.
      { by eapply @measurableT. }
      { by simpl. }
      { by eapply @measurableT. }
    }
  Qed.
  Hint Resolve hp_update_meas_fun : measlang.

  Definition hp_updateC : (<<discr loc>> * (T * hp))%type -> hp := uncurry hp_update.
  Lemma hp_updateC_meas_fun : measurable_fun setT hp_updateC.
  Proof. by apply (@uncurry_loc_measurable _ _ _ _ hp_update), hp_update_meas_fun. Qed.
  Hint Resolve hp_updateC_meas_fun : measlang.

End hp_measure.

Global Arguments hp {_} _.
Global Arguments MeasHeapDom {_} _.


Section dom.
  Local Open Scope classical_set_scope.
  (** domain of a heap function hpf *)
  Context {d} {T : measurableType d}.

  (*

  Definition hpf_point (l0 : <<discr loc>>) (t : T) : hpf (option T) :=
    fun l => if decide(l = l0) then Some t else None.

  Lemma hp_point_singleton_measurable l0 (S : set T) (HS : measurable S) :
    measurable (image S (hp_point l0)).
  Proof.
    (* This set is the countable intersection of the preimage of (image S Some) in location l0
       and [set None] in all others  *)
  Admitted.
   *)

  Definition dom (m : hp (option T)) : MeasHeapDom <<discr loc>> :=
    {| v := [set l | is_Some (hp_eval l m) ] |}.

  Lemma dom_measurable : measurable_fun setT dom.
  Proof.
    (* Suffices to show that the preimages of generators of (MeasHeapDom <<discr loc>>) are measurable
       Suffices to show that forall (S : set <<discr loc>>), preimage [set S] dom is measurable
       Suffices to show that forall (S : set <<discr loc>>), the set of hpfs which
          assign l to Some _ iff l is in S is measurable
       This set is the countable intersection of preimages of (image Some setT) or [None]
          under (eval l); so is measurable.
     *)
  Admitted.

End dom.

Definition loc_lt (l1 l2 : <<discr loc>>) : Prop :=
  (l1.(loc_car) < l2.(loc_car))%Z.

Definition hasMax : MeasHeapDom <<discr loc>> -> Prop :=
  fun S => exists (l : <<discr loc>>), forall l' : <<discr loc>>, S.(v) l -> loc_lt l' l.

Section hp.
  Local Open Scope classical_set_scope.
  Context {d} (T : measurableType d).

  (* The set of MeasHeapDom's that have a maximum is measurable. *)
  Lemma hasMaxMeasurable : measurable hasMax.
  Proof.
    (* hasMax = U_(i in i) [set S | |S| = i ]
              = U_(i in i), U(S : set <<discr loc>>, |S| = i), [set S]
        Because <<discr loc>> is discrete, each S is measurable, so each [set S] is measurable.
        So this set is measurable. *)
  Admitted.

  (** A heap (hp) is a map from <<discr loc>> to some type, whose domain is finite. *)
  Definition hp_finite : set (hp (option T)) := preimage dom hasMax.

  Lemma hp_finite_measurable : measurable hp_finite.
  Proof.
    unfold hp_finite.
    rewrite <- (setTI (preimage _ _)).
    apply dom_measurable; try by eauto.
    by apply hasMaxMeasurable.
  Qed.
  Hint Resolve hp_finite_measurable : measlang.


  Definition get_fresh (m : hp (option T)) (H : hasMax (dom m)): <<discr loc>>.
    (* The minimum loc that is greater than every element of ...
       Exists because of H.
     *)
  Admitted.

  Definition fresh : hp (option T) -> <<discr loc>> :=
    fun m => extern_if point (get_fresh m).

  Lemma fresh_meas : measurable_fun hp_finite fresh.
  Proof.
    (*
      On this set, it's equal to...

      Suffices to consider the preimage of each [set l]
      This preimage (when restructred to hp_finite) is the empty map when l = 0
      Otherwise, the preimage (when restructred to hp_finite) is the set of all heaps
      with (l-1) set to (Some _).
      This is a generator of the function sigma algebra.
     *)
  Admitted.

End hp.

Global Arguments fresh {_ _} _.

Section hpfuns.
  Local Open Scope classical_set_scope.
  Context {d} {T : measurableType d}.

  (** Stdpp instances for hp

      Note: These instances are possibly not what you want to use, because they
      uncurry the definitions so are not measurable.

      Could prove that the real definitions are extensionally equal to stdpp-looking ones though,
      to make porting the logic easier.
   *)

  Instance : PartialAlter <<discr loc>> T (hp (option T)) := {
      partial_alter f l h := hp_updateC (l, (f $ hp_evalC (l, h), h)) }.

End hpfuns.




(** The state: a [loc]-indexed heap of [val]s, and [loc]-indexed tapes, and [loc]-indexed utapes *)
Record state : Type := {
    state_v : ((hp (option val)) * (hp (option btape)) * (hp (option utape )))%type
}.

Definition prod_of_state (s : state) : ((hp (option val)) * (hp (option btape)) * (hp (option utape ))) :=
  match s with {| state_v := x |} => x end.

Definition state_of_prod (v : (hp (option val)) * (hp (option btape)) * (hp (option utape ))) : state :=
  {| state_v := v |}.

Lemma prod_of_state_of_prod p : prod_of_state (state_of_prod p) = p.
Proof. by rewrite /prod_of_state/state_of_prod//. Qed.

Lemma state_of_prod_of_state s : state_of_prod (prod_of_state s) = s.
Proof. destruct s. by rewrite /prod_of_state/state_of_prod//. Qed.

HB.instance Definition _ := gen_eqMixin state.
HB.instance Definition _ := gen_choiceMixin state.
HB.instance Definition _ := isPointed.Build state (state_of_prod point).

Definition state_measurable : set (set state) :=
  flip image (flip image state_of_prod) measurable.

Lemma state_display : measure_display.
Proof. done. Qed.

Lemma state_measurable_of_prod_measurable S : measurable S -> state_measurable (image S state_of_prod).
Proof.
  move=>HS.
  rewrite /state_measurable/image/flip//=.
  exists S; done.
Qed.

Lemma prod_measurable_of_state_measurable {S} :
  state_measurable S -> measurable (image S prod_of_state).
Proof.
  intro HS.
  destruct HS as [S' HS' <-].
  rewrite image_comp.
  have -> : ssrfun.comp prod_of_state state_of_prod = (fun x => x).
  { apply functional_extensionality; intro x. by rewrite /ssrfun.comp prod_of_state_of_prod. }
  by rewrite image_id.
Qed.

Lemma state_meas0 : state_measurable set0.
Proof.
  have -> : (set0 : set state) = (image set0 state_of_prod).
  { apply functional_extensionality; intro x; apply propext.
    rewrite /image/state_of_prod/set0//=.
    split; [by move=>?|by move=>[??]].
  }
  by apply state_measurable_of_prod_measurable, @measurable0.
Qed.

Lemma state_measC X : (state_measurable X) -> state_measurable (~` X).
Proof.
  move=>H.
  (*
  destruct (exists_prod_measurable_of_state_measurable H) as [P [HP ->]].
  have -> : (~` [set state_of_prod x | x in P]) = image (~` P) state_of_prod.
  { apply functional_extensionality; intro x; apply propext.
    admit. }
  apply state_measurable_of_prod_measurable.
  by apply measurableC, HP. *)
Admitted.

Lemma state_measU (F : sequences.sequence (set state)) : (forall i, state_measurable (F i)) -> state_measurable (\bigcup_i F i).
Proof.
  intro H.
Admitted.

HB.instance Definition _ :=
  @isMeasurable.Build state_display state state_measurable state_meas0 state_measC state_measU.

(*
Definition state_lift_fun {d} {T : measurableType d} f : state -> T := ssrfun.comp f prod_of_state.
*)

Definition state_lift_set D : set state := image D state_of_prod.

Lemma prod_of_state_meas D (H : measurable D) : measurable_fun D prod_of_state.
Proof.
  intros HD Y HY.
  have -> : (D `&` prod_of_state @^-1` Y) = (image (setI (image D prod_of_state) Y) state_of_prod).
  { rewrite /setI/image//=.
    apply functional_extensionality; intro y; apply propext; split; rewrite //=.
    { move=>[??].
      eexists (prod_of_state y); last by rewrite state_of_prod_of_state.
      split; [|done].
      eexists _; done. }
    { move=> [? [+ +]]. move=> [? ?] H1 H2 <-.
      rewrite prod_of_state_of_prod.
      split; last done.
      rewrite <-H1.
      rewrite state_of_prod_of_state.
      done. } }
  apply state_measurable_of_prod_measurable.
  apply measurableI.
  { by apply prod_measurable_of_state_measurable. }
  { done. }
Qed.

Lemma state_of_prod_meas D (H : measurable D) : measurable_fun D state_of_prod.
Proof.
  intros HD Y HY.
  have -> : (D `&` state_of_prod @^-1` Y) = (image (setI (image D state_of_prod) Y) prod_of_state).
  { rewrite /setI/image//=.
    apply functional_extensionality; intro y; apply propext; split; rewrite //=.
    { move=>[??].
      eexists (state_of_prod y); last by rewrite prod_of_state_of_prod.
      split; [|done].
      eexists _; done. }
    { move=> [? [+ +]]. move=> [? ?] H1 H2 <-.
      rewrite state_of_prod_of_state.
      split; last done.
      rewrite <-H1.
      rewrite prod_of_state_of_prod.
      done. } }
  apply prod_measurable_of_state_measurable.
  suffices HM : measurable ([set state_of_prod x | x in D] `&` Y) by done.
  apply measurableI.
  { by apply state_measurable_of_prod_measurable. }
  { done. }
Qed.


(*
Definition state_lift_fun_meas {d} {T : measurableType d} (f : _ -> T) D (HD : measurable D) (H : measurable_fun D f) :
    measurable_fun (state_lift_set D) (state_lift_fun f).
Proof.
  intros H1 Y HY.
  have -> :  (state_lift_set D `&` state_lift_fun f @^-1` Y) = (image (D `&` f @^-1` Y) state_of_prod).
  { rewrite /image/setI/preimage/state_lift_fun/state_lift_set/state_of_prod//=.
    apply functional_extensionality; intro y; apply propext; split; rewrite //=.
    { move=>[[??]<-].
      rewrite prod_of_state_of_state.
      move=>?. by eexists _. }
    { move=>[?[??]]<-.
      split; [eexists _; done|].
      by rewrite prod_of_state_of_state. }
  }
  by apply state_measurable_of_prod_measurable, (H HD), HY.
Qed.
*)

Definition heap : state -> hp (option val) := ssrfun.comp (ssrfun.comp fst fst) prod_of_state.
Lemma heap_meas : measurable_fun setT heap.
Proof.
  eapply (@measurable_comp _ _ _ _ _ _ setT (ssrfun.comp fst fst) setT prod_of_state); simpl.
  { by eapply @measurableT. }
  { done. }
  { eapply measurable_comp.
    { by eapply @measurableT. }
    { done. }
    { by apply @measurable_fst. }
    { by apply @measurable_fst. }
  }
  { eapply prod_of_state_meas. by apply @measurableT. }
Qed.
Hint Resolve heap_meas : measlang.

Definition tapes  : state -> hp (option btape) := ssrfun.comp (ssrfun.comp snd fst) prod_of_state.
Lemma tapes_meas : measurable_fun setT tapes.
Proof.
  eapply (@measurable_comp _ _ _ _ _ _ setT (ssrfun.comp snd fst) setT prod_of_state); simpl.
  { by eapply @measurableT. }
  { done. }
  { eapply measurable_comp.
    { by eapply @measurableT. }
    { done. }
    { by apply @measurable_snd. }
    { by apply @measurable_fst. }
  }
  { eapply prod_of_state_meas. by apply @measurableT. }
Qed.
Hint Resolve tapes_meas : measlang.

Definition utapes : state -> hp (option utape) := ssrfun.comp snd prod_of_state.
Lemma utapes_meas : measurable_fun setT utapes.
Proof.
  eapply (@measurable_comp _ _ _ _ _ _ setT snd setT prod_of_state); simpl.
  { by eapply @measurableT. }
  { done. }
  { by eapply @measurable_snd. }
  { eapply prod_of_state_meas. by apply @measurableT. }
Qed.
Hint Resolve utapes_meas : measlang.

(** Operations on states *)

Definition state_upd_heap (f : hp (option val) -> hp (option val)) : state -> state :=
  ssrfun.comp state_of_prod $
  mProd (mProd (ssrfun.comp f heap) tapes) utapes.

Lemma state_upd_heap_meas f (H : measurable_fun setT f) : measurable_fun setT (state_upd_heap f).
Proof.
  eapply (@measurable_comp _ _ _ _ _ _ setT state_of_prod  setT _).
  { by eapply @measurableT. }
  { done. }
  { by apply state_of_prod_meas. }
  mcrunch_prod.
  { mcrunch_prod.
    { eapply @measurable_comp; [by eapply @measurableT|done| |].
      { done. }
      { by apply heap_meas.  }
    }
    { by apply tapes_meas. }
  }
  { by apply utapes_meas. }
Qed.
Hint Resolve state_upd_heap_meas : measlang.

Definition state_upd_tapes (f : hp (option btape) -> hp (option btape)) : state -> state :=
  ssrfun.comp state_of_prod $
  mProd (mProd heap (ssrfun.comp f tapes)) utapes.

Lemma state_upd_tapes_meas f (H : measurable_fun setT f) : measurable_fun setT (state_upd_tapes f).
Proof.
  eapply (@measurable_comp _ _ _ _ _ _ setT state_of_prod  setT _).
  { by eapply @measurableT. }
  { done. }
  { by apply state_of_prod_meas. }
  mcrunch_prod.
  { mcrunch_prod.
    { by apply heap_meas.  }
    { eapply @measurable_comp; [by eapply @measurableT|done| |].
      { done. }
      { by apply tapes_meas. }
    }
  }
  { by apply utapes_meas. }
Qed.
Hint Resolve state_upd_tapes_meas : measlang.

Definition state_upd_utapes (f : hp (option utape) -> hp (option utape)) : state -> state :=
  ssrfun.comp state_of_prod $
  mProd (mProd heap tapes) (ssrfun.comp f utapes).

Lemma state_upd_utapes_meas f (H : measurable_fun setT f) : measurable_fun setT (state_upd_utapes f).
Proof.
  eapply (@measurable_comp _ _ _ _ _ _ setT state_of_prod  setT _).
  { by eapply @measurableT. }
  { done. }
  { by apply state_of_prod_meas. }
  mcrunch_prod.
  { mcrunch_prod.
    { by apply heap_meas.  }
    { by apply tapes_meas. }
  }
  { eapply @measurable_comp; [by eapply @measurableT|done| |].
    { done. }
    { by apply utapes_meas. }
  }
Qed.
Hint Resolve state_upd_utapes_meas : measlang.

(*
Lemma state_upd_tapes_twice σ l xs ys :
  state_upd_tapes <[ l := ys ]> (state_upd_tapes <[ l := xs ]> σ) = state_upd_tapes <[ l:= ys ]> σ.
Proof. Admitted. (* rewrite /state_upd_tapes /=. f_equal. apply insert_insert. Qed. *)

Lemma state_upd_tapes_same σ σ' l xs ys :
  state_upd_tapes <[l:=ys]> σ = state_upd_tapes <[l:=xs]> σ' -> xs = ys.
Proof. rewrite /state_upd_tapes /=. intros K. simplify_eq.
       rewrite map_eq_iff in H.
       specialize (H l).
       rewrite !lookup_insert in H.
       by simplify_eq.
Qed.

Lemma state_upd_tapes_no_change σ l ys :
  tapes σ !! l = Some ys ->
  state_upd_tapes <[l := ys]> σ = σ .
Proof.
  destruct σ as [? t]. simpl.
  intros Ht.
  f_equal.
  (* apply insert_id. done. *)
Admitted.

(*
Lemma state_upd_tapes_same' σ σ' l n xs (x y : stdpp.fin.fin (S n)) :
  state_upd_tapes <[l:=(fin (n; xs++[x]))]> σ = state_upd_tapes <[l:=(fin(n; xs++[y]))]> σ' -> x = y.
Proof. intros H. apply state_upd_tapes_same in H. by simplify_eq. Qed.

Lemma state_upd_tapes_neq' σ σ' l n xs (x y : stdpp.fin.fin (S n)) :
  x≠y -> state_upd_tapes <[l:=(fin(n; xs++[x]))]> σ ≠ state_upd_tapes <[l:=(fin(n; xs++[y]))]> σ'.
Proof. move => H /state_upd_tapes_same ?. simplify_eq. Qed.
*)

Fixpoint heap_array (l : <<discr loc>>) (vs : list val) : gmap <<discr loc>> val :=
  match vs with
  | [] => ∅
  | v :: vs' => {[l := v]} ∪ heap_array (l +ₗ 1) vs'
  end.

Lemma heap_array_singleton l v : heap_array l [v] = {[l := v]}.
Proof. by rewrite /heap_array right_id. Qed.

Lemma heap_array_app l vs1 vs2 : heap_array l (vs1 ++ vs2) = (heap_array l vs1) ∪ (heap_array (l +ₗ (length vs1)) vs2) .
Proof.
  revert l.
  induction vs1; intro l.
  - simpl.
    rewrite map_empty_union loc_add_0 //.
  - rewrite -app_comm_cons /= IHvs1.
    rewrite map_union_assoc.
    do 2 f_equiv.
    rewrite Nat2Z.inj_succ /=.
    rewrite /Z.succ
      Z.add_comm
      loc_add_assoc //.
Qed.

Lemma heap_array_lookup l vs v k :
  heap_array l vs !! k = Some v ↔
  ∃ j, (0 ≤ j)%Z ∧ k = l +ₗ j ∧ vs !! (Z.to_nat j) = Some v.
Proof.
  revert k l; induction vs as [|v' vs IH] => l' l /=.
Admitted.
(*
  { rewrite lookup_empty. naive_solver lia. }
  rewrite -insert_union_singleton_l lookup_insert_Some IH. split.
  - intros [[-> ?] | (Hl & j & ? & -> & ?)].
    { eexists 0. rewrite loc_add_0. naive_solver lia. }
    eexists (1 + j)%Z. rewrite loc_add_assoc !Z.add_1_l Z2Nat.inj_succ; auto with lia.
  - intros (j & ? & -> & Hil). destruct (decide (j = 0)); simplify_eq/=.
    { rewrite loc_add_0; eauto. }
    right. split.
    { rewrite -{1}(loc_add_0 l). intros ?%(inj (loc_add _)); lia. }
    assert (Z.to_nat j = S (Z.to_nat (j - 1))) as Hj.
    { rewrite -Z2Nat.inj_succ; last lia. f_equal; lia. }
    rewrite Hj /= in Hil.
    eexists (j - 1)%Z. rewrite loc_add_assoc Z.add_sub_assoc Z.add_simpl_l.
    auto with lia.
Qed.
*)

Lemma heap_array_map_disjoint (h : gmap <<discr loc>> val) (l : loc) (vs : list val) :
  (∀ i, (0 ≤ i)%Z → (i < length vs)%Z → h !! (l +ₗ i) = None) →
  (heap_array l vs) ##ₘ h.
Proof.
  intros Hdisj. apply map_disjoint_spec=> l' v1 v2.
  intros (j&?&->&Hj%lookup_lt_Some%inj_lt)%heap_array_lookup.
  move: Hj. rewrite Z2Nat.id // => ?. by rewrite Hdisj.
Qed.
*)

(*
Definition state_upd_hp_N : (<<discr loc>> * <<discr Z>> * val * (hp (option val)))%type -> (hp (option val)).
Admitted.


Lemma
                              (l : loc) (n : nat) (v : val) (σ : state) : state :=
  state_upd_heap (λ h, heap_array l (replicate n v) ∪ h) σ.
*)



(*
Lemma state_upd_heap_singleton l v σ :
  state_upd_heap_N l 1 v σ = state_upd_heap <[l:= v]> σ.
Proof.
  destruct σ as [h p]. rewrite /state_upd_heap_N /=. f_equiv.
Admitted.
(*
  rewrite right_id insert_union_singleton_l. done.
Qed.
*)

Lemma state_upd_tapes_heap σ l1 l2 xs m v :
  state_upd_tapes <[l2:=xs]> (state_upd_heap_N l1 m v σ) =
  state_upd_heap_N l1 m v (state_upd_tapes <[l2:=xs]> σ).
Proof.
  by rewrite /state_upd_tapes /state_upd_heap_N /=.
Qed.

Lemma heap_array_replicate_S_end l v n :
  heap_array l (replicate (S n) v) = heap_array l (replicate n v) ∪ {[l +ₗ n:= v]}.
Proof.
  induction n.
  - simpl.
    rewrite map_union_empty.
    rewrite map_empty_union.
    by rewrite loc_add_0.
  - rewrite replicate_S_end
     heap_array_app
     IHn /=.
    rewrite map_union_empty replicate_length //.
Qed.
*)

Global Instance state_inhabited : Inhabited state := populate point.


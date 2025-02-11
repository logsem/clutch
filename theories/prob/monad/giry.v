(** Axioms of a the Giry Monad type (a sigma algebra for subdistributions) *)

From mathcomp Require Import all_ssreflect all_algebra finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
From mathcomp.analysis Require Import reals ereal signed normedtype esum numfun measure lebesgue_measure lebesgue_integral.
From Coq Require Import Logic.ClassicalEpsilon Psatz Logic.FunctionalExtensionality Reals.
From Coq Require Import Classes.Morphisms.

From HB Require Import structures.

From clutch.prob.monad Require Export prelude.
From clutch.prelude Require Import classical.

Import Coq.Logic.FunctionalExtensionality.
Import Coq.Relations.Relation_Definitions.
Import Coq.Classes.RelationClasses.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Default Proof Using "Type".




Section giryM_ax.
  Local Open Scope classical_set_scope.
  Context `{R : realType} `{d : measure_display} (T : measurableType d).

  Definition giryM : Type := @subprobability d T R.

  Axiom giry_measurable : set (set giryM).
  Axiom giry_measurable0 : giry_measurable set0.
  Axiom giry_measurableC : forall (S : set giryM),
    giry_measurable S -> giry_measurable (~` S).
  Axiom giry_measurableU : forall (A : sequences.sequence (set giryM)),
    (forall i : nat, giry_measurable (A i)) -> giry_measurable (\bigcup_i A i).

  Definition giry_display : measure_display.
  Proof. by constructor. Qed.

  Lemma mzero_setT : (@mzero d T R setT <= 1)%E.
  Proof. by rewrite /mzero/=. Qed.

  HB.instance Definition _ := gen_eqMixin giryM.
  HB.instance Definition _ := gen_choiceMixin giryM.
  HB.instance Definition _ := Measure_isSubProbability.Build _ _ _ (@mzero d T R) mzero_setT.
  HB.instance Definition _ := isPointed.Build giryM mzero.
  HB.instance Definition _ :=
    @isMeasurable.Build giry_display giryM giry_measurable
      giry_measurable0 giry_measurableC giry_measurableU.

End giryM_ax.



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


Definition degenerate {T : Type} : T -> T -> Prop := fun _ _ => True.

Section giry_eval.
  Local Open Scope classical_set_scope.
  Context `{R : realType} `{d : measure_display} {T : measurableType d}.
  Notation giryM := (giryM (R := R)).

  Axiom gEval : forall (S : set T), (d.-measurable S) -> (giryM T -> \bar R).
  Axiom gEval_measurable : forall (S : set T) (H : d.-measurable S), measurable_fun setT (gEval H).
  Axiom gEval_eval : forall (S : set T) (H : d.-measurable S) (μ : giryM T), gEval H μ = μ S.

End giry_eval.



Section giry_join.
  Local Open Scope classical_set_scope.
  Context `{R : realType} `{d : measure_display} {T : measurableType d}.
  Notation giryM := (giryM (R := R)).

  Axiom gJoin : giryM (giryM T) -> giryM T.
  Axiom gJoin_measurable : measurable_fun setT gJoin.
  Axiom gJoin_proper : (Proper (measure_eq ==> measure_eq) gJoin).
  Global Existing Instance gJoin_proper.

End giry_join.

Section giry_map.
  Local Open Scope classical_set_scope.
  Context `{R : realType} `{d1 : measure_display} `{d2 : measure_display}.
  Context {T1 : measurableType d1} {T2 : measurableType d2}.
  Notation giryM := (giryM (R := R)).

  Axiom gMap : forall (f : T1 -> T2), measurable_fun setT f -> (giryM T1 -> giryM T2).
  Axiom gMap_measurable : forall (f : T1 -> T2) (H : measurable_fun setT f), measurable_fun setT (gMap H).
  Axiom gMap_proper : forall (f : T1 -> T2) (H : measurable_fun setT f), (Proper (measure_eq ==> measure_eq) (gMap H)).
  Global Existing Instance gMap_proper.


End giry_map.

Section giry_ret.
  Local Open Scope classical_set_scope.
  Context `{R : realType} `{d : measure_display} {T : measurableType d}.
  Notation giryM := (giryM (R := R)).

  Axiom gRet : T -> giryM T.
  Axiom gRet_measurable : measurable_fun setT gRet.

End giry_ret.

Section giry_bind.
  Local Open Scope classical_set_scope.
  Context `{R : realType} `{d1 : measure_display} `{d2 : measure_display}.
  Context {T1 : measurableType d1} {T2 : measurableType d2}.
  Notation giryM := (giryM (R := R)).

  Definition gBind (f : T1 -> giryM T2) (H : measurable_fun setT f) : giryM T1 -> giryM T2 :=
    gJoin \o (gMap H).

  Lemma gBind_measurable (f : T1 -> giryM T2) (H : measurable_fun setT f) :  measurable_fun setT (gBind H).
  Proof.
    eapply (@measurable_comp _ _ _ _ _ _ setT).
    { by eapply @measurableT. }
    { by apply subsetT. }
    { by apply gJoin_measurable. }
    { by apply gMap_measurable. }
  Qed.

  Global Instance gBind_proper (f : T1 -> giryM T2) (H : measurable_fun setT f) : Proper (measure_eq ==> measure_eq) (gBind H).
  Proof.
    intros x y H'.
    rewrite /gBind.
    intros S HS.
    rewrite /ssrfun.comp.
    apply gJoin_proper; [|done].
    by apply gMap_proper.
  Qed.

End giry_bind.

Section giry_monad.
  Local Open Scope classical_set_scope.
  Context `{R : realType} `{d1 : measure_display} `{d2 : measure_display} `{d3 : measure_display}.
  Context {T1 : measurableType d1} {T2 : measurableType d2} {T3 : measurableType d3}.
  Notation giryM := (giryM (R := R)).


  Axiom gJoin_assoc : forall (x : giryM (giryM (giryM T1))),
    (gJoin \o (gMap gJoin_measurable)) x ≡μ (gJoin \o gJoin) x.

  Axiom gJoin_id1 : forall (x : giryM T1),
   (gJoin \o (gMap gRet_measurable)) x ≡μ (gJoin \o gRet) x.

  Axiom gJoin_id2 : forall (x : giryM (giryM T1)) (f : T1 -> T2) (H : measurable_fun setT f),
    (gJoin \o gMap (gMap_measurable H)) x ≡μ (gMap H \o gJoin) x.

  (*
    Laws in terms of ret and bind

  Axiom gRet_gBind : forall (t : T1) (f : T1 -> giryM T2) (H : measurable_fun setT f),
    gBind H (gRet t) ≡μ f t.

  Axiom gBind_gRet : forall (t : giryM T1),
    gBind gRet_measurable t ≡μ t.

  Context (f : T1 -> giryM T2).
  Context (g : T2 -> giryM T3).
  Context (Hf : measurable_fun setT f).
  Context (Hg : measurable_fun setT g).
  Context (t : giryM T1).

  Lemma Hfg : measurable_fun setT (gBind Hg \o f).
  Proof using Hf Hg R T1 T2 T3 d1 d2 d3 f g.
    eapply (@measurable_comp _ _ _ _ _ _ setT).
    { by eapply @measurableT. }
    { by apply subsetT. }
    { by apply gBind_measurable. }
    { by apply Hf. }
  Qed.

  Axiom gBind_assoc : gBind Hg (gBind Hf t) ≡μ gBind Hfg t.
   *)

End giry_monad.

Section giry_zero.
  Local Open Scope classical_set_scope.
  Context `{R : realType}.
  Notation giryM := (giryM (R := R)).

  Section giry_zero_def.
    Context `{d1 : measure_display} {T1 : measurableType d1}.
    Axiom gZero : giryM T1.
  End giry_zero_def.

  Context `{d1 : measure_display} `{d2 : measure_display} {T1 : measurableType d1} {T2 : measurableType d2}.

  Axiom gZero_map : forall (f : T1 -> T2) (H : measurable_fun setT f),
    gMap H gZero ≡μ (gZero : giryM T2).

End giry_zero.

Section giry_external_map.
  Local Open Scope classical_set_scope.
  Context `{R : realType} `{d1 : measure_display} `{d2 : measure_display}.
  Context {T1 : measurableType d1} {T2 : measurableType d2}.
  Notation giryM := (giryM (R := R)).

  Definition gMap' (f : T1 -> T2) : giryM T1 -> giryM T2 :=
    extern_if (cst gZero) (fun h : measurable_fun setT f => gMap h).

  Lemma gMap'_measurable (f : T1 -> T2) (H : measurable_fun setT f) : measurable_fun setT (gMap' f).
  Proof. by rewrite /gMap' extern_if_eq; apply gMap_measurable. Qed.

  Global Instance gMap'_proper : Proper (eq ==> measure_eq ==> measure_eq) gMap'.
  Proof.
    intros f ? <-.
    destruct (ExcludedMiddle (measurable_fun setT f)) as [E|E].
    { by rewrite /gMap' extern_if_eq; apply gMap_proper. }
    { by rewrite /gMap' extern_if_neq. }
  Qed.

End giry_external_map.

Section giry_external_bind.
  Local Open Scope classical_set_scope.
  Context `{R : realType} `{d1 : measure_display} `{d2 : measure_display}.
  Context {T1 : measurableType d1} {T2 : measurableType d2}.
  Notation giryM := (giryM (R := R)).

  Definition gBind' (f : T1 -> giryM T2) : giryM T1 -> giryM T2 :=
    gJoin \o (gMap' f).

  Lemma gBind'_measurable (f : T1 -> giryM T2) (H : measurable_fun setT f) : measurable_fun setT (gBind' f).
  Proof. by rewrite /gBind'/gMap' extern_if_eq; apply gBind_measurable. Qed.


  (*  Program Definition gBind'' : (<<discr (T1 -> giryM T2)>> * giryM T1)%type -> giryM T2 := *)


End giry_external_bind.






Section giry_prod.
  Local Open Scope classical_set_scope.
  Context `{R : realType} `{d1 : measure_display} `{d2 : measure_display}.
  Context {T1 : measurableType d1} {T2 : measurableType d2}.
  Notation giryM := (giryM (R := R)).



  Check giryM (<<discr (T1 -> T2)>>).

  (* https://en.wikipedia.org/wiki/Giry_monad#Product_distributions  *)

  Axiom gProd : (giryM T1 * giryM T2) -> giryM (T1 * T2)%type.
  (*  gBind' (fun v1 => gBind' (gRet \o (pair v1)) (snd μ)) (fst μ). *)

  Axiom gProd_measurable : measurable_fun setT gProd.

  (*
  Lemma gProd_measurable : measurable_fun setT gProd.
  Proof.
    have HM1 (v1 : T1) : measurable_fun setT (gRet \o (pair v1) : T2 -> giryM (T1 * T2)%type).
    { eapply (@measurable_comp _ _ _ _ _ _ setT).
      { by eapply @measurableT. }
      { by apply subsetT. }
      { by apply gRet_measurable. }
      { by apply measurable_pair1. }
    }
    rewrite /gProd.
    intros _ Y HY.
    rewrite setTI/preimage//=.
  Abort.
   *)

End giry_prod.

(*
Definition giryM_ap {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2} :
  (giryM T1 * giryM T2)%type -> giryM (T1 * T2)%type :=
  fun X =>
    (ssrfun.comp
       (giryM_bind_external ^~ (fun x => ((giryM_bind_external ^~ (fun y => giryM_ret (x, y))) (snd X))))
       fst) X.

(*
Check fun X => (giryM_bind_external (fst X) (fun x => (giryM_bind_external (snd X) (fun y => giryM_ret (x, y))))).
*)
(*  \xy -> (fst xy) >>= (\x -> (snd xy) >>= (\y -> ret (x, y))) *)
(* liftM2 (>>=) fst ((. ((ret .) . (,))) . (>>=) . snd)  *)

Lemma giryM_ap_meas {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2} :
    measurable_fun setT (@giryM_ap _ _ T1 T2).
Proof.
  unfold giryM_ap.
Admitted.
*)



Section giry_iterM.
  Local Open Scope classical_set_scope.
  Context `{R : realType}.
  Notation giryM := (giryM (R := R)).
  Context {d} {T : measurableType d}.

  Fixpoint gIter (n : nat) (f : T -> giryM T) : T -> giryM T
    := match n with
         O => gRet
       | (S n) => fun a => gBind' (gIter n f) (f a)
       end.

  Lemma giryM_iterN_zero (f : T -> giryM T) : gIter 0 f = gRet.
  Proof. done. Qed.

  (*
  Lemma giryM_iterN_S_rev_eq n (f : T -> giryM T) :
    (fun a => giryM_bind_external (f a) (giryM_iterN n f)) = (ssrfun.comp (giryM_bind_external^~ f) (giryM_iterN n f)).
  Proof.
  Admitted.
  (*
    apply functional_extensionality.
    intro a.
    rewrite /ssrfun.comp//=.
    induction n.
    { rewrite giryM_iterN_zero. admit. }
    simpl.
    rewrite IHn.
    *)

  Lemma giryM_iterN_S_rev n (f : T -> giryM T) :
    giryM_iterN (S n) f = ssrfun.comp (giryM_bind_external^~ f) (giryM_iterN n f).
  Proof. by rewrite <- giryM_iterN_S_rev_eq. Qed.
*)

  Lemma gIter_measurable (f : T -> giryM T) (HF : measurable_fun setT f) :
      forall n, measurable_fun setT (gIter n f).
  Proof.
    induction n.
    { by rewrite giryM_iterN_zero; apply gRet_measurable. }
    { admit.
      (*
      rewrite giryM_iterN_S_rev.
      eapply @measurable_comp.
      { by eapply @measurableT. }
      { done. }
      { by apply giryM_bind_external'_meas. }
      { done. }
    }
  Qed.
*)
  Admitted.

End giry_iterM.


Section giry_is_zero.
  Local Open Scope classical_set_scope.
  Context `{R : realType}.
  Notation giryM := (giryM (R := R)).
  Context {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}.

  Definition is_zero {d} {T : measurableType d} (s : giryM T) : Prop := s ≡μ gZero.

  Lemma is_zero_gMap' (m : giryM T1) (f : T1 -> T2) (H : measurable_fun setT f) : is_zero m -> is_zero (gMap' f m).
  Proof.
    unfold is_zero; move=>->.
    rewrite /gMap' extern_if_eq.
    by apply gZero_map.
  Qed.

End giry_is_zero.

Section giry_is_prob.
  Local Open Scope classical_set_scope.
  Context `{R : realType}.
  Notation giryM := (giryM (R := R)).

  Definition is_prob  {d} {T : measurableType d} (s : giryM T) : Prop := s [set: T] = 1%E.

End giry_is_prob.

Section giry_has_support_in.
  Local Open Scope classical_set_scope.
  Context `{R : realType}.
  Notation giryM := (giryM (R := R)).
  Context {d} {T : measurableType d}.

  Definition mass (μ : giryM T) (S : set T) (_ : d.-measurable S) : \bar R :=
    (\int[μ]_(x in S) 1)%E.

  (* This may be redundant due to the behavior of \int on non-measurable sets, but we should
     fix it to zero for when we axiomatize. *)
  Definition mass' (μ : giryM T) (S : set T) : \bar R :=
    extern_if 0%E (fun (h : d.-measurable S) => mass μ h).

  Definition has_support_in (μ : giryM T) (S : set T) : Prop := mass' μ S = mass' μ setT.

End giry_has_support_in.

Section giry_is_det.
  Local Open Scope classical_set_scope.
  Context `{R : realType}.
  Notation giryM := (giryM (R := R)).
  Context {d} {T : measurableType d}.

  Definition is_det (t : T) (μ : giryM T) : Prop :=
    has_support_in μ [set t].

End giry_is_det.

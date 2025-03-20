(** Axioms of a the Giry Monad type (a sigma algebra for subdistributions) *)
From mathcomp Require Import all_ssreflect all_algebra boolp classical_sets functions.
From mathcomp.analysis Require Import reals ereal measure lebesgue_measure lebesgue_integral Rstruct.
From clutch.prob.monad Require Export prelude.
From clutch.prelude Require Import classical.
Import Coq.Relations.Relation_Definitions.
From Coq Require Import Classes.Morphisms Reals.
From HB Require Import structures.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Default Proof Using "Type".

Section giryM_ax.
  Local Open Scope classical_set_scope.
  Context `{d : measure_display} (T : measurableType d).

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



Definition measure_eq `{d : measure_display} {T : measurableType d} : relation (giryM T) :=
  fun μ1 μ2 => forall (S : set T), measurable S -> μ1 S = μ2 S.
Notation "x ≡μ y" := (measure_eq x y) (at level 70).
Global Hint Extern 0 (_ ≡μ _) => reflexivity : core.
Global Hint Extern 0 (_ ≡μ _) => symmetry; assumption : core.

Instance equivalence_measure_eq `{d : measure_display} {T : measurableType d} :
  Equivalence (@measure_eq d T).
Proof.
  constructor.
  - done.
  - rewrite /Symmetric.
    intros ? ? H ? ?.
    by rewrite H //=.
  - intros ? ? ? H0 H1 ? ?.
    by rewrite H0 //= H1 //=.
Qed.

Section giry_eval.
  Local Open Scope classical_set_scope.
  Context `{d : measure_display} {T : measurableType d}.

  Axiom gEval : forall (S : set T), (d.-measurable S) -> (giryM T -> \bar R).
  Axiom gEval_meas_fun : forall (S : set T) (H : d.-measurable S), measurable_fun setT (gEval H).
  Axiom gEval_eval : forall (S : set T) (H : d.-measurable S) (μ : giryM T), gEval H μ = μ S.

End giry_eval.


Section giry_integral.
  Local Open Scope classical_set_scope.
  Local Open Scope ereal_scope.
  Context `{d : measure_display} {T : measurableType d}.

  (* TODO: Check if additional conditions on f are needed *)
  Axiom gInt : forall (f : T -> \bar R), (measurable_fun setT f) -> (giryM T -> \bar R).
  Axiom gInt_meas_fun : forall (f : T -> \bar R) (H : measurable_fun setT f), measurable_fun setT (gInt H).
  Axiom gInt_eval : forall (f : T -> \bar R) (H : measurable_fun setT f) (μ : giryM T), gInt H μ = (\int[μ]_x f x).

End giry_integral.

Section giry_join.
  Local Open Scope classical_set_scope.
  Context `{d : measure_display} {T : measurableType d}.

  Axiom gJoin : giryM (giryM T) -> giryM T.
  Axiom gJoin_meas_fun : measurable_fun setT gJoin.
  Axiom gJoin_proper : (Proper (measure_eq ==> measure_eq) gJoin).
  Global Existing Instance gJoin_proper.

End giry_join.

Section giry_map.
  Local Open Scope classical_set_scope.
  Context `{d1 : measure_display} `{d2 : measure_display}.
  Context {T1 : measurableType d1} {T2 : measurableType d2}.

  Axiom gMap : forall (f : T1 -> T2), measurable_fun setT f -> (giryM T1 -> giryM T2).
  Axiom gMap_meas_fun : forall (f : T1 -> T2) (H : measurable_fun setT f), measurable_fun setT (gMap H).
  Axiom gMap_proper : forall (f : T1 -> T2) (H : measurable_fun setT f), (Proper (measure_eq ==> measure_eq) (gMap H)).
  Global Existing Instance gMap_proper.


End giry_map.

Section giry_ret.
  Local Open Scope classical_set_scope.
  Context `{d : measure_display} {T : measurableType d}.

  Axiom gRet : T -> giryM T.
  Axiom gRet_meas_fun : measurable_fun setT gRet.
  (** Use bool_decide or as_bool? *)
  (* Axiom gRet_eval : forall S x (H: d.-measurable S), gRet x S = if (S x) then 1%E else 0%E. *)

End giry_ret.

Section giry_bind.
  Local Open Scope classical_set_scope.
  Context `{d1 : measure_display} `{d2 : measure_display}.
  Context {T1 : measurableType d1} {T2 : measurableType d2}.

  Definition gBind (f : T1 -> giryM T2) (H : measurable_fun setT f) : giryM T1 -> giryM T2 :=
    gJoin \o (gMap H).

  Lemma gBind_meas_fun (f : T1 -> giryM T2) (H : measurable_fun setT f) :  measurable_fun setT (gBind H).
  Proof.
    eapply (@measurable_comp _ _ _ _ _ _ setT).
    { by eapply @measurableT. }
    { by apply subsetT. }
    { by apply gJoin_meas_fun. }
    { by apply gMap_meas_fun. }
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
  Local Open Scope ereal_scope.
  Context `{d1 : measure_display} `{d2 : measure_display} `{d3 : measure_display}.
  Context {T1 : measurableType d1} {T2 : measurableType d2} {T3 : measurableType d3}.

  Axiom gJoin_assoc : forall (x : giryM (giryM (giryM T1))),
    (gJoin \o (gMap gJoin_meas_fun)) x ≡μ (gJoin \o gJoin) x.

  Axiom gJoin_id1 : forall (x : giryM T1),
   (gJoin \o (gMap gRet_meas_fun)) x ≡μ (gJoin \o gRet) x.

  Axiom gJoin_id2 : forall (x : giryM (giryM T1)) (f : T1 -> T2) (H : measurable_fun setT f),
    (gJoin \o gMap (gMap_meas_fun H)) x ≡μ (gMap H \o gJoin) x.


  Axiom gRetInt : forall (x : T1) (f : T1 -> \bar R) (H : measurable_fun setT f),
      gInt H (gRet x) = f x.

  Lemma gRetInt_rw (x : T1) (f : T1 -> \bar R) (H : measurable_fun setT f) :
      \int[gRet x]_x f x = f x.
  Proof.
    rewrite -gInt_eval.
    apply gRetInt.
  Qed.

  Lemma gBindInt_meas_fun (μ : giryM T1) (f : T1 -> giryM T2) (H : measurable_fun setT f) (h : T2 -> \bar R)
                          (mh : measurable_fun setT h) :
      measurable_fun setT (fun x => gInt mh (f x)).
  Proof.
    eapply (@measurable_comp _ _ _ _ _ _ setT).
    { by eapply @measurableT. }
    { by apply subsetT. }
    { by apply gInt_meas_fun. }
    { by apply H. }
  Qed.

  Axiom gBindInt : forall (μ : giryM T1) (f : T1 -> giryM T2) (H : measurable_fun setT f) (h : T2 -> \bar R) (mh : measurable_fun setT h),
      gInt mh (gBind H μ) = gInt (gBindInt_meas_fun μ H mh) μ.

  (* TODO : Cleaner proof? *)
  Lemma gBindInt_rw (μ : giryM T1) (f : T1 -> giryM T2) (H : measurable_fun setT f) (h : T2 -> \bar R) (mh : measurable_fun setT h) :
    \int[gBind H μ]_y h y = \int[μ]_x \int[f x]_y  h y.
  Proof.
    pose proof (gBindInt μ H mh) as Haux.
    do 2 rewrite gInt_eval in Haux.
    rewrite Haux.
    f_equal.
    apply functional_extensionality.
    intros.
    rewrite gInt_eval //.
  Qed.

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

  Section giry_zero_def.
    Context `{d1 : measure_display} {T1 : measurableType d1}.
    Axiom gZero : giryM T1.
    Axiom gZero_eval : forall S (H: d1.-measurable S), gZero S = (0% E).
  End giry_zero_def.

  Context `{d1 : measure_display} `{d2 : measure_display} {T1 : measurableType d1} {T2 : measurableType d2}.

  Axiom gZero_map : forall (f : T1 -> T2) (H : measurable_fun setT f),
    gMap H gZero ≡μ (gZero : giryM T2).

End giry_zero.

Section giry_external_map.
  Local Open Scope classical_set_scope.
  Context `{d1 : measure_display} `{d2 : measure_display}.
  Context {T1 : measurableType d1} {T2 : measurableType d2}.

  Definition gMap' (f : T1 -> T2) : giryM T1 -> giryM T2 :=
    extern_if (cst gZero) (fun h : measurable_fun setT f => gMap h).

  Lemma gMap'_meas_fun (f : T1 -> T2) (H : measurable_fun setT f) : measurable_fun setT (gMap' f).
  Proof. by rewrite /gMap' extern_if_eq; apply gMap_meas_fun. Qed.

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
  Context `{d1 : measure_display} `{d2 : measure_display}.
  Context {T1 : measurableType d1} {T2 : measurableType d2}.

  Definition gBind' (f : T1 -> giryM T2) : giryM T1 -> giryM T2 :=
    gJoin \o (gMap' f).

  Lemma gBind'_meas_fun (f : T1 -> giryM T2) (H : measurable_fun setT f) : measurable_fun setT (gBind' f).
  Proof. by rewrite /gBind'/gMap' extern_if_eq; apply gBind_meas_fun. Qed.

End giry_external_bind.


Section giry_prod.
  Local Open Scope classical_set_scope.
  Context `{d1 : measure_display} `{d2 : measure_display}.
  Context {T1 : measurableType d1} {T2 : measurableType d2}.

  (* https://en.wikipedia.org/wiki/Giry_monad#Product_distributions  *)
  Axiom gProd : (giryM T1 * giryM T2) -> giryM (T1 * T2)%type.
  (*  gBind' (fun v1 => gBind' (gRet \o (pair v1)) (snd μ)) (fst μ). *)

  Axiom gProd_meas_fun : measurable_fun setT gProd.

End giry_prod.


Section giry_iterM.
  Local Open Scope classical_set_scope.
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

  Lemma gIter_meas_fun (f : T -> giryM T) (HF : measurable_fun setT f) :
      forall n, measurable_fun setT (gIter n f).
  Proof.
    induction n.
    { by rewrite giryM_iterN_zero; apply gRet_meas_fun. }
    { simpl.
      assert ((fun a : T => gBind' (gIter n f) (f a)) = ((gBind' (gIter n f ))\o f)) as Hrewrite.
      { by apply functional_extensionality_dep. }
      rewrite Hrewrite.
      eapply measurable_comp; [| |by apply gBind'_meas_fun|done]; last first.
      - done.
      - eapply @measurableT.
    }
  Qed.

End giry_iterM.


Section giry_is_zero.
  Local Open Scope classical_set_scope.
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

  Definition is_prob  {d} {T : measurableType d} (s : giryM T) : Prop := s [set: T] = 1%E.

  Lemma is_prob_gRet {d} {T : measurableType d} (x:T) : is_prob (gRet x).
  Proof.
  Admitted.
  
End giry_is_prob.

Section giry_has_support_in.
  Local Open Scope classical_set_scope.
  Context {d} {T : measurableType d}.

  Definition mass (μ : giryM T) (S : set T) (_ : d.-measurable S) : \bar R :=
    (\int[μ]_(x in S) 1)%E.

  (* This may be redundant due to the behavior of \int on non-measurable sets, but we should
     fix it to zero for when we axiomatize. *)
  Definition mass' (μ : giryM T) (S : set T) : \bar R :=
    extern_if 0%E (fun (h : d.-measurable S) => mass μ h).
  
  Lemma mass'_subset (μ : giryM T) (S1 S2 : set T):
    d.-measurable S1 -> d.-measurable S2 -> S1 `<=` S2 -> (mass' μ S1 <= mass' μ S2)%E.
  Proof.
    rewrite /mass'.
    intros ?? H1.
    rewrite !extern_if_eq.
    rewrite /mass.
    by apply ge0_subset_integral.
  Qed.

  Definition has_support_in (μ : giryM T) (S : set T) : Prop := mass' μ S = mass' μ setT.

  Lemma has_support_in_subset (μ : giryM T) (S1 S2 : set T) :
    d.-measurable S1 -> d.-measurable S2 -> S1 `<=` S2 -> has_support_in μ S1 -> has_support_in μ S2.
  Proof.
    rewrite /has_support_in.
    intros ?? H1 H2.
    unshelve epose proof @mass'_subset μ S1 S2 _ _ H1; try done.
    epose proof @mass'_subset μ S2 ([set:T]) _ _ _; try done.
    (* sandwich of extended R? *)
    
  Admitted.
    
    
              
    
End giry_has_support_in.

Section giry_is_det.
  Local Open Scope classical_set_scope.
  Context {d} {T : measurableType d}.

  Definition is_det (t : T) (μ : giryM T) : Prop :=
    has_support_in μ [set t].

End giry_is_det.

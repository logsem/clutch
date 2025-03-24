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

Section giryM_def.
  Local Open Scope classical_set_scope.
  Context `{d : measure_display} (T : measurableType d).

  Definition giryM : Type := @subprobability d T R.

  Definition gEval (S : set T) (μ : giryM) := μ S.
  Definition gEvalPreImg (S : set T) := (preimage_class setT (gEval S) measurable).

  Definition giry_measurable := <<s \bigcup_(S in measurable) (gEvalPreImg S)>>.

  (*  Axiom giry_measurable : set (set giryM). *)
  Lemma giry_measurable0 : giry_measurable set0.
    Proof.
      apply sigma_algebra0.
  Qed.

  Lemma giry_measurableC : forall (S : set giryM),
    giry_measurable S -> giry_measurable (~` S).
  Proof.
    intros ? ?.
    rewrite -setTD.
    apply sigma_algebraCD.
    auto.
  Qed.

 Lemma giry_measurableU : forall (A : sequences.sequence (set giryM)),
    (forall i : nat, giry_measurable (A i)) -> giry_measurable (\bigcup_i A i).
 Proof.
   apply sigma_algebra_bigcup.
 Qed.

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

End giryM_def.



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

  Lemma gEval_meas_fun : forall (S : set T) (H : d.-measurable S), measurable_fun setT (gEval S).
  Proof.
    intros S HmS.
    simpl.
    eapply (@measurability giry_display _ (giryM T) _ setT (gEval S)).
    {
      rewrite smallest_id; auto.
      simpl.
      apply sigma_algebra_measurable.
    }
    rewrite /giry_display.-measurable /= /giry_measurable /=.
    eapply subset_trans; [  | apply sub_gen_smallest].
    eapply subset_trans; [  | apply bigcup_sup]; eauto.
    rewrite /gEvalPreImg.
    apply subset_refl.
  Qed.

  (*
  Lemma gEval_eval : forall (S : set T) (H : d.-measurable S) (μ : giryM T), gEval H μ = μ S.
  *)

End giry_eval.


Section giry_integral.
  Local Open Scope classical_set_scope.
  Local Open Scope ereal_scope.
  Context `{d : measure_display} {T : measurableType d}.

  (* TODO: Check if additional conditions on f are needed *)
  Definition gInt (f : T -> \bar R) (Hmf : measurable_fun setT f) (Hfge0 : forall x, 0 <= f x) (μ : giryM T) := (\int[μ]_x f x).

  Lemma gInt_meas_fun : forall (f : T -> \bar R) (Hmf : measurable_fun setT f) (Hfge0 : forall x, 0 <= f x),
      measurable_fun setT (gInt Hmf Hfge0).
    Proof.
      (*
        The idea is to reconstruct f from simple functions, then use
        measurability of gEval. See "Codensity and the Giry monad", Avery

        TODO: The proof could be cleaner
       *)
      intros f Hmf Hfge0.
      rewrite /gInt.

      have HTmeas : d.-measurable [set: T]; auto.
      have Hfge0' : (forall t, [set: T] t -> 0 <= f t); auto.

      (* f is the limit of a monotone sequence of simple functions *)
      pose proof (approximation HTmeas Hmf Hfge0') as [g [Hgmono Hgconv]].

      set gE := (fun n => EFin \o (g n)).
      have HgEmeas : (forall n : nat, measurable_fun [set: T] (gE n)).
      {
        intro.
        rewrite /gE /=.
        apply EFin_measurable_fun; auto.
      }
      have HgEge0: (forall (n : nat) (x : T), [set: T] x -> 0 <= gE n x).
      {
        intros.
        rewrite /gE /= //.
        apply g.
      }
      have HgEmono : (forall x: T, [set: T] x -> {homo gE^~ x : n m / (Order.le n m) >-> n <= m}).
      {
        intros x Hx n m Hnm.
        apply lee_tofin.
        pose (lefP _ _ (Hgmono n m Hnm)); auto.
      }

      (* By MCT, limit of the integrals of g_n is the integral of the limit of g_n *)
      have Hcvg := (cvg_monotone_convergence _ HgEmeas HgEge0 HgEmono).

      set gInt := (fun n => (fun μ => \int[μ]_x (gE n) x )).
      have HgIntmeas : (forall n : nat, measurable_fun [set: giryM T] (gInt n)).
      {
        intro n.
        rewrite /gInt /gE /=.
        eapply eq_measurable_fun.
        intros μ Hμ.
        rewrite integralT_nnsfun sintegralE //.
        apply emeasurable_fun_fsum; auto.
        intros r.
        have Hrmeas : d.-measurable (preimage (g n) (set1 r)); auto.
        apply (measurable_funeM (r%:E)).
        have : measurable_fun [set: giryM T] (fun x : giryM T => x (g n @^-1` [set r])); auto.
        eapply eq_measurable_fun.
        intros ? ?.
        auto.
        apply gEval_meas_fun; auto.
      }
      (* The μ ↦ int[mu] lim g_n is measurable if every μ ↦ int[mu] g_n is measurable *)
      apply (emeasurable_fun_cvg _ (fun (μ : giryM T) => \int[μ]_x f x) HgIntmeas).
      intros μ Hμ.
      rewrite /gInt /=.
      erewrite (eq_integral _ f); [apply (Hcvg μ HTmeas) |].
      intros x Hx.
      have HxT : [set: T] x; [auto |].
      specialize (Hgconv x HxT).
      rewrite (topology.cvg_unique _
                 Hgconv (topology.cvgP _ Hgconv)) //.
   Qed.

  (*
  Axiom gInt_eval : forall (f : T -> \bar R) (H : measurable_fun setT f) (μ : giryM T), gInt H μ = (\int[μ]_x f x).
  *)

End giry_integral.


Section giry_map.
  Local Open Scope classical_set_scope.
  Context `{d1 : measure_display} `{d2 : measure_display}.
  Context {T1 : measurableType d1} {T2 : measurableType d2}.

  Variables (f : T1 -> T2) (Hmf : measurable_fun setT f) (μ1 : giryM T1).

  Definition gMap_ev := pushforward μ1 Hmf.

  Let gMap0 : gMap_ev set0 = 0%E.
  Proof.
    rewrite /gMap_ev measure0 //.
  Qed.

  Let gMap_ge0 A : (0 <= gMap_ev A)%E.
  Proof.
    rewrite /gMap_ev measure_ge0 //.
  Qed.

  Let gMap_semi_sigma_additive : semi_sigma_additive (gMap_ev).
  Proof.
    rewrite /gMap_ev.
    apply measure_semi_sigma_additive.
  Qed.

  Let gMap_setT : (gMap_ev setT <= 1)%E.
  Proof.
    rewrite /gMap_ev /pushforward /=.
    apply sprobability_setT.
  Qed.


  HB.instance Definition _ := isMeasure.Build d2 T2 R gMap_ev gMap0 gMap_ge0 gMap_semi_sigma_additive.
  HB.instance Definition _ := Measure_isSubProbability.Build _ _ _ gMap_ev gMap_setT.

  Definition gMap : giryM T2 := gMap_ev.

  (* Axiom gMap : forall (f : T1 -> T2), measurable_fun setT f -> (giryM T1 -> giryM T2). *)

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


Section giry_join.
  Local Open Scope classical_set_scope.
  Context `{d : measure_display} {T : measurableType d}.

  Axiom gJoin : giryM (giryM T) -> giryM T.
  Axiom gJoin_meas_fun : measurable_fun setT gJoin.
  Axiom gJoin_proper : (Proper (measure_eq ==> measure_eq) gJoin).
  Global Existing Instance gJoin_proper.

End giry_join.

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


  Axiom gRetEq : forall (x : T1) (S : set T1) (Hms : measurable S), (gRet x S) = (dirac x S).
  Axiom gMapEq : forall (f : T1 -> T2) (Hmf: measurable_fun setT f) (μ : giryM T1)
                   (S : set T2) (Hms : measurable S),
                      gMap Hmf μ S = pushforward μ Hmf S.

  Definition gJoinMeas (M : giryM (giryM T1)) := fun (S : set T1) => \int[M]_μ μ S.

  Let join_meas0 (M : giryM (giryM T1)): gJoinMeas M set0 = 0.
  Proof.
    rewrite /gJoinMeas.
    rewrite -(integral0 M setT).
    apply ae_eq_integral; auto.
    rewrite -gEval_eval.
    apply gEval_meas_fun.
    Search integral.    erewrite ae_eq_integral.
    Search integral.
    rewrite measure_set0.
    Search integral set0.
      indic0. Qed.

  Let dirac_ge0 B : 0 <= dirac B. Proof. by rewrite /dirac indicE. Qed.


  Axiom gJoinEq: forall (M : giryM (giryM T1)) (S : set T1) (Hms : measurable S),
      gJoin M S = \int[M]_μ (fun μ => μ S) μ.



Let dirac_sigma_additive : semi_sigma_additive dirac.

  Lemma gRetInt (x : T1) (h : T1 -> \bar R) (H : measurable_fun setT h) (Hpos : forall x, 0 <= h x):
      gInt H Hpos (gRet x) = h x.
  Proof.
    rewrite /gInt.
    have Haux : (forall S, d1.-measurable S -> S `<=` [set : T1] -> gRet x S = dirac x S).
    {
      intros. rewrite gRetEq; auto.
    }
    erewrite (eq_measure_integral _ Haux).
    rewrite integral_dirac; auto.
    rewrite diracT mul1e //.
  Qed.

  Lemma gMapInt (f : T1 -> T2) (Hmf : measurable_fun setT f) (μ : giryM T1)
    (h : T2 -> \bar R) (Hmh : measurable_fun setT h) (Hpos : forall x, 0 <= h x):
    gInt Hmh Hpos (gMap Hmf μ) = \int[μ]_x (h \o f) x.
  Proof.
    rewrite /gInt.
    have Haux : (forall S, d2.-measurable S -> S `<=` [set : T2] -> gMap Hmf μ S = pushforward μ Hmf S).
    {
      intros. rewrite gMapEq; auto.
    }
    erewrite (eq_measure_integral _ Haux).
    rewrite ge0_integral_pushforward; auto.
  Qed.


  Lemma gJoinInt (M : giryM (giryM T1))
    (h : T1 -> \bar R) (Hmh : measurable_fun setT h) (Hpos : forall x, 0 <= h x):
    gInt Hmh Hpos (gJoin M) = \int[M]_μ \int[μ]_x h x.
  Proof.
    rewrite /gInt.
    rewrite -fubini_tonelli.
    Search integral.
    rewrite Fubini.
    eapply (eq_measure_integral M).
    have Haux : (forall S, d1.-measurable S -> S `<=` [set : T1] -> gJoin M S = \int[M]_μ (fun μ => μ S) μ).
    {
      intros. rewrite gJoinEq; auto.
    }
    Search integral.
    Unset Printing Notations.
    erewrite (eq_measure_integral _ Haux).

  Lemma gRetInt_rw (x : T1) (f : T1 -> \bar R) (H : measurable_fun setT f) (Hpos : forall x, 0 <= f x) :
      \int[gRet x]_x f x = f x.
  Proof.
    rewrite -/gInt.
    eapply gRetInt.
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

  Definition has_support_in (μ : giryM T) (S : set T) : Prop := mass' μ S = mass' μ setT.

End giry_has_support_in.

Section giry_is_det.
  Local Open Scope classical_set_scope.
  Context {d} {T : measurableType d}.

  Definition is_det (t : T) (μ : giryM T) : Prop :=
    has_support_in μ [set t].

End giry_is_det.

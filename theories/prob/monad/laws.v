(** Examples *)

From mathcomp Require Import all_ssreflect all_algebra finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
From mathcomp.analysis Require Import reals ereal signed (* topology *) normedtype esum numfun measure lebesgue_measure lebesgue_integral.
From HB Require Import structures.

From clutch.prob.monad Require Export types eval ret integrate const map zero compose join bind identity.

Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Default Proof Using "Type".

(**
    The Giry Probability Monad

    Types:
      measurable_map T1 T2 (written T1 -mm-> T2 )
        - coerces to regular functions T1 -> T2

      giryM T
        - measurable type of probability subdistributions over T

      borelER
        - Borel type on the extended real numbers


    Definitions:

      m_id                                            : A -mm-> A
      m_cmp (f : B -mm-> C) (g : A -mm-> B)           : A -mm-> C
      m_cst (k : B)                                   : A -mm-> B

      giryM_zero                                      : giryM A
      giryM_eval (S : measurable set A)               : giryM A -mm-> \bar R
      giryM_integrate (f : nonnegative A -> borelER)  : giryM A -mm-> \bar R
      giryM_map (f : A -mm-> B)                       : giryM A -mm-> giryM B

      giryM_ret                                       : A -mm-> giryM A
      giryM_bind (f : A -mm-> giryM B)                : giryM A -mm-> giryM B
      giryM_join                                      : giryM (giryM A) -mm-> giryM A

    Each function giryM_X has an evaluation function giryM_X_eval (the definition itself
    should not be unfolded)

    Laws:
      giryM_join (giryM_zero)                 = giryM_zero
      giryM_integrate f (giryM_join m)        = giryM_integrate (giryM_integrate f) m
      giryM_join (giryM_map (giryM_map f) m)  = giryM_map f (giryM_join m)
      giryM_join (giryM_map giryM_join m)     = giryM_join (giryM_join m)
      giryM_join (giryM_map giryM_ret t)      = t
      giryM_join (giryM_ret t)                = t
      giryM_bind f giryM_zero                 = giryM_zero
      giryM_bind (m_cst giryM_zero) t         = giryM_zero
      giryM_bind f (giryM_ret t)              = f t
      giryM_bind giryM_ret m                  = m
      giryM_bind g (giryM_bind f m)           = giryM_bind (m_cmp (giryM_bind g) f) m
      giryM_map f giryM_zero                  = giryM_zero
      giryM_map (m_cst k) t                   = giryM_ret R k     (only for proper distributions)

 *)

Section monad_laws.
  Context `{R : realType}.
  Notation giryM := (giryM (R := R)).

  Local Open Scope classical_set_scope.

  Lemma giryM_join_zero {d1} {T1 : measurableType d1} : giryM_join giryM_zero = (giryM_zero: giryM T1).
  Proof.
    apply giryM_ext.
    intro S.
    rewrite giryM_join_eval.
    rewrite giryM_zero_eval.
    by rewrite integral_measure_zero.
  Qed.


  (* FIXME: Express using nonnegative functions (I think they're in the hierarhy?) *)
  (* FIXME: giryM_integrate @ symbol *)
  Lemma giryM_join_integrate {d1} {T1 : measurableType d1}
      (f : measurable_map T1 (\bar R)) (Hf : forall x : T1, (0%R <= f x)%E)
      (Hf' : forall x : giryM T1, (0%R <= giryM_integrate Hf x)%E)
      (m : giryM (giryM T1)) :
    (@giryM_integrate _ _ _ f Hf) (giryM_join m) = (@giryM_integrate _ _ _ (@giryM_integrate _ _ _ f Hf)) Hf' m.
  Proof.
    (* Rewrite integral over (giryM_join M) to limit. *)
    have HM : d1.-measurable [set: T1] by apply @measurableT.
    rewrite giryM_integrate_eval.
    rewrite (nd_ge0_integral_lim (giryM_join m) _ _ (fun _ => @cvg_nnsfun_approx _ T1 R setT HM f _ _ _ _)); cycle 2.
    - by apply Hf.
    - intros x t n' m' Hle.
      have HR := (@nd_nnsfun_approx _ _ _ _ HM _ x n' m' Hle).
      (* apply Order.POrderTheory.leif_eq in HR. *)
      admit.
    - by intros ???; apply Hf.
    - by intros; simpl.
    - by apply @measurable_mapP.
    intro Hfmf.

    (* Rewrite integral over μ to limit, under the RHS integral. *)
    rewrite giryM_integrate_eval.
    under eq_integral=> ? _ do rewrite giryM_integrate_eval.
    under eq_integral=> ? _ do erewrite (nd_ge0_integral_lim _ _ _ (fun x => (@cvg_nnsfun_approx _ _ _ setT _ _ Hfmf _ _ _))).
    Unshelve.
    all: cycle 1.
    - by apply Hf.
    - intros x n' m' Hle.
      (* See above *)
      admit.
    - by intros ??; apply Hf.
    - by simpl.
    - by simpl.

    (* Rewrite the sintegral of nnsfun_approx into a sum (on the left?)*)
    rewrite topology.fmap_comp.

    have Setoid1 : forall g h, g = h -> (\int[m]_μ g μ)%E = (\int[m]_μ (h μ))%E.
    { intros. f_equal. apply functional_extensionality. intros. by rewrite H. }
    have Setoid2 : forall S, forall g h, g = h  -> (topology.fmap g S) = (topology.fmap h S).
    { by intros ? ? ? ? ? H; rewrite H. }

    (* Change to use under? *)
    erewrite Setoid2; last first.
    - by apply (functional_extensionality _ _ (sintegralE _)).
      (* FIXME: Possible issue down the road: sintegralE vs sintegralET *)

    under eq_integral=> ? _ do rewrite topology.fmap_comp.
    erewrite Setoid1; last first.
    - apply functional_extensionality.
      intro x.
      rewrite (functional_extensionality _ _ (sintegralE _ )).
      reflexivity.

    under eq_integral=> ? _ do rewrite /=-topology.fmap_comp.
    rewrite (@monotone_convergence _ (giryM T1) R m setT _ _ _ _ _); first last.
    - (* Sequence is monotone *)
      (* Unset Printing Notations. *)
      intros μ _.
      (* Check nd_nnsfun_approx.
      (* Search homomorphism_2 bigop.body. *) *)

      (* Might need to do this directly.. I can't find any relevant theorems for this type of sum *)
      (* Surely this proof was done somewhere else so I'm confident it's possible. *)
      intros x y Hle.

      admit.
    - (* Sequence is nonnegative *)
      intros n μ _.
      rewrite /= fsume_ge0 //=.
      intros i [t ? <-].
      apply mule_ge0.
      + rewrite nnsfun_approxE.
        rewrite /approx /=.
        (* How to lower bound these sums? *)
        admit.
      + by eapply @measure_ge0.
    - (* Sequence is pointwise measurable *)
      intros n.
      apply emeasurable_fun_fsum. (* Measurability of finite sums *)
      { rewrite nnsfun_approxE.
        rewrite /finite_set.
        (* Sum is finite *)  admit. }
      intro range_element.
      (* Seems to be no lemmas that mul measurable is measurable in ENNR, only R *)
      admit.
    - by apply @measurableT.
    (* Pointwise equality between limits *)
    f_equal.
    rewrite -topology.fmap_comp.
    f_equal.
    rewrite /comp.
    apply functional_extensionality.
    intro n.

    (* Exchange finite sum with integral on the RHS (LHS seems harder) *)
    rewrite ge0_integral_fsum; first last.
    - (* Range of approximation is finite *)
      admit.
    - (* Argument is nonnegative *)
      intros n' μ _.
      apply mule_ge0.
      + admit.
      + by apply @measure_ge0.
    - (* Argument is pointwise measurable. *)
      intro range_element.
      admit.
    - by apply @measurableT.

    f_equal.
    - (* The index sets are the same *)
      (* As predicted, it's way easier do prove this down here *)
      f_equal.
      apply functional_extensionality.
      intro x.
      rewrite /= giryM_join_eval.
      rewrite integralZl /=.
      + done.
      + by apply (@measurableT (@giryM_display R d1 T1) (@salgebraType (@giryType R d1 T1) (@giry_subbase R d1 T1))).
      + (* apply base_eval_measurable. *)
        admit.
    - (* The bodies are the same *)
      apply functional_extensionality.
      intro x.
      f_equal.
      rewrite /= giryM_join_eval.
      rewrite integralZl.
      + done.
      + by apply (@measurableT (@giryM_display R d1 T1) (@salgebraType (@giryType R d1 T1) (@giry_subbase R d1 T1))).
      + admit.
  Admitted.

  Lemma giryM_map_zero {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2} (f : measurable_map T1 T2) :
      giryM_map f giryM_zero = (giryM_zero : giryM T2).
  Proof.
    apply giryM_ext.
    intro S.
    rewrite giryM_map_eval.
    rewrite giryM_zero_eval.
    by rewrite /=/mzero/pushforward.
  Qed.


  (* Note: this does not hold for subdistributions! *)
  Lemma giryM_map_cst {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}
    (μ : giryM T1) (Hμ : μ [set: T1] = 1%:E) (k : T2) :
      giryM_map (m_cst k) μ = giryM_ret R k .
  Proof.
    apply giryM_ext.
    intro S.
    rewrite giryM_map_eval.
    rewrite giryM_ret_eval.
    rewrite /pushforward.
    rewrite preimage_cst.
    rewrite /dirac/indic/=.
    destruct (k \in S); simpl.
    - trivial.
    - by rewrite measure0.
  Qed.


  Lemma giryM_map_integrate  {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}
      (g : measurable_map T2 (\bar R)) (Hg : forall x : T2, (0%R <= g x)%E)
      (h : measurable_map T1 T2) (Hgh : forall x : T1, (0%R <= (m_cmp g h) x)%E)
      (μ : giryM T1):
    (giryM_integrate Hg (giryM_map h μ) = giryM_integrate Hgh μ)%E.
  Proof.
    rewrite giryM_integrate_eval.
    rewrite giryM_integrate_eval.
    rewrite integral_pushforward; cycle 1.
    - by apply measurable_mapP.
    - by apply measurable_mapP.
    - by apply Hg.
    f_equal.
  Qed.


  Lemma giryM_join_map_map {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}
      (mf : measurable_map T1 T2) (m : giryM (giryM T1)) :
    giryM_join (giryM_map (giryM_map mf) m) ≡μ giryM_map mf (giryM_join m).
  Proof.
    intros S HS.
    rewrite giryM_join_eval.
    rewrite integral_pushforward; cycle 1.
    - by apply measurable_mapP.
    - by apply base_eval_measurable.
    - by intro u; apply (measure_ge0 u).
    rewrite giryM_map_eval.
    rewrite /pushforward.
    rewrite giryM_join_eval.
    f_equal.
  Qed.

  Lemma giryM_join_map_join {d1} {T1 : measurableType d1} (m : giryM (giryM (giryM T1))) :
    giryM_join (giryM_map giryM_join m) = giryM_join (giryM_join m).
  Proof.
    apply giryM_ext.
    intro S.
    rewrite giryM_join_eval.
    rewrite giryM_join_eval.
    f_equal.
    (* FIXME: This is an independently useful result, if true.
       Is it true though? I'm not convinced yet. Did I steal this from somwehere?.
       The lemma could still be true even if this step is false.
     *)
  Abort.

  (* TODO: Can I prove this for all sets?*)
  Lemma giryM_join_map_ret {d1} {T1 : measurableType d1} (μ : (giryM T1)) :
    giryM_join (giryM_map (giryM_ret R) μ) ≡μ μ.
  Proof.
    intros S HS.
    rewrite giryM_join_eval.
    rewrite integral_pushforward; cycle 1.
    - by apply measurable_mapP.
    - by apply base_eval_measurable.
    - by intro u; apply (measure_ge0 u).
    simpl.
    rewrite /dirac/=.
    rewrite integral_indic.
    - by rewrite setIT.
    - by apply @measurableT.
    - done.
  Qed.

  Lemma giryM_join_ret {d1} {T1 : measurableType d1} (μ : (giryM T1)) :
    giryM_join (giryM_ret R μ) ≡μ μ.
  Proof.
    intros S HS.
    rewrite giryM_join_eval.
    rewrite integral_dirac.
    - by rewrite diracT mul1e.
    - by apply @measurableT.
    - apply (@measurable_comp _ _ _ _ _ _ setT).
      - by apply @measurableT.
      - by apply subsetT.
      - by apply base_eval_measurable.
      - by apply measurable_id.
  Qed.


  Lemma giryM_bind_0_l {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2} {f : measurable_map T1 (giryM T2)} :
    giryM_bind f giryM_zero = giryM_zero .
  Proof.
    apply giryM_ext.
    intro S.
    rewrite giryM_join_eval.
    rewrite giryM_map_zero.
    rewrite integral_measure_zero.
    by rewrite giryM_zero_eval.
  Qed.


  Lemma giryM_bind_0_r {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2} (μ : giryM T1) :
    giryM_bind (m_cst giryM_zero) μ ≡μ (giryM_zero : giryM T2).
  Proof.
    intros S HS.
    rewrite giryM_join_eval.
    rewrite integral_pushforward; cycle 1.
    - by apply measurable_mapP.
    - by apply base_eval_measurable.
    - by intro u; apply (measure_ge0 u).
    rewrite /=/mzero.
    rewrite integral_cst.
    - by rewrite mul0e.
    - by apply @measurableT.
  Qed.

  (* TODO: Can I fit this into the framework? *)
  Lemma giryM_bind_eval {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}
    (m : giryM T1) {S : set T2} (HS : measurable S) (f : measurable_map T1 (giryM T2)) :
    (giryM_bind f m S = \int[m]_x (f x S))%E.
  Proof.
    rewrite giryM_join_eval.
    rewrite integral_pushforward /=; cycle 1.
    - by apply measurable_mapP.
    - by apply base_eval_measurable.
    - by intro u; apply (measure_ge0 u).
    done.
  Qed.

  Lemma giryM_bind_ret_l {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2} {f : measurable_map T1 (giryM T2)} t :
    giryM_bind f (giryM_ret R t) ≡μ f t.
  Proof.
    intros S HS.
    rewrite giryM_join_eval.
    rewrite integral_pushforward; cycle 1.
    - by apply measurable_mapP.
    - by apply base_eval_measurable.
    - by intro u; apply (measure_ge0 u).
    rewrite integral_dirac.
    - by rewrite diracT /= mul1e.
    - by apply @measurableT.
    apply (@measurable_comp _ _ _ _ _ _ setT).
    - by apply @measurableT.
    - by apply subsetT.
    - by apply base_eval_measurable.
    - by apply measurable_mapP.
  Qed.


  Lemma giryM_bind_ret_r_meas {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2} {f : measurable_map T1 (giryM T2)}
    (m : giryM T1) :
    giryM_bind (giryM_ret R) m ≡μ m.
  Proof.
    intros S HS.
    rewrite giryM_join_eval.
    rewrite integral_pushforward; cycle 1.
    - by apply measurable_mapP.
    - by apply base_eval_measurable.
    - by intro u; apply (measure_ge0 u).
    rewrite /=.
    rewrite /dirac integral_indic.
    - by rewrite setIT.
    - by apply @measurableT.
    - done.
  Qed.

  Lemma giryM_bind_bind_meas {d1 d2 d3} {T1 : measurableType d1} {T2 : measurableType d2} {T3 : measurableType d3}
    {f : measurable_map T1 (giryM T2)} {g : measurable_map T2 (giryM T3)}
    (m : giryM T1) :
    giryM_bind g (giryM_bind f m) ≡μ giryM_bind (m_cmp (giryM_bind g) f) m.
  Proof.
    intros S HS.
    rewrite giryM_join_eval.
    rewrite integral_pushforward; cycle 1.
    - by apply measurable_mapP.
    - by apply base_eval_measurable.
    - by intro u; apply (measure_ge0 u).
    have IHF : forall x : T2, (0%R <= m_cmp (giryM_eval R HS) g x)%E.
    { intro x.
      rewrite m_cmp_eval.
      rewrite /comp.
      rewrite giryM_eval_eval.
      by apply (measure_ge0 (g x)).
    }
    have IHF' :  forall x : giryM T2, (0%R <= giryM_integrate IHF x)%E.
    { intros ?.
      rewrite giryM_integrate_eval.
      apply integral_ge0.
      intros y _.
      rewrite m_cmp_eval.
      rewrite /comp.
      rewrite giryM_eval_eval.
      by apply (measure_ge0 (g y)).
    }
    have I := @giryM_join_integrate _ T2 (m_cmp (giryM_eval _ HS) g) IHF IHF' (giryM_map f m).
    rewrite giryM_integrate_eval in I.
    rewrite I.
    rewrite giryM_join_eval.
    rewrite giryM_integrate_eval.
    rewrite integral_pushforward; cycle 1.
    - by apply measurable_mapP.
    - by apply measurable_mapP.
    - by apply IHF'.
    rewrite integral_pushforward; cycle 1.
    - by apply measurable_mapP.
    - by apply base_eval_measurable.
    - by intro u; apply (measure_ge0 u).
    f_equal.
    apply functional_extensionality.
    intro t.
    simpl.
    rewrite giryM_integrate_eval.
    rewrite giryM_join_eval.
    rewrite integral_pushforward; cycle 1.
    - by apply measurable_mapP.
    - by apply base_eval_measurable.
    - by intro u; apply (measure_ge0 u).
    f_equal.
  Qed.

  Lemma giryM_join_bind {d} {T : measurableType d} (m : giryM (giryM T)) :
    giryM_join m = giryM_bind m_id m.
  Proof.
    apply giryM_ext.
    intro S.
    rewrite giryM_join_eval.
    rewrite giryM_join_eval.
    f_equal.
  Qed.
End monad_laws.

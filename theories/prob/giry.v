(** Measures and probabilitiy from mathcomp-analysis *)

From mathcomp Require Import all_ssreflect all_algebra finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
From mathcomp.analysis Require Import reals ereal signed (* topology *) normedtype esum numfun measure lebesgue_measure lebesgue_integral.
From HB Require Import structures.

From clutch.prob.monad Require Export types.

Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Default Proof Using "Type".

  Context `{R : realType}.
  Notation giryM := (giryM (R := R)).

(*




  (** ********** 7. Monad map  *)

  Section giryM_map_definition.
    Context {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2}.

    Lemma pushforward_setT (f : measurable_map T1 T2) (m : giryM T1) : (pushforward m (@measurable_mapP _ _ _ _ f) setT <= 1)%E.
    Proof using Type. rewrite /pushforward preimage_setT. apply sprobability_setT. Qed.

    HB.instance Definition _ (f : measurable_map T1 T2) (m : giryM T1) := Measure_isSubProbability.Build _ _ _ (pushforward m (@measurable_mapP _ _ _ _ f)) (pushforward_setT f m).

    Definition giryM_map_def (f : measurable_map T1 T2) (m : giryM T1) : giryM T2 := pushforward m (@measurable_mapP _ _ _ _ f).

    Lemma giryM_map_def_is_measurable (f : measurable_map T1 T2) : @measurable_fun _ _ (giryM T1) (giryM T2) setT (giryM_map_def f).
    Proof.
      apply measurable_if_measurable_evals.
      rewrite /measurable_evaluations.
      (* Check pushforward. *)

      intros S HS.
      apply measurable_if_pushfowrard_subset.
      intros Y HY.
      simpl.

      (*

      have HM := @measurable_mapP _ _ _ _ f.
      apply measurable_if_pushfowrard_subset.
      rewrite /giryM_map_def.
      intros S SM.
      simpl.
      rewrite /pushforward.
      simpl.*)


      (* rewrite /giryM_map_def/measurable_fun.
      intros ? Y YMeas.
      rewrite setTI.
      rewrite /pushforward.
      rewrite /preimage.*)
    Admitted.

    HB.instance Definition _ (f : measurable_map T1 T2) :=
      isMeasurableMap.Build _ _ (giryM T1) (giryM T2) (giryM_map_def f) (giryM_map_def_is_measurable f).

  End giryM_map_definition.


  (* FIXME: Seal above definitions *)
  Definition giryM_map {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2} (f : measurable_map T1 T2) :
      measurable_map (giryM T1) (giryM T2)
    := giryM_map_def f.
  Lemma giryM_map_aux {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2} (f : measurable_map T1 T2) :
    forall μ, giryM_map f μ = pushforward μ  (@measurable_mapP _ _ _ _ f).
  Proof. done. Qed.


  Section giry_map_laws.
    (* TODO: Port laws from prob here *)
    Context {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}.

    Lemma giryM_map_zero (f : measurable_map T1 T2) : giryM_map f mzero = mzero.
    Proof.
      rewrite giryM_map_aux/mzero/pushforward.
      (* functional_extensionality doesn't work... weird *)
    Admitted.

    Lemma giryM_map_cst (μ : giryM T1) (k : T2) : giryM_map (cst k) μ = giryM_ret k .
    Proof.
      rewrite giryM_map_aux.
      rewrite /pushforward.
      rewrite giryM_ret_aux.

      (* Defining a specific version of cst that is a measurable function (Mcst, like Mcmp) might fix this *)

      (* Weird that I can't apply functional extensionality *)
      have H : (fun A : set T2 => μ (cst k @^-1` A)) = (fun A : set T2 => ((\1_A k)%:E)).
      { apply functional_extensionality.
        intro A.
        rewrite preimage_cst.
        rewrite /indic.
        destruct (k \in A).
        - simpl.
          admit.
        - simpl.
          admit.
      }
      rewrite H.
      clear H.
      rewrite /dirac.
      Fail reflexivity.
      (* ???? *)
      (* This whole proof is haunted *)
    Admitted.

    Lemma giryM_map_integrate (g : measurable_map T2 (\bar R)) (h : measurable_map T1 T2) (μ : giryM T1):
      (\int[giryM_map h μ]_x g x  = \int[μ]_x g (h x))%E.
    Proof.
      rewrite giryM_map_aux.
      rewrite integral_pushforward.
      (* Can this be weakened to include negative g? *)
      - simpl.
        reflexivity.
      - admit.
      - admit.
    Admitted.
  End giry_map_laws.



  (** ********** 8. Monad join *)


  Section giryM_join_definition.
    Context {d} {T : measurableType d}.

    Definition giryM_join_def {d} {T : measurableType d} (m : giryM (giryM T)) : (set T -> \bar R)
      := (fun S => \int[m]_μ (μ S))%E.

    (* For the proofs,
        I don't know if there's any way to reuse the measurability of evaluation functions to do this. *)

    Section giryM_join_measure_def.
      Context (m : giryM (giryM T)).

      Definition giryM_join0 : giryM_join_def m set0 = 0%E.
      Proof.
        rewrite /giryM_join_def.
        have X1 : (\int[m]_μ μ set0)%E  = ((integral m setT (cst GRing.zero)))%E.
        { f_equal.
          apply functional_extensionality.
          intro μ.
          by rewrite measure0.
        }
        rewrite X1.
        rewrite integral_cst.
        - by rewrite (mul0e _).
        - rewrite /=.
          by apply (@measurableT _ (salgebraType _)).
      Qed.

      Definition giryM_join_ge0 A : (0 <= giryM_join_def m A)%E.
      Proof.
        rewrite /giryM_join_def.
        apply integral_ge0.
        intros μ _.
        apply (measure_ge0 μ A).
      Qed.

      Definition giryM_join_semi_additive : semi_sigma_additive (giryM_join_def m).
      Proof.
        (* Search semi_sigma_additive.
        Search sigma_additive.
        Search additive. *)
        rewrite /semi_sigma_additive.
        intros F Fmeas Htriv_int HFunion_meas.
        rewrite /giryM_join_def.
        (* Search integral bigcup. (* Seems like the limit we want *) *)

        (* Check (integral_bigcup Htriv_int Fmeas).
        (* Search topology.cvg_to topology.lim.
        Search (topology.cvg_to _ (topology.nbhs _)) topology.lim. *) *)

      Admitted.

      HB.instance Definition _
        := isMeasure.Build _ _ _
             (giryM_join_def m)
             giryM_join0
             giryM_join_ge0
             giryM_join_semi_additive.

      Lemma giryM_join_setT : (giryM_join_def m setT <= 1)%E.
      Proof.
        rewrite /giryM_join_def.
        have H : (\int[m]_μ μ [set: T] <= \int[m]_μ 1)%E.
        { (* Search integral (_ <= _)%E. *)
          apply ge0_le_integral.
          - by [].
          - intros ? ?; by [].
          - simpl.
            admit.
          - intros ? ?; by [].
          - admit.
          - intros ? ?.
            (* Because of subprobability *)
            admit.  }

      (* Now I just need that the measure of m is at most 1,
         Also true because of subprobability. *)
      Admitted.

      HB.instance Definition _ :=  Measure_isSubProbability.Build _ _ _ (giryM_join_def m) giryM_join_setT.

    End giryM_join_measure_def.

    Definition giryM_join_def' : giryM (giryM T) -> (giryM T) := giryM_join_def.

    Lemma giryM_join_def'_measurable : @measurable_fun _ _ (giryM (giryM T)) (giryM T) setT giryM_join_def'.
    Proof.

    Admitted.

    HB.instance Definition _ :=
      isMeasurableMap.Build _ _ (giryM (giryM T)) (giryM T) giryM_join_def' giryM_join_def'_measurable.

  End giryM_join_definition.


  (* FIXME: Seal above defs *)
  Definition giryM_join {d} {T : measurableType d} : measurable_map (giryM (giryM T)) (giryM T) := giryM_join_def'.
  Lemma giryM_join_aux {d} {T : measurableType d} (m : giryM (giryM T)) :
    forall S, (giryM_join m S = \int[m]_μ (μ S))%E.
  Proof. done. Qed.



  Section giryM_join_laws.
    (* TODO: Port laws from prob here *)
    Context {d} {T : measurableType d}.
    Context {d2} {T2 : measurableType d2}.

    Lemma giryM_join_zero : giryM_join mzero = (mzero : giryM T).
    Proof.
      apply giryM_ext.
      apply functional_extensionality.
      intro S.
      rewrite /mzero.
      (* Odd that it doesn't reduce mzero? *)
      simpl.


    Admitted.

    (* lintegral_join *)
    Lemma giryM_join_integrate (m : giryM (giryM T)) (f : T -> \bar R) (Hf : forall x : T, (0%R <= f x)%E)
      (mf : measurable_fun setT f) :
      (\int[giryM_join m]_x (f x) = \int[m]_μ (\int[μ]_x f x))%E.
    Proof.
      have HTmeas : d.-measurable [set: T] by [].

      (* Rewrite integral over (giryM_join M) to limit. *)
      erewrite nd_ge0_integral_lim; first last.
      - intro x.
        apply (@cvg_nnsfun_approx _ _ _ setT HTmeas _ mf).
        - intros. apply Hf.
        - by simpl.
      - intros x n' m' Hle.
        (* Check (@nd_nnsfun_approx _ _ _ _ _ _ _ n' m' Hle). *)
        (* Need to turn the %R comparison into %O)*)
        admit.
      - apply Hf.

      (* Rewrite integral over μ to limit, under the RHS integral. *)
      have Setoid1 : forall g h, g = h -> (\int[m]_μ g μ)%E = (\int[m]_μ (h μ))%E.
      { intros. f_equal. apply functional_extensionality. intros. by rewrite H. }

      erewrite Setoid1; last first.
      { apply functional_extensionality.
        move=> y.
        erewrite nd_ge0_integral_lim.
        - reflexivity.
        - apply Hf.
        - (* See above admit *)
          admit.
        - intro x.
          apply (@cvg_nnsfun_approx _ _ _ setT HTmeas _ mf).
          - intros. apply Hf.
          - by simpl.
      }

    (* Rewrite the sintegral of nnsfun_approx into a sum *)
    rewrite topology.fmap_comp.

    have Setoid2 : forall S, forall g h, g = h  -> (topology.fmap g S) = (topology.fmap h S).
    { intros ? ? ? ? ? H. by rewrite H. }
    erewrite Setoid2; last first.
    - apply functional_extensionality.
      apply (sintegralE _).  (* FIXME: Possible issue down the road: sintegralE vs sintegralET *)

    under eq_integral=> ? _ do rewrite topology.fmap_comp.

    (* Evaluate the giryM_join on the LHS into an integral *)
    erewrite
      (Setoid2 _ _ _ _
         (fun f' => (bigop.body GRing.zero
                    (finite_support GRing.zero (image setT (fun i : T => f' i))
                       (fun x : R => _))
                    _ ))); last first.
    - (* What a nightmare, there has to be a better way to rewrite under the integral sign *)
      (* Look for an example in mathcomp analysis source *)
      apply functional_extensionality.
      intro f'.
      f_equal.
      apply functional_extensionality.
      intro x.
      f_equal.
      rewrite /giryM_join.
      rewrite /giryM_join_def'.
      simpl.
      rewrite /giryM_join_def.
      done.
    simpl.
    rewrite -topology.fmap_comp.

    under eq_integral=> ? _ do rewrite -topology.fmap_comp.

    rewrite (@monotone_convergence _ (giryM T) R m setT _ _ _ _ _); first last.
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
      simpl.
      (* Search 0%R (_ <= _)%E "sum". *)
      (* None of the relevant theorems work, but something will. *)
      admit.
    - (* Sequence is pointwise measurable *)
      intros n.
      apply emeasurable_fun_fsum. (* Measurability of finite sums *)
      { (* Sum is finite *)  admit. }
      intro range_element.
      (* Seems to be no lemmas that mul measurable is measurable in ENNR, only R *)
      admit.
    - (* ⊤ is measurable *)
      admit.


    (* Pointwise equality between limits *)
    f_equal.
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
      admit.
    - (* Argument is pointwise measurable. *)
      admit.
    - (* ⊤ is measurable *)
      admit.


    f_equal.
    - (* The index sets are the same *)
      (* As predicted, it's way easier do prove this down here *)
      f_equal.
      apply functional_extensionality.
      intro x.
      rewrite /giryM_join_def.
      (* Scalar multiplication *)
      admit.
    - (* The bodies are the same *)
      apply functional_extensionality.
      intro x.
      f_equal.
      (* Scalar multiplication *)
      admit.
    Admitted.


    Lemma giryM_join_map_map (mf : measurable_map T T2) (m : giryM (giryM T)) :
      giryM_join (giryM_map (giryM_map mf) m) = giryM_map mf (giryM_join m).
    Proof.
      apply giryM_ext.
      apply functional_extensionality.
      intro S.
      rewrite giryM_join_aux.
      rewrite giryM_map_aux.
      rewrite giryM_map_aux.
      (* rewrite giryM_join_integrate. *)
    Admitted.

    Lemma giryM_join_map_join (m : giryM (giryM (giryM T))) :
      giryM_join (giryM_map giryM_join m) = giryM_join (giryM_join m).
    Proof. Admitted.

    Lemma giryM_join_map_ret (μ : (giryM T)) :
      giryM_join (giryM_map giryM_ret μ) = μ.
    Proof. Admitted.

    Lemma giryM_join_ret (μ : (giryM T)) :
      giryM_join (giryM_ret μ) = μ.
    Proof. Admitted.
  End giryM_join_laws.


  (** ********** ?. Composition of Measurable Maps (move up) *)

  (* FIXME: What is Coq's default composition operator? Make an instance for that. *)

  Section MeasurableMap_cmp.
    Context {d1 d2 d3} {T1 : measurableType d1} {T2 : measurableType d2} {T3 : measurableType d3}.

    Lemma cmp_measurable (f : measurable_map T2 T3) (g : measurable_map T1 T2) :
      @measurable_fun _ _ T1 T3 setT (comp f g).
    Proof.
      apply (@measurable_comp _ _ _ _ _ _ setT).
      - (* Search measurable setT. *)
        (* Annoying *)
        admit.
      - apply subsetT.
      - apply measurable_mapP.
      - apply measurable_mapP.
    Admitted.

    HB.instance Definition _ (f : measurable_map T2 T3) (g : measurable_map T1 T2) :=
      isMeasurableMap.Build _ _ T1 T3 (comp f g) (cmp_measurable f g).

  End MeasurableMap_cmp.

  Definition Mcmp {d1 d2 d3} {T1 : measurableType d1} {T2 : measurableType d2} {T3 : measurableType d3}
    (f : measurable_map T2 T3) (g : measurable_map T1 T2) : measurable_map T1 T3
    := comp f g.


  (** ********** 8. Monad bind *)

  Definition giryM_bind {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}
                        (f : measurable_map T1 (giryM T2)) : measurable_map (giryM T1) (giryM T2)
    := Mcmp giryM_join (giryM_map f).

  Section giryM_bind_laws.
    (* TODO: Port laws from prob here *)
    Context {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}.
    Context {f : measurable_map T1 (giryM T2)}.

    Lemma giryM_bind_0_l : giryM_bind f mzero = mzero.
    Proof using Type.
      rewrite /giryM_bind.
      rewrite /Mcmp/comp.
      (* FIXME *)
      Opaque giryM_join.
      Opaque giryM_map.
      simpl.
      Transparent giryM_join.
      Transparent giryM_map.
      rewrite giryM_map_zero.
      apply giryM_join_zero.
    Qed.

    (* FIXME: make it so that I don't have to annotate giryM T2 here? *)
    Lemma giryM_bind_0_r (μ : giryM T1) : giryM_bind (cst (mzero : giryM T2)) μ = mzero.
    Proof using Type.
      rewrite /giryM_bind.
      rewrite /Mcmp/comp.
      (* FIXME *)
      Opaque giryM_join.
      Opaque giryM_map.
      simpl.
      Transparent giryM_join.
      Transparent giryM_map.
      rewrite giryM_map_cst.
      by rewrite giryM_join_ret.
    Qed.

    Lemma giryM_bind_measurable : measurable_fun setT (giryM_bind f).
    Proof using Type.
      rewrite /giryM_bind.
      rewrite /Mcmp/comp.
      (* FIXME *)
      Opaque giryM_join.
      Opaque giryM_map.
      simpl.
      Transparent giryM_join.
      Transparent giryM_map.
      apply cmp_measurable.
    Qed.

    Lemma giryM_bind_eval (m : giryM T1) (s : set T2) (HS : measurable s) :
      (giryM_bind f m s = \int[m]_x f x s)%E.
    Proof. Admitted.

    Lemma giryM_bind_integrate (m : giryM T1) (g : T2 -> \bar R) (mg : measurable_fun setT g) :
      (\int[giryM_bind f m]_x g x = \int[m]_a (\int[f a]_x g x))%E.
    Proof. Admitted.

    Lemma giryM_bind_ret_l t : giryM_bind f (giryM_ret t) = f t.
    Proof. Admitted.

    Lemma giryM_bind_ret_r (m : giryM T1) : giryM_bind giryM_ret m = m.
    Proof. Admitted.


    Context {d3} {T3 : measurableType d3} (g : measurable_map T2 (giryM T3)).

    Lemma giryM_bind_bind (m : giryM T1) :
      giryM_bind g (giryM_bind f m) = giryM_bind (comp (giryM_bind g) f) m.
    Proof.
      (* Probably Mcmp *)
      rewrite /giryM_bind.
    Admitted.

    (* Make identity a measurable_map *)
    (* Lemma giryM_join_bind (m : giryM (giryM T1)) :
      giryM_join m = giryM_bind (fun x => x) m. *)

  End giryM_bind_laws.

End giry.
*)

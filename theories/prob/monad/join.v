(** join *)
#[warning="-notation-incompatible-prefix -hiding-delimiting-key"]
From mathcomp Require Import all_boot all_algebra finmap.
#[warning="-notation-incompatible-prefix"]
From mathcomp Require Import mathcomp_extra boolp classical_sets functions reals interval_inference.
From mathcomp Require Import cardinality fsbigop.
From mathcomp.analysis Require Import ereal normedtype esum numfun measure lebesgue_measure lebesgue_integral.
From HB Require Import structures.

From clutch.prob.monad Require Export types eval compose integrate.

From Stdlib.Logic Require Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Default Proof Using "Type".

Section giryM_join_definition.
  Context `{R : realType}.
  Notation giryM := (giryM (R := R)).
  Context {d} {T : measurableType d}.

  Local Open Scope classical_set_scope.

  (* Specification of giryM_join as an integral *)
  Local Definition giryM_join_def {d} {T : measurableType d} (m : giryM (giryM T)) : (set T -> \bar R)
    := (fun S => \int[m]_μ (μ S))%E.

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
      rewrite /semi_sigma_additive.
      intros F Fmeas Htriv_int HFunion_meas.
      simpl.

      (*
      rewrite /giryM_join_def.
      Check @integral_bigcup _ _ _ _ F _ Htriv_int Fmeas .
      *)

      (* Setoid lemmas for the next step: *)
      have Setoid1 (S1 S2 S3 : filter.set_system (extended (Real.sort R))) :
        (S1 = S2) -> filter.cvg_to S1 S3 -> filter.cvg_to S2 S3 by move=>->.
      have Setoid2 G H : (G = H) -> (filter.nbhs G) = (filter.nbhs H) by move=>->.
      have Setoid3 (G H : nat -> (extended (Real.sort R))) S : (G = H) -> filter.fmap G S = filter.fmap H S by move=>->.
      have Setoid4 (G H : types.giryM T -> \bar R) : (G = H) ->  (integral m setT G)%E =  (integral m setT H)%E by admit.

      (* Perform rewrites underneath the cvg_to and nbhs *)
      eapply Setoid1.
      { symmetry.
        eapply Setoid2.
        eapply etrans.
        { eapply Setoid3.
          eapply etrans.
          { apply functional_extensionality.
            intro n.
            (* Rewrite giryM_join_def to an integral *)
            rewrite /giryM_join_def.

            (* Exchange integral and finite sum *)
            have Goal1 : (\sum_(0 <= i < n) (\int[m]_μ μ (F i))%E)%R = (\int[m]_μ (\sum_(0 <= i < n) (μ (F i))%R))%E.
            { admit. }
            rewrite Goal1.
            clear Goal1.

            (* By disjointness: finite sum of measures of sets = measure of union of sets *)
            (* FIXME: There's got to be some place in mathcomp where they do this already *)
            eapply Setoid4.
            apply functional_extensionality.
            intro μ.
            have Goal2 :
              (bigop.body GRing.zero (index_iota 0 n) (fun i : nat => BigBody i GRing.add true (μ (F i)))) =
              μ (bigop.body set0 (index_iota 0 n) (fun i : nat => BigBody i setU true (F i))).
            { admit. }
            rewrite Goal2 /=.
            reflexivity.
          }

          (* Rewrite to \comp *)
          have Goal3 :
            (fun n : nat => (\int[m]_μ μ (\big[setU/set0]_(0 <= i < n) F i))%E) =
            comp
              (fun (S : set T) => (\int[m]_μ (μ S))%E) (* Basically giryM_integrate of giryM_eval *)
              (fun n : nat => (bigop.body set0 (index_iota 0 n) (fun i : nat => BigBody i setU true (F i)))).
          { admit.
          }
          apply Goal3.
        }

        (* Rewrite with fmap_comp*)
        rewrite filter.fmap_comp.
        reflexivity.
      }

      (* Now I want to take the union of the sequence, turn it into bigcup *)
      (* Or go the other way around: rewrite RHS to comp and cancel the cts function integrate *)
      (* The former seems easier *)


      (* Finish using one of these:
      Check filter.cvg_fmap.
      Search (filter.fmap _ (filter.nbhs _)).
      Check filter.cvg_fmap2.
      Search (filter.nbhs (filter.fmap _ _)).
       *)
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
      have H : (\int[m]_μ μ [set: T] <= \int[m]_μ (cst 1 μ))%E.
      { apply ge0_le_integral.
        - by [].
        - intros ? ?; by [].
        - apply base_eval_measurable.
          by apply @measurableT.
        - intros ? ?; by [].
        - by apply measurable_cst.
        - intros ? ?.
          simpl.
          by apply sprobability_setT.
      }
      rewrite integral_cst/= in H; last by apply (@measurableT _ (giryM T)).
      apply (le_trans_ereal H).
      rewrite mul1e.
      apply sprobability_setT.
    Qed.

    HB.instance Definition _ :=  Measure_isSubProbability.Build _ _ _ (giryM_join_def m) giryM_join_setT.

  End giryM_join_measure_def.

  (* Workaround for HB bindings issue *)
  Definition giryM_join_def' : giryM (giryM T) -> (giryM T) := giryM_join_def.


  (* The measurable evaluation function which computes the giryM_join_def on measurable sets *)
  Definition giryM_join_meas_map_pre {S : set T} (HS : d.-measurable S) : measurable_map (giryM (giryM T)) (\bar R) :=
    @giryM_integrate R _ (giryM T) (giryM_eval R HS) (giryM_eval_nonneg HS).

  (* giryM_join_def equals the measurable evaluation function at each measruable set *)
  Lemma giryM_join_meas_map_pre_spec {S : set T} (HS : d.-measurable S) (m : giryM (giryM T)):
      giryM_join_meas_map_pre HS m = giryM_join_def m S.
  Proof. by rewrite /giryM_join_meas_map_pre giryM_integrate_eval /giryM_join_def. Qed.


  Lemma giryM_join_def'_measurable : @measurable_fun _ _ (giryM (giryM T)) (giryM T) setT giryM_join_def'.
  Proof.
    apply measurable_if_measurable_evals.
    rewrite /giryM_join_def'/measurable_evaluations.
    intros S HS.
    have H1 : (fun x : giryM (giryM T) => giryM_join_def x S) = (fun x : giryM (giryM T) => giryM_join_meas_map_pre HS x).
    { apply functional_extensionality.
      intros ?.
      by rewrite giryM_join_meas_map_pre_spec.
    }
    rewrite H1.
    rewrite /giryM_join_meas_map_pre.
    (* Broken by new mathcomp-analysis *)

  Admitted.
  (*
    apply measurable_mapP.
  Qed.
   *)

  HB.instance Definition _ :=
    isMeasurableMap.Build _ _ (giryM (giryM T)) (giryM T) (giryM_join_def' : giryM (giryM T) -> (giryM T)) giryM_join_def'_measurable.

End giryM_join_definition.

(** Public definition of join*)
Definition giryM_join {R : realType} {d} {T : measurableType d} :
    measurable_map (@giryM R _ (@giryM R _ T)) (@giryM R _ T) :=
  giryM_join_def'.

(** Public equation for join*)
Lemma giryM_join_eval {R : realType} {d} {T : measurableType d} (m : @giryM R _ (@giryM R _ T)) :
  forall S, (giryM_join m S = \int[m]_μ (μ S))%E.
Proof. done. Qed.

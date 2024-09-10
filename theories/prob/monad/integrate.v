(** Expectations *)

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

Section giryM_integrate_laws.
  Context `{R : realType}.
  Notation giryM := (giryM (R := R)).
  Context {d} {T : measurableType d}.

  Local Open Scope classical_set_scope.

  Local Definition giryM_integrate_def {f : measurable_map T (\bar R)} (Hf : forall x : T, (0%R <= f x)%E) : giryM T -> \bar R
    := fun μ => (\int[μ]_x (f x))%E.

  Local Lemma giry_meas_integrate {f : measurable_map T (\bar R)} (Hf : forall x : T, (0%R <= f x)%E) :
    measurable_fun setT (giryM_integrate_def Hf).
  Proof.
    have Setoid1 (d1 d2: measure_display) (X : measurableType d1) (Y : measurableType d2) (S : set X) (f1 f2 : X -> Y) (Hfg : f1 = f2) :
      measurable_fun S f1 =  measurable_fun S f2.
    { by rewrite Hfg. }
    have Setoid2 S1 S2 (HSS : S1 = S2): topology.lim S1 = topology.lim S2 by rewrite HSS.
    have Setoid3 f1 f2 S (Hff : f1 = f2): topology.fmap f1 S = topology.fmap f2 S by rewrite Hff.

    (* Search (topology.lim _ _ = topology.lim _ _). *)

    rewrite /giryM_integrate_def.
    have HMTop : d.-measurable [set: T] by done.
    pose HApprox := (nnsfun_approx HMTop (@measurable_mapP _ _ _ _ f)).

    (* Move under the measurable_fun *)
    (* Broken by new mathcomp-analysis *)

    (*
    erewrite (Setoid1 _ _ _ _ _ _ (fun (μ : giryM T) => _)); last first.
    { apply functional_extensionality; intro μ.
      (* Rewrite this integral to the limit of a finite sum  *)
      rewrite (@nd_ge0_integral_lim _ _ _ _ _ HApprox); cycle 1.
      - by apply Hf.
      - intros x.
        intros n1 n2 Hle.
        have HR := (@nd_nnsfun_approx d T R setT HMTop f (@measurable_mapP _ _ _ _ f)) n1 n2 Hle.
        by apply (asboolW HR).
      - intro x.
        refine (@cvg_nnsfun_approx d T R setT HMTop f (@measurable_mapP _ _ _ _ f) _ x _).
        - intros ? ?.
          by apply Hf.
        - by simpl.

      (* Combine the composition into a single sum *)
      eapply Setoid2.
      eapply Setoid3.
      rewrite /comp.
      apply functional_extensionality; intro n.
      rewrite sintegralEnnsfun.

      (* Could simplify the preimage (its a singleton) *)
      (* Search topology.lim "sum". *)
      reflexivity.
    }
     *)

    (* Target: *)
    (*Search measurable_fun "sum".
    Check ge0_emeasurable_fun_sum. *)


    (* Search sintegral. *)

    (*

    (* The approximation lemma for f that corresponds roughly to the mathlib limits *)
    have HMT : d.-measurable [set: T] by [].
    have X : forall μ : measure T R,
     (\int[μ]_x f x)%E =
     @topology.lim (@constructive_ereal_extended__canonical__topology_Nbhs R)
       (@topology.fmap nat \bar R
          (@sintegral T R μ \o
             (fun x : nat =>
              @nnsfun_approx d T R [set: T] HMT f (@measurable_mapP d default_measure_display T \bar R f) x))
          (@topology.nbhs nat (topology.topology_set_system__canonical__topology_Filtered nat) topology.eventually)).
    { intro μ.
      refine (@nd_ge0_integral_lim d T R μ f (nnsfun_approx HMT (@measurable_mapP _ _ _ _ f)) Hf _ _).
      - intro x.
        intros n1 n2 Hle.
        have HR := (@nd_nnsfun_approx d T R setT HMT f (@measurable_mapP _ _ _ _ f)) n1 n2 Hle.
        by apply (asboolW HR).
      - intro x.
        refine (@cvg_nnsfun_approx d T R setT HMT f (@measurable_mapP _ _ _ _ f) _ x _).
        - intros ? ?.
          by apply Hf.
        - by simpl.
    }
    have Hr1 :
     (fun μ : giryType T => (\int[μ]_x f x)%E) =
     (fun μ => @topology.lim (@constructive_ereal_extended__canonical__topology_Nbhs R)
       (@topology.fmap nat \bar R
          (@sintegral T R μ \o
             (fun x : nat =>
              @nnsfun_approx d T R [set: T] HMT f (@measurable_mapP d default_measure_display T \bar R f) x))
          (@topology.nbhs nat (topology.topology_set_system__canonical__topology_Filtered nat) topology.eventually))).
    { apply functional_extensionality.
      intro x.
      apply (X x).
    }
    rewrite Hr1.
    clear Hr1.
    clear X.

    (* This is a related measurable function *)
    (* Check @ge0_emeasurable_fun_sum d T R setT. (* This sum is over T.*) *)

    (* This one could actually be applied, if we can do the right rewrites to the sum? *)
    (* Reduces the problem to proving measurablility at evey approximation level *)
    have h_seq (i : nat) (μ : giryM T) : \bar R.
    { admit.  }

    (* Check @ge0_emeasurable_fun_sum _ (giryM T) R setT h_seq _. *)


    Check sintegralEnnsfun.
    Check (comp (sintegral _) (fun x : nat => nnsfun_approx HMT measurable_mapP x)).
    Search measurable_fun topology.lim.

    have Questionable : forall μ : giryType T,
         (topology.lim
           (topology.fmap (sintegral μ \o (fun x : nat => nnsfun_approx HMT measurable_mapP x))
              (@topology.nbhs nat (topology.topology_set_system__canonical__topology_Filtered nat) topology.eventually)))
      =
           (topology.lim
             (topology.fmap (fun n : nat => (\sum_(0 <= i < n) h_seq i μ)%R)
                (@topology.nbhs nat (topology.topology_set_system__canonical__topology_Filtered nat) topology.eventually))).
    { intros AAAA. (* ???? *)
      simpl.
      intro μ.

      (* Rewriting sintegral *)
      have X1 : (comp (sintegral μ) (fun x : nat => nnsfun_approx HMT measurable_mapP x)) =
                (fun x : nat => (sintegral μ (nnsfun_approx HMT measurable_mapP x))).
      { intros What1 What2. rewrite /comp. apply functional_extensionality. intro x. simpl.
        admit. }
      erewrite X1. Unshelve. 2: apply AAAA. (* ???? *)
      clear X1.
      have X2 : forall n : nat,
        sintegral μ (nnsfun_approx HMT measurable_mapP n)
        =
          (\sum_(x <- finite_support 0 [set r | 0 < r]
              (fun x : join_Num_POrderedZmodule_between_GRing_Nmodule_and_Order_POrder R =>
               (x%:E * μ (nnsfun_approx HMT measurable_mapP n @^-1` [set x]))%E))
    (x%:E * μ (nnsfun_approx HMT measurable_mapP n @^-1` [set x]))%E)%R.
      { intros What1 What2 What3.
        intro n.

        rewrite (@sintegralEnnsfun _ _ R μ (nnsfun_approx HMT measurable_mapP n)).
        simpl.
        admit.
      }
    rewrite (functional_extensionality _ _ (X2 AAAA AAAA AAAA)).
    clear X2.
    simpl.
    f_equal.
    f_equal.
    apply functional_extensionality.
    intro n.
    simpl.

    (* have Strange : forall z, h_seq z μ = (z%:E * μ (nnsfun_approx HMT measurable_mapP n @^-1` [set z]))%R.  *)

    (* FIXME: Next step-- is this provable? *)
    (* Check [set r | 0 < r].
    Check index_iota 0 n. *)

    (* Aside from coercion hell, we should be able to define
       h_seq = (x%:E * μ (nnsfun_approx HMT measurable_mapP n @^-1` [set x])) *)
    (* I think that some of this could be avoided by just picking a single RealType? I see these weird
     types join_Num_POrderedZmodule_between_GRing_Nmodule_and_Order_POrder so think it originates from
     some inference related to coercions. Plus, it's weird that I can't use the type that's displayed
     for sintegralEnnsfun... that "finite support" magically pops up when I declare it using the type
     from sintegralEnnsfun  *)
    admit.
    }
    rewrite (functional_extensionality _ _ (Questionable _)).
    clear Questionable.

    refine (@ge0_emeasurable_fun_sum _ (giryM T) R setT h_seq _ _).
    - (* Probably doable for sane h_seq *)
      admit.

    (* Need to prove h_seq is measurable *)
    (* mult. measurable is measurable *)
    (* measure ofnnsfun_approx is measurable? *)
    (* - Regardless of a lemma for this, there should be a lemma for finite sums, which that is. *)
    (* Then I just need measuring a set is measurable, which is giryM_eval_def_measurable? Or something like that. *)


    (*
    Restart.

    have H1 : (forall x : T, [set: T] x -> (0%R <= f x)%E) by admit.
    have H2 : d.-measurable [set: T] by admit.
    (*

    Check @is_cvg_sintegral d T R.

    Search (topology.lim (topology.fmap _ _) = _).

    Check @emeasurable_fun_cvg _ (giryM T) R setT _
      (fun μ : giryType T =>
         topology.lim
           (topology.fmap (sintegral μ \o (fun x : nat => nnsfun_approx _ measurable_mapP x))
              (@topology.nbhs nat (topology.topology_set_system__canonical__topology_Filtered nat) topology.eventually))).
    (* Maybe, but this is not my main approach. *)


    (* I want to pull terms through that limit to eventually get to the limit of approximations of f. *)
    (* f x is the limit of approximations evaluated at x *)
    Check @cvg_nnsfun_approx d T R setT H2 f (@measurable_mapP _ _ _ _ f) H1.
    (* Search topology.lim topology.cvg_to. *)

    Search measurable_fun topology.lim.
    *)



    (* Check sequences.congr_lim. (* Only aesthetically useful *) *)

    (* Relate cvg_lim to lim *)
    (* Check topology.cvg_lim. *)

    (* Approximations converge to the limit *)
    (* Check is_cvg_sintegral. (* Limit of sintegral *) *)

    (* Check approximation. (* Use on Hypothesis. *) *)

    (* Can I turn the lim thing into a cvg_to problem? *)


    (* Can I simplify the sintegral? *)
    (* Check sintegralEnnsfun. (* Turn integral into sum *)
    Search topology.fmap (_ \o _).
    Check fun μ => @sintegralE d T R _. *)
    (* (μ \o (fun x : nat => nnsfun_approx HMT measurable_mapP x)). *)


    (* Check topology.fmap_comp (sintegral _) (fun x : nat => nnsfun_approx _ measurable_mapP x). *)

    (* Search topology.lim topology.fmap topology.eventually.
    Search topology.lim sintegral.

    Search topology.fmap sintegral.
    Search measurable_fun. *)




    (* I don't know if I can do much more with measurable_fun? Maybe MCT? since it's about th emeasurability of a limit? *)
    (* Locate cvg_monotone_convergence. *)

    (* Search measurable_fun.
    rewrite /measurable_fun.
    intros _.
    intros B HB.
    rewrite setTI.
     *)

      (*
        What is this stuff. Why did I save it.
        measurable_fun_esups:
        measurable_fun_limn_esup:
        measurableT_comp:
        measurable_fun_sups:
        measurable_comp:
        measurable_fun_limn_sup:
       *)

    (* Search measurable_fun topology.lim. *)
    rewrite /sintegral/=.
*)
*)
  Admitted.

  HB.instance Definition _ {f : measurable_map T (\bar R)} (Hf : forall x : T, (0%R <= f x)%E):=
    isMeasurableMap.Build _ _ (giryM T) (\bar R) (giryM_integrate_def Hf) (giry_meas_integrate Hf).

End giryM_integrate_laws.


(** Public definition for integrate (integral over nonnegative measurable functions into borelER)*)
Definition giryM_integrate {R : realType} {d} {T : measurableType d} (f : measurable_map T (\bar R))
    (Hf : forall x : T, (0%R <= f x)%E) :
    measurable_map (@giryM R _ T) (\bar R)
  := (giryM_integrate_def Hf).

(** Public equality for integrate *)
Lemma giryM_integrate_eval {R : realType} {d} {T : measurableType d} (f : measurable_map T (\bar R)) (Hf : forall x : T, (0%R <= f x)%E) :
  forall μ, (giryM_integrate Hf μ = \int[μ]_x (f x))%E.
Proof. done. Qed.

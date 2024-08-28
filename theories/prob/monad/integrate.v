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
  Notation borelER := (borelER (R := R)).
  Context {d} {T : measurableType d}.

  Local Open Scope classical_set_scope.

  (* TODO:
      I changed the definition to take functions to borelER rather than (\bar R)
      IIUC the default sigma algebra on (\bar R) is the Lebesge SA
      borelER is strictly weaker in terms of measurability, and I think it's enough
      for what we need, but I'm not totally sure yet.

      It also breaks the proof skeleton below.

      I also added the restriction that we only integrate nonnegative functions to the
      definition, since it's necessary in the measuability proof and we're only
      exposing the measurable interface. Might consider adding nonnegative functions
      into borelER into the hierarchy.
   *)

  Local Definition giryM_integrate_def {f : measurable_map T borelER} (Hf : forall x : T, (0%R <= f x)%E) : giryM T -> borelER
    := fun μ => (\int[μ]_x (f x))%E.

  Local Lemma giry_meas_integrate {f : measurable_map T borelER} (Hf : forall x : T, (0%R <= f x)%E) :
    measurable_fun setT (giryM_integrate_def Hf).
  Proof.
    rewrite /giryM_integrate_def.
    rewrite /=/salgebraType.
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
      { intros What1 What2. rewrite /comp. apply functional_extensionality. intro x. simpl. admit. }
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
    *)
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
  Admitted.

  HB.instance Definition _ {f : measurable_map T borelER} (Hf : forall x : T, (0%R <= f x)%E):=
    isMeasurableMap.Build _ _ (giryM T) borelER (giryM_integrate_def Hf) (giry_meas_integrate Hf).

End giryM_integrate_laws.


(** Public definition for integrate (integral over nonnegative measurable functions into borelER)*)
Definition giryM_integrate {R : realType} {d} {T : measurableType d} {f : measurable_map T (@borelER R)}
    (Hf : forall x : T, (0%R <= f x)%E) :
    measurable_map (@giryM R _ T) (@borelER R)
  := (giryM_integrate_def Hf).

(** Public equality for integrate *)
Lemma giryM_integrate_eval {R : realType} {d} {T : measurableType d} {f : measurable_map T (@borelER R)}  (Hf : forall x : T, (0%R <= f x)%E) :
  forall μ, (giryM_integrate Hf μ = \int[μ]_x (f x))%E.
Proof. done. Qed.

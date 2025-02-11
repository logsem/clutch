(*

Giry Monad definition


Definition preimage_class_of_measures (S : set T) : set (set (giryType T)) :=
  @preimage_class (giryType T)
    (\bar R)                  (* Range type *)
    setT                      (* Domain set *)
    (fun μ => μ S)              (* Evaluation function *)
    'measurable               (* Range sets *).

Definition giry_subbase : set (set (giryType T))
  := [set C | exists (S : set T) (_ : measurable S), preimage_class_of_measures S C].

Definition giry_measurable : set (set (giryType T)) := <<s giry_subbase>>.


Definition giryM_display `{R : realType} `{d : measure_display} `{T : measurableType d} :=
  sigma_display (@giry_subbase R d T).
Global Arguments giryM_display {_} {_} {_}.

(** Use giryM for any Giry Monad type *)
Definition giryM (R : realType) (d : measure_display) (T : measurableType d) : measurableType giryM_display :=
  [the measurableType _ of g_sigma_algebraType (@giry_subbase R d T)].
Global Arguments giryM {_} {_} _.

Lemma giryM_ext (μ1 μ2 : giryM T) (H : forall S : set T, μ1 S = μ2 S) : μ1 = μ2.
Proof.
  apply functional_extensionality in H.
  move: H.
  move: μ1 μ2 => [x [[x1] x2 [x3] [x4] [x5 [x6]] [x7]]] [y [[+] + [+] [+] [+ [+]] [+]]] /= xy.
  rewrite -{}xy => y1 y2 y3 y4 y5 y6 y7.
  f_equal.
  by rewrite
    (_ : x1 = y1)//
    (_ : x2 = y2)//
    (_ : x3 = y3)//
    (_ : x4 = y4)//
    (_ : x5 = y5)//
    (_ : x6 = y6)//
    (_ : x7 = y7)//.
Qed.

  Definition base_eval_internal {d1} {T1 : measurableType d1} (S : set T1) (HS : measurable S) :
      giryM T1 -> \bar R :=
    fun μ => μ S.
  Axiom base_eval_meas : forall {d1} {T1 : measurableType d1} (S : set T1) (HS : measurable S),
    measurable_fun setT (base_eval_internal HS).

  (* External
  Definition eval {d1} {T1 : measurableType d1} (S : set T1) :
  *)

(*
Section giryNotation.
  Notation "T .-giry" := (@giryM_display _ T) : measure_display_scope.
  Notation "T .-giry.-measurable" := ((@measurable _ (giryM T)) : set (set (giryM T))) : classical_set_scope.
End giryNotation.
*)

*)

(*


Section discrete_space_of_maps.

  Local Open Scope classical_set_scope.

  Context {d1 d2 : measure_display}.
  Context (T1 : measurableType d1).
  Context (T2 : measurableType d2).

  (** Bundled: a measurable map equipped with the set it's measurable out of. *)
  Structure MeasurableMap (dom : set T1) : Type := {
      mf_car :> T1 -> T2;
      dom_meas : d1.-measurable dom;
      f_meas : measurable_fun dom mf_car
  }.

  Definition MeasurableMapT : Type := @MeasurableMap setT.

  Program Definition MeasurableMapT_mk (f : T1 -> T2) (Hf : measurable_fun setT f) : MeasurableMapT :=
    {| mf_car := f ; dom_meas := _; f_meas := Hf |}.
  Next Obligation. intros. by eapply @measurableT. Qed.

  Program Definition MeasurableMapT_default : MeasurableMapT :=
    @MeasurableMapT_mk (cst point) _.
  Next Obligation. intros. by apply measurable_cst. Qed.

  HB.instance Definition _ := gen_eqMixin MeasurableMapT.
  HB.instance Definition _ := gen_choiceMixin MeasurableMapT.
  HB.instance Definition _ := isPointed.Build MeasurableMapT MeasurableMapT_default.

  (*  Check ((<<discr (MeasurableMapT)>>) : measurableType _) . *)

  Definition lift (f : T1 -> T2) (H : measurable_fun setT f) : T1 -> <<discr MeasurableMapT>> :=
    cst (@MeasurableMapT_mk f H).

  (* What do we need for this to be measurable? *)
  Lemma lift_meas (f : T1 -> T2) (H : measurable_fun setT f) : measurable_fun setT (@lift f H).
  Proof.
    unfold lift.
    apply measurable_cst.
  Qed.

  (*
    unfold MeasurableMapT_mk.
    unfold measurable_fun.
    simpl.
    intros _ Y HY.
    rewrite /preimage//=.
    rewrite setTI.
    (* It's either set0 or setT becuase the choice to t doesn't matter (proof irrelevance) *)
  Admitted.
*)


End discrete_space_of_maps.

*)

(*
Section subset_salgebra_instance.
Local Open Scope classical_set_scope.

Context d1 (T1 : measurableType d1).

(* Hierachy Builder problem:
    I want to make a sigma algebra over {a : T1 | A a}
    In order to do that, I need {a : T1 | A a} to be pointed (for some reason)
    In order to do that, I need to internalize the nonemptiness into the type, or else it breaks the canonical structures.
    Hopefully that explains the insane type here I'm using here.
 *)

Definition ne_subset (A : set T1) (p : T1) (_ : A p) : Type := {a : T1 | A a}.


(* The type of subsets of A. Has to be written this way to work wiht the sigma algebra construction, even though it's annoying to use later.*)

Definition sub (A : set T1) {p : T1} (Hp : A p) : Type := set (@ne_subset A _ Hp).

Definition sub_to_ambient (A : set T1) {p : T1} (Hp : A p) (s : @sub A p Hp) : set T1 :=
  [set (proj1_sig x) | x in s ].

(* A subset S1 of A is the intersection of a larger set S2 with A *)
Program Definition is_restriction (A : set T1) {p : T1} (Hp : A p) (S1 : @sub A p Hp) (S2 : set T1) : Prop :=
  forall a : T1, forall H : A a, S2 a <-> S1 _.
Next Obligation. intros A S1 S2 a H p Hp. unfold ne_subset. exists p. apply Hp. Defined.
(* For all elements a, if a is in A, then a is in S2 iff a is in S1*)

(* The sigma algebra is the set of subsets of A, which are equal to restrictions of a measurable set. *)
Definition subset_system {A : set T1} {p : T1} (Hp : A p) (_ : d1.-measurable A) : set (@sub A p Hp) :=
  [set X | exists M : set T1, d1.-measurable M /\ is_restriction X M].

Lemma subset_algebra_set0 {A : set T1} {p : T1} (Hp : A p) (H : d1.-measurable A) : subset_system H (set0 : @sub A p Hp).
Proof.
  unfold subset_system; simpl.
  exists set0.
  split.
  - by apply measurable0.
  - rewrite /is_restriction.
    intros a Ha.
    by simpl.
Qed.

Lemma subset_algebra_setC {A : set T1} {p : T1} (Hp : A p) (H : d1.-measurable A) (B : @sub A p Hp) :
  @subset_system A p Hp H B ->
  @subset_system A p Hp H (~` B).
Proof.
  unfold subset_system; simpl.
  intros [S [HS HBS]].
  exists (~` S).
  split.
  - simpl.
    by apply measurableC.
  - unfold is_restriction.
    simpl.
    intros a Ha.
    rewrite /is_restriction in HBS.
    have HBS' := HBS a Ha.
    (* Deal with HB's idiotic reflections, then trivial *)
    admit.
Admitted.


Definition subset_algebra_bigcup {A : set T1} {p : T1} (Hp : A p) (H : d1.-measurable A) (F : sequences.sequence _) :
  (forall i, @subset_system A p Hp H (F i)) ->
  @subset_system A p Hp H (\bigcup_i (F i)).
Proof.
  intro H1.
  unfold subset_system.
  simpl.
  exists ((\bigcup_i (sub_to_ambient (F i))) `&` A).
  split.
  - rewrite setI_bigcupl.
    apply bigcup_measurable.
    intros k _.
    apply measurableI; last by trivial.
    unfold subset_system in H1.
    destruct (H1 k) as [S [H3 H4]].
    unfold sub_to_ambient.
    unfold is_restriction in H4.
    admit.
  - unfold is_restriction.
    intros a Ha.
    split.
    - intro H2.
      admit.
    - intro H2.
      admit.
Admitted.

(* Why do sigma algebras have to be pointed??? This is stupid *)

Definition make_point {A : set T1} {p : T1} (Hp : A p) : @ne_subset A p Hp :=
  exist _ p Hp.

HB.instance Definition _ {A : set T1} {p : T1} (Hp : A p) := isPointed.Build (@ne_subset A p Hp) (make_point Hp).

Definition sub_display (A : set T1) : measure_display.
Proof. exact. Qed.

(*
HB.instance Definition subset_algebra_mixin {A : set T1} (H : d1.-measurable A) {p : T1} (Hp : A p) :=
  @isMeasurable.Build
    (sub_display A)
    (@ne_subset A p Hp)
    (@subset_system H)
    (@subset_algebra_set0)
    (@subset_algebra_setC)
    (@subset_algebra_bigcup).
*)
*)

(*
  Lemma base_eval_measurable {d1} {T1 : measurableType d1} (S : set T1) (HS : measurable S):
    measurable_fun [set: giryM T1] ((SubProbability.sort (R:=R))^~ S).
  Proof.
    eapply @measurability.
    { rewrite /measurable/=.
      symmetry.
      rewrite smallest_id.
      - done.
      - constructor.
        - by apply emeasurable0.
        - intros ??.
          rewrite setTD.
          by apply emeasurableC.
        - by apply bigcupT_emeasurable.
    }
    rewrite /measurable/=.
    rewrite {2}/giry_subbase/=.
    apply  (@subset_trans _ (giry_subbase (T:=T1))); last by apply sub_gen_smallest.
    rewrite /subset/=.
    intros X.
    rewrite /preimage_class/=.
    intros [Y HY <-].
    rewrite {1}/giry_subbase/=.
    exists S, HS.
    rewrite /preimage_class_of_measures/preimage_class/=.
    exists Y.
    - done.
    - by rewrite setTI.
  Qed.
*)
(*
  Lemma is_zero_map (μ : giryM T1) (f : T1 -> T2) (Hf : measurable_fun setT f) :
    is_zero μ -> is_zero (giryM_map f Hf μ).
  Proof.
    move=> HZ.
    unfold is_zero.
    apply giryM_ext.
    intro S.
    rewrite giryM_map_eval/pushforward HZ.
    by rewrite giryM_zero_eval giryM_zero_eval.
  Qed.
*)
(*


  Global Instance inj_map_inj_eq (f : T1 -> T2) (Hm : measurable_fun setT f) :
    Inj (=) (=) f →
    Inj (=) (=) (@giryM_map R _ _ _ _ f Hm).
  Proof.
    move=> Hf x y HI.
    have W0 : forall S, giryM_map f Hm x S = giryM_map f Hm y S.
    { rewrite HI. by intro S. }
    have W1 : forall S, pushforward x Hm S = pushforward y Hm S.
    { intro S.
      specialize W0 with S.
      by rewrite giryM_map_eval giryM_map_eval in W0. }
    rewrite /pushforward in W1.
    apply giryM_ext.
    intro S.
    have H_inj_lemma : (f @^-1` [set f x | x in S]) = S.
    { rewrite /preimage.
      apply functional_extensionality.
      intro s.
      rewrite <- (@image_inj _ _ f S s).
      - by simpl.
      - (* stdpp and ssreflect injective are the same *)
        unfold injective.
        move=> ? ? Hx.
        apply Hf, Hx.
    }
    rewrite <-H_inj_lemma.
    rewrite <-H_inj_lemma.
    apply W1.
  Qed.

  (*
  Lemma inj_map_inj (f : measurable_map T1 T2) :
    Inj (=) (=) f →
    Inj (measure_eq) (measure_eq) (@giryM_map R _ _ _ _ f).
  Proof.
    move=> Hf x y HI.
    have W0 : forall S, d2.-measurable S -> giryM_map f x S = giryM_map f y S.
    {  intro S. apply HI. }
    have W1 : forall S, d2.-measurable S -> pushforward x (@measurable_mapP _ _ _ _ f) S = pushforward y (@measurable_mapP _ _ _ _ f) S.
    { intro S.
      specialize W0 with S.
      by rewrite giryM_map_eval giryM_map_eval in W0. }
    rewrite /pushforward in W1.
    intros S HS.

    (*
    move /(_ (f @` S)).
    rewrite giryM_map_eval giryM_map_eval /pushforward. *)
    have H_inj_lemma : (f @^-1` [set f x | x in S]) = S.
    { rewrite /preimage.
      apply functional_extensionality.
      intro s.
      rewrite <- (@image_inj _ _ f S s).
      - by simpl.
      - (* stdpp and ssreflect injective are the same *)
        unfold injective.
        move=> ? ? Hx.
        apply Hf, Hx.
    }
    rewrite <- H_inj_lemma.
    rewrite <- H_inj_lemma.
    apply W1.
    rewrite H_inj_lemma.
    (* I think this is false *)
  Abort.
*)
End is_zero.
 *)

(*
Section giryM_integrate_laws.
  Context `{R : realType}.
  Notation giryM := (giryM (R := R)).
  Context {d} {T : measurableType d}.

  Local Open Scope classical_set_scope.

  Context {f : T -> (\bar R)}.
  Context (Hf : forall x : T, (0%R <= f x)%E).

  Definition giryM_integrate : giryM T -> \bar R := fun μ => (\int[μ]_x (f x))%E.

  Axiom giryM_integrate_meas : measurable_fun setT giryM_integrate.

  (** Public equality for integrate *)
  Lemma giryM_integrate_eval : forall μ, (giryM_integrate μ = \int[μ]_x (f x))%E.
  Proof. done. Qed.

End giryM_integrate_laws.
*)
(*

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
*)

(*
Section giryM_eval.
  Context `{R : realType}.
  Notation giryM := (giryM (R := R)).
  Context {d} {T : measurableType d}.

  Context (S : set T).
  Context (HS : measurable S).

  Definition giryM_eval : giryM T -> \bar R := (fun μ => μ S).

  Lemma giryM_eval_meas : measurable_fun setT giryM_eval.
  Proof using HS R S T d. by apply base_eval_measurable. Qed.

  (** Public equality for eval *)
  Lemma giryM_eval_eval : forall μ, giryM_eval μ = μ S.
  Proof. done. Qed.

  (** Eval is nonnegative *)
  Lemma giryM_eval_nonneg : forall x : giryM T, (0%R <= giryM_eval x)%E.
  Proof.
    intro μ.
    rewrite /giryM_eval_eval.
    apply (measure_ge0 μ S).
  Qed.

End giryM_eval.




Section giryM_eval_char.
  (** Characterize measurability of A -> giryM B functions using evaluations *)
  Context `{R : realType}.
  Notation giryM := (giryM (R := R)).

  Local Open Scope classical_set_scope.

  Context {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}.
  Variable (f : T1 -> giryM T2).

  (** f has measurable_evaluations when:
      for all measurable sets S, evaluating f by S is a measurable function.
   *)
  Definition measurable_evaluations {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2} (f : T1 -> giryM T2) : Prop
    := forall (S : set T2), d2.-measurable S -> (measurable_fun setT ((f ^~ S) : T1 -> \bar R)).

  Lemma measurable_evals_if_measurable : measurable_fun setT f -> measurable_evaluations f.
  Proof.
    intros Hm.
    rewrite /measurable_evaluations.
    intros S HS.
    replace (fun x : T1 => f x S) with ((@^~ S) \o f); last by apply functional_extensionality.

    apply (@measurable_comp _ _ _ _ _ _ setT (@^~ S : giryM T2 -> \bar R)); auto.
    { apply subsetT. }
    apply (giryM_eval_meas HS).
  Qed.


  Lemma measurable_if_measurable_evals : measurable_evaluations f -> measurable_fun setT f.
  Proof.
    intro Hm.
    rewrite /measurable_evaluations/measurable_fun/= in Hm.

    apply (@measurable_if_pushfowrard_subset _ _ _ _ f).
    rewrite {1}/measurable/=.
    apply smallest_sub.
    { rewrite /sigma_algebra.
      constructor.
      - rewrite /= preimage_set0.
        apply measurable0.
      - intros ?.
        simpl.
        intro HA.
        rewrite setTD.
        rewrite -preimage_setC.
        apply measurableC.
        apply HA.
      - simpl.
        intros S MS.
        rewrite preimage_bigcup.
        apply bigcup_measurable.
        intros k _.
        apply MS.
    }
    rewrite /giry_subbase/subset/=.
    intros X [Y [HY HX]].

    have G1 : d1.-measurable [set: T1] by auto.
    specialize (Hm Y HY G1).
    rewrite /g_sigma_algebraType/= in Hm.
    clear G1.

    rewrite /preimage_class_of_measures/preimage_class/= in HX.
    destruct HX as [B HB HBf].
    rewrite setTI in HBf.

    specialize (Hm B HB).
    rewrite setTI in Hm.

    rewrite <- HBf.
    rewrite <- comp_preimage.
    simpl.

    have HF : (fun x : T1 => f x Y) = ((SubProbability.sort (R:=R))^~ Y \o f).
    { apply functional_extensionality.
      intro x.
      by simpl.
    }

    rewrite HF in Hm.
    apply Hm.
  Qed.

  (** A function A -> giryM B is measurable iff its evaluation function at every S is measurable. *)
  Lemma measurable_evals_iff_measurable : measurable_evaluations f <-> measurable_fun setT f.
  Proof. split; [apply measurable_if_measurable_evals | apply measurable_evals_if_measurable]. Qed.

End giryM_eval_char.

*)

(*
Section giry_ret.
  Context `{R : realType}.
  Notation giryM := (giryM (R := R)).
  Context {d} {T : measurableType d}.

  Definition giryM_ret : T -> giryM T := fun t0 => @dirac _ T t0 _.

  Lemma giry_ret_measurable : @measurable_fun _ _ T (giryM T) setT giryM_ret.
  Proof.
    apply measurable_evals_iff_measurable.
    rewrite /measurable_evaluations.
    intros S SMeas.
    rewrite /measurable_fun/= .
    intros ? Y HY.
    (* NOTE: Since its using 'measurable, it seems that Borel or Lebesgue doesn't matter here.  *)
    remember (fun x : T => (\d_x)%R S) as f.
    rewrite /dirac in Heqf.
    have W : f = (comp EFin (indic S)).
    { apply functional_extensionality. intro. by rewrite Heqf/=. }
    rewrite W.
    rewrite setTI.
    rewrite comp_preimage.
    rewrite preimage_indic.
    remember (in_mem GRing.zero (mem (preimage EFin Y))) as B1; rewrite -HeqB1.
    remember (in_mem (GRing.one R) (mem (preimage EFin Y))) as B2; rewrite -HeqB2.
    destruct B1; destruct B2; simpl.
    - apply H.
    - apply measurableC, SMeas.
    - apply SMeas.
    - apply measurable0.
  Qed.

  (** Public equality for ret *)
  Lemma giryM_ret_eval (t : T) : forall z, giryM_ret t z = dirac t z.
  Proof. auto. Qed.

End giry_ret.
*)

(*
Section giryM_join_definition.
  Context `{R : realType}.
  Notation giryM := (giryM (R := R)).
  Context {d} {T : measurableType d}.

  Local Open Scope classical_set_scope.

  (* Specification of giryM_join as an integral *)
  Local Definition giryM_join_def (m : giryM (giryM T)) : (set T -> \bar R)
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
        by apply (@measurableT _ (g_sigma_algebraType _)).
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
      have Setoid1 (S1 S2 S3 : topology.set_system (extended (Real.sort R))) :
        (S1 = S2) -> topology.cvg_to S1 S3 -> topology.cvg_to S2 S3 by move=>->.
      have Setoid2 G H : (G = H) -> (topology.nbhs G) = (topology.nbhs H) by move=>->.
      have Setoid3 (G H : nat -> (extended (Real.sort R))) S : (G = H) -> topology.fmap G S = topology.fmap H S by move=>->.
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
        rewrite topology.fmap_comp.
        reflexivity.
      }

      (* Now I want to take the union of the sequence, turn it into bigcup *)
      (* Or go the other way around: rewrite RHS to comp and cancel the cts function integrate *)
      (* The former seems easier *)


      (* Finish using one of these:
      Check topology.cvg_fmap.
      Search (topology.fmap _ (topology.nbhs _)).
      Check topology.cvg_fmap2.
      Search (topology.nbhs (topology.fmap _ _)).
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
      apply (Order.le_trans H).
      rewrite mul1e.
      apply sprobability_setT.
    Qed.

    HB.instance Definition _ :=  Measure_isSubProbability.Build _ _ _ (giryM_join_def m) giryM_join_setT.

  End giryM_join_measure_def.

  (* Workaround for HB bindings issue *)
  Definition giryM_join : giryM (giryM T) -> (giryM T) := giryM_join_def.

  (* The measurable evaluation function which computes the giryM_join_def on measurable sets *)
  Definition giryM_join_meas_map_pre {S : set T} (HS : d.-measurable S) : (giryM (giryM T)) -> (\bar R) :=
    @giryM_integrate R _ (giryM T) (giryM_eval S).

  (* giryM_join_def equals the measurable evaluation function at each measruable set *)
  Lemma giryM_join_meas_map_pre_spec {S : set T} (HS : d.-measurable S) (m : giryM (giryM T)):
      giryM_join_meas_map_pre HS m = giryM_join m S.
  Proof. by rewrite /giryM_join_meas_map_pre giryM_integrate_eval /giryM_join_def. Qed.

  Lemma giryM_join_def'_measurable : @measurable_fun _ _ (giryM (giryM T)) (giryM T) setT giryM_join.
  Proof.
    (*
    apply measurable_if_measurable_evals.
    rewrite /giryM_join_def'/measurable_evaluations.
    intros S HS.
    have H1 : (fun x : giryM (giryM T) => giryM_join_def x S) = (fun x : giryM (giryM T) => giryM_join_meas_map_pre HS x).
    { apply functional_extensionality.
      intros ?.
      by rewrite giryM_join_meas_map_pre_spec.
    }
    rewrite H1.
    rewrite /giryM_join_meas_map_pre. *)
  Admitted.

  (*
  Lemma giryM_join_eval {R : realType} {d} {T : measurableType d} (m : giryM  (giryM T )) :
    forall (S : set T), (giryM_join m S = \int[m]_μ (μ S))%E.
  Proof. done. Qed.
*)
End giryM_join_definition.
*)

(*
Section giryM_map_definition.
  Context `{R : realType}.
  Notation giryM := (giryM (R := R)).
  Context {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2}.

  Local Open Scope classical_set_scope.

  Context (f : T1 -> T2).
  Context (Hf : measurable_fun setT f).
  Context (m : giryM T1).

  Local Definition giryM_map_def : set T2 -> \bar R :=
    fun A => m (f @^-1` A).

  Local Lemma giryM_map_def_pushforward_equiv (S : set T2) :
      giryM_map_def S = pushforward m Hf S.
  Proof. by rewrite /pushforward/giryM_map_def. Qed.

  Local Lemma giryM_map_def_0 : giryM_map_def set0 = 0%E.
  Proof using Hf R T1 T2 d1 d2 f m.
    rewrite giryM_map_def_pushforward_equiv.
    apply (measure0 (pushforward m Hf)).
  Qed.

  Local Lemma giryM_map_def_ge0 A : (0 <= giryM_map_def A)%E.
  Proof using Hf R T1 T2 d1 d2 f m.
    rewrite giryM_map_def_pushforward_equiv.
    apply (measure_ge0 (pushforward m Hf)).
  Qed.

  Local Lemma giryM_map_def_semi_additive : semi_sigma_additive giryM_map_def.
  Proof using Hf R T1 T2 d1 d2 f m.
    rewrite (functional_extensionality _ _ giryM_map_def_pushforward_equiv).
    apply (@measure_semi_sigma_additive _ _ _ (pushforward m Hf)).
  Qed.

  Local Lemma giryM_map_def_setT : (giryM_map_def setT <= 1)%E.
  Proof using Hf R T1 T2 d1 d2 f m.
    rewrite giryM_map_def_pushforward_equiv.
    rewrite /pushforward.
    rewrite preimage_setT.
    apply sprobability_setT.
  Qed.

  HB.instance Definition _
    := isMeasure.Build _ _ R
         (giryM_map_def )
         (giryM_map_def_0 )
         (giryM_map_def_ge0 )
         (@giryM_map_def_semi_additive ).

  HB.instance Definition _ := Measure_isSubProbability.Build _ _ _ giryM_map_def giryM_map_def_setT.

  Definition giryM_map : giryM T2 := giryM_map_def.

  (*
  Local Lemma giryM_map_def_is_measurable (f : measurable_map T1 T2) :
    @measurable_fun _ _ (giryM T1) (giryM T2) setT (giryM_map_def f).
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
  *)


End giryM_map_definition.





Section giryM_map.
  Context `{R : realType}.
  Notation giryM := (giryM (R := R)).
  Context {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2}.

  Axiom giryM_map_meas :
    forall (f : T1 -> T2) (Hf : measurable_fun setT f), @measurable_fun _ _ (giryM T1) (giryM T2) setT (giryM_map Hf).
    (*
    apply measurable_if_measurable_evals.
    rewrite /measurable_evaluations.
    intros S HS.
    rewrite /giryM_map_def'.
    erewrite functional_extensionality.
    2: {
      intro m.
      rewrite /= giryM_map_def_pushforward_equiv.
      reflexivity.
    }
    simpl.
    *)
    (*
    apply measurable_if_pushfowrard_subset.
    Check (@measurability _ _ _ _ setT _ ereal_borel_subbase _).
    Search subset smallest.
    rewrite /subset.
    intros Rs HRs.
    simpl.
    rewrite /pushforward.
    rewrite /preimage.
     *)
End giryM_map.



Section giryM_map_external.
  Context `{R : realType}.
  Notation giryM := (giryM (R := R)).
  Context {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2}.
  Local Open Scope classical_set_scope.

  (** This definition doesn't need a proof of the measurability of f at definition-time. *)
  Definition giryM_map_external (f : T1 -> T2) (m : giryM T1) : giryM T2 :=
    @extern_if (giryM T2) (measurable_fun setT f) giryM_zero (fun H => giryM_map H m) .


  (** Public equality for giryM_map *)
  Lemma giryM_map_eval  (f : T1 -> T2) (Hf : measurable_fun setT f) :
    forall μ S, (@giryM_map R _ _ _ _ f Hf μ) S = pushforward μ Hf S.
  Proof.
    intros μ S.
    rewrite /giryM_map/giryM_map_def.
    rewrite -giryM_map_def_pushforward_equiv.
    simpl.
    done.
  Qed.


End giryM_map_external.

Global Arguments giryM_map {_} {_} {_} {_} {_} _.
*)

(*
Section bind.
  Context `{R : realType}.
  Notation giryM := (giryM (R := R)).
  Context {d1} {T1 : measurableType d1}.
  Context {d2} {T2 : measurableType d2}.

  Definition giryM_bind (f : T1 -> (giryM T2)) (Hf : measurable_fun setT f): giryM T1 -> giryM T2
    := ssrfun.comp giryM_join (giryM_map f Hf).

  (** This is probably the one you want to use *)
  Definition giryM_bind_external (m : giryM T1) (f : T1 -> (giryM T2)) : giryM T2 :=
    giryM_join (giryM_map_external f m).

  Lemma giryM_bind_external_eq (m : giryM T1) (f : T1 -> (giryM T2)) (H : measurable_fun setT f) :
    giryM_bind_external m f = giryM_bind H m.
  Proof.
    rewrite /giryM_bind_external/giryM_bind/giryM_map_external.
    rewrite /ssrfun.comp//=.
    f_equal.
    by rewrite extern_if_eq.
  Qed.

  Definition giryM_bind_meas (f : T1 -> (giryM T2)) (Hf : measurable_fun setT f):
    measurable_fun setT (@giryM_bind f Hf).
  Proof. Admitted.

  (** Use this form when you want bind to be measurable *)
  Lemma giryM_bind_external'_meas (f : T1 -> (giryM T2)) (Hf : measurable_fun setT f) :
    measurable_fun setT (giryM_bind_external ^~ f).
  Proof.
    suffices -> : (giryM_bind_external^~ f) = (@giryM_bind f Hf) by apply giryM_bind_meas.
    apply functional_extensionality.
    intro m.
    by apply giryM_bind_external_eq.
  Qed.

End bind.

*)

(*


(**
    The Giry Probability Monad

    Types:
      measurable_map T1 T2 (written T1 -mm-> T2 )
        - coerces to regular functions T1 -> T2

      giryM T
        - measurable type of probability subdistributions over T

      <<discr T>>
        - measurable type for the discrete space on a pointed type T

      borelER
        - Borel type on the extended real numbers


    Notations:
      p =μ q
        - p, q are equal on all measurable sets


    Definitions:
    - Each function giryM_X has an evaluation function giryM_X_eval.
    - The definition itself should not be unfolded!

      m_id                                            : A -mm-> A
      m_cmp (f : B -mm-> C) (g : A -mm-> B)           : A -mm-> C
      m_cst (k : B)                                   : A -mm-> B

      m_discr (f : A -> B)                            : <<discr A>> -mm-> B

      giryM_zero                                      : giryM A
      giryM_eval (S : measurable set A)               : giryM A -mm-> \bar R
      giryM_integrate (f : nonnegative A -> borelER)  : giryM A -mm-> \bar R
      giryM_map (f : A -mm-> B)                       : giryM A -mm-> giryM B

      giryM_ret                                       : A -mm-> giryM A
      giryM_join                                      : giryM (giryM A) -mm-> giryM A

      giryM_unif (m : nat)                            : giryM <<discr ('I_(S m))>>


    Derived forms:
      giryM_bind (f : A -mm-> giryM B)                : giryM A -mm-> giryM B
      giryM_iterN (n : nat) (f : A -mm-> giryM A)     : A -mm-> giryM A


    Laws:
      giryM_join (giryM_zero)                 =    giryM_zero
      giryM_integrate f (giryM_join m)        =    giryM_integrate (giryM_integrate f) m  ** for f nonnegative
      giryM_map f giryM_zero                  =    giryM_zero
      giryM_map (m_cst k) t                   =    giryM_ret R k                          ** for t proper
      giryM_integrate g (giryM_map f t)       =    giryM_integrate (m_cmp g h)            ** for g, (g ∘ h) nonnegative
      giryM_join (giryM_map (giryM_map f) m)  =μ   giryM_map f (giryM_join m)
      giryM_join (giryM_map giryM_join m)     =    giryM_join (giryM_join m)              !! Aborted !!
      giryM_join (giryM_map giryM_ret t)      =μ   t
      giryM_join (giryM_ret t)                =μ   t
      giryM_bind f giryM_zero                 =    giryM_zero
      giryM_bind (m_cst giryM_zero) t         =μ   giryM_zero
      giryM_bind f m S                        =    \int[m]_x (f x S)                      !! Refactor me !!
      giryM_bind f (giryM_ret t)              =μ   f t
      giryM_bind giryM_ret m                  =μ   m
      giryM_bind g (giryM_bind f m)           =μ   giryM_bind (m_cmp (giryM_bind g) f) m
      giryM_join m                            =    giryM_bind m_id m


 *)

Section monad_laws.
  Context `{R : realType}.
  Notation giryM := (giryM (R := R)).

  Local Open Scope classical_set_scope.

  (*
  Lemma giryM_join_zero {d1} {T1 : measurableType d1} : giryM_join giryM_zero = (giryM_zero: giryM T1).
  Proof.
    apply giryM_ext.
    intro S.
  Admitted.
  (*
    rewrite giryM_join_eval.
    rewrite giryM_zero_eval.
    by rewrite integral_measure_zero.
  Qed.
*)

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
      unfold Order.le in HR.
      simpl in HR.
      unfold FunOrder.lef in HR.
      by rewrite asboolE in HR.
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
      have HR := (@nd_nnsfun_approx _ _ _ _ HM _ Hfmf n' m' Hle).
      unfold Order.le in HR.
      simpl in HR.
      unfold FunOrder.lef in HR.
      by rewrite asboolE in HR.
    - by intros ??; apply Hf.
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

      (*
      (* Might need to do this directly.. I can't find any relevant theorems for this type of sum *)
      (* Surely this proof was done somewhere else so I'm confident it's possible. *)
      intros x y Hle.
      have H1 : range (nnsfun_approx HM Hfmf x) = range (nnsfun_approx HM Hfmf y).
      { unfold range.
        simpl.
        apply functional_extensionality.
        intro r.
        simpl.
        rewrite nnsfun_approxE.
        rewrite exists2E.
        rewrite exists2E.
        (* rewrite True_and. *)
        apply propext.
        split.
        - intros [A [_ B]].
          exists A.
          rewrite True_and.
          rewrite nnsfun_approxE.
          rewrite <- B.
          unfold approx.
          admit.
        - admit.

        }

      (*  Search "le" (\sum_(_ \in _) _)%E. *)
      rewrite H1.
      apply lee_fsum.
      - (* Is this even true? *)
        unfold range.
        rewrite nnsfun_approxE.

        admit.
      - intros r Hr.

        admit.
       *)

      intros x y Hle.
      admit.


    - (* Sequence is nonnegative *)
      intros n μ _.
      rewrite /= fsume_ge0 //=.
      intros i [t ? <-].
      apply mule_ge0.
      +
        rewrite nnsfun_approxE.
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
      rewrite nnsfun_approxE.
      (* Is this even true? *)
      unfold range.
      unfold finite_set.
      simpl.
      exists n. (* Seems right but not 100% sure *)
      simpl.
      (* Check card_II.
         Search card_eq mkset.
         rewrite nnsfun_approxE. *)
      admit.
    - (* Argument is nonnegative *)
      intros n' μ _.
      apply mule_ge0.
      +
        unfold Order.le.
        simpl.
        (* Oh no, this is not provable... *)
        admit.
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
        (*
        Search integrable measurable.
        Check base_eval_measurable. *)
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
  *)

  Lemma giryM_map_zero {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2} (f : T1 -> T2) (Hf : measurable_fun setT f) :
      giryM_map f Hf giryM_zero  = (giryM_zero : giryM T2).
  Proof.
    apply giryM_ext.
    intro S.
    rewrite giryM_map_eval.
    rewrite giryM_zero_eval.
    by rewrite /=/mzero/pushforward.
  Qed.

  (*


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
    rewrite ge0_integral_pushforward; cycle 1.
    - by apply measurable_mapP.
    - by apply (@measurable_mapP _ _ _ _ g).
    - by apply Hg.
    f_equal.
  Qed.

  Lemma giryM_join_map_map {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}
      (mf : measurable_map T1 T2) (m : giryM (giryM T1)) :
    giryM_join (giryM_map (giryM_map mf) m) ≡μ giryM_map mf (giryM_join m).
  Proof.
    intros S HS.
    rewrite giryM_join_eval.
    rewrite ge0_integral_pushforward; cycle 1.
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
    rewrite ge0_integral_pushforward; cycle 1.
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
    rewrite ge0_integral_pushforward; cycle 1.
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
    rewrite ge0_integral_pushforward /=; cycle 1.
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
    rewrite ge0_integral_pushforward; cycle 1.
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
    rewrite ge0_integral_pushforward; cycle 1.
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
    rewrite ge0_integral_pushforward; cycle 1.
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
    rewrite ge0_integral_pushforward; cycle 1.
    - by apply measurable_mapP.
    - by apply @measurable_mapP.
    - by apply IHF'.
    rewrite ge0_integral_pushforward; cycle 1.
    - by apply measurable_mapP.
    - by apply base_eval_measurable.
    - by intro u; apply (measure_ge0 u).
    f_equal.
    apply functional_extensionality.
    intro t.
    simpl.
    rewrite giryM_integrate_eval.
    rewrite giryM_join_eval.
    rewrite ge0_integral_pushforward; cycle 1.
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
*)
End monad_laws.

 *)(*

(*

(** ********** Test: Examples of measuring sets *)
Section giry_space_example.
  Context `{R : realType}.
  Notation giryM := (giryM (R := R)).
  Context {d : measure_display} (T : measurableType d).


  (* Example: Measuring sets in the Giry space *)
  Example test_giry_measures_0 : measurable (set0 : set (giryM T)).
  Proof. by apply measurable0. Qed.

  Example test_giry_measures_T : measurable [set: giryM T].
  Proof. by eapply @measurableT. Qed.

  (* giryM is also a measurable type, so can be nested. *)
  Example test_giry_measures_0' : measurable (set0 : set (giryM (giryM T))).
  Proof. by apply measurable0. Qed.

End giry_space_example.


(** ********** Test: Examples of integrals *)
Section giry_integral_example.
  Context {d : measure_display} (T : measurableType d).
  Context `{R : realType}.
  Notation giryM := (giryM (R := R)).

  Variable (μ_target : giryM T).  (* Some point in the space of measures on T*)

  (* The dirac measure using that point *)
  Example giry_ret_μ : giryM (giryM T) := @dirac _ _ μ_target _.

  Example int_zero_over_dirac : (\int[giry_ret_μ]_x cst 0%:E x)%E = 0%:E.
  Proof. apply integral0. Qed.

  Example int_one_over_dirac : (\int[giry_ret_μ]_x cst 1%:E x)%E = 1%:E.
  Proof.
    rewrite integral_cst /=.
    - by rewrite diracT mul1e.
    - rewrite -setC0.
      apply (@measurableC _ (giryM _)).
      by apply measurable0.
  Qed.
End giry_integral_example.



(** ********** Test: sealing *)
Section seal_example.
  Context {d : measure_display} (T : measurableType d).
  Context {d2 : measure_display} (T2 : measurableType d).
  Context {d3 : measure_display} (T3 : measurableType d).

  Context `{R : realType}.
  Notation giryM := (giryM (R := R)).

  Lemma X (S : set T) (HS : measurable S) : giryM_eval R HS = giryM_eval R HS.
  Proof.
    rewrite /giryM_eval.
    (* unfold eval.giryM_eval_def. This should be sealed! *)
    apply measurable_map_ext.
    intro μ.
    rewrite giryM_eval_eval.
    Set Printing All.
    Unset Printing All.
  Abort.

  Lemma X (v : T) : giryM_ret R v = giryM_ret R v.
  Proof.
    rewrite /giryM_ret.
    (* unfold ret.giryM_ret_def. This should be sealed! *)
    apply giryM_ext.
    intro S.
    rewrite giryM_ret_eval.
    Set Printing All.
    Unset Printing All.
  Abort.

  Lemma X (f : measurable_map T (\bar R)) (Hf : forall x : T, (0%R <= f x)%E) :
    giryM_integrate Hf = giryM_integrate Hf.
  Proof.
    rewrite /giryM_integrate.
    (* unfold integrate.giryM_integrate_def. This should be sealed! *)
    apply measurable_map_ext.
    intro μ.
    rewrite giryM_integrate_eval.
    Set Printing All.
    Unset Printing All.
  Abort.

  Lemma X (v : T2) : (m_cst v : measurable_map T T2) = m_cst v.
  Proof.
    rewrite /m_cst.
    (* unfold const.m_cst_def. This should be sealed! *)
    apply measurable_map_ext.
    intro x.
    rewrite m_cst_eval.
    Set Printing All.
    Unset Printing All.
  Abort.

  Lemma X (f : measurable_map T T2) (m1 : giryM T) : giryM_map f m1 = giryM_map f m1.
  Proof.
    rewrite /giryM_map.
    (* unfold map.giryM_map_def. This should be sealed! *)
    apply giryM_ext.
    intro S.
    rewrite giryM_map_eval.
    (* FIXME: eliminate reverse coercion!! *)
    Set Printing All.
    Unset Printing All.
  Abort.

  Lemma X : (giryM_zero : giryM T) = giryM_zero.
  Proof.
    rewrite /giryM_zero.
    (* unfold map.giryM_zero_def. This should be sealed! *)
    apply giryM_ext.
    intro S.
    rewrite giryM_zero_eval.
    Set Printing All.
    Unset Printing All.
  Abort.


  Lemma X (f : measurable_map T2 T3) (g : measurable_map T T2) : m_cmp f g = m_cmp f g.
  Proof.
    rewrite /m_cmp.
    (* unfold compose.m_cmp_def. This should be sealed! *)
    apply measurable_map_ext.
    intro t.
    rewrite m_cmp_eval.
    Set Printing All.
    Unset Printing All.
  Abort.

  Lemma X (m : giryM (giryM T)) : giryM_join m = giryM_join m.
  Proof.
    rewrite /giryM_join.
    (* unfold .m_cmp_def. This should be sealed! *)
    apply giryM_ext.
    intro S.
    rewrite giryM_join_eval.
    Set Printing All.
    Unset Printing All.
  Abort.

  Lemma X : (m_id : measurable_map T T) = m_id .
  Proof.
    rewrite /m_id.
    (* unfold .m_id. This should be sealed! *)
    apply measurable_map_ext.
    intro S.
    rewrite m_id_eval.
    Set Printing All.
    Unset Printing All.
  Abort.


End seal_example.
*)
    *)

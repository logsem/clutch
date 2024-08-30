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
      giryM_eval (S : measurable set A)               : giryM A -mm-> borelER
      giryM_integrate (f : nonnegative A -> borelER)  : giryM A -mm-> borelER
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
      giryM_map (m_cst k) t                   = giryM_ret R k

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
      (f : measurable_map T1 borelER) (Hf : forall x : T1, (0%R <= f x)%E)
      (Hf' : forall x : giryM T1, (0%R <= giryM_integrate Hf x)%E)
      (m : giryM (giryM T1)) :
    (@giryM_integrate _ _ _ f Hf) (giryM_join m) = (@giryM_integrate _ _ _ (@giryM_integrate _ _ _ f Hf)) Hf' m.
  Proof.
    (* Rewrite integral over (giryM_join M) to limit. *)
    have HM : d1.-measurable [set: T1] by apply @measurableT.
    rewrite giryM_integrate_eval.
    rewrite (nd_ge0_integral_lim (giryM_join m) _ _ (fun _ => @cvg_nnsfun_approx _ T1 R setT HM f _ _ _ _)); cycle 2.
    - by apply Hf.
    - intros x n' m' Hle.
      (* Check (@nd_nnsfun_approx _ _ _ _ _ _ _ n' m' Hle). *)
      (* Need to turn the %R comparison into %O)*)
      admit.
    - by intros ???; apply Hf.
    - by intros; simpl.
    - have f' := (@measurable_mapP _ _ _ _ f).
      (* Might be fixable by changing borelER to 'measurable*)
      admit.
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
      admit.
    - (* Argument is pointwise measurable. *)
      admit.
    - (* ⊤ is measurable *)
      apply @measurableT.

    f_equal.
    - (* The index sets are the same *)
      (* As predicted, it's way easier do prove this down here *)
      f_equal.
      apply functional_extensionality.
      intro x.

      (* rewrite (giryM_join_eval m). *)
      admit.
      (* rewrite /giryM_join. *)
      (* Scalar multiplication *)
    - (* The bodies are the same *)
      apply functional_extensionality.
      intro x.
      f_equal.
      (* Scalar multiplication *)
      admit.
  Admitted.

  Lemma giryM_join_map_map {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}
      (mf : measurable_map T1 T2) (m : giryM (giryM T1)) :
    giryM_join (giryM_map (giryM_map mf) m) = giryM_map mf (giryM_join m).
  Proof.
    apply giryM_ext.
    intro S.
    (* rewrite giryM_join_aux.
    rewrite giryM_map_aux.
    rewrite giryM_map_aux. *)
    (* rewrite giryM_join_integrate. *)
  Admitted.


  Lemma giryM_join_map_join {d1} {T1 : measurableType d1} (m : giryM (giryM (giryM T1))) :
    giryM_join (giryM_map giryM_join m) = giryM_join (giryM_join m).
  Proof. Admitted.

  Lemma giryM_join_map_ret {d1} {T1 : measurableType d1} (μ : (giryM T1)) :
    giryM_join (giryM_map (giryM_ret R) μ) = μ.
  Proof. Admitted.

  Lemma giryM_join_ret {d1} {T1 : measurableType d1} (μ : (giryM T1)) :
    giryM_join (giryM_ret R μ) = μ.
  Proof. Admitted.


  Lemma giryM_bind_0_l {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2} {f : measurable_map T1 (giryM T2)} :
    giryM_bind f giryM_zero = giryM_zero .
  Proof.
    (* rewrite /giryM_bind.
    rewrite /Mcmp/comp.
    (* FIXME *)
    Opaque giryM_join.
    Opaque giryM_map.
    simpl.
    Transparent giryM_join.
    Transparent giryM_map.
    rewrite giryM_map_zero.
    apply giryM_join_zero. *)
  Admitted.

  Lemma giryM_bind_0_r {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2} (μ : giryM T1) :
    giryM_bind (m_cst giryM_zero) μ = (giryM_zero : giryM T2).
  Proof.
    (*
    rewrite /giryM_bind.
    rewrite /Mcmp/comp.
    (* FIXME *)
    Opaque giryM_join.
    Opaque giryM_map.
    simpl.
    Transparent giryM_join.
    Transparent giryM_map.
    rewrite giryM_map_cst.
    by rewrite giryM_join_ret. *)
  Admitted.


  (* I don't know if I want this in the interface yet-- probably express it similar to join_integrate
     instead?

     Lemma giryM_bind_eval (m : giryM T1) (s : set T2) (HS : measurable s) :
     (giryM_bind f m s = \int[m]_x f x s)%E.
     Proof. Admitted.


    Lemma giryM_bind_integrate (m : giryM T1) (g : T2 -> \bar R) (mg : measurable_fun setT g) :
      (\int[giryM_bind f m]_x g x = \int[m]_a (\int[f a]_x g x))%E.
    Proof. Admitted.
   *)


  Lemma giryM_bind_ret_l {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2} {f : measurable_map T1 (giryM T2)} t :
    giryM_bind f (giryM_ret R t) = f t.
  Proof. Admitted.

  Lemma giryM_bind_ret_r {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2} {f : measurable_map T1 (giryM T2)} (m : giryM T1) :
    giryM_bind (giryM_ret R) m = m.
  Proof. Admitted.

  Lemma giryM_bind_bind {d1 d2 d3} {T1 : measurableType d1} {T2 : measurableType d2} {T3 : measurableType d3}
    {f : measurable_map T1 (giryM T2)} {g : measurable_map T2 (giryM T3)}
    (m : giryM T1) :
    giryM_bind g (giryM_bind f m) = giryM_bind (m_cmp (giryM_bind g) f) m.
  Proof.
    rewrite /giryM_bind.
  Admitted.

  Lemma giryM_join_bind {d} {T : measurableType d} (m : giryM (giryM T)) :
    giryM_join m = giryM_bind m_id m.
  Admitted.

  Lemma giryM_map_zero {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2} (f : measurable_map T1 T2) :
      giryM_map f giryM_zero = (giryM_zero : giryM T2).
  Proof.
    (* rewrite giryM_map_aux/mzero/pushforward. *)
    (* functional_extensionality doesn't work... weird *)
  Admitted.


  Lemma giryM_map_cst {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2} (μ : giryM T1) (k : T2) :
      giryM_map (m_cst k) μ = giryM_ret R k .
  Proof.
    (*
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
     *)
    (* ???? *)
    (* This whole proof is haunted *)
  Admitted.

  (* FIXME: Use Integrate instead *)
  Lemma giryM_map_integrate  {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}
      (g : measurable_map T2 (\bar R)) (h : measurable_map T1 T2) (μ : giryM T1):
    (\int[giryM_map h μ]_x g x  = \int[μ]_x g (h x))%E.
  Proof.
    (*
    rewrite giryM_map_aux.
    rewrite integral_pushforward.
    (* Can this be weakened to include negative g? *)
    - simpl.
      reflexivity.
    - admit.
    - admit.
      *)
  Admitted.
End monad_laws.

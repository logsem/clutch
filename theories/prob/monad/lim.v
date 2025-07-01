Set Warnings "-hiding-delimiting-key".
From HB Require Import structures.
From Coq Require Import Logic.ClassicalEpsilon Psatz Logic.FunctionalExtensionality Program.Wf Reals Lia.
From mathcomp Require Import ssrbool all_algebra eqtype choice boolp classical_sets num_normedtype complete_normed_module.
From Coq.ssr Require Import ssreflect ssrfun.
From mathcomp.analysis Require Import measure ereal sequences normedtype lebesgue_measure lebesgue_integral esum realfun measurable_realfun.
From mathcomp.ssreflect Require Import order.
From clutch.prob.monad Require Export giry.
Require Import mathcomp.reals_stdlib.Rstruct.
Require Import Coq.micromega.Lra.
Require Import mathcomp.reals.reals.

From mathcomp.analysis Require Import topology.

From Coq.ssr Require Import ssreflect ssrfun.

Set Warnings "hiding-delimiting-key".

Section setwise_measure_limit.
  Context {d} {T : measurableType d}.
  Context (μ : nat -> subprobability T R).
  Context (Hm : forall n, giryM_le (μ n) (μ (S n))).
  
  Local Open Scope classical_set_scope.

  Definition limit_measure (S : set T) : \bar R :=
    let _ := Hm in 
    limn_esup (fun n => μ n S).

  Lemma limit_measure0 : limit_measure set0 = 0%E.
  Proof.
    rewrite /limit_measure.
    rewrite limn_esup_lim.
    suffices -> : (esups (R := R) (fun n : nat => μ n set0)) = (fun n => (0)%E) by rewrite lim_cst.
    apply funext; intro n.
    rewrite /esups/sdrop//=. 
    eapply eq_trans_r; last (symmetry; eapply ereal_sup1).
    f_equal.
    apply funext; intro x.
    apply propext; simpl; split.
    { by intros [??<-]. }
    { move=>->//=; by exists n. }
  Qed. 

  Lemma limit_measure_ge0 X : (0 <= limit_measure X)%E.
  Proof.
    rewrite /limit_measure.
    rewrite /limn_esup/=.
    by apply: limf_esup_ge0.
  Qed. 

  Lemma cvg_limit_measure X (Hx : measurable X) : cvgn (μ ^~ X).
  Proof.
    apply ereal_nondecreasing_is_cvgn => n m Hnm.
    eapply giryM_le_mono_equiv; auto. 
    by rewrite -(rwP ssrnat.leP) in Hnm.  
  Qed. 


  Local Open Scope ereal_scope.

  Lemma semi_sigma_additive_limit_measure : semi_sigma_additive limit_measure.
  Proof.
    rewrite /semi_sigma_additive.
    intros F HF HFTriv HcupF.
    eassert (limit_measure (\bigcup_n F n) =
            limn (fun n  => (bigop.bigop.body GRing.zero (bigop.index_iota 0 n) (fun i => bigop.BigBody i GRing.add true (limit_measure (F i))))%R)
           ) as ->. 
    { 
      rewrite /limit_measure. 
      rewrite is_cvg_limn_esupE.
      2: apply cvg_limit_measure; auto.
      have -> : (fun n : nat => μ n (\bigcup_n0 F n0)) = fun n => \sum_(i <oo) μ n (F i).
      { 
        apply /funext=> n. 
        epose proof (cvg_lim _ (measure_semi_sigma_additive (s := μ n) F HF HFTriv HcupF)).
        simpl in *.
        by rewrite -H. 
      }
      have -> : ((fun n => (\sum_(0 <= i < n) limn_esup (fun n0 : nat => μ n0 (F i)))%R )= (fun n => (\sum_(0 <= i < n) limn (fun n0 : nat => μ n0 (F i)))%R)). {
        apply /funext=>x. f_equal. apply /funext=>i. 
        f_equal.
        by apply is_cvg_limn_esupE, cvg_limit_measure.
      }
      unfold giryM_le in Hm.
      rewrite -ge0_integral_count. 2 : {
        intros.
        apply /lime_ge.
        2 : { exists 0%nat; try done. }
        apply ereal_nondecreasing_is_cvgn.
        move => n m Hnm. 
        apply giryM_le_mono_equiv; auto.
        by rewrite (rwP ssrnat.leP). 
      }
      eassert ((fun n : nat => limn (fun n0 : nat => (\sum_(0 <= i < n0) μ n (F i))%R)) = _) as ->. {
        apply /funext=>x. 
        rewrite -ge0_integral_count; try done.
      }
      intros. 
      rewrite monotone_convergence; auto.  
      { move => n _ s Hs. done. }
      { 
        move => n _ x y. 
        rewrite -(rwP ssrnat.leP) => a. 
        by apply giryM_le_mono_equiv.  
      }
    }
    exact (is_cvg_nneseries (fun n _ _ => limit_measure_ge0 (F n))).
    Unshelve. (* ??? *)
    apply ereal_hausdorff. 
  Qed.
  Local Close Scope ereal_scope.

  HB.instance Definition _ :=
    isMeasure.Build _ _ _ limit_measure
    limit_measure0 limit_measure_ge0 semi_sigma_additive_limit_measure.

  Lemma limit_measure_setT : (limit_measure setT <= 1)%E.
  Proof.
    rewrite /limit_measure.
    rewrite /limn_esup.
    rewrite /limf_esup.
    apply ereal_inf_le.
    eexists _.
    { simpl. exists setT.
      - rewrite /eventually.
        rewrite /filter_from. simpl.
        by exists 0.       
             - done. }
    apply: ub_ereal_sup.
    rewrite /ubound/=.
    intros ?[??<-].
    apply: sprobability_setT.
  Qed. 
  HB.instance Definition _ := Measure_isSubProbability.Build _ _ _ limit_measure limit_measure_setT.

End setwise_measure_limit.

Section Measurable. 
  Import Order.TTheory GRing.Theory Num.Def Num.Theory.
  Import numFieldTopology.Exports.

  Local Open Scope classical_set_scope.

  Context {d} {T : measurableType d}.

  Search ((_ : realType) -> (_ : realType) -> bool).

  Lemma cvg_pointwise_meas_fun (R : realType) (f : nat -> T -> R) (g : T -> R):
    (forall n x, f n x <= f (S n) x)%O ->
    (forall x, (f n x) @[n --> \oo] --> (g x)) -> 
    (forall n, measurable_fun (U := Real_sort__canonical__measure_SigmaRing R) setT (f n)) ->
    measurable_fun (U := Real_sort__canonical__measure_SigmaRing R)  setT g.
  Proof.
    intros.
    simpl in *.
    move => _ s Hs.
    rewrite setTI.
    Search ocitv.
    set P := fun x : set R => d.-measurable (g @^-1` x).
    assert (forall b, g @^-1` (`] b, +oo[) = \bigcup_n ((f n) @^-1` (`] b, +oo[))). {
      move => b. 
      apply eq_set => x //=.
      rewrite propeqE. split; [intros | intros [n H2]].
      - admit.
      - admit.
    }
    assert (forall x, ocitv x -> measurable (g @^-1` x)). {
      intros.
      apply ocitvP in H3 as [Hx | [[a b] Hx]];
      [by rewrite Hx preimage_set0| simpl in *].
      rewrite H3. 
      have -> : `]a, b] = `]a, +oo[ `\` `]b, +oo[. {
        admit.
      }
      Search (preimage).
      admit.
    }
    (* 

    eapply (dynkin_induction (ocitv (R := R)) P); rewrite /P //=.
    { apply ocitvI. }
    { apply H1. }
    { } *)

  Admitted.

  Lemma bounded_cvg_pointwise_meas_fun (f : nat -> T -> \bar R) (g : T -> \bar R) (l u : R):
    (forall x, l%:E <= g x <= u%:E)%E ->
    (forall x, f n x @[n --> \oo] --> g x)%E -> 
    (forall n, measurable_fun setT (f n)) ->
    measurable_fun setT g.
  Proof.
    Check cvg_nbhsP.
    Check (realfun.cvg_pinftyP (R:=R)).
    intros.
    simpl in *.
    move => _ s Hs.
    rewrite -(preimage_range g) -preimage_setI. 
    Print emeasurable.
    set P := fun x : set R => d.-measurable (g @^-1` [set r%:E | r in x]).
    Search (image).
    Search (preimage).
    (* eapply (dynkin_induction _ P); rewrite /P //=.
    rewrite /'measurable //= /emeasurable /measurable //=.
    (* set pp := (measurable (s := (constructive_ereal_extended__canonical__measure_SigmaRing R))).
    unfold emeasurable.  *) *)
    
  Admitted.
End Measurable.
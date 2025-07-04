Set Warnings "-hiding-delimiting-key".
From HB Require Import structures.
From Coq Require Import Logic.ClassicalEpsilon Psatz Logic.FunctionalExtensionality Program.Wf Reals Lia.
From mathcomp Require Import ssrbool all_algebra eqtype choice boolp classical_sets num_normedtype complete_normed_module. 
From Coq.ssr Require Import ssreflect ssrfun.
From mathcomp.analysis Require Import measure ereal sequences normedtype lebesgue_measure lebesgue_integral esum realfun measurable_realfun charge.
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

Section lim.
  Local Open Scope classical_set_scope.
  Import HBNNSimple. 
  Import fsbigop.
  Import bigop.
  Import cardinality.
  Import fintype.
  Import ssrnum.

  Lemma ebounded_nondecreasing_lub [u : R] [f : nat -> \bar R] :
    (forall n, f n <= u%:E)%E ->
    {homo f : n m / ssrnat.leq n m >-> (n <= m)%E} ->
    cvgn f -> 
    (limn f <= u%:E)%E.
  Proof.
    intros.
    destruct ((limn f <= u%:E)%E) eqn : He; auto.
    assert (u%:E < limn f)%E. { 
      apply /(Order.TotalTheory.contraTlt (b := true)); simpl; auto.
      by rewrite He.
    }
    eapply lte_lim in H2; auto. 
    assert (\forall n \near \oo, f n = u%:E). {
      erewrite eq_near. 
      { exact H2. }
      intros. split.
      { intros. by rewrite H3. }
      { intros. apply Order.le_anti. by rewrite H3 (H x). }
    }
    apply (lim_near_cst (@ereal_hausdorff _)) in H3.
    rewrite H3 in He. rewrite -He.
    apply Order.le_refl.
  Qed.

  Lemma ebounded_nondecreasing_lub' [u : R] [f : nat -> \bar R] :
    (forall n, f n <= u%:E)%E ->
    {homo f : n m / ssrnat.leq n m >-> (n <= m)%E} ->
    cvgn f -> 
    (limn_esup f <= u%:E)%E.
  Proof.
    by intros; erewrite is_cvg_limn_esupE => //=; apply ebounded_nondecreasing_lub.
  Qed.

  Lemma elimn_nondecreasing_lub [u : \bar R] [f : nat -> \bar R] :
    (forall n, f n <= u)%E ->
    {homo f : n m / ssrnat.leq n m >-> (n <= m)%E} ->
    cvgn f -> 
    (limn f <= u)%E.
  Proof.
    intros; destruct u.
    - apply ebounded_nondecreasing_lub => //=.
    - apply /leey.
    - assert (f = (functions.cst -oo)%E) as ->. {
        apply /funext => n. 
        apply /Order.le_anti /andP; split => //=. 
        by apply /leNye.
      }
      by rewrite lim_cst.
  Qed.

  Lemma elimn_esup_nondecreasing_lub [u : \bar R] [f : nat -> \bar R] :
    (forall n, f n <= u)%E ->
    {homo f : n m / ssrnat.leq n m >-> (n <= m)%E} ->
    cvgn f -> 
    (limn_esup f <= u)%E.
  Proof.
    by intros; erewrite is_cvg_limn_esupE => //=; apply elimn_nondecreasing_lub.
  Qed.

  Lemma ebounded_nondecreasing_cvgn_le [l u : R] [f : nat -> \bar R] : 
    (forall n, l%:E <= f n <= u%:E)%E ->
    {homo f : n m / ssrnat.leq n m >-> (n <= m)%E} ->
    cvgn f -> 
    forall n : nat, (f n <= limn f)%E.
  Proof. 
    intros.
    set f' := fine \o f.
    assert (forall n, f n = (f' n)%:E). {
      rewrite /f' //=.
      intro. specialize (H n0).
      destruct (f n0) eqn: Hf'; auto.
      { rewrite leye_eq in H. 
        apply andb_prop in H as [_ H]. 
        inversion H. }
      {  
        rewrite leeNy_eq in H. 
        apply andb_prop in H as [H _]. 
        inversion H.
      }
    }
    replace f with (EFin \o f'). 2 : {
      apply /funext => n'. by rewrite H2.
    }
    assert ({homo f' : n0 m / ssrnat.leq n0 m >-> (Order.le n0 m)}). {
      move => x y Hxy.
      pose proof (H0 x y Hxy).
      by rewrite !H2 lee_fin in H3. 
    }
    epose proof (nondecreasing_is_cvgn (u_ := f') _ _).
    rewrite EFin_lim //.
    apply lee_tofin, nondecreasing_cvgn_le; auto.
    Unshelve. all: auto.
    unfold has_ubound, nonempty, ubound. 
    exists u. simpl.
    intros x [m Hs].
    rewrite -H4 -lee_fin -H2.
    specialize (H m). 
    by apply andb_prop in H as [_ H]. 
  Qed.

  Lemma ebounded_fin_lim [l u : R] [f : nat -> \bar R] : 
    (forall n, l%:E <= f n <= u%:E)%E ->
    cvgn f ->
    (limn f) \is a fin_num.
  Proof.
    intros.
    rewrite fin_real; auto.
    apply /andP; split.
    { 
      eapply Order.POrderTheory.lt_le_trans.
      { by apply/ (ltNyr l ) => //=.  } 
      apply /lime_ge => //=.
      apply: nearW => a; specialize (H a); rewrite -(rwP andP) in H.
      by destruct H.
    }
    {
      eapply Order.POrderTheory.le_lt_trans.
      2 : { by apply/ (ltry u) => //=.  } 
      apply /lime_le => //=.
      apply: nearW => a; specialize (H a); rewrite -(rwP andP) in H.
      by destruct H.
    }
  Qed.

  Lemma ecvg_lim_le_lim (f g : nat -> \bar R) (H : forall n, (f n <= g n)%E):
    cvgn f -> cvgn g ->
    (limn f <= limn g)%E.
  Proof.
    intros.
    apply (lee_lim (f:=f) (g:=g)); auto.
    by exists 0.
  Qed.

  Lemma lim_n_Sn (f : nat -> \bar R) : 
    cvgn f ->
    limn f = limn (fun n => f (S n)).
  Proof.
    intros.
    epose proof (cvg_shiftn 1 f).
    rewrite -H0 in H. simpl in *.
    assert ((fun n => f (ssrnat.addn n 1)) = (fun n => f (S n))). {
      apply /funext => n //=. rewrite ssrnat.addn1 //.
    }
    rewrite H1 in H.
    by erewrite <- (cvg_lim (@ereal_hausdorff _) H).
  Qed.

  Lemma fin_sum_lim_cvg {T : choiceType} n (f : nat -> nat -> \bar R): 
    (forall n, cvgn (f n)) -> 
    (forall n, (limn (f n)) \is a fin_num) ->
    cvgn (fun m => (\sum_(i \in `I_n) (f i m))%E).
  Proof.
    revert f.
    induction n.
    {
      intros.
      have -> : ((fun m : nat => (\sum_(i \in `I_0) f i m)%E) = functions.cst 0%E). {
        apply/ funext => m. 
        by rewrite -!fsbig_ord //= big_ord0.
      }
      apply /ereal_nondecreasing_is_cvgn => ??? //=.
    }
    intros.
    have -> : ((fun m : nat => (\sum_(i \in `I_(S n)) f i m)%E) = ((f 0%nat) \+ (fun m : nat => (\sum_(i \in `I_n) f (bump 0 i) m)%E))%E). {
      apply/ funext => m. 
      rewrite -!fsbig_ord big_ord_recl //=. 
    }
    apply/ is_cvgeD => //=. 
    { apply fin_num_adde_defr => //=. }
    apply IHn => //=.
  Qed.

  Lemma fin_sum_lim_exchange_ord {T : choiceType} n (f : nat -> nat -> \bar R): 
    (forall n, cvgn (f n)) -> 
    (forall n, (limn (f n)) \is a fin_num) ->
    (\sum_(i \in `I_n) (limn (f i)))%E = limn (fun m => (\sum_(i \in `I_n) (f i m))%E).
  Proof.
    rewrite -!fsbig_ord //=.
    revert f.
    induction n. 
    { 
      intros.
      rewrite big_ord0.
      have -> : ((fun m : nat => (\sum_(i \in `I_0) f i m)%E) = functions.cst 0%E). {
        apply/ funext => m. 
        by rewrite -!fsbig_ord //= big_ord0.
      }
      by rewrite lim_cst.
    }
    intros.
    rewrite big_ord_recl //=.
    have -> : ((fun m : nat => (\sum_(i \in `I_(S n)) f i m)%E) = ((f 0%nat) \+ (fun m : nat => (\sum_(i \in `I_n) f (bump 0 i) m)%E))%E). {
      apply/ funext => m. 
      rewrite -!fsbig_ord big_ord_recl //=. 
    }
    symmetry.
    apply/ (cvg_lim (@ereal_hausdorff _)).
    apply/ cvgeD => //=. 
    { apply fin_num_adde_defr => //=. }
    rewrite (IHn (fun i => f (bump 0 i))) //=. 
    apply /fin_sum_lim_cvg => //=.
  Qed.

  (* To check: does T have to be pointed? *)
  Lemma fin_sum_lim_exchange {T : pointedType} [A : set T] (f : T -> nat -> \bar R): 
    finite_set A ->
    (forall n, cvgn (f n)) -> 
    (forall n, (limn (f n)) \is a fin_num) ->
    (\sum_(i \in A) (limn (f i)))%E = limn (fun n => (\sum_(i \in A) (f i n))%E).
  Proof.
    intros.
    destruct H.
    rewrite card_eq_sym in H.
    apply <- rwP in H.
    2 : apply card_set_bijP.
    destruct H as [h H].
    rewrite (reindex_fsbig h _ _ _ H) //=. 
    rewrite fin_sum_lim_exchange_ord //=.
    2 : exact (classical_sets_Pointed__to__choice_Choice T).
    do 2 f_equal; apply/ funext => n.
    rewrite (reindex_fsbig h _ _ _ H) //=. 
  Qed.

  Lemma limit_exchange {d} {T : measurableType d} (f : T -> \bar R) (Hflb : forall a : T, (0 <= f a)%E)
    (μ : nat -> giryM T) (Hmono : forall n, giryM_le (μ n) (μ (S n))) l u:
    measurable_fun setT f -> 
    (forall x, l <= f x <= u)%E ->
    (\int[limit_measure μ Hmono]_x f x)%E =
      limn (esups (R:=R) (fun n : nat => (\int[μ n]_x f x)%E)).
  Proof.
    (* Antisymmetry *) 
    intros.
    assert (cvgn (fun n0 : nat => (\int[μ n0]_x f x)%E)). {
      apply ereal_nondecreasing_is_cvgn => m n Hmn //=.
      apply ge0_le_measure_integral => //=.
      apply giryM_le_mono_equiv => //.
      by apply /ssrnat.leP.
    }
    rewrite -limn_esup_lim is_cvg_limn_esupE //=.
    apply /Order.le_anti /andP; split; last first.
    {
      (* ∀ n, ∫ f d(μ_n) ≤ ∫ f d(limit_measure μ)       by def. pointwise monotonicity (add hypothesis) *)
      (* so lim_n ∫ f d(μ_n) = sup_n ∫ f d(μ_n)         true for every convergent limit
                             ≤  ∫ f d(limit_measure μ)  by inequality above *)

      (* Change the limsup to the the sup of the sequence *)
      suff : forall n, (\int[μ n]_x f x <= \int[limit_measure μ Hmono]_x f x)%E. {
        move=> n; apply: lime_le => //.
        by apply: nearW => x.
      }
      intros.
      apply ge0_le_measure_integral => //= => ??.
      rewrite /limit_measure is_cvg_limn_esupE. 
      2 : by apply cvg_limit_measure.
      apply /ebounded_nondecreasing_cvgn_le. 
      { by intros; apply /andP; split; [apply /measure_ge0 | by apply /eval_le_1]. }
      { by move => x y Hxy; apply giryM_le_mono_equiv => //=; apply /ssrnat.leP. }
      { by apply cvg_limit_measure. }
    }
    {
      rewrite ge0_integralTE; [|done].
      (* Apply the theorem in the case of simple integrals *)
      suff HSimple :
        forall (h : {nnsfun T >-> R}), ([set h | forall x : T, ((h x)%:E <= f x)%E] h)%classic ->
             sintegral (limit_measure μ Hmono) h =
             filter.lim (filter.fmap (esups (R:=R) (fun n : nat => sintegral (μ n) h))
                (@filter.nbhs nat (filter.filter_set_system__canonical__filter_Filtered nat) filter.eventually)). 
      { 
        apply ub_ereal_sup.
        intros ?; rewrite //=; intros [h Hnn <-].
        rewrite HSimple; [|done].
        rewrite //=. rewrite -(is_cvg_limn_esupE (u := (fun n : nat => \int[μ n]_x f x))%E) //=. 
        rewrite limn_esup_lim.
        apply ecvg_lim_le_lim => //=; try by apply is_cvg_esups. 
        intros.
        eapply ub_ereal_sup.  
        rewrite /ubound /sdrop //= => x [m Hx <-].
        apply ereal_sup_le => //=; exists (\int[μ m]_x0 f x0)%E => //=.
        { econstructor; eauto. } 
        rewrite -integralT_nnsfun.
        apply ge0_le_integral => //=. 
        { intros. by rewrite lee_fin. }
        { by apply measurable_EFinP. }
      }
      move => h HH.
      rewrite -limn_esup_lim. 
      rewrite sintegralE.
      eassert ((fun n : nat => sintegral _ _) = _) as ->; first by apply/ funext => n; rewrite sintegralE.
      rewrite is_cvg_limn_esupE. 
      2 : { 
        apply ereal_nondecreasing_is_cvgn => n m Hnm.
        apply lee_fsum => //= => ?[??]<-.
        apply /lee_pmul => //=; first by apply lee_tofin.
        apply giryM_le_mono_equiv => //=.
        by apply/ ssrnat.leP.
      }
      have Hn : (forall n : R, cvgn (fun n0 : nat => (n%:E * μ n0 (h @^-1` [set n]))%E)). {
        intros x.
        apply/ is_cvgeZl => //=. 
        by apply cvg_limit_measure.
      }
      rewrite -(fin_sum_lim_exchange (T:=numFieldTopology.Real_sort__canonical__classical_sets_Pointed R)) //=; first last.
      { 
        move => x. 
        set x1 := Num.norm x. simpl in *.
        apply /(ebounded_fin_lim (l := -x1) (u := x1)) => //= => m.
        rewrite /x1; apply /andP. split.
        {
          destruct (Rle_lt_dec x 0). 
          - rewrite Num.Theory.ler0_norm /GRing.opp //=; last by apply /RleP => //=.
            rewrite !EFinN leeNl. 
            rewrite -(mule1 (oppe _)) -mulNe.
            apply /lee_pmul => //=; first by rewrite lee_fin; apply /RleP /Ropp_0_ge_le_contravar; lra. 
            by apply eval_le_1.
          - rewrite Num.Theory.gtr0_norm /GRing.opp //=; last by apply /RltP => //=. 
            apply (@Order.POrderTheory.le_trans _ _ 0%:E); first by rewrite lee_fin /GRing.opp ; apply /RleP /Rlt_le /Ropp_0_lt_gt_contravar. 
            apply /mule_ge0 => //=; apply /RleP /Rlt_le => //=.
        }
        {
          destruct (Rle_lt_dec 0 x). 
          - rewrite Num.Theory.ger0_norm /GRing.opp //=; last by apply /RleP => //=.
            rewrite <-(mule1 x%:E) at 2. 
            apply /lee_pmul => //=; first by rewrite lee_fin; apply /RleP. 
            by apply eval_le_1.
          - rewrite Num.Theory.ltr0_norm /GRing.opp //=; last by apply /RltP => //=.
            eapply Order.POrderTheory.le_trans; first by apply /mule_le0_ge0 => //=; apply /RleP /Rlt_le. 
            by apply /RleP /Rlt_le /Ropp_0_gt_lt_contravar. 
        }
      }
      apply eq_fsbigr => x Hx //=.
      rewrite /limit_measure is_cvg_limn_esupE. 
      2 : apply cvg_limit_measure => //=.
      symmetry.
      apply/ cvg_lim => //.
      apply/ cvgeZl => //=. 
      by apply cvg_limit_measure.
    }
  Qed.
End lim.


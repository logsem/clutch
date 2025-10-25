From mathcomp Require Import ssrbool all_algebra eqtype choice boolp classical_sets ssreflect ssralg ssrnum ssrint ssrfun.
From mathcomp.analysis Require Import all_analysis.
Import ereal landau topology function_spaces cantor prodnormedzmodule normedtype realfun sequences exp trigo esum lebesgue_measure derive measure numfun lebesgue_integral ftc hoelder probability lebesgue_stieltjes_measure convex charge kernel pi_irrational gauss_integral reals measurable_realfun order.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.
Import HBNNSimple.
From mathcomp.analysis Require Import num_normedtype.
From mathcomp Require Import reals Rstruct.
Require Import Coq.Unicode.Utf8.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Definition epsilon {A : Type} {P : A->Prop} (H : exists x, P x) := proj1_sig (Epsilon.constructive_indefinite_description P H).
Definition epsilon_spec {A : Type} {P : A->Prop} (H : exists x, P x) : P (epsilon H) := proj2_sig (Epsilon.constructive_indefinite_description P H).


Section lebesgue.

Context [R : realType].

Notation mu := (@lebesgue_measure R).

(* inf {∫_D g | f <= g, g is integrable} *)
Definition upper_lebesgue (D : set R) (f : R -> R) := ereal_inf [set integral mu D (EFin \o g) | g in [set g : R -> R | (mu.-integrable D (EFin \o g)) ∧ (∀ x, x \in D -> f x <= g x)]].
(* sup {∫_D g | g <= f, g is integrable} *)
Definition lower_lebesgue (D : set R) (f : R -> R) := ereal_sup [set integral mu D (EFin \o g) | g in [set g : R -> R | (mu.-integrable D (EFin \o g)) ∧ (∀ x, x \in D -> g x <= f x)]].


Lemma upper_ge_lower_lebesgue D f :
  'measurable D ->
  (lower_lebesgue D f <= upper_lebesgue D f)%E.
Proof.
  intro HD.
  rewrite /upper_lebesgue /lower_lebesgue.
  apply ub_ereal_sup => //= x //= [g0 [Hg0 Hg0']] ?; subst.
  apply lb_ereal_inf => //= x //= [g1 [Hg1 Hg1']] ?; subst.
  apply le_integral => //=.
  move => x Hx.
  rewrite lee_fin. eapply le_trans.
  - by apply Hg0'.
  - by apply Hg1'.
Qed.

Lemma upper_lower_agree_integrable (D : set R) (f : R -> R) (r : R): 
  'measurable D ->
  upper_lebesgue D f = EFin r ->
  lower_lebesgue D f = EFin r ->
  mu.-integrable D (EFin \o f) ∧ \int[mu]_(t in D) f t = r. 
Proof.
  intros.
  assert (∀ n : nat, ∃ g : R -> R, (∀ x, x \in D -> f x <= g x) ∧ (mu.-integrable D (EFin \o g)) ∧ \int[mu]_(t in D) g t <= r + 1 / (S n)%:R). {
    intros.
    assert (is_true (@Order.lt ring_display (join_Num_POrderedZmodule_between_GRing_Nmodule_and_Order_POrder (reals_Real__to__Num_POrderedZmodule R)) (@GRing.zero (Num_POrderedZmodule__to__GRing_Nmodule (reals_Real__to__Num_POrderedZmodule R))) (@GRing.mul (GRing_UnitRing__to__GRing_SemiRing (reals_Real__to__GRing_UnitRing R)) (GRing.one (GRing_UnitRing__to__GRing_SemiRing (reals_Real__to__GRing_UnitRing R))) (@GRing.inv (reals_Real__to__GRing_UnitRing R) (@GRing.natmul (GRing_SemiRing__to__GRing_Nmodule (GRing_UnitRing__to__GRing_SemiRing (reals_Real__to__GRing_UnitRing R))) (GRing.one (GRing_UnitRing__to__GRing_SemiRing (reals_Real__to__GRing_UnitRing R))) (S n)))))); first by apply divr_gt0. 
    rewrite /upper_lebesgue in H0.
    eapply (@lb_ereal_inf_adherent _ [set integral mu D (EFin \o g) | g in [set g : R -> R | (mu.-integrable D (EFin \o g)) ∧ (∀ x, x \in D -> f x <= g x)]]) in H2 as [x H2]; last by rewrite H0.
    simpl in H2. destruct H2 as [g [H2 H2']]; subst.
    rewrite H0 in H3. 
    exists g; split; try split; auto.
    rewrite -EFinD in H3.
    rewrite -lee_fin. apply ltW.
    admit.
  }
  assert (∀ n : nat, ∃ g : R -> R, (∀ x, x \in D -> g x <= f x) ∧ (mu.-integrable D (EFin \o g)) ∧ \int[mu]_(t in D) g t >= r - 1 / (S n)%:R). {
    intros.
    assert (is_true (@Order.lt ring_display (join_Num_POrderedZmodule_between_GRing_Nmodule_and_Order_POrder (reals_Real__to__Num_POrderedZmodule R)) (@GRing.zero (Num_POrderedZmodule__to__GRing_Nmodule (reals_Real__to__Num_POrderedZmodule R))) (@GRing.mul (GRing_UnitRing__to__GRing_SemiRing (reals_Real__to__GRing_UnitRing R)) (GRing.one (GRing_UnitRing__to__GRing_SemiRing (reals_Real__to__GRing_UnitRing R))) (@GRing.inv (reals_Real__to__GRing_UnitRing R) (@GRing.natmul (GRing_SemiRing__to__GRing_Nmodule (GRing_UnitRing__to__GRing_SemiRing (reals_Real__to__GRing_UnitRing R))) (GRing.one (GRing_UnitRing__to__GRing_SemiRing (reals_Real__to__GRing_UnitRing R))) (S n)))))); first by apply divr_gt0. 
    rewrite /lower_lebesgue in H1.
    eapply (@ub_ereal_sup_adherent _ [set integral mu D (EFin \o g) | g in [set g : R -> R | (mu.-integrable D (EFin \o g)) ∧ (∀ x, x \in D -> g x <= f x)]]) in H3 as [x H3]; last by rewrite H1.
    destruct H3 as [g [H3 H3']]; subst.
    rewrite H1 in H4. 
    exists g; split; try split; auto.
    rewrite -EFinD in H4. 
    rewrite -lee_fin. apply ltW.
    admit.
  }
  set fu := fun n : nat => epsilon (H2 n). 
  set fl := fun n : nat => epsilon (H3 n). 
  set Fu := (λ x, infs (fu ^~ x) 0%nat).
  set Fl := (λ x, sups (fl ^~ x) 0%nat).
  assert (measurable_fun D Fu). {
    rewrite /Fu.
    apply measurable_fun_infs; rewrite /fu; intros.
    rewrite /has_lbound /lbound. exists (f t). simpl.
    - intros ? [???]; subst. pose proof (epsilon_spec (H2 x0)) as [??].
      apply H6 => //=. by apply mem_set.
    - pose proof (epsilon_spec (H2 n)) as Hn;
      destruct Hn as [?[??]];
      rewrite -(rwP (integrableP _ _ _)) measurable_EFinP in H5.
      by destruct H5.
  }
  assert (measurable_fun D Fl). {
    rewrite /Fu.
    apply measurable_fun_sups; rewrite /fl; intros.
    - rewrite /has_ubound /ubound. exists (f t). simpl.
      intros ? [???]; subst. pose proof (epsilon_spec (H3 x0)) as [??].
      apply H7 => //=. by apply mem_set.
    - pose proof (epsilon_spec (H3 m)) as Hn.
      destruct Hn as [?[??]].
      rewrite -(rwP (integrableP _ _ _)) measurable_EFinP in H6.
      by destruct H6.
  }
  assert (∀ x, x \in D -> Fl x <= f x). {
    rewrite /Fl /sups /sdrop //= => a. intro Ha.
    replace ([set k | ssrnat.leq 0 k]) with [set : nat]. 2 : {
      rewrite predeqE. intros. simpl. split; auto.
    }
    rewrite sup_le_ub //=; first by exists (fl 0 a).
    rewrite /ubound //=.
    intros ? [??]; subst.
    pose proof (epsilon_spec (H3 x0)) as Hn.
    destruct Hn. by apply H7.
  }
  assert (∀ x, x \in D ->  f x <= Fu x). {
    rewrite /Fu /infs /sdrop //= => a. intro Ha.
    replace ([set k | ssrnat.leq 0 k]) with [set : nat]. 2 : {
      rewrite predeqE. intros. simpl. split; auto.
    }
    rewrite lb_le_inf //=; first by exists (fu 0 a).
    rewrite /lbound //=.
    intros ? [??]; subst.
    pose proof (epsilon_spec (H2 x0)) as Hn.
    destruct Hn. by apply H8.
  }
  assert (mu.-integrable D (EFin \o Fu)). {
    apply /integrableP. 
    split; first by apply /measurable_EFinP.
    (* Fu is sandwiched between integrable functions fl_0 and fu_0 and is hence integrable*)
    admit.
  }
  assert (\int[mu]_(t in D) Fu t <= r). {
    
    admit.
  }
  assert (r <= \int[mu]_(t in D) Fl t). {

    admit.
  }
  assert (\int[mu]_(t in D) Fu t = r). {
    admit.
  }
  assert (\int[mu]_(t in D) Fl t = r). {
    admit.
  } 
  assert (ae_eq mu D (EFin \o Fl) (EFin \o Fu)). {
    admit.
  }
   assert (ae_eq mu D (EFin \o f) (EFin \o Fu)). {
    admit.
  }
  Check ae_measurable_fun.
  assert (mu.-integrable D (EFin \o f)). {
    Check negligible_integrable.
    Check eq_integrable.
    admit.
  }
  split; auto.
  rewrite -H11. 
  rewrite /Rintegral.
  f_equal.
  apply ae_eq_integral; auto.
  - rewrite -(rwP (integrableP _ _ _)) in H15.
    by destruct H15. 
  - rewrite -(rwP (integrableP _ _ _)) in H8.
    by destruct H8.
Admitted.

Check dominated_cvg.

End lebesgue.

From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt Lub Rbar.
From clutch.prelude Require Export Reals_ext.

Section riemann.

Import Hierarchy.
Import RiemannInt.
Import Rdefinitions Rcomplements RIneq SF_seq.
Lemma pairmap_sf (g : R -> R -> R -> R) a b1 b2 l : 
  (seq.pairmap (λ x y : R * R, g x.1 y.1 y.2) (a, b1) l) = (seq.pairmap (λ x y : R * R, g x.1 y.1 y.2) (a, b2) l).
Proof. destruct l => //=. Qed.

Notation mu := (@lebesgue_measure R).

Definition isPartition a b P := pointed_subdiv P ∧ SF_h P = a ∧ seq.last (SF_h P) (seq.unzip1 (SF_t P)) = b.

Definition riemann_sum_f P (f : R -> R) : R -> R := fun a => seq.foldr Rplus 0
  (seq.pairmap 
    (λ x y : R * R, (\1_`[(fst x), (fst y)[ a) * f (snd y)) 
      (SF_h P, 0) (SF_t P)). 

Lemma riemann_sum_f_range P (f : R -> R) a b x : 
  a < b -> 
  a <= x < b -> 
  isPartition a b P ->
  ∃ i, seq.nth 0 (SF_lx P) i <= x <= seq.nth 0 (SF_lx P) (S i) ∧ 
    riemann_sum_f P f x = f (seq.nth 0 (SF_ly P) i).
Proof.
  destruct P as [h l] => //=.
  rewrite /SF_lx  /isPartition /pointed_subdiv /riemann_sum_f /SF_ly /SF_lx /SF_size //=. 
  intros H1 H2 [H3 [H4 H5]]; subst.
  generalize dependent a.
  revert l.
  induction l; intros; simpl in *; first by real_solver.
  destruct (lem (x < a0.1)). 
  - exists 0%nat.
    simpl. split. split; real_solver. 
    rewrite indicE set_itvco mem_set //=.
    2 : {
      apply /andP. split. apply /RleP. real_solver. by apply /RltP.
    }
    rewrite Rmult_1_l -{2}(Rplus_0_r (f a0.2)). f_equal.

    admit.
  - assert (a0.1 <= x < seq.last a0.1 (seq.unzip1 l)); first real_solver.
    pose proof H0.
    apply IHl in H0 as [i [Hi H0]]; intros; try real_solver; last by apply (H3 (S i)); real_solver.
    exists (S i).
    simpl. split; auto. 
    rewrite (pairmap_sf (λ a b c, \1_`[a, b[ x * f c) a0.1 0 a0.2 l) in H0.
    replace (a0) with (a0.1, a0.2); last by destruct a0.
    rewrite H0 //= indicE set_itvco memNset //=; first by rewrite Rmult_0_l; real_solver.
    rewrite -(rwP andP). move => [??]. apply H. 
    by apply /RltP.
Admitted.

Lemma riemann_sum_f_integrable P (f : R -> R) a b :
  a < b -> 
  isPartition a b P -> 
  mu.-integrable setT (EFin \o (riemann_sum_f P f)).
Proof.
  destruct P as [h l] => //=.
  rewrite /SF_lx  /isPartition /pointed_subdiv /riemann_sum_f /SF_ly /SF_lx /SF_size //=. 
  intros H1 [H3 [H4 H5]]; subst.
  generalize dependent a.
  revert l.
  induction l; intros; simpl in *.
  { eapply eq_integrable => //=. apply integrable0. }
  Check eq_integrable.
  intros. 
  
Admitted.
  
Lemma riemann_sum_f_integral P (f : R -> R) a b :
  a < b -> 
  isPartition a b P -> 
  \int[mu]_(t in `[a, b[) riemann_sum_f P f t = Riemann_sum f P.
Proof.
  destruct P as [h l] => //=.
  rewrite /SF_lx  /isPartition /pointed_subdiv /riemann_sum_f /SF_ly /SF_lx /SF_size //=. 
  intros H1 [H3 [H4 H5]]; subst.
  generalize dependent a.
  revert l.
  induction l; intros; rewrite /Riemann_sum //= /zero; simpl in *.
  - admit.
  - 
Admitted.

Section upper_lower.

Context (f : R -> R) (d a b : R).

(* 
this is a tagged partition (l0, [(l1, x1), (l2, x2), ...]) 
 of [a,b] that satisfies:
- ∀ i, l_(i+1) - l_i < d
- ∀ i, f x_(i+1) = inf {f x| l_i <= x < l_(i+1)}

note that when f is bounded, x_i is guaranteed to exist
*)
Definition lower_part : @SF_seq R.
Admitted.

(*
similar to the previous definition, 
except that ∀ i, f x_(i+1) = sup {f x| l_i <= x < l_(i+1)}
*)
Definition upper_part : @SF_seq R.
Admitted.

Lemma lower_part_step : 
  a < b ->
  d <= b - a ->
  seq_step (SF_lx lower_part) < d.
Admitted.

Lemma upper_part_step: 
  a < b ->
  d <= b - a ->
  seq_step (SF_lx upper_part) < d.
Admitted.

Lemma lower_part_is_part: 
  a < b ->
  d <= b - a -> 
  isPartition a b lower_part.
Admitted.

Lemma upper_part_is_part: 
  a < b ->
  d <= b - a -> 
  isPartition a b upper_part.
Admitted.

Lemma upper_part_riemann l u x:
  a < b ->
  d <= b - a -> 
  (∀ y, a <= y <= b -> l <= f y <= u) ->
  a <= x < b -> 
  f x <= riemann_sum_f upper_part f x.
Proof.
Admitted.

Lemma lower_part_riemann l u x:
  a < b ->
  d <= b - a -> 
  (∀ y, a <= y <= b -> l <= f y <= u) ->
  a <= x < b -> 
  riemann_sum_f lower_part f x <= f x.
Proof.
Admitted.

End upper_lower.


Lemma RInt_Lebesgue' (f : R -> R) (a b r l u: R) :
  a < b -> 
  (∀ x, a <= x <= b -> l <= f x <= u)  ->
  is_RInt f a b r -> 
  mu.-integrable `[a, b[ (EFin \o f) ∧
  \int[mu]_(t in `[a, b[) f t = r.
Proof.
  intro.
  rewrite /is_RInt /filterlim /locally /SF_seq.Riemann_fine /within /locally_dist /filtermap /filter_le //=.
  replace (Rbasic_fun.Rmin a b) with a; last by rewrite /Rbasic_fun.Rmin; real_solver. 
  replace (Rbasic_fun.Rmax a b) with b; last by rewrite /Rbasic_fun.Rmax; real_solver. 
  eassert (@scal R_Ring (NormedModule.ModuleSpace R_AbsRing R_NormedModule) (Rcomplements.sign (Rminus b a)) = (fun r : R => r)) as ->. {
    apply FunctionalExtensionality.functional_extensionality => x. rewrite /scal /Rcomplements.sign //=  /mult //=. 
    destruct (total_order_T 0 (b - a)); try real_solver.
  }
  intros.
  assert (∀ ε : R, (0 < ε)%R -> (r - ε)%:E <= lower_lebesgue `[a, b[ f)%E. {
    intros.
    epose proof (H1 (ball r ε) _) as [d'].
    set d := Rbasic_fun.Rmin (b - a) d'.
    set pl := lower_part f d a b.
    specialize (H3 pl).
    assert (isPartition a b pl). {
      apply lower_part_is_part => //=.
      apply Rbasic_fun.Rmin_l.
    }
    assert (d <= b - a). {
      apply Rbasic_fun.Rmin_l. 
    }
    assert (d <= d'). {
      apply Rbasic_fun.Rmin_r.
    }
    eapply le_trans.
    Unshelve. 4 : exact (EFin (Riemann_sum f pl)).
    - rewrite lee_fin. apply /RleP. apply Rlt_le.
      rewrite /ball //= /AbsRing_ball /abs /minus /plus /AbsRing.abs //= in H3. 
      rewrite Rabs_lt_between' in H3. apply H3 => //=. 
      eapply Rlt_le_trans; rewrite /d.
      apply lower_part_step => //=. auto.
    - erewrite <-(riemann_sum_f_integral _ _ _ _ H) => //=.
      rewrite /lower_lebesgue. 
      eapply ereal_sup_le => //=. eexists _. exists (riemann_sum_f pl f) => //=.
      + split. eapply (@integrableS _ _ _ _ setT) => //=.
        by apply (riemann_sum_f_integrable _ _ _ _ H).
        intros. apply /RleP. eapply lower_part_riemann => //=; eauto.
        rewrite set_itvco in H7. apply set_mem in H7.
        simpl in H7. apply andb_prop in H7 as [??]. split. 
        by apply /RleP. by apply /RltP.
      + rewrite /comp /Rintegral fineK //=.
        apply integral_fune_fin_num => //=.
        eapply (@integrableS _ _ _ _ setT) => //=. 
        by apply (riemann_sum_f_integrable _ _ _ _ H). 
    - exists (mkposreal ε H2) => //=. 
  }
  assert (∀ ε : R, (0 < ε)%R -> upper_lebesgue `[a, b[ f <= (r + ε)%:E)%E. {
    intros.
    epose proof (H1 (ball r ε) _) as [d'].
    set d := Rbasic_fun.Rmin (b - a) d'.
    set pl := upper_part f d a b.
    specialize (H4 pl).
    assert (isPartition a b pl). {
      apply upper_part_is_part => //=.
      apply Rbasic_fun.Rmin_l.
    }
    assert (d <= b - a). {
      apply Rbasic_fun.Rmin_l. 
    }
    assert (d <= d'). {
      apply Rbasic_fun.Rmin_r.
    }
    eapply le_trans.
    Unshelve. 4 : exact (EFin (Riemann_sum f pl)).
    - erewrite <-(riemann_sum_f_integral _ _ _ _ H) => //=.
      rewrite /upper_lebesgue. eapply ereal_inf_le => //=. eexists _. exists (riemann_sum_f pl f) => //=.
      + split. eapply (@integrableS _ _ _ _ setT) => //=.
        by apply (riemann_sum_f_integrable _ _ _ _ H). 
        intros. apply /RleP. eapply upper_part_riemann => //=; eauto.
        rewrite set_itvco in H8. apply set_mem in H8.
        apply andb_prop in H8 as [??]. split. 
        by apply /RleP. by apply /RltP.
      + rewrite /comp /Rintegral fineK //=.
        apply integral_fune_fin_num => //=.
        eapply (@integrableS _ _ _ _ setT) => //=. 
        by apply (riemann_sum_f_integrable _ _ _ _ H). 
    - rewrite lee_fin. apply /RleP. apply Rlt_le.
      rewrite /ball //= /AbsRing_ball /abs /minus /plus /AbsRing.abs //= in H4. 
      rewrite Rabs_lt_between' in H4. apply H4 => //=. 
      eapply Rlt_le_trans; rewrite /d.
      apply upper_part_step => //=. auto.
    - exists (mkposreal ε H3) => //=.
  }
  assert (upper_lebesgue `[a, b[ f <= r%:E)%E. {
    apply /lee_addgt0Pr. intros. apply H3. 
    by apply /RltP => //=.
  }
  assert (r%:E <=  lower_lebesgue `[a, b[ f)%E. {
    apply /lee_subgt0Pr. intros. apply H2. 
    by apply /RltP => //=.
  }
  apply upper_lower_agree_integrable => //=.
  - apply le_anti. apply /andP. split; auto.
    eapply le_trans; first exact H5.
    by apply upper_ge_lower_lebesgue.
  - apply le_anti. apply /andP. split; auto.
    eapply le_trans; last exact H4.
    by apply upper_ge_lower_lebesgue.
Qed.

End riemann.
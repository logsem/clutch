From Coq Require Import Reals Psatz.
From Coq.ssr Require Import ssreflect ssrfun.
From Coquelicot Require Import Rcomplements Rbar Series Lim_seq Hierarchy.
From stdpp Require Export countable.
From self.prelude Require Export base Coquelicot_ext Reals_ext.
From self.prob Require Export countable_sum double distribution.

Arguments MkDistr {_ _ _}.
Arguments pmf {_ _ _ _}.
Arguments pmf_pos {_ _ _}.
Arguments pmf_ex_seriesC {_ _ _}.
Arguments pmf_SeriesC {_ _ _}.

#[global] Hint Resolve pmf_pos pmf_ex_seriesC pmf_SeriesC : core.
Notation Decidable P := (∀ x, Decision (P x)).

Open Scope R.

Section couplings.
  Context `{Countable A, Countable B, Countable A', Countable B'}.
  Context (μ1 : distr A) (μ2 : distr B) (R : A -> B -> Prop) (S : A' → B' → Prop).

(* There are multiple options we could try here. We have the usual
   existential definition, but we can also define it universally via
   Strassens theorem,

  Definition coupl μ1 μ2 R :=
    forall (P1 : A -> Bool) (P2 : B -> Bool),
           (forall a b, P1(a)=true /\ R(A,B) -> P2(a)= true),
                   prob μ1 P1 <= prob μ2 P2
 *)


  Definition isCoupl (μ : distr (A * B)) : Prop :=
    lmarg μ = μ1 /\ rmarg μ = μ2.

  Definition coupl :=
    ∃ (μ : distr (A * B)), isCoupl μ.

  Definition isRcoupl (μ : distr (A * B)) : Prop :=
    isCoupl μ ∧ (forall (p : A * B), (μ p > 0) -> R (fst p) (snd p)).

  Definition Rcoupl :=
    ∃ (μ : distr (A * B)), isRcoupl μ.


  Lemma isRcoupl_isCoupl μ : isRcoupl μ -> isCoupl μ.
  Proof.
    intro C; destruct C; auto.
  Qed.

  Lemma isCoupl_mass_l μ : isCoupl μ -> SeriesC μ = SeriesC μ1.
  Proof.
    intro Hμ.
    destruct Hμ as (Hμl & Hμr).
    rewrite <- Hμl.
    rewrite /lmarg.
    rewrite <- dmap_mass.
    auto.
  Qed.

  Lemma isCoupl_mass_r μ : isCoupl μ -> SeriesC μ = SeriesC μ2.
  Proof.
    intro Hμ.
    destruct Hμ as (Hμl & Hμr).
    rewrite <- Hμr.
    rewrite /rmarg.
    rewrite <- dmap_mass.
    auto.
  Qed.

  Lemma isCoupl_mass_eq μ : isCoupl μ -> SeriesC μ1 = SeriesC μ2.
  Proof.
    intro Hμ.
    rewrite <- (isCoupl_mass_l μ); auto.
    rewrite <- (isCoupl_mass_r μ); auto.
  Qed.



End couplings.

Section couplings_theory.
  Context `{Countable A, Countable B, Countable A', Countable B'}.

  Proposition is_coupl_ret :
    forall (a : A) (b : B), isCoupl (dret a) (dret b) (dret (a, b)).
  Proof.
    intros a b; split; [rewrite /lmarg dmap_dret // | rewrite /rmarg dmap_dret //].
   Qed.

  Proposition coupl_ret :
    forall (a : A) (b : B), coupl (dret a) (dret b).
  Proof.
    intros a b.
    exists (dret (a, b)).
    apply is_coupl_ret.
  Qed.

  Proposition isRcoupl_ret :
    forall (a : A) (b : B) (R : A → B → Prop), R a b -> isRcoupl (dret a) (dret b) R (dret (a, b)).
  Proof.
    intros a b R HR.
    split; [apply is_coupl_ret | ].
    intro p.
    rewrite /pmf /= /dret_pmf /=.
    case_bool_decide as H3; [rewrite H3; auto | lra ].
  Qed.

  Proposition Rcoupl_ret :
    forall (a : A) (b : B) (R : A → B → Prop) , R a b -> Rcoupl (dret a) (dret b) R.
  Proof.
    intros a b R HR.
    exists (dret (a, b)).
    apply isRcoupl_ret.
    auto.
  Qed.

  Lemma Rcoupl_mass_eq (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) :
    Rcoupl μ1 μ2 R → SeriesC μ1 = SeriesC μ2.
  Proof. intros (?&?&?). by eapply isCoupl_mass_eq. Qed.


  Proposition Rcoupl_eq (μ1 : distr A) :
    Rcoupl μ1 μ1 (=).
  Proof.
    exists (ddiag μ1); split; [split | ].
    + apply distr_ext.
      intro a.
      rewrite lmarg_pmf.
      rewrite {1}/pmf/=/dbind_pmf/=.
      rewrite SeriesC_singleton'; auto.
    + apply distr_ext.
      intro a.
      rewrite rmarg_pmf.
      rewrite {1}/pmf/=/dbind_pmf/=.
      (* TODO: Need lemma to rewrite these singletons *)
      rewrite (SeriesC_ext _ (λ a0 : A, if bool_decide (a0 = a) then μ1 a else 0));
      [rewrite SeriesC_singleton; auto | ].
      intro a'; case_bool_decide; simplify_eq; auto.
    + intros (a1 & a2) Hpos; simpl.
      rewrite /pmf/= in Hpos.
      case_bool_decide; simplify_eq; auto; lra.
  Qed.

  Proposition coupl_sym (μ1 : distr A) (μ2 : distr B) :
    coupl μ1 μ2 -> coupl μ2 μ1.
  Proof.
    intros (μ & HμL & HμR).
    exists (dmap (λ '(a, b), (b, a)) μ); split; apply distr_ext.
    + intro b.
      rewrite <- HμR.
      rewrite lmarg_pmf rmarg_pmf.
      apply SeriesC_ext; intro a.
      simpl.
      rewrite {1}/pmf /= /dbind_pmf /=.
      rewrite {2}/pmf /= /dret_pmf /=.
      assert (forall a0 : A * B, μ a0 * (if bool_decide ((b, a) = (let '(a1, b0) := a0 in (b0, a1))) then 1 else 0)
                                     = if bool_decide ((a, b) = a0 ) then μ (a, b) else 0) as Heq1.
      { intros (a' & b').
        case_bool_decide; case_bool_decide; simplify_eq; try lra.
      }
      rewrite (SeriesC_ext _ _ Heq1).
      apply SeriesC_singleton'.
    + intro a.
      rewrite <- HμL.
      rewrite lmarg_pmf rmarg_pmf.
      apply SeriesC_ext; intro b.
      simpl.
      rewrite {1}/pmf /= /dbind_pmf /=.
      rewrite {2}/pmf /= /dret_pmf /=.
      assert (forall a0 : A * B, μ a0 * (if bool_decide ((b, a) = (let '(a1, b0) := a0 in (b0, a1))) then 1 else 0)
                                     = if bool_decide ((a, b) = a0 ) then μ (a, b) else 0) as Heq1.
      { intros (a' & b').
        case_bool_decide; case_bool_decide; simplify_eq; try lra. }
      rewrite (SeriesC_ext _ _ Heq1).
      apply SeriesC_singleton'.
  Qed.




  Proposition coupl_bind :
    forall (f : A → distr A') (g : B → distr B') (μ1 : distr A) (μ2 : distr B),
      (∀ a b, coupl (f a) (g b)) → coupl μ1 μ2 → coupl (dbind f μ1) (dbind g μ2).
  Proof.
    intros f g μ1 μ2 Hfg (μ & Hμ).
    rewrite /coupl in Hfg.
    assert (∀ (p : A * B), ∃ μ : distr (A' * B'), isCoupl (f p.1) (g p.2) μ) as Hfg'; auto.
    pose proof (Choice (A * B) (distr (A' * B')) _ Hfg') as Ch.

    rewrite /coupl.
    destruct Ch as (Ch & HCh).
    exists (dbind Ch μ); split.
    + apply distr_ext; intro a'.
      rewrite lmarg_pmf.
      simpl.
      unfold dbind_pmf.
      rewrite (SeriesC_double_swap (λ '(b, a), μ a * Ch a (a', b))).
      assert (∀ b, SeriesC (λ a : B', μ b * Ch b (a', a)) = μ b * SeriesC (λ a : B', Ch b (a', a))) as Heq1.
      {
        intro b; apply SeriesC_scal_l.
      }
      rewrite (SeriesC_ext _ _ Heq1).
      assert (∀ p , μ p * SeriesC (λ b' : B', Ch p (a', b')) = μ p * f p.1 a') as Heq2.
      { intros (a & b).
        specialize (HCh (a, b)) as (HChL & HChR).
        rewrite <- HChL.
        rewrite lmarg_pmf.
        auto.
      }
      rewrite (SeriesC_ext _ _ Heq2).
      rewrite SeriesC_double_prod_lr.
      assert (∀ a : A, SeriesC (λ b : B, μ (a, b) * f (a, b).1 a')
               = SeriesC (λ b : B, μ (a, b) ) * f a a') as Heq3.
      {
        intro a; simpl; apply SeriesC_scal_r.
      }
      rewrite (SeriesC_ext _ _ Heq3).
      assert (∀ a, SeriesC (λ b : B, μ (a, b)) = μ1 a) as Heq4.
      {
        intro a.
        destruct Hμ as (Hμ1 & Hμ2).
        rewrite <- Hμ1;
        rewrite lmarg_pmf; auto.
      }
      apply SeriesC_ext.
      intro a.
      rewrite (Heq4 a); auto.
(* The second half is esentially the same as the first, can it be proven somehow by symmetry? *)
    + apply distr_ext; intro b'.
      rewrite rmarg_pmf.
      simpl.
      unfold dbind_pmf.
      rewrite (SeriesC_double_swap (λ '(a, a0), μ a0 * Ch a0 (a, b'))).
      assert (∀ p, SeriesC (λ a : A', μ p * Ch p (a, b')) = μ p * SeriesC (λ a : A', Ch p (a, b'))) as Heq1.
      {
        intro p; apply SeriesC_scal_l.
      }
      rewrite (SeriesC_ext _ _ Heq1).
      assert (∀ p , μ p * SeriesC (λ a' : A', Ch p (a', b')) = μ p * g p.2 b') as Heq2.
      { intros (a & b).
        specialize (HCh (a, b)) as (HChL & HChR).
        rewrite <- HChR.
        rewrite rmarg_pmf.
        auto.
      }
      rewrite (SeriesC_ext _ _ Heq2).
      rewrite SeriesC_double_prod_rl.
      assert (∀ b : B, SeriesC (λ a : A, μ (a, b) * g (a, b).2 b')
               = SeriesC (λ a : A, μ (a, b) ) * g b b') as Heq3.
      {
        intro b; simpl; apply SeriesC_scal_r.
      }
      rewrite (SeriesC_ext _ _ Heq3).
      assert (∀ b, SeriesC (λ a : A, μ (a, b)) = μ2 b) as Heq4.
      {
        intro b.
        destruct Hμ as (Hμ1 & Hμ2).
        rewrite <- Hμ2;
        rewrite rmarg_pmf; auto.
      }
      apply SeriesC_ext.
      intro b.
      rewrite (Heq4 b); auto.
  Qed.


  Proposition Rcoupl_bind :
    forall (f : A → distr A') (g : B → distr B') (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) (S : A' → B' → Prop),
      (∀ a b, R a b → Rcoupl (f a) (g b) S) → Rcoupl μ1 μ2 R → Rcoupl (dbind f μ1) (dbind g μ2) S.
  Proof.
    intros f g μ1 μ2 R S Hfg (μ & HμC & HμS).
    rewrite /Rcoupl /isRcoupl in Hfg.
    (* First we rewrite Hfg to be able to use Choice *)
    assert (∀ (p : A * B), ∃ μ' : distr (A' * B'), R p.1 p.2 → (isCoupl (f p.1) (g p.2) μ' ∧
                                                     (∀ q : A' * B', μ' q > 0 → S q.1 q.2))) as Hfg'; auto.
    {
      intro p.
      specialize (HμS p).
      specialize (Hfg p.1 p.2).
      pose proof (ExcludedMiddle (R p.1 p.2)) as H3; destruct H3 as [HR | HnR].
      + specialize (Hfg HR).
        destruct Hfg as (μ' & Hμ'1 & Hμ'2).
        exists μ'; auto.
      + exists dzero; intro ; done.
    }
    pose proof (Choice (A * B) (distr (A' * B')) _ Hfg') as (Ch & HCh).
    rewrite /Rcoupl /isRcoupl.
    exists (dbind Ch μ); split; try split.
 (* To prove that the first marginal coincides is a matter of rearranging the sums and using the
    fact that μ and (Ch p) are couplings *)
    + apply distr_ext; intro a'.
      rewrite lmarg_pmf /= /dbind_pmf
       (SeriesC_double_swap (λ '(b, a), μ a * Ch a (a', b))).
      erewrite (SeriesC_ext _ (λ b, μ b * SeriesC (λ a : B', Ch b (a', a))) );
      [ | intro p; apply SeriesC_scal_l].
      erewrite (SeriesC_ext _ (λ p, μ p * f p.1 a')); last first.
      { intros (a & b).
        destruct (Rtotal_order (μ (a, b)) 0) as [Hlt | [Heqz | Hgt]].
        - pose proof (pmf_pos μ (a, b)); lra.
        - rewrite Heqz; lra.
        - specialize (HCh (a, b) (HμS (a, b) Hgt )) as ((HChL & HChR) & HChS).
          rewrite -HChL lmarg_pmf //=. }
      rewrite SeriesC_double_prod_lr.
      erewrite (SeriesC_ext _ (λ a, SeriesC (λ b : B, μ (a, b) ) * f a a'));
      [ | intro a; simpl; apply SeriesC_scal_r ].
      erewrite (SeriesC_ext _ (λ a, (μ1 a) * f a a')); auto.
      intro a.
      destruct HμC as (Hμ1 & Hμ2).
      rewrite <- Hμ1;
      rewrite lmarg_pmf; auto.
(* The second half is esentially the same as the first, can it be proven somehow by symmetry? *)
    + apply distr_ext; intro b'.
      rewrite rmarg_pmf /= /dbind_pmf
      (SeriesC_double_swap (λ '(a, a0), μ a0 * Ch a0 (a, b'))).
      erewrite (SeriesC_ext _ (λ b, μ b * SeriesC (λ a : A', Ch b (a, b'))) );
      [ | intro p; apply SeriesC_scal_l].
      erewrite (SeriesC_ext _ (λ p, μ p * g p.2 b')); last first.
      {intros (a & b);
        destruct (Rtotal_order (μ (a, b)) 0) as [Hlt | [Heqz | Hgt]];
        [ pose proof (pmf_pos μ (a, b)); lra | rewrite Heqz; lra |
        specialize (HCh (a, b) (HμS (a, b) Hgt)) as ((HChL & HChR) & HChS);
        rewrite -HChR rmarg_pmf //=].
       }
      rewrite SeriesC_double_prod_rl.
      erewrite (SeriesC_ext _ (λ b, SeriesC (λ a : A, μ (a, b) ) * g b b'));
      [ | intro b; simpl; apply SeriesC_scal_r].
      erewrite (SeriesC_ext _ (λ b, (μ2 b) * g b b')); auto.
      intro b.
      destruct HμC as (Hμ1 & Hμ2).
      rewrite <- Hμ2;
      rewrite rmarg_pmf; auto.
    + intros (a' & b') H3; simpl.
      pose proof (dbind_pos_support Ch μ (a', b')) as (H4 & H5).
      specialize (H4 H3) as ((a0, b0) & H7 & H8).
      specialize (HCh (a0, b0) (HμS (a0, b0) H8)) as (HCh1 & HCh2).
      specialize (HCh2 (a', b') H7).
      done.
  Qed.



  Proposition eqcoupl_elim :
    forall (μ1 μ2 : distr A),
      Rcoupl μ1 μ2 (=) → μ1 = μ2.
  Proof.
    intros μ1 μ2 (μ & (HμL & HμR) & HμS).
    rewrite <- HμL, <- HμR.
    apply distr_ext.
    intro a1.
    rewrite lmarg_pmf rmarg_pmf.
    apply SeriesC_ext.
    intro a2.
    specialize (HμS (a1, a2)) as HμS12.
    specialize (HμS (a2, a1)) as HμS21.
    simpl in HμS12.
    simpl in HμS21.
    pose proof (Rtotal_order (μ (a1, a2)) (μ (a2, a1))) as [Hlt | [Heq | Hgt]]; auto.
    + pose proof (pmf_pos μ (a1, a2)).
      assert (μ (a2, a1) > 0) as H'; try lra.
      specialize (HμS21 H'); destruct HμS21; auto.
    + pose proof (pmf_pos μ (a2, a1)).
      assert (μ (a1, a2) > 0) as H'; try lra.
      specialize (HμS12 H'); destruct HμS12; auto.
  Qed.

  Proposition Rcoupl_wk (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) (S : A → B → Prop):
      (forall a b, R a b -> S a b) -> Rcoupl μ1 μ2 R -> Rcoupl μ1 μ2 S.
  Proof.
    intros Hwk [μ [[HμL HμR] HμSupp]].
    exists μ; split; [split | ]; auto.
  Qed.


  Lemma Rcoupl_inhabited_l (μ1 : distr A) (μ2 : distr B) R :
    Rcoupl μ1 μ2 R →
    SeriesC μ1 > 0 →
    ∃ a b, R a b.
  Proof.
    intros [μ [Hcpl HR]] Hz.
    assert (SeriesC μ > 0) as Hsup by by erewrite isCoupl_mass_l.
    apply SeriesC_gtz_ex in Hsup as [[a b] Hμ]; [|done].
    eauto.
  Qed.

  Lemma Rcoupl_inhabited_r (μ1 : distr A) (μ2 : distr B) R :
    Rcoupl μ1 μ2 R →
    SeriesC μ2 > 0 →
    ∃ a b, R a b.
  Proof.
    intros [μ [Hcpl HR]] Hz.
    assert (SeriesC μ > 0) as Hsup by by erewrite isCoupl_mass_r.
    apply SeriesC_gtz_ex in Hsup as [[a b] Hμ]; [|done].
    eauto.
  Qed.



End couplings_theory.



(* TODO: cleanup *)
Section Rcoupl.
  Context `{Countable A, Countable B}.
  Variable (μ1 : distr A) (μ2 : distr B).

  Lemma Rcoupl_trivial :
    SeriesC μ1 = 1 ->
    SeriesC μ2 = 1 ->
    Rcoupl μ1 μ2 (λ _ _, True).
  Proof.
    intros Hμ1 Hμ2.
    exists (dprod μ1 μ2). split; [|done].
    split; [apply lmarg_dprod|apply rmarg_dprod]; done.
  Qed.

  Lemma Rcoupl_pos_R R :
    Rcoupl μ1 μ2 R → Rcoupl μ1 μ2 (λ a b, R a b ∧ μ1 a > 0 ∧ μ2 b > 0).
  Proof.
    intros [μ [[Hμ1 Hμ2] HR]].
    exists μ. split; [done|].
    intros [a b] Hρ. split; [auto|].
    rewrite -Hμ1 -Hμ2.
    rewrite 2!dmap_pos.
    split; eauto.
  Qed.

End Rcoupl.

Lemma Rcoupl_dzero_r_inv `{Countable A, Countable B} μ1 (R : A → B → Prop) :
  Rcoupl μ1 dzero R → μ1 = dzero.
Proof.
  intros Hz%Rcoupl_mass_eq.
  apply SeriesC_zero_dzero.
  rewrite Hz SeriesC_0 //.
Qed.

Lemma Rcoupl_dzero_l_inv `{Countable A, Countable B} μ2 (R : A → B → Prop) :
  Rcoupl dzero μ2 R → μ2 = dzero.
Proof.
  intros Hz%Rcoupl_mass_eq.
  apply SeriesC_zero_dzero.
  rewrite -Hz SeriesC_0 //.
Qed.

  Proposition Rcoupl_map `{Countable A, Countable B, Countable A', Countable B'}:
    forall (f : A → A') (g : B → B') (μ1 : distr A) (μ2 : distr B) (R : A' → B' → Prop),
      Rcoupl μ1 μ2 (λ a a', R (f a) (g a')) -> Rcoupl (dmap f μ1) (dmap g μ2) R.
  Proof.
    intros f g μ1 μ2 R Hcoupl.
    rewrite /dmap.
    eapply (Rcoupl_bind _ _ _ _ (λ (a : A) (a' : B), R (f a) (g a'))); auto.
    intros a b Hab.
    apply (Rcoupl_ret (f a) (g b) R Hab).
  Qed.


  (* I think this should be true, maybe it can be proven through Strassens theorem, but
  I don't see how to do it directly

  Proposition Rcoupl_from_map `{Countable A, Countable B, Countable A', Countable B'}:
    forall (f : A → A') (g : B → B') (μ1 : distr A) (μ2 : distr B) (R : A' → B' → Prop),
      Rcoupl (dmap f μ1) (dmap g μ2) R -> Rcoupl μ1 μ2 (λ a a', R (f a) (g a')).
  Proof.
    intros f g μ1 μ2 R (μ & ((HμL & HμR) & HμSup)).
    eexists (dprod μ1 μ2).
    split; [split | ].

    eexists (MkDistr (λ '(a, b), μ (f a , g b)) _ _ _).

  Qed.
*)





  (* This is a lemma about convex combinations, but it is easier to prove with couplings
     TODO: find a better place to put it in *)
  Lemma fair_conv_comb_dbind `{Countable A, Countable B} (μ1 μ2 : distr A) (f : A -> distr B) :
    dbind f (fair_conv_comb μ1 μ2) = fair_conv_comb (dbind f μ1) (dbind f μ2).
  Proof.
    rewrite /fair_conv_comb -dbind_assoc.
    apply eqcoupl_elim.
    eapply (Rcoupl_bind _ _ _ _ (=)); [ | apply Rcoupl_eq].
    intros b1 b2 ->.
    destruct b2; apply Rcoupl_eq.
  Qed.


Section Rcoupl_strength.
  Context `{Countable A, Countable B, Countable D, Countable E}.

  Variable (μ1 : distr A) (μ2 : distr B).

  Lemma Rcoupl_strength_l (R : A → B → Prop) (d : D)  :
    Rcoupl μ1 μ2 R →
    Rcoupl (strength_l d μ1) μ2 (λ '(d', a) b, d' = d ∧ R a b).
  Proof.
    rewrite /strength_l /dmap.
    intros Hcpl.
    rewrite -(dret_id_right μ2).
    eapply Rcoupl_bind; [|done].
    intros. by apply Rcoupl_ret.
  Qed.

  Lemma Rcoupl_strength (R : A → B → Prop) (d : D) (e : E) :
    Rcoupl μ1 μ2 R →
    Rcoupl (strength_l d μ1) (strength_l e μ2)
      (λ '(d', a) '(e', b), d' = d ∧ e' = e ∧ R a b).
  Proof.
    rewrite /strength_l /dmap.
    eapply Rcoupl_bind.
    intros. by apply Rcoupl_ret.
  Qed.

End Rcoupl_strength.



Section refinement_couplings.

  Context `{Countable A, Countable B, Countable A', Countable B'}.
  Context (μ1 : distr A) (μ2 : distr B) (R : A -> B -> Prop) (S : A' → B' → Prop).

  Definition isRefCoupl (μ : distr (A * B)) : Prop :=
    lmarg μ = μ1 /\ (∀ a, rmarg μ a <= μ2 a).

  Definition refCoupl :=
    ∃ (μ : distr (A * B)), isRefCoupl μ.

  Definition isRefRcoupl (μ : distr (A * B)) : Prop :=
    isRefCoupl μ ∧ (forall (p : A * B), (μ p > 0) -> R (fst p) (snd p)).

  Definition refRcoupl :=
    ∃ (μ : distr (A * B)), isRefRcoupl μ.


End refinement_couplings.

Section ref_couplings_theory.

Context `{Countable A, Countable B}.


  (* TODO
  Lemma refRcoupl_trivial (μ1 :distr A) (μ2 :distr B):
    SeriesC μ1 <= SeriesC μ2 ->
    refRcoupl μ1 μ2 (λ _ _, True).
  Proof.
    intros Hμ.
    Search Rle.
    destruct (Rle_lt_dec (SeriesC μ1) 0) as [H3 | H3].
    + destruct H3; [pose proof (pmf_SeriesC_ge_0 μ1); lra | ].
    eexists (distr_scal (Rinv(SeriesC μ1)) (dprod μ1 μ2) _).
    Unshelve.
    2:{
      split.
      + admit.
      + admit.
    }
    split; [|done].
    split.
    + intro a.
      rewrite lmarg_pmf.
      rewrite {2}/pmf/=.
      rewrite SeriesC_scal_l.
      rewrite -lmarg_pmf.
      rewrite lmarg_dprod_pmf.
      rewrite <- Rmult_comm.
      rewrite Rmult_assoc.
      rewrite <- Rmult_1_r at 1.
      apply Rmult_le_compat; auto; try lra.
      Search Rinv.


    [apply lmarg_dprod|apply rmarg_dprod]; done.
  Qed.
*)

  Proposition refcoupl_elim :
    forall (μ1 μ2 : distr A),
      refRcoupl μ1 μ2 (=) → (∀ a, μ1 a <= μ2 a).
  Proof.
    intros μ1 μ2 (μ & (HμL & HμR) & HμS) a.
    eapply (Rle_Transitive _ (rmarg μ a) _); auto.
    rewrite <- HμL.
    rewrite lmarg_pmf rmarg_pmf.
    eapply SeriesC_le.
    { intro .  specialize (HμS (a,n)). simpl in HμS.
      destruct (Rtotal_order (μ (a,n)) 0) as [? | [? | H3]];
      [ pose proof (pmf_pos μ (a, n)); lra |
       pose proof (pmf_pos μ (n, a)); lra |
      pose proof (HμS H3); simplify_eq; lra ].
    }
    apply ex_seriesC_rmarg.
  Qed.


  Proposition refcoupl_from_ineq (μ1 μ2 : distr A) :
      (∀ a, μ1 a <= μ2 a) -> refRcoupl μ1 μ2 (=).
  Proof.
    intro Hleq.
    exists (ddiag μ1). split;[ split  | ].
    + apply distr_ext; intro a.
      rewrite lmarg_pmf {2}/pmf/=.
      rewrite SeriesC_singleton'; auto.
    + intro a.
      rewrite ddiag_rmarg.
      auto.
    + intros p Hp.
      rewrite ddiag_pmf in Hp.
      case_bool_decide; auto; lra.
  Qed.

  Proposition is_ref_coupl_ret :
    forall (a : A) (b : B), isRefCoupl (dret a) (dret b) (dret (a, b)).
  Proof.
    intros a b; split; [rewrite /lmarg dmap_dret // | rewrite /rmarg dmap_dret //].
   Qed.

  Proposition ref_coupl_ret :
    forall (a : A) (b : B), refCoupl (dret a) (dret b).
  Proof.
    intros a b.
    exists (dret (a, b)).
    apply is_ref_coupl_ret.
  Qed.


  Proposition weaken_coupl (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) :
      Rcoupl μ1 μ2 R → refRcoupl μ1 μ2 R.
  Proof.
    rewrite /refRcoupl /Rcoupl.
    intros (μ & ((HμL & HμR) & HμSupp)).
    exists μ.
    split; auto.
    split; auto.
    intro.
    rewrite HμR; lra.
  Qed.

  Lemma refRcoupl_ret a b (R : A → B → Prop) :
    R a b → refRcoupl (dret a) (dret b) R.
  Proof.
    intros HR.
    eexists. split; [eapply is_ref_coupl_ret|].
    intros [] [=<- <-]%dret_pos. done.
  Qed.

  Context `{Countable A', Countable B'}.

 Proposition refRcoupl_bind :
    forall (f : A → distr A') (g : B → distr B') (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) (S : A' → B' → Prop),
      (∀ a b, R a b → refRcoupl (f a) (g b) S) → refRcoupl μ1 μ2 R → refRcoupl (dbind f μ1) (dbind g μ2) S.
  Proof.
    intros f g μ1 μ2 R S Hfg (μ & HμC & HμS).
    rewrite /Rcoupl /isRcoupl in Hfg.
    (* First we rewrite Hfg to be able to use Choice *)
    assert (∀ (p : A * B), ∃ μ' : distr (A' * B'), R p.1 p.2 → (isRefCoupl (f p.1) (g p.2) μ' ∧
                                                     (∀ q : A' * B', μ' q > 0 → S q.1 q.2))) as Hfg'; auto.
    {
      intro p.
      specialize (HμS p).
      specialize (Hfg p.1 p.2).
      pose proof (ExcludedMiddle (R p.1 p.2)) as H3; destruct H3 as [HR | HnR].
      + specialize (Hfg HR).
        destruct Hfg as (μ' & Hμ'1 & Hμ'2).
        exists μ'; auto.
      + exists dzero; intro ; done.
    }
    pose proof (Choice (A * B) (distr (A' * B')) _ Hfg') as (Ch & HCh).
    rewrite /Rcoupl /isRcoupl.
    exists (dbind Ch μ); split; try split.
 (* To prove that the first marginal coincides is a matter of rearranging the sums and using the
    fact that μ and (Ch p) are couplings *)
    + apply distr_ext; intro a'.
      rewrite lmarg_pmf /= /dbind_pmf
       (SeriesC_double_swap (λ '(b, a), μ a * Ch a (a', b))).
      erewrite (SeriesC_ext _ (λ b, μ b * SeriesC (λ a : B', Ch b (a', a))) );
      [ | intro p; apply SeriesC_scal_l].
      erewrite (SeriesC_ext _ (λ p, μ p * f p.1 a')); last first.
      { intros (a & b).
        destruct (Rtotal_order (μ (a, b)) 0) as [Hlt | [Heqz | Hgt]].
        + pose proof (pmf_pos μ (a, b)); lra.
        + rewrite Heqz; lra.
        + specialize (HCh (a, b) (HμS (a, b) Hgt )) as ((HChL & HChR) & HChS).
          rewrite -HChL lmarg_pmf //=.
          }
      rewrite SeriesC_double_prod_lr.
      erewrite (SeriesC_ext _ (λ a, SeriesC (λ b : B, μ (a, b) ) * f a a'));
      [ | intro a; simpl; apply SeriesC_scal_r ].
      erewrite (SeriesC_ext _ (λ a, (μ1 a) * f a a')); auto.
      intro a.
      destruct HμC as (Hμ1 & Hμ2).
      rewrite <- Hμ1;
      rewrite lmarg_pmf; auto.
    + intro b'.
      rewrite rmarg_pmf /dbind_pmf.
      rewrite (SeriesC_double_swap (λ '(a, a0), μ a0 * Ch a0 (a, b'))).
      erewrite (SeriesC_ext _ (λ b, μ b * SeriesC (λ a : A', Ch b (a, b'))) );
      [ | intro p; apply SeriesC_scal_l].
      apply (Rle_trans _ (SeriesC (λ p, μ p * g p.2 b')) _).
      {
        apply SeriesC_le; [ | ]; last first.
        + apply (ex_seriesC_le _ μ); auto.
          intros; split.
          ++ apply Rmult_le_pos; auto.
          ++ rewrite <- Rmult_1_r.
             apply Rmult_le_compat_l; auto.
        + intros (a & b); split; [ apply Rmult_le_pos; auto | ].
        {
          assert (SeriesC (λ a0 : A', Ch (a, b) (a0, b')) = rmarg (Ch (a, b)) b') as ->;
          [rewrite rmarg_pmf; auto | apply pmf_pos].
        }
        destruct (Rtotal_order (μ (a, b)) 0) as [Hlt | [Heqz | Hgt]].
        ++ pose proof (pmf_pos μ (a, b)); lra.
        ++ rewrite Heqz; lra.
        ++ specialize (HCh (a, b) (HμS (a, b) Hgt )) as ((HChL & HChR) & HChS).
          specialize (HChR b').
          rewrite (rmarg_pmf (Ch (a, b))) in HChR.
          apply Rmult_le_compat_l; auto.
      }
      rewrite {3}/pmf /= /dbind_pmf /=.
      rewrite SeriesC_double_prod_rl /=.
      apply SeriesC_le; [ | ]; last first.
      {
        apply (ex_seriesC_le _ μ2); auto.
        intros; split.
        + apply Rmult_le_pos; auto.
        + rewrite <- Rmult_1_r.
          apply Rmult_le_compat_l; auto.
      }
      intro b; split.
      ++ rewrite SeriesC_scal_r.
         apply Rmult_le_pos ; auto.
         assert (SeriesC (λ x : A, μ (x, b)) = rmarg μ b ) as -> ; [rewrite rmarg_pmf | apply pmf_pos ]; auto.
      ++ destruct HμC as [HμCL HμCR].
         rewrite SeriesC_scal_r.
         apply Rmult_le_compat_r; auto.
         specialize (HμCR b).
         rewrite rmarg_pmf in HμCR; auto.
    + intros (a' & b') H3; simpl.
      pose proof (dbind_pos_support Ch μ (a', b')) as (H4 & H5).
      specialize (H4 H3) as ((a0, b0) & H7 & H8).
      specialize (HCh (a0, b0) (HμS (a0, b0) H8)) as (HCh1 & HCh2).
      specialize (HCh2 (a', b') H7).
      done.
  Qed.

  Lemma refRcoupl_dzero (μ : distr B) (R: A → B → Prop):
    refRcoupl dzero μ R.
  Proof.
    exists dzero; split; try split.
    + rewrite /lmarg dmap_dzero; done.
    + intro a.
      rewrite rmarg_pmf {1}/pmf/=.
      rewrite SeriesC_0; auto.
    + rewrite /pmf/=; intros; lra.
  Qed.


  Proposition refRcoupl_wk (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) (S : A → B → Prop):
      (forall a b, R a b -> S a b) -> refRcoupl μ1 μ2 R -> refRcoupl μ1 μ2 S.
  Proof.
    intros Hwk [μ [[HμL HμR] HμSupp]].
    exists μ; split; [split | ]; auto.
  Qed.

End ref_couplings_theory.





(*
Section iter_couplings.



Fixpoint iter_dbind `{Countable A} (F : A → distr A) (n : nat) (a : A) : distr A :=
  match n with
  | 0 => dret a
  | S m => dbind (iter_dbind F m) (F a)
  end.

Lemma iter_dbind_sym `{Countable A} (F : A → distr A) (a : A) (n : nat) :
  dbind (iter_dbind F n) (F a) = dbind F (iter_dbind F n a).
Proof.
  generalize a.
  induction n.
  + intro; simpl.
    rewrite dret_id_right.
    rewrite dret_id_left.
    auto.
  + (* This can be made cleaner, but it works for now *)
    intro a'.
    assert (iter_dbind F (S n) a' = dbind (iter_dbind F n) (F a')) as ->; auto.
    assert (iter_dbind F (S n) = λ x, dbind (iter_dbind F n) (F x)) as ->; auto.
    apply distr_ext; intros a''.
    rewrite <- dbind_assoc.
    rewrite /pmf/=/dbind_pmf/=.
    apply SeriesC_ext; intros.
    assert ((F n0 ≫= iter_dbind F n) a'' = (iter_dbind F n n0 ≫= [eta F]) a'' ) as ->; [ | try lra].
    rewrite IHn; auto.
Qed.


Program Definition iter_lim `{Countable A} (F : A → distr A) (a : A) : distr A :=
  MkDistr (λ a', Lim_seq (λ n, iter_dbind F n a a')) _ _ _.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

Lemma lim_is_fixpoint `{Countable A} (F : A → distr A) (a : A) :
  dbind F (iter_lim F a) = iter_lim F a.
Proof. Admitted.

Lemma lim_is_fixpoint2 `{Countable A} (F : A → distr A) (a : A) :
  dbind (iter_lim F) (F a) = iter_lim F a.
Proof. Admitted.


Lemma lim_is_fixpoint3 `{Countable A} (F : A → distr A) (a : A) :
  dbind (iter_lim F) (iter_lim F a) = iter_lim F a.
Proof. Admitted.

Definition step_refRcoupl `{Countable A, Countable B} (F : A → distr A) (G : B → distr B) (R : A → B → Prop) (a : A) (b : B)  :=
  forall n, refRcoupl (iter_dbind F n a) (iter_lim G b) R.

Lemma step_refRcoupl_ind `{Countable A, Countable B} (F : A → distr A) (G : B → distr B) (a : A) (b : B) (R : A → B → Prop) :
  (refRcoupl (dret a) (iter_lim G b) R) ->
  (∀ a b, R a b -> refRcoupl (F a) (G b) (step_refRcoupl F G R)) ->
  step_refRcoupl F G R a b.
Proof.
  intros Hz Hstep n.
  induction n.
  + rewrite {1}/iter_dbind; auto.
  + (*destruct IHn as [m Hm].*)
    assert (iter_dbind F (S n) a = dbind (iter_dbind F n) (F a)) as ->; auto.
    pose proof (refRcoupl_bind F G (iter_dbind F n a) (iter_lim G b) R (step_refRcoupl F G R) IHn Hstep) as Haux.
    rewrite lim_is_fixpoint in Haux.
    rewrite <- iter_dbind_sym in Haux.
    rewrite /step_refRcoupl in Haux.
    apply (refRcoupl_wk (F a ≫= iter_dbind F n) (iter_lim G b) _
             (λ (a : A) (b : B), refRcoupl (iter_dbind F 0 a) (iter_lim G b) R)) in Haux; auto.
    assert (refRcoupl ((F a ≫= iter_dbind F n) ≫= (iter_dbind F 0)) ((iter_lim G b) ≫= (iter_lim G)) R) as Hcoupl.
    { apply (refRcoupl_bind _ _ _ _ (λ (a : A) (b : B), refRcoupl (iter_dbind F 0 a) (iter_lim G b) R)); auto.
    }
    rewrite {1}/iter_dbind/= dret_id_right lim_is_fixpoint3 in Hcoupl.
    done.
Qed.




End iter_couplings.
*)

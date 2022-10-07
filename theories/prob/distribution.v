From Coq Require Import Reals Psatz.
From Coq.ssr Require Import ssreflect.
From Coquelicot Require Import Rcomplements Rbar Series Lim_seq Hierarchy.
From stdpp Require Export countable.
From self.prelude Require Export base Coquelicot_ext Reals_ext classical.
From self.prob Require Export countable_sum double.

Record distr (A : Type) `{Countable A} := MkDistr {
  pmf :> A → R;
  pmf_pos : ∀ a, 0 <= pmf a;
  pmf_ex_seriesC : ex_seriesC pmf;
  pmf_SeriesC : SeriesC pmf <= 1;
}.

Arguments MkDistr {_ _ _}.
Arguments pmf {_ _ _ _}.
Arguments pmf_pos {_ _ _}.
Arguments pmf_ex_seriesC {_ _ _}.
Arguments pmf_SeriesC {_ _ _}.

#[global] Hint Resolve pmf_pos pmf_ex_seriesC pmf_SeriesC : core.

Notation Decidable P := (∀ x, Decision (P x)).

#[local] Open Scope R.

Section distributions.
  Context `{Countable A}.

  Implicit Types μ d : distr A.

  Lemma pmf_le_1 μ a : μ a <= 1.
  Proof.
    assert (SeriesC (λ a', if bool_decide (a' = a) then μ a else 0) = μ a) as <-.
    { eapply SeriesC_singleton. }
    etransitivity; [|eapply (pmf_SeriesC μ)].
    apply SeriesC_le; [|done].
    intros a'. case_bool_decide; subst; split; try (lra || done).
  Qed.

  Lemma pmf_SeriesC_ge_0 μ : 0 <= SeriesC μ.
  Proof.
    transitivity (SeriesC (λ (_ : A), 0)).
    { apply SeriesC_ge_0; [done|]. apply ex_seriesC_0. }
    apply SeriesC_le'; auto. apply ex_seriesC_0.
  Qed.

  Lemma pmf_ex_seriesC_mult (μ1 μ2 : distr A) :
    ex_seriesC (λ a, μ1 a * μ2 a).
  Proof.
    eapply (ex_seriesC_le _ (λ a, μ1 a * 1)); [|by apply ex_seriesC_scal_r].
    intros a.
    split; [by apply Rmult_le_pos|].
    eapply Rmult_le_compat_l; [done|].
    apply pmf_le_1.
  Qed.

  (* N.B. uses [functional_extensionality] and [proof_irrelevance] axioms  *)
  Lemma distr_ext (d1 d2 : distr A) :
    (∀ a, d1.(pmf) a = d2.(pmf) a) → d1 = d2.
  Proof.
    destruct d1 as [pmf1 ?], d2 as [pmf2 ?] =>/=. intros Ha.
    assert (pmf1 = pmf2) as ->; [by extensionality b|].
    f_equal; apply proof_irrelevance.
  Qed.

End distributions.

Section zero_distr.
  Context `{Countable A}.

  Program Definition dzero : distr A := MkDistr (λ _, 0) _ _ _.
  Next Obligation. done. Qed.
  Next Obligation. eapply ex_seriesC_0. Qed.
  Next Obligation. rewrite SeriesC_0 //. lra. Qed.
End zero_distr.

Section monadic.
  Context `{Countable A}.

  Definition dret_pmf (a : A) : A → R :=
    λ (a' : A), if bool_decide (a' = a) then 1 else 0.

  Program Definition dret (a : A) : distr A := MkDistr (dret_pmf a) _ _ _.
  Next Obligation. intros. rewrite /dret_pmf. case_bool_decide; nra. Qed.
  Next Obligation. intros. apply ex_seriesC_singleton. Qed.
  Next Obligation. intros. rewrite SeriesC_singleton //. Qed.

  Context `{Countable B}.

  Definition dbind_pmf (f : A → distr B) (μ : distr A) : B → R :=
    λ (b : B), SeriesC (λ (a : A), μ a * f a b).

  Program Definition dbind (f : A → distr B) (μ : distr A) : distr B :=
    MkDistr (dbind_pmf f μ) _ _ _.
  Next Obligation.
    intros f μ b. rewrite /dbind_pmf.
    apply SeriesC_ge_0.
    - intros a'. by apply Rmult_le_pos.
    - eapply (ex_seriesC_le _ (λ a, μ a * 1)); [|by apply ex_seriesC_scal_r].
      intros a. split; [by apply Rmult_le_pos|].
      eapply Rmult_le_compat_l; [done|].
      eapply pmf_le_1.
  Qed.
  Next Obligation.
    intros f μ. rewrite /dbind_pmf.
    eapply (ex_seriesC_double_swap_impl (λ '(a, b), _)).
    eapply (ex_seriesC_ext (λ j, μ j * SeriesC (λ k, f j k))).
    { intros a. rewrite SeriesC_scal_l //. }
    apply (ex_seriesC_le _ (λ a : A, μ a * 1)); [|by apply ex_seriesC_scal_r].
    intros a. split.
    - apply Rmult_le_pos; [done|].
      apply SeriesC_ge_0; auto.
    - by apply Rmult_le_compat_l.
  Qed.
  Next Obligation.
    intros f μ. rewrite /dbind_pmf.
    rewrite (SeriesC_double_swap (λ '(a, b), _)).
    rewrite -(SeriesC_ext (λ k, μ k * SeriesC (λ j, f k j))); last first.
    { intros a. rewrite SeriesC_scal_l //. }
    transitivity (SeriesC μ); [|done].
    eapply SeriesC_le; [|done].
    intros a.
    split.
    - apply Rmult_le_pos; [done|].
      apply SeriesC_ge_0; auto.
    - rewrite -{2}(Rmult_1_r (μ a)).
      by apply Rmult_le_compat_l.
  Qed.

End monadic.

(* TODO: generalize to distributions with countable support so that we can use
   the [stdpp] typeclasses *)
Notation "m ≫= f" := (dbind f m) (at level 60, right associativity) : stdpp_scope.
Notation "( m ≫=.)" := (λ f, dbind f m) (only parsing) : stdpp_scope.
Notation "(.≫= f )" := (dbind f) (only parsing) : stdpp_scope.
Notation "(≫=)" := (λ m f, dbind f m) (only parsing) : stdpp_scope.

Notation "x ← y ; z" := (y ≫= (λ x : _, z))
  (at level 20, y at level 100, z at level 200, only parsing) : stdpp_scope.

Notation "' x ← y ; z" := (y ≫= (λ x : _, z))
  (at level 20, x pattern, y at level 100, z at level 200, only parsing) : stdpp_scope.

Section dmap.
  Context `{Countable A, Countable B}.

  Definition dmap (f : A → B) (μ : distr A) : distr B :=
    a ← μ; dret (f a).
End dmap.

Section strength.
  Context `{Countable A, Countable B}.

  Definition strength_l (a : A) (μ : distr B) : distr (A * B) :=
    b ← μ; dret (a, b).

End strength.

Lemma dret_1 `{Countable A} (a a' : A) :
  a = a' → dret a a' = 1.
Proof. intros -> ; rewrite /= /dret_pmf bool_decide_eq_true_2 //. Qed.

Lemma dret_0 `{Countable A} (a a' : A) :
  a' ≠ a → dret a a' = 0.
Proof. intros ?. rewrite /= /dret_pmf bool_decide_eq_false_2 //. Qed.

Lemma dret_Rgt_zero_inv `{Countable A} (a a' : A) :
  dret a a' > 0 → a' = a.
Proof. rewrite /= /dret_pmf. intros ?. case_bool_decide; [done|lra]. Qed.

Lemma dret_pmf_map `{Countable A} (f : A → A) (a a' : A) `{Inj A A (=) (=) f} :
  dret (f a) (f a') = dret a a'.
Proof.
  rewrite /= /dret_pmf. case_bool_decide as Hcase.
  - apply (inj f) in Hcase as ->.  rewrite bool_decide_eq_true_2 //.
  - case_bool_decide; [|done]. simplify_eq.
Qed.

Lemma dbind_dret_pmf_map `{Countable A} (μ : distr A) (a : A) (f : A → A) `{Inj A A (=) (=) f} :
  (μ ≫= (λ a', dret (f a'))) (f a) = μ a.
Proof.
  rewrite /= /dbind_pmf /= /dret_pmf.
  rewrite (SeriesC_ext _ (λ a', if bool_decide (a' = a) then μ a else 0)).
  { rewrite SeriesC_singleton //. }
  intros a'. case_bool_decide as Heq; simplify_eq.
  - rewrite bool_decide_eq_true_2 //. lra.
  - rewrite bool_decide_eq_false_2; [lra|].
    by intros ->.
Qed.

Lemma dbind_pmf_ext `{Countable A, Countable B} (μ1 μ2 : distr A) (f g : A → distr B) (b1 b2 : B) :
  (∀ a b, f a b = g a b) →
  μ1 = μ2 →
  b1 = b2 →
  dbind f μ1 b1 = dbind g μ2 b2.
Proof.
  intros Hfg -> ->=>/=. rewrite /dbind_pmf.
  setoid_rewrite Hfg. done.
Qed.

(* #[global] Instance Proper_dbind `{Countable A, Countable B} : *)
(*   Proper (pointwise_relation A (=) ==> (=) ==> (=)) (@dbind A _ _ B _ _). *)
(* Proof. intros ?? Hp ?? ->. f_equal. extensionality x. done. Qed. *)

(* TODO: not all the lemmas rely on both A and B and the [Context {...}` will
   automatically add both [Countable X] instances as an assumption *)
Section monadic_theory.
  Context `{Countable A, Countable B}.

  Lemma dret_id_left_pmf (f : A → distr B) (a : A) (b : B) :
    (a' ← dret a; f a') b = f a b.
  Proof.
    rewrite /= /dbind_pmf /= /dret_pmf.
    rewrite (SeriesC_ext _ (λ a', if bool_decide (a' = a) then f a b else 0)).
    { rewrite SeriesC_singleton //. }
    intros a'. case_bool_decide; simplify_eq; lra.
  Qed.

  Lemma dret_id_left (f : A → distr B) (a : A) :
    (a' ← dret a; f a') = f a.
  Proof. apply distr_ext, dret_id_left_pmf. Qed.

  Lemma dret_id_right_pmf (μ : distr A) (a : A) :
    (a ← μ; dret a) a = μ a.
  Proof.
    rewrite /= /dbind_pmf /= /dret_pmf.
    rewrite (SeriesC_ext _ (λ a', if bool_decide (a' = a) then μ a else 0)).
    { rewrite SeriesC_singleton //. }
    intros a'. case_bool_decide; simplify_eq.
    - rewrite bool_decide_eq_true_2 //. lra.
    - rewrite bool_decide_eq_false_2 //. lra.
  Qed.

  Lemma dret_id_right (μ : distr A) :
    (a ← μ; dret a) = μ.
  Proof. apply distr_ext, dret_id_right_pmf. Qed.

  Lemma dbind_assoc_pmf `{Countable B'} (f : A → distr B) (g : B → distr B') (μ : distr A) c :
    (a ← μ ; b ← f a; g b) c = (b ← (a ← μ; f a); g b) c.
  Proof.
    simpl.
    rewrite /dbind_pmf.
    simpl.
    rewrite /dbind_pmf.
    assert (SeriesC (λ a : A, μ a * SeriesC (λ a0 : B, f a a0 * g a0 c)) =
              SeriesC (λ a : A, SeriesC (λ a0 : B, μ a * f a a0 * g a0 c))) as Heq1.
    { apply SeriesC_ext; intro a.
      rewrite <- SeriesC_scal_l.
      apply SeriesC_ext; intros n; lra. }
    rewrite Heq1.
    pose proof (SeriesC_double_swap (λ '(a ,a0), μ a * f a a0 * g a0 c)) as Heq2.
    simpl in Heq2.
    rewrite Heq2.
    apply SeriesC_ext.
    intro b.
    rewrite <- SeriesC_scal_r.
    apply SeriesC_ext.
    intro a.
    done.
  Qed.

  Lemma dbind_assoc `{Countable B'} (f : A → distr B) (g : B → distr B') (μ : distr A) :
    (a ← μ ; b ← f a; g b) = (b ← (a ← μ; f a); g b).
  Proof. apply distr_ext, dbind_assoc_pmf. Qed.


  Lemma dbind_pos_support (f : A → distr B) (μ : distr A) (b : B) :
    dbind f μ b > 0 ↔ ∃ a, f a b > 0 ∧ μ a > 0.
  Proof.
    rewrite /= /dbind_pmf. split.
    - eapply contrapositive. intros Hna.
      assert (∀ a, μ a * f a b = 0) as Hz.
      { intros a.
        pose proof (not_exists_forall_not _ _ Hna a) as [Hne | Hne]%not_and_or_not.
        - pose proof (pmf_pos (f a) b). assert (f a b = 0) as ->; lra.
        - pose proof (pmf_pos μ a). assert (μ a = 0) as ->; lra. }
      apply Rge_not_gt. rewrite SeriesC_0 //.
    - intros (a & Hf & Hμ). eapply Rlt_gt.
      eapply (Rlt_le_trans _ (SeriesC (λ a', if bool_decide (a' = a) then μ a * f a b else 0))).
      { rewrite SeriesC_singleton. eapply Rmult_gt_0_compat; lra. }
      eapply SeriesC_le.
      + intros ?. case_bool_decide; simplify_eq; split; done || by eapply Rmult_le_pos.
      + apply (ex_seriesC_le _ (λ a : A, μ a * 1)); [|by apply ex_seriesC_scal_r].
        intros a'. split.
        * by apply Rmult_le_pos.
        * apply Rmult_le_compat_l; [done|]. eapply pmf_le_1.
  Qed.

  Lemma dmap_dret_pmf (f : A → B) (a : A) (b : B) :
    dmap f (dret a) b = dret (f a) b.
  Proof. rewrite /dmap dret_id_left_pmf //. Qed.

  Lemma dmap_dret (f : A → B) a :
    dmap f (dret a) = dret (f a) .
  Proof. apply distr_ext, dmap_dret_pmf. Qed.

  Lemma dbind_dzero_pmf (f : A → distr B) b :
    (a ← dzero; f a) b = 0.
  Proof.
    rewrite /= /dbind_pmf.
    rewrite /= /dzero.
    apply SeriesC_0.
    intros.
    rewrite Rmult_0_l; auto.
  Qed.

  Lemma dbind_dzero (f : A → distr B) :
    (a ← dzero; f a) = dzero.
  Proof. apply distr_ext, dbind_dzero_pmf. Qed.

  Lemma dmap_mass (μ : distr A) (f : A → B):
    SeriesC μ = SeriesC (dmap f μ).
  Proof.
    rewrite /= /dmap /= /dbind_pmf.
    rewrite <- (SeriesC_double_swap (λ '(a , b), (μ a * dret (f a) b) )).
    apply SeriesC_ext.
    intro n.
    rewrite /= /dret /dret_pmf.
    rewrite SeriesC_scal_l.
    rewrite SeriesC_singleton.
    lra.
  Qed.



  Lemma dzero_ext (μ : distr A) :
    (forall a, μ a = 0) -> μ = dzero.
  Proof.
    intro Hμ.
    apply distr_ext; auto.
  Qed.


  Lemma SeriesC_zero_dzero (μ : distr A) :
    SeriesC μ = 0 -> μ = dzero.
  Proof.
    intro Hμ.
    apply dzero_ext.
    apply SeriesC_const0; auto.
    pose proof (pmf_ex_seriesC μ).
    apply SeriesC_correct'; auto.
  Qed.


  Lemma dmap_dzero (f : A → B):
    (dmap f dzero) = dzero.
  Proof.
    apply dbind_dzero.
  Qed.

(*  Lemma dmap_dzero (f : A → B):
    dmap f dzero = dzero.
  Proof.
    apply dbind_dzero.
  Qed.

  Lemma dmap_dzero_inv (f : A → B) (μ : distr A) :
    dmap f μ = dzero -> μ = dzero.
  Proof.
    rewrite /= /dmap.
    intro Hμ.
    assert (forall b, (μ ≫= (λ a : A, dret (f a))) b = 0) as Hμ'.
    {
      intro b.
      rewrite Hμ.
      auto.
    }
    rewrite /= /dbind_pmf in Hμ'.
    apply distr_ext.
    rewrite /= /dzero.
    intro a.
    specialize (Hμ' (f a)).
    rewrite <- Hμ'.
    rewrite /= /dret_pmf.
    assert (SeriesC (λ a0 : A, μ a0 * (if bool_decide (f a = f a0) then 1 else 0))
           = SeriesC (λ a0 : A, (if bool_decide (f a0 = f a) then μ a0 else 0))) as Heq.
    { apply SeriesC_ext.
      intro n.
      assert (bool_decide (f n = f a) = bool_decide (f a = f n)) as Haux; try (apply bool_decide_ext; split; auto).
      rewrite Haux.
      destruct (bool_decide (f a = f n)); try lra.
    }
    rewrite Heq.
    apply SeriesC_singleton.
*)




End monadic_theory.

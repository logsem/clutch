From Coq Require Import Reals Psatz.
From Coquelicot Require Import Series Hierarchy Lim_seq Rbar Lub.
From stdpp Require Import option.
From stdpp Require Export countable finite gmap.
From clutch.prelude Require Import base Reals_ext Coquelicot_ext Series_ext stdpp_ext classical fin.
Set Default Proof Using "Type*".
Import Hierarchy.

Open Scope R.

(** A theory of (in)finite series over countable types.  *)
Section countable_sum.
  Context `{Countable A}.

  Implicit Types f g : A → R.

  (** 'Traverses' the type in the order given by decoding [0, 1, 2, ...] *)
  Definition countable_sum (f : A → R) :=
    λ (n : nat), from_option f 0 (encode_inv_nat n).

  Lemma countable_sum_0 f m :
    (∀ n, f n = 0) → countable_sum f m = 0.
  Proof. intros. rewrite /countable_sum. destruct (encode_inv_nat _); eauto. Qed.

  Lemma countable_sum_ge_0 f m :
    (∀ n, 0 <= f n) → 0 <= countable_sum f m.
  Proof. intros. rewrite /countable_sum. destruct (encode_inv_nat _)=>//=. Qed.

  Lemma countable_sum_ext f g m :
    (∀ n, f n = g n) → countable_sum f m = countable_sum g m.
  Proof. intros ?. rewrite /countable_sum. destruct (encode_inv_nat _) => //=. Qed.

  Lemma countable_sum_le f g m :
    (∀ n, f n <= g n) → countable_sum f m <= countable_sum g m.
  Proof. intros ?. rewrite /countable_sum. destruct (encode_inv_nat _) =>//=. Qed.

  Lemma countable_sum_scal c f n :
    countable_sum (λ x, scal c (f x)) n = scal c (countable_sum f n).
  Proof.
    intros. rewrite //= /countable_sum /scal //= /mult //=.
    destruct (encode_inv_nat _) => //=; lra.
  Qed.

  Lemma countable_sum_plus f g n :
    countable_sum (λ x, f x + g x) n = countable_sum f n + countable_sum g n.
  Proof.
    intros. rewrite //=/countable_sum; destruct (encode_inv_nat) => //=. lra.
  Qed.

  Lemma countable_sum_minus f g n :
    countable_sum (λ x, f x - g x) n = countable_sum f n - countable_sum g n.
  Proof.
    intros. rewrite //=/countable_sum; destruct (encode_inv_nat) => //=. lra.
  Qed.

  Lemma countable_sum_mult f g n :
    countable_sum (λ x, f x * g x) n = countable_sum f n * countable_sum g n.
  Proof.
    intros. rewrite //=/countable_sum; destruct (encode_inv_nat) => //=. lra.
  Qed.

  Lemma countable_sum_Rabs f n :
    countable_sum (λ x, Rabs (f x)) n = Rabs (countable_sum f n).
  Proof.
    intros. rewrite //=/countable_sum; destruct (encode_inv_nat _) => //=. rewrite Rabs_R0 //=.
  Qed.

  Lemma countable_sum_scal_l f c n :
    countable_sum (λ x, c * f x) n = c * countable_sum f n.
  Proof. apply countable_sum_scal. Qed.

  Lemma countable_sum_scal_r f c n :
    countable_sum (λ x, f x * c) n = countable_sum f n * c.
  Proof.
    intros. rewrite //=/countable_sum; destruct (encode_inv_nat) => //=. lra. Qed.

  Global Instance countable_sum_Proper:
    Proper (pointwise_relation A (@eq R) ==> pointwise_relation nat (@eq R)) countable_sum.
  Proof. intros ?? ? x. rewrite /countable_sum. destruct (encode_inv_nat _); eauto. Qed.

  Global Instance countable_sum_Proper' :
    Proper (pointwise_relation A (@eq R) ==> eq ==> eq) countable_sum.
  Proof. intros ?? ? ? ??. subst. eapply countable_sum_ext; eauto. Qed.

  (** TODO: more lifted lemmas on [sumC] *)
  Definition sumC_n (f : A → R) := sum_n (countable_sum f).

End countable_sum.

Section series.
  Context `{Countable A}.

  Implicit Types f g : A → R.

  (** Lifting of the Coquliecot predicates for working with series *)
  Definition is_seriesC f := is_series (countable_sum f).
  Definition ex_seriesC f := ∃ a, is_seriesC f a.
  Definition SeriesC f := Series (countable_sum f).

  Lemma is_seriesC_0 f :
    (∀ n, f n = 0) → is_seriesC f 0.
  Proof.
    intros ?. apply is_series_0=> n.
    rewrite /countable_sum. destruct (encode_inv_nat _)=>/=; auto.
  Qed.

  Lemma is_seriesC_ext f g l :
    (∀ n, f n = g n) → is_seriesC g l → is_seriesC f l.
  Proof.
    intros ?. apply is_series_ext=> n. by apply countable_sum_ext.
  Qed.

  Lemma is_seriesC_unique f l :
    is_seriesC f l → SeriesC f = l.
  Proof.
    apply is_series_unique.
  Qed.

  Lemma ex_seriesC_ex_series f :
     ex_series (countable_sum f) → ex_seriesC f .
  Proof.
    intros; auto.
  Qed.

  Lemma ex_seriesC_ex_series_inv f :
     ex_seriesC f → ex_series (countable_sum f).
  Proof.
    intros; auto.
  Qed.

  Lemma ex_seriesC_ext f g :
    (∀ n, f n = g n) → ex_seriesC f → ex_seriesC g.
  Proof.
    intros ?. apply ex_series_ext=> n. by apply countable_sum_ext.
  Qed.

  Lemma is_seriesC_chain f g v : is_seriesC g (SeriesC f) → is_seriesC f v → is_seriesC g v.
  Proof.
    intros Hs2 Hs1. apply is_seriesC_unique in Hs1. rewrite -Hs1. done.
  Qed.

  Lemma SeriesC_correct f :
    ex_seriesC f → is_seriesC f (SeriesC f).
  Proof. apply Series_correct. Qed.

  Lemma SeriesC_correct' a v:
    SeriesC a = v → ex_seriesC a → is_seriesC a v.
  Proof. by intros <- ?; apply SeriesC_correct. Qed.

  Lemma SeriesC_0 f :
    (∀ x, f x = 0) → SeriesC f = 0.
  Proof. intros Heq0. apply Series_0=> ?. by apply countable_sum_0. Qed.

  Lemma SeriesC_ge_0 (f : A → R) :
    (∀ x, 0 <= f x) →
    ex_seriesC f →
    0 <= SeriesC f.
  Proof.
    intros Heq0 Hex.
    rewrite -(SeriesC_0 (λ _ : A, 0)); [|done].
    apply Series_le; [|done].
    intros n. split.
    + apply countable_sum_ge_0. intros ?; lra.
    + by apply countable_sum_le.
  Qed.

  Lemma SeriesC_ge_0' (f : A → R) :
    (∀ x, 0 <= f x) →
    0 <= SeriesC f.
  Proof.
    intros Heq0.
    apply series_ge_0=> ?.
    apply countable_sum_ge_0; intros; auto.
  Qed.

  Lemma SeriesC_ext f g :
    (∀ n, f n = g n) → SeriesC f = SeriesC g.
  Proof. intros Hext. apply Series_ext => // n. by apply countable_sum_ext. Qed.

  Lemma SeriesC_le f g :
    (∀ n, 0 <= f n <= g n) →
    ex_seriesC g →
    SeriesC f <= SeriesC g.
  Proof.
    intros Hrange Hex. apply Series_le => // n.
    rewrite /countable_sum.
    destruct (encode_inv_nat _) => //=; lra.
  Qed.

  Lemma SeriesC_le' f g :
    (∀ n, f n <= g n) →
    ex_seriesC f →
    ex_seriesC g →
    SeriesC f <= SeriesC g.
  Proof.
    intros ???. apply Series_le' => //= n.
    rewrite /countable_sum.
    destruct (encode_inv_nat _) => //=.
  Qed.





  Lemma SeriesC_scal_l f c :
    SeriesC (λ x, c * f x) = c * SeriesC f.
  Proof.
    intros. rewrite -Series_scal_l. apply Series_ext. apply countable_sum_scal_l.
  Qed.

  Lemma SeriesC_scal_r f c :
    SeriesC (λ x, f x * c) = SeriesC f * c.
  Proof.
    intros. rewrite -Series_scal_r. apply Series_ext. apply countable_sum_scal_r.
  Qed.

  Lemma SeriesC_plus f g :
    ex_seriesC f →
    ex_seriesC g →
    SeriesC (λ x, f x + g x) = SeriesC f + SeriesC g.
  Proof.
    intros. rewrite -Series_plus //. apply Series_ext. apply countable_sum_plus.
  Qed.

  Lemma SeriesC_minus f g :
    ex_seriesC f →
    ex_seriesC g →
    SeriesC (λ x, f x - g x) = SeriesC f - SeriesC g.
  Proof.
    intros. rewrite -Series_minus //. apply Series_ext. apply countable_sum_minus.
  Qed.

  Lemma ex_seriesC_0 :
    ex_seriesC (λ _, 0).
  Proof.
    eexists; by eapply is_seriesC_0.
  Qed.

  Lemma ex_seriesC_le f g :
    (∀ n, 0 <= f n <= g n) →
    ex_seriesC g →
    ex_seriesC f.
  Proof.
    intros Hle Hex.
    eapply @ex_series_le; [|eauto].
    intros n. rewrite /norm//=/abs//=.
    rewrite -countable_sum_Rabs. apply countable_sum_le.
    intros x. destruct (Hle x); eauto. rewrite Rabs_right; eauto; lra.
  Qed.

  Lemma ex_seriesC_scal_l f c :
    ex_seriesC f →
    ex_seriesC (λ x, c * f x).
  Proof.
    intros. eapply ex_series_ext.
    { intros n. rewrite countable_sum_scal_l. done. }
    by eapply @ex_series_scal_l.
  Qed.

  Lemma ex_seriesC_scal_r f c :
    ex_seriesC f →
    ex_seriesC (λ x, f x * c).
  Proof.
    intros. eapply ex_series_ext.
    { intros n. rewrite countable_sum_scal_r. done. }
    apply: ex_series_scal_r; eauto.
  Qed.

  Lemma ex_seriesC_plus f g :
    ex_seriesC f →
    ex_seriesC g →
    ex_seriesC (λ x, f x + g x).
  Proof.
    intros. eapply ex_series_ext.
    { intros n. rewrite countable_sum_plus. done. }
    apply: ex_series_plus; eauto.
  Qed.

  Lemma is_seriesC_scal_l f c v :
    is_seriesC f v →
    is_seriesC (λ x, c * f x) (c * v).
  Proof.
    intros. eapply is_series_ext.
    { intros n. rewrite countable_sum_scal_l. done. }
    apply: is_series_scal_l; eauto.
  Qed.

  Lemma is_seriesC_scal_r f c v:
    is_seriesC f v →
    is_seriesC (λ x, f x * c) (v * c).
  Proof.
    intros. eapply is_series_ext.
    { intros n. rewrite countable_sum_scal_r. done. }
    apply: is_series_scal_r; eauto.
  Qed.

  Lemma is_seriesC_plus f g v1 v2:
    is_seriesC f v1 →
    is_seriesC g v2 →
    is_seriesC (λ x, f x + g x) (v1 + v2).
  Proof.
    intros. eapply is_series_ext.
    { intros n. rewrite countable_sum_plus. done. }
    apply: is_series_plus; eauto.
  Qed.

  Lemma ex_seriesC_Rabs f :
    ex_seriesC (λ x, Rabs (f x)) →
    ex_seriesC f.
  Proof.
    intros. eapply ex_series_Rabs.
    eapply ex_series_ext.
    { intros n. rewrite -countable_sum_Rabs. done. }
    eauto.
  Qed.


  Global Instance is_series_Proper:
    Proper (pointwise_relation A (@eq R) ==> @eq R ==> iff) is_seriesC.
  Proof. intros ?? ? ?? ?; subst; split; eapply is_seriesC_ext; eauto. Qed.

  Global Instance ex_series_Proper:
    Proper (pointwise_relation A (@eq R) ==> iff) ex_seriesC.
  Proof. intros ?? ?; split; eapply ex_seriesC_ext; eauto. Qed.

  Global Instance Series_Proper:
    Proper (pointwise_relation A (@eq R) ==> eq) SeriesC.
  Proof. intros ?? ?; eapply SeriesC_ext; eauto. Qed.

End series.

Section series_nat.

  Lemma encode_inv_nat_nat (n : nat) :
    (encode_inv_nat n) = Some n.
  Proof.
    rewrite /encode_inv_nat/decode_nat/decode/nat_countable/decode/N_countable.
    destruct n eqn:Hn; simpl; auto.
    rewrite decide_False //=; [ | lia].
    rewrite Nat2Pos.inj_succ //
              positive_N_nat
              Pos.pred_succ
              Nat2Pos.id //
              option_guard_True //
              /encode_nat/encode/=.
      lia.
  Qed.


  Lemma ex_seriesC_nat (f : nat -> R) :
    ex_series f <-> ex_seriesC f.
  Proof.
    split; intro Hex.
    - apply (ex_series_ext f); auto.
      intros. rewrite /countable_sum.
      rewrite encode_inv_nat_nat //.
    - destruct Hex as [r Hr].
      exists r.
      rewrite /is_seriesC/countable_sum in Hr.
      setoid_rewrite encode_inv_nat_nat in Hr.
      auto.
  Qed.

  Lemma SeriesC_nat (f : nat -> R) :
    SeriesC f = Series f.
  Proof.
    rewrite /SeriesC/Series/countable_sum.
    f_equal.
    apply Lim_seq_ext.
    intro n.
    apply sum_n_ext.
    intro; rewrite encode_inv_nat_nat; auto.
  Qed.

End series_nat.

Section filter.
  Context `{Countable A, Countable B}.

  Implicit Types P Q : A → Prop.

  Lemma is_seriesC_singleton_dependent (a : A) v :
    is_seriesC (λ (n : A), if bool_decide (n = a) then v n else 0) (v a).
  Proof.
    rewrite /is_seriesC.
    eapply is_series_ext; [|apply (is_series_singleton (encode_nat a))].
    intros n =>/=. rewrite /countable_sum.
    case_bool_decide as Hneq=>/=; subst.
    - rewrite encode_inv_encode_nat //= bool_decide_eq_true_2 //.
    - destruct (encode_inv_nat _) eqn:Heq=>//=.
      case_bool_decide; [|done]; subst.
      exfalso. apply Hneq. symmetry. by apply encode_inv_Some_nat.
  Qed.

  Lemma is_seriesC_singleton (a : A) v :
    is_seriesC (λ (n : A), if bool_decide (n = a) then v else 0) v.
  Proof. apply is_seriesC_singleton_dependent. Qed.

  Lemma ex_seriesC_singleton_dependent (a : A) v :
    ex_seriesC (λ (n : A), if bool_decide (n = a) then v n else 0).
  Proof. eexists. eapply is_seriesC_singleton_dependent. Qed.

  Lemma ex_seriesC_singleton (a : A) v :
    ex_seriesC (λ (n : A), if bool_decide (n = a) then v else 0).
  Proof. eexists. eapply is_seriesC_singleton. Qed.

  Lemma SeriesC_singleton_dependent (a : A) v :
    SeriesC (λ n, if bool_decide (n = a) then v n else 0) = v a.
  Proof. apply is_series_unique, is_seriesC_singleton_dependent. Qed.

  Lemma SeriesC_singleton (a : A) v :
    SeriesC (λ n, if bool_decide (n = a) then v else 0) = v.
  Proof. apply is_series_unique, is_seriesC_singleton. Qed.

  Lemma SeriesC_subset g f {_:∀ a, Decision (g a)}:
    (∀ (a:A), (¬ g a) -> f a = 0)-> 
    SeriesC f = SeriesC (λ a, if bool_decide (g a) then f a else 0).
  Proof.
    intros H1.
    apply SeriesC_ext.
    intros. case_bool_decide; first done.
    naive_solver.
  Qed.

  Lemma is_seriesC_singleton_inj (b : B) (f : A → B) v `{Inj A B (=) (=) f} :
    (∃ a, f a = b) →
    is_seriesC (λ (a : A), if bool_decide (f a = b) then v else 0) v.
  Proof.
    intros (a & Ha).
    rewrite /is_seriesC.
    eapply is_series_ext; [|apply (is_series_singleton (encode_nat a))].
    intros n =>/=. rewrite /countable_sum.
    case_bool_decide as Hneq=>/=; subst.
    - rewrite (encode_inv_encode_nat a) //= bool_decide_eq_true_2 //.
    - destruct (encode_inv_nat _) eqn:Heq=>//=.
      case_bool_decide; [|done]; subst.
      exfalso.
      specialize (H1 a0 a H2); simplify_eq.
      apply Hneq. symmetry. by apply encode_inv_Some_nat.
  Qed.

  Lemma ex_seriesC_singleton_inj (b : B) (f : A → B) v `{Inj A B (=) (=) f} :
    (∃ a, f a = b) →
    ex_seriesC (λ (a : A), if bool_decide (f a = b) then v else 0).
  Proof.
    eexists. apply is_seriesC_singleton_inj; auto.
  Qed.

  Lemma SeriesC_singleton_inj (b : B) (f : A → B) v `{Inj A B (=) (=) f} :
    (∃ a, f a = b) →
    SeriesC (λ (a : A), if bool_decide (f a = b) then v else 0) = v.
  Proof.
    intros. apply is_seriesC_unique, is_seriesC_singleton_inj; auto.
  Qed.

  Lemma SeriesC_ge_elem  (f : A → R) (a : A) :
    (∀ x, 0 <= f x) →
    ex_seriesC f →
    f a <= SeriesC f.
  Proof.
    intros Hf Hex.
    rewrite -(SeriesC_singleton a (f a)).
    apply SeriesC_le; [|done].
    intros a'. specialize (Hf a').
    case_bool_decide; simplify_eq; lra.
  Qed.

  Lemma ex_seriesC_singleton' (a : A) v :
    ex_seriesC (λ (n : A), if bool_decide (a = n) then v else 0).
  Proof.
    apply (ex_seriesC_ext (λ n : A, if bool_decide (n = a) then v else 0)
             (λ n : A, if bool_decide (a = n) then v else 0)).
    + intro a'; rewrite (bool_decide_ext (a = a') (a' = a)); done.
    + apply ex_seriesC_singleton.
  Qed.

  Lemma SeriesC_singleton' (a : A) v :
    SeriesC (λ n, if bool_decide (a = n) then v else 0) = v.
  Proof.
    rewrite (SeriesC_ext (λ n : A, if bool_decide (a = n) then v else 0)
               (λ n : A, if bool_decide (n = a) then v else 0)).
    + apply SeriesC_singleton.
    + intro a'; rewrite (bool_decide_ext (a = a') (a' = a)); done.
  Qed.

  Lemma ex_seriesC_list (l : list A) (f : A -> R):
    ex_seriesC (λ (a : A), if bool_decide(a ∈ l) then f a else 0).
  Proof.
    induction l.
    { eapply ex_seriesC_ext; last apply ex_seriesC_0.
      intros; done.
    }
    destruct (decide(a ∈ l)).
    { eapply ex_seriesC_ext; last done.
      intros.
      simpl.
      erewrite bool_decide_ext; first done.
      set_solver.
    }
    eapply ex_seriesC_ext; last apply ex_seriesC_plus.
    2:{ apply IHl. }
    2:{ eapply (ex_seriesC_singleton _ (f a)). }
    intros x.
    simpl.
    repeat case_bool_decide; try set_solver.
    all: try (by subst).
    all: try lra.
    - subst. apply Rplus_0_l.
    - subst. set_solver.
  Qed.

  Lemma SeriesC_list (l:list A) f:
    NoDup l -> SeriesC (λ (a : A), if bool_decide(a ∈ l) then f a else 0) =
    foldr (Rplus ∘ f) 0%R l.
  Proof.
    induction l as [|a l IHl].
    - intros. simpl. apply SeriesC_0; naive_solver.
    - intro Hnd. simpl. rewrite -IHl; last first.
      { inversion Hnd. done. }
      erewrite <-(SeriesC_singleton_dependent _ ) at 1.
      erewrite <-SeriesC_plus; last first.
      { apply ex_seriesC_list. } 
      { apply ex_seriesC_singleton_dependent. }
      apply SeriesC_ext.
      intros.
      rewrite NoDup_cons in Hnd.
      destruct Hnd as [H1 H2].
      repeat case_bool_decide; try lra; set_solver.
    Qed.
  
  
  Lemma SeriesC_list_1 (l:list A):
    NoDup l -> SeriesC (λ (a : A), if bool_decide(a ∈ l) then 1 else 0) = length l.
  Proof.
    intros.
    rewrite SeriesC_list; last done.
    clear.
    induction l; first (simpl;lra).
    simpl. rewrite -/(INR (S _)). rewrite S_INR.
    rewrite IHl. lra.
  Qed.

  Lemma SeriesC_list_2 (l:list A) r:
    NoDup l -> SeriesC (λ (a : A), if bool_decide(a ∈ l) then r else 0) = r * length l.
  Proof.
    intros.
    rewrite SeriesC_list; last done.
    clear.
    induction l; first (simpl;lra).
    simpl. rewrite -/(INR (S _)). rewrite S_INR.
    rewrite IHl. lra.
  Qed. 
    

  Lemma ex_seriesC_finite_from_option (l : list A) (f : B -> R) (g : A -> option B):
    (∀ a : A, is_Some (g a) <-> a ∈ l) ->
    ex_seriesC (λ (a : A), from_option f 0%R (g a)).
  Proof.
    intros Hl.
    eapply ex_seriesC_ext; last apply (ex_seriesC_list l).
    intros a.
    simpl.
    case_bool_decide as H1; first done.
    destruct (g a) eqn:K.
    { exfalso. apply H1. apply Hl. done. }
    done.
  Qed.

  Lemma is_seriesC_filter_pos f v P `{∀ x, Decision (P x)} :
    (∀ n, 0 <= f n) →
    is_seriesC f v →
    ex_seriesC (λ n, if bool_decide (P n) then f n else 0).
  Proof.
    intros Hge Hconv.
    apply: ex_seriesC_le; last by (exists v; eauto).
    intros n. rewrite /norm /= /abs.
    specialize (Hge n). case_bool_decide; lra.
  Qed.

  Lemma is_seriesC_filter_impl f v P Q `{∀ x, Decision (P x), ∀ x, Decision (Q x)} :
    (∀ n, 0 <= f n) →
    is_seriesC (λ n, if bool_decide (P n) then f n else 0) v →
    (∀ n, Q n → P n) →
    ex_seriesC (λ n, if bool_decide (Q n) then f n else 0).
  Proof.
    intros Hge Hconv Himp. apply ex_seriesC_Rabs.
    apply: ex_seriesC_le; last by (exists v; eauto).
    intros n. rewrite /norm//=/abs//=.
    specialize (Hge n). specialize (Himp n).
    do 2 case_bool_decide; try (rewrite Rabs_right; auto; lra).
    tauto.
  Qed.

  Lemma ex_seriesC_filter_impl f P Q `{∀ x, Decision (P x), ∀ x, Decision (Q x)} :
    (∀ n, 0 <= f n) →
    ex_seriesC (λ n, if bool_decide (P n) then f n else 0) →
    (∀ n, Q n → P n) →
    ex_seriesC (λ n, if bool_decide (Q n) then f n else 0).
  Proof. intros ? [? ?] ?. eapply is_seriesC_filter_impl; eauto. Qed.

  Lemma ex_seriesC_filter_pos f P `{∀ x, Decision (P x)} :
    (∀ n, 0 <= f n) →
    ex_seriesC f →
    ex_seriesC (λ n, if bool_decide (P n) then f n else 0).
  Proof. intros ? [v His]. by eapply is_seriesC_filter_pos. Qed.


  Lemma SeriesC_filter_leq f P `{∀ x, Decision (P x)} :
    (∀ n, 0 <= f n) →
    ex_seriesC f →
    SeriesC (λ n, if bool_decide (P n) then f n else 0) <= SeriesC f.
  Proof. intros ? ?.
         apply SeriesC_le; auto.
         intro n; case_bool_decide; simpl; split; auto; lra.
  Qed.

  (* TODO: make a [SeriesC_minus] lemma and cleanup proof *)
  Lemma is_seriesC_filter_union f v P Q `{∀ x, Decision (P x), ∀ x, Decision (Q x)} :
    (∀ n, 0 <= f n) →
    is_seriesC (λ n, if bool_decide (P n ∨ Q n) then f n else 0) v →
    SeriesC (λ n, if bool_decide (P n) then f n else 0) +
      SeriesC (λ n, if bool_decide (Q n) then f n else 0) -
      SeriesC (λ n, if bool_decide (P n ∧ Q n) then f n else 0) = v.
  Proof.
    intros Hge Hexists.
    rewrite -SeriesC_plus; last first.
    {apply (is_seriesC_filter_impl  _ _ _ _ Hge Hexists); eauto. }
    { apply (is_seriesC_filter_impl  _ _ _ _ Hge Hexists); eauto. }
    rewrite -SeriesC_minus.
    - rewrite -(is_seriesC_unique _ v Hexists).
      apply SeriesC_ext => n.
      do 2 repeat case_bool_decide=>//=; try tauto; lra.
    - apply: (ex_seriesC_le _ (λ a, scal 2 (if bool_decide (P a ∨ Q a) then f a else 0))).
      + intros a. rewrite /scal /= /mult /=.
        specialize (Hge a). do 3 case_bool_decide => /=; try (lra || tauto).
      + eexists. by eapply is_seriesC_scal_l.
    - eapply (is_seriesC_filter_impl  _ _ _ _ Hge Hexists). intros ? []; auto.
  Qed.

  Lemma ex_seriesC_split_elem f (a0 : A) :
    ex_seriesC (λ a, if bool_decide (a ≠ a0) then f a else 0) → ex_seriesC f.
  Proof.
    intros Ha0.
    eapply (ex_seriesC_ext (λ a, (λ a, if bool_decide (a = a0) then f a else 0) a +
                                   (λ a, if bool_decide (a ≠ a0) then f a else 0) a)).
    { intros a. case_bool_decide; simplify_eq.
      - rewrite bool_decide_eq_false_2; [lra|auto].
      - rewrite bool_decide_eq_true_2 //. lra. }
    eapply ex_seriesC_plus; [|done].
    eapply ex_seriesC_ext; [|eapply (ex_seriesC_singleton a0 (f a0))].
    intros a. simpl. by case_bool_decide; simplify_eq.
  Qed.

  Lemma SeriesC_split_elem f (a0 : A) :
    (∀ a, 0 <= f a) →           (* TODO: this requirements should not be necessary? *)
    ex_seriesC f →
    SeriesC f = SeriesC (λ a, if bool_decide (a = a0) then f a else 0) +
                  SeriesC (λ a, if bool_decide (a ≠ a0) then f a else 0).
  Proof.
    intros Hle Hex.
    erewrite SeriesC_ext.
    { eapply SeriesC_plus; [by eapply ex_seriesC_filter_pos|].
      eapply (ex_seriesC_le _ f); [|done].
      intros a'. case_bool_decide; split; (done || lra). }
    intros a. simpl. case_bool_decide as Heq.
    - rewrite bool_decide_eq_false_2; [lra|]. eauto.
    - rewrite bool_decide_eq_true_2 //. lra.
  Qed.


  Lemma SeriesC_split_pred f (P : A -> bool) :
    (∀ a, 0 <= f a) →
    ex_seriesC f →
    SeriesC f = SeriesC (λ a, if P a then f a else 0) +
                  SeriesC (λ a, if P a then 0 else f a).
  Proof.
    intros Hle Hex.
    rewrite -SeriesC_plus.
    - apply SeriesC_ext; intro.
      destruct (P _); lra.
    - apply (ex_seriesC_le _ f); auto.
      intro; real_solver.
    - apply (ex_seriesC_le _ f); auto.
      intro; real_solver.
  Qed.

  Lemma ex_seriesC_filter_bool_pos f (P : A → bool) :
    (∀ a, 0 <= f a) →
    ex_seriesC f →
    ex_seriesC (λ a, if P a then f a else 0).
  Proof.
    intros Hpos Hex.
    apply (ex_seriesC_le _ f); auto.
    intro n; specialize (Hpos n); destruct (P n); lra.
  Qed.

  Lemma SeriesC_pos (f : A → R) a :
    (∀ a, 0 <= f a) →
    ex_seriesC f →
    f a > 0 →
    SeriesC f > 0.
  Proof.
    intros Hpos Hex Ha.
    rewrite (SeriesC_split_elem _ a); [|done|done].
    rewrite SeriesC_singleton_dependent.
    assert (0 <= SeriesC (λ a', if bool_decide (a' ≠ a) then f a' else 0)); [|lra].
    eapply SeriesC_ge_0' => a'.
    by case_bool_decide.
  Qed.

End filter.

Lemma SeriesC_Series_nat (f : nat → R)  :
  SeriesC f = Series f.
Proof.
  rewrite /SeriesC.
  erewrite Series_ext; [done|].
  rewrite /countable_sum /from_option /= => n.
  case_match eqn:He.
  - by apply encode_inv_nat_Some_inj in He as ->.
  - by apply encode_inv_nat_None in He.
Qed.

Lemma is_seriesC_is_series_nat (f : nat → R) v :
  is_series f v → is_seriesC f v.
Proof.
  intros Hf.
  eapply is_series_ext; [|done]=> n.
  rewrite /is_seriesC /countable_sum /from_option /=.
  case_match eqn:He.
  - by apply encode_inv_nat_Some_inj in He as ->.
  - by apply encode_inv_nat_None in He.
Qed.

Lemma SeriesC_bool (f : bool → R) :
  SeriesC f = f true + f false.
Proof.
  rewrite (SeriesC_ext _ (λ b, (if bool_decide (b = true) then f true else 0) +
                                if bool_decide (b = false) then f false else 0)).
  { rewrite SeriesC_plus; [|eapply ex_seriesC_singleton..].
    rewrite 2!SeriesC_singleton //. }
  intros []; simpl; lra.
Qed.

Lemma SeriesC_fin2 (f : fin 2 → R) :
  SeriesC f = f 0%fin + f 1%fin.
Proof.
  rewrite (SeriesC_ext _ (λ b, (if bool_decide (b = 0%fin) then f 0%fin else 0) +
                                 if bool_decide (b = 1%fin) then f 1%fin else 0)).
  { rewrite SeriesC_plus; [|eapply ex_seriesC_singleton..].
    rewrite 2!SeriesC_singleton //. }
  intros n; inv_fin n; [simpl; lra|].
  intros n; inv_fin n; [simpl; lra|].
  intros n; inv_fin n.
Qed.

Lemma ex_seriesC_nat_bounded (f : nat -> R) (N : nat) :
  ex_seriesC (λ (n : nat), if bool_decide ((n <= N)%nat) then f n else 0).
Proof.
  induction N.
  - apply (ex_seriesC_ext (λ n : nat, if bool_decide (n = 0%nat) then f 0%nat else 0)); [ | apply ex_seriesC_singleton ].
    intro; do 2 case_bool_decide; simplify_eq; try lia; try lra.
  - eapply (ex_seriesC_ext); last first.
    + apply ex_seriesC_plus; [ apply IHN | ].
      apply (ex_seriesC_singleton (S N) (f (S N))).
    + intros; do 3 case_bool_decide; simplify_eq; try lia; try lra.
Qed.

Lemma ex_seriesC_nat_bounded_Rle (f : nat -> R) (N : nat) :
  ex_seriesC (λ (n : nat), if bool_decide (n <= N) then f n else 0).
Proof.
  eapply ex_seriesC_ext; [ | apply (ex_seriesC_nat_bounded f N)].
  intro.
  case_bool_decide.
  - rewrite bool_decide_eq_true_2; auto.
    by apply INR_le.
  - rewrite bool_decide_eq_false_2; auto.
    apply Nat.lt_nge.
    apply INR_lt.
    lra.
Qed.




Lemma SeriesC_nat_bounded (f : nat -> R) (N : nat) :
  SeriesC (λ (n : nat), if bool_decide ((n <= N)%nat) then f n else 0) = sum_n f N.
Proof.
  induction N.
  - rewrite sum_O.
    rewrite (SeriesC_ext _ (λ n : nat, if bool_decide (n = 0%nat) then f 0%nat else 0)).
    {
      apply SeriesC_singleton.
    }
    intros n.
    pose proof (pos_INR n).
    case_bool_decide as H2; case_bool_decide as H3;
      simplify_eq; auto.
    + inversion H2; done.
    + destruct H2; auto.
  - rewrite sum_Sn //.
    rewrite -IHN.
    rewrite -(SeriesC_singleton (S N) (f (S N))).
    rewrite /plus/=.
    rewrite -SeriesC_plus.
    + apply SeriesC_ext.
      intro.
      do 3 case_bool_decide; simplify_eq; try lia; try lra.
    + apply ex_seriesC_nat_bounded.
    + apply ex_seriesC_singleton.
Qed.


Section strict.
  Context `{Countable A}.

  Implicit Types f g : A → R.

  Lemma SeriesC_lt f g :
    (∀ n, 0 <= f n <= g n) →
    (∃ m, f m < g m) →
    ex_seriesC g →
    SeriesC f < SeriesC g.
  Proof.
    intros Hle Hlt Hg.
    assert (ex_seriesC f) as Hf.
    { apply (ex_seriesC_le f g); auto. }
    destruct Hlt as (m & Hlt).
    assert (g m - f m > 0) as Hgtz ; try lra.
    set (d := g m - f m).
    set (h := (λ n, if bool_decide (n = m) then d else 0) ).
    assert (ex_seriesC h) as Hh.
    { apply ex_seriesC_singleton. }
    assert (SeriesC h > 0) as Hhgt.
    { rewrite SeriesC_singleton; auto. }
    assert (SeriesC f + SeriesC h <= SeriesC g); try lra.
    rewrite <- SeriesC_plus; auto.
    apply SeriesC_le; auto.
    intro n.
    specialize (Hle n) as (Hle1 & Hle2).
    rewrite /h /d.
    case_bool_decide as Hnm; split; try lra.
    rewrite Hnm; lra.
  Qed.

  Lemma SeriesC_const0 f :
    (∀ n, 0 <= f n) →
    is_seriesC f 0 →
    (∀ n, f n = 0).
  Proof.
    intros Hf Hz n.
    pose proof (is_seriesC_unique _ _ Hz) as Hz'.
    pose proof (Rtotal_order (f n) 0) as Htri.
    destruct Htri as [H1 | [H2 | H3]] ; try lra.
    - specialize (Hf n); lra.
    - assert (0 < SeriesC f); try lra.
      assert (SeriesC (λ _ : A, 0) = 0) as H4.
      { apply SeriesC_0; auto. }
      destruct H4.
      eapply (SeriesC_lt (λ n, 0) f).
      + intro n0; specialize (Hf n0); lra.
      + exists n; lra.
      + exists 0; done.
  Qed.

  Lemma SeriesC_gtz_ex f :
    (∀ n, 0 <= f n) →
    SeriesC f > 0 →
    ∃ n, f n > 0.
  Proof.
    intro Hf.
    eapply contrapositive. intros Hna.
    assert (∀ a, f a = 0) as Hz.
    { intros a.
      pose proof (not_exists_forall_not _ _ Hna a).
      specialize (Hf a); lra. }
    apply Rge_not_gt. rewrite SeriesC_0 //.
  Qed.

End strict.

Section finite.
  Context `{Finite A}.

  Lemma ex_seriesC_finite (f : A → R) :
    ex_seriesC f.
  Proof.
    apply ex_series_eventually0.
    exists (card A).
    intros n Hn.
    rewrite /countable_sum /=.
    destruct (encode_inv_nat _) as [a|] eqn:Heq=>//=.
    pose proof (encode_lt_card a).
    rewrite /encode_inv_nat in Heq.
    destruct (decode_nat n); simplify_option_eq.
    lia.
  Qed.

  Lemma SeriesC_finite_foldr (f : A → R) :
    SeriesC f = foldr (Rplus ∘ f) 0%R (enum A).
  Proof.
    rewrite /SeriesC /countable_sum.
    setoid_rewrite encode_inv_nat_finite.
    generalize (enum A).
    induction l.
    { apply Series_0. eauto. }
    rewrite Series_incr_1.
    { rewrite IHl //. }
    eapply ex_series_ext;
      [|eapply ex_seriesC_nat, (ex_seriesC_nat_bounded _ (length l + 1))].
    intros n => /=.
    case_bool_decide; [done|].
    rewrite lookup_ge_None_2 //=. lia.
  Qed.

  Lemma SeriesC_finite_mass v :
    SeriesC (λ _ : A, v) = card A * v.
  Proof.
    rewrite /SeriesC.
    rewrite -(Series_ext (λ n, if bool_decide (n < card A)%nat then v else 0)); last first.
    { intros n. rewrite /countable_sum /=.
      case_bool_decide as Hn; simpl.
      - destruct (encode_inv_nat) eqn:Heq; [done|]; simpl.
        destruct (encode_inv_decode _ Hn) as (a & Hinv & He).
        simplify_option_eq.
      - destruct (encode_inv_nat) eqn:Heq; [|done]; simpl.
        rewrite encode_inv_decode_ge in Heq; [done|lia]. }
    apply (SeriesC_leq (card A) v).
  Qed.

  Lemma SeriesC_finite_bound (f : A → R) v :
    (∀ a, 0 <= f a <= v) →
    SeriesC f <= card A * v.
  Proof.
    intros Hf.
    rewrite -SeriesC_finite_mass.
    apply SeriesC_le ; [done|].
    apply ex_seriesC_finite.
  Qed.


End finite.


(* We might need the results below to reason about uniform distributions *)

  Definition extend_fin_to_R {n : nat} (f: fin n -> R) : (nat->R) :=
   fun x =>
     match le_lt_dec n x with
       | left _ => 0%R
       | right h => f (nat_to_fin h)
     end.

  Local Lemma foldr_ext_strong {A B} (f1 f2 : B → A → A) x1 l1 :
  (∀ b a, b∈ l1 -> f1 b a = f2 b a) → foldr f1 x1 l1 = foldr f2 x1 l1.
  Proof. revert x1.
         induction l1.
         - naive_solver.
         - intros. simpl. rewrite IHl1.
           + rewrite H; [done|set_solver].
           + intros. set_unfold. naive_solver.
  Qed.

  Lemma SeriesC_fin_sum {n : nat} (f : fin (S n) -> R) :
    SeriesC f = sum_n (extend_fin_to_R f) n.
  Proof.
    rewrite SeriesC_finite_foldr.
    rewrite <- seq_enum_fin.
    revert f. induction n.
    - naive_solver.
    - intros. rewrite sum_n_shift'. rewrite Rplus_comm.
      rewrite -cons_seq fmap_cons foldr_cons. 
      assert (forall x y, (Rplus ∘ f) x y = f x + y) as -> by naive_solver.
      f_equal. rewrite -fmap_S_seq -list_fmap_compose.
      replace (foldr (Rplus ∘ f) 0
    ((λ x : nat, match le_lt_dec (S (S n)) x with
                 | left _ => 0%fin
                 | right h => nat_to_fin h
               end) ∘ S <$> seq 0 (S n))) with 
        (foldr (Rplus ∘ (λ x, f (FS x))) 0
           ((λ x : nat, match le_lt_dec (S n) x with
                 | left _ => 0%fin
                 | right h => nat_to_fin h
                      end)  <$> seq 0 (S n))).
      + rewrite IHn.
        apply sum_n_ext_loc.
        clear.
        intros x Hx.
        rewrite /extend_fin_to_R.
        repeat case_match; try lia.
        f_equal. apply fin_to_nat_inj.
        simpl. by rewrite !fin_to_nat_to_fin.
      + clear.
        rewrite !foldr_fmap. apply foldr_ext_strong.
        intros b a. rewrite elem_of_seq.
        intros Hb. simpl. repeat case_match; try lia.
        * do 3 f_equal.
        * do 3 f_equal. apply fin_to_nat_inj. simpl. by rewrite !fin_to_nat_to_fin.
  Qed.

  Lemma SeriesC_nat_bounded_fin f N:
    SeriesC (λ n : nat, if bool_decide (n ≤ N) then f n else 0) =
    SeriesC (λ n:(fin (S N)), f (fin_to_nat n)).
  Proof.
    rewrite SeriesC_fin_sum.
    rewrite SeriesC_nat_bounded.
    apply sum_n_ext_loc.
    intros n ?.
    rewrite /extend_fin_to_R.
    case_match; first lia.
    by rewrite fin_to_nat_to_fin.
  Qed.

  
  Lemma SeriesC_nat_bounded' (f : nat -> R) (N : nat) :
    SeriesC (λ (n : nat), if bool_decide ((n <= N)%nat) then f n else 0) = foldr (Rplus ∘ f ∘ fin_to_nat) 0%R (enum (fin (S N))).
  Proof.
    rewrite SeriesC_nat_bounded_fin.
    by rewrite SeriesC_finite_foldr.
  Qed.

(** Results about positive (non-negative) series *)
Section positive.
  Context `{Countable A}.
  Implicit Types f g : A → R.

  Lemma limC_is_sup (h: A → R) r :
    (∀ n, 0 <= h n) →
    is_seriesC h r →
    is_sup_seq (sumC_n h) (Rbar.Finite r).
  Proof.
    intros Hge Hs.
    rewrite /is_seriesC in Hs.
    eapply (lim_is_sup (countable_sum h) r); auto.
    intro n. rewrite /countable_sum /from_option; edestruct (@encode_inv_nat A _ H n); auto ; lra.
  Qed.

  Lemma sup_is_limC (h: A → R) r :
    (∀ n, 0 <= h n) →
    is_sup_seq (sumC_n h) (Rbar.Finite r) →
    is_seriesC h r.
  Proof.
    intros Hge Hsup.
    rewrite /is_seriesC.
    eapply (sup_is_lim); auto.
    intro n; rewrite /countable_sum /from_option; destruct (encode_inv_nat _); auto; lra.
  Qed.

End positive.

Section bounds.
  Context `{Countable A}.

  Definition is_lubC (h: A → R) (u : Rbar) :=
    (∀ a, Rbar_le (h a) u) /\ (∀ u', (∀ a, Rbar_le (h a) u') → Rbar_le u u').

  Lemma ex_lubC (h : A → R) :
    {u | is_lubC h u}.
  Proof.
    destruct (Lub_Rbar_correct ((λ r : R, ∃ a0 : A, h a0 = r))) as [H1 H2].
    exists (Lub_Rbar (λ (r : R), exists a, h a = r)); split.
    - intro a.
      apply H1; eauto.
    - intros u' Hu'.
      apply H2; auto.
      rewrite /is_ub_Rbar.
      intros x (a & <-); auto.
  Qed.

  Definition LubC (h : A → R) := proj1_sig (ex_lubC h).

  Lemma LubC_correct (h : A → R) :
    is_lubC h (LubC h).
  Proof.
    rewrite /LubC ; by case: ex_lubC => l /= Hl.
  Qed.

  Lemma seriesC_le_lub (h : A → R) :
    ex_seriesC h →
    is_finite (LubC h) →
    ex_seriesC (λ a : A, real (LubC h)) →
    SeriesC h <= SeriesC (λ a : A, real (LubC h)).
  Proof.
    intros Hex Hfin Hex2.
    apply SeriesC_le'; auto.
    intro n.
    destruct (LubC_correct h) as [H1 H2].
    apply rbar_le_finite; auto.
  Qed.

  Definition is_glbC (h: A → R) (l : Rbar) :=
    (∀ a, Rbar_le l (h a) ) ∧ (∀ l', (∀ a, Rbar_le l' (h a)) → Rbar_le l' l).

  Lemma ex_glbC (h : A → R) :
    {u | is_glbC h u}.
  Proof.
    destruct (Glb_Rbar_correct ((λ r : R, ∃ a0 : A, h a0 = r))) as [H1 H2].
    exists (Glb_Rbar (λ (r : R), exists a, h a = r)); split.
    - intro a.
      apply H1; eauto.
    - intros u' Hu'.
      apply H2; auto.
      rewrite /is_lb_Rbar.
      intros x (a & <-); auto.
  Qed.

  Definition GlbC (h : A → R) := proj1_sig (ex_glbC h).

  Lemma GlbC_correct (h : A → R) :
    is_glbC h (GlbC h).
  Proof.
    rewrite /GlbC ; by case: ex_glbC => l /= Hl.
  Qed.

  Lemma seriesC_le_glb (h : A → R) :
    ex_seriesC h →
    is_finite (GlbC h) →
    ex_seriesC (λ a : A, real (GlbC h)) →
    SeriesC (λ a : A, real (GlbC h)) <= SeriesC h.
  Proof.
    intros Hex Hfin Hex2.
    apply SeriesC_le'; auto.
    intro n.
    destruct (GlbC_correct h) as [H1 H2].
    apply finite_rbar_le; auto.
  Qed.

End bounds.

Section fubini.
  Context `{Countable A, Countable B}.


  (*
     The following three lemmas have been proven for
     Series, so the only missing part is lifting them
     to SeriesC
   *)

  Lemma fubini_pos_seriesC_ex (h : A * B → R) :
    (∀ a b, 0 <= h (a, b)) →
    (∀ a, ex_seriesC (λ b, h (a, b))) →
    (ex_seriesC (λ a, SeriesC (λ b, h (a, b)))) →
    (∀ b, ex_seriesC (λ a, h (a, b))).
  Proof.
    intros Hpos Hex1 Hex2 b.
    set (f := λ '(n, m), countable_sum (λ a, countable_sum (λ b, h (a,b)) m) n).
    assert (∀ m, ex_series (λ n, f (n, m))) as H1.
    {
      apply fubini_pos_series_ex.
      - intros n m.
        rewrite /f/countable_sum.
        destruct (encode_inv_nat n);
        destruct (encode_inv_nat m);
        simpl; real_solver.
      - intro n. rewrite /f {1}/countable_sum.
        destruct (encode_inv_nat n); simpl.
        + apply Hex1.
        + exists 0. apply is_series_0; auto.
     - rewrite /f/countable_sum/=.
       apply ex_seriesC_ex_series_inv in Hex2.
       rewrite /SeriesC/countable_sum/= in Hex2.
       eapply ex_series_ext; [ | apply Hex2].
       intro n; simpl.
       destruct (encode_inv_nat n); simpl; auto.
       symmetry; apply Series_0; auto.
    }
    apply ex_seriesC_ex_series.
    eapply ex_series_ext; [ | apply (H1 (encode_nat b)) ].
    intros; simpl.
    apply countable_sum_ext => a.
    rewrite /countable_sum encode_inv_encode_nat //.
  Qed.

  Lemma fubini_pos_seriesC_ex_double (h : A * B → R) :
    (∀ a b, 0 <= h (a, b)) →
    (∀ a, ex_seriesC (λ b, h (a, b))) →
    (ex_seriesC (λ a, SeriesC (λ b, h (a, b)))) →
    (ex_seriesC (λ b, SeriesC (λ a, h (a, b)))).
  Proof.
    intros Hpos Hex1 Hex2.
    set (f := λ '(n, m), countable_sum (λ a, countable_sum (λ b, h (a,b)) m) n).
    assert (ex_series (λ m, Series (λ n, f (n, m)))) as H1.
    {
      apply fubini_pos_series_ex_double.
      - intros n m.
        rewrite /f/countable_sum.
        destruct (encode_inv_nat n);
        destruct (encode_inv_nat m);
        simpl; real_solver.
      - intro n. rewrite /f {1}/countable_sum.
        destruct (encode_inv_nat n); simpl.
        + apply Hex1.
        + exists 0. apply is_series_0; auto.
     - rewrite /f/countable_sum/=.
       apply ex_seriesC_ex_series_inv in Hex2.
       rewrite /SeriesC/countable_sum/= in Hex2.
       eapply ex_series_ext; [ | apply Hex2].
       intro n; simpl.
       destruct (encode_inv_nat n); simpl; auto.
       symmetry; apply Series_0; auto.
    }
    apply ex_seriesC_ex_series.
    eapply ex_series_ext; [ | apply H1 ].
    intros; simpl.
    rewrite /SeriesC /countable_sum.
    destruct (encode_inv_nat n); simpl; auto.
    apply Series_0.
    intro m.
    destruct (encode_inv_nat m); simpl; auto.
  Qed.

  Lemma fubini_pos_seriesC (h : A * B → R) :
    (∀ a b, 0 <= h (a, b)) →
    (∀ a, ex_seriesC (λ b, h (a, b))) →
    (ex_seriesC (λ a, SeriesC (λ b, h (a, b)))) →
    SeriesC (λ b, SeriesC (λ a, h (a, b))) =
      SeriesC (λ a, SeriesC (λ b, h (a, b))).
  Proof.
    intros Hpos Hex1 Hex2.
    set (f := λ '(n, m), countable_sum (λ a, countable_sum (λ b, h (a,b)) m) n).
    assert (Series (λ m, Series (λ n, f (n, m))) = Series (λ n, Series (λ m, f (n, m)))) as H1.
    {
      apply fubini_pos_series.
      - intros n m.
        rewrite /f/countable_sum.
        destruct (encode_inv_nat n);
        destruct (encode_inv_nat m);
        simpl; real_solver.
      - intro n. rewrite /f {1}/countable_sum.
        destruct (encode_inv_nat n); simpl.
        + apply Hex1.
        + exists 0. apply is_series_0; auto.
     - rewrite /f/countable_sum/=.
       apply ex_seriesC_ex_series_inv in Hex2.
       rewrite /SeriesC/countable_sum/= in Hex2.
       eapply ex_series_ext; [ | apply Hex2].
       intro n; simpl.
       destruct (encode_inv_nat n); simpl; auto.
       symmetry; apply Series_0; auto.
    }
    etrans; [ etrans; [ | exact H1] | ].
    - rewrite /f/SeriesC/countable_sum.
      apply Series_ext.
      intro n.
      destruct (encode_inv_nat n); simpl; auto.
      symmetry; apply Series_0; auto.
      intro m.
      destruct (encode_inv_nat m); simpl; auto.
    - rewrite /f/SeriesC/countable_sum.
      apply Series_ext.
      intro n.
      destruct (encode_inv_nat n); simpl; auto.
      apply Series_0; auto.
  Qed.

  Lemma fubini_pos_seriesC' (h : A -> B → R) :
    (∀ a b, 0 <= h a b) →
    (∀ a, ex_seriesC (λ b, h a b)) →
    (ex_seriesC (λ a, SeriesC (λ b, h a b))) →
    SeriesC (λ b, SeriesC (λ a, h a b)) =
    SeriesC (λ a, SeriesC (λ b, h a b)).
  Proof.
    intros.
    pose (h' := λ '(a,b), h a b).
    assert (forall a b, h a b = h' (a,b)) as H'.
    { intros. by rewrite /h'. }
    setoid_rewrite H'.
    apply fubini_pos_seriesC.
    all: by setoid_rewrite <-H'.
  Qed.

End fubini.

Section mct.
  Context `{Countable A}.

  Lemma MCT_seriesC (h : nat → A → R) (l : nat → R) (r : R) :
    (∀ n a, 0 <= (h n a)) →
    (∀ n a, (h n a) <= (h (S n) a)) →
    (∀ a, exists s, ∀ n, h n a <= s ) →
    (∀ n, is_seriesC (h n) (l n)) →
    is_sup_seq l (Rbar.Finite r) →
    SeriesC (λ a, Sup_seq (λ n, h n a)) = r.
  Proof.
    intros Hpos Hle1 Hle2 Hsr Hsup.
    set (f := λ n m, countable_sum (λ a, h n a) m).
    assert (Series (λ m, Sup_seq (λ n, f n m)) = r ) as H1.
    {
      apply (MCT_series f l r).
      - intros n m.
        rewrite /f/countable_sum.
        destruct (encode_inv_nat m);
        simpl; real_solver.
      - intros n m.
        rewrite /f/countable_sum.
        destruct (encode_inv_nat m);
        simpl; real_solver.
      - intro n.
        rewrite /f/countable_sum.
        destruct (encode_inv_nat) as [a | ].
        + destruct (Hle2 a) as [s Hs].
          exists s; auto.
        + exists 0; real_solver.
      - intro n.
        specialize (Hsr n).
        eapply is_series_ext; [ | exact Hsr].
        intro m.
        rewrite /f /countable_sum.
        destruct (encode_inv_nat m); simpl; auto.
     - auto.
    }
    rewrite -H1.
    apply Series_ext.
    intro n.
    rewrite /f/countable_sum.
    destruct (encode_inv_nat n); simpl; auto.
    symmetry.
    apply sup_seq_const.
  Qed.

  Lemma MCT_ex_seriesC (h : nat → A → R) (l : nat → R) (r : R) :
    (∀ n a, 0 <= (h n a)) →
    (∀ n a, (h n a) <= (h (S n) a)) →
    (∀ a, exists s, ∀ n, h n a <= s ) →
    (∀ n, is_seriesC (h n) (l n)) →
    is_sup_seq l (Rbar.Finite r) →
    ex_seriesC (λ a, Sup_seq (λ n, h n a)).
  Proof.
    intros Hpos Hle1 Hle2 Hsr Hsup.
    set (f := λ n m, countable_sum (λ a, h n a) m).
    assert (ex_series (λ m, real (Sup_seq (λ n, f n m)))) as H1.
    {
      apply (MCT_ex_series f l r).
      - intros n m.
        rewrite /f/countable_sum.
        destruct (encode_inv_nat m);
          simpl; real_solver.
      - intros n m.
        rewrite /f/countable_sum.
        destruct (encode_inv_nat m);
          simpl; real_solver.
      - intro n.
        rewrite /f/countable_sum.
        destruct (encode_inv_nat) as [a | ].
        + destruct (Hle2 a) as [s Hs].
          exists s; auto.
        + exists 0; real_solver.
      - intro n.
        specialize (Hsr n).
        eapply is_series_ext; [ | exact Hsr].
        intro m.
        rewrite /f /countable_sum.
        destruct (encode_inv_nat m); simpl; auto.
      - auto.
    }
    eapply ex_series_ext; [ | apply H1].
    intro n.
    rewrite /f/countable_sum.
    destruct (encode_inv_nat n); simpl; auto.
    apply sup_seq_const.
  Qed.

  Lemma SeriesC_Sup_seq_swap (r : R) (l : nat → R) (h : nat → A → R) :
    (∀ n a, 0 <= (h n a)) →
    (∀ n a, (h n a) <= (h (S n) a)) →
    (∀ a, exists s, ∀ n, h n a <= s ) →
    (∀ n, is_seriesC (h n) (l n)) →
    (∀ n, l n <= r) →
    SeriesC (λ a, Sup_seq (λ n, h n a)) = Sup_seq (λ n, SeriesC (h n)).
  Proof.
    intros ?????.
    eapply MCT_seriesC; [done..|].
    assert (∀ n, SeriesC (λ a : A, h n a) = l n) as Heq.
    { intros ?. by eapply is_seriesC_unique. }
    erewrite Sup_seq_ext; last first.
    { intros n. rewrite Heq //. }
    rewrite (Rbar_le_sandwich 0 r).
    - apply Sup_seq_correct.
    - apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
      rewrite -Heq. by apply SeriesC_ge_0'.
    - by apply upper_bound_ge_sup=>/=.
  Qed.

End mct.

Section double.
  Context `{Countable A, Countable B}.

  Variable (h : A * B → R).
  Variable (POS : ∀ a b, 0 <= h (a, b)).

  Definition σprod (n : nat) :=
    match @encode_inv_nat (A*B) _ _ n with
    | Some (a, b) => (S (encode_nat a), S (encode_nat b))
    | None => (O, O)
    end.

  Definition aprod (mn : nat * nat) :=
    match mn with
    | (S m, S n) =>
        match @encode_inv_nat A _ _ m, @encode_inv_nat B _ _ n with
        | Some a, Some b => h (a, b)
        | _, _ => 0
        end
    | _ => 0
    end.

  Lemma aprod_pos: ∀ m n, 0 <= aprod (m, n).
  Proof .
    intros m n. rewrite /aprod.
    do 4 (case_match; try lra). auto.
  Qed.

  Lemma σprod_inj n n' :
    aprod (σprod n) ≠ 0 → σprod n = σprod n' → n = n'.
  Proof.
    rewrite /σprod /aprod.
    destruct (encode_inv_nat n) as [[a b]|] eqn: Heq1 => /=; [|nra].
    destruct (encode_inv_nat (encode_nat a)) as [a'|] eqn: Heq2; [|nra].
    destruct (encode_inv_nat (encode_nat b)) as [b'|] eqn: Heq3; [|nra].
    intros _.
    destruct (encode_inv_nat n') as [[a'' b'']|] eqn:Heq4;
      intros [= <-%(inj _) <-%(inj _)].
    rewrite encode_inv_encode_nat in Heq2.
    rewrite encode_inv_encode_nat in Heq3.
    simplify_eq. rewrite -Heq1 in Heq4.
    by eapply encode_inv_nat_some_inj.
  Qed.

  Lemma σprod_cov n : aprod n ≠ 0 → ∃ m, σprod m = n.
  Proof.
    destruct n as [[] []]=> //=.
    case_match eqn:Ha; [|lra].
    case_match eqn:Hb; [|lra].
    intros _.
    exists (encode_nat (a, b)).
    rewrite /σprod.
    rewrite encode_inv_encode_nat.
    erewrite encode_inv_Some_nat; [|done].
    erewrite encode_inv_Some_nat; [|done].
    done.
  Qed.

  Lemma aprod_σprod_countable_sum n :
    (aprod ∘ σprod) n = countable_sum h n.
  Proof.
    rewrite /aprod/σprod/countable_sum/=.
    destruct (encode_inv_nat n) as [[]|] eqn:Heq; simpl; [|lra].
    do 2 rewrite encode_inv_encode_nat.
    lra.
  Qed.

  Lemma ex_series_σprod :
    ex_seriesC h → ex_series (aprod ∘ σprod).
  Proof.
    intros Hex.
    apply ex_pos_bounded_series.
    + intros n. simpl. destruct (σprod n). apply aprod_pos.
    + exists (SeriesC h).
      apply ex_seriesC_ex_series_inv in Hex.
      intro n.
      etrans; last first.
      * eapply series_pos_partial_le; [|done].
        intro m. apply countable_sum_ge_0. by intros [].
      * apply sum_n_le => m.
        rewrite aprod_σprod_countable_sum //.
  Qed.

  #[local] Hint Resolve aprod_pos σprod_inj σprod_cov ex_series_σprod : core.

  Lemma aprod_double_summable:
    ex_seriesC h → double_summable aprod.
  Proof. intros Hex. eapply (summable_implies_ds aprod σprod); auto. Qed.

  Lemma aprod_S_double_summable :
    ex_seriesC h → double_summable (λ '(j, k), aprod (S j, S k)).
  Proof.
    intros [r Hr]%aprod_double_summable.
    rewrite /double_summable.
    exists r.
    intros n.
    erewrite sum_n_ext; last first.
    { intros m. rewrite (sum_n_shift (λ k, aprod (S m, k))) //. }
    rewrite sum_n_plus /plus /=.
    rewrite (sum_n_shift (λ k, sum_n (λ j, aprod (k, j)) (S n))).
    rewrite sum_n_const.
    assert (0 <= sum_n (λ j, aprod (0%nat, j)) (S n)) by eapply partial_sum_pos=>//.
    specialize (Hr (S n)).
    lra.
  Qed.

  Lemma is_seriesC_prod_row:
    ex_seriesC h → is_seriesC h (Series (λ j, Series (λ k, aprod (S j, S k)))).
  Proof.
    intro Hex.
    apply (is_series_ext (aprod ∘ σprod)); [apply aprod_σprod_countable_sum|].
    eapply is_series_chain; [apply is_series_double_covering'; auto|].
    cut (Series (λ j, Series (λ k, aprod (j, k))) =
           (Series (λ j, Series (λ k, aprod (S j, S k))))).
    { intros <-. apply Series_correct. eexists.
      eapply (is_series_double_covering aprod σprod); auto. }
    rewrite Series_incr_1; last first.
    { eexists. eapply is_series_double_covering; eauto. }
    rewrite {1}/aprod Series_0 // Rplus_0_l.
    apply Series_ext => n.
    rewrite Series_incr_1; last first.
    { apply ex_series_row; [|auto]. by apply aprod_double_summable. }
    rewrite {1}/aprod Rplus_0_l => //=.
  Qed.

  Lemma is_seriesC_prod_column:
    ex_seriesC h → is_seriesC h (Series (λ k, Series (λ j, aprod (S j, S k)))).
  Proof.
    intros Hex.
    rewrite -(double_summable_fubini (λ '(j, k), aprod (S j, S k))).
    - by apply is_seriesC_prod_row.
    - intros []; auto.
    - by apply aprod_S_double_summable.
  Qed.

  Lemma SeriesC_prod_row :
    ex_seriesC h → SeriesC h = Series (λ j, Series (λ k, aprod (S j, S k))).
  Proof. intros ?. by apply is_series_unique, is_seriesC_prod_row. Qed.

  Lemma SeriesC_prod_column :
    ex_seriesC h → SeriesC h = Series (λ k, Series (λ j, aprod (S j, S k))).
  Proof. intros ?. by apply is_series_unique, is_seriesC_prod_column. Qed.

  Lemma fubini_pos_seriesC_prod_lr  :
    ex_seriesC h → SeriesC h = SeriesC (λ a, SeriesC (λ b, h (a, b))).
  Proof.
    intros Hex.
    rewrite SeriesC_prod_row //.
    rewrite /SeriesC/aprod/countable_sum.
    apply Series_ext => n.
    destruct (encode_inv_nat n); simpl; [ | apply Series_0; auto].
    apply Series_ext => m.
    destruct (encode_inv_nat m); simpl; auto.
  Qed .

  Lemma fubini_pos_seriesC_prod_rl :
    ex_seriesC h → SeriesC h = SeriesC (λ b, SeriesC (λ a, h (a, b))).
  Proof.
    intros Hex.
    rewrite SeriesC_prod_column //.
    rewrite /SeriesC/aprod/countable_sum.
    apply Series_ext => n.
    destruct (encode_inv_nat n); simpl; last first.
    { rewrite Series_0 //. intros. by case_match. }
    apply Series_ext => m.
    destruct (encode_inv_nat m); simpl; auto.
  Qed.

  Lemma fubini_pos_ex_seriesC_prod_ex_lr  :
    ex_seriesC h → ex_seriesC (λ a, SeriesC (λ b, h (a, b))).
  Proof.
    intros Hex.
    apply ex_seriesC_ex_series.
    rewrite /SeriesC/countable_sum.
    assert (∀ n,
               (from_option
                  (λ a, Series (λ n0, from_option (λ b, h (a, b)) 0 (encode_inv_nat n0))) 0
                  (encode_inv_nat n)) =
                 (Series (λ n0, from_option
                                  (λ a, from_option (λ b, h (a, b)) 0 (encode_inv_nat n0)) 0
                                  (encode_inv_nat n)))) as Haux.
    { intro n. destruct (encode_inv_nat); simpl; auto. by rewrite Series_0. }
    setoid_rewrite Haux.
    apply (ex_series_row_col
             (λ '(n,n0),
               from_option (λ a, from_option (λ b, h (a, b)) 0 (encode_inv_nat n0)) 0
                 (encode_inv_nat n))).
    - apply aprod_double_summable in Hex as (r&Hr).
      exists r.
      intro n.
      etrans; [ | apply (Hr (S n))].
      right.
      rewrite sum_n_shift'.
      replace (sum_n (λ k : nat, aprod (0%nat, k)) (S n)) with 0; last first.
      { rewrite (sum_n_ext _ (λ n, 0)).
        - rewrite sum_n_const; lra.
        - intro; rewrite /aprod //. }
      rewrite Rplus_0_r.
      apply sum_n_ext; intro m.
      rewrite sum_n_shift'.
      replace (aprod (S m, 0%nat)) with 0; [ | by rewrite /aprod].
      rewrite Rplus_0_r.
      apply sum_n_ext; intro l.
      rewrite /aprod.
      destruct (encode_inv_nat m), (encode_inv_nat l); simpl; auto.
    - intros n m.
      destruct (encode_inv_nat n), (encode_inv_nat m); simpl; auto; lra.
  Qed.

  (* TODO: simplify using previous lemma  *)
  Lemma fubini_pos_ex_seriesC_prod_ex_rl  :
    ex_seriesC h → ex_seriesC (λ b, SeriesC (λ a, h (a, b))).
  Proof.
    intros Hex.
    apply ex_seriesC_ex_series.
    rewrite /SeriesC/countable_sum.
    assert (∀ n,
               (from_option
                  (λ b,
                    Series (λ n0 : nat, from_option (λ a, h (a, b)) 0 (encode_inv_nat n0))) 0
                  (encode_inv_nat n)) =
                 (Series (λ n0 : nat,
                        from_option
                          (λ b, from_option (λ a, h (a, b)) 0 (encode_inv_nat n0)) 0
                          (encode_inv_nat n)))) as Haux.
    {
      intro n. destruct (encode_inv_nat); simpl; auto.
      by rewrite Series_0.
    }
    setoid_rewrite Haux.
    apply (ex_series_row_col
             (λ '(n,n0),
               from_option (λ b, from_option (λ a, h (a, b)) 0 (encode_inv_nat n0)) 0
                 (encode_inv_nat n))).
    - apply aprod_double_summable in Hex as (r&Hr).
      exists r.
      intro n.
      etrans; [ | apply (Hr (S n))].
      right.
      rewrite fubini_fin_sum.
      rewrite sum_n_shift'.
      replace (sum_n (λ a : nat, aprod (a, 0%nat)) (S n)) with 0; last first.
      {
        rewrite (sum_n_ext _ (λ n, 0)).
        - rewrite sum_n_const; lra.
        - intro; rewrite /aprod.
          case_match; auto.
      }
      rewrite Rplus_0_r.
      apply sum_n_ext; intro m.
      rewrite sum_n_shift'.
      replace (aprod (0%nat, S m)) with 0; [ | by rewrite /aprod].
      rewrite Rplus_0_r.
      apply sum_n_ext; intro l.
      rewrite /aprod.
      destruct (encode_inv_nat m), (encode_inv_nat l); simpl; auto.
    - intros n m.
      destruct (encode_inv_nat n), (encode_inv_nat m); simpl; auto; lra.
  Qed.

  Lemma ex_seriesC_lmarg a :
    ex_seriesC h → ex_seriesC (λ b, h (a, b)).
  Proof.
    intros Hex.
    apply ex_seriesC_ex_series.
    rewrite /SeriesC/countable_sum.
    apply aprod_double_summable in Hex.
    apply DS_n_to_nm in Hex as (r&Hr); last first.
    {
      intros n m.
      rewrite /aprod.
      do 4 (case_match; simpl; auto; try lra).
    }
    apply ex_pos_bounded_series.
    - intro n; destruct (encode_inv_nat n); simpl; auto.
      lra.
    - exists r. intro n.
      etrans; [ | apply (Hr (S n) (S (encode_nat a)))].
      rewrite sum_n_shift'.
      rewrite (sum_n_ext ((λ k : nat, aprod (0%nat, k))) (λ _, 0)); last first.
      {
        intro; rewrite /aprod //.
      }
      rewrite sum_n_const Rmult_0_r Rplus_0_r.
      etrans; [ | apply partial_sum_elem]; last first.
      {
        intro.
        apply partial_sum_pos.
        intro.
        rewrite /aprod.
        do 4 (case_match; simpl; auto; try lra).
      }
      rewrite sum_n_shift'.
      etrans; last first.
      {
        apply (Rplus_le_compat_l _ 0).
        rewrite /aprod; lra.
      }
      rewrite Rplus_0_r.
      right.
      apply sum_n_ext.
      intro m.
      rewrite /aprod.
      rewrite encode_inv_encode_nat.
      destruct (encode_inv_nat m); simpl; auto.
  Qed.

  Lemma ex_seriesC_rmarg b :
    ex_seriesC h → ex_seriesC (λ a, h (a, b)).
  Proof.
    intros Hex.
    apply ex_seriesC_ex_series.
    rewrite /SeriesC/countable_sum.
    apply aprod_double_summable in Hex.
    apply DS_n_to_nm in Hex as (r&Hr); last first.
    {
      intros n m.
      rewrite /aprod.
      do 4 (case_match; simpl; auto; try lra).
    }
    apply ex_pos_bounded_series.
    - intro n; destruct (encode_inv_nat n); simpl; auto.
      lra.
    - exists r. intro n.
      etrans; [ | apply (Hr (S (encode_nat b)) (S n) )].
      rewrite fubini_fin_sum.
      rewrite sum_n_shift'.
      rewrite (sum_n_ext (λ a : nat, aprod (a, 0%nat)) (λ _, 0)); last first.
      {
        intro; rewrite /aprod //.
        case_match; auto.
      }
      rewrite sum_n_const Rmult_0_r Rplus_0_r.
      etrans; [ | apply partial_sum_elem]; last first.
      {
        intro.
        apply partial_sum_pos.
        intro.
        rewrite /aprod.
        do 4 (case_match; simpl; auto; try lra).
      }
      rewrite sum_n_shift'.
      etrans; last first.
      {
        apply (Rplus_le_compat_l _ 0).
        rewrite /aprod; lra.
      }
      rewrite Rplus_0_r.
      right.
      apply sum_n_ext.
      intro m.
      rewrite /aprod.
      rewrite encode_inv_encode_nat.
      destruct (encode_inv_nat m); simpl; auto.
  Qed.

  Lemma seriesC_lmarg_le a :
    ex_seriesC h → SeriesC (λ b, h (a, b)) <= SeriesC h.
  Proof.
    intros Hex.
    rewrite fubini_pos_seriesC_prod_rl //.
    apply SeriesC_le; [ | eapply fubini_pos_ex_seriesC_prod_ex_rl; eauto].
    intro b; split; [real_solver | ].
    apply (SeriesC_ge_elem (λ a0, h (a0, b))); [ | apply ex_seriesC_rmarg; auto]; auto.
  Qed.

  Lemma seriesC_rmarg_le b :
    ex_seriesC h → SeriesC (λ a, h (a, b)) <= SeriesC h.
  Proof.
    intros Hex.
    rewrite fubini_pos_seriesC_prod_lr //.
    apply SeriesC_le; [ | eapply fubini_pos_ex_seriesC_prod_ex_lr; eauto].
    intro a; split; [real_solver | ].
    apply (SeriesC_ge_elem (λ b0, h (a, b0))); [ | apply ex_seriesC_lmarg; auto]; auto.
  Qed.

  Lemma ex_seriesC_prod :
    (∀ a, ex_seriesC (λ b, h (a,b))) →
    ex_seriesC (λ a, SeriesC (λ b, h (a,b))) →
    ex_seriesC h.
  Proof.
    intros Hex1 Hex2.
    assert (ex_series (aprod ∘ σprod)) as Haux; last first.
    {
      apply ex_seriesC_ex_series.
      apply (ex_series_ext _ _ aprod_σprod_countable_sum Haux).
    }
    apply ds_implies_exseries; auto.
    apply ex_series_rows_ds.
    - apply aprod_pos.
    - intro m. rewrite /aprod.
      destruct m as [ | m'].
      {
        apply ex_pos_bounded_series.
        - intro; lra.
        - exists 0. intro. rewrite sum_n_const; lra.
      }
      destruct (encode_inv_nat m') as [ |]; last first.
      {
        apply ex_pos_bounded_series.
        - intro. case_match; lra.
        - exists 0. intro. rewrite (sum_n_ext _ (λ _, 0)).
          + rewrite sum_n_const; lra.
          + intro; case_match; auto.
      }
      specialize (Hex1 a).
      apply ex_seriesC_ex_series_inv in Hex1.
      rewrite /countable_sum in Hex1.
      apply ex_series_incr_1.
      eapply (ex_series_ext _ _ _ Hex1). Unshelve.
      intro n; simpl.
      destruct (encode_inv_nat n); auto.
    - apply ex_seriesC_ex_series_inv in Hex2.
      rewrite /SeriesC/countable_sum in Hex2.
      apply ex_series_incr_1.
      eapply (ex_series_ext _ _ _ Hex2). Unshelve.
      intro n; simpl.
      destruct (encode_inv_nat n); simpl.
      + rewrite (Series_incr_1_aux
                   (λ k, match k with
                     | 0%nat => 0
                     | S n0 => _
                     end)); auto.
      + rewrite Series_0 //. intro; by case_match.
  Qed.

End double.

Section inj.
  Context `{Countable A, Countable B}.

    (* A lemma about rearranging SeriesC along an injective function *)

  Lemma SeriesC_le_inj (f : B -> R) (h : A -> option B) :
    (∀ n, 0 <= f n) →
    (forall n1 n2 m, h n1 = Some m -> h n2 = Some m -> n1 = n2) ->
    ex_seriesC f →
    SeriesC (λ a, from_option f 0 (h a)) <= SeriesC f.
  Proof.
    intros Hf Hinj Hex.
    rewrite {1}/SeriesC/Series.
    apply Series_Ext.Lim_seq_le_loc_const.
    - by apply SeriesC_ge_0'.
    - rewrite /eventually. exists 0%nat.
      intros n Hn.
      assert (∃ l : list _, (∀ m, m∈l->(∃ k a, (k<=n)%nat /\
                                              (@encode_inv_nat A _ _ k%nat) = Some a /\
                                              h a = Some m)) /\
                   sum_n (countable_sum (λ a : A, from_option f 0 (h a))) n <=
                    SeriesC (λ a, if bool_decide(a ∈ l) then f a else 0)
             ) as H'; last first.
      { destruct H' as [?[??]].
        etrans; first exact.
        apply SeriesC_le'; try done.
        - intros. case_bool_decide; try lra. apply Hf.
        - apply ex_seriesC_list.
      }
      induction n.
      + destruct (@encode_inv_nat A _ _ 0%nat) eqn:Ha.
        * destruct (h a) eqn : Hb.
          -- exists [b]. split.
             ++ intros. exists 0%nat, a.
                repeat split; try lia; try done.
                rewrite Hb. f_equal. set_solver.
             ++ rewrite sum_O. rewrite /countable_sum.
                rewrite Ha. simpl. rewrite Hb. simpl.
                erewrite SeriesC_ext.
                ** erewrite SeriesC_singleton_dependent. done.
                ** intro. simpl.
                   repeat case_bool_decide; set_solver.
          -- exists []. split.
             ++ intros; set_solver.
             ++ rewrite sum_O. rewrite /countable_sum.
                rewrite Ha. simpl. rewrite Hb. simpl.
                rewrite SeriesC_0; intros; lra.
        * exists []. split.
          ++ intros; set_solver.
          ++ rewrite sum_O. rewrite /countable_sum.
             rewrite Ha. simpl.
             rewrite SeriesC_0; intros; lra.
      + assert (0<=n)%nat as Hge0.
        * lia.
        * specialize (IHn Hge0) as [l[H1 H2]].
          destruct (@encode_inv_nat A _ _ (S n)%nat) eqn:Ha.
          -- destruct (h a) eqn : Hb.
             ++ exists (b::l). split.
                ** intros. set_unfold.
                   destruct H3; subst.
                   --- exists (S n), a. split; try lia. split; done.
                   --- specialize (H1 m H3).
                       destruct H1 as [?[?[?[??]]]].
                       exists x, x0. split; try lia. by split.
                ** rewrite sum_Sn. rewrite {2}/countable_sum.
                   rewrite Ha. simpl. rewrite Hb. simpl.
                   rewrite (SeriesC_ext _ (λ x, (if bool_decide (x=b) then f b else 0) +
                                                  if bool_decide (x∈l) then f x else 0
                           )); last first.
                   { intros.
                     case_bool_decide.
                     - set_unfold. destruct H3.
                       + case_bool_decide; last done.
                         case_bool_decide.
                         * subst. specialize (H1 b H5).
                           destruct H1 as [?[?[?[??]]]].
                           rewrite -H6 in Hb.
                           assert (a = x0).
                           { eapply Hinj; try done. rewrite Hb. done. }
                           subst. exfalso.
                           rewrite -H3 in Ha. assert (x≠ (S n)) by lia.
                           apply H7. by eapply encode_inv_nat_some_inj.
                         * subst. lra.
                       + case_bool_decide.
                         { subst. specialize (H1 b H3) as [?[?[?[??]]]].
                           assert (x ≠ S n) by lia.
                           exfalso. apply H6. eapply encode_inv_nat_some_inj; try done.
                           rewrite Ha H4. f_equal.
                           by eapply Hinj.
                         }
                         case_bool_decide; try done. lra.
                     - repeat case_bool_decide.
                       + set_solver.
                       + set_solver.
                       + set_solver.
                       + lra.
                   }
                   rewrite SeriesC_plus; last first.
                   { by apply ex_seriesC_filter_pos. }
                   { by apply ex_seriesC_singleton. }
                   rewrite Rplus_comm. rewrite SeriesC_singleton.
                   trans ((sum_n (countable_sum (λ a0 : A, from_option f 0 (h a0))) n) + f b); try lra.
                   done.
             ++ exists l. split.
                ** intros. specialize (H1 _ H3) as [?[?[?[??]]]].
                   exists x, x0. repeat split; try done. lia.
                ** rewrite sum_Sn. rewrite {2}/countable_sum. rewrite Ha. simpl.
                   rewrite Hb. simpl. etrans; last exact.
                   by rewrite plus_zero_r.
          -- exists l. split.
             ++ intros. specialize (H1 _ H3) as [?[?[?[??]]]].
                exists x, x0. repeat split; try done. lia.
             ++ rewrite sum_Sn. rewrite {2}/countable_sum. rewrite Ha. simpl.
                etrans; last exact.
                by rewrite plus_zero_r.
  Qed.

End inj.


Section Inj_finite.

  Lemma SeriesC_filter_finite_1 `{Countable A} (M:nat) (f:A -> R) (g: fin M -> R) h:
    Inj eq eq h -> (0 < M)%nat -> (∀ a: A, 0 <= f a <= 1) -> (∀ b: fin M, 0 <= g b <= 1) ->
    (∀ (a : A) (b : fin M), a = h b → f a <= g b) ->
    SeriesC (λ a : A, if bool_decide (∃ y : fin M, a = h y) then f a else 0) <= SeriesC g.
  Proof.
    intros Hinj Hineq Hf Hg Hfg.
    rewrite {1}/SeriesC. apply series_bounded. 
    { intros. apply countable_sum_ge_0. intros; case_bool_decide; naive_solver. }
    2:{ eapply ex_seriesC_ex_series_inv, ex_seriesC_ext; last eapply ex_seriesC_list.
        instantiate (2:= h <$> enum (fin M)).
        intros. case_bool_decide as H1; case_bool_decide as H2; try done.
        - exfalso.
          apply H2. destruct H1. subst. apply elem_of_list_fmap_1, elem_of_enum.
        - exfalso. apply H1. rewrite elem_of_list_fmap in H2. destruct H2 as [y[??]].
          naive_solver.           
    }
    intros n.
    cut (∃ l', NoDup l' /\ (∀ y, y ∈ l' <-> (∃ x, x = h y /\ (encode_nat x <= n)%nat)) /\
               sum_n (countable_sum (λ a : A, if bool_decide (∃ y : fin M, a = h y) then f a else 0)) n <= SeriesC (λ x, if bool_decide (x ∈ l') then g x else 0)
        ).
    { intros [?[?[??]]]. etrans; first exact. apply SeriesC_filter_leq; last apply ex_seriesC_finite.
      intros; naive_solver.
    }
    induction n.
    - rewrite sum_O /countable_sum. destruct (encode_inv_nat _) eqn:H1; simpl.
      + case_bool_decide as H2.
        * destruct H2 as [y?].
          exists [y].
          repeat split.
          -- repeat constructor. set_solver.
          -- intros. exists a. split; first set_solver.
             apply encode_inv_Some_nat in H1. lia.
          -- intros [?[??]].
             subst. assert (encode_nat (h y0) = 0%nat) by lia.
             apply encode_inv_Some_nat in H1. rewrite -H1 in H0.
             apply encode_nat_inj in H0. apply Hinj in H0. set_solver.
          -- subst. erewrite SeriesC_ext.
             { erewrite SeriesC_singleton_dependent. by apply Hfg. }
             intros. repeat case_bool_decide; set_solver.
        * exists []. repeat split.
          -- constructor.
          -- set_solver.
          -- intros [? [??]]. exfalso. apply H2. apply encode_inv_Some_nat in H1.
             assert (encode_nat x = 0%nat) by lia. rewrite -H1 in H4. apply encode_nat_inj in H4; subst.
             naive_solver.
          -- apply SeriesC_ge_0'. intros. case_bool_decide; naive_solver.
      + exists []. repeat split.
        -- constructor.
        -- set_solver.
        -- intros [?[??]]. assert (encode_nat x = 0%nat) by lia. rewrite -H3 in H1.
           by rewrite encode_inv_encode_nat in H1.
        -- apply SeriesC_ge_0'. intros. case_bool_decide; naive_solver.
    - destruct IHn as [l'[Hnd[H1 H2]]].
      rewrite sum_Sn /countable_sum. destruct (encode_inv_nat _) eqn:H3; simpl.
      + case_bool_decide as H4.
        * destruct H4 as [y?].
          exists (y::l'). repeat split.
          -- constructor; last done. move /H1. intros [?[??]]. subst.
             apply encode_inv_Some_nat in H3. lia.
          -- move /elem_of_cons. intros [->|?].
             ++ exists a. split; first done. apply encode_inv_Some_nat in H3. lia.
             ++ subst. rewrite H1 in H4. naive_solver.
          -- intros [?[??]]. subst.
             rewrite Nat.le_succ_r in H5. destruct H5.
             ++ apply elem_of_list_further. rewrite H1.
                eexists _; by split.
             ++ apply encode_inv_Some_nat in H3. rewrite -H3 in H0. apply encode_nat_inj in H0.
                apply Hinj in H0. set_solver.
          -- rewrite (SeriesC_ext _ (λ x : fin M, (if bool_decide (x ∈ l') then g x else 0)+if bool_decide (x = y) then g x else 0)).
             ++ rewrite SeriesC_plus; try apply ex_seriesC_finite.
                apply Rplus_le_compat; first done.
                rewrite SeriesC_singleton_dependent.
                by apply Hfg.
             ++ intros n'. repeat case_bool_decide; try done; try lra; subst.
                ** rewrite H1 in H5. destruct H5 as [?[??]]. subst.
                   apply encode_inv_Some_nat in H3. lia.
                ** set_solver.
                ** set_solver.
                ** set_solver.
                ** set_solver.
        * exists l'. repeat split; try done.
          -- intros. naive_solver.
          -- intros [?[??]]. rewrite H1. subst. eexists _; split; first done.
             rewrite Nat.le_succ_r in H5. destruct H5; try lia.
             exfalso. apply H4. apply encode_inv_Some_nat in H3. rewrite -H3 in H0.
             apply encode_nat_inj in H0. naive_solver.
          -- rewrite plus_zero_r. done.
      + exists l'. repeat split; try done.
        * intros. naive_solver.
        * elim. intros ?[??]. subst. rewrite H1. eexists _; split; first done.
          rewrite Nat.le_succ_r in H4. destruct H4; first done.
          rewrite -H0 in H3. by rewrite encode_inv_encode_nat in H3.
        * by rewrite plus_zero_r.
  Qed.

  Lemma SeriesC_filter_finite_1_bounds `{Countable A} (M:nat) (f:A -> R) (g: fin M -> R) h r:
    Inj eq eq h -> (0 < M)%nat -> (0<r)-> (∀ a: A, 0 <= f a <= r) -> (∀ b: fin M, 0 <= g b <= r) ->
    (∀ (a : A) (b : fin M), a = h b → f a <= g b) ->
    SeriesC (λ a : A, if bool_decide (∃ y : fin M, a = h y) then f a else 0) <= SeriesC g.
  Proof.
    intros Hinj Hm Hr Hf Hg Hfg.
    apply (Rmult_le_reg_r (/r)).
    { rewrite -Rdiv_1_l. apply Rdiv_lt_0_compat; lra. }
    rewrite -!SeriesC_scal_r.
    erewrite (SeriesC_ext _ (λ x : A, (if bool_decide (∃ y : fin M, x = h y) then (λ x, f x / r) x else 0))); last first.
    { intros. case_bool_decide; lra. }
    apply SeriesC_filter_finite_1; try done.
    - intros; split.
      + apply Rcomplements.Rdiv_le_0_compat; try lra. naive_solver.
      + rewrite Rcomplements.Rle_div_l; last naive_solver. rewrite Rmult_1_l. naive_solver.
    - intros; split.
      + apply Rcomplements.Rdiv_le_0_compat; try lra. naive_solver.
      + rewrite Rcomplements.Rle_div_l; last naive_solver. rewrite Rmult_1_l. naive_solver.
    - intros. rewrite Rdiv_def. apply Rmult_le_compat_r; last naive_solver.
      rewrite -Rdiv_1_l. apply Rcomplements.Rdiv_le_0_compat; try lra.
  Qed.
    

  Lemma SeriesC_filter_finite_1' (N M:nat) (f:fin N -> R) (g: fin M -> R) h:
    Inj eq eq h -> (0 < M <= N)%nat -> (∀ a: fin N, 0 <= f a <= 1) -> (∀ b: fin M, 0 <= g b <= 1) ->
    (∀ (a : fin N) (b : fin M), a = h b → f a <= g b) ->
    SeriesC (λ a : fin N, if bool_decide (∃ y : fin M, a = h y) then f a else 0) <= SeriesC g.
  Proof.
    intros Hinj Hineq Hf Hg Hfg.
    apply SeriesC_filter_finite_1; try done.
    lia.
  Qed.

  Lemma SeriesC_filter_finite_2 (N M:nat) (f:fin N -> R) h:
    Inj eq eq h -> (0 < M <= N)%nat -> (∀ a: fin N, 0 <= f a <= 1) ->
    SeriesC (λ a : fin N, if bool_decide (∃ y : fin M, a = h y) then 0 else f a) <= (N-M)%nat.
  Proof.
    intros Hinj Hineq Hf. rewrite minus_INR; last naive_solver.
    rewrite Rcomplements.Rle_minus_r.
    replace (INR M) with (SeriesC (λ a : fin N, if bool_decide (∃ y : fin M, a = h y) then 1 else 0)).
    - rewrite -SeriesC_plus; try apply ex_seriesC_finite.
      trans (SeriesC (λ _:fin N, 1)).
      + apply SeriesC_le; last apply ex_seriesC_finite.
        intros n; case_bool_decide; try lra.
        rewrite Rplus_0_r; naive_solver.
      + rewrite SeriesC_finite_mass fin_card. lra.
    - replace (INR M) with (SeriesC (λ _:fin M, 1)); last (rewrite SeriesC_finite_mass fin_card; lra).
      apply Rle_antisym.
      + apply SeriesC_filter_finite_1'; try done; intros; lra.
      + etrans; last first.
        * eapply SeriesC_le_inj; last apply ex_seriesC_finite.
          -- intros. case_bool_decide; lra.
          -- intros ???. instantiate (2 := (λ x, (Some (h x)))). simpl.
             intros H1 H2. rewrite -H1 in H2. inversion H2. by apply Hinj.
        * apply SeriesC_le; last apply ex_seriesC_finite.
          intros n. split; first lra.
          simpl. case_bool_decide; first done.
          exfalso; naive_solver.
  Qed.
  
End Inj_finite.


Ltac series_solver_partial :=
  match goal with
  | |- 0 <= SeriesC _ => apply SeriesC_ge_0'
  | |- SeriesC _ = SeriesC _ => apply SeriesC_ext
  end.

Ltac series := repeat (series_solver_partial || real_solver_partial).

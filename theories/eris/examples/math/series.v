From clutch.eris.examples.math Require Import prelude.
From clutch.eris Require Import infinite_tape.
Import Hierarchy.
Set Default Proof Using "Type*".
#[local] Open Scope R.

(** Series shifting lemmas *)

(* I need either ex_SeriesC or maybe nn *)
Lemma SeriesC_nat_shift {f : nat → R} (Hex :  Series.ex_series f) : SeriesC f = f 0%nat + SeriesC (f ∘ S).
Proof.
  rewrite SeriesC_nat.
  rewrite SeriesC_nat.
  rewrite Series.Series_incr_1; last done.
  f_equal.
Qed.

Lemma SeriesC_nat_shift_rev {f : nat → R} (Hex :  Series.ex_series f) : SeriesC (f ∘ S) = - f 0%nat + SeriesC f.
Proof. pose proof (SeriesC_nat_shift Hex); lra. Qed.
(* Proof. have ? := SeriesC_nat_shift Hex. lra. Qed. *)

Lemma ex_SeriesC_nat_shift {f : nat → R} : ex_seriesC f → ex_seriesC (f ∘ S).
Proof.
  intro H.
  apply ex_seriesC_nat in H.
  apply Series.ex_series_incr_1 in H.
  apply ex_seriesC_nat in H.
  apply H.
Qed.

Lemma ex_SeriesC_nat_shiftN_l {f : nat → R} (N : nat) : ex_seriesC (f ∘ (fun n => (n - N))%nat) → ex_seriesC f.
Proof.
  revert f.
  induction N as [|N IH].
  { intros f.
    replace (f ∘ λ n : nat, (n - 0)%nat) with f; [done|].
    by rewrite /compose//=; apply functional_extensionality; intros ?; rewrite Nat.sub_0_r.
  }
  intros f.
  replace ((f ∘ λ n : nat, (n - S N)%nat)) with (((f ∘ (λ n : nat, (n - 1)%nat)) ∘ λ n : nat, (n - N)%nat)).
  { intros Hf.
    specialize IH with (f ∘ (λ n : nat, (n - 1)%nat)).
    apply IH in Hf.
    apply ex_SeriesC_nat_shift in Hf.
    apply ex_SeriesC_nat_shift in Hf.
    suffices H : Series.ex_series f by apply ex_seriesC_nat in H.
    apply Series.ex_series_incr_1.
    apply ex_seriesC_nat.
    eapply ex_seriesC_ext; [|apply Hf].
    intros n.
    rewrite /compose//=.
  }
  { rewrite /compose//=; apply functional_extensionality; intros ?.
    f_equal.
    lia.
  }
Qed.

Lemma ex_SeriesC_nat_shiftN_r {f : nat → R} (N : nat) : ex_seriesC (f ∘ (fun n => (n + N))%nat) → ex_seriesC f.
Proof.
  induction N as [|N IH].
  { replace (f ∘ λ n : nat, (n + 0)%nat) with f; [done|].
    by rewrite /compose//=; apply functional_extensionality; intros ?; rewrite Nat.add_0_r.
  }
  { intros Hf.
    apply IH.
    suffices H : Series.ex_series (f ∘ λ n : nat, (n + N)%nat) by apply ex_seriesC_nat in H.
    apply Series.ex_series_incr_1.
    apply ex_seriesC_nat.
    eapply ex_seriesC_ext; [|apply Hf].
    intros n.
    rewrite /compose//=.
    f_equal.
    lia.
  }
Qed.


Lemma ex_SeriesC_nat_shiftN_r' {f : nat → R} (N : nat) : ex_seriesC f → ex_seriesC (f ∘ (fun n => (n + N))%nat).
Proof.
  induction N as [|N IH].
  { replace (f ∘ λ n : nat, (n + 0)%nat) with f; [done|].
    by rewrite /compose//=; apply functional_extensionality; intros ?; rewrite Nat.add_0_r.
  }
  { intros Hf.
    replace (f ∘ λ n : nat, (n + S N)%nat) with ((f ∘ λ n : nat, (n + N)%nat) ∘ S).
    2: { apply functional_extensionality. intros ?. simpl. f_equal. lia. }
    rewrite -ex_seriesC_nat.
    rewrite -Series.ex_series_incr_1.
    rewrite ex_seriesC_nat.
    apply IH.
    apply Hf.
  }
Qed.


Lemma SeriesC_term_le {h : nat → R} (Hh : ∀ n, 0 <= h n) (Hex : ex_seriesC h) :
  ∀ n, h n <= SeriesC h.
Proof.
  intros n.
  have Heq : SeriesC h = SeriesC (λ m, if bool_decide (m = n) then h m else 0) +
                         SeriesC (λ m, if bool_decide (m ≠ n) then h m else 0).
  { rewrite -SeriesC_plus.
    - apply SeriesC_ext.
      intros m. case_bool_decide; case_bool_decide; try lra; try (exfalso; auto).
    - apply ex_seriesC_singleton_dependent.
    - apply (ex_seriesC_le _ h); auto.
      intros m. split; case_bool_decide; auto; lra.
  }
  rewrite Heq.
  rewrite SeriesC_singleton_dependent.
  have Hrest : 0 <= SeriesC (λ m, if bool_decide (m ≠ n) then h m else 0).
  { apply SeriesC_ge_0' => m. case_bool_decide; auto. lra. }
  lra.
Qed.

Lemma ex_seriesC_mult {f g : nat → R} (Hf : ∀ n : nat, 0 <= f n) (Hg : ∀ n : nat, 0 <= g n) :
  ex_seriesC f → ex_seriesC g → ex_seriesC (fun n => f n * g n).
Proof.
  intros Hexf Hexg.
  apply (ex_seriesC_le _ (fun n => (SeriesC g) * f n)).
  { intros n. split.
    - apply Rmult_le_pos; auto.
    - rewrite Rmult_comm. apply Rmult_le_compat_r; auto. apply SeriesC_term_le; done.
  }
  by apply ex_seriesC_scal_l.
Qed.

Section TailSeries.

Definition TailSeries (F : nat → R) (M : nat) :=
  Series.Series (F ∘ (fun n => n + (S M))%nat).

(* TODO: What other hypotheses do we need here? Existence? Nonnegativity? *)
(* Key lemma in UnifomConverge_Series *)
Definition TailSeries_eq {F M} :
  Series.ex_series F →
  TailSeries F M = (minus (Series.Series F) (sum_n F M)).
Proof.
  intro H.
  rewrite /TailSeries/minus//=/plus//=/opp//=.
  symmetry.
  rewrite (@Series.Series_incr_n _ (S M)); [| lia | done].
  rewrite -sum_n_Reals -pred_Sn Rplus_comm -Rplus_assoc Rplus_opp_l Rplus_0_l.
  rewrite /compose//=.
  f_equal. apply functional_extensionality; intros ?. do 2 f_equal.
  lia.
Qed.

End TailSeries.


Lemma Le_Nat_sum (N : nat) (v : R) : SeriesC (λ n : nat, if bool_decide (n ≤ N) then v else 0) = (N + 1)* v.
Proof.
  rewrite SeriesC_nat_bounded'.
  induction N.
  { rewrite //=. lra. }
  replace ((S N + 1) * v) with ((N + 1) * v + v) by (rewrite S_INR; lra).
  rewrite -IHN //=.
  rewrite Rplus_assoc. f_equal. rewrite Rplus_comm.
  f_equal.
  suffices HLenFold : ∀ L, foldr (Rplus ∘ (λ _ : nat, v) ∘ fin_to_nat) 0 L = length L *  v.
  { rewrite HLenFold.
    rewrite HLenFold.
    rewrite fmap_length.
    rewrite fin.length_enum_fin.
    rewrite fmap_length.
    rewrite fmap_length.
    by rewrite fin.length_enum_fin.
  }
  clear IHN.
  intros M L.
  induction L.
  { simpl. lra. }
  { rewrite foldr_cons.
    rewrite IHL.
    rewrite cons_length.
    rewrite S_INR.
    rewrite //=.
    lra.
  }
Qed.

Lemma even_pow_neg {x : R} {n : nat} : Zeven n → (- x) ^ n = x ^ n.
Proof.
  intro H.
  destruct (Zeven_ex _ H).
  replace n with (Z.to_nat (Z.of_nat n)); last first.
  { rewrite Nat2Z.id. done. }
  rewrite H0.
  rewrite Z2Nat.inj_mul; last first.
  { pose proof (pos_INR n); lia. }
  (* { have ? := pos_INR n. lia. } *)
  { done. }
  rewrite pow_mult.
  rewrite pow_mult.
  replace ((- x) ^ Z.to_nat 2) with ((x) ^ Z.to_nat 2); last first.
  { simpl. lra. }
  done.
Qed.

Lemma not_even_pow_neg {x : R} {n : nat} : ¬ Zeven n → (- x) ^ n = - x ^ n.
Proof.
  intro H.
  destruct (Zeven_odd_dec n); first (by exfalso).
  destruct (Zodd_ex _ z).
  replace n with (Z.to_nat (Z.of_nat n)); last first.
  { rewrite Nat2Z.id. done. }
  rewrite H0.
  rewrite Z2Nat.inj_add; try done.
  2: {
    apply Z.mul_nonneg_nonneg; first lia.
    destruct n. { by simpl in z. }
    pose proof (pos_INR n); lia.
    (* have ? := pos_INR n. lia. *)
  }
  rewrite pow_add.
  rewrite pow_add.
  rewrite Ropp_mult_distr_r.
  f_equal.
  2: { simpl. lra. }
  rewrite Z2Nat.inj_mul; last first.
  { pose proof (pos_INR n); lia. }
  (* { have ? := pos_INR n. lia. } *)
  { done. }
  rewrite pow_mult.
  rewrite pow_mult.
  replace ((- x) ^ Z.to_nat 2) with ((x) ^ Z.to_nat 2); last first.
  { simpl. lra. }
  done.
Qed.


Lemma Geo_ex_SeriesC {𝛾 : R} (H𝛾 : 0 <= 𝛾 <= 1) : ex_seriesC (λ x : nat, 𝛾 ^ x * (1 - 𝛾)).
Proof.
  destruct H𝛾.
  destruct H0.
  { apply ex_seriesC_scal_r.
    have H𝛾' : Rabs 𝛾 < 1.
    { rewrite Rabs_pos_eq; lra. }
    have H' := Series.ex_series_geom 𝛾 H𝛾'.
    by rewrite ex_seriesC_nat in H'.
  }
  apply (ex_seriesC_ext (fun _ : nat => 0%R)).
  { intros ?; rewrite H0; lra. }
  { apply ex_seriesC_0. }
Qed.

Lemma ex_seriesC_finite_dec (M : nat) (F : nat → R) :
  ex_seriesC (λ x : nat, if bool_decide (x ≤ M) then F x else 0).
Proof. apply ex_seriesC_nat_bounded. Qed.

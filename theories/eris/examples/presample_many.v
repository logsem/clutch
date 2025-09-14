From clutch.eris Require Export adequacy.
From clutch.eris Require Export eris error_rules receipt_rules.

Set Default Proof Using "Type*".

Local Open Scope R_scope.

Section presample_many.
  Context `{!erisGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.

  Notation list_fixed_len A k := { ls : list A | length ls = k}.

  Definition cons_length {A k} (x : A) (ls: list_fixed_len A k) : list_fixed_len A (S k).
    exists (x :: `ls).
    destruct ls as (?&Hlen).
    rewrite /= Hlen //.
  Defined.

  Lemma cons_length_bij {A} k :
    Bij (λ nns' : A * list_fixed_len A k, cons_length nns'.1 nns'.2).
  Proof.
    split.
    - intros (a1&l1) (a2&l2) => Heq.
      rewrite /cons_length//= in Heq.
      inversion Heq. f_equal.
      apply proj1_sig_inj; auto. apply _.
    - intros (l&Hpf).
      destruct l as [| a l].
      { simpl in Hpf; lia. }
      simpl in Hpf.
      inversion Hpf as [Hpf'].
      set (l' := (exist _ _ Hpf' : list_fixed_len A k)).
      exists (a, l').
      apply proj1_sig_inj; auto; apply _.
  Qed.

  Lemma SeriesC_list_fixed_len_cons `{Finite A} (k: nat) (f : list_fixed_len A (S k) → R):
    (∀ ns, 0 <= f ns)%R →
    SeriesC f =
    SeriesC (λ n : A, SeriesC (λ ns' : list_fixed_len A k, f (cons_length n ns'))).
  Proof.
    intros Hnonneg.
    rewrite -(fubini_pos_seriesC_prod_lr (λ nns', f (cons_length (fst nns') (snd nns')))); auto.
    - symmetry. etransitivity; last eapply (SeriesC_eq_bij (λ nns', cons_length (fst nns') (snd nns')) f); auto.
      * eapply SeriesC_Countable_instance_irrel; eauto.
        ** eapply ex_seriesC_Countable_instance_irrel; eauto.
           eapply @ex_seriesC_finite.
      * apply cons_length_bij.
      * apply ex_seriesC_finite.
    - eapply ex_seriesC_Countable_instance_irrel; eauto.
      apply ex_seriesC_finite.
  Qed.


  Lemma wp_presample_many_adv_comp (N : nat) z E e α Φ ns (k : nat) (ε1 : R) (ε2 : { ls : list (fin (S N)) | length ls = k} -> R) :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (forall n, (0 <= ε2 n)%R) ->
    SeriesC (λ ns', (1 / (S N) ^ k) * ε2 ns')%R = ε1 →
    α ↪ (N; ns) ∗
      ↯ ε1 ∗
      (∀ (ns' : {ls : list (fin (S N)) | length ls = k }),
             ↯ (ε2 ns') ∗ α ↪ (N; ns ++ `ns') -∗ WP e @ E {{ Φ }})
      ⊢ WP e @ E {{ Φ }}.
  Proof.
    revert ns ε1 ε2.
    induction k.
    - iIntros (ns ε1 ε2 ? Hnval Hnneg Hexp_pres) "(Hα&Hε1&Hwp)".
      assert (Hlen : length (nil : list (fin (S N))) = O) by auto.
      set (ns' := exist (λ ls : list (fin (S N)), length ls = O) _ (vec_to_list_length [# ])).
      iApply ("Hwp" $! ns').
      rewrite /= app_nil_r; iFrame.
      rewrite SeriesC_finite_foldr /enum//= in Hexp_pres.
      field_simplify in Hexp_pres.
      subst; auto.
    - iIntros (ns ε1 ε2 ? Hnval Hnneg Hexp_pres) "(Hα&Hε1&Hwp)".
      set (ε2' := fun n : fin (S N) =>
                    SeriesC (λ ns' : list_fixed_len (fin (S N)) k, (1 / S N ^ k * ε2 (cons_length n ns'))%R)).
      assert (∀ k', ∀ ns : list_fixed_len (fin (S N)) (S k), 0 <= 1 / S N ^ k' * ε2 ns).
      {
        intros.
        apply Rmult_le_pos; auto.
        apply Rcomplements.Rdiv_le_0_compat; first by lra.
        apply pow_lt. apply lt_0_INR. lia.
      }
      assert (∀ n, ∀ k', ∀ x : list_fixed_len (fin (S N)) k, 0 <= 1 / S N ^ k' * ε2 (cons_length n x)).
      {
        intros.
        apply Rmult_le_pos; auto.
        apply Rcomplements.Rdiv_le_0_compat; first by lra.
        apply pow_lt. apply lt_0_INR. lia.
      }
      assert (Hexp_pres':
               SeriesC (λ ns' : list_fixed_len (fin (S N)) (S k), (1 / S N ^ S k * ε2 ns')%R) =
               SeriesC (λ n : fin (S N), 1 / S N * ε2' n)).
      {
        rewrite /ε2'.
        setoid_rewrite <-SeriesC_scal_l.
        rewrite SeriesC_list_fixed_len_cons //.
        * eapply SeriesC_ext => n.
          eapply SeriesC_ext => ns'.
          rewrite (pow_add _ 1).
          field. split.
          ** cut (0 < S N ^ k); try nra.
             apply pow_lt. apply lt_0_INR. lia.
          ** cut (0 < S N); try nra.
             apply lt_0_INR. lia.
      }
      rewrite -Hexp_pres Hexp_pres'.
      wp_apply (wp_presample_adv_comp _ _ _ _ _ _ _ _ ε2' with "[$Hα $Hε1 Hwp]"); auto.
      {
        intros ?. rewrite /ε2'.
        apply SeriesC_ge_0'.
        intros. auto.
      }
      iIntros (n) "(Hε2&Hα)".
      iApply (IHk _ _ (λ ns, ε2 (cons_length n ns))) ; auto.
      iFrame "Hα Hε2".
      iIntros.
      iApply ("Hwp" $! (cons_length n ns')).
      iEval (rewrite {2}/cons_length//=).
      rewrite -app_assoc /= //.
  Qed.
End presample_many.

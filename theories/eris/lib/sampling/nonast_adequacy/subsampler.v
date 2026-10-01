From clutch.eris Require Import eris.
From clutch.eris.lib.sampling Require Import nonast_distribution_adequacy.

Section subsampler. 

  Definition μ : val → R := λ v, if bool_decide (v = #true) then (1/2)%R else 0%R.
  Definition μ_div : R := 1 - SeriesC μ.
  Definition μ_mass := SeriesC μ.
  Lemma μ_div_half : (μ_div = 1/2)%R.
  Admitted.

  Definition subsampler : expr := if: (rand #1 = #1) then #true else (rec: "loop" <> := "loop" #()) #().

  Lemma μmass_μv_μdiv v : (μ_mass - μ v + μ_div = 1 - μ v)%R.
  Admitted. 

  Lemma twp_subsampler_spec `{erisGS Σ} v :
    [[{ ↯ (1 - μ v) }]] subsampler [[{ w, RET w; ⌜ w = v ⌝ }]].
  Proof.
    destruct (bool_decide (v = #true)) eqn:Heq.
    - unfold μ. 
      rewrite Heq. simpl. 
      assert (1 - (1 / 2) = 1 / 2)%R as -> by lra.
      iIntros (Φ) "Herr HΦ".
      unfold subsampler.
      wp_apply (twp_rand_err_nat _ _ 0).      
      iSplitL "Herr".
      { by rewrite Rdiv_1_l. }
      iIntros (x(Hle&Hneq)).
      wp_pures. 
      rewrite bool_decide_eq_true_2; last first.
      { f_equal. apply Nat.le_1_r in Hle as [-> | ->]; done. }
      wp_pures.
      apply bool_decide_eq_true_1 in Heq.
      by iApply "HΦ". 
    - unfold μ. 
      rewrite Heq. simpl.
      iIntros (Φ) "Herr". 
      by iDestruct (ec_contradict with "Herr") as "%"; first lra.
  Qed. 

  Lemma wp_subsampler `{erisGS Σ} ε D :
    (0 <= ε)%R →
    (∀ (v : val), 0 <= D v <= 1)%R →
    SeriesC (λ (v : val), D v * μ v)%R = ε →
    ⊢ {{{ ↯ ε }}} subsampler {{{ v, RET v; ↯ (D v)}}}.
  Proof. 
    iIntros (Hpos Hbound Heq Φ) "!>Herr HΦ".
    iPoseProof (ec_valid with "Herr") as "%Hbounds".
    rewrite -Heq.
    unfold subsampler.
    set (ε2 := λ n, match n with
                    | S 0 => (D #true)%R
                    | _ => 0%R
                    end).
    wp_apply (wp_rand_exp_nat _ _ _ ε2 with "[$]"); last first.
    - iIntros (?) "(%Hlt & Herr)".
      apply Nat.le_1_r in Hlt as [-> | ->].
      + wp_pures.
        iClear "Herr HΦ".
        iLöb as "IH".
        by wp_pures.
      + wp_pures.
        by iApply "HΦ".
    - erewrite (SeriesC_ext _ (λ v, if bool_decide (v = #true) then ((1/2) * (D v))%R else 0%R)); last first.
      + intros v. unfold μ. destruct (bool_decide (v = #true)); lra.
      + rewrite SeriesC_singleton_dependent.
        erewrite (SeriesC_ext _ (λ v, if bool_decide (v = 1) then ((1/2) * (D #true))%R else 0%R)); last first.
        * intros n. destruct (bool_decide (n ≤ Z.to_nat 1)) eqn:Hlt.
          -- apply bool_decide_eq_true_1 in Hlt. apply Nat.le_1_r in Hlt as [-> | ->].
             ++ simpl. by rewrite Rmult_0_r.
             ++ simpl. lra.
          -- apply bool_decide_eq_false_1 in Hlt.
             assert (n ≠ 1) as Hneq by lia.
             rewrite bool_decide_false; done.
        * by rewrite SeriesC_singleton.
    - destruct n; simpl.
      + simpl. lra.
      + destruct n; simpl; last lra.
        done.
  Qed. 

End subsampler.

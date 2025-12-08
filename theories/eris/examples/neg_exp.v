From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt RInt_analysis AutoDerive RInt_gen.
From clutch.eris Require Import infinite_tape.
From clutch.eris.examples Require Import lazy_real max_lazy_real indicators real_decr_trial.
Set Default Proof Using "Type*".
#[local] Open Scope R.

Section pmf.

  Local Definition NegExp_ρ0 (x : R) : R :=
    Iverson (Rle 0%R) x * exp (-x)%R.

  Theorem NegExp_ρ0_not_supp {x} (H : Rlt x 0%R) : NegExp_ρ0 x = 0.
  Proof. rewrite /NegExp_ρ0 Iverson_False //=; [lra|lra]. Qed.

  Theorem NegExp_ρ0_supp {x} (H : Rlt 0%R x) : NegExp_ρ0 x = exp (-x)%R.
  Proof. rewrite /NegExp_ρ0 Iverson_True //=; [lra|lra]. Qed.

  Local Definition NegExp_ρ (L : nat) (x : R) : R :=
    Iverson (le 0) L * NegExp_ρ0 (x - INR L).

  Theorem NegExp_ρ_not_supp {x L} (H : lt L 0) : NegExp_ρ L x = 0.
  Proof. rewrite /NegExp_ρ Iverson_False //=; [lra|lia]. Qed.

  Theorem NegExp_ρ_supp {x L} (H : le 0 L) : NegExp_ρ L x = NegExp_ρ0 (x - INR L).
  Proof. rewrite /NegExp_ρ Iverson_True //=; lra. Qed.

End pmf.

Section credits.
  Import Hierarchy.

  Definition NegExp_CreditV (F : R → R) (L : nat) : R :=
    RInt_gen (fun x : R => F x * NegExp_ρ L x) (at_point 0%R) (Rbar_locally Rbar.p_infty).

  Lemma NegExp_ρ0_nn {x} : 0 <= NegExp_ρ0 x.
  Proof.
    rewrite /NegExp_ρ0.
    apply Rmult_le_pos; first apply Iverson_nonneg.
    apply Rexp_nn.
  Qed.

  Lemma NegExp_ρ_nn {x L} : 0 <= NegExp_ρ x L.
  Proof.
    rewrite /NegExp_ρ.
    apply Rmult_le_pos; first apply Iverson_nonneg.
    apply NegExp_ρ0_nn.
  Qed.


  Theorem NegExp_ρ0_ex_RInt {F : R → R} {a b} (Hex : ∀ b : R, ex_RInt F a b) :
    ex_RInt NegExp_ρ0 a b.
  Proof.
    rewrite /NegExp_ρ0.
    apply ex_RInt_mult.
    { apply ex_RInt_Iverson_le. }
    apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
    intros ??.
    eapply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
    auto_derive. OK.
  Qed.

  Theorem NegExp_ρ_ex_RInt {L a b} :
    ex_RInt (NegExp_ρ L) a b.
  Proof.
    rewrite /NegExp_ρ0.
    apply ex_RInt_mult.
    { apply ex_RInt_const. }
    rewrite /NegExp_ρ0.
    apply ex_RInt_mult.
    { replace (λ y : R, Iverson (Rle 0) (y - L))
         with (λ y : R, scal 1 (Iverson (Rle 0) (1 * y + - L))); last first.
      { funexti. rewrite /scal//=/mult//= Rmult_1_l. f_equal; OK. }
      apply (ex_RInt_comp_lin (Iverson (Rle 0)) 1 (-L) a b).
      apply ex_RInt_Iverson_le. }
    apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
    intros ??.
    eapply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
    auto_derive. OK.
  Qed.

  Lemma NegExp_CreditV_nn {F : R -> R} {M} (Hnn : ∀ r, 0 <= F r <= M) {L : nat} (H : ∀ b, ex_RInt F 0 b) :
    0 <= NegExp_CreditV F (L + 1).
  Proof.
    rewrite /NegExp_CreditV.
    apply RInt_gen_pos_strong.
    { intros ?. apply Rmult_le_pos; first apply Hnn. apply NegExp_ρ_nn. }
    { intros b. apply ex_RInt_mult; [apply H|apply NegExp_ρ_ex_RInt]. }
    { intros b Hb.
      apply RInt_ge_0; try done.
      { apply ex_RInt_mult; [apply H|apply NegExp_ρ_ex_RInt]. }
      { intros ??.  apply Rmult_le_pos; first apply Hnn. apply NegExp_ρ_nn. }
    }

    (* We need stronger assumptions on F here.

       Split at L (for NegExp_ρ)
       Split at every discontinuity of F.
       Then on all intervals, it is the multiplication of constant functions.
       Comparison not needed.

    *)

    (*
    apply (@ex_RInt_gen_Ici_compare_strong 0 (λ x : R, M * NegExp_ρ (L + 1) x)).
    { (* OK this might not be exactly right (might need to split again at L) but something will work for this goal *)
      (*
      intros ??.
      apply (@Continuity.continuous_mult R_UniformSpace R_AbsRing).
      { apply Continuity.continuous_const. }
      rewrite /NegExp_ρ.
      apply (@Continuity.continuous_mult R_UniformSpace R_AbsRing).
      { apply Continuity.continuous_const. }
      rewrite /NegExp_ρ0.
      admit.
      *)
    admit.}
    { intros ??. (* Require that F be continuous *) admit. }
    { intros ??. (* OK *) admit. }
    { admit. }
    *)
  Admitted.

  Theorem NegExp_CreditV_ub {F L M} (HF : ∀ x, 0 <= F x <= M) : NegExp_CreditV F L <= M.
  Proof.
    rewrite /NegExp_CreditV.
    (* Bounded above by M times the body *)
    (* The integral of the body is 1 (I think). If not just change the constant. *)
  Admitted.


  Local Definition hx (F : R → R) (x : R) (L : nat) : nat → R := fun z =>
    Iverson Zeven z * F (x + INR L) +
    Iverson (not ∘ Zeven) z * NegExp_CreditV F (L + 1).

  Local Definition g (F : R -> R) (L : nat) : R -> R := fun x =>
    RealDecrTrial_CreditV (hx F x L) 0 x.

  Lemma hx_nonneg {F M xr L} (Hnn : ∀ r, 0 <= F r <= M) (Hb : ∀ b : R, ex_RInt F 0 b) : ∀ n : nat, 0 <= hx F xr L n.
  Proof.
    rewrite /hx.
    intros ?.
    apply Rplus_le_le_0_compat; (apply Rmult_le_pos; [apply Iverson_nonneg|]).
    { apply Hnn. }
    { eapply NegExp_CreditV_nn; auto. }
  Qed.

  Lemma g_nonneg {F M L r} (Hnn : ∀ r, 0 <= F r <= M) (Hr : 0 <= r <= 1) (Hb : ∀ b : R, ex_RInt F 0 b) : 0 <= g F L r.
  Proof.
    rewrite /g.
    apply CreditV_nonneg; auto.
    intros ?.
    eapply hx_nonneg; auto.
  Qed.

  Local Lemma g_ex_RInt {F L M} (Hbound : ∀ x, 0 <= F x <= M) (Hb : ∀ a b : R, ex_RInt F a b) : ex_RInt (g F L) 0 1.
  Proof.
    rewrite -ex_RInt_dom /ex_RInt /g /RealDecrTrial_CreditV.
    replace (λ x : R, Iverson (Ioo 0 1) x * SeriesC (λ n : nat, RealDecrTrial_μ x 0 n * hx F x L n))
       with (λ x : R, Series.Series (λ n : nat, Iverson (Ioo 0 1) x * (RealDecrTrial_μ x 0 n * hx F x L n))); last first.
    { apply functional_extensionality; intros ?.
      rewrite -SeriesC_scal_l SeriesC_Series_nat. done. }
    pose s : nat → R → R_CompleteNormedModule :=
      fun M x => sum_n (λ n : nat, Iverson (Ioo 0 1) x * (RealDecrTrial_μ x 0 n * hx F x L n)) M.
    pose h : nat → R_CompleteNormedModule :=
      fun x => (RInt (λ x0 : R, sum_n (λ n : nat, Iverson (Ioo 0 1) x0 * (RealDecrTrial_μ x0 0 n * hx F x0 L n)) x) 0 1).
    have HSLim : filterlim s eventually
      (locally (λ x : R, Series.Series (λ n : nat, Iverson (Ioo 0 1) x * (RealDecrTrial_μ x 0 n * hx F x L n)))).
    { rewrite /s.
      apply (UniformConverge_Series (fun n => 2 * M * / (fact (n - 0)%nat))).
      { replace (λ n : nat, 2 * M * / fact (n - 0)) with (λ n : nat, / fact n * (2 * M)); last first.
        { funexti. rewrite Rmult_comm. repeat f_equal. OK. }
        apply Series.ex_series_scal_r.
        apply ex_exp_series.
      }
      intros x n.
      rewrite Rabs_right; last first.
      { apply Rle_ge. rewrite /Iverson; case_decide.
        { rewrite Rmult_1_l. apply Rmult_le_pos; [apply RealDecrTrial_μnn|].
          { rewrite /Ioo in H. rewrite Rmin_left in H; OK. rewrite Rmax_right in H; OK. }
          rewrite /hx. apply Rplus_le_le_0_compat; apply Rmult_le_pos;
            [apply Iverson_nonneg | apply Hbound | apply Iverson_nonneg | ].
          eapply NegExp_CreditV_nn; OK. }
        OK. }
      rewrite /Iverson. case_decide; last first.
      { rewrite Rmult_0_l.
        apply Rle_mult_inv_pos; last apply INR_fact_lt_0.
        have ? := Hbound 0. lra.
      }
      rewrite /Ioo in H. rewrite Rmin_left in H; OK. rewrite Rmax_right in H; OK.
      rewrite Rmult_1_l Rmult_comm.
      have Hhx : hx F x L n <= 2 * M.
      { rewrite /hx.
        apply (Rle_trans _ (M + M)).
        { apply Rplus_le_compat.
          { rewrite -(Rmult_1_l M).
            apply Rmult_le_compat; OK.
            { apply Iverson_nonneg. }
            { apply Hbound. }
            { apply Iverson_le_1. }
            { apply Hbound. }
          }
          { rewrite -(Rmult_1_l M).
            apply Rmult_le_compat; OK.
            { apply Iverson_nonneg. }
            { eapply NegExp_CreditV_nn; OK. }
            { apply Iverson_le_1. }
            { apply NegExp_CreditV_ub; OK. }
          }
        }
        lra. }
      apply Rmult_le_compat.
      { eapply hx_nonneg; OK. }
      { apply RealDecrTrial_μnn. OK. }
      { OK. }
      rewrite /RealDecrTrial_μ /Iverson. case_decide; last first.
      { rewrite Rmult_0_l. left. apply Rinv_0_lt_compat. apply INR_fact_lt_0. }
      rewrite Rmult_1_l /RealDecrTrial_μ0. repeat rewrite Rdiv_def.
      replace (n - 0 + 1)%nat with (S (n - 0)) by OK.
      rewrite fact_simpl mult_INR Rinv_mult -Rmult_assoc -Rmult_minus_distr_r.
      rewrite -{2}(Rmult_1_l (/ fact (n - 0))).
      apply Rmult_le_compat.
      { apply Rle_0_le_minus. rewrite -(Rmult_1_l (x ^ (n - 0))) Rmult_comm.
        apply Rmult_le_compat; [| apply pow_le; OK | | ].
        { rewrite -(Rmult_1_l (/ _)). apply Rle_mult_inv_pos; OK. apply pos_INR_S. }
        { rewrite -Rinv_1. apply Rinv_le_contravar; OK. rewrite -INR_1. apply le_INR. OK. }
        rewrite -(Rmult_1_l (x ^ (n - 0))) -tech_pow_Rmult.
        apply Rmult_le_compat_r; OK. apply pow_le; OK. }
      { rewrite -(Rmult_1_l (/ _)). apply Rle_mult_inv_pos; OK. apply INR_fact_lt_0. }
      { have ? : 0 <= x ^ S (n - 0) * / S (n - 0).
        { apply Rle_mult_inv_pos; OK. { apply pow_le; OK. } apply pos_INR_S. }
        suffices ? : x ^ (n - 0) <= 1 by OK.
        rewrite -(pow1 (n - 0)). apply pow_incr; OK. }
      apply Rinv_le_contravar; OK. apply INR_fact_lt_0.
    }
    have HSInt : ∀ N : nat, is_RInt (s N) 0 1 (h N).
    { rewrite /s /h. intro N'.
      apply (@RInt_correct R_CompleteNormedModule).
      apply ex_RInt_sum_n. intros n.
      rewrite ex_RInt_dom.
      apply ex_RInt_mult.
      { apply RealDecrTrial_μ_ex_RInt. }
      { rewrite /hx.
        apply (ex_RInt_plus (V := R_CompleteNormedModule)).
        2: { apply ex_RInt_const. }
        apply (ex_RInt_mult).
        { apply ex_RInt_const. }
        replace (λ y : R, F (y + L)) with  (λ y : R, scal 1 (F (1 * y + L))).
        2: { funexti. rewrite /scal//=/mult//= Rmult_1_l; f_equal; OK. }
        apply (ex_RInt_comp_lin F 1 L 0 1).
        repeat rewrite Rmult_1_l.
        apply Hb.
      }
    }
    destruct (@filterlim_RInt nat R_CompleteNormedModule s 0 1 eventually eventually_filter
      (λ x : R, Series.Series (λ n : nat, Iverson (Ioo 0 1) x * (RealDecrTrial_μ x 0 n * hx F x L n)))
      h HSInt HSLim) as [IF [HIf1 HIf2]].
    by exists IF.
  Qed.


  Local Theorem g_expectation {F L M} (Hf : ∀ x, 0 <= F x <= M) (Hex : ∀ (a b : R), ex_RInt F a b) : is_RInt (g F L) 0 1 (NegExp_CreditV F L).
  Proof.
    suffices H : RInt (g F L) 0 1 = NegExp_CreditV F L.
    { rewrite -H. apply (RInt_correct (V := R_CompleteNormedModule)), (g_ex_RInt (M := M)); first OK. apply Hex. }
    rewrite /g.
    rewrite /RealDecrTrial_CreditV.
    rewrite /hx.
    (* Separate the sum *)
    replace  (RInt (λ x, SeriesC (λ n, RealDecrTrial_μ x 0 n * (Iverson Zeven n * F (x + L) + Iverson (not ∘ Zeven) n * NegExp_CreditV F (L + 1)))) 0 1)
      with  ((RInt (λ x, SeriesC (λ n, RealDecrTrial_μ x 0 n * Iverson (not ∘ Zeven) n * NegExp_CreditV F (L + 1))) 0 1 +
             (RInt (λ x, SeriesC (λ n, RealDecrTrial_μ x 0 n * Iverson Zeven n * F (x + L))) 0 1)));
      last first.
    { rewrite RInt_add.
      3: { eapply ex_RInt_SeriesC.
        all: admit.
        Unshelve. admit.
      }
      2: { eapply ex_RInt_SeriesC.
        all: admit.
        Unshelve. admit.
      }
      apply RInt_ext.
      rewrite Rmin_left; OK.
      rewrite Rmax_right; OK.
      intros ??.
      rewrite -SeriesC_plus.
      3: {
        rewrite /RealDecrTrial_μ.
        eapply (ex_seriesC_le _ (λ n : nat, RealDecrTrial_μ0 x (n + 0) * M)).
        2: { apply ex_seriesC_scal_r. apply (RealDecrTrial_μ0_ex_seriesC (x := x) (M := 0)). OK. }
        intros n.
        split.
        { apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rmult_le_pos|]|].
          { apply Iverson_nonneg. }
          { apply RealDecrTrial_μ0nn. OK. }
          { apply Iverson_nonneg. }
          { apply Hf. }
        }
        { apply Rmult_le_compat.
          2: { apply Hf; OK. }
          3: { apply Hf; OK. }
          1: { apply Rmult_le_pos; [apply Rmult_le_pos|].
               { apply Iverson_nonneg. }
               { apply RealDecrTrial_μ0nn. OK. }
               { apply Iverson_nonneg. }
          }
          rewrite -(Rmult_1_r (RealDecrTrial_μ0 x (n + 0))).
          apply Rmult_le_compat.
          { apply Rmult_le_pos.
            { apply Iverson_nonneg. }
            { apply RealDecrTrial_μ0nn. OK. }
          }
          { apply Iverson_nonneg. }
          2: {  apply Iverson_le_1. }
          rewrite -(Rmult_1_l (RealDecrTrial_μ0 x (n + 0))).
          apply Rmult_le_compat.
          { apply Iverson_nonneg. }
          { apply RealDecrTrial_μ0nn. OK. }
          {  apply Iverson_le_1. }
          right.
          f_equal; OK.
        }
      }
      2: {
        rewrite /RealDecrTrial_μ.
        eapply (ex_seriesC_le _ (λ n : nat, RealDecrTrial_μ0 x (n + 0) * M)).
        2: { apply ex_seriesC_scal_r. apply (RealDecrTrial_μ0_ex_seriesC (x := x) (M := 0)). OK. }
        intros n.
        split.
        { apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rmult_le_pos|]|].
          { apply Iverson_nonneg. }
          { apply RealDecrTrial_μ0nn. OK. }
          { apply Iverson_nonneg. }
          { eapply NegExp_CreditV_nn; last apply Hex. intros ?. eapply Hf. }
        }
        { apply Rmult_le_compat.
          2: { eapply NegExp_CreditV_nn; last apply Hex. intros ?. apply Hf. }
          3: { apply NegExp_CreditV_ub. intros ?. apply Hf. }
          1: { apply Rmult_le_pos; [apply Rmult_le_pos|].
               { apply Iverson_nonneg. }
               { apply RealDecrTrial_μ0nn. OK. }
               { apply Iverson_nonneg. }
          }
          rewrite -(Rmult_1_r (RealDecrTrial_μ0 x (n + 0))).
          apply Rmult_le_compat.
          { apply Rmult_le_pos.
            { apply Iverson_nonneg. }
            { apply RealDecrTrial_μ0nn. OK. }
          }
          { apply Iverson_nonneg. }
          2: {  apply Iverson_le_1. }
          rewrite -(Rmult_1_l (RealDecrTrial_μ0 x (n + 0))).
          apply Rmult_le_compat.
          { apply Iverson_nonneg. }
          { apply RealDecrTrial_μ0nn. OK. }
          {  apply Iverson_le_1. }
          right.
          f_equal; OK.
        }
      }
      f_equal; apply functional_extensionality; intro n.
      lra.
    }
    (* Apply Fubini to the odd term *)
    rewrite {1}/NegExp_CreditV.
    replace (RInt (λ x : R, SeriesC (λ n : nat,
            RealDecrTrial_μ x 0 n * Iverson (not ∘ Zeven) n *
            RInt_gen (λ x0 : R, F x0 * NegExp_ρ (L + 1) x0) (at_point 0) (Rbar_locally Rbar.p_infty))) 0 1)
      with  (RInt_gen (λ x0 : R, (F x0 * NegExp_ρ (L + 1) x0) * (RInt (λ x : R, SeriesC (λ n : nat, RealDecrTrial_μ x 0 n * Iverson (not ∘ Zeven) n)) 0 1)) (at_point 0) (Rbar_locally Rbar.p_infty));
      last first.
    { pose B (x : R) (n : nat) (x0 : R) := ((RealDecrTrial_μ x 0 n * Iverson (not ∘ Zeven) n * F x0 * NegExp_ρ (L + 1) x0)).
      replace (RInt_gen (λ x0 : R, F x0 * NegExp_ρ (L + 1) x0 * RInt (λ x : R, SeriesC (λ n : nat, RealDecrTrial_μ x 0 n * Iverson (not ∘ Zeven) n)) 0 1)  (at_point 0) (Rbar_locally Rbar.p_infty))
         with (RInt_gen (λ x0 : R, RInt (λ x : R, SeriesC (λ n : nat, B x n x0)) 0 1)  (at_point 0) (Rbar_locally Rbar.p_infty)).
      2: {
        f_equal.
        funexti.
        rewrite RInt_Rmult.
        2: {
          apply (ex_RInt_SeriesC (fun n => 1 / (fact n))). (* UB here might be wrong but I do think one exists *)
          { admit. }
          { admit. }
          { admit. }
        }
        apply RInt_ext.
        intros ??.
        rewrite -SeriesC_scal_l.
        apply SeriesC_ext.
        intros ?.
        rewrite /B.
        OK.
      }
      replace (RInt (λ x : R, SeriesC (λ n : nat, RealDecrTrial_μ x 0 n * Iverson (not ∘ Zeven) n * RInt_gen (λ x0 : R, F x0 * NegExp_ρ (L + 1) x0) (at_point 0) (Rbar_locally Rbar.p_infty))) 0 1)
         with (RInt (λ x : R, SeriesC (λ n : nat, RInt_gen (λ x0 : R, B x n x0) (at_point 0) (Rbar_locally Rbar.p_infty))) 0 1).
      2: {
        apply RInt_ext.
        intros ??.
        apply SeriesC_ext.
        intros ?.
        rewrite /B//=.
        (* Scaling a RInt_gen *)

        admit.
      }
      replace (RInt_gen (λ x0 : R, RInt (λ x : R, SeriesC (λ n : nat, B x n x0)) 0 1) (at_point 0) (Rbar_locally Rbar.p_infty))
         with (RInt (λ x : R, RInt_gen (λ x0 : R,SeriesC (λ n : nat, B x n x0)) (at_point 0) (Rbar_locally Rbar.p_infty)) 0 1).
      2: {
        (* Fubini *)
        symmetry.
        apply FubiniImproper_eq; [|done].
        rewrite /B//=.
        (* Derive this from the fact that F is FubiniCondition.
           and exp (the closed form for the inner series) is FubiniCondition.  *)
        intros xb.
        rewrite /FubiniCondition.

        admit.
      }
      apply RInt_ext.
      rewrite Rmin_left; OK.
      rewrite Rmax_right; OK.
      intros ??.
      (* Punishment *)
      admit.
    }
    replace (RInt_gen (λ x0 : R, (F x0 * NegExp_ρ (L + 1) x0) * (RInt (λ x : R, SeriesC (λ n : nat, RealDecrTrial_μ x 0 n * Iverson (not ∘ Zeven) n)) 0 1)) (at_point 0) (Rbar_locally Rbar.p_infty))
       with (RInt_gen (λ x0 : R, (F x0 * NegExp_ρ (L + 1) x0) * (RInt (λ x : R, 1 - exp (-x)) 0 1)) (at_point 0) (Rbar_locally Rbar.p_infty));
      last first.
    { f_equal; apply functional_extensionality; intro x0.
      f_equal.
      f_equal; apply functional_extensionality; intro x.
      rewrite /RealDecrTrial_μ.
      rewrite /RealDecrTrial_μ0.
      replace (λ n : nat, Iverson (uncurry le) (0%nat, n) * (x ^ (n - 0) / fact (n - 0) - x ^ (n - 0 + 1) / fact (n - 0 + 1)) * Iverson (not ∘ Zeven) n)
         with (λ n : nat, Iverson (not ∘ Zeven) n * (x ^ n / fact n - x ^ (n + 1) / fact (n + 1))); last first.
      { funexti.
        symmetry. rewrite Iverson_True; [|rewrite //=; OK].
        rewrite Rmult_comm.
        f_equal; OK.
        rewrite Rmult_1_l.
        f_equal; OK.
        { f_equal; f_equal; OK. f_equal; OK. }
        { f_equal; f_equal; OK. f_equal; OK. }
      }
      replace (SeriesC (λ n : nat, Iverson (not ∘ Zeven) n * (x ^ n / fact n - x ^ (n + 1) / fact (n + 1))))
         with ((-1) * SeriesC (λ n : nat, Iverson (not ∘ Zeven) n * ((-x) ^ n / fact n + (-x) ^ (n + 1) / fact (n + 1)))); last first.
      { rewrite -SeriesC_scal_l.
        apply SeriesC_ext.
        intros n.
        rewrite /Iverson.
        case_decide; OK.
        rewrite Rmult_plus_distr_l.
        repeat rewrite Rmult_1_l.
        rewrite Rmult_plus_distr_l.
        rewrite Rminus_def.
        repeat rewrite Rdiv_def.
        f_equal.
        { rewrite -Rmult_assoc; f_equal; OK. rewrite not_even_pow_neg; OK. }
        { repeat rewrite -Rmult_assoc.
          rewrite Ropp_mult_distr_l; f_equal.
          rewrite even_pow_neg; OK.
          replace (Z.of_nat (n + 1)%nat) with (Z.succ (Z.of_nat n)) by OK.
          apply Zeven_Sn.
          destruct (Zeven_odd_dec n); OK.
        }
      }
      rewrite ExpSeriesOdd.
      OK.
    }
    (* Compute the integral *)
    replace (RInt_gen (λ x0 : R, F x0 * NegExp_ρ (L + 1) x0 * RInt (λ x : R, 1 - exp (- x)) 0 1) (at_point 0) (Rbar_locally Rbar.p_infty))
       with (RInt_gen (λ x0 : R, F x0 * NegExp_ρ (L + 1) x0 * exp (-1)) (at_point 0) (Rbar_locally Rbar.p_infty));
      last first.
    { f_equal; apply functional_extensionality; intro x0.
      f_equal.
      have H : (Derive.Derive (fun x : R => x + exp (- x))) = (λ x : R, 1 - exp (- x)).
      { funexti.
        rewrite Derive.Derive_plus; [|by auto_derive| by auto_derive].
        rewrite Rminus_def.
        f_equal.
        { apply Derive.Derive_id. }
        { apply Derive_exp_neg. }
      }
      rewrite -H.
      rewrite RInt_Derive.
      { rewrite Rplus_0_l Ropp_0 exp_0.  replace (Ropp 1) with (-1) by OK. OK. }
      { intros ??. auto_derive. OK. (* Wait why does this work*) }
      { intros ??.
        rewrite H.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
      }
    }
    (* Separate out the gen integrals.
       Use RInt_gen_Chasles, though it's timing out my proof process right now *)
    replace (RInt_gen (λ x0 : R, F x0 * NegExp_ρ (L + 1) x0 * exp (-1)) (at_point 0) (Rbar_locally Rbar.p_infty))
      with ((RInt_gen (λ x0 : R, F x0 * NegExp_ρ (L + 1) x0 * exp (-1)) (at_point 0) (at_point (L + 1))) +
             (RInt_gen (λ x0 : R, F x0 * NegExp_ρ (L + 1) x0 * exp (-1)) (at_point (L + 1)) (Rbar_locally Rbar.p_infty)));
      last first.
    { rewrite -(@RInt_gen_Chasles R_CompleteNormedModule (at_point 0) (Rbar_locally Rbar.p_infty) _ _ (λ x0 : R, F x0 * NegExp_ρ (L + 1) x0 * exp (-1)) (L + 1) _ _).
      { OK. }
      { apply ex_RInt_gen_at_point.
        eapply ex_RInt_Rmult'.
        eapply ex_RInt_mult.
        { eapply Hex. }
        apply NegExp_ρ_ex_RInt.
      }
      {
        (* Upper bound this by M * ... * (exp -1) *)
        (* Probably need the inegral from (L + 1) to infinity of F to exist... *)
        admit. }
    }
    rewrite RInt_gen_at_point.
    2: {
      eapply ex_RInt_Rmult'.
      eapply ex_RInt_mult.
      { eapply Hex. }
      apply NegExp_ρ_ex_RInt.
    }
    replace (RInt (λ x0 : R, F x0 * NegExp_ρ (L + 1) x0 * exp (-1)) 0 (L + 1))
       with (RInt (λ x0 : R, 0) 0 (L + 1)); last first.
    { apply RInt_ext; intros x [Hx1 Hx2].
      rewrite /NegExp_ρ/NegExp_ρ0.
      rewrite (@Iverson_False _ (Rle 0)); [lra|].
      intro Hk.
      rewrite -Rcomplements.Rminus_le_0 in Hk.
      have ? : (L + 1 <= x).
      { etransitivity; last apply Hk. by rewrite plus_INR. }
      rewrite Rmax_right in Hx2; last first.
      { apply Rplus_le_le_0_compat; [apply pos_INR |lra]. }
      lra.
    }
    rewrite RInt_const /scal//=/mult//= Rmult_0_r Rplus_0_l.
    rewrite /NegExp_CreditV.
    replace (RInt_gen (λ x : R, F x * NegExp_ρ L x) (at_point 0) (Rbar_locally Rbar.p_infty))
      with (RInt_gen (λ x : R, F x * NegExp_ρ L x) (at_point 0) (at_point (INR L)) +
            RInt_gen (λ x : R, F x * NegExp_ρ L x) (at_point (INR L)) (at_point (L + 1)) +
            RInt_gen (λ x : R, F x * NegExp_ρ L x) (at_point (L + 1)) (Rbar_locally Rbar.p_infty));
      last first.
    { rewrite -(@RInt_gen_Chasles R_CompleteNormedModule (at_point 0) (Rbar_locally Rbar.p_infty) _ _  (λ x : R, F x * NegExp_ρ L x) (L + 1) _ _).
      { rewrite /plus//=.
        rewrite RInt_gen_at_point.
        2: { apply ex_RInt_mult. { apply Hex. } { apply NegExp_ρ_ex_RInt. } }
        rewrite RInt_gen_at_point.
        2: { apply ex_RInt_mult. { apply Hex. } { apply NegExp_ρ_ex_RInt. } }
        rewrite RInt_gen_at_point.
        2: { apply ex_RInt_mult. { apply Hex. } { apply NegExp_ρ_ex_RInt. } }
        rewrite -(RInt_Chasles (λ x : R, F x * NegExp_ρ L x) 0 L (L + 1)).
        2: { apply ex_RInt_mult. { apply Hex. } { apply NegExp_ρ_ex_RInt. } }
        2: { apply ex_RInt_mult. { apply Hex. } { apply NegExp_ρ_ex_RInt. } }
        OK.
      }
      { apply ex_RInt_gen_at_point.
        apply ex_RInt_mult. { apply Hex. } { apply NegExp_ρ_ex_RInt. } }
      { (* Upper bound this by M * ...
           OK if f pcs continuous *)
        admit. }
    }
    rewrite RInt_gen_at_point.
    2: { apply ex_RInt_mult. { apply Hex. } { apply NegExp_ρ_ex_RInt. } }
    rewrite RInt_gen_at_point.
    2: { apply ex_RInt_mult. { apply Hex. } { apply NegExp_ρ_ex_RInt. } }
    replace (RInt (λ x : R, F x * NegExp_ρ L x) 0 L) with (RInt (λ x : R, 0) 0 L); last first.
    { apply RInt_ext; intros x [Hx1 Hx2].
      rewrite /NegExp_ρ/NegExp_ρ0.
      rewrite (@Iverson_False _ (Rle 0)); [lra|].
      intro Hk.
      rewrite -Rcomplements.Rminus_le_0 in Hk.
      have ? : (L <= x).
      { etransitivity; last apply Hk. done. }
      rewrite Rmax_right in Hx2; last apply pos_INR.
      lra.
    }
    rewrite RInt_const /scal//=/mult//= Rmult_0_r Rplus_0_l.
    rewrite Rplus_comm.
    f_equal.
    { (* Change of variables *)
      replace (RInt (λ x : R, F x * NegExp_ρ L x) L (L + 1)) with (RInt (λ x : R, F (x + L) * NegExp_ρ L (x + L)) 0 1); last first.
      { replace (RInt (λ x : R, F x * NegExp_ρ L x) L (L + 1)) with (RInt (λ x : R, F x * NegExp_ρ L x) (1 * 0 + L) (1 * 1 + L)); last first.
        { f_equal; OK. }
        rewrite -(RInt_comp_lin (λ x : R, F x * NegExp_ρ L x) 1 L 0 1).
        2: {
          rewrite Rmult_0_r Rplus_0_l.
          rewrite Rmult_1_l Rplus_comm.
          apply ex_RInt_mult. { apply Hex. } { apply NegExp_ρ_ex_RInt. }
        }
        f_equal. apply functional_extensionality. intros ?. rewrite /scal//=/mult//= Rmult_1_l.
        f_equal; f_equal; OK.
      }
      apply RInt_ext; intros x [Hx1 Hx2].
      (* Factor out F *)
      rewrite SeriesC_scal_r Rmult_comm; f_equal.
      (* Simplify *)
      rewrite /NegExp_ρ.
      rewrite Iverson_True; last lia.
      rewrite Rmult_1_l.
      rewrite /NegExp_ρ0.
      rewrite Rplus_minus_r.
      rewrite Iverson_True; last (rewrite Rmin_left in Hx1; lra).
      rewrite Rmult_1_l.
      (* Exponential series *)
      rewrite /RealDecrTrial_μ.
      rewrite /RealDecrTrial_μ0.
      replace  (λ x0 : nat, Iverson (uncurry le) (0%nat, x0) * (x ^ (x0 - 0) / fact (x0 - 0) - x ^ (x0 - 0 + 1) / fact (x0 - 0 + 1)) * Iverson Zeven x0) with (λ x0 : nat, (x ^ (x0) / fact (x0) - x ^ (x0 + 1) / fact (x0 + 1)) * Iverson Zeven x0); last first.
      { funexti.
        symmetry. rewrite Iverson_True; [|rewrite //=; OK].
        rewrite Rmult_1_l.
        f_equal; OK.
        f_equal; OK.
        { f_equal; f_equal; OK. f_equal; OK. }
        { f_equal; f_equal; OK. f_equal; OK. }
      }
      replace (SeriesC (λ x0 : nat, (x ^ x0 / fact x0 - x ^ (x0 + 1) / fact (x0 + 1)) * Iverson Zeven x0)) with
              (SeriesC (λ x0 : nat, Iverson Zeven x0 * ((-x) ^ x0 / fact x0 + (-x) ^ (x0 + 1) / fact (x0 + 1)))); last first.
      { apply SeriesC_ext.
        intros n.
        rewrite /Iverson.
        case_decide; OK.
        repeat rewrite Rmult_1_l.
        repeat rewrite Rmult_1_r.
        rewrite Rminus_def.
        repeat rewrite Rdiv_def.
        f_equal.
        { f_equal; OK. rewrite even_pow_neg; OK. }
        { repeat rewrite -Rmult_assoc.
          rewrite Ropp_mult_distr_l; f_equal.
          rewrite not_even_pow_neg; OK.
          replace (Z.of_nat (n + 1)%nat) with (Z.succ (Z.of_nat n)) by OK.
          intro Hk.
          apply Zodd_Sn in H.
          apply Zodd_not_Zeven in H.
          apply Zeven_not_Zodd in Hk.
          destruct (Zeven_odd_dec (Z.succ n)); OK.
        }
      }
      rewrite ExpSeriesEven.
      OK.
    }
    {
      apply RInt_gen_ext_eq_Ici.
      2: {


        admit. }
      intros x Hx.
      rewrite Rmult_assoc. f_equal.
      rewrite /NegExp_ρ.
      rewrite Iverson_True; last lia.
      rewrite Rmult_1_l.
      rewrite Iverson_True; last lia.
      rewrite Rmult_1_l.
      rewrite /NegExp_ρ0.
      (* Can't simply get the inequalities for the bounds by cases
         on the iverson function here; the terms are not equal on the [L, L+1] interval. *)
      rewrite Iverson_True; last first.
      { (* Need the bounds here *)
        apply error_credits.Rle_0_le_minus.
        etrans; last eapply Hx.
        rewrite plus_INR INR_1. OK. }
      rewrite Rmult_1_l.
      rewrite Iverson_True; last first.
      { apply error_credits.Rle_0_le_minus.
        etrans; last eapply Hx.
        OK. }
      rewrite Rmult_1_l.
      rewrite -exp_plus; f_equal.
      rewrite plus_INR INR_1.
      lra.
    }
  Admitted.

End credits.


Section program.
  Context `{!erisGS Σ}.
  Import Hierarchy.

  (* Tail-recursive Negative Exponential sampling*)
  Definition NegExp : val :=
    rec: "trial" "L" :=
      let: "x" := init #() in
      let: "y" := lazyDecrR #Nat.zero "x" in
      if: ("y" `rem` #2%Z = #0%Z) then
        ("L", "x")
      else
        "trial" ("L" + #1%Z).

  Lemma wp_NegExp_gen {M} (F : R → R) (Hnn : ∀ n, 0 <= F n <= M) E (Hex : ∀ a b : R, ex_RInt F a b) :
    ⊢ ∀ L, ↯ (NegExp_CreditV F L) -∗
           WP NegExp #L @ E
      {{ p, ∃ (vz : Z) (vr : R) (ℓ : val), ⌜p = PairV #vz ℓ⌝ ∗ lazy_real ℓ vr ∗ ↯(F (vr + IZR vz))}}.
  Proof.
    iLöb as "IH".
    iIntros (L) "Hε".
    rewrite {2}/NegExp.
    wp_pure.
    wp_apply wp_init; first done.
    iIntros (x) "Hx".
    iApply (wp_lazy_real_presample_adv_comp _ _ x _ (NegExp_CreditV F L) (g F L)); auto.
    { intros ??; eapply g_nonneg; auto. }
    { eapply g_expectation; first apply Hnn.  OK. }
    iFrame.
    iIntros (xr) "(%Hrange & Hε & Hx)".
    do 2 wp_pure.
    wp_bind (lazyDecrR _ _).
    iApply (pgl_wp_mono_frame (□ _) with "[Hx Hε] IH"); last first.
    { iApply (wp_lazyDecrR_gen (hx F xr L) _ E $! _ x xr).
      by rewrite /g; iFrame.
      Unshelve.
      1: { exact ((F (xr + L)) + (NegExp_CreditV F (L + 1))). }
      1: {
        rewrite /hx.
        intro n.
        split.
        { apply Rplus_le_le_0_compat; apply Rmult_le_pos; try apply Iverson_nonneg.
          { apply Hnn.  }
          { eapply NegExp_CreditV_nn; last apply Hex. intro r. apply Hnn. }
        }
        { apply Rplus_le_compat.
          { rewrite -{2}(Rmult_1_l (F (xr + L))).
            apply Rmult_le_compat_r; [|apply Iverson_le_1].
            apply Hnn.
          }
          { rewrite -{2}(Rmult_1_l (NegExp_CreditV F (L + 1))).
            apply Rmult_le_compat_r; [|apply Iverson_le_1].
            eapply NegExp_CreditV_nn; last apply Hex. intro r. apply Hnn.
          }
        }
      }
    }
    iIntros (v) "(#IH & [%l (%Hv & Hε & Hx)])"; rewrite Hv.
    wp_pures.
    case_bool_decide.
    { have Heven : Zeven l.
      { inversion H as [H'].
        apply Z.rem_mod_eq_0 in H'; [|lia].
        by apply Zeven_bool_iff; rewrite Zeven_mod H' //. }
      wp_pures.
      iModIntro.
      iExists L, xr, x.
      iFrame.
      iSplitR; first done.
      unfold hx.
      iPoseProof (ec_split _ _ with "Hε") as "(Hε & _)".
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
      { apply Rmult_le_pos; [apply Iverson_nonneg | eapply NegExp_CreditV_nn; OK]. }
      rewrite Iverson_True; last done.
      by rewrite Rmult_1_l INR_IZR_INZ.
    }
    { do 2 wp_pure.
      rewrite {1}/NegExp.
      iPoseProof (ec_split _ _ with "Hε") as "(_ & Hε)".
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
      { apply Rmult_le_pos; [apply Iverson_nonneg | eapply NegExp_CreditV_nn; OK ]. }
      rewrite Iverson_True; last first.
      { intro Hk; apply H. f_equal.
        apply Zeven_bool_iff in Hk.
        rewrite Zeven_mod in Hk.
        apply Zeq_bool_eq in Hk.
        apply (Z.rem_mod_eq_0 l 2 ) in Hk; [by f_equal|lia].
      }
      rewrite Rmult_1_l.
      iSpecialize ("IH" $! (Nat.add L 1) with "Hε").
      rewrite Nat2Z.inj_add.
      iApply "IH".
    }
  Qed.

End program.

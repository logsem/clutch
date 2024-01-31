(** * Higher order specification for incremental sampling algorithms *)
From clutch.ub_logic Require Export ub_clutch ub_rules.
From Coquelicot Require Import Series.
Require Import Lra.

Set Default Proof Using "Type*".

Section samplers.
  (* higher order boundeded rejection sampler *)
  Definition gen_bounded_rejection_sampler :=
    (λ: "depth" "sampler" "checker",
        let: "do_sample" :=
          (rec: "f" "tries_left" :=
              if: ("tries_left" - #1) < #0
                then NONE
                else let: "next_sample" := ("sampler" #()) in
                     if: ("checker" "next_sample")
                        then SOME "next_sample"
                        else "f" ("tries_left" - #1))
        in "do_sample" "depth")%E.


  (* higher order unbounded rejection sampler *)
  Definition gen_rejection_sampler :=
    (λ: "sampler" "checker",
        let: "do_sample" :=
          (rec: "f" "_" :=
             let: "next_sample" := ("sampler" #()) in
              if: ("checker" "next_sample")
                  then SOME "next_sample"
                  else "f" #())
        in "do_sample" #())%E.
End samplers.


Section finSeries.
  Local Open Scope R.

  (* generalizes foldr_ext in stdpp *)
  Lemma foldr_ext' {A B} (f1 f2 : B → A → A) l :
    (∀ b a, (b ∈ l) -> f1 b a = f2 b a) → (forall x1 x2, x1 = x2 -> foldr f1 x1 l = foldr f2 x2 l).
  Proof.
    intros Hf.
    induction l as [|x' l' IH] using rev_ind ; [done|].
    intros x1 x2 ->.
    do 2 (rewrite foldr_app; simpl).
    apply IH; intros; apply Hf, elem_of_app.
    - by left.
    - right; apply elem_of_list_here.
  Qed.

  Lemma reindex_fin_series M z K (Hnm : (z < M)%nat):
    SeriesC (fun x : fin M => nonneg (if bool_decide (x < z)%nat then nnreal_zero else K)) = (M-z) * nonneg K.
  Proof.
    induction z as [|z' IH].
    - rewrite -(SeriesC_ext (fun _ => K)); last auto.
      rewrite SeriesC_finite_mass fin_card /=.
      rewrite Rminus_0_r; done.
    - rewrite -(SeriesC_ext (fun x => nonneg (if bool_decide (fin_to_nat x < z')%nat then nnreal_zero else K) -
                                     nonneg (if bool_decide (fin_to_nat x = z')%nat then K else nnreal_zero))); last first.
      { intros z.
        destruct (lt_eq_lt_dec (fin_to_nat z) z') as [H|H]; [destruct H as [H|H]|];
          repeat (try (rewrite bool_decide_true; last by lia);
                  try (rewrite bool_decide_false; last by lia);
                  try (simpl; lra)).
      }
      rewrite SeriesC_plus; try apply ex_seriesC_finite.
      assert (Hz' : (z' < M)%nat) by lia.
      rewrite IH; last apply Hz'.
      rewrite -(SeriesC_ext (fun x => (if bool_decide (x = (nat_to_fin Hz'))%nat then -K else nnreal_zero))); last first.
      { intros.
         replace (bool_decide (n = nat_to_fin Hz')) with (bool_decide (fin_to_nat n = z')).
         { case_bool_decide; simpl; try lra. }
         apply bool_decide_ext.
         assert (H1 : (fin_to_nat (nat_to_fin Hz') = z')%nat); first by rewrite fin_to_nat_to_fin.
         split; intros.
        - apply (@inj _ _ eq eq _ fin_to_nat_inj). rewrite H H1. done.
        - rewrite -H1. f_equal. done.
      }
      Opaque INR.
      rewrite SeriesC_singleton /=.
      rewrite S_INR.
      lra.
  Qed.
End finSeries.





Section accounting.
  Local Open Scope R.

  Definition err_factor n m : nonnegreal := (nnreal_div (nnreal_nat (m - n)%nat) (nnreal_nat m%nat)).


  Lemma err_factor_lt1 n m : (0 < n)%nat -> (n < m)%nat -> err_factor n m < 1.
  Proof.
    intros ? ?.
    rewrite /err_factor /=.
    apply Rcomplements.Rlt_div_l.
    - apply Rlt_gt; apply lt_0_INR; by lia.
    - rewrite Rmult_1_l; apply lt_INR; by lia.
  Qed.

  Lemma err_factor_nz n m : (n < m)%nat -> (m - n)%nat * / m ≠ 0.
  Proof.
    intros ?.
    rewrite /not; intros HR; apply Rmult_integral in HR; destruct HR as [HRL|HRR].
    * rewrite minus_INR in HRL; last lia.
      apply Rminus_diag_uniq_sym in HRL.
      apply INR_eq in HRL.
      lia.
    * assert (K : not (eq (INR m) 0)).
      { apply not_0_INR; apply PeanoNat.Nat.neq_0_lt_0; lia. }
      by apply (Rinv_neq_0_compat (INR m) K).
  Qed.


  (* closed form for the error in the bounded sampler, with a given number of tries remaining *)
  Program Definition bdd_cf_error n m depth (Hnm : (n < m)%nat) := mknonnegreal ((err_factor n m) ^ depth) _.
  Next Obligation.
    intros.
    apply pow_le; rewrite /err_factor /=.
    apply Rle_mult_inv_pos.
    - apply pos_INR.
    - apply lt_0_INR; lia.
  Qed.


  (* distribution of error mass ε₁ for a given sample:
      - zero error given to cases which are inbounds
      - uniform error to the recursive case *)
  Definition bdd_cf_sampling_error n m ε₁ : (fin m) -> nonnegreal
    := fun sample =>
         if bool_decide (sample < n)%nat
            then nnreal_zero
            else (nnreal_div ε₁ (err_factor n m)).


  (* simplify amplified errors *)
  Lemma simplify_amp_err (n m d': nat) (s : fin m) Hnm :
    (s <? n)%nat = false ->
    bdd_cf_sampling_error n m (bdd_cf_error n m (S d') Hnm) s = (bdd_cf_error n m d' Hnm).
  Proof.
    intros Hcase.
    apply nnreal_ext.
    rewrite /bdd_cf_sampling_error.
    rewrite bool_decide_false; last by apply Nat.ltb_nlt.
    rewrite /bdd_cf_error /=.
    apply Rinv_r_simpl_m.
    by apply err_factor_nz.
  Qed.


  Lemma factor_lt_1 n m :
    (0 < n)%nat ->
    (n < m)%nat ->
    ((m - n)%nat  * / m) < 1.
  Proof.
    intros.
    apply (Rmult_lt_reg_l m); first (apply lt_0_INR; lia).
    rewrite Rmult_1_r.
    replace (m * (INR ((m-n)%nat) * / m)) with (INR (m-n)%nat); [apply lt_INR; lia|].
    rewrite Rmult_comm Rmult_assoc Rinv_l; [|apply not_0_INR; lia].
    by rewrite Rmult_1_r.
  Qed.


  (* error distribution is bounded above for each possible sample *)
  Lemma sample_err_wf n m d (s : fin m) Hnm :
    (0 < n)%nat ->
    bdd_cf_sampling_error n m (bdd_cf_error n m (S d) Hnm) s <= 1.
  Proof.
    intros.
    rewrite /bdd_cf_sampling_error.
    destruct (s <? n)%nat as [|] eqn:Hs; simpl.
    - rewrite bool_decide_true; [|by apply Nat.ltb_lt].
      by apply Rle_0_1.
    - rewrite bool_decide_false; [|by apply Nat.ltb_nlt].
      rewrite /nnreal_div /=.
      rewrite -> Rinv_r_simpl_m.
      + destruct d as [|d'].
        * simpl; apply Rge_refl.
        * apply Rlt_le, pow_lt_1_compat; try lia; split.
          -- apply Rle_mult_inv_pos; [ apply pos_INR | apply lt_0_INR; lia ].
          -- apply factor_lt_1; auto.
      + apply err_factor_nz; auto.
  Qed.


  (* mean of error distribution is preserved *)
  Lemma sample_err_mean n' m' (Hnm : (n' < m')%nat) 𝜀₁ :
    SeriesC (λ s : fin (S m'), (1 / S m') * bdd_cf_sampling_error (S n') (S m') 𝜀₁ s) = 𝜀₁.
  Proof.
    rewrite /bdd_cf_sampling_error SeriesC_scal_l.
    apply (Rmult_eq_reg_l (S m')); last (apply not_0_INR; lia).
    rewrite Rmult_assoc -Rmult_assoc Rmult_1_r.
    assert (X : forall A B C, (Rmult A (Rmult B C)) = (Rmult (Rmult A B) C)).
    { intros. by rewrite Rmult_assoc. }
    rewrite X -Rinv_r_sym; last (apply not_0_INR; lia).
    rewrite Rmult_1_l.
    rewrite reindex_fin_series; last lia.
    rewrite /err_factor.
    Opaque INR.
    rewrite /= Rinv_mult Rinv_inv.
    rewrite -Rmult_assoc -Rmult_assoc Rmult_comm.
    apply Rmult_eq_compat_l.
    rewrite Rmult_comm -Rmult_assoc.
    rewrite -minus_INR; [|lia].
    rewrite Nat.sub_succ Rinv_l.
    - by rewrite Rmult_1_l.
    - apply not_0_INR; lia.
  Qed.

  Lemma error_limit' (r : nonnegreal) : (r < 1) -> forall ε : posreal, exists n : nat, r ^ n < ε.
  Proof.
    intros Hr ε.
    assert (H1 : Lim_seq.is_lim_seq (fun n => (r ^ n)%R) (Rbar.Finite 0)).
    { eapply Lim_seq.is_lim_seq_geom.
      rewrite Rabs_pos_eq; auto.
      apply cond_nonneg.
    }
    rewrite /Lim_seq.is_lim_seq
            /Hierarchy.filterlim
            /Hierarchy.filter_le
            /Hierarchy.eventually
            /Hierarchy.filtermap
            in H1.
    destruct (H1 (fun e' : R => (e' < ε)%R)); simpl.
    - rewrite /Hierarchy.locally.
      eexists _. intros.
      rewrite /Hierarchy.ball /Hierarchy.UniformSpace.ball /Hierarchy.R_UniformSpace /=
              /Hierarchy.AbsRing_ball Hierarchy.minus_zero_r /Hierarchy.abs /=
            in H.
      eapply Rle_lt_trans; [eapply RRle_abs| eapply H].
    - exists x. by apply H.
  Qed.


End accounting.




Section incremental_spec.
  Local Open Scope R.
  Context `{!ub_clutchGS Σ}.

  (* Ψ : state
     ξ : error
     L : progress bound
   *)
  Definition incr_sampling_scheme_spec (sampler checker : val) (Ψ : nat -> iProp Σ) (ξ : nat -> nonnegreal) L iL E : iProp Σ :=
    ( (* Either 0 credit or 0 progress => we will sample a value which the checker accepts
         Allowed to consume (or invalidate Ψ) in this process *)
      ((€ (ξ 0%nat) ∨ Ψ 0%nat) -∗ WP sampler #() @ E {{ fun s => WP checker (Val s) @ E {{fun v => ⌜v = #true⌝}}}}) ∗
      (* Given any amount of credit and progress, we can get a sample such that... *)
     □ (∀ i p, (⌜((S p) <= L)%nat ⌝ ∗ ⌜((S i) < iL)%nat ⌝ ∗ € (ξ (S i)) ∗ Ψ (S p)) -∗
            WP sampler #() @ E {{ fun s =>
                   (*...we're done by chance alone, or... *)
                  (WP checker (Val s) @ E {{fun v => ⌜v = #true⌝}}) ∨
                   (*... we make prgress, and can run the checker on the sample without losing progress, or *)
                  (€ (ξ (S i)) ∗ Ψ p ∗ (Ψ p -∗ WP checker (Val s) @ E {{fun v => Ψ p ∗ ∃ b: bool, ⌜v = #b⌝}})) ∨
                   (*... we lose progress & amplify error, and can run the checker on the sample without losing progress. *)
                  (∃ p', ⌜(p' <= L)%nat ⌝ ∗ € (ξ i) ∗ Ψ p' ∗ (Ψ p' -∗ WP checker (Val s) @ E {{fun v => Ψ p' ∗ ∃ b: bool, ⌜v = #b⌝}}))}}))%I.


  Lemma ho_incremental_ubdd_approx_safe (sampler checker : val) Ψ ξ L E i iL p :
    ⊢ ⌜(p <= L)%nat ⌝ ∗
      ⌜(i < iL)%nat ⌝ ∗
    incr_sampling_scheme_spec sampler checker Ψ ξ L iL E ∗
    € (ξ i) ∗
    Ψ p -∗
    WP (gen_rejection_sampler sampler checker) @ E {{ fun v => ∃ v', ⌜ v = SOMEV v' ⌝}}.
  Proof.
    rewrite /incr_sampling_scheme_spec.
    iIntros "(%Hl&%Hil&(Hfinal&#Hamp)&Hcr&HΨ)".
    rewrite /gen_rejection_sampler.
    do 7 wp_pure.
    iRevert (Hl).
    iInduction i as [|i'] "IHerror" forall (p).
    - (* base case for error credits *)
      iIntros "%Hl".
      wp_pures.
      wp_bind (sampler _).
      wp_apply (ub_wp_wand with "[Hfinal Hcr]"); first (iApply "Hfinal"; iFrame).
      iIntros (s) "Hcheck"; wp_pures.
      wp_apply (ub_wp_wand with "Hcheck").
      iIntros (v) "->"; wp_pures.
      eauto.
    - (* inductive case for error credits *)
      iIntros "%Hl".
      iInduction p as [|p'] "IHp".
      + (* base case for progress measure *)
        wp_pures.
        wp_bind (sampler _).
        wp_apply (ub_wp_wand with "[Hfinal HΨ]"); first (iApply "Hfinal"; iFrame).
        iIntros (s) "Hcheck"; wp_pures.
        wp_apply (ub_wp_wand with "Hcheck").
        iIntros (v) "->"; wp_pures.
        eauto.
      + (* Inductive case for progress measure *)
        wp_pures.
        wp_bind (sampler _).
        wp_apply (ub_wp_wand with "[Hamp Hcr HΨ]"); first (iApply "Hamp"; iFrame; eauto).
        iIntros (s) "[Hluck | [(Hcr&HΨ&Hcheck)|[%p'' (%Hp''&Hcr&HΨ&Hcheck)]]]".
        * (* luck *)
          wp_pures.
          wp_bind (checker _).
          wp_apply (ub_wp_wand with "Hluck").
          iIntros (?) "->".
          wp_pures.
          eauto.
        * (* progress *)
          wp_pures.
          wp_bind (checker _).
          wp_apply (ub_wp_wand with "[Hcheck HΨ]"); first (iApply ("Hcheck" with "[$]")).
          iIntros (r) "(HΨ&[%b ->])".
          destruct b as [|].
          -- (* lucky: checker accepts *)
             wp_pures. eauto.
          -- (* not lucky: checker rejects *)
             wp_pure. iApply ("IHp" with "[] Hfinal Hcr HΨ").
             iPureIntro. lia.
        * (* amplification *)
          wp_pures.
          wp_bind (checker _).
          wp_apply (ub_wp_wand with "[Hcheck HΨ]"); first (iApply ("Hcheck" with "[$]")).
          iIntros (r) "(HΨ&[%b ->])".
          destruct b as [|].
          -- (* lucky: checker accepts *)
             wp_pures. eauto.
          -- (* not lucky: checker rejects *)
             assert (HiL' : (i' < iL)%nat) by lia.
             wp_pure. iApply ("IHerror" $! HiL' with "Hfinal Hcr HΨ"). eauto.
    Qed.


End incremental_spec.


Section remove_me.

  Local Open Scope R.
  Context `{!ub_clutchGS Σ}.

  Lemma wp_ec_spend e E Φ ε :
    (1 <= ε.(nonneg))%R →
    (to_val e = None) ->
    € ε -∗ WP e @ E {{ Φ }}.
  Proof. Admitted.


End remove_me.

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





(* FIXME: move. Or better yet delete. *)
Section finite.
  (* generalization of Coq.Logic.FinFun: lift functions over fin to functions over nat *)
  Definition f_lift_fin_nat {A} (N : nat) (a : A) (f : fin N -> A) : (nat -> A) :=
    fun n =>
      match le_lt_dec N n with
      | left _ => a
      | right h => f (Fin.of_nat_lt h)
      end.


  (* uses proof irrelevance *)
  Lemma f_lift_fin_nat_ltN {A} (n N: nat) (a : A) (Hn : (n < N)%nat) f :
    (f_lift_fin_nat N a f) n = f (nat_to_fin Hn).
  Proof.
    rewrite /f_lift_fin_nat.
    destruct (le_lt_dec N n) as [Hl|Hr].
    - lia.
    - f_equal; f_equal.
      apply proof_irrelevance.
  Qed.


  Lemma f_lift_fin_nat_geN {A} (N n: nat) (a : A) (Hn : not (n < N)%nat) f :
    (f_lift_fin_nat N a f) n = a.
  Proof.
    rewrite /f_lift_fin_nat.
    destruct (le_lt_dec N n); [done | lia].
  Qed.


  Lemma encode_inv_nat_nat_total (n : nat) : (@encode_inv_nat nat _ _ n)  = Some n.
  Proof.
    rewrite -encode_inv_encode_nat.
    f_equal.
    rewrite /encode_nat.
    rewrite /encode /nat_countable.
    destruct n; try done.
    rewrite /= /encode /N_countable /= -SuccNat2Pos.inj_succ.
    symmetry; apply SuccNat2Pos.pred_id.
  Qed.



  Lemma fin2_enum (x : fin 2) : (fin_to_nat x = 0%nat) \/ (fin_to_nat x = 1%nat).
  Proof. Admitted.


  (* surely there has to be a better way *)
  Lemma fin2_not_0 (x : fin 2) : not (x = 0%fin) -> (x = 1%fin).
  Proof.
    intros Hx.
    destruct (fin2_enum x) as [H|H].
    - replace 0%nat with (@fin_to_nat 2 (0%fin)) in H by auto.
      apply fin_to_nat_inj in H.
      exfalso; apply Hx; apply H.
    - replace 1%nat with (@fin_to_nat 2 (1%fin)) in H by auto.
      apply fin_to_nat_inj in H.
      done.
  Qed.


  Lemma fin2_not_1 (x : fin 2) : not (x = 1%fin) -> (x = 0%fin).
  Proof.
    intros Hx.
    destruct (fin2_enum x) as [H|H]; last first.
    - replace 1%nat with (@fin_to_nat 2 (1%fin)) in H by auto.
      apply fin_to_nat_inj in H.
      exfalso; apply Hx; apply H.
    - replace 0%nat with (@fin_to_nat 2 (0%fin)) in H by auto.
      apply fin_to_nat_inj in H.
      done.
  Qed.

  Lemma fin2_nat_bool (x : fin 2) : (fin_to_nat x =? 1)%nat = (fin_to_bool x).
  Proof.
    destruct (fin2_enum x) as [H|H]; rewrite H; simpl.
    - replace 0%nat with (@fin_to_nat 2 (0%fin)) in H by auto.
      apply fin_to_nat_inj in H.
      by rewrite H /=.
    - replace 1%nat with (@fin_to_nat 2 (1%fin)) in H by auto.
      apply fin_to_nat_inj in H.
      by rewrite H /=.
  Qed.
End finite.


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

  Lemma fin_enum_length M : length (enum (fin M)) = M.
  Proof. induction M; simpl; [done|]. f_equal; by rewrite fmap_length. Qed.

  Lemma fin_enum_take n N (v : fin N) :
    v ∈ take n (enum (fin N)) -> (fin_to_nat v < n)%nat.
  Proof.
    Opaque firstn.
    simpl.
    induction v as [|N' v' IH].
    - simpl; intros. admit. (* wait now this isn't true too *)
    - simpl.
      intros H.
      destruct n; simpl.
      { exfalso. rewrite take_0 in H. by eapply (elem_of_nil _). }
      rewrite firstn_cons in H.
      apply elem_of_cons in H; destruct H; first simplify_eq.
      rewrite -fmap_take in H.
      (* really, we should be able to get the v ∈ take n (fin_enum N') now from H *)
      assert (HIH: v' ∈ take n (fin_enum N')).
      { admit. }

      (* anad this should be provable *)
      assert (Hs: forall A x i (l : list A), (x ∈ take i l) -> (x ∈ take (S i) l) (* and it's not the last element *)).
      { admit. }

      apply Hs, IH in HIH.
  Admitted.


  Lemma fin_enum_drop n N (v : fin N) :
    v ∈ drop n (enum (fin N)) -> not (fin_to_nat v < n)%nat.
  Proof. Admitted.


  (* FIXME: bad name, and maybe bad proof *)
  Lemma reindex_fin_series M z K (Hnm : ((S z) < M)%nat):
    SeriesC (fun x : fin M => nonneg (if bool_decide (x < (S z))%nat then nnreal_zero else K)) = (M-(S z)) * nonneg K.
  Proof.
    rewrite countable_sum.SeriesC_finite_foldr.
    rewrite -(take_drop (S z) (enum (fin M))).
    rewrite foldr_app.
    assert (Hfoldr_const : forall A K l r0, foldr (Rplus ∘ (fun x : A => K)) r0 l = r0 + K * length l).
    { intros.
      generalize dependent r0.
      induction l as [|l' ls IH] using rev_ind; intros; [simpl; lra| ].
      rewrite app_length foldr_app plus_INR Rmult_plus_distr_l Rmult_1_r.
      rewrite -Rplus_assoc IH /=.
      lra. }
    replace (foldr _ 0 _) with  ((M - S z) * K).
    - (* Outer series (0) *)
      rewrite -{2}(Rplus_0_r (_ * K)).
      replace 0 with (0 * length (take (S z) (enum (fin M)))); [|lra].
      rewrite -Hfoldr_const.
      apply foldr_ext'; [|lra].
      intros; simpl.
      rewrite bool_decide_true; [done|].
      apply fin_enum_take, H.
    - (* Inner series (K) *)
      rewrite -(Rplus_0_l (_ * K)).
      rewrite Rmult_comm.
      replace (_ - _)%R with (INR (length (drop (S z) (enum (fin M))))); last first.
      { rewrite drop_length fin_enum_length. apply minus_INR; lia. }
      rewrite -Hfoldr_const.
      apply foldr_ext'; [|lra].
      intros. simpl.
      rewrite bool_decide_false; [done|].
      apply fin_enum_drop, H.
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
End accounting.




Section incremental_spec.
  Local Open Scope R.
  Context `{!ub_clutchGS Σ}.

  (* Ψ : state
     ξ : error
     L : progress bound
   *)
  Definition incr_sampling_scheme_spec (sampler checker : val) (Ψ : nat -> iProp Σ) (ξ : nat -> nonnegreal) L E : iProp Σ :=
    ( (* Either 0 credit or 0 progress => we will sample a value which the checker accepts
         Allowed to consume (or invalidate Ψ) in this process *)
      ((€ (ξ 0%nat) ∨ Ψ 0%nat) -∗ WP sampler #() @ E {{ fun s => WP checker (Val s) @ E {{fun v => ⌜v = #true⌝}}}}) ∗
      (* Given any amount of credit and progress, we can get a sample such that... *)
     □ (∀ i p, (⌜((S p) <= L)%nat ⌝ ∗ € (ξ (S i)) ∗ Ψ (S p)) -∗
            WP sampler #() @ E {{ fun s =>
                   (*... we make prgress, and can run the checker on the sample without losing progress, or *)
                  ((€ (ξ (S i)) ∗ Ψ p ∗ (Ψ p -∗ WP checker (Val s) @ E {{fun v => Ψ p ∗ ∃ b: bool, ⌜v = #b⌝}})) ∨
                   (*... we lose progress & amplify error, and can run the checker on the sample without losing progress. *)
                   (∃ p', ⌜(p' <= L)%nat ⌝ ∗ € (ξ i) ∗ Ψ p' ∗ (Ψ p' -∗ WP checker (Val s) @ E {{fun v => Ψ p' ∗ ∃ b: bool, ⌜v = #b⌝}})))}}))%I.


  Lemma ho_incremental_ubdd_approx_safe (sampler checker : val) Ψ ξ L E i p :
    ⊢ ⌜(p <= L)%nat ⌝ ∗
    incr_sampling_scheme_spec sampler checker Ψ ξ L E ∗
    € (ξ i) ∗
    Ψ p -∗
    WP (gen_rejection_sampler sampler checker) @ E {{ fun v => ∃ v', ⌜ v = SOMEV v' ⌝}}.
  Proof.
    rewrite /incr_sampling_scheme_spec.
    iIntros "(%Hl&(Hfinal&#Hamp)&Hcr&HΨ)".
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
        iIntros (s) "[(Hcr&HΨ&Hcheck)|[%p'' (%Hp''&Hcr&HΨ&Hcheck)]]".
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
             wp_pure. iApply ("IHerror" with "Hfinal Hcr HΨ"). eauto.
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

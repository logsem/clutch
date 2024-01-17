(** * Examples related to rejection samplers with a bounded number of attempts *)
From clutch.ub_logic Require Export ub_clutch ub_rules.
From iris.base_logic.lib Require Import invariants.
From Coquelicot Require Import Series.
Require Import Lra.

Set Default Proof Using "Type*".

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
  Local Lemma reindex_fin_series M z K (Hnm : ((S z) < M)%nat):
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




Section basic.
  (** * Correctness of bounded and unbounded rejection samplers using error credits instead of Löb induction *)
  (** The samplers in this section simulate (rand #n') using (rand #m') samplers *)

  Local Open Scope R.
  Context `{!ub_clutchGS Σ}.

  (** Bounded sampler (fails after `depth` attempts) *)
  Definition bdd_rejection_sampler (n' m' : nat) : val :=
    λ: "depth",
      let: "do_sample" :=
        (rec: "f" "tries_left" :=
           if: ("tries_left" - #1) < #0
            then NONE
            else let: "next_sample" := (rand #m') in
                if: ("next_sample" ≤ #n')
                then SOME "next_sample"
                else "f" ("tries_left" - #1))
      in "do_sample" "depth".


  (** Unbounded sampler (may not terminate) *)
  Definition ubdd_rejection_sampler (n' m' : nat) : val :=
    λ: "_",
      let: "do_sample" :=
        (rec: "f" "_" :=
           let: "next_sample" := (rand #m') in
           if: ("next_sample" ≤ #n')
            then SOME "next_sample"
            else "f" #())
      in "do_sample" #().

  (* constant we can amplify our error by in the case that the samplers reject *)
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



  (** general case for the bounded sampler *)
  Definition bdd_approx_safe (n' m' depth : nat) (Hnm : (S n' < S m')%nat) E :
    {{{ € (bdd_cf_error (S n') (S m') (S depth) Hnm) }}} bdd_rejection_sampler n' m' #(S depth)@ E {{{ v, RET v ; ⌜exists v' : nat, v = SOMEV #v' /\ (v' < S n')%nat⌝ }}}.
  Proof.
 iIntros (Φ) "Hcr HΦ"; rewrite /bdd_rejection_sampler.
    assert (Hnm' : (n' < m')%nat) by lia.
    do 4 wp_pure.
    (* Induction will reach the base cse when S depth = 1 <=> depth = 0 *)
    iInduction depth as [|depth' Hdepth'] "IH".
    - wp_pures.
      wp_apply (wp_rand_err_list_nat _ m' (seq (S n') ((S m') - (S n')))).
      iSplitL "Hcr".
      + iApply (ec_spend_irrel with "[$]").
        rewrite /= Rmult_1_r.
        rewrite seq_length; apply Rmult_eq_compat_l.
        do 2 f_equal; lia.
      + iIntros (sample'') "%Hsample''".
        wp_pures.
        case_bool_decide; wp_pures.
        * iApply "HΦ"; iModIntro; iPureIntro; eexists _; split; [auto|lia].
        * exfalso.
          rewrite List.Forall_forall in Hsample''.
          specialize Hsample'' with sample''.
          apply Hsample''; last reflexivity.
          rewrite in_seq.
          split; first lia.
          replace (S n' + (S m' - S n'))%nat with (S m') by lia.
          apply fin_to_nat_lt.
    - wp_pures.
      replace (bool_decide _) with false; last (symmetry; apply bool_decide_eq_false; lia).
      wp_pures.
      wp_apply (wp_couple_rand_adv_comp _ _ _ Φ _ (bdd_cf_sampling_error (S n') _ _) with "Hcr").
      { exists 1. intros s. apply sample_err_wf; try lia. }
      { by apply sample_err_mean. }
      iIntros (sample') "Hcr".
      wp_pures.
      case_bool_decide.
      + wp_pures; iApply "HΦ"; iModIntro; iPureIntro; exists (fin_to_nat sample'); split; [auto|lia].
      + wp_pure.
        rewrite (simplify_amp_err (S n') (S m') _); last (apply Nat.ltb_nlt; by lia); try lia.
        wp_bind (#_ - #_)%E; wp_pure.
        replace (S (S depth') - 1)%Z with (Z.of_nat (S depth')) by lia.
        wp_apply ("IH" with "Hcr HΦ").
  Qed.



  (** (approximate) safety of the unbounded rejection sampler *)
  Definition ubdd_approx_safe (n' m' depth : nat) Hnm E :
    {{{ € (bdd_cf_error (S n') (S m') (S depth) Hnm) }}}
      ubdd_rejection_sampler n' m' #() @ E
    {{{ v, RET v ; ⌜exists v' : nat, v = SOMEV #v' /\ (v' < S n')%nat⌝  }}}.
  Proof.
    iIntros (Φ) "Hcr HΦ"; rewrite /ubdd_rejection_sampler.
    assert (Hnm' : (n' < m')%nat) by lia.
    do 4 wp_pure.

    iInduction depth as [|depth' Hdepth'] "IH".
    - wp_pures.
      wp_apply (wp_rand_err_list_nat _ _ (seq (S n') (S m' - S n'))).
      iSplitL "Hcr".
      + iApply (ec_spend_irrel with "[$]").
        rewrite /= Rmult_1_r.
        rewrite seq_length; apply Rmult_eq_compat_l.
        do 2 f_equal; lia.
      + iIntros (sample'') "%Hsample''".
        wp_pures.
        case_bool_decide; wp_pures.
        * iApply "HΦ"; iModIntro; iPureIntro; eexists _. split; [auto|lia].
        * exfalso.
          rewrite List.Forall_forall in Hsample''.
          specialize Hsample'' with sample''.
          apply Hsample''; last reflexivity.
          rewrite in_seq.
          split; first lia.
          replace (S n' + (S m'-S n'))%nat with (S m') by lia.
          specialize (fin_to_nat_lt sample''); by lia.
    - wp_pures.
      wp_apply (wp_couple_rand_adv_comp _ _ _ Φ _ (bdd_cf_sampling_error (S n') _ _) with "Hcr").
      { eexists _. intros s. apply sample_err_wf; try lia. }
      { pose P := (sample_err_mean n' m' Hnm' (bdd_cf_error (S n') (S m') _ Hnm)). by eapply P. }
      iIntros (sample') "Hcr".
      wp_pures.
      case_bool_decide.
      + wp_pures. iApply "HΦ"; iModIntro; iPureIntro; exists (fin_to_nat sample'); split; [auto|lia].
      + wp_pure.
        rewrite simplify_amp_err; last (apply Nat.ltb_nlt; by lia); try lia.
        wp_apply ("IH" with "Hcr HΦ").
  Qed.


  (* FIXME: maybe use errror_limit' from below with ε/2 *)
  Lemma error_limit (r : nonnegreal) : (r < 1) -> forall ε : posreal, exists n : nat, r ^ (S n) < ε.
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
    destruct (H1 (fun e' : R => (e' <= ε)%R)); simpl.
    - rewrite /Hierarchy.locally.
      eexists _. intros.
      rewrite /Hierarchy.ball /Hierarchy.UniformSpace.ball /Hierarchy.R_UniformSpace /=
              /Hierarchy.AbsRing_ball Hierarchy.minus_zero_r /Hierarchy.abs /=
            in H.
      eapply Rle_trans; [eapply RRle_abs|].
      by apply Rlt_le.
    - exists x.
      apply (Rcomplements.Rle_mult_Rlt r); [apply cond_pos|lra|].
      rewrite Rmult_comm.
      apply Rmult_le_compat_r; [apply cond_nonneg|].
      auto.
  Qed.


  (** Improve the safety of the unbounded sampler to use any positive amount of error credit *)
  Theorem ubdd_cf_safety (n' m' : nat) ε E :
    (n' < m')%nat ->
    ⊢ {{{ €ε ∗ ⌜0 < ε ⌝ }}}
        ubdd_rejection_sampler n' m' #() @ E
      {{{ v, RET v ; ⌜exists v' : nat, v = SOMEV #v' /\ (v' < S n')%nat⌝ }}}.
  Proof.
    iIntros (? Φ) "!> (Hcr&%Hcrpos) HΦ".
    assert (Hef: (err_factor (S n') (S m')) < 1) by (apply err_factor_lt1; lia).
    destruct (error_limit (err_factor (S n') (S m')) Hef (mkposreal ε Hcrpos)) as [d].
    iApply ((ubdd_approx_safe _ _ d _) with "[Hcr] [HΦ]"); auto.
    iApply ec_weaken; last iAssumption.
    rewrite /bdd_cf_error /=; simpl in H.
    apply Rlt_le. done.
    Unshelve. by lia.
  Qed.

End basic.



Section higherorder.
  (** Specification for general (stateful) bounded rejection samplers which makes use of
      Iris' higher order Hoare triples *)
  Local Open Scope R.
  Context `{!ub_clutchGS Σ}.

  (* higher order boundeded rejection sampler *)
  Definition ho_bdd_rejection_sampler :=
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
  Definition ho_ubdd_rejection_sampler :=
    (λ: "sampler" "checker",
        let: "do_sample" :=
          (rec: "f" "_" :=
             let: "next_sample" := ("sampler" #()) in
              if: ("checker" "next_sample")
                  then SOME "next_sample"
                  else "f" #())
        in "do_sample" #())%E.


  Definition sampling_scheme_spec (sampler checker : val) 𝜀factor 𝜀final E : iProp Σ
    := ((∀ 𝜀,
          {{{ € 𝜀 }}}
            ((Val sampler) #())%E @ E
          {{{ (v : val), RET v;
               ((WP ((Val checker) v) @ E {{ λ v', ⌜v' = #true ⌝ }}) ∨
               (∃ 𝜀', € 𝜀' ∗ ⌜𝜀 <= 𝜀' * 𝜀factor ⌝ ∗ (WP ((Val checker) v) @ E {{ λ v', ⌜v' = #true \/ v' = #false⌝ }})))}}}) ∗
        (∀ v : val,
          {{{ € 𝜀final }}}
            ((Val sampler) v) @ E
          {{{ (v' : val), RET v'; (WP ((Val checker) v') @ E {{ λ v', ⌜v' = #true ⌝ }})}}}))%I.

  Program Definition generic_geometric_error (r 𝜀final : nonnegreal) (depth : nat) : nonnegreal
    := (𝜀final * (mknonnegreal (r ^ depth) _))%NNR.
  Next Obligation. intros. apply pow_le. by destruct r. Qed.

  Lemma final_generic_geometric_error (r 𝜀final : nonnegreal) : (generic_geometric_error r 𝜀final 0%nat) = 𝜀final.
  Proof. apply nnreal_ext; by rewrite /generic_geometric_error /= Rmult_1_r. Qed.

  Lemma simpl_generic_geometric_error (r 𝜀final : nonnegreal) (depth : nat) :
    (not (eq (nonneg r) 0)) ->
    (nnreal_div (generic_geometric_error r 𝜀final (S depth)) r)%NNR = (generic_geometric_error r 𝜀final  depth).
  Proof.
    intros.
    rewrite /generic_geometric_error /nnreal_div /nnreal_mult.
    apply  nnreal_ext; simpl.
    rewrite Rmult_assoc;  apply Rmult_eq_compat_l.
    rewrite -Rmult_comm -Rmult_assoc Rinv_l; [lra|auto].
  Qed.

  (* safety for higher-order bounded rejection samplers *)
  Lemma ho_bdd_approx_safe (sampler checker : val) (r εfinal : nonnegreal) (depth : nat) E :
    (0 < r < 1) ->
    (0 < εfinal < 1) ->
    sampling_scheme_spec sampler checker r εfinal E -∗
    € (generic_geometric_error r εfinal depth) -∗
    (WP (ho_bdd_rejection_sampler #(S depth) sampler checker) @ E {{ fun v => ∃ v', ⌜ v = SOMEV v' ⌝}})%I.
  Proof.
    (* initial setup *)
    rewrite /sampling_scheme_spec.
    iIntros ([Hr_pos Hr] [Hεfinal_pos Hεfinal]) "(#Hamplify&#Haccept) Hcr".
    rewrite /ho_bdd_rejection_sampler.
    do 9 wp_pure.
    iInduction depth as [|depth' Hdepth'] "IH".
    - wp_pures; wp_bind (sampler #())%E.
      wp_apply ("Haccept" with "[Hcr]").
      { iApply (ec_weaken with "Hcr"); rewrite /generic_geometric_error /=; lra. }
      iIntros (next_sample) "Hcheck_accept".
      wp_pures; wp_bind (checker next_sample)%E.
      iApply (ub_wp_wand with "Hcheck_accept").
      iIntros (?) "#->"; wp_pures.
      iModIntro; iExists next_sample; iFrame; auto.
    - wp_pures.
      replace (bool_decide _) with false; last (symmetry; apply bool_decide_eq_false; lia).
      wp_pures; wp_bind (sampler #())%E.
      iApply ("Hamplify" $! (generic_geometric_error r εfinal (S depth')) with "Hcr").
      iIntros (next_sample) "!> [Hcheck_accept|[%ε'(Hcr&%Hε'&Hcheck_reject)]]"; wp_pures.
      + wp_bind (checker next_sample)%V.
        iApply (ub_wp_wand with "Hcheck_accept").
        iIntros (?) "#->"; wp_pures.
        iModIntro; iExists next_sample; iFrame; auto.
      + wp_bind (checker next_sample)%V.
        iApply (ub_wp_wand with "Hcheck_reject").
        iIntros (?) "%Hresult".
        iSpecialize ("IH" with "[Hcr]").
        * iApply (ec_spend_le_irrel with "Hcr").
          rewrite /generic_geometric_error /=.
          apply (Rmult_le_reg_r r); auto.
          by rewrite /generic_geometric_error /=
                     (Rmult_comm r _) -Rmult_assoc in Hε'.
        * destruct Hresult as [-> | ->].
          { wp_pures; eauto. }
          { do 2 wp_pure.
            iClear "#".
            replace #((S (S depth')) - 1) with #(S depth'); [| do 2 f_equal; lia].
            iApply "IH". }
  Qed.


  (* safety for higher-order unbounded rejection samplers (almost the same proof) *)
  Lemma ho_ubdd_approx_safe (sampler checker : val) (r εfinal : nonnegreal) (depth : nat) E :
    (0 < r < 1) ->
    (0 < εfinal < 1) ->
    sampling_scheme_spec sampler checker r εfinal E -∗
    ▷ € (generic_geometric_error r εfinal depth) -∗
    (WP (ho_ubdd_rejection_sampler sampler checker) @ E {{ fun v => ∃ v', ⌜ v = SOMEV v' ⌝}})%I.
  Proof.
    rewrite /sampling_scheme_spec.
    iIntros ([Hr_pos Hr] [Hεfinal_pos Hεfinal]) "(#Hamplify&#Haccept) Hcr".
    rewrite /ho_ubdd_rejection_sampler.
    do 7 wp_pure.
    iInduction depth as [|depth' Hdepth'] "IH".
    - wp_pures; wp_bind (sampler #())%E.
      wp_apply ("Haccept" with "[Hcr]").
      { iApply (ec_weaken with "Hcr"); rewrite /generic_geometric_error /=; lra. }
      iIntros (next_sample) "Hcheck_accept".
      wp_pures; wp_bind (checker next_sample)%E.
      iApply (ub_wp_wand with "Hcheck_accept").
      iIntros (?) "#->"; wp_pures.
      iModIntro; iExists next_sample; iFrame; auto.
    - wp_pures.
      wp_pures; wp_bind (sampler #())%E.
      iApply ("Hamplify" $! (generic_geometric_error r εfinal (S depth')) with "Hcr").
      iIntros (next_sample) "!> [Hcheck_accept|[%ε'(Hcr&%Hε'&Hcheck_reject)]]"; wp_pures.
      + wp_bind (checker next_sample)%V.
        iApply (ub_wp_wand with "Hcheck_accept").
        iIntros (?) "#->"; wp_pures.
        iModIntro; iExists next_sample; iFrame; auto.
      + wp_bind (checker next_sample)%V.
        iApply (ub_wp_wand with "Hcheck_reject").
        iIntros (?) "%Hresult".
        iSpecialize ("IH" with "[Hcr]").
        * iApply (ec_spend_le_irrel with "Hcr").
          rewrite /generic_geometric_error /=.
          apply (Rmult_le_reg_r r); auto.
          by rewrite /generic_geometric_error /=
                     (Rmult_comm r _) -Rmult_assoc in Hε'.
        * destruct Hresult as [-> | ->].
          { wp_pures; eauto. }
          { wp_pure.
            iClear "#".
            replace #((S (S depth')) - 1) with #(S depth'); [| do 2 f_equal; lia].
            iApply "IH". }
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

  (** Limiting argument: any amount of credit suffices to show the unbounded sampler is safe *)
  Lemma ho_ubdd_safe (sampler checker : val) (r εfinal ε : nonnegreal) E :
    (0 < r < 1) ->
    (0 < εfinal < 1) ->
    0 < ε ->
    ⊢ sampling_scheme_spec sampler checker r εfinal E -∗
      €ε -∗
      WP ho_ubdd_rejection_sampler sampler checker @ E {{ v, ∃ v', ⌜ v = SOMEV v' ⌝ }}.
  Proof.
    iIntros (? ? ?) "#Hspec Hcr".
    remember (/ NNRbar_to_real (NNRbar.Finite εfinal) * nonneg ε) as p.
    assert (Hp : (0 < p)).
    { rewrite Heqp.
      apply Rmult_lt_0_compat; try done.
      apply Rinv_0_lt_compat.
      by destruct H0. }
    assert (H' : r < 1); first by destruct H.
    destruct (error_limit' r H' (mkposreal p Hp)) as [depth Hlim].
    iApply (ho_ubdd_approx_safe _ _ _ _ depth);[|done|done|];[done|]. (* weird unification order *)
    iApply (ec_spend_le_irrel with "Hcr").
    rewrite /generic_geometric_error /=.
    apply (Rmult_le_reg_l (/ εfinal)).
    { apply Rinv_0_lt_compat; by destruct H0. }
    rewrite /= Heqp in Hlim.
    rewrite -Rmult_assoc Rinv_l; last lra.
    rewrite Rmult_1_l.
    by apply Rlt_le.
  Qed.


End higherorder.



Section higherorder_rand.
  (** Instantiation of the higher-order spec for a basic rejection sampler *)
  Local Open Scope R.
  Context `{!ub_clutchGS Σ}.

  Definition rand_ε2 (n' m' : nat) (ε1 : nonnegreal) : (fin (S m')) -> nonnegreal
    := fun z => if (bool_decide (z < S n')%nat)
                  then nnreal_zero
                  else (nnreal_div ε1 (err_factor (S n') (S m'))).


  Lemma sample_err_mean_higherorder n' m' (Hnm : (n' < m')%nat) 𝜀₁ :
    SeriesC (λ n : fin (S m'), (1 / S m') * rand_ε2 n' m' 𝜀₁ n) = 𝜀₁.
  Proof.
    rewrite /bdd_cf_sampling_error SeriesC_scal_l.
    apply (Rmult_eq_reg_l (S m')); last (apply not_0_INR; lia).
    rewrite Rmult_assoc -Rmult_assoc Rmult_1_r.
    rewrite -Rmult_assoc -Rinv_r_sym; last (apply not_0_INR; lia).
    rewrite Rmult_1_l.
    rewrite /rand_ε2.
    rewrite reindex_fin_series; try lia.
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

  Lemma rand_sampling_scheme_spec (n' m' : nat) (Hnm : (n' < m')%nat) E :
    ⊢ sampling_scheme_spec
          (λ: "_", rand #m')%V
          (λ: "sample", "sample" ≤ #n')%V
          (err_factor (S n') (S m'))
          (err_factor (S n') (S m'))
          E.
  Proof.
    Opaque INR.
    rewrite /sampling_scheme_spec.
    iStartProof; iSplit.
    - (* sampling rule *)
      iIntros (ε Φ) "!> Hcr HΦ"; wp_pures.
      iApply (wp_couple_rand_adv_comp  m' _ _ _ ε (rand_ε2 n' m' ε) _ with "Hcr").
      { (* uniform bound *)
        eexists (nnreal_div ε (err_factor (S n') (S m'))); intros s.
        rewrite /rand_ε2.
        case_bool_decide; simpl; [|lra].
        apply Rmult_le_pos.
        - by apply cond_nonneg.
        - apply Rlt_le, Rinv_0_lt_compat, Rmult_lt_0_compat.
          + apply lt_0_INR. lia.
          + apply Rinv_0_lt_compat. apply lt_0_INR. lia.
      }

      { (* series convergence *)
        by apply sample_err_mean_higherorder. }

      iNext; iIntros (s) "Hcr".
      iApply "HΦ".
      destruct (le_gt_dec s n') as [|] eqn:Hdec; [iLeft | iRight].
      + (* the sample is inbounds, the checker should accept *)
        wp_pures; iModIntro; iPureIntro.
        do 2 f_equal; apply bool_decide_true; lia.
      + (* the sample is out of bounds *)
        iExists _; iSplitL; first iFrame.
        iSplit.
        * (* credit is amplified *)
          iPureIntro.
          rewrite /rand_ε2 bool_decide_eq_false_2; last first.
          { rewrite /not; intros; lia. }
          rewrite /nnreal_div Rmult_assoc /nnreal_inv; simpl.
          rewrite Rinv_l; [lra|].
          apply Rmult_integral_contrapositive; split.
          -- apply Rgt_not_eq, Rlt_gt, lt_0_INR; lia.
          -- apply Rinv_neq_0_compat.
             apply Rgt_not_eq, Rlt_gt, lt_0_INR; lia.
        * (* sampler rejects *)
          wp_pures; iModIntro; iPureIntro. right.
          do 2 f_equal; apply bool_decide_false; lia.

    - (* checking rule *)
      iIntros (s Φ) "!> Hcr HΦ"; wp_pures.
      wp_apply (wp_rand_err_list_nat _ m' (seq (S n') ((S m') - (S n')))).
      iSplitL "Hcr".
      + (* credit accounting *)
        iApply (ec_spend_irrel with "Hcr").
        rewrite /err_factor seq_length /=.
        apply Rmult_eq_compat_l.
        do 2 f_equal; lia.
      + iIntros (s') "%Hs'".
        iApply "HΦ"; wp_pures.
        iModIntro; iPureIntro.
        do 2 f_equal; apply bool_decide_true.
        rewrite List.Forall_forall in Hs'.
        specialize Hs' with s'.
        apply Znot_gt_le.
        intros Hcont; apply Hs'; last reflexivity.
        rewrite in_seq.
        split; first lia.
        replace (S n' + (S m' - S n'))%nat with (S m') by lia.
        specialize (fin_to_nat_lt s'); by lia.

    Unshelve.
    { apply Φ. }
    { rewrite Nat2Z.id; apply TCEq_refl. }
  Qed.

End higherorder_rand.




Section higherorder_flip2.
  (** Instantiation of the higher-order spec for a pair of coin flips *)
  Local Open Scope R.
  Context `{!ub_clutchGS Σ}.

  Definition ε2_flip2 (ε1 : nonnegreal) (v : fin (S 1%nat)) : nonnegreal :=
    if (fin_to_bool v)
      then nnreal_zero
      else (nnreal_nat(2%nat) * ε1)%NNR.

  Definition flip_is_1  (v : val): bool :=
    match v with
    | LitV (LitInt 1%Z) => true
    | _ => false
    end.

  Definition ε2_flip1 (ε1 εh εt : nonnegreal) (v : fin (S 1%nat)) : nonnegreal :=
    if (fin_to_bool v) then εh else εt.

  Definition scale_flip (ε1 εh εt : nonnegreal) : val -> nonnegreal
    := (fun z => if (flip_is_1 z) then εh else εt).

  Lemma flip_amplification (ε1 εh εt : nonnegreal) (Hmean : (εh + εt) = 2 * ε1 ) E :
    {{{ € ε1 }}}
      rand #1 @ E
    {{{ v, RET #v; ⌜(v = 0%nat) \/ (v = 1%nat) ⌝ ∗ € (scale_flip ε1 εh εt #v) }}}.
  Proof.
    iIntros (Φ) "Hcr HΦ".
    iApply (wp_couple_rand_adv_comp 1%nat  _ _ _ ε1 (ε2_flip1 ε1 εh εt) _ with "Hcr").
    - (* uniform bound *)
      exists (εh + εt)%NNR; intros n.
      rewrite /ε2_flip1.
      destruct (fin_to_bool n); destruct εt, εh; rewrite /bound /=; lra.
    - (* series mean *)
      rewrite SeriesC_finite_foldr /enum /fin_finite /fin_enum /ε2_flip1 /=.
      rewrite Rplus_0_r -Rmult_plus_distr_l Rplus_comm Hmean /=.
      lra.
    - (* continutation *)
      iNext. iIntros (n) "Hcr".
      iApply ("HΦ" $! (fin_to_nat n)); iSplitR.
      + iPureIntro; apply fin2_enum.
      + iApply (ec_spend_irrel with "Hcr"). rewrite /ε2_flip2.
        destruct (fin2_enum n) as [H|H].
        * rewrite /ε2_flip1 H /=.
          rewrite -fin2_nat_bool.
          replace (n =? 1)%nat with false; [done|].
          symmetry; apply Nat.eqb_neq; lia.
        * rewrite /ε2_flip1 H /=.
          rewrite -fin2_nat_bool.
          replace (n =? 1)%nat with true; [done|].
          symmetry; apply Nat.eqb_eq; lia.
      Unshelve.
      { apply Φ. }
      { apply TCEq_refl. }
  Qed.

  (* not importing, for some reason? *)
  Lemma wp_ec_spend e E Φ ε :
    (1 <= ε.(nonneg))%R →
    (to_val e = None) ->
    € ε -∗ WP e @ E {{ Φ }}.
  Proof. Admitted.


  Lemma flip2_sampling_scheme_spec E :
    ⊢ sampling_scheme_spec
          (λ: "_", Pair (rand #1) (rand #1))
          (λ: "sample", (((Fst "sample") = #1) && ((Snd "sample") = #1)))
          (nnreal_div (nnreal_nat 3%nat) (nnreal_nat 4%nat))
          (nnreal_div (nnreal_nat 3%nat) (nnreal_nat 4%nat))
          E.
  Proof.
    rewrite /sampling_scheme_spec.
    iStartProof; iSplit.
    - (* amplification rule *)
      iIntros (𝜀 Φ) "!> Hcr HΦ"; wp_pures.
      wp_apply (flip_amplification 𝜀
                  (nnreal_mult 𝜀 (nnreal_div (nnreal_nat 2) (nnreal_nat 3)))
                  (nnreal_mult 𝜀 (nnreal_div (nnreal_nat 4) (nnreal_nat 3)))
                   with "Hcr"); [simpl; lra| ].
      iIntros (v) "(%Hv&Hcr)".
      destruct Hv as [-> | ->].
      + (* first flip was zero, check is going to false and the second flip doesn't matter. *)
        wp_bind (rand _)%E; iApply wp_rand; auto.
        iNext; iIntros (v') "_"; wp_pures; iModIntro; iApply "HΦ".
        iRight; iExists _.
        iSplitL "Hcr"; [iFrame|].
        iSplit.
        * (* credit accounting *)
          iPureIntro; simpl; lra.
        * (* step the checker *)
          wp_pures; case_bool_decide; wp_pures; auto.
      + (* first flip was 1, we only have 2/3 error so we need to amplify up to 4/3
            in the case that the second flip is not 1 *)
        replace (scale_flip 𝜀 _ _ _) with (𝜀 * nnreal_div (nnreal_nat 2) (nnreal_nat 3))%NNR; last first.
        { rewrite /scale_flip /flip_is_1 /=. by apply nnreal_ext. }
        remember (𝜀 * nnreal_div (nnreal_nat 2) (nnreal_nat 3))%NNR as 𝜀'.
        wp_bind (rand #1 )%E.
        wp_apply (flip_amplification 𝜀' nnreal_zero (nnreal_mult 𝜀' (nnreal_nat 2)) with "Hcr").
        { simpl. lra. }
        iIntros (v) "(%Hv&Hcr)".
        destruct Hv as [-> | ->].
        * (* second flip was zero *)
          wp_pures; iModIntro; iApply "HΦ".
          iRight; iExists _.
          iSplitL "Hcr"; [iFrame|].
          iSplit.
          -- (* credit accounting *)
            iPureIntro; rewrite Heq𝜀' /=; lra.
          -- (* step the checker *)
            wp_pures; auto.
        * (* both flips are 1, checker should accept *)
          wp_pures; iModIntro; iApply "HΦ".
          iLeft; wp_pures; auto.

    - (* credit spending rule *)
      iIntros (s Φ) "!> Hcr HΦ"; wp_pures.
      wp_bind (rand #1)%E.

      (* give € 1 to the 0 flip, and € 1/2 to the 1 flip *)
      wp_apply (flip_amplification
                  (nnreal_div (nnreal_nat 3) (nnreal_nat 4))
                  (nnreal_div (nnreal_nat 1) (nnreal_nat 2))
                  nnreal_one with "Hcr"); [simpl; lra|].
      iIntros (v') "(%Hv'&Hcr)".
      destruct Hv' as [-> | ->].
      + (* first flip is zero: but we can spend € 1 to conclude *)
        iApply (wp_ec_spend with "Hcr").
        * rewrite /scale_flip /flip_is_1 /=; lra.
        * rewrite /to_val; done.
      +  (* we have € 1/2 so we can make the second flip be 1 too *)
        wp_bind (rand #1)%E.
        iApply (wp_rand_err _ _ 0%fin with "[Hcr HΦ]").
        iSplitL "Hcr". { iApply (ec_spend_irrel with "Hcr"). rewrite /=; lra. }
        iIntros (v') "%Hv'".
        wp_pures; iModIntro; iApply "HΦ".
        wp_pures; case_bool_decide; wp_pures; auto.
        (* we have a contradiction in Hv' and H *)
        exfalso. apply fin2_not_0  in Hv'. apply H. rewrite Hv' /=. f_equal.
  Qed.

End higherorder_flip2.

Section presampled_flip2.
  (** Demonstration of using the planner rule instead of the higher-order spec *)
  (** This proof is fairly idiomatic Iris and does not need to do manual credit accounting *)
  Local Open Scope R.
  Context `{!ub_clutchGS Σ}.

  Lemma tapes_flip2_ubdd_safe (ε : nonnegreal) E :
    0 < ε ->
    ⊢ €ε -∗
      WP
        let: "α" := (alloc #(Z.succ 0)) in
        ho_ubdd_rejection_sampler
        (λ: "_", Pair (rand("α")#1) (rand("α") #1))
        (λ: "sample", (((Fst "sample") = #1) && ((Snd "sample") = #1)))
        @ E {{ v, ∃ v', ⌜ v = SOMEV v' ⌝ }}.
  Proof.
    iIntros (?) "Hcr".
    wp_bind (alloc _)%I.
    wp_apply (wp_alloc_tape); auto.
    iIntros (α) "Hα".
    rewrite Z2Nat.inj_succ; try lia.
    wp_apply (presample_planner_aligned _ _ _ _ _ _ _ _ [1%fin; 1%fin]); auto; [apply H|].
    iFrame.
    iIntros "[%junk Hα] /=".
    pose flip2_junk_inv k s : iProp Σ := (∃ j, α ↪ (S (Z.to_nat 0); j ++ s) ∗ ⌜length j = (2 * k)%nat ⌝)%I.
    iAssert (flip2_junk_inv _ _ _ _ _) with "[Hα]" as "Hinv".
    { rewrite /flip2_junk_inv app_assoc.
      iExists _; iFrame; iPureIntro.
      apply Nat.Div0.div_exact.
      rewrite app_length.
      apply (blocks_aligned (Z.to_nat 0%nat) 2%nat).
      lia.
    }
    do 11 wp_pure.
    iInduction (length (junk ++ block_pad (Z.to_nat 0) 2 junk) `div` 2) as [|k'] "IH".
    - rewrite /flip2_junk_inv /=.
      iDestruct "Hinv" as "[%j (Hα & %Hl)] /=".
      rewrite (nil_length_inv _ Hl) /=.
      wp_pures.
      wp_bind (Rand _ _); wp_apply (wp_rand_tape with "Hα"); iIntros "Hα".
      wp_bind (Rand _ _); wp_apply (wp_rand_tape with "Hα"); iIntros "Hα".
      wp_pures.
      iModIntro; iExists _; iPureIntro. done.
    - rewrite /flip2_junk_inv.
      iDestruct "Hinv" as "[%j (Hα & %Hl)] /=".
      rewrite Nat.mul_succ_r Nat.add_comm /= in Hl.
      destruct j as [| s0 j0]. { simpl in Hl. exfalso; lia. }
      destruct j0 as [| s1 j']. { simpl in Hl. exfalso; lia. }
      wp_pures.
      wp_bind (Rand _ _); wp_apply (wp_rand_tape with "Hα"); iIntros "Hα".
      wp_bind (Rand _ _); wp_apply (wp_rand_tape with "Hα"); iIntros "Hα".
      iSpecialize ("IH" with "[Hα]").
      { iExists _; iFrame; iPureIntro. do 2 rewrite cons_length in Hl. congruence. }
      wp_pures.
      case_bool_decide; [wp_pures; case_bool_decide|].
      + wp_pures; iModIntro; iExists _; auto.
      + wp_pure. iApply "IH".
      + do 2 wp_pure; iApply "IH".
  Qed.
End presampled_flip2.

Section higherorder_walkSAT.
  (** Demonstration of using the higher-order spec for stateful computation (WalkSAT) *)
  (** This "sampler" does not just return a value, but modifies a state *)
  Local Open Scope R.
  Context `{!ub_clutchGS Σ}.

  Context (N : nat).

  (* set up a random assignment of n boolean variables *)
  Definition mk_init_asn : expr :=
    (rec: "mk_asn'" "n" :=
       if: ("n" = #0)
        then NONE
        else
          let: "b" := rand #1 in
          let: "r" := ("mk_asn'" ("n" - #1)) in
          SOME ("b", "r"))
    #N.

  Definition error : expr := (#42 #42)%E.

  (* An assignment is a linked list, NONE is the empty list, and SOME (b, L)*)
  Definition eval_asn : val :=
    (rec: "eval_asn" "asnV" "n" :=
       match: "asnV" with
          NONE => error
        | SOME "R" => if: ("n" = #0)
                        then (Fst "R")
                        else ("eval_asn" (Snd "R") ("n" - #1))
       end)%V.

  (* to avoid needless reflections, we will paramaterize the checker by a fixed formula *)
  (* A formula is a list of clauss, we should be able to access formula m by (formula !! m) *)
  Inductive clause :=
      | ClauseV (e1 e2 e3 : fVar)
    with fVar :=
      | Pos (n : Z)
      | Neg (n : Z).
  Definition formula : Type := list clause.

  (* evaluate an assignment against an fVar *)
  Definition evaluate_fvar (f: fVar) : val :=
    (λ: "asnV",
       match f with
        | (Pos n) => (#true = eval_asn "asnV" #n)
        | (Neg n) => (#false = eval_asn "asnV" #n)
       end).

  (* so this is actually not what we want to measure... we want to evaluate how closely the
     assignemnt matches some fixed satisfying assignment (since that progresses monotonely).
     The problem is, if there's multiple satisfying assignments, now our analysis will not
     actually decrease *)
  Definition evaluate_clause (c : clause) : val :=
    (λ: "asnV",
        match c with
         | ClauseV e1 e2 e3 => ((evaluate_fvar e1 "asnV") || (evaluate_fvar e2 "asnV") || (evaluate_fvar e3 "asnV"))
        end)%V.

  (* collect the indices of all UNSAT clauses as a value-level list *)
  Fixpoint collect_unsat_clauses_rec (f : formula) (start_index : nat) : val :=
    (λ: "asnV",
       match f with
         | (c :: cs) =>
             if: ((evaluate_clause c) "asnV")
              then SOME (#start_index, (collect_unsat_clauses_rec cs (S start_index)) "asnV")
              else ((collect_unsat_clauses_rec cs (S start_index)) "asnV")
         | [] => NONE
       end).

  Definition collect_unsat_clauses (f : formula) : val :=
    (λ: "asnV", collect_unsat_clauses_rec f 0%nat "asnV").

  (* return true when the list of UNSAT clauses is [] *)
  Definition checker (f : formula) : val :=
    (λ: "asnV", (collect_unsat_clauses f) "asnV" = NONEV).

  (* collect the indices of the UNSAT clauses and either
      - return the Hoare triple which says (checker "asnV") {{ True }}
      - resample a random clause. Either it's SAT, and it makes progress, or we amplify the error
   *)
  Definition sampler (f : formula) : val :=
    (λ: "asnV", #()).


  Definition incremental_sampling_scheme_spec (sampler checker : val) Ψ εfactor εfinal E : iProp Σ
    := (  (* 1. After some amount of progress, we can ensure the checker will pass *)
          (* 2. We can always spend εfinal to obtain a sample which will surely pass *)
          {{{ € εfinal ∨ Ψ 0%nat }}}
            ((Val sampler) #())%E @ E
          {{{ (v : val), RET v; WP ((Val checker) v) @ E {{ λ v', ⌜v' = #true ⌝ }}}}} ∗
          (* 3. Given any amount of credit and progress, the sampler will either... *)
          (∀ ε p,
            {{{ € ε }}}
              ((Val sampler) #())%E @ E
            {{{ (v : val), RET v;
                (* 3.1: obtain a sample which makes progress without consuming error, or *)
                (Ψ p -∗ ∃ p', € ε ∗ Ψ p' ∗ (* ⌜ (p' < p)%nat ⌝*) ⌜S p' = p ⌝ ∗ ((WP ((Val checker) v) @ E {{ λ v', ⌜v' = #true \/ v' = #false⌝ }}))) ∨
                (* 3.2: amplifies the error by a factor, possibly losing progress *)
                (∃ ε', € ε' ∗ ⌜(ε <= ε' * εfactor)%NNR ⌝ ∗ (WP ((Val checker) v) @ E {{ λ v', ⌜v' = #true \/ v' = #false⌝ }}))}}}))%I.

  Lemma ho_incremental_ubdd_approx_safe (sampler checker : val) Ψ p (εfactor εfinal : nonnegreal) (depth : nat) E :
    (0 < εfactor < 1) ->
    (0 < εfinal < 1) ->
    incremental_sampling_scheme_spec sampler checker Ψ εfactor εfinal E -∗
    ▷ € (generic_geometric_error εfactor εfinal depth) -∗
    ▷ Ψ p -∗
    (WP (ho_ubdd_rejection_sampler sampler checker) @ E {{ fun v => ∃ v', ⌜ v = SOMEV v' ⌝}})%I.
  Proof.
    iIntros ([Hfactor_lb Hfactor_ub] [Hfinal_lb Hfinal_ub]) "(#Haccept & #Hamplify) Hε HΨ".
    do 7 wp_pure.
    iInduction p as [|p'] "IHp". (* FIXME: this should be strong induction but iInduction isn't happy with that  *)
    { wp_pures; wp_bind (sampler #())%E.
      wp_apply (ub_wp_wand with "[HΨ]").
      { iApply ("Haccept" with "[$]").
        iNext. iIntros (?) "Hv"; iApply "Hv". }
      iIntros (s) "Hs".
      wp_pures.
      wp_bind (checker s)%E.
      iApply (ub_wp_wand with "Hs").
      iIntros (?) "#->".
      wp_pures.
      iModIntro; iExists _; eauto.
    }
    iInduction depth as [|depth' Hdepth'] "IH".
    - wp_pures; wp_bind (sampler #())%E.
      wp_apply (ub_wp_wand with "[Hε]").
      { iApply ("Haccept" with "[Hε]").
        - iLeft.
          iApply ec_spend_irrel; [|iFrame].
          rewrite /generic_geometric_error /=; lra.
        - iNext. iIntros (?) "Hv"; iApply "Hv".
      }
      iIntros (s) "Hs".
      wp_pures.
      wp_bind (checker s)%E.
      iApply (ub_wp_wand with "Hs").
      iIntros (?) "#->"; wp_pures.
      iModIntro; iExists _; iFrame; auto.
    - wp_pures.
      wp_bind (sampler #())%E.
      iApply ("Hamplify" with "[$]"); iNext.
      iIntros (s)  "[H1|[%ε' (Hε'&%Hamp&Hcheck)]]"; wp_pures.
      + (* we get lucky and make progress. Should be able to conclude by IHp *)
        iSpecialize ("H1" with "HΨ").
        iDestruct "H1" as "[%p'' (Hε&HΨ&%Hp''&Hcheck)]".
        inversion Hp''; simplify_eq.
        wp_bind (checker s)%E.
        wp_apply (ub_wp_wand with "Hcheck").
        iIntros (v) "[ -> | -> ]"; [wp_pures; eauto|].
        wp_pure.
        iApply ("IHp" with "[$]"); iFrame.
      + (* we do not get lucky, but we can amplify *)
        wp_bind (checker s)%E.
        wp_apply (ub_wp_wand with "Hcheck").
        iIntros (v) "[ -> | -> ]"; [wp_pures; eauto|].
        wp_pure.
        iApply ("IH" with "[] [Hε'] [HΨ]"); [| | iFrame].
        * iIntros "!> Hε' HΨ".
          wp_apply ("IHp" with "[Hε'] HΨ").
          iApply (ec_spend_le_irrel with "Hε'").
          rewrite /generic_geometric_error /=.
          rewrite Rmult_comm (Rmult_comm εfinal) Rmult_assoc.
          eapply Rle_trans.
          { apply Rlt_le.
            eapply Rmult_lt_compat_r; [|done].
            apply Rmult_lt_0_compat; [|done].
            by apply pow_lt. }
          by rewrite Rmult_1_l.
        * iApply (ec_spend_le_irrel with "Hε'").
          rewrite /generic_geometric_error /=; simpl in Hamp.
          eapply (Rmult_le_reg_r (nonneg εfactor)); [done|lra].
  Qed.

End higherorder_walkSAT.

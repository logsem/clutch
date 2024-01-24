(** * Examples related to rejection samplers with a bounded number of attempts *)
From clutch.ub_logic Require Export ub_clutch ub_rules.
(* From iris.base_logic.lib Require Import invariants. *)
From iris.algebra Require Import auth.
From Coquelicot Require Import Series.
Require Import iris.base_logic.lib.cancelable_invariants.
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
    WP (ho_ubdd_rejection_sampler sampler checker) @ E {{ fun v => ∃ v', ⌜ v = SOMEV v' ⌝}}.
  Proof.
    rewrite /incr_sampling_scheme_spec.
    iIntros "(%Hl&(Hfinal&#Hamp)&Hcr&HΨ)".
    rewrite /ho_ubdd_rejection_sampler.
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


Section integer_walk.
  (** Random walk: Sampler increments or decrements a value, checker accepts when that value is negative *)

  (* This might fit into the higher-order spec, the problem is our error and progress are linked.
     We don't really get "excess error" in the same way that we do with eg. WalkSAT. *)

  Context `{!ub_clutchGS Σ, cinvG Σ}. (* inG Σ (authR natUR)}. *)

  Definition int_walk_sampler : val :=
    (λ: "l",
       if: (rand #1 = #1)
        then "l" <- (!"l" + #1%nat)
        else "l" <- (!"l" - #1%nat))%V.

  Definition int_walk_checker : val :=
    (λ: "l", (!"l" < #0))%V.



  (** Credit accounting for the invariant *)

  Definition L (εᵢ : nonnegreal) : nat := Z.to_nat (up (1 / εᵢ)%R - 1)%Z.

  Program Definition IC εᵢ : Z -> nonnegreal := fun n => mknonnegreal (Rmax 0 (nonneg εᵢ * IZR (n + 1)%Z))%R _.
  Next Obligation. intros; apply Rmax_l. Defined.

  Lemma IC_neg εᵢ : forall (z : Z), (z < 0)%Z -> (nonneg (IC εᵢ z) = 0)%R.
  Proof.
    intros. rewrite /IC /=.
    apply Rmax_left.
    apply Rcomplements.Rmult_le_0_l; [apply cond_nonneg|].
    (* true... but how do I do this? *)
  Admitted.

  Lemma IC_ge_L εᵢ : forall (z : Z), (z >= (L εᵢ))%Z -> (nonneg (IC εᵢ z) >= 1)%R.
  Proof.
    intros. rewrite /IC /=.
    rewrite Rmax_right; last first.
    { apply Rmult_le_pos; [apply cond_nonneg|].
      (* FIXME: *)
      admit.
    }
    rewrite /L in H0.
    (* yep *)
  Admitted.

  Lemma IC_mean εᵢ : forall (z : Z), (z >= 0)%Z ->
                       (nonneg (IC εᵢ (z - 1)%Z) + nonneg (IC εᵢ (z + 1)%Z) = 2 * nonneg (IC εᵢ z))%R.
  Proof.
    (* It's linear for z ∈ [-1, ∞) *)
  Admitted.

  (* Credit to amplify within the sequence *)
  Definition AC (εᵢ : nonnegreal) (εₐ : posreal) (p : nat) pwf kwf : nonnegreal :=
    εR 2 (L εᵢ) p εₐ (mk_fRwf _ _ _ kwf pwf).

  Program Definition I (εᵢ : nonnegreal) εₐ (l : loc) kwf : nat -> iProp Σ :=
    fun p => (∃ z: Z, l ↦ #z ∗ € (IC εᵢ p) ∗ ⌜(z < p - 1)%Z⌝ ∗ € (AC εᵢ εₐ ((L εᵢ) - p) _ kwf))%I.
  Next Obligation. intros. lia. Qed.

  (** Credit accounting for the amplifcation *)

  Program Definition kwf_L εᵢ (Hεᵢ : (nonneg εᵢ < 1)%R) : kwf 2 (L εᵢ) := mk_kwf _ _ _ _.
  Next Obligation. intros; lia. Qed.
  Next Obligation. intros. rewrite /L. Admitted. (* doable *)

  Program Definition Δε (εᵢ : nonnegreal) (εₐ : posreal) kwf : nonnegreal :=
    mknonnegreal (εAmp 2 (L εᵢ) εₐ kwf - εₐ)%R _.
  Next Obligation. intros. pose P := (εAmp_amplification 2 (L εᵢ) εₐ kwf). lra. Qed.

  Lemma Δε_exchange (εᵢ : nonnegreal) (εₐ : posreal) kwf :
    € (εAmp 2 (L εᵢ) εₐ kwf) -∗ (€ (Δε εᵢ εₐ kwf) ∗ € (pos_to_nn εₐ)).
  Proof.
    iIntros.
    iApply ec_split.
    iApply ec_spend_irrel; [|iFrame].
    rewrite /Δε /=.
    lra.
  Qed.

  (* This is easy to initialize for sufficiently large i! *)
  Program Definition AX (εᵢ : nonnegreal) (εₐ : posreal) kwf : nat -> nonnegreal :=
    (fun i => mknonnegreal (Rmax 0 (1 - i * (Δε εᵢ εₐ kwf))%R) _).
  Next Obligation. intros; apply Rmax_l. Defined.

  (* Error credit distribution at each amplifications step *)

  Program Definition integer_walk_distr εᵢ εₐ (p : nat) kwf : fin 2 -> nonnegreal :=
    (fun v => if v =? 1
              then (εAmp 2 (L εᵢ) εₐ kwf        + IC εᵢ (p + 1))%NNR  (* moves right; amplification *)
              else (AC εᵢ εₐ ((L εᵢ) - (p - 1)) _ kwf + IC εᵢ (p - 1))%NNR  (* moves left; progress *)).
  Next Obligation. intros. apply PeanoNat.Nat.le_sub_l. Qed.


  (* sampler either gives us progress or amplifies our error *)
  Lemma wp_sampler_amp εᵢ εₐ l p i kwf E :
    ⊢ I εᵢ εₐ l kwf (S p) ∗ € (AX εᵢ εₐ kwf (S i)) -∗
      WP (int_walk_sampler #l) @ E {{ fun _ => ((I εᵢ εₐ l kwf p ∗ € (AX εᵢ εₐ kwf (S i))) ∨
                                     (I εᵢ εₐ l kwf (S (S p)) ∗ € (AX εᵢ εₐ kwf i)))}}.
  Proof.
    iIntros "([%z (Hl & HcrIC & %Hz & HcrAC)] & HcrAX)".
    rewrite /int_walk_sampler.
    wp_pures.
    wp_bind (rand _)%E.

    (* I think we need a special case for z < 0? *)
    wp_apply (wp_couple_rand_adv_comp1 _ _ _ _
                ((IC εᵢ (S p)) + (AC εᵢ εₐ (L εᵢ - S p) (I_obligation_1 εᵢ (S p)) kwf))%NNR
                (integer_walk_distr εᵢ εₐ (S p) kwf) with "[HcrAC HcrIC]").
    { (* Series mean *)
      rewrite SeriesC_fin2.
      admit.
    }
    { (* credit total *)
      iApply ec_split; iFrame. }
    iIntros (s) "Hcr".
    wp_pures.
    destruct (fin_to_bool s) as [|] eqn:sB; last first.
    - assert (Hs : s = 0%fin) by admit.  (* FIXME fin 2 nonsense *)
      rewrite Hs.
      wp_pures; wp_load; wp_pures; wp_store.
      iModIntro.
      iLeft.
      iFrame.
      iExists _; iFrame.
      rewrite /integer_walk_distr /=.
      iAssert (€ (AC εᵢ εₐ (L εᵢ - (p - 0)) (integer_walk_distr_obligation_1 εᵢ (S p)) kwf) ∗ € (IC εᵢ (S p - 1)))%I with "[Hcr]" as "[HcrAmp HcrIC]".
      { iApply ec_split; iFrame. }
      iSplitL "HcrIC".
      { iApply ec_spend_irrel; [|iFrame]. f_equal. f_equal. lia. }
      iSplitR.
      { iPureIntro. lia. }
      iApply ec_spend_irrel; [|iFrame].
      (* some kind of proof irrelevance here, same as the kwf stuff. *)
      admit.
    - assert (Hs : s = 1%fin) by admit.  (* FIXME fin 2 nonsense *)
      rewrite Hs.
      wp_pures; wp_load; wp_pures; wp_store.
      iModIntro.
      (* moved right: amplification *)
      iRight.
      rewrite /integer_walk_distr /=.
      iAssert (€ (εAmp 2 (L εᵢ) εₐ kwf) ∗ € (IC εᵢ (S p + 1)))%I with "[Hcr]" as "[HcrAmp HcrIC]".
      { iApply ec_split; iFrame. }

      assert (HAX: ((AX εᵢ εₐ kwf (S i)) + (Δε εᵢ εₐ kwf) = (AX εᵢ εₐ kwf i))%NNR).
      { Opaque INR.
        rewrite /AX.
        apply nnreal_ext. simpl.
        (* True because (εₐ * k 2 (L εᵢ) kwf - εₐ) > 0*)
        admit.
      }
      iDestruct (Δε_exchange with "HcrAmp") as "(HΔε&Hεₐ)".
      rewrite -HAX.

      iSplitR "HcrAX HΔε"; [|iApply ec_split; iFrame].
      rewrite /I.
      iExists _.
      iFrame.
      iSplitL "HcrIC".
      { iApply ec_spend_irrel; [|iFrame].
        simpl; do 3 f_equal.
        lia. }
      iSplitR.
      { iPureIntro. lia. }
      iApply ec_spend_le_irrel; [|iFrame].
      rewrite /AC.
      simpl nonneg.
      (* holds because fR is <= 1 *)
      admit.

  Admitted.


  (* We can always run the checker with any bound on it's position (with no loss in progress) *)
  Lemma wp_checker_triv εᵢ εₐ l kwf E : forall p, I εᵢ εₐ l kwf p -∗ WP int_walk_checker #l @ E {{fun v => I εᵢ εₐ l kwf p ∗ ∃ b: bool, ⌜v = #b⌝}}.
  Proof.
    iIntros (p) "[%z (Hl & HcrIC & %Hz & HcrAC)]".
    rewrite /int_walk_checker.
    wp_pures; wp_load; wp_pures.
    iModIntro.
    iSplitL.
    - iFrame. eauto.
    - eauto.
  Qed.

  Lemma integer_walk_sampling_scheme (l : loc) εᵢ εₐ kwf E :
    ⊢ (* ⌜(0 < nonneg ε0)%R ⌝ -∗ *)
      incr_sampling_scheme_spec
        (λ: "_", int_walk_sampler #l)
        (λ: "_", int_walk_checker #l)
        (I εᵢ εₐ l kwf)
        (AX εᵢ εₐ kwf)
        (L εᵢ)
        E.
  Proof.
    iSplit.
    - (* Spending rules *)
      iIntros "[Hcr | [%z (Hl & _ & %Hz & _)]]".
      + (* Credit spending rule *)
        wp_apply (wp_ec_spend _ _ _ nnreal_one); simpl; [lra|eauto|].
        iApply (ec_spend_le_irrel with "Hcr"); simpl.
        rewrite Rmult_0_l Rminus_0_r.
        apply Rmax_r.
      + (* Progress spending rule *)
        rewrite /int_walk_sampler; wp_pures.
        wp_bind (rand _)%E; wp_apply wp_rand; eauto.
        iIntros (n) "_"; wp_pures.
        rewrite /int_walk_checker.
        (* the rest of the symbolic execution doesn't change depeding on the value.  *)
        case_bool_decide; repeat (try wp_pures; try wp_load; try wp_store).
        * (* l ↦ -3 *)
          iModIntro. iPureIntro. f_equal. f_equal.
          apply bool_decide_eq_true_2. lia.
        * (* l ↦ -1 *)
          iModIntro. iPureIntro. f_equal. f_equal.
          apply bool_decide_eq_true_2. lia.
    - iModIntro.
      iIntros (i p) "(%Hpwf&HcrAX&HI)".
      wp_pure.
      wp_apply (ub_wp_wand with "[HcrAX HI]"); first iApply (wp_sampler_amp with "[$]").
      iIntros (s) "[(HI&HAX)|(HI&HAX)]".
      + (* progress *)
        iLeft; iFrame.
        iIntros "?"; wp_pure.
        iApply (wp_checker_triv with "[$]").
      + (* amplification *)
        iRight; iFrame.
        (* S (S p) may or may not be less than (L εᵢ), but if it isn't, we have € 1. *)
        destruct (le_lt_eq_dec _ _ Hpwf) as [Hp|Hp].
        * iExists (S (S p)).
          iSplitR; [iPureIntro; lia|].
          iFrame.
          iIntros "?"; wp_pure.
          iApply (wp_checker_triv with "[$]").
        * iExFalso.
          iDestruct "HI" as "[%z (_& HIC &_&_)]".
          assert (Hk :  (Z.of_nat (S (L εᵢ)) >= Z.of_nat (L εᵢ))%Z) by lia.
          Check (IC_ge_L εᵢ (S (L εᵢ)) Hk).
          (* We have an amount of credit greater than or equal to 1, so we conclude *)
  Admitted.
End integer_walk.



Section higherorder_walkSAT.
  (** Demonstration of using the higher-order spec for stateful computation (WalkSAT) *)
  (** This "sampler" does not just return a value, but modifies a state *)
  Local Open Scope R.
  Context `{!ub_clutchGS Σ}.

  Context (N : nat).

  (* an assignment is a list of length N booleans *)
  (* value-level representation for assignments *)
  Inductive inv_asn' : list bool -> val -> Prop :=
    | inv_emp : inv_asn' [] NONEV
    | inv_cons (b : bool) (m' : list bool) (asn' : val) : (inv_asn' m' asn') -> inv_asn' (b :: m') (SOMEV (#b, asn')).
  Definition inv_asn m asn : Prop := length m = N /\ inv_asn' m asn.

  (* stuck expression *)
  Definition error : expr := (#42 #42)%E.

  (* set up a random assignment of n boolean variables *)
  Definition mk_init_asn': val :=
    (rec: "mk_asn'" "n" :=
       if: ("n" = #0)
       then NONE
       else
         let: "b" := (rand #1 = #1) in
         let: "r" := ("mk_asn'" ("n" - #1)) in
         SOME ("b", "r"))%V.
  Definition mk_init_asn : val := (λ: "_", mk_init_asn' #N).


  Lemma init_asn'_inv (M: nat) E : (⊢ WP (mk_init_asn' #M) @ E {{ fun v' => ∃ m, ⌜ inv_asn' m v' /\ length m = M ⌝}})%I.
  Proof.
    iInduction M as [|M'] "IH".
    - rewrite /mk_init_asn'; wp_pures.
      iModIntro; iExists []; iPureIntro; split; [constructor | by simpl].
    - rewrite /mk_init_asn'.
      do 3 wp_pure.
      wp_bind (rand _)%E; wp_apply wp_rand; eauto; iIntros (b) "%Hb".
      do 4 wp_pure.
      replace #(S M' - 1)%Z with #M'; [| do 2 f_equal; lia].
      wp_bind (RecV _ _ _ _).
      wp_apply (ub_wp_wand  with "IH").
      iIntros (asn') "[%m' (%Hm'_inv' & %Hm'_len)]".
      wp_pures.
      iModIntro; iExists ((bool_decide (#b = #1)) :: m').
      iPureIntro; split.
      + by apply inv_cons.
      + rewrite cons_length Hm'_len /=; lia.
  Qed.

  Definition eval_asn : val :=
    (rec: "eval_asn" "asn" "n" :=
       match: "asn" with
          NONE => error
        | SOME "R" => if: ("n" = #0)
                        then (Fst "R")
                        else ("eval_asn" (Snd "R") ("n" - #1))
       end)%V.


  Definition wp_eval_asn m asn E (n : nat) :
    (⊢ ⌜ (n < (length m))%nat ⌝ -∗ ⌜ inv_asn' m asn ⌝ -∗ WP (eval_asn asn #n)%E @ E {{ fun v => ⌜#(m !!! n : bool) = v⌝}})%I .
  Proof.
    iIntros "%Hn %Hinv".
    iRevert (Hn).
    iRevert (n).
    iInduction Hinv as [| b m' asn' Hinv H] "IH".
    - iIntros (? Hk). simpl in Hk; lia.
    - iIntros (n' Hlen).
      rewrite /eval_asn.
      wp_pures.
      case_bool_decide.
      + wp_pures.
        iModIntro; iPureIntro.
        inversion H as [H'].
        by rewrite -(Nat2Z.id n') H' /=.
      + do 3 wp_pure.
        replace (Z.of_nat n' - 1)%Z with (Z.of_nat (n' - 1)%nat); last first.
        { rewrite Nat2Z.inj_sub; try lia.
          pose Hc := Nat.le_0_l; apply (Nat.lt_eq_cases 0%nat n') in Hc.
          destruct Hc; try lia.
          by rewrite -H0 /= Nat2Z.inj_0 in H. }
        destruct n' as [|n''] eqn:Hn'; [by rewrite Nat2Z.inj_0 in H |].
        wp_apply (ub_wp_wand with "[IH]").
        { iApply "IH".
          iPureIntro.
          rewrite cons_length in Hlen.
          apply (Nat.le_lt_add_lt 1%nat 1%nat); try lia. }
        iIntros (v) "%Hv"; iPureIntro.
        rewrite lookup_total_cons_ne_0; try eauto.
        rewrite -Hv Nat.pred_succ.
        by replace (S n'' - 1)%nat with n'' by lia.
  Qed.


  Definition update_asn : val :=
    (rec: "update_asn'" "asn" "n" "b" :=
       match: "asn" with
         NONE => error
        | SOME "R" =>
            if: ("n" = #0)
              then SOME ("b", (Snd "R"))
              else
                let: "b0" := (Fst "R") in
                let: "r0" := ("update_asn'" (Snd "R") ("n" - #1) "b") in
                SOME ("b0", "r0")
       end)%V.

  Definition wp_update_asn m asn E n (b: bool) :
    (⊢ ⌜(n < length m)%nat ⌝ -∗ ⌜inv_asn' m asn ⌝ -∗ WP (update_asn asn #n #b)%E @ E {{ fun asn' => ⌜inv_asn' (<[n := b]> m) asn' ⌝}})%I.
  Proof.
    iIntros "%Hn %Hinv".
    iRevert (Hn).
    iRevert (n).
    iInduction Hinv as [| b' m' asn' Hinv H] "IH".
    - iIntros (? Hk). simpl in Hk; lia.
    - iIntros (n' Hlen).
      rewrite /update_asn.
      wp_pures.
      case_bool_decide.
      + wp_pures.
        iModIntro; iPureIntro.
        inversion H as [H'].
        replace (<[n':=b]> (b' :: m')) with (b :: m'); [by constructor|].
        rewrite -Nat2Z.inj_0 in H'; apply Nat2Z.inj in H'.
        by rewrite H' /=.
      + do 6 wp_pure.
        wp_bind (RecV _ _ _ _ _ _).
        replace (Z.of_nat n' - 1)%Z with (Z.of_nat (n' - 1)%nat); last first.
        { rewrite Nat2Z.inj_sub; try lia.
          pose Hc := Nat.le_0_l; apply (Nat.lt_eq_cases 0%nat n') in Hc.
          destruct Hc; try lia.
          by rewrite -H0 /= Nat2Z.inj_0 in H. }
        wp_apply (ub_wp_wand with "[IH]").
        { iApply "IH".
          iPureIntro.
          rewrite cons_length in Hlen.
          apply (Nat.le_lt_add_lt 1%nat 1%nat); try lia.
          admit. (* doable *)
        }
        iIntros (v) "%Hv".
        wp_pures.
        iModIntro; iPureIntro.
        replace (n')%nat with (S (n' - 1))%nat; last admit. (* provable *)
        simpl.
        by constructor.
  Admitted.

  (* our program will be indexed by a fixed formula to avoid manipulating value-level formulae *)
  Inductive Polarity := Pos | Neg.

  Inductive clause :=
      | ClauseV (e1 e2 e3 : fVar)
    with fVar :=
      | FvarV (p : Polarity) (n : nat) (nwf : (n < N)%nat).
  Definition formula : Type := list (clause).

  Definition fVar_index (v : fVar) : nat :=
    match v with
      | FvarV _ n _ => n
    end.

  Definition fVar_in_clause (v : fVar) (c : clause) : Prop :=
    match c with
      | ClauseV e1 e2 e3  => (v = e1) \/ (v = e2) \/ (v = e3)
    end.

  Definition index_in_clause (n : nat) (c : clause) : Prop :=
    match c with
      | ClauseV e1 e2 e3 => (n = fVar_index e1) \/ (n = fVar_index e1) \/ (n = fVar_index e1)
    end.

  Definition proj_clause_value (c : clause) (target : fin 3) : fVar :=
    match c with
      | (ClauseV e1 e2 e3) =>
          if target =? (0 : fin 3)%fin
            then e1
            else if target =? (1 : fin 3)%fin
                 then e2
                 else e3
      end.


  (* evaluation of the coq-level assignments *)

  Definition fvar_SAT (m : list bool) (v : fVar) : bool :=
    match v with
    | FvarV p n _ =>
        match p with
          | Pos => (m !!! n)
          | Neg => (negb (m !!! n))
        end
    end.

  Definition clause_SAT (m : list bool) (c : clause) : bool :=
    match c with
      | ClauseV e1 e2 e3 => (fvar_SAT m e1) || (fvar_SAT m e2) || (fvar_SAT m e3)
    end.

  Definition formula_SAT (m : list bool) (f : formula) : bool :=
    fold_left (fun acc c => acc && clause_SAT m c) f true.


  (* If there is a solution s, for any unsatisfied clause, the clause contains a variable
      which differers from the solution. *)
  Lemma progress_is_possible_clause (c : clause) (m solution : list bool) :
    (clause_SAT solution c = true) ->
    (clause_SAT m c = false) ->
    exists (v : fVar), (fVar_in_clause v c) /\ (m !!! (fVar_index v) = negb (solution !!! (fVar_index v))).
  Proof.
    intros Hsat Hunsat.
    destruct c as [e1 e2 e3].
    rewrite /clause_SAT /= in Hsat, Hunsat.
    apply orb_false_elim in Hunsat as [Hunsat' He3].
    apply orb_false_elim in Hunsat' as [He1 He2].
    apply orb_prop in Hsat as [Hsat'|Hsat]; first apply orb_prop in Hsat' as [Hsat|Hsat].
    - exists e1; simpl; split; [by left |].
      destruct e1 as [p n nwf]; simpl.
      destruct p; simpl in Hsat, He1.
      + by rewrite Hsat He1 /=.
      + apply negb_true_iff in Hsat, He1; rewrite negb_involutive in He1.
        by rewrite Hsat He1 /=.
    - exists e2; simpl; split; [right; by left|].
      destruct e2 as [p n nwf]; simpl.
      destruct p; simpl in Hsat, He2.
      + by rewrite Hsat He2 /=.
      + apply negb_true_iff in Hsat, He2; rewrite negb_involutive in He2.
        by rewrite Hsat He2 /=.
    - exists e3; simpl; split; [right; by right|].
      destruct e3 as [p n nwf]; simpl.
      destruct p; simpl in Hsat, He3.
      + by rewrite Hsat He3 /=.
      + apply negb_true_iff in Hsat, He3; rewrite negb_involutive in He3.
        by rewrite Hsat He3 /=.
  Qed.



  (* turns the existence of an fvar that can be improved into a concrete sample to amplify against *)
  Lemma reflect_progress_to_target (v : fVar) (c : clause) :
    fVar_in_clause v c -> exists s : fin 3, (proj_clause_value c s = v).
  Proof.
    intros H.
    destruct c as [e1 e2 e3].
    simpl in H; destruct H as [H|[H|H]].
    - exists 0%fin. by simpl.
    - exists 1%fin. by simpl.
    - exists 2%fin. by simpl.
  Qed.


  (* obtains the clause which simplified walkSAT will resample*)
  Lemma find_progress m f :
    (formula_SAT m f = false) ->
    exists f1 f2 c,
      f = f1 ++ [c] ++ f2 /\
      Forall (fun c' => clause_SAT m c' = true) f1 /\
      clause_SAT m c = false.
  Proof.
    intros Hunsat.
    induction f as [|c f' IH].
    - rewrite /formula_SAT /= in Hunsat. discriminate.
    - destruct (clause_SAT m c) as [|] eqn:Hc.
      + assert (Hunsat' : formula_SAT m f' = false).
        { (* true b/c clause_SAT m c is true (another fold commuting problem) *)
          rewrite /formula_SAT /= in Hunsat.
          admit.
        }
        destruct (IH Hunsat') as [f1 [f2 [c' (H & Hf1 & Hc')]]].
        exists (c :: f1), f2, c'; split; last split.
        * by rewrite /= H.
        * apply Forall_cons_2; [apply Hc | apply Hf1].
        * apply Hc'.
      + exists [], f', c; split; last split.
        * by simpl.
        * apply Forall_nil_2.
        * apply Hc.
  Admitted.




  (* this proof measues progress by the similarity to a fixed (known) solution *)
  Definition progress_measure (m solution : list bool) : nat :=
    fold_right (fun p acc => (acc + match p with | (s, t) => if (eqb s t)then 0%nat else 1%nat end)%nat) 0%nat (zip m solution).


  Lemma progress_complete m solution : (length m = length solution) -> (progress_measure m solution = 0%nat) -> m = solution.
  Proof.
    generalize dependent solution.
    induction m as [|m0 ms IH].
    - intros solution Hl _; destruct solution; eauto.
      simpl in Hl; discriminate.
    - intros solution Hl Hp.
      destruct solution as [|s0 ss].
      { simpl in Hl; discriminate. }
      rewrite /progress_measure /fold_left /= in Hp.
      apply Nat.eq_add_0 in Hp; destruct Hp as [Hp Hhp].
      f_equal.
      + apply eqb_eq. destruct (eqb m0 s0); [done|discriminate].
      + apply IH.
        * do 2 rewrite cons_length in Hl; by inversion Hl.
        * by rewrite /progress_measure.
  Qed.


  (* flipping a variable which is different to the solution brings an assignment closer to the solution *)
  Lemma flip_makes_progress (m solution : list bool) (v : fVar) :
      (m !!! (fVar_index v) = negb (solution !!! (fVar_index v))) ->
      (progress_measure (<[fVar_index v := negb (m !!! (fVar_index v))]> m ) solution < progress_measure m solution)%nat.
  Proof.
    intros Hdiff.
    (* Induct over the lists, = when not equal to fVar_index v, < when equal *)
    (* need to show we hit fVar_index... induction should keep track of location? *)
  Admitted.


  (* evaluation of the value-level assignments *)

  Definition evaluate_fvar (f: fVar) : val :=
    (λ: "asn",
       match f with
         | FvarV p n _ =>
             let: "b" := (eval_asn "asn" #n) in
             match p with
               | Pos => "b"
               | Neg => ~"b"
              end
        end).

  Lemma wp_evaluate_fvar l asn m v E :
    (⊢ ⌜ inv_asn m asn ⌝ -∗ l ↦ asn -∗ WP (evaluate_fvar v) asn @ E {{ fun v' => l ↦ asn ∗ ⌜v' = #(fvar_SAT m v)⌝ }} )%I.
  Proof.
    iIntros "%Hinv Hl".
    destruct v as [p v vwf].
    rewrite /evaluate_fvar.
    wp_pures.
    wp_bind (eval_asn _ _)%E.
    wp_apply (ub_wp_wand with "[]").
    { iApply wp_eval_asn; iPureIntro; last first.
      - rewrite /inv_asn in Hinv. by destruct Hinv.
      - destruct Hinv; lia. }
    iIntros (b) "<-".
    destruct p; wp_pures; iModIntro; eauto.
  Qed.


  Definition evaluate_clause (c : clause) : val :=
    (λ: "asn",
        match c with
         | ClauseV e1 e2 e3 => ((evaluate_fvar e1 "asn") || (evaluate_fvar e2 "asn") || (evaluate_fvar e3 "asn"))
        end)%V.

  Lemma wp_evaluate_clause l asn m c E :
    (⊢ ⌜ inv_asn m asn ⌝ -∗ l ↦ asn -∗ WP (evaluate_clause c) asn @ E {{ fun v => l ↦ asn ∗ ⌜v = #(clause_SAT m c)⌝ }} )%I.
  Proof.
    iIntros "%Hinv Hl".
    destruct c as [e1 e2 e3].
    rewrite /evaluate_clause.
    wp_pures.
    wp_bind (evaluate_fvar _ _).
    wp_apply (ub_wp_wand with "[Hl]").
    { iApply wp_evaluate_fvar; [eauto|iFrame]. }
    iIntros (s1) "(Hl&%Hs1)".
    destruct (fvar_SAT m e1) as [|] eqn:HeqS1; rewrite Hs1; wp_pures.
    { iModIntro; iFrame; iPureIntro; f_equal. simpl; by rewrite HeqS1. }
    wp_bind (evaluate_fvar _ _).
    wp_apply (ub_wp_wand with "[Hl]").
    { iApply wp_evaluate_fvar; [eauto|iFrame]. }
    iIntros (s2) "(Hl&%Hs2)".
    destruct (fvar_SAT m e2) as [|] eqn:HeqS2; rewrite Hs2; wp_pures.
    { iModIntro; iFrame; iPureIntro; f_equal. simpl; by rewrite HeqS2 orb_true_r. }
    wp_apply (ub_wp_wand with "[Hl]").
    { iApply wp_evaluate_fvar; [eauto|iFrame]. }
    iIntros (s3) "(Hl&%Hs3)".
    destruct (fvar_SAT m e3) as [|] eqn:HeqS3; rewrite Hs3.
    { iFrame; iPureIntro; f_equal. simpl; by rewrite HeqS3 orb_true_r. }
    iFrame; iPureIntro; f_equal.
    by rewrite /= HeqS1 HeqS2 HeqS3 /=.
  Qed.


  (** WALKSAT (simplified version): Find the first UNSAT clause and randomly flip a variable from it *)


  Definition clause_to_index (c : clause) : val :=
    (λ: "i",
       match c with
       | (ClauseV e1 e2 e3) =>
           (if: ("i" = #0)
            then #(fVar_index e1)
            else if: ("i" = #1)
                 then #(fVar_index e2)
                 else #(fVar_index e3))%E
       end)%V.


  Lemma wp_clause_to_index (c: clause) (target : fin 3) E :
    ⊢ (WP (clause_to_index c #target)%E @ E {{ fun i => ⌜ i = #(fVar_index (proj_clause_value c target))⌝ }})%I.
  Proof.
    iStartProof; rewrite /clause_to_index /proj_clause_value /fVar_index.
    destruct c.
    destruct target; simpl; wp_pures; eauto.
    destruct target; simpl; wp_pures; eauto.
    rewrite (bool_decide_false); first (wp_pures; eauto).
    rewrite /not; intros Hk; inversion Hk; lia.
  Qed.

  (* selects a variable references in the clause, and flips it *)
  Definition resample_clause (c : clause) : val :=
    (λ: "l",
       let: "asn" := (! "l") in
       let: "n" := clause_to_index c (rand #2) in
       let: "b" := eval_asn "asn" "n" in
       "l" <- (update_asn "asn" "n" (~ "b")))%V.

  Definition εFac : nonnegreal := (nnreal_div (nnreal_nat 3) (nnreal_nat 2)).

  (* amplify using the 1/6 chance that the resampler flips a variable "target" *)
  (* this proof repeats itself, I think I could refactor my lemmas above to make it cleaner.
     in any case, this follows directly by symbolic execution. *)
  Lemma resample_amplify (c : clause) (target : fin 3) (m : list bool) (l: loc) ε (asn : val) E :
    inv_asn m asn ->
    ⊢ (l ↦ asn -∗
       € ε -∗
       WP (resample_clause c #l)%E @ E
         {{ fun _ => ∃ asn' m', (l ↦ asn') ∗ ⌜inv_asn m' asn' ⌝ ∗
                              ((⌜(m' !!! (fVar_index (proj_clause_value c target))) = (negb (m !!! (fVar_index (proj_clause_value c target)))) ⌝) ∨
                               (€ (ε * εFac)%NNR ))}})%I.
  Proof.
    iIntros (Hinv) "Hl Hε".
    Opaque update_asn.
    rewrite /resample_clause.
    wp_pures.
    wp_apply (wp_load with "Hl").
    iIntros "Hl".
    wp_pures.
    wp_bind (rand _)%E.
    wp_apply (wp_couple_rand_adv_comp1 _ _ _ _ ε
                (fun s => if (s =? target)
                         then (nnreal_nat 0%nat)%NNR
                         else (ε * (nnreal_div (nnreal_nat 3%nat) (nnreal_nat 2%nat)))%NNR)
              with "Hε").
    { (* (0 + 3/2 + 3/2) / 3 = 1 *)
      admit. }
    iIntros  (i) "Hcr".
    destruct (i =? target) eqn:Hi.
    - (* sampler chooses the target index; flips it *)
      wp_bind (clause_to_index c _)%E.
      wp_apply (ub_wp_wand); first iApply (wp_clause_to_index c i).
      iIntros (i') "->".
      wp_pures.
      wp_bind (eval_asn _ _)%E.
      wp_apply (ub_wp_wand with "[]").
      { iApply wp_eval_asn; iPureIntro; last first.
        - rewrite /inv_asn in Hinv. by destruct Hinv.
        - destruct (proj_clause_value c i) as [? ? ?].
          destruct Hinv as [? ?] .
          simpl; lia. }
      iIntros (v) "<-".
      wp_pures.
      wp_bind (update_asn _ _ _).
      wp_apply (ub_wp_wand with "[]").
      { iApply wp_update_asn; iPureIntro; last first.
        - rewrite /inv_asn in Hinv. by destruct Hinv.
        - destruct (proj_clause_value c i) as [? ? ?].
          destruct Hinv as [? ?] .
          simpl; lia. }
      iIntros (v) "%Hinv'".
      wp_pures.
      wp_store.
      iModIntro.
      iExists _, _.
      iFrame.
      iSplitR.
      { iPureIntro; split; [|eapply Hinv'].
        rewrite insert_length.
        by destruct Hinv.  }
      iLeft.
      iPureIntro.
      apply Nat.eqb_eq in Hi.
      replace i with target; [|by apply fin_to_nat_inj].
      apply list_lookup_total_insert.
      destruct (proj_clause_value c target) as [? ? ?].
      simpl; destruct Hinv; lia.
    - (* sampler chooses the wrong index, step through and conclude by the amplification  *)
      wp_bind (clause_to_index c _)%E.
      wp_apply (ub_wp_wand); first iApply (wp_clause_to_index c i).
      iIntros (i') "->".
      wp_pures.
      wp_bind (eval_asn _ _)%E.
      wp_apply (ub_wp_wand with "[]").
      { iApply wp_eval_asn; iPureIntro; last first.
        - rewrite /inv_asn in Hinv. by destruct Hinv.
        - destruct (proj_clause_value c i) as [? ? ?].
          destruct Hinv as [? ?] .
          simpl; lia. }
      iIntros (v) "<-".
      wp_pures.
      wp_bind (update_asn _ _ _).
      wp_apply (ub_wp_wand with "[]").
      { iApply wp_update_asn; iPureIntro; last first.
        - rewrite /inv_asn in Hinv. by destruct Hinv.
        - destruct (proj_clause_value c i) as [? ? ?].
          destruct Hinv as [? ?] .
          simpl; lia. }
      iIntros (v) "%Hinv'".
      wp_pures; wp_store.
      iModIntro.
      iExists _, _; iFrame.
      iPureIntro.
      split; last apply Hinv'.
      rewrite insert_length.
      by destruct Hinv.
  Admitted.


  Fixpoint sampler (f : formula) : val :=
    (λ: "asnV",
        match f with
          | [] => #()
          | (c :: cs) =>
              if: (evaluate_clause c) (! "asnV")
                then (sampler cs) "asnV"
                else (resample_clause c) "asnV"
        end)%V.

  Fixpoint checker (f : formula) : val :=
    (λ: "asnV",
       match f with
        | [] => #true
        | (c :: cs) => (evaluate_clause c (! "asnV")) && (checker cs "asnV")
        end).


  (* running the checker *)
  Lemma wp_check l asn m f E :
    (⊢ ⌜ inv_asn m asn ⌝ -∗ l ↦ asn -∗ ((WP ((Val (checker f)) #l) @ E {{ λ v', l ↦ asn ∗ ⌜v' = #(formula_SAT m f)⌝ }})))%I.
  Proof.
    iInduction f as [|c f'] "IH".
    - iIntros "%Hinv Hl".
      rewrite /checker.
      wp_pures.
      iModIntro; iFrame; iPureIntro; f_equal.
    - iIntros "%Hinv Hl".
      wp_pures.
      wp_bind (! _)%E.
      wp_load.
      wp_bind (evaluate_clause _ _)%E.
      wp_apply (ub_wp_wand with "[Hl]").
      { wp_apply wp_evaluate_clause; [|iFrame]. iPureIntro. eapply Hinv.  }
      iIntros (ev) "(Hl&->)".
      destruct (clause_SAT m c) as [|] eqn:Hcsat.
      + wp_pure.
        wp_apply (ub_wp_wand with "[Hl]").
        { iApply "IH"; [eauto|iFrame]. }
        iIntros (v) "(Hl&%Hf')".
        iFrame; iPureIntro.
        rewrite Hf'; f_equal.
        by rewrite {2}/formula_SAT /= Hcsat /formula_SAT.
      + wp_pures.
        iModIntro; iFrame; iPureIntro; f_equal.
        rewrite /formula_SAT /= Hcsat.
        induction f' as [|? ? ?]; simpl; done.
  Qed.


  (* running the sampler when the formula is SAT (equal to the solution or not) does nothing *)
  Lemma wp_sampler_done l asn m f E :
    (⊢ ⌜formula_SAT m f = true ⌝ -∗
       ⌜ inv_asn m asn ⌝ -∗
       l ↦ asn -∗
       (WP ((Val (sampler f)) #l) @ E {{ λ v', l ↦ asn }}))%I.
  Proof.
    iInduction f as [|c f'] "IHf".
    - iIntros "? ? ?".
      rewrite /sampler /=.
      wp_pures.
      iModIntro; iFrame.
    - iIntros "%Hsat %Hinv Hl".
      rewrite {2}/sampler.
      wp_pures.
      wp_bind (! _)%E.
      wp_load.
      wp_pures.
      wp_bind (evaluate_clause _ _)%E.
      wp_apply (ub_wp_wand with "[Hl]").
      { wp_apply wp_evaluate_clause; [|iFrame].
        iPureIntro. eapply Hinv.  }
      iIntros (v) "(Hl&->)".
      rewrite /formula_SAT /= in Hsat.
      assert (Hcsat: (clause_SAT m c && fold_left (λ (acc : bool) (c : clause), acc && clause_SAT m c) f' true) = true).
      { (* commuting problem (fixable, even if maybe manually) *)
        admit. }
      apply andb_prop in Hcsat; destruct Hcsat as [Hcsat Hfsat].
      rewrite Hcsat.
      wp_pures.
      iApply "IHf".
      + iPureIntro. by rewrite /formula_SAT.
      + iPureIntro; done.
      + iFrame.
  Admitted.



  Lemma wp_sampler_amplify l asn m solution f ε E :
    (⊢ ⌜formula_SAT solution f = true ⌝ -∗
       ⌜formula_SAT m f = false ⌝ -∗
       ⌜ inv_asn m asn ⌝ -∗
       l ↦ asn -∗
       € ε -∗
       (WP ((Val (sampler f)) #l) @ E
          {{ λ v', ∃ asn' m', l ↦ asn' ∗ ⌜ inv_asn m' asn' ⌝ ∗
                      (⌜(progress_measure m' solution < progress_measure m solution)%nat ⌝ ∨
                       € (ε * εFac)%NNR) }}))%I.
    Proof.
      iIntros "%Hsol %Hm %Hinv Hl Hε".
      destruct (find_progress _ _ Hm) as [f1 [f2 [c (-> & Hf1 & Hc)]]].
      (* induct over the SAT clauses doing nothing *)
      iInduction f1 as [| c' f1'] "IH"; last first.
      { assert (Hc': clause_SAT m c' = true) by admit. (* uses Hf1*)
        rewrite /sampler.
        wp_pures.
        wp_load.
        wp_bind (evaluate_clause _ _)%E.
        wp_apply (ub_wp_wand with "[Hl]").
        { wp_apply (wp_evaluate_clause with "[] Hl").
          iPureIntro; eauto. }
        iIntros (r) "(Hl&->)".
        rewrite Hc'.
        wp_pure.
        wp_apply ("IH" with "[] [] [] Hl Hε").
        - admit. (* by Hm and Hc'*)
        - admit. (* by Hsol*)
        - admit. (* by Hf1*)
      }
      simpl app.

      (* Now we start with an UNSAT clause, so do the amplification at the resample step *)
      rewrite /sampler.
      wp_pures.
      wp_load.
      wp_bind (evaluate_clause _ _)%E.
      wp_apply (ub_wp_wand with "[Hl]").
      { wp_apply (wp_evaluate_clause with "[] Hl"). iPureIntro; eapply Hinv. }
      iIntros (r) "(Hl&->)".
      rewrite Hc; wp_pures.
      wp_apply (ub_wp_wand with "[Hε Hl]").
      { wp_apply (resample_amplify with "Hl Hε").  eapply Hinv. }

      iIntros (s) "[%asn' [%m' (Hl & %Hasn' & Hs)]]".
      iExists _, _.
      iFrame.
      iSplit; [iPureIntro; eapply Hasn'|].
      iDestruct "Hs" as "[%H|Hε]".

      - (* Flip is lucky and makes progress *)
        iLeft.
        iPureIntro.
        (* the lemma I proved before seems almost usable *)


      (* Lemma flip_makes_progress (m solution : list bool) (v : fVar) :
         (m !!! (fVar_index v) = negb (solution !!! (fVar_index v))) ->
         (progress_measure (<[fVar_index v := negb (m !!! (fVar_index v))]> m ) solution
         < progress_measure m solution)%nat. *)

        admit.

      - iRight; iFrame.
  Admitted.



  (*
  Lemma walksat_sampling_scheme (f : formula) solution (l : loc) E :
    (⊢ ⌜formula_SAT solution f = true ⌝ -∗
       ⌜length solution = N ⌝ -∗
       ⌜(length f > 0)%nat ⌝ -∗
        incremental_sampling_scheme_spec
          (λ: "_", (sampler f) #l)%V
          (λ: "_", (checker f) #l)%V
          (fun n => ∃ asn m,
                      (l ↦ asn ∗
                      ⌜ inv_asn m asn ⌝ ∗
                      ⌜(progress_measure m solution <= n)%nat⌝))
          εFac
          (nnreal_nat 1%nat)
          E)%I.
  Proof.
    iIntros "%Hsolution %Hsl %Hnontrivial".
    rewrite /incremental_sampling_scheme_spec.
    iSplit.
    - iIntros (Φ) "!> [Hcr | [%asn [%m (Hl&%Hinv&%Hp)]]] HΦ".
      + (* € 1 case: spend *)
        iApply (wp_ec_spend with "Hcr"); [|auto].
        simpl; lra.
      + (* Ψ 0 case *)
        apply Nat.le_0_r in Hp.
        apply (progress_complete _) in Hp; [|destruct Hinv; lia].
        simplify_eq.
        (* using Ψ, asn now equals the solution. step the sampler... *)
        wp_pures.
        wp_apply (ub_wp_wand with "[Hl]").
        { wp_apply wp_sampler_done; try by iPureIntro. iFrame. }
        iIntros (v) "Hl".
        iApply "HΦ".
        (* then step the checker... *)
        wp_pures.
        wp_apply (ub_wp_wand with "[Hl]").
        { iApply wp_check; [|iFrame].
          iPureIntro; apply Hinv. }
        iIntros (r) "(Hl&->)"; iPureIntro; do 2 f_equal.
        done.
    - iIntros (ε p Φ) "!> (Hε&[%asn [%m (Hl&%Hinv&%Hp)]]) HΦ".
      wp_pures.
      (* step the sampler differently depending on if it is SAT *)
      destruct (formula_SAT m f) as [|] eqn:Hsat.
      + (* SAT: we can't make progress or amplify, but that is be okay, since we can pass the check *)
        wp_apply (ub_wp_wand with "[Hl]").
        { wp_apply wp_sampler_done; try by iPureIntro. iFrame. }
        iIntros (?) "Hl".
        iApply "HΦ".
        (* go directly to jail, do not pass go, do not collect € εFac *)
        iLeft.
        wp_pures.
        wp_apply (ub_wp_wand with "[Hl]").
        { iApply wp_check; [|iFrame].
          iPureIntro. eapply Hinv. }
        iIntros (?) "(Hr&->)"; iPureIntro.
        do 2 f_equal. done.
      + (* UNSAT *)

        wp_apply (ub_wp_wand with "[Hl Hε]").
        { wp_apply (wp_sampler_amplify with "[] [] [] Hl Hε"); iPureIntro.
          - apply Hsolution.
          - apply Hsat.
          - apply Hinv. }

        iIntros (s) "[%Hasn' [%Hm' (Hl & %Hinv' & [Hp | Hε])]]".
        * (* amkes progress *)
          iApply "HΦ".
          iRight. iLeft.

          (* PROBLEM: Spec needs to let credit decrease in the good cases
             so really, the invariant should connect a lower bound of credit
             and an upper bound on progress
           *)
          admit.

        * iApply "HΦ".
          iRight. iRight.
          iExists _, _.
          iFrame.
          iSplitR; [iPureIntro|].
          { (* something backwards here *) admit.  }
          iSplitL.
          -- iExists _, _.
             iFrame.
             iSplit; iPureIntro; eauto.
          -- wp_pures.
             wp_apply ub_wp_wand.
             (* Also a problem: I lose l ↦ asn' here. I guess I need to use proper invariants instead of Ψ? *)
             { iApply (wp_check with "[]"); admit. }
             iIntros (?) "(? & ->)". iPureIntro; eexists; eauto.
  Abort.
*)


  (*
  Lemma ho_spec_is_incremental (sampler checker : val) (εfactor εfinal : nonnegreal) E :
    ⊢ sampling_scheme_spec sampler checker εfactor εfinal E -∗ incremental_sampling_scheme_spec sampler checker (fun n: nat => ⌜False⌝) εfactor εfinal E.
  Proof.
    iIntros "(#Hamp&#Hspend)".
    rewrite /incremental_sampling_scheme_spec.
    iSplit.
    - iIntros (Φ) "!> [Hcr|?] HΦ"; [|iExFalso; iFrame].
      iSpecialize ("Hspend" $! #()).
      wp_apply (ub_wp_wand with "[Hcr]").
      + iApply ("Hspend" with "Hcr").
        iNext.  (* sus *)
        iIntros (?) "Hr".
        iApply "Hr".
      + iIntros (?).
        (* problem: need to strip a later here *)
        admit.
    - iIntros (ε p) "!>"; iIntros (Φ) "Hcr HΦ".
      iSpecialize ("Hamp" $! ε with "Hcr").
      iApply "Hamp".
      iNext.
      iIntros (v).
      iSpecialize ("HΦ" $! v).
      (* very sus *)
    Abort.
   *)

End higherorder_walkSAT.

  (*

  Definition incremental_sampling_scheme_spec' (sampler checker : val) Ψ εfactor εfinal E : iProp Σ
    := (* 0: we always need to be able to construct some progress measurement *)
       (  (* 1. After some amount of progress, we can ensure the checker will pass *)
          (* 2. We can always spend εfinal to obtain a sample which will surely pass *)
          {{{ € εfinal ∨ Ψ 0%nat }}}
            ((Val sampler) #())%E @ E
          {{{ (v : val), RET v; WP ((Val checker) v) @ E {{ λ v', ⌜v' = #true ⌝ }}}}} ∗
          (* 3. Given any amount of credit and progress, the sampler will either... *)
          (∀ ε p,
            {{{ € ε ∗ Ψ (S p)}}}
              ((Val sampler) #())%E @ E
            {{{ (v : val), RET v;
                (* 3.0 just get lucky and end up done *)
                (WP ((Val checker) v) @ E {{ λ v', ⌜v' = #true⌝ }}) ∨
                (* 3.1: obtain a sample which makes progress without consuming error, or *)
                (€ ε ∗ Ψ p ∗ ((WP ((Val checker) v) @ E {{ λ v', ⌜exists b: bool, v' = #b⌝ }}))) ∨
                (* 3.2: amplifies the error by a factor, possibly losing progress *)
                (∃ ε' p', € ε' ∗ ⌜(ε <= ε' * εfactor)%NNR ⌝ ∗ Ψ p' ∗ (WP ((Val checker) v) @ E {{ λ v', ⌜exists b: bool, v' = #b⌝ }}))}}}))%I.

  Lemma ho_incremental_ubdd_approx_safe (sampler checker : val) Ψ p (εfactor εfinal : nonnegreal) (depth : nat) E :
    (0 < εfactor < 1) ->
    (0 < εfinal < 1) ->
    incremental_sampling_scheme_spec' sampler checker Ψ εfactor εfinal E -∗
    ▷ € (generic_geometric_error εfactor εfinal depth) -∗
    Ψ p -∗
    (WP (ho_ubdd_rejection_sampler sampler checker) @ E {{ fun v => ∃ v', ⌜ v = SOMEV v' ⌝}})%I.
  Proof.
    iIntros ([Hfactor_lb Hfactor_ub] [Hfinal_lb Hfinal_ub]) "(#Haccept & #Hamplify) Hε HΨ".
    do 7 wp_pure.
    (* outermost induction should be on depth, generalized over p, since amplification can lose progress *)
    iInduction depth as [|depth' Hdepth'] "IH" forall (p).
    - (* depth=0, ie we have €εfinal *)
      wp_pures.
      wp_bind (sampler #())%E.
      wp_apply ("Haccept" with "[Hε]").
      { iLeft. iApply (ec_spend_irrel with "Hε"). rewrite /generic_geometric_error /=. lra. }
      iIntros (v) "Hcheck".
      wp_pures.
      wp_bind (checker v)%E.
      wp_apply (ub_wp_wand with "Hcheck").
      iIntros (r) "->".
      wp_pures.
      iModIntro; eauto.
    - (* depth > 0; either make sufficient progress or amplify. *)
      iInduction p as [|p'] "IHp". (* FIXME: this should be strong induction but iInduction isn't happy with that  *)
      + (* p = 0; progress complete *)
        wp_pures; wp_bind (sampler #())%E.
        wp_apply ("Haccept" with "[HΨ]"); [iRight; eauto|].
        iIntros (v) "Hcheck".
        wp_pures.
        wp_bind (checker v)%E.
        wp_apply (ub_wp_wand with "Hcheck").
        iIntros (r) "->".
        wp_pures.
        iModIntro; eauto.
      + (* p > 0, make progress or amplify *)
        wp_pures.
        wp_pures; wp_bind (sampler #())%E.
        wp_apply ("Hamplify" with "[$]").
        iIntros (v) "[Hluck|[(Hε&HΨ&Hcheck)|[%ε'[%p'' (Hε&%Hamp&Hp''&Hcheck)]]]]".
        * (* very lucky sample: we are done *)
          wp_pures.
          wp_apply (ub_wp_wand with "Hluck").
          iIntros (?) "->".
          wp_pures.
          iModIntro; eauto.
        * (* lucky sample: makes progress *)
          wp_pures.
          wp_bind (checker _)%E.
          wp_apply (ub_wp_wand with "Hcheck").
          iIntros (r) "[%b ->]".
          destruct b.
          -- (* lucky day, checker accepts! *)
             wp_pures; iModIntro; eauto.
          -- (* checker rejects (but we keep the progress) *)
             wp_pure. wp_apply ("IHp" with "[$] [$]").
        * (* unlucky guess, progress may get worse but we can amplify *)
          wp_pures.
          wp_bind (checker _)%E.
          wp_apply (ub_wp_wand with "Hcheck").
          iIntros (r) "[%b ->]".
          destruct b.
          -- (* really lucky day! checker accepts on bad sample *)
             wp_pures. iModIntro; eauto.
          -- (* use the amplified credit *)
             wp_pure.
             wp_apply ("IH" with "[Hε] Hp''").
             iApply (ec_spend_le_irrel with "Hε").
             simpl in Hamp.
             rewrite /generic_geometric_error /=.
             rewrite (Rmult_comm εfactor) -Rmult_assoc in Hamp.
             apply (Rmult_le_reg_r εfactor); done.
  Qed.
*)

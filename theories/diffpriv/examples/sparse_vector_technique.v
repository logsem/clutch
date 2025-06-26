From iris.base_logic Require Export na_invariants.
From clutch.common Require Import inject.
From clutch.prelude Require Import tactics.
From clutch.prob Require Import differential_privacy.
From clutch.diffpriv Require Import adequacy diffpriv proofmode.
From clutch.diffpriv.examples Require Import list.


Section svt.
  Context `{!diffprivGS Σ}.

  #[local] Open Scope R.

  Lemma Rdiv_pos_pos x y a (div_pos: 0 < x/y) (den_pos : 0 < a) : 0 < x / (a*y).
  Proof.
    destruct (Rdiv_pos_cases _ _ div_pos) as [[]|[]].
    - apply Rdiv_pos_pos ; real_solver.
    - apply Rdiv_neg_neg ; try real_solver.
      rewrite Rmult_comm.
      apply Rmult_neg_pos => //.
  Qed.

  Lemma Rdiv_nneg_nneg x y a (div_nneg: 0 <= x/y) (den_nneg : 0 <= a) : 0 <= x / (a*y).
  Proof.
    destruct (Rle_lt_or_eq _ _ div_nneg) as [|h].
    - destruct (Rle_lt_or_eq _ _ den_nneg).
      + left. apply Rdiv_pos_pos => //.
      + subst. rewrite Rmult_0_l. rewrite Rdiv_0_r. done.
    - rewrite Rmult_comm. rewrite Rdiv_mult_distr. rewrite -h. rewrite /Rdiv. lra.
  Qed.

  Lemma Rdiv_pos_den_0 x y (div_pos : 0 < x/y) : ¬ y = 0.
  Proof.
    intro d0. rewrite d0 in div_pos. rewrite Rdiv_0_r in div_pos. lra.
  Qed.


  (* above_threshold ((num/den) : Q) (T : Z) (db : DB) (qᵢ : DB -o Z) : option (DB -o Z)  *)
  (* "give me ↯ε and I'll privately find a query qᵢ above T" *)

  (* in terms of affine / quantitative resources: *)
  (* "give me ↯ε and I'll privately find a query qᵢ above T ONCE" *)
  (* "for ↯ε you get a value that you can use once to privately find a query qᵢ above T" *)


  (* { ↯ ε } A_T T { f . f : (DB -o Z) -> DB -o option Z }  *)

  (* We can give the following naive specs: *)
  (* { ↯ ε } A_T T ~ AT T
     { f f' . AUTH
            ∗ ∀ db db' : adjacent, ∀ q : 1-sensitive,
[equality post:]
              { AUTH } f db q ~ f' db' q { b : bool . b = false -∗ AUTH }
[or pointwise eq:]
              ∀ R , { AUTH } f db qi ~ f db' qi { b b' : bool . ⌜b = R -> b' = R⌝ ∗ (⌜R = false⌝ -∗ AUTH) }
     }  *)
  Definition above_threshold : val :=
    λ:"num" "den" "T",
      let: "T'" := Laplace "num" (#2*"den") "T" in
      let: "reset" := ref #false in
      λ:"db",
        let: "f" :=
          (λ: "qi",
             if: ! "reset" then
               NONE
             else
               (let: "vi" := Laplace "num" (#4*"den") ("qi" "db") in
                (if: "T'" ≤ "vi" then
                   "reset" <- #true ;;
                   SOME #true
                 else
                   SOME #false)))
        in "f".

  (* We don't actually need `reset` since it is always set to `false` so long as a client holds AUTH. *)
  Definition above_threshold_no_flag : val :=
    λ:"num" "den" "T",
      let: "T'" := Laplace "num" (#2*"den") "T" in
      λ:"db" "qi",
        let: "vi" := Laplace "num" (#4*"den") ("qi" "db") in
        "T'" ≤ "vi".


  (* For the version with the flag, we can prove the following point-wise spec where the
  postcondition does some additional book-keeping to connect the result R to the return values when
  we decide on whether AUTH should be returned. *)
  Lemma above_threshold_online_spec_pw (num den T : Z) (εpos : 0 < IZR num / IZR den) `(dDB : Distance DB) (db db' : DB) (adj : dDB db db' <= 1) K :
    ↯m (IZR num / IZR den) -∗
    ⤇ fill K ((Val above_threshold) #num #den #T (Val (inject db')))
    -∗
    WP (Val above_threshold) #num #den #T (Val (inject db))
       {{ f, ∃ f' : val,
             ⤇ fill K (Val f') ∗
             ∃ AUTH : iProp Σ,
               AUTH ∗
               ( ∀ q, wp_sensitive (Val q) 1 dDB dZ -∗
                      AUTH -∗
                      ⤇ fill K (f' q) -∗
                      ∀ R : bool,
                        WP (Val f) (Val q)
                          {{ v, ∃ v', ⤇ fill K (Val v') ∗
                                      ⌜ v = SOMEV #R → v' = SOMEV #R ⌝ ∗
                                      (⌜R = false ∧ v = v' ∧ v = SOMEV #R⌝ -∗ AUTH)
               }} )
       }}.
  Proof with (tp_pures ; wp_pures).
    iIntros "ε rhs". rewrite /above_threshold...
    tp_bind (Laplace _ _ _). wp_bind (Laplace _ _ _).
    set (ε := (IZR num / IZR den)). replace ε with (ε / 2 + ε / 2) by real_solver.
    fold ε in εpos.
    iDestruct (ecm_split with "ε") as "[ε ε']". 1,2: real_solver.
    iApply (hoare_couple_laplace _ _ 1%Z 1%Z with "[$rhs ε']") => //.
    1: apply Zabs_ind ; lia.
    1: rewrite mult_IZR ; apply Rdiv_pos_pos. 1,2: real_solver.
    { iApply ecm_eq. 2: iFrame. subst ε. replace (IZR (2 * den)) with (2 * IZR den).
      2: qify_r ; zify_q ; lia.
      field. eapply Rdiv_pos_den_0 => //.
    }
    iIntros (T') "!> rhs" => /=...
    tp_alloc as reset_r "reset_r". wp_alloc reset_l as "reset_l"...
    iModIntro. iExists _. iFrame.
    iExists (↯m (ε / 2) ∗ reset_r ↦ₛ #false ∗ reset_l ↦ #false)%I. iFrame.
    iIntros "%q q_sens (ε & reset_r & reset_l) rhs %R"... tp_load. wp_load...

    tp_bind (q _). wp_bind (q _). rewrite /wp_sensitive.
    iSpecialize ("q_sens" $! _ _ db db'). iSpecialize ("q_sens" with "rhs").
    Unshelve. 2: lra.
    iPoseProof (wp_frame_l with "[reset_r $q_sens]") as "q_sens". 1: iAssumption.
    iPoseProof (wp_frame_l with "[reset_l $q_sens]") as "q_sens". 1: iAssumption.
    iPoseProof (wp_frame_l with "[ε $q_sens]") as "q_sens". 1: iAssumption.
    iApply (wp_mono with "q_sens").
    iIntros (?) "(ε & reset_l & reset_r & %vq_l & %vq_r & -> & rhs & %adj')" => /=...
    assert (-1 <= vq_l - vq_r <= 1)%Z as [].
    {
      rewrite Rmult_1_l in adj'.
      assert (dZ vq_l vq_r <= 1) as h by (etrans ; eauto).
      revert h.
      rewrite /dZ/distance Rabs_Zabs.
      apply Zabs_ind ; intros ? h; split.
      all: pose proof (le_IZR _ _ h) ; lia.
    }
    (* case on whether the result is the one that will get released (pweq) *)
    destruct R eqn:HR.
    - tp_bind (Laplace _ _ _). wp_bind (Laplace _ _ _).
      iApply (hoare_couple_laplace vq_l vq_r 1%Z 2%Z with "[$rhs ε]") => //.
      1: apply Zabs_ind ; lia.
      1: rewrite mult_IZR ; apply Rdiv_pos_pos ; real_solver.
      { subst ε. iApply ecm_eq. 2: iFrame. rewrite mult_IZR. field. eapply Rdiv_pos_den_0 => //. }
      iIntros "%vi !> rhs" => /=...
      case_bool_decide (_ (T' + 1)%Z _) ; tp_pures ; try tp_store ; tp_pures. all: case_bool_decide...
      all: try tp_store ; try wp_store ; try tp_pures ; try wp_pures.
      + iFrame. iModIntro. iSplitR. 1: done.
        iIntros ((h_R & h_vv' & h_vR)). exfalso. inversion h_R.
      + exfalso. lia.
      + exfalso. lia.
      + iFrame. iSplitR. 1: done. iModIntro.
        iIntros ((h_R & h_vv' & h_vR)). exfalso. inversion h_R.
    - tp_bind (Laplace _ _ _). wp_bind (Laplace _ _ _).
      iMod ecm_zero as "ε0".
      iApply (hoare_couple_laplace vq_l vq_r (vq_r - vq_l)%Z 0%Z with "[$rhs ε0]") => //.
      1: apply Zabs_ind ; lia.
      1: rewrite mult_IZR ; apply Rdiv_pos_pos ; real_solver.
      1: rewrite Rmult_0_l ; iFrame.
      iIntros "%vi !> rhs" => /=...
      case_bool_decide (_ (T' + 1)%Z _) ; tp_pures ; try tp_store ; tp_pures. all: case_bool_decide...
      all: try tp_store ; try wp_store ; try tp_pures ; try wp_pures.
      + iFrame. iModIntro. iSplitR. 1: done.
        iIntros ((_h_R & h_vv' & h_vR)). exfalso. inversion h_vR.
      + exfalso. lia.
      + iFrame. iModIntro. iSplitR. 1: done.
        iIntros ((_h_R & h_vv' & h_vR)). exfalso. inversion h_vR.
      + iFrame. done.
  Qed.

  Definition AT_spec (AUTH : iProp Σ) (f f' : val) : iProp Σ :=
    ∀ (DB : Type) (dDB : Distance DB) (db db' : DB)
      (_ : dDB db db' <= 1) (q : val) (K0 : list ectx_item),
      wp_sensitive q 1 dDB dZ -∗
      AUTH -∗
      ⤇ fill K0 (f' (inject db') q) -∗
      ∀ R2 : bool,
        WP f (inject db) q
          {{ v,
               ∃ v' : val, ⤇ fill K0 v' ∗ ⌜v = #R2 → v' = #R2⌝ ∗
                           ∃ (b b' : bool), ⌜v = #b⌝ ∗ ⌜v' = #b'⌝ ∗
                           (⌜R2 = false⌝ -∗ AUTH) }}
  .


  (* Removing ownership of the references from AUTH actually makes the postcondition simpler.
     This is basically the less-naive version of the point-wise equality spec. *)
  Lemma above_threshold_online_no_flag_spec_pw (num den T : Z) (εpos : 0 < IZR num / IZR den) K :
    ↯m (IZR num / IZR den) -∗
    ⤇ fill K ((Val above_threshold_no_flag) #num #den #T)
    -∗
    WP (Val above_threshold_no_flag) #num #den #T
       {{ f, ∃ f' : val,
             ⤇ fill K (Val f') ∗
             ∃ AUTH : iProp Σ,
               AUTH ∗
AT_spec AUTH f f'
               (* ( ∀ `(dDB : Distance DB) (db db' : DB) (adj : dDB db db' <= 1) q K,
                      wp_sensitive (Val q) 1 dDB dZ -∗
                      AUTH -∗
                      ⤇ fill K (f' (Val (inject db')) q) -∗
                      ∀ R : bool,
                        WP (Val f) (Val (inject db)) (Val q)
                          {{ v, ∃ v', ⤇ fill K (Val v') ∗
                                      ⌜ v = #R → v' = #R ⌝ ∗
                                      ∃ (b b' : bool), ⌜v = #b⌝ ∗ ⌜v' = #b'⌝ ∗
                                      (⌜R = false⌝ -∗ AUTH)
                          }}
                  ) *)
       }}.
  Proof with (tp_pures ; wp_pures).
    iIntros "ε rhs". rewrite /above_threshold_no_flag...
    tp_bind (Laplace _ _ _). wp_bind (Laplace _ _ _).
    set (ε := (IZR num / IZR den)). replace ε with (ε / 2 + ε / 2) by real_solver.
    fold ε in εpos.
    iDestruct (ecm_split with "ε") as "[ε ε']". 1,2: real_solver.
    iApply (hoare_couple_laplace _ _ 1%Z 1%Z with "[$rhs ε']") => //.
    1: apply Zabs_ind ; lia.
    1: rewrite mult_IZR ; apply Rdiv_pos_pos. 1,2: real_solver.
    { iApply ecm_eq. 2: iFrame. subst ε. replace (IZR (2 * den)) with (2 * IZR den).
      2: qify_r ; zify_q ; lia.
      field. eapply Rdiv_pos_den_0 => //. }
    iIntros (T') "!> rhs" => /=...
    iModIntro. iExists _. iFrame "rhs".
    iExists (↯m (ε / 2))%I. iFrame "ε". clear K.
    iIntros (?????) "%q %K q_sens ε rhs %R"...

    tp_bind (q _) ; wp_bind (q _). rewrite /wp_sensitive.
    iSpecialize ("q_sens" $! _ _ db db'). iSpecialize ("q_sens" with "rhs").
    Unshelve. 2: lra.

    iApply (wp_strong_mono'' with "q_sens [ε]") => //.
    iIntros (?) "(%vq_l & %vq_r & -> & rhs & %adj')" => /=...
    assert (-1 <= vq_l - vq_r <= 1)%Z as [].
    {
      rewrite Rmult_1_l in adj'.
      assert (dZ vq_l vq_r <= 1) as h by (etrans ; eauto).
      revert h. rewrite /dZ/distance Rabs_Zabs.
      apply Zabs_ind ; intros ? h; split.
      all: pose proof (le_IZR _ _ h) ; lia.
    }
    tp_bind (Laplace _ _ _). wp_bind (Laplace _ _ _).
    (* case on whether the result is the one that will get released (pweq) *)
    destruct R eqn:HR.
    - iApply (hoare_couple_laplace vq_l vq_r 1%Z 2%Z with "[$rhs ε]") => //.
      1: apply Zabs_ind ; lia.
      1: rewrite mult_IZR ; apply Rdiv_pos_pos ; real_solver.
      { subst ε. iApply ecm_eq. 2: iFrame. rewrite mult_IZR. field. eapply Rdiv_pos_den_0 => //. }
      iIntros "%z_l !> rhs" => /=. tp_pures.
      case_bool_decide (_ (T' + 1)%Z _)...
      all: destruct_decide (bool_decide_reflect (T' ≤ z_l)%Z) as res_l.
      all: iFrame "rhs" ; iModIntro.
      + iSplitR => //. iExists true,true. do 2 iSplitR => //. iIntros (h_R). exfalso. inversion h_R.
      + exfalso. lia.
      + exfalso. lia.
      + iSplitR => //. iExists false, false. do 2 iSplitR => //. iIntros (h_R). exfalso. inversion h_R.
    - iMod ecm_zero as "ε0".
      iApply (hoare_couple_laplace vq_l vq_r (vq_r - vq_l)%Z 0%Z with "[$rhs ε0]") => //.
      1: apply Zabs_ind ; lia.
      1: rewrite mult_IZR ; apply Rdiv_pos_pos ; real_solver.
      1: rewrite Rmult_0_l ; iFrame.
      iIntros "%z_l !> rhs" => /=...
      case_bool_decide (_ (T' + 1)%Z _).
      all: destruct_decide (bool_decide_reflect (T' ≤ z_l)%Z) as res_l ; iModIntro ; iFrame "rhs".
      all: iSplitR ; [|by (iExists _,_ ; iFrame "ε")].
      + iIntros (Rf). inversion Rf.
      + exfalso. lia.
      + iIntros (Rf). inversion Rf.
      + done.
  Qed.

  (* Clearly, getting the result of the comparison helps. How much does it help? *)
  (* If we get R before having to pick the coupling for the noisy T', then we can just couple the first
     Laplacian so that the comparisons are synchronised and use the error for the second Laplace instead. *)
  (* Only half of the error has to be provided upfront, the other half is to be paid for a query
     that produces an above-threshold result. *)
  (* We can reformulate the postcondition ; no need to return AUTH since the error
     was only provided in the case where it would have been consumed. *)
  (* At first glance, this spec may seem silly. But for now, it is unclear if this spec is
     substantially worse than the other pointwise-equality spec. If Above Threshold is simply run in
     a loop until a good query is found, then we would presumably have to know the index of the good
     query in advance in both cases; maybe that would suffice to conjure up `R` at the time of
     initialization of AT. *)
  Lemma above_threshold_online_no_flag_spec_pw_no_AUTH' (num den T : Z)
    (εpos : 0 < IZR num / IZR den) K (R : bool) :
    ↯m (IZR num / (2 * IZR den)) -∗
    ⤇ fill K ((Val above_threshold_no_flag) #num #den #T)
    -∗
    WP (Val above_threshold_no_flag) #num #den #T
       {{ f, ∃ f' : val,
             ⤇ fill K (Val f') ∗
               ( ∀ `(dDB : Distance DB) (db db' : DB) (adj : dDB db db' <= 1) q K,
                   wp_sensitive (Val q) 1 dDB dZ -∗
                      ⤇ fill K (f' (Val (inject db')) q) -∗
                      (if R then ↯m (IZR num / (2 * IZR den)) else emp) -∗
                        WP (Val f) (Val (inject db)) (Val q)
                          {{ v, ∃ v', ⤇ fill K (Val v') ∗
                                      ⌜ v = #R → v' = #R ⌝
               }} )
       }}.
  Proof with (tp_pures ; wp_pures).
    iIntros "ε rhs". rewrite /above_threshold_no_flag...
    tp_bind (Laplace _ _ _). wp_bind (Laplace _ _ _).
    set (ε := (IZR num / 2 * IZR den)).
    fold ε in εpos.
    (* case on whether the result is the one that will get released (pweq) *)
    destruct R eqn:HR.
    {
      iApply (hoare_couple_laplace _ _ 1%Z 1%Z with "[$rhs ε]") => //.
      1: apply Zabs_ind ; lia.
      1: rewrite mult_IZR ; apply Rdiv_pos_pos ; real_solver.
      { iApply ecm_eq. 2: iFrame. subst ε. replace (IZR (2 * den)) with (2 * IZR den).
        2: qify_r ; zify_q ; lia.
        field. eapply Rdiv_pos_den_0 => //. }
      iIntros (T') "!> rhs" => /=...
      iModIntro. iExists _. iFrame "rhs". clear K.
      iIntros (?????) "%q %K q_sens rhs ε" => /=...

      tp_bind (q _) ; wp_bind (q _). rewrite /wp_sensitive.
      iSpecialize ("q_sens" $! _ _ db db'). iSpecialize ("q_sens" with "rhs").
      Unshelve. 2: lra.

      iApply (wp_strong_mono'' with "q_sens [ε]") => //.
      iIntros (?) "(%vq_l & %vq_r & -> & rhs & %adj')" => /=...
      assert (-1 <= vq_l - vq_r <= 1)%Z as [adj_lb adj_ub].
      {
        rewrite Rmult_1_l in adj'.
        assert (dZ vq_l vq_r <= 1) as h by (etrans ; eauto).
        revert h. rewrite /dZ/distance Rabs_Zabs.
        apply Zabs_ind ; intros ? h; split.
        all: pose proof (le_IZR _ _ h) ; lia.
      }
      tp_bind (Laplace _ _ _). wp_bind (Laplace _ _ _).
      iApply (hoare_couple_laplace vq_l vq_r 1%Z 2%Z with "[$rhs ε]") => //.
      1: apply Zabs_ind ; lia.
      1: rewrite mult_IZR ; apply Rdiv_pos_pos ; real_solver.
      { subst ε. iApply ecm_eq. 2: iFrame. rewrite mult_IZR. field. eapply Rdiv_pos_den_0 => //. }
      iIntros "%z_l !> rhs" => /=. tp_pures.
      case_bool_decide (_ (T' + 1)%Z _) as res_r...
      all: destruct_decide (bool_decide_reflect (T' ≤ z_l)%Z) as res_l.
      all: iFrame "rhs" ; iModIntro.
      + done.
      + exfalso. lia.
      + exfalso. lia.
      + done.
    }

    {
      iMod ecm_zero as "ε0".
      iApply (hoare_couple_laplace _ _ 0%Z 0%Z with "[$rhs ε0]") => //.
      1: apply Zabs_ind ; lia.
      1: rewrite mult_IZR ; apply Rdiv_pos_pos ; real_solver.
      { iApply ecm_eq. 2: iFrame. lra. }
      iIntros (T') "!> rhs" => /=...
      iModIntro. iExists _. iFrame "rhs". clear K.
      iIntros (?????) "%q %K q_sens rhs ε'" => /=...

      tp_bind (q _) ; wp_bind (q _). rewrite /wp_sensitive.
      iSpecialize ("q_sens" $! _ _ db db'). iSpecialize ("q_sens" with "rhs").
      Unshelve. 2: lra.

      iApply (wp_strong_mono'' with "q_sens [ε]") => //.
      iIntros (?) "(%vq_l & %vq_r & -> & rhs & %adj')" => /=...
      assert (-1 <= vq_l - vq_r <= 1)%Z as [adj_lb adj_ub].
      {
        rewrite Rmult_1_l in adj'.
        assert (dZ vq_l vq_r <= 1) as h by (etrans ; eauto).
        revert h. rewrite /dZ/distance Rabs_Zabs.
        apply Zabs_ind ; intros ? h; split.
        all: pose proof (le_IZR _ _ h) ; lia.
      }
      tp_bind (Laplace _ _ _). wp_bind (Laplace _ _ _).
      iApply (hoare_couple_laplace vq_l vq_r 0%Z 1%Z with "[$rhs ε]") => //.
      1: apply Zabs_ind ; lia.
      1: rewrite mult_IZR ; apply Rdiv_pos_pos ; real_solver.
      1: rewrite Rmult_1_l mult_IZR.
      (* Actually, only half the error we have is needed. *)
      { subst ε. iApply ecm_weaken. 2: iFrame. split.
        - apply Rdiv_nneg_nneg ; lra.
        - rewrite (Rmult_comm 4). rewrite (Rmult_comm 2).
          rewrite Rdiv_mult_distr. rewrite Rdiv_mult_distr.
          rewrite /Rdiv. apply Rmult_le_compat_l.
          1: lra. lra.
      }
      iIntros "%z_l !> rhs" => /=...
      case_bool_decide (_ (T' + 0)%Z _) as res_r.
      all: rewrite !Zplus_0_r in res_r.
      all: destruct_decide (bool_decide_reflect (T' ≤ z_l)%Z) as res_l ; iModIntro ; iFrame "rhs".
      + done.
      + exfalso. clear -res_l res_r. done.
      + exfalso. clear -res_l res_r. done.
      + done.
    }
  Qed.



  (* SVT calibrates the noise by simply dividing up the initial budget ε =
  num/den over the number of queries c exceeding the threshold T and running
  each "above_threshold" query with privacy budget ε/c. *)
  (* SVT : ℚ → ℤ → ℕ → DB → (DB → Z) → option 𝔹 *)
  Definition SVT_online (num den : Z) : val :=
    λ:"T" "c",
      let: "found_above_T" := ref #true in
      let: "T'" := ref "T" in
      let: "count" := ref #0 in
      let: "f" :=
        λ:"db" "qi",
          if: "c" < !"count" then NONEV else
            SOME
              ((if: ! "found_above_T" then
                  (* need to reset T' from T with fresh noise *)
                  "T'" <- Laplace #num ("c" * #(2*den)) "T" else #()) ;;
               let: "vi" := Laplace #num #(4*den) ("qi" "db") in
               if: "T'" ≤ "vi" then
                 "found_above_T" <- #true ;;
                 "count" <- !"count"+#1 ;;
                 #true
               else
                 #false)
      in "f".

  (* SVT expressed in terms of Above Threshold, for modular analysis. *)
  (* NB: This is different from bounded oracles ("q_calls" in Approxis) because
     we only count calls to above_threshold that return a #true result. *)
  Definition SVT_AT_online (num den : Z) : val :=
    λ:"T" "c",
      let: "count" := ref #0 in
      let: "AT" := ref (above_threshold #num ("c" * #den) "T" "db") in
      λ:"db" "qi",
        if: "c" < !"count" then NONE else
          match: !"AT" "db" "qi" with
          | SOME "v" =>
              (if: "v" then
                 ("AT" <- (above_threshold #num ("c" * #den) "T" "db") ;;
                  "count" <- !"count" + #1)
               else #()) ;;
              SOME "v"
          | NONE => NONE (* should never happen because we always reset AT diligently *)
          end.


  (* SVT without counting, expressed in terms of Above Threshold without Flag, for modular analysis. *)
  Definition SVT_AT_NF_NC_online : val :=
    λ:"num" "den" "T" "N",
      let: "AT" := ref (above_threshold_no_flag "num" "den" "T") in
      λ:"db" "qi",
        let: "bq" := !"AT" "db" "qi" in
        (if: "bq" then
           "AT" <- (above_threshold_no_flag "num" "den" "T")
         else #()) ;;
        "bq"
  .

  (* In Justin's thesis, the discussion of choice couplings (p.70) and especially of randomized
  privacy cost (p.71) is relevant ; it suggests that the point-wise equality proof may not be
  required for SVT. How exactly do choice couplings help? *)



  Lemma SVT_online_diffpriv (num den T : Z) (N : nat) (Npos : (0 < N)%nat) K :
    let ε := IZR num / IZR den in
    ∀ (εpos : 0 < ε),
      ↯m (N * ε) -∗
      ⤇ fill K (SVT_AT_NF_NC_online #num #den #T #N) -∗
      WP SVT_AT_NF_NC_online #num #den #T #N
        {{ f, ∃ (f' : val) (iSVT : nat → iProp Σ),
              ⤇ fill K f' ∗
              iSVT N ∗
              (∀ `(dDB : Distance DB) (db db' : DB) (adj : dDB db db' <= 1) (q : val) K,
                  wp_sensitive (Val q) 1 dDB dZ -∗
                  ⤇ fill K (Val f' (inject db') q) -∗
                  ∀ n, iSVT (S n) -∗
                       ∀ (RES : bool),
                         WP Val f (inject db) q {{v, ∃ v' : val, ⌜v = #RES → v' = #RES⌝ ∗ iSVT (if RES then n else S n) }}
        )}}.
  Proof with (tp_pures ; wp_pures).
    (* make sure we have at least enough credit to initialise AT once *)
    destruct N as [|N'] ; [lia|] ; clear Npos.
    iIntros (??) "SNε rhs". rewrite /SVT_AT_NF_NC_online...
    tp_bind (above_threshold_no_flag _ _ _) ; wp_bind (above_threshold_no_flag _ _ _).
    assert (INR (N'+1)%nat ≠ 0). { replace 0 with (INR 0) => //. intros ?%INR_eq. lia. }
    replace (S N' * ε) with (ε + N' * ε).
    2:{ replace (S N') with (N'+1)%nat by lia. replace (INR (N'+1)) with (N' + 1) by real_solver. lra. }
    iDestruct (ecm_split with "SNε") as "[ε Nε]". 1,2: real_solver.
    opose proof (above_threshold_online_no_flag_spec_pw num den T _) as AT_pw.
    1: done.
    iPoseProof (AT_pw with "[ε] [rhs]") as "AT_pw" => // ; clear AT_pw.
    iApply (wp_strong_mono'' with "AT_pw").
    replace (S N') with (N'+1)%nat by lia.
    iIntros "%f (%f' & rhs & %AUTH & auth & AT) /=".
    tp_alloc as ref_f' "ref_f'". wp_alloc ref_f as "ref_f"...
    iModIntro. iExists _. iFrame "rhs".
    set (iSVT := (λ n : nat,
                       if Nat.ltb 0%nat n then
                         ↯m ((n-1)%nat * ε) ∗ ∃ token f f',
                           token ∗ ref_f ↦ f ∗ ref_f' ↦ₛ f' ∗ AT_spec token f f'
                       else emp
                 )%I). iExists iSVT.
    iSplitL.
    { rewrite /iSVT /=. destruct (0 <? N'+1)%nat => //. replace (N'+1-1)%nat with N' by lia. iFrame. }
    clear f f'.
    iIntros (???????) "q_sens rhs %n (nε & (%TOKEN & %f & %f' & auth & ref_f & ref_f' & AT)) %RES"...
    replace (S n - 1)%nat with n by lia.
    tp_load ; wp_load. tp_bind (f' _ _) ; wp_bind (f _ _).
    iSpecialize ("AT" $! _ _ _ _ adj _ _).
    iSpecialize ("AT" with "q_sens auth rhs").
    iSpecialize ("AT" $! RES).
    iApply (wp_strong_mono'' with "AT").
    iIntros "%vq (%vq' & rhs & %pweq & %bq & %bq' & -> & -> & maybe_auth)".
    iSimpl in "rhs"...
    iAssert (AT_spec TOKEN f f') as "AT". 1: admit. (* should have been persistent *)
    destruct bq eqn:case_bq, RES eqn:case_RES.
    - rewrite pweq //...
      (* We should only end up in this case if 0<n holds!
         SVT shouldn't re-allocate another AT on the last (Nth) invocation since it won't get used.
         Maybe it needs a counter?
       *)
      destruct (0 <? n)%nat eqn:n_pos => //.
      2: admit.
      iFrame.
      tp_bind (above_threshold_no_flag _ _ _) ; wp_bind (above_threshold_no_flag _ _ _).
      opose proof (above_threshold_online_no_flag_spec_pw num den T _) as AT_pw.
      1: done.
      iMod ecm_zero as "ε0".
      iPoseProof (AT_pw with "[ε0] [rhs]") as "AT_pw" => // ; clear AT_pw.
      1: admit.
      iApply (wp_strong_mono'' with "AT_pw [-]").
      iIntros "%g (%g' & rhs & %AUTH' & auth & AT') /=".
      tp_store ; wp_store.
      iFrame. iExists #true. iSplitR. 1: done.
      rewrite /iSVT.
      admit.
    - simpl...
      iSpecialize ("maybe_auth" $! eq_refl).
      (* still should only be doing this if 0<n. *)
      destruct bq' eqn:case_bq'.
      + simpl...
        admit.
      + simpl...
        admit.
    - simpl... iExists _. iSplitR. 1: done.
      subst.
      admit.
    - rewrite pweq //... iExists _. iSplitR. 1: done.
      rewrite /iSVT. destruct (0 <? S n)%nat => //. iFrame.
      replace (S n -1)%nat with n by lia. iFrame.
      iExists TOKEN.
      iSpecialize ("maybe_auth" $! eq_refl).
      iFrame. done.
  Admitted.

  (* Iterate online SVT over a list of queries. *)
  Definition SVT : val :=
    λ:"num" "den" "T" "N" "db" "qs",
      let: "f" := SVT_AT_NF_NC_online "num" "den" "T" "N" in
      (rec: "SVT" "i" "bs" :=
         if: "i" = "N" then "bs" else
           match: list_nth "i" "qs" with
           | NONE => "bs"
           | SOME "q" =>
               let: "b" := "f" "db" "q" in
               "SVT" ("i" + #1) (list_cons "b" "bs")
           end) #0 list_nil.

  (* pointwise diff priv *)
  Lemma SVT_diffpriv (num den T : Z) (N : nat)
    `(dDB : Distance DB) (db db' : DB) (adj : dDB db db' <= 1)
    (qs : list val) (QS : val) (is_qs : is_list qs QS)
    K
    :
    let ε := IZR num / IZR den in
    ∀ (εpos : 0 < ε),
      ([∗ list] q ∈ qs, wp_sensitive (Val q) 1 dDB dZ) -∗
      ↯m ε -∗
      ∀ RES,
        ⤇ fill K (SVT #num #den #T #(S N)) (inject db') QS -∗
        WP SVT #num #den #T #(S N) (inject db) QS
          {{ v, ∃ v' : val, ⤇ fill K v' ∗ ⌜v = RES → v' = RES⌝ }}.
  Proof with (tp_pures ; wp_pures).

  Abort.

End svt.

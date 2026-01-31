From iris.base_logic Require Export na_invariants.
From clutch.common Require Import inject.
From clutch.prelude Require Import tactics.
From clutch.prob Require Import differential_privacy.
From clutch.diffpriv Require Import adequacy diffpriv proofmode.
From clutch.diffpriv.examples Require Import list sparse_vector_technique.


Section svt_pw.
  Context `{!diffprivGS Σ}.

  #[local] Open Scope R.

  (* The spec that AT satisfies after initialising T'. *)
  Definition AT_spec_pw (AUTH : iProp Σ) (f f' : val) : iProp Σ :=
    □ ∀ (DB : Type) (dDB : Distance DB) (db db' : DB)
      (_ : dDB db db' <= 1) (q : val) (K0 : list ectx_item),
      wp_sensitive q 1 dDB dZ -∗
      AUTH -∗
      ⤇ fill K0 (f' (inject db') q) -∗
      ∀ R : bool,
        WP f (inject db) q
          {{ v,
               ∃ v' : val, ⤇ fill K0 v' ∗ ⌜v = #R → v' = #R⌝ ∗
                           ∃ (b b' : bool), ⌜v = #b⌝ ∗ ⌜v' = #b'⌝ ∗
                           (⌜R = false⌝ -∗ AUTH) }}.

  (* For the version of AT with the flag, we can prove the following point-wise spec where the
  postcondition does some additional book-keeping to connect the result R to the return values when
  we decide on whether AUTH should be returned. *)
  Lemma above_threshold_online_spec_pw (num den T : Z) (εpos : 0 < IZR num / IZR den) `(dDB : Distance DB) (db db' : DB) (adj : dDB db db' <= 1) K :
    ↯m (IZR num / IZR den) -∗
    ⤇ fill K ((Val above_threshold_reset) #num #den #T (Val (inject db')))
    -∗
    WP (Val above_threshold_reset) #num #den #T (Val (inject db))
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
    iIntros "ε rhs". rewrite /above_threshold_reset...
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

  (* Removing ownership of the references from AUTH actually makes the postcondition simpler.
     This is basically the less-naive version of the point-wise equality spec. *)
  Lemma above_threshold_online_no_flag_spec_pw (num den T : Z) (εpos : 0 < IZR num / IZR den) K :
    ↯m (IZR num / IZR den) -∗
    ⤇ fill K ((Val above_threshold) #num #den #T)
    -∗
    WP (Val above_threshold) #num #den #T
       {{ f, ∃ f' : val,
             ⤇ fill K (Val f') ∗
             ∃ AUTH : iProp Σ,
               AUTH ∗
               AT_spec_pw AUTH f f'
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
      field. eapply Rdiv_pos_den_0 => //. }
    iIntros (T') "!> rhs" => /=...
    iModIntro. iExists _. iFrame "rhs".
    iExists (↯m (ε / 2))%I. iFrame "ε". clear K.
    iModIntro.
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
    ⤇ fill K ((Val above_threshold) #num #den #T)
    -∗
    WP (Val above_threshold) #num #den #T
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
    iIntros "ε rhs". rewrite /above_threshold...
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

  (* TODO move *)
  Lemma AT_NF_safe num den T :
    ⊢ WP (above_threshold #num #den #T) {{ v, ⌜True⌝ }}.
  Proof.
    rewrite /above_threshold.
  Admitted.

  (* TODO move *)
  (* Pointwise equality spec for oSVT based on pweq oAT. *)
  (* Crucially, the whole post-condition is guarded by ⌜v = #RES⌝. This is analogous to the
     point-wise equality postcondition: only if the "guess" of RES was correct do we guarantee
     anything about the RHS return value (v' = #RES) and the predicate iSVT. *)
  Lemma SVT_online_diffpriv (num den T : Z) (N : nat) (Npos : (0 < N)%nat) K :
    let ε := IZR num / IZR den in
    ∀ (εpos : 0 < ε),
      ↯m (N * ε) -∗
      ⤇ fill K (oSVT #num #den #T #N) -∗
      WP oSVT #num #den #T #N
        {{ f, ∃ (f' : val) (iSVT : nat → iProp Σ),
              ⤇ fill K f' ∗
              iSVT N ∗
              (∀ `(dDB : Distance DB) (db db' : DB) (adj : dDB db db' <= 1) (q : val) K,
                  wp_sensitive (Val q) 1 dDB dZ -∗
                  ⤇ fill K (Val f' (inject db') q) -∗
                  ∀ n, iSVT (S n) -∗
                       ∀ (RES : bool),
                         WP Val f (inject db) q {{v, ∃ v' : val,
                                 ⌜v = #RES⌝ -∗
                                 (⤇ fill K (Val v') ∗ ⌜v' = #RES⌝ ∗ iSVT (if RES then n else S n)) }}
        )}}.
  Proof with (tp_pures ; wp_pures).
    (* make sure we have at least enough credit to initialise AT once *)
    destruct N as [|N'] ; [lia|] ; clear Npos.
    iIntros (??) "SNε rhs". rewrite /oSVT...
    tp_alloc as count_r "count_r". wp_alloc count_l as "count_l"...
    tp_bind (above_threshold _ _ _) ; wp_bind (above_threshold _ _ _).
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
                         let n' := (n-1)%nat in
                         count_l ↦ #n' ∗ count_r ↦ₛ #n' ∗
                         ↯m (n' * ε) ∗ ∃ token f f',
                           token ∗ ref_f ↦ f ∗ ref_f' ↦ₛ f' ∗ AT_spec_pw token f f'
                       else emp
                 )%I). iExists iSVT.
    iSplitL.
    { rewrite /iSVT /=. destruct (0 <? N'+1)%nat => //.
      replace ((N'+1)%nat-1)%Z with (Z.of_nat N') by lia.
      replace (N'+1-1)%nat with N' by lia. iFrame. }
    clear f f'.
    iIntros (???????) "q_sens rhs %n (count_l & count_r & nε & (%TOKEN & %f & %f' & auth & ref_f & ref_f' & #AT)) %RES"...
    iCombine "AT" as "AT_cpy".
    (* replace (S n - 1)%nat with n by lia. *)
    tp_load ; wp_load. tp_bind (f' _ _) ; wp_bind (f _ _).
    iSpecialize ("AT" $! _ _ _ _ adj _ _).
    iSpecialize ("AT" with "q_sens auth rhs").
    iSpecialize ("AT" $! RES).
    iApply (wp_strong_mono'' with "AT").
    iIntros "%vq (%vq' & rhs & %pweq & %bq & %bq' & -> & -> & maybe_auth)".
    iSimpl in "rhs"...
    destruct bq eqn:case_bq, RES eqn:case_RES.
    - rewrite pweq //...
      tp_load ; wp_load...
      rewrite /= !Nat.sub_0_r.
      destruct n as [|n']...
      { rewrite /iSVT. simpl. iExists #true. iModIntro. iIntros. iFrame. done. }
      replace (S n' * ε) with (ε + n' * ε).
      2:{ replace (S n') with (n'+1)%nat by lia. replace (INR (n'+1)) with (n' + 1) by real_solver. lra. }
      iDestruct (ecm_split with "nε") as "[ε n'ε]". 1,2: real_solver.
      tp_bind (above_threshold _ _ _) ; wp_bind (above_threshold _ _ _).
      opose proof (above_threshold_online_no_flag_spec_pw num den T _) as AT_pw.
      1: done.
      iPoseProof (AT_pw with "[ε] [rhs]") as "AT_pw" => // ; clear AT_pw.
      iApply (wp_strong_mono'' with "AT_pw [-]").
      iIntros "%g (%g' & rhs & %AUTH' & auth & AT') /=".
      tp_store ; wp_store... tp_load... tp_store ; wp_load... wp_store.
      iFrame. iModIntro. iIntros. iSplitR. 1: done.
      rewrite /iSVT.
      replace (Z.of_nat (S n' - 1)%nat) with (S n' - 1)%Z by lia. iFrame.
      replace (S n' - 1)%nat with n' by lia. iFrame.
    - simpl... rewrite /= !Nat.sub_0_r.
      iSpecialize ("maybe_auth" $! eq_refl).
      tp_load ; wp_load...
      destruct n as [|n']...
      { rewrite /iSVT. iFrame. iModIntro. iIntros (h). inversion h. }
      wp_bind (above_threshold _ _ _).

  (*     iApply (wp_strong_mono'' with "AT_NF_safe"). iIntros...
         wp_store ; wp_load ; wp_store. iExists _. iIntros "!>**". exfalso. done.
       - simpl... rewrite /= !Nat.sub_0_r. tp_load ; wp_load...
         destruct n as [|n']...
         { rewrite /iSVT. iFrame. iModIntro. iIntros (h). inversion h. }
         iExists _. iIntros "!>**". exfalso. done.
       - rewrite pweq //... tp_load ; wp_load...
         case_bool_decide...
         +
           iExists _. iIntros "!>**". iFrame. iSplitR. 1: done.
           iExists TOKEN.
           iSpecialize ("maybe_auth" $! eq_refl).
           iFrame. done.
         +
           iExists _. iIntros "!>**". iFrame. iSplitR. 1: done.
           iExists TOKEN.
           iSpecialize ("maybe_auth" $! eq_refl).
           iFrame. done.
           Unshelve. all: easy.
     Qed. *)
  Abort.


  Lemma SVT_online_diffpriv (num den T : Z) (N : nat) (Npos : (0 < N)%nat) K :
    let ε := IZR num / IZR den in
    ∀ (εpos : 0 < ε),
      ↯m (N * ε) -∗
      ⤇ fill K (oSVT #num #den #T #N) -∗
      WP oSVT #num #den #T #N
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
  (*   (* make sure we have at least enough credit to initialise AT once *)
       destruct N as [|N'] ; [lia|] ; clear Npos.
       iIntros (??) "SNε rhs". rewrite /oSVT...
       assert (INR (N'+1)%nat ≠ 0). { replace 0 with (INR 0) => //. intros ?%INR_eq. lia. }
       replace (S N' * ε) with (ε + N' * ε).
       2:{ replace (S N') with (N'+1)%nat by lia. replace (INR (N'+1)) with (N' + 1) by real_solver. lra. }
       tp_alloc as count_r "count_r" ; wp_alloc count_l as "count_l" => //=...
       tp_bind (above_threshold _ _ _) ; wp_bind (above_threshold _ _ _).
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
                              token ∗ ref_f ↦ f ∗ ref_f' ↦ₛ f' ∗ AT_spec_pw token f f'
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
       iAssert (AT_spec_pw TOKEN f f') as "AT". 1: admit. (* should have been persistent *)
       destruct bq eqn:case_bq, RES eqn:case_RES.
       - rewrite pweq //...
         (* We should only end up in this case if 0<n holds!
            SVT shouldn't re-allocate another AT on the last (Nth) invocation since it won't get used.
            Maybe it needs a counter?
          *)
         destruct (0 <? n)%nat eqn:n_pos => //.
         2: admit.
         iFrame...
         tp_load.
         tp_bind (above_threshold _ _ _) ; wp_bind (above_threshold _ _ _).
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
     Admitted. *)
  Abort.

End svt_pw.

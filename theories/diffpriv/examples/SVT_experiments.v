From iris.base_logic Require Export na_invariants.
From clutch.common Require Import inject.
From clutch.prelude Require Import tactics.
From clutch.prob Require Import differential_privacy.
From clutch.diffpriv Require Import adequacy diffpriv proofmode.
From clutch.diffpriv.examples Require Import list sparse_vector_technique.


Section svt_experiments.
  Context `{!diffprivGS Σ}.

  #[local] Open Scope R.


  (* Here's the first spec with equal return values in the postcondition. I was only able to
  conclude the proof by assuming some dubious rules. *)
  Lemma above_threshold_online_spec (num den T : Z) (εpos : 0 < IZR num / IZR den) `(dDB : Distance DB) (db db' : DB) (adj : dDB db db' <= 1) K :
    ↯m (IZR num / IZR den) -∗
    ⤇ fill K ((Val above_threshold_reset) #num #den #T (Val (inject db')))
    -∗
    WP (Val above_threshold_reset) #num #den #T (Val (inject db))
       {{ f, ∃ f' : val,
             ⤇ fill K (Val f') ∗
             ∃ AUTH : iProp Σ,
               AUTH ∗
               (∀ q, wp_sensitive (Val q) 1 dDB dZ -∗
                     AUTH -∗
                     ⤇ fill K (f' q) -∗
                     WP (Val f) (Val q)
                       {{ v, ∃ v', ⤇ fill K (Val v') ∗
                                   ⌜ v = v' ⌝ ∗
                                   (⌜ v = SOMEV #false⌝ -∗ AUTH)
                       }}

               )
       }}.
  Proof with (tp_pures ; wp_pures).
    iIntros "ε rhs". rewrite /above_threshold_reset...
    tp_bind (Laplace _ _ _). wp_bind (Laplace _ _ _).
    set (ε := (IZR num / IZR den)). replace ε with (ε / 2 + ε / 2) by real_solver.
    fold ε in εpos.
    assert (IZR den ≠ 0) by admit.
    assert (0 < IZR num / IZR (2 * den)) by admit.
    assert (0 < IZR num / IZR (4 * den)) by admit.
    iDestruct (ecm_split with "ε") as "[ε ε']". 1,2: real_solver.
    iApply (hoare_couple_laplace _ _ 1%Z 1%Z with "[$rhs ε']") => //.
    1: apply Zabs_ind ; lia.
    { iApply ecm_eq. 2: iFrame. subst ε. replace (IZR (2 * den)) with (2 * IZR den).
      2: qify_r ; zify_q ; lia.
      field. done. }
    iIntros (T') "!> rhs" => /=...
    tp_alloc as reset_r "reset_r". wp_alloc reset_l as "reset_l"...
    iModIntro. iExists _. iFrame.
    set (AUTH := (↯m (ε / 2) ∗ reset_r ↦ₛ #false ∗ reset_l ↦ #false)%I).
    iExists AUTH. iFrame.
    iIntros "%q q_sens (ε & reset_r & reset_l) rhs"... tp_load. wp_load...

    tp_bind (q _). wp_bind (q _). rewrite /wp_sensitive.
    iSpecialize ("q_sens" $! _ _ db db'). iSpecialize ("q_sens" with "rhs").
    Unshelve. 2: lra.
    (* iPoseProof (wp_frame_l with "[reset_r $q_sens]") as "q_sens". 1: iAssumption.
       iPoseProof (wp_frame_l with "[reset_l $q_sens]") as "q_sens". 1: iAssumption.
       iPoseProof (wp_frame_l with "[ε $q_sens]") as "q_sens". 1: iAssumption. *)
    iApply (wp_strong_mono'' with "q_sens [-]").
    iIntros (?) "(%vq_l & %vq_r & -> & rhs & %adj')" => /=...
    assert (-1 <= vq_l - vq_r <= 1)%Z as [].
    {
      rewrite Rmult_1_l in adj'.
      assert (dZ vq_l vq_r <= 1) as h by (etrans ; eauto).
      revert h.
      rewrite /dZ/distance Rabs_Zabs.
      apply Zabs_ind ; intros ? h; split.
      all: pose proof (le_IZR _ _ h) ; lia.
    }

    (* We want to case on whether the result is the one that will get released (pweq?) *)
    (* destruct R eqn:HR. *)
    (* NB: no point in casing on T' ≤ vq_l: that doesn't mean (Lap vq_l ε') will be above T'. *)

    (* Case 1, where the result is above the threshold. We can get a (v_l v_r . v_l+1 = v_r) coupling
     between Lap vq_l and Lap vq_r for ↯(2*ε') by adjacency of vq_l and vq_r. Hence, we get v_l and
     v_r adjacent. Then, since v_l is above T', v_r = v_l+1 is above T'+1 (by adjacency of v_l and
     v_r). *)
    assert (∀ v_l v_r,
               T' ≤ v_l →
               v_l + 1 = v_r →
               T'+1 ≤ v_r)%Z
      as case1 by intuition lia.

    (* Case 2, where the result is below the threshold. We can get an isometry-coupling for free.
     Then, by adjacency of vq_l and vq_r, if the left is below, then the right is below too. *)
    assert (∀ v_l v_r,
               (¬ T' ≤ v_l) →
               v_l + (vq_r - vq_l) = v_r →
               (¬ T'+1 ≤ v_r))%Z
      as case2 by intuition lia.

    set
      (goal := ↯m (ε / 2) ∗
               reset_l ↦ #false ∗
               reset_r ↦ₛ #false ∗
               ⤇ fill K
                 (let: "vi" := Laplace #num #(4 * den) #vq_r in
                  if: #(T' + 1) ≤ "vi" then #reset_r <- #true;; InjR #true
                  else InjR #false)%E
               ⊢
                 WP let: "vi" := Laplace #num #(4 * den) #vq_l in
                    if: #T' ≤ "vi" then #reset_l <- #true;; InjR #true else InjR #false
                    {{ v, ∃ v' : val, ⤇ fill K v' ∗ ⌜v = v'⌝ ∗ (⌜v = InjRV #false⌝ -∗ AUTH) }}).
    (* sanity check: is this the current goal? *)
    cut goal.
    { intros h. iApply h. iFrame. }

    (* Here's how to prove the above-T case alone, admitting the other case. *)
    assert goal as _.
    {
      subst goal.
      iIntros "(ε & reset_l & reset_r & rhs)".
      tp_bind (Laplace _ _ _). wp_bind (Laplace _ _ _).

      (* case 1 *)
      (* A direct proof of this case with the appropriate coupling is commented out here. *)
      iApply (hoare_couple_laplace vq_l vq_r 1%Z 2%Z with "[$rhs $ε]") => //.
      1: apply Zabs_ind ; lia.
      { subst ε. replace (IZR (4 * den)) with (4 * IZR den). 2: qify_r ; zify_q ; lia. field. done. }
      iIntros "!> %v_l rhs" => /=...
      destruct_decide (@bool_decide_reflect (T' ≤ v_l)%Z _) as res_l.
      - eapply (case1) in res_l => //. rewrite (bool_decide_eq_true_2 _ res_l)...
        tp_store ; wp_store... iFrame. iModIntro ; iSplitR ; iIntros ; done.
      -
        (* the credits are gone, can't re-establish AUTH. *)
        admit.
    }

    (* Here's how to prove the below-T case alone, admitting the other case. *)
    assert goal as _.
    {
      subst goal.
      iIntros "(ε & reset_l & reset_r & rhs)".
      tp_bind (Laplace _ _ _). wp_bind (Laplace _ _ _).

      (* case 2 *)
      (* A direct proof of this case with the appropriate coupling is commented out here. *)
      iMod ecm_zero as "ε0".
      iApply (hoare_couple_laplace vq_l vq_r (vq_r - vq_l)%Z 0%Z with "[$rhs $ε0]") => //.
      1: apply Zabs_ind ; lia.
      1: lra.
      iIntros "!> %v_l rhs" => /=...
      destruct_decide (@bool_decide_reflect (T' ≤ v_l)%Z _) as res_l.
      - wp_pures.
        case_bool_decide as res_r => /=... all: try tp_store ; tp_pures ; wp_store...
        + iFrame. iSplitR. 1: done. iModIntro. iIntros (?). exfalso. done.
        + iFrame. iSplitR. 2: iModIntro ; iIntros ; exfalso ; done.
          iPureIntro.
          (* LHS was above T, but RHS was not, and we don't know enough about the relation between
             LHS and RHS to rule out this case. *)
          Fail lia.
          admit.
      - eapply case2 in res_l. 2: eauto.
        rewrite (bool_decide_eq_false_2 _ res_l)...
        iExists _. iFrame. subst ε. iSplitR. 1: done. iIntros "!> _". done.
    }

    (* This magic rule for the Laplacian allows us to consume the errors only if we need to.
       Specifically, we get to split on whether we are above a threshold.
       Φ is just there to get the points-to into the post condition and can probably be removed. *)
    set (Magic := ∀ num den loc loc' k k' ε K
                    (Hdist : (Z.abs (k + loc - loc') <= k')%Z) (Hε : ε = IZR num / IZR den) Φ,
            ↯m (IZR k' * ε) -∗
            ⤇ fill K (Laplace #num #den #loc') -∗
            Φ -∗
            ∀ T : Z,
              WP Laplace #num #den #loc
                {{ v_l, ∃ z_l : Z,
                      ⌜ v_l = #z_l ⌝ ∗
                      ∃ z_r : Z,
                        ⤇ fill K (Val #(z_r)%Z) ∗
                        Φ ∗
                        if bool_decide (T ≤ z_l)%Z then
                          ⌜ (z_r = z_l + k)%Z ⌝
                        else ⌜ (z_r = z_l + (loc' - loc))%Z ⌝ ∗ ↯m (IZR k' * ε)
        }}).

    (* The Magic rule implies the goal. *)
    assert (Magic → goal) as _.
    { intros magic. subst goal Magic.
      iIntros "(ε & reset_l & reset_r & rhs)".
      tp_bind (Laplace _ _ _). wp_bind (Laplace _ _ _).

      opose proof (magic num (4*den)%Z vq_l vq_r 1%Z 2%Z _ _ _ _ _) as magic' ; clear magic.
      1: apply Zabs_ind ; lia.
      1: reflexivity.

      iPoseProof (magic' with "[ε] [$rhs] [-]") as "magic" ; clear magic'.
      { iApply ecm_eq. 2: iFrame. subst ε. replace (IZR (4 * den)) with (4 * IZR den).
        2: qify_r ; zify_q ; lia. field. done. }
      { iAssert (reset_l ↦ #false ∗ reset_r ↦ₛ #false)%I with "[$]" as "h". iExact "h". }
      unshelve iApply (wp_mono with "magic").
      1: exact T'.
      iIntros "% (%z_l & -> & %z_r & rhs & [reset_l reset_r] & h) /="...

      destruct_decide (@bool_decide_reflect (T' ≤ z_l)%Z _) as res_l.

      - eapply case1 in res_l => //. iDestruct "h" as "->". rewrite (bool_decide_eq_true_2 _ res_l)...
        tp_store ; wp_store... iFrame. iModIntro ; iSplitR ; iIntros ; done.
      - eapply case2 in res_l. 2: eauto.
        iDestruct "h" as "[-> ε]".
        rewrite (bool_decide_eq_false_2 _ res_l)...
        iExists _. iFrame. subst ε. iSplitR. 1: done. iIntros "!> _". iApply ecm_eq. 2: iFrame.
        replace (IZR (4 * den)) with (4 * IZR den). 2: qify_r ; zify_q ; lia. field. done.
    }


    (* An attempt at a point-wise version of Laplace coupling. *)
    set (hoare_couple_laplace_pw := ∀ (loc loc' k k' : Z)
                                   (Hdist : (Z.abs (k + loc - loc') <= k')%Z)
                                   (num den : Z) (ε ε' : R) K E,
            IZR num / IZR den = ε →
            0 < IZR num / IZR den →
            ε' = (IZR k' * ε) →
            ∀ RES : Z,
              {{{ ⤇ fill K (Laplace #num #den #loc') ∗ ↯m ε' }}}
                Laplace #num #den #loc @ E
                {{{ (z_l : Z), RET #z_l; ∃ z_r : Z, ⤇ fill K #(z_r) ∗ ⌜z_l = RES → (z_r = RES+k)%Z⌝ }}}).

    (* General point-wise rule.  *)
    set (Pweq := ∀ (e e' : expr) K,
            (∀ x : bool, ⤇ fill K e' -∗ WP e {{ v, ∃ v', ⤇ fill K (of_val v') ∗ ⌜v = NONEV → v' = NONEV⌝ ∗ ⌜v = SOMEV #x -> v' = SOMEV #x⌝}})
            -∗
            (⤇ fill K e' -∗ WP e {{ v, ⤇ fill K (of_val v) }})).

    (* This is pretty rough, and relies on further admits. *)
    assert (Pweq → goal) as _.

    { intros pweq. clear Magic. subst goal Pweq.
      iIntros "(ε & reset_l & reset_r & rhs)".

      (* Prove the point-wise spec for Above Threshold instead. *)
      cut (
          ∀ RES : Z,
            ↯m (ε / 2) ∗
            reset_l ↦ #false ∗
            reset_r ↦ₛ #false ∗
            ⤇ fill K
              (let: "vi" := Laplace #num #(4 * den) #vq_r in
               if: #(T' + 1) ≤ "vi" then #reset_r <- #true;; InjR #true
               else InjR #false)%E
            ⊢
              WP let: "vi" := Laplace #num #(4 * den) #vq_l in
                if: #T' ≤ "vi" then #reset_l <- #true;; InjR #true else InjR #false
                {{ v, ∃ v' : val, ⤇ fill K v' ∗ ⌜v = SOMEV #RES → v' = SOMEV #RES⌝ ∗ (⌜v = SOMEV #false⌝ -∗ AUTH) }}).

      { intros h.
        (* actually, not even pweq is strong enough as stated *)
        Fail iApply pweq. Fail iApply h. give_up. }

      intros z_l.
      iIntros "(ε & reset_l & reset_r & rhs)".

      tp_bind (Laplace _ _ _). wp_bind (Laplace _ _ _).

      destruct_decide (@bool_decide_reflect (T' ≤ z_l)%Z _) as res_l.
      (* case 1 *)
      - assert hoare_couple_laplace_pw as lap_pw by admit.
        unshelve iApply (lap_pw vq_l vq_r 1%Z 2%Z with "[$rhs $ε]") => //.
        1: exact z_l.
        1: apply Zabs_ind ; lia.
        { subst ε. replace (IZR (4 * den)) with (4 * IZR den). 2: qify_r ; zify_q ; lia. field. done. }
        iIntros "!> %v_l (%v_r & rhs & %h_pw)" => /=...

        opose proof (case1 _ _ res_l _) as res_r => //.
        assert (v_l = z_l) as -> by admit.
        rewrite (bool_decide_eq_true_2 _ res_l).
        rewrite h_pw => //.
        rewrite (bool_decide_eq_true_2 _ res_r)...
        tp_store ; wp_store... iFrame. iModIntro ; iSplitR ; iIntros ; done.

      (* case 2 *)
      - iMod ecm_zero as "ε0".
        iApply (hoare_couple_laplace vq_l vq_r (vq_r - vq_l)%Z 0%Z with "[$rhs $ε0]") => //.
        1: apply Zabs_ind ; lia.
        1: lra.
        iIntros "!> %v_l rhs" => /=...
        assert (v_l = z_l) as -> by admit.
        destruct_decide (@bool_decide_reflect (T' ≤ z_l)%Z _) as res_l' ; [lia|].
        eapply case2 in res_l'. 2: eauto.
        rewrite (bool_decide_eq_false_2 _ res_l')...
        iFrame. done.
    }
    Fail Qed.
  Abort.

  (* Question: If we had a WP rule for pointwise equality, could we use it to strengthen the
  pointwise AT spec into the exact one? This seems rather difficult since the ⌜RES = false⌝ -∗ AUTH
  part of the postcondition also mentions the variable that the pointwise equality quantifies over. *)

  Definition WP_PWEQ : iProp Σ :=
    ∀ (e e' : expr) K,
      (∀ RES : val, ⤇ fill K e' -∗
                    WP e {{ v, ∃ v', ⤇ fill K (of_val v') ∗ ⌜v = RES -> v' = RES⌝}})
      -∗
      (⤇ fill K e' -∗ WP e {{ v, ⤇ fill K (of_val v) }}).

  Lemma pweq_frame_nodep e e' K : WP_PWEQ -∗ ∀ (AUTH : iProp Σ),
      (∀ RES : val,
          ⤇ fill K e' -∗
          WP e {{ v, ∃ v', ⤇ fill K (of_val v') ∗ ⌜v = RES -> v' = RES⌝ ∗ AUTH }}) ∗
      ⤇ fill K e' -∗
        WP e
          {{ v, ⤇ fill K (Val v) ∗
                AUTH
               }}.
  Proof.
    iIntros "wp_pweq". iIntros (?) "[h rhs]".
    rewrite /WP_PWEQ.
    iSpecialize ("wp_pweq" $! e  e' K).
    iSpecialize ("wp_pweq" with "[h]").
    { iIntros (?) "rhs". iSpecialize ("h" $! RES). iSpecialize ("h" with "rhs").
      iApply wp_mono. 2: iAssumption. iIntros "% (% & ? & ? & ?)". iFrame.
    }
    iSpecialize ("wp_pweq" with "rhs"). iApply (wp_mono with "wp_pweq").
    iIntros. iFrame.
    give_up.
  Abort.

  Definition magic_post :=
    forall e Φ Ψ Ξ R,
    (R -∗ WP e {{ v , Φ v ∗ Ξ v }}) ∗
    ((R -∗ WP e {{ v , Φ v }}) -∗ R -∗ WP e {{ v , Ψ v}}) ⊢ R -∗ WP e {{ v , Ψ v ∗ Ξ v }}.


  Lemma pweq_frame e e' K : WP_PWEQ -∗ ∀ (AUTH : val -> iProp Σ),
      (∀ RES : val,
          ⤇ fill K e' -∗
          WP e {{ v, ∃ v', ⤇ fill K (of_val v') ∗ ⌜v = RES -> v' = RES⌝ ∗ AUTH RES }}) ∗
      ⤇ fill K e' -∗
        WP e
          {{ v, ⤇ fill K (Val v) ∗
                AUTH v
               }}.
  Proof.
    iIntros "wp_pweq". iIntros (?) "h".
    rewrite /WP_PWEQ.
    iSpecialize ("wp_pweq" $! e  e' K).
  Abort.

  Lemma above_threshold_online_no_flag_spec_pw_no_AUTH (num den T : Z) (εpos : 0 < IZR num / IZR den) K :
    ↯m (IZR num / (2 * IZR den)) -∗
    ⤇ fill K ((Val above_threshold) #num #den #T)
    -∗
    WP (Val above_threshold) #num #den #T
       {{ f, ∃ f' : val,
             ⤇ fill K (Val f') ∗
               ( ∀ `(dDB : Distance DB) (db db' : DB) (adj : dDB db db' <= 1)
                   q, wp_sensitive (Val q) 1 dDB dZ -∗
                      ⤇ fill K (f' (Val (inject db')) q) -∗
                      ∀ R : bool, (if R then ↯m (IZR num / (2 * IZR den)) else emp) -∗
                        WP (Val f) (Val (inject db)) (Val q)
                          {{ v, ∃ v', ⤇ fill K (Val v') ∗
                                      ⌜ v = v' ⌝
               }} )
       }}.
  Proof with (tp_pures ; wp_pures).
    iIntros "ε rhs". rewrite /above_threshold...
    tp_bind (Laplace _ _ _). wp_bind (Laplace _ _ _).
    set (ε := (IZR num / 2 * IZR den)).
    fold ε in εpos.
    (* iDestruct (ecm_split with "ε") as "[ε ε']". 1,2: real_solver. *)
    iApply (hoare_couple_laplace _ _ 1%Z 1%Z with "[$rhs ε]") => //.
    1: apply Zabs_ind ; lia.
    1: rewrite mult_IZR ; apply Rdiv_pos_pos. 1,2: real_solver.
    { iApply ecm_eq. 2: iFrame. subst ε. replace (IZR (2 * den)) with (2 * IZR den).
      2: qify_r ; zify_q ; lia.
      field. eapply Rdiv_pos_den_0 => //. }
    iIntros (T') "!> rhs" => /=...
    iModIntro. iExists _. iFrame "rhs".
    (* iExists (↯m (ε / 2))%I. iFrame "ε". *)
    iIntros (?????) "%q q_sens rhs %R ε" => /=...

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
    (* case on whether the result is the one that will get released (pweq) *)
    destruct R eqn:HR.
    - iApply (hoare_couple_laplace vq_l vq_r 1%Z 2%Z with "[$rhs ε]") => //.
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
    - iMod ecm_zero as "ε0".
      iApply (hoare_couple_laplace vq_l vq_r (vq_r - vq_l)%Z 0%Z with "[$rhs ε0]") => //.
      1: apply Zabs_ind ; lia.
      1: rewrite mult_IZR ; apply Rdiv_pos_pos ; real_solver.
      1: rewrite Rmult_0_l ; iFrame.
      iIntros "%z_l !> rhs" => /=...
      case_bool_decide (_ (T' + 1)%Z _) as res_r.
      all: destruct_decide (bool_decide_reflect (T' ≤ z_l)%Z) as res_l ; iModIntro ; iFrame "rhs".
      + done.
      + exfalso. clear -res_l res_r adj_lb. assert (z_l < T')%Z as res_l' by lia ; clear res_l. lia.
      + exfalso. assert (z_l + (vq_r - vq_l) < T' + 1)%Z as res_r' by lia ; clear res_r.
        clear -res_l res_r' adj_lb adj_ub.
        (* still don't have enough assumptions about the results of the comparisons to rule out this case *)
        give_up.
      + done.
  Abort.
  (* Doesn't seem doable :( *)


End svt_experiments.

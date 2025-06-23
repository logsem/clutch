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

  (* Here's the first spec with equal return values in the postcondition. I was only able to
  conclude the proof by assuming some dubious rules. *)
  Lemma above_threshold_online_spec (num den T : Z) (εpos : 0 < IZR num / IZR den) `(dDB : Distance DB) (db db' : DB) (adj : dDB db db' <= 1) K :
    ↯ (IZR num / IZR den) -∗
    ⤇ fill K ((Val above_threshold) #num #den #T (Val (inject db')))
    -∗
    WP (Val above_threshold) #num #den #T (Val (inject db))
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
    iIntros "ε rhs". rewrite /above_threshold...
    tp_bind (Laplace _ _ _). wp_bind (Laplace _ _ _).
    set (ε := (IZR num / IZR den)). replace ε with (ε / 2 + ε / 2) by real_solver.
    fold ε in εpos.
    assert (IZR den ≠ 0) by admit.
    assert (0 < IZR num / IZR (2 * den)) by admit.
    assert (0 < IZR num / IZR (4 * den)) by admit.
    iDestruct (ec_split with "ε") as "[ε ε']". 1,2: real_solver.
    iApply (hoare_couple_laplace _ _ 1%Z 1%Z with "[$rhs ε']") => //.
    1: apply Zabs_ind ; lia.
    { iApply ec_eq. 2: iFrame. subst ε. replace (IZR (2 * den)) with (2 * IZR den).
      2: qify_r ; zify_q ; lia.
      field. done. }
    iIntros (T') "!> rhs" => /=...
    tp_alloc as reset_r "reset_r". wp_alloc reset_l as "reset_l"...
    iModIntro. iExists _. iFrame.
    set (AUTH := (↯ (ε / 2) ∗ reset_r ↦ₛ #false ∗ reset_l ↦ #false)%I).
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
      (goal := ↯ (ε / 2) ∗
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
      iMod ec_zero as "ε0".
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
            ↯ (IZR k' * ε) -∗
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
                        else ⌜ (z_r = z_l + (loc' - loc))%Z ⌝ ∗ ↯ (IZR k' * ε)
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
      { iApply ec_eq. 2: iFrame. subst ε. replace (IZR (4 * den)) with (4 * IZR den).
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
        iExists _. iFrame. subst ε. iSplitR. 1: done. iIntros "!> _". iApply ec_eq. 2: iFrame.
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
              {{{ ⤇ fill K (Laplace #num #den #loc') ∗ ↯ ε' }}}
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
            ↯ (ε / 2) ∗
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
      - iMod ec_zero as "ε0".
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

  (* We can prove the following point-wise spec where the postcondition does some additional
  book-keeping to connect the result R to the return values when we decide on whether AUTH should be
  returned. *)
  Lemma above_threshold_online_spec_pw (num den T : Z) (εpos : 0 < IZR num / IZR den) `(dDB : Distance DB) (db db' : DB) (adj : dDB db db' <= 1) K :
    ↯ (IZR num / IZR den) -∗
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
    iDestruct (ec_split with "ε") as "[ε ε']". 1,2: real_solver.
    iApply (hoare_couple_laplace _ _ 1%Z 1%Z with "[$rhs ε']") => //.
    1: apply Zabs_ind ; lia.
    1: rewrite mult_IZR ; apply Rdiv_pos_pos. 1,2: real_solver.
    { iApply ec_eq. 2: iFrame. subst ε. replace (IZR (2 * den)) with (2 * IZR den).
      2: qify_r ; zify_q ; lia.
      field. eapply Rdiv_pos_den_0 => //.
    }
    iIntros (T') "!> rhs" => /=...
    tp_alloc as reset_r "reset_r". wp_alloc reset_l as "reset_l"...
    iModIntro. iExists _. iFrame.
    iExists (↯ (ε / 2) ∗ reset_r ↦ₛ #false ∗ reset_l ↦ #false)%I. iFrame.
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
      { subst ε. iApply ec_eq. 2: iFrame. rewrite mult_IZR. field. eapply Rdiv_pos_den_0 => //. }
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
      iMod ec_zero as "ε0".
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


  (* We don't actually need `reset` since it is always set to `false` so long as a client holds AUTH. *)
  Definition above_threshold_no_flag : val :=
    λ:"num" "den" "T",
      let: "T'" := Laplace "num" (#2*"den") "T" in
      λ:"db" "qi",
        let: "vi" := Laplace "num" (#4*"den") ("qi" "db") in
        "T'" ≤ "vi".

  (* Removing ownership of the references from AUTH actually makes the postcondition simpler.
     This is basically the less-naive version of the point-wise equality spec. *)
  Lemma above_threshold_online_no_flag_spec_pw (num den T : Z) (εpos : 0 < IZR num / IZR den) K :
    ↯ (IZR num / IZR den) -∗
    ⤇ fill K ((Val above_threshold_no_flag) #num #den #T)
    -∗
    WP (Val above_threshold_no_flag) #num #den #T
       {{ f, ∃ f' : val,
             ⤇ fill K (Val f') ∗
             ∃ AUTH : iProp Σ,
               AUTH ∗
               ( ∀ `(dDB : Distance DB) (db db' : DB) (adj : dDB db db' <= 1) q K,
                   wp_sensitive (Val q) 1 dDB dZ -∗
                   AUTH -∗
                   ⤇ fill K (f' (Val (inject db')) q) -∗
                   ∀ R : bool,
                     WP (Val f) (Val (inject db)) (Val q)
                       {{ v, ∃ v', ⤇ fill K (Val v') ∗
                                   ⌜ v = #R → v' = #R ⌝ ∗
                                   (⌜R = false⌝ -∗ AUTH)
                       }}
               )
       }}.
  Proof with (tp_pures ; wp_pures).
    iIntros "ε rhs". rewrite /above_threshold_no_flag...
    tp_bind (Laplace _ _ _). wp_bind (Laplace _ _ _).
    set (ε := (IZR num / IZR den)). replace ε with (ε / 2 + ε / 2) by real_solver.
    fold ε in εpos.
    iDestruct (ec_split with "ε") as "[ε ε']". 1,2: real_solver.
    iApply (hoare_couple_laplace _ _ 1%Z 1%Z with "[$rhs ε']") => //.
    1: apply Zabs_ind ; lia.
    1: rewrite mult_IZR ; apply Rdiv_pos_pos. 1,2: real_solver.
    { iApply ec_eq. 2: iFrame. subst ε. replace (IZR (2 * den)) with (2 * IZR den).
      2: qify_r ; zify_q ; lia.
      field. eapply Rdiv_pos_den_0 => //. }
    iIntros (T') "!> rhs" => /=...
    iModIntro. iExists _. iFrame "rhs".
    iExists (↯ (ε / 2))%I. iFrame "ε". clear K.
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
      { subst ε. iApply ec_eq. 2: iFrame. rewrite mult_IZR. field. eapply Rdiv_pos_den_0 => //. }
      iIntros "%z_l !> rhs" => /=. tp_pures.
      case_bool_decide (_ (T' + 1)%Z _)...
      all: destruct_decide (bool_decide_reflect (T' ≤ z_l)%Z) as res_l.
      all: iFrame "rhs" ; iModIntro.
      + iSplitR => //. iIntros (h_R). exfalso. inversion h_R.
      + exfalso. lia.
      + exfalso. lia.
      + iSplitR => //. iIntros (h_R). exfalso. inversion h_R.
    - iMod ec_zero as "ε0".
      iApply (hoare_couple_laplace vq_l vq_r (vq_r - vq_l)%Z 0%Z with "[$rhs ε0]") => //.
      1: apply Zabs_ind ; lia.
      1: rewrite mult_IZR ; apply Rdiv_pos_pos ; real_solver.
      1: rewrite Rmult_0_l ; iFrame.
      iIntros "%z_l !> rhs" => /=...
      case_bool_decide (_ (T' + 1)%Z _).
      all: destruct_decide (bool_decide_reflect (T' ≤ z_l)%Z) as res_l ; iModIntro ; iFrame "rhs".
      all: iSplitR ; [|by iFrame "ε"].
      + iIntros (Rf). inversion Rf.
      + exfalso. lia.
      + iIntros (Rf). inversion Rf.
      + done.
  Qed.


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
    ↯ (IZR num / (2 * IZR den)) -∗
    ⤇ fill K ((Val above_threshold_no_flag) #num #den #T)
    -∗
    WP (Val above_threshold_no_flag) #num #den #T
       {{ f, ∃ f' : val,
             ⤇ fill K (Val f') ∗
               ( ∀ `(dDB : Distance DB) (db db' : DB) (adj : dDB db db' <= 1)
                   q, wp_sensitive (Val q) 1 dDB dZ -∗
                      ⤇ fill K (f' (Val (inject db')) q) -∗
                      ∀ R : bool, (if R then ↯ (IZR num / (2 * IZR den)) else emp) -∗
                        WP (Val f) (Val (inject db)) (Val q)
                          {{ v, ∃ v', ⤇ fill K (Val v') ∗
                                      ⌜ v = v' ⌝
               }} )
       }}.
  Proof with (tp_pures ; wp_pures).
    iIntros "ε rhs". rewrite /above_threshold_no_flag...
    tp_bind (Laplace _ _ _). wp_bind (Laplace _ _ _).
    set (ε := (IZR num / 2 * IZR den)).
    fold ε in εpos.
    (* iDestruct (ec_split with "ε") as "[ε ε']". 1,2: real_solver. *)
    iApply (hoare_couple_laplace _ _ 1%Z 1%Z with "[$rhs ε]") => //.
    1: apply Zabs_ind ; lia.
    1: rewrite mult_IZR ; apply Rdiv_pos_pos. 1,2: real_solver.
    { iApply ec_eq. 2: iFrame. subst ε. replace (IZR (2 * den)) with (2 * IZR den).
      2: qify_r ; zify_q ; lia.
      field. eapply Rdiv_pos_den_0 => //. }
    iIntros (T') "!> rhs" => /=...
    iModIntro. iExists _. iFrame "rhs".
    (* iExists (↯ (ε / 2))%I. iFrame "ε". *)
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
      { subst ε. iApply ec_eq. 2: iFrame. rewrite mult_IZR. field. eapply Rdiv_pos_den_0 => //. }
      iIntros "%z_l !> rhs" => /=. tp_pures.
      case_bool_decide (_ (T' + 1)%Z _) as res_r...
      all: destruct_decide (bool_decide_reflect (T' ≤ z_l)%Z) as res_l.
      all: iFrame "rhs" ; iModIntro.
      + done.
      + exfalso. lia.
      + exfalso. lia.
      + done.
    - iMod ec_zero as "ε0".
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


  (* Clearly, getting the result of the comparison helps. How much does it help? *)
  (* If we get R before having to pick the coupling for the noisy T', then we can just couple the first
     Laplacian so that the comparisons are synchronised and use the error for the second Laplace instead. *)
  (* Only half of the error has to be provided upfront, the other half is to be paid for a query
     that produces an above-threshold result. *)
  (* We can reformulate the postcondition to be an equality; no need to return AUTH since the error
     was only provided in the case where it would have been consumed. *)
  (* At first glance, this spec may seem silly. But for now, it is unclear if this spec is
     substantially worse than the other pointwise-equality spec. If Above Threshold is simply run in
     a loop until a good query is found, then we would presumably have to know the index of the good
     query in advance in both cases; maybe that would suffice to conjure up `b` at the time of
     initialization of AT. *)
  Lemma above_threshold_online_no_flag_spec_pw_no_AUTH' (num den T : Z)
    (εpos : 0 < IZR num / IZR den) K (R : bool) :
    ↯ (IZR num / (2 * IZR den)) -∗
    ⤇ fill K ((Val above_threshold_no_flag) #num #den #T)
    -∗
    WP (Val above_threshold_no_flag) #num #den #T
       {{ f, ∃ f' : val,
             ⤇ fill K (Val f') ∗
               ( ∀ `(dDB : Distance DB) (db db' : DB) (adj : dDB db db' <= 1) q K,
                   wp_sensitive (Val q) 1 dDB dZ -∗
                      ⤇ fill K (f' (Val (inject db')) q) -∗
                      (if R then ↯ (IZR num / (2 * IZR den)) else emp) -∗
                        WP (Val f) (Val (inject db)) (Val q)
                          {{ v, ∃ v', ⤇ fill K (Val v') ∗
                                      ⌜ v = v' ⌝
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
      { iApply ec_eq. 2: iFrame. subst ε. replace (IZR (2 * den)) with (2 * IZR den).
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
      { subst ε. iApply ec_eq. 2: iFrame. rewrite mult_IZR. field. eapply Rdiv_pos_den_0 => //. }
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
      iMod ec_zero as "ε0".
      iApply (hoare_couple_laplace _ _ 0%Z 0%Z with "[$rhs ε0]") => //.
      1: apply Zabs_ind ; lia.
      1: rewrite mult_IZR ; apply Rdiv_pos_pos ; real_solver.
      { iApply ec_eq. 2: iFrame. lra. }
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
      { subst ε. iApply ec_weaken. 2: iFrame. split.
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
      ↯ (N * ε) -∗
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
    destruct N as [|N] ; [lia|] ; clear Npos.
    iIntros (??) "SNε rhs". rewrite /SVT_AT_NF_NC_online...
    tp_bind (above_threshold_no_flag _ _ _) ; wp_bind (above_threshold_no_flag _ _ _).
    assert (INR (N+1)%nat ≠ 0). { replace 0 with (INR 0) => //. intros ?%INR_eq. lia. }
    replace (ε) with (ε / (N + 1) + N * ε / (N + 1)).
    2: { field. pose proof (INR_le 0 _ (pos_INR N)). replace 1 with (INR 1) => //. rewrite -plus_INR => //. }
    rewrite Rmult_plus_distr_l.
    iDestruct (ec_split with "SNε") as "[ε Nε]". 1,2: real_solver.
    opose proof (above_threshold_online_no_flag_spec_pw num den T _) as AT_pw.
    (* 1: rewrite mult_IZR ; apply Rdiv_pos_pos ; real_solver. *)
    1: done.
    (* 1: admit. *)
    iPoseProof (AT_pw with "[ε] [rhs]") as "AT_pw" => // ; clear AT_pw.
    { subst ε. iApply ec_eq. 2: iFrame. rewrite ?mult_IZR.
      replace (INR N + 1) with (INR (N+1)%nat) by by rewrite plus_INR.
      rewrite -?INR_IZR_INZ. replace (S N) with (N + 1)%nat by lia.
      field. split.
      - eapply Rdiv_pos_den_0 => //.
      - done.
    }
    iApply (wp_strong_mono'' with "AT_pw [Nε]").
    iIntros "%f (%f' & rhs & %AUTH & auth & AT) /=".
    tp_alloc as ref_f' "ref_f'". wp_alloc ref_f as "ref_f"...
    iModIntro. iExists _. iFrame "rhs". set (iSVT := (λ n, ↯ (n * ε / (N + 1)) ∗ AUTH)%I). iExists iSVT. iFrame.
Abort.
  (*   iIntros (???????) "q_sens rhs %n (Snε & auth) %RES"...
       tp_load ; wp_load. tp_bind (f' _ _) ; wp_bind (f _ _).
       iSpecialize ("AT" $! _ _ _ _ adj _ _).
       iSpecialize ("AT" with "q_sens auth rhs").
       iSpecialize ("AT" $! RES).
       iApply (wp_strong_mono'' with "AT [-]").
       iIntros (vq) "(%vq' & rhs & %pweq & maybe_auth)".
       iSimpl in "rhs"...
       assert (∃ bq : bool, vq = #bq) as [bq ->] by admit.
       assert (∃ bq' : bool, vq' = #bq') as [bq' ->] by admit.
       destruct bq eqn:case_bq, RES eqn:case_RES.
       - rewrite pweq => //...
         replace (S n * ε / (N + 1)) with (ε / (N + 1) + n * ε / (N + 1)).
         2: { replace (S n) with (1 + n)%nat by lia. rewrite plus_INR. replace (INR 1%nat) with 1 => //.
              field. pose proof (INR_le 0 _ (pos_INR N)). replace 1 with (INR 1) => //. rewrite -plus_INR => //. }
         iDestruct (ec_split with "Snε") as "[ε nε]". 1,2: real_solver.
         tp_bind (above_threshold_no_flag _ _ _) ; wp_bind (above_threshold_no_flag _ _ _).
         opose proof (above_threshold_online_no_flag_spec_pw num (S N * den)%Z T _) as AT_pw.
         1: rewrite mult_IZR ; apply Rdiv_pos_pos ; real_solver.
         iPoseProof (AT_pw with "[ε] [rhs]") as "AT_pw" => // ; clear AT_pw.
         { subst ε. iApply ec_eq. 2: iFrame. rewrite mult_IZR.
           replace (INR N + 1) with (INR (N+1)%nat) by by rewrite plus_INR.
           rewrite -INR_IZR_INZ. replace (S N) with (N + 1)%nat by lia.
           field. split.
           - eapply Rdiv_pos_den_0 => //.
           - done.
         }
         iApply (wp_strong_mono'' with "AT_pw [-]").
         iIntros "%g (%g' & rhs & %AUTH' & auth & AT) /=".
         tp_store ; wp_store.
         iFrame. iExists #true.
     Admitted. *)

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
      ↯ ε -∗
      ∀ RES,
        ⤇ fill K (SVT #num #den #T #(S N)) (inject db') QS -∗
        WP SVT #num #den #T #(S N) (inject db) QS
          {{ v, ∃ v' : val, ⤇ fill K v' ∗ ⌜v = RES → v' = RES⌝ }}.
  Proof with (tp_pures ; wp_pures).

  Abort.

End svt.

From iris.base_logic Require Export na_invariants.
From clutch.common Require Import inject.
From clutch.prelude Require Import tactics.
From clutch.prob Require Import differential_privacy.
From clutch.diffpriv_simple_pw_again Require Import adequacy_simple diffpriv_simple_pw_again proofmode_simple.

Section rnm.
  Context `{!diffprivGS Σ}.

  #[local] Open Scope R.

  Definition report_noisy_max (num den : Z) : val :=
    λ:"evalQ" "N" "d",
      let: "maxI" := ref #(-1) in
      let: "maxA" := ref #0 in
      let: "f" :=
        (rec: "rnm" "i" :=
           if: "i" = "N" then
             ! "maxI"
           else
             (let: "a" := Laplace #num #(2*den) ("evalQ" "i" "d") in
              (if: "i" = #0 `or` ! "maxA" < "a" then
                 "maxA" <- "a" ;;
                 "maxI" <- "i"
               else #()) ;;
              "rnm" ("i" + #1)))
      in "f" #0.

  Definition rnm_body (num den : Z) (evalQ : val) {DB} (dDB : Distance DB) (N : nat) (db : DB) (maxI maxA : loc) :=
    (rec: "rnm" "i" :=
       if: "i" = #N then ! #maxI
       else let: "a" := Laplace #num #(2*den) (evalQ "i" (inject db)) in
            (if:  "i" = #0 `or` ! #maxA < "a"
             then #maxA <- "a";; #maxI <- "i" else #());;
            "rnm" ("i" + #1))%V.

  (* This proof is *almost* completed modulo the (impossible) case where the return value `j` is
     not a positive integer. *)
  Lemma rnm_pw_diffpriv num den (evalQ : val) DB (dDB : Distance DB) (N : nat) K :
    (0 < IZR num / IZR (2 * den)) →
    (∀ i : Z, ⊢ hoare_sensitive (evalQ #i) 1 dDB dZ) →
    ∀ db db', dDB db db' <= 1 →
              ∀ j : val,
                {{{ ↯m (IZR num / IZR den) ∗
                    ⤇ fill K (report_noisy_max num den evalQ #N (inject db')) }}}
                  report_noisy_max num den evalQ #N (inject db)
                  {{{ v, RET v ; ∃ (v' : val), ⤇ fill K v' ∗ ⌜ v = j → v' = j ⌝  }}}
  .
  Proof with (tp_pures ; wp_pures).
    (* destruct j to make sure it's an integer *)
    intros εpos qi_sens.
    iIntros (db db' db_adj j Φ) "(ε & rnm) HΦ".
    rewrite /report_noisy_max.
    simpl. tp_pures. wp_pures.
    (* initialize *)
    tp_alloc as maxI2 "maxI2". tp_pures. tp_alloc as maxA2 "maxA2". do 5 tp_pure.
    wp_pures. wp_alloc maxI1 as "maxI1". wp_alloc maxA1 as "maxA1". do 5 wp_pure.
    destruct (decide ((∃ zj : nat, j = #zj))) as [[zj ->]|].
    2: shelve.
    rename zj into j.
    rewrite -/(rnm_body num den evalQ dDB N db maxI1 maxA1).
    rewrite -/(rnm_body num den evalQ dDB N db' maxI2 maxA2).
    (* generalize loop variable, set up invariants *)
    cut
      (∀ (i imax1 imax2 : Z) (amax1 amax2 : Z),
          {{{ maxI1 ↦ #imax1 ∗ maxI2 ↦ₛ #imax2 ∗ maxA1 ↦ #amax1 ∗ maxA2 ↦ₛ #amax2
              ∗ ↯m (if (bool_decide (i <= j))%Z then (IZR num / IZR den) else 0)
              ∗ ⤇ fill K (rnm_body num den evalQ dDB N db' maxI2 maxA2 #i)
              ∗ ⌜ 0 <= i <= N ⌝%Z
              ∗ ⌜ i < j
                  → ((dZ amax1 amax2 <= 1)%R
                     ∧ imax1 < i ∧ imax2 < i
                     ∧ ((¬ (i <= N ∧ i < j)) → i = j)
                ) ⌝%Z
              ∗ ⌜ i = j
                  → ( (dZ amax1 amax2 <= 1)%R
                      ∧ (imax1 = j → (imax2 = j ∧ amax1 + 1 = amax2))
                      ∧ (¬ (i <= N ∧ i = j) → i = j+1) )%Z ⌝
              ∗ ⌜ (j < i)%Z
                  → ( imax1 = j → (imax2 = j ∧ amax1 + 1 = amax2) )%Z ⌝
          }}}
            rnm_body num den evalQ dDB N db maxI1 maxA1 #i
            {{{ (v : Z), RET #v;
                ∃ (v' : Z), ⤇ fill K #v' ∗ ⌜ v = j -> v' = j ⌝
            }}}
      ).
    (* the general statement implies the original goal *)
    1: { intros h.
         iMod ecm_zero as "ε0".
         iApply (h with "[-HΦ]").
         - (* We have all the reference resources for the IH. *)
           iFrame.
           iSplitL.
           (* We have the error credits too *)
           + case_bool_decide ; iFrame.
           (* and the arithmetic works out fine *)
           + iPureIntro. split ; [|split ; [|split]]. 1: lia.
             * clear. intros. repeat split.
               -- rewrite distance_0 //. lra.
               -- intros []. lia.
             * clear. intros. repeat split. all: try lia.
               -- rewrite distance_0 // ; lra.
             * clear. intros. lia.
         - (* The post-condition of the IH implies the original post. *)
           iNext ; iIntros (v) "(%v' & v' & %h')".
           iApply "HΦ". iExists _. iFrame.
           iPureIntro. intro h''. do 3 f_equal. apply h'. inversion h''. done.
    }
    clear Φ.

    (* the actual induction begins *)
    iLöb as "IH".
    iIntros (i imax1 imax2 amax1 amax2 Φ) "(maxI1 & maxI2 & maxA1 & maxA2 & ε & rnm' & %iN & %below_j & %at_j & %above_j) HΦ".
    rewrite {4}/rnm_body. wp_pures.
    rewrite {3}/rnm_body. tp_pures.
    case_bool_decide (#i = #N) as iN'.

    (* base case *)
    - tp_pures. wp_pures. tp_load ; wp_load. iApply "HΦ". iExists imax2. iFrame "rnm'". iPureIntro.
      intros ij1. inversion iN'.
      subst. clear -below_j at_j above_j.
      lia.

    (* rnm body *)
    - assert (i ≠ N). { intro h. apply iN'. subst. done. }
      assert (i < N)%Z by lia.
      tp_pures ; wp_pures.
      rewrite -/(rnm_body _ _ _ _ _ _ _ maxA1).
      rewrite -/(rnm_body _ _ _ _ _ _ _ maxA2).

      (* sensitivity of evalQ *)
      tp_bind (evalQ _ _). wp_bind (evalQ _ _).
      rewrite /hoare_sensitive in qi_sens.
      iApply (qi_sens i $! _ _ db db' _ with "rnm'").
      Unshelve. 2: shelve. 2: lra.
      iIntros "!> % (%e1 & %e2 & -> & rnm' & %e1e2_adj)" => /=.
      assert (-1 <= e1 - e2 <= 1)%Z as [].
      {
        rewrite Rmult_1_l in e1e2_adj.
        assert (dZ e1 e2 <= 1) as h by (etrans ; eauto).
        revert h.
        rewrite /dZ/distance Rabs_Zabs.
        apply Zabs_ind ; intros ? h; split.
        all: pose proof (le_IZR _ _ h) ; lia.
      }

      (* case on the whether i is below, at, or above the result j. *)
      destruct (Z.lt_trichotomy i j) as [ij | [e|ij]].
      2:{                       (* i = j *)
        tp_bind (Laplace _ _ _).
        wp_bind (Laplace _ _ _).
        iApply (hoare_couple_laplace e1 e2 1%Z 2%Z with "[$rnm' ε]") => //.
        1: apply Zabs_ind ; lia.
        { case_bool_decide. 2: lia.
          iApply ecm_eq. 2: iFrame.
          rewrite /Rdiv. rewrite mult_IZR. field. clear -εpos.
          intro d0.
          rewrite mult_IZR in εpos.
          rewrite Rdiv_mult_distr in εpos.
          rewrite d0 in εpos.
          rewrite Rdiv_0_r in εpos.
          lra.
        }
        iNext ; iIntros (a) "rnm'" => /=.
        wp_pures. tp_pures.
        tp_load ; wp_load ; tp_pures. wp_pures.
        specialize (at_j e). destruct at_j as (amax_adj & jmax1 & inext).
        case_bool_decide (amax1 < a)%Z as case_l ; try rewrite orb_true_r ; tp_pures ; wp_pures.
        all: case_bool_decide (amax2 < a+1)%Z as case_r ; try rewrite orb_true_r ; tp_pures ; wp_pures.
        * do 2 (tp_store ; tp_pures ; wp_store ; wp_pures).
          iMod ecm_zero as "ε0".
          iApply ("IH" with "[-HΦ]") ; iFrame.
          rewrite e. case_bool_decide ; try lia. iFrame.
          iPureIntro. intuition lia.
        * exfalso. clear -case_l case_r amax_adj.
          assert (a+1 <= amax2)%Z by lia.
          revert amax_adj.
          rewrite /dZ/distance Rabs_Zabs. apply Zabs_ind ; intros.
          -- lia.
          -- pose proof (le_IZR _ _ amax_adj). lia.
        * iMod ecm_zero as "ε0".
          tp_store ; tp_pures ; tp_store ; tp_pures.
          iSpecialize ("IH" $! (i+1)%Z imax1 i amax1 (a+1)%Z).
          admit.
          (* case_bool_decide (#i = #0) => /= ; tp_pures ; wp_pures. *)
          (* iSpecialize ("IH" with "[ε0 $rnm' $maxA1 $maxA2 $maxI1 $maxI2]").
             2: iApply ("IH" with "[HΦ]") ; iFrame.
             iSplitL. 1: case_bool_decide ; try lia ; iFrame "ε0".
             iPureIntro ; intuition lia. *)

        * iMod ecm_zero as "ε0".
          admit.
          (* iApply ("IH" with "[-HΦ]") ; iFrame.
             rewrite e. case_bool_decide ; try lia. iFrame.
             iFrame. iPureIntro. intuition lia. *)
      }

      (* i < j *)
      {
        destruct (below_j ij) as (amax_adj & imax1i & imax2i & inext).
        tp_bind (Laplace _ _ _).
        wp_bind (Laplace _ _ _).
        iMod ecm_zero as "ε0".
        iApply (hoare_couple_laplace e1 e2 (e2 - e1)%Z 0%Z with "[$rnm' ε0]") => //.
        1: eapply Zabs_ind ; intuition lia.
        1: rewrite Rmult_0_l => //.
        iNext ; iIntros (a) "rnm'" => /=.
        wp_pures. tp_pures.
        tp_load ; wp_load ; tp_pures. wp_pures.
        case_bool_decide (amax1 < a)%Z as case_l.
        all: case_bool_decide (amax2 < a + (e2 - e1))%Z as case_r.
        all: try rewrite orb_true_r ; tp_pures ; wp_pures.
        - do 2 (tp_store ; tp_pures ; wp_store ; wp_pures).
          iApply ("IH" with "[-HΦ]") ; iFrame.
          iSplitL. 1: repeat case_bool_decide ; try lia ; iFrame.
          iPureIntro.
          intuition try lia.
          all: rewrite /dZ/distance Rabs_Zabs ; apply Zabs_ind ; intros ; apply IZR_le ; intuition try lia.
        - wp_store ; wp_pures ; wp_store ; wp_pures.
          admit.
          (* iApply ("IH" $! (i+1)%Z with "[-HΦ]") ; iFrame.
             iSplitL. 1: repeat case_bool_decide ; try lia ; iFrame.
             assert (a+(e2-e1) <= amax2)%Z by lia.
             rewrite /dZ/distance Rabs_Zabs.
             all: iPureIntro ; repeat split ; try by intuition lia.
             + apply IZR_le.
               revert amax_adj. rewrite /dZ/distance Rabs_Zabs.
               apply Zabs_ind ; intros ; pose proof (le_IZR _ _ amax_adj).
               all: apply Zabs_ind ; intros ; lia.
             + apply IZR_le.
               revert amax_adj. rewrite /dZ/distance Rabs_Zabs.
               apply Zabs_ind ; intros ; pose proof (le_IZR _ _ amax_adj).
               all: apply Zabs_ind ; intros ; lia. *)
        - admit.
          (* tp_store ; tp_pures ; tp_store ; tp_pures.
             iApply ("IH" $! (i+1)%Z with "[-HΦ]") ; iFrame.
             iSplitL. 1: repeat case_bool_decide ; try lia ; iFrame.
             assert (a <= amax1)%Z by lia.
             rewrite /dZ/distance Rabs_Zabs.
             all: iPureIntro ; repeat split ; try by intuition lia.
             + apply IZR_le.
               revert amax_adj.
               rewrite /dZ/distance Rabs_Zabs.
               apply Zabs_ind ; intros.
               all: pose proof (le_IZR _ _ amax_adj).
               all: apply Zabs_ind ; intros ; lia.
             + apply IZR_le.
               revert amax_adj.
               rewrite /dZ/distance Rabs_Zabs.
               apply Zabs_ind ; intros.
               all: pose proof (le_IZR _ _ amax_adj).
               all: apply Zabs_ind ; intros ; lia. *)
        -
          admit.
          (* iApply ("IH" $! (i+1)%Z with "[-HΦ]") ; iFrame.
             iSplitL. 1: repeat case_bool_decide ; try lia ; iFrame.
             all: iPureIntro ; repeat split ; try by intuition lia. *)
      }
      (* j < i *)
      {
        specialize (above_j ij).
        tp_bind (Laplace _ _ _).
        wp_bind (Laplace _ _ _).
        iMod ecm_zero as "ε0".
        iApply (hoare_couple_laplace e1 e2 (e2 - e1)%Z 0%Z with "[$rnm' ε0]") => //.
        1: eapply Zabs_ind ; intuition lia.
        1: rewrite Rmult_0_l => //.
        iNext ; iIntros (a) "rnm'" => /=.
        wp_pures. tp_pures.
        admit.
        (* tp_load ; wp_load ; tp_pures ; wp_pures.

           case_bool_decide (amax1 < a)%Z as case_l.
           all: case_bool_decide (amax2 < a + (e2 - e1))%Z as case_r.
           all: tp_pures ; wp_pures.
           - do 2 (tp_store ; tp_pures ; wp_store ; wp_pures).
             iApply ("IH" with "[-HΦ]") ; iFrame.
             iSplitL. 1: repeat case_bool_decide ; try lia ; iFrame.
             iPureIntro ; lia.
           - wp_store ; wp_pures ; wp_store ; wp_pures.
             iApply ("IH" $! (i+1)%Z with "[-HΦ]") ; iFrame.
             iSplitL. 1: repeat case_bool_decide ; try lia ; iFrame.
             iPureIntro ; lia.
           - tp_store ; tp_pures ; tp_store ; tp_pures.
             iApply ("IH" $! (i+1)%Z with "[-HΦ]") ; iFrame.
             iSplitL. 1: repeat case_bool_decide ; try lia ; iFrame.
             iPureIntro ; lia.
           - iApply ("IH" $! (i+1)%Z with "[-HΦ]") ; iFrame.
             iSplitL. 1: repeat case_bool_decide ; try lia ; iFrame.
             iPureIntro ; lia. *)
      }
      Unshelve.

      destruct N.
      {
        tp_pures. wp_pures. tp_load ; wp_load. iApply "HΦ".
        iFrame. done.
      }
      tp_pures. wp_pures.


      tp_bind (evalQ _ _). wp_bind (evalQ _ _).
      rewrite /hoare_sensitive in qi_sens.
      iApply (qi_sens _ $! _ _ db db' _ with "rnm").
      Unshelve. 2: lra.
      iIntros "!> % (%e1 & %e2 & -> & rnm' & %e1e2_adj)" => /=.
      assert (-1 <= e1 - e2 <= 1)%Z as [].
      {
        rewrite Rmult_1_l in e1e2_adj.
        assert (dZ e1 e2 <= 1) as h by (etrans ; eauto).
        revert h.
        rewrite /dZ/distance Rabs_Zabs.
        apply Zabs_ind ; intros ? h; split.
        all: pose proof (le_IZR _ _ h) ; lia.
      }

        tp_bind (Laplace _ _ _).
        wp_bind (Laplace _ _ _).

        iMod ecm_zero as "ε0".
        iApply (hoare_couple_laplace e1 e2 (e2 - e1)%Z 0%Z with "[$rnm' ε0]") => //.
        1: eapply Zabs_ind ; intuition lia.
        1: rewrite Rmult_0_l => //.
        iNext ; iIntros (a) "rnm'" => /=.
        wp_pures. tp_pures.

        tp_load ; wp_load. tp_pures. wp_pures.
        tp_store ; tp_pures. wp_store. wp_pures.
        tp_store ; tp_pure ; tp_pure ; tp_pure. wp_store. wp_pure.
        rewrite -!/(rnm_body _ _ _ _ _ _ _ _).

    cut
      (∀ (i : Z) (imax1 imax2 : nat) (amax1 amax2 : Z),
          {{{ maxI1 ↦ #imax1 ∗ maxI2 ↦ₛ #imax2 ∗ maxA1 ↦ #amax1 ∗ maxA2 ↦ₛ #amax2
              (* ∗ ↯m (if (bool_decide (i <= j))%Z then (IZR num / IZR den) else 0) *)
              ∗ ⤇ fill K (rnm_body num den evalQ dDB (S N) db' maxI2 maxA2 #i)
              ∗ ⌜ 0 <= i <= (S N) ⌝%Z
          }}}
            rnm_body num den evalQ dDB (S N) db maxI1 maxA1 #i
            {{{ (v : nat), RET #v;
                ∃ (v' : nat), ⤇ fill K #v' ∗ ⌜ #v = j -> #v' = j ⌝
            }}}
      ).
    (* the general statement implies the original goal *)
    1: { intros h.
         iMod ecm_zero as "ε0".
         iApply (h with "[-HΦ]").
         - (* We have all the reference resources for the IH. *)
           replace 0%Z with (Z.of_nat 0) by lia.
           iFrame.
           iSplitL.
           + done.
           (* and the arithmetic works out fine *)
           + iPureIntro. lia.
         - (* The post-condition of the IH implies the original post. *)
           iNext ; iIntros (v) "(%v' & v' & %h')".
           iApply "HΦ". iExists _. iFrame.
           iPureIntro. intro h''. do 3 f_equal. apply h'. inversion h''. done.
    }
    clear Φ.

    iLöb as "IH".
    iIntros (i imax1 imax2 amax1 amax2 Φ) "(maxI1 & maxI2 & maxA1 & maxA2 & rnm' & %iN) HΦ".
    rewrite {4}/rnm_body. wp_pures.
    rewrite {3}/rnm_body. tp_pures.
    case_bool_decide (#i = #(S N)) as iN'.

    (* base case *)
    + tp_pures. wp_pures. tp_load ; wp_load. iApply "HΦ". iExists imax2. iFrame "rnm'". iPureIntro.
      intros ij1. inversion iN'.
      subst.
      exfalso. apply n. naive_solver.

    (* rnm body *)
    + assert (i ≠ S N). { intro h. apply iN'. subst. done. }
      assert (i < S N)%Z by lia.
      tp_pures ; wp_pures.
      rewrite -/(rnm_body _ _ _ _ _ _ _ maxA1).
      rewrite -/(rnm_body _ _ _ _ _ _ _ maxA2).

      tp_bind (evalQ _ _). wp_bind (evalQ _ _).
      rewrite /hoare_sensitive in qi_sens.
      iApply (qi_sens _ $! _ _ db db' _ with "rnm'").
      Unshelve. 2: lra.
      clear H0 e1 e2 e1e2_adj H.
      iIntros "!> % (%e1 & %e2 & -> & rnm' & %e1e2_adj)" => /=.
      assert (-1 <= e1 - e2 <= 1)%Z as [].
      {
        rewrite Rmult_1_l in e1e2_adj.
        assert (dZ e1 e2 <= 1) as h by (etrans ; eauto).
        revert h.
        rewrite /dZ/distance Rabs_Zabs.
        apply Zabs_ind ; intros ? h; split.
        all: pose proof (le_IZR _ _ h) ; lia.
      }

        tp_bind (Laplace _ _ _).
        wp_bind (Laplace _ _ _).

      iMod ecm_zero as "ε0".
      iApply (hoare_couple_laplace e1 e2 (e2 - e1)%Z 0%Z with "[$rnm' ε0]") => //.
        1: eapply Zabs_ind ; intuition lia.
        1: rewrite Rmult_0_l => //.
        iNext ; iIntros (a') "rnm'" => /=.
        wp_pures. tp_pures.

        tp_load ; wp_load. tp_pures. wp_pures.
        destruct (bool_decide (#i = #0) || bool_decide (amax1 < a')%Z).
        all: destruct (bool_decide (#i = #0) || bool_decide (amax2 < a' + (e2 - e1))%Z).
        * wp_pures ; tp_pures. tp_store ; tp_pures ; tp_store ; tp_pure. wp_store ; wp_pures ; wp_store ; wp_pure.
          tp_pure.
          tp_pure.
          replace i with (Z.of_nat (Z.to_nat i)). 2: lia. iFrame.
          iApply ("IH" with "[-HΦ]") => //. iFrame.
          iPureIntro. lia.
        * wp_pures ; tp_pures. wp_store ; wp_pures ; wp_store ; wp_pure.
          replace i with (Z.of_nat (Z.to_nat i)). 2: lia. iFrame.
          iApply ("IH" with "[-HΦ]") => //. iFrame.
          iPureIntro. lia.
        * wp_pures ; tp_pures. tp_store ; tp_pures ; tp_store ; tp_pure.
          tp_pure. tp_pure.
          replace i with (Z.of_nat (Z.to_nat i)). 2: lia. iFrame.
          iApply ("IH" with "[-HΦ]") => //. iFrame.
          iPureIntro. lia.
        * tp_pures ; wp_pures.
          replace i with (Z.of_nat (Z.to_nat i)). 2: lia. iFrame.
          iApply ("IH" with "[-HΦ]") => //. iFrame. iPureIntro. lia.
  (* Qed. *)
  Admitted.


  Lemma rnm_diffpriv num den (evalQ : val) DB (dDB : Distance DB) (N : nat) K :
    (0 < IZR num / IZR (2 * den)) →
    (∀ i : Z, ⊢ hoare_sensitive (evalQ #i) 1 dDB dZ) →
    ∀ db db', dDB db db' <= 1 →
                ↯m (IZR num / IZR den) ∗
                    ⤇ fill K (report_noisy_max num den evalQ #N (inject db'))
                    ⊢
                      WP report_noisy_max num den evalQ #N (inject db)
                        {{ v, ∃ (v' : val), ⤇ fill K v' ∗ ⌜ v = v' ⌝  }}
  .
  Proof.
    intros ?????. iIntros "(ε & rhs)".
    iMod ec_zero as "δ". replace 0 with (nonneg 0%NNR) by auto.
    opose proof (wp_pweq _ (report_noisy_max num den evalQ #N (inject db)) _ 0%NNR (λ _, 0%NNR) _ _ _ _ _).
    1: apply ex_seriesC_0. 1: simpl ; symmetry ; apply SeriesC_0 => //.
    (* Missing an administrative redex here; this could be accounted for by applying wp_pweq directly in the proof of rnm_pw_diffpriv. *)
    { right. admit. }
    iApply (H2 with "[ε] rhs δ").
    iIntros (RES) "rhs δ".
    iApply (rnm_pw_diffpriv with "[$ε $rhs]") => //.
    iIntros "!> **". iFrame.
  Admitted.

End rnm.

Lemma rnm_diffpriv_cpl_direct num den (evalQ : val) DB (dDB : Distance DB) (N : nat) :
  (0 < IZR num / IZR (2 * den))%R →
  (0 <= IZR num / IZR den)%R →
  (∀ `{!diffprivGS Σ}, ∀ i : Z, ⊢ hoare_sensitive (evalQ #i) 1 dDB dZ) →
  ∀ db db',
    (dDB db db' <= 1)%R →
    ∀ σ,
      DPcoupl
        (lim_exec ((report_noisy_max num den evalQ #N (inject db)), σ))
        (lim_exec ((report_noisy_max num den evalQ #N (inject db')), σ))
        (λ v v', v = v')
        (IZR num / IZR den) 0
.
Proof.
  intros. eapply (wp_adequacy_refl diffprivΣ) => //.
  iIntros "% rnm' ε δ".
  iApply (rnm_diffpriv _ _ _ _ _ N [] with "[$]") => //.
Qed.


Lemma rnm_pw_diffpriv_cpl num den (evalQ : val) DB (dDB : Distance DB) (N : nat) :
  (0 < IZR num / IZR (2 * den))%R →
  (0 <= IZR num / IZR den)%R →
  (∀ `{!diffprivGS Σ}, ∀ i : Z, ⊢ hoare_sensitive (evalQ #i) 1 dDB dZ) →
  ∀ db db',
    (dDB db db' <= 1)%R →
    ∀ σ,
    ∀ j : nat,
      DPcoupl
        (lim_exec ((report_noisy_max num den evalQ #N (inject db)), σ))
        (lim_exec ((report_noisy_max num den evalQ #N (inject db')), σ))
        (λ v v', v = #j → v' = #j)
        (IZR num / IZR den) 0
.
Proof.
  intros.
  eapply (wp_adequacy_refl diffprivΣ) => //.
  iIntros (?) "rnm' ε".
  iPoseProof (rnm_pw_diffpriv num den evalQ DB dDB N [] H (H1 _ _) db db' H2 #j
    %I) as "h" => //.
  simpl.
  iSpecialize ("h" with "[$]").
  iIntros.
  iApply "h". iNext. iIntros (?) "[% [? %h]]".
  iExists v' ; iFrame.
  subst. iPureIntro. intros. subst. apply h. reflexivity.
Qed.


Lemma rnm_diffpriv_cpl num den (evalQ : val) DB (dDB : Distance DB) (N : nat) :
  (0 < IZR num / IZR (2 * den))%R →
  (0 <= IZR num / IZR den)%R →
  (∀ `{!diffprivGS Σ}, ∀ i : Z, ⊢ hoare_sensitive (evalQ #i) 1 dDB dZ) →
  ∀ db db',
    (dDB db db' <= 1)%R →
    ∀ σ,
      DPcoupl
        (lim_exec ((report_noisy_max num den evalQ #N (inject db)), σ))
        (lim_exec ((report_noisy_max num den evalQ #N (inject db')), σ))
        (λ v v', v = v')
        (IZR num / IZR den) 0
.
Proof.
  intros.
  replace 0%R with (SeriesC (λ _ : val, 0)). 2: by by apply SeriesC_0.
  apply DPcoupl_pweq => //. 1: apply ex_seriesC_0.
  simpl.
  intros x'.
  eapply (wp_adequacy_refl diffprivΣ) => //.
  iIntros (?) "rnm' ε".
  unshelve iPoseProof (rnm_pw_diffpriv num den evalQ DB dDB N [] H (H1 _ _) db db' H2 x'
    (λ v, ∃ v' : val, ⤇ v' ∗ ⌜v = x' → v' = x'⌝)%I) as "h" => //.
  simpl.
  iSpecialize ("h" with "[$]"). iIntros.
  iApply "h". iNext. iIntros (?) "[% [? %h]]".
  iExists v' ; iFrame.
  subst. iPureIntro. subst.
  apply h.
Qed.

Lemma rnm_diffpriv' num den (evalQ : val) DB (dDB : Distance DB) (N : nat) :
  (0 < IZR num / IZR (2 * den))%R →
  (0 <= IZR num / IZR den)%R →
  (∀ `{!diffprivGS Σ}, ∀ i : Z, ⊢ hoare_sensitive (evalQ #i) 1 dDB dZ) →
  ∀ σ,
    diffpriv_pure
      dDB
      (λ db, lim_exec ((report_noisy_max num den evalQ #N (inject db)), σ))
      (IZR num / IZR den)
.
Proof.
  intros. apply diffpriv_approx_pure. apply DPcoupl_diffpriv.
  intros. apply rnm_diffpriv_cpl => //.
Qed.

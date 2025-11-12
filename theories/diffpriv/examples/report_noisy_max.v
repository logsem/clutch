From iris.base_logic Require Export na_invariants.
From clutch.common Require Import inject.
From clutch.prelude Require Import tactics.
From clutch.prob Require Import differential_privacy.
From clutch.diffpriv Require Import adequacy diffpriv proofmode.

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

  #[local] Definition rnm_body (num den : Z) (evalQ : val) {DB} (dDB : Distance DB) (N : nat) (db : DB) (maxI maxA : loc) :=
    (rec: "rnm" "i" :=
       if: "i" = #N then ! #maxI
       else let: "a" := Laplace #num #(2*den) (evalQ "i" (inject db)) in
            (if:  "i" = #0 `or` ! #maxA < "a"
             then #maxA <- "a";; #maxI <- "i" else #());;
            "rnm" ("i" + #1))%V.

  Lemma rnm_pw_diffpriv num den (evalQ : val) DB (dDB : Distance DB) (N : nat) K :
    (0 < IZR num / IZR (2 * den)) →
    (∀ i : Z, ⊢ hoare_sensitive (evalQ #i) 1 dDB dZ) →
    ∀ db db', dDB db db' <= 1 →
              ∀ j : val,
                {{{ ↯m (IZR num / IZR den) ∗
                    ⤇ fill K (report_noisy_max num den evalQ #N (inject db')) }}}
                  report_noisy_max num den evalQ #N (inject db)
                  {{{ v, RET v ; ∃ (v' : val), ⤇ fill K v' ∗ ⌜ v = j → v' = j ⌝  }}}.
  Proof with (tp_pures ; wp_pures).
    intros εpos qi_sens. iIntros (db db' db_adj j Φ) "(ε & rnm) HΦ".
    rewrite /report_noisy_max /=...
    (* initialize *)
    tp_alloc as maxI2 "maxI2". tp_pures. tp_alloc as maxA2 "maxA2". do 5 tp_pure.
    wp_pures. wp_alloc maxI1 as "maxI1". wp_alloc maxA1 as "maxA1". do 5 wp_pure.
    destruct (decide ((∃ zj : Z, j = #zj))) as [[zj ->]|]. 2: shelve.
    rename zj into j. rewrite -!/(rnm_body _ _ _ _ _ _ _ _).
    (* generalize loop variable, set up invariants *)
    cut
      (∀ (i imax1 imax2 : Z) (amax1 amax2 : Z),
          {{{ maxI1 ↦ #imax1 ∗ maxI2 ↦ₛ #imax2 ∗ maxA1 ↦ #amax1 ∗ maxA2 ↦ₛ #amax2
              ∗ ↯m (if (bool_decide (i <= j))%Z then (IZR num / IZR den) else 0)
              ∗ ⤇ fill K (rnm_body num den evalQ dDB N db' maxI2 maxA2 #i)
              ∗ ⌜ 0 <= i <= N ⌝%Z
              ∗ ⌜ (i = 0) → (imax1 = -1 ∧ imax2 = -1)⌝%Z
              ∗ ⌜ i < j ∧ ¬ (i = 0) → ((dZ amax1 amax2 <= 1)%R ∧ imax1 < i ∧ imax2 < i) ⌝%Z
              ∗ ⌜ i = j ∧ ¬ (i = 0)%Z
                  → ( (dZ amax1 amax2 <= 1)%R ∧ (imax1 = j → (imax2 = j ∧ amax1 + 1 = amax2)))%Z ⌝
              ∗ ⌜ (j < i)%Z ∧ ¬ (i = 0)%Z → ( imax1 = j → (imax2 = j ∧ amax1 + 1 = amax2) )%Z ⌝ }}}
            rnm_body num den evalQ dDB N db maxI1 maxA1 #i
            {{{ (v : Z), RET #v ; ∃ (v' : Z), ⤇ fill K #v' ∗ ⌜ v = j -> v' = j ⌝ }}}
      ).
    (* the general statement implies the original goal *)
    1: { intros h. iMod ecm_zero as "ε0". iApply (h with "[-HΦ]").
         - (* We have all the reference resources for the IH. *)
           iFrame. iSplitL. 1: case_bool_decide ; iFrame.
           (* The arithmetic works out fine. *)
           iPureIntro. split ; [|split ; [|split ; [|split]]] ; clear ; intros. 1: lia.
           + auto.
           + rewrite distance_0 //. lia.
           + lia.
           + exfalso. lia.
         - (* The post-condition of the IH implies the original post. *)
           iNext ; iIntros (v) "(%v' & v' & %h')". iApply "HΦ". iExists _. iFrame.
           iPureIntro. intro h''. do 3 f_equal. apply h'. inversion h''. done.
    }
    clear Φ.

    iLöb as "IH". (* the actual induction begins *)
    iIntros (i imax1 imax2 amax1 amax2 Φ)
      "(maxI1 & maxI2 & maxA1 & maxA2 & ε & rnm' & %iN & %i0 & %below_j & %at_j & %above_j) HΦ".
    rewrite {3 4}/rnm_body... case_bool_decide (#i = #N) as iN'...

    (* base case: exiting the loop at i = N *)
    - tp_load ; wp_load. iApply "HΦ". iExists imax2. iFrame "rnm'". iPureIntro.
      intros ij1. inversion iN'. subst. clear -i0 below_j at_j above_j. lia.

    (* rnm body *)
    - assert (i ≠ N). { intro h. apply iN'. subst. done. }
      assert (i < N)%Z by lia.
      rewrite -!/(rnm_body _ _ _ _ _ _ _ _).
      (* sensitivity of evalQ *)
      tp_bind (evalQ _ _). wp_bind (evalQ _ _).
      iApply (hoare_sensitive_Z_bounded $! (qi_sens i) with "[] [] rnm'") => //.
      1: real_solver. rewrite Zmult_1_l.
      iIntros "!> % (%e1 & %e2 & -> & rnm' & %e1e2_adj & %e1e2_adj')" => /=.
      iMod ecm_zero as "ε0".
      (* case on the whether i is below, at, or above the result j. *)
      destruct (Z.lt_trichotomy i j) as [ij | [e|ij]].
      2:{                       (* i = j *)
        tp_bind (Laplace _ _ _). wp_bind (Laplace _ _ _).
        iApply (hoare_couple_laplace e1 e2 1%Z 2%Z with "[$rnm' ε]") => //.
        1: apply Zabs_ind ; lia.
        { case_bool_decide. 2: lia. iApply ecm_eq. 2: iFrame.
          rewrite mult_IZR. field. clear -εpos.
          intro d0. rewrite mult_IZR in εpos. rewrite Rdiv_mult_distr in εpos.
          rewrite d0 in εpos. rewrite Rdiv_0_r in εpos. lra. }
        iNext ; iIntros (a) "rnm'" => /=... tp_load ; wp_load...
        case_bool_decide (#i = #0) as case_i0 ; [inversion case_i0 as [ei0]|] => /=...
        { tp_store ; tp_pures ; tp_store ; do 2 wp_store...
          iApply ("IH" with "[-HΦ]") ; iFrame.
          case_bool_decide ; try lia. iFrame. iPureIntro. intuition lia. }
        assert (¬ i = 0)%Z as nei0 ; [intros ? ; apply case_i0 ; by subst |].
        specialize (at_j (conj e nei0)). destruct at_j as (amax_adj & jmax1).
        case_bool_decide (amax1 < a)%Z as case_l ; try rewrite orb_true_r ; tp_pures ; wp_pures.
        all: case_bool_decide (amax2 < a+1)%Z as case_r ; try rewrite orb_true_r ; tp_pures ; wp_pures.
        * do 2 (tp_store ; tp_pures ; wp_store ; wp_pures).
          iApply ("IH" with "[-HΦ]") ; iFrame. case_bool_decide ; try lia ; iFrame.
          iPureIntro. intuition lia.
        * exfalso. clear -case_l case_r amax_adj. assert (a+1 <= amax2)%Z by lia.
          revert amax_adj. rewrite /dZ/distance Rabs_Zabs. apply Zabs_ind ; intros.
          -- lia.
          -- pose proof (le_IZR _ _ amax_adj). lia.
        * tp_store ; tp_pures ; tp_store ; tp_pures.
          iSpecialize ("IH" $! (i+1)%Z imax1 i amax1 (a+1)%Z).
          iSpecialize ("IH" with "[ε0 $rnm' $maxA1 $maxA2 $maxI1 $maxI2]").
          2: iApply ("IH" with "[HΦ]") ; iFrame.
          iSplitL. 1: case_bool_decide ; try lia ; iFrame "ε0".
          iPureIntro ; intuition lia.
        * iApply ("IH" with "[-HΦ]") ; iFrame. case_bool_decide ; try lia.
          iFrame. iFrame. iPureIntro. intuition lia. }

      (* i < j *)
      { tp_bind (Laplace _ _ _) ; wp_bind (Laplace _ _ _).
        iApply (hoare_couple_laplace e1 e2 (e2 - e1)%Z 0%Z with "[$rnm' ε0]") => //.
        1: eapply Zabs_ind ; intuition lia. 1: rewrite Rmult_0_l => //.
        iNext ; iIntros (a) "rnm'" => /=... tp_load ; wp_load...

        case_bool_decide (#i = #0) as case_i0 ; [inversion case_i0 as [ei0]|] => /=...
        { do 2 (tp_store ; tp_pures ; wp_store ; wp_pures).
          iApply ("IH" with "[-HΦ]") ; iFrame.
          iSplitL. 1: repeat case_bool_decide ; try lia ; iFrame.
          iPureIntro. intuition try lia.
          all: rewrite Rabs_Zabs ; apply Zabs_ind ; intros ; apply IZR_le ; intuition try lia.
        }
        assert (¬ i = 0)%Z as nei0 ; [intros ? ; apply case_i0 ; by subst |].
        destruct (below_j (conj ij nei0)) as (amax_adj & imax1i & imax2i).
        destruct (dZ_bounded_cases _ _ _ amax_adj).
        case_bool_decide (amax1 < a)%Z as case_l.
        all: case_bool_decide (amax2 < a + (e2 - e1))%Z as case_r...
        all: try do 2 (tp_store ; tp_pures) ; try do 2 wp_store...
        - iApply ("IH" with "[-HΦ]") ; iFrame.
          iSplitL. 1: repeat case_bool_decide ; try lia ; iFrame.
          iPureIntro ; intuition try lia.
          all: rewrite Rabs_Zabs ; apply IZR_le, Zabs_ind ; lia.
        - iApply ("IH" $! (i+1)%Z with "[-HΦ]") ; iFrame.
          iSplitL. 1: repeat case_bool_decide ; try lia ; iFrame.
          assert (a+(e2-e1) <= amax2)%Z by lia.
          iPureIntro ; intuition try lia.
          all: rewrite Rabs_Zabs ; apply IZR_le, Zabs_ind ; lia.
        - iApply ("IH" $! (i+1)%Z with "[-HΦ]") ; iFrame.
          iSplitL. 1: repeat case_bool_decide ; try lia ; iFrame.
          assert (a <= amax1)%Z by lia.
          iPureIntro ; intuition try lia.
          all: rewrite Rabs_Zabs ; apply IZR_le, Zabs_ind ; lia.
        - iApply ("IH" $! (i+1)%Z with "[-HΦ]") ; iFrame.
          iSplitL. 1: repeat case_bool_decide ; try lia ; iFrame.
          iPureIntro ; intuition try lia. }

      (* j < i *)
      { tp_bind (Laplace _ _ _) ; wp_bind (Laplace _ _ _).
        iApply (hoare_couple_laplace e1 e2 (e2 - e1)%Z 0%Z with "[$rnm' ε0]") => //.
        1: eapply Zabs_ind ; intuition lia. 1: rewrite Rmult_0_l => //.
        iNext ; iIntros (a) "rnm'" => /=... tp_load ; wp_load...

        case_bool_decide (#i = #0) as case_i0 ; [inversion case_i0 as [ei0]|] => /=...
        { do 2 (tp_store ; tp_pures ; wp_store ; wp_pures).
          iApply ("IH" with "[-HΦ]") ; iFrame.
          iSplitL. 1: repeat case_bool_decide ; try lia ; iFrame.
          iPureIntro ; lia. }

        assert (¬ i = 0)%Z as nei0 ; [intros ? ; apply case_i0 ; by subst |].
        specialize (above_j (conj ij nei0)).
        case_bool_decide (amax1 < a)%Z as case_l.
        all: case_bool_decide (amax2 < a + (e2 - e1))%Z as case_r...
        all: try do 2 (tp_store ; tp_pures) ; try do 2 wp_store...
        - iApply ("IH" with "[-HΦ]") ; iFrame.
          iSplitL. 1: repeat case_bool_decide ; iFrame ; lia. iPureIntro ; lia.
        - iApply ("IH" $! (i+1)%Z with "[-HΦ]") ; iFrame.
          iSplitL. 1: repeat case_bool_decide ; iFrame ; lia. iPureIntro ; lia.
        - iApply ("IH" $! (i+1)%Z with "[-HΦ]") ; iFrame.
          iSplitL. 1: repeat case_bool_decide ; iFrame ; lia. iPureIntro ; lia.
        - iApply ("IH" $! (i+1)%Z with "[-HΦ]") ; iFrame.
          iSplitL. 1: repeat case_bool_decide ; iFrame ; lia. iPureIntro ; lia.
      }

      (* this is the case where the predicted result j is not actually an integer *)
      Unshelve. destruct N... { tp_load ; wp_load. iApply "HΦ". iFrame. done. }
      tp_bind (evalQ _ _) ; wp_bind (evalQ _ _).
      iApply (hoare_sensitive_Z_bounded $! (qi_sens _) with "[] [] rnm") => //.
      1: real_solver. rewrite Zmult_1_l.
      iIntros "!> % (%e1 & %e2 & -> & rnm & %e1e2_adj & %e1e2_adj')" => /=.
      tp_bind (Laplace _ _ _) ; wp_bind (Laplace _ _ _). iMod ecm_zero as "ε0".
      iApply (hoare_couple_laplace e1 e2 (e2 - e1)%Z 0%Z with "[$rnm ε0]") => //.
      1: eapply Zabs_ind ; intuition lia.
      1: rewrite Rmult_0_l => //.
      iNext ; iIntros (a) "rnm'" => /=...

      tp_load ; wp_load... tp_store ; wp_store...
      tp_store ; tp_pure ; tp_pure ; tp_pure. wp_store. wp_pure.
      rewrite -!/(rnm_body _ _ _ _ _ _ _ _).

      cut (∀ (i : Z) (imax1 imax2 : nat) (amax1 amax2 : Z),
              {{{ maxI1 ↦ #imax1 ∗ maxI2 ↦ₛ #imax2 ∗ maxA1 ↦ #amax1 ∗ maxA2 ↦ₛ #amax2
                  ∗ ⤇ fill K (rnm_body num den evalQ dDB (S N) db' maxI2 maxA2 #i)
                  ∗ ⌜ 0 <= i <= (S N) ⌝%Z }}}
                rnm_body num den evalQ dDB (S N) db maxI1 maxA1 #i
                {{{ (v : nat), RET #v; ∃ (v' : nat), ⤇ fill K #v' ∗ ⌜ #v = j -> #v' = j ⌝ }}}).
      { intros h. iMod ecm_zero as "ε0". iApply (h with "[-HΦ]").
        - replace 0%Z with (Z.of_nat 0) by lia. iFrame. iPureIntro ; lia.
        - iNext ; iIntros (v) "(%v' & v' & %h')". iApply "HΦ". iFrame.
          iPureIntro. intro h''. do 3 f_equal. apply h'. inversion h''. done.
      }
      clear Φ.

      iLöb as "IH".
      iIntros (i imax1 imax2 amax1 amax2 Φ) "(maxI1 & maxI2 & maxA1 & maxA2 & rnm' & %iN) HΦ".
      rewrite {3 4}/rnm_body... case_bool_decide (#i = #(S N)) as iN'...
      + tp_load ; wp_load. iApply "HΦ". iExists imax2. iFrame "rnm'". iPureIntro.
        intros ij1. rewrite -ij1 in n. exfalso. apply n. eexists _. reflexivity.
      + assert (i ≠ S N) as iN''. { intro h. apply iN'. subst. done. }
        assert (i < S N)%Z by lia.
        rewrite -!/(rnm_body _ _ _ _ _ _ _ _).
        clear e1 e2 e1e2_adj e1e2_adj'.
        tp_bind (evalQ _ _) ; wp_bind (evalQ _ _).
        iApply (hoare_sensitive_Z_bounded $! (qi_sens _) with "[] [] rnm'") => //.
        1: real_solver. rewrite Zmult_1_l.
        iIntros "!> % (%e1 & %e2 & -> & rnm' & %e1e2_adj & %e1e2_adj')" => /=.
        tp_bind (Laplace _ _ _) ; wp_bind (Laplace _ _ _).
        iMod ecm_zero as "ε0".
        iApply (hoare_couple_laplace e1 e2 (e2 - e1)%Z 0%Z with "[$rnm' ε0]") => //.
        1: eapply Zabs_ind ; intuition lia.
        1: rewrite Rmult_0_l => //.
        iNext ; iIntros (a') "rnm'" => /=... tp_load ; wp_load...
        destruct (bool_decide (#i = #0) || bool_decide (amax1 < a')%Z)...
        all: destruct (bool_decide (#i = #0) || bool_decide (amax2 < a' + (e2 - e1))%Z)...
        all: repeat (tp_store ; tp_pures) ; repeat wp_store...
        all: replace i with (Z.of_nat (Z.to_nat i)) ; [|lia] ; iFrame...
        all: iApply ("IH" with "[-HΦ]") => // ; iFrame.
        all: iPureIntro ; lia.
  Qed.

End rnm.

Lemma rnm_diffpriv_cpl num den (evalQ : val) DB (dDB : Distance DB) (N : nat) :
  (0 < IZR num / IZR (2 * den))%R →
  (0 <= IZR num / IZR den)%R →
  (∀ `{!diffprivGS Σ}, ∀ i : Z, ⊢ hoare_sensitive (evalQ #i) 1 dDB dZ) →
  ∀ db db', (dDB db db' <= 1)%R → ∀ σ,
      DPcoupl
        (lim_exec ((report_noisy_max num den evalQ #N (inject db)), σ))
        (lim_exec ((report_noisy_max num den evalQ #N (inject db')), σ))
        (λ v v', v = v')
        (IZR num / IZR den) 0.
Proof.
  intros. replace 0%R with (SeriesC (λ _ : val, 0)). 2: by by apply SeriesC_0.
  apply DPcoupl_pweq => //=. 1: apply ex_seriesC_0. intros x'.
  eapply (adequacy.wp_adequacy diffprivΣ) => //.
  iIntros (?) "rnm' ε _".
  unshelve iPoseProof (rnm_pw_diffpriv num den evalQ DB dDB N [] H (H1 _ _) db db' H2 x'
    (λ v, ∃ v' : val, ⤇ v' ∗ ⌜v = x' → v' = x'⌝)%I) as "h" => //=.
  iSpecialize ("h" with "[$]"). iApply "h".
  iNext. iIntros (?) "[% [? %h]]". iExists v' ; iFrame. iPureIntro. exact h.
Qed.

Lemma rnm_diffpriv num den (evalQ : val) DB (dDB : Distance DB) (N : nat) :
  (0 < IZR num / IZR (2 * den))%R →
  (0 <= IZR num / IZR den)%R →
  (∀ `{!diffprivGS Σ}, ∀ i : Z, ⊢ hoare_sensitive (evalQ #i) 1 dDB dZ) → ∀ σ,
      diffpriv_pure
        dDB
        (λ db, lim_exec ((report_noisy_max num den evalQ #N (inject db)), σ))
        (IZR num / IZR den).
Proof.
  intros. apply diffpriv_approx_pure. apply DPcoupl_diffpriv.
  intros. apply rnm_diffpriv_cpl => //.
Qed.

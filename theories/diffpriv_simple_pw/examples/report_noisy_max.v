From iris.base_logic Require Export na_invariants.
From clutch.common Require Import inject.
From clutch.prelude Require Import tactics.
From clutch.prob Require Import differential_privacy.
From clutch.diffpriv_simple_pw Require Import adequacy_simple_pw diffpriv_simple_pw proofmode_simple_pw.

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

  (* Really, the guard on the if statement that ensures initialization on the
     first iteration should be pulled out of the recursion as follows:

  Definition report_noisy_max (num den : Z) : val :=
    λ:"evalQ" "N" "d",
      if: "N" ≤ #0 then #(-1) else
      let: "maxI" := ref #0 in
      let: "maxA" := ref #0 in
      let: "f" :=
        (rec: "rnm" "i" :=
           if: "i" = "N" then
             ! "maxI"
           else
             (let: "a" := Laplace #num #(2*den) ("evalQ" "i" "d") in
              (if: ! "maxA" < "a" then
                 "maxA" <- "a" ;;
                 "maxI" <- "i"
               else #()) ;;
              "rnm" ("i" + #1)))
      in "f" #0.

 *)

  Definition rnm_body (num den : Z) (evalQ : val) {DB} (dDB : Distance DB) (N : nat) (db : DB) (maxI maxA : loc) :=
    (rec: "rnm" "i" :=
       if: "i" = #N then ! #maxI
       else let: "a" := Laplace #num #(2*den) (evalQ "i" (inject db)) in
            (if:  "i" = #0 `or` ! #maxA < "a"
             then #maxA <- "a";; #maxI <- "i" else #());;
            "rnm" ("i" + #1))%V.

  (* An online version of RNM (oRNM) providing two methods:
- add_query receives and evaluates queries one at a time, storing the highest (noisy) result,
- release outputs the index of the query with the highest result. *)
  Definition report_noisy_max_online : val :=
    λ:"num" "den" "evalQ" "d",
      let: "maxI" := ref #(-1) in
      let: "maxA" := ref #0 in
      let: "add_query" :=
        λ:"i",
          (let: "a" := Laplace "num" (#2 * "den") ("evalQ" "i" "d") in
           (if: "i" = #0 `or` ! "maxA" < "a" then
              "maxA" <- "a" ;;
              "maxI" <- "i"
            else #())) in
      let: "release" :=
        λ:"_",
          ! "maxI"
      in ("add_query", "release").

  (* Given the error credits for one run of RNM, initializing oRNM provides an abstract token AUTH
  that is required to call the add_query and release methods, and...
- add_query processes a query and returns AUTH back to the caller
- release consumes the AUTH token and ensures that both db and db' yield (pointwise) equal results *)
  Lemma rnm_online (j : Z) (num den : Z) (evalQ : val)
    (εpos : 0 < IZR num / IZR den) `(dDB : Distance DB) (db db' : DB) (adj : dDB db db' <= 1) K
    :
    (∀ i, wp_sensitive (Val evalQ i) 1 dDB dZ) -∗
    ↯m (IZR num / IZR den) -∗

    ⤇ fill K (report_noisy_max_online #num #den (Val evalQ) (inject db')) -∗
    WP report_noisy_max_online #num #den evalQ (inject db)

      {{ add_release,
           ∃ (add' release' : val) (AUTH : iProp Σ),

             ⤇ fill K (add', release')%V ∗

             AUTH ∗

             (∀ K i,
                 AUTH -∗
                 ⤇ fill K (add' #i) -∗
                 WP (Fst (Val add_release) #i) {{ _, ⤇ fill K #() ∗ AUTH }}) ∗

             (∀ K,
                 AUTH -∗
                 ⤇ fill K (release' #()) -∗
                 WP (Snd (Val add_release) #())
                   {{ v, ∃ v' : val, ⌜ v = #j → v' = #j ⌝ }})
            }}.
  Proof with (tp_pures ; wp_pures).
    (* The privacy proof of RNM hinges on the fact that the credit gets spent when the "winning"
    query gets evaluated, i.e., when the index matches that of the result in the point-wise
    equality.

    For oRNM, the result index in the point-wise equality of the release method can either be
    quantified before or after the initialisation of oRNM. Knowing the index is required to decide
    which coupling to spend the credit on. If the index is quantified in the spec for `release`,
    then `add` cannot know about it, and we don't know how to couple.

    This is why this current spec quantifies over `i : Z` before initialising oRNM. *)

    (* NB: Actually, since we require to know `j` in advance, we could also make the queries on
    `i≠j` free and only require ↯ε on the j-th query. *)

    iIntros "sens ε rhs".
    rewrite /report_noisy_max_online... simpl...
    tp_alloc as maxI2 "maxI2". tp_pures. tp_alloc as maxA2 "maxA2". do 5 tp_pure.
    wp_pures. wp_alloc maxI1 as "maxI1". wp_alloc maxA1 as "maxA1". do 5 wp_pure.
    simpl...
    iExists _,_.
    (* TODO: This is too simple-minded; the availability of ε in AUTH has to depend on whether or
    not `i` has been queried. *)
    iExists (
        maxI2 ↦ₛ #(-1) ∗
        maxA2 ↦ₛ #0 ∗
        maxI1 ↦ #(-1) ∗
        maxA1 ↦ #0 ∗
        ↯m (IZR num / IZR den)
      )%I.
    iFrame.
    clear K.
    iModIntro. iSplitL.
    - iIntros "%K %i (maxI2 & maxA2 & maxI1 & maxA1 & ε) rhs".
      admit.
    - iIntros "%K (maxI2 & maxA2 & maxI1 & maxA1 & ε) rhs".
      admit.
  Abort.

  (* The above-mentioned issue with anticipating when an error-credit gets spent by examining the
  index returned as final result can be exhibited in an example simpler than oRNM.

   This problem can be stated in Eris as follows. Sufficient use of laziness in `get` might solve
   this particular problem. *)

  Goal
    ↯m (1/4)  -∗
    WP
      let: "res" := ref (rand #3) in
      let: "resample" := λ:"_", "res" <- rand #3 in
      let: "get" := λ:"_", !"res" in
      ("resample", "get")
        {{ resample_get ,
             let (resample, get) := ((Fst (Val resample_get))%E, (Snd (Val resample_get))%E) in
             ∃ TOKEN : iProp Σ,
               TOKEN ∗
               (TOKEN -∗ WP resample #() {{ _, TOKEN }}) ∗
               (TOKEN -∗ WP get #() {{ v, ∃ k : Z, ⌜v = #k⌝ ∗ ⌜0 < k⌝%Z }})
        }}.
  Abort.

  (* One can generalize this argument by parametrising `resample` by some function `f` which is
  (i) known to be safe, and (ii) produces the result 1 if given some resource `X`.

    This is now a problem in unary separation logic, although it is not immediate what `X` and `f` should be.
   *)
  Goal
    ∀ (f : val), ∃ (X : iProp Σ),
      (X -∗ WP (Val f) #()  {{ v, ⌜v = #1⌝}}) -∗
      (WP (Val f) #()  {{ _, ⌜True⌝ }}) -∗
      X -∗
      WP
        let: "res" := ref (f #()) in
        let: "resample" := (λ:"_", "res" <- f #()) in
        let: "get" := (λ:"_", !"res") in
        ("resample", "get")
          {{ resample_get ,
               let (resample, get) := ((Fst (Val resample_get))%E, (Snd (Val resample_get))%E) in
               ∃ TOKEN,
                 TOKEN ∗
                 (TOKEN -∗ WP resample #() {{ _, TOKEN }}) ∗
                 (TOKEN -∗ WP get #() {{ v, ∃ k : Z, ⌜v = #k⌝ ∗ ⌜0 < k⌝%Z }})
          }}.
  Abort.

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

  Definition WP_PWEQ := ∀ e e' K E,
    (
      ⤇ fill K e' ⊢
      ∀ (RES : val),
          WP e @ E
            {{ v, ∃ v' : val, ⤇ fill K (Val v') ∗ ⌜v = RES → v' = RES⌝ }} )
→
    (⤇ fill K e'
    ⊢
     WP e @ E
      {{ v, ∃ v' : val, ⤇ fill K (Val v') ∗ ⌜v = v'⌝ }}).


  (* unclear how to close because the error resources don't work out *)
  (* Lemma rnm_diffpriv num den (evalQ : val) DB (dDB : Distance DB) (N : nat) K :
       (0 < IZR num / IZR (2 * den)) →
       (∀ i : Z, ⊢ hoare_sensitive (evalQ #i) 1 dDB dZ) →
       ∀ db db', dDB db db' <= 1 →
                 WP_PWEQ →
                   ↯m (IZR num / IZR den) ∗
                       ⤇ fill K (report_noisy_max num den evalQ #N (inject db'))
                       ⊢
                         WP report_noisy_max num den evalQ #N (inject db)
                           {{ v, ∃ (v' : val), ⤇ fill K v' ∗ ⌜ v = v' ⌝  }}
     .
     Proof.
       intros ????? wp_pweq. iIntros "(ε & rhs)".
       iPoseProof (wp_pweq with "[$rhs]") as "pweq".
       iApply (wp_pweq with "[$rhs]") ; iIntros "rhs %RES".
       iApply (rnm_pw_diffpriv with "[$ε $rhs]") => //.
       by iNext ; iIntros.
     Qed. *)

  Lemma wp_pweq_couple : WP_PWEQ.
  Proof.
    iLöb as "IH". iIntros (e e' K E).
    iIntros "%pw rhs".
    (* iIntros "[rhs pw] /=". *)
    rewrite wp_unfold /wp_pre //=.
    setoid_rewrite wp_unfold at 3.
    rewrite {1}/wp_pre /=.
    iIntros (?????) "([H T] & S & ε & δ)".
    iSpecialize ("pw" with "rhs").
    destruct (to_val e) eqn:ev.
    -
      iSpecialize ("pw" $! v).
      iMod ("pw" with "[$]") as "pw". iModIntro.
      iApply (spec_coupl_mono ∅ with "[] pw") => //=.
      iIntros (?????) "> (HT & S & E & %v' & rhs & %pweq)". iFrame.
      rewrite pweq => //.
    -
      iApply spec_coupl_ret.
      iSpecialize ("pw" with "[$H $T $S $ε $δ]").

      fail.

      iApply (prog_coupl_mono with "[pw] ") => //=.


    (*   iApply fupd_mask_intro => //.
         iIntros "hclose".
       iApply spec_coupl_ret. iFrame.

       rewrite spec_coupl_unfold /spec_coupl_pre //=.
       iLeft.

       rewrite wp_unfold /wp_pre //=.
       rewrite ev.
       iSpecialize ("pw" $! _ _ _ _ _).
       iSpecialize ("pw" with "[$H $T $S $ε $δ]").
         iFrame. iMod "hclose". iModIntro.
         admit.
       - *)
  Admitted.


  Corollary wp_pweq_couple_swap K (* E  *)e e' :
    ⤇ fill K e' ∗
    (∀ (RES : val),
        ⤇ fill K e' -∗
          WP e (* @ E *)
            {{ v, ∃ v' : val, ⤇ fill K (Val v') ∗ ⌜v = RES → v' = RES⌝ }} )
    -∗
     WP e (* @ E *)
      {{ v, ∃ v' : val, ⤇ fill K (Val v') ∗ ⌜v = v'⌝ }}.
  Proof.
    iIntros "[rhs pw]". iPoseProof (wp_pweq_couple e e' K with "[$rhs pw]") as "h".
    2: iApply "h".
    iIntros. iApply "pw". done.
  Qed.


  (* Lemma hoare_pweq_couple K E e e' ε :
       {{{ ⤇ fill K e' ∗ ↯m ε ∗
           (∀ (RES : val),
               {{{ ⤇ fill K e' ∗ ↯m ε }}}
                 e @ E
                 {{{ (v : val), RET v; ∃ v' : val, ⤇ fill K (Val v') ∗ ⌜v = RES → v' = RES⌝ }}} )
       }}}
         e @ E
         {{{ (v : val), RET v; ∃ v' : val, ⤇ fill K (Val v') ∗ ⌜v = v'⌝ }}}.
     Proof.
       iIntros (Φ) "[rhs [ε pw]] HΦ".
       iPoseProof (wp_pweq_couple_swap with "[$rhs pw ε HΦ]") as "wppw" => //.
       { iIntros "%RES rhs". iSpecialize ("pw" $! RES with "[$]").
     Admitted.

     (* persistence is annoying *)
     Lemma hoare_pweq_couple' K E e e' num den :
       {{{ ⤇ fill K e' ∗ ↯m (IZR num / IZR den) ∗
           (∀ (RES : val),
               {{{ ⤇ fill K e' ∗ ↯m (IZR num / IZR den) }}}
                 e @ E
                 {{{ (v : val), RET v; ∃ v' : val, ⤇ fill K (Val v') ∗ ⌜v = RES → v' = RES⌝ }}} )
       }}}
         e @ E
         {{{ (v : val), RET v; ∃ v' : val, ⤇ fill K (Val v') ∗ ⌜v = v'⌝ }}}.
     Proof.
       (* iIntros "%φ [rhs [ε h]] hφ".
          iApply (pweq_couple with "[$rhs h ε]") => //.
          iIntros.
          iIntros (ψ).
          iSpecialize ("h" $! RES _).
          iApply (wp_strong_mono'' with "h").
          iApply "h".
          iRevert "ε". *)
     Admitted. *)




End rnm.


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
  eapply (adequacy.wp_adequacy diffprivΣ) => //.
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
  eapply (adequacy.wp_adequacy diffprivΣ) => //.
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

Lemma rnm_diffpriv num den (evalQ : val) DB (dDB : Distance DB) (N : nat) :
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

(* sketchy obsolete concrete example below *)

(* Definition DB := (Z * Z * Z)%type. *)
(* Definition dDB : Distance DB. *)
(*   unshelve econstructor. *)
(*   - exact (λ (x y : DB), match (x,y) with *)
(*                          | ((x1, x2, x3), (y1, y2, y3)) => *)
(*                              (if Z.eqb x1 y1 then 0 else 1) *)
(*                              + (if Z.eqb x2 y2 then 0 else 1) *)
(*                              + (if Z.eqb x3 y3 then 0 else 1) *)
(*                          end). *)
(*   - apply _. *)
(*   - intros [[x1 x2] x3] [[y1 y2] y3]. destruct (x1 =? y1)%Z, (x2 =? y2)%Z, (x3 =? y3)%Z. *)
(*     all: compute ; lra. *)
(*   - simpl. intros [[x1 x2] x3] [[y1 y2] y3] [[-> ->] ->]. rewrite !Z.eqb_refl. compute ; lra. *)
(*   - simpl. intros [[x1 x2] x3] [[y1 y2] y3]. *)
(*     destruct (x1 =? y1)%Z eqn:h1, (x2 =? y2)%Z eqn:h2, (x3 =? y3)%Z eqn:h3 ; try (compute ; intuition auto ; try lra). *)
(*     + rewrite (Z.eqb_eq x1 y1) // in h1. *)
(*     + rewrite (Z.eqb_eq x2 y2) // in h2. *)
(*     + rewrite (Z.eqb_eq x3 y3) // in h3.  *)
(* Defined. *)

Definition ID := Fst.
Definition age := Snd.
(* Two example databases with three rows each containing a ID number and an age. *)
Definition db : val := ( (#3, #12), (#1, #42), (#0, #57) ).
Definition db' : val := ( (#3, #12), (#2, #24), (#0, #57) ).

Definition under_40 : val := λ:"r", if: age "r" < #40 then #1 else #0.
Definition over_80 : val := λ:"r", if: #80 < age "r" then #1 else #0.
Definition setmap : val := λ: "f" "db", ("f" (Fst (Fst "db")) , "f" (Snd (Fst "db")) , "f" (Snd "db")).
Definition setsum : val := λ: "db", (Fst (Fst "db")) + (Snd (Fst "db")) + (Snd "db").
Definition count_query (num den : Z) : val := λ:"b", setsum (setmap (λ:"z", Laplace #num #den "z") (setmap under_40 "b")).

Definition count_under_40 : val := λ:"db", setsum $ setmap under_40 "db".
Definition count_over_80 : val := λ:"db", setsum $ setmap over_80 "db".

Definition evalQ : val :=
  λ:"i" "db", if: "i" = #0 then count_under_40 "db"
              else if: "i" = #1 then count_over_80 "db"
                   else #0.

(* concrete example run *)
(* Lemma rnm_diffpriv_3 num den :
       (0 < IZR num / IZR den) →
       ∀ (K : list (ectxi_language.ectx_item prob_ectxi_lang)),
         {{{ ⤇ fill K (report_noisy_max num den evalQ #2 (inject db')) ∗
             ↯m (IZR num / IZR den)
               (* ↯m 0 *)
         }}}
           (report_noisy_max num den evalQ #2 (inject db))
           {{{ (v : val), RET v; ⤇ fill K v }}}.
     Proof.
       iIntros (???) "[rnm' ε] hφ".
       rewrite /report_noisy_max.
       simpl.
       tp_pures.
       tp_alloc as maxI2 "maxI2". tp_pures. tp_alloc as maxA2 "maxA2". do 5 tp_pure.
       wp_pures. wp_alloc maxI1 as "maxI1". wp_alloc maxA1 as "maxA1". do 5 wp_pure.
       wp_rec. wp_pures.
       tp_pures.
       rewrite {2 4}/evalQ. tp_pures. wp_pures.
       rewrite /count_under_40/setsum/setmap/under_40/age. wp_pures. tp_pures.

       wp_bind (Laplace _ _ _). tp_bind (Laplace _ _ _).
       iMod ecm_zero as "ε0".
       unshelve iApply (hoare_couple_laplace 1 2 1 0 _ (num) (2*den) _ _  (AppRCtx _ :: K)
           with "[ε0 $rnm']" ) => //=.
       1: by cbv.
       { rewrite mult_IZR.
         rewrite Rmult_comm.
         rewrite Rdiv_mult_distr.
         rewrite {1}/Rdiv.
         revert H.
         set (r := (IZR num / IZR den)).
         lra.
       }
       1: rewrite Rmult_0_l => //.
       simpl. tp_pures.
       iIntros "!> %z f'" => /=. wp_pures. tp_pures. tp_load ; wp_load. wp_pures.
       wp_load. tp_pures. tp_load. tp_pures. wp_pures.
       tp_store. tp_pures. tp_store. do 2 wp_store. wp_pures. tp_pures.
       rewrite {2 4}/evalQ. tp_pures. 1,2: try naive_solver. wp_pures.
       rewrite /count_over_80/setsum/setmap/over_80/age. wp_pures. tp_pures.
       wp_bind (Laplace _ _ _). tp_bind (Laplace _ _ _).
       iMod ecm_zero as "ε0".
       unshelve iApply (hoare_couple_laplace _ _ 0 0 _ (num) (2*den) _ _  (AppRCtx _ :: K)
           with "[ε ε0 $f']" ) => //=.
       1: try naive_solver.
       { rewrite mult_IZR.
         rewrite Rmult_comm.
         rewrite Rdiv_mult_distr.
         rewrite {1}/Rdiv.
         revert H.
         set (r := (IZR num / IZR den)).
         lra.
       }
       (* 1: rewrite Rmult_1_l => //. 1:admit. *)
       1: rewrite Rmult_0_l => //.
       simpl. tp_pures.
       iIntros "!> %z2 f'" => /=. wp_pures. tp_pures. tp_load ; wp_load. wp_pures.
       wp_load. wp_pures.
       tp_pures. tp_load. tp_pures.
       rewrite !Zplus_0_r ?Zplus_0_l.
       case_bool_decide.
       - do 2 wp_store. wp_pures.
         tp_pures. tp_store ; tp_pures ; tp_store ; tp_pures.
         tp_load.
         wp_load.
         iApply "hφ". done.
         Unshelve.
         2: f_equal. simpl.
       - wp_pures.
         tp_pures.
         tp_load.
         wp_load.
         iApply "hφ". done.
         Unshelve.
         all: f_equal.
     Qed. *)

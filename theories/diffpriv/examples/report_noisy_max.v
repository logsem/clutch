From iris.base_logic Require Export na_invariants.
From clutch.common Require Import inject.
From clutch.prelude Require Import tactics.
From clutch.prob Require Import differential_privacy.
From clutch.diffpriv Require Import adequacy diffpriv proofmode.

Definition logN : namespace := nroot .@ "logN".

Class diffprivRGS Σ := DiffprivRGS {
                           diffprivRGS_diffprivGS :: diffprivGS Σ;
                           diffprivRGS_na_invG :: na_invG Σ;
                           diffprivRGS_nais : na_inv_pool_name;
                         }.

Definition na_ownP `{!diffprivRGS Σ} := na_own diffprivRGS_nais.
Definition na_invP `{!diffprivRGS Σ} := na_inv diffprivRGS_nais.
Definition na_closeP `{!diffprivRGS Σ} P N E := (▷ P ∗ na_ownP (E ∖ ↑N) ={⊤}=∗ na_ownP E)%I.


Section rnm.
  Context `{!diffprivRGS Σ}.

  #[local] Open Scope R.

  Definition report_noisy_max (num den : Z) : val :=
    λ:"evalQ" "N" "d",
      let: "maxI" := ref #(-1) in
      let: "maxA" := ref #0 in
      let: "cur" := ref #0 in
      let: "f" :=
        (rec: "rnm" "i" :=
           if: "i" = "N" then
             ! "maxI"
           else
             (let: "a" := Laplace #num #(2*den) ("evalQ" "i" "d") in
              "cur" <- "a" ;;
              (if: (* (! "maxI" = #(-1)) `or` *) (! "maxA" < "a") then
                 "maxA" <- "a" ;;
                 "maxI" <- "i"
               else #()) ;;
              "rnm" ("i" + #1)))
      in "f" #0.

  Definition rnm_body (num den : Z) (evalQ : val) {DB} (dDB : Distance DB) (N : nat) (db : DB) (maxI maxA cur : loc) :=
    (rec: "rnm" "i" :=
       if: "i" = #N then ! #maxI
       else let: "a" := Laplace #num #(2*den) (evalQ "i" (inject db)) in
            #cur <- "a" ;;
            (if: (* ! #maxI = #(-1) `or` *) ! #maxA < "a"
             then #maxA <- "a";; #maxI <- "i" else #());;
            "rnm" ("i" + #1))%V.

  Definition DB := (Z * Z * Z)%type.
  Definition dDB : Distance DB.
    unshelve econstructor.
    - exact (λ (x y : DB), match (x,y) with
                           | ((x1, x2, x3), (y1, y2, y3)) =>
                               (if Z.eqb x1 y1 then 0 else 1)
                               + (if Z.eqb x2 y2 then 0 else 1)
                               + (if Z.eqb x3 y3 then 0 else 1)
                           end).
    - apply _.
    - intros [[x1 x2] x3] [[y1 y2] y3]. destruct (x1 =? y1)%Z, (x2 =? y2)%Z, (x3 =? y3)%Z.
      all: lra.
    - simpl. intros [[x1 x2] x3]. rewrite !Z.eqb_refl. lra.
    - simpl. intros [[x1 x2] x3] [[y1 y2] y3].
      destruct (x1 =? y1)%Z eqn:h1, (x2 =? y2)%Z eqn:h2, (x3 =? y3)%Z eqn:h3 ; intuition auto ; try lra.
      rewrite (Z.eqb_eq x1 y1) in h1.
      rewrite (Z.eqb_eq x2 y2) in h2.
      rewrite (Z.eqb_eq x3 y3) in h3. subst ; done.
  Defined.

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

  (* Definition rwp (e e' : expr) E (R : val → val → iProp Σ) : iProp Σ :=
       (⤇ e' -∗ WP e @ E {{ v, ∃ v', R v v' }})%I.

     (* Notation "'RWP' e ~ e' {{ Φ } } " := (rwp e e' top Φ) (only parsing).
        Notation "'RWP' e ~ e' @ E {{ Φ } } " := (rwp e e' E Φ) (only parsing). *)
     (* Notation "'RWP' e ~ e' @ E {{ v v' , Φ } } " := (rwp e e' E (λ v v', Φ)). *)

     Notation "'RWP' e << e' {{ v , v' , Φ } } " := (rwp e e' top (λ v v', Φ))
       (at level 20, e, e', Φ at level 200,
      format "'[hv' 'RWP'  e  <<  e'  '/' {{  '[' v ,  v' ,  Φ  ']' } } ']'") : bi_scope.

     Lemma pweq (e e' : expr) :
       (⊢ RWP e << e' {{ v , v' ,  ⌜ v = v' ⌝ }})
       →
       (∀ x : val, ⤇ e' ⊢ WP e {{ v, ∃ v', ⤇ (of_val v') ∗ ⌜v = x -> v' = x⌝}})
       →
         (⤇ e' ⊢ WP e {{ v, ∃ v', ⤇ (of_val v') ∗ ⌜v = v'⌝ }}). *)

  Lemma pweq_weak (e e' : expr) K :
    (⊢ (⤇ e' -∗ WP e {{ v, ∃ v', ⤇ (of_val v')}}))
    →
      (⤇ fill K e' -∗ WP e {{ v, (∃ z : Z, ⌜v = #z⌝)
                                 ∗ ∃ v', ⤇ fill K (of_val v') ∗ ⌜∀ x : Z, v = #x -> v' = #x⌝}})
      -∗
    (⤇ fill K e' -∗ WP e {{ v, ∃ z : Z, ⌜v = #z⌝ ∗ ⤇ fill K (of_val v) }}).
  Proof.
    iIntros (?) "h Ke'".
    iSpecialize ("h" with "Ke'").
    iApply (wp_mono with "h").
    iIntros (v) "((%z & %eq_v_z) & %v' & Kv' & %alleq)".
    iExists z. rewrite (alleq _ eq_v_z). rewrite eq_v_z. iFrame. done.
  Qed.


  (* Lemma pweq (e e' : expr) K :
       (* (⊢ (⤇ e' -∗ WP e {{ v, ∃ v', ⤇ (of_val v')}}))
          → *)
       ∀ x : Z,
       ( ⤇ fill K e' -∗ WP e {{ v, ∃ v', ⤇ fill K (of_val v') ∗ ⌜v = #x -> v' = #x⌝}})
       -∗
         (⤇ fill K e' -∗ WP e {{ v, ∃ z : Z, ⌜v = #z⌝ ∗ ⤇ fill K (of_val v) }}).
     (* Admitted. *)
     Proof.
       intros x. iIntros "alleq e'".
       (* iDestruct (safe with "[$e']") as "H". *)
       iDestruct ("alleq" with "[$e']") as "H".
       iApply (wp_mono with "H").
       iIntros (v) "(%v' & v' & %h)".
       iExists _.
       rewrite h.
       iSplitR ; [iPureIntro|]. *)
  Lemma pweq (e e' : expr) K :
    (∀ x : Z, ⤇ fill K e' -∗ WP e {{ v, ∃ v', ⤇ fill K (of_val v') ∗ ⌜v = #x -> v' = #x⌝}})
    -∗
    ({{{ ⤇ fill K e'}}} e {{{ (v : Z), RET #v; ⤇ fill K (of_val #v) }}}).
  Admitted.


  Goal forall (N : nat), {{{ ⌜True⌝ }}} (rec: "f" "i" := if: "i" = #N then #42 else "f" ("i" + #1)) #0 {{{v, RET #v; ⌜v = 42%Z⌝}}}.
    intros. iIntros "_ h". wp_pure.
    cut (∀ i : Z, ⌜0 <= i <= N ⌝%Z ⊢ WP (rec: "f" "i" := if: "i" = #N then #42 else "f" ("i" + #1))%V #i {{ v, ⌜ v = #42 ⌝ }}).
    { intros h. iPoseProof (h 0%Z) as "hh".
      iApply wp_strong_mono'. 1: auto. 1: iApply "hh". 1: iPureIntro ; lia.
      iIntros (????) "[? [? [? ->]]]" ; iFrame. iModIntro. iApply "h".
      done.
    }
    iLöb as "IH". iIntros (i) "%iN".
    wp_pures. case_bool_decide.
    - wp_pures. done.
    - wp_pure. wp_pure. iApply "IH".
      assert (i ≠ N). { intro. apply H. subst. done. }
      iPureIntro.
      lia.
  Qed.

  Lemma rnm_pw_diffpriv num den (evalQ : val) DB (dDB : Distance DB) (N : nat) K :
    (0 < IZR num / IZR (2 * den)) →
    (∀ i : Z, wp_sensitive (evalQ #i) 1 dDB dZ) →
    ∀ db db', dDB db db' <= 1 →
              ∀ j : nat,
                {{{ ↯ (IZR num / IZR den) ∗
                    ⤇ fill K (report_noisy_max num den evalQ #N (inject db')) }}}
                  report_noisy_max num den evalQ #N (inject db)
                  {{{ v, RET v ; ∃ v', ⤇ fill K v' ∗ ⌜ v = #j → v' = #j ⌝  }}}
  .
  Proof with (tp_pures ; wp_pures).
    intros εpos qi_sens.
    iIntros (db db' db_adj x Φ) "(ε & rnm) HΦ".
    rewrite /report_noisy_max.
    simpl.
    tp_pures.
    wp_pures.
    tp_alloc as maxI2 "maxI2". tp_pures. tp_alloc as maxA2 "maxA2". tp_pures. tp_alloc as cur2 "cur2".  do 5 tp_pure.
    wp_pures. wp_alloc maxI1 as "maxI1". wp_alloc maxA1 as "maxA1". wp_alloc cur1 as "cur1".  do 5 wp_pure.
    rewrite -/(rnm_body num den evalQ dDB N db maxI1 maxA1 cur1).
    rewrite -/(rnm_body num den evalQ dDB N db' maxI2 maxA2 cur2).
    rename x into j.
    cut
      (∀ (i imax1 imax2 : Z) (amax1 amax2 vcur1 vcur2 : Z),
          {{{ maxI1 ↦ #imax1 ∗ maxI2 ↦ₛ #imax2 ∗ maxA1 ↦ #amax1 ∗ maxA2 ↦ₛ #amax2
              ∗ cur1 ↦ #vcur1 ∗ cur2 ↦ₛ #vcur2
              ∗ ↯ (if (bool_decide (i <= j))%Z then (IZR num / IZR den) else 0)
              ∗ ⤇ fill K (rnm_body num den evalQ dDB N db' maxI2 maxA2 cur2 #i)
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
            rnm_body num den evalQ dDB N db maxI1 maxA1 cur1 #i
            {{{ (v : Z), RET #v;
                ∃ (v' : Z), ⤇ fill K #v' ∗ ⌜ v = j -> v' = j ⌝
            }}}
      ).
    1: { intros h.
         iMod ec_zero as "ε0".
         iApply (h with "[-HΦ]").
         - (* We have all the reference resources for the IH. *)
           iFrame.
           iSplitL.
           (* We have the error credits too *)
           + case_bool_decide ; iFrame.
           (* and the arithmetic works out fine *)
           + iPureIntro. split ; [|split ; [|split]]. 1: lia.
             * clear. intros. repeat split.
               -- rewrite distance_0 ; lra.
               -- intros []. lia.
             * clear. intros. repeat split. all: try lia.
               -- rewrite distance_0 ; lra.
             * clear. intros. lia.
         - (* The post-condition of the IH implies the original post. *)
           iNext ; iIntros (v) "(%v' & v' & %h')".
           iApply "HΦ". iExists _. iFrame.
           iPureIntro. intro h''. do 3 f_equal. apply h'. inversion h''. done.
    }
    clear Φ.
    iLöb as "IH".
    iIntros (i imax1 imax2 amax1 amax2 vcur1 vcur2 Φ) "(maxI1 & maxI2 & maxA1 & maxA2 & cur1 & cur2 & ε & rnm' & %iN & %below_j & %at_j & %above_j) HΦ".
    rewrite {4}/rnm_body. wp_pures.
    rewrite {3}/rnm_body. tp_pures ; [cbv ; auto|].
    case_bool_decide (#i = #N) as iN'.
    - tp_pures. wp_pures. tp_load ; wp_load. iApply "HΦ". iExists imax2. iFrame "rnm'". iPureIntro.
      intros ij1. inversion iN'.
      try lia.
    -
      assert (i ≠ N). { intro h. apply iN'. subst. done. }
      assert (i < N)%Z by lia.
      tp_pures ; wp_pures.
      rewrite -/(rnm_body _ _ _ _ _ _ _ maxA1 _).
      rewrite -/(rnm_body _ _ _ _ _ _ _ maxA2 _).
      tp_bind (evalQ _ _).
      wp_bind (evalQ _ _).

      rewrite /wp_sensitive in qi_sens.
      opose proof (qi_sens i _ _ db db') as ev ; [lra|].
      iApply (ev with "rnm'").
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

      destruct (make_decision (i = j)) as [e|n].
      + tp_bind (Laplace _ _ _).
        wp_bind (Laplace _ _ _).
        iApply (wp_couple_laplace e1 e2 1%Z 2%Z with "[$rnm' ε]") => //.
        { apply Zabs_ind ; lia. }
        { case_bool_decide. 2: lia.
          iApply ec_eq. 2: iFrame.
          rewrite /Rdiv. rewrite mult_IZR. rewrite Rinv_mult.
          field. clear -εpos.
          intro d0.
          rewrite mult_IZR in εpos.
          rewrite Rdiv_mult_distr in εpos.
          rewrite d0 in εpos.
          rewrite Rdiv_0_r in εpos.
          lra.
        }
        iNext ; iIntros (a) "rnm'" => /=.
        wp_pures. tp_pures.
        (* rewrite !Zplus_0_r. *)
        tp_store ; tp_pures ; wp_store.
        tp_load ; wp_load ; tp_pures ; wp_pures.
        specialize (at_j e). destruct at_j as (amax_adj & jmax1 & inext).
        case_bool_decide (amax1 < a)%Z as case_l ; tp_pures ; wp_pures.
        all: case_bool_decide as case_r ; tp_pures ; wp_pures.
        * do 2 (tp_store ; tp_pures ; wp_store ; wp_pures).
          iMod ec_zero as "ε0".
          iApply ("IH" with "[-HΦ]") ; iFrame.
          rewrite e. case_bool_decide ; try lia. iFrame.
          iPureIntro.

          split ; [| split ; [|split] ]. 1,2,3: lia.
          intros. split => //.
        *
          exfalso. clear -case_l case_r amax_adj.
          assert (a+1 <= amax2)%Z by lia.
          revert amax_adj.
          rewrite /dZ/distance Rabs_Zabs. apply Zabs_ind ; intros.
          -- lia.
          -- pose proof (le_IZR _ _ amax_adj). lia.
        *
          iMod ec_zero as "ε0".
          tp_store ; tp_pures ; tp_store ; tp_pures.
          iSpecialize ("IH" $! (i+1)%Z imax1 i amax1 (a+1)%Z a (a+1)%Z).
          iSpecialize ("IH" with "[ε0 $rnm' $maxA1 $maxA2 $maxI1 $maxI2 $cur1 $cur2]").
          2: iApply ("IH" with "[HΦ]") ; iFrame.
          iSplitL. 1: case_bool_decide ; try lia ; iFrame "ε0".
          iPureIntro ; split ; [|split; [|split]].
          1,2,3: by intuition lia.
          intros.
          split => //. lia.

        * iMod ec_zero as "ε0".
          iApply ("IH" with "[-HΦ]") ; iFrame.
          rewrite e. case_bool_decide ; try lia. iFrame.
          iFrame. iPureIntro. intuition lia.

      + destruct (Z.lt_trichotomy i j) as [ij | [ij|ij]]. 2: by exfalso.

        *
          destruct (below_j ij) as (amax_adj & imax1i & imax2i & inext).
          tp_bind (Laplace _ _ _).
          wp_bind (Laplace _ _ _).
          iMod ec_zero as "ε0".
          iApply (wp_couple_laplace e1 e2 (e2 - e1)%Z 0%Z with "[$rnm' ε0]") => //.
          {
            eapply Zabs_ind ; intuition lia.
          }
          1: rewrite Rmult_0_l => //.
          iNext ; iIntros (a) "rnm'" => /=.
          wp_pures. tp_pures. tp_store ; tp_pures ; wp_store.
          tp_load ; wp_load ; tp_pures ; wp_pures.

          case_bool_decide (amax1 < a)%Z as case_l.
          all: case_bool_decide (amax2 < a + (e2 - e1))%Z as case_r.
          all: tp_pures ; wp_pures.

          -- do 2 (tp_store ; tp_pures ; wp_store ; wp_pures).
             iApply ("IH" with "[-HΦ]") ; iFrame.
             iSplitL. 1: repeat case_bool_decide ; try lia ; iFrame.
             iPureIntro.
             intuition try lia.
             all: rewrite /dZ/distance Rabs_Zabs ; apply Zabs_ind ; intros ; apply IZR_le ; intuition try lia.
          -- wp_store ; wp_pures ; wp_store ; wp_pures.
             iApply ("IH" $! (i+1)%Z with "[-HΦ]") ; iFrame.
             iSplitL. 1: repeat case_bool_decide ; try lia ; iFrame.
             assert (a+(e2-e1) <= amax2)%Z by lia.
             rewrite /dZ/distance Rabs_Zabs.
             all: iPureIntro ; repeat split ; try by intuition lia.
             ++ apply IZR_le.
               revert amax_adj. rewrite /dZ/distance Rabs_Zabs.
               apply Zabs_ind ; intros ; pose proof (le_IZR _ _ amax_adj).
               all: apply Zabs_ind ; intros ; lia.
             ++ apply IZR_le.
               revert amax_adj. rewrite /dZ/distance Rabs_Zabs.
               apply Zabs_ind ; intros ; pose proof (le_IZR _ _ amax_adj).
               all: apply Zabs_ind ; intros ; lia.
          -- tp_store ; tp_pures ; tp_store ; tp_pures.
             iApply ("IH" $! (i+1)%Z with "[-HΦ]") ; iFrame.
             iSplitL. 1: repeat case_bool_decide ; try lia ; iFrame.
             assert (a <= amax1)%Z by lia.
             rewrite /dZ/distance Rabs_Zabs.
             all: iPureIntro ; repeat split ; try by intuition lia.
             ++ apply IZR_le.
                revert amax_adj.
                rewrite /dZ/distance Rabs_Zabs.
                apply Zabs_ind ; intros.
                all: pose proof (le_IZR _ _ amax_adj).
                all: apply Zabs_ind ; intros ; lia.
             ++ apply IZR_le.
                revert amax_adj.
                rewrite /dZ/distance Rabs_Zabs.
                apply Zabs_ind ; intros.
                all: pose proof (le_IZR _ _ amax_adj).
                all: apply Zabs_ind ; intros ; lia.
          -- iApply ("IH" $! (i+1)%Z with "[-HΦ]") ; iFrame.
            iSplitL. 1: repeat case_bool_decide ; try lia ; iFrame.
            all: iPureIntro ; repeat split ; try by intuition lia.

        *
          specialize (above_j ij).
          tp_bind (Laplace _ _ _).
          wp_bind (Laplace _ _ _).
          iMod ec_zero as "ε0".
          iApply (wp_couple_laplace e1 e2 (e2 - e1)%Z 0%Z with "[$rnm' ε0]") => //.
          {
            eapply Zabs_ind ; intuition lia.
          }
          1: rewrite Rmult_0_l => //.
          iNext ; iIntros (a) "rnm'" => /=.
          wp_pures. tp_pures. tp_store ; tp_pures ; wp_store.

          tp_load ; wp_load ; tp_pures ; wp_pures.

          case_bool_decide (amax1 < a)%Z as case_l.
          all: case_bool_decide (amax2 < a + (e2 - e1))%Z as case_r.
          all: tp_pures ; wp_pures.

          -- do 2 (tp_store ; tp_pures ; wp_store ; wp_pures).
             iApply ("IH" with "[-HΦ]") ; iFrame.
             iSplitL. 1: repeat case_bool_decide ; try lia ; iFrame.
             iPureIntro.
             intuition try lia.
          -- wp_store ; wp_pures ; wp_store ; wp_pures.
             iApply ("IH" $! (i+1)%Z with "[-HΦ]") ; iFrame.
             iSplitL. 1: repeat case_bool_decide ; try lia ; iFrame.
             all: iPureIntro ; repeat split ; try by intuition lia.

          -- tp_store ; tp_pures ; tp_store ; tp_pures.

             iApply ("IH" $! (i+1)%Z with "[-HΦ]") ; iFrame.
             iSplitL. 1: repeat case_bool_decide ; try lia ; iFrame.
             all: iPureIntro ; repeat split ; try by intuition lia.
          --
            iApply ("IH" $! (i+1)%Z with "[-HΦ]") ; iFrame.
            iSplitL. 1: repeat case_bool_decide ; try lia ; iFrame.
            all: iPureIntro ; repeat split ; try by intuition lia.
Qed.

























          Lemma rnm_diffpriv num den (evalQ : val) DB (dDB : Distance DB) (N : nat) :
            (0 < IZR num / IZR den) →
            (∀ i : Z, wp_sensitive (evalQ #i) 1 dDB dZ) →
            wp_diffpriv (report_noisy_max num den evalQ #N) (IZR num / IZR den) dDB.
          Proof with (tp_pures ; wp_pures).
            intros εpos qi_sens.
            iIntros (? c db db' db_adj Φ) "(rnm & ε) HΦ".
            rewrite /report_noisy_max.
            tp_pures.
            tp_alloc as maxI2 "maxI2". tp_pures. tp_alloc as maxA2 "maxA2". tp_pures. tp_alloc as cur2 "cur2".  do 5 tp_pure.
            wp_pures. wp_alloc maxI1 as "maxI1". wp_alloc maxA1 as "maxA1". wp_alloc cur1 as "cur1".  do 5 wp_pure.
            rewrite -/(rnm_body num den evalQ dDB N db maxI1 maxA1 cur1).
            rewrite -/(rnm_body num den evalQ dDB N db' maxI2 maxA2 cur2).
            iApply (pweq with "[-HΦ rnm] [$rnm] [HΦ]"). 2: iNext ; iIntros ; iApply "HΦ" ; done.
            clear Φ.
            iIntros (x) "rnm'".

            cut
              (∀ (j i imax1 imax2 : Z) (amax1 amax2 vcur1 vcur2 : Z),
                  {{{ maxI1 ↦ #imax1 ∗ maxI2 ↦ₛ #imax2 ∗ maxA1 ↦ #amax1 ∗ maxA2 ↦ₛ #amax2
                      ∗ cur1 ↦ #vcur1 ∗ cur2 ↦ₛ #vcur2
                      ∗ ↯ (if (bool_decide (i <= j))%Z then c * (IZR num / IZR den) else 0)
                      ∗ ⤇ fill K (rnm_body num den evalQ dDB N db' maxI2 maxA2 cur2 #i)
                      ∗ ⌜(amax1 < vcur1 → imax1 = i)%Z⌝
                      ∗ ⌜(amax2 < vcur2 → imax1 = i)%Z⌝
                      ∗ ⌜ imax1 = imax2 ⌝
                      (* ∗ ⌜((i = N → imax1 = j → imax2 = j))%Z⌝ *)
                      ∗ ⌜True%Z⌝
                  }}}
                    rnm_body num den evalQ dDB N db maxI1 maxA1 cur1 #i
                    {{{ (v : Z), RET #v;
                        ∃ (v' : Z), ⤇ fill K #v' ∗ ⌜ v = j -> v' = j ⌝
                    }}}

              ).

            1: { intros h.
                 iMod ec_zero as "ε0".
                 iApply (h x with "[-]").
                 - (* We have all the reference resources for the IH. *)
                   iFrame.
                   iSplitL.
                   (* We have the error credits too *)
                   + case_bool_decide ; iFrame.
                   (* and the arithmetic works out fine *)
                   + iPureIntro. repeat split. all: auto.
                 - (* The post-condition of the IH implies the original post. *)
                   iNext ; iIntros (v) "(%v' & v' & %h')".
                   iExists _. iFrame.
                   iPureIntro. intro h''. do 2 f_equal. apply h'. inversion h''. done.
            }
            iLöb as "IH".
            iIntros (j i imax1 imax2 amax1 amax2 vcur1 vcur2 Φ) "(maxI1 & maxI2 & maxA1 & maxA2 & cur1 & cur2 & ε & rnm' & %maxcur1 & %maxcur2 & %imax12 & %iN) HΦ".
            rewrite {4}/rnm_body. wp_pures.
            rewrite {3}/rnm_body. tp_pures ; [cbv ; auto|].
            case_bool_decide (#i = #N).
            - tp_pures. wp_pures. tp_load ; wp_load. iApply "HΦ". iExists imax2. iFrame "rnm'". iPureIntro.
              intros ij1. inversion H.
              try lia.
            - tp_pures ; wp_pures.
              rewrite -/(rnm_body _ _ _ _ _ _ _ maxA1 _).
              rewrite -/(rnm_body _ _ _ _ _ _ _ maxA2 _).
              tp_bind (evalQ _ _).
              wp_bind (evalQ _ _).
              iAssert ({{{⌜True⌝}}} evalQ #i (inject db) {{{ v, RET v; ∃ z : Z, ⌜v = #z⌝ }}})%I as "wp_ev". 1: admit.
              iApply "wp_ev" => // ; iIntros "!> % [%e1 ->]" ; iClear "wp_ev".
              iAssert (∀ K, ⤇ fill K (evalQ #i (inject db')) -∗ spec_update top (∃ z : Z, ⤇ fill K #z))%I as "tp_ev". 1: admit.
              iMod ("tp_ev" with "rnm'") as "[%e2 rnm']" => /= ; iClear "tp_ev".
              destruct (make_decision (i = j)) as [e|n].
              + tp_bind (Laplace _ _ _).
                wp_bind (Laplace _ _ _).
                (* the Laplace sampling should preserve the two assumptions that
           if (the value stored at maxA1) < (the value stored at cur1)
           then (the val stored at maxI1) = i
         and
           if (the value stored at maxA2) < (the value stored at cur2)
           then (the val stored at maxI1) = i
         i.e., preserve
  maxcur1 : (amax1 < vcur1)%Z → imax1 = i
  maxcur2 : (amax2 < vcur2)%Z → imax1 = i
         where vcur1 and vcur2 are updated to be `a`, the result of the sampling
                 *)
                iApply (wp_couple_laplace e1 e2 0%Z 1%Z with "[$rnm' ε]") => //.
                {
                  (* sensitivity of evalQ *)
                  admit.
                }
                { case_bool_decide. 2: lia.
                  (* would be fine if we had phrased the adjacency of db and db' as dDB db db' <= 1. *)
                  admit.
                }
                iNext ; iIntros (a) "rnm'" => /=.
                wp_pures. tp_pures. rewrite !Zplus_0_r.
                tp_store ; tp_pures ; wp_store.
                (* both samplings resolve to the same `a`, so the implications above become... *)
                assert (amax1 < a → imax1 = i)%Z as amax1_i.
                {
                  intros.
                }
                assert (amax2 < a → imax1 = i)%Z as amax2_i by admit.
                tp_load ; wp_load ; tp_pures ; wp_pures.
                case_bool_decide (amax1 < a)%Z as case_l ; tp_pures ; wp_pures.
                all: case_bool_decide as case_r ; tp_pures ; wp_pures.
                * do 2 (tp_store ; tp_pures ; wp_store ; wp_pures).
                  iMod ec_zero as "ε0".
                  iApply ("IH" $! j with "[-HΦ]") ; iFrame.
                  rewrite e. case_bool_decide ; try lia. iFrame.
                  iPureIntro. intuition lia.
                * iMod ec_zero as "ε0".
                  wp_store ; wp_pures ; wp_store ; wp_pures.
                  iSpecialize ("IH" $! j (i+1)%Z i imax2 a amax2 a a).
                  iSpecialize ("IH" with "[ε0 $rnm' $maxA1 $maxA2 $maxI1 $maxI2 $cur1 $cur2]").
                  2: iApply ("IH" with "[HΦ]") ; iFrame.
                  iSplitL. 1: case_bool_decide ; try lia ; iFrame "ε0".
                  iPureIntro ; split ; [|split ; [|split]].
                  1,2,4: intuition lia.

                  (* to show: the outputs are equal. we updated the left but not the right. *)

                  assert
                    (forall DB (adj : DB → DB → Prop) db1 db2 i1 i2 output1 output2 max1 max2 cur1 cur2 N k,
                        (((adj db1 db2 /\
                           i1 = i2 /\
                           output1 = output2 /\
                           (max1 < cur1 ->
                            output1 = i1) /\
                           (max2 < cur2 ->
                            output1 = i1) /\
                           i1 < N /\
                           k = N - i1 - 1 /\
                           N - i1 - 1 <= N /\
                           cur1 = cur2) /\
                          max1 < cur1) /\
                         (¬ (max2 < cur2))) ->
                        (let max_L := cur1 in
                         let output_L := i1 in
                         let i_R := i2 + 1 in
                         let i_L := i1 + 1 in
                         (adj db1 db2 /\
                          (i_L = i_R /\ output_L = output2) /\
                          (max_L < cur1 -> output_L = i_L) /\
                          (max2 < cur2 -> output_L = i_L)) /\
                         (i_L < N <-> i_R < N) /\ N - i_L - 1 < k)
                    )%Z.
                  {
                    clear.
                    intros.
                    destruct H as (((adj12 & i12 & out12 & outi1 & outi2 & i1N & kN & NN & cur12) & maxcur1) &  maxcur2).
                    repeat split.
                    1: assumption.
                    all: try (intros ; exfalso ; by lia).
                    1,3,4,5: try by lia.

                    symmetry.
                    (* the new left output is the current loop index i *)
                    unfold output_L.
                    (* the old right output is equal to the old left output *)
                    rewrite -out12.
                    (* that one in turn is equal to i if the current left max is below the current left sampled value *)
                    apply outi1.
                    (* and the left sampled value is indeed larger than the left max *)
                    exact maxcur1.
                  }

                  symmetry.
                  (* the old right output was equal to the old left *)
                  rewrite -imax12.
                  (* the old left is i if amax1 < a *)
                  (* this doesn't make sense? the old left doesn't care about the current a *)
                  apply amax1_i.
                  exact case_l.

                * iMod ec_zero as "ε0".
                  tp_store ; tp_pures ; tp_store ; tp_pures.
                  iApply ("IH" $! j with "[-HΦ]") ; [|by iFrame].
                  (* we need 0 credits for the IH since we just dealt with the case i=j, so i+1 <> j. *)
                  rewrite e ; case_bool_decide as Si_j ; try lia.
                  iFrame "rnm' ε0".

                  assert
                    (forall DB (adj : DB → DB → Prop) db1 db2 i1 i2 output1 output2 max1 max2 cur1 cur2 N k,
                        (((adj db1 db2 /\
                           i1 = i2 /\ output1 = output2 /\
                           (max1 < cur1 ->
                            output1 = i1) /\
                           (max2 < cur2 ->
                            output1 = i1) /\
                           i1 < N /\
                           k = N - i1 - 1 /\
                           N - i1 - 1 <= N /\ cur1 = cur2) /\
                          max1 < cur1) /\
                         ((max2 < cur2) -> False)) ->
                        (let i_R := i2 + 1 in
                         let i_L := i1 + 1 in
                         (output1 = output2 /\ adj db1 db2 /\
                          (i_L = i_R /\ i1 = output2) /\
                          (cur1 < cur1 -> i1 = i_L) /\
                          (max2 < cur2 -> i1 = i_L)) /\
                         (i_L < N <-> i_R < N) /\ N - i_L - 1 < k)
                    )%Z.
                  {
                    clear.
                    intros.
                    destruct H as (((adj12 & i12 & out12 & outi1 & outi2 & i1N & kN & NN & cur12) & maxcur1) &  maxcur2).
                    repeat split.
                    1: assumption.
                    all: try (intros ; exfalso ; by lia).
                    all: try by lia.
                    done.
                  }
                  clear H0.
                  iFrame. iPureIntro. repeat split. 1,2: intuition try lia.
                  subst. apply amax2_i. done.
                (*         intros Sj_N jj.
           subst.
   admit. *)

                * iMod ec_zero as "ε0".
                  iApply ("IH" $! j with "[-HΦ]") ; iFrame.
                  rewrite e. case_bool_decide ; try lia. iFrame.
                  iFrame. iPureIntro. repeat split. 1,2: intuition try lia.
                  (* intros.
           admit. *)
                  done.

              + tp_bind (Laplace _ _ _).
                wp_bind (Laplace _ _ _).
                iMod ec_zero as "ε0".
                iApply (wp_couple_laplace e1 e2 (e2 - e1)%Z 0%Z with "[$rnm' ε0]") => //.
                {
                  eapply Zabs_ind ; intuition lia.
                }
                1: rewrite Rmult_0_l => //.
                iNext ; iIntros (a) "rnm'" => /=.
                wp_pures. tp_pures. tp_store ; tp_pures ; wp_store.
                assert (amax1 < a → imax1 = i)%Z as amax1_i by admit.
                assert (amax2 < a + (e2 - e1) → imax1 = i)%Z as amax2_i by admit.

                tp_load ; wp_load ; tp_pures ; wp_pures.
                destruct_decide (@bool_decide_reflect (amax1 < a)%Z _) as case_l.
                all: destruct_decide (@bool_decide_reflect (amax2 < a + (e2 - e1))%Z _) as case_r.
                all: tp_pures ; wp_pures.

                * do 2 (tp_store ; tp_pures ; wp_store ; wp_pures).
                  iApply ("IH" $! j (i+1)%Z i with "[-HΦ]") ; iFrame.
                  repeat case_bool_decide ; try lia ; iFrame.
                  all: iPureIntro ; intuition lia.
                * wp_store ; wp_pures ; wp_store ; wp_pures.
                  iApply ("IH" $! j (i+1)%Z with "[-HΦ]") ; iFrame.
                  iSplitL. 1: repeat case_bool_decide ; try lia ; iFrame.
                  all: iPureIntro ; intuition try lia.
                * tp_store ; tp_pures ; tp_store ; tp_pures.
                  iApply ("IH" $! j (i+1)%Z with "[-HΦ]") ; iFrame.
                  iSplitL. 1: repeat case_bool_decide ; try lia ; iFrame.
                  all: iPureIntro ; intuition lia.
                (* 1,2: admit. *)
                * iApply ("IH" $! j (i+1)%Z with "[-HΦ]") ; iFrame.
                  repeat case_bool_decide ; try lia ; iFrame.
                  all: iPureIntro ; intuition lia.

          Admitted.

          Lemma rnm_diffpriv_3 num den :
            (0 < IZR num / IZR den) →
            ∀ (K : list (ectxi_language.ectx_item prob_ectxi_lang)),
              {{{ ⤇ fill K (report_noisy_max num den evalQ #2 (inject db')) ∗
                  ↯ (IZR num / IZR den)
                    (* ↯ 0 *)
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
            tp_pures. 1: cbv ; auto.
            rewrite {2 4}/evalQ. tp_pures. 1: cbv ; auto. wp_pures.
            rewrite /count_under_40/setsum/setmap/under_40/age. wp_pures. tp_pures.


            wp_bind (Laplace _ _ _). tp_bind (Laplace _ _ _).
            iMod ec_zero as "ε0".
            unshelve iApply (wp_couple_laplace 1 2 1 0 _ (num) (2*den) _ _  (AppRCtx _ :: K)
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
            wp_load. tp_pures. tp_load. tp_pures. 1: cbv ; auto. wp_pures.
            tp_store. tp_pures. tp_store. do 2 wp_store. wp_pures. tp_pures. 1: cbv ; auto.
            rewrite {2 4}/evalQ. tp_pures. 1,2: cbv ; auto. wp_pures.
            rewrite /count_over_80/setsum/setmap/over_80/age. wp_pures. tp_pures.
            wp_bind (Laplace _ _ _). tp_bind (Laplace _ _ _).
            iMod ec_zero as "ε0".
            unshelve iApply (wp_couple_laplace _ _ 0 0 _ (num) (2*den) _ _  (AppRCtx _ :: K)
                with "[ε ε0 $f']" ) => //=.
            1: by cbv.
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
            tp_pures. tp_load. tp_pures ; [cbv ; auto|].
            rewrite !Zplus_0_r ?Zplus_0_l.
            case_bool_decide.
            - do 2 wp_store. wp_pures.
              tp_pures. tp_store ; tp_pures ; tp_store ; tp_pures.
              1: cbv ; auto. tp_load.
              wp_load.
              iApply "hφ". done.
              Unshelve.
              2: f_equal. simpl.
            - wp_pures.
              tp_pures.
              1: cbv ; auto. tp_load.
              wp_load.
              iApply "hφ". done.
              Unshelve.
              all: f_equal.
          Qed.

End rnm.

From clutch.common Require Import inject.
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
           (let: "a" := Laplace #num #(2 * den) ("evalQ" "i" "d") in
           (if: (! "maxI" = #(-1)) `or` (! "maxA" < "a") then
             "maxA" <- "a" ;;
             "maxI" <- "i"
           else #()) ;;
           "rnm" ("i" + #1)))
      in "f" #0.

  Definition rnm_body (num den : Z) (evalQ : val) {DB} (dDB : Distance DB) (N : nat) (db : DB) (maxI maxA : loc) :=
    (rec: "rnm" "i" :=
        if: "i" = #N then ! #maxI
        else let: "a" := Laplace #num #(2 * den) (evalQ "i" (inject db)) in
             (if: ! #maxI = #0 `or` ! #maxA < "a"
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

  Lemma rnm_diffpriv num den (evalQ : val) DB (dDB : Distance DB) (N : nat) :
    (0 < IZR num / IZR den) →
    (∀ i : Z, wp_sensitive (evalQ #i) 1 dDB dZ) →
    wp_diffpriv (report_noisy_max num den evalQ #N) (IZR num / IZR den) dDB.
  Proof with (tp_pures ; wp_pures).
    intros εpos qi_sens.
    iIntros (? c db db' db_adj Φ) "(rnm & ε) HΦ".
    rewrite /report_noisy_max.
    tp_pures.
    tp_alloc as maxI2 "maxI2". tp_pures. tp_alloc as maxA2 "maxA2". do 5 tp_pure.
    wp_pures. wp_alloc maxI1 as "maxI1". wp_alloc maxA1 as "maxA1". do 5 wp_pure.
    rewrite -/(rnm_body num den evalQ dDB N db maxI1 maxA1).
    rewrite -/(rnm_body num den evalQ dDB N db' maxI2 maxA2).

    (* Todo generalize over the current iteration index (initially/now: 0) and come up with a better invariant / induction hypothesis. *)
    iAssert (∃ i : Z, maxI1 ↦ #i ∗ maxI2 ↦ₛ #i ∗ ⌜ 0 <= i <= N ⌝%Z)%I with "[$maxI1 $maxI2]" as "maxI". 1: iPureIntro ; lia.
    iAssert (∃ a : Z, maxA1 ↦ #a ∗ maxA2 ↦ₛ #a)%I with "[$maxA1 $maxA2]" as "maxA".
    iRevert "maxA maxI".
    iLöb as "IH".
    iIntros "(% & maxA1 & maxA2) (% & maxI1 & maxI2 & %i_N)".
    rewrite /rnm_body. tp_pures. 1: cbv ; auto. wp_pures. case_bool_decide ; tp_pures ; wp_pures.
    - tp_load. wp_load. iApply "HΦ" => //.
    - give_up.
  Admitted.

End rnm.

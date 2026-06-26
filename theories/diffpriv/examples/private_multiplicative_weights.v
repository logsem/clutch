From iris.base_logic Require Export na_invariants.
From clutch.common Require Import inject.
From clutch.prelude Require Import tactics.
From clutch.prob Require Import differential_privacy.
From clutch.diffpriv Require Import adequacy diffpriv proofmode.
From clutch.diffpriv.examples Require Import list numeric_sparse_vector_technique.

Section pmw.
  Context `{!diffprivGS Σ}.

  #[local] Open Scope R.

  (* The following comment is not updated and then should be ignored.
     In this part, we consider that x is a distribution and is stored in an couple of arrays.
     Each element is of the form: (Edb, Pdb) (we will call it DB)
     where Edp is the array of the databases and Pdb is the array of the probability of each db.
     We assume that queries are of the type DB -> R, and works as the following:
        - Samples an index following the Pdb distribution
        - Executes the query on this db
  *)


  (* For the proof we need to adapt the algo from the book. *)
  (* Indeed, in order to get result on the call to `f`, *)
  (* the numeric sparse vector technique, we need to call *)
  (* it again for e2 only when we know that e1 is None. *)
  (* Otherwise, we can not state no result on e2 since if *)
  (* e1 returned a value then we would not have inSVT (S x). *)
  (* Knowing that even if e1 and e2 are values, then we will *)
  (* not use e2. Hence we call it only when necessary. *)

  (* We are giving to the oPMW technique a lot of functions in *)
  (* parameters. We also make a lot of assumptions about those *)
  (* functions in the specification. *)
  (* That is why this is only a partial implementation of the *)
  (* private multiplicative weight technique. *)

  
  Definition oPMW : val :=
    λ: "x" "stream_q" "num" "den" "c" "t" "unif" "upd" "f1" "f2",
      let: "f" := (onSVT "num" "den" "t" "c") in
      (rec: "aux" "i" "bs" "distrib" :=
         match: "stream_q" "bs" with
         | NONE => "bs"  (* No more queries *)
         | SOME "q" =>
             if: "i" = "c" then (* We have to query the distribution *)
               "aux" "i" (list_cons ("q" "distrib") "bs") "distrib"
             else (
               match: "f" "x" ("f1" "q" "distrib") with
               | NONE =>
                   match: "f" "x" ("f2" "q" "distrib") with
                   | NONE => "aux" "i" (list_cons ("q" "distrib") "bs") "distrib"
                   (* The answer is under the threshold *)
                   | SOME "v" => "aux" ("i" + #1) (list_cons "v" "bs") ("upd" "distrib" "q" ("q" "distrib" + "v"))
                   end
               | SOME "v" => "aux" ("i" + #1) (list_cons "v" "bs") ("upd" "distrib" "q" ("q" "distrib" - "v"))
               end)
         end) #0 list_nil "unif".


  #[local] Definition pMW_body (c : nat) (stream_q : val) {DB} {_ : Inject DB val} (db : DB) (f : val) (upd f1 f2: val) :=
       (rec: "aux" "i" "bs" "distrib" :=
        match: stream_q "bs" with
          InjL <> => "bs"
        | InjR "q" =>
          if: "i" = #c then "aux" "i" (list_cons ("q" "distrib") "bs") "distrib"
          else match: f (inject db) (f1 "q" "distrib") with
                 InjL <> =>
                   match: f (inject db) (f2 "q" "distrib") with
                     InjL <> =>
                       "aux" "i" (list_cons ("q" "distrib") "bs") "distrib"
                   | InjR "v" =>
                     "aux" ("i" + #1) (list_cons "v" "bs")
                       (upd "distrib" "q" ("q" "distrib" + "v"))
                   end
               | InjR "v" =>
                 "aux" ("i" + #1) (list_cons "v" "bs")
                   (upd "distrib" "q" ("q" "distrib" - "v"))
               end
        end)%V.

  Lemma pMW_diffpriv (num den : Z) (c t : nat) (stream_q : val) `(dDB : Distance DB) (upd f1 f2: val) (unif : DB) :
    let ε := IZR num / IZR den in
    ∀ (εpos : 0 < ε) (cpos : (0 < c)%nat) (tpos : (0 < t)%nat),
      □ (∀ K (bs : val),
          ⤇ fill K (stream_q bs) -∗
          WP stream_q bs
          {{ qopt, ⤇ fill K (Val qopt) ∗
                     (⌜qopt = NONEV⌝ ∨ ∃ q : val, ⌜qopt = SOMEV q⌝ ∗ □ wp_sensitive q 1 dDB dZ ∗
                        □ (∀ K db, ⤇ fill K (q db) -∗ WP q db {{v, ∃ r : Z, ⌜v = inject r⌝ ∗ ⤇ fill K (Val v) }}) ) }}) -∗
       □ (∀ K (distrib : DB) (q v : val),
          ⤇ fill K (upd (Val (inject distrib)) q v) -∗
          WP upd (Val (inject distrib)) q v
          {{ v, ⤇ fill K (Val v) ∗ ∃ distrib' : DB, ⌜v = (inject distrib')⌝}}) -∗
      □ (∀ K (distrib q : val), (* we get back a 1sens query *)
          (* (wp_sensitive q 1 dDB dZ) -∗ we need the original query to be 1 sensitive *)
          ⤇ fill K (f1 q distrib) -∗
          WP f1 q distrib
          {{ v, ⤇ fill K (Val v) ∗ □ wp_sensitive v 1 dDB dZ }}) -∗
      □ (∀ K (distrib q : val),
          (* (wp_sensitive q 1 dDB dZ) -∗ *)
          ⤇ fill K (f2 q distrib) -∗
          WP f2 q distrib
          {{ v, ⤇ fill K (Val v) ∗ □ wp_sensitive v 1 dDB dZ }}) -∗
      ∀ (db db' : DB) (adj : dDB db db' <= 1) K,
      ↯m (c * ε) -∗
      ⤇ fill K (oPMW (Val (inject db')) stream_q #num #den #c #t (Val (inject unif)) upd f1 f2) -∗
      WP oPMW (Val (inject db)) stream_q #num #den #c #t (Val (inject unif)) upd f1 f2
      {{ v, ⤇ fill K (Val v) }}.
  Proof with (tp_pures; wp_pures).
    iIntros (ε εpos cpos tpos) "#sens #Hup #Hf1 #Hf2 % % % % ε rhs".
    rewrite /oPMW...
    tp_bind (onSVT _ _ _ _); wp_bind (onSVT _ _ _ _).
    iPoseProof (nSVT_online_diffpriv with "ε rhs") as "spec" => //.
    iApply (wp_strong_mono'' with "spec").
    iIntros "%f (%f' & % & rhs & inSVT & spec) /=".
    do 4 tp_pure; do 4 wp_pure.
    rewrite -!/(pMW_body _ _ _ _ _ _ _).
    set (distrib := inject unif).
    set (bs := InjLV #()). rewrite {1}/bs.
    set (i := 0%Z). set (c' := c). rewrite {1 3}/c'.
    assert (0 <= i)%Z as ipos by lia. assert (c' + i = c)%Z as hi by lia.
    generalize i c' bs hi ipos distrib. clear i c' bs hi ipos distrib.
    intros.
    iRevert (i c' bs hi ipos distrib) "rhs inSVT spec".
    iLöb as "IH".
    iIntros (i c' bs hi ipos distrib) "rhs inSVT #spec".
    rewrite {3 4}/pMW_body...

    wp_bind (stream_q _); tp_bind (stream_q _).
    iPoseProof ("sens" $! _  with "rhs") as "sens_bs".
    iApply (wp_strong_mono'' with "sens_bs").
    iIntros "%qopt (rhs & [->|(%q & -> & #sens_q & #Hdet)]) /="... 1: done.
    case_bool_decide...
    - (* Case where we have already proceed all the allowed updates *)
      do 2 rewrite -/(pMW_body _ _ _ _ _ _ _).
      (* Need to get that `q distrib` is a value. *)
      (* Then we will be able to call IH. *)
      wp_bind (q _); tp_bind (q _).
      iPoseProof ("Hdet" $! _ distrib with "rhs") as "Hdet'".
      iApply (wp_strong_mono'' with "Hdet'").
      iIntros (v) "(%r & -> & rhs)"...
      simpl.
      rewrite /list_cons...
      iApply ("IH" with "[] [] rhs inSVT"). 3: done. 1,2: iPureIntro. 1,2: lia.
    - do 2 rewrite -/(pMW_body _ _ _ _ _ _ _).
      wp_bind (f _ _); tp_bind (f' _ _).
      wp_bind (f1 _ _); tp_bind (f1 _ _).
      iPoseProof ("Hf1" $! _ with "rhs") as "Hf1'".
      iApply (wp_strong_mono'' with "Hf1'").
      iIntros (q1) "[rhs #sens_q1]".
      tp_bind (f' _ _).
      iCombine "spec" as "spec_i".
      iEval (rewrite /nSVT_spec) in "spec_i".
      assert (not (i = c)). 1: intros h ; subst ; auto.
      assert (∃ c'', c' = S c'') as [? ->]. { destruct c'. 1: lia. eauto. }
      iSpecialize ("spec_i" $! _ _ db db' adj with "sens_q1 rhs inSVT") => //.
      iApply (wp_strong_mono'' with "spec_i").
      iIntros "% (rhs & %e1 & -> & inSVT) /="...
      destruct e1...
      + (* e1 is a value (not none) *)
        wp_bind (q _); tp_bind (q _).
        iPoseProof ("Hdet" $! _ distrib with "rhs") as "Hdet'".
        iApply (wp_strong_mono'' with "Hdet'").
        iIntros (v) "(%r & -> & rhs)"...
        simpl.
        tp_binop.
        wp_bind (upd _ _ _); tp_bind (upd _ _ _).
        iPoseProof ("Hup" $! K _ q #(r - z)) as "Hup'".
        (* Issue, we don't know that distrib = inject db  #1# *)
        admit.
      + (* e1 is none but we have inSVT (S x) *)
        iSimpl in "inSVT"...
        wp_bind (f _ _); tp_bind (f' _ _).
        wp_bind (f2 _ _); tp_bind (f2 _ _).
        iPoseProof ("Hf2" $! _ with "rhs") as "Hf2'".
        iApply (wp_strong_mono'' with "Hf2'").
        iIntros (q2) "[rhs #sens_q2]".
        tp_bind (f' _ _).
        iCombine "spec" as "spec_i".
        iEval (rewrite /nSVT_spec) in "spec_i".
        iSpecialize ("spec_i" $! _ _ db db' adj with "sens_q2 rhs inSVT") => //.
        iApply (wp_strong_mono'' with "spec_i").
        iIntros "% (rhs & %e2 & -> & inSVT) /=".
        destruct e2...
        -- (* e2 is a value (not none) *)
          wp_bind (q _); tp_bind (q _).
          iPoseProof ("Hdet" $! _ distrib with "rhs") as "Hdet'".
          iApply (wp_strong_mono'' with "Hdet'").
          iIntros (v) "(%r & -> & rhs)"...
          simpl.
          tp_binop.
          wp_bind (upd _ _ _); tp_bind (upd _ _ _).
          iPoseProof ("Hup" $! K _ q #(r - z)) as "Hup'".
          (* Issue, we don't know that distrib = inject db same as #1# *)
          admit.
        -- (* both answers are under the threshold *)
          wp_bind (q _); tp_bind (q _).
          iPoseProof ("Hdet" $! _ distrib with "rhs") as "Hdet'".
          iApply (wp_strong_mono'' with "Hdet'").
          iIntros (v) "(%r & -> & rhs)"...
          simpl.
          rewrite /list_cons...
          iApply ("IH" with "[] [] rhs inSVT"). 3: done. 1,2: iPureIntro. 1,2: lia.
Admitted.

  (* There is two of `admit.` in this parial proof. *)
  (* However each of them should have the same proof. *)
  (* We need to show that the call to `upd _ distrib _` *)
  (* works well. In other words we want to show that  *)
  (* there exists a db such that distrib = inject db *)
  (* (it is maybe one solution) *)

End pmw.

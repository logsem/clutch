From iris.base_logic Require Export na_invariants.
From clutch.common Require Import inject.
From clutch.prelude Require Import tactics.
From clutch.prob Require Import differential_privacy.
From clutch.diffpriv Require Import adequacy diffpriv proofmode.
From clutch.diffpriv.examples Require Import list numeric_sparse_vector_technique.

Section pmw.
  Context `{!diffprivGS Σ}.

  #[local] Open Scope R.

(* In this part, we consider that x is a distribution and is stored in an couple of arrays.
     Each element is of the form: (Edb, Pdb) (we will call it DB)
     where Edp is the array of the databases and Pdb is the array of the probability of each db.
     We assume that queries are of the type DB -> R, and works as the following:
        - Samples an index following the Pdb distribution
        - Executes the query on this db
  *)

(*
  Definition MW : val :=
    λ:"x" "f" "v",
      let: "r" := (if: ("v" >= "f" "x") then (λ:"q", #1 - "f" "q") else "f") in
      (* Need the update *)
      "x".
 *)
(*
  Definition oPMW : val :=
    (*
    λ: "x" "nDB" "card_Sdb" "log" "exp" "stream_q" "num" "den" "α" "β" "cmpC" "cmpT" "unif" "upd",
      let: "cNum" := (#4 * ("log" "card_Sdb")) in
      let: "cDen" := ("α" * "α") in
      let: "tNum" := ("den" * #18 * ("c" * ("log" (#2 * "card_Sq") + "log" (#4 * "c") - "log" "β"))) in
      let: "tDen" := ("num" * ("nDB" "x")) in *)
    λ: "x" "stream_q" "num" "den" "cmpC" "cmpT" "unif" "upd",
      let: "c" := "cmpC" "num" "den" in
      let: "t" := "cmpT" "num" "den" in
      let: "f" := (onSVT "num" "den" "t" "c") "x" in
      let: "distrib" := ref "unif" in
      (rec: "nSVT" "i" "bs" :=
         match: "stream_q" "bs" with
         | NONE => "bs"  (* No more queries *)
         | SOME "q" =>
             if: "i" = "c" then (* We have to query the distribution *)
               "nSVT" "i" (list_cons ("q" "distrib") "bs")
             else (
               let: "e1" := "f" (λ: "x'", "q" "x'" - "q" "distrib") in
               let: "e2" := "f" (λ: "x'", "q" "distrib" - "q" "x'") in
               let: "a" := ref NONE in
               match: "e1" with
               | NONE =>
                   match: "e2" with
                   | NONE => #() (* The answer is under the threshold *)
                   | SOME "v" => "a" <- SOME ("q" "distrib" + "v")
                   end
               | SOME "v" => "a" <- SOME ("q" "distrib" - "v")
               end;;
               match: "a" with
               | NONE => "nSVT" "i" (list_cons ("q" "distrib") "bs")
               | SOME "v" => "distrib" <- "upd" "distrib" "q" "v";; "nSVT" ("i" + #1) (list_cons "v" "bs")
               end)
         end) #0 list_nil.

 Lemma pMW_diffpriv (num den : Z) (stream_q : val) `(dDB : Distance DB) (cmpC cmpT upd : val) (unif : DB) :
    let ε := IZR num / IZR den in
    ∀ (εpos : 0 < ε),
      □ (∀ K (bs : val),
          ⤇ fill K (stream_q bs) -∗
          WP stream_q bs
          {{ qopt, ⤇ fill K (Val qopt) ∗
                     (⌜qopt = NONEV⌝ ∨ ∃ q : val, ⌜qopt = SOMEV q⌝ ∗ □ wp_sensitive q 1 dDB dZ) }}) -∗
      □ (∀ K (v1 v2 : val),
          ⤇ fill K (cmpC v1 v2) -∗
          WP cmpC v1 v2
          {{ v, ⤇ fill K (Val v) ∗ ∃ n : Z, ⌜v = inject n⌝}}) -∗
      □ (∀ K (v1 v2 : val),
          ⤇ fill K (cmpT v1 v2) -∗
          WP cmpT v1 v2
          {{ v, ⤇ fill K (Val v) ∗ ∃ n : Z, ⌜v = inject n⌝}}) -∗
      □ (∀ K (distrib : DB) (q v : val),
          ⤇ fill K (upd (Val (inject distrib)) q v) -∗
          WP upd (Val (inject distrib)) q v
          {{ v, ⤇ fill K (Val v) ∗ ∃ distrib' : DB, ⌜v = (inject distrib')⌝}}) -∗
      ∀ (db db' : DB) (adj : dDB db db' <= 1) K,
      ↯m ε -∗
      ⤇ fill K (oPMW (Val (inject db')) stream_q #num #den cmpC cmpT (Val (inject unif)) upd) -∗
      WP oPMW (Val (inject db)) stream_q #num #den cmpC cmpT (Val (inject unif)) upd
      {{ v, ⤇ fill K (Val v) }}.



  *)
  Definition oPMW : val :=
    λ: "x" "stream_q" "num" "den" "c" "t" "unif" "upd",
      let: "f" := (onSVT "num" "den" "t" "c") in
      let: "distrib" := ref "unif" in
      (rec: "nSVT" "i" "bs" :=
         match: "stream_q" "bs" with
         | NONE => "bs"  (* No more queries *)
         | SOME "q" =>
             if: "i" = "c" then (* We have to query the distribution *)
               "nSVT" "i" (list_cons ("q" (!"distrib")) "bs")
             else (
               let: "e1" := "f" "x" (λ: "x'", "q" "x'" - "q" (!"distrib")) in
               let: "e2" := "f" "x" (λ: "x'", "q" (!"distrib") - "q" "x'") in
               let: "a" := ref NONE in
               match: "e1" with
               | NONE =>
                   match: "e2" with
                   | NONE => #() (* The answer is under the threshold *)
                   | SOME "v" => "a" <- SOME ("q" (!"distrib") + "v")
                   end
               | SOME "v" => "a" <- SOME ("q" (!"distrib") - "v")
               end;;
               match: "a" with
               | NONE => "nSVT" "i" (list_cons ("q" (!"distrib")) "bs")
               | SOME "v" => "distrib" <- "upd" (!"distrib") "q" "v";; "nSVT" ("i" + #1) (list_cons "v" "bs")
               end)
         end) #0 list_nil.

    #[local] Definition pMW_body (c : nat) (l : loc) (stream_q : val) {DB} {_ : Inject DB val} (db : DB) (f : val) (upd : val) :=
      (rec: "nSVT" "i" "bs" :=
        match: stream_q "bs" with
          InjL <> => "bs"
        | InjR "q" =>
          if: "i" = #c then "nSVT" "i" (list_cons ("q" (!#l)) "bs")
          else let: "e1" := f (inject db) (λ: "x'", "q" "x'" - "q" (!#l)) in
               let: "e2" := f (inject db) (λ: "x'", "q" (!#l) - "q" "x'") in
               let: "a" := ref (InjL #()) in
               match: "e1" with
                 InjL <> => match: "e2" with InjL <> => #() | InjR "v" => "a" <- InjR ("q" (!#l) + "v") end
               | InjR "v" => "a" <- InjR ("q" (!#l) - "v")
               end;;
               match: "a" with
                 InjL <> => "nSVT" "i" (list_cons ("q" (!#l)) "bs")
               | InjR "v" => #l <- upd (!#l) "q" "v";; "nSVT" ("i" + #1) (list_cons "v" "bs")
               end
        end)%V.

  Lemma pMW_diffpriv (num den : Z) (c t : nat) (stream_q : val) `(dDB : Distance DB) (upd : val) (unif : DB) :
    let ε := IZR num / IZR den in
    ∀ (εpos : 0 < ε) (cpos : (0 < c)%nat) (tpos : (0 < t)%nat),
      □ (∀ K (bs : val),
          ⤇ fill K (stream_q bs) -∗
          WP stream_q bs
          {{ qopt, ⤇ fill K (Val qopt) ∗
                     (⌜qopt = NONEV⌝ ∨ ∃ q : val, ⌜qopt = SOMEV q⌝ ∗ □ wp_sensitive q 1 dDB dZ) }}) -∗
      □ (∀ K (distrib : DB) (q v : val),
          ⤇ fill K (upd (Val (inject distrib)) q v) -∗
          WP upd (Val (inject distrib)) q v
          {{ v, ⤇ fill K (Val v) ∗ ∃ distrib' : DB, ⌜v = (inject distrib')⌝}}) -∗
      ∀ (db db' : DB) (adj : dDB db db' <= 1) K,
      ↯m (c * ε) -∗
      ⤇ fill K (oPMW (Val (inject db')) stream_q #num #den #c #t (Val (inject unif)) upd) -∗
      WP oPMW (Val (inject db)) stream_q #num #den #c #t (Val (inject unif)) upd
      {{ v, ⤇ fill K (Val v) }}.
  Proof with (tp_pures; wp_pures).
    iIntros (ε εpos cpos tpos) "#sens #Hup % % % % ε rhs".
    rewrite /oPMW...
    tp_bind (onSVT _ _ _ _); wp_bind (onSVT _ _ _ _).
    iPoseProof (nSVT_online_diffpriv with "ε rhs") as "spec" => //.
    iApply (wp_strong_mono'' with "spec").
    iIntros "%f (%f' & % & rhs & inSVT & spec) /="...
    wp_alloc lw as "lw"; tp_alloc as lt "lt".
    do 4 wp_pure; do 4 tp_pure.

    rewrite -!/(pMW_body _ _ _ _ _ _).
    set (i := 0%Z). set (c' := c). rewrite {1 3}/c'.
    assert (0 <= i)%Z as ipos by lia. assert (c' + i = c)%Z as hi by lia.
    set (bs := InjLV #()). rewrite {1}/bs. generalize i c' bs hi ipos. clear i c' hi ipos bs.
    intros. iRevert (i c' bs hi ipos) "rhs inSVT spec". iLöb as "IH". iIntros (i c' bs hi ipos) "rhs inSVT #spec".
    rewrite {3 4}/pMW_body...
    tp_bind (stream_q _); wp_bind (stream_q _)...
    iPoseProof ("sens" $! _ bs with "rhs") as "sens_bs".
    iApply (wp_strong_mono'' with "sens_bs").
    iIntros "%qopt (rhs & [->|(%q & -> & #sens_q)]) /="... 1: done.
    case_bool_decide as Hcbd; rewrite -!/(pMW_body _ _ _ _ _ _)...
    - (* We have already updated c times *)
      wp_load; tp_load. (* We get back the values of the refs content with lw and lt *)
      rewrite /list_cons...
      set (bs' := ((λ: "elem" "list", InjR ("elem", "list"))%V (q (inject unif)) bs) : val).
      iDestruct ("IH" with "lw lt") as "IH'".
      wp_bind (q _); tp_bind (q _).
      (*iApply ("IH'" $! i 0%nat bs').*)
      admit.
    - (* We are allowed to do another update *)
      wp_bind (f _ _); tp_bind (f' _ _).
      set (q1 := f (inject db) (λ: "x'", q "x'" - q ! #lw)%V).
      subst q1.
      (* Issue with the call to the stream ??*)


      iApply ("IH'" $! i 0%nat (inject (list_cons (q (inject unif)) bs))).




      iCombine "spec" as "spec_i".
      iEval (rewrite /nSVT_spec) in "spec_i".
      iSpecialize ("spec_i" $! _ _ db db' adj with "sens_q rhs inSVT") => //.

      iApply ("IH" with "lw lt c' ").
    iApply ("IH" with "[] [] rhs inSVT").
    iIntros "%qopt (rhs & [->|(%q & -> & #sens_q]) /="...
    tp_let.
    rewrite -!/(pMW_body _ _ _ _ _).


    replace ε with (IZR c * (IZR num / (IZR (c * den)) )).
    2: {
      rewrite mult_IZR.
      rewrite Rmult_div_assoc Rdiv_mult_distr.
      rewrite Rmult_comm -Rmult_div_assoc.
      subst ε.
      replace (IZR c / IZR c) with 1.
      1: rewrite Rmult_1_r; reflexivity.
      rewrite Rdiv_diag; first reflexivity.
      apply not_0_IZR; lia.
    }
    iPoseProof (nSVT_online_diffpriv num (c%Z * den) t c cpos K) as "spec".
    { Search "IZR". rewrite mult_IZR. rewrite Rmult_comm Rdiv_mult_distr.
      subst ε. Search "R" "div". apply Rdiv_lt_0_compat => //.
      Search "INR". admit. (*apply lt_INR.*) }
    iApply (wp_strong_mono'' with "ε"). with "spec"*).

End pmw.

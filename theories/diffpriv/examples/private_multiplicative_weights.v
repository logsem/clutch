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
               "nSVT" "i" (list_cons ("q" "distrib") "bs")
             else (
               let: "e1" := "f" "x" (λ: "x'", "q" "x'" - "q" "distrib") in
               let: "e2" := "f" "x" (λ: "x'", "q" "distrib" - "q" "x'") in
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
      ↯m ε -∗
      ⤇ fill K (oPMW (Val (inject db')) stream_q #num #den #c #t (Val (inject unif)) upd) -∗
      WP oPMW (Val (inject db)) stream_q #num #den #c #t (Val (inject unif)) upd
      {{ v, ⤇ fill K (Val v) }}.
  Proof with (tp_pures; wp_pures).
    iIntros (ε εpos cpos tpos) "#sens #Hup % % % % ε rhs".
    rewrite /oPMW...
    tp_bind (onSVT _ _ _ _); wp_bind (onSVT _ _ _ _).
    replace ε with (IZR c * (IZR num / (IZR (c * den)) )).
    2: {
      rewrite mult_IZR.
      rewrite Rmult_div_assoc Rdiv_mult_distr.
      rewrite Rmult_comm.
      rewrite -Rmult_div_assoc.
      subst ε.
      replace (IZR c / IZR c) with 1.
      Search "R" "mul" "div".
      1: rewrite Rmult_1_r; reflexivity.
      Search "R" "div".
      rewrite Rdiv_diag; first reflexivity.
      Search "IZR" "0".
      apply not_0_IZR; lia.
    }
    iPoseProof (nSVT_online_diffpriv with "ε") as "spec". ; first apply cpos.
    1: subst ε; apply εpos.
    iApply wp_strong_mono''. with "ε"). with "spec").

End pmw.

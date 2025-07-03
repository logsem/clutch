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


  (* We can give the following specs: *)
  (* { ↯ ε } A_T T ~ AT T
     { f f' . AUTH
            ∗ ∀ db db' : adjacent, ∀ q : 1-sensitive,
[equality post:]
              { AUTH } f db q ~ f' db' q { b : bool . b = false -∗ AUTH }
[or pointwise eq:]
              ∀ R , { AUTH } f db qi ~ f db' qi { b b' : bool . ⌜b = R -> b' = R⌝ ∗ (⌜R = false⌝ -∗ AUTH) }
     }  *)

  (* If we add a flag to track whether an above-threshold query has been found, we can remain
  private (and return AUTH) even after finding such a query by returning None. Probably not very
  useful in practice. *)
  Definition above_threshold_reset : val :=
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

  (* We don't actually need `reset` since it is always set to `false` so long as a client holds AUTH. *)
  Definition above_threshold : val :=
    λ:"num" "den" "T",
      let: "T'" := Laplace "num" (#2*"den") "T" in
      λ:"db" "qi",
        let: "vi" := Laplace "num" (#4*"den") ("qi" "db") in
        "T'" ≤ "vi".

  (* The spec that AT satisfies after initialising T'. *)
  Definition AT_spec (AUTH : iProp Σ) (f f' : val) : iProp Σ :=
    □ ∀ `(dDB : Distance DB) (db db' : DB)
      (_ : dDB db db' <= 1) (q : val) (K0 : list ectx_item),
      wp_sensitive q 1 dDB dZ -∗
      AUTH -∗
      ⤇ fill K0 (f' (inject db') q) -∗
      WP f (inject db) q
        {{ v, ∃ (b : bool), ⌜v = #b⌝ ∗ ⤇ fill K0 #b ∗
                            (⌜b = false⌝ -∗ AUTH) }}.

  (* SVT calibrates the noise by simply dividing up the initial budget ε =
  num/den over the number of queries c exceeding the threshold T and running
  each "above_threshold" query with privacy budget ε/c. *)
  (* SVT : ℚ → ℤ → ℕ → DB → (DB → Z) → option 𝔹 *)
  (* This definition is unused; instead we construct SVT as a client of AT. *)
  Definition SVT_online_AT_inlined (num den : Z) : val :=
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

  (* SVT expressed in terms of Above Threshold, for modular analysis.

     The reference "AT" stores an initialised above_threshold at all times. We need to keep track
     of the number of `true` results we returned in the reference "count" because we can only
     perform N initialisations of AT. *)
  (* NB: This is different from bounded oracles ("q_calls" in Approxis) because we only count calls
     to above_threshold that return a #true result: we invoke the closure not only N many times,
     but until we a `true` result N times. *)

  Definition oSVT : val :=
    λ:"num" "den" "T" "N",
      let: "count" := ref ("N" - #1) in
      let: "AT" := ref (above_threshold "num" "den" "T") in
      λ:"db" "qi",
        let: "bq" := !"AT" "db" "qi" in
        (if: #0 < !"count" `and` "bq" then
           ("AT" <- (above_threshold "num" "den" "T") ;;
            "count" <- !"count" - #1)
         else #()) ;;
        "bq".


  (* We prove the (non-pw) spec for oAT from hoare_couple_laplace_choice. *)
  Lemma above_threshold_online_AT_spec (num den T : Z) (εpos : 0 < IZR num / IZR den) K :
    ↯m (IZR num / IZR den) -∗
    ⤇ fill K ((Val above_threshold) #num #den #T)
    -∗ WP (Val above_threshold) #num #den #T
         {{ f, ∃ (f' : val) (AUTH : iProp Σ),
               ⤇ fill K (Val f') ∗ AUTH ∗ AT_spec AUTH f f' }}.
  Proof with (tp_pures ; wp_pures).
    iIntros "ε rhs". rewrite /above_threshold...
    tp_bind (Laplace _ _ _). wp_bind (Laplace _ _ _).
    set (ε := (IZR num / IZR den)). replace ε with (ε / 2 + ε / 2) by real_solver.
    fold ε in εpos.
    iDestruct (ecm_split with "ε") as "[ε ε']". 1,2: real_solver.
    iApply (hoare_couple_laplace _ _ 1%Z 1%Z with "[$rhs ε']") => //.
    1: apply Zabs_ind ; lia.
    1: rewrite mult_IZR ; apply Rdiv_pos_pos. 1,2: real_solver.
    { iApply ecm_eq. 2: iFrame. subst ε. replace (IZR (2 * den)) with (2 * IZR den).
      2: qify_r ; zify_q ; lia.
      field. eapply Rdiv_pos_den_0 => //. }
    iIntros (T') "!> rhs" => /=...
    iModIntro. iExists _. iFrame "rhs".
    iExists (↯m (ε / 2))%I. iFrame "ε". clear K.
    iModIntro. iIntros (?????) "%q %K q_sens ε rhs"...
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
    iApply (hoare_couple_laplace_choice vq_l (vq_r) T' with "[$]") => //.
    1: apply Zabs_ind ; lia.
    1: rewrite mult_IZR ; apply Rdiv_pos_pos. 1,2: real_solver.
    { subst ε. rewrite mult_IZR. field. eapply Rdiv_pos_den_0 => //. }
    iIntros "%z !> (%z' & rhs & hh)".
    iDestruct "hh" as "[%h_above | [%h_below ε]]".
    - simpl... case_bool_decide.
      + iFrame. iModIntro. case_bool_decide. 2: lia. iSplit => //. by iIntros (?).
      + lia.
    - simpl... destruct h_below. case_bool_decide.
      + lia.
      + iModIntro. iFrame. case_bool_decide ; try lia. repeat iSplitR => //.
  Qed.


  (* We can now prove the non-pw spec for oSVT without much pain. *)
  Lemma SVT_online_diffpriv (num den T : Z) (N : nat) (Npos : (0 < N)%nat) K :
    let ε := IZR num / IZR den in
    ∀ (εpos : 0 < ε),
      ↯m (N * ε) -∗
      ⤇ fill K (oSVT #num #den #T #N) -∗
      WP oSVT #num #den #T #N
        {{ f, ∃ (f' : val) (iSVT : nat → iProp Σ),
              ⤇ fill K f' ∗
              iSVT N ∗
              (∀ `(dDB : Distance DB) (db db' : DB) (adj : dDB db db' <= 1) (q : val) K,
                  wp_sensitive (Val q) 1 dDB dZ -∗
                  ⤇ fill K (Val f' (inject db') q) -∗
                  ∀ n, iSVT (S n) -∗
                       WP Val f (inject db) q
                         {{v, ⤇ fill K (Val v) ∗
                              ∃ b : bool, ⌜v = #b⌝ ∗ iSVT (if b then n else S n) }}
        )}}.
  Proof with (tp_pures ; wp_pures).
    (* make sure we have at least enough credit to initialise AT once *)
    destruct N as [|N'] ; [lia|] ; clear Npos.
    iIntros (??) "SNε rhs". rewrite /oSVT...
    tp_alloc as count_r "count_r". wp_alloc count_l as "count_l"...
    tp_bind (above_threshold _ _ _) ; wp_bind (above_threshold _ _ _).
    assert (INR (N'+1)%nat ≠ 0). { replace 0 with (INR 0) => //. intros ?%INR_eq. lia. }
    replace (S N' * ε) with (ε + N' * ε).
    2:{ replace (S N') with (N'+1)%nat by lia. replace (INR (N'+1)) with (N' + 1) by real_solver. lra. }
    iDestruct (ecm_split with "SNε") as "[ε Nε]". 1,2: real_solver.
    opose proof (above_threshold_online_AT_spec num den T _) as AT.
    1: done.
    iPoseProof (AT with "[ε] [rhs]") as "AT" => // ; clear AT.
    iApply (wp_strong_mono'' with "AT").
    replace (S N') with (N'+1)%nat by lia.
    iIntros "%f (%f' & %AUTH & rhs & auth & AT) /=".
    tp_alloc as ref_f' "ref_f'". wp_alloc ref_f as "ref_f"...
    iModIntro. iExists _. iFrame "rhs".
    set (iSVT := (λ n : nat,
                    if Nat.ltb 0%nat n then
                      let n' := (n-1)%nat in
                      count_l ↦ #n' ∗ count_r ↦ₛ #n' ∗
                      ↯m (n' * ε) ∗ ∃ token f f',
                          token ∗ ref_f ↦ f ∗ ref_f' ↦ₛ f' ∗ AT_spec token f f'
                    else emp
                 )%I). iExists iSVT.
    iSplitL.
    { rewrite /iSVT /=. destruct (0 <? N'+1)%nat => //.
      replace ((N'+1)%nat-1)%Z with (Z.of_nat N') by lia.
      replace (N'+1-1)%nat with N' by lia. iFrame. }
    clear f f'.
    iIntros (???????) "q_sens rhs %n (count_l & count_r & nε & (%TOKEN & %f & %f' & auth & ref_f & ref_f' & #AT))"...
    tp_load ; wp_load. tp_bind (f' _ _) ; wp_bind (f _ _).
    iCombine "AT" as "AT_cpy".
    iSpecialize ("AT" $! _ _ _ _ adj _ _) as #.
    iSpecialize ("AT" with "q_sens auth rhs").
    iApply (wp_strong_mono'' with "AT").
    iIntros "%vq (%b & -> & rhs & maybe_auth)".
    iSimpl in "rhs"...
    destruct b eqn:case_bq.
    - tp_load ; wp_load...
      rewrite /= !Nat.sub_0_r.
      destruct n as [|n']...
      { rewrite /iSVT. iFrame. iExists _. iSplitR. 1: done. simpl. done. }
      replace (S n' * ε) with (ε + n' * ε).
      2:{ replace (S n') with (n'+1)%nat by lia. replace (INR (n'+1)) with (n' + 1) by real_solver. lra. }
      iDestruct (ecm_split with "nε") as "[ε n'ε]". 1,2: real_solver.
      simpl. simplify_eq...
      tp_bind (above_threshold _ _ _) ; wp_bind (above_threshold _ _ _).
      opose proof (above_threshold_online_AT_spec num den T _) as AT_pw.
      1: done.
      iPoseProof (AT_pw with "[ε] [rhs]") as "AT_pw" => // ; clear AT_pw.
      iApply (wp_strong_mono'' with "AT_pw [-]").
      iIntros "%g (%g' & %AUTH' & rhs & auth & AT') /=".
      tp_store ; wp_store... tp_load... tp_store ; wp_load... wp_store.
      iFrame. iExists true. iSplitR. 1: done.
      rewrite /iSVT. simpl.
      replace ((n' - 0)%nat) with n' by lia. iFrame.
      replace (Z.of_nat (S n') - 1)%Z with (Z.of_nat n') by lia. iFrame. done.
    - simpl... rewrite /= !Nat.sub_0_r. simplify_eq.
      iSpecialize ("maybe_auth" $! eq_refl).
      tp_load ; wp_load...
      destruct n as [|n']...
      { rewrite /iSVT. iFrame.
        iExists false. iSplitR => //. simpl. iFrame.
        iExists TOKEN. iFrame. done.
      }
      iFrame. iExists _ ; iSplitR => //. iSimpl. iFrame. iExists TOKEN. iFrame. done.
  Qed.

  (* Iterate online SVT over a list of queries. *)
  Definition SVT : val :=
    λ:"num" "den" "T" "N" "db" "qs",
      let: "f" := oSVT "num" "den" "T" "N" in
      (rec: "SVT" "i" "bs" :=
         if: "i" = "N" then "bs" else
           match: list_nth "i" "qs" with
           | NONE => "bs"
           | SOME "q" =>
               let: "b" := "f" "db" "q" in
               "SVT" ("i" + #1) (list_cons "b" "bs")
           end) #0 list_nil.

  (* pointwise diff priv *)
  (* Lemma SVT_diffpriv (num den T : Z) (N : nat)
       `(dDB : Distance DB) (db db' : DB) (adj : dDB db db' <= 1)
       (qs : list val) (QS : val) (is_qs : is_list qs QS)
       K
       :
       let ε := IZR num / IZR den in
       ∀ (εpos : 0 < ε),
         ([∗ list] q ∈ qs, wp_sensitive (Val q) 1 dDB dZ) -∗
         ↯m ε -∗
         ⤇ fill K (SVT #num #den #T #(S N)) (inject db') QS -∗
         WP SVT #num #den #T #(S N) (inject db) QS
           {{ v, ⤇ fill K v }}.
     Proof with (tp_pures ; wp_pures).

     Abort. *)

End svt.

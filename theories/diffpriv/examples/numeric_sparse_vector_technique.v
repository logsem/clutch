From iris.base_logic Require Export na_invariants.
From clutch.common Require Import inject.
From clutch.prelude Require Import tactics.
From clutch.prob Require Import differential_privacy.
From clutch.diffpriv Require Import adequacy diffpriv proofmode.
From clutch.diffpriv.examples Require Import list.

Section nsvt.
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

  (** Numeric Above Threshold **)

  Definition num_above_threshold : val :=
    λ:"num" "den" "T",
      let: "T'" := Laplace (#4*"num") (#9*"den") "T" #() in
      λ:"db" "qi",
        let: "vi" := Laplace (#2*"num") (#9*"den") ("qi" "db") #() in
        if: "T'" ≤ "vi" then SOME (Laplace (#1*"num") (#9*"den") ("qi" "db") #()) else NONEV.

  (* The spec that nAT satisfies after initialising T'. *)

  Definition nAT_spec (c : R) (AUTH : iProp Σ) (f f' : val) : iProp Σ :=
    □ ∀ `(dDB : Distance DB) (db db' : DB) (_ : dDB db db' <= c) (q : val) (K0 : list ectx_item),
      □ wp_sensitive q 1 dDB dZ -∗
      AUTH -∗
      ⤇ fill K0 (f' (inject db') q) -∗
      WP f (inject db) q
        {{ v, ∃ (b : option Z), ⌜v = inject b⌝ ∗ ⤇ fill K0 (inject b) ∗
                                       (⌜v = NONEV⌝ -∗ AUTH) }}.



  (* We prove the (non-pw) spec for onAT from hoare_couple_laplace_choice. *)
  Lemma num_above_threshold_online_nAT_spec (num den T : Z) (εpos : 0 < IZR num / IZR den) K :
    ↯m (1 * (IZR num / IZR den)) -∗
    ⤇ fill K ((Val num_above_threshold) #num #den #T)
    -∗ WP (Val num_above_threshold) #num #den #T
         {{ f, ∃ (f' : val) (AUTH : iProp Σ),
               ⤇ fill K (Val f') ∗ AUTH ∗ nAT_spec 1 AUTH f f' }}.
  Proof with (tp_pures ; wp_pures).
    iIntros "ε rhs". rewrite /num_above_threshold...
    tp_bind (Laplace _ _ _ _). wp_bind (Laplace _ _ _ _).
    set (ε := (IZR num / IZR den)). replace ε with ((1*ε) / 9 + (4*ε) / 9 + (4*ε) / 9) by real_solver.
    fold ε in εpos. repeat rewrite Rmult_plus_distr_l.
    iDestruct (ecm_split with "ε") as "[ε ε3]". 1,2: real_solver.
    iDestruct (ecm_split with "ε") as "[ε2 ε1]". 1,2: real_solver.
    iApply (hoare_couple_laplace _ _ 1%Z 1%Z with "[$rhs ε1]") => //; first by lia.
    { 1: repeat rewrite mult_IZR ; repeat apply Rdiv_pos_pos.
      2: real_solver.
     rewrite -Rmult_div_assoc. apply Rmult_lt_0_compat; first lra. subst ε. apply εpos. }
    { iApply ecm_eq. 2: iFrame. subst ε. replace (IZR (4 * num)) with (4 * IZR num).
      2: qify_r ; zify_q ; lia.
      replace (4 * (IZR num / IZR den) / 9) with (4 * IZR num / IZR (9 * den)).
      1: reflexivity.
      rewrite Rmult_div_assoc.
      rewrite -Rdiv_mult_distr.
      rewrite mult_IZR.
      replace (9 * IZR den) with (IZR den * 9).
      1: reflexivity.
      by rewrite Rmult_comm. }
    iIntros (T') "!> rhs" => /=...
    iModIntro. iExists _. iFrame "rhs".
    iExists (↯m (ε / 9) ∗ ↯m (4 * ε / 9))%I. repeat rewrite Rmult_1_l. iFrame "ε2 ε3". clear K.
    rewrite /nAT_spec.
    iModIntro. iIntros (?????? K) "#q_sens ε rhs"...
    tp_bind (q _) ; wp_bind (q _).
    iCombine "q_sens" as "q_sens'".
    rewrite /wp_sensitive.
    iSpecialize ("q_sens" $! _ _ db db' with "rhs").
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
    tp_bind (Laplace _ _ _ _); wp_bind (Laplace _ _ _ _).
    iDestruct "ε" as "(ε1 & ε2)".
    iApply (hoare_couple_laplace_choice vq_l (vq_r) T' with "[$]") => //.
    1: apply Zabs_ind ; lia.
    1: { repeat rewrite mult_IZR ; apply Rdiv_pos_pos. 2: real_solver. subst ε. lra. }
    { subst ε. rewrite -Rmult_div_assoc. rewrite -Rdiv_mult_distr.
      repeat rewrite Rmult_div_assoc. repeat rewrite mult_IZR. repeat rewrite Rdiv_mult_distr.
      rewrite -Rmult_assoc. replace (2 * 2) with 4. 1, 2: lra. }
    iIntros "%z !> (%z' & rhs & hh)".
    iDestruct "hh" as "[%h_above | [%h_below ε]]".
    - (* above the threshold *)
      simpl... case_bool_decide as Hf1; case_bool_decide as Hf2.
      2, 3, 4: lia.
      wp_if_true; tp_if_true...
      tp_bind (q _); wp_bind (q _).
      iSpecialize ("q_sens'" $! _ _ db db' with "rhs").
      Unshelve. 2: lra.
      (* We apply q_sens a second time that is why it is now persistent in the spec *)
      iApply (wp_strong_mono'' with "q_sens' [ε1]") => //.
      iIntros (?) "(%vq_l' & %vq_r' & -> & rhs & %adj'')" => /=...
      tp_bind (Laplace _ _ _ _); wp_bind (Laplace _ _ _ _).
      iApply (hoare_couple_laplace _ _ 0 1 with "[$rhs ε1]") => //.
      + rewrite Z.add_comm. rewrite -Zplus_0_r_reverse.
        apply le_IZR. rewrite abs_IZR.
        lra.
      + subst ε. repeat rewrite mult_IZR. rewrite Rdiv_mult_distr. lra.
      + iApply ecm_eq. 2: iFrame. subst ε. repeat rewrite mult_IZR. rewrite Rdiv_mult_distr. lra.
      + iIntros (v) "!> rhs" => /=...
        iModIntro.
        iExists (Some v).
        rewrite -Zplus_0_r_reverse.
        iFrame.
        iSplitL.
        1: by iPureIntro.
        iIntros "%Hfalse".
        inversion Hfalse.
    - (* under the threshold *)
      simpl... destruct h_below. case_bool_decide as Hf1; case_bool_decide as Hf2.
      1, 2, 3: lia.
      tp_if_false; wp_if_false.
      iModIntro.
      iExists None.
      iFrame.
      iSplitR; first by iPureIntro.
      by iIntros (Hfin) => //.
  Qed.

  (* ALT def to use tiple *)
  Definition nAT_spec_triple (c : R) (AUTH : iProp Σ) (f f' : val) : iProp Σ :=
    □ ∀ `(dDB : Distance DB) (db db' : DB) (_ : dDB db db' <= c) (q : val) (K0 : list ectx_item),
      {{{ □ wp_sensitive q 1 dDB dZ ∗ AUTH ∗ ⤇ fill K0 (f' (inject db') q) }}}
      f (inject db) q
      {{{ v, RET v; ∃ (b : option Z), ⌜v = inject b⌝ ∗ ⤇ fill K0 (inject b) ∗
                                             (⌜v = NONEV⌝ -∗ AUTH) }}}.
  (*Lemma num_above_threshold_online_nAT_spec_triple (num den T : Z) (εpos : 0 < IZR num / IZR den) K :
    {{{ ↯m (1 * (IZR num / IZR den)) ∗ ⤇ fill K ((Val num_above_threshold) #num #den #T) }}}
      (Val num_above_threshold) #num #den #T
    {{{ f, RET f; ∃ (f' : val) (AUTH : iProp Σ),
               ⤇ fill K (Val f') ∗ AUTH ∗ nAT_spec 1 AUTH f f' }}}.
  Proof.
    iIntros (Φ) "[Hε Hres] HΦ".

    iApply (wp_strong_mono'' with "HΦ").*)


  (** Numeric Sparse Vector **)

  Definition onSVT : val :=
    λ:"num" "den" "T" "N",
      let: "count" := ref ("N" - #1) in
      let: "nAT" := ref (num_above_threshold "num" "den" "T") in
      λ:"db" "qi",
        let: "bq" := !"nAT" "db" "qi" in
        (if: !"count" <= #0 `or` "bq" = NONEV then
           #()
         else ("nAT" <- (num_above_threshold "num" "den" "T") ;;
            "count" <- !"count" - #1)) ;;
        "bq".

  Definition nSVT_spec (f f' : val) (inSVT : nat → iProp Σ) : iProp Σ :=
    (∀ `(dDB : Distance DB) (db db' : DB) (adj : dDB db db' <= 1) (q : val) K,
          □ wp_sensitive (Val q) 1 dDB dZ -∗
          ⤇ fill K (Val f' (inject db') q) -∗
          ∀ n, inSVT (S n) -∗
               WP Val f (inject db) q
               {{v, ⤇ fill K (Val v) ∗ ∃ (b : option Z), ⌜v = inject b⌝ ∗
                              inSVT (if bool_decide(v = NONEV) then S n
                                                               else n) }}
      ).

  Lemma nSVT_online_diffpriv (num den T : Z) (N : nat) (Npos : (0 < N)%nat) K :
    let ε := IZR num / IZR den in
    ∀ (εpos : 0 < ε),
      ↯m (N * ε) -∗
      ⤇ fill K (onSVT #num #den #T #N) -∗
      WP onSVT #num #den #T #N
        {{ f,
             ∃ (f' : val) (inSVT : nat → iProp Σ),
              ⤇ fill K f' ∗
              inSVT N ∗
             □ nSVT_spec f f' inSVT }}.

  Proof with (tp_pures ; wp_pures).
    (* make sure we have at least enough credit to initialise nAT once *)
    destruct N as [|N'] ; [lia|] ; clear Npos.
    iIntros (??) "SNε rhs". rewrite /onSVT...
    tp_alloc as count_r "count_r"; wp_alloc count_l as "count_l"...
    tp_bind (num_above_threshold _ _ _) ; wp_bind (num_above_threshold _ _ _).
    assert (INR (N'+1)%nat ≠ 0).
    { replace 0 with (INR 0) => //. intros ?%INR_eq. lia. }
    replace (S N' * ε) with (ε + N' * ε).
    2:{ replace (S N') with (N'+1)%nat by lia. replace (INR (N'+1)) with (N' + 1) by real_solver. lra. }
    iDestruct (ecm_split with "SNε") as "[ε Nε]". 1,2: real_solver.
    opose proof (num_above_threshold_online_nAT_spec num den T _) as nAT; first done.
    iPoseProof (nAT with "[ε] [rhs]") as "nAT" => // ; clear nAT. 1: by rewrite Rmult_1_l.
    iApply (wp_strong_mono'' with "nAT").
    replace (S N') with (N'+1)%nat by lia.
    iIntros "%f (%f' & %AUTH & rhs & auth & nAT) /=".
    tp_alloc as ref_f' "ref_f'"; wp_alloc ref_f as "ref_f"...
    iModIntro. iExists _. iFrame "rhs".
    set (inSVT := (λ n : nat,
                    if Nat.ltb 0%nat n then
                      let n' := (n-1)%nat in
                      count_l ↦ #n' ∗ count_r ↦ₛ #n' ∗
                      ↯m (n' * ε) ∗ ∃ token f f',
                          token ∗ ref_f ↦ f ∗ ref_f' ↦ₛ f' ∗ nAT_spec 1 token f f'
                    else emp
                 )%I). iExists inSVT.
    iSplitL.
    { rewrite /inSVT /=. destruct (0 <? N'+1)%nat => //.
      replace ((N'+1)%nat-1)%Z with (Z.of_nat N') by lia.
      replace (N'+1-1)%nat with N' by lia. iFrame. }
    clear f f'.
    rewrite /nSVT_spec.
    iIntros "!>" (???????) "#q_sens rhs %n (count_l & count_r & nε & (%TOKEN & %f & %f' & auth & ref_f & ref_f' & #nAT))"...
    tp_load ; wp_load.
    tp_bind (f' _ _); wp_bind (f _ _).
    iCombine "nAT" as "nAT_cpy".
    iSpecialize ("nAT" $! _ _ _ _ adj) as #.
    iSpecialize ("nAT" with "q_sens auth rhs").
    iApply (wp_strong_mono'' with "nAT").
    iIntros "%vq (%b & -> & rhs & maybe_auth)".
    iSimpl in "rhs"...
    case_bool_decide as H1.
    - (* Case where the returned value is None *)
      destruct b; first inversion H1.
      simpl... rewrite /= !Nat.sub_0_r. simplify_eq.
      tp_load ; wp_load...
      iSpecialize ("maybe_auth" $! eq_refl).
      destruct n as [|n']...
      { rewrite /inSVT. iFrame.
        iExists None. iSplitR => //. simpl. iFrame.
        iExists TOKEN. iFrame. done.
      }
      iModIntro.
      iFrame. iExists None ; iSplitR => //.
      iSimpl. iFrame. iExists TOKEN. iFrame. done.

    - (* Case where the returned value is Some(v) *)
      tp_load ; wp_load...
      rewrite /= !Nat.sub_0_r.
      destruct b; last done.
      destruct n as [|n']...
      { (* Case where n <= 0 *)
        rewrite /inSVT. iFrame. iExists (Some z). iModIntro. iPureIntro. done.
      }
      (* Case where n>0 *)
      replace (S n' * ε) with (ε + n' * ε).
      2:{ replace (S n') with (n'+1)%nat by lia. replace (INR (n'+1)) with (n' + 1) by real_solver. lra. }
      iDestruct (ecm_split with "nε") as "[ε n'ε]". 1,2: real_solver.
      simpl. simplify_eq...
      tp_bind (num_above_threshold _ _ _) ; wp_bind (num_above_threshold _ _ _).
      opose proof (num_above_threshold_online_nAT_spec num den T _) as nAT_pw; first done.
      iPoseProof (nAT_pw with "[ε] [rhs]") as "nAT_pw" => // ; clear nAT_pw; first by rewrite Rmult_1_l.
      iApply (wp_strong_mono'' with "nAT_pw [-]").
      iIntros "%g (%g' & %AUTH' & rhs & auth & nAT') /=".
      tp_store ; wp_store... tp_load... tp_store ; wp_load... wp_store.
      iFrame. iExists (Some z). iSplitR; first done.
      rewrite /inSVT.
      case_bool_decide as H1'; first done.
      simpl.
      replace ((n' - 0)%nat) with n' by lia.
      iFrame.
      replace (Z.of_nat (S n') - 1)%Z with (Z.of_nat n') by lia. iFrame. done.
  Qed.

  Definition nSVT_stream : val :=
    λ:"num" "den" "T" "N" "stream_qs" "db",
      let: "f" := onSVT "num" "den" "T" "N" in
      (rec: "nSVT" "i" "bs" :=
         if: "i" = "N" then "bs" else
           match: "stream_qs" "bs" with
           | NONE => "bs"
           | SOME "q" =>
               let: "b" := "f" "db" "q" in
               "nSVT" (if: "b" = NONEV then "i" else ("i" + #1)) (list_cons "b" "bs")
           end) #0 list_nil.

  #[local] Definition nSVT_stream_body (N : nat) (stream_qs : val) {DB} {_ : Inject DB val} (db : DB) (f : val) := (rec: "nSVT" "i" "bs" :=
        if: "i" = #N then "bs"
        else match: stream_qs "bs" with
               InjL <> => "bs"
             | InjR "q" =>
               let: "b" := f (Val (inject db)) "q" in
               "nSVT" (if: "b" = NONEV then "i" else ("i" + #1)) (list_cons "b" "bs")
             end)%V.


  Lemma nSVT_stream_diffpriv (num den T : Z) (N : nat) (Npos : (0 < N)%nat) (stream_qs : val) `(dDB : Distance DB) :
    let ε := IZR num / IZR den in
    ∀ (εpos : 0 < ε),
      □ (∀ K (bs : val),
            ⤇ fill K (stream_qs bs) -∗
            WP stream_qs bs
              {{ qopt, ⤇ fill K (Val qopt) ∗
                       (⌜qopt = NONEV⌝ ∨ ∃ q : val, ⌜qopt = SOMEV q⌝ ∗ □ wp_sensitive q 1 dDB dZ) }}) -∗
      ∀ (db db' : DB) (adj : dDB db db' <= 1) K,
      ↯m (N * ε) -∗
      ⤇ fill K (nSVT_stream #num #den #T #N stream_qs (Val (inject db'))) -∗
      WP nSVT_stream #num #den #T #N stream_qs (Val (inject db))
        {{ v, ⤇ fill K (Val v) }}.
  Proof with (tp_pures ; wp_pures).
    iIntros (ε εpos) "#sens % % % % Nε rhs". rewrite /nSVT_stream...
    tp_bind (onSVT _ _ _ _) ; wp_bind (onSVT _ _ _ _).
    iPoseProof (nSVT_online_diffpriv with "Nε rhs") as "spec" => //.
    iApply (wp_strong_mono'' with "spec"). iIntros "%f (%f' & % & rhs & inSVT & spec) /=".
    do 4 tp_pure. do 4 wp_pure. rewrite -!/(nSVT_stream_body _ _ _ _).
    set (i := 0%Z). set (N' := N). rewrite {1 3}/N'.
    assert (0 <= i)%Z as ipos by lia. assert (N' + i = N)%Z as hi by lia.
    set (bs := InjLV #()). rewrite {1}/bs. generalize i N' bs hi ipos. clear i N' hi ipos bs.
    intros. iRevert (i N' bs hi ipos) "rhs inSVT spec". iLöb as "IH". iIntros (i N' bs hi ipos) "rhs inSVT #spec".
    rewrite {3 4}/nSVT_stream_body...
    case_bool_decide... 1: done.
    tp_bind (stream_qs _) ; wp_bind (stream_qs _).
    iPoseProof ("sens" $! _ bs with "rhs") as "sens_bs".
    iApply (wp_strong_mono'' with "sens_bs").
    iIntros "%qopt (rhs & [->|(%q & -> & #sens_q)]) /="... 1: done.
    tp_bind (f' _ _) ; wp_bind (f _ _).
    iCombine "spec" as "spec_i".
    assert (not (i = N)). 1: intros h ; subst ; auto.
    assert (∃ N'', N' = S N'') as [? ->]. { destruct N'. 1: lia. eauto. }
    iEval (rewrite /nSVT_spec) in "spec_i".
    iSpecialize ("spec_i" $! _ _ db db' adj with "sens_q rhs inSVT") => //.
    iApply (wp_strong_mono'' with "spec_i").
    rewrite -!/(nSVT_stream_body _ _ _ _).
    iIntros "% (rhs & %b & -> & inSVT) /="...
    destruct b. rewrite /list_cons...
    - iApply ("IH" with "[] [] rhs inSVT"). 3: done. 1,2: iPureIntro. 2: lia. lia.
    - iApply ("IH" with "[] [] rhs [inSVT]"). 3,4: done. 1,2: iPureIntro. 2: lia. lia.
  Qed.

End nsvt.

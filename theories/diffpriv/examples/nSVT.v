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


  (* We can give the following specs: *)
  (* { ↯ ε } nA_T T ~ nAT T
     { f f' . AUTH
            ∗ ∀ db db' : adjacent, ∀ q : 1-sensitive,
[equality post:]
              { AUTH } f db q ~ f' db' q { b : option R . b = None -∗ AUTH }
[or pointwise eq:]
              ∀ V , { AUTH } f db qi ~ f db' qi { b b' : option R . ⌜b = V -> b' = V⌝ ∗ (⌜V = None⌝ -∗ AUTH) }
     }  *)

  Definition num_above_threshold : val :=
    λ:"num" "den" "T",
      let: "T'" := Laplace "num" (#4*"den") "T" #() in
      λ:"db" "qi",
        let: "vi" := Laplace "num" (#8*"den") ("qi" "db") #() in
        if: "T'" ≤ "vi" then SOME (Laplace "num" (#2*"den") ("qi" "db") #()) else NONEV.

  (* The spec that AT satisfies after initialising T'. *)

  Definition nAT_spec (c : R) (AUTH : iProp Σ) (f f' : val) : iProp Σ :=
    □ ∀ `(dDB : Distance DB) (db db' : DB) (_ : dDB db db' <= c) (q : val) (K0 : list ectx_item),
      □ wp_sensitive q 1 dDB dZ -∗
      AUTH -∗
      ⤇ fill K0 (f' (inject db') q) -∗
      WP f (inject db) q
        {{ v, ∃ (b : val), ⌜v = b⌝ ∗ ⤇ fill K0 b ∗
                            (⌜v = NONEV⌝ -∗ AUTH) }}.

  (* We prove the (non-pw) spec for onAT from hoare_couple_laplace_choice. *)
  Lemma num_above_threshold_online_AT_spec (num den T : Z) (εpos : 0 < IZR num / IZR den) K :
    ↯m (1 * (IZR num / IZR den)) -∗
    ⤇ fill K ((Val num_above_threshold) #num #den #T)
    -∗ WP (Val num_above_threshold) #num #den #T
         {{ f, ∃ (f' : val) (AUTH : iProp Σ),
               ⤇ fill K (Val f') ∗ AUTH ∗ nAT_spec 1 AUTH f f' }}.
  Proof with (tp_pures ; wp_pures).
    iIntros "ε rhs". rewrite /num_above_threshold...
    tp_bind (Laplace _ _ _ _). wp_bind (Laplace _ _ _ _).
    set (ε := (IZR num / IZR den)). replace ε with (ε / 2 + ε / 4 + ε / 4) by real_solver.
    fold ε in εpos. repeat rewrite Rmult_plus_distr_l.
    (*iDestruct (ecm_split with "ε") as "[ε ε4]". 1,2: real_solver.*)
    iDestruct (ecm_split with "ε") as "[ε ε3]". 1,2: real_solver.
    iDestruct (ecm_split with "ε") as "[ε2 ε1]". 1,2: real_solver.
    iApply (hoare_couple_laplace _ _ 1%Z 1%Z with "[$rhs ε1]") => //.
    1: lia.
    1: rewrite mult_IZR ; apply Rdiv_pos_pos. 1,2: real_solver.
    { iApply ecm_eq. 2: iFrame. subst ε. replace (IZR (4 * den)) with (4 * IZR den).
      2: qify_r ; zify_q ; lia.
      field. eapply Rdiv_pos_den_0 => //. }
    iIntros (T') "!> rhs" => /=...
    iModIntro. iExists _. iFrame "rhs".
    iExists (↯m (ε / 2) ∗ ↯m (ε / 4))%I. repeat rewrite Rmult_1_l. iFrame "ε2 ε3". clear K.
    rewrite /nAT_spec.
    iModIntro. iIntros (?????? K) "#q_sens ε rhs"...
    tp_bind (q _) ; wp_bind (q _).
    iCombine "q_sens" as "q_sens'".
    rewrite /wp_sensitive.
    iSpecialize ("q_sens" $! _ _ db db' with "rhs").
    Unshelve. 2: lra.
    Search "wp_strong_mono".
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
    tp_bind (Laplace _ _ _ _). wp_bind (Laplace _ _ _ _).
    iDestruct "ε" as "(ε1 & ε2)".
    iApply (hoare_couple_laplace_choice vq_l (vq_r) T' with "[$]") => //.
    1: apply Zabs_ind ; lia.
    1: rewrite mult_IZR ; apply Rdiv_pos_pos. 1,2: real_solver.
    { subst ε. rewrite mult_IZR. field. eapply Rdiv_pos_den_0 => //. }
    iIntros "%z !> (%z' & rhs & hh)".
    iDestruct "hh" as "[%h_above | [%h_below ε]]".
    - (* above the threshold *)
      simpl... case_bool_decide as Hf1; case_bool_decide as Hf2.
      2, 3, 4: lia.
      wp_if_true; tp_if_true...
      tp_bind (q _); wp_bind (q _).
      iSpecialize ("q_sens'" $! _ _ db db' with "rhs").
      Unshelve. 2: lra.
      iApply (wp_strong_mono'' with "q_sens' [ε1]") => //.
      iIntros (?) "(%vq_l' & %vq_r' & -> & rhs & %adj'')" => /=...
      tp_bind (Laplace _ _ _ _); wp_bind (Laplace _ _ _ _).
      iApply (hoare_couple_laplace _ _ 0 1 with "[$rhs ε1]") => //.
      + rewrite Z.add_comm. rewrite -Zplus_0_r_reverse.
        Search "Z" "R". apply le_IZR. rewrite abs_IZR.
        lra.
      + rewrite mult_IZR; apply Rdiv_pos_pos. 1, 2: real_solver.
      + iApply ecm_eq. 2: iFrame. subst ε. replace (IZR (2 * den)) with (2 * IZR den).
        2: qify_r; zify_q; lia.
        field. eapply Rdiv_pos_den_0 => //.
      + iIntros (v) "!> rhs" => /=...
        iModIntro.
        iExists (InjRV #v).
        replace #(v + 0) with #v.
        2: by rewrite -Zplus_0_r_reverse.
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
      iExists (InjLV #()).
      iFrame.
      iSplitR; first by iPureIntro; reflexivity.
      by iIntros (Hfin) => //.
  Qed.

 End nsvt.

(** Pointwise-equality specs for the Sparse Vector Technique, ported from
    [clutch.diffpriv.examples.pointwise_eq_sparse_vector_technique] to the
    GENERIC language.  As in [sparse_vector_technique] we "enable" the Laplace
    distribution and replicate the gen-specific spec-tactic fixes (keep the
    Laplace parameter [Pair] syntactic with a literal denominator so the surface
    coupling rule [hoare_couple_laplace] matches).

    NB: the two [SVT_online_diffpriv] lemmas were [Abort]ed in the original
    development (open research questions), and [AT_NF_safe] was [Admitted]
    there; we preserve that status here. *)
From iris.base_logic Require Export na_invariants.
From clutch.prelude Require Import tactics.
From clutch.prob Require Import differential_privacy.
From clutch.gen_diffpriv Require Import all.
From clutch.gen_diffpriv.lib Require Import laplace laplace_choice.
From clutch.gen_prob_lang Require Import inject families.
From clutch.gen_diffpriv.examples Require Import list sparse_vector_technique.
From iris.prelude Require Import options.

(** [Ssvt] and its [SampleIn] instance are inherited from
    [sparse_vector_technique] (imported above) so the imported [above_threshold]
    / [oSVT] specs share the same signature. *)

Lemma inject_expr_Val {A} `{!Inject A val} (x : A) :
  (inject x : expr) = Val (inject x).
Proof. reflexivity. Qed.

Lemma inject_Z_val (z : Z) : (inject z : val) = LitV (LitInt z).
Proof. reflexivity. Qed.

#[global] Opaque sample_idx.

Section svt_pw.
  Context `{!diffprivGS Ssvt Σ}.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Ssvt)).

  #[local] Open Scope R.

  (** As in [sparse_vector_technique]: reduce the [#k * #den] BinOp inside a
      Laplace parameter [Pair] WITHOUT collapsing the [Pair] to a [Val]. *)
  Ltac lap_reduce_den :=
    try (tp_bind (BinOp _ _ _); tp_pure; tp_normalise);
    try (wp_bind (BinOp _ _ _); wp_pure).
  Ltac lap_focus :=
    tp_normalise; rewrite ?inject_Z_val;
    lap_reduce_den;
    tp_bind (Laplace _ _ _ _); wp_bind (Laplace _ _ _ _).
  Ltac tpload  := tp_load;  tp_normalise.
  Ltac tpstore := tp_store; tp_normalise.

  (* The spec that AT satisfies after initialising T'. *)
  Definition AT_spec_pw (AUTH : iProp Σ) (f f' : val) : iProp Σ :=
    □ ∀ (DB : Type) (dDB : Distance DB) (db db' : DB)
      (_ : dDB db db' <= 1) (q : val) (K0 : list ectx_item),
      wp_sensitive Ssvt q 1 dDB dZ -∗
      AUTH -∗
      ⤇ fill K0 (f' (inject db') q) -∗
      ∀ R : bool,
        WP f (inject db) q
          {{ v,
               ∃ v' : val, ⤇ fill K0 v' ∗ ⌜v = #R → v' = #R⌝ ∗
                           ∃ (b b' : bool), ⌜v = #b⌝ ∗ ⌜v' = #b'⌝ ∗
                           (⌜R = false⌝ -∗ AUTH) }}.

  (* For the version of AT with the flag, we can prove the following point-wise spec. *)
  Lemma above_threshold_online_spec_pw (num den T : Z) (εpos : 0 < IZR num / IZR den) `(dDB : Distance DB) (db db' : DB) (adj : dDB db db' <= 1) K :
    ↯m (IZR num / IZR den) -∗
    ⤇ fill K ((Val above_threshold_reset) #num #den #T (Val (inject db')))
    -∗
    WP (Val above_threshold_reset) #num #den #T (Val (inject db))
       {{ f, ∃ f' : val,
             ⤇ fill K (Val f') ∗
             ∃ AUTH : iProp Σ,
               AUTH ∗
               ( ∀ q, wp_sensitive Ssvt (Val q) 1 dDB dZ -∗
                      AUTH -∗
                      ⤇ fill K (f' q) -∗
                      ∀ R : bool,
                        WP (Val f) (Val q)
                          {{ v, ∃ v', ⤇ fill K (Val v') ∗
                                      ⌜ v = SOMEV #R → v' = SOMEV #R ⌝ ∗
                                      (⌜R = false ∧ v = v' ∧ v = SOMEV #R⌝ -∗ AUTH)
               }} )
       }}.
  Proof with (tp_pures ; wp_pures).
    iIntros "ε rhs". rewrite /above_threshold_reset.
    do 5 tp_pure. tp_normalise. do 5 wp_pure.
    tp_bind (BinOp _ _ _). tp_pure. tp_normalise. wp_bind (BinOp _ _ _). wp_pure.
    tp_bind (Laplace _ _ _ _). wp_bind (Laplace _ _ _ _).
    set (ε := (IZR num / IZR den)). replace ε with (ε / 2 + ε / 2) by real_solver.
    fold ε in εpos.
    iDestruct (ecm_split with "ε") as "[ε ε']". 1,2: real_solver.
    iApply (hoare_couple_laplace (S:=Ssvt) _ _ 1%Z 1%Z with "[$rhs ε']") => //.
    1: apply Zabs_ind ; lia.
    1: rewrite mult_IZR ; apply Rdiv_pos_pos. 1,2: real_solver.
    { iApply ecm_eq. 2: iFrame. subst ε. replace (IZR (2 * den)) with (2 * IZR den).
      2: qify_r ; zify_q ; lia.
      field. eapply Rdiv_pos_den_0 => //.
    }
    iIntros (T') "!> rhs". tp_normalise...
    tp_alloc as reset_r "reset_r". tp_normalise. wp_alloc reset_l as "reset_l"...
    iModIntro. iExists _. iFrame.
    iExists (↯m (ε / 2) ∗ reset_r ↦ₛ #false ∗ reset_l ↦ #false)%I. iFrame.
    iIntros "%q q_sens (ε & reset_r & reset_l) rhs %R"... tpload. wp_load...

    tp_bind (q _). wp_bind (q _). rewrite /wp_sensitive.
    iSpecialize ("q_sens" $! (ltac:(lra) : (0 <= 1)%R) _ db db' with "rhs").
    iPoseProof (wp_frame_l with "[reset_r $q_sens]") as "q_sens". 1: iAssumption.
    iPoseProof (wp_frame_l with "[reset_l $q_sens]") as "q_sens". 1: iAssumption.
    iPoseProof (wp_frame_l with "[ε $q_sens]") as "q_sens". 1: iAssumption.
    iApply (wp_mono with "q_sens").
    iIntros (?) "(ε & reset_l & reset_r & %vq_l & %vq_r & -> & rhs & %adj')".
    assert (-1 <= vq_l - vq_r <= 1)%Z as [].
    {
      rewrite Rmult_1_l in adj'.
      assert (dZ vq_l vq_r <= 1) as h by (etrans ; eauto).
      revert h.
      rewrite /dZ/distance Rabs_Zabs.
      apply Zabs_ind ; intros ? h; split.
      all: pose proof (le_IZR _ _ h) ; lia.
    }
    (* case on whether the result is the one that will get released (pweq) *)
    destruct R eqn:HR.
    - lap_focus.
      iApply (hoare_couple_laplace (S:=Ssvt) vq_l vq_r 1%Z 2%Z with "[$rhs ε]") => //.
      1: apply Zabs_ind ; lia.
      1: rewrite mult_IZR ; apply Rdiv_pos_pos ; real_solver.
      { subst ε. iApply ecm_eq. 2: iFrame. rewrite mult_IZR. field. eapply Rdiv_pos_den_0 => //. }
      iIntros "%vi !> rhs". tp_normalise...
      case_bool_decide (_ (T' + 1)%Z _) ; tp_pures ; try tpstore ; tp_pures. all: case_bool_decide...
      all: try tpstore ; try wp_store ; try tp_pures ; try wp_pures.
      + iFrame. iModIntro. iSplitR. 1: done.
        iIntros ((h_R & h_vv' & h_vR)). exfalso. inversion h_R.
      + exfalso. lia.
      + exfalso. lia.
      + iFrame. iSplitR. 1: done. iModIntro.
        iIntros ((h_R & h_vv' & h_vR)). exfalso. inversion h_R.
    - lap_focus.
      iMod ecm_zero as "ε0".
      iApply (hoare_couple_laplace (S:=Ssvt) vq_l vq_r (vq_r - vq_l)%Z 0%Z with "[$rhs ε0]") => //.
      1: apply Zabs_ind ; lia.
      1: rewrite mult_IZR ; apply Rdiv_pos_pos ; real_solver.
      1: rewrite Rmult_0_l ; iFrame.
      iIntros "%vi !> rhs". tp_normalise...
      case_bool_decide (_ (T' + 1)%Z _) ; tp_pures ; try tpstore ; tp_pures. all: case_bool_decide...
      all: try tpstore ; try wp_store ; try tp_pures ; try wp_pures.
      + iFrame. iModIntro. iSplitR. 1: done.
        iIntros ((_h_R & h_vv' & h_vR)). exfalso. inversion h_vR.
      + exfalso. lia.
      + iFrame. iModIntro. iSplitR. 1: done.
        iIntros ((_h_R & h_vv' & h_vR)). exfalso. inversion h_vR.
      + iFrame. done.
    Unshelve. all: try exact Ssvt.
  Qed.

  (* Removing ownership of the references from AUTH actually makes the postcondition simpler. *)
  Lemma above_threshold_online_no_flag_spec_pw (num den T : Z) (εpos : 0 < IZR num / IZR den) K :
    ↯m (IZR num / IZR den) -∗
    ⤇ fill K ((Val above_threshold) #num #den #T)
    -∗
    WP (Val above_threshold) #num #den #T
       {{ f, ∃ f' : val,
             ⤇ fill K (Val f') ∗
             ∃ AUTH : iProp Σ,
               AUTH ∗
               AT_spec_pw AUTH f f'
       }}.
  Proof with (tp_pures ; wp_pures).
    iIntros "ε rhs". rewrite /above_threshold.
    do 5 tp_pure. tp_normalise. do 5 wp_pure.
    tp_bind (BinOp _ _ _). tp_pure. tp_normalise. wp_bind (BinOp _ _ _). wp_pure.
    tp_bind (Laplace _ _ _ _). wp_bind (Laplace _ _ _ _).
    set (ε := (IZR num / IZR den)). replace ε with (ε / 2 + ε / 2) by real_solver.
    fold ε in εpos.
    iDestruct (ecm_split with "ε") as "[ε ε']". 1,2: real_solver.
    iApply (hoare_couple_laplace (S:=Ssvt) _ _ 1%Z 1%Z with "[$rhs ε']") => //.
    1: apply Zabs_ind ; lia.
    1: rewrite mult_IZR ; apply Rdiv_pos_pos. 1,2: real_solver.
    { iApply ecm_eq. 2: iFrame. subst ε. replace (IZR (2 * den)) with (2 * IZR den).
      2: qify_r ; zify_q ; lia.
      field. eapply Rdiv_pos_den_0 => //. }
    iIntros (T') "!> rhs". tp_normalise...
    iModIntro. iExists _. iFrame "rhs".
    iExists (↯m (ε / 2))%I. iFrame "ε". clear K.
    iModIntro.
    iIntros (?????) "%q %K q_sens ε rhs %R"...

    tp_bind (q _) ; wp_bind (q _). rewrite /wp_sensitive.
    iSpecialize ("q_sens" $! (ltac:(lra) : (0 <= 1)%R) _ db db' with "rhs").

    iApply (wp_strong_mono'' with "q_sens [ε]") => //.
    iIntros (?) "(%vq_l & %vq_r & -> & rhs & %adj')".
    assert (-1 <= vq_l - vq_r <= 1)%Z as [].
    {
      rewrite Rmult_1_l in adj'.
      assert (dZ vq_l vq_r <= 1) as h by (etrans ; eauto).
      revert h. rewrite /dZ/distance Rabs_Zabs.
      apply Zabs_ind ; intros ? h; split.
      all: pose proof (le_IZR _ _ h) ; lia.
    }
    (* case on whether the result is the one that will get released (pweq) *)
    destruct R eqn:HR.
    - lap_focus.
      iApply (hoare_couple_laplace (S:=Ssvt) vq_l vq_r 1%Z 2%Z with "[$rhs ε]") => //.
      1: apply Zabs_ind ; lia.
      1: rewrite mult_IZR ; apply Rdiv_pos_pos ; real_solver.
      { subst ε. iApply ecm_eq. 2: iFrame. rewrite mult_IZR. field. eapply Rdiv_pos_den_0 => //. }
      iIntros "%z_l !> rhs". tp_normalise. tp_pures.
      case_bool_decide (_ (T' + 1)%Z _)...
      all: destruct_decide (bool_decide_reflect (T' ≤ z_l)%Z) as res_l.
      all: iFrame "rhs" ; iModIntro.
      + iSplitR => //. iExists true,true. do 2 iSplitR => //. iIntros (h_R). exfalso. inversion h_R.
      + exfalso. lia.
      + exfalso. lia.
      + iSplitR => //. iExists false, false. do 2 iSplitR => //. iIntros (h_R). exfalso. inversion h_R.
    - lap_focus.
      iMod ecm_zero as "ε0".
      iApply (hoare_couple_laplace (S:=Ssvt) vq_l vq_r (vq_r - vq_l)%Z 0%Z with "[$rhs ε0]") => //.
      1: apply Zabs_ind ; lia.
      1: rewrite mult_IZR ; apply Rdiv_pos_pos ; real_solver.
      1: rewrite Rmult_0_l ; iFrame.
      iIntros "%z_l !> rhs". tp_normalise...
      case_bool_decide (_ (T' + 1)%Z _).
      all: destruct_decide (bool_decide_reflect (T' ≤ z_l)%Z) as res_l ; iModIntro ; iFrame "rhs".
      all: iSplitR ; [|by (iExists _,_ ; iFrame "ε")].
      + iIntros (Rf). inversion Rf.
      + exfalso. lia.
      + iIntros (Rf). inversion Rf.
      + done.
    Unshelve. all: try exact Ssvt.
  Qed.

  (* If we get R before having to pick the coupling for the noisy T', then we can just couple the
     first Laplacian so that the comparisons are synchronised and use the error for the second. *)
  Lemma above_threshold_online_no_flag_spec_pw_no_AUTH' (num den T : Z)
    (εpos : 0 < IZR num / IZR den) K (R : bool) :
    ↯m (IZR num / (2 * IZR den)) -∗
    ⤇ fill K ((Val above_threshold) #num #den #T)
    -∗
    WP (Val above_threshold) #num #den #T
       {{ f, ∃ f' : val,
             ⤇ fill K (Val f') ∗
               ( ∀ `(dDB : Distance DB) (db db' : DB) (adj : dDB db db' <= 1) q K,
                   wp_sensitive Ssvt (Val q) 1 dDB dZ -∗
                      ⤇ fill K (f' (Val (inject db')) q) -∗
                      (if R then ↯m (IZR num / (2 * IZR den)) else emp) -∗
                        WP (Val f) (Val (inject db)) (Val q)
                          {{ v, ∃ v', ⤇ fill K (Val v') ∗
                                      ⌜ v = #R → v' = #R ⌝
               }} )
       }}.
  Proof with (tp_pures ; wp_pures).
    iIntros "ε rhs". rewrite /above_threshold.
    do 5 tp_pure. tp_normalise. do 5 wp_pure.
    tp_bind (BinOp _ _ _). tp_pure. tp_normalise. wp_bind (BinOp _ _ _). wp_pure.
    tp_bind (Laplace _ _ _ _). wp_bind (Laplace _ _ _ _).
    set (ε := (IZR num / 2 * IZR den)).
    fold ε in εpos.
    (* case on whether the result is the one that will get released (pweq) *)
    destruct R eqn:HR.
    {
      iApply (hoare_couple_laplace (S:=Ssvt) _ _ 1%Z 1%Z with "[$rhs ε]") => //.
      1: apply Zabs_ind ; lia.
      1: rewrite mult_IZR ; apply Rdiv_pos_pos ; real_solver.
      { iApply ecm_eq. 2: iFrame. subst ε. replace (IZR (2 * den)) with (2 * IZR den).
        2: qify_r ; zify_q ; lia.
        field. eapply Rdiv_pos_den_0 => //. }
      iIntros (T') "!> rhs". tp_normalise...
      iModIntro. iExists _. iFrame "rhs". clear K.
      iIntros (?????) "%q %K q_sens rhs ε"...

      tp_bind (q _) ; wp_bind (q _). rewrite /wp_sensitive.
      iSpecialize ("q_sens" $! (ltac:(lra) : (0 <= 1)%R) _ db db' with "rhs").

      iApply (wp_strong_mono'' with "q_sens [ε]") => //.
      iIntros (?) "(%vq_l & %vq_r & -> & rhs & %adj')".
      assert (-1 <= vq_l - vq_r <= 1)%Z as [adj_lb adj_ub].
      {
        rewrite Rmult_1_l in adj'.
        assert (dZ vq_l vq_r <= 1) as h by (etrans ; eauto).
        revert h. rewrite /dZ/distance Rabs_Zabs.
        apply Zabs_ind ; intros ? h; split.
        all: pose proof (le_IZR _ _ h) ; lia.
      }
      lap_focus.
      iApply (hoare_couple_laplace (S:=Ssvt) vq_l vq_r 1%Z 2%Z with "[$rhs ε]") => //.
      1: apply Zabs_ind ; lia.
      1: rewrite mult_IZR ; apply Rdiv_pos_pos ; real_solver.
      { subst ε. iApply ecm_eq. 2: iFrame. rewrite mult_IZR. field. eapply Rdiv_pos_den_0 => //. }
      iIntros "%z_l !> rhs". tp_normalise. tp_pures.
      case_bool_decide (_ (T' + 1)%Z _) as res_r...
      all: destruct_decide (bool_decide_reflect (T' ≤ z_l)%Z) as res_l.
      all: iFrame "rhs" ; iModIntro.
      + done.
      + exfalso. lia.
      + exfalso. lia.
      + done.
    }

    {
      iMod ecm_zero as "ε0".
      iApply (hoare_couple_laplace (S:=Ssvt) _ _ 0%Z 0%Z with "[$rhs ε0]") => //.
      1: apply Zabs_ind ; lia.
      1: rewrite mult_IZR ; apply Rdiv_pos_pos ; real_solver.
      { iApply ecm_eq. 2: iFrame. lra. }
      iIntros (T') "!> rhs". tp_normalise...
      iModIntro. iExists _. iFrame "rhs". clear K.
      iIntros (?????) "%q %K q_sens rhs ε'"...

      tp_bind (q _) ; wp_bind (q _). rewrite /wp_sensitive.
      iSpecialize ("q_sens" $! (ltac:(lra) : (0 <= 1)%R) _ db db' with "rhs").

      iApply (wp_strong_mono'' with "q_sens [ε]") => //.
      iIntros (?) "(%vq_l & %vq_r & -> & rhs & %adj')".
      assert (-1 <= vq_l - vq_r <= 1)%Z as [adj_lb adj_ub].
      {
        rewrite Rmult_1_l in adj'.
        assert (dZ vq_l vq_r <= 1) as h by (etrans ; eauto).
        revert h. rewrite /dZ/distance Rabs_Zabs.
        apply Zabs_ind ; intros ? h; split.
        all: pose proof (le_IZR _ _ h) ; lia.
      }
      lap_focus.
      iApply (hoare_couple_laplace (S:=Ssvt) vq_l vq_r 0%Z 1%Z with "[$rhs ε]") => //.
      1: apply Zabs_ind ; lia.
      1: rewrite mult_IZR ; apply Rdiv_pos_pos ; real_solver.
      1: rewrite Rmult_1_l mult_IZR.
      (* Actually, only half the error we have is needed. *)
      { subst ε. iApply ecm_weaken. 2: iFrame. split.
        - apply Rdiv_nneg_nneg ; lra.
        - rewrite (Rmult_comm 4). rewrite (Rmult_comm 2).
          rewrite Rdiv_mult_distr. rewrite Rdiv_mult_distr.
          rewrite /Rdiv. apply Rmult_le_compat_l.
          1: lra. lra.
      }
      iIntros "%z_l !> rhs". tp_normalise...
      case_bool_decide (_ (T' + 0)%Z _) as res_r.
      all: rewrite !Zplus_0_r in res_r.
      all: destruct_decide (bool_decide_reflect (T' ≤ z_l)%Z) as res_l ; iModIntro ; iFrame "rhs".
      + done.
      + exfalso. clear -res_l res_r. done.
      + exfalso. clear -res_l res_r. done.
      + done.
    }
    Unshelve. all: try exact Ssvt.
  Qed.

  (* TODO move *)
  Lemma AT_NF_safe num den T :
    ⊢ WP (above_threshold #num #den #T) {{ v, ⌜True⌝ }}.
  Proof.
    rewrite /above_threshold.
  Admitted. (* TODO(port): Admitted in the original development. *)

End svt_pw.

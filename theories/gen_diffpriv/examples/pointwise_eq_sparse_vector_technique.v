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

(** [Sg] and its [SampleIn] instance are inherited from
    [sparse_vector_technique] (imported above) so the imported [above_threshold]
    / [oSVT] specs share the same signature. *)

Lemma inject_expr_Val {A} `{!Inject A val} (x : A) :
  (inject x : expr) = Val (inject x).
Proof. reflexivity. Qed.

Lemma inject_Z_val (z : Z) : (inject z : val) = LitV (LitInt z).
Proof. reflexivity. Qed.

#[global] Opaque sample_idx.

Section svt_pw.
  Context {Sg : Sig} `{!SampleIn laplace_family Sg} `{!diffprivGS Sg Σ}.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Sg)).

  #[local] Open Scope R.

  Ltac lap_focus :=
    tp_normalise; rewrite ?inject_Z_val;
    tp_pures; wp_pures;
    tp_bind (Sample _ _ _); wp_bind (Sample _ _ _).
  Ltac tpload  := tp_load;  tp_normalise.
  Ltac tpstore := tp_store; tp_normalise.

  (* The spec that AT satisfies after initialising T'.  Parametric over query
     sensitivity [Δ ≥ 1]; with [Δ = 1] this is exactly the original sensitivity-1
     spec ([wp_sensitive Sg q 1 dDB dZ]). *)
  Definition AT_spec_pw (Δ : Z) (AUTH : iProp Σ) (f f' : val) : iProp Σ :=
    □ ∀ (DB : Type) (dDB : Distance DB) (db db' : DB)
      (_ : dDB db db' <= 1) (q : val) (K0 : list ectx_item),
      wp_sensitive Sg q (IZR Δ) dDB dZ -∗
      AUTH -∗
      ⤇ fill K0 (f' (inject db') q) -∗
      ∀ R : bool,
        WP f (inject db) q
          {{ v,
               ∃ v' : val, ⤇ fill K0 v' ∗ ⌜v = #R → v' = #R⌝ ∗
                           ∃ (b b' : bool), ⌜v = #b⌝ ∗ ⌜v' = #b'⌝ ∗
                           (⌜R = false⌝ -∗ AUTH) }}.

  (* For the version of AT with the flag, we can prove the following point-wise
     spec.  Generalised to query sensitivity [Δ ≥ 1]; the noise budget scales to
     [Δ·(num/den)], with [Δ = 1] recovering the original [num/den] bound. *)
  Lemma above_threshold_online_spec_pw (Δ : Z) (HΔ : (1 <= Δ)%Z) (num den T : Z) (εpos : 0 < IZR num / IZR den) `(dDB : Distance DB) (db db' : DB) (adj : dDB db db' <= 1) K :
    ↯m (IZR Δ * (IZR num / IZR den)) -∗
    ⤇ fill K ((Val above_threshold_reset) #num #den #T (Val (inject db')))
    -∗
    WP (Val above_threshold_reset) #num #den #T (Val (inject db))
       {{ f, ∃ f' : val,
             ⤇ fill K (Val f') ∗
             ∃ AUTH : iProp Σ,
               AUTH ∗
               ( ∀ q, wp_sensitive Sg (Val q) (IZR Δ) dDB dZ -∗
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
    tp_pures. tp_normalise. wp_pures.
    tp_bind (Sample _ _ _). wp_bind (Sample _ _ _).
    assert (HΔpos : (0 <= IZR Δ)%R) by (apply IZR_le; lia).
    set (ε := (IZR num / IZR den)).
    replace (IZR Δ * ε)%R with (IZR Δ * ε / 2 + IZR Δ * ε / 2)%R by real_solver.
    fold ε in εpos.
    iDestruct (ecm_split with "ε") as "[ε ε']". 1,2: real_solver.
    iApply (wp_couple_laplace (S:=Sg) T T Δ Δ ltac:(lia) num (2*den)%Z
            with "[$rhs ε']") => //.
    1: rewrite mult_IZR ; apply Rdiv_pos_pos. 1,2: real_solver.
    { iApply ecm_eq. 2: iFrame. subst ε. replace (IZR (2 * den)) with (2 * IZR den).
      2: qify_r ; zify_q ; lia.
      field. eapply Rdiv_pos_den_0 => //.
    }
    iIntros (T') "!> rhs". tp_normalise...
    tp_alloc as reset_r "reset_r". tp_normalise. wp_alloc reset_l as "reset_l"...
    iModIntro. iExists _. iFrame.
    iExists (↯m (IZR Δ * ε / 2) ∗ reset_r ↦ₛ #false ∗ reset_l ↦ #false)%I. iFrame.
    iIntros "%q q_sens (ε & reset_r & reset_l) rhs %R"... tpload. wp_load...

    tp_bind (q _). wp_bind (q _). rewrite /wp_sensitive.
    iSpecialize ("q_sens" $! HΔpos _ db db' with "rhs").
    iPoseProof (wp_frame_l with "[reset_r $q_sens]") as "q_sens". 1: iAssumption.
    iPoseProof (wp_frame_l with "[reset_l $q_sens]") as "q_sens". 1: iAssumption.
    iPoseProof (wp_frame_l with "[ε $q_sens]") as "q_sens". 1: iAssumption.
    iApply (wp_mono with "q_sens").
    iIntros (?) "(ε & reset_l & reset_r & %vq_l & %vq_r & -> & rhs & %adj')".
    assert (- Δ <= vq_l - vq_r <= Δ)%Z as [].
    {
      assert (dZ vq_l vq_r <= IZR Δ) as h.
      { etrans; first apply adj'.
        rewrite -{2}(Rmult_1_r (IZR Δ)). apply Rmult_le_compat_l; [exact HΔpos|].
        etrans; first apply adj. lra. }
      revert h.
      rewrite /dZ/distance Rabs_Zabs.
      apply Zabs_ind ; intros ? h; split.
      all: pose proof (le_IZR _ _ h) ; lia.
    }
    (* case on whether the result is the one that will get released (pweq) *)
    destruct R eqn:HR.
    - lap_focus.
      iApply (wp_couple_laplace (S:=Sg) vq_l vq_r Δ (2*Δ)%Z
              ltac:(apply Zabs_ind ; lia) num (4*den)%Z
              with "[$rhs ε]") => //.
      1: rewrite mult_IZR ; apply Rdiv_pos_pos. 1,2: real_solver.
      { subst ε. iApply ecm_eq. 2: iFrame. rewrite !mult_IZR. field. eapply Rdiv_pos_den_0 => //. }
      iIntros "%vi !> rhs". tp_normalise...
      case_bool_decide (_ (T' + Δ)%Z _) ; tp_pures ; try tpstore ; tp_pures. all: case_bool_decide...
      all: try tpstore ; try wp_store ; try tp_pures ; try wp_pures.
      + iFrame. iModIntro. iSplitR. 1: done.
        iIntros ((h_R & h_vv' & h_vR)). exfalso. inversion h_R.
      + exfalso. lia.
      + exfalso. lia.
      + iFrame. iSplitR. 1: done. iModIntro.
        iIntros ((h_R & h_vv' & h_vR)). exfalso. inversion h_R.
    - lap_focus.
      iMod ecm_zero as "ε0".
      iApply (wp_couple_laplace (S:=Sg) vq_l vq_r (vq_r - vq_l)%Z 0%Z
              ltac:(apply Zabs_ind ; lia) num (4*den)%Z
              with "[$rhs ε0]") => //.
      1: rewrite mult_IZR ; apply Rdiv_pos_pos. 1,2: real_solver.
      1: rewrite Rmult_0_l ; iFrame.
      iIntros "%vi !> rhs". tp_normalise...
      case_bool_decide (_ (T' + Δ)%Z _) ; tp_pures ; try tpstore ; tp_pures. all: case_bool_decide...
      all: try tpstore ; try wp_store ; try tp_pures ; try wp_pures.
      + iFrame. iModIntro. iSplitR. 1: done.
        iIntros ((_h_R & h_vv' & h_vR)). exfalso. inversion h_vR.
      + exfalso. lia.
      + iFrame. iModIntro. iSplitR. 1: done.
        iIntros ((_h_R & h_vv' & h_vR)). exfalso. inversion h_vR.
      + iFrame. done.
    Unshelve. all: try exact Sg.
  Qed.

  (* Removing ownership of the references from AUTH actually makes the
     postcondition simpler.  Generalised to query sensitivity [Δ ≥ 1]; budget
     [Δ·(num/den)], with [Δ = 1] recovering the original [num/den]. *)
  Lemma above_threshold_online_no_flag_spec_pw (Δ : Z) (HΔ : (1 <= Δ)%Z) (num den T : Z) (εpos : 0 < IZR num / IZR den) K :
    ↯m (IZR Δ * (IZR num / IZR den)) -∗
    ⤇ fill K ((Val above_threshold) #num #den #T)
    -∗
    WP (Val above_threshold) #num #den #T
       {{ f, ∃ f' : val,
             ⤇ fill K (Val f') ∗
             ∃ AUTH : iProp Σ,
               AUTH ∗
               AT_spec_pw Δ AUTH f f'
       }}.
  Proof with (tp_pures ; wp_pures).
    iIntros "ε rhs". rewrite /above_threshold.
    tp_pures. tp_normalise. wp_pures.
    tp_bind (Sample _ _ _). wp_bind (Sample _ _ _).
    assert (HΔpos : (0 <= IZR Δ)%R) by (apply IZR_le; lia).
    set (ε := (IZR num / IZR den)).
    replace (IZR Δ * ε)%R with (IZR Δ * ε / 2 + IZR Δ * ε / 2)%R by real_solver.
    fold ε in εpos.
    iDestruct (ecm_split with "ε") as "[ε ε']". 1,2: real_solver.
    iApply (wp_couple_laplace (S:=Sg) T T Δ Δ ltac:(lia) num (2*den)%Z
            with "[$rhs ε']") => //.
    1: rewrite mult_IZR ; apply Rdiv_pos_pos. 1,2: real_solver.
    { iApply ecm_eq. 2: iFrame. subst ε. replace (IZR (2 * den)) with (2 * IZR den).
      2: qify_r ; zify_q ; lia.
      field. eapply Rdiv_pos_den_0 => //. }
    iIntros (T') "!> rhs". tp_normalise...
    iModIntro. iExists _. iFrame "rhs".
    iExists (↯m (IZR Δ * ε / 2))%I. iFrame "ε". clear K.
    iModIntro.
    iIntros (DB dDB db db' adj) "%q %K q_sens ε rhs %R"...

    tp_bind (q _) ; wp_bind (q _). rewrite /wp_sensitive.
    iSpecialize ("q_sens" $! HΔpos _ db db' with "rhs").

    iApply (wp_strong_mono'' with "q_sens [ε]") => //.
    iIntros (?) "(%vq_l & %vq_r & -> & rhs & %adj')".
    assert (- Δ <= vq_l - vq_r <= Δ)%Z as [].
    {
      assert (dZ vq_l vq_r <= IZR Δ) as h.
      { etrans; first apply adj'.
        rewrite -{2}(Rmult_1_r (IZR Δ)). apply Rmult_le_compat_l; [exact HΔpos|].
        etrans; first apply adj. lra. }
      revert h. rewrite /dZ/distance Rabs_Zabs.
      apply Zabs_ind ; intros ? h; split.
      all: pose proof (le_IZR _ _ h) ; lia.
    }
    (* case on whether the result is the one that will get released (pweq) *)
    destruct R eqn:HR.
    - lap_focus.
      iApply (wp_couple_laplace (S:=Sg) vq_l vq_r Δ (2*Δ)%Z
              ltac:(apply Zabs_ind ; lia) num (4*den)%Z
              with "[$rhs ε]") => //.
      1: rewrite mult_IZR ; apply Rdiv_pos_pos. 1,2: real_solver.
      { subst ε. iApply ecm_eq. 2: iFrame. rewrite !mult_IZR. field. eapply Rdiv_pos_den_0 => //. }
      iIntros "%z_l !> rhs". tp_normalise. tp_pures.
      case_bool_decide (_ (T' + Δ)%Z _)...
      all: destruct_decide (bool_decide_reflect (T' ≤ z_l)%Z) as res_l.
      all: iFrame "rhs" ; iModIntro.
      + iSplitR => //. iExists true,true. do 2 iSplitR => //. iIntros (h_R). exfalso. inversion h_R.
      + exfalso. lia.
      + exfalso. lia.
      + iSplitR => //. iExists false, false. do 2 iSplitR => //. iIntros (h_R). exfalso. inversion h_R.
    - lap_focus.
      iMod ecm_zero as "ε0".
      iApply (wp_couple_laplace (S:=Sg) vq_l vq_r (vq_r - vq_l)%Z 0%Z
              ltac:(apply Zabs_ind ; lia) num (4*den)%Z
              with "[$rhs ε0]") => //.
      1: rewrite mult_IZR ; apply Rdiv_pos_pos. 1,2: real_solver.
      1: rewrite Rmult_0_l ; iFrame.
      iIntros "%z_l !> rhs". tp_normalise...
      case_bool_decide (_ (T' + Δ)%Z _).
      all: destruct_decide (bool_decide_reflect (T' ≤ z_l)%Z) as res_l ; iModIntro ; iFrame "rhs".
      all: iSplitR ; [|by (iExists _,_ ; iFrame "ε")].
      + iIntros (Rf). inversion Rf.
      + exfalso. lia.
      + iIntros (Rf). inversion Rf.
      + done.
    Unshelve. all: try exact Sg.
  Qed.

  (* If we get R before having to pick the coupling for the noisy T', then we can just couple the
     first Laplacian so that the comparisons are synchronised and use the error for the second. *)
  Lemma above_threshold_online_no_flag_spec_pw_no_AUTH' (Δ : Z) (HΔ : (1 <= Δ)%Z) (num den T : Z)
    (εpos : 0 < IZR num / IZR den) K (R : bool) :
    ↯m (IZR Δ * (IZR num / (2 * IZR den))) -∗
    ⤇ fill K ((Val above_threshold) #num #den #T)
    -∗
    WP (Val above_threshold) #num #den #T
       {{ f, ∃ f' : val,
             ⤇ fill K (Val f') ∗
               ( ∀ `(dDB : Distance DB) (db db' : DB) (adj : dDB db db' <= 1) q K,
                   wp_sensitive Sg (Val q) (IZR Δ) dDB dZ -∗
                      ⤇ fill K (f' (Val (inject db')) q) -∗
                      (if R then ↯m (IZR Δ * (IZR num / (2 * IZR den))) else emp) -∗
                        WP (Val f) (Val (inject db)) (Val q)
                          {{ v, ∃ v', ⤇ fill K (Val v') ∗
                                      ⌜ v = #R → v' = #R ⌝
               }} )
       }}.
  Proof with (tp_pures ; wp_pures).
    iIntros "ε rhs". rewrite /above_threshold.
    tp_pures. tp_normalise. wp_pures.
    tp_bind (Sample _ _ _). wp_bind (Sample _ _ _).
    assert (HΔpos : (0 <= IZR Δ)%R) by (apply IZR_le; lia).
    set (ε := (IZR num / 2 * IZR den)).
    fold ε in εpos.
    (* case on whether the result is the one that will get released (pweq) *)
    destruct R eqn:HR.
    {
      iApply (wp_couple_laplace (S:=Sg) T T Δ Δ ltac:(lia) num (2*den)%Z
              with "[$rhs ε]") => //.
      1: rewrite mult_IZR ; apply Rdiv_pos_pos. 1,2: real_solver.
      { iApply ecm_eq. 2: iFrame. subst ε. replace (IZR (2 * den)) with (2 * IZR den).
        2: qify_r ; zify_q ; lia.
        field. eapply Rdiv_pos_den_0 => //. }
      iIntros (T') "!> rhs". tp_normalise...
      iModIntro. iExists _. iFrame "rhs". clear K.
      iIntros (DB dDB db db' adj) "%q %K q_sens rhs ε"...

      tp_bind (q _) ; wp_bind (q _). rewrite /wp_sensitive.
      iSpecialize ("q_sens" $! HΔpos _ db db' with "rhs").

      iApply (wp_strong_mono'' with "q_sens [ε]") => //.
      iIntros (?) "(%vq_l & %vq_r & -> & rhs & %adj')".
      assert (- Δ <= vq_l - vq_r <= Δ)%Z as [adj_lb adj_ub].
      {
        assert (dZ vq_l vq_r <= IZR Δ) as h.
        { etrans; first apply adj'.
          rewrite -{2}(Rmult_1_r (IZR Δ)). apply Rmult_le_compat_l; [exact HΔpos|].
          etrans; first apply adj. lra. }
        revert h. rewrite /dZ/distance Rabs_Zabs.
        apply Zabs_ind ; intros ? h; split.
        all: pose proof (le_IZR _ _ h) ; lia.
      }
      lap_focus.
      iApply (wp_couple_laplace (S:=Sg) vq_l vq_r Δ (2*Δ)%Z
              ltac:(apply Zabs_ind ; lia) num (4*den)%Z
              with "[$rhs ε]") => //.
      1: rewrite mult_IZR ; apply Rdiv_pos_pos. 1,2: real_solver.
      { subst ε. iApply ecm_eq. 2: iFrame. rewrite !mult_IZR. field. eapply Rdiv_pos_den_0 => //. }
      iIntros "%z_l !> rhs". tp_normalise. tp_pures.
      case_bool_decide (_ (T' + Δ)%Z _) as res_r...
      all: destruct_decide (bool_decide_reflect (T' ≤ z_l)%Z) as res_l.
      all: iFrame "rhs" ; iModIntro.
      + done.
      + exfalso. lia.
      + exfalso. lia.
      + done.
    }

    {
      iMod ecm_zero as "ε0".
      iApply (wp_couple_laplace (S:=Sg) T T 0%Z 0%Z ltac:(simpl ; lia) num (2*den)%Z
              with "[$rhs ε0]") => //.
      1: rewrite mult_IZR ; apply Rdiv_pos_pos. 1,2: real_solver.
      1: rewrite Rmult_0_l ; iFrame.
      iIntros (T') "!> rhs". tp_normalise...
      iModIntro. iExists _. iFrame "rhs". clear K.
      iIntros (DB dDB db db' adj) "%q %K q_sens rhs ε'"...

      tp_bind (q _) ; wp_bind (q _). rewrite /wp_sensitive.
      iSpecialize ("q_sens" $! HΔpos _ db db' with "rhs").

      iApply (wp_strong_mono'' with "q_sens [ε]") => //.
      iIntros (?) "(%vq_l & %vq_r & -> & rhs & %adj')".
      assert (- Δ <= vq_l - vq_r <= Δ)%Z as [adj_lb adj_ub].
      {
        assert (dZ vq_l vq_r <= IZR Δ) as h.
        { etrans; first apply adj'.
          rewrite -{2}(Rmult_1_r (IZR Δ)). apply Rmult_le_compat_l; [exact HΔpos|].
          etrans; first apply adj. lra. }
        revert h. rewrite /dZ/distance Rabs_Zabs.
        apply Zabs_ind ; intros ? h; split.
        all: pose proof (le_IZR _ _ h) ; lia.
      }
      lap_focus.
      iApply (wp_couple_laplace (S:=Sg) vq_l vq_r 0%Z Δ
              ltac:(apply Zabs_ind ; lia) num (4*den)%Z
              with "[$rhs ε]") => //.
      1: rewrite mult_IZR ; apply Rdiv_pos_pos. 1,2: real_solver.
      (* Actually, only half the error we have is needed. *)
      { subst ε. iApply ecm_weaken. 2: iFrame. rewrite mult_IZR. split.
        - apply Rmult_le_pos; [exact HΔpos|]. apply Rdiv_nneg_nneg ; lra.
        - apply Rmult_le_compat_l; [exact HΔpos|].
          rewrite (Rmult_comm 4). rewrite (Rmult_comm 2).
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
    Unshelve. all: try exact Sg.
  Qed.

  (* TODO move *)
  Lemma AT_NF_safe num den T :
    ⊢ WP (above_threshold #num #den #T) {{ v, ⌜True⌝ }}.
  Proof.
    rewrite /above_threshold.
  Admitted. (* TODO(port): Admitted in the original development. *)

End svt_pw.

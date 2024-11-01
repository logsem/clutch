From iris.proofmode Require Import base proofmode.
From iris.bi Require Export weakestpre fixpoint big_op.
From iris.base_logic.lib Require Import ghost_map invariants fancy_updates.
From iris.algebra Require Import excl.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.con_prob_lang Require Import erasure notation.
From clutch.common Require Export con_language sch_erasable.
From clutch.base_logic Require Import error_credits.
From clutch.coneris Require Import weakestpre primitive_laws.
From clutch.prob Require Import distribution.
Import uPred.

Notation con_prob_lang_mdp := (con_lang_mdp con_prob_lang).
(** Normal adequacy *)
Section adequacy.
  Context `{!conerisGS Σ}.
  
  Lemma step_fupd_fupdN_S n (P : iProp Σ) :  ((|={∅}▷=>^(S n) P) ⊣⊢ (|={∅}=> |={∅}▷=>^(S n) P))%I.
  Proof. iSplit; iIntros; simpl; iApply fupd_idemp; iFrame. Qed.
  
  Lemma pgl_dbind' `{Countable A, Countable A'}
    (f : A → distr A') (μ : distr A) (R : A → Prop) (T : A' → Prop) ε ε' n :
    ⌜ 0 <= ε ⌝ -∗
    ⌜ 0 <= ε' ⌝ -∗
    ⌜pgl μ R ε⌝ -∗
    (∀ a , ⌜R a⌝ ={∅}=∗ |={∅}▷=>^(n) ⌜pgl (f a) T ε'⌝) -∗
    |={∅}=> |={∅}▷=>^(n) ⌜pgl (dbind f μ) T (ε + ε')⌝ : iProp Σ.
  Proof.
    iIntros (???) "H".
    iApply (step_fupdN_mono _ _ _ (⌜(∀ a b, R a → pgl (f a) T ε')⌝)).
    { iIntros (?). iPureIntro. eapply pgl_dbind; eauto. }
    iIntros (???) "/=".
    iApply ("H" with "[//]"). 
  Qed.
  
  Lemma pgl_dbind_adv' `{Countable A, Countable A'}
    (f : A → distr A') (μ : distr A) (R : A → Prop) (T : A' → Prop) ε ε' n :
    ⌜ 0 <= ε ⌝ -∗
    ⌜ exists r, forall a, 0 <= ε' a <= r ⌝ -∗
    ⌜pgl μ R ε⌝ -∗
    (∀ a , ⌜R a⌝ ={∅}=∗ |={∅}▷=>^(n) ⌜pgl (f a) T (ε' a)⌝) -∗
    |={∅}=> |={∅}▷=>^(n) ⌜pgl (dbind f μ) T (ε + Expval μ ε')⌝ : iProp Σ.
  Proof.
    iIntros (???) "H".
    iApply (step_fupdN_mono _ _ _ (⌜(∀ a b, R a → pgl (f a) T (ε' a))⌝)).
    { iIntros (?). iPureIntro. eapply pgl_dbind_adv; eauto. }
    iIntros (???) "/=".
    iApply ("H" with "[//]").
  Qed.

  Lemma wp_adequacy_val_fupd `{Countable sch_int_state}  (ζ : sch_int_state) e es (sch: scheduler con_prob_lang_mdp sch_int_state) n v σ ε φ `{!TapeOblivious sch_int_state sch}:
    to_val e = Some v →
    state_interp σ ∗ err_interp ε ∗
    WP e {{ v, ⌜φ v ⌝ }} ⊢
    |={⊤, ∅}=> ⌜pgl (sch_exec sch n (ζ, (Val v :: es, σ))) φ ε⌝.
  Proof.
    iIntros (Hval) "(?&?&Hwp)".
    rewrite pgl_wp_unfold/pgl_wp_pre.
    iMod ("Hwp" with "[$]") as "H".
    simpl. rewrite Hval.
    iRevert (σ ε) "H".
    iApply state_step_coupl_ind.
    iModIntro.
    iIntros (??) "[%|[>(_&_&%)|[H|(%R&%μ&%&%&%Herasable&%&%Hineq&%Hpgl&H)]]]".
    - iPureIntro. by apply pgl_1.
    - iApply fupd_mask_intro; first done.
      iIntros "_".
      iPureIntro.
      erewrite sch_exec_is_final; last done.
      eapply pgl_mon_grading; last apply pgl_dret; auto.
    - iApply (fupd_mono _ _ (⌜_⌝)%I).
      { iPureIntro.
        intros H'.
        apply pgl_epsilon_limit; last exact.
        by apply Rle_ge. 
      }
      iIntros (ε' ?).
      unshelve iDestruct ("H" $! (mknonnegreal ε' _) with "[]") as "[H _]"; [|done..].
      pose proof cond_nonneg ε. lra.
    - erewrite <-Herasable; last done.
      iApply (fupd_mono _ _ (⌜_⌝)%I).
      { iPureIntro.
        intros H'.
        eapply pgl_mon_grading; first apply Hineq.
        eapply pgl_dbind_adv; [auto| |exact H'|exact].
        naive_solver.
      }
      iIntros (??).
      by iMod ("H" with "[//]") as "[? _]".
  Qed.

  Lemma state_step_coupl_erasure `{Countable sch_int_state} (ζ : sch_int_state) es σ ε Z n (sch: scheduler con_prob_lang_mdp sch_int_state) φ `{H0 : !TapeOblivious sch_int_state sch}:
    state_step_coupl σ ε Z -∗
    (∀ σ2 ε2, Z σ2 ε2 ={∅}=∗ |={∅}▷=>^(n)
                               ⌜pgl (sch_exec sch n (ζ, (es, σ2))) φ ε2⌝) -∗
    |={∅}=> |={∅}▷=>^(n)
             ⌜pgl (sch_exec sch n (ζ, (es, σ))) φ ε⌝.
  Proof.
    iRevert (σ ε).
    iApply state_step_coupl_ind.
    iIntros "!>" (σ ε) "[%|[?|[H|(%&%μ&%&%&%Herasable&%&%&%&H)]]] Hcont".
    - iApply step_fupdN_intro; first done.
      iPureIntro.
      by apply pgl_1.
    - by iMod ("Hcont" with "[$]").
    - iApply (step_fupdN_mono _ _ _ (⌜(∀ ε', _)⌝)).
      { iPureIntro.
        intros.
        apply pgl_epsilon_limit; [simpl; by apply Rle_ge|done].
      }
      iIntros (ε' ?).
      unshelve iDestruct ("H" $! (mknonnegreal ε' _) with "[]") as "[H _]";
        [pose proof cond_nonneg ε; simpl in *; lra|done|simpl].
      iApply ("H" with "[$]").
    - rewrite -Herasable.
      iApply (step_fupdN_mono _ _ _ (⌜pgl _ _ (_+_)⌝)%I).
      { iPureIntro.
        intros. eapply pgl_mon_grading; exact.
      }
      iApply (pgl_dbind_adv' with "[][][][-]"); [done|naive_solver|done|].
      iIntros (??).
      iMod ("H" with "[//]") as "[H _]".
      simpl.
      iApply ("H" with "[$]").
  Qed.

  Lemma state_step_coupl_erasure' `{Countable sch_int_state} (ζ : sch_int_state) e es e' σ ε Z n num (sch: scheduler con_prob_lang_mdp sch_int_state) φ `{!TapeOblivious sch_int_state sch}:
    ((e::es)!!num = Some e') ->
    to_val e = None ->
    to_val e' = None ->
    state_step_coupl σ ε Z -∗
    (∀ σ2 ε2, Z σ2 ε2 ={∅}=∗ |={∅}▷=>^(S n)
                               ⌜pgl (prim_step e' σ2 ≫= λ '(e3, σ3, efs), sch_exec sch n (ζ, (<[num:=e3]> (e :: es) ++ efs, σ3))) φ ε2⌝) -∗
    |={∅}=> |={∅}▷=>^(S n)
             ⌜pgl (prim_step e' σ ≫= λ '(e3, σ3, efs), sch_exec sch n (ζ, (<[num:=e3]> (e :: es) ++ efs, σ3))) φ ε⌝.
  Proof.
    intros ???.
    iRevert (σ ε).
    iApply state_step_coupl_ind.
    iIntros "!>" (σ ε) "[%|[?|[H|(%&%μ&%&%&%&%&%&%&H)]]] Hcont".
    - iApply step_fupdN_intro; first done.
      iPureIntro.
      by apply pgl_1.
    - by iMod ("Hcont" with "[$]").
    - iApply (step_fupdN_mono _ _ _ (⌜(∀ ε', _)⌝)).
      { iPureIntro.
        intros.
        apply pgl_epsilon_limit; [simpl; by apply Rle_ge|done].
      }
      iIntros (ε' ?).
      unshelve iDestruct ("H" $! (mknonnegreal ε' _) with "[]") as "[H _]";
        [pose proof cond_nonneg ε; simpl in *; lra|done|simpl].
      iApply ("H" with "[$]").
    - unshelve erewrite (Rcoupl_eq_elim _ _ (prim_coupl_step_prim_sch_erasable _ _ _ _ _ _ _ μ _ _ _ _)); [done..|].
      iApply (step_fupdN_mono _ _ _ (⌜pgl _ _ (_+_)⌝)%I).
      { iPureIntro.
        intros. eapply pgl_mon_grading; exact.
      }
      iApply (pgl_dbind_adv'); [done|naive_solver|done|].
      iIntros (??).
      iMod ("H" with "[//]") as "[H _]".
      simpl.
      iApply ("H" with "[$]").
  Qed.

  Lemma wp_refRcoupl_step_fupdN `{Countable sch_int_state} (ζ : sch_int_state) (ε : nonnegreal)
    (e : expr) es (σ : state) n φ (sch: scheduler con_prob_lang_mdp sch_int_state) `{!TapeOblivious sch_int_state sch}:
    state_interp σ ∗ err_interp (ε) ∗ WP e {{ v, ⌜φ v⌝ }}  ∗ ([∗ list] e'∈ es, WP e' {{ _, True%I }})  ⊢
    |={⊤,∅}=> |={∅}▷=>^n ⌜pgl (sch_exec sch n (ζ, (e::es, σ))) φ ε⌝.
  Proof.
    iInduction n as [|n] "IH" forall (ζ ε e es σ); iIntros "((Hσh & Hσt) & Hε & Hwp & Hwps)".
    - Local Transparent sch_exec.
      destruct (to_val e) eqn:Heq.
      + apply of_to_val in Heq as <-.
        iApply wp_adequacy_val_fupd; last iFrame.
        done.
      + rewrite /sch_exec /=.
        iApply fupd_mask_intro; [set_solver|]; iIntros "_".
        iPureIntro. rewrite Heq.
        apply pgl_dzero,
        Rle_ge,
        cond_nonneg.
    - rewrite sch_exec_Sn /sch_step_or_final/=.
      destruct (to_val e) eqn:Heq.
      + apply of_to_val in Heq as <-.
        rewrite dret_id_left'/=.
        iMod (wp_adequacy_val_fupd with "[$]") as "%"; first done.
        repeat iModIntro.
        by iApply step_fupdN_intro.
      + rewrite {1}/sch_step. rewrite <-dbind_assoc.
        replace (ε) with (0+ε)%NNR; last (apply nnreal_ext;simpl; lra).
        iApply fupd_mask_intro; first done.
        iIntros "Hclose".
        rewrite -fupd_idemp.
        iApply (pgl_dbind' _ _ _ _ _ _ (S _)); [done|
                             iPureIntro; apply cond_nonneg|
                             iPureIntro;apply pgl_trivial;simpl;lra|
                             ..].
        iIntros ([sch_σ sch_a] _).
        iMod "Hclose" as "_".
        simpl. rewrite Heq.
        destruct ((e::es)!!sch_a) as [chosen_e|] eqn:Hlookup; rewrite Hlookup; last first.
        { (* step a thread thats out of bounds *)
          rewrite dmap_dret dret_id_left'.
          iApply fupd_mask_intro; first done.
          iIntros "Hclose".
          do 2 iModIntro. iMod "Hclose" as "_".
          iApply "IH". iFrame.
          iApply ec_supply_eq; last done.
          simpl. lra.
        }
        case_match eqn:Hcheckval.
        { (* step a thread thats a value *)
          rewrite dmap_dret dret_id_left'.
          iApply fupd_mask_intro; first done.
          iIntros "Hclose".
          do 2 iModIntro. iMod "Hclose" as "_".
          iApply "IH". iFrame.
          iApply ec_supply_eq; last done.
          simpl. lra.
        }
        rewrite dmap_comp/dmap-dbind_assoc.
        erewrite (distr_ext _ _); last first.
        { intros x. erewrite (dbind_ext_right _ _ (λ '(_,_,_), _)); last first.
          - intros [[??]?].
            by rewrite dret_id_left/=.
          - done.
        }
        destruct sch_a as [|sch_a].
        *  (* step main thread *)
          rewrite pgl_wp_unfold /pgl_wp_pre. iSimpl in "Hwp". rewrite Heq.
          iMod ("Hwp" with "[$]") as "Hlift".
          replace (0+ε)%NNR with ε; [|apply nnreal_ext; simpl; lra].
          iApply (state_step_coupl_erasure' with "[$Hlift]"); [done..|].
          iIntros (σ2 ε2) "(%&%&%&%&%&%&%&H)".
          iApply (step_fupdN_mono _ _ _ (⌜pgl _ _ (_+_)⌝)%I).
          { iPureIntro.
            intros. eapply pgl_mon_grading; exact.
          }
          replace (chosen_e) with e; last by (simpl in Hlookup; simplify_eq).
          iApply (pgl_dbind_adv' with "[][][][-]"); [done|naive_solver|done|].
          iIntros ([[??]?]?).
          iMod ("H" with "[//]") as "H".
          simpl.
          do 3 iModIntro.
          iApply (state_step_coupl_erasure with "[$][-]").
          iIntros (??) ">(?&?&?&?)".
          iApply ("IH" with "[-]"). iFrame.
        * (* step other threads*)
          simpl in Hlookup.
          apply elem_of_list_split_length in Hlookup as (l1 & l2 & -> & ->).
          iDestruct "Hwps" as "[Hl1 [Hwp' Hl2]]".
          rewrite (pgl_wp_unfold _ _ chosen_e)/pgl_wp_pre.
          iSimpl in "Hwp'".
          rewrite Hcheckval.
          iMod ("Hwp'" with "[$]") as "Hlift".
          replace (0+ε)%NNR with ε; [|apply nnreal_ext; simpl; lra].
          iApply (state_step_coupl_erasure' _ e _ chosen_e with "[$]"); [|done..|].
          { simpl.
            rewrite lookup_app_r//.
            by replace (_-_)%nat with 0%nat by lia.
          }
          iIntros (σ2 ε2) "(%&%&%&%&%&%&%&H)".
          iApply (step_fupdN_mono _ _ _ (⌜pgl _ _ (_+_)⌝)%I).
          { iPureIntro.
            intros. eapply pgl_mon_grading; exact.
          }
          iApply (pgl_dbind_adv' with "[][][][-]"); [done|naive_solver|done|].
          iIntros ([[??]?]?).
          iMod ("H" with "[//]") as "H".
          simpl.
          do 3 iModIntro.
          iApply (state_step_coupl_erasure with "[$][-]").
          iIntros (??) ">(?&?&?&?)".
          iApply ("IH" with "[-]"). iFrame.
          rewrite insert_app_r_alt//.
          replace (_-_)%nat with 0%nat by lia.
          simpl.
          iFrame.
  Qed.

End adequacy.

Class conerisGpreS Σ := ConerisGpreS {
  conerisGpreS_iris  :: invGpreS Σ;
  conerisGpreS_heap  :: ghost_mapG Σ loc val;
  conerisGpreS_tapes :: ghost_mapG Σ loc tape;
  conerisGpreS_err   :: ecGpreS Σ;
}.

Definition conerisΣ : gFunctors :=
  #[invΣ; ghost_mapΣ loc val;
    ghost_mapΣ loc tape;
    GFunctor (authR nonnegrealUR)].
Global Instance subG_conerisGPreS {Σ} : subG conerisΣ Σ → conerisGpreS Σ.
Proof. solve_inG. Qed.

Theorem wp_pgl_multi Σ `{conerisGpreS Σ} `{Countable sch_int_state} (ζ : sch_int_state) n
  (e : expr) es (σ : state) (ε : R) (sch: scheduler con_prob_lang_mdp sch_int_state) φ `{!TapeOblivious sch_int_state sch}:
  0 <= ε →
  (∀ `{conerisGS Σ}, ⊢ ↯ ε -∗ (WP e {{ v, ⌜φ v⌝ }} ∗ [∗ list] e'∈ es, WP e' {{ _, True%I }})) →
  pgl (sch_exec sch n (ζ, (e::es, σ))) φ ε.
Proof.
  intros Hε Hwp.
  eapply pure_soundness, (step_fupdN_soundness_no_lc _ n 0).
  iIntros (Hinv) "_".
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh _]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht _]]".
  (* Handle the trivial 1 <= ε case *)
  destruct (decide (ε < 1)) as [Hcr|Hcr]; last first.
  { iClear "Hh Ht".
    iApply (fupd_mask_intro); [eauto|].
    iIntros "_".
    iApply step_fupdN_intro; [eauto|].
    iApply laterN_intro; iPureIntro.
    apply not_Rlt, Rge_le in Hcr.
    rewrite /pgl; intros.
    eapply Rle_trans; [eapply prob_le_1|done]. }
  set ε' := mknonnegreal _ Hε.
  iMod (ec_alloc ε') as (?) "[??]"; [done|].
  set (HclutchGS := HeapG Σ _ _ _ γH γT _).
  iApply (wp_refRcoupl_step_fupdN _ ε').
  iFrame. by iApply Hwp.
Qed.

Theorem wp_pgl Σ `{conerisGpreS Σ} `{Countable sch_int_state} (ζ : sch_int_state) n
  (e : expr) (σ : state) (ε : R) (sch: scheduler con_prob_lang_mdp sch_int_state) φ `{!TapeOblivious sch_int_state sch}:
  0 <= ε →
  (∀ `{conerisGS Σ}, ⊢ ↯ ε -∗ WP e {{ v, ⌜φ v⌝ }}) →
  pgl (sch_exec sch n (ζ, ([e], σ))) φ ε.
Proof.
  intros ? Hwp.
  eapply wp_pgl_multi; [done..|].
  simpl.
  iIntros.
  iSplitL; last done.
  by iApply Hwp.
Qed.

Lemma pgl_closed_lim `{Countable sch_int_state} (ζ : sch_int_state) (e : expr) (σ : state) (ε : R)
  (sch: scheduler con_prob_lang_mdp sch_int_state) φ `{!TapeOblivious sch_int_state sch}:
  (∀ n, pgl (sch_exec sch n (ζ, ([e], σ))) φ ε) →
  pgl (sch_lim_exec sch (ζ, ([e], σ))) φ ε .
Proof. intros Hn. by apply sch_lim_exec_continuous_prob. Qed.

Theorem wp_pgl_lim Σ `{conerisGpreS Σ} `{Countable sch_int_state} (ζ : sch_int_state)
  (e : expr) (σ : state) (ε : R) (sch: scheduler con_prob_lang_mdp sch_int_state) φ `{!TapeOblivious sch_int_state sch}:
  0 <= ε →
  (∀ `{conerisGS Σ}, ⊢ ↯ ε -∗ WP e {{ v, ⌜φ v⌝ }}) →
  pgl (sch_lim_exec sch (ζ, ([e], σ))) φ ε.
Proof.
  intros.
  apply pgl_closed_lim; first done.
  intros.
  by eapply wp_pgl.
Qed.


(** safety *)
Definition sch_mass_1 `{Countable sch_int_state} (sch: scheduler con_prob_lang_mdp sch_int_state) :=
  ∀ sch_cfg, SeriesC (sch sch_cfg)=1.

Section safety.
  Context `{!conerisGS Σ}.
  
  Lemma safety_dbind_adv `{Countable A, Countable A'}(h : A → distr A')
    (μ : distr A) ε (ε2 : A → R) R :
    SeriesC μ = 1  ->
    (exists r, forall a, 0 <= ε2(a) <= r) →
    pgl μ R ε ->
    (∀ a, R a -> SeriesC (h a) >= 1 - ε2 a) →
    SeriesC (μ ≫= h) >= 1 - (ε + Expval μ ε2).
  Proof.
    intros H' H1 Hpgl H2.
    rewrite dbind_mass/Expval.
    rewrite /pgl in Hpgl.
    setoid_rewrite <-SeriesC_scal_l.
    rewrite -H'.
    trans (SeriesC μ - ( prob μ (λ a : A, Datatypes.negb (bool_decide (R a))) + SeriesC (λ a : A, μ a * ε2 a))); last lra.
    replace (SeriesC μ) with (prob μ (λ a, bool_decide (R a))+prob μ (λ a, Datatypes.negb (bool_decide (R a)))); last first.
    { rewrite /prob. rewrite -SeriesC_plus.
      - apply SeriesC_ext. intros. case_bool_decide; simpl; lra.
      - apply ex_seriesC_filter_bool_pos; auto.
      - apply ex_seriesC_filter_bool_pos; auto.
    }
    rewrite Rminus_plus_r_l.
    rewrite /prob.
    rewrite Rminus_def.
    replace (-_) with (-1 * SeriesC (λ a, μ a * ε2 a)) by lra.
    rewrite -SeriesC_scal_l -SeriesC_plus; [|by apply ex_seriesC_filter_bool_pos|by apply ex_seriesC_scal_l, pmf_ex_seriesC_mult_fn].
    apply Rle_ge.
    rewrite Rcomplements.Rminus_le_0.
    rewrite Rminus_def.
    replace (-_) with (-1 * SeriesC (λ x : A, (if bool_decide (R x) then μ x else 0) + -1 * (μ x * ε2 x))) by lra.
    rewrite -SeriesC_scal_l -SeriesC_plus; last first.
    { apply ex_seriesC_scal_l, ex_seriesC_plus; first by apply ex_seriesC_filter_bool_pos.
      apply ex_seriesC_scal_l. by apply pmf_ex_seriesC_mult_fn.
    }
    { setoid_rewrite SeriesC_scal_l. apply pmf_ex_seriesC_mult_fn. naive_solver. }
    apply SeriesC_ge_0'.
    intros a.
    rewrite SeriesC_scal_l.
    case_bool_decide.
    - trans (μ a * (1 - ε2 a) - μ a + μ a * ε2 a); first lra.
      assert (μ a * (1 - ε2 a)<= μ a * SeriesC (h a)); last lra.
      apply Rmult_le_compat_l; first done.
      apply Rge_le.
      naive_solver.
    - apply Rplus_le_le_0_compat; first real_solver.
      assert (0<=μ a) by done.
      assert (0<=ε2 a) by naive_solver.
      rewrite Rmult_plus_distr_l -Rmult_assoc.
      replace (-1*-1) with 1 by lra.
      rewrite Rmult_0_r Rplus_0_l Rmult_1_l.
      real_solver.
  Qed.

  Lemma safety_dbind_adv' `{Countable A, Countable A'}(h : A → distr A')
    (μ : distr A) ε (ε2 : A → R) n R:
    ⌜SeriesC μ = 1 ⌝ -∗
    ⌜exists r, forall a, 0 <= ε2(a) <= r⌝ -∗
               ⌜pgl μ R ε⌝ -∗
               (∀ a, ⌜R a ⌝ ={∅}=∗ |={∅}▷=>^(n)⌜SeriesC (h a) >= 1 - ε2 a⌝) -∗
               |={∅}=> |={∅}▷=>^(n) ⌜SeriesC (μ ≫= h) >= 1 - (ε + Expval μ ε2)⌝ : iProp Σ.
  Proof.
    iIntros (???) "H".
    iApply (step_fupdN_mono _ _ _ (⌜(∀ a, R a -> SeriesC (h a) >= 1 - ε2 a)⌝)).
    { iPureIntro. intros. by eapply safety_dbind_adv. }
    iIntros (??).
    by iApply "H".
  Qed.

  Lemma safety_dbind' `{Countable A, Countable A'}(h : A → distr A')
    (μ : distr A) (ε : R) n:
    ⌜0 <= ε⌝ -∗
    ⌜SeriesC μ = 1 ⌝ -∗
    (∀ a, |={∅}▷=>^(n)⌜SeriesC (h a) >= 1 - ε⌝) -∗
    |={∅}=> |={∅}▷=>^(n) ⌜SeriesC (μ ≫= h) >= 1 - ε⌝ : iProp Σ.
  Proof.
    iIntros (? Hmass) "H".
    pose (ε' (a:A):= ε).
    assert (ε=0+Expval μ ε') as K.
    { rewrite /ε'. rewrite Expval_const; last done. rewrite Hmass. simpl. lra. }
    rewrite {2}K.
    iPoseProof (safety_dbind_adv' _ _ 0 ε' with "[][][][H]") as "K".
    - done.
    - iPureIntro. exists ε. intros. naive_solver.
    - iPureIntro. by apply pgl_trivial.
    - iIntros. rewrite /ε'. iApply "H".
    - rewrite /ε'.
      rewrite Expval_const; last done.
      by rewrite Hmass Rmult_1_r.
  Qed.

  Lemma state_step_coupl_erasure_safety `{Countable sch_int_state} (ζ : sch_int_state) es σ ε Z n (sch: scheduler con_prob_lang_mdp sch_int_state) `{H0 : !TapeOblivious sch_int_state sch}:
    state_step_coupl σ ε Z -∗
    (∀ σ2 ε2, Z σ2 ε2 ={∅}=∗ |={∅}▷=>^(n)
                               ⌜SeriesC (sch_pexec sch n (ζ, (es, σ2))) >= 1 - ε2⌝) -∗
    |={∅}=> |={∅}▷=>^(n)
             ⌜SeriesC (sch_pexec sch n (ζ, (es, σ))) >= 1- nonneg ε⌝.
  Proof.
  Admitted.

  Lemma state_step_coupl_erasure_safety' `{Countable sch_int_state} (ζ : sch_int_state) e es e' σ ε Z n num (sch: scheduler con_prob_lang_mdp sch_int_state) `{!TapeOblivious sch_int_state sch}:
    ((e::es)!!num = Some e') ->
    to_val e = None ->
    to_val e' = None ->
    state_step_coupl σ ε Z -∗
    (∀ σ2 ε2, Z σ2 ε2 ={∅}=∗ |={∅}▷=>^(S n)
                               ⌜SeriesC (prim_step e' σ2 ≫= λ '(e3, σ3, efs), sch_pexec sch n (ζ, (<[num:=e3]> (e :: es) ++ efs, σ3))) >=1- ε2⌝) -∗
    |={∅}=> |={∅}▷=>^(S n)
             ⌜SeriesC (prim_step e' σ ≫= λ '(e3, σ3, efs), sch_pexec sch n (ζ, (<[num:=e3]> (e :: es) ++ efs, σ3))) >= 1- nonneg ε⌝.
  Proof.
  Admitted.
  
  Lemma wp_safety_step_fupdN `{Countable sch_int_state} (ζ : sch_int_state) (ε : nonnegreal)
    (e : expr) es (σ : state) n φ (sch: scheduler con_prob_lang_mdp sch_int_state) `{!TapeOblivious sch_int_state sch}:
    sch_mass_1 sch->
    state_interp σ ∗ err_interp (ε) ∗ WP e {{ v, ⌜φ v⌝ }}  ∗ ([∗ list] e'∈ es, WP e' {{ _, True%I }})  ⊢
    |={⊤,∅}=> |={∅}▷=>^n ⌜SeriesC (sch_pexec sch n (ζ, (e::es, σ)))  >= 1 - ε⌝.
  Proof.
    intros Hmass.
    iInduction n as [|n] "IH" forall (ζ ε e es σ); iIntros "((Hσh & Hσt) & Hε & Hwp & Hwps)".
    - iApply (fupd_mask_intro); [eauto|].
      iIntros "_".
      iApply step_fupdN_intro; [eauto|].
      iPureIntro.
      rewrite sch_pexec_O dret_mass.
      pose proof cond_nonneg ε. simpl. lra.
    - rewrite sch_pexec_Sn /sch_step_or_final/=.
      case_match eqn:Hval.
      { erewrite SeriesC_ext; last (intros; by rewrite dret_id_left').
        iApply fupd_mask_intro; first done.
        iIntros "Hclose".
        do 2 iModIntro.
        iMod "Hclose". iApply "IH".
        iFrame.
      }
      rewrite /sch_step. rewrite <-dbind_assoc.
      iApply fupd_mask_intro; first done.
      iIntros "Hclose".
      rewrite -fupd_idemp.
      iApply (safety_dbind' _ _ _ (S _)); [done..|].
      iIntros ([ζ' thid]).
      simpl. rewrite Hval.
      destruct ((e::es)!!thid) as [chosen_e|] eqn:Hlookup; rewrite Hlookup; last first.
      { erewrite SeriesC_ext; last first.
        - intros.
          by rewrite dmap_dret dret_id_left'.
        - do 2 iModIntro. iMod "Hclose".
          iApply "IH". iFrame. }
      case_match eqn:Hcheckval.
      { erewrite SeriesC_ext; last first.
        - intros.
          by rewrite dmap_dret dret_id_left'.
        - do 2 iModIntro. iMod "Hclose".
          iApply "IH". iFrame. }
      rewrite dmap_comp/dmap-dbind_assoc.
      erewrite (distr_ext _ _); last first.
      { intros x. erewrite (dbind_ext_right _ _ (λ '(_,_,_), _)); last first.
        - intros [[??]?].
          by rewrite dret_id_left/=.
        - done. }
      destruct thid as [|thid].
      + iMod "Hclose". rewrite pgl_wp_unfold/pgl_wp_pre.
        iMod ("Hwp" with "[$]") as "Hwp".
        rewrite -fupd_idemp.
        iApply (state_step_coupl_erasure_safety'  with "[$Hwp]"); try done.
        iIntros (σ2 ε2). simpl. rewrite Hval.
        rewrite /prog_coupl.
        iIntros "(%R&%εa & %εb & %Hred &%Hbound & %Hineq & %Hpgl & Hlift)".
        assert (e = chosen_e) as ?; last simplify_eq.
        { simpl in Hlookup. by simplify_eq. }
        iApply (step_fupdN_mono _ _ _ (⌜SeriesC
           (prim_step chosen_e σ2 ≫= λ '(e3, σ3, efs), sch_pexec sch n (ζ', (e3 :: es ++ efs, σ3))) >=
                                         1 - (εa + Expval (prim_step chosen_e σ2) εb)⌝)).
        { iPureIntro. simpl in *.
          intros. etrans; first exact.
          apply Rle_ge.
          apply Ropp_le_cancel.
          rewrite !Ropp_minus_distr. by apply Rplus_le_compat_r. 
        }
        iApply (safety_dbind_adv' _ _ _ _ (S n) with "[][][]").
        * iPureIntro. eapply mixin_prim_step_mass; [apply con_language_mixin|done].
        * iPureIntro. naive_solver.
        * done.
        * iIntros (((e' & σ') & efs) HR).
          iMod ("Hlift" with "[//]").
          simpl.
          do 3 iModIntro.
          iApply (state_step_coupl_erasure_safety with "[$]").
          iIntros (??) ">(?&?&?&?)". iApply "IH". iFrame.
      + simpl in Hlookup.
        apply elem_of_list_split_length in Hlookup as (l1 & l2 & -> & ->).
        iDestruct "Hwps" as "[Hl1 [Hwp' Hl2]]".
        rewrite (pgl_wp_unfold _ _ chosen_e)/pgl_wp_pre.
        iSimpl in "Hwp'".
        rewrite Hcheckval.
        iMod "Hclose".
        iMod ("Hwp'" with "[$]") as "Hlift".
        rewrite -fupd_idemp.
        iApply (state_step_coupl_erasure_safety'  with "[$]"); try done.
        { simpl. by apply list_lookup_middle. }
        iIntros (σ2 ε2). simpl. rewrite /prog_coupl. 
        iIntros "(%R&%εa & %εb & %Hred &%Hbound & %Hineq & %Hpgl & Hlift)".
        iApply (step_fupdN_mono _ _ _ (⌜SeriesC
           (prim_step chosen_e σ2 ≫= λ '(e3, σ3, efs),
                 sch_pexec sch n (ζ', (e :: <[length l1:=e3]> (l1 ++ chosen_e :: l2) ++ efs, σ3))) >=
                                         1 - (εa + Expval (prim_step chosen_e σ2) εb)⌝)).
        { iPureIntro. simpl in *.
          intros. etrans; first exact.
          apply Rle_ge.
          apply Ropp_le_cancel.
          rewrite !Ropp_minus_distr. by apply Rplus_le_compat_r. }
        iApply (safety_dbind_adv' _ _ _ _ (S n) with "[][][]").
        * iPureIntro. eapply mixin_prim_step_mass; [apply con_language_mixin|done].
        * iPureIntro. naive_solver.
        * done.
        * iIntros (((e' & σ') & efs) HR).
          iMod ("Hlift" with "[//]").
          simpl.
          do 3 iModIntro.
          iApply (state_step_coupl_erasure_safety with "[$]").
          iIntros (??) ">(?&?&?&?)". iApply "IH". iFrame.
          rewrite insert_app_r_alt//.
          replace (_-_)%nat with 0%nat by lia.
          simpl. iFrame.
  Qed.
  
End safety.


Theorem wp_safety_multi Σ `{conerisGpreS Σ} `{Countable sch_int_state} (ζ : sch_int_state) n
  (e : expr) es (σ : state) (ε : R) (sch: scheduler con_prob_lang_mdp sch_int_state) φ `{!TapeOblivious sch_int_state sch}:
  0 <= ε →
  sch_mass_1 sch ->
  (∀ `{conerisGS Σ}, ⊢ ↯ ε -∗ (WP e {{ v, ⌜φ v⌝ }} ∗ [∗ list] e'∈ es, WP e' {{ _, True%I }})) →
  SeriesC (sch_pexec sch n (ζ, (e::es, σ)))  >= 1 - ε.
Proof.
  intros Hε Hmass Hwp.
  eapply pure_soundness, (step_fupdN_soundness_no_lc _ n 0).
  iIntros (Hinv) "_".
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh _]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht _]]".
  (* Handle the trivial 1 <= ε case *)
  destruct (decide (ε < 1)) as [Hcr|Hcr]; last first.
  { iClear "Hh Ht".
    iApply (fupd_mask_intro); [eauto|].
    iIntros "_".
    iApply step_fupdN_intro; [eauto|].
    iApply laterN_intro; iPureIntro.
    trans 0; [by apply Rle_ge, SeriesC_ge_0|lra].
  }
  set ε' := mknonnegreal _ Hε.
  iMod (ec_alloc ε') as (?) "[??]"; [done|].
  set (HclutchGS := HeapG Σ _ _ _ γH γT _).
  iApply (wp_safety_step_fupdN _ ε'); first done.
  iFrame. by iApply Hwp.
Qed.

Theorem wp_safety Σ `{conerisGpreS Σ} `{Countable sch_int_state} (ζ : sch_int_state)
  (e : expr) (σ : state) (ε : R) n (sch: scheduler con_prob_lang_mdp sch_int_state) φ `{!TapeOblivious sch_int_state sch}:
  0 <= ε →
  sch_mass_1 sch ->
  (∀ `{conerisGS Σ}, ⊢ ↯ ε -∗ WP e {{ v, ⌜φ v⌝ }}) →
  SeriesC (sch_pexec sch n (ζ, ([e], σ)))  >= 1 - ε.
Proof.
  iIntros (Hε Hmass Hwp).
  eapply wp_safety_multi; [done..|].
  iIntros.
  iSplitL; last done.
  by iApply Hwp.
Qed.


(* Definition sch_reducible `{Countable sch_int_state} (sch: scheduler con_prob_lang_mdp sch_int_state) (ζ : sch_int_state) ρ:= *)
(*   ∀ x, sch (ζ, ρ) x > 0 -> SeriesC (step x.2 ρ) >0. *)
  
(* Lemma sch_pexec_safety_relate `{Countable sch_int_state} (sch: scheduler con_prob_lang_mdp sch_int_state) (ζ : sch_int_state) ρ n: *)
(*   sch_mass_1 sch -> *)
(*   probp (sch_pexec sch n (ζ, ρ)) (λ '(ζ', ρ), (is_final ρ ∨ sch_reducible sch ζ' ρ)) = *)
(*   SeriesC (sch_pexec sch (S n) (ζ, ρ)). *)
(* Proof. *)
(*   intros Hmass. *)
(*   revert ζ ρ. *)
(*   induction n; intros ζ ρ. *)
(*   { rewrite sch_pexec_O sch_pexec_1/sch_step_or_final. *)
(*     case_match. *)
(*     - rewrite dret_mass. *)
(*       rewrite probp_dret_true; first done. *)
(*       left. *)
(*       rewrite /is_final. naive_solver. *)
(*     - destruct (decide (sch_reducible sch ζ ρ)). *)
(*       + rewrite probp_dret_true; last naive_solver. *)
(*         rewrite /sch_step. *)
(*         rewrite dbind_mass. *)
(*         erewrite (SeriesC_ext _ (λ a, sch (ζ, ρ) a)); first by rewrite Hmass. *)
(*         intros [ζ' ac']. *)
(*         destruct (pmf_pos (sch (ζ, ρ)) (ζ', ac')) as [K' | <-]; last lra. *)
(*         rewrite dmap_mass.  *)
(*         rewrite /sch_reducible in s. *)
(*         unshelve epose proof s (ζ', ac') _ as H1; first lra. *)
(*         rewrite /=/con_lang_mdp_step in H1. *)
(*         rewrite /=/con_lang_mdp_step. *)
(*         destruct ρ. *)
(*         case_match. *)
(*         { simpl in *. *)
(*           rewrite dzero_mass in H1; lra. *)
(*         } *)
(*         case_match; last (rewrite dret_mass; lra). *)
(*         case_match; first (rewrite dret_mass; lra). *)
(*         rewrite dmap_mass. *)
(*         erewrite mixin_prim_step_mass; [lra|apply con_language_mixin|]. *)
(*         unshelve epose proof SeriesC_gtz_ex _ _ H1 as [? H5]; first by intros. *)
(*         rewrite dmap_pos in H5. destruct H5 as [?[->?]]. *)
(*         clear -H5. *)
(*         naive_solver. *)
(*       + rewrite probp_dret_false; last first. *)
(*         { rewrite /is_final. intros [[??]|]; naive_solver. } *)
(*         rewrite /sch_reducible in n. *)
(*         symmetry. apply SeriesC_0. *)
(*         intros [ζ' cfg]. *)
(*         rewrite /sch_step. *)
(*         rewrite dbind_unfold_pmf. *)
(*         apply SeriesC_0. *)
(*         intros [ζ'' ac']. *)
(*         rewrite dmap_unfold_pmf/=. *)
(*         destruct (pmf_pos (sch (ζ, ρ)) (ζ'', ac')) as [|H1]; last (rewrite -H1; lra). *)
(*         rewrite SeriesC_0; first lra. *)
(*         intros ρ'. *)
(*         case_bool_decide; last lra. *)
(*         simplify_eq. *)
(*         destruct (pmf_pos (con_lang_mdp_step con_prob_lang ac' ρ) ρ') as [|H2]; last (rewrite -H2; lra). *)
(*         exfalso. *)
(*         apply n. *)
        
(*   }  *)
(* Admitted. *)

(* Corollary wp_safety' Σ `{conerisGpreS Σ} `{Countable sch_int_state} (ζ : sch_int_state) *)
(*   (e : expr) (σ : state) (ε : R) n (sch: scheduler con_prob_lang_mdp sch_int_state) φ `{!TapeOblivious sch_int_state sch}: *)
(*   0 <= ε → *)
(*   sch_mass_1 sch -> *)
(*   (∀ `{conerisGS Σ}, ⊢ ↯ ε -∗ WP e {{ v, ⌜φ v⌝ }}) → *)
(*   probp (sch_pexec sch n (ζ, ([e], σ))) *)
(*     (λ '(ζ', ρ), is_final ρ \/ *)
(*                    sch_reducible sch ζ' ρ *)
(*     ) >= 1 - ε. *)
(* Proof. *)
(*   intros Hε Hmass Hwp. *)
(*   rewrite sch_pexec_safety_relate. *)
(*   by eapply wp_safety. *)
(* Qed. *)

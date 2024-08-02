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

Section adequacy.
  Context `{!conerisGS Σ}.

  Lemma pgl_dbind' `{Countable A, Countable A'}
    (f : A → distr A') (μ : distr A) (R : A → Prop) (T : A' → Prop) ε ε' n :
    ⌜ 0 <= ε ⌝ -∗
    ⌜ 0 <= ε' ⌝ -∗
    ⌜pgl μ R ε⌝ -∗
    (∀ a , ⌜R a⌝ ={∅}▷=∗^(S n) ⌜pgl (f a) T ε'⌝) -∗
    |={∅}▷=>^(S n) ⌜pgl (dbind f μ) T (ε + ε')⌝ : iProp Σ.
  Proof.
    iIntros (???) "H".
    iApply (step_fupdN_mono _ _ _ (⌜(∀ a b, R a → pgl (f a) T ε')⌝)).
    { iIntros (?). iPureIntro. eapply pgl_dbind; eauto. }
    iIntros (???) "/=".
    iMod ("H" with "[//]"); auto.
  Qed.

  Lemma wp_refRcoupl_step_fupdN `{Countable sch_int_state} (ζ : sch_int_state) (ε : nonnegreal)
    (e : expr) es (σ : state) n φ (sch: scheduler con_prob_lang_mdp sch_int_state):
    state_interp σ ∗ err_interp (ε) ∗ WP e {{ v, ⌜φ v⌝ }}  ∗ ([∗ list] e'∈ es, WP e' {{ _, True%I }})  ⊢
    |={⊤,∅}=> |={∅}▷=>^n ⌜pgl (sch_exec sch n (ζ, (e::es, σ))) φ ε⌝.
  Proof.
    iInduction n as [|n] "IH" forall (ζ ε e es σ); iIntros "((Hσh & Hσt) & Hε & Hwp & Hwps)".
    - rewrite /sch_exec /=.
      destruct (to_val e) eqn:Heq.
      + apply of_to_val in Heq as <-.
        rewrite pgl_wp_value_fupd.
        iMod "Hwp" as "%".
        iApply fupd_mask_intro; [set_solver|]; iIntros.
        iPureIntro.
        apply (pgl_mon_grading _ _ 0); [apply cond_nonneg | ].
        apply pgl_dret; auto.
      + iApply fupd_mask_intro; [set_solver|]; iIntros "_".
        iPureIntro.
        apply pgl_dzero,
        Rle_ge,
        cond_nonneg.
    - rewrite sch_exec_Sn /sch_step_or_final/=.
      destruct (to_val e) eqn:Heq.
      + apply of_to_val in Heq as <-.
        rewrite pgl_wp_value_fupd.
        iMod "Hwp" as "%".
        iApply fupd_mask_intro; [set_solver|]; iIntros "_".
        iApply step_fupdN_intro; [done|]. do 4 iModIntro.
        iPureIntro.
        rewrite dret_id_left'/=.
        erewrite sch_exec_is_final; last done.
        apply (pgl_mon_grading _ _ 0); [apply cond_nonneg | ].
        apply pgl_dret; auto.
      + rewrite /sch_step. rewrite -dbind_assoc.
        replace (ε) with (0+ε)%NNR; last (apply nnreal_ext;simpl; lra).
        iApply pgl_dbind'; [done|
                             iPureIntro; apply cond_nonneg|
                             iPureIntro;apply pgl_trivial;simpl;lra|
                             ..].
        (* OK This doesnt work*)
        (* iIntros (? _). *)
  Admitted.
  
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
  (e : expr) es (σ : state) (ε : R) (sch: scheduler con_prob_lang_mdp sch_int_state) φ :
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
  (e : expr) (σ : state) (ε : R) (sch: scheduler con_prob_lang_mdp sch_int_state) φ :
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
  (sch: scheduler con_prob_lang_mdp sch_int_state) φ :
  (∀ n, pgl (sch_exec sch n (ζ, ([e], σ))) φ ε) →
  pgl (sch_lim_exec sch (ζ, ([e], σ))) φ ε .
Proof. intros Hn. by apply sch_lim_exec_continuous_prob. Qed.

Theorem wp_pgl_lim Σ `{conerisGpreS Σ} `{Countable sch_int_state} (ζ : sch_int_state)
  (e : expr) (σ : state) (ε : R) (sch: scheduler con_prob_lang_mdp sch_int_state) φ :
  0 <= ε →
  (∀ `{conerisGS Σ}, ⊢ ↯ ε -∗ WP e {{ v, ⌜φ v⌝ }}) →
  pgl (sch_lim_exec sch (ζ, ([e], σ))) φ ε.
Proof.
  intros.
  apply pgl_closed_lim.
  intros.
  by eapply wp_pgl.
Qed.

(* TODO limit stronger adequacy*)

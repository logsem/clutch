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
  
  Lemma step_fupd_fupdN_S n (P : iProp Σ) :  ((|={∅}▷=>^(S n) P) ⊣⊢ (|={∅}=> |={∅}▷=>^(S n) P))%I.
  Proof. iSplit; iIntros; simpl; iApply fupd_idemp; iFrame. Qed.
  
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
  
  Lemma pgl_dbind_adv' `{Countable A, Countable A'}
    (f : A → distr A') (μ : distr A) (R : A → Prop) (T : A' → Prop) ε ε' n :
    ⌜ 0 <= ε ⌝ -∗
    ⌜ exists r, forall a, 0 <= ε' a <= r ⌝ -∗
    ⌜pgl μ R ε⌝ -∗
    (∀ a , ⌜R a⌝ ={∅}▷=∗^(S n) ⌜pgl (f a) T (ε' a)⌝) -∗
    |={∅}▷=>^(S n) ⌜pgl (dbind f μ) T (ε + Expval μ ε')⌝ : iProp Σ.
  Proof.
    iIntros (???) "H".
    iApply (step_fupdN_mono _ _ _ (⌜(∀ a b, R a → pgl (f a) T (ε' a))⌝)).
    { iIntros (?). iPureIntro. eapply pgl_dbind_adv; eauto. }
    iIntros (???) "/=".
    iMod ("H" with "[//]"); auto.
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
    iIntros (??) "[%|[>(_&_&%)|(%R&%μ&%&%&%Herasable&%&%Hineq&%Hpgl&H)]]".
    - iPureIntro. by apply pgl_1.
    - iApply fupd_mask_intro; first done.
      iIntros "_".
      iPureIntro.
      erewrite sch_exec_is_final; last done.
      eapply pgl_mon_grading; last apply pgl_dret; auto.
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

  Lemma state_step_coupl_erasure `{Countable sch_int_state} (ζ : sch_int_state) es σ ε Z n (sch: scheduler con_prob_lang_mdp sch_int_state) φ `{!TapeOblivious sch_int_state sch}:
    state_step_coupl σ ε Z -∗
    (∀ σ2 ε2, Z σ2 ε2 ={∅}=∗ |={∅}▷=>^(n)
                               ⌜pgl (sch_exec sch n (ζ, (es, σ2))) φ ε2⌝) -∗
    |={∅}=> |={∅}▷=>^(n)
             ⌜pgl (sch_exec sch n (ζ, (es, σ))) φ ε⌝.
  Proof.
    iRevert (σ ε).
    iApply state_step_coupl_ind.
    iIntros "!>" (σ ε) "[%|[?|(%&%μ&%&%&%&%&%&%&H)]] Hcont".
  Admitted.

  Lemma state_step_coupl_erasure' `{Countable sch_int_state} (ζ : sch_int_state) e es e' σ ε Z n num (sch: scheduler con_prob_lang_mdp sch_int_state) φ `{!TapeOblivious sch_int_state sch}:
    state_step_coupl σ ε Z -∗
    ⌜((e::es)!!num = Some e')⌝ -∗
    ⌜to_val e = None⌝ -∗
    ⌜to_val e' = None⌝ -∗
    (∀ σ2 ε2, Z σ2 ε2 ={∅}=∗ |={∅}▷=>^(S n)
                               ⌜pgl (prim_step e' σ2 ≫= λ '(e3, σ3, efs), sch_exec sch n (ζ, (<[num:=e3]> (e :: es) ++ efs, σ3))) φ ε2⌝) -∗
    |={∅}=> |={∅}▷=>^(S n)
             ⌜pgl (prim_step e' σ ≫= λ '(e3, σ3, efs), sch_exec sch n (ζ, (<[num:=e3]> (e :: es) ++ efs, σ3))) φ ε⌝.
  Proof.
    iRevert (σ ε).
    iApply state_step_coupl_ind.
    iIntros "!>" (σ ε) "[%|[?|(%&%μ&%&%&%&%&%&%&H)]] Hcont".
  Admitted.

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
        iApply pgl_dbind'; [done|
                             iPureIntro; apply cond_nonneg|
                             iPureIntro;apply pgl_trivial;simpl;lra|
                             ..].
        iApply fupd_mask_intro; first done.
        iIntros "Hclose".
        iIntros ([sch_σ sch_a] _).
        rewrite step_fupd_fupdN_S.
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
          iApply (state_step_coupl_erasure' with "[$][//][//][//]").
          iIntros (σ2 ε2) "(%&%&%&%&%&%&%&H)".
          iApply (step_fupdN_mono _ _ _ (⌜pgl _ _ (_+_)⌝)%I).
          { iPureIntro.
            intros. eapply pgl_mon_grading; exact.
          }
          replace (chosen_e) with e; last by (simpl in Hlookup; simplify_eq).
          iApply (pgl_dbind_adv' with "[][][][-]"); [done|naive_solver|done|].
          iIntros ([[??]?]?).
          rewrite step_fupd_fupdN_S.
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
          iApply (state_step_coupl_erasure' _ e _ chosen_e with "[$][][//][//]").
          { simpl.
            iPureIntro. rewrite lookup_app_r//.
            by replace (_-_)%nat with 0%nat by lia.
          } 
          iIntros (σ2 ε2) "(%&%&%&%&%&%&%&H)".
          iApply (step_fupdN_mono _ _ _ (⌜pgl _ _ (_+_)⌝)%I).
          { iPureIntro.
            intros. eapply pgl_mon_grading; exact.
          }
          iApply (pgl_dbind_adv' with "[][][][-]"); [done|naive_solver|done|].
          iIntros ([[??]?]?).
          rewrite step_fupd_fupdN_S.
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

(* TODO limit stronger adequacy*)

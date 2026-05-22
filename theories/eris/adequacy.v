From iris.proofmode Require Import base proofmode.
From iris.bi Require Export lib.fixpoint_mono big_op.
From iris.base_logic.lib Require Import ghost_map invariants fancy_updates.
From iris.algebra Require Import excl.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.prob_lang Require Import erasure notation.
From clutch.common Require Export language erasable exec.
From clutch.base_logic Require Import error_credits.
From clutch.eris Require Import weakestpre primitive_laws.
From clutch.prob Require Import distribution.
Import uPred.

Section adequacy.
  Context `{!erisGS Σ}.

  (** Pure-monotonicity through [▷^k ◇ ⌜·⌝]. *)
  Local Lemma laterN_except_0_pure_mono k (P Q : Prop) :
    (P → Q) → ((▷^k ◇ ⌜P⌝ : iProp Σ)%I ⊢ ▷^k ◇ ⌜Q⌝).
  Proof. intros HPQ. apply bi.laterN_mono, bi.except_0_mono, bi.pure_mono, HPQ. Qed.

  (** Push [∀] through [|={∅}▷=>^n] of plain pure props (via [fupd_finally]). *)
  Lemma step_fupdN_pure_forall_intro {A} (Φ : A → Prop) n E :
    (∀ a, |={E|}=> ▷^n ◇ ⌜Φ a⌝) ⊢ |={E|}=> ▷^n ◇ ⌜∀ a, Φ a⌝ : iProp Σ.
  Proof.
    iIntros "H".
    iApply (fupd_finally_mono _ _ (▷^n ◇ ⌜∀ a, Φ a⌝)%I); last first.
    { iApply fupd_finally_forall. iIntros (a). iApply "H". }
    rewrite -laterN_forall. apply bi.laterN_mono.
    rewrite -except_0_forall. apply bi.except_0_mono.
    apply pure_forall_2.
  Qed.

  Lemma pgl_dbind' `{Countable A, Countable A'}
    (f : A → distr A') (μ : distr A) (R : A → Prop) (T : A' → Prop) ε ε' n :
    ⌜ 0 <= ε ⌝ -∗
    ⌜ 0 <= ε' ⌝ -∗
    ⌜pgl μ R ε⌝ -∗
    (∀ a, ⌜R a⌝ -∗ |={∅|}=> ▷^(S n) ◇ ⌜pgl (f a) T ε'⌝) -∗
    |={∅|}=> ▷^(S n) ◇ ⌜pgl (dbind f μ) T (ε + ε')⌝.
  Proof.
    iIntros (Hε Hε' Hpgl) "H".
    iAssert (∀ a, |={∅|}=> ▷^(S n) ◇ ⌜R a → pgl (f a) T ε'⌝)%I with "[H]" as "H".
    { iIntros (a). destruct (ExcludedMiddle (R a)) as [HR|HnR].
      - iSpecialize ("H" $! a with "[//]").
        iApply (fupd_finally_mono with "H").
        apply (laterN_except_0_pure_mono (S n)). by intros.
      - iApply fupd_finally_intro. iPureIntro. by intros. }
    iPoseProof (step_fupdN_pure_forall_intro _ (S n) ∅ with "H") as "H".
    iApply (fupd_finally_mono with "H").
    apply (laterN_except_0_pure_mono (S n)). intros Hall.
    eapply pgl_dbind; eauto.
  Qed.

  Lemma pgl_dbind_adv' `{Countable A, Countable A'}
    (f : A → distr A') (μ : distr A) (R : A → Prop) (T : A' → Prop) ε ε' n :
    ⌜ 0 <= ε ⌝ -∗
    ⌜ exists r, forall a, 0 <= ε' a <= r ⌝ -∗
    ⌜pgl μ R ε⌝ -∗
    (∀ a, ⌜R a⌝ -∗ |={∅|}=> ▷^(S n) ◇ ⌜pgl (f a) T (ε' a)⌝) -∗
    |={∅|}=> ▷^(S n) ◇ ⌜pgl (dbind f μ) T (ε + SeriesC (λ a : A, (μ a * ε' a)%R))⌝.
  Proof.
    iIntros (Hε [r Hr] Hpgl) "H".
    iAssert (∀ a, |={∅|}=> ▷^(S n) ◇ ⌜R a → pgl (f a) T (ε' a)⌝)%I with "[H]" as "H".
    { iIntros (a). destruct (ExcludedMiddle (R a)) as [HR|HnR].
      - iSpecialize ("H" $! a with "[//]").
        iApply (fupd_finally_mono with "H").
        apply (laterN_except_0_pure_mono (S n)). by intros.
      - iApply fupd_finally_intro. iPureIntro. by intros. }
    iPoseProof (step_fupdN_pure_forall_intro _ (S n) ∅ with "H") as "H".
    iApply (fupd_finally_mono with "H").
    apply (laterN_except_0_pure_mono (S n)). intros Hall.
    eapply pgl_dbind_adv; [done|exists r; done|done|done].
  Qed.

  Local Definition cfgO := (prodO exprO stateO).

  (** ** Compatibility shims for the old [|={l; E|}=> ▷^k ◇ P] (hfupd)
       interface, expressed in terms of the new [fupd_finally] modality
       [|={E|}=> ▷^k ◇ P].  These keep the call sites below close to their
       pre-MR-1217 form. *)

  Notation hfupd_mono := fupd_finally_mono (only parsing).

  Lemma hfupd_intro {E} (P : iProp Σ) `{!Plain P} :
    P -∗ |={E|}=> P.
  Proof.
    iIntros "HP".
    iAssert (■ P)%I with "[HP]" as "#HP'"; [by iApply plain_plainly|].
    by iApply fupd_finally_intro.
  Qed.

  Lemma hfupd_intro_pure {E n} (φ : Prop) :
    φ → ⊢ |={E|}=> ▷^n ◇ ⌜φ⌝ : iProp Σ.
  Proof.
    intros Hφ. iApply fupd_finally_intro. by iPureIntro.
  Qed.

  Lemma laterN_hfupd l {E} k (P : iProp Σ) :
    ▷^l (|={E|}=> ▷^k ◇ P) ⊢ |={E|}=> ▷^(l + k) ◇ P.
  Proof.
    induction l as [|l IH]; simpl.
    - iIntros "H". by iApply (fupd_finally_mono with "H").
    - iIntros "H". rewrite IH. rewrite fupd_finally_later.
      iApply (fupd_finally_mono with "H"). iIntros "H".
      by rewrite except_0_laterN except_0_idemp.
  Qed.

  Lemma elim_fupd_hfupd_plain (k l : nat) (E1 E2 : coPset) (P Q : iProp Σ) :
    l ≤ k →
    (|={E1, E2}=> P) ∗ (∀ l', ⌜l' = l⌝ -∗ P -∗ |={E2|}=> ▷^(k - l') ◇ Q)
    ⊢ |={E1|}=> ▷^k ◇ Q.
  Proof.
    iIntros (Hlk) "[H1 H2]". iMod "H1" as "HP".
    iSpecialize ("H2" $! l with "[//] HP").
    iApply (fupd_finally_mono with "H2").
    replace k with (l + (k - l))%nat at 2 by lia.
    rewrite laterN_add. iIntros "H". by iApply laterN_intro.
  Qed.

  Lemma fupd_plain_hfupd' (l : nat) (E1 E2 : coPset) {P : iProp Σ} `{!Plain P} :
    (|={E1, E2}=> P) ⊢ |={E1|}=> ▷^l ◇ P.
  Proof.
    iIntros "H". iMod "H" as "HP". by iApply hfupd_intro.
  Qed.

  (** [glm_erasure] in fupd_finally form. *)
  Lemma glm_erasure (e : expr) (σ : state) (n : nat) φ (ε : nonnegreal) :
    to_val e = None →
    glm e σ ε (λ '(e2, σ2) ε',
        |={∅|}=> ▷^(S n) ◇ ⌜pgl (exec n (e2, σ2)) φ ε'⌝)
      ⊢ |={∅|}=> ▷^(S n) ◇ ⌜pgl (exec (S n) (e, σ)) φ ε⌝.
  Proof.
    iIntros (Hv) "Hexec".
    iAssert (⌜to_val e = None⌝)%I as "-#H"; [done|]. iRevert "Hexec H".
    rewrite /glm /glm'.
    set (Φ := (λ '((e1, σ1), ε''),
                (⌜to_val e1 = None⌝ -∗
                  |={∅|}=> ▷^(S n) ◇ ⌜pgl (exec (S n) (e1, σ1)) φ ε''⌝)%I) :
           prodO cfgO NNRO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros m ((?&?)&?) ((?&?)&?) [[[=] [=]] [=]]. by simplify_eq. }
    set (F := (glm_pre (λ '(e2, σ2) ε',
                   |={∅|}=> ▷^(S n) ◇ ⌜pgl (exec n (e2, σ2)) φ ε'⌝)%I)).
    iPoseProof (least_fixpoint_iter F Φ with "[]") as "H"; last first.
    { iIntros "Hfix %".
      by iApply ("H" $! ((_, _)) with "Hfix"). }
    clear Hv.
    iIntros "!#" ([[e1 σ1] ε'']). rewrite /Φ/F/glm_pre.
    iIntros " [H | [ (%R & %ε1 & %ε2 & %Hred & (%r & %Hr) & %Hsum & %Hlift & H)|H]] %Hv".

    (* Case 1: thin air ε-inflation. Mirrors the original step_fupdN proof,
       with [hfupd_mono] doing the role of [step_fupdN_mono] and
       [elim_fupd_hfupd_plain] doing the role of [step_fupd_fupdN_S; iMod ...]. *)
    - iApply (hfupd_mono _ (▷^(S n) ◇ ⌜∀ ε' : nonnegreal,
          (ε'' < ε')%R → pgl (exec (S n) (e1, σ1)) φ ε'⌝)%I).
      { apply (laterN_except_0_pure_mono (S n)). intros Hall.
        eapply pgl_epsilon_limit; auto.
        - apply Rle_ge, cond_nonneg.
        - intros ε' Hε'.
          apply (Hall (mknonnegreal ε' (Rle_trans _ _ _ (cond_nonneg _) (Rlt_le _ _ Hε'))) Hε'). }
      iIntros (ε' Hε').
      destruct (decide (ε' < 1)%R) as [Hε'1|Hε'1]; last first.
      { iApply hfupd_intro. iApply laterN_intro.
        rewrite /bi_except_0. iRight. iPureIntro. apply pgl_1. lra. }
      iApply (elim_fupd_hfupd_plain (S n) 0 ∅ ∅ _
        ⌜pgl (exec (S n) (e1, σ1)) φ ε'⌝); [lia|].
      iSplitL "H"; [iApply ("H" $! ε' with "[//]")|].
      iIntros (l Hl) "Hst". assert (l = 0%nat) as -> by lia.
      try rewrite Nat.add_0_r; replace (S n - 0)%nat with (S n) by lia.
      iDestruct "Hst" as "(%R' & %ε1' & %ε2' & %Hsum' & %Hlift' & Hwand')".
      rewrite -(dret_id_left' (λ _ : (), exec (S n) (e1, σ1)) tt).
      iApply (hfupd_mono _
        (▷^(S n) ◇ ⌜pgl (dret tt ≫= λ _ : (), exec (S n) (e1, σ1)) φ (ε1' + ε2')⌝)%I).
      { apply (laterN_except_0_pure_mono (S n)).
        intros Hpgl. eapply pgl_mon_grading; [|exact Hpgl]. exact Hsum'. }
      iApply (pgl_dbind' _ (dret tt) R' (λ x, φ x) ε1' ε2' n).
      { iPureIntro. apply cond_nonneg. }
      { iPureIntro. apply cond_nonneg. }
      { iPureIntro. apply tgl_implies_pgl, Hlift'. }
      iIntros (a HRa). destruct a.
      iSpecialize ("Hwand'" with "[//]").
      iSpecialize ("Hwand'" with "[//]").
      rewrite dret_id_left.
      iApply "Hwand'".

    (* Case 2: prim_step with adv composition. *)
    - rewrite exec_Sn_not_final; [|by rewrite /is_final /= Hv].
      iApply (hfupd_mono _ (▷^(S n) ◇ ⌜pgl (prim_step e1 σ1 ≫= exec n) φ
        (ε1 + SeriesC (λ ρ, (prim_step e1 σ1 ρ) * ε2 ρ))%R⌝)%I).
      { apply (laterN_except_0_pure_mono (S n)). intros Hpgl.
        eapply pgl_mon_grading; [|exact Hpgl]. done. }
      iApply pgl_dbind_adv'.
      { iPureIntro. apply cond_nonneg. }
      { iPureIntro. exists r. intros a. split; [apply cond_nonneg | apply Hr]. }
      { done. }
      iIntros ([e' σ'] HRes).
      iApply (elim_fupd_hfupd_plain (S n) 0 ∅ ∅ _
        ⌜pgl (exec n (e', σ')) φ (ε2 (e', σ'))⌝); [lia|].
      iSplitL "H"; [iApply ("H" with "[//]")|].
      iIntros (l Hl) "Hst". assert (l = 0%nat) as -> by lia.
      try rewrite Nat.add_0_r; replace (S n - 0)%nat with (S n) by lia.
      iDestruct "Hst" as "(%R' & %ε1' & %ε2' & %Hsum' & %Hlift' & Hwand')".
      rewrite -(dret_id_left' (λ _ : (), exec n (e', σ')) tt).
      iApply (hfupd_mono _ (▷^(S n) ◇
        ⌜pgl (dret tt ≫= λ _ : (), exec n (e', σ')) φ (ε1' + ε2')⌝)%I).
      { apply (laterN_except_0_pure_mono (S n)).
        intros Hpgl. eapply pgl_mon_grading; [|exact Hpgl]. exact Hsum'. }
      iApply (pgl_dbind' _ (dret tt) R' (λ x, φ x) ε1' ε2' n).
      { iPureIntro. apply cond_nonneg. }
      { iPureIntro. apply cond_nonneg. }
      { iPureIntro. apply tgl_implies_pgl, Hlift'. }
      iIntros (a HRa). destruct a.
      iSpecialize ("Hwand'" with "[//]").
      rewrite dret_id_left.
      iApply "Hwand'".

    (* Case 3: state_step with adv composition. eris has tapes, so [get_active]
       can be non-empty. We pick a tape α and erase the [state_step] step into the
       outer execution via [prim_coupl_step_prim]. *)
    - iDestruct (big_orL_mono _ (λ _ _,
                     |={∅|}=> ▷^(S n)
                       ◇ ⌜pgl (exec (S n) (e1, σ1)) φ ε''⌝)%I
                  with "H") as "H".
      { iIntros (i α Hα%list_elem_of_lookup_2) "(% & %ε1 & %ε2 & %Hε'' & %Hleq & %Hlift & H)".
        iApply (hfupd_mono _ (▷^(S n) ◇
          ⌜∀ σ2, R2 σ2 → pgl (exec (S n) (e1, σ2)) φ (ε2 (e1, σ2))⌝)%I).
        { apply (laterN_except_0_pure_mono (S n)). intros Hall.
          rewrite /= /get_active in Hα.
          apply elem_of_elements, elem_of_dom in Hα as [bs Hα].
          erewrite (Rcoupl_eq_elim _ _ (prim_coupl_step_prim _ _ _ _ _ Hα)); eauto.
          apply (pgl_mon_grading _ _
                   (ε1 + (SeriesC (λ ρ : language.state prob_lang,
                              language.state_step σ1 α ρ * ε2 (e1, ρ))))) => //.
          eapply pgl_dbind_adv; eauto; [by destruct ε1|].
          destruct Hε'' as [r Hr]; exists r.
          intros a. split; [by destruct (ε2 _) | by apply Hr]. }
        iIntros (σ2 HR2).
        iApply (elim_fupd_hfupd_plain (S n) 0 ∅ ∅ _
          ⌜pgl (exec (S n) (e1, σ2)) φ (ε2 (e1, σ2))⌝); [lia|].
        iSplitL "H".
        { iApply ("H" $! σ2 with "[//]"). }
        iIntros (l Hl) "Hst". assert (l = 0%nat) as -> by lia.
        try rewrite Nat.add_0_r; replace (S n - 0)%nat with (S n) by lia.
        iDestruct "Hst" as "(%R' & %ε1' & %ε2' & %Hsum' & %Hlift' & Hwand')".
        rewrite -(dret_id_left' (λ _ : (), exec (S n) (e1, σ2)) tt).
        iApply (hfupd_mono _ (▷^(S n) ◇
          ⌜pgl (dret tt ≫= λ _ : (), exec (S n) (e1, σ2)) φ (ε1' + ε2')⌝)%I).
        { apply (laterN_except_0_pure_mono (S n)).
          intros Hpgl. eapply pgl_mon_grading; [|exact Hpgl]. exact Hsum'. }
        iApply (pgl_dbind' _ (dret tt) R' (λ x, φ x) ε1' ε2' n).
        { iPureIntro. apply cond_nonneg. }
        { iPureIntro. apply cond_nonneg. }
        { iPureIntro. apply tgl_implies_pgl, Hlift'. }
        iIntros (a HRa). destruct a.
        iSpecialize ("Hwand'" with "[//]").
        iSpecialize ("Hwand'" with "[//]").
        rewrite dret_id_left.
        iApply "Hwand'". }
      iInduction (language.get_active σ1) as [| α] "IH"; [done|].
      rewrite big_orL_cons.
      iDestruct "H" as "[H | Ht]"; [done|].
      by iApply "IH".
      Unshelve.
       
  Qed.

  Theorem wp_refRcoupl_hfupd k (ε : nonnegreal) (e : expr) (σ : state) n φ :
    (∀ m, num_laters_per_step m = 0%nat) →
    £ n ∗ state_interp k σ ∗ err_interp ε ∗ WP e {{ v, ⌜φ v⌝ }} ⊢
    |={⊤|}=> ▷^n ◇ ⌜pgl (exec n (e, σ)) φ ε⌝.
  Proof.
    iIntros (Hnls).
    iInduction n as [|n] "IH" forall (k e σ ε); iIntros "(Hlc & Hσ & Hε & Hwp)".
    - rewrite /exec /=.
      destruct (to_val e) eqn:Heq.
      + apply of_to_val in Heq as <-.
        rewrite pgl_wp_value_fupd'.
        iApply (fupd_plain_hfupd' 0 ⊤ ⊤).
        iMod "Hwp" as "%". iModIntro.
        iPureIntro.
        apply (pgl_mon_grading _ _ 0); [apply cond_nonneg|].
        apply pgl_dret; auto.
      + iApply hfupd_intro. simpl.
        rewrite /bi_except_0. iRight.
        iPureIntro. apply pgl_dzero, Rle_ge, cond_nonneg.
    - destruct (to_val e) eqn:Heq.
      + apply of_to_val in Heq as <-.
        rewrite pgl_wp_value_fupd'.
        iApply (elim_fupd_hfupd_plain (S n) 0 ⊤ ⊤ ⌜φ v⌝
          ⌜pgl (exec (S n) (of_val v, σ)) φ ε⌝); [lia|].
        iSplitL "Hwp"; [iApply "Hwp"|].
        iIntros (l Hl) "Hpure". assert (l = 0%nat) as -> by lia.
        iApply hfupd_intro.
        iDestruct "Hpure" as %Hφv.
        iApply laterN_intro.
        rewrite /bi_except_0. iRight. iPureIntro.
        erewrite exec_is_final; [|by simpl].
        apply (pgl_mon_grading _ _ 0); [apply cond_nonneg|].
        apply pgl_dret; auto.
      + rewrite pgl_wp_unfold /pgl_wp_pre /= Heq.
        iSpecialize ("Hwp" $! k with "[$Hσ $Hε]").
        iDestruct (lc_succ with "Hlc") as "[Hcred Hlc]".
        iApply (elim_fupd_hfupd_plain (S n) 0 ⊤ ∅ _
          ⌜pgl (prim_step e σ ≫= exec n) φ ε⌝
          with "[$Hwp Hcred Hlc]"); first lia.
        iIntros (l Hl) "Hlift". assert (l = 0%nat) as -> by lia.
        try rewrite Nat.add_0_r; replace (S n - 0)%nat with (S n) by lia.
        iPoseProof
          (glm_mono _ (λ '(e2, σ2) ε2, |={∅|}=> ▷^(S n)
             ◇ ⌜pgl (exec n (e2, σ2)) φ ε2⌝)%I
            with "[%] [Hcred Hlc] Hlift") as "H".
        { apply Rle_refl. }
        { iIntros ([e' σ'] ε') "H".
          (* The instance gives [num_laters_per_step _ := 0]; Coq has
             already reduced [S (num_laters_per_step k)] to [1], so [H]
             is [£1 -∗ |={∅,∅}=> ▷ |={∅,∅}=> |={∅,⊤}=> ...]. *)
          iSpecialize ("H" with "Hcred").
          iApply (elim_fupd_hfupd_plain (S n) 0 ∅ ∅
            (▷ |={∅,∅}=> |={∅,⊤}=>
                (state_interp (S k) σ' ∗ err_interp ε' ∗
                   WP e' {{ v, ⌜φ v⌝ }}))%I
            ⌜pgl (exec n (e', σ')) φ ε'⌝); first lia.
          iSplitL "H"; [iApply "H"|].
          iIntros (l' Hl') "H". assert (l' = 0%nat) as -> by lia.
          try rewrite Nat.add_0_r; replace (S n - 0)%nat with (S n) by lia.
          iApply (laterN_hfupd 1). iNext.
          iApply (elim_fupd_hfupd_plain n 0 ∅ ⊤
            (state_interp (S k) σ' ∗ err_interp ε' ∗ WP e' {{ v, ⌜φ v⌝ }})%I
            ⌜pgl (exec n (e', σ')) φ ε'⌝); first lia.
          iSplitL "H".
          { iMod "H". iMod "H". iModIntro. iExact "H". }
          iIntros (l'' Hl'') "(Hσ' & Hε' & Hwp')".
          assert (l'' = 0%nat) as -> by lia.
          try rewrite Nat.add_0_r; replace (n - 0)%nat with n by lia.
          iApply ("IH" $! (S k) with "[$Hlc $Hσ' $Hε' $Hwp']"). }
        replace (prim_step e σ) with (step (e, σ)) by reflexivity.
        rewrite -exec_Sn_not_final; last by rewrite /is_final /to_final /= Heq.
        by iApply (glm_erasure with "H").
  Qed.

  (** [glm_erasure_safety] in hfupd form: erases a [glm] derivation about safety
      mass into a single hfupd-wrapped pure mass-bound. *)
  Lemma glm_erasure_safety (e : expr) (σ : state) (n : nat) (ε : nonnegreal) :
    to_val e = None →
    glm e σ ε (λ '(e2, σ2) ε',
        |={∅|}=> ▷^(S n) ◇ ⌜SeriesC (iterM n prim_step_or_val (e2, σ2)) >= 1 - ε'⌝)
      ⊢ |={∅|}=> ▷^(S n) ◇
          ⌜SeriesC (iterM (S n) prim_step_or_val (e, σ)) >= 1 - ε⌝.
  Proof.
    iIntros (Hv) "Hexec".
    iAssert (⌜to_val e = None⌝)%I as "-#H"; [done|]. iRevert "Hexec H".
    rewrite /glm /glm'.
    set (Φ := (λ '((e1, σ1), ε''),
                (⌜to_val e1 = None⌝ -∗
                 |={∅|}=> ▷^(S n) ◇
                   ⌜SeriesC (iterM (S n) prim_step_or_val (e1, σ1)) >= 1 - ε''⌝)%I) :
           prodO cfgO NNRO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros m ((?&?)&?) ((?&?)&?) [[[=] [=]] [=]]. by simplify_eq. }
    set (F := (glm_pre (λ '(e2, σ2) ε',
                   |={∅|}=> ▷^(S n) ◇
                     ⌜SeriesC (iterM n prim_step_or_val (e2, σ2)) >= 1 - ε'⌝)%I)).
    iPoseProof (least_fixpoint_iter F Φ with "[]") as "H"; last first.
    { iIntros "Hfix %".
      by iApply ("H" $! ((_, _)) with "Hfix"). }
    clear Hv.
    iIntros "!#" ([[e1 σ1] ε'']). rewrite /Φ/F/glm_pre.
    iIntros " [ H | [ (%R & %ε1 & %ε2 & %Hred & (%r & %Hr) & %Hsum & %Hlift & H)|H]] %Hv".
    - iApply (hfupd_mono _ (▷^(S n) ◇
          ⌜∀ ε' : nonnegreal, (ε'' < ε')%R →
            SeriesC (iterM (S n) prim_step_or_val (e1, σ1)) >= 1 - ε'⌝)%I).
      { apply (laterN_except_0_pure_mono (S n)). intros Hall.
        apply Rle_ge, real_le_limit. intros δ Hδ.
        apply Rge_le. replace (1 - ε'' - δ) with (1 - (ε'' + δ)) by lra.
        destruct ε'' as [ε'' Hε''nn]. simpl in *.
        assert (0 <= ε'' + δ)%R as Hsum_nn by lra.
        specialize (Hall (mknonnegreal (ε'' + δ) Hsum_nn)).
        simpl in Hall. apply Hall. lra. }
      iIntros (ε' Hε').
      iApply (elim_fupd_hfupd_plain (S n) 0 ∅ ∅
        (exec_stutter (λ ε0 : nonnegreal, (⌜to_val e1 = None⌝ -∗
          |={∅|}=> ▷^(S n) ◇
            ⌜SeriesC (iterM (S n) prim_step_or_val (e1, σ1)) >= 1 - ε0⌝)%I) ε')
        ⌜SeriesC (iterM (S n) prim_step_or_val (e1, σ1)) >= 1 - ε'⌝); [lia|].
      iSplitL "H"; [iApply ("H" $! ε' with "[//]")|].
      iIntros (l Hl) "Hexecs".
      assert (l = 0%nat) as -> by lia.
      try rewrite Nat.add_0_r; replace (S n - 0)%nat with (S n) by lia.
      iDestruct (exec_stutter_compat_1 _ _ with "[] Hexecs") as "[%H'|H2]".
      { iIntros (εa εb Hle) "H %Hto".
        iSpecialize ("H" with "[//]").
        iApply (hfupd_mono _ _ with "H").
        apply (laterN_except_0_pure_mono (S n)). intros Hge.
        apply Rle_ge. eapply Rle_trans; [|by apply Rge_le].
        apply Rplus_le_compat_l, Ropp_le_contravar. exact Hle. }
      + iApply hfupd_intro. iApply laterN_intro.
        rewrite /bi_except_0. iRight. iPureIntro.
        apply Rle_ge. trans 0%R.
        { destruct ε' as [? ?]; simpl in *. lra. }
        apply SeriesC_ge_0'. intros; auto.
      + iApply ("H2" with "[//]").

    (* Case 2: prim_step *)
    - iApply (hfupd_mono _ (▷^(S n) ◇
        ⌜∀ ρ, R ρ → SeriesC (iterM n prim_step_or_val ρ) >= 1 - (ε2 ρ)⌝)%I).
      { apply (laterN_except_0_pure_mono (S n)). intros Hall.
        apply Rle_ge.
        simpl.
        rewrite /dbind/dbind_pmf{1}/pmf.
        setoid_rewrite prim_step_or_val_no_val; last done.
        rewrite /pgl in Hlift. rewrite /prob in Hlift.
        rewrite distr_double_swap. setoid_rewrite SeriesC_scal_l.
        trans (1 - SeriesC
            (λ a : language.expr prob_lang * language.state prob_lang,
               if Datatypes.negb (bool_decide (R a)) then language.prim_step e1 σ1 a else 0) - SeriesC
                            (λ ρ : language.expr prob_lang * language.state prob_lang, language.prim_step e1 σ1 ρ * ε2 ρ)).
          { simpl. simpl in *. lra. }
          simpl. simpl in *.
          rewrite !Rcomplements.Rle_minus_l.
          replace 1 with (SeriesC (prim_step e1 σ1)); last first.
          { eapply mixin_prim_step_mass; last auto.
            apply ectx_lang_mixin. }
          assert (ex_seriesC (λ a : language.cfg prob_lang, prim_step e1 σ1 a * SeriesC (iterM n prim_step_or_val a))).
          { apply pmf_ex_seriesC_mult_fn. naive_solver. }
          assert (ex_seriesC (λ ρ : expr * state, prim_step e1 σ1 ρ * ε2 ρ) ).
          { apply pmf_ex_seriesC_mult_fn. exists r. intros a. pose proof cond_nonneg (ε2 a). naive_solver. }
          eassert (ex_seriesC (λ a : expr * state, if Datatypes.negb (bool_decide (R a)) then prim_step e1 σ1 a else 0)).
          { apply ex_seriesC_filter_bool_pos; auto. }
          rewrite -!SeriesC_plus; auto; last first.
          { apply ex_seriesC_plus; auto. }
          apply SeriesC_le; last first.
          { repeat apply ex_seriesC_plus; auto. }
          intros x; split; first auto.
          case_bool_decide; simpl.
          + rewrite -Rmult_plus_distr_l.
            cut (prim_step e1 σ1 x *1 <= prim_step e1 σ1 x * (SeriesC (iterM n prim_step_or_val x) + ε2 x)).
            { rewrite Rmult_1_r. rewrite Rplus_0_r. intros; done. }
            apply Rmult_le_compat_l; auto.
            rewrite -Rcomplements.Rle_minus_l.
            apply Rge_le. naive_solver.
          + apply Rle_plus_r; first done.
            apply Rplus_le_le_0_compat; first real_solver.
            apply Rmult_le_pos; auto. }
      iIntros ([e' σ'] HR).
      iSpecialize ("H" $! e' σ' with "[//]").
      iApply (elim_fupd_hfupd_plain (S n) 0 ∅ ∅
        (exec_stutter (λ ε0 : nonnegreal,
          (|={∅|}=> ▷^(S n) ◇
            ⌜SeriesC (iterM n prim_step_or_val (e', σ')) >= 1 - ε0⌝)%I)
          (ε2 (e', σ')))
        ⌜SeriesC (iterM n prim_step_or_val (e', σ')) >= 1 - (ε2 (e', σ'))⌝); [lia|].
      iSplitL "H"; [iApply "H"|].
      iIntros (l Hl) "Hst". assert (l = 0%nat) as -> by lia.
      try rewrite Nat.add_0_r; replace (S n - 0)%nat with (S n) by lia.
      iDestruct (exec_stutter_compat_1 _ _ with "[] Hst") as "[%H'|H2]".
      { iIntros (εa εb Hle) "H".
        iApply (hfupd_mono _ _ with "H").
        apply (laterN_except_0_pure_mono (S n)). intros Hge.
        apply Rle_ge. eapply Rle_trans; [|by apply Rge_le].
        apply Rplus_le_compat_l, Ropp_le_contravar. exact Hle. }
      + iApply hfupd_intro. iApply laterN_intro.
        rewrite /bi_except_0. iRight. iPureIntro.
        apply Rle_ge. trans 0%R.
        { destruct (ε2 (e', σ')) as [? ?]; simpl in *. lra. }
        apply SeriesC_ge_0'. intros; auto.
      + iApply "H2".

    (* Case 3: state_step *)
    - iDestruct (big_orL_mono _ (λ _ _,
                     |={∅|}=> ▷^(S n) ◇
                       ⌜SeriesC (iterM (S n) prim_step_or_val (e1, σ1)) >= 1 - ε''⌝)%I
                  with "H") as "H".
      { iIntros (i α Hα%list_elem_of_lookup_2) "(% & %ε1 & %ε2 & %Hε'' & %Hleq & %Hlift & H)".
        iApply (hfupd_mono _ (▷^(S n) ◇
          ⌜∀ σ2, R2 σ2 →
            SeriesC (iterM (S n) prim_step_or_val (e1, σ2)) >= 1 - (ε2 (e1, σ2))⌝)%I).
        { apply (laterN_except_0_pure_mono (S n)). intros Hall.
          assert (SeriesC (iterM (S n) prim_step_or_val (e1, σ1)) =
                  SeriesC (state_step σ1 α ≫= λ σ1', iterM (S n) prim_step_or_val (e1, σ1'))) as ->.
          { erewrite (SeriesC_ext _ (pexec (S n) (e1, σ1))); last first.
            { rewrite /pexec. done. }
            erewrite (SeriesC_ext (_≫=_) (_≫=λ σ1', pexec (S n) (e1, σ1'))); last first.
            { rewrite /pexec. done. }
            rewrite -!(dmap_mass _ (λ x, x.1)).
            eapply Rcoupl_mass_eq.
            rewrite /=/get_active elem_of_elements elem_of_dom in Hα.
            destruct Hα as [??].
            by eapply pexec_coupl_step_pexec. }
          simpl. apply Rle_ge.
          setoid_rewrite prim_step_or_val_no_val; last done.
          simpl. simpl in *.
          rewrite {1}/dbind/dbind_pmf{1}/pmf.
          rewrite /pgl in Hlift. rewrite /prob in Hlift.
          rewrite distr_double_swap. setoid_rewrite SeriesC_scal_l.
          trans (1 - SeriesC
                       (λ a ,
                          if Datatypes.negb (bool_decide (R2 a)) then language.state_step σ1 α a else 0) - SeriesC
                                                                                                                               (λ σ2 , language.state_step σ1 α σ2 * ε2 (e1, σ2))).
          { simpl. simpl in *. rewrite -Rminus_plus_distr.
            rewrite !Rminus_def. apply Rplus_le_compat_l.
            apply Ropp_le_contravar. etrans; last exact.
            apply Rplus_le_compat_r. auto. }
          simpl. simpl in *.
          rewrite !Rcomplements.Rle_minus_l.
          replace 1 with (SeriesC (state_step σ1 α)); last first.
          { apply state_step_mass. rewrite /get_active in Hα.
            rewrite elem_of_elements in Hα. done. }
          assert (ex_seriesC (λ a : state, state_step σ1 α a * SeriesC (prim_step e1 a ≫= iterM n prim_step_or_val)) ).
          { apply pmf_ex_seriesC_mult_fn. exists 1. intros; auto. }
          eassert (ex_seriesC (λ σ2 : state, state_step σ1 α σ2 * ε2 (e1, σ2))).
          { apply pmf_ex_seriesC_mult_fn. destruct Hε''. epose proof cond_nonneg. naive_solver. }
          eassert (ex_seriesC (λ a : state, if Datatypes.negb (bool_decide (R2 a)) then state_step σ1 α a else 0)).
          { apply ex_seriesC_filter_bool_pos; auto. }
          rewrite -!SeriesC_plus; auto; last first.
          { apply ex_seriesC_plus; auto. }
          apply SeriesC_le; last first.
          { repeat apply ex_seriesC_plus; auto. }
          intros x; split; first auto.
          case_bool_decide; simpl.
          - rewrite -Rmult_plus_distr_l.
            cut (state_step σ1 α x *1 <=
                  state_step σ1 α x * (SeriesC (prim_step e1 x ≫= iterM n prim_step_or_val) + ε2 (e1, x))).
            { rewrite Rmult_1_r. rewrite Rplus_0_r. intros; done. }
            apply Rmult_le_compat_l; auto.
            rewrite -Rcomplements.Rle_minus_l.
            apply Rge_le. simpl.
            setoid_rewrite prim_step_or_val_no_val in Hall; last auto.
            apply Hall. naive_solver.
          - apply Rle_plus_r; first done.
            apply Rplus_le_le_0_compat; first real_solver.
            apply Rmult_le_pos; auto. }
        iIntros (σ2 HR2).
        iSpecialize ("H" $! σ2 with "[//]").
        iApply (elim_fupd_hfupd_plain (S n) 0 ∅ ∅
          (exec_stutter (λ ε0 : nonnegreal,
            (⌜to_val e1 = None⌝ -∗
             |={∅|}=> ▷^(S n) ◇
               ⌜SeriesC (iterM (S n) prim_step_or_val (e1, σ2)) >= 1 - ε0⌝)%I)
            (ε2 (e1, σ2)))
          ⌜SeriesC (iterM (S n) prim_step_or_val (e1, σ2)) >= 1 - (ε2 (e1, σ2))⌝); [lia|].
        iSplitL "H"; [iApply "H"|].
        iIntros (l Hl) "Hst". assert (l = 0%nat) as -> by lia.
        try rewrite Nat.add_0_r; replace (S n - 0)%nat with (S n) by lia.
        iDestruct (exec_stutter_compat_1 _ _ with "[] Hst") as "[%H'|H2]".
        { iIntros (εa εb Hle) "H %Hto".
          iSpecialize ("H" with "[//]").
          iApply (hfupd_mono _ _ with "H").
          apply (laterN_except_0_pure_mono (S n)). intros Hge.
          apply Rle_ge. eapply Rle_trans; [|by apply Rge_le].
          apply Rplus_le_compat_l, Ropp_le_contravar. exact Hle. }
        + iApply hfupd_intro. iApply laterN_intro.
          rewrite /bi_except_0. iRight. iPureIntro.
          apply Rle_ge. trans 0%R.
          { destruct (ε2 (e1, σ2)) as [? ?]; simpl in *. lra. }
          apply SeriesC_ge_0'. intros; auto.
        + iApply ("H2" with "[//]"). }
      iInduction (language.get_active σ1) as [| α] "IH"; [done|].
      rewrite big_orL_cons.
      iDestruct "H" as "[H | Ht]"; [done|].
      by iApply "IH".
  Qed.

  Theorem wp_safety_hfupd k (ε : nonnegreal) (e : expr) (σ : state) n φ :
    (∀ m, num_laters_per_step m = 0%nat) →
    £ n ∗ state_interp k σ ∗ err_interp ε ∗ WP e {{ v, ⌜φ v⌝ }} ⊢
    |={⊤|}=> ▷^n ◇ ⌜SeriesC (pexec n (e, σ)) >= 1 - ε⌝.
  Proof.
    iIntros (Hnls).
    iInduction n as [|n] "IH" forall (k e σ ε); iIntros "(Hlc & Hσ & Hε & Hwp)".
    - iApply hfupd_intro. simpl.
      rewrite /bi_except_0. iRight. iPureIntro.
      trans 1; last first.
      { pose proof cond_nonneg ε. lra. }
      apply Rle_ge. rewrite dret_mass. done.
    - destruct (to_val e) eqn:Heq.
      + apply of_to_val in Heq as <-.
        rewrite pgl_wp_value_fupd'.
        iApply (elim_fupd_hfupd_plain (S n) 0 ⊤ ⊤ ⌜φ v⌝
          ⌜SeriesC (pexec (S n) (of_val v, σ)) >= 1 - ε⌝); [lia|].
        iSplitL "Hwp"; [iApply "Hwp"|].
        iIntros (l Hl) "_". assert (l = 0%nat) as -> by lia.
        iApply hfupd_intro.
        iApply laterN_intro.
        rewrite /bi_except_0. iRight. iPureIntro.
        erewrite pexec_is_final; last by rewrite /is_final /to_final /=; eexists.
        rewrite dret_mass.
        destruct ε as [ε ?]; simpl in *. apply Rle_ge. lra.
      + rewrite pgl_wp_unfold /pgl_wp_pre /= Heq.
        iSpecialize ("Hwp" $! k with "[$Hσ $Hε]").
        iDestruct (lc_succ with "Hlc") as "[Hcred Hlc]".
        iApply (elim_fupd_hfupd_plain (S n) 0 ⊤ ∅ _
          ⌜SeriesC (iterM (S n) prim_step_or_val (e, σ)) >= 1 - ε⌝
          with "[$Hwp Hcred Hlc]"); first lia.
        iIntros (l Hl) "Hlift". assert (l = 0%nat) as -> by lia.
        try rewrite Nat.add_0_r; replace (S n - 0)%nat with (S n) by lia.
        iPoseProof
          (glm_mono _ (λ '(e2, σ2) ε2, |={∅|}=> ▷^(S n) ◇
             ⌜SeriesC (iterM n prim_step_or_val (e2, σ2)) >= 1 - ε2⌝)%I
            with "[%] [Hcred Hlc] Hlift") as "H".
        { apply Rle_refl. }
        { iIntros ([e' σ'] ε') "H".
          iSpecialize ("H" with "Hcred").
          iApply (elim_fupd_hfupd_plain (S n) 0 ∅ ∅
            (▷ |={∅,∅}=> |={∅,⊤}=>
                (state_interp (S k) σ' ∗ err_interp ε' ∗
                   WP e' {{ v, ⌜φ v⌝ }}))%I
            ⌜SeriesC (iterM n prim_step_or_val (e', σ')) >= 1 - ε'⌝); first lia.
          iSplitL "H"; [iApply "H"|].
          iIntros (l' Hl') "H". assert (l' = 0%nat) as -> by lia.
          try rewrite Nat.add_0_r; replace (S n - 0)%nat with (S n) by lia.
          iApply (laterN_hfupd 1). iNext.
          iApply (elim_fupd_hfupd_plain n 0 ∅ ⊤
            (state_interp (S k) σ' ∗ err_interp ε' ∗ WP e' {{ v, ⌜φ v⌝ }})%I
            ⌜SeriesC (iterM n prim_step_or_val (e', σ')) >= 1 - ε'⌝); first lia.
          iSplitL "H".
          { iMod "H". iMod "H". iModIntro. iExact "H". }
          iIntros (l'' Hl'') "(Hσ' & Hε' & Hwp')".
          assert (l'' = 0%nat) as -> by lia.
          try rewrite Nat.add_0_r; replace (n - 0)%nat with n by lia.
          iApply ("IH" $! (S k) with "[$Hlc $Hσ' $Hε' $Hwp']"). }
        by iApply (glm_erasure_safety with "H").
  Qed.

End adequacy.

Class erisGpreS Σ := ErisGpreS {
  erisGpreS_iris  :: invGpreS Σ;
  erisGpreS_heap  :: ghost_mapG Σ loc val;
  erisGpreS_tapes :: ghost_mapG Σ loc tape;
  erisGpreS_err   :: ecGpreS Σ;
}.

Definition erisΣ : gFunctors :=
  #[invΣ; ghost_mapΣ loc val;
    ghost_mapΣ loc tape;
    GFunctor (authR nonnegrealUR)].
Global Instance subG_erisGPreS {Σ} : subG erisΣ Σ → erisGpreS Σ.
Proof. solve_inG. Qed.

Theorem wp_pgl Σ `{erisGpreS Σ} (e : expr) (σ : state) n (ε : R) φ :
  0 <= ε →
  (∀ `{erisGS Σ}, ⊢ ↯ ε -∗ WP e {{ v, ⌜φ v⌝ }}) →
  pgl (exec n (e, σ)) φ ε.
Proof.
  intros Hε Hwp.
  apply (pure_soundness (PROP:=iPropI Σ)).
  apply (laterN_soundness _ (S n)).
  rewrite laterN_later -except_0_into_later.
  destruct (decide (ε < 1)) as [Hcr|Hcr]; last first.
  { iApply laterN_intro. iApply except_0_intro. iPureIntro.
    apply not_Rlt, Rge_le in Hcr.
    rewrite /pgl. intros. eapply Rle_trans; [apply prob_le_1|done]. }
  apply (fupd_finally_soundness HasLc n ⊤).
  iIntros (Hinv) "Hlc".
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh _]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht _]]".
  set ε' := mknonnegreal _ Hε.
  iMod (ec_alloc ε') as (Hec) "[Hs Hf]"; [done|].
  set (HclutchGS := HeapG Σ _ _ _ γH γT _).
  change ε with (nonneg ε').
  iPoseProof (wp_refRcoupl_hfupd O ε' e σ n φ (λ _, eq_refl)
                with "[Hlc Hs Hh Ht Hf]") as "H".
  { iFrame "Hlc Hs". rewrite /state_interp /=. iFrame "Hh Ht".
    iApply Hwp. iApply "Hf". }
  iApply "H".
Qed.

Lemma pgl_closed_lim (e : expr) (σ : state) (ε : R) φ :
  (∀ n, pgl (exec n (e, σ)) φ ε) →
  pgl (lim_exec (e, σ)) φ ε .
Proof. intros Hn. by apply lim_exec_continuous_prob. Qed.

Theorem wp_pgl_lim Σ `{erisGpreS Σ} (e : expr) (σ : state) (ε : R) φ :
  0 <= ε →
  (∀ `{erisGS Σ}, ⊢ ↯ ε -∗ WP e {{ v, ⌜φ v⌝ }}) →
  pgl (lim_exec (e, σ)) φ ε.
Proof.
  intros.
  apply pgl_closed_lim.
  intro n.
  by apply (wp_pgl Σ).
Qed.

Theorem wp_pgl_epsilon_lim Σ `{erisGpreS Σ} (e : expr) (σ : state) (ε : R) φ :
  0 <= ε →
  (∀ `{erisGS Σ} (ε':nonnegreal), ε<ε' -> ⊢ ↯ ε' -∗ WP e {{ v, ⌜φ v⌝ }}) →
  pgl (lim_exec (e, σ)) φ ε.
Proof.
  intros ? H'.
  apply pgl_epsilon_limit; [lra|].
  intros ε0 H1.
  assert (0<=ε0) as Hε0 by lra.
  pose (mknonnegreal ε0 Hε0) as NNRε0.
  assert (ε0 = (NNRbar_to_real (NNRbar.Finite (NNRε0)))) as Heq.
  { by simpl. }
  rewrite Heq.
  eapply wp_pgl_lim; [done|done|].
  intros. iIntros "He".
  iApply H'; try iFrame.
  lra.
Qed.

Theorem wp_safety Σ `{erisGpreS Σ} (e : expr) (σ : state) (ε : R) φ n:
  0 <= ε →
  (∀ `{erisGS Σ}, ⊢ ↯ ε -∗ WP e {{ v, ⌜φ v⌝ }}) →
  SeriesC (pexec n (e, σ)) >= 1 - ε.
Proof.
  intros Hε Hwp.
  apply (pure_soundness (PROP:=iPropI Σ)).
  apply (laterN_soundness _ (S n)).
  rewrite laterN_later -except_0_into_later.
  destruct (decide (ε < 1)) as [Hcr|Hcr]; last first.
  { iApply laterN_intro. iApply except_0_intro. iPureIntro.
    apply not_Rlt, Rge_le in Hcr.
    trans 0%R; last first.
    { lra. }
    apply Rle_ge, SeriesC_ge_0'. intros. auto. }
  apply (fupd_finally_soundness HasLc n ⊤).
  iIntros (Hinv) "Hlc".
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh _]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht _]]".
  set ε' := mknonnegreal _ Hε.
  iMod (ec_alloc ε') as (Hec) "[Hs Hf]"; [done|].
  set (HclutchGS := HeapG Σ _ _ _ γH γT _).
  change ε with (nonneg ε').
  iPoseProof (wp_safety_hfupd O ε' e σ n φ (λ _, eq_refl)
                with "[Hlc Hs Hh Ht Hf]") as "H".
  { iFrame "Hlc Hs". rewrite /state_interp /=. iFrame "Hh Ht".
    iApply Hwp. iApply "Hf". }
  iApply "H".
Qed.

Lemma pexec_safety_relate (e:expr) σ n:
  probp (pexec n (e, σ)) (λ ρ, (is_final ρ ∨ reducible ρ)) =
  SeriesC (pexec (S n) (e, σ)).
Proof.
  revert e σ.
  induction n; intros e σ.
  - simpl. rewrite pexec_O. rewrite pexec_1.
    rewrite /probp. rewrite /step_or_final.
    erewrite (SeriesC_ext _ (λ x, if bool_decide (is_final (e, σ) ∨ reducible (e, σ))
                                  then dret (e, σ) x else 0)); last first.
    { intros. destruct (decide (n=(e,σ))).
      - subst. done.
      - rewrite dret_0; last done. by repeat case_match.
    }
    case_bool_decide as H.
    + rewrite dret_mass. case_match; first by rewrite dret_mass.
      simpl. erewrite mixin_prim_step_mass; auto.
      * apply: ectx_lang_mixin.
      * destruct H; auto.
        exfalso.
        destruct H. naive_solver.
    + rewrite SeriesC_0; last done.
      case_match; first exfalso.
      * apply H. naive_solver.
      * symmetry. apply SeriesC_0.
        intros x. assert (0<=step (e, σ) x) as [|] by auto; auto.
        exfalso. apply H. right. rewrite /reducible. naive_solver.
  - rewrite /prob in IHn. rewrite /prob.
    rewrite (pexec_Sn_r _ (S n)).
    rewrite dbind_mass.
    apply SeriesC_ext.
    intros [].
    case_bool_decide as H.
    + replace (SeriesC _) with 1; first lra.
      symmetry.
      destruct H.
      * rewrite /step_or_final. case_match; first apply dret_mass.
        exfalso. destruct H. naive_solver.
      * rewrite /step_or_final. case_match; first apply dret_mass.
        simpl. erewrite mixin_prim_step_mass; auto.
        apply: ectx_lang_mixin.
    + replace (SeriesC _) with 0; first lra.
      symmetry.
      rewrite /step_or_final.
      case_match.
      * exfalso. naive_solver.
      * apply SeriesC_0.
        intros x. eassert (0<= step _ x) as [|<-] by auto; auto.
        exfalso. apply H. right. rewrite /reducible. naive_solver.
Qed.

Corollary wp_safety' Σ `{erisGpreS Σ} (e : expr) (σ : state) (ε : R) φ n:
  0 <= ε →
  (∀ `{erisGS Σ}, ⊢ ↯ ε -∗ WP e {{ v, ⌜φ v⌝ }}) →
  probp (pexec n (e, σ)) (λ ρ, is_final ρ ∨ reducible ρ) >= 1 - ε.
Proof.
  intros Hε Hwp.
  rewrite pexec_safety_relate.
  by eapply (wp_safety Σ).
Qed.

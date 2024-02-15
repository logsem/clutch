From iris.proofmode Require Import base proofmode.
(* From iris.bi Require Export weakestpre fixpoint big_op. *)
From iris.algebra Require Import auth excl.
From iris.base_logic.lib Require Export ghost_map invariants fancy_updates.
From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.prob Require Import distribution couplings.
(* From clutch.bi Require Import weakestpre. *)
From clutch.common Require Export language.
From clutch.generic Require Export generic_weakestpre.
From clutch.prob_lang Require Export class_instances.
From clutch.prob_lang Require Import tactics lang notation erasure.
From iris.prelude Require Import options.
From clutch.prob Require Import distribution.
Import uPred.

(* TODO: Fix dependencies *)


Class clutchGS Σ := HeapG {
  clutchGS_invG : invGS_gen HasNoLc Σ;
  (* CMRA for the state *)
  clutchGS_heap : ghost_mapG Σ loc val;
  clutchGS_tapes : ghost_mapG Σ loc tape;
  (* ghost names for the state *)
  clutchGS_heap_name : gname;
  clutchGS_tapes_name : gname;
}.


Definition progUR : ucmra := optionUR (exclR exprO).
Definition cfgO : ofe := prodO exprO stateO.
Definition cfgUR : ucmra := optionUR (exclR cfgO).

Definition heap_auth `{clutchGS Σ} :=
  @ghost_map_auth _ _ _ _ _ clutchGS_heap clutchGS_heap_name.
Definition tapes_auth `{clutchGS Σ} :=
  @ghost_map_auth _ _ _ _ _ clutchGS_tapes clutchGS_tapes_name.


Global Instance clutchGS_irisGS `{!clutchGS Σ} : irisGS prob_lang Σ := {
  iris_invGS := clutchGS_invG;
  state_interp σ := (heap_auth 1 σ.(heap) ∗ tapes_auth 1 σ.(tapes))%I;
}.

Section adequacy.


  Context `{!clutchGS Σ}.
  Context (M : mlift).


  Lemma ub_lift_dbind' `{Countable A, Countable A'}
    (f : A → distr A') (μ : distr A) (R : A → Prop) (T : A' → Prop) n :
    ⌜M.(mlift_funct) μ R⌝ -∗
    (∀ a , ⌜R a⌝ ={∅}▷=∗^(S n) ⌜M.(mlift_funct) (f a) T⌝) -∗
    |={∅}▷=>^(S n) ⌜M.(mlift_funct) (dbind f μ) T⌝ : iProp Σ.
  Proof.
    iIntros (?) "H".
    iApply (step_fupdN_mono _ _ _ (⌜(∀ a b, R a → M.(mlift_funct) (f a) T)⌝)).
    { iIntros (?). iPureIntro. eapply M.(mlift_bind); eauto. }
    iIntros (???) "/=".
    iMod ("H" with "[//]"); auto.
  Qed.

  Lemma exec_ub_erasure (e : expr) (σ : state) (n : nat) φ  :
    to_val e = None →
    exec_mlift M e σ (λ '(e2, σ2),
        |={∅}▷=>^(S n) ⌜ M.(mlift_funct) (exec n (e2, σ2)) φ ⌝)
    ⊢ |={∅}▷=>^(S n) ⌜M.(mlift_funct) (exec (S n) (e, σ)) φ ⌝.
  Proof.
    iIntros (Hv) "Hexec".
    iAssert (⌜to_val e = None⌝)%I as "-#H"; [done|]. iRevert "Hexec H".
    rewrite /exec_mlift /exec_mlift'.
    set (Φ := (λ '(e1, σ1),
                (⌜to_val e1 = None⌝ ={∅}▷=∗^(S n)
                 ⌜M.(mlift_funct) (exec (S n) (e1, σ1)) φ ⌝)%I) :
           cfgO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros m (?&?) (?&?) [[=] [=]]. by simplify_eq. }
    set (F := (exec_mlift_pre M (λ '(e2, σ2),
                   |={∅}▷=>^(S n) ⌜M.(mlift_funct) (exec n (e2, σ2)) φ⌝)%I)).
    iPoseProof (least_fixpoint_iter F Φ with "[]") as "H"; last first.
    { iIntros "Hfix %".
      by iMod ("H" $! ((_, _)) with "Hfix [//]").
    }
    clear.
    iIntros "!#" ([e1 σ1]). rewrite /Φ/F/exec_mlift_pre.
    iIntros "[ (%R & %Hlift & H)| H] %Hv".
    - rewrite exec_Sn_not_final; [|eauto].
      iApply ub_lift_dbind'.
      + iPureIntro; apply Hlift.
      + iIntros ([] ?).
        by iMod ("H"  with "[//]").
    - rewrite exec_Sn_not_final; [|eauto].
      iDestruct (big_orL_mono _ (λ _ _,
                     |={∅}▷=>^(S n)
                       ⌜M.(mlift_funct) (prim_step e1 σ1 ≫= exec n) φ ⌝)%I
                  with "H") as "H".
      { iIntros (i α Hα%elem_of_list_lookup_2) "(% & %Hlift & H)".
        replace (prim_step e1 σ1) with (step (e1, σ1)) by easy.
        rewrite -exec_Sn_not_final ; [|eauto].
        iApply (step_fupdN_mono _ _ _
                  (⌜∀ σ2 , R2 σ2 → M.(mlift_funct) (exec (S n) (e1, σ2)) φ ⌝)%I).
        - iIntros (?). iPureIntro.
          rewrite /= /get_active in Hα.
          apply elem_of_elements, elem_of_dom in Hα as [bs Hα].
          erewrite (Rcoupl_eq_elim _ _ (prim_coupl_step_prim _ _ _ _ _ Hα)); eauto.
          eapply M.(mlift_bind); eauto.
        - iIntros (??). by iMod ("H" with "[//] [//]"). }
      iInduction (language.get_active σ1) as [| α] "IH"; [done|].
      rewrite big_orL_cons.
      iDestruct "H" as "[H | Ht]"; [done|].
      by iApply "IH".
  Qed.

  Import generic_weakestpre.

  (* TODO: Fix notation to get rid of the mask *)
  Theorem wp_refRcoupl_step_fupdN (e : expr prob_lang) (σ : state prob_lang) n φ  :
    state_interp σ ∗ WP e @ M ; ⊤ {{ v, ⌜φ v⌝ }} ⊢
    |={⊤,∅}=> |={∅}▷=>^n ⌜M.(mlift_funct) (exec n (e, σ)) φ ⌝.
  Proof.
    iInduction n as [|n] "IH" forall (e σ); iIntros "((Hσh & Hσt) & Hwp)".
    - rewrite /exec_val /=.
      destruct (prob_lang.to_val e) eqn:Heq.
      + apply of_to_val in Heq as <-.
        rewrite mlift_wp_value_fupd.
        iMod (fupd_mask_subseteq _); [set_solver |].
        iMod "Hwp" as "%".
        iApply fupd_mask_intro; [set_solver|]; iIntros.
        iPureIntro.
        apply M.(mlift_unit); auto.
      + iApply fupd_mask_intro; [set_solver|]; iIntros "_".
        iPureIntro.
        apply M.(mlift_dzero).
    - rewrite exec_Sn /step_or_final /=.
      destruct (prob_lang.to_val e) eqn:Heq.
      + apply prob_lang.of_to_val in Heq as <-.
        rewrite mlift_wp_value_fupd.
        iMod "Hwp" as "%".
        iApply fupd_mask_intro; [set_solver|]; iIntros "_".
        iApply step_fupdN_intro; [done|]. do 4 iModIntro.
        iPureIntro.
        rewrite exec_unfold dret_id_left /=.
        apply M.(mlift_unit); auto.
      + rewrite mlift_wp_unfold /mlift_wp_pre /= Heq.
        iMod ("Hwp" with "[$]") as "(%Hexec_ub & Hlift)".
        iModIntro.
        iPoseProof
          (exec_mlift_mono M _ (λ '(e2, σ2), |={∅}▷=>^(S n)
             ⌜M.(mlift_funct) (exec_val n (e2, σ2)) φ⌝)%I
            with "[] Hlift") as "H".
        { iIntros ([]) "H !> !>".
          iMod "H" as "(Hstate & Hwp)".
          iMod ("IH" with "[$]") as "H".
          iModIntro. done. }
        rewrite -exec_val_Sn_not_val; [|done].
        iAssert
          (|={∅}▷=> |={∅}▷=>^n ⌜M.(mlift_funct) (exec_val (S n) (e, σ)) φ⌝)%I
          with "[H]" as "Haux"; last first.
        {  iMod "Haux".
           do 2 iModIntro.
           iMod "Haux".
           iModIntro.
           iApply (step_fupdN_wand with "Haux").
           iPureIntro; done.
         }
        by iApply (exec_ub_erasure with "H").
  Qed.

End adequacy.


Class clutchGpreS Σ := ClutchGpreS {
  clutchGpreS_iris  :: invGpreS Σ;
  clutchGpreS_heap  :: ghost_mapG Σ loc val;
  clutchGpreS_tapes :: ghost_mapG Σ loc tape;
}.

Definition clutchΣ : gFunctors :=
  #[invΣ; ghost_mapΣ loc val;
    ghost_mapΣ loc tape].
Global Instance subG_clutchGPreS {Σ} : subG clutchΣ Σ → clutchGpreS Σ.
Proof. solve_inG. Qed.

Import generic_weakestpre.

Theorem wp_mlift Σ `{clutchGpreS Σ} (M : mlift) (e : expr prob_lang) (σ : state prob_lang) n φ :
  (∀ `{clutchGS Σ}, ⊢ WP e @ M ; ⊤ {{ v, ⌜φ v⌝ }}) →
  M.(mlift_funct) (exec n (e, σ)) φ.
Proof.
  intros Hwp.
  eapply pure_soundness, (step_fupdN_soundness_no_lc _ n 0).
  iIntros (Hinv) "_".
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh _]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht _]]".
  set (HclutchGS := HeapG Σ _ _ _ γH γT).
  iApply wp_refRcoupl_step_fupdN.
  iFrame.
  iApply Hwp.
Qed.

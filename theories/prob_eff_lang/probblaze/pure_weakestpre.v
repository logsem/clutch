From clutch.prob_eff_lang.probblaze Require Import primitive_laws.
From iris.proofmode Require Import base proofmode.
From clutch.prob_eff_lang.probblaze Require Import syntax semantics notation class_instances logic.

(* Consider generalizing the PureExec construction *)
Definition prel `{Σ : gFunctors} (e1 e2 : expr) (Φ : val → val → iProp Σ) : iProp Σ := 
  match (to_val e1), (to_val e2) with
  | Some v1, Some v2 => Φ v1 v2
  | Some v1, None => ∃ (v2 : val), (∃ n2, ⌜nsteps pure_step n2 e2 v2⌝) ∗ Φ v1 v2
  | None, Some v2 =>  ∃ (v1 : val), (∃ n1, ⌜nsteps pure_step n1 e1 v1⌝) ∗ Φ v1 v2
  | None, None => ∃ (v1 v2 : val) n1 n2,  ⌜nsteps pure_step n1 e1 v1 ∧ nsteps pure_step n2 e2 v2⌝ ∗ Φ v1 v2
  end. 

Lemma prel_intuitionistically `{Σ : gFunctors} e1 e2 Φ : 
  (□ prel e1 e2 Φ) -∗ @prel Σ e1 e2 (λ v1 v2, □ (Φ v1 v2)).
Proof.
  iIntros "#Hrel". unfold prel.
  destruct (to_val e1) eqn:Heq1, (to_val e2) eqn:Heq2; first done.
  1, 2: iDestruct "Hrel" as (??) "H"; iExists _; iSplit; first (by iPureIntro); by iModIntro. 
  iDestruct "Hrel" as (????) "H". iExists _,_,_,_. iDestruct "H" as "($ & H2)". by iModIntro. 
Qed.

Notation "'PREL' e1 ≤ e2 '[{' Φ '}]'" := (prel e1%E e2%E Φ)
                                           (at level 20, e1, e2, Φ at next level, only parsing) : bi_scope.
Notation "'PREL' e1 ≤ e2 '[{' v1 ; v2 , Φ '}]'" := (prel e1%E e2%E (λ v1 v2, Φ)%I)
                                                   (at level 20, v1 ident, v2 ident, e1, e2, Φ at next level) : bi_scope.


Lemma prel_brel `{!probblazeRGS Σ} e1 e2 Φ :                         
  prel e1 e2 Φ -∗ brel ⊤ e1 e2 ⊥ Φ.
Proof.
  iIntros "He".
  destruct (to_val e1) eqn:Heq1, (to_val e2) eqn:Heq2;
    rewrite /prel Heq1 Heq2/=.
  - rewrite -(of_to_val _ _ Heq1). rewrite -(of_to_val _ _ Heq2).
    iApply brel_value. by iIntros "$ !>".
  - rewrite -(of_to_val _ _ Heq1).
    iDestruct "He" as (w) "[(%n & %Hs) HΦ]".
    iApply (brel_pure_step_r _ _ _ w True n _ _ (λ _, Hs) I).
    iApply brel_value. by iIntros "$ !>".
  - rewrite -(of_to_val _ _ Heq2).
    iDestruct "He" as (w) "[(%n & %Hs) HΦ]".
    iApply (brel_pure_step_later _ _ w _ True n _ _ (λ _, Hs) I).
    iApply bi.laterN_intro.
    iApply brel_value. by iIntros "$ !>".
  - iDestruct "He" as (w1 w2 m1 m2) "[(%Hs1 & %Hs2) HΦ]".
    iApply (brel_pure_step_r _ _ _ w2 True m2 _ _ (λ _, Hs2) I).
    iApply (brel_pure_step_later _ _ w1 _ True m1 _ _ (λ _, Hs1) I).
    iApply bi.laterN_intro.
    iApply brel_value. by iIntros "$ !>".
Qed.

Lemma prel_mono `{Σ : gFunctors} e1 e2 Φ Ψ : 
  (∀ v1 v2, Φ v1 v2 -∗ Ψ v1 v2) -∗
  PREL e1 ≤ e2 [{ v1; v2, Φ v1 v2}] -∗ @prel Σ e1 e2 Ψ.
Proof.
  iIntros "Hvv Hprel". rewrite /prel.
  destruct (to_val e1) eqn:Heq1, (to_val e2) eqn:Heq2.
  - by iApply "Hvv".
  - iDestruct "Hprel" as (w) "(Hs & HΦ)". iExists w. iFrame "Hs".
    by iApply "Hvv".
  - iDestruct "Hprel" as (w) "(Hs & HΦ)". iExists w. iFrame "Hs".
    by iApply "Hvv".
  - iDestruct "Hprel" as (w1 w2 m1 m2) "(Hs & HΦ)". iExists w1, w2, m1, m2.
    iFrame "Hs". by iApply "Hvv".
Qed.


Lemma pure_step_det_val (e a b : expr) :
  pure_step e a → pure_step e b → a = b.
Proof.
  intros Ha Hb.
  set (σ := @inhabitant state state_inhabited).
  pose proof (pure_step_det _ _ Ha σ) as H1.
  pose proof (pure_step_det _ _ Hb σ) as H2.
  destruct (decide (a = b)) as [Heq | Hne]; first done.
  exfalso.
  assert ((a, σ) ≠ (b, σ)) as Hpair.
  { intros Hcontra. apply Hne. by inversion Hcontra. }
  pose proof (pmf_1_not_eq (language.prim_step e σ)
                (a, σ) (b, σ) Hpair H1) as H0.
  rewrite H0 in H2. lra.
Qed.

Lemma val_no_pure_step (w : val) (y : expr) : pure_step (of_val w) y → False.
Proof.
  intros Hstep.
  pose proof (pure_step_det _ _ Hstep (@inhabitant state state_inhabited))
    as Hp.
  assert (language.prim_step (of_val w) (@inhabitant state state_inhabited)
            (y, @inhabitant state state_inhabited) > 0) as Hgt.
  { rewrite Hp. lra. }
  pose proof (val_prim_stuck _ _ _ Hgt) as Hnone.
  rewrite to_of_val in Hnone. done.
Qed.

Lemma nsteps_pure_step_det (n m : nat) (e : expr) (v v' : val) :
  nsteps pure_step n e (of_val v) → nsteps pure_step m e (of_val v') →
  v = v'.
Proof.
  revert m e v v'.
  induction n as [|n IHn]; intros m e v v' Hn Hm.
  - inversion Hn; subst.
    destruct m as [|m].
    + inversion Hm; subst. by apply (inj of_val).
    + inversion Hm as [|m' x y z Hstep Hrest]; subst.
      exfalso. by eapply val_no_pure_step.
  - inversion Hn as [|n0 x0 y0 z0 Hstep1 Hrest1]; subst.
    destruct m as [|m].
    + inversion Hm; subst.
      exfalso. by eapply val_no_pure_step.
    + inversion Hm as [|m0 x1 y1 z1 Hstep2 Hrest2]; subst.
      pose proof (pure_step_det_val _ _ _ Hstep1 Hstep2) as Heq; subst.
      by eapply IHn.
Qed.

Lemma prel_forall `{!Inhabited A} `{Σ : gFunctors} e1 e2 (Φ : A → val → val → iProp Σ) :
  (∀ x, PREL e1 ≤ e2 [{ (Φ x) }]) -∗ PREL e1 ≤ e2 [{ v1; v2, (∀ x, Φ x v1 v2) }].
Proof. 
  iIntros "Hprel".
  destruct (to_val e1) eqn:Heq1, (to_val e2) eqn:Heq2;
    rewrite /prel Heq1 Heq2/=; first done.
  - iAssert (⌜∃ (v2:val) (n2:nat), nsteps pure_step n2 e2 v2⌝)%I
      as %(v2 & n2 & Hs2).
    { iDestruct ("Hprel" $! inhabitant) as (v2) "[(%n2 & %Hs2) _]".
      iPureIntro. eauto. }
    iExists v2. iSplitR; [iExists n2; by iPureIntro|].
    iIntros (x).
    iDestruct ("Hprel" $! x) as (w2) "[(%m2 & %Hsx) HΦ]".
    pose proof (nsteps_pure_step_det _ _ _ _ _ Hsx Hs2) as Heq; subst.
    done.
  - iAssert (⌜∃ (v1:val) (n1:nat), nsteps pure_step n1 e1 v1⌝)%I
      as %(v1 & n1 & Hs1).
    { iDestruct ("Hprel" $! inhabitant) as (v1) "[(%n1 & %Hs1) _]".
      iPureIntro. eauto. }
    iExists v1. iSplitR; [iExists n1; by iPureIntro|].
    iIntros (x).
    iDestruct ("Hprel" $! x) as (w1) "[(%m1 & %Hsx) HΦ]".
    pose proof (nsteps_pure_step_det _ _ _ _ _ Hsx Hs1) as Heq; subst.
    done.
  - iAssert (⌜∃ (v1 v2:val) (n1 n2:nat),
               nsteps pure_step n1 e1 v1 ∧ nsteps pure_step n2 e2 v2⌝)%I
      as %(v1 & v2 & n1 & n2 & Hs1 & Hs2).
    { iDestruct ("Hprel" $! inhabitant)
        as (v1 v2 m1 m2) "[(%Hs1 & %Hs2) _]".
      iPureIntro. eauto 10. }
    iExists v1, v2, n1, n2. iSplitR; [by iPureIntro|].
    iIntros (x).
    iDestruct ("Hprel" $! x) as (w1 w2 k1 k2) "[(%Hsx1 & %Hsx2) HΦ]".
    pose proof (nsteps_pure_step_det _ _ _ _ _ Hsx1 Hs1) as Hq1; subst.
    pose proof (nsteps_pure_step_det _ _ _ _ _ Hsx2 Hs2) as Hq2; subst.
    done.
Qed.

(* Each side of a [prel] reduces to a value satisfying [Φ]. *)
Lemma prel_steps_to_val `{Σ : gFunctors} e1 e2 Φ :
  @prel Σ e1 e2 Φ -∗ ∃ v1 v2 n1 n2,
    ⌜nsteps pure_step n1 e1 (of_val v1)⌝ ∗
    ⌜nsteps pure_step n2 e2 (of_val v2)⌝ ∗ Φ v1 v2.
Proof.
  iIntros "He". rewrite /prel.
  destruct (to_val e1) eqn:Heq1, (to_val e2) eqn:Heq2.
  - apply of_to_val in Heq1; apply of_to_val in Heq2; subst.
    iExists v, v0, 0%nat, 0%nat. iFrame.
    iPureIntro; split; apply nsteps_O.
  - apply of_to_val in Heq1; subst.
    iDestruct "He" as (w) "[(%n & %Hs) HΦ]".
    iExists v, w, 0%nat, n. iFrame.
    iPureIntro; split; [apply nsteps_O | done].
  - apply of_to_val in Heq2; subst.
    iDestruct "He" as (w) "[(%n & %Hs) HΦ]".
    iExists w, v, n, 0%nat. iFrame.
    iPureIntro; split; [done | apply nsteps_O].
  - iDestruct "He" as (w1 w2 m1 m2) "[(%Hs1 & %Hs2) HΦ]".
    iExists w1, w2, m1, m2. iFrame. iPureIntro; split; done.
Qed.

(* Build a [prel] for a pair from [prel]s for its components, reducing
   each component through the pair evaluation context. *)
Lemma prel_pair `{Σ : gFunctors} e1 e1' e2 e2'
  (Φ Ψ : val → val → iProp Σ) :
  prel e1 e1' Φ -∗ prel e2 e2' Ψ -∗
  prel (Pair e1 e2) (Pair e1' e2')
    (λ w1 w2, ∃ a1 a2 b1 b2, ⌜w1 = (a1, b1)%V⌝ ∗
       ⌜w2 = (a2, b2)%V⌝ ∗ Φ a1 a2 ∗ Ψ b1 b2)%I.
Proof.
  iIntros "H1 H2".
  iDestruct (prel_steps_to_val with "H1")
    as (a1 a2 na1 na2) "(%Ha1 & %Ha2 & HΦ)".
  iDestruct (prel_steps_to_val with "H2")
    as (b1 b2 nb1 nb2) "(%Hb1 & %Hb2 & HΨ)".
  rewrite /prel /=.
  iExists (PairV a1 b1), (PairV a2 b2), _, _.
  iSplitR.
  { iPureIntro. split.
    - eapply nsteps_trans;
        [eapply (pure_step_nsteps_ctx [PairRCtx e1]); exact Hb1|].
      eapply nsteps_trans;
        [eapply (pure_step_nsteps_ctx [PairLCtx b1]); exact Ha1|].
      exact (pure_pairc a1 b1 I).
    - eapply nsteps_trans;
        [eapply (pure_step_nsteps_ctx [PairRCtx e1']); exact Hb2|].
      eapply nsteps_trans;
        [eapply (pure_step_nsteps_ctx [PairLCtx b2]); exact Ha2|].
      exact (pure_pairc a2 b2 I). }
  iExists a1, a2, b1, b2. by iFrame.
Qed.

(* Build a [prel] for a left injection from a [prel] for its argument. *)
Lemma prel_injl `{Σ : gFunctors} e e' (Φ : val → val → iProp Σ) :
  prel e e' Φ -∗
  prel (InjL e) (InjL e')
    (λ w1 w2, ∃ a1 a2, ⌜w1 = InjLV a1⌝ ∗ ⌜w2 = InjLV a2⌝ ∗ Φ a1 a2)%I.
Proof.
  iIntros "H".
  iDestruct (prel_steps_to_val with "H")
    as (a1 a2 n1 n2) "(%Ha1 & %Ha2 & HΦ)".
  rewrite /prel /=.
  iExists (InjLV a1), (InjLV a2), _, _.
  iSplitR.
  { iPureIntro. split.
    - eapply nsteps_trans;
        [eapply (pure_step_nsteps_ctx [InjLCtx]); exact Ha1|].
      exact (pure_injlc a1 I).
    - eapply nsteps_trans;
        [eapply (pure_step_nsteps_ctx [InjLCtx]); exact Ha2|].
      exact (pure_injlc a2 I). }
  iExists a1, a2. by iFrame.
Qed.

(* Build a [prel] for a right injection from a [prel] for its argument. *)
Lemma prel_injr `{Σ : gFunctors} e e' (Φ : val → val → iProp Σ) :
  prel e e' Φ -∗
  prel (InjR e) (InjR e')
    (λ w1 w2, ∃ a1 a2, ⌜w1 = InjRV a1⌝ ∗ ⌜w2 = InjRV a2⌝ ∗ Φ a1 a2)%I.
Proof.
  iIntros "H".
  iDestruct (prel_steps_to_val with "H")
    as (a1 a2 n1 n2) "(%Ha1 & %Ha2 & HΦ)".
  rewrite /prel /=.
  iExists (InjRV a1), (InjRV a2), _, _.
  iSplitR.
  { iPureIntro. split.
    - eapply nsteps_trans;
        [eapply (pure_step_nsteps_ctx [InjRCtx]); exact Ha1|].
      exact (pure_injrc a1 I).
    - eapply nsteps_trans;
        [eapply (pure_step_nsteps_ctx [InjRCtx]); exact Ha2|].
      exact (pure_injrc a2 I). }
  iExists a1, a2. by iFrame.
Qed.

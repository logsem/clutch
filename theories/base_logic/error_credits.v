(** This file implements error credits *)
From Coq Require Import Reals RIneq Psatz.
From Coquelicot Require Import Lim_seq.
From clutch.prelude Require Export base classical Reals_ext NNRbar.
From iris.prelude Require Import options.
From iris.proofmode Require Import tactics.
From iris.algebra Require Export auth numbers.
From iris.base_logic.lib Require Import iprop own.
Import uPred.

Canonical Structure nonnegrealO : ofe := leibnizO nonnegreal.

(** ** RA for the reals in the interval [0, 1) with addition as the operation. *)
Section nonnegreal.
  
  Global Instance R_inhabited : Inhabited R := populate (1%R).
  Global Instance nonnegreal_inhabited : Inhabited nonnegreal := populate (nnreal_one).

  #[local] Open Scope R.
  #[local] Open Scope NNR.

  #[local] Instance nonnegreal_valid_instance : Valid (nonnegreal)  := λ r, r < 1.
  #[local] Instance nonnegreal_validN_instance : ValidN (nonnegreal) := λ _ r, r < 1.
  #[local] Instance nonnegreal_pcore_instance : PCore (nonnegreal) := λ _, Some 0.
  #[local] Instance nonnegreal_op_instance : Op (nonnegreal) := λ x y, (x + y).
  #[local] Instance nonnegreal_equiv : Equiv nonnegreal := λ x y, x = y.

  Definition nonnegreal_op (x y : nonnegreal) : x ⋅ y = x + y := eq_refl.

  #[local] Lemma Rle_0_le_minus (x y : R) : x <= y → 0 <= y - x.
  Proof. lra. Qed.

  Lemma nonnegreal_included (x y : nonnegreal) : x ≼ y ↔ x <= y.
  Proof.
    split; intros.
    - destruct x, y => /=.
      destruct H as ((z & Hz) & H).
      rewrite nonnegreal_op /nnreal_plus in H.
      simplify_eq. lra.
    - destruct x as (x & Hx), y as (y & Hy).
      simpl in H.
      eexists ({| nonneg := y - x ; cond_nonneg := Rle_0_le_minus x y H |}).
      rewrite nonnegreal_op /= /equiv/nonnegreal_equiv /=.
      apply nnreal_ext => /=. lra.
  Qed.

  Lemma nonnegreal_ra_mixin : RAMixin nonnegreal.
  Proof.
    apply ra_total_mixin; try by eauto.
    - solve_proper.
    - solve_proper.
    - intros ? ? ?.
      rewrite /equiv/nonnegreal_equiv.
      apply nnreal_ext; simpl; lra.
    - intros ? ?.
      rewrite /equiv/nonnegreal_equiv.
      apply nnreal_ext; simpl; lra.
    - intros ?.
      rewrite /equiv/nonnegreal_equiv.
      apply nnreal_ext; simpl; lra.
    - intros ? ? ?.
      apply nonnegreal_included; simpl; lra.
    - rewrite /valid/nonnegreal_valid_instance.
      rewrite /op/nonnegreal_op_instance /=.
      intros ? ? ?.
      pose (cond_nonneg y). lra.
  Qed.

  Canonical Structure nonnegrealR : cmra := discreteR nonnegreal nonnegreal_ra_mixin.

  Global Instance nonnegreal_cmra_discrete : CmraDiscrete nonnegrealR.
  Proof. apply discrete_cmra_discrete. Qed.
  Local Instance nonnegreal_unit_instance : Unit nonnegreal := nnreal_zero.

  Lemma nonnegreal_ucmra_mixin : UcmraMixin nonnegreal.
  Proof.
    split.
    - rewrite /valid.
      rewrite /nonnegreal_valid_instance.
      simpl. lra.
    - rewrite /LeftId.
      intro.
      rewrite /equiv/nonnegreal_equiv/op/nonnegreal_op_instance/=.
      apply nnreal_ext; simpl; lra.
    - rewrite /pcore/nonnegreal_pcore_instance; auto.
  Qed.

  Canonical Structure nonnegrealUR : ucmra := Ucmra nonnegreal nonnegreal_ucmra_mixin.

  Lemma nonnegreal_add_cancel_l (x y z : nonnegreal) :
    z + x = z + y ↔ x = y.
  Proof.
    rewrite /nnreal_plus.
    split; intro H.
    - apply nnreal_ext. simplify_eq. lra.
    - simplify_eq; auto.
  Qed.

  Global Instance nonnegreal_cancelable (x : nonnegreal) : Cancelable x.
  Proof. by intros ???? ?%nonnegreal_add_cancel_l. Qed.

  Lemma nonnegreal_local_update (x y x' y' : nonnegreal) :
    y' <= y → x + y' = x' + y → (x,y) ~l~> (x',y').
  Proof.
    intros ??; apply (local_update_unital_discrete x y x' y') => z H1 H2.
    compute in H2; simplify_eq; simpl.
    destruct y, x', y', z; simplify_eq; simpl.
    split.
    - compute; compute in *.
      eapply Rle_lt_trans; [| eapply H1].
      lra.
    - compute.
      apply nnreal_ext; simpl in *; lra.
  Qed.

  Global Instance nonnegreal_is_op (n1 n2 : nonnegreal) : IsOp (n1 + n2) n1 n2.
  Proof. done. Qed.

End nonnegreal.

Class ecGpreS (Σ : gFunctors) := EcGpreS {
  ecGpreS_inG :: inG Σ (authR nonnegrealUR)
}.

Class ecGS (Σ : gFunctors) := EcGS {
  ecGS_inG : inG Σ (authR nonnegrealUR);
  ecGS_name : gname;
}.

Global Hint Mode ecGS - : typeclass_instances.
Local Existing Instances ecGS_inG ecGpreS_inG.

Definition ecΣ := #[GFunctor (authR (nonnegrealUR))].
Global Instance subG_ecΣ {Σ} : subG ecΣ Σ → ecGpreS Σ.
Proof. solve_inG. Qed.

(** The internal authoritative part of the credit ghost state,
  tracking how many credits are available in total.
  Users should not directly interface with this. *)
Local Definition ec_supply_def `{!ecGS Σ} (ε : nonnegreal) : iProp Σ := own ecGS_name (● ε).
Local Definition ec_supply_aux : seal (@ec_supply_def). Proof. by eexists. Qed.
Definition ec_supply := ec_supply_aux.(unseal).
Local Definition ec_supply_unseal :
  @ec_supply = @ec_supply_def := ec_supply_aux.(seal_eq).
Global Arguments ec_supply {Σ _} ε.

(** The user-facing error resource, denoting ownership of [ε] error credits. *)
Local Definition ec_def `{!ecGS Σ} (ε : nonnegreal) : iProp Σ := own ecGS_name (◯ ε).
Local Definition ec_aux : seal (@ec_def). Proof. by eexists. Qed.
Definition ec := ec_aux.(unseal).
Local Definition ec_unseal :
  @ec = @ec_def := ec_aux.(seal_eq).
Global Arguments ec {Σ _} ε.

Notation "'↯'  ε" := (∃ (x : nonnegreal), ⌜x.(nonneg) = ε%R⌝ ∗ ec x)%I
  (at level 1).

Section error_credit_theory.
  Context `{!ecGS Σ}.
  Implicit Types (P Q : iProp Σ).

  #[local] Open Scope R.

  (** Error credit rules *)
  Lemma ec_split (ε1 ε2 : R) :
    0 <= ε1 →
    0 <= ε2 →
    ↯ (ε1 + ε2) ⊢ ↯ ε1 ∗ ↯ ε2.
  Proof.
    iIntros (Hx1 Hx2) "(%x & %Hx & Hx)".
    rewrite ec_unseal /ec_def.
    set (x1' := mknonnegreal _ Hx1).
    set (x2' := mknonnegreal _ Hx2).
    assert (x = (x1' + x2')%NNR) as -> by apply nnreal_ext => //=.
    rewrite auth_frag_op own_op.
    iDestruct (own_op with "Hx") as "[Hx1 Hx2]".
    iSplitL "Hx1"; by iExists _; iFrame.
  Qed.

  Lemma ec_split_le (r1 r2 : R) :
    0 <= r1 <= r2 →
    ↯ r2 ⊢ ↯ r1 ∗ ↯ (r2 - r1).
  Proof.
    iIntros (?).
    assert (r2 = (r1 + (r2 - r1))%R) as Hr2 by lra.
    rewrite {1}Hr2.
    apply ec_split; lra.
  Qed.

  Lemma ec_combine (r1 r2 : R) :
    ↯ r1 ∗ ↯ r2 ⊢ ↯ (r1 + r2).
  Proof.
    iIntros "[(%x1 & <- & Hr1) (%x2 & <- & Hr2)]".
    rewrite ec_unseal /ec_def.
    iExists (x1 + x2)%NNR.
    iSplit; [done|].
    rewrite auth_frag_op own_op.
    iFrame.
  Qed.

  Lemma ec_zero : ⊢ |==> ↯ 0.
  Proof.
    rewrite ec_unseal /ec_def.
    iExists nnreal_zero.
    iMod own_unit as "H".
    iModIntro. iSplit; done.
  Qed.

  Lemma ec_supply_bound (ε1 : R) (ε2 : nonnegreal) :
    ec_supply ε2 -∗ ↯ ε1 -∗ ⌜ε1 <= ε2⌝.
  Proof.
    rewrite ec_unseal /ec_def ec_supply_unseal /ec_supply_def.
    iIntros "H1 (%r & <- & H2)".
    iDestruct (own_valid_2 with "H1 H2") as "%Hop".
    by eapply auth_both_valid_discrete in Hop as [Hlt%nonnegreal_included ?].
  Qed.

  Lemma ec_supply_ec_inv r1 x2 :
    ec_supply x2 -∗ ↯ r1 -∗ ∃ x1 x3, ⌜x2 = (x1 + x3)%NNR⌝ ∗ ⌜x1.(nonneg) = r1⌝.
  Proof.
    iIntros "Hx2 Hr1".
    iDestruct (ec_supply_bound with "Hx2 Hr1") as %Hb.
    iDestruct "Hr1" as (x1) "[<- Hx1]".
    set (x3 := nnreal_minus x2 x1 Hb).
    iExists _, x3. iSplit; [|done].
    iPureIntro. apply nnreal_ext=>/=; lra.
  Qed.

  (** The statement of this lemma is a bit convoluted, because only implicitly (by validity and
      unfolding) can we conclude that [0 <= r1 <= x2] so thus that [x2 - r1] is nonnegative *)
  Lemma ec_supply_decrease (r1 : R) (x2 : nonnegreal) :
    ec_supply x2 -∗ ↯ r1 -∗ |==> ∃ x1 x3, ⌜(x2 = x3 + x1)%NNR⌝ ∗ ⌜x1.(nonneg) = r1⌝ ∗ ec_supply x3.
  Proof.
    iIntros "Hx2 Hr1".
    iDestruct (ec_supply_ec_inv with "Hx2 Hr1") as %(x1 & x3 & -> & <-).
    iDestruct "Hr1" as (x1') "[% Hx1]".
    rewrite ec_unseal /ec_def ec_supply_unseal /ec_supply_def.
    iMod (own_update_2 with "Hx2 Hx1") as "Hown".
    { eapply (auth_update_dealloc _ _ x3), nonnegreal_local_update.
      - apply cond_nonneg.
      - apply nnreal_ext =>/=. lra. }
    iModIntro.
    iExists _, _. iFrame. iSplit; [|done].
    iPureIntro. apply nnreal_ext=>/=; lra.
  Qed.

  Lemma ec_supply_increase (ε1 ε2 : nonnegreal) :
    ε1 + ε2 < 1 →
    ec_supply ε1 -∗ |==> ec_supply (ε1 + ε2)%NNR ∗ ↯ ε2.
  Proof.
    rewrite ec_unseal /ec_def.
    rewrite ec_supply_unseal /ec_supply_def.
    iIntros (?) "H".
    iMod (own_update with "H") as "[$ $]"; [|done].
    eapply auth_update_alloc.
    apply (local_update_unital_discrete _ _ _ _) => z H1 H2.
    split; [done|].
    apply nnreal_ext. simpl.
    rewrite Rplus_comm.
    apply Rplus_eq_compat_l.
    rewrite H2 /=. lra.
  Qed.

  Lemma ec_weaken (r1 r2 : R) :
    0 <= r2 <= r1 → ↯ r1 -∗ ↯ r2.
  Proof.
    iIntros (?) "Hr1".
    assert (r1 = (r1 - r2) + r2) as -> by lra.
    iDestruct (ec_split with "Hr1") as "[? $]"; lra.
  Qed.

  Lemma ec_eq x1 x2 :
    x1 = x2 → ↯ x1 -∗ ↯ x2.
  Proof. iIntros (->) "$". Qed.

  Lemma ec_supply_eq x1 x2 :
    (x1.(nonneg) = x2.(nonneg)) → ec_supply x1 -∗ ec_supply x2.
  Proof.
    iIntros (?) "?".
    replace x1 with x2; [iFrame|by apply nnreal_ext].
  Qed.

  Lemma ec_contradict (ε : R) :
    1 <= ε → ↯ ε ⊢ False.
  Proof.
    iIntros (Hge1) "(% & <- & Hε)".
    rewrite ec_unseal /ec_def.
    iDestruct (own_valid with "Hε") as %?%auth_frag_valid_1.
    destruct x.
    compute in H.
    simpl in *.
    lra.
  Qed.

  Lemma ec_valid (ε : R) : ↯ ε -∗ ⌜(0<=ε<1)%R⌝.
  Proof.
    iIntros "(%&<-&H)".
    rewrite ec_unseal /ec_def.
    iDestruct (own_valid with "H") as %?%auth_frag_valid_1.
    destruct x. compute in H. simpl in *. iPureIntro. lra.
  Qed. 

  #[local] Lemma err_amp_power ε k :
    0 < ε →
    1 < k →
    ∃ n, 1 <= ε * k ^ n.
  Proof.
    intros Hε Hk.
    destruct (Lim_seq.is_lim_seq_geom_p k Hk (λ r, / ε <= r)) as [n Hn] => /=.
    - exists (/ ε). real_solver.
    - exists n.
      apply (Rmult_le_reg_l (/ ε)).
      + apply Rinv_0_lt_compat, Hε.
      + rewrite -Rmult_assoc Rinv_l; [|lra].
        rewrite Rmult_1_l Rmult_1_r. by apply Hn.
  Qed.

  Lemma ec_ind_amp_external (ε k : R) P :
    0 < ε →
    1 < k →
    (∀ (ε' : R), 0 < ε' → □ (↯ (k * ε') -∗ P) ∗ ↯ ε' ⊢ P) →
    (↯ ε ⊢ P).
  Proof.
    iIntros (Hε Hk Hamp) "Herr".
    destruct (err_amp_power ε k) as [n Hn]; [done|done|].
    iInduction n as [|m] "IH" forall (ε Hε Hn Hk) "Herr".
    - iDestruct (ec_contradict with "Herr") as %[]. lra.
    - iApply (Hamp with "[$Herr]"); [done|].
      iIntros "!> Herr".
      iApply ("IH" with "[] [] [//] Herr"); iPureIntro.
      + real_solver.
      + simpl in Hn. lra.
  Qed.


  #[local] Lemma ec_ind_simpl_external_aux (ε ε' k : R) P :
    0 < ε →
    ε <= ε' ->
    1 < k →
    ((↯ (k * ε) -∗ P) ∗ ↯ ε ⊢ P) →
    (↯ ε' ⊢ P).
  Proof.
    iIntros (Hε Hleq Hk Hamp) "Herr".
    assert (exists n:nat, 1 <= n*(k-1)*ε + ε') as Haux.
    {
      edestruct (Rcomplements.nfloor_ex (1/((k-1)*ε))) as [n [Hn1 Hn2]].
      - apply Rmult_le_pos; [lra|].
        left.
        apply Rinv_0_lt_compat.
        real_solver.
      - exists (S n).
        rewrite S_INR.
        transitivity ((1 / ((k - 1) * ε)) * (k - 1) * ε + ε').
        + rewrite Rmult_assoc.
          rewrite /Rdiv Rmult_1_l.
          rewrite Rinv_l; [lra |].
          assert (0<(k-1)*ε); real_solver.
        + apply Rplus_le_compat_r.
          apply Rmult_le_compat_r; [lra|].
          apply Rmult_le_compat_r; lra.
    }
    destruct Haux as [n Hn].
    iInduction n as [|m] "IH" forall (ε ε' Hε Hleq Hn Hk Hamp) "Herr".
    - iDestruct (ec_contradict with "Herr") as %[].
      simpl in Hn.
      lra.
    - replace (ε') with (ε + (ε' - ε)) by lra.
      iDestruct (ec_split with "Herr") as "[Herr1 Herr2]"; [lra | lra |].
      iApply (Hamp with "[$Herr1 Herr2]").
      iIntros "Herr".
      assert (k * ε = (k-1)*ε + ε) as ->; [lra |].
      iDestruct (ec_split with "Herr") as "[Herr3 Herr4]"; [ real_solver | lra |].
      iDestruct (ec_combine with "[$Herr2 $Herr3]") as "Herr".
      iDestruct (ec_combine with "[$Herr $Herr4]") as "Herr".
      iApply ("IH" $! ε with "[] [] [] [] [] Herr"); auto.
      + iPureIntro.
        replace (ε' - ε + (k-1) * ε + ε) with (ε' + (k-1) * ε) by lra.
        rewrite <- (Rplus_0_r ε) at 1.
        apply Rplus_le_compat; auto.
        apply Rmult_le_pos; lra.
      + iPureIntro.
        replace (ε' - ε + (k - 1) * ε + ε) with (ε' + (k - 1) * ε) by lra.
        replace (m * (k - 1) * ε + (ε' + (k - 1) * ε)) with ((m + 1) * (k - 1) * ε + ε') by lra.
        etrans; eauto.
        rewrite S_INR //.
  Qed.


  Lemma ec_ind_simpl_external (ε k : R) P :
    0 < ε →
    1 < k →
    ((↯ (k * ε) -∗ P) ∗ ↯ ε ⊢ P) →
    (↯ ε ⊢ P).
  Proof.
    iIntros (Hε HK Hamp).
    eapply ec_ind_simpl_external_aux; eauto.
    lra.
  Qed.

  #[local] Lemma ec_ind_simpl_aux (ε ε' k : R) P :
    0 < ε →
    ε <= ε' ->
    1 < k →
    □ ((↯ (k * ε) -∗ P) ∗ ↯ ε -∗ P) ⊢
    (↯ ε' -∗ P).
  Proof.
    iIntros (Hε Hleq Hk) "#Hamp Herr".
    assert (exists n:nat, 1 <= n*(k-1)*ε + ε') as Haux.
    {
      edestruct (Rcomplements.nfloor_ex (1/((k-1)*ε))) as [n [Hn1 Hn2]].
      - apply Rmult_le_pos; [lra|].
        left.
        apply Rinv_0_lt_compat.
        real_solver.
      - exists (S n).
        rewrite S_INR.
        transitivity ((1 / ((k - 1) * ε)) * (k - 1) * ε + ε').
        + rewrite Rmult_assoc.
          rewrite /Rdiv Rmult_1_l.
          rewrite Rinv_l; [lra |].
          assert (0<(k-1)*ε); real_solver.
        + apply Rplus_le_compat_r.
          apply Rmult_le_compat_r; [lra|].
          apply Rmult_le_compat_r; lra.
    }
    destruct Haux as [n Hn].
    iInduction n as [|m] "IH" forall (ε ε' Hε Hleq Hn Hk) "Hamp Herr".
    - iDestruct (ec_contradict with "Herr") as %[].
      simpl in Hn.
      lra.
    - replace (ε') with (ε + (ε' - ε)) by lra.
      iDestruct (ec_split with "Herr") as "[Herr1 Herr2]"; [lra | lra |].
      iApply ("Hamp" with "[$Herr1 Herr2]").
      iIntros "Herr".
      assert (k * ε = (k-1)*ε + ε) as ->; [lra |].
      iDestruct (ec_split with "Herr") as "[Herr3 Herr4]"; [ real_solver | lra |].
      iDestruct (ec_combine with "[$Herr2 $Herr3]") as "Herr".
      iDestruct (ec_combine with "[$Herr $Herr4]") as "Herr".
      iApply ("IH" $! ε with "[] [] [] [] [] Herr"); auto.
      + iPureIntro.
        replace (ε' - ε + (k-1) * ε + ε) with (ε' + (k-1) * ε) by lra.
        rewrite <- (Rplus_0_r ε) at 1.
        apply Rplus_le_compat; auto.
        apply Rmult_le_pos; lra.
      + iPureIntro.
        replace (ε' - ε + (k - 1) * ε + ε) with (ε' + (k - 1) * ε) by lra.
        replace (m * (k - 1) * ε + (ε' + (k - 1) * ε)) with ((m + 1) * (k - 1) * ε + ε') by lra.
        etrans; eauto.
        rewrite S_INR //.
      + replace ((k - 1) * ε + ε) with (k * ε) by lra.
        auto.
  Qed.

  Lemma ec_ind_simpl (ε k : R) P :
    0 < ε →
    1 < k →
    □((↯ (k * ε) -∗ P) ∗ ↯ ε -∗ P) ⊢
    (↯ ε -∗ P).
  Proof.
    iIntros (Hε Hk) "#Hamp Herr".
    iApply ec_ind_simpl_aux; eauto.
    lra.
  Qed.



  (* TODO: can [ec_ind_amp] be derived from [ec_ind_amp_external] ? *)
  Lemma ec_ind_amp (ε k : R) P :
    0 < ε →
    1 < k →
    □ (∀ (ε' : R), ⌜0 < ε'⌝ -∗ □ (↯ (k * ε') -∗ P) -∗ ↯ ε' -∗ P) ⊢
    (↯ ε -∗ P).
  Proof.
    iIntros (Hpos Hgt1) "#Hamp Herr".
    destruct (err_amp_power ε k) as [n Hn]; [done|done|].
    iInduction n as [|m] "IH" forall (ε Hpos Hn Hgt1) "Herr".
    - iDestruct (ec_contradict with "Herr") as %[].
      simpl in Hn. lra.
    - iApply ("Hamp" with "[//] [] Herr").
      iIntros "!# Herr".
      iApply ("IH" with "[] [] [//] Herr"); iPureIntro.
      + real_solver.
      + simpl in Hn. lra.
  Qed.

  Global Instance ec_timeless r : Timeless (↯ r).
  Proof. rewrite ec_unseal /ec_def. apply _. Qed.

  Global Instance from_sep_ec_combine r1 r2 :
    FromSep (↯ (r1 + r2)) (↯ r1) (↯ r2) | 0.
  Proof. rewrite /FromSep ec_combine //. Qed.

  Global Instance into_sep_ec_add r1 r2 :
    0 <= r1 → 0 <= r2 →
    IntoSep (↯ (r1 + r2)) (↯ r1) (↯ r2) | 0.
  Proof. rewrite /IntoSep. apply ec_split. Qed.

  Global Instance combine_sep_as_ec_add r1 r2 :
    CombineSepAs (↯ r1) (↯ r2) (↯ (r1 + r2)) | 0.
  Proof. rewrite /CombineSepAs ec_combine //. Qed.

End error_credit_theory.

Lemma ec_alloc `{!ecGpreS Σ} (n : nonnegreal) :
  (n < 1)%R → ⊢ |==> ∃ _ : ecGS Σ, ec_supply n ∗ ↯ n.
Proof.
  iIntros (?).
  rewrite ec_unseal /ec_def ec_supply_unseal /ec_supply_def.
  iMod (own_alloc (● n ⋅ ◯ n)) as (γEC) "[H● H◯]".
  - apply auth_both_valid_2.
    + compute. destruct n; simpl in H. lra.
    + apply nonnegreal_included; lra.
  - pose (C := EcGS _ _ γEC).
    iModIntro. iExists C. by iFrame.
Qed.

#[global] Hint Resolve cond_nonneg : core.

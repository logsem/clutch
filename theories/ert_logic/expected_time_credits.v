From Coq Require Import Reals RIneq Psatz.
From tachis.prelude Require Export base classical Reals_ext NNRbar.
From iris.prelude Require Import options.
From iris.proofmode Require Import tactics.
From iris.algebra Require Export auth numbers.
From iris.base_logic.lib Require Import iprop own.

Import uPred.

(* TODO: move to [algebra/NNR.v] *)

(** ** Non-negative real numbers with addition as the operation. *)
Section NNR.
  Canonical Structure NNRO : ofe := leibnizO nonnegreal.

  Local Instance NNR_valid_instance : Valid (nonnegreal)  := (λ _, True).
  Local Instance NNR_validN_instance : ValidN (nonnegreal) := (λ _ _, True).
  Local Instance NNR_pcore_instance : PCore (nonnegreal) := λ _, Some (nnreal_zero).
  Local Instance NNR_op_instance : Op (nonnegreal) := λ x y, nnreal_plus x y.
  Local Instance NNR_equiv : Equiv nonnegreal := λ x y, x = y.

  Definition NNR_op (x y : nonnegreal) : x ⋅ y = nnreal_plus x y := eq_refl.

  Lemma NNR_included (x y : nonnegreal) : x ≼ y ↔ (x <= y)%R.
  Proof.
    split; intros.
    - destruct x.
      destruct y.
      simpl.
      rewrite /included in H.
      destruct H as ((z & Hz) & H).
      rewrite NNR_op /nnreal_plus in H.
      simplify_eq.
      lra.
    - rewrite /included.
      destruct x as (x & Hx).
      destruct y as (y & Hy).
      simpl in H.
      eexists ({| nonneg := y - x ; cond_nonneg := Rle_0_le_minus x y H |}).
      rewrite NNR_op/=.
      rewrite /equiv/NNR_equiv/=.
      apply nnreal_ext.
      simpl.
      lra.
  Qed.

  Lemma NNR_ra_mixin : RAMixin nonnegreal.
  Proof.
    apply ra_total_mixin; try by eauto.
    - solve_proper.
   - intros ? ? ?.
      rewrite /equiv/NNR_equiv.
      apply nnreal_ext; simpl; lra.
    - intros ? ?.
      rewrite /equiv/NNR_equiv.
      apply nnreal_ext; simpl; lra.
    - intros ?.
      rewrite /equiv/NNR_equiv.
      apply nnreal_ext; simpl; lra.
    - intros ? ? ?.
      rewrite /core. simpl. rewrite /included.
      eexists _.  rewrite /equiv/NNR_equiv.
      apply nnreal_ext; simpl. instantiate (1:=nnreal_zero). simpl. lra.
  Qed.

  (* Massive hack to override Coq reals's [id : R → R] *)
  Definition id {A} := (λ (a : A), a).

  Canonical Structure nonnegrealR : cmra := discreteR nonnegreal NNR_ra_mixin.

  Global Instance NNR_cmra_discrete : CmraDiscrete nonnegrealR.
  Proof. apply discrete_cmra_discrete. Qed.

  Local Instance NNR_unit_instance : Unit nonnegreal := Finite nnreal_zero.

  Lemma NNR_ucmra_mixin : UcmraMixin nonnegreal.
  Proof.
    split.
    - rewrite /valid.
      rewrite /NNR_valid_instance/NNR_unit_instance/ε. done.
    - rewrite /LeftId.
      intro.
      rewrite /equiv/NNR_equiv/op/NNR_op_instance/=.
      destruct x => //. f_equal.
      apply nnreal_ext; simpl; lra.
    - rewrite /pcore/NNR_pcore_instance; auto.
  Qed.

  Canonical Structure nonnegrealUR : ucmra := Ucmra nonnegreal NNR_ucmra_mixin.

  Lemma NNR_local_update (x y x' y' : nonnegreal) :
    (y' <= y)%R -> nnreal_plus x y' = nnreal_plus x' y → (x,y) ~l~> (x',y').
  Proof.
    intros ??; apply (local_update_unital_discrete x y x' y') => z H1 H2.
    compute in H2; simplify_eq; simpl.
    destruct y, x', y', z; simplify_eq; simpl.
    split.
    - compute; compute in *. done.
    - compute.
      apply nnreal_ext; simpl in *; lra.
  Qed.

End NNR.

(** The ghost state for expected time credits *)
Class etcGpreS (Σ : gFunctors) := EtcGpreS {
  etcGpreS_inG :: inG Σ (authR nonnegrealUR)
}.

Class etcGS (Σ : gFunctors) := EtcGS {
  etcGS_inG : inG Σ (authR nonnegrealUR);
  etcGS_name : gname;
}.

Global Hint Mode etcGS - : typeclass_instances.
Local Existing Instances etcGS_inG etcGpreS_inG.

Definition etcΣ := #[GFunctor (authR (nonnegrealUR))].
Global Instance subG_etcΣ {Σ} : subG etcΣ Σ → etcGpreS Σ.
Proof. solve_inG. Qed.

(** The internal authoritative part of the credit ghost state, tracking how many credits are
  available in total.  Users should not directly interface with this. *)
Local Definition etc_supply_def `{!etcGS Σ} (x : nonnegreal) : iProp Σ := own etcGS_name (● x).
Local Definition etc_supply_aux : seal (@etc_supply_def). Proof. by eexists. Qed.
Definition etc_supply := etc_supply_aux.(unseal).
Local Definition etc_supply_unseal :
  @etc_supply = @etc_supply_def := etc_supply_aux.(seal_eq).
Global Arguments etc_supply {Σ _} x.

(** The user-facing error resource, denoting ownership of [x] credits. *)
Local Definition etc_def `{!etcGS Σ} (x : nonnegreal) : iProp Σ := own etcGS_name (◯ x).
Local Definition etc_aux : seal (@etc_def). Proof. by eexists. Qed.
Definition ec := etc_aux.(unseal).
Local Definition etc_unseal :
  @ec = @etc_def := etc_aux.(seal_eq).
Global Arguments ec {Σ _} x.

Notation "'⧖'  r" := (∃ (x : nonnegreal), ⌜x.(nonneg) = r%R⌝ ∗ ec x)%I
  (at level 1).

Section etc_credit_theory.
  Context `{!etcGS Σ}.
  Implicit Types (P Q : iProp Σ).
  Implicit Types (r : R).
  Implicit Types (x : nonnegreal).

  Open Scope R.

  (** Credit rules *)
  Lemma etc_split (r1 r2 : R) :
    0 <= r1 →
    0 <= r2 →
    ⧖ (r1 + r2) ⊢ ⧖ r1 ∗ ⧖ r2.
  Proof.
    iIntros (Hx1 Hx2) "(%x & %Hx & Hx)".
    rewrite etc_unseal /etc_def.
    set (x1' := mknonnegreal _ Hx1).
    set (x2' := mknonnegreal _ Hx2).
    assert (x = (x1' + x2')%NNR) as -> by apply nnreal_ext => //=.
    rewrite auth_frag_op own_op.
    iDestruct (own_op with "Hx") as "[Hx1 Hx2]".
    iSplitL "Hx1"; by iExists _; iFrame.
  Qed.

  Lemma etc_split_le (r1 r2 : R) :
    0 <= r1 <= r2 →
    ⧖ r2 ⊢ ⧖ r1 ∗ ⧖ (r2 - r1).
  Proof.
    iIntros (?).
    assert (r2 = (r1 + (r2 - r1))) as Hr2 by lra.
    rewrite {1}Hr2.
    apply etc_split; lra. 
  Qed. 

  Lemma etc_combine (r1 r2 : R) :
    ⧖ r1 ∗ ⧖ r2 ⊢ ⧖ (r1 + r2).
  Proof.
    iIntros "[(%x1 & <- & Hr1) (%x2 & <- & Hr2)]".
    rewrite etc_unseal /etc_def.
    iExists (x1 + x2)%NNR.
    iSplit; [done|].
    rewrite auth_frag_op own_op.
    iFrame.
  Qed.

  Lemma etc_zero : ⊢ |==> ⧖ 0.
  Proof.
    rewrite etc_unseal /etc_def.
    iExists nnreal_zero.
    iMod own_unit as "H".
    iModIntro. iSplit; done.
  Qed.

  Lemma etc_supply_bound (r1 : R) (x2 : nonnegreal) :
    etc_supply x2 -∗ ⧖ r1 -∗ ⌜r1 <= x2⌝.
  Proof.
    rewrite etc_unseal /etc_def etc_supply_unseal /etc_supply_def.
    iIntros "H1 (%r & <- & H2)".
    iDestruct (own_valid_2 with "H1 H2") as "%Hop".
    by eapply auth_both_valid_discrete in Hop as [Hlt%NNR_included ?].
  Qed.

  Lemma etc_supply_bound' r1 x2 :
    etc_supply x2 -∗ ⧖ r1 -∗ ∃ x1 x3, ⌜x2 = (x1 + x3)%NNR⌝ ∗ ⌜x1.(nonneg) = r1⌝.
  Proof.
    iIntros "Hx2 Hr1".
    iDestruct (etc_supply_bound with "Hx2 Hr1") as %Hb.
    iDestruct "Hr1" as (x1) "[<- Hx1]".
    set (x3 := nnreal_minus x2 x1 Hb).
    iExists _, x3. iSplit; [|done].
    iPureIntro. apply nnreal_ext=>/=; lra.
  Qed.

  (** The statement of this lemma is a bit convoluted, because only implicitly (by validity and
      unfolding) can we conclude that [0 <= r1 <= x2] so thus that [x2 - r1] is nonnegative *)
  Lemma etc_supply_decrease (r1 : R) (x2 : nonnegreal) :
    etc_supply x2 -∗ ⧖ r1 -∗ |==> ∃ x1 x3, ⌜(x2 = x3 + x1)%NNR⌝ ∗ ⌜x1.(nonneg) = r1⌝ ∗ etc_supply x3.
  Proof.
    iIntros "Hx2 Hr1".
    iDestruct (etc_supply_bound' with "Hx2 Hr1") as %(x1 & x3 & -> & <-).
    iDestruct "Hr1" as (x1') "[% Hx1]".
    rewrite etc_unseal /etc_def etc_supply_unseal /etc_supply_def.
    iMod (own_update_2 with "Hx2 Hx1") as "Hown".
    { eapply (auth_update_dealloc _ _ x3), NNR_local_update.
      - apply cond_nonneg.
      - apply nnreal_ext =>/=. lra. }
    iModIntro.
    iExists _, _. iFrame. iSplit; [|done].
    iPureIntro. apply nnreal_ext=>/=; lra.
  Qed.

  Lemma etc_supply_decrease_1 (x1 : nonnegreal) :
    etc_supply x1 -∗ ⧖ 1 -∗ |==> ∃ x2, ⌜(x1 = x2 + 1)%NNR⌝ ∗ etc_supply x2.
  Proof.
    iIntros "Hx2 Hc".
    iMod (etc_supply_decrease with "Hx2 Hc") as (?? -> ?) "Hx".
    iModIntro. iExists _. iFrame. iPureIntro.
    apply nnreal_ext=>/=. lra.
  Qed.

  Lemma etc_supply_increase (x1 : nonnegreal) (r2 : R) :
    0 <= r2 →
    etc_supply x1 -∗ |==> ∃ x2, etc_supply (x1 + x2)%NNR ∗ ⌜x2.(nonneg) = r2⌝ ∗ ⧖ r2.
  Proof.
    rewrite etc_unseal /etc_def etc_supply_unseal /etc_supply_def.
    iIntros (Hr2) "H".
    set (x2 := mknonnegreal _ Hr2).
    iExists x2.
    iMod (own_update with "H") as "[$ ?]".
    { apply (auth_update_alloc _ (x1 + x2)%NNR x2).
      apply (local_update_unital_discrete _ _ _ _) => z H1 H2.
      split; [done|]. simplify_eq.
      rewrite nnreal_plus_comm left_id //. }
    iModIntro. iSplit; [done|].
    iExists _. by iFrame.
  Qed.

  Lemma etc_weaken (r1 r2 : R) :
     0 <= r2 <= r1 → ⧖ r1 -∗ ⧖ r2.
  Proof.
    iIntros (?) "Hr1".
    assert (r1 = (r1 - r2) + r2) as -> by lra.
    iDestruct (etc_split with "Hr1") as "[? $]"; lra.
  Qed.

  Lemma etc_irrel (r1 r2:R) :
    r1=r2 → ⧖ r1 -∗ ⧖ r2.
  Proof.
    iIntros (->) "Hr1". done.
  Qed.

  Lemma etc_nat_Sn (n : nat) :
    ⧖ (S n) ⊣⊢ ⧖ 1 ∗ ⧖ n.
  Proof.
    assert (INR (S n) = 1 + n)%R as ->.
    { rewrite -Nat.add_1_l plus_INR S_INR INR_0. lra. }
    iSplit.
    - iApply etc_split; [lra|].
      replace 0 with (INR 0); [|done]. eapply le_INR. lia.
    - iApply etc_combine.
  Qed.

  Lemma etc_split_list {A} (xs : list A) (r : R) :
    0 <= r →
    ⧖ (length xs * r) ⊢ [∗ list] _ ∈ xs, ⧖ r.
  Proof.
    iIntros (?) "Hxs".
    iInduction xs as [|x xs] "IH"; [auto|].
    assert (length (x :: xs) * r = r + length xs * r)%R as ->.
    { rewrite cons_length S_INR. lra. }
    iDestruct (etc_split with "Hxs") as "[$ Hr]"; [done| |].
    { assert (0 <= length xs)%R by eauto with real. real_solver. }
    by iApply "IH".
  Qed.   

  Lemma etc_supply_irrel x1 x2 :
    (x1.(nonneg) = x2.(nonneg)) → etc_supply x1 -∗ etc_supply x2.
  Proof.
    iIntros (?) "?".
    replace x1 with x2; [iFrame|by apply nnreal_ext].
  Qed.

  Global Instance etc_timeless r : Timeless (⧖ r).
  Proof. rewrite etc_unseal /etc_def. apply _. Qed.

  Global Instance from_sep_etc_combine r1 r2 :
    FromSep (⧖ (r1 + r2)) (⧖ r1) (⧖ r2) | 0.
  Proof. rewrite /FromSep etc_combine //. Qed.

  Global Instance into_sep_etc_add r1 r2 :
    0 <= r1 → 0 <= r2 →
    IntoSep (⧖ (r1 + r2)) (⧖ r1) (⧖ r2) | 0.
  Proof. rewrite /IntoSep. apply etc_split. Qed.

  Global Instance combine_sep_as_etc_add r1 r2 :
    CombineSepAs (⧖ r1) (⧖ r2) (⧖ (r1 + r2)) | 0.
  Proof. rewrite /CombineSepAs etc_combine //. Qed.

End etc_credit_theory.

Lemma etc_alloc `{!etcGpreS Σ} (x : nonnegreal) :
  ⊢|==> ∃ _ : etcGS Σ, etc_supply x ∗ ⧖ x.
Proof.
  rewrite etc_unseal /etc_def etc_supply_unseal /etc_supply_def.
  iMod (own_alloc (● x ⋅ ◯ x)) as (γEC) "[H● H◯]".
  - by apply auth_both_valid_2.
  - iExists (EtcGS _ _ γEC). iModIntro. iFrame. iExists _. by iFrame.
Qed.

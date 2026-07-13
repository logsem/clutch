(** This file implements Renyi-DP error credits *)
From Stdlib Require Import Reals RIneq Psatz.
From Coquelicot Require Import Lim_seq.
From clutch.prelude Require Export base classical Reals_ext NNRbar.
From iris.prelude Require Import options.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Export auth numbers.
From iris.base_logic.lib Require Import iprop own.
Import uPred.

(** ** RA for Renyi-DP credits.

    An element is a pair [(α, ρ)] of a Renyi order [α : nonnegreal] and a
    budget [ρ : nonnegreal].

    - Valid elements are those [Renyi α ρ] with [1 <= α] (the budget is
      nonnegative by construction of [nonnegreal]).
    - The operation takes the min on the order [α] and adds the budgets [ρ].
      This uses a weakening of the order, due to the fact that if
      [α1 < α2] and a mechanism is [(α2,ρ)-RDP] then it is also [(α1,ρ)-RDP].
    - The core of [Renyi α ρ] is [Renyi α 0]. *)

Definition renyi_car : Set := nonnegreal * nonnegreal.

#[local] Open Scope R.
#[local] Open Scope NNR.

Canonical Structure renyi_carO : ofe := leibnizO renyi_car.

Section renyi_ra.

  #[local] Instance renyi_valid_instance : Valid renyi_car :=
    λ '(α, ρ), 1 <= α.

  #[local] Instance renyi_pcore_instance : PCore renyi_car :=
    λ '(α, ρ), Some (α, 0).


  #[local] Instance renyi_op_instance : Op renyi_car :=
    λ '(α1, ρ1) '(α2, ρ2), (NNRmin α1 α2, ρ1 + ρ2).

  Lemma renyi_op_same α r s : (α, r) ⋅ (α, s) = (α, r + s).
  Proof. by rewrite /op /renyi_op_instance NNRmin_left //. Qed.

  Lemma renyi_ra_mixin : RAMixin renyi_car.
  Proof.
    apply ra_total_mixin.
    - intros []; eauto.
    - intros x y1 y2 ->. done.
    - intros x y ->. done.
    - intros x y ->. done.
    - intros [α r] [β s] [γ t].
      rewrite /op /renyi_op_instance /=.
      rewrite NNRmin_assoc.
      f_equal; apply nnreal_ext; simpl; lra.
    - intros [α r] [β s].
      rewrite /op /renyi_op_instance /=.
      rewrite NNRmin_comm.
      f_equal; apply nnreal_ext; simpl; lra.
    - intros [α r].
      rewrite /core /pcore /renyi_pcore_instance /=.
      rewrite /op /renyi_op_instance /=.
      rewrite NNRmin_left; [|lra].
      f_equal; apply nnreal_ext; simpl; lra.
    - intros [α r]; done.
    - intros x y [z ->].
      destruct x as [α r], z as [β s].
      rewrite /core /pcore /renyi_pcore_instance /op /renyi_op_instance /=.
      exists (β, 0).
      rewrite /op /renyi_op_instance /=.
      f_equal; apply nnreal_ext; simpl; lra.
    - intros [α r] [β s].
      rewrite /op /renyi_op_instance /valid /renyi_valid_instance /=.
      intros Hle.
      apply (Rle_trans _ _ _ Hle).
      apply Rmin_l.
  Qed.

  Canonical Structure renyi_carR : cmra :=
    discreteR renyi_car renyi_ra_mixin.

  Global Instance renyi_cmra_discrete : CmraDiscrete renyi_carR.
  Proof. apply discrete_cmra_discrete. Qed.

End renyi_ra.

(** [renyi_carR] has no unit, so we take he authoritative
    construction over [optionUR renyi_carR], whose unit is
    [None]. *)
Notation renyi_authR := (authR (optionUR renyi_carR)).

Class rcGpreS (Σ : gFunctors) := RcGpreS {
  rcGpreS_inG :: inG Σ renyi_authR
}.

Class rcGS (Σ : gFunctors) := RcGS {
  rcGS_inG : inG Σ renyi_authR;
  rcGS_name : gname;
}.

Global Hint Mode rcGS - : typeclass_instances.
Local Existing Instances rcGS_inG rcGpreS_inG.

Definition rcΣ := #[GFunctor renyi_authR].
Global Instance subG_rcΣ {Σ} : subG rcΣ Σ → rcGpreS Σ.
Proof. solve_inG. Qed.

(** The authoritative part of the Renyi-credit ghost state, tracking the total
    order/budget available. Users should not directly interface with this. *)
Local Definition rc_supply_def `{!rcGS Σ} (x : renyi_car) : iProp Σ :=
  own rcGS_name (● (Some x)).
Local Definition rc_supply_aux : seal (@rc_supply_def). Proof. by eexists. Qed.
Definition rc_supply := rc_supply_aux.(unseal).
Local Definition rc_supply_unseal :
  @rc_supply = @rc_supply_def := rc_supply_aux.(seal_eq).
Global Arguments rc_supply {Σ _} x.

(** The user-facing resource, denoting ownership of [ρ] budget at order [α]. *)
Local Definition rc_def `{!rcGS Σ} (α ρ : nonnegreal) : iProp Σ :=
  own rcGS_name (◯ (Some ((α, ρ) : renyi_car))).
Local Definition rc_aux : seal (@rc_def). Proof. by eexists. Qed.
Definition rc := rc_aux.(unseal).
Local Definition rc_unseal : @rc = @rc_def := rc_aux.(seal_eq).
Global Arguments rc {Σ _} α ρ.

Notation "↯R ( α , ρ )" := (∃ (x y : nonnegreal), ⌜x.(nonneg) = α%R /\ y.(nonneg) = ρ%R⌝ ∗ rc x y)%I
  (at level 1, format "↯R ( α ,  ρ )").

Section renyi_credit_theory.
  Context `{!rcGS Σ}.
  Implicit Types (α β ρ r s : R).

  #[local] Open Scope R.

  (** Fragments at a common order [α] split and combine, adding the budget. *)
  Lemma rc_split α r s :
    1 <= α ->
    0 <= r ->
    0 <= s ->
    ↯R (α, (r + s)) ⊢ ↯R (α, r) ∗ ↯R (α, s).
  Proof.
    iIntros (Hα Hr Hs) "(%a & %rs & (%Ha & %Hrs) & Hrc)".
    rewrite rc_unseal /rc_def.
    set (r' := mknonnegreal r Hr).
    set (s' := mknonnegreal s Hs).
    assert (rs = (r' + s')%NNR) as ->.
    { apply nnreal_ext. rewrite /r' /s' /=. rewrite Hrs. lra. }
    rewrite -renyi_op_same Some_op auth_frag_op own_op.
    iDestruct "Hrc" as "[H1 H2]".
    iSplitL "H1".
    - iExists a, r'. iFrame "H1". iPureIntro. split; [exact Ha|done].
    - iExists a, s'. iFrame "H2". iPureIntro. split; [exact Ha|done].
  Qed.

  (** Combining fragments takes the min of the orders (order weakening) and
      adds the budgets. *)
  Lemma rc_combine α β r s :
    1 <= α ->
    1 <= β ->
    0 <= r ->
    0 <= s ->
    ↯R (α, r) ∗ ↯R (β, s) ⊢ ↯R (Rmin α β, r + s).
  Proof.
    iIntros (Hα Hβ Hr Hs)
      "[(%a & %ra & (%Ha & %Hra) & H1) (%b & %rb & (%Hb & %Hrb) & H2)]".
    rewrite rc_unseal /rc_def.
    iDestruct (own_op with "[$H1 $H2]") as "H".
    rewrite -auth_frag_op -Some_op /op /renyi_op_instance.
    iExists (NNRmin a b), (ra + rb)%NNR.
    iFrame "H". iPureIntro. split.
    - rewrite /NNRmin /=. rewrite Ha Hb //.
    - rewrite /=. rewrite Hra Hrb //.
  Qed.

  (** The supply also enforces the order side condition [1 <= α]. *)
  Lemma rc_supply_valid (α ρ : nonnegreal) : rc_supply (α, ρ) ⊢ ⌜1 <= α⌝.
  Proof.
    rewrite rc_supply_unseal /rc_supply_def.
    iIntros "H". iDestruct (own_valid with "H") as %Hv.
    rewrite auth_auth_valid Some_valid in Hv.
    iPureIntro. revert Hv. rewrite /cmra_valid /= /renyi_valid_instance //.
  Qed.

  (** Any owned fragment enforces the order side condition [1 <= α]. *)
  Lemma rc_valid α ρ : ↯R (α, ρ) ⊢ ⌜1 <= α⌝.
  Proof.
    iIntros "(%x & %y & (%Hx & %Hy) & Hrc)".
    rewrite rc_unseal /rc_def.
    iDestruct (own_valid with "Hrc") as %Hv.
    rewrite auth_frag_valid Some_valid in Hv.
    iPureIntro. rewrite -Hx. revert Hv.
    rewrite /cmra_valid /= /renyi_valid_instance //.
  Qed.

  (** The supply lower-bounds the order and upper-bounds the budget of any
      fragment: the authoritative order is the min over all fragments. *)
  Lemma rc_supply_bound (α ρ : nonnegreal) (β r : R) :
    rc_supply (α, ρ) -∗ ↯R (β, r) -∗ ⌜α <= β ∧ r <= ρ⌝.
  Proof.
    iIntros "Ha (%x & %y & (%Hx & %Hy) & Hf)".
    rewrite rc_unseal /rc_def rc_supply_unseal /rc_supply_def.
    iDestruct (own_valid_2 with "Ha Hf") as %Hv.
    apply auth_both_valid_discrete in Hv as [Hincl _].
    iPureIntro.
    apply Some_included in Hincl as [Heq | [[γ t] Hz]].
    - inversion Heq; simplify_eq. split; lra.
    - rewrite /op /cmra_op /= /renyi_op_instance in Hz.
      inversion Hz as [[Hαmin Hρ]].
      split.
      + rewrite -Hx. apply Rmin_l.
      + rewrite -Hy. destruct y, t; simpl; lra.
  Qed.


  Lemma rc_supply_rc_inv (α ρ1 ρ2 : nonnegreal) :
    rc_supply (α , ρ2) -∗ ↯R (α, ρ1) -∗ ∃ x y, ⌜ρ2 = (x + y)%NNR⌝ ∗ ⌜x.(nonneg) = ρ1⌝.
  Proof.
    iIntros "Hρ2 Hρ1".
    iDestruct (rc_supply_bound with "Hρ2 Hρ1") as "(% & %Hb)".
    iDestruct "Hρ1" as (α' x) "((% & %) & Hx)".
    set (y := nnreal_minus ρ2 ρ1 Hb).
    iExists _, y. iSplit; [|done].
    iPureIntro. apply nnreal_ext=>/=; lra.
  Qed.

  (** Spend a fragment [↯R (α, ρ)] against the supply, decreasing the total
      budget by [ρ] (the order is unchanged; the frame-preserving update keeps
      the spent fragment at order [α] with zero budget, so the [min] on orders
      matches on both sides). *)
  Lemma rc_supply_decrease (αs ρs : nonnegreal) (α ρ : R) :
    rc_supply (αs, ρs) -∗ ↯R (α, ρ) ==∗
      ∃ ρs' : nonnegreal, ⌜(ρs'.(nonneg) + ρ)%R = ρs⌝ ∗ rc_supply (αs, ρs').
  Proof.
    iIntros "Ha Hf".
    iDestruct (rc_supply_bound with "Ha Hf") as %[Hαle Hρle].
    iDestruct "Hf" as (x y) "((%Hx & %Hy) & Hf)".
    rewrite rc_unseal /rc_def rc_supply_unseal /rc_supply_def.
    assert (0 <= ρs - ρ)%R as Hnn by lra.
    set (ρs' := mknonnegreal _ Hnn).
    iMod (own_update_2 with "Ha Hf") as "H".
    { apply (auth_update _ _ (Some ((αs, ρs') : renyi_car))
                             (Some ((x, 0%NNR) : renyi_car))).
      apply option_local_update.
      apply local_update_discrete => -[[αz ρz]|] Hv Heq.
      - split; [done|].
        rewrite /op /cmra_op /= /renyi_op_instance in Heq.
        assert (Hα : αs = NNRmin x αz) by (apply (f_equal fst) in Heq; done).
        assert (Hρ : ρs = (y + ρz)%NNR) by (apply (f_equal snd) in Heq; done).
        rewrite /op /cmra_op /= /renyi_op_instance.
        rewrite /op /cmra_op /= /renyi_op_instance -Hα.
        f_equal.
        apply nnreal_ext => /=. rewrite /ρs' /=.
        apply (f_equal nonneg) in Hρ. simpl in Hρ. rewrite Hy in Hρ. lra.
      - split; [done|].
        rewrite /= in Heq.
        assert (Hα : αs = x) by (apply (f_equal fst) in Heq; done).
        assert (Hρ : ρs = y) by (apply (f_equal snd) in Heq; done).
        rewrite /=.
        f_equal; [exact Hα|].
        apply nnreal_ext => /=. rewrite /ρs' /=.
        apply (f_equal nonneg) in Hρ. simpl in Hρ. rewrite Hy in Hρ. lra. }
    iDestruct "H" as "[Ha _]".
    iModIntro. iExists ρs'. iSplit; [iPureIntro; rewrite /ρs' /=; lra|].
    iFrame.
  Qed.

End renyi_credit_theory.


Lemma rc_alloc `{!rcGpreS Σ} (α ρ : nonnegreal) :
  (1 <= α)%R → ⊢ |==> ∃ _ : rcGS Σ, rc_supply (α, ρ) ∗ ↯R (α, ρ).
Proof.
  iIntros (?).
  rewrite rc_unseal /rc_def rc_supply_unseal /rc_supply_def.
  iMod (own_alloc (● Some ((α, ρ) : renyi_car) ⋅ ◯ Some ((α, ρ) : renyi_car))) as (γRC) "[H● H◯]".
  - apply auth_both_valid_2.
    + compute. destruct α; simpl in H. lra.
    + apply Some_included.
      left.
      done.
  - pose (C := RcGS _ _ γRC).
    iModIntro. iExists C. by iFrame.
Qed.

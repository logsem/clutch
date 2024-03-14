(** This file implements error credits, following the ideas from
    the implementation of later credits
 *)

From Coq Require Import Reals RIneq Psatz.
From clutch.prelude Require Export base classical Reals_ext NNRbar.
From iris.prelude Require Import options.
From iris.proofmode Require Import tactics.
From iris.algebra Require Export auth numbers.
From iris.base_logic.lib Require Import iprop own.

Import uPred.


(** ** Non-negative real numbers with addition as the operation. *)
Section NNR.
  Canonical Structure NNRbarO : ofe := leibnizO NNRbar.

  Local Instance NNRbar_valid_instance : Valid (NNRbar)  := is_finite.
  Local Instance NNRbar_validN_instance : ValidN (NNRbar) := λ _ , is_finite.
  Local Instance NNRbar_pcore_instance : PCore (NNRbar) := λ _, Some (Finite nnreal_zero).
  Local Instance NNRbar_op_instance : Op (NNRbar) := λ x y, NNRbar_plus x y.
  Local Instance NNRbar_equiv : Equiv NNRbar := λ x y, x = y.

  Definition NNRbar_op (x y : NNRbar) : x ⋅ y = NNRbar_plus x y := eq_refl.

  Lemma Rle_0_le_minus (x y : R) : (x <= y)%R -> (0 <= y - x)%R.
  Proof.
    lra.
  Qed.

  (* Lemma R_included (x y : NNRbar) : x ≼ y ↔ (x <= y)%R.
     Proof.
       split; intros H.
       - destruct x as [x|], y as [y|].
         + rewrite /included in H.
           destruct n, n0. simpl in H. simpl.
           simpl.
         rewrite /included in H.
         destruct H as ((z & Hz) & H).
         rewrite R_op /nnreal_plus in H.
         simplify_eq.
         lra.
       - rewrite /included.
         destruct x as (x & Hx).
         destruct y as (y & Hy).
         simpl in H.
         eexists ({| nonneg := y - x ; cond_nonneg := Rle_0_le_minus x y H |}).
         rewrite R_op/=.
         rewrite /equiv/R_equiv/=.
         apply nnreal_ext.
         simpl.
         lra.
     Qed. *)


  (*
  Local Instance RR_valid_instance : Valid (R)  := λ _ , True.
  Local Instance RR_validN_instance : ValidN (R) := λ _ _, True.
  Local Instance RR_pcore_instance : PCore (R) := λ _, Some 0%R.
  Local Instance RR_op_instance : Op (nonnegreal) := λ x y, Rplus x y.
  Local Instance RR_equiv : Equiv R := λ x y, x = y.
  Lemma RR_ra_mixin : RAMixin R.
  *)

  Lemma NNRbar_plus_assoc (x y z : NNRbar) :
    NNRbar_plus x (NNRbar_plus y z) = NNRbar_plus (NNRbar_plus x y) z.
  Proof.
    destruct x, y, z ; simpl => //.
    f_equal.
    apply nnreal_ext.
    simpl.
    lra.
    Qed.

  Lemma NNRbar_ra_mixin : RAMixin NNRbar.
  Proof.
    apply ra_total_mixin; try by eauto.
    - solve_proper.
    - solve_proper.
    - intros ? ? ?.
      rewrite /equiv/NNRbar_equiv.
      rewrite /NNRbar_op_instance.
      rewrite /op.
      apply NNRbar_plus_assoc.
    - intros ? ?.
      rewrite /equiv/NNRbar_equiv.
      destruct x, y => //=. rewrite /op. simpl. f_equal.
      apply nnreal_ext; simpl; lra.
    - intros ?.
      rewrite /equiv/NNRbar_equiv.
      destruct x => //=. rewrite /op. simpl. f_equal.
      apply nnreal_ext; simpl; lra.
    - intros ? ? ?.
      destruct x, y => //= ; rewrite /core ; simpl ; auto ;
                       rewrite /included ; exists nnreal_zero ;
                       rewrite /equiv/NNRbar_equiv/op/NNRbar_op_instance ;
                       simpl ; f_equal ;
                       apply nnreal_ext ; simpl ; lra.
      (* apply R_included; simpl; lra. *)
    - rewrite /valid/NNRbar_valid_instance.
      rewrite /op/NNRbar_op_instance /=.
      intros ? ? ?.
      destruct x.
      + move : H. rewrite /is_finite => H.
        simpl. done.
      + simpl in H. rewrite /is_finite in H. simpl in H. discriminate H.
  Qed.

  (* Massive hack to override Coq reals *)
  Definition id {A} := (λ (a : A), a).

  Canonical Structure NNRbarR : cmra := discreteR NNRbar NNRbar_ra_mixin.

  Global Instance NNRbar_cmra_discrete : CmraDiscrete NNRbarR.
  Proof. apply discrete_cmra_discrete. Qed.

  Local Instance NNRbar_unit_instance : Unit NNRbar := Finite nnreal_zero.
  Lemma NNRbar_ucmra_mixin : @UcmraMixin NNRbar _ _ _ _ _ NNRbar_unit_instance.
  Proof. split.
         - rewrite /valid.
           rewrite /NNRbar_valid_instance/NNRbar_unit_instance/ε.
           rewrite /is_finite. done.
         - rewrite /LeftId.
           intro.
           rewrite /equiv/NNRbar_equiv/op/NNRbar_op_instance/=.
           destruct x => //. f_equal.
           apply nnreal_ext; simpl; lra.
         - rewrite /pcore/NNRbar_pcore_instance; auto.
  Qed.

  Canonical Structure NNRbarUR : ucmra := Ucmra NNRbar NNRbar_ucmra_mixin.

  Lemma nonnegreal_add_cancel_l : ∀ x y z : nonnegreal, nnreal_plus z x = nnreal_plus z y ↔ x = y.
  Proof.
    intros ? ? ?; split; intro H.
    - apply nnreal_ext.
      rewrite /nnreal_plus in H.
      simplify_eq.
      lra.
    - simplify_eq; auto.
  Qed.

  Lemma NNRbar_add_cancel_l : ∀ x y z : NNRbar, NNRbar_plus z x = NNRbar_plus z y ↔ x = y.
  Proof.
    intros ? ? ?; split; intro H.
    -
      (* Well, this simply doesn't hold if z = +oo. *)
  Abort.


  (* Global Instance NNRbar_cancelable (x : NNRbar) : Cancelable x.
     Proof. by intros ???? ?%nonnegreal_add_cancel_l. Qed. *)

  (* FIXME: unused (it should factor out the proof in ec_credit_supply) *)
  Lemma NNRbar_local_update (x y x' y' : NNRbar) :
    (NNRbar_le y' y) -> NNRbar_plus x y' = NNRbar_plus x' y → (x,y) ~l~> (x',y').
  Proof.
    intros ??; apply (local_update_unital_discrete x y x' y') => z H1 H2.
    compute in H2; simplify_eq; simpl.
    split.
    -
      destruct y eqn:hy, x' eqn:hx', y' eqn:hy', z eqn:hz.
      all: compute ; try easy.
    - destruct y, x', y', z; simplify_eq; simpl ; compute.
      all: try easy.
      destruct n, n0, n1, n2; simplify_eq; simpl.
      compute; compute in *.
      f_equal. apply nnreal_ext. simpl. lra.
  Qed.

  (* This one has a higher precendence than [is_op_op] so we get a [+] instead
     of an [⋅].
  Global Instance nat_is_op (n1 n2 : nat) : IsOp (n1 + n2) n1 n2.
  Proof. done. Qed.
  *)
End NNR.



(** The ghost state for expected time credits *)
Class etcGpreS (Σ : gFunctors) := EtcGpreS {
  etcGpreS_inG :: inG Σ (authR NNRbarUR)
}.

Class etcGS (Σ : gFunctors) := EtcGS {
  etcGS_inG : inG Σ (authR NNRbarUR);
  etcGS_name : gname;
}.

Global Hint Mode etcGS - : typeclass_instances.
Local Existing Instances etcGS_inG etcGpreS_inG.

Definition etcΣ := #[GFunctor (authR (NNRbarUR))].
Global Instance subG_etcΣ {Σ} : subG etcΣ Σ → etcGpreS Σ.
Proof. solve_inG. Qed.


(** The user-facing error resource, denoting ownership of [ε] error credits. *)
Local Definition etc_def `{!etcGS Σ} (x : NNRbar) : iProp Σ := own etcGS_name (◯ x).
Local Definition etc_aux : seal (@etc_def). Proof. by eexists. Qed.
Definition ec := etc_aux.(unseal).
Local Definition etc_unseal :
  @ec = @etc_def := etc_aux.(seal_eq).
Global Arguments ec {Σ _} x.

Notation "'⧖'  x" := (ec x) (at level 1).

(** The internal authoritative part of the credit ghost state,
  tracking how many credits are available in total.
  Users should not directly interface with this. *)
Local Definition etc_supply_def `{!etcGS Σ} (x : NNRbar) : iProp Σ := own etcGS_name (● x).
Local Definition etc_supply_aux : seal (@etc_supply_def). Proof. by eexists. Qed.
Definition etc_supply := etc_supply_aux.(unseal).
Local Definition etc_supply_unseal :
  @etc_supply = @etc_supply_def := etc_supply_aux.(seal_eq).
Global Arguments etc_supply {Σ _} x.


Section error_credit_theory.
  Context `{!etcGS Σ}.
  Implicit Types (P Q : iProp Σ).

  (** Later credit rules *)
  Lemma etc_split x1 x2 :
    ⧖ (NNRbar_plus x1 x2) ⊣⊢ ⧖ x1 ∗ ⧖ x2.
  Proof.
    rewrite etc_unseal /etc_def.
    rewrite -own_op auth_frag_op //=.
  Qed.

  Lemma etc_zero : ⊢ |==> ⧖ nnreal_zero.
  Proof.
    rewrite etc_unseal /etc_def. iApply own_unit.
  Qed.

  Lemma etc_supply_bound x1 x2 :
    etc_supply x2 -∗ ⧖ x1 -∗ ⌜(x1 <= x2)%R⌝.
  Proof.
    rewrite etc_unseal /etc_def.
    rewrite etc_supply_unseal /etc_supply_def.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as "%Hop".
    iPureIntro. eapply auth_both_valid_discrete in Hop as [Hlt ?].
    rewrite /included in Hlt. rewrite /op/cmra_op/ucmra_op in Hlt ; simpl in Hlt.
    destruct Hlt as [z Hz]. simplify_eq. rewrite /ucmra_op. simpl. rewrite /NNRbar_op_instance.
    rewrite /ucmra_op. simpl in H. rewrite /NNRbar_op_instance in H.
    rewrite /valid/cmra_valid in H ; simpl in H.
    rewrite /ucmra_valid/NNRbar_valid_instance in H ; simpl in H.
    rewrite /NNRbar_valid_instance in H ; simpl in H.
    rewrite /ucmra_op in H. simpl in H. rewrite /NNRbar_op_instance in H.
    destruct (NNRbar_plus_finite _ _ H) as [??].
    rewrite /NNRbar_to_real. destruct x1 as [x1|] => //. destruct z as [z|] => //.
    simpl. apply Rle_plus_l => //. destruct z. simpl. lra.
  Qed.

  Lemma etc_decrease_supply x1 x2 :
    etc_supply (NNRbar_plus x1 x2) -∗ ⧖ x1 -∗ |==> etc_supply x2.
  Proof.
    rewrite etc_unseal /etc_def.
    rewrite etc_supply_unseal /etc_supply_def.
    iIntros "H1 H2".
    iMod (own_update_2 with "H1 H2") as "Hown".
    { eapply auth_update. eapply (NNRbar_local_update _ _ x2 nnreal_zero).
      1: destruct x1 => // ; apply cond_nonneg.
      by rewrite NNRbar_plus_0_r NNRbar_plus_comm.
    }
    by iDestruct "Hown" as "[Hm _]".
  Qed.

  Lemma etc_increase_supply (x1 x2 : NNRbar) :
    ⌜ is_finite (NNRbar_plus x1 x2) ⌝ ∗ etc_supply x1 -∗ |==> etc_supply (NNRbar_plus x1 x2) ∗ ⧖ x2.
  Proof.
    rewrite etc_unseal /etc_def.
    rewrite etc_supply_unseal /etc_supply_def.
    iIntros "[%Hsum H]".
    iMod (own_update with "H") as "[$ $]"; [|done].
    eapply (auth_update_alloc _ ). (* (x1 + x2)%NNR x2%NNR). *)
    apply (local_update_unital_discrete _ _ _ _) => z H1 H2.
    split.
    - compute. done.
    -
      (* compute. apply nnreal_ext. simpl. *)
      (* destruct z as [z|] => //. *)
  (*     compute in H2.
         simpl in H2.
         rewrite Rplus_comm.
         apply Rplus_eq_compat_l.
         rewrite H2 /=.
         lra.
     Qed. *)
  Admitted.


  Lemma etc_split_supply x1 x2 :
    etc_supply x2 -∗ ⧖ x1 -∗ ∃ x3, ⌜x2 = (NNRbar_plus x1 x3)⌝.
  Proof.
    rewrite etc_unseal /etc_def.
    rewrite etc_supply_unseal /etc_supply_def.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as "%Hop".
    iPureIntro. eapply auth_both_valid_discrete in Hop as [Hlt _].
    done.
  Qed.

  Lemma etc_weaken {x1 : NNRbar} (x2 : NNRbar) :
    (NNRbar_le x2 x1) → ⧖ x1 -∗ ⧖ x2.
  Proof.
    intros H.
  (*   set diff := NNRbar_minus (x1 - x2) (Rle_0_le_minus x2 x1 H).

       set diff := mknonnegreal (x1 - x2) (Rle_0_le_minus x2 x1 H).
       assert (x1 = nnreal_plus x2 diff) as H2.
       { apply nnreal_ext; simpl; lra. }
       rewrite H2.
       rewrite etc_split. iIntros "[$ _]".
     Qed. *)
  Admitted.

  Lemma etc_spend (x : NNRbar) : (NNRbar_le p_infty x) -> ⧖ x -∗ False.
  Proof.
    iIntros (Hge1) "Hx".
    rewrite etc_unseal /etc_def.
    iAssert (✓ (◯ x))%I with "[Hx]" as "%Hx" ; [by iApply own_valid|].
    apply auth_frag_valid_1 in Hx.
    exfalso; destruct x; compute in * => //.
  Qed.


  (* Lemma etc_spend_le_irrel x1 x2 : (x2.(nonneg) <= x1.(nonneg))%R → ⧖ x1 -∗ ⧖ x2.
     Proof. iIntros (?) "?". iApply etc_weaken; done. Qed.


     Lemma etc_spend_irrel x1 x2 : (x1.(nonneg) = x2.(nonneg)) → ⧖ x1 -∗ ⧖ x2.
     Proof.
       iIntros (?) "?".
       replace x1 with x2; [iFrame|by apply nnreal_ext].
     Qed. *)

  Global Instance etc_timeless x : Timeless (⧖ x).
  Proof.
    rewrite etc_unseal /etc_def. apply _.
  Qed.

  Global Instance etc_0_persistent : Persistent (⧖ nnreal_zero).
  Proof.
    rewrite etc_unseal /etc_def. apply _.
  Qed.

  Global Instance from_sep_etc_add x1 x2 :
    FromSep (⧖ (NNRbar_plus x1 x2)) (⧖ x1) (⧖ x2) | 0.
  Proof.
    by rewrite /FromSep etc_split.
  Qed.

  Global Instance into_sep_etc_add x1 x2 :
    IntoSep (⧖ (NNRbar_plus x1 x2)) (⧖ x1) (⧖ x2) | 0.
  Proof.
    by rewrite /IntoSep etc_split.
  Qed.

  Global Instance combine_sep_as_etc_add x1 x2 :
    CombineSepAs (⧖ x1) (⧖ x2) (⧖ (NNRbar_plus x1 x2)) | 0.
  Proof.
    by rewrite /CombineSepAs etc_split.
  Qed.

End error_credit_theory.

Lemma etc_alloc `{!etcGpreS Σ} (x : NNRbar) :
  ⌜is_finite x⌝ ⊢ |==> ∃ _ : etcGS Σ, etc_supply x ∗ ⧖ x.
Proof.
  iIntros.
  rewrite etc_unseal /etc_def etc_supply_unseal /etc_supply_def.
  iMod (own_alloc (● x ⋅ ◯ x)) as (γEC) "[H● H◯]".
  - apply auth_both_valid_2.
    + compute. destruct x; simpl in H => //.
    + rewrite /included. eexists. symmetry. apply NNRbar_plus_0_r.
  - pose (C := EtcGS _ _ γEC).
    iModIntro. iExists C. iFrame.
Qed.

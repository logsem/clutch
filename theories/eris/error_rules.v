(** * Union bound rules  *)
From stdpp Require Import namespaces finite.
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext.
From clutch.prob_lang Require Import notation tactics metatheory.
From clutch.prob_lang Require Export lang.
From clutch.eris Require Export lifting proofmode ectx_lifting primitive_laws seq_amplification.
From clutch.eris Require Export total_lifting total_ectx_lifting total_primitive_laws.

(** TODO: this file needs to get properly updated to take into account that the error credits [↯ ε]
    now works for [ε : R] rather than [ε : nonnegreal]. Ideally, no `nonnegreal` should appear at
    the level of the lemma statements! *)

Section metatheory.

Local Open Scope R.

(** * rand(N) no error *)
Lemma pgl_rand_trivial N z σ1 :
  N = Z.to_nat z →
  pgl
    (prim_step (rand #z) σ1)
    (λ ρ2, ∃ (n : fin (S N)),
        ρ2 = (Val #n, σ1)) 0.
Proof.
  simpl in *.
  intros Hz.
  rewrite head_prim_step_eq /=.
  rewrite /dmap -Hz.
  rewrite -(Rplus_0_r 0).
  eapply (pgl_dbind _ _ _ _ _ 0);
    [done|done| |by apply pgl_trivial].
  intros n ?.
  apply pgl_dret.
  by exists n.
Qed.

(** * rand(N) error *)
Lemma pgl_rand_err N z σ1 (m : fin (S N)):
  N = Z.to_nat z →
  pgl
    (prim_step (rand #z) σ1)
    (λ ρ2, ∃ (n : fin (S N)),
        (n ≠ m)%fin /\ ρ2 = (Val #n, σ1)) (1/(N+1)).
Proof.
  simpl in *.
  intros Hz.
  rewrite head_prim_step_eq /=.
  rewrite /dmap -Hz.
  rewrite -(Rplus_0_r (1 / (N + 1))).
  eapply (pgl_dbind _ _ _ _ _ 0); last first.
  { by apply ub_unif_err. }
  - intros n ?.
    apply pgl_dret.
    exists n; split; [apply H | auto].
  - lra.
  - rewrite /Rdiv.
    apply Rle_mult_inv_pos; [lra |].
    apply (Rle_lt_trans _ N).
    + apply pos_INR.
    + rewrite <- (Rplus_0_r) at 1.
      apply Rplus_lt_compat_l.
      lra.
Qed.

(* Same lemma holds for m an arbitrary natural *)
Lemma pgl_rand_err_nat N z σ1 (m : nat):
  N = Z.to_nat z →
  pgl
    (prim_step (rand #z) σ1)
    (λ ρ2, ∃ (n : fin (S N)),
        (fin_to_nat n ≠ m)%fin /\ ρ2 = (Val #n, σ1)) (1/(N+1)).
Proof.
  simpl in *.
  intros Hz.
  rewrite head_prim_step_eq /=.
  rewrite /dmap -Hz.
  rewrite -(Rplus_0_r (1 / (N + 1))).
  eapply (pgl_dbind _ _ _ _ _ 0); last first.
  { by apply ub_unif_err_nat. }
  - intros n ?.
    apply pgl_dret.
    exists n; split; [apply H | auto].
  - lra.
  - rewrite /Rdiv.
    apply Rle_mult_inv_pos; [lra |].
    apply (Rle_lt_trans _ N).
    + apply pos_INR.
    + rewrite <- (Rplus_0_r) at 1.
      apply Rplus_lt_compat_l.
      lra.
Qed.

(* Generalization to lists *)
Lemma pgl_rand_err_list_nat N z σ1 (ms : list nat):
  N = Z.to_nat z →
  pgl
    (prim_step (rand #z) σ1)
    (λ ρ2, ∃ (n : fin (S N)),
        Forall (λ m, (fin_to_nat n ≠ m)%fin) ms /\ ρ2 = (Val #n, σ1)) ((length ms)/(N+1)).
Proof.
  simpl in *.
  intros Hz.
  rewrite head_prim_step_eq /=.
  rewrite /dmap -Hz.
  rewrite -(Rplus_0_r ((length ms) / (N + 1))).
  eapply (pgl_dbind _ _ _ _ _ 0); last first.
  { by apply ub_unif_err_list_nat. }
  - intros n ?.
    apply pgl_dret.
    exists n; split; [apply H | auto].
  - lra.
  - rewrite /Rdiv.
    apply Rle_mult_inv_pos; [apply pos_INR | ].
    apply (Rle_lt_trans _ N).
    + apply pos_INR.
    + rewrite <- (Rplus_0_r) at 1.
      apply Rplus_lt_compat_l.
      lra.
Qed.

Lemma pgl_rand_err_list_int N z σ1 (ms : list Z):
  N = Z.to_nat z →
  pgl
    (prim_step (rand #z) σ1)
    (λ ρ2, ∃ (n : fin (S N)),
        Forall (λ m, (Z.of_nat (fin_to_nat n) ≠ m)%fin) ms /\ ρ2 = (Val #n, σ1)) ((length ms)/(N+1)).
Proof.
  simpl in *.
  intros Hz.
  rewrite head_prim_step_eq /=.
  rewrite /dmap -Hz.
  rewrite -(Rplus_0_r ((length ms) / (N + 1))).
  eapply (pgl_dbind _ _ _ _ _ 0); last first.
  { by apply ub_unif_err_list_int. }
  - intros n ?.
    apply pgl_dret.
    exists n; split; [apply H | auto].
  - lra.
  - rewrite /Rdiv.
    apply Rle_mult_inv_pos; [apply pos_INR | ].
    apply (Rle_lt_trans _ N).
    + apply pos_INR.
    + rewrite <- (Rplus_0_r) at 1.
      apply Rplus_lt_compat_l.
      lra.
Qed.

End metatheory.

Section rules.
  Context `{!erisGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types v : val.
  Implicit Types l : loc.

Lemma twp_rand_err (N : nat) (z : Z) (m : fin (S N)) E Φ s :
  TCEq N (Z.to_nat z) →
  ↯ (/ (N + 1)) ∗ (∀ x, ⌜x ≠ m⌝ -∗ Φ #x)
  ⊢ WP rand #z @ s; E [{ Φ }].
Proof.
  iIntros (->) "[Herr Hwp]".
  iApply twp_lift_step_fupd_glm; [done|].
  iIntros (σ1 ε) "[Hσ Hε]".
  iApply fupd_mask_intro; [set_solver|].
  iIntros "Hclose'".
  iDestruct (ec_supply_ec_inv with "Hε Herr") as %(?&?& -> & He).
  iApply glm_prim_step.
  iExists
      (λ (ρ : expr * state),
        ∃ (n : fin (S (Z.to_nat z))), n ≠ m /\ ρ = (Val #n, σ1)), _, _.
  iSplit.
  { iPureIntro. eapply head_prim_reducible; eauto with head_step. }
  iSplit.
  {
    iPureIntro.
    apply Rle_refl.
  }
  iSplit.
  {
    iPureIntro.
    eapply pgl_mon_pred; last first.
    - rewrite He.
      assert (/ (Z.to_nat z + 1) = Rdiv 1 (Z.to_nat z + 1)) as ->.
      { simpl.
        rewrite /Rdiv/= Rmult_1_l //.
       }
      apply (pgl_rand_err (Z.to_nat z) z σ1); auto.
    - intros [] (n & Hn1 & [=]). simplify_eq.
      eauto.
  }
  iIntros (e2 σ2) "%H".
  destruct H as (n & Hn1 & [=]); simplify_eq.
  iMod (ec_supply_decrease with "Hε Herr") as (????) "Hdec".
  iModIntro.
  iMod "Hclose'".
  iFrame.
  iModIntro.
  rewrite -tgl_wp_value.
  iDestruct ("Hwp" with "[//]") as "$".
  iApply ec_supply_eq; [|done].
  simplify_eq.
  lra.
Qed.

Lemma wp_rand_err (N : nat) (z : Z) (m : fin (S N)) E Φ :
  TCEq N (Z.to_nat z) →
  ↯ (/ (N + 1)) ∗
  (∀ x, ⌜x ≠ m⌝ -∗ Φ #x)
  ⊢ WP rand #z @ E {{ Φ }}.
Proof.
  iIntros. iApply tgl_wp_pgl_wp'.
  iApply (twp_rand_err with "[$]").
Qed.

Lemma twp_rand_err_nat (N : nat) (z : Z) (m : nat) E Φ s :
  TCEq N (Z.to_nat z) →
  ↯ (/ (N+1)) ∗
  (∀ x : fin (S N), ⌜(fin_to_nat x) ≠ m⌝ -∗ Φ #x)
  ⊢ WP rand #z @ s; E [{ Φ }].
Proof.
  iIntros (->) "[Herr Hwp]".
  iApply twp_lift_step_fupd_glm; [done|].
  iIntros (σ1 ε) "[Hσ Hε]".
  iApply fupd_mask_intro; [set_solver|].
  iIntros "Hclose'".
  iDestruct (ec_supply_ec_inv with "Hε Herr ") as %(?&?&->&He).
  iApply glm_prim_step.
  iExists
      (λ (ρ : expr * state),
        ∃ (n : fin (S (Z.to_nat z))), fin_to_nat n ≠ m /\ ρ = (Val #n, σ1)),_,_.
  iSplit.
  { iPureIntro. eapply head_prim_reducible; eauto with head_step. }
  iSplit.
  { iPureIntro; apply Rle_refl. }
  iSplit.
  {
    iPureIntro.
    eapply pgl_mon_pred; last first.
    - rewrite He.
      assert (/ (Z.to_nat z + 1) = Rdiv 1 (Z.to_nat z + 1)) as ->.
      { simpl.
        rewrite /Rdiv/= Rmult_1_l //. }
      apply (pgl_rand_err_nat (Z.to_nat z) z σ1); auto.
    - intros [] (n & Hn1 & [=]). simplify_eq.
      eauto.
  }
  iIntros (e2 σ2) "%H".
  destruct H as (n & Hn1 & [=]); simplify_eq.
  iMod (ec_supply_decrease with "Hε Herr") as (????) "Hdec".
  iModIntro.
  iMod "Hclose'".
  iFrame.
  iModIntro.
  rewrite -tgl_wp_value.
  iDestruct ("Hwp" with "[//]") as "$".
  iApply ec_supply_eq; [|done].
  simplify_eq.
  lra.
Qed.

Lemma wp_rand_err_nat (N : nat) (z : Z) (m : nat) E Φ :
  TCEq N (Z.to_nat z) →
  ↯ (/ (N+1)) ∗
  (∀ x : fin (S N), ⌜(fin_to_nat x) ≠ m⌝ -∗ Φ #x)
  ⊢ WP rand #z @ E {{ Φ }}.
Proof.
  iIntros. iApply tgl_wp_pgl_wp'.
  iApply (twp_rand_err_nat with "[$]").
Qed.


Lemma twp_rand_err_list_nat (N : nat) (z : Z) (ns : list nat) E Φ :
  TCEq N (Z.to_nat z) →
  ↯ (length ns / (N+1)) ∗
  (∀ x : fin (S N), ⌜Forall (λ m, fin_to_nat x ≠ m) ns⌝ -∗ Φ #x)
  ⊢ WP rand #z @ E [{ Φ }].
Proof.
  iIntros (->) "[Herr Hwp]".
  iApply twp_lift_step_fupd_glm; [done|].
  iIntros (σ1 ε) "[Hσ Hε]".
  iApply fupd_mask_intro; [set_solver|].
  iIntros "Hclose'".
  iDestruct (ec_supply_ec_inv with "Hε Herr") as %(?&?&->&He).
  iApply glm_prim_step.
  iExists
    (λ (ρ : expr * state),
      ∃ (n : fin (S (Z.to_nat z))), Forall (λ m, fin_to_nat n ≠ m) ns /\ ρ = (Val #n, σ1)),_,_.
  iSplit.
  { iPureIntro. eapply head_prim_reducible; eauto with head_step. }
  iSplit.
  { iPureIntro; apply Rle_refl. }
  iSplit.
  {
    iPureIntro.
    eapply pgl_mon_pred; last first.
    - rewrite He.
      apply (pgl_rand_err_list_nat (Z.to_nat z) z σ1); auto.
    - intros [] (n & Hn1 & [=]). simplify_eq.
      eauto.
  }
  iIntros (e2 σ2) "%H".
  destruct H as (n & Hn1 & [=]); simplify_eq.
  iMod (ec_supply_decrease with "Hε Herr") as (????) "Hdec".
  iModIntro.
  iMod "Hclose'".
  iFrame.
  iModIntro.
  rewrite -tgl_wp_value.
  iDestruct ("Hwp" with "[//]") as "$".
  iApply ec_supply_eq; [|done].
  simplify_eq.
  lra.
Qed.

Lemma wp_rand_err_list_nat (N : nat) (z : Z) (ns : list nat) E Φ :
  TCEq N (Z.to_nat z) →
  ↯ (length ns / (N+1)) ∗
    (∀ x : fin (S N), ⌜Forall (λ m, (fin_to_nat x) ≠ m) ns⌝ -∗ Φ #x)
    ⊢ WP rand #z @ E {{ Φ }}.
Proof.
  iIntros. iApply tgl_wp_pgl_wp'.
  by iApply (twp_rand_err_list_nat).
Qed.

Lemma twp_rand_err_list_int (N : nat) (z : Z) (zs : list Z) E Φ :
  TCEq N (Z.to_nat z) →
  ↯ (length zs / (N+1)) ∗
  (∀ x : fin (S N), ⌜Forall (λ m, (Z.of_nat $ fin_to_nat x) ≠ m) zs⌝ -∗ Φ #x)
  ⊢ WP rand #z @ E [{ Φ }].
Proof.
  iIntros (->) "[Herr Hwp]".
  iApply twp_lift_step_fupd_glm; [done|].
  iIntros (σ1 ε) "[Hσ Hε]".
  iApply fupd_mask_intro; [set_solver|].
  iIntros "Hclose'".
  iDestruct (ec_supply_ec_inv with "Hε Herr ") as %(?&?&->&He).
  iApply glm_prim_step.
  iExists
    (λ (ρ : expr * state),
      ∃ (n : fin (S (Z.to_nat z))), Forall (λ m, Z.of_nat (fin_to_nat n) ≠ m) zs /\ ρ = (Val #n, σ1)),_,_.
  iSplit.
  { iPureIntro. eapply head_prim_reducible; eauto with head_step. }
  iSplit.
  { iPureIntro; apply Rle_refl. }
  iSplit.
  {
    iPureIntro.
    eapply pgl_mon_pred; last first.
    - rewrite He. apply (pgl_rand_err_list_int (Z.to_nat z) z σ1); auto.
    - intros [] (n & Hn1 & [=]). simplify_eq. eauto.
  }
  iIntros (e2 σ2) "%H".
  destruct H as (n & Hn1 & [=]); simplify_eq.
  iMod (ec_supply_decrease with "Hε Herr") as (????) "Hdec".
  iModIntro.
  iMod "Hclose'".
  iFrame.
  iModIntro.
  rewrite -tgl_wp_value.
  iDestruct ("Hwp" with "[//]") as "$".
  iApply ec_supply_eq; [|done].
  simplify_eq.
  lra.
Qed.

Lemma wp_rand_err_list_int (N : nat) (z : Z) (zs : list Z) E Φ :
  TCEq N (Z.to_nat z) →
  ↯ (length zs / (N + 1)) ∗
  (∀ x : fin (S N), ⌜Forall (λ m, (Z.of_nat $ fin_to_nat x) ≠ m) zs⌝ -∗ Φ #x)
  ⊢ WP rand #z @ E {{ Φ }}.
Proof.
  iIntros. iApply tgl_wp_pgl_wp'.
  by iApply twp_rand_err_list_int.
Qed.

Lemma wp_rand_err_filter (N : nat) (z : Z) (P : nat -> bool) E Φ :
  TCEq N (Z.to_nat z) →
  ↯ (length (List.filter P (seq 0 (S N))) / (N + 1)) ∗
    (∀ x : fin (S N), ⌜ P x = false ⌝ -∗ Φ #x)
    ⊢ WP rand #z @ E {{ Φ }}.
Proof.
  iIntros (?) "[H1 H2]".
  iApply tgl_wp_pgl_wp'.
  iApply (twp_rand_err_list_nat _ _ (List.filter P (seq 0 (S N)))).
  iFrame.
  iIntros (x) "%H0".
  iApply "H2".
  iPureIntro.
  edestruct (List.Forall_forall) as (H1 & H2).
  specialize (H1 H0).
  destruct (P x) eqn:HPx ; auto.
  exfalso.
  apply (H1 x); auto.
  apply filter_In; split; auto.
  apply in_seq.
  simpl.
  split; auto with arith.
  apply fin_to_nat_lt.
Qed.


(* FIXME: where should this go (if anywhere?) *)
Lemma match_nonneg_coercions (n : nonnegreal) : NNRbar_to_real (NNRbar.Finite n) = nonneg n.
Proof. by simpl. Qed.

Lemma mean_constraint_ub (N : nat) ε1 (ε2 : fin (S N) → nonnegreal) :
  SeriesC (λ n, (1 / (S N)) * ε2 n)%R = (nonneg ε1) →
  (∃ r, (0 <= r)%R ∧ ∀ n,(ε2 n <= r)%R).
Proof.
  intros Hsum.
  exists (nnreal_nat (S N) * ε1)%NNR.
  split. { apply Rmult_le_pos; apply cond_nonneg. }
  intros n.
  Opaque nnreal_nat.
  rewrite /= -Hsum.
  rewrite SeriesC_scal_l -Rmult_assoc -(Rmult_1_l (nonneg (ε2 _))).
  apply Rmult_le_compat; try lra.
  - by apply cond_nonneg.
  - rewrite /Rdiv Rmult_1_l.
    rewrite /= Rinv_r; try lra.
    Transparent nnreal_nat.
    rewrite /nnreal_nat.
    replace (nonneg {| nonneg := INR (S N); cond_nonneg := _ |}) with (INR (S N)); [| by simpl ].
    by apply not_0_INR.
  - rewrite -match_nonneg_coercions.
    rewrite -(SeriesC_singleton_dependent _ ε2).
    apply SeriesC_le.
    + intros n'.
      assert (H : (0 <= (nonneg (ε2 n')))%R) by apply cond_nonneg.
      rewrite /nnreal_zero /=.
      case_bool_decide; try lra.
    + apply ex_seriesC_finite.
Qed.


#[local] Fixpoint Rmax_seq (f : nat -> R) n :=
  match n with
  | 0 => f 0%nat
  | S m => Rmax (f (S m)) (Rmax_seq f m)
  end.

#[local] Lemma le_Rmax_seq (f : nat -> R) n m :
  (m ≤ n) ->
  (f m <= Rmax_seq f n)%R.
Proof.
  intros Hleq.
  induction Hleq.
  - destruct m; simpl; [lra|].
    apply Rmax_l.
  - simpl.
    etrans; eauto.
    apply Rmax_r.
Qed.

#[local] Lemma fin_function_bounded (N : nat) (f : fin N -> R) :
  exists r, forall n, (f n <= r)%R.
Proof.
  induction N as [|M].
  - exists 0.
    intros.
    by apply Fin.case0.
  - set (g := (λ (n : nat), f (fin.fin_force _ n))).
    exists (Rmax_seq g M).
    intros n.
    pose proof (fin_to_nat_lt n).
    transitivity (g n).
    + rewrite /g /=.
      right.
      f_equal.
      apply fin_to_nat_inj.
      rewrite fin.fin_force_to_nat_le; lia.
    + apply le_Rmax_seq; lia.
Qed.

Lemma twp_couple_rand_adv_comp (N : nat) z E (ε1 : R) (ε2 : fin (S N) -> R) :
  TCEq N (Z.to_nat z) →
  (∀ n, (0 <= ε2 n)%R) →
  SeriesC (λ n, (1 / (S N)) * ε2 n)%R = ε1 →
  [[{ ↯ ε1 }]] rand #z @ E [[{ n, RET #n; ↯ (ε2 n) }]].
Proof.
  iIntros (-> Hleq Hε1 Ψ) "Herr HΨ".
  destruct (fin_function_bounded _ ε2) as [r Hε2].
  iApply twp_lift_step_fupd_glm; [done|].
  iIntros (σ1 ε_now) "[Hσ Hε]".
  iApply fupd_mask_intro; [set_solver|].
  iIntros "Hclose'".
  iApply glm_adv_comp; simpl.
  (* iDestruct (ec_supply_bound with "Hε Herr") as %?. *)
  iDestruct (ec_supply_ec_inv with "Hε Herr") as %(ε1' & ε3 & Hε_now & Hε1').
  set (foo := (λ (ρ : expr * state),
                ε3 +
                  match ρ with
                  | (Val (LitV (LitInt n)), σ) =>
                      if bool_decide(σ = σ1)
                      then if bool_decide (0 ≤ n)%Z
                           then match (lt_dec (Z.to_nat n) (S (Z.to_nat z))) with
                                | left H => mknonnegreal _ (Hleq (@Fin.of_nat_lt (Z.to_nat n) (S (Z.to_nat z)) H))
                                | _ => nnreal_zero
                                end
                           else nnreal_zero
                      else nnreal_zero
                  | _ => nnreal_zero
                  end)%NNR).
  iExists
    (λ (ρ : expr * state),
      ∃ (n : fin (S (Z.to_nat z))), ρ = (Val #n, σ1)), nnreal_zero, foo.
  iSplit.
  { iPureIntro. eapply head_prim_reducible; eauto with head_step. }
  iSplit.
  {
    iPureIntro. exists (ε3 + r)%R.
    intros (e & σ); simpl.
    apply Rplus_le_compat; [lra |].
    assert (0 <= r)%R.
    { transitivity (ε2 0%fin); auto.
    }
    do 6 (case_match; auto).
    apply Hε2.
  }
  iSplit.
  {
    iPureIntro.
    rewrite /foo /= Rplus_0_l.
    setoid_rewrite Rmult_plus_distr_l.
    rewrite SeriesC_plus.
    - rewrite Rplus_comm.
      subst.
      apply Rplus_le_compat.
      + rewrite Hε1'.
        etrans; last first.
        * apply (SeriesC_le_inj _
                   (λ ρ : expr * state,
                       let (e, σ) := ρ in
                       if bool_decide (σ = σ1) then
                         match e with
                         | Val #(LitInt n) =>
                             if bool_decide (0 ≤ n)%Z
                             then match lt_dec (Z.to_nat n) (S (Z.to_nat z)) with
                                  | left H => Some (nat_to_fin H)
                                  | right _ => None
                                  end
                             else None
                         | _ => None
                         end
                       else None)).
          ** intros.
             (* TODO: Add this to real solver *)
             apply Rmult_le_pos; [ | auto ].
             apply Rmult_le_pos; [lra |].
             left. apply RinvN_pos'.
          ** intros ρ1 ρ2 m Hc1 Hc2.
             do 14 ((case_bool_decide || case_match); simplify_eq).
             f_equal.
             do 3 f_equal.
             assert (fin_to_nat (nat_to_fin l0) = fin_to_nat (nat_to_fin l)) as He.
             { by rewrite Hc1. }
             rewrite !fin_to_nat_to_fin in He.
             by apply Z2Nat.inj.
          ** apply ex_seriesC_finite.
        * apply SeriesC_le.
          ** intros []; split.
             *** apply Rmult_le_pos; auto.
             *** case_bool_decide; simplify_eq.
                 **** do 5 (case_match; simpl; (try (rewrite Rmult_0_r; lra))).
                      apply Rmult_le_compat_r; [ auto |].
                      rewrite head_prim_step_eq /=.
                      rewrite /dmap /pmf/=/dbind_pmf/dunifP.
                      setoid_rewrite dunif_pmf.
                      rewrite SeriesC_scal_l /= /Rdiv Rmult_1_l.
                      rewrite <- Rmult_1_r.
                      apply Rmult_le_compat_l; auto.
                      ***** left. eapply Rlt_le_trans; [apply (RinvN_pos' (Z.to_nat z)) |].
                      done.
                      ***** rewrite /pmf/=/dret_pmf.
                      erewrite <- (SeriesC_singleton (nat_to_fin l0)).
                      apply SeriesC_le; [ | apply ex_seriesC_singleton ].
                      intro; split; [ real_solver |].
                      case_bool_decide; simplify_eq.
                      case_bool_decide; try real_solver.
                      rewrite bool_decide_eq_true_2; [lra|].
                      simplify_eq.
                      apply fin_to_nat_inj.
                      rewrite fin_to_nat_to_fin.
                      rewrite Nat2Z.id //.
                 **** simpl. etrans; [ | right; eapply Rmult_0_l ].
                      apply Rmult_le_compat_r; [ auto | ].
                      right.
                      rewrite head_prim_step_eq /=.
                      rewrite /dmap /pmf/=/dbind_pmf/dunifP.
                      setoid_rewrite dunif_pmf.
                      rewrite SeriesC_scal_l /= /Rdiv.
                      erewrite (SeriesC_ext _ (λ _, 0));
                        [rewrite SeriesC_0; auto; by rewrite Rmult_0_r|].
                      intro; rewrite dret_0; auto.
                      intro; simplify_eq.
          ** eapply ex_seriesC_finite_from_option.
             instantiate (1 := (λ n:nat, ( Val #(LitInt n), σ1)) <$> (seq 0%nat (S (Z.to_nat z)))).
             intros [e s].
             split.
             --- case_bool_decide; last first.
                 { inversion 1. done. }
                 case_match; try (by inversion 1).
                 case_match; try (by inversion 1).
                 case_match; try (by inversion 1).
                 case_bool_decide; try (by inversion 1).
                 case_match; try (by inversion 1).
                 intros. subst. eapply elem_of_list_fmap_1_alt; last first.
                 { repeat f_equal. instantiate (1 := Z.to_nat n). lia. }
                 rewrite elem_of_seq. lia.
             --- intros H1. apply elem_of_list_fmap_2 in H1.
                 destruct H1 as [n[H1 H2]].
                 inversion H1.
                 replace (bool_decide (_=_)) with true.
                 2: { case_bool_decide; done. }
                 replace (bool_decide _) with true.
                 2: { case_bool_decide; lia. }
                 case_match; first done.
                 rewrite elem_of_seq in H2. lia.
      + rewrite SeriesC_scal_r.
        rewrite <- Rmult_1_l.
        apply Rmult_le_compat; auto; try lra; apply cond_nonneg.
    - by apply ex_seriesC_scal_r.
    - eapply ex_seriesC_ext; last eapply ex_seriesC_list.
      intros [e s].
      instantiate (2 := (λ n:nat, ( Val #(LitInt n), σ1)) <$> (seq 0%nat (S (Z.to_nat z)))).
      case_bool_decide; last first.
      + repeat (case_match; try (simpl; lra)).
        exfalso. apply H. subst.
        eapply elem_of_list_fmap_1_alt; last first.
        { apply bool_decide_eq_true_1 in H3, H4. repeat f_equal.
          - instantiate (1 := Z.to_nat n). lia.
          - done.
        }
        rewrite elem_of_seq. lia.
      + instantiate (1 :=
                       (λ '(e, s), (prim_step (rand #z) σ1 (e, s) *
                                      match e with
                                      | Val #(LitInt n) =>
                                          if bool_decide (s = σ1)
                                          then
                                            if bool_decide (0 ≤ n)%Z
                                            then
                                              match lt_dec (Z.to_nat n) (S (Z.to_nat z)) with
                                              | left H0 => ε2 (nat_to_fin H0)
                                              | right _ => nnreal_zero
                                              end
                                            else nnreal_zero
                                          else nnreal_zero
                                      | _ => nnreal_zero
                                      end)%R)).
        simpl. repeat f_equal.
        repeat (case_match; try (simpl; lra)).
  }
  iSplit.
  {
    iPureIntro.
    eapply pgl_mon_pred; last first.
    - apply (pgl_rand_trivial (Z.to_nat z) z σ1); auto.
    - done.
  }
  iIntros (e2 σ2) "%H".
  destruct H as (n & Hn1); simplify_eq.
  rewrite /foo.
  rewrite bool_decide_eq_true_2; last done.
  rewrite bool_decide_eq_true_2; last first.
  { by zify. }


  case_match.
  2:{
    destruct n0.
    rewrite Nat2Z.id.
    apply fin_to_nat_lt.
  }
  iMod (ec_supply_decrease with "Hε Herr") as (????) "Hε2".
  iModIntro.
  destruct (Rlt_decision (nonneg ε3 + (ε2 (nat_to_fin l)))%R 1%R) as [Hdec|Hdec]; last first.
  { apply Rnot_lt_ge, Rge_le in Hdec.
    iApply exec_stutter_spend.
    iPureIntro.
    simpl.
    lra.
  }
  (* replace (nonneg ε3 + (ε2 (nat_to_fin l)))%R with (nonneg (ε3 + (ε2 (nat_to_fin l)))%NNR); [|by simpl]. *)
  iApply exec_stutter_free.
  iMod (ec_supply_increase ε3 (mknonnegreal _ (Hleq (nat_to_fin l))) with "[Hε2]") as "[Hε2 Hcr]".
  { simpl. lra. }
  { iApply ec_supply_eq; [|done]. simplify_eq. lra. }
  iMod "Hclose'".
  iApply fupd_mask_intro; [eauto|]; iIntros "_".
  iFrame.
  iApply tgl_wp_value.
  iApply "HΨ".
  assert (nat_to_fin l = n) as ->; [|done].
  apply fin_to_nat_inj.
  rewrite fin_to_nat_to_fin.
  rewrite Nat2Z.id.
  reflexivity.
Qed.

Lemma wp_couple_rand_adv_comp (N : nat) z E (ε1 : R) (ε2 : fin (S N) -> R) :
  TCEq N (Z.to_nat z) →
  (∀ n, (0 <= ε2 n)%R) →
  SeriesC (λ n, (1 / (S N)) * ε2 n)%R = ε1 →
  {{{ ↯ ε1 }}} rand #z @ E {{{ n, RET #n; ↯ (ε2 n) }}}.
Proof.
  iIntros.
  iApply (tgl_wp_pgl_wp_step' with "[$]").
  wp_apply (twp_couple_rand_adv_comp with "[$]"); try done.
  iIntros (?) "H1 H2". iModIntro.
  iApply ("H2" with "[$]").
Qed.

Lemma twp_couple_rand_adv_comp1 (N : nat) z E (ε1 : R) (ε2 : fin (S N) -> R) :
  TCEq N (Z.to_nat z) →
  (∀ n, (0 <= ε2 n)%R) →
  SeriesC (λ n, (1 / (S N)) * ε2 n)%R = ε1 →
  [[{ ↯ ε1 }]] rand #z @ E [[{ n, RET #n; ↯ (ε2 n) }]].
Proof.
  iIntros (H1 H2).
  eapply (twp_couple_rand_adv_comp _ _ _ ε1 ε2); auto.
Qed.

Lemma wp_couple_rand_adv_comp1 (N : nat) z E (ε1 : R) (ε2 : fin (S N) -> R) :
  TCEq N (Z.to_nat z) →
  (∀ n, (0 <= ε2 n)%R) →
  SeriesC (λ n, (1 / (S N)) * ε2 n)%R = ε1 →
  {{{ ↯ ε1 }}} rand #z @ E {{{ n, RET #n; ↯ (ε2 n) }}}.
Proof.
  iIntros (H1 H2).
  eapply (wp_couple_rand_adv_comp _ _ _ ε1 ε2); auto.
Qed.


Lemma twp_rand_err_amp (N : nat) (z : Z) (m : nat) (ε0 : R) E Φ :
  TCEq N (Z.to_nat z) →
  ↯ ε0 ∗
  (∀ x : fin (S N), (⌜fin_to_nat x ≠ m⌝ ∨ ↯ (ε0 * (N + 1))) -∗ Φ #x)
  ⊢ WP rand #z @ E [{ Φ }].
Proof.
  iIntros (?) "(Herr&Hwp)".
  iPoseProof (ec_valid with "Herr") as "(%Hε00 & %Hε01)".
  destruct (le_lt_dec (S N) m) as [H1 | H2].
  - wp_apply (twp_rand); auto.
    iIntros (n) "?".
    iApply "Hwp".
    iLeft.
    iPureIntro.
    intros ?.
    pose proof (fin_to_nat_lt n).
    lia.
  -
  set (ε2 := (λ x : fin (S N), if bool_decide ((fin_to_nat x) =  (Fin.of_nat_lt H2))
                               then (ε0 * (N + 1))%R
                               else 0%R)).
  wp_apply (twp_couple_rand_adv_comp1 _ _ _ ε0 ε2 with "Herr").
  {
    intros n.
    rewrite /ε2.
    case_bool_decide; [ |lra].
    apply Rmult_le_pos; [lra|].
    pose proof (pos_INR N).
    lra.
  }
  {
    rewrite -(SeriesC_singleton (Fin.of_nat_lt H2) ε0) /ε2.
    apply SeriesC_ext.
    intro n.
    case_bool_decide; case_bool_decide; simplify_eq; [| simpl; lra].
    rewrite S_INR /=.
    rewrite /Rdiv Rmult_1_l Rmult_comm Rmult_assoc Rmult_inv_r; [lra | ].
    intros Heq.
    pose proof (pos_INR N).
    lra.
  }
  iIntros (n) "Herr".
  iApply "Hwp".
  rewrite /ε2.
  case_bool_decide as Hdec.
  + by iRight.
  + iLeft.
    iPureIntro.
    intros H3.
    simplify_eq.
    apply Hdec.
    f_equal.
    rewrite nat_to_fin_to_nat //.
Qed.


Lemma wp_rand_err_amp (N : nat) (z : Z) (m : nat) (ε0 : R) E Φ :
  TCEq N (Z.to_nat z) →
  ↯ ε0 ∗
  (∀ x : fin (S N), (⌜fin_to_nat x ≠ m⌝ ∨ ↯ (ε0 * (N + 1))) -∗ Φ #x)
  ⊢ WP rand #z @ E {{ Φ }}.
Proof.
  iIntros (?) "[Herr Hwp]".
  iApply tgl_wp_pgl_wp'.
  iApply (twp_rand_err_amp with "[$Herr Hwp]"); done.
Qed.

Lemma wp_rand_err_amp_nat (N : nat) (z : Z) (m : nat) (ε0 : R) E Φ :
  TCEq N (Z.to_nat z) →
  ↯ ε0 ∗
  (∀ n : nat, ⌜ n ≤ N ⌝ ∗ (⌜n ≠ m⌝ ∨ ↯ (ε0 * (N + 1))) -∗ Φ #n)
  ⊢ WP rand #z @ E {{ Φ }}.
Proof.
  iIntros (?) "[Herr Hwp]".
  iApply tgl_wp_pgl_wp'.
  iApply (twp_rand_err_amp N z m with "[$Herr Hwp]").
  iIntros (x) "Hx".
  iApply "Hwp".
  iSplit.
  - iPureIntro.
    pose proof (fin_to_nat_lt x); lia.
  - done.
Qed.

Lemma twp_rand_err_list_adv (N : nat) (z : Z) (ns : list nat) (ε0 ε1 : R) E Φ :
  TCEq N (Z.to_nat z) →
  (0 <= ε1)%R ->
  (ε1 * (length ns) <= ε0 * (N + 1))%R ->
  ↯ ε0 ∗
    (∀ x : fin (S N),
        (⌜Forall (λ m, (fin_to_nat x) ≠ m) ns⌝ ∨ ↯ ε1) -∗ Φ #x)
    ⊢ WP rand #z @ E [{ Φ }].
Proof.
  iIntros (HN Hε1pos Hleq) "[Herr Hwp]".
  set (ε2 := (λ x : fin (S N), if bool_decide (Exists (λ m : nat, (fin_to_nat x) =  m) ns) then ε1 else 0%R)).
  wp_apply (twp_couple_rand_adv_comp1 _ _ _ (SeriesC (λ n : fin (S N), (1 / (N + 1) * ε2 n)%R)) ε2 with "[Herr]").
  - intros n.
    rewrite /ε2.
    case_bool_decide; auto.
    lra.
  - rewrite S_INR //.
  - iApply ec_weaken; auto.
    simpl.
    rewrite SeriesC_scal_l /ε2.
    rewrite (SeriesC_ext _ (λ x : fin (S N),
                   ε1 * (if bool_decide (Exists (λ m : nat, fin_to_nat x = m) ns) then 1 else 0))%R); last first.
    {
      intro n.
      case_bool_decide; simpl; lra.
    }
    rewrite SeriesC_scal_l.
    rewrite /Rdiv Rmult_1_l.
    rewrite Rmult_comm.
    rewrite -Rdiv_def.
    pose proof (pos_INR N).
    split.
    { apply Rmult_le_pos; [|real_solver].
      apply Rmult_le_pos; [auto|].
      apply SeriesC_ge_0; [|apply ex_seriesC_finite].
      intros ?. case_bool_decide; lra. }

    apply Rcomplements.Rle_div_l; [lra |].
    assert (SeriesC (λ x : fin (S N), if bool_decide (Exists (λ m : nat, fin_to_nat x = m) ns) then 1 else 0) <= length ns)%R as Haux.
    {
      induction ns as [|?].
      - erewrite SeriesC_ext; last first.
        + intros.
          erewrite bool_decide_ext; [ | apply Exists_nil ].
          done.
        + simpl.
          setoid_rewrite bool_decide_False.
          rewrite SeriesC_0 ; auto.
          lra.
      - erewrite SeriesC_ext; last first.
        + intros.
          erewrite bool_decide_ext; [ | apply Exists_cons ].
          done.
        + etrans.
          * right. symmetry.
            eapply is_seriesC_filter_union.
            2: { apply SeriesC_correct, ex_seriesC_finite. }
            intro; simpl; lra.
          * rewrite cons_length S_INR /=.
            assert (SeriesC (λ n : fin (S N), if bool_decide (fin_to_nat n = a) then 1 else 0) <= 1)%R as Haux2.
            {
              destruct (decide (a < S N)).
              - rewrite SeriesC_singleton_inj; [lra |].
                exists (nat_to_fin l).
                rewrite fin_to_nat_to_fin //.
              - transitivity 0%R; [ | lra].
                right.
                apply SeriesC_0.
                intro.
                case_bool_decide; auto.
                simplify_eq.
                exfalso. apply n.
                apply fin_to_nat_lt.
            }
            rewrite (Rplus_comm _ 1).
            rewrite -Rplus_minus_assoc.
            apply Rplus_le_compat; [apply Haux2 |].
            etrans; last first.
            ** apply IHns.
               etrans; eauto.
               apply Rmult_le_compat_l; [auto |].
               rewrite cons_length S_INR; lra.
            **
              apply Rcomplements.Rle_minus_l.
              rewrite <- (Rplus_0_r) at 1.
              apply Rplus_le_compat; [ apply Rle_refl |].
              apply SeriesC_ge_0; [ | apply ex_seriesC_finite ].
              intros; real_solver.
    }
    etrans; eauto.
    apply Rmult_le_compat_l; auto.
  - iIntros (n) "Herrn".
    rewrite /ε2.
    case_bool_decide.
    + iApply "Hwp".
      iRight.
      iFrame.
    + iApply "Hwp".
      iLeft.
      iPureIntro.
      apply not_Exists_Forall; auto.
      apply _.
Qed.

Lemma wp_rand_err_list_adv (N : nat) (z : Z) (ns : list nat) (ε0 ε1 : R) E Φ :
  TCEq N (Z.to_nat z) →
  (0 <= ε1)%R ->
  (ε1 * (length ns) <= ε0 * (N + 1))%R ->
  ↯ ε0 ∗
    (∀ x : fin (S N),
        (⌜Forall (λ m, (fin_to_nat x) ≠ m) ns⌝ ∨  ↯ ε1 ) -∗ Φ #x)
    ⊢ WP rand #z @ E {{ Φ }}.
Proof.
  iIntros (HN Hε1 HK) "[Herr Hwp]".
  iApply tgl_wp_pgl_wp'.
  wp_apply twp_rand_err_list_adv; eauto.
  iFrame.
Qed.

Lemma twp_rand_err_filter_adv (N : nat) (z : Z) (P : nat -> bool) (ε0 ε1 : R) E Φ :
  TCEq N (Z.to_nat z) →
  (0 <= ε1)%R ->
  (ε1 * (length (List.filter P (seq 0 (S N)))) <= ε0 * (N + 1))%R ->
  ↯ ε0 ∗
    (∀ x : fin (S N), ((⌜ P x = false⌝) ∨ ↯ ε1 ) -∗ Φ #x)
    ⊢ WP rand #z @ E [{ Φ }].
Proof.
  iIntros (? ? HK) "[H1 Hwp]".
  iApply (twp_rand_err_list_adv _ _ (List.filter P (seq 0 (S N))) ε0 ε1); auto.
  iFrame.
  iIntros (x) "[%Hfor|Herr]".
  - iApply "Hwp".
    iLeft.
    iPureIntro.
    edestruct (List.Forall_forall) as (H1 & H2).
    specialize (H1 Hfor).
    destruct (P x) eqn:HPx ; auto.
    exfalso.
    apply (H1 x); auto.
    apply filter_In; split; auto.
    apply in_seq.
    simpl.
    split; auto with arith.
    apply fin_to_nat_lt.
  - iApply "Hwp".
    iRight. iFrame.
Qed.


(* Two lemmas about lists. Could be moved, but not sure where to *)
Lemma length_filter_seq_below (N M : nat):
  (M <= N) ->
  length (List.filter (λ x : nat, bool_decide (x ≤ M)) (seq 0 (S N))) = (M + 1).
Proof.
  intro HMN.
  induction HMN.
  - rewrite forallb_filter_id.
    + rewrite seq_length. lia.
    + apply Is_true_eq_true.
      apply forallb_True.
      apply Forall_seq.
      intros.
      rewrite bool_decide_eq_true_2; auto.
      lia.
  - rewrite seq_S List.filter_app.
    rewrite app_length IHHMN.
    simpl.
    rewrite bool_decide_eq_false_2 /=; first by lia.
    intro H.
    lia.
Qed.


Lemma length_filter_seq_above (N M : nat):
  (M <= N) ->
  length (List.filter (λ x : nat, bool_decide (M < x)) (seq 0 (S N))) = (N - M).
Proof.
  intro HMN.
  induction HMN.
  - replace (length (List.filter (λ x : nat, bool_decide (M < x)) (seq 0 (S M))))
      with
      ((S M) - length (List.filter (λ x : nat, bool_decide (x <= M)) (seq 0 (S M)))).
    + rewrite forallb_filter_id.
      * rewrite seq_length. lia.
      * apply Is_true_eq_true.
        apply forallb_True.
        apply Forall_seq.
        intros.
        rewrite bool_decide_eq_true_2; auto.
        lia.
    + replace (S M) with (length (seq 0 (S M))) at 1;
        last by rewrite seq_length; auto.
      rewrite -(List.filter_length (λ x, bool_decide (x <= M))).
      rewrite Nat.add_sub'.
      f_equal.
      apply filter_ext.
      intro a.
      case_bool_decide; case_bool_decide; auto; lia.
  - rewrite seq_S List.filter_app.
    rewrite app_length IHHMN.
    simpl.
    rewrite bool_decide_eq_true_2 /=; first by lia.
    lia.
Qed.


Lemma twp_rand_err_filter_below (N : nat) (M : nat) (z : Z) (ε0 ε1 : R) E Φ :
  TCEq N (Z.to_nat z) →
  (M <= N) ->
  (0 <= ε1)%R ->
  (ε1 * (M + 1) <= ε0 * (N + 1))%R ->
  ↯ ε0 ∗
    (∀ x : fin (S N), ((⌜ M < x ⌝) ∨ ↯ ε1 ) -∗ Φ #x)
    ⊢ WP rand #z @ E [{ Φ }].
Proof.
  iIntros (? HMN ? HK) "[H1 Hwp]".
  iApply (twp_rand_err_filter_adv _ _ (λ x, bool_decide (x <= M))); eauto.
  - rewrite length_filter_seq_below; auto.
    rewrite plus_INR /=.
    done.
  - iFrame.
    iIntros (x) "[%H1 | H2]".
    + iApply "Hwp".
      iLeft.
      iPureIntro.
      apply bool_decide_eq_false_1 in H1.
      lia.
    + iApply "Hwp".
      iRight. done.
Qed.


Lemma twp_rand_err_filter_above (N : nat) (M : nat) (z : Z) (ε0 ε1 : R) E Φ :
  TCEq N (Z.to_nat z) →
  (M <= N) ->
  (0 <= ε1)%R ->
  (ε1 * (N - M) <= ε0 * (N + 1))%R ->
  ↯ ε0 ∗
    (∀ x : fin (S N), ((⌜ x <= M ⌝) ∨ ↯ ε1 ) -∗ Φ #x)
    ⊢ WP rand #z @ E [{ Φ }].
Proof.
  iIntros (? HMN ? HK) "[H1 Hwp]".
  iApply (twp_rand_err_filter_adv _ _ (λ x, bool_decide (M < x))); eauto.
  - rewrite length_filter_seq_above; auto.
    rewrite minus_INR /= //.
  - iFrame.
    iIntros (x) "[%H1 | H2]".
    + iApply "Hwp".
      iLeft.
      iPureIntro.
      apply bool_decide_eq_false_1 in H1.
      lia.
    + iApply "Hwp".
      iRight. done.
Qed.


Lemma wp_rand_err_filter_adv (N : nat) (z : Z) (P : nat -> bool) (ε0 ε1 : R) E Φ :
  TCEq N (Z.to_nat z) →
  (0 <= ε1)%R ->
  (ε1 * (length (List.filter P (seq 0 (S N)))) <= ε0 * (N + 1))%R ->
  ↯ ε0 ∗
    (∀ x : fin (S N), (⌜ P x = false⌝ ∨ ↯ ε1) -∗ Φ #x)
    ⊢ WP rand #z @ E {{ Φ }}.
Proof.
  iIntros (? ? HK) "[H1 Hwp]".
  iApply tgl_wp_pgl_wp'.
  wp_apply twp_rand_err_filter_adv; eauto.
  iFrame.
Qed.



Lemma wp_bind_err_simpl e `{Hctx:!LanguageCtx K} s E (ε1 ε2 : R) P (Q : val -> iProp Σ) Φ:
  (0 <= ε1)%R →
  (0 <= ε2)%R →
  (↯ ε1 -∗ P -∗ WP e @ s; E {{ Q }}) -∗
  (∀ x, Q x -∗ ↯ ε2 -∗ WP K (Val x) @ s ; E {{ Φ }}) -∗
  P -∗ ↯ (ε1+ε2)%NNR -∗ WP K e @ s; E {{ Φ }}.
  Proof.
    iIntros (??) "H1 H2 HP Hε".
    iApply pgl_wp_bind.
    rewrite ec_split //.
    iDestruct ("Hε") as "[He1 He2]".
    iApply (pgl_wp_wand with "[H1 He1 HP]").
    { by iApply ("H1" with "[$]"). }
    iIntros (v) "HQ".
    iApply ("H2" with "[$]"). done.
  Qed.

  Lemma wp_bind_err_exp e `{Hctx:!LanguageCtx K} s E ε1 ε2 P (Q : val -> iProp Σ) Φ:
    (↯ ε1 -∗ P -∗ WP e @ s; E {{ v, ↯ (ε2 v) ∗ (Q v)}}) -∗
    (∀ x, Q x -∗ ↯ (ε2 x) -∗ WP K (Val x) @ s ; E {{ Φ }}) -∗
    P -∗ ↯ ε1 -∗ WP K e @ s; E {{ Φ }}.
  Proof.
    iIntros "H1 H2 HP Hε".
    iApply pgl_wp_bind.
    iApply (pgl_wp_wand with "[H1 Hε HP]").
    { instantiate (1 := (λ v, ↯ (ε2 v) ∗ Q v)%I). by iApply ("H1" with "[$]"). }
    iIntros (v) "[Hε HQ]".
    iApply ("H2" with "[$]"). done.
  Qed.

  (** * Approximate Lifting *)

  Lemma pgl_state (N : nat) 𝜎 𝛼 ns :
    𝜎.(tapes) !! 𝛼 = Some (N; ns) →
    pgl
      (state_step 𝜎 𝛼)
      (λ 𝜎', ∃ (n : fin (S N)), 𝜎' = state_upd_tapes <[𝛼 := (N; ns ++ [n])]> 𝜎)
      nnreal_zero.
  Proof.
    rewrite /pgl. intros Htapes.
    apply Req_le_sym; simpl.
    rewrite /prob SeriesC_0; auto.
    intros 𝜎'.
    case_bool_decide; auto.
    rewrite /state_step.
    case_bool_decide.
    2: { exfalso. apply H0. by apply elem_of_dom. }
    intros.
    replace (lookup_total 𝛼 (tapes 𝜎)) with (N; ns).
    2: { rewrite (lookup_total_correct _ _ (existT N ns)); auto.  }
    apply dmap_unif_zero.
    intros n Hcont.
    apply H.
    naive_solver.
  Qed.

  (** adapted from wp_couple_tapes in the relational logic *)
  Lemma twp_presample (N : nat) E e 𝛼 Φ ns :
    to_val e = None →
    𝛼 ↪ (N; ns) ∗
      (∀ (n : fin (S N)), 𝛼 ↪ (N; ns ++ [n]) -∗ WP e @ E [{ Φ }])
      ⊢ WP e @ E [{ Φ }].
  Proof.
    iIntros (He) "(H𝛼&Hwp)".
    iApply twp_lift_step_fupd_glm; [done|].
    iIntros (𝜎 ε) "((Hheap&Htapes)&Hε)".
    iDestruct (ghost_map_lookup with "Htapes H𝛼") as %Hlookup.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    replace ε with (nnreal_zero + ε)%NNR by (apply nnreal_ext; simpl; lra).
    iApply glm_state_step.
    { rewrite /= /get_active.
      by apply elem_of_list_In, elem_of_list_In, elem_of_elements, elem_of_dom. }
    iExists _.
    iSplitR.
    { iPureIntro. apply pgl_state, Hlookup. }
    iIntros (𝜎') "[%n %H𝜎']".
    iDestruct (ghost_map_lookup with "Htapes H𝛼") as %?%lookup_total_correct.
    iMod (ghost_map_update ((N; ns ++ [n]) : tape) with "Htapes H𝛼") as "[Htapes H𝛼]".
    iMod "Hclose'" as "_".
    iSpecialize ("Hwp" $! n with "H𝛼").
    rewrite !tgl_wp_unfold /tgl_wp_pre /= He.
    iSpecialize ("Hwp" $! 𝜎' ε).
    iMod ("Hwp" with "[Hheap Htapes Hε]") as "Hwp".
    { replace (nnreal_zero + ε)%NNR with ε by (apply nnreal_ext; simpl; lra).
      rewrite H𝜎'.
      iFrame.
    }
    iModIntro. iApply "Hwp".
  Qed.

  Lemma wp_presample (N : nat) E e 𝛼 Φ ns :
    to_val e = None →
    ▷ 𝛼 ↪ (N; ns) ∗
      (∀ (n : fin (S N)), 𝛼 ↪ (N; ns ++ [n]) -∗ WP e @ E {{ Φ }})
      ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (He) "(>H𝛼&Hwp)".
    iApply wp_lift_step_fupd_glm; [done|].
    iIntros (𝜎 ε) "((Hheap&Htapes)&Hε)".
    iDestruct (ghost_map_lookup with "Htapes H𝛼") as %Hlookup.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    replace ε with (nnreal_zero + ε)%NNR by (apply nnreal_ext; simpl; lra).
    iApply glm_state_step.
    { rewrite /= /get_active.
      by apply elem_of_list_In, elem_of_list_In, elem_of_elements, elem_of_dom. }
    iExists _.
    iSplitR.
    { iPureIntro. apply pgl_state, Hlookup. }
    iIntros (𝜎') "[%n %H𝜎']".
    iDestruct (ghost_map_lookup with "Htapes H𝛼") as %?%lookup_total_correct.
    iMod (ghost_map_update ((N; ns ++ [n]) : tape) with "Htapes H𝛼") as "[Htapes H𝛼]".
    iMod "Hclose'" as "_".
    iSpecialize ("Hwp" $! n with "H𝛼").
    rewrite !pgl_wp_unfold /pgl_wp_pre /= He.
    iSpecialize ("Hwp" $! 𝜎' ε).
    iMod ("Hwp" with "[Hheap Htapes Hε]") as "Hwp".
    { replace (nnreal_zero + ε)%NNR with ε by (apply nnreal_ext; simpl; lra).
      rewrite H𝜎'.
      iFrame.
    }
    iModIntro. iApply "Hwp".
  Qed.

  Lemma twp_presample_adv_comp (N : nat) z E e α Φ ns (ε1 : R) (ε2 : fin (S N) -> R) :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (forall n, (0 <= ε2 n)%R) ->
    SeriesC (λ n, (1 / (S N)) * ε2 n)%R = ε1 →
    α ↪ (N; ns) ∗
      ↯ ε1 ∗
      (∀ (n : fin (S N)), ↯ (ε2 n) ∗ α ↪ (N; ns ++ [n]) -∗ WP e @ E [{ Φ }])
      ⊢ WP e @ E [{ Φ }].
  Proof.
    iIntros (-> Hσ_red Hε2pos Hsum) "(Hα & Hε & Hwp)".
    destruct (fin_function_bounded (S (Z.to_nat z)) ε2) as [r Hr_ub].
    assert (0 <= r)%R as Hrpos.
    {
      transitivity (ε2 0%fin); auto.
    }
    iApply twp_lift_step_fupd_glm; [done|].
    iIntros (σ1 ε_now) "[(Hheap&Htapes) Hε_supply]".
    iDestruct (ghost_map_lookup with "Htapes Hα") as %Hlookup.
    iDestruct (ec_supply_bound with "Hε_supply Hε") as %Hε1_ub.

    iMod (ec_supply_decrease with "Hε_supply Hε") as (ε1' ε_rem -> Hε1') "Hε_supply".
    iApply fupd_mask_intro; [set_solver|].
    iIntros "Hclose".
    iApply (glm_state_adv_comp' α); simpl.
    { rewrite /get_active.
      apply elem_of_list_In, elem_of_list_In, elem_of_elements, elem_of_dom.
      done. }
    (* iDestruct (ec_supply_ec_inv with "Hε_supply Hε") as %(ε1' & ε_rem & -> & Hε1'). *)


    (* R: predicate should hold iff tapes σ' at α is ns ++ [n] *)
    iExists
      (fun σ' : state => exists n : fin _, σ' = (state_upd_tapes <[α:=(_; ns ++ [n]) : tape]> σ1)),
      (fun ρ => (ε_rem +
                   match finite.find (fun s => state_upd_tapes <[α:=(_; ns ++ [s]) : tape]> σ1 = snd ρ) with
                   | Some s => mknonnegreal _ (Hε2pos s)
                   | None => nnreal_zero
                   end))%NNR.

    (* upper bound on ε2 *)
    iSplit.
    { iPureIntro.
      assert (Hr_nnonneg : (0 <= r)%R).
      { eapply Rle_trans; [|apply (Hr_ub 0%fin)].
        auto.
      }
      exists (ε_rem + r)%R.
      intros [e' σ'].
      apply Rplus_le_compat_l.
      destruct (finite.find _); auto; apply Hr_ub.
    }

    (* upper bound on total error *)
    iSplit.
    { iPureIntro. simpl.
      rewrite Hε1'.
      rewrite -Hsum.
      setoid_rewrite Rmult_plus_distr_l.
      rewrite SeriesC_plus.
      (* existence *)
      2: { apply ex_seriesC_scal_r, pmf_ex_seriesC. }
      2: { apply pmf_ex_seriesC_mult_fn.
           exists r; intros; split.
           - apply cond_nonneg.
           - destruct (finite.find _); [apply Hr_ub | simpl; auto]. }

      apply Rplus_le_compat.
      { (* holds because state_step is a pmf so is lt 1 *)
        rewrite SeriesC_scal_r -{2}(Rmult_1_l (nonneg ε_rem)).
        apply Rmult_le_compat; try auto; lra. }

      (* rewrite to a form for SeriesC_le *)
      pose f := (fun n : fin _ => 1 / S (Z.to_nat z) * ε2 n)%R.
      rewrite (SeriesC_ext
                 (λ x : state, state_step σ1 α x * _)%R
                 (fun x : state => from_option f 0
                                     (finite.find (fun n => state_upd_tapes <[α:=(_; ns ++ [n]) : tape]> σ1 = x ))%R));
        last first.
      { intros n.
        destruct (finite.find _) as [sf|] eqn:HeqF.
        - Opaque INR.
          apply find_Some in HeqF.
          simpl in HeqF; rewrite -HeqF.
          rewrite /from_option /f.
          apply Rmult_eq_compat_r.
          rewrite /state_upd_tapes /=.
          rewrite /pmf /state_step.
          rewrite bool_decide_true; last first.
          { rewrite elem_of_dom Hlookup /= /is_Some; by exists (Z.to_nat z; ns). }
          rewrite (lookup_total_correct _ _ (Z.to_nat z; ns)); auto.
          rewrite /dmap /dbind /dbind_pmf /pmf.
          rewrite /= SeriesC_scal_l -{1}(Rmult_1_r (1 / _))%R.
          rewrite /Rdiv Rmult_1_l; apply Rmult_eq_compat_l.
          (* this series is 0 unless a = sf *)
          rewrite /dret /dret_pmf.
          rewrite -{2}(SeriesC_singleton sf 1%R).
          apply SeriesC_ext; intros.
          symmetry.
          case_bool_decide; simplify_eq.
          + rewrite bool_decide_true; auto.
          + rewrite bool_decide_false; auto.
            rewrite /not; intros Hcont.
            rewrite /not in H; apply H.
            rewrite /state_upd_tapes in Hcont.
            assert (R1 : ((Z.to_nat z; ns ++ [sf]) : tape) = (Z.to_nat z; ns ++ [n0])).
            { apply (insert_inv (tapes σ1) α). by inversion Hcont. }
            apply Eqdep_dec.inj_pair2_eq_dec in R1; [|apply PeanoNat.Nat.eq_dec].
            apply app_inv_head in R1.
            by inversion R1.
            Transparent INR.
        - rewrite /from_option /INR /=. lra.
      }

      apply SeriesC_le_inj.
      - (* f is nonnegative *)
        intros.
        apply Rmult_le_pos.
        + rewrite /Rdiv.
          apply Rmult_le_pos; try lra.
          apply Rlt_le, Rinv_0_lt_compat, pos_INR_S.
        + auto.
      - (* injection *)
        intros ? ? ? HF1 HF2.
        apply find_Some in HF1.
        apply find_Some in HF2.
        by rewrite -HF1 -HF2.
      - (* existence *)
        apply ex_seriesC_finite.
    }

    (* lifted lookup on tapes *)
    iSplit.
    {
      iPureIntro.
      eapply pgl_mon_pred; last first.
      - apply pgl_state. apply Hlookup.
      - done.
    }

    iIntros ((heap2 & tapes2)) "[%sample %Hsample]".

    rewrite /= Hsample.
    destruct (@find_is_Some _ _ _
                (λ s : fin (S (Z.to_nat z)), state_upd_tapes <[α:=(Z.to_nat z; ns ++ [s])]> σ1 = state_upd_tapes <[α:=(Z.to_nat z; ns ++ [sample])]> σ1)
                _ sample eq_refl)
      as [r' [Hfind Hr']].
    rewrite Hfind.
    replace r' with sample; last first.
    { rewrite /state_upd_tapes in Hr'.
      inversion Hr' as [Heqt].
      apply (insert_inv (tapes σ1) α) in Heqt.
      apply Eqdep_dec.inj_pair2_eq_dec in Heqt; [|apply PeanoNat.Nat.eq_dec].
      apply app_inv_head in Heqt.
      by inversion Heqt. }
    destruct (Rlt_decision (nonneg ε_rem + (ε2 sample))%R 1%R) as [Hdec|Hdec]; last first.
    { apply Rnot_lt_ge, Rge_le in Hdec.
      iApply exec_stutter_spend.
      iPureIntro.
      simpl ; lra.
    }
    (* replace (nonneg ε_rem + nonneg (ε2 sample))%R with (nonneg (ε_rem + ε2 sample)%NNR); [|by simpl]. *)
    iApply exec_stutter_free.
    iMod (ec_supply_increase _ (mknonnegreal _ (Hε2pos sample)) with "[$Hε_supply]") as "[Hε_supply Hε]".
    { simplify_eq. simpl. lra. }


    iMod (ghost_map_update ((Z.to_nat z; ns ++ [sample]) : tape) with "Htapes Hα") as "[Htapes Hα]".
    iSpecialize ("Hwp" $! sample).
    rewrite tgl_wp_unfold /tgl_wp_pre.
    simpl.
    remember {| heap := heap2; tapes := tapes2 |} as σ2.
    rewrite Hσ_red.
    iSpecialize ("Hwp" with "[Hε Hα]"); first iFrame.
    iSpecialize ("Hwp" $! σ2 _).
    iSpecialize ("Hwp" with "[Hheap Htapes Hε_supply]").
    { iSplitL "Hheap Htapes".
      - rewrite /tapes_auth.
        rewrite Heqσ2 in Hsample. inversion Hsample.
        simplify_eq. simpl. iFrame.
      - iFrame. }
    rewrite -Hsample.
    iMod "Hclose"; iMod "Hwp"; iModIntro.
    simplify_eq.
    done.
  Qed.

  Lemma wp_presample_adv_comp (N : nat) z E e α Φ ns (ε1 : R) (ε2 : fin (S N) -> R) :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (forall n, (0 <= ε2 n)%R) ->
    SeriesC (λ n, (1 / (S N)) * ε2 n)%R = ε1 →
    α ↪ (N; ns) ∗
      ↯ ε1 ∗
      (∀ (n : fin (S N)), ↯ (ε2 n) ∗ α ↪ (N; ns ++ [n]) -∗ WP e @ E {{ Φ }})
      ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (-> Hσ_red Hε2pos Hsum) "(Hα & Hε & Hwp)".
    destruct (fin_function_bounded (S (Z.to_nat z)) ε2) as [r Hr_ub].
    assert (0 <= r)%R as Hrpos.
    {
      transitivity (ε2 0%fin); auto.
    }
    iApply wp_lift_step_fupd_glm; [done|].
    iIntros (σ1 ε_now) "[(Hheap&Htapes) Hε_supply]".
    iDestruct (ghost_map_lookup with "Htapes Hα") as %Hlookup.
    iDestruct (ec_supply_bound with "Hε_supply Hε") as %Hε1_ub.
    iMod (ec_supply_decrease with "Hε_supply Hε") as (ε1' ε_rem -> Hε1') "Hε_supply".
    iApply fupd_mask_intro; [set_solver|].
    iIntros "Hclose".
    iApply (glm_state_adv_comp' α); simpl.
    { rewrite /get_active.
      apply elem_of_list_In, elem_of_list_In, elem_of_elements, elem_of_dom.
      done. }

    (* R: predicate should hold iff tapes σ' at α is ns ++ [n] *)
    iExists
      (fun σ' : state => exists n : fin _, σ' = (state_upd_tapes <[α:=(_; ns ++ [n]) : tape]> σ1)),
      (fun ρ => (ε_rem +
                   match finite.find (fun s => state_upd_tapes <[α:=(_; ns ++ [s]) : tape]> σ1 = snd ρ) with
                   | Some s => mknonnegreal _ (Hε2pos s)
                   | None => nnreal_zero
                   end))%NNR.

    (* upper bound on ε2 *)
    iSplit.
    { iPureIntro.
      exists (ε_rem + r)%R.
      intros [e' σ'].
      apply Rplus_le_compat_l.
      destruct (finite.find _); auto; apply Hr_ub.
    }

    (* upper bound on total error *)
    iSplit.
    { iPureIntro. simpl.
      rewrite Hε1'.
      rewrite -Hsum.
      setoid_rewrite Rmult_plus_distr_l.
      rewrite SeriesC_plus.
      (* existence *)
      2: { apply ex_seriesC_scal_r, pmf_ex_seriesC. }
      2: { apply pmf_ex_seriesC_mult_fn.
           exists r; intros; split.
           - apply cond_nonneg.
           - destruct (finite.find _); [apply Hr_ub | simpl; auto ]. }

      apply Rplus_le_compat.
      { (* holds because state_step is a pmf so is lt 1 *)
        rewrite SeriesC_scal_r -{2}(Rmult_1_l (nonneg ε_rem)).
        apply Rmult_le_compat; try auto; lra. }

      (* rewrite to a form for SeriesC_le *)
      pose f := (fun n : fin _ => 1 / S (Z.to_nat z) * ε2 n)%R.
      rewrite (SeriesC_ext
                 (λ x : state, state_step σ1 α x * _)%R
                 (fun x : state => from_option f 0
                                     (finite.find (fun n => state_upd_tapes <[α:=(_; ns ++ [n]) : tape]> σ1 = x ))%R));
        last first.
      { intros n.
        destruct (finite.find _) as [sf|] eqn:HeqF.
        - Opaque INR.
          apply find_Some in HeqF.
          simpl in HeqF; rewrite -HeqF.
          rewrite /from_option /f.
          apply Rmult_eq_compat_r.
          rewrite /state_upd_tapes /=.
          rewrite /pmf /state_step.
          rewrite bool_decide_true; last first.
          { rewrite elem_of_dom Hlookup /= /is_Some; by exists (Z.to_nat z; ns). }
          rewrite (lookup_total_correct _ _ (Z.to_nat z; ns)); auto.
          rewrite /dmap /dbind /dbind_pmf /pmf.
          rewrite /= SeriesC_scal_l -{1}(Rmult_1_r (1 / _))%R.
          rewrite /Rdiv Rmult_1_l; apply Rmult_eq_compat_l.
          (* this series is 0 unless a = sf *)
          rewrite /dret /dret_pmf.
          rewrite -{2}(SeriesC_singleton sf 1%R).
          apply SeriesC_ext; intros.
          symmetry.
          case_bool_decide; simplify_eq.
          + rewrite bool_decide_true; auto.
          + rewrite bool_decide_false; auto.
            rewrite /not; intros Hcont.
            rewrite /not in H; apply H.
            rewrite /state_upd_tapes in Hcont.
            assert (R1 : ((Z.to_nat z; ns ++ [sf]) : tape) = (Z.to_nat z; ns ++ [n0])).
            { apply (insert_inv (tapes σ1) α). by inversion Hcont. }
            apply Eqdep_dec.inj_pair2_eq_dec in R1; [|apply PeanoNat.Nat.eq_dec].
            apply app_inv_head in R1.
            by inversion R1.
            Transparent INR.
        - rewrite /from_option /INR /=. lra.
      }

      apply SeriesC_le_inj.
      - (* f is nonnegative *)
        intros.
        apply Rmult_le_pos.
        + rewrite /Rdiv.
          apply Rmult_le_pos; try lra.
          apply Rlt_le, Rinv_0_lt_compat, pos_INR_S.
        + auto.
      - (* injection *)
        intros ? ? ? HF1 HF2.
        apply find_Some in HF1.
        apply find_Some in HF2.
        by rewrite -HF1 -HF2.
      - (* existence *)
        apply ex_seriesC_finite.
    }

    (* lifted lookup on tapes *)
    iSplit.
    {
      iPureIntro.
      eapply pgl_mon_pred; last first.
      - apply pgl_state. apply Hlookup.
      - done.
    }

    iIntros ((heap2 & tapes2)) "[%sample %Hsample]".

    rewrite Hsample /=.
    destruct (@find_is_Some _ _ _
                (λ s : fin (S (Z.to_nat z)), state_upd_tapes <[α:=(Z.to_nat z; ns ++ [s])]> σ1 = state_upd_tapes <[α:=(Z.to_nat z; ns ++ [sample])]> σ1)
                _ sample eq_refl)
      as [r' [Hfind Hr']].
    rewrite Hfind.
    replace r' with sample; last first.
    { rewrite /state_upd_tapes in Hr'.
      inversion Hr' as [Heqt].
      apply (insert_inv (tapes σ1) α) in Heqt.
      apply Eqdep_dec.inj_pair2_eq_dec in Heqt; [|apply PeanoNat.Nat.eq_dec].
      apply app_inv_head in Heqt.
      by inversion Heqt. }
    destruct (Rlt_decision (nonneg ε_rem + (ε2 sample))%R 1%R) as [Hdec|Hdec]; last first.
    { apply Rnot_lt_ge, Rge_le in Hdec.
      iApply exec_stutter_spend.
      iPureIntro.
      simpl ; lra.
    }
    iMod (ec_supply_increase _ (mknonnegreal _ (Hε2pos sample)) with "Hε_supply") as "[Hε_supply Hε]".
    { simplify_eq. simpl. lra. }
    iMod (ghost_map_update ((Z.to_nat z; ns ++ [sample]) : tape) with "Htapes Hα") as "[Htapes Hα]".
    iSpecialize ("Hwp" $! sample).
    rewrite pgl_wp_unfold /pgl_wp_pre.
    remember {| heap := heap2; tapes := tapes2 |} as σ2.
    rewrite /= Hσ_red /=.
    iSpecialize ("Hwp" with "[Hε Hα]"); first iFrame.
    iSpecialize ("Hwp" $! σ2 _).
    iSpecialize ("Hwp" with "[Hheap Htapes Hε_supply]").
    { iSplitL "Hheap Htapes".
      - rewrite /tapes_auth.
        rewrite Heqσ2 in Hsample. inversion Hsample.
        simplify_eq. simpl. iFrame.
      - iFrame. }
    rewrite -Hsample.
    iMod "Hclose"; iMod "Hwp"; iModIntro.
    (* replace (nonneg ε_rem + nonneg (ε2 sample))%R with (nonneg (ε_rem + ε2 sample)%NNR); [|by simpl]. *)
    iApply exec_stutter_free.
    iFrame.
  Qed.

  Lemma wp_presample_adv_comp_leq (N : nat) z E e α Φ ns (ε1 : R) (ε2 : fin (S N) -> R) :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (forall n, (0 <= ε2 n)%R) ->
    (SeriesC (λ n, (1 / (S N)) * ε2 n) <= ε1)%R →
    α ↪ (N; ns) ∗
      ↯ ε1 ∗
      (∀ (n : fin (S N)), ↯ (ε2 n) ∗ α ↪ (N; ns ++ [n]) -∗ WP e @ E {{ Φ }})
      ⊢ WP e @ E {{ Φ }}.
  Proof.
    set (ε3 := SeriesC (λ n, (1 / (S N)) * ε2 n)%R).
    iIntros (-> Hσ_red Hε2pos Hsum) "(Hα & Hε & Hwp)".
    iPoseProof (ec_weaken with "Hε") as "Hε".
    { split; last apply Hsum.
      apply SeriesC_ge_0'.
      intros x.
      real_solver.
    }
    iApply wp_presample_adv_comp; eauto; iFrame.
  Qed.


  Lemma wp_presample_adv_comp_leq_double (N : nat) z E e α Φ ns (ε11 ε12 : R) (ε21 ε22 : fin (S N) -> R) :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (forall n, (0 <= ε21 n)%R) ->
    (forall n, (0 <= ε22 n)%R) ->
    (SeriesC (λ n, (1 / (S N)) * ε21 n) <= ε11)%R →
    (SeriesC (λ n, (1 / (S N)) * ε22 n)%R <= ε12)%R →
    α ↪ (N; ns) ∗
      ↯ ε11 ∗ ↯ ε12 ∗
      (∀ (n : fin (S N)), ↯ (ε21 n) ∗ ↯ (ε22 n) ∗ α ↪ (N; ns ++ [n]) -∗ WP e @ E {{ Φ }})
      ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (-> Hσ_red Hε21pos Hε22pos Hsum1 Hsum2) "(Hα & Hε11 & Hε12 & Hwp)".
    set (bigε := λ j, (ε21 j + ε22 j)%R ).
    iPoseProof (ec_combine with "[$]") as "Hε".
    iApply (wp_presample_adv_comp_leq _ _ _ _ _ _ _ _ bigε with "[$Hα $Hε Hwp]"); eauto.
    { intros n.
      rewrite /bigε.
      apply Rplus_le_le_0_compat; auto.
    }
    - rewrite /bigε.
      setoid_rewrite Rmult_plus_distr_l.
      rewrite SeriesC_plus; [ |apply ex_seriesC_finite| apply ex_seriesC_finite].
      rewrite Rplus_comm.
      apply Rplus_le_compat; auto.
    - iIntros (n) "(Hε & Hα)".
      rewrite /bigε.
      iPoseProof (ec_split with "Hε") as "(?&?)"; auto.
      iApply ("Hwp" with "[$]").
  Qed.


  Lemma wp_1_err e E Φ :
    to_val e = None -> (forall σ, reducible (e, σ)) -> ↯ nnreal_one ⊢ WP e @ E {{Φ}}.
  Proof.
    iIntros (H1 H2) "He".
    iApply wp_lift_step_fupd_glm; first done.
    iIntros (σ1 ε) "[Hσ Hε]".
    iApply fupd_mask_intro; [set_solver|].
    iIntros "Hclose'".
    iDestruct (ec_supply_bound with "Hε He ") as %Hle.
    iApply glm_prim_step.
    iExists (λ _, False), nnreal_one, nnreal_zero.
    iSplitR.
    { iPureIntro. eauto. }
    iSplitR.
    { iPureIntro.
      assert (nnreal_one + nnreal_zero = nnreal_one)%R as Heq; last by rewrite Heq.
      simpl. lra.
    }
    iSplitR.
    { iPureIntro. unfold pgl. intros.
      by epose proof prob_le_1 as K.
    }
    by iIntros (? Hfalse) "%".
  Qed.

  (* FIXME: remove me *)
  Lemma twp_ec_spend e E Φ ε :
    (1 <= ε.(nonneg))%R →
    (to_val e = None) ->
    ↯ ε -∗ WP e @ E [{ Φ }].
  Proof.
    iIntros (? ?) "?".
    iExFalso.
    by iApply ec_contradict.
  Qed.

  (* FIXME: remove me *)
  Lemma wp_ec_spend e E Φ ε :
    (1 <= ε.(nonneg))%R →
    (to_val e = None) ->
    ↯ ε -∗ WP e @ E {{ Φ }}.
  Proof.
    iIntros.
    iApply tgl_wp_pgl_wp'.
    iApply twp_ec_spend; try done.
  Qed.


  Lemma amplification_depth N L (kwf : kwf N L) (ε : posreal) :
    exists n : nat, (1 <= ε * (k N L kwf) ^ n)%R.
  Proof.
    destruct kwf.
    intros.
    remember (1 + 1 / (S N ^ L - 1))%R as β.
    assert (H1 : Lim_seq.is_lim_seq (fun n => (β ^ n)%R) Rbar.p_infty).
    { eapply Lim_seq.is_lim_seq_geom_p.
      rewrite Heqβ.
      apply (Rplus_lt_reg_l (-1)%R).
      rewrite -Rplus_assoc Rplus_opp_l Rplus_0_l.
      rewrite /Rdiv Rmult_1_l.
      apply Rinv_0_lt_compat.
      apply (Rplus_lt_reg_r 1%R).
      rewrite Rplus_assoc Rplus_opp_l Rplus_0_r Rplus_0_l.
      apply Rlt_pow_R1; auto.
      apply lt_1_INR; lia.
    }
    rewrite /Lim_seq.is_lim_seq
      /Hierarchy.filterlim
      /Hierarchy.filter_le
      /Hierarchy.eventually
      /Hierarchy.filtermap
      /= in H1.
    destruct (H1 (fun r : R => (/ ε <= r)%R)); simpl.
    - exists (/ε)%R; intros; by apply Rlt_le.
    - exists x.
      apply (Rmult_le_reg_l (/ ε)%R).
      + apply Rinv_0_lt_compat, cond_pos.
      + rewrite -Rmult_assoc Rinv_l; last first.
        { pose (cond_pos ε); lra. }
        rewrite Rmult_1_l Rmult_1_r /k -Heqβ.
        by apply H.
  Qed.

  (* FIXME: relocate? *)
  Lemma lookup_ex {A} (n : nat) (L : list A) : (n < length L)%nat -> exists x, (L !! n) = Some x.
  Proof.
    intros HL.
    destruct L as [|h H]; [simpl in HL; lia|].
    generalize dependent H. generalize dependent h.
    induction n as [|n' IH].
    - intros h ? ?. exists h; by simpl.
    - intros h H HL.
      rewrite cons_length in HL. apply PeanoNat.lt_S_n in HL.
      destruct H as [|h' H']; [simpl in HL; lia|].
      replace ((h :: h' :: H') !! S n') with ((h' :: H') !! n'); last by simpl.
      by apply IH.
  Qed.


  Lemma twp_presample_amplify' N z e E α Φ (ε : posreal) L kwf prefix suffix_total (suffix_remaining : list (fin (S N))) :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    L = length suffix_total ->
    (0 < L)%nat ->
    (α ↪ (N; prefix) ∗
       (↯ (pos_to_nn ε))
       ⊢ (∀ (i : nat) (HL : (i <= L)%nat),
           (((∃ junk, α ↪ (N; prefix ++ junk) ∗ ↯(εAmp N L ε kwf)) ∨
               (α ↪ (N; prefix ++ (take i suffix_total)) ∗ ↯ (εR N L i ε (mk_fRwf N L i kwf HL))))
            -∗ WP e @ E [{ Φ }])
           -∗ WP e @ E [{ Φ }]))%I.
  Proof.
    iIntros (? ? Htotal HLpos) "(Htape & Hcr_initial)".
    iIntros (i HL).
    iInduction i as [|i'] "IH" forall (suffix_remaining).
                                      - iIntros "Hwp"; iApply "Hwp".
                                        iRight. iSplitL "Htape".
                                        + rewrite take_0. rewrite app_nil_r. iFrame.
                                        + rewrite /εR /fR /pos_to_nn /=.
                                          rewrite Rmult_1_r //.
                                      - iIntros "Hwand".
                                        assert (HL' : (i' <= L)%nat) by lia.
                                        iSpecialize ("IH" $! HL' _ with "Htape Hcr_initial").
                                        iApply "IH". iIntros "[[%junk(Htape&Hcr)]|(Htape&Hcr)]".
                                        + iApply "Hwand".
                                          iLeft; iExists junk. iFrame.
                                        + assert (Hi' : (i' < length suffix_total)%nat) by lia.
                                          destruct (lookup_ex i' suffix_total Hi') as [target Htarget].
                                          rewrite (take_S_r _ _ target); [|apply Htarget].
                                          pose HMean := (εDistr_mean N L i' ε target (mk_fRwf N L (S i') kwf HL)).
                                          wp_apply twp_presample_adv_comp; [done | | apply HMean | ].
                                          {
                                            intros i.
                                            apply cond_nonneg.
                                          }
                                          replace {| k_wf := kwf; i_ub := HL' |} with
                                            (fRwf_dec_i N L i' {| k_wf := kwf; i_ub := HL |}); [|apply fRwf_ext].
                                          iFrame.
                                          iIntros (s) "(Htape&Hcr)".
                                          iApply "Hwand".
                                          rewrite /εDistr.
                                          case_bool_decide.
                                          * iRight. simplify_eq; rewrite app_assoc; iFrame.
                                          * iLeft. iExists (take i' suffix_total ++ [s]).
                                            replace (k_wf N L (S i') {| k_wf := kwf; i_ub := HL |}) with kwf; last by apply kwf_ext.
                                            rewrite -app_assoc; iFrame.
                                            Unshelve. auto.
  Qed.

  Lemma presample_amplify' N z e E α Φ (ε : posreal) L kwf prefix suffix_total (suffix_remaining : list (fin (S N))) :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    L = length suffix_total ->
    (0 < L)%nat ->
    (α ↪ (N; prefix) ∗
       (↯ (pos_to_nn ε))
       ⊢ (∀ (i : nat) (HL : (i <= L)%nat),
           (((∃ junk, α ↪ (N; prefix ++ junk) ∗ ↯(εAmp N L ε kwf)) ∨
               (α ↪ (N; prefix ++ (take i suffix_total)) ∗ ↯ (εR N L i ε (mk_fRwf N L i kwf HL))))
            -∗ WP e @ E {{ Φ }})
           -∗ WP e @ E {{ Φ }}))%I.
  Proof.
    iIntros (? ? Htotal HLpos) "(Htape & Hcr_initial)".
    iIntros (i HL).
    iInduction i as [|i'] "IH" forall (suffix_remaining).
                                      - iIntros "Hwp"; iApply "Hwp".
                                        iRight. iSplitL "Htape".
                                        + rewrite take_0 app_nil_r. iFrame.
                                        + rewrite /εR /fR /pos_to_nn /=.
                                          rewrite Rmult_1_r //.
                                      - iIntros "Hwand".
                                        assert (HL' : (i' <= L)%nat) by lia.
                                        iSpecialize ("IH" $! HL' _ with "Htape Hcr_initial").
                                        iApply "IH". iIntros "[[%junk(Htape&Hcr)]|(Htape&Hcr)]".
                                        + iApply "Hwand".
                                          iLeft; iExists junk. iFrame.
                                        + assert (Hi' : (i' < length suffix_total)%nat) by lia.
                                          destruct (lookup_ex i' suffix_total Hi') as [target Htarget].
                                          rewrite (take_S_r _ _ target); [|apply Htarget].
                                          pose HMean := (εDistr_mean N L i' ε target (mk_fRwf N L (S i') kwf HL)).
                                          wp_apply wp_presample_adv_comp; [done | | apply HMean | ].
                                          {
                                            intros; apply cond_nonneg.
                                          }
                                          replace {| k_wf := kwf; i_ub := HL' |} with
                                            (fRwf_dec_i N L i' {| k_wf := kwf; i_ub := HL |}); [|apply fRwf_ext].
                                          iFrame.
                                          iIntros (s) "(Htape&Hcr)".
                                          iApply "Hwand".
                                          rewrite /εDistr.
                                          case_bool_decide.
                                          * iRight. simplify_eq; rewrite app_assoc; iFrame.
                                          * iLeft. iExists (take i' suffix_total ++ [s]).
                                            replace (k_wf N L (S i') {| k_wf := kwf; i_ub := HL |}) with kwf; last by apply kwf_ext.
                                            rewrite -app_assoc; iFrame.
                                            Unshelve. auto.
  Qed.

  (* do one step in the amplification sequence *)
  Lemma twp_presample_amplify N z e E α Φ (ε : posreal) L (kwf: kwf N L) prefix suffix :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    L = (length suffix) ->
    ↯ (pos_to_nn ε) ∗
      (α ↪ (N; prefix)) ∗
      ((α ↪ (N; prefix ++ suffix) ∨ (∃ junk, α ↪ (N; prefix ++ junk) ∗ ↯(εAmp N L ε kwf))) -∗ WP e @ E [{ Φ }])
      ⊢ WP e @ E [{ Φ }].
  Proof.
    iIntros (? ? Hl) "(Hcr & Htape & Hwp)".
    destruct suffix as [|s0 sr].
    - iApply "Hwp". iLeft. rewrite app_nil_r. iFrame.
    - remember (s0 :: sr) as suffix.
      assert (Hl_pos : (0 < L)%nat).
      { rewrite Hl Heqsuffix cons_length. lia. }
      iApply (twp_presample_amplify' with "[Htape Hcr]"); eauto; [iFrame|].
      iIntros "[H|(H&_)]"; iApply "Hwp".
      + iRight. by iFrame.
      + iLeft. erewrite firstn_all; iFrame.
        Unshelve. lia.
  Qed.

  (* do one step in the amplification sequence *)
  Lemma wp_presample_amplify N z e E α Φ (ε : posreal) L (kwf: kwf N L) prefix suffix :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    L = (length suffix) ->
    ↯ (pos_to_nn ε) ∗
      (α ↪ (N; prefix)) ∗
      ((α ↪ (N; prefix ++ suffix) ∨ (∃ junk, α ↪ (N; prefix ++ junk) ∗ ↯(εAmp N L ε kwf))) -∗ WP e @ E {{ Φ }})
      ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (? ? Hl) "(Hcr & Htape & Hwp)".
    destruct suffix as [|s0 sr].
    - iApply "Hwp". iLeft. rewrite app_nil_r. iFrame.
    - remember (s0 :: sr) as suffix'.
      assert (Hl_pos : (0 < L)%nat).
      { rewrite Hl Heqsuffix' cons_length. lia. }
      iApply (presample_amplify' with "[Htape Hcr]"); eauto; [iFrame|].
      iIntros "[H|(H&_)]"; iApply "Hwp".
      + iRight. by iFrame.
      + iLeft. erewrite firstn_all; iFrame.
        Unshelve. lia.
  Qed.

  Lemma twp_seq_amplify N z e E α Φ (ε : posreal) L (kwf: kwf N L) prefix suffix d :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (forall junk, 0 < (length (suffix (prefix ++ junk))) <= L)%nat ->
    ↯ (pos_to_nn ε) ∗
      (α ↪ (N; prefix)) ∗
      ((∃ junk, α ↪ (N; prefix ++ junk ++ (suffix (prefix ++ junk))) ∨ α ↪ (N; prefix ++ junk) ∗ ↯(pos_to_nn (εAmp_iter N L d ε kwf)))
       -∗ WP e @ E [{ Φ }])
      ⊢ WP e @ E [{ Φ }].
  Proof.
    iIntros (? ? HL) "(Hcr&Htape&Hwp)".
    iInduction (d) as [|d'] "IH".
    - iApply "Hwp".
      iExists []; rewrite app_nil_r. iRight. iFrame.
      rewrite /εAmp_iter /pos_to_nn /= Rmult_1_r //.
    - iApply ("IH" with "Hcr Htape").
      iIntros "[%junk [Hlucky|(Htape&Hcr)]]".
      + iApply "Hwp". iExists junk; iLeft; iFrame.
      + pose L' := (length (suffix (prefix ++ junk))).
        iApply (twp_presample_amplify _ _ _ _ _ _ _ L'); eauto; iFrame.
        iIntros "[?|[%junk' (Htape&Hcr)]]"; iApply "Hwp".
        * iExists _; iLeft.
          rewrite -app_assoc; iFrame.
        * iExists _; iRight.
          rewrite -app_assoc -εAmp_iter_cmp; iFrame.
          iApply (ec_weaken with "Hcr").
          rewrite /εAmp /=.
          split.
          { apply Rmult_le_pos.
            - apply Rmult_le_pos; [apply Rlt_le, cond_pos | apply pow_le, Rlt_le, k_pos].
            - apply Rlt_le, k_pos. }
          apply Rmult_le_compat_l.
          { apply Rmult_le_pos; [apply Rlt_le, cond_pos | apply pow_le, Rlt_le, k_pos]. }
          apply Rplus_le_compat_l.
          rewrite /Rdiv Rmult_1_l Rmult_1_l.
          apply Rinv_le_contravar.
          -- apply (Rplus_lt_reg_r 1%R).
             rewrite /Rminus Rplus_assoc Rplus_opp_l Rplus_0_l Rplus_0_r.
             apply Rlt_pow_R1.
             --- apply lt_1_INR; destruct kwf; lia.
             --- rewrite /L'. by destruct (HL junk).
          -- apply Rplus_le_compat_r, Rle_pow.
             --- rewrite S_INR. pose P := (pos_INR N); lra.
             --- rewrite /L'. by destruct (HL junk).
                 Unshelve.
                 destruct kwf.
                 destruct (HL junk).
                 rewrite /L'.
                 constructor; try lia.
  Qed.

  Lemma seq_amplify N z e E α Φ (ε : posreal) L (kwf: kwf N L) prefix suffix d :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (forall junk, 0 < (length (suffix (prefix ++ junk))) <= L)%nat ->
    ↯ (pos_to_nn ε) ∗
      (α ↪ (N; prefix)) ∗
      ((∃ junk, α ↪ (N; prefix ++ junk ++ (suffix (prefix ++ junk))) ∨ α ↪ (N; prefix ++ junk) ∗ ↯(pos_to_nn (εAmp_iter N L d ε kwf)))
       -∗ WP e @ E {{ Φ }})
      ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (? ? HL) "(Hcr&Htape&Hwp)".
    iInduction (d) as [|d'] "IH".
    - iApply "Hwp".
      iExists []; rewrite app_nil_r. iRight. iFrame.
      iApply ec_eq; last auto.
      by rewrite /εAmp_iter /pos_to_nn /= Rmult_1_r.
    - iApply ("IH" with "Hcr Htape").
      iIntros "[%junk [Hlucky|(Htape&Hcr)]]".
      + iApply "Hwp". iExists junk; iLeft; iFrame.
      + pose L' := (length (suffix (prefix ++ junk))).
        iApply (wp_presample_amplify _ _ _ _ _ _ _ L'); eauto; iFrame.
        iIntros "[?|[%junk' (Htape&Hcr)]]"; iApply "Hwp".
        * iExists _; iLeft.
          rewrite -app_assoc; iFrame.
        * iExists _; iRight.
          rewrite -app_assoc -εAmp_iter_cmp; iFrame.
          iApply (ec_weaken with "Hcr").
          split.
          { apply Rmult_le_pos.
            - apply Rmult_le_pos; [apply Rlt_le, cond_pos | apply pow_le, Rlt_le, k_pos].
            - apply Rlt_le, k_pos. }
          rewrite /εAmp /=.
          apply Rmult_le_compat_l.
          { apply Rmult_le_pos; [apply Rlt_le, cond_pos | apply pow_le, Rlt_le, k_pos]. }
          apply Rplus_le_compat_l.
          rewrite /Rdiv Rmult_1_l Rmult_1_l.
          apply Rinv_le_contravar.
          -- apply (Rplus_lt_reg_r 1%R).
             rewrite /Rminus Rplus_assoc Rplus_opp_l Rplus_0_l Rplus_0_r.
             apply Rlt_pow_R1.
             --- apply lt_1_INR; destruct kwf; lia.
             --- rewrite /L'. by destruct (HL junk).
          -- apply Rplus_le_compat_r, Rle_pow.
             --- rewrite S_INR. pose P := (pos_INR N); lra.
             --- rewrite /L'. by destruct (HL junk).
                 Unshelve.
                 destruct kwf.
                 destruct (HL junk).
                 rewrite /L'.
                 constructor; try lia.
  Qed.

  Lemma twp_presample_planner_pos N z e E α Φ (ε : nonnegreal) L prefix suffix :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (0 < N)%nat ->
    (forall junk, 0 < (length (suffix (prefix ++ junk))) <= L)%nat ->
    (0 < ε)%R ->
    ↯ ε ∗
      (α ↪ (N; prefix)) ∗
      ((∃ junk, α ↪ (N; prefix ++ junk ++ (suffix (prefix ++ junk)))) -∗ WP e @ E [{ Φ }])
      ⊢ WP e @ E [{ Φ }].
  Proof.
    iIntros (? ? ? ? Hε) "(Hcr & Htape & Hwp)".
    assert (kwf : kwf N L). {
      apply mk_kwf; try lia.
      destruct (H2 []) as [H2' H2''].
      eapply Nat.lt_le_trans; eauto. }
    pose ε' := mkposreal ε.(nonneg) Hε.
    replace ε with (pos_to_nn ε'); last first.
    { rewrite /ε' /pos_to_nn. by apply nnreal_ext. }
    destruct (amplification_depth N L kwf ε') as [d Hdepth].
    iApply twp_seq_amplify; eauto; iFrame.
    iIntros "[%junk [?|(_&Hcr)]]".
    + iApply "Hwp"; iExists _; iFrame.
    + iApply (twp_ec_spend with "Hcr"); auto.
      rewrite /pos_to_nn /εAmp_iter /=.
      replace (nonneg ε) with (pos ε') by auto.
      done.
  Qed.

  Lemma presample_planner_pos N z e E α Φ (ε : nonnegreal) L prefix suffix :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (0 < N)%nat ->
    (forall junk, 0 < (length (suffix (prefix ++ junk))) <= L)%nat ->
    (0 < ε)%R ->
    ↯ ε ∗
      (α ↪ (N; prefix)) ∗
      ((∃ junk, α ↪ (N; prefix ++ junk ++ (suffix (prefix ++ junk)))) -∗ WP e @ E {{ Φ }})
      ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (? ? ? ? Hε) "(Hcr & Htape & Hwp)".
    assert (kwf : kwf N L). {
      apply mk_kwf; try lia.
      destruct (H2 []) as [H2' H2''].
      eapply Nat.lt_le_trans; eauto. }
    pose ε' := mkposreal ε.(nonneg) Hε.
    replace ε with (pos_to_nn ε'); last first.
    { rewrite /ε' /pos_to_nn. by apply nnreal_ext. }
    destruct (amplification_depth N L kwf ε') as [d Hdepth].
    iApply seq_amplify; eauto; iFrame.
    iIntros "[%junk [?|(_&Hcr)]]".
    + iApply "Hwp"; iExists _; iFrame.
    + iApply (wp_ec_spend with "Hcr"); auto.
      rewrite /pos_to_nn /εAmp_iter /=.
      replace (nonneg ε) with (pos ε') by auto.
      done.
  Qed.

  (* general planner rule, with bounded synchronization strings *)
  Lemma twp_presample_planner_sync N z e E α Φ (ε : nonnegreal) L prefix suffix :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (0 < ε)%R ->
    (forall junk, 0 < (length (suffix (prefix ++ junk))) <= L)%nat ->
    ↯ ε ∗
      (α ↪ (S N; prefix)) ∗
      ((∃ junk, α ↪ (S N; prefix ++ junk ++ suffix (prefix ++ junk))) -∗ WP e @ E [{ Φ }])
      ⊢ WP e @ E [{ Φ }].
  Proof.
    iIntros (? ? ? ?).
    destruct (suffix prefix) as [|h R] eqn:Hsp.
    - iIntros "(_ & Htape & Hwp)".
      iApply "Hwp".
      iExists [].
      rewrite app_nil_r app_assoc app_nil_r Hsp app_nil_r.
      iFrame.
    - iApply (twp_presample_planner_pos); eauto; try lia.
      by erewrite Nat2Z.id.
  Qed.

  (* general planner rule, with bounded synchronization strings *)
  Lemma presample_planner_sync N z e E α Φ (ε : nonnegreal) L prefix suffix :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (0 < ε)%R ->
    (forall junk, 0 < (length (suffix (prefix ++ junk))) <= L)%nat ->
    ↯ ε ∗
      (α ↪ (S N; prefix)) ∗
      ((∃ junk, α ↪ (S N; prefix ++ junk ++ suffix (prefix ++ junk))) -∗ WP e @ E {{ Φ }})
      ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (? ? ? ?).
    destruct (suffix prefix) as [|h R] eqn:Hsp.
    - iIntros "(_ & Htape & Hwp)".
      iApply "Hwp".
      iExists [].
      rewrite app_nil_r app_assoc app_nil_r Hsp app_nil_r.
      iFrame.
    - iApply (presample_planner_pos); eauto; try lia.
      by erewrite Nat2Z.id.
  Qed.


  (* classic version *)
  Lemma twp_presample_planner N z e E α Φ (ε : nonnegreal) prefix suffix :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (0 < ε)%R ->
    ↯ ε ∗
      (α ↪ (S N; prefix)) ∗
      ((∃ junk, α ↪ (S N; prefix ++ junk ++ suffix)) -∗ WP e @ E [{ Φ }])
      ⊢ WP e @ E [{ Φ }].
  Proof.
    iIntros (? ? ?) "(Hcr&Htape&Hwp)".
    destruct suffix as [|] eqn:HS.
    - iApply "Hwp".
      iExists [].
      do 2 rewrite app_nil_r; iFrame.
    - iApply (twp_presample_planner_sync _ _ _ _ _ _ _ (length suffix) _ (fun _ => suffix)); eauto.
      + intros; rewrite HS /=. lia.
      + rewrite HS. iFrame.
  Qed.

  Lemma presample_planner N z e E α Φ (ε : nonnegreal) prefix suffix :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (0 < ε)%R ->
    ↯ ε ∗
      (α ↪ (S N; prefix)) ∗
      ((∃ junk, α ↪ (S N; prefix ++ junk ++ suffix)) -∗ WP e @ E {{ Φ }})
      ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (? ? ?) "(Hcr&Htape&Hwp)".
    destruct suffix as [|] eqn:HS.
    - iApply "Hwp".
      iExists [].
      do 2 rewrite app_nil_r; iFrame.
    - iApply (presample_planner_sync _ _ _ _ _ _ _ (length suffix) _ (fun _ => suffix)); eauto.
      + intros; rewrite HS /=. lia.
      + rewrite HS. iFrame.
  Qed.

  (* pads the junk up to a multiple of blocksize *)
  Definition block_pad N blocksize : list (fin (S (S N))) -> list (fin (S (S N))) :=
    fun junk => repeat 0%fin ((blocksize - (length junk mod blocksize)) mod blocksize)%nat.

  Lemma blocks_aligned N blocksize : (0 < blocksize) -> forall junk, (length junk + length (block_pad N blocksize junk)) mod blocksize = 0%nat.
  Proof.
    intros Hblocksize junk.
    rewrite /block_pad.
    rewrite repeat_length.
    rewrite -Nat.Div0.add_mod_idemp_l.
    rewrite -Nat.Div0.add_mod.
    rewrite -Nat.Div0.add_mod_idemp_l.
    rewrite -Nat.le_add_sub; [apply Nat.Div0.mod_same|].
    apply Nat.lt_le_incl.
    apply Nat.mod_bound_pos; [apply Nat.le_0_l | done].
  Qed.

  Lemma block_pad_ub N blocksize : (0 < blocksize) -> forall junk, (length (block_pad N blocksize junk) <= blocksize)%nat.
  Proof.
    intros. rewrite /block_pad repeat_length.
    edestruct Nat.mod_bound_pos; last first.
    - eapply Nat.lt_le_incl, H1.
    - lia.
    - lia.
  Qed.

  (* version where junk is a mipltple of sample length *)
  Lemma twp_presample_planner_aligned N z e E α Φ (ε : nonnegreal) prefix suffix :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (0 < ε)%R ->
    ↯ ε ∗
      (α ↪ (S N; prefix)) ∗
      ((∃ junk, α ↪ (S N; prefix ++ junk ++ (block_pad N (length suffix) (prefix ++ junk)) ++ suffix)) -∗ WP e @ E [{ Φ }])
      ⊢ WP e @ E [{ Φ }].
  Proof.
    iIntros (? ? ?) "(Hcr&Htape&Hwp)".
    destruct suffix as [|] eqn:HS.
    - iApply "Hwp".
      iExists [].
      do 2 rewrite app_nil_r; iFrame.
    - iApply (twp_presample_planner_sync _ _ _ _ _ _ _ (length suffix + length suffix) _ (fun samples => block_pad N (length suffix) samples ++ suffix)); eauto.
      + intros. split.
        * rewrite app_length HS /=. lia.
        * rewrite app_length /=.
          apply Nat.add_le_mono_r, block_pad_ub.
          rewrite HS /=. lia.
      + rewrite HS.
        iFrame.
  Qed.

  Lemma presample_planner_aligned N z e E α Φ (ε : nonnegreal) prefix suffix :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (0 < ε)%R ->
    ↯ ε ∗
      (α ↪ (S N; prefix)) ∗
      ((∃ junk, α ↪ (S N; prefix ++ junk ++ (block_pad N (length suffix) (prefix ++ junk)) ++ suffix)) -∗ WP e @ E {{ Φ }})
      ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (? ? ?) "(Hcr&Htape&Hwp)".
    destruct suffix as [|] eqn:HS.
    - iApply "Hwp".
      iExists [].
      do 2 rewrite app_nil_r; iFrame.
    - iApply (presample_planner_sync _ _ _ _ _ _ _ (length suffix + length suffix) _ (fun samples => block_pad N (length suffix) samples ++ suffix)); eauto.
      + intros. split.
        * rewrite app_length HS /=. lia.
        * rewrite app_length /=.
          apply Nat.add_le_mono_r, block_pad_ub.
          rewrite HS /=. lia.
      + rewrite HS.
        iFrame.
  Qed.


  Lemma presample_amplify_variant_aux N z e E α Φ Ψ (ε : posreal) li (U : list (fin (S N)) -> nat) (L : nat) kwf :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (forall l : list (fin (S N)), U(l) <= L)%R ->
    (forall l : list (fin (S N)), Ψ l <-> U(l) = 0) ->
    (forall l : list (fin (S N)), ¬ Ψ l ->
      exists c : (fin (S N)), (U(l++[c]) < U(l))%R)  ->
    (0 < U li) ->
    (α ↪ (N; li) ∗
       (↯ (pos_to_nn ε))
       ⊢ (∀ (i : nat) (HL : (i <= L)%nat),
           (((∃ lf1, α ↪ (N; lf1) ∗ ↯(εAmp N L ε kwf)) ∨
               (∃ lf2, α ↪ (N; lf2) ∗  ⌜ U(lf2) + i <= L ⌝ ∗ ↯ (εR N L i ε (mk_fRwf N L i kwf HL))))
            -∗ WP e @ E {{ Φ }})
           -∗ WP e @ E {{ Φ }}))%I.
  Proof.
    iIntros (? ? HUL HU0 HUdec HUli) "(Htape & Hcr_initial)".
    iIntros (i HL).
    iInduction i as [|i'] "IH".
        - iIntros "Hwp".
          iApply "Hwp".
          iRight.
          iExists li.
          iFrame.
          iSplit.
          { iPureIntro.
            rewrite Nat.add_0_r.
            by apply INR_le.
          }
          iFrame.
          rewrite /εR /fR /pos_to_nn /=.
          rewrite Rmult_1_r //.
        - iIntros "Hwand".
          assert (HL' : (i' <= L)%nat) by lia.
          iSpecialize ("IH" $! HL' with "Htape Hcr_initial").
          iApply "IH".
          iIntros  "[[%lf1 [Htape Hcr]]|[%lf2 [Htape (%HUi' & Hcr)]]]".
          + iApply "Hwand".
            iLeft; iExists lf1; iFrame.
          + assert (Hi' : (i' < L)%nat) by lia.
            assert (0 = U lf2 \/ 0 < U lf2)%nat as [HUlf2 | HUlf2 ]by lia.
            * iApply "Hwand".
              iRight.
              iExists lf2.
              iFrame.
              iSplit.
              {
                iPureIntro.
                lia.
              }
              iApply ec_weaken; last by iFrame.
              split; [apply cond_nonneg |].
              rewrite /εR.
              apply Rmult_le_compat_l; [left; apply cond_pos |].
              apply fR_mon_dec.

           * assert (¬ Ψ lf2) as HnΨlf2.
             {
               intros HΨlf2.
               specialize (HU0 lf2) as [HU0 ?].
               specialize (HU0 HΨlf2).
               lia.
             }
             destruct (HUdec lf2 HnΨlf2) as [target Htarget].
             pose HMean := (εDistr_mean N L i' ε target (mk_fRwf N L (S i') kwf HL)).
             wp_apply wp_presample_adv_comp; [done | | apply HMean | ].
             {
               intros; apply cond_nonneg.
             }
             replace {| k_wf := kwf; i_ub := HL' |} with
               (fRwf_dec_i N L i' {| k_wf := kwf; i_ub := HL |}); [|apply fRwf_ext].
             iFrame.
             iIntros (s) "(Hcr&Htape)".
             iApply "Hwand".
             rewrite /εDistr.
             case_bool_decide.
             ** iRight. iFrame. simplify_eq.
                iPureIntro.
                apply INR_lt in Htarget.
                lia.
             ** iLeft. iFrame.
  Qed.


  (* do one step in the amplification sequence *)
  Lemma wp_presample_amplify_variant N z e E α Φ Ψ (ε : posreal) li (U : list (fin (S N)) -> nat) L (kwf: kwf N L) :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (forall l : list (fin (S N)), U(l) <= L)%R ->
    (forall l : list (fin (S N)), Ψ l <-> U(l) = 0) ->
    (forall l : list (fin (S N)), ¬ Ψ l ->
      exists c : (fin (S N)), (U(l++[c]) < U(l))%R)  ->
    ↯ (pos_to_nn ε) ∗
      (α ↪ (N; li)) ∗
      (((∃ lf, ⌜ Ψ lf ⌝ ∗ α ↪ (N; lf)) ∨ (∃ junk, α ↪ (N; junk) ∗ ↯(εAmp N L ε kwf))) -∗ WP e @ E {{ Φ }})
      ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (? ? HUL HU0 HUdec) "(Hcr & Htape & Hwp)".
    destruct (U li) as [|u] eqn:Hu.
    - iApply "Hwp".
      iLeft.
      iExists li.
      iFrame.
      iPureIntro.
      destruct (decide (Ψ li)) as [?|HnΨli]; auto.
      specialize (HUdec li HnΨli) as [c Hc].
      apply INR_lt in Hc.
      lia.
    - assert (0 < U li) by lia.
      iApply (presample_amplify_variant_aux with "[Htape Hcr]"); eauto; [iFrame|].
      iIntros  "[[%lf1 [Htape Hcr]]|[%lf2 [Htape (%HUlf2 & Hcr)]]]"; iApply "Hwp".
      + iRight. by iFrame.
      + iLeft. iFrame.
        Unshelve.
        2: exact L.
        2: lia.
        iPureIntro.
        apply HU0.
        lia.
  Qed.

  Lemma presample_variant N z e E α Φ Ψ (ε : nonnegreal) li (U : list (fin (S N)) -> nat) (M : nat) :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (0 < ε)%R ->
    (forall l : list (fin (S N)), U(l) <= M)%R ->
    (forall l : list (fin (S N)), Ψ l <-> U(l) = 0) ->
    (forall l : list (fin (S N)), ¬ Ψ l ->
                             exists c : (fin (S N)), (U(l++[c]) < U(l))%R)  ->
    ↯ (ε) ∗
      (α ↪ (N; li)) ∗
      (∀ lf, ⌜ Ψ lf ⌝ ∗ α ↪ (N; lf) -∗ WP e @ E {{ Φ }})
      ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (? ? Hε HUL HU0 HUdec) "(Hcr & Htape & Hwp)".
    assert (N = 0 \/ 0 < N) as [-> | HN] by lia.
    (* Corner case: N = 0 *)
    {
      assert (exists n, U li <= n) as [n Hn].
      {
        exists M.
        by apply INR_le.
      }
      iInduction (n) as [Hli|?] "IH" forall (li Hn).
      - iApply "Hwp".
        iFrame.
        iPureIntro.
        apply HU0.
        lia.
      - destruct (decide (U li = 0)) as [HUli0 | HUlin0].
        + iApply "Hwp".
          iFrame.
          iPureIntro.
          by apply HU0.
        + assert (¬ Ψ li) as HnΨ.
          {
            intros HΨ.
            apply HUlin0.
            by apply HU0.
          }
          iApply wp_presample; auto; iFrame.
          iIntros (n0) "Hα".
          destruct (HUdec _ HnΨ) as [c Hc].
          assert (n0 = 0%fin) as ->.
          {
            inv_fin n0; auto.
            intros i.
            inv_fin i.
          }
          assert (c = 0%fin) as ->.
          {
            inv_fin c; auto.
            intros i ?.
            inv_fin i.
          }
          iApply ("IH" with "[][$][$]").
          * iPureIntro.
            apply INR_lt in Hc.
            lia.
          * iIntros (lf) "(%Hlf & Hα)".
            iApply "Hwp"; iFrame; done.
    }
    assert (M = 0 \/ 0 < M) as [-> | HL] by lia.
    (* Corner case: M = 0 *)
    {
      iApply "Hwp"; iFrame.
      iPureIntro.
      apply HU0.
      specialize (HUL li).
      apply INR_le in HUL.
      lia.
    }
    pose kwf := mk_kwf _ _ HN HL.
    pose ε' := mkposreal ε.(nonneg) Hε.
    replace ε with (pos_to_nn ε'); last first.
    { rewrite /ε' /pos_to_nn. by apply nnreal_ext. }
    iRevert (li) "Htape Hwp".
    iApply (ec_ind_incr _ ((εAmp N M ε' _)) with "[] Hcr").
    - apply cond_pos.
    - rewrite /εAmp /=.
      rewrite -{1}(Rmult_1_r (nonneg ε)).
      apply Rmult_lt_compat_l; [real_solver|].
      apply lt_1_k.
    - iModIntro.
      iIntros "[Hind Herr]".
      iIntros (li) "Hα Hcont".
      iApply wp_presample_amplify_variant; eauto.
      iFrame.
      iIntros  "[[%lf1 [HΨ Htape]]|[%lf2 [Htape Hcr]]]".
      + iApply "Hcont".
        iFrame.
      + iApply ("Hind" with "[Hcr] [$Htape]").
        * iFrame.
        * iIntros (?) "(?&?)".
          iApply ("Hcont" with "[$]").
     Unshelve. auto.
  Qed.


  Lemma presample_amplify_rsm_aux N z e E α Φ Ψ (ε : posreal) li (Vε : list (fin (S N)) -> R) (U : list (fin (S N)) -> nat) (L : nat) kwf :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (forall l : list (fin (S N)), Ψ l <-> U(l) = 0) ->
    (forall l : list (fin (S N)), 0 <= Vε l)%R ->
    (forall l : list (fin (S N)), (SeriesC (λ (i : fin (S N)), 1/(S N) * Vε(l ++ [i]) ) <= Vε(l))%R ) ->
    (forall l : list (fin (S N)), ¬ Ψ l ->
      exists c : (fin (S N)), (U(l++[c]) < U(l))%R)  ->
    (0 < U li) ->
    (U li <= L) ->
    (α ↪ (N; li) ∗
       (↯ (pos_to_nn ε) ∗ ↯ (Vε li) )
       ⊢ (∀ (i : nat) (HL : (i <= L)%nat),
           (((∃ lf1, α ↪ (N; lf1) ∗ ↯(εAmp N L ε kwf) ∗ ↯ (Vε lf1)) ∨
               (∃ lf2, α ↪ (N; lf2) ∗  ⌜ U(lf2) + i <= L ⌝ ∗ ↯ (εR N L i ε (mk_fRwf N L i kwf HL)) ∗ ↯ (Vε lf2)  ))
            -∗ WP e @ E {{ Φ }})
           -∗ WP e @ E {{ Φ }}))%I.
  Proof.
    iIntros (? ? HU0 HVεpos Hrsm HUdec H0Uli HUliL) "(Htape & Hcr_initial)".
    iIntros (i HL).
    iInduction i as [|i'] "IH".
        - iIntros "Hwp".
          iApply "Hwp".
          iRight.
          iExists li.
          iFrame.
          iSplit.
          { iPureIntro.
            rewrite Nat.add_0_r //.
          }
          rewrite /εR /fR /pos_to_nn /=.
          rewrite Rmult_1_r //.
        - iIntros "Hwand".
          assert (HL' : (i' <= L)%nat) by lia.
          iSpecialize ("IH" $! HL' with "Htape Hcr_initial").
          iApply "IH".
          iIntros  "[[%lf1 [Htape Hcr]]|[%lf2 [Htape (%HUi' & Hcr1 & Hcr2)]]]".
          + iApply "Hwand".
            iLeft; iExists lf1; iFrame.
          + assert (Hi' : (i' < L)%nat) by lia.
            assert (0 = U lf2 \/ 0 < U lf2)%nat as [HUlf2 | HUlf2 ]by lia.
            * iApply "Hwand".
              iRight.
              iExists lf2.
              iFrame.
              iSplit.
              {
                iPureIntro.
                lia.
              }
              iApply ec_weaken; last by iFrame.
              split; [apply cond_nonneg |].
              rewrite /εR.
              apply Rmult_le_compat_l; [left; apply cond_pos |].
              apply fR_mon_dec.

            * assert (¬ Ψ lf2) as HnΨlf2.
              {
                intros HΨlf2.
                specialize (HU0 lf2) as [HU0 ?].
                specialize (HU0 HΨlf2).
                lia.
              }
             destruct (HUdec lf2 HnΨlf2) as [target Htarget].
             pose HMean := (εDistr_mean N L i' ε target (mk_fRwf N L (S i') kwf HL)).
             wp_apply wp_presample_adv_comp_leq_double ; [done | | | right; apply HMean | apply Hrsm | ].
             {
               intros; apply cond_nonneg.
             }
             {
               intros; apply HVεpos.
             }
             replace {| k_wf := kwf; i_ub := HL' |} with
               (fRwf_dec_i N L i' {| k_wf := kwf; i_ub := HL |}); [|apply fRwf_ext].
             iFrame.
             iIntros (s) "(Hcr1 & Hcr2 & Htape)".
             iApply "Hwand".
             rewrite /εDistr.
             case_bool_decide.
             ** iRight. iFrame. simplify_eq.
                iPureIntro.
                apply INR_lt in Htarget.
                lia.
             ** iLeft. iFrame.
  Qed.

  (* do one step in the amplification sequence *)
  Lemma wp_presample_amplify_rsm N z e E α Φ Ψ (ε : posreal) li (Vε : list (fin (S N)) -> R) (U : list (fin (S N)) -> nat) L (kwf: kwf N L) :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (forall l : list (fin (S N)), Ψ l <-> U(l) = 0) ->
    (forall l : list (fin (S N)), 0 <= Vε l)%R ->
    (forall l : list (fin (S N)), (SeriesC (λ (i : fin (S N)), 1/(S N) * Vε(l ++ [i]) ) <= Vε(l))%R ) ->
    (forall l : list (fin (S N)), ¬ Ψ l ->
      exists c : (fin (S N)), (U(l++[c]) < U(l))%R)  ->
    (forall l : list (fin (S N)), (L < U l)%nat -> (1 <= Vε l)%R) ->
      ↯ (pos_to_nn ε) ∗
      ↯ (Vε li) ∗
      (α ↪ (N; li)) ∗
      (((∃ lf, ⌜ Ψ lf ⌝ ∗ α ↪ (N; lf)) ∨
          (∃ junk, α ↪ (N; junk) ∗ ↯(εAmp N L ε kwf) ∗ ↯(Vε junk))) -∗ WP e @ E {{ Φ }})
      ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (? ? HU0 HVεpos Hrsm HUdec HVbd) "(Hcr1 & Hcr2 & Htape & Hwp)".
    destruct (U li) as [|u] eqn:Hu.
    - iApply "Hwp".
      iLeft.
      iExists li.
      iFrame.
      iPureIntro.
      destruct (decide (Ψ li)) as [?|HnΨli]; auto.
      specialize (HUdec li HnΨli) as [c Hc].
      apply INR_lt in Hc.
      lia.
    - assert (0 < U li) by lia.
      assert (U li <= L \/ L < U li) as [HUliL | HLUli ] by lia; last first.
      {
        iPoseProof (ec_contradict with "Hcr2") as "?"; auto.
      }
      iApply (presample_amplify_rsm_aux with "[Htape Hcr1 Hcr2]"); eauto; [iFrame|].
      iIntros  "[[%lf1 (Htape & Hcr1 & Hcr2) ]|[%lf2 [Htape (%HUlf2 & Hcr)]]]"; iApply "Hwp".
      + iRight.
        iExists lf1.
        iFrame.
      + iLeft. iFrame.
        Unshelve.
        2: exact L.
        2: lia.
        iPureIntro.
        assert (U lf2 = 0) by lia.
        destruct (decide (Ψ lf2)) as [? | HnΨlf2]; auto.
        specialize (HUdec lf2 HnΨlf2) as [c Hc].
        apply INR_lt in Hc.
        lia.
  Qed.




  Lemma presample_rsm N z e E α Φ Ψ (ε : nonnegreal) li (V : list (fin (S N)) -> R) (U : list (fin (S N)) -> nat) :
    TCEq N (Z.to_nat z) →
    to_val e = None ->
    (forall l : list (fin (S N)), 0 <= V(l))%R ->
    (forall l : list (fin (S N)), Ψ l <-> V(l) = 0) ->
    (forall l : list (fin (S N)), Ψ l <-> U(l) = 0) ->
    (* U is bounded in downsets of V *)
    (forall r : R, exists n : nat, forall l : list (fin (S N)), V(l) <= r -> U(l) ≤ n)%R ->
    (* U decreases with non-zero probability *)
    (forall l : list (fin (S N)), ¬ Ψ l ->
           exists c : (fin (S N)), (U(l++[c]) < U(l))%R)  ->
    (* V is a supermartingale *)
    (forall l : list (fin (S N)), (SeriesC (λ (i : fin (S N)), 1/(S N) * V(l ++ [i]) ) <= V(l))%R ) ->
    (0 < ε)%R ->
    ↯ (ε) ∗
      (α ↪ (N; li)) ∗
    (∀ lf, ⌜ Ψ lf ⌝ ∗ α ↪ (N; lf) -∗ WP e @ E {{ Φ }})
      ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (? ? HVpos HΨV HΨU HUbd HUdec HVsm Hε) "(Hcr & Hα & Hcont)".
    destruct (decide (V li = 0)) as [HVli0 | HVlin0].
    {
      iApply "Hcont".
      iFrame.
      iPureIntro.
      by apply HΨV.
    }
    assert (0 < V li)%R as HVlipos.
    {
      specialize (HVpos li).
      destruct (Rle_lt_or_eq_dec _ _ HVpos); done.
    }
    assert (N = 0 \/ 0 < N) as [-> | HN] by lia.
    (* Corner case: N = 0 *)
    {
      assert (exists n, U li <= n) as [n Hn].
      {
        exists (U li).
        by lia.
      }
      clear HVlipos.
      clear HVlin0.
      iInduction (n) as [Hli|?] "IH" forall (li Hn).
      - iApply "Hcont".
        iFrame.
        iPureIntro.
        apply HΨU.
        lia.
      - destruct (decide (U li = 0)) as [HUli0 | HUlin0].
        + iApply "Hcont".
          iFrame.
          iPureIntro.
          by apply HΨU.
        + assert (¬ Ψ li) as HnΨ.
          {
            intros HΨ.
            apply HUlin0.
            by apply HΨU.
          }
          iApply wp_presample; auto; iFrame.
          iIntros (n0) "Hα".
          destruct (HUdec _ HnΨ) as [c Hc].
          assert (n0 = 0%fin) as ->.
          {
            inv_fin n0; auto.
            intros i.
            inv_fin i.
          }
          assert (c = 0%fin) as ->.
          {
            inv_fin c; auto.
            intros i ?.
            inv_fin i.
          }
          iApply ("IH" with "[][$][$]").
          * iPureIntro.
            apply INR_lt in Hc.
            lia.
          * iIntros (lf) "(%Hlf & Hα)".
            iApply "Hcont"; iFrame; done.
    }
    set (εhalf := (ε/2)%NNR).
    replace ε with (εhalf + εhalf)%NNR; last first.
    {
      apply nnreal_ext.
      rewrite /εhalf /=.
      lra.
    }
    assert (0 < εhalf)%R as Hεhalf.
    {
      simpl.
      apply Rcomplements.Rdiv_lt_0_compat; auto.
      lra.
    }
    iPoseProof (ec_split with "Hcr") as "[HcrU HcrV]".
    { apply cond_nonneg. }
    { apply cond_nonneg. }

    specialize (HUbd (2/ε * V li)%R) as [L HL].
    assert (0 < S L) as HSL by lia.
    pose kwf := mk_kwf _ _ HN HSL.

    set (Vε := λ (l : list (fin (S N))), ((ε / 2) * (V l / V li))%R).
    iDestruct (ec_eq _ (Vε li) with "HcrV") as "HcrV".
    {
      rewrite /εhalf /Vε /=.
      rewrite /Rdiv Rmult_inv_r //.
      lra.
    }

    pose εhalf' := mkposreal εhalf.(nonneg) Hεhalf.
    replace εhalf with (pos_to_nn εhalf'); last first.
    { rewrite /εhalf' /pos_to_nn. by apply nnreal_ext. }
    set (Hinv_pre :=
           (∃ (Wε : list (fin (S N)) -> R) (lc : list (fin (S N))),
               ⌜ forall l : list (fin (S N)), (0 <= Wε l)%R ⌝ ∗
             ⌜ forall l : list (fin (S N)), (SeriesC (λ (i : fin (S N)), 1/(S N) * Wε(l ++ [i]) ) <= Wε(l))%R ⌝ ∗
            ⌜ forall l : list (fin (S N)), (S L < U l)%nat -> (1 <= Wε l)%R ⌝ ∗
            α ↪ (N; lc) ∗ ↯ (Wε lc)
           )%I : iProp Σ
        ).
    iAssert Hinv_pre with "[Hα HcrV]" as "Hinv".
    {
      rewrite /Hinv_pre.
      iExists Vε, li.
      rewrite /Vε.
      iSplit.
      {
        iPureIntro.
        intros Hlc.
        apply Rmult_le_pos; [real_solver |].
        apply Rcomplements.Rdiv_le_0_compat; eauto.
      }
      iSplit.
      {
        iPureIntro.
        intros Hlc.
        setoid_rewrite <- (Rmult_assoc _ (ε/2)).
        setoid_rewrite (Rmult_comm _ (ε/2)).
        setoid_rewrite (Rmult_assoc (ε/2)).
        rewrite SeriesC_scal_l.
        apply Rmult_le_compat_l; [real_solver |].
        setoid_rewrite <- (Rmult_assoc (1 / (S N))).
        rewrite SeriesC_scal_r.
        apply Rmult_le_compat_r; auto.
        left.
        by apply Rinv_0_lt_compat.
      }
      iSplit.
      {
        iPureIntro.
        intros lc Hlc.
        destruct (Rle_lt_dec 1 (ε / 2 * (V lc / V li))%R) as [Hle | Hnle]; auto.
        assert (U lc <= L); last by lia.
        apply HL.
        apply Rlt_le in Hnle.
        apply Rcomplements.Rle_div_l; [lra|].
        apply (Rcomplements.Rle_div_r _ _ ε); auto.
        lra.
      }
      iFrame.
    }
    clear Vε.
    iRevert "Hcont Hinv".
    iApply (ec_ind_incr _ (εAmp N (S L) εhalf' _) with "[] HcrU").
    - apply cond_pos.
    - rewrite /εAmp /=.
      rewrite -{1}(Rmult_1_r (ε * / (1 + 1))).
      apply Rmult_lt_compat_l; [real_solver|].
      apply lt_1_k.

    - iModIntro.
      iIntros "[Hind Herr] Hcont".
      iIntros "(%W & %lc & %HWpos & %HWsm & %HWbd & Hβ & HεW)".
      iApply (wp_presample_amplify_rsm); eauto.
      iSplitL "Herr"; [iFrame|].
      iFrame.
      iIntros  "[[%lf1 [HΨ Htape]]|[%lf2 [Htape [HcrU HcrW]]]]".
      + iApply "Hcont".
        iFrame.
      + iApply ("Hind" with "[HcrU] [Hcont] [Htape HcrW]").
        * iFrame.
        * iIntros (?) "(?&?)".
          iApply ("Hcont" with "[$]").
        * iExists _,_.
          iSplit; auto.
          iSplit; auto.
          iSplit; auto.
           iFrame.
     Unshelve. auto.
  Qed.



  Lemma twp_rec_total E (ε k : R) e Φ Ψ :
    to_val e = None →
    (0 < ε)%R →
    (1 < k)%R →
    □ (∀ (ε' : R), ⌜(0<ε')%R⌝ -∗ □ (Ψ -∗ ↯ (k * ε')%NNR -∗ WP e @ E [{ Φ }]) -∗
      Ψ -∗ ↯ ε' -∗ WP e @ E [{ Φ }]) -∗
      Ψ -∗ ↯ ε -∗ WP e @ E [{ Φ }].
  Proof.
    iIntros (Hnval Hpos Hgt1) "#Hrec HΨ Herr".
    iRevert "HΨ".
    iApply (ec_ind_amp _ k with "[] Herr");  [done|done|].
    iIntros "!#" (ε') "%Hε' #HWP Herr HΨ".
    iApply ("Hrec" $! ε' with "[//] [HWP] HΨ Herr").
    iModIntro.
    iIntros "HΨ Herr".
    iApply ("HWP" with "Herr HΨ").
  Qed.

End rules.

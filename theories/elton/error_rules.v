(** * Coneris error bound rules rules  *)
From stdpp Require Import namespaces finite fin_sets.
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext.
From clutch.delay_prob_lang Require Import notation tactics metatheory.
From clutch.delay_prob_lang Require Export lang.
From clutch.elton Require Export lifting proofmode ectx_lifting primitive_laws. 

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
  case_match; last first.
  { exfalso.
    rename select (¬ _) into Hcontra.
    apply Hcontra.
    eexists _.
    by apply urn_subst_equal_obv.
  }
  erewrite urn_subst_equal_epsilon_unique; last done.
  rewrite /dmap -Hz.
  rewrite -(Rplus_0_r 0).
  eapply (pgl_dbind _ _ _ _ _ 0);
    [done|done| |by apply pgl_trivial].
  intros n ?.
  apply pgl_dret.
  by exists n.
Qed.

(* (** * rand(N) error *) *)
(* Lemma pgl_rand_err N z σ1 (m : fin (S N)): *)
(*   N = Z.to_nat z → *)
(*   pgl *)
(*     (prim_step (rand #z) σ1) *)
(*     (λ ρ2, ∃ (n : fin (S N)), *)
(*         (n ≠ m)%fin /\ ρ2 = (Val #n, σ1, [])) (1/(N+1)). *)
(* Proof. *)
(*   simpl in *. *)
(*   intros Hz. *)
(*   rewrite head_prim_step_eq /=. *)
(*   rewrite /dmap -Hz. *)
(*   rewrite -(Rplus_0_r (1 / (N + 1))). *)
(*   eapply (pgl_dbind _ _ _ _ _ 0); last first. *)
(*   { by apply ub_unif_err. } *)
(*   - intros n ?. *)
(*     apply pgl_dret. *)
(*     exists n; split; [apply H | auto]. *)
(*   - lra. *)
(*   - rewrite /Rdiv. *)
(*     apply Rle_mult_inv_pos; [lra |]. *)
(*     apply (Rle_lt_trans _ N). *)
(*     + apply pos_INR. *)
(*     + rewrite <- (Rplus_0_r) at 1. *)
(*       apply Rplus_lt_compat_l. *)
(*       lra. *)
(* Qed. *)

(* (* Same lemma holds for m an arbitrary natural *) *)
(* Lemma pgl_rand_err_nat N z σ1 (m : nat): *)
(*   N = Z.to_nat z → *)
(*   pgl *)
(*     (prim_step (rand #z) σ1) *)
(*     (λ ρ2, ∃ (n : fin (S N)), *)
(*         (fin_to_nat n ≠ m)%fin /\ ρ2 = (Val #n, σ1, [])) (1/(N+1)). *)
(* Proof. *)
(*   simpl in *. *)
(*   intros Hz. *)
(*   rewrite head_prim_step_eq /=. *)
(*   rewrite /dmap -Hz. *)
(*   rewrite -(Rplus_0_r (1 / (N + 1))). *)
(*   eapply (pgl_dbind _ _ _ _ _ 0); last first. *)
(*   { by apply ub_unif_err_nat. } *)
(*   - intros n ?. *)
(*     apply pgl_dret. *)
(*     exists n; split; [apply H | auto]. *)
(*   - lra. *)
(*   - rewrite /Rdiv. *)
(*     apply Rle_mult_inv_pos; [lra |]. *)
(*     apply (Rle_lt_trans _ N). *)
(*     + apply pos_INR. *)
(*     + rewrite <- (Rplus_0_r) at 1. *)
(*       apply Rplus_lt_compat_l. *)
(*       lra. *)
(* Qed. *)

(* (* Generalization to lists *) *)
(* Lemma pgl_rand_err_list_nat N z σ1 (ms : list nat): *)
(*   N = Z.to_nat z → *)
(*   pgl *)
(*     (prim_step (rand #z) σ1) *)
(*     (λ ρ2, ∃ (n : fin (S N)), *)
(*         Forall (λ m, (fin_to_nat n ≠ m)%fin) ms /\ ρ2 = (Val #n, σ1, [])) ((length ms)/(N+1)). *)
(* Proof. *)
(*   simpl in *. *)
(*   intros Hz. *)
(*   rewrite head_prim_step_eq /=. *)
(*   rewrite /dmap -Hz. *)
(*   rewrite -(Rplus_0_r ((length ms) / (N + 1))). *)
(*   eapply (pgl_dbind _ _ _ _ _ 0); last first. *)
(*   { by apply ub_unif_err_list_nat. } *)
(*   - intros n ?. *)
(*     apply pgl_dret. *)
(*     exists n; split; [apply H | auto]. *)
(*   - lra. *)
(*   - rewrite /Rdiv. *)
(*     apply Rle_mult_inv_pos; [apply pos_INR | ]. *)
(*     apply (Rle_lt_trans _ N). *)
(*     + apply pos_INR. *)
(*     + rewrite <- (Rplus_0_r) at 1. *)
(*       apply Rplus_lt_compat_l. *)
(*       lra. *)
(* Qed. *)

(* Lemma pgl_rand_err_list_int N z σ1 (ms : list Z): *)
(*   N = Z.to_nat z → *)
(*   pgl *)
(*     (prim_step (rand #z) σ1) *)
(*     (λ ρ2, ∃ (n : fin (S N)), *)
(*         Forall (λ m, (Z.of_nat (fin_to_nat n) ≠ m)%fin) ms /\ ρ2 = (Val #n, σ1, [])) ((length ms)/(N+1)). *)
(* Proof. *)
(*   simpl in *. *)
(*   intros Hz. *)
(*   rewrite head_prim_step_eq /=. *)
(*   rewrite /dmap -Hz. *)
(*   rewrite -(Rplus_0_r ((length ms) / (N + 1))). *)
(*   eapply (pgl_dbind _ _ _ _ _ 0); last first. *)
(*   { by apply ub_unif_err_list_int. } *)
(*   - intros n ?. *)
(*     apply pgl_dret. *)
(*     exists n; split; [apply H | auto]. *)
(*   - lra. *)
(*   - rewrite /Rdiv. *)
(*     apply Rle_mult_inv_pos; [apply pos_INR | ]. *)
(*     apply (Rle_lt_trans _ N). *)
(*     + apply pos_INR. *)
(*     + rewrite <- (Rplus_0_r) at 1. *)
(*       apply Rplus_lt_compat_l. *)
(*       lra. *)
(* Qed. *)

End metatheory.

Section rules.
  Context `{!eltonGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types v : val.
  Implicit Types l : loc.

(* Lemma wp_rand_err (N : nat) (z : Z) (m : fin (S N)) E Φ s : *)
(*   TCEq N (Z.to_nat z) → *)
(*   ↯ (/ (N + 1)) ∗ (∀ x, ⌜x ≠ m⌝ -∗ Φ #x) *)
(*   ⊢ WP rand #z @ s; E {{ Φ }}. *)
(* Proof. *)
(*   iIntros (->) "[Herr Hwp]". *)
(*   iApply wp_lift_step_fupd_glm. *)
(*   iIntros (σ1 ε) "[Hσ Hε]". *)
(*   iApply fupd_mask_intro; [set_solver|]. *)
(*   iIntros "Hclose'". *)
(*   iDestruct (ec_supply_ec_inv with "Hε Herr") as %(?&?& -> & He). *)
(*   iApply state_step_coupl_ret. *)
(*   iApply prog_coupl_prim_step; first (iModIntro; iIntros; by iApply state_step_coupl_ret_err_ge_1). *)
(*   iExists *)
(*       (λ ρ , *)
(*         ∃ (n : fin (S (Z.to_nat z))), n ≠ m /\ ρ = (Val #n, σ1, [])), _, _. *)
(*   iSplit. *)
(*   { iPureIntro. eapply head_prim_reducible; eauto with head_step. } *)
(*   iSplit. *)
(*   { *)
(*     iPureIntro. *)
(*     apply Rle_refl. *)
(*   } *)
(*   iSplit. *)
(*   { *)
(*     iPureIntro. *)
(*     eapply pgl_mon_pred; last first. *)
(*     - rewrite He. *)
(*       assert (/ (Z.to_nat z + 1) = Rdiv 1 (Z.to_nat z + 1)) as ->. *)
(*       { simpl. *)
(*         rewrite /Rdiv/= Rmult_1_l //. *)
(*        } *)
(*       apply (pgl_rand_err (Z.to_nat z) z σ1); auto. *)
(*     - intros [] (n & Hn1 & [=]). simplify_eq. *)
(*       eauto. *)
(*   } *)
(*   iIntros (e2 σ2 efs) "%H". *)
(*   destruct H as (n & Hn1 & [=]); simplify_eq. *)
(*   iMod (ec_supply_decrease with "Hε Herr") as (????) "Hdec". *)
(*   do 2 iModIntro. *)
(*   iApply state_step_coupl_ret. *)
(*   iMod "Hclose'". *)
(*   iFrame. *)
(*   iModIntro. *)
(*   rewrite -pgl_wp_value. *)
(*   iDestruct ("Hwp" with "[//]") as "$". iSplitL; last done. *)
(*   iApply ec_supply_eq; [|done]. *)
(*   simplify_eq. *)
(*   lra. *)
(* Qed. *)

(* Lemma wp_rand_err_nat (N : nat) (z : Z) (m : nat) E Φ s : *)
(*   TCEq N (Z.to_nat z) → *)
(*   ↯ (/ (N+1)) ∗ *)
(*   (∀ x : fin (S N), ⌜(fin_to_nat x) ≠ m⌝ -∗ Φ #x) *)
(*   ⊢ WP rand #z @ s; E {{ Φ }}. *)
(* Proof. *)
(*   iIntros (->) "[Herr Hwp]". *)
(*   iApply wp_lift_step_fupd_glm. *)
(*   iIntros (σ1 ε) "[Hσ Hε]". *)
(*   iApply fupd_mask_intro; [set_solver|]. *)
(*   iIntros "Hclose'". *)
(*   iDestruct (ec_supply_ec_inv with "Hε Herr ") as %(?&?&->&He). *)
(*   iApply state_step_coupl_ret. *)
(*   iApply prog_coupl_prim_step; first (iModIntro; iIntros; by iApply state_step_coupl_ret_err_ge_1). *)
(*   iExists *)
(*       (λ ρ , *)
(*         ∃ (n : fin (S (Z.to_nat z))), fin_to_nat n ≠ m /\ ρ = (Val #n, σ1, [])),_,_. *)
(*   iSplit. *)
(*   { iPureIntro. eapply head_prim_reducible; eauto with head_step. } *)
(*   iSplit. *)
(*   { iPureIntro; apply Rle_refl. } *)
(*   iSplit. *)
(*   { *)
(*     iPureIntro. *)
(*     eapply pgl_mon_pred; last first. *)
(*     - rewrite He. *)
(*       assert (/ (Z.to_nat z + 1) = Rdiv 1 (Z.to_nat z + 1)) as ->. *)
(*       { simpl. *)
(*         rewrite /Rdiv/= Rmult_1_l //. } *)
(*       apply (pgl_rand_err_nat (Z.to_nat z) z σ1); auto. *)
(*     - intros [] (n & Hn1 & [=]). simplify_eq. *)
(*       eauto. *)
(*   } *)
(*   iIntros (e2 σ2 efs) "%H". *)
(*   destruct H as (n & Hn1 & [=]); simplify_eq. *)
(*   iMod (ec_supply_decrease with "Hε Herr") as (????) "Hdec". *)
(*   do 2 iModIntro. *)
(*   iApply state_step_coupl_ret. *)
(*   iMod "Hclose'". *)
(*   iFrame. *)
(*   iModIntro. *)
(*   rewrite -pgl_wp_value. *)
(*   iDestruct ("Hwp" with "[//]") as "$"; iSplitL; last done. *)
(*   iApply ec_supply_eq; [|done]. *)
(*   simplify_eq. *)
(*   lra. *)
(* Qed. *)

(* Lemma wp_rand_err_list_nat (N : nat) (z : Z) (ns : list nat) E Φ : *)
(*   TCEq N (Z.to_nat z) → *)
(*   ↯ (length ns / (N+1)) ∗ *)
(*   (∀ x : fin (S N), ⌜Forall (λ m, fin_to_nat x ≠ m) ns⌝ -∗ Φ #x) *)
(*   ⊢ WP rand #z @ E {{ Φ }}. *)
(* Proof. *)
(*   iIntros (->) "[Herr Hwp]". *)
(*   iApply wp_lift_step_fupd_glm. *)
(*   iIntros (σ1 ε) "[Hσ Hε]". *)
(*   iApply fupd_mask_intro; [set_solver|]. *)
(*   iIntros "Hclose'". *)
(*   iDestruct (ec_supply_ec_inv with "Hε Herr") as %(?&?&->&He). *)
(*   iApply state_step_coupl_ret. *)
(*   iApply prog_coupl_prim_step; first (iModIntro; iIntros; by iApply state_step_coupl_ret_err_ge_1). *)
(*   iExists *)
(*     (λ ρ , *)
(*       ∃ (n : fin (S (Z.to_nat z))), Forall (λ m, fin_to_nat n ≠ m) ns /\ ρ = (Val #n, σ1, [])),_,_. *)
(*   iSplit. *)
(*   { iPureIntro. eapply head_prim_reducible; eauto with head_step. } *)
(*   iSplit. *)
(*   { iPureIntro; apply Rle_refl. } *)
(*   iSplit. *)
(*   { *)
(*     iPureIntro. *)
(*     eapply pgl_mon_pred; last first. *)
(*     - rewrite He. *)
(*       apply (pgl_rand_err_list_nat (Z.to_nat z) z σ1); auto. *)
(*     - intros [] (n & Hn1 & [=]). simplify_eq. *)
(*       eauto. *)
(*   } *)
(*   iIntros (e2 σ2 efs) "%H". *)
(*   destruct H as (n & Hn1 & [=]); simplify_eq. *)
(*   iMod (ec_supply_decrease with "Hε Herr") as (????) "Hdec". *)
(*   do 2 iModIntro. *)
(*   iApply state_step_coupl_ret. *)
(*   iMod "Hclose'". *)
(*   iFrame. *)
(*   iModIntro. *)
(*   rewrite -pgl_wp_value. *)
(*   iDestruct ("Hwp" with "[//]") as "$". *)
(*   iSplitL; last done. *)
(*   iApply ec_supply_eq; [|done]. *)
(*   simplify_eq. *)
(*   lra. *)
(* Qed. *)

(* Lemma wp_rand_err_list_int (N : nat) (z : Z) (zs : list Z) E Φ : *)
(*   TCEq N (Z.to_nat z) → *)
(*   ↯ (length zs / (N+1)) ∗ *)
(*   (∀ x : fin (S N), ⌜Forall (λ m, (Z.of_nat $ fin_to_nat x) ≠ m) zs⌝ -∗ Φ #x) *)
(*   ⊢ WP rand #z @ E {{ Φ }}. *)
(* Proof. *)
(*   iIntros (->) "[Herr Hwp]". *)
(*   iApply wp_lift_step_fupd_glm. *)
(*   iIntros (σ1 ε) "[Hσ Hε]". *)
(*   iApply fupd_mask_intro; [set_solver|]. *)
(*   iIntros "Hclose'". *)
(*   iDestruct (ec_supply_ec_inv with "Hε Herr ") as %(?&?&->&He). *)
(*   iApply state_step_coupl_ret. *)
(*   iApply prog_coupl_prim_step; first (iModIntro; iIntros; by iApply state_step_coupl_ret_err_ge_1). *)
(*   iExists *)
(*     (λ ρ, *)
(*       ∃ (n : fin (S (Z.to_nat z))), Forall (λ m, Z.of_nat (fin_to_nat n) ≠ m) zs /\ ρ = (Val #n, σ1, [])),_,_. *)
(*   iSplit. *)
(*   { iPureIntro. eapply head_prim_reducible; eauto with head_step. } *)
(*   iSplit. *)
(*   { iPureIntro; apply Rle_refl. } *)
(*   iSplit. *)
(*   { *)
(*     iPureIntro. *)
(*     eapply pgl_mon_pred; last first. *)
(*     - rewrite He. apply (pgl_rand_err_list_int (Z.to_nat z) z σ1); auto. *)
(*     - intros [] (n & Hn1 & [=]). simplify_eq. eauto. *)
(*   } *)
(*   iIntros (e2 σ2 efs) "%H". *)
(*   destruct H as (n & Hn1 & [=]); simplify_eq. *)
(*   iMod (ec_supply_decrease with "Hε Herr") as (????) "Hdec". *)
(*   do 2 iModIntro. *)
(*   iApply state_step_coupl_ret. *)
(*   iMod "Hclose'". *)
(*   iFrame. *)
(*   iModIntro. *)
(*   rewrite -pgl_wp_value. *)
(*   iDestruct ("Hwp" with "[//]") as "$". *)
(*   iSplitL; last done. *)
(*   iApply ec_supply_eq; [|done]. *)
(*   simplify_eq. *)
(*   lra. *)
(* Qed. *)

(* Lemma wp_rand_err_filter (N : nat) (z : Z) (P : nat -> bool) E Φ : *)
(*   TCEq N (Z.to_nat z) → *)
(*   ↯ (length (List.filter P (seq 0 (S N))) / (N + 1)) ∗ *)
(*     (∀ x : fin (S N), ⌜ P x = false ⌝ -∗ Φ #x) *)
(*     ⊢ WP rand #z @ E {{ Φ }}. *)
(* Proof. *)
(*   iIntros (?) "[H1 H2]". *)
(*   iApply (wp_rand_err_list_nat _ _ (List.filter P (seq 0 (S N)))). *)
(*   iFrame. *)
(*   iIntros (x) "%H0". *)
(*   iApply "H2". *)
(*   iPureIntro. *)
(*   edestruct (List.Forall_forall) as (H1 & H2). *)
(*   specialize (H1 H0). *)
(*   destruct (P x) eqn:HPx ; auto. *)
(*   exfalso. *)
(*   apply (H1 x); auto. *)
(*   apply filter_In; split; auto. *)
(*   apply in_seq. *)
(*   simpl. *)
(*   split; auto with arith. *)
(*   apply fin_to_nat_lt. *)
(* Qed. *)


(* (* (* FIXME: where should this go (if anywhere?) *) *) *)
(* Lemma match_nonneg_coercions (n : nonnegreal) : NNRbar_to_real (NNRbar.Finite n) = nonneg n. *)
(* Proof. by simpl. Qed. *)

(* Lemma mean_constraint_ub (N : nat) (ε1:R) (ε2 : fin (S N) → R) : *)
(*   (0<=ε1)%R -> *)
(*   (forall n, (0<=ε2 n)%R) -> *)
(*   SeriesC (λ n, (1 / (S N)) * ε2 n)%R = (ε1) → *)
(*   (∃ r, (0 <= r)%R ∧ ∀ n,(ε2 n <= r)%R). *)
(* Proof. *)
(*   intros Hineq1 Hineq2 Hsum. *)
(*   exists (INR (S N) * ε1)%R. *)
(*   split. { apply Rmult_le_pos; try lra. apply pos_INR. } *)
(*   intros n. *)
(*   rewrite -Hsum. *)
(*   rewrite SeriesC_scal_l -Rmult_assoc -(Rmult_1_l ((ε2 _))). *)
(*   apply Rmult_le_compat; try lra. *)
(*   - naive_solver. *)
(*   - rewrite /Rdiv Rmult_1_l. *)
(*     rewrite Rinv_r; try lra. *)
(*     pose proof pos_INR_S N. lra. *)
(*   - rewrite -(SeriesC_singleton_dependent _ ε2). *)
(*     apply SeriesC_le. *)
(*     + intros n'. *)
(*       subst. *)
(*       case_bool_decide; try lra; naive_solver. *)
(*     + apply ex_seriesC_finite. *)
(* Qed. *)


(* (* TODO: Move somwhere else to avoid duplications *) *)

(* #[local] Fixpoint Rmax_seq (f : nat -> R) n := *)
(*   match n with *)
(*   | 0 => f 0%nat *)
(*   | S m => Rmax (f (S m)) (Rmax_seq f m) *)
(*   end. *)

(* #[local] Lemma le_Rmax_seq (f : nat -> R) n m : *)
(*   (m ≤ n) -> *)
(*   (f m <= Rmax_seq f n)%R. *)
(* Proof. *)
(*   intros Hleq. *)
(*   induction Hleq. *)
(*   - destruct m; simpl; [lra|]. *)
(*     apply Rmax_l. *)
(*   - simpl. *)
(*     etrans; eauto. *)
(*     apply Rmax_r. *)
(* Qed. *)

(* #[local] Lemma fin_function_bounded (N : nat) (f : fin N -> R) : *)
(*   exists r, forall n, (f n <= r)%R. *)
(* Proof. *)
(*   induction N as [|M]. *)
(*   - exists 0. *)
(*     intros. *)
(*     by apply Fin.case0. *)
(*   - set (g := (λ (n : nat), f (fin.fin_force _ n))). *)
(*     exists (Rmax_seq g M). *)
(*     intros n. *)
(*     pose proof (fin_to_nat_lt n). *)
(*     transitivity (g n). *)
(*     + rewrite /g /=. *)
(*       right. *)
(*       f_equal. *)
(*       apply fin_to_nat_inj. *)
(*       rewrite fin.fin_force_to_nat_le; lia. *)
(*     + apply le_Rmax_seq; lia. *)
(* Qed. *)

  Local Opaque INR.
Lemma wp_couple_rand_adv_comp (N : nat) z E (ε1 : R) (ε2 : fin (S N) -> R) :
  TCEq N (Z.to_nat z) →
  (∀ n, (0 <= ε2 n)%R) ->
  (SeriesC (λ n, (1 / (S N)) * ε2 n)%R = ε1)%R →
  {{{ ↯ ε1 }}} rand #z @ E {{{ n, RET #n; ↯ (ε2 n) }}}.
Proof.
  iIntros (-> Hε2leq Hε1 Ψ) "Herr HΨ".
  destruct (fin_function_bounded _ ε2) as [r Hε2].
  iApply wp_lift_step_fupd_glm.
  iIntros (σ1 ε_now) "[Hσ Hε]".
  iApply fupd_mask_intro; [set_solver|].
  iIntros "Hclose'".
  iApply state_step_coupl_ret.
  iApply prog_coupl_adv_comp; simpl; first (iModIntro; iIntros; by iApply state_step_coupl_ret_err_ge_1).
  (* iDestruct (ec_supply_bound with "Hε Herr") as %?. *)
  iDestruct (ec_supply_ec_inv with "Hε Herr") as %(ε1' & ε3 & Hε_now & Hε1').
  unshelve eset (foo := (λ (ρ : expr * state),
                ε3 +
                  match ρ with
                  | (Val (LitV (LitInt n)), σ) =>
                      if bool_decide(σ = σ1)
                      then if bool_decide (0 ≤ n)%Z
                           then match (lt_dec (Z.to_nat n) (S (Z.to_nat z))) with
                                | left H => mknonnegreal (ε2 (@Fin.of_nat_lt (Z.to_nat n) (S (Z.to_nat z)) H)) _
                                | _ => nnreal_zero
                                end
                           else nnreal_zero
                      else nnreal_zero
                  | _ => nnreal_zero
                  end)%NNR); first naive_solver.
  iExists
    (λ ρ,
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
    do 6 (case_match; auto);
    apply Hε2.
  }
  iSplit.
  {
    iPureIntro.
    rewrite /Expval.
    rewrite /foo Rplus_0_l.
    setoid_rewrite Rmult_plus_distr_l.
    rewrite SeriesC_plus.
    - rewrite Rplus_comm.
      subst.
      apply Rplus_le_compat.
      + erewrite Hε1'.
        etrans; last first.
        * apply (SeriesC_le_inj _
                   (λ ρ : expr * state,
                       let '(e, σ) := ρ in
                       if bool_decide (σ = σ1) then
                         match (e) with
                         | (Val #(LitInt n)) =>
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
             apply Rmult_le_pos; [ | done ].
             apply Rmult_le_pos; [lra |].
             left. apply RinvN_pos'.
          ** intros ρ1 ρ2 m Hc1 Hc2.
             do 14 ((case_bool_decide || case_match); simplify_eq).
             f_equal.
             do 4 f_equal.
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
                      apply Rmult_le_compat_r; [ done |].
                      rewrite head_prim_step_eq /=.
                      case_match; last first.
                      { exfalso. rename select (¬ _) into Hcontra.
                        apply Hcontra.
                        eexists _.
                        by apply urn_subst_equal_obv.
                      }
                      rewrite /dmap /pmf/=/dbind_pmf/dunifP.
                      setoid_rewrite dunif_pmf.
                      rewrite SeriesC_scal_l /= /Rdiv Rmult_1_l.
                      rewrite <- Rmult_1_r.
                      erewrite urn_subst_equal_epsilon_unique; last done.
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
                      apply Rmult_le_compat_r; [apply cond_nonneg | ].
                      right.
                      rewrite head_prim_step_eq /=.
                      case_match; last done.
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
                 case_match; try (by inversion 1).
                 case_bool_decide; try (by inversion 1).
                 case_match; try (by inversion 1).
                 intros. subst. eapply list_elem_of_fmap_2'; last first.
                 { repeat f_equal. instantiate (1 := Z.to_nat n). lia. }
                 rewrite elem_of_seq. lia.
             --- intros H1. apply list_elem_of_fmap_1 in H1.
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
      + do 6 (case_match; try (simpl; rewrite INR_0; lra)).
        exfalso. apply H. subst.
        eapply list_elem_of_fmap_2'; last first.
        { apply bool_decide_eq_true_1 in H3, H4. repeat f_equal.
          - instantiate (1 := Z.to_nat n). lia.
          - done.
        }
        rewrite elem_of_seq. lia. 
      + instantiate (1 :=
                       (λ '(e, s), (prim_step (rand #z) σ1 (e, s) *
                                      match (e) with
                                      | (Val #(LitInt n)) =>
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
    iApply state_step_coupl_ret_err_ge_1.
    simpl.
    lra.
  }
  iApply state_step_coupl_ret.
  iModIntro.
  unshelve iMod (ec_supply_increase ε3 (mknonnegreal (ε2 (nat_to_fin l)) _) with "[Hε2]") as "[Hε2 Hcr]"; first done.
  { simpl. lra. }
  { iApply ec_supply_eq; [|done]. simplify_eq. lra. }
  iMod "Hclose'".
  iApply fupd_mask_intro; [eauto|]; iIntros "_".
  simpl. iFrame.
  iApply pgl_wp_value.
  iApply "HΨ".
  assert (nat_to_fin l = n) as ->; [|done].
  apply fin_to_nat_inj.
  rewrite fin_to_nat_to_fin.
  rewrite Nat2Z.id.
  reflexivity.
Qed.

Lemma wp_couple_rand_adv_comp' (N : nat) z E (ε1 : R) (ε2 : fin (S N) -> R) :
  TCEq N (Z.to_nat z) →
  (∀ n, (0<=ε2 n)%R) ->
  (SeriesC (λ n, (1 / (S N)) * ε2 n)%R <= ε1)%R →
  {{{ ↯ ε1 }}} rand #z @ E {{{ n, RET #n; ↯ (ε2 n) }}}.
Proof.
  iIntros (H1 Hineq H2).
  epose (difference :=  ((ε1)-SeriesC (λ n, (1 / (S N)) * (ε2 n)))%R ). 
  epose (ε2' n:= (ε2 n + difference)%R).
  iIntros (Φ) "Herr HΦ". 
  wp_apply (wp_couple_rand_adv_comp _ _ _ ε1 ε2' with "[$]").
  - rewrite /ε2'/difference. intros. apply Rplus_le_le_0_compat; first done.
    lra.
  - rewrite /ε2'. rewrite /difference; simpl. rewrite -/(INR (S N)).
    setoid_rewrite Rmult_plus_distr_l.
    rewrite SeriesC_plus; [|apply ex_seriesC_finite..].
    setoid_rewrite Rmult_plus_distr_l.
    rewrite SeriesC_plus; [|apply ex_seriesC_finite..].
    rewrite SeriesC_finite_mass fin_card. 
    replace (INR (S N) * (1 / INR (S N) * ε1))%R with (ε1); last first.
    { rewrite -Rmult_assoc Rdiv_1_l Rinv_r; first lra. pose proof pos_INR_S N. lra.  }
    assert ((SeriesC (λ x : fin (S N), 1 / S N * (ε2 x))
             + SeriesC (λ _ : fin (S N), 1 / S N * - SeriesC (λ n : fin (S N), 1 / S N * (ε2 n))))%R = 0)%R; last lra.
    rewrite SeriesC_finite_mass fin_card.
    rewrite -Rmult_assoc Rdiv_1_l Rinv_r; first lra. pose proof pos_INR_S N. lra.
  - iIntros. iApply "HΦ". iApply ec_weaken; last done.
    simpl; split; first done.
    rewrite -/(INR (S N)).
    apply Rplus_le_0_compat. rewrite /difference; lra. 
Qed.

(* Lemma wp_rand_err_list_adv (N : nat) (z : Z) (ns : list nat) (ε0 : R) (ε1 : R) E Φ : *)
(*   TCEq N (Z.to_nat z) → *)
(*   (0<=ε1)%R -> *)
(*   (ε1 * (length ns) <= ε0 * (N + 1))%R -> *)
(*   ↯ ε0 ∗ *)
(*     (∀ x : fin (S N), *)
(*         (⌜Forall (λ m, (fin_to_nat x) ≠ m) ns⌝ ∨ ↯ ε1) -∗ Φ #x) *)
(*     ⊢ WP rand #z @ E {{ Φ }}. *)
(* Proof. *)
(*   iIntros (HN Hineq Hleq) "[Herr Hwp]". *)
(*   set (ε2 := (λ x : fin (S N), if bool_decide (Exists (λ m : nat, (fin_to_nat x) =  m) ns) then ε1 else 0)). *)
(*   wp_apply (wp_couple_rand_adv_comp1 _ _ _  (SeriesC (λ n : fin (S N), (1 / (N + 1) * ε2 n)%R)) ε2 with "[Herr]"). *)
(*   { intros. rewrite /ε2. by case_bool_decide. } *)
(*   { rewrite S_INR. done. } *)
(*   - iApply ec_weaken; auto. *)
(*     simpl. *)
(*     rewrite SeriesC_scal_l /ε2. *)
(*     rewrite (SeriesC_ext _ (λ x : fin (S N), *)
(*                    ε1 * (if bool_decide (Exists (λ m : nat, fin_to_nat x = m) ns) then 1 else 0))%R); last first. *)
(*     { *)
(*       intro n. *)
(*       case_bool_decide; simpl; lra. *)
(*     } *)
(*     rewrite SeriesC_scal_l. *)
(*     rewrite /Rdiv Rmult_1_l. *)
(*     rewrite Rmult_comm. *)
(*     rewrite -Rdiv_def. *)
(*     pose proof (pos_INR N). *)
(*     split. *)
(*     { apply Rmult_le_pos; [|real_solver]. *)
(*       apply Rmult_le_pos; [lra|]. *)
(*       apply SeriesC_ge_0; [|apply ex_seriesC_finite]. *)
(*       intros ?. case_bool_decide; lra. } *)

(*     apply Rcomplements.Rle_div_l; [lra |]. *)
(*     assert (SeriesC (λ x : fin (S N), if bool_decide (Exists (λ m : nat, fin_to_nat x = m) ns) then 1 else 0) <= length ns)%R as Haux. *)
(*     { *)
(*       induction ns as [|?]. *)
(*       - erewrite SeriesC_ext; last first. *)
(*         + intros. *)
(*           erewrite bool_decide_ext; [ | apply Exists_nil ]. *)
(*           done. *)
(*         + simpl. *)
(*           setoid_rewrite bool_decide_False. *)
(*           rewrite SeriesC_0 ; auto. *)
(*           lra. *)
(*       - erewrite SeriesC_ext; last first. *)
(*         + intros. *)
(*           erewrite bool_decide_ext; [ | apply Exists_cons ]. *)
(*           done. *)
(*         + etrans. *)
(*           * right. symmetry. *)
(*             eapply is_seriesC_filter_union. *)
(*             2: { apply SeriesC_correct, ex_seriesC_finite. } *)
(*             intro; simpl; lra. *)
(*           * rewrite length_cons S_INR /=. *)
(*             assert (SeriesC (λ n : fin (S N), if bool_decide (fin_to_nat n = a) then 1 else 0) <= 1)%R as Haux2. *)
(*             { *)
(*               destruct (decide (a < S N)). *)
(*               - rewrite SeriesC_singleton_inj; [lra |]. *)
(*                 exists (nat_to_fin l). *)
(*                 rewrite fin_to_nat_to_fin //. *)
(*               - transitivity 0%R; [ | lra]. *)
(*                 right. *)
(*                 apply SeriesC_0. *)
(*                 intro. *)
(*                 case_bool_decide; auto. *)
(*                 simplify_eq. *)
(*                 exfalso. apply n. *)
(*                 apply fin_to_nat_lt. *)
(*             } *)
(*             rewrite (Rplus_comm _ 1). *)
(*             rewrite -Rplus_minus_assoc. *)
(*             apply Rplus_le_compat; [apply Haux2 |]. *)
(*             etrans; last first. *)
(*             ** apply IHns. *)
(*                etrans; eauto. *)
(*                apply Rmult_le_compat_l; [lra |]. *)
(*                rewrite length_cons S_INR; lra. *)
(*             ** *)
(*               apply Rcomplements.Rle_minus_l. *)
(*               rewrite <- (Rplus_0_r) at 1. *)
(*               apply Rplus_le_compat; [ apply Rle_refl |]. *)
(*               apply SeriesC_ge_0; [ | apply ex_seriesC_finite ]. *)
(*               intros; real_solver. *)
(*     } *)
(*     etrans; eauto. *)
(*     apply Rmult_le_compat_l; auto. *)
(*   - iIntros (n) "Herrn". *)
(*     rewrite /ε2. *)
(*     case_bool_decide. *)
(*     + iApply "Hwp". *)
(*       iRight. *)
(*       iFrame. *)
(*     + iApply "Hwp". *)
(*       iLeft. *)
(*       iPureIntro. *)
(*       apply not_Exists_Forall; auto. *)
(*       apply _. *)
(* Qed. *)


(* Lemma wp_rand_err_set_in_out (N : nat) (z : Z) (ns : gset nat) (ε εI εO : R) E Φ : *)
(*   TCEq N (Z.to_nat z) → *)
(*   (0<=εI)%R -> *)
(*   (0<=εO)%R -> *)
(*   (forall n, n ∈ ns -> n < S N) -> *)
(*   (εI * (size ns) + εO * (N + 1 - size ns)  <= ε * (N + 1))%R -> *)
(*   ↯ ε ∗ *)
(*     (∀ x : fin (S N), *)
(*         (( ⌜ ¬ (fin_to_nat x ∈ ns) ⌝ ∗ ↯ εO ) ∨ *)
(*          ( ⌜ fin_to_nat x ∈ ns ⌝ ∗ ↯ εI ) -∗ Φ #x)) *)
(*     ⊢ WP rand #z @ E {{ Φ }}. *)
(* Proof. *)
(*   iIntros (HN HineqI HineqO Hlen Hleq) "[Herr Hwp]". *)
(*   set (ε2 := (λ x : fin (S N), if bool_decide (fin_to_nat x ∈ ns) then εI else εO)). *)
(*   wp_apply (wp_couple_rand_adv_comp1 _ _ _  (SeriesC (λ n : fin (S N), (1 / (N + 1) * ε2 n)%R)) ε2 with "[Herr]"). *)
(*   { intros. rewrite /ε2. by case_bool_decide. } *)
(*   { rewrite S_INR. done. } *)
(*   - iApply ec_weaken; auto. *)
(*     simpl. *)
(*     rewrite SeriesC_scal_l /ε2. *)
(*     rewrite (SeriesC_ext _ (λ x : fin (S N), *)
(*                    εI * (if bool_decide (fin_to_nat x ∈ ns) then 1 else 0) + *)
(*                    εO * (if bool_decide (¬(fin_to_nat x ∈ ns)) then 1 else 0))%R); last first. *)
(*     { *)
(*       intro n. *)
(*       case_bool_decide as HE ; case_bool_decide as HF; simpl. *)
(*       - done. *)
(*       - lra. *)
(*       - lra. *)
(*       - done. *)
(*     } *)
(*     rewrite SeriesC_plus; [ | apply ex_seriesC_finite | apply ex_seriesC_finite]. *)
(*     rewrite 2!SeriesC_scal_l. *)
(*     rewrite /Rdiv Rmult_1_l. *)
(*     rewrite Rmult_comm. *)
(*     rewrite -Rdiv_def. *)
(*     pose proof (pos_INR N). *)
(*     split. *)
(*     { apply Rmult_le_pos; [|real_solver]. *)
(*       apply Rplus_le_le_0_compat. *)
(*       - apply Rmult_le_pos; [lra|]. *)
(*         apply SeriesC_ge_0; [|apply ex_seriesC_finite]. *)
(*         intros ?. case_bool_decide; lra. *)
(*       - apply Rmult_le_pos; [lra|]. *)
(*         apply SeriesC_ge_0; [|apply ex_seriesC_finite]. *)
(*         intros ?. case_bool_decide; lra. *)
(*     } *)

(*     apply Rcomplements.Rle_div_l; [lra |]. *)
(*     rewrite SeriesC_fin_in_set; auto. *)
(*     rewrite SeriesC_fin_not_in_set; auto. *)
(*   - iIntros (n) "Herrn". *)
(*     rewrite /ε2. *)
(*     case_bool_decide. *)
(*     + iApply "Hwp". *)
(*       iRight. *)
(*       iFrame. *)
(*       done. *)
(*     + iApply "Hwp". *)
(*       iLeft. *)
(*       iFrame. *)
(*       done. *)
(* Qed. *)

(* Lemma wp_rand_err_filter_adv (N : nat) (z : Z) (P : nat -> bool) (ε0 : R) (ε1 : R) E Φ : *)
(*   TCEq N (Z.to_nat z) → *)
(*   (0<=ε1)%R-> *)
(*   (ε1 * (length (List.filter P (seq 0 (S N)))) <= ε0 * (N + 1))%R -> *)
(*   ↯ ε0 ∗ *)
(*     (∀ x : fin (S N), ((⌜ P x = false⌝) ∨ ↯ ε1 ) -∗ Φ #x) *)
(*     ⊢ WP rand #z @ E {{ Φ }}. *)
(* Proof. *)
(*   iIntros (? Hineq HK) "[H1 Hwp]". *)
(*   iApply (wp_rand_err_list_adv _ _ (List.filter P (seq 0 (S N))) ε0 ε1); auto. *)
(*   iFrame. *)
(*   iIntros (x) "[%Hfor|Herr]". *)
(*   - iApply "Hwp". *)
(*     iLeft. *)
(*     iPureIntro. *)
(*     edestruct (List.Forall_forall) as (H1 & H2). *)
(*     specialize (H1 Hfor). *)
(*     destruct (P x) eqn:HPx ; auto. *)
(*     exfalso. *)
(*     apply (H1 x); auto. *)
(*     apply filter_In; split; auto. *)
(*     apply in_seq. *)
(*     simpl. *)
(*     split; auto with arith. *)
(*     apply fin_to_nat_lt. *)
(*   - iApply "Hwp". *)
(*     iRight. iFrame. *)
(* Qed. *)

(* Lemma pgl_state (N : nat) 𝜎 𝛼 ns : *)
(*   𝜎.(tapes) !! 𝛼 = Some (N; ns) → *)
(*   pgl *)
(*     (state_step 𝜎 𝛼) *)
(*     (λ 𝜎', ∃ (n : fin (S N)), 𝜎' = state_upd_tapes <[𝛼 := (N; ns ++ [n])]> 𝜎) *)
(*     nnreal_zero. *)
(* Proof. *)
(*   rewrite /pgl. intros Htapes. *)
(*   apply Req_le_sym; simpl. *)
(*   rewrite /prob SeriesC_0; auto. *)
(*   intros 𝜎'. *)
(*   case_bool_decide; auto. *)
(*   rewrite /state_step. *)
(*   case_bool_decide. *)
(*   2: { exfalso. apply H0. by apply elem_of_dom. } *)
(*   intros. *)
(*   replace (lookup_total 𝛼 (tapes 𝜎)) with (N; ns). *)
(*   2: { rewrite (lookup_total_correct _ _ (existT N ns)); auto.  } *)
(*   apply dmap_unif_zero. *)
(*   intros n Hcont. *)
(*   apply H. *)
(*   naive_solver. *)
(* Qed. *)

(* Lemma pgl_iterM_state N p σ α ns: *)
(*   σ.(tapes) !! α = Some (N; ns) → *)
(*   pgl (iterM p (λ σ, state_step σ α) σ) *)
(*     (λ σ', *)
(*        ∃ ns' : list (fin (S N)), *)
(*          ns' ∈ enum_uniform_fin_list N p ∧ σ' = state_upd_tapes <[α:=(N; ns ++ ns')]> σ) 0. *)
(* Proof. *)
(*   intros H. *)
(*   rewrite /pgl. *)
(*   apply Req_le_sym. *)
(*   rewrite /prob SeriesC_0; auto. *)
(*   intros σ'. *)
(*   case_bool_decide as H0; auto. *)
(*   simpl. *)
(*   erewrite iterM_state_step_unfold; last done. *)
(*   apply dmap_elem_ne. *)
(*   { intros ?? H'. *)
(*     apply state_upd_tapes_same in H'. *)
(*     by simplify_eq. *)
(*   } *)
(*   intros [?[? <-]]. *)
(*   rewrite -dunifv_pos in H1. *)
(*   apply H0. *)
(*   exists x. *)
(*   split; [by apply elem_of_enum_uniform_fin_list|done]. *)
(* Qed.  *)

(* Lemma state_step_coupl_iterM_state_adv_comp_con_prob_lang (p:nat) α σ1 Z (ε ε_rem: nonnegreal) N ns: *)
(*   (σ1.(tapes)!!α=Some (N;ns) -> *)
(*    (∃ (ε2 : (list (fin (S N))) -> nonnegreal), *)
(*        ⌜ (SeriesC (λ n, if (length n =? p) then (1/((S N)^ p)) * ε2 n else 0%R) <= ε)%R ⌝ ∗ *)
(*        ∀ n, ⌜(length n = p)%nat⌝ -∗ |={∅}=> state_step_coupl (state_upd_tapes <[α:=(_; ns ++ n) : tape]> σ1) (ε_rem+ε2 n)%NNR Z) *)
(*    ⊢ state_step_coupl σ1 (ε_rem+ε)%NNR Z)%I. *)
(* Proof. *)
(*   iIntros (Hin) "(%ε2 & %Hε & H)". *)
(*   iApply state_step_coupl_iterM_state_adv_comp. *)
(*   { rewrite /=/con_prob_lang.get_active. *)
(*     by apply list_elem_of_In, list_elem_of_In, elem_of_elements, elem_of_dom. } *)
(*   assert (0<=1 / S N ^ p)%R as Hineq. *)
(*   { apply Rcomplements.Rdiv_le_0_compat; first lra. apply pow_lt. apply pos_INR_S. } *)
(*  (* R: predicate should hold iff tapes σ' at α is ns ++ [nx] where ns is in enum_uniform_fin_list N p *)  *)
(*   unshelve iExists *)
(*     (fun σ' : state => exists ns', ns' ∈ enum_uniform_fin_list N p /\ σ' = (state_upd_tapes <[α:=(_; ns ++ ns') : tape]> σ1)), nnreal_zero, *)
(*              (fun ρ => (ε_rem + *)
(*                        match ClassicalEpsilon.excluded_middle_informative (exists ns', ns' ∈ enum_uniform_fin_list N p /\ ρ = (state_upd_tapes <[α:=(_; ns ++ ns') : tape]> σ1)) with *)
(*                        | left p => mknonnegreal (ε2 (epsilon p)) _ *)
(*                        |  _ => nnreal_zero *)
(*                        end))%NNR. *)
(*   { simpl; done. } *)
(*   repeat iSplit. *)
(*   - iPureIntro. *)
(*     exists (ε_rem + (INR (S N))^p * ε)%R. *)
(*     intros. pose proof pos_INR ((S N)) as H.  *)
(*     case_match eqn:K; rewrite S_INR; last first. *)
(*     { apply Rplus_le_compat_l. apply Rmult_le_pos; simpl; auto. apply pow_le. rewrite -S_INR; lra. } *)
(*     pose proof epsilon_correct _ e as [H1 H2]. *)
(*     apply Rplus_le_compat_l. simpl. *)
(*     assert (1 / S N ^ p * ε2 (epsilon e) <= ε)%R as T; last first. *)
(*     { rewrite Rmult_comm. apply Rcomplements.Rle_div_l. *)
(*       - apply Rlt_gt. apply pow_lt. pose proof pos_INR N; lra.  *)
(*       - rewrite -S_INR; simpl in *; lra. *)
(*     } *)
(*     rewrite elem_of_enum_uniform_fin_list in H1. *)
(*     etrans; last exact. *)
(*     etrans; last apply (SeriesC_ge_elem _ (epsilon e)). *)
(*     + rewrite S_INR. rewrite H1. by rewrite Nat.eqb_refl. *)
(*     + intros; case_match; last lra. *)
(*       apply Rmult_le_pos; try done. by simpl. *)
(*     + apply (ex_seriesC_ext (λ n, if bool_decide (n∈enum_uniform_fin_list N p) then (1 / S N ^ p * ε2 n)%R else 0%R)); last apply ex_seriesC_list. *)
(*       intros. case_bool_decide as H'; rewrite elem_of_enum_uniform_fin_list in H'. *)
(*       * subst. by rewrite Nat.eqb_refl. *)
(*       * rewrite -Nat.eqb_neq in H'. by rewrite H'. *)
(*   - iPureIntro. *)
(*     simpl. *)
(*     setoid_rewrite iterM_state_step_unfold; last done. *)
(*     rewrite /Expval. *)
(*     erewrite SeriesC_ext; last first. *)
(*     { intros.  *)
(*       by rewrite dmap_unfold_pmf -SeriesC_scal_r. *)
(*     } *)
(*     rewrite fubini_pos_seriesC'; last first. *)
(*     + eapply (ex_seriesC_ext (λ a, if bool_decide (a ∈ enum_uniform_fin_list N p) then _ else 0%R)); last apply ex_seriesC_list. *)
(*       intros n. *)
(*       case_bool_decide as H; first done. *)
(*       rewrite SeriesC_0; first done. *)
(*       intros x. *)
(*       rewrite dunifv_pmf bool_decide_eq_false_2; first lra. *)
(*       by rewrite -elem_of_enum_uniform_fin_list. *)
(*     + intros a. *)
(*       rewrite dunifv_pmf. *)
(*       eapply (ex_seriesC_ext (λ b, if bool_decide (b=state_upd_tapes <[α:=(N; ns ++ a)]> σ1) then _ else 0%R)); last apply ex_seriesC_singleton_dependent. *)
(*       intros. *)
(*       case_bool_decide as H; [done|lra]. *)
(*     + intros. *)
(*       repeat apply Rmult_le_pos; repeat case_match; simpl; try lra; try done. *)
(*       all: apply Rplus_le_le_0_compat; by try lra. *)
(*     + erewrite (SeriesC_ext _ (λ n, (if bool_decide (n∈enum_uniform_fin_list N p) then 1 / S N ^ p * ε2 n else 0) + (if bool_decide (n∈enum_uniform_fin_list N p) then 1 / S N ^ p * ε_rem else 0)))%R. *)
(*       * rewrite SeriesC_plus; [|apply ex_seriesC_list..]. *)
(*         rewrite SeriesC_list_2; last apply NoDup_enum_uniform_fin_list. *)
(*         rewrite enum_uniform_fin_list_length. *)
(*         setoid_rewrite elem_of_enum_uniform_fin_list'. *)
(*         rewrite Rplus_0_l. *)
(*         rewrite Rplus_comm. apply Rplus_le_compat; last done. *)
(*         rewrite -pow_INR. simpl. *)
(*         assert (INR (S N ^ p) / INR (S N ^ p) * nonneg ε_rem  <= nonneg ε_rem)%R; try lra. *)
(*         rewrite Rdiv_diag; try lra. *)
(*         replace 0%R with (INR 0) by done. *)
(*         intro H. *)
(*         apply INR_eq in H. *)
(*         rewrite Nat.pow_eq_0_iff in H. lia. *)
(*       * intros l. *)
(*         case_bool_decide as H. *)
(*         -- (* only one state is relevant *) *)
(*           erewrite (SeriesC_ext _ (λ b, if bool_decide (b=state_upd_tapes <[α:=(N; ns ++ l)]> σ1) then _ else 0%R)); last first. *)
(*           ++ intros n. *)
(*              case_bool_decide; [done|lra]. *)
(*           ++ rewrite SeriesC_singleton_dependent. *)
(*              case_match; last first. *)
(*              { exfalso. apply n. naive_solver. } *)
(*              rewrite dunifv_pmf. *)
(*              rewrite bool_decide_eq_true_2; last by apply elem_of_enum_uniform_fin_list. *)
(*              rewrite -pow_INR. simpl. *)
(*              pose proof epsilon_correct _ e as H'. simpl in H'. *)
(*              replace (epsilon e) with l; try lra. *)
(*              destruct H' as [? H']. *)
(*              apply state_upd_tapes_same in H'. *)
(*              by simplify_eq. *)
(*         -- rewrite SeriesC_0; first lra. *)
(*            intros. *)
(*            rewrite dunifv_pmf. *)
(*            rewrite bool_decide_eq_false_2; first lra. *)
(*            by rewrite -elem_of_enum_uniform_fin_list. *)
(*   - simpl. *)
(*     iPureIntro. *)
(*     eapply pgl_mon_pred; last first. *)
(*     + apply pgl_iterM_state. apply Hin. *)
(*     + done. *)
(*   - iIntros (σ2 [ns' [Helem ->]]). *)
(*     pose proof Helem as Helem'. *)
(*     rewrite elem_of_enum_uniform_fin_list in Helem. rewrite <- Helem. *)
(*     iMod ("H" with "[]") as "H"; first done. *)
(*     case_match; last first. *)
(*     + (* contradiction *) *)
(*       exfalso. apply n. *)
(*       naive_solver. *)
(*     + iModIntro. pose proof epsilon_correct _ e as [? H']. simpl in H'. *)
(*       assert (epsilon e = ns') as ->. *)
(*       { apply state_upd_tapes_same in H'. by simplify_eq. } *)
(*       replace (_+{|nonneg := _ ; cond_nonneg := _|})%NNR with (ε_rem+ ε2 ns')%NNR; try done. *)
(*       apply nnreal_ext. by simpl. *)
(* Qed. *)


(* Lemma state_step_coupl_state_adv_comp_con_prob_lang α σ1 Z (ε ε_rem: nonnegreal) N ns: *)
(*   (σ1.(tapes)!!α=Some (N;ns) -> *)
(*    (∃ (ε2 : (fin (S N)) -> nonnegreal), *)
(*        ⌜ (SeriesC (λ n, (1/(S N)) * ε2 n) <= ε)%R ⌝ ∗ *)
(*        ∀ n, |={∅}=> state_step_coupl (state_upd_tapes <[α:=(_; ns ++ [n]) : tape]> σ1) (ε_rem+ε2 n)%NNR Z) *)
(*    ⊢ state_step_coupl σ1 (ε_rem+ε)%NNR Z)%I. *)
(* Proof. *)
(*   iIntros (Hin) "(%ε2 & %Hε & H)". *)
(*   iApply (state_step_coupl_iterM_state_adv_comp_con_prob_lang 1%nat); first done. *)
(*   iExists (λ ls, match ls with |[x] => ε2 x | _ => nnreal_zero end). *)
(*   iSplit; first iPureIntro. *)
(*   - etrans; last exact. *)
(*     etrans; last eapply (SeriesC_le_inj _ (λ x, match x with |[x'] => Some x' | _ => None end)). *)
(*     + apply SeriesC_le. *)
(*       * intros. split; repeat case_match; try rewrite S_INR; simpl; try rewrite Rmult_1_r; try lra. *)
(*         all: apply Rmult_le_pos; last done. *)
(*         all: rewrite -S_INR; apply Rdiv_INR_ge_0. *)
(*       * eapply (ex_seriesC_ext (λ x, if (bool_decide (x∈enum_uniform_fin_list N 1%nat)) then *)
(*                                      match x with |[x'] => (1 / S N * ε2 x')%R | _ => 0 end else 0)); *)
(*           last apply ex_seriesC_list. *)
(*         intros [|n[|]]. *)
(*         -- rewrite bool_decide_eq_false_2; first done. *)
(*            by rewrite elem_of_enum_uniform_fin_list. *)
(*         -- rewrite bool_decide_eq_true_2; first done. *)
(*            by rewrite elem_of_enum_uniform_fin_list. *)
(*         -- rewrite bool_decide_eq_false_2; first done. *)
(*            by rewrite elem_of_enum_uniform_fin_list. *)
(*     + intros; apply Rmult_le_pos; last by simpl. *)
(*       apply Rdiv_INR_ge_0. *)
(*     + intros. repeat case_match; by simplify_eq. *)
(*     + apply ex_seriesC_finite. *)
(*   - iIntros (??). *)
(*     by destruct n as [|n [|]]. *)
(* Qed.  *)

(* Lemma wp_presample (N : nat) E e 𝛼 Φ ns : *)
(*   ▷ 𝛼 ↪N (N;ns) ∗ *)
(*   (∀ n, 𝛼 ↪N (N; ns ++ [n]) -∗ WP e @ E {{ Φ }}) *)
(*   ⊢ WP e @ E {{ Φ }}. *)
(* Proof. *)
(*   iIntros "(>H𝛼&Hwp)". *)
(*   iApply wp_lift_step_fupd_glm. *)
(*   iIntros (𝜎 ε) "((Hheap&Htapes)&Hε)". *)
(*   iDestruct "H𝛼" as (ns') "(%Hmap & H𝛼)". *)
(*   iDestruct (ghost_map_lookup with "Htapes H𝛼") as %Hlookup. *)
(*   iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'". *)
(*   replace ε with (nnreal_zero + ε)%NNR by (apply nnreal_ext; simpl; lra). *)
(*   iApply state_step_coupl_state_adv_comp_con_prob_lang; first done. *)
(*   iExists (λ _, ε). *)
(*   iSplitR. *)
(*   { iPureIntro. rewrite SeriesC_finite_mass fin_card. rewrite -Rmult_assoc. *)
(*     rewrite Rdiv_1_l  Rinv_r; first lra. *)
(*     pose proof pos_INR_S N; lra. *)
(*   } *)
(*   iIntros (n).  *)
(*   iDestruct (ghost_map_lookup with "Htapes H𝛼") as %?%lookup_total_correct. *)
(*   iMod (ghost_map_update ((N; ns' ++ [n]) : tape) with "Htapes H𝛼") as "[Htapes H𝛼]". *)
(*   iMod "Hclose'" as "_". *)
(*   iSpecialize ("Hwp" $! (fin_to_nat n) with "[H𝛼]"). *)
(*   { iExists _. iFrame. iPureIntro. rewrite fmap_app; by f_equal. } *)
(*   rewrite !pgl_wp_unfold /pgl_wp_pre /=. *)
(*   iSpecialize ("Hwp" $! (state_upd_tapes <[𝛼:=(N; ns' ++ [n]):tape]> 𝜎) ε). *)
(*   iMod ("Hwp" with "[Hheap Htapes Hε]") as "Hwp". *)
(*   { replace (nnreal_zero + ε)%NNR with ε by (apply nnreal_ext; simpl; lra). *)
(*     simpl. *)
(*     iFrame. *)
(*   } *)
(*   iModIntro. *)
(*   iApply state_step_coupl_mono_err; last done. *)
(*   simpl; lra. *)
(* Qed. *)


(* Lemma wp_presample_adv_comp (N : nat) E e α Φ ns (ε1 : R) (ε2 : fin (S N) -> R) : *)
(*   (∀ n, 0<=ε2 n)%R -> *)
(*   (SeriesC (λ n, (1 / (S N)) * ε2 n)%R <= ε1)%R → *)
(*   ▷α ↪N (N; ns) ∗ *)
(*   ↯ ε1 ∗ *)
(*   (∀ n, ↯ (ε2 n) ∗ α ↪N (N; ns ++ [fin_to_nat n]) -∗ WP e @ E {{ Φ }}) *)
(*   ⊢ WP e @ E {{ Φ }}. *)
(* Proof. *)
(*   iIntros (Hpos Hsum) "(>Hα & Hε & Hwp)". *)
(*   iApply wp_lift_step_fupd_glm. *)
(*   iIntros (σ1 ε_now) "[(Hheap&Htapes) Hε_supply]". *)
(*   iDestruct "Hα" as (ns') "(%Hmap & Hα)". *)
(*   iDestruct (ghost_map_lookup with "Htapes Hα") as "%Hlookup". *)
(*   iDestruct (ec_supply_bound with "Hε_supply Hε") as %Hε1_ub. *)
(*   iMod (ec_supply_decrease with "Hε_supply Hε") as (ε1' ε_rem -> Hε1') "Hε_supply". *)
(*   iApply fupd_mask_intro; [set_solver|]. *)
(*   iIntros "Hclose". *)
(*   subst. *)
(*   iApply (state_step_coupl_state_adv_comp_con_prob_lang); first done. *)
(*   iExists (λ x, mknonnegreal (ε2 x) _). *)
(*   iSplit; first done. *)
(*   iIntros (sample). *)
(*   destruct (Rlt_decision (ε_rem + (ε2 sample))%R 1%R) as [Hdec|Hdec]; last first. *)
(*   { apply Rnot_lt_ge, Rge_le in Hdec. *)
(*     iApply state_step_coupl_ret_err_ge_1. *)
(*     simpl. simpl in *. lra. *)
(*   } *)
(*   unshelve iMod (ec_supply_increase _ (mknonnegreal (ε2 sample) _) with "Hε_supply") as "[Hε_supply Hε]"; first done. *)
(*   { simplify_eq. simpl. done. } *)
(*   iMod (ghost_map_update ((N; ns' ++ [sample]) : tape) with "Htapes Hα") as "[Htapes Hα]". *)
(*   iSpecialize ("Hwp" $! sample). *)
(*   rewrite pgl_wp_unfold /pgl_wp_pre. *)
(*   simpl. *)
(*   remember {| heap := heap (σ1); tapes := (<[α:=(N; ns' ++ [sample])]> (tapes σ1)) |} as σ2. *)
(*   rewrite /=. *)
(*   iSpecialize ("Hwp" with "[Hε Hα]"); first iFrame. *)
(*   { iPureIntro. rewrite fmap_app; by f_equal. } *)
(*   iSpecialize ("Hwp" $! σ2 _). *)
(*   subst. *)
(*   iSpecialize ("Hwp" with "[Hheap Htapes Hε_supply]"). *)
(*   { iSplitL "Hheap Htapes". *)
(*     - rewrite /tapes_auth. iFrame. *)
(*     - iFrame. } *)
(*   iMod "Hclose"; iMod "Hwp"; iModIntro. *)
(*   done. *)
(* Qed. *)

(*   Lemma wp_update_presample E α N ns : *)
(*     α ↪N (N; ns) -∗ wp_update E (∃ n, α ↪N (N; ns ++ [n])). *)
(*   Proof. *)
(*     rewrite wp_update_unseal. *)
(*     iIntros "Hα" (e Φ) "Hwp". *)
(*     iApply wp_presample. *)
(*     iFrame. iIntros (n) "Hα". *)
(*     iApply ("Hwp" with "[$Hα]"). *)
(*   Qed. *)

(*   Lemma wp_update_presample_exp E α N ns (ε1 : R) (ε2 : fin (S N) → R) : *)
(*     (∀ n, 0<=ε2 n)%R -> *)
(*     (SeriesC (λ n, 1 / (S N) * ε2 n)%R <= ε1)%R → *)
(*     α ↪N (N; ns) ∗ ↯ ε1 -∗ wp_update E (∃ n, α ↪N (N; ns ++ [fin_to_nat n]) ∗ ↯ (ε2 n)). *)
(*   Proof. *)
(*     rewrite wp_update_unseal. *)
(*     iIntros (? ?) "[Hα Hε1]". iIntros (e Φ) "Hwp". *)
(*     iApply (wp_presample_adv_comp _ _ _ _ _ _ _ ε2); [done|done|..]. *)
(*     iFrame. iIntros (n) "[Hα Hε2]". *)
(*     iApply ("Hwp" with "[$Hα $Hε2]"). *)
(*   Qed. *)

(*   Lemma wp_update_presample_exp' E α N ns (ε1 : R) (ε2 : nat → R) : *)
(*     (∀ n, 0<=ε2 n)%R -> *)
(*     (SeriesC (λ n, if (bool_decide (n≤N)) then 1 / (S N) * ε2 n else 0%R)%R <= ε1)%R → *)
(*     α ↪N (N; ns) ∗ ↯ ε1 -∗ wp_update E (∃ n, α ↪N (N; ns ++ [n]) ∗ ↯ (ε2 n)). *)
(*   Proof. *)
(*     iIntros (? ?) "[Hα Hε1]". *)
(*     iPoseProof (wp_update_presample_exp _ _ _ _ _ (λ x, ε2 (fin_to_nat x))  with "[$]") as "K". *)
(*     - naive_solver. *)
(*     - etrans; last exact. *)
(*       erewrite (SeriesC_ext _ (λ x, from_option (λ m, if bool_decide (m≤N) then 1/S N * ε2 m else 0)%R 0 (Some (fin_to_nat x)))); last first. *)
(*       { intros. rewrite S_INR. simpl. *)
(*         rewrite bool_decide_eq_true_2; first done. *)
(*         pose proof fin_to_nat_lt n. lia. *)
(*       } *)
(*       apply SeriesC_le_inj. *)
(*       + intros; case_bool_decide; last lra. *)
(*         apply Rmult_le_pos; last done. *)
(*         apply Rdiv_INR_ge_0. *)
(*       + intros. by simplify_eq. *)
(*       + apply ex_seriesC_nat_bounded. *)
(*     - iApply wp_update_mono; iFrame. *)
(*       iIntros "(%&H1&H2)". *)
(*       iFrame. *)
(*   Qed. *)

(*   Lemma state_update_presample_iterM_exp E α N ns p (ε1 : R) (ε2 : list (fin (S N)) → R) : *)
(*     (∀ n, 0<=ε2 n)%R -> *)
(*     (SeriesC (λ n, if (length n =? p) then (1/((S N)^ p)) * ε2 n else 0%R )<= ε1)%R → *)
(*      α ↪N (N; ns) -∗ ↯ ε1 -∗ state_update E E (∃ n, α ↪N (N; ns ++ (fin_to_nat <$> n)) ∗ *)
(*                                                   ↯ (ε2 n) ∗ *)
(*                                                   ⌜length n = p⌝ *)
(*                                ). *)
(*   Proof.  *)
(*     rewrite state_update_unseal/state_update_def. *)
(*     iIntros (Hpos Hsum) "Hα Hε". *)
(*     iIntros (σ1 ε_now) "[(Hheap&Htapes) Hε_supply]". *)
(*     iDestruct "Hα" as (ns') "(%Hmap & Hα)". *)
(*     iDestruct (ghost_map_lookup with "Htapes Hα") as "%Hlookup". *)
(*     iDestruct (ec_supply_bound with "Hε_supply Hε") as %Hε1_ub. *)
(*     iMod (ec_supply_decrease with "Hε_supply Hε") as (ε1' ε_rem -> Hε1') "Hε_supply". *)
(*     iApply fupd_mask_intro; [set_solver|]. *)
(*     iIntros "Hclose". *)
(*     subst. *)
(*     iApply (state_step_coupl_iterM_state_adv_comp_con_prob_lang); first done. *)
(*     iExists (λ x, mknonnegreal (ε2 x) _). *)
(*     iSplit; first done. *)
(*     iIntros (sample <-). *)
(*     destruct (Rlt_decision (ε_rem + (ε2 sample))%R 1%R) as [Hdec|Hdec]; last first. *)
(*     { apply Rnot_lt_ge, Rge_le in Hdec. *)
(*       iApply state_step_coupl_ret_err_ge_1. *)
(*       simpl. simpl in *. lra. *)
(*     } *)
(*     unshelve iMod (ec_supply_increase _ (mknonnegreal (ε2 sample) _) with "Hε_supply") as "[Hε_supply Hε]"; first done. *)
(*     { simplify_eq. simpl. done. } *)
(*     iMod (ghost_map_update ((N; ns' ++ sample) : tape) with "Htapes Hα") as "[Htapes Hα]". *)
(*     (* iSpecialize ("Hwp" $! sample). *) *)
(*     (* rewrite pgl_wp_unfold /pgl_wp_pre. *) *)
(*     (* simpl. *) *)
(*     remember {| heap := heap (σ1); tapes := (<[α:=(N; ns' ++ sample)]> (tapes σ1)) |} as σ2. *)
(*     rewrite /=. *)
(*     iModIntro. *)
(*     iApply state_step_coupl_ret. *)
(*     iMod "Hclose". *)
(*     iFrame. *)
(*     iPureIntro. rewrite fmap_app; by f_equal. *)
(*   Qed. *)

(*   Lemma state_update_presample_exp E α N ns (ε1 : R) (ε2 : fin (S N) → R) : *)
(*     (∀ n, 0<=ε2 n)%R -> *)
(*     (SeriesC (λ n, 1 / (S N) * ε2 n)%R <= ε1)%R → *)
(*     α ↪N (N; ns) -∗ ↯ ε1 -∗ state_update E E (∃ n, α ↪N (N; ns ++ [fin_to_nat n]) ∗ ↯ (ε2 n)). *)
(*   Proof. *)
(*     rewrite state_update_unseal/state_update_def. *)
(*     iIntros (Hpos Hsum) "Hα Hε". *)
(*     iIntros (σ1 ε_now) "[(Hheap&Htapes) Hε_supply]". *)
(*     iDestruct "Hα" as (ns') "(%Hmap & Hα)". *)
(*     iDestruct (ghost_map_lookup with "Htapes Hα") as "%Hlookup". *)
(*     iDestruct (ec_supply_bound with "Hε_supply Hε") as %Hε1_ub. *)
(*     iMod (ec_supply_decrease with "Hε_supply Hε") as (ε1' ε_rem -> Hε1') "Hε_supply". *)
(*     iApply fupd_mask_intro; [set_solver|]. *)
(*     iIntros "Hclose". *)
(*     subst. *)
(*     iApply (state_step_coupl_state_adv_comp_con_prob_lang); first done. *)
(*     iExists (λ x, mknonnegreal (ε2 x) _). *)
(*     iSplit; first done. *)
(*     iIntros (sample). *)
(*     destruct (Rlt_decision (ε_rem + (ε2 sample))%R 1%R) as [Hdec|Hdec]; last first. *)
(*     { apply Rnot_lt_ge, Rge_le in Hdec. *)
(*       iApply state_step_coupl_ret_err_ge_1. *)
(*       simpl. simpl in *. lra. *)
(*     } *)
(*     unshelve iMod (ec_supply_increase _ (mknonnegreal (ε2 sample) _) with "Hε_supply") as "[Hε_supply Hε]"; first done. *)
(*     { simplify_eq. simpl. done. } *)
(*     iMod (ghost_map_update ((N; ns' ++ [sample]) : tape) with "Htapes Hα") as "[Htapes Hα]". *)
(*     (* iSpecialize ("Hwp" $! sample). *) *)
(*     (* rewrite pgl_wp_unfold /pgl_wp_pre. *) *)
(*     (* simpl. *) *)
(*     remember {| heap := heap (σ1); tapes := (<[α:=(N; ns' ++ [sample])]> (tapes σ1)) |} as σ2. *)
(*     rewrite /=. *)
(*     iModIntro. *)
(*     iApply state_step_coupl_ret. *)
(*     iMod "Hclose". *)
(*     iFrame. *)
(*     iPureIntro. rewrite fmap_app; by f_equal. *)
(*   Qed. *)

(*   Lemma state_step_err_set_in_out (N : nat) (bad : gset nat) (ε εI εO : R) E α ns : *)
(*     (0 <= εI)%R → *)
(*     (0 <= εO)%R → *)
(*     (∀ n, n ∈ bad -> n < S N) → *)
(*     (εI * (size bad) + εO * (N + 1 - size bad)  <= ε * (N + 1))%R → *)
(*     α ↪N (N; ns) -∗ *)
(*     ↯ ε -∗ *)
(*     state_update E E (∃ (x : fin (S N)), *)
(*         ((⌜fin_to_nat x ∉ bad⌝ ∗ ↯ εO) ∨ (⌜fin_to_nat x ∈ bad⌝ ∗ ↯ εI)) ∗ *)
(*           α ↪N (N; ns ++ [fin_to_nat x])). *)
(*   Proof. *)
(*     iIntros (HineqI HineqO Hlen Hleq) "Htape Herr". *)
(*     set (ε2 := (λ x : fin (S N), if bool_decide (fin_to_nat x ∈ bad) then εI else εO)). *)
(*     iMod (state_update_presample_exp _ _ _ _ (SeriesC (λ n : fin (S N), (1 / (N + 1) * ε2 n)%R)) ε2 *)
(*            with "Htape [Herr]") as (x) "[Htape Herr]". *)
(*     { intros. rewrite /ε2. by case_bool_decide. } *)
(*     { rewrite S_INR. done. } *)
(*     { iApply ec_weaken; auto. *)
(*       simpl. *)
(*       rewrite SeriesC_scal_l /ε2. *)
(*       erewrite (SeriesC_ext _ (λ x : fin (S N), *)
(*                      εI * (if bool_decide (fin_to_nat x ∈ bad) then 1 else 0) + *)
(*                      εO * (if bool_decide (fin_to_nat x ∉ bad) then 1 else 0))%R); last first. *)
(*       { intro n. do 2 case_bool_decide; done || lra. } *)
(*       rewrite SeriesC_plus; [ | apply ex_seriesC_finite | apply ex_seriesC_finite]. *)
(*       rewrite 2!SeriesC_scal_l. *)
(*       rewrite /Rdiv Rmult_1_l. *)
(*       rewrite Rmult_comm. *)
(*       rewrite -Rdiv_def. *)
(*       pose proof (pos_INR N). *)
(*       split. *)
(*       { apply Rmult_le_pos; [|real_solver]. *)
(*         apply Rplus_le_le_0_compat. *)
(*         - apply Rmult_le_pos; [lra|]. *)
(*           apply SeriesC_ge_0; [|apply ex_seriesC_finite]. *)
(*           intros ?. case_bool_decide; lra. *)
(*         - apply Rmult_le_pos; [lra|]. *)
(*           apply SeriesC_ge_0; [|apply ex_seriesC_finite]. *)
(*           intros ?. case_bool_decide; lra. } *)
(*       apply Rcomplements.Rle_div_l; [lra |]. *)
(*       rewrite SeriesC_fin_in_set; auto. *)
(*       rewrite SeriesC_fin_not_in_set; auto. } *)
(*     rewrite /ε2. *)
(*     iModIntro. *)
(*     case_bool_decide; iFrame; eauto. *)
(*   Qed. *)

(*   Lemma wp_couple_empty_tape_adv_comp E α N (ε1 : R) (ε2 : nat → R) : *)
(*     (∀ (n:nat), 0<= ε2 n)%R -> *)
(*     (SeriesC (λ n, if (bool_decide (n≤N)) then 1 / (S N) * ε2 n else 0%R)%R <= ε1)%R → *)
(*     {{{ α ↪N (N; []) ∗ ↯ ε1 }}} *)
(*       rand(#lbl:α) #N @ E *)
(*       {{{ n, RET #n; α ↪N (N; []) ∗ ↯ (ε2 n) }}}. *)
(*   Proof. *)
(*     iIntros (Hpos Hineq Φ) "[Hα Herr] HΦ". *)
(*     iMod (wp_update_presample_exp' with "[$]") as "(%&H1&H2)"; [done|done|]. *)
(*     wp_apply (wp_rand_tape with "[$]") as "[??]". *)
(*     iApply "HΦ". iFrame. *)
(*   Qed.  *)
      
End rules.

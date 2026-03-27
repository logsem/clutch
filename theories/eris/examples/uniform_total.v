From clutch.eris Require Export eris adequacy total_adequacy.
From clutch.eris Require Import infinite_tape.
From clutch.eris.examples Require Import lazy_real_programs.
From clutch.eris.examples Require Import lazy_real lazy_real_expr lazy_real_adequacy.
From clutch.eris.examples Require Import math.
From Coquelicot Require Import RInt RInt_gen.
Import Hierarchy.
Set Default Proof Using "Type*".
#[local] Open Scope R.

(** The uniform sampler: sample a lazy real and convert to approximation sequence *)
Definition UnifSampler : expr := R_ofUnif (init #()).

Section uniform_total.
  Context `{!erisGS Σ}.

  (** TWP for init: allocate a lazy real *)
  Lemma twp_init E :
    ⊢ WP init #() @ E [{ v, lazy_real_uninit v }].
  Proof.
    rewrite /init.
    wp_pures.
    wp_alloc l as "Hl".
    wp_pures.
    wp_apply (twp_alloc_tape); [done|].
    iIntros (α) "Hα".
    wp_pures.
    iModIntro.
    iExists _, _. iSplit; [done|].
    iFrame.
  Qed.

  (*

  Lemma twp_get_chunk α l E :
    chunk_list l [] ∗ α ↪ (1%nat; [])
    ⊢ WP get_chunk #lbl:α #l @ E
      [{ v, ∃ l' (b : Z), ⌜v = (#b, #l')%V⌝ ∗ chunk_list l' [] ∗ α ↪ (1%nat; []) }].

  Lemma twp_get_bits α l E (n : Z) :
    (0 ≤ n)%Z →
    chunk_list l [] ∗ α ↪ (1%nat; [])
    ⊢ WP get_bits (#lbl:α, #l)%V #n #0 @ E
      [{ v, ∃ (R : Z) l', ⌜v = #R⌝ ∗ chunk_list l' [] ∗ α ↪ (1%nat; []) }].
*)

  (** Total WP for the checker — the key new result using total Eris *)
  Lemma twp_lazy_real_cdf_checker E (ε : R) (B C : Z) :
    (0 < ε)%R →
    ⊢ ↯ ε -∗ WP lazy_real_cdf_checker UnifSampler B C @ E [{ v, ⌜ True ⌝ }].
  Proof.
    iIntros (Hε) "Hε".
    rewrite /UnifSampler /lazy_real_cdf_checker.
    wp_bind (init _)%E.
    iApply (tgl_wp_wand with "[]").
    { iApply twp_init. }
    iIntros (v) "Hv".
    rewrite /R_ofUnif.
    wp_pures.
    rewrite /R_ofZ.
    wp_pures.
    rewrite /R_mulPow.
    wp_pures.
    rewrite /lazy_real_uninit.
    iDestruct "Hv" as (l a) "(-> & Hl & Ha)".
    (* Bundle tape and ref into the goal for ec_ind_amp *)
    iAssert (∃ zs, chunk_list l zs ∗ a ↪ (1%nat; zs))%I with "[Hl Ha]" as "I".
    { iExists []. simpl. iFrame. }
    iRevert "I".
    rewrite /R_cmp.
    iApply (ec_ind_amp _ 2 with "[] Hε"); [lra|lra|].
    iModIntro.
    iIntros (ε') "%Hε' #IH Hε' I".
    wp_pures.
    case_bool_decide.
    { by wp_pures. }
    wp_pures.
    case_bool_decide.
    { by wp_pures. }
    wp_pure.
    wp_pures.
    case_bool_decide.
    { by wp_pures. }
    wp_pures.
    case_bool_decide.
    { by wp_pures. }
    wp_pures.
    case_bool_decide.
    { by wp_pures. }
    wp_pures.
    case_bool_decide.
    { by wp_pures. }
    wp_pures.
    case_bool_decide.
    { by wp_pures. }
    wp_pures.
    case_bool_decide.
    { by wp_pures. }
    wp_pures.

    (* The loop body evaluates get_bits (which samples bits) then compares.
    { by wp_pures. }
       We need TWP lemmas for get_bits/get_chunk, or a different approach. *)
    admit.
  Admitted.

End uniform_total.

(** Termination: tgl from total Eris *)
Theorem uniform_cdf_checker_tgl Σ `{erisGpreS Σ} (σ : state) (ε : R) (B C : Z) :
  (0 < ε)%R →
  tgl (lim_exec (lazy_real_cdf_checker UnifSampler B C, σ)) (λ _, True) ε.
Proof.
  intros Hε.
  eapply (twp_tgl _ _ _ ε); [lra|].
  intros.
  iIntros "Hε".
  iApply twp_lazy_real_cdf_checker; [done|].
  iFrame.
Qed.

(** Hterm: the checker terminates with probability 1 *)
Theorem uniform_cdf_checker_terminates Σ `{erisGpreS Σ} (σ : state) (B C : Z) :
  prob (lim_exec (lazy_real_cdf_checker UnifSampler B C, σ)) (fun _ => true) = 1.
Proof.
  rewrite /prob.
  erewrite SeriesC_ext; [|intros; simpl; done].
  apply Rle_antisym; [apply pmf_SeriesC|].
  replace 1 with (1 - 0) by lra.
  eapply (twp_mass_lim_exec_limit _ _ _ 0 (fun _ => True)); [lra|].
  intros ? ε' Hε'.
  iIntros "Hε".
  iApply (twp_lazy_real_cdf_checker with "Hε"); lra.
Qed.

(** Uniform density: Iverson bracket on [0,1] *)
Definition uniform_density : R → R := Iverson (Icc 0 1).

(** IPCts for the uniform density *)
Lemma uniform_density_eq x :
  uniform_density x = Iverson (Ici 0) x * Iverson (Iic 1) x.
Proof.
  rewrite /uniform_density /Iverson /Icc /Ici /Iic.
  rewrite Rmin_left; [|lra]. rewrite Rmax_right; [|lra].
  repeat case_decide; lra.
Qed.

Lemma IPCts_uniform : IPCts uniform_density.
Proof.
  have H : IPCts (fun x => Iverson (Ici 0) x + Iverson (Iic 1) x + -1 * 1).
  { apply IPCts_plus.
    - apply IPCts_plus; [apply IPCts_Ici|apply IPCts_Iic].
    - apply (IPCts_scal_mult (c := -1)). apply IPCts_cts. intros. apply Continuity.continuous_const. }
  destruct H as [f0 [L [Hext [Hcts Hf0]]]].
  exists f0, L. split; [|done].
  intros x.
  have Heq : uniform_density x = Iverson (Ici 0) x + Iverson (Iic 1) x + -1 * 1.
  { rewrite uniform_density_eq /Iverson /Ici /Iic. repeat case_decide; lra. }
  rewrite Heq. apply Hext.
Qed.

(** Integrability on the left half-line *)
Lemma ex_RInt_gen_uniform_neg :
  ex_RInt_gen uniform_density (Rbar_locally Rbar.m_infty) (at_point 0).
Proof.
  eapply ex_RInt_gen_ext_eq_Iio; last first.
  { eapply ex_RInt_gen_neg_change_of_var_rev.
    - intros b Hb. apply ex_RInt_const.
    - apply ex_RInt_gen_0. }
  intros x Hx. rewrite /uniform_density /Iverson.
  case_decide as H; [|done].
  rewrite /Icc in H. exfalso.
  rewrite Rmin_left in H; lra.
Qed.

(** Integrability on the right half-line *)
Lemma ex_RInt_gen_uniform_pos :
  ex_RInt_gen uniform_density (at_point 0) (Rbar_locally Rbar.p_infty).
Proof.
  have Htail : ex_RInt_gen uniform_density (at_point 1) (Rbar_locally Rbar.p_infty).
  { eapply ex_RInt_gen_ext_eq_Ioi; last apply (ex_RInt_gen_0 1).
    intros x Hx. rewrite /uniform_density /Iverson.
    case_decide as H; [|done].
    rewrite /Icc in H. exfalso.
    rewrite Rmin_left in H; [|lra].
    rewrite Rmax_right in H; [|lra]. lra. }
  have Hfin : ex_RInt_gen uniform_density (at_point 0) (at_point 1).
  { rewrite ex_RInt_gen_at_point. apply IPCts_RInt. apply IPCts_uniform. }
  destruct Htail as [lt Hlt].
  destruct Hfin as [lf Hlf].
  exists (plus lf lt).
  eapply is_RInt_gen_Chasles; eassumption.
Qed.

(** Boundedness *)
Lemma uniform_density_range : ∀ x, 0 <= uniform_density x <= 1.
Proof.
  intros x. rewrite /uniform_density /Iverson.
  case_decide; lra.
Qed.

(** Total mass is 1 *)
Lemma uniform_density_zero_left x : x < 0 → uniform_density x = 0.
Proof.
  intros. rewrite /uniform_density /Iverson /Icc.
  rewrite Rmin_left; [|lra]. rewrite Rmax_right; [|lra].
  case_decide; lra.
Qed.

Lemma uniform_density_zero_right x : 1 < x → uniform_density x = 0.
Proof.
  intros. rewrite /uniform_density /Iverson /Icc.
  rewrite Rmin_left; [|lra]. rewrite Rmax_right; [|lra].
  case_decide; lra.
Qed.

Lemma uniform_density_one x : 0 <= x <= 1 → uniform_density x = 1.
Proof.
  intros. rewrite /uniform_density /Iverson /Icc.
  rewrite Rmin_left; [|lra]. rewrite Rmax_right; [|lra].
  case_decide; lra.
Qed.

Lemma RInt_gen_0_neg :
  RInt_gen (λ _ : R, 0) (Rbar_locally Rbar.m_infty) (at_point 0) = 0.
Proof.
  rewrite -(@RInt_gen_neg_change_of_var (λ _, 0)).
  - apply RInt_gen_0.
  - intros. apply ex_RInt_const.
  - intros. apply ex_RInt_const.
  - eapply (@ex_RInt_gen_neg_change_of_var_rev (fun _ : R => 0)).
    + intros. apply ex_RInt_const.
    + apply ex_RInt_gen_0.
Qed.

Lemma uniform_density_mass :
  RInt_gen uniform_density (Rbar_locally Rbar.m_infty) (Rbar_locally Rbar.p_infty) = 1.
Proof.
  rewrite -(@RInt_gen_Chasles R_CompleteNormedModule
    (Rbar_locally Rbar.m_infty) (Rbar_locally Rbar.p_infty) _ _
    uniform_density 0).
  3: { apply ex_RInt_gen_uniform_pos. }
  2: { apply ex_RInt_gen_uniform_neg. }
  rewrite (RInt_gen_ext_eq_Iio (f := uniform_density) (g := fun _ => 0)).
  3: { apply ex_RInt_gen_uniform_neg. }
  2: { intros. apply uniform_density_zero_left. done. }
  rewrite -(@RInt_gen_Chasles R_CompleteNormedModule
    (at_point 0) (Rbar_locally Rbar.p_infty) _ _
    uniform_density 1).
  3: { eapply ex_RInt_gen_ext_eq_Ioi;
       [intros; symmetry; apply uniform_density_zero_right; done
       |apply (ex_RInt_gen_0 1)]. }
  2: { rewrite ex_RInt_gen_at_point. apply IPCts_RInt, IPCts_uniform. }
  rewrite (RInt_gen_ext_eq_Ioi (f := uniform_density) (g := fun _ => 0)).
  3: { eapply ex_RInt_gen_ext_eq_Ioi;
       [intros; symmetry; apply uniform_density_zero_right; done
       |apply (ex_RInt_gen_0 1)]. }
  2: { intros. apply uniform_density_zero_right. done. }
  rewrite RInt_gen_0 RInt_gen_0_neg RInt_gen_at_point.
  2: { apply IPCts_RInt, IPCts_uniform. }
  rewrite (RInt_ext uniform_density (fun _ => 1)).
  2: { intros x [Hx1 Hx2]. apply uniform_density_one.
       rewrite Rmin_left in Hx1; [|lra]. rewrite Rmax_right in Hx2; [|lra]. lra. }
  rewrite RInt_const /scal /= /mult /plus /=. lra.
Qed.

Lemma uniform_density_RInt_gen_eq (F : R → R) {M}
    (Hnn : ∀ x, 0 <= F x <= M) (HP : IPCts F) :
  RInt_gen (fun x => uniform_density x * F x)
    (Rbar_locally Rbar.m_infty) (Rbar_locally Rbar.p_infty) = RInt F 0 1.
Proof.
  rewrite -(@RInt_gen_Chasles R_CompleteNormedModule
    (Rbar_locally Rbar.m_infty) (Rbar_locally Rbar.p_infty) _ _
    (fun x => uniform_density x * F x) 0).
  3: { admit. }
  2: { admit. }
  rewrite (RInt_gen_ext_eq_Iio
    (f := fun x => uniform_density x * F x) (g := fun _ => 0)).
  3: { admit. }
  2: { intros x Hx. rewrite uniform_density_zero_left; [ring|done]. }
  rewrite -(@RInt_gen_Chasles R_CompleteNormedModule
    (at_point 0) (Rbar_locally Rbar.p_infty) _ _
    (fun x => uniform_density x * F x) 1).
  3: { admit. }
  2: { admit. }
  rewrite (RInt_gen_ext_eq_Ioi
    (f := fun x => uniform_density x * F x) (g := fun _ => 0)).
  3: { admit. }
  2: { intros x Hx. rewrite uniform_density_zero_right; [ring|done]. }
  rewrite RInt_gen_0 RInt_gen_0_neg RInt_gen_at_point.
  2: { apply ex_RInt_mult. { apply IPCts_RInt, IPCts_uniform. } { apply IPCts_RInt. done. } }
  rewrite (RInt_ext (fun x => uniform_density x * F x) F).
  2: { intros x [Hx1 Hx2].
       rewrite Rmin_left in Hx1; [|lra]. rewrite Rmax_right in Hx2; [|lra].
       rewrite /uniform_density/Iverson/=.
       case_decide; try lra.
       exfalso.
       revert H.
       rewrite /Icc//=.
       rewrite Rmin_left; OK.
       rewrite Rmax_right; OK.
  }
  rewrite /plus//=.
  OK.
Admitted.

(** Main theorem: the uniform sampler correctly implements the CDF *)
Theorem uniform_cdf_prob Σ `{erisGpreS Σ} (σ : state) :
  ∀ B C : Z,
    prob (lim_exec (lazy_real_cdf_checker UnifSampler B C, σ))
      (fun x => bool_decide (x = #(-1)%Z)) =
    RInt_gen uniform_density (Rbar_locally Rbar.m_infty) (at_point (IZR B / powerRZ 2 C)).
Proof.
  intros B C.
  apply (@lazy_real_expr_adequacy_cdf_prob _ _ 1 UnifSampler σ uniform_density).
  - apply uniform_density_range.
  - apply IPCts_uniform.
  - apply ex_RInt_gen_uniform_neg.
  - apply ex_RInt_gen_uniform_pos.
  - iIntros (?? F [M HM] HI) "Hε".
    unfold UnifSampler.
    wp_bind (init _)%E.
    iApply wp_init; [done|].
    iIntros (v) "Hv".
    iApply (wp_lazy_real_presample_adv_comp E (R_ofUnif v) v _ (RInt F 0 1) F with "[-]"); auto.
    { intros r Hr. apply HM. }
    { apply (@RInt_correct R_CompleteNormedModule F 0 1), IPCts_RInt. done. }
    iFrame "Hv".
    iSplitL "Hε".
    { iApply ec_eq. { apply (@uniform_density_RInt_gen_eq F M). { intros; apply HM. } done. } iFrame. }
    iIntros (r) "(%Hr & Hε & Hr)".
    iApply (pgl_wp_wand with "[Hr]").
    { iApply (wp_R_ofUnif r with "Hr"). }
    iIntros (cont) "Happrox".
    iExists r. iFrame.
  - apply uniform_density_mass.
  - intros B' C'. apply (uniform_cdf_checker_terminates Σ σ B' C').
Admitted.

(** Closed theorem: instantiate with erisΣ *)
Theorem uniform_cdf_prob_closed (σ : state) :
  ∀ B C : Z,
    prob (lim_exec (lazy_real_cdf_checker UnifSampler B C, σ))
      (fun x => bool_decide (x = #(-1)%Z)) =
    RInt_gen uniform_density (Rbar_locally Rbar.m_infty) (at_point (IZR B / powerRZ 2 C)).
Proof.
  apply (uniform_cdf_prob erisΣ).
Qed.

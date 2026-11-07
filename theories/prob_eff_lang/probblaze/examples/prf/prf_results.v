From clutch.prob_eff_lang.probblaze.uc Require Import advantage.
From iris.algebra Require Import excl.
From iris.algebra.lib Require Import dfrac_agree.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_judgement sem_row syntax semantics proofmode valgroup adequacy mode compatibility.
From clutch.prob_eff_lang.probblaze.uc Require Import uc_systems uc_advantage uc_theorem.
From clutch.prob_eff_lang.probblaze.examples Require Import
  ske_sec_chan_def ske ske_sec_chan_common ske_sec_chan_typing advantage_ske_sec_chan
  fin_val_type fin_val_type_prod ske_prf dhke_common dhke_typing advantage_dhke_ske_sec_chan.
From clutch.prob_eff_lang.probblaze.examples.dhke Require Import dhke_def advantage_dhke.

From mathcomp Require finset.
Import fingroup.
Import fingroup.fingroup.

#[local] Open Scope factory_scope.

(** * The one-message secure channel with the PRF-based scheme

    [adv_SKE] bounds the channel advantage of [A] by the advantage of
    [RED_SKE A] against [enc_real]/[enc_ideal] of the scheme, and
    [adv_enc_prf] bounds that by the advantage against the PRF games. *)

Section prf_results.
  Context {vg: val_group}.
  Context {cg: clutch_group_struct}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.
  Context {vgg : @val_group_generator vg}.
  Context `{probblazeRGpreS Σ}.

  Lemma vg_fvt_nontriv : (2 ≤ fin_val_type.card (fin_val_type := vg_fvt))%nat.
  Proof using vgg. rewrite /fin_val_type.card /= -finset.cardsT vgG_card. lia. Qed.

  #[local] Notation n := (S n'').
  Context {nt mt : fin_val_type}.
  Context {ns : @fin_val_type_struct nt} {ms : @fin_val_type_struct mt}.
  Context {nonce : ∀ `{!probblazeRGS Σ}, @fin_val Σ _ nt ns} {msg : ∀ `{!probblazeRGS Σ}, @fin_val Σ _ mt ms}.
  Context {prf_struct : @PRF_struct vg_fvt nt mt vg_fvts ns ms}.
  Context {PRF_inst : ∀ `{H : !probblazeRGS Σ},
             @PRF Σ _ vg_fvt nt mt vg_fvts ns ms (vg_fv (Σ := Σ) (H := H)) (nonce _) (msg _) prf_struct}.
  Context `{!Inhabited (fvt_sort vg_fvts), !Inhabited (fvt_sort ns), !Inhabited (fvt_sort ms)}.

  Hypothesis nt_nonempty : (1 ≤ fin_val_type.card (fin_val_type := nt))%nat.
  Hypothesis mt_nontriv : (2 ≤ fin_val_type.card (fin_val_type := mt))%nat.

  Import valgroup_notation.

  #[local] Notation CIPHER := (λ (H: probblazeRGS Σ), @prod_fv Σ H nt mt ns ms (nonce H) (msg H)).
  #[local] Notation SKES := (@prf_sym_struct vg_fvt nt mt vg_fvts ns ms prf_struct _ _ _).
  #[local] Notation RED := (@red_prf nt mt ns ms).
  #[local] Notation PREAL := (@prf_real vg_fvt nt mt vg_fvts ns ms prf_struct).
  #[local] Notation PIDEAL := (@prf_ideal nt mt ns ms).
  #[local] Notation CT := (@prod_fvt nt mt).
  #[local] Notation CS := (@prod_fvts nt mt ns ms).
  #[local] Notation SKE_INST := (PRF_SKE (PRF_inst := PRF_inst _) vg_fvt_nontriv nt_nonempty mt_nontriv).
  #[local] Notation SC_REAL := (@REAL_SKE vg cg vgg mt CT ms CS SKES).
  #[local] Notation SC_IDEAL := (@SIM_IDEAL_SKE vg cg mt CT ms CS SKES).
  #[local] Notation REDC := (@RED_SKE vg cg vgg mt ms).

  (* The computational step is through one-shot oracles, so the statement is
     for single-session environments. *)
  Theorem adv_schan_prf A :
    (∀ `{!probblazeRGS Σ},
       ⊢ sem_val_typed A A (fac OS (τ_SKE (msg _) (CIPHER _)) → 𝔹)%T) →
    advantage A SC_REAL SC_IDEAL #true <=
      advantage (λ: "F", REDC A (RED "F")) PREAL PIDEAL #true.
  Proof using All.
    intros HA.
    etrans.
    { apply (adv_SKE (ske := SKES) (SKE := λ _, SKE_INST) OS). apply HA. }
    apply (adv_enc_prf (PRF_inst := PRF_inst)
             ltac:(pose proof vg_fvt_nontriv; lia) nt_nonempty mt_nontriv).
    - intros v. reflexivity.
    - intros ?. iApply sem_typed_val. iApply (RED_SKE_typed (SKE := SKE_INST) OS). iApply HA.
  Qed.

End prf_results.

(** * The composed protocol (DH key exchange followed by the channel)

    [dhke_ske_realises] bounds the advantage by a DDH term plus the advantage
    of [RED_SKE_DHKE A] against [enc_real]/[enc_ideal]; the latter is bounded
    by [adv_enc_prf]. *)
Section prf_results_comp.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.
  Context `{Hpre : probblazeRGpreS Σ}.
  Context {nt mt : fin_val_type}.
  Context {ns : @fin_val_type_struct nt} {ms : @fin_val_type_struct mt}.
  Context {nonce : ∀ `{!probblazeRGS Σ}, @fin_val Σ _ nt ns} {msg : ∀ `{!probblazeRGS Σ}, @fin_val Σ _ mt ms}.
  Context {prf_struct : @PRF_struct vg_fvt nt mt vg_fvts ns ms}.
  Context {PRF_inst : ∀ `{H : !probblazeRGS Σ},
             @PRF Σ _ vg_fvt nt mt vg_fvts ns ms (vg_fv (Σ := Σ) (H := H)) (nonce _) (msg _) prf_struct}.
  Context `{!Inhabited (fvt_sort vg_fvts), !Inhabited (fvt_sort ns), !Inhabited (fvt_sort ms)}.

  Hypothesis nt_nonempty : (1 ≤ fin_val_type.card (fin_val_type := nt))%nat.
  Hypothesis mt_nontriv : (2 ≤ fin_val_type.card (fin_val_type := mt))%nat.

  Import valgroup_notation.

  #[local] Notation CT := (@prod_fvt nt mt).
  #[local] Notation CS := (@prod_fvts nt mt ns ms).
  #[local] Notation CIPHER := (λ (H : probblazeRGS Σ), @prod_fv Σ H nt mt ns ms (nonce H) (msg H)).
  #[local] Notation SKES := (@prf_sym_struct vg_fvt nt mt vg_fvts ns ms prf_struct).
  #[local] Notation RED := (@red_prf nt mt ns ms).
  #[local] Notation PREAL := (@prf_real vg_fvt nt mt vg_fvts ns ms prf_struct).
  #[local] Notation PIDEAL := (@prf_ideal nt mt ns ms).
  #[local] Notation SKE_INST := (PRF_SKE (PRF_inst := PRF_inst _) (vg_fvt_nontriv (vgg := vgg)) nt_nonempty mt_nontriv).
  #[local] Notation REAL := (@REAL_DHKE_SKE vg cg vgg mt CT ms CS SKES).
  #[local] Notation IDEAL := (@IDEAL_DHKE_SKE mt ms).
  #[local] Notation SIM := (@SIM_DHKE_SKE vg cg vgg mt CT ms CS SKES).
  #[local] Notation DH_RED := (@RED_DHKE_SKE vg cg mt CT ms CS SKES).
  #[local] Notation ENC_RED := (@RED_SKE_DHKE vg cg vgg mt ms).

  Theorem adv_composition_prf A :
    (∀ `{!probblazeRGS Σ},
       ⊢ sem_val_typed A A (fac OS (τ_DHKE_SKE (vg := vg) (msg _) (CIPHER _)) → 𝔹)%T) →
    advantage A REAL (SIM ∘f IDEAL) #true <=
      advantage (DH_RED A) (DH_real (vg := vg) (cg := cg) (vgg := vgg))
                (DH_rand (vg := vg) (cg := cg) (vgg := vgg)) #true
      + advantage (λ: "F", ENC_RED A (RED "F")) PREAL PIDEAL #true.
  Proof using All.
    intros HA.
    etrans.
    - by apply (dhke_ske_realises (SKE := λ _, SKE_INST) OS).
    - apply Rplus_le_compat_l.
      apply (adv_enc_prf (PRF_inst := PRF_inst)
             ltac:(pose proof (vg_fvt_nontriv (vgg := vgg)); lia) nt_nonempty mt_nontriv).
      + intros v. reflexivity.
      + intros HRGS. rewrite /RED_SKE_DHKE. iApply sem_typed_val. iApply (RED_SKE_typed (SKE := SKE_INST) OS).
        change (SIM_DHKE ∘Fₚ "v")%fac with (fill (sim_ctx SIM_DHKE) "v").
        iApply ctx_adv_typed; first iApply HA. rewrite /τ_SKE /τ_DHKE_SKE.
        iApply (ctx_sim_typed OS SIM_DHKE (λ θ, hdl (cli (msg _)) θ) (oaleak (CIPHER _)) leakI aleak).
        iApply SIM_DHKE_typed_f.
  Qed.

End prf_results_comp.

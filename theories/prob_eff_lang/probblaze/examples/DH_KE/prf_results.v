From clutch.prob_eff_lang.probblaze Require Import advantage.
From iris.algebra Require Import excl.
From iris.algebra.lib Require Import dfrac_agree.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_judgement sem_row syntax semantics proofmode valgroup adequacy mode.
From clutch.prob_eff_lang.probblaze.typing Require Import types interp fundamental.
From clutch.prob_eff_lang.probblaze.examples.DH_KE Require Import
  ske_sec_chan_def ske_sec_chan_prf ske_sec_chan_ideal_prf ske ske_sec_chan_common ske_typing
  advantage_ske_schan fin_val_type fin_val_type_prod ske_prf
  ske_composition ske_composition_defs dhke_common ske_composition_typing advantage_ske_comp.

From mathcomp Require finset.
Import fingroup.
Import fingroup.fingroup.

(** * The one-message secure channel with the PRF-based scheme

    [adv_ske_schan] bounds the channel advantage of [A] by the advantage of
    [λ "enc", A (reduction "enc")] against [enc_real]/[enc_ideal] of the scheme, and
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

  #[local] Notation CIPHER := (λ `{!probblazeRGS Σ}, @prod_fv Σ _ nt mt ns ms (nonce _) (msg _)).
  #[local] Notation SKES := (@prf_sym_struct vg_fvt nt mt vg_fvts ns ms prf_struct _ _ _).
  #[local] Notation RED := (@red_prf nt mt ns ms).
  #[local] Notation PREAL := (@prf_real vg_fvt nt mt vg_fvts ns ms prf_struct).
  #[local] Notation PIDEAL := (@prf_ideal nt mt ns ms).
  #[local] Notation CT := (@prod_fvt nt mt).
  #[local] Notation CS := (@prod_fvts nt mt ns ms).
  #[local] Notation SC_REAL := (@sc_real vg cg vgg mt CT ms CS SKES).
  #[local] Notation SC_IDEAL := (@sc_ideal vg cg mt CT ms CS SKES).
  #[local] Notation REDC := (@reduction vg cg vgg mt ms).

  Theorem adv_schan_prf A :
    (∀ `{!probblazeRGS Σ},
       ⊢ sem_val_typed A A ((τsc (msg := msg _) (cipher := CIPHER _)) → 𝔹)%T) →
    advantage A SC_REAL SC_IDEAL #true <=
      advantage (λ: "F", (λ: "enc", A (REDC "enc")) (RED "F")) PREAL PIDEAL #true.
  Proof using All.
    intros HA.
    etrans.
    { apply (adv_ske_schan (ske := SKES)
               (SKE := λ _, PRF_SKE (PRF_inst := PRF_inst _) vg_fvt_nontriv nt_nonempty mt_nontriv)).
      apply HA. }
    apply (adv_enc_prf (PRF_inst := PRF_inst)
             ltac:(pose proof vg_fvt_nontriv; lia) nt_nonempty mt_nontriv).
    - intros v. reflexivity.
    - intros ?. iApply sem_typed_adv_red; [iApply HA|].
      iApply (reduction_val_typed
                (SKE := PRF_SKE (PRF_inst := PRF_inst _) vg_fvt_nontriv nt_nonempty mt_nontriv)).
  Qed.

End prf_results.

(** * The composed protocol (DH key exchange followed by the channel)

    [adv_composition_real] bounds the advantage by a DDH term plus the advantage of
    [λ "v", A (DHSIM_FKE_RED "v")] against [enc_real]/[enc_ideal]; the latter is
    bounded by [adv_enc_prf]. *)
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
  #[local] Notation CIPHER := (λ `{!probblazeRGS Σ}, @prod_fv Σ _ nt mt ns ms (nonce _) (msg _)).
  #[local] Notation SKES := (@prf_sym_struct vg_fvt nt mt vg_fvts ns ms prf_struct _ _ _).
  #[local] Notation RED := (@red_prf nt mt ns ms).
  #[local] Notation PREAL := (@prf_real vg_fvt nt mt vg_fvts ns ms prf_struct).
  #[local] Notation PIDEAL := (@prf_ideal nt mt ns ms).
  #[local] Notation SKE_INST := (PRF_SKE (PRF_inst := PRF_inst _) (vg_fvt_nontriv (vgg := vgg)) nt_nonempty mt_nontriv).
  #[local] Notation REAL := (REAL_CHAN_DHKE (vg := vg) (cg := cg) (vgg := vgg) (ske := SKES)).
  #[local] Notation IDEAL := (SIMSIMFCHAN (vg := vg) (cg := cg) (ske := SKES)).
  #[local] Notation DH_RED := (REAL_CHAN_DH_RED (vg := vg) (cg := cg) (ske := SKES)).
  #[local] Notation FKE_RED := (DHSIM_FKE_RED (vg := vg) (cg := cg) (vgg := vgg) (mt := mt) (ms := ms)).

  Let τ `{H : !probblazeRGS Σ} :=
    (ske_composition_defs.τ (ms := ms) (cs := CS) (msg := msg H) (cipher := CIPHER H) (mt := mt) (ct := CT)).

  Theorem adv_composition_prf A :
    (∀ `{!probblazeRGS Σ}, ⊢ sem_val_typed A A (τ → 𝔹)%T) →
    advantage A REAL IDEAL #true <=
      advantage (λ: "v", A (DH_RED "v")) (DH_real (vg := vg) (cg := cg) (vgg := vgg))
                (DH_rand (vg := vg) (cg := cg) (vgg := vgg)) #true
      + advantage (λ: "F", (λ: "v", A (FKE_RED "v")) (RED "F")) PREAL PIDEAL #true.
  Proof using All.
    intros HA.
    etrans.
    { apply (adv_composition_real (ske := SKES) (SKE := λ _, SKE_INST)). apply HA. }
    apply Rplus_le_compat_l.
    apply (adv_enc_prf (PRF_inst := PRF_inst)
             ltac:(pose proof (vg_fvt_nontriv (vgg := vgg)); lia) nt_nonempty mt_nontriv).
    - done. 
    - intros ?. iApply sem_typed_adv_red_expr; first iApply HA.
      iApply (DHSIM_FKE_RED_typed (SKE := SKE_INST)).
  Qed.

End prf_results_comp.

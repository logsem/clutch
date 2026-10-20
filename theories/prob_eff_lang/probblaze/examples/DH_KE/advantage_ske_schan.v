From clutch.prob_eff_lang.probblaze Require Import advantage.
From iris.algebra Require Import excl.
From iris.algebra.lib Require Import dfrac_agree.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_judgement sem_row syntax semantics proofmode valgroup adequacy mode.
From clutch.prob_eff_lang.probblaze.typing Require Import types interp fundamental.
From clutch.prob_eff_lang.probblaze.examples.DH_KE Require Import ske_sec_chan_def ske_sec_chan_prf ske_sec_chan_ideal_prf ske.

Import fingroup.
Import fingroup.fingroup.

Section adv_schan.
  Context {vg: val_group}.
  Context {cg: clutch_group_struct}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.
  Context {vgg : @val_group_generator vg}.
  Context `{probblazeRGpreS Σ}.
  #[local] Notation n := (S n'').
  Context {mt ct : fin_val_type}.
  Context {ms : @fin_val_type_struct mt} {cs : @fin_val_type_struct ct}.
  (* key space is valgroup *)
  Context {ske : @SYM_struct vg_fvt vg_fvts mt ms ct cs}.
  (* the semantic side of the scheme: the key space is [vg_fv], the message and
     cipher spaces are abstract.  [enc_sem]/[dec_sem] take and return VALUES of
     those spaces, so nothing below ever decodes a key or a message. *)
  Context {msg : ∀ `(!probblazeRGS Σ), @fin_val Σ _ mt ms} {cipher : ∀ `(!probblazeRGS Σ), @fin_val Σ _ ct cs}.
  Context {SKE : ∀ `{H : !probblazeRGS Σ}, @SYM Σ _ vg_fvt mt ct vg_fvts ms cs (vg_fv (Σ := Σ) (H := H)) (msg H) (cipher H) ske}.

  Import valgroup_notation.
  
  Lemma adv_sc_real_game1 A : 
    (∀ `{!probblazeRGS Σ}, 
       ⊢ sem_val_typed A A ((τsc (msg := msg _) (cipher := cipher _)) → 𝔹)%T) →
    nonneg (advantage A sc_real game1 #true) = 0.
  Proof using All.
    intros HA. eapply sem_typed_advantage; first apply HA. split.
    - intros Hrgs. eapply sc_real_game1.
    - intros Hrgs. apply game1_sc_real.
  Qed. 

  Lemma adv_game2_sc_ideal A : 
    (∀ `{!probblazeRGS Σ}, 
       ⊢ sem_val_typed A A ((τsc (msg := msg _) (cipher := cipher _)) → 𝔹)%T) →
    nonneg (advantage A game2 sc_ideal #true) = 0.
  Proof using All.
    intros HA. eapply sem_typed_advantage; first apply HA. split.
    - intros Hrgs. apply game2_sc_ideal. 
    - intros Hrgs. apply sc_ideal_game2.
  Qed. 
 
  Lemma adv_game1_game2 A : 
    (∀ `{!probblazeRGS Σ}, 
       ⊢ sem_val_typed A A ((τsc (msg := msg _) (cipher := cipher _)) → 𝔹)%T) →
    nonneg (advantage A game1 game2 #true) <= advantage (λ: "enc", A ((reduction (mt := mt) (ms := ms)) "enc")) (enc_real_tape ske) (enc_ideal ske) #true.
  Proof using All.
    intros HA. unfold game1, game2.
    apply advantage_reduction_expr.
    intros ?. eexists _,_.
    split; first done.
    split; last split.
    - admit.                    (* reduction well-tyepd *)
    - admit.                    (* enc_real well-typed *)
    - admit.                    (* enc_ideal well_typed *)
  Admitted. 

  Lemma adv_ske_schan A :
    (∀ `{!probblazeRGS Σ}, 
       ⊢ sem_val_typed A A ((τsc (msg := msg _) (cipher := cipher _)) → 𝔹)%T) →
    nonneg (advantage A sc_real sc_ideal #true) <= advantage (λ: "enc", A ((reduction (mt := mt) (ms := ms)) "enc")) (enc_real ske) (enc_ideal ske) #true.
  Proof using All.
    intros HA. 
    eapply advantage_triangle.
    - right. by apply adv_sc_real_game1.
    - eapply advantage_triangle.
      + by apply adv_game1_game2.
      + right. by apply adv_game2_sc_ideal.
      + rewrite Rplus_0_r. eapply (advantage_triangle _ _ (enc_real ske)).
        * right. eapply sem_typed_advantage_expr.
          -- admit.             (* A ∘ reduction well-typed *)
          -- split.
             ++ iIntros (?). apply (enc_real_tape_enc_real (ske := SKE H0)) .
             ++ iIntros (?). apply (enc_real_enc_real_tape (ske := SKE H0)).
        * done.
        * done. 
    - by rewrite !Rplus_0_l. 
  Admitted. 
  
End adv_schan.

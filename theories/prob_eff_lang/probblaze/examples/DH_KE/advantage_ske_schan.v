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
  Context {msg_card : nat}.
  Context {cipher_card : nat}.
  Instance ske_params : SYM_params := {
      card_key := n;
      card_message := msg_card;
      card_cipher := cipher_card }.
  Context {ske_struct : @SYM_struct ske_params}.
  Context {ske : ∀ `{!probblazeRGS Σ}, SYM}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.

  Import valgroup_notation.

  Lemma adv_sc_real_game1 A : 
    (∀ `{!probblazeRGS Σ}, 
       ⊢ sem_val_typed A A (τsc → 𝔹)%T) →
    nonneg (advantage A sc_real game1 #true) = 0.
  Proof using All.
    intros HA. eapply sem_typed_advantage; first apply HA. split.
    - intros Hrgs. apply sc_real_game1. 
    - intros Hrgs. apply game1_sc_real.
  Qed. 

  Lemma adv_game2_sc_ideal A : 
    (∀ `{!probblazeRGS Σ}, 
       ⊢ sem_val_typed A A (τsc → 𝔹)%T) →
    nonneg (advantage A game2 sc_ideal #true) = 0.
  Proof using All.
    intros HA. eapply sem_typed_advantage; first apply HA. split.
    - intros Hrgs. apply game2_sc_ideal. 
    - intros Hrgs. apply sc_ideal_game2.
  Qed. 
 
  Lemma adv_game1_game2 A : 
    (∀ `{!probblazeRGS Σ}, 
       ⊢ sem_val_typed A A (τsc → 𝔹)%T) →
    nonneg (advantage A game1 game2 #true) <= advantage (λ: "enc", A (reduction (msg_card := msg_card) (cipher_card := cipher_card) "enc")) enc_real_tape enc_ideal #true.
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
       ⊢ sem_val_typed A A (τsc → 𝔹)%T) →
    nonneg (advantage A sc_real sc_ideal #true) <= advantage (λ: "enc", A (reduction (msg_card := msg_card) (cipher_card := cipher_card) "enc")) enc_real enc_ideal #true.
  Proof using All.
    intros HA. 
    eapply advantage_triangle.
    - right. by apply adv_sc_real_game1.
    - eapply advantage_triangle.
      + by apply adv_game1_game2.
      + right. by apply adv_game2_sc_ideal.
      + rewrite Rplus_0_r. eapply advantage_triangle.
        * right. eapply sem_typed_advantage_expr.
          -- admit.             (* A ∘ reduction well-typed *)
          -- split.
             ++ iIntros (?). apply enc_real_tape_enc_real.
             ++ iIntros (?). apply enc_real_enc_real_tape.
        * done.
        * done. 
    - by rewrite !Rplus_0_l. 
  Admitted. 
  
End adv_schan.

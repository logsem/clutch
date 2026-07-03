From clutch.prob_eff_lang.probblaze Require Import advantage.
From iris.algebra Require Import excl.
From iris.algebra.lib Require Import dfrac_agree.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_judgement sem_row syntax semantics proofmode valgroup.
From clutch.prob_eff_lang.probblaze Require Import OT_Rcorrupt_thunk definition_thunk_receiver_corrupt adequacy. 
Import fingroup. 

Section adv_dhke.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.
  Context `{probblazeRGpreS Σ}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.
  #[local] Notation n := (S (S n'')).
  Context `{n_prime : is_true (prime.prime n)}.

  Notation "'𝔾'" := sem_ty_group.   
  Definition τ_ot `{probblazeRGS Σ} := (∀ᵣ θ, τC θ ⊸ ((((𝔾 × 𝔾) × (𝔾 × 𝔾)) -{ θ }-> 𝟙) × (𝟙 -{ θ }-> Option (𝔾 × 𝔾)))
            -{ ¡[OS] θ}-∘ 𝟙)%T.


  Theorem adv_ot_rc A (ε : R) :
    (∀ `{!probblazeRGS Σ},⊢ sem_val_typed A A (τ_ot → 𝔹)%T) →
    advantage A OT_SIM_FOT_thunk (λ: "f" "effs", F_CRS (λ: "doCRS", OT_Real_Receiver_Corrupted "f" ("effs", "doCRS"))%E)%V #true <= 3/n. 
  Proof using n_prime G inG2 H. 
    intros. eapply sem_typed_advantage_aff; try done; last split.
    - apply Rcomplements.Rdiv_le_0_compat; first lra.
      apply lt_0_INR. lia.
    - intros Hrgs. by unshelve iApply OT_ideal_real.
    - intros Hrgs. by unshelve iApply OT_real_ideal.
  Qed.

  

End adv_dhke.

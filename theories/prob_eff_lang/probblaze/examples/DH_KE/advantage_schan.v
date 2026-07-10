From clutch.prob_eff_lang.probblaze Require Import advantage.
From iris.algebra Require Import excl.
From iris.algebra.lib Require Import dfrac_agree.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_judgement sem_row syntax semantics proofmode valgroup.
From clutch.prob_eff_lang.probblaze Require Import xor sec_channel_def sec_channel_prf adequacy.


Section adv_schan.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.
  Context `{probblazeRGpreS Σ}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.
  Context (lka1 lka2 klk1 klk2 : label).
  Variable xor_struct : XOR (Key := S (S n'')) (Support := S (S n'')).

  Definition τ_CHAN `{!probblazeRGS Σ}
      :=  (∀ᵣ θ__L ,(∀ᵣ θₕ, (((⊤ × (sem_ty_sum 𝟙 𝟙)) -{ θₕ }-> (Option ⊤)) × ((sem_ty_sum 𝟙 𝟙) -{ θₕ }-> (Option  ⊤))) -{ sem_row_union  θₕ θ__L }-> 𝟙) ⊸ (*type of client*)
               (* (∀ᵣ θ₁,  (((⊤ × (𝟙 + 𝟙)) -{ θ₁ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ₁ }-> Option ⊤)) ⊸ ((𝟙 + 𝟙) -{ θ₁ }-> Option ⊤) -{ sem_row_union θ₁ θ__L }-∘ 𝟙))%T.*) 
                    (∀ᵣ θ₁, ∀ᵣ θ₂,  (((⊤ × (𝟙 + 𝟙)) -{ θ₁ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ₁ }-> Option ⊤)) ⊸ ((𝟙 + 𝟙) -{ θ₂ }-> Option ⊤) -{ sem_row_union (sem_row_union θ₁ θ₂) θ__L }-∘ 𝟙))%T.

  Lemma adv_SCHAN A :
    (∀ `{!probblazeRGS Σ}, 
       ⊢ sem_val_typed A A (τ_CHAN → 𝔹)%T) →
    nonneg (advantage A (λ: "f", REAL_CHAN xor_struct "f")%V (λ: "f", CHAN_SIM (F_CHAN "f"))%V #true) = 0%R.
  Proof.
  Abort.
  
End adv_schan.

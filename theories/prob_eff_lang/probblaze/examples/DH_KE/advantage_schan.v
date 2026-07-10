From clutch.prob_eff_lang.probblaze Require Import advantage.
From iris.algebra Require Import excl.
From iris.algebra.lib Require Import dfrac_agree.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_judgement sem_row syntax semantics proofmode valgroup.
From clutch.prob_eff_lang.probblaze Require Import xor sec_channel_def sec_channel_prf adequacy.

Import fingroup.
Import fingroup.fingroup.

Section adv_schan.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.
  Context `{probblazeRGpreS Σ}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.
  (* Context (lka1 lka2 klk1 klk2 : label). *)
  Let Key := S (S n'').
  Let Support := S (S n'').
  Context {xor_struct : XOR (Key := Key) (Support := Support)}.
  Context `{X : ∀ `{!probblazeRGS Σ}, XOR_spec (Key := Key) (Support := Support) (H := xor_struct)}.

  Variable group_xor_sem : vgG -> vgG -> vgG.
  (* actual BITWISE xor has both left and right inverse, so this assumption is a valid spec.*)
  Hypothesis Bij_xor_sem : ∀ g1 g2 : vgG, group_xor_sem (group_xor_sem g1 g2) g2 = g1.
  Hypothesis Bij_xor_sem_l : ∀ g1 g2 : vgG, group_xor_sem g1 (group_xor_sem g1 g2) = g2.
  Hypothesis vg_int_xor_sem : ∀ `{!probblazeRGS Σ}, ∀ g1 g2 : vgG, vg_of_int_sem (xor_sem (int_of_vg_sem g1) (int_of_vg_sem g2)) = Some (group_xor_sem g1 g2 ).
  Variable log__g : vgG -> fin (S (S n'')).
  Hypothesis Val_log : ∀ x : vgG, (g ^+(log__g x))%g = x.
  Hypothesis Bij_log : forall m : vgG, @Bij (fin (S (S n''))) (fin (S (S n''))) (λ n, log__g (group_xor_sem m (g ^+n))).
  Hypothesis Bdd_int_vg : ∀ `{!probblazeRGS Σ}, ∀ g : vgG, (int_of_vg_sem g < S (S (S n'')))%nat.

  Import valgroup_notation.

  Definition τ_CHAN `{!probblazeRGS Σ}
      :=  (∀ᵣ θ__L ,(∀ᵣ θₕ, (((𝔾 -{ θₕ }-> 𝟙) × (𝟙 -{ θₕ }-> (Option  𝔾))) -{ sem_row_union  θₕ θ__L }-∘ 𝟙)) ⊸ (*type of client*)
                 (∀ᵣ θ₁, ∀ᵣ θ₂,  (((𝔾 × (𝟙 + 𝟙)) -{ θ₁ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ₁ }-> Option 𝟙)) ⊸ (((𝟙 + 𝟙) -{ θ₂ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ₂ }-> Option 𝟙)) -{ sem_row_union θ₁ (sem_row_union θ₂ θ__L) }-∘ 𝟙))%T.

  Lemma adv_SCHAN A :
    (∀ `{!probblazeRGS Σ}, 
       ⊢ sem_val_typed A A (τ_CHAN → 𝔹)%T) →
    nonneg (advantage A (R_CHAN xor_struct) (λ: "f", CHAN_SIM_lazy (F_CHAN "f"))%V #true) = 0%R.
  Proof using All.
    intros. eapply sem_typed_advantage; eauto. split.
    - intros Hrgs. by unshelve eapply R_I_SCHAN.
    - intros Hrgs. by unshelve eapply I_R_SCHAN.
  Qed. 
  
End adv_schan.

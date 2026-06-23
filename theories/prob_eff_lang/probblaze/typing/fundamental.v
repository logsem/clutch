From iris.base_logic Require Export invariants.
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext. 
From clutch.prob_eff_lang.probblaze Require Import metatheory notation syntax semantics sem_judgement sem_def.
From clutch.prob_eff_lang.probblaze Require Import primitive_laws compatibility.
From clutch.prob_eff_lang.probblaze Require Import types.
From clutch.prob_eff_lang.probblaze Require Import interp logic.

Section fundamental.
  Context `{!probblazeRGS Σ}.

Lemma ctx_dom_env_dom x Γ :
  ∀ η μ δ ξ, x ∉ ctx_dom Γ → x ∉ env_dom ((λ '(s, τ), (s, interp._ty η μ δ τ ξ)) <$> Γ).
Proof. 
  iIntros (???? Hnin).
  induction Γ as [| (y, κ) Γ' IH]; first set_solver; simpl.
Admitted. 

Theorem fundamental Δ Γ1 e ρ τ Γ2 :
  Δ .| Γ1 ⊢ₜ e : ρ : τ ⊣ Γ2 → ⊢ 〈Δ;Γ1〉 ⊨ₜ e ≤log≤ e : ρ : τ ⫤ Γ2
  with fundamental_val v τ :
    ⊢ᵥ v : τ → ⊢ ⊨ᵥ v ≤log≤ v : τ
  with fundamental_pure Γ e τ :
    Γ ⊢ₚ e : τ → ⊢ bin_log_pure_related Γ e e τ.
Proof.
  - intros Ht. destruct Ht; iIntros (??????).
    + iApply sem_typed_var.
    + iApply sem_typed_val; by iApply fundamental_val.
    + rewrite fmap_app. iApply sem_typed_oval.
      by iApply fundamental_pure.
    + iApply sem_typed_pair_gen; [admit|apply fundamental in Ht1 as Ht|apply fundamental in Ht2 as Ht]; 
        iPoseProof Ht as "Ht"; iSpecialize ("Ht" $! _ _ _ _ _ _); iApply "Ht".
    + iApply sem_typed_fst_expr. apply fundamental in Ht. 
        iPoseProof Ht as "Ht"; iSpecialize ("Ht" $! _ _ _ _ _ _); iApply "Ht".
    + iApply sem_typed_snd_expr. apply fundamental in Ht. 
        iPoseProof Ht as "Ht"; iSpecialize ("Ht" $! _ _ _ _ _ _); iApply "Ht".
    + iApply sem_typed_left_inj.
      apply fundamental in Ht. 
      iPoseProof Ht as "Ht"; iSpecialize ("Ht" $! _ _ _ _ _ _); iApply "Ht".
    + iApply sem_typed_right_inj.
      apply fundamental in Ht. 
      iPoseProof Ht as "Ht"; iSpecialize ("Ht" $! _ _ _ _ _ _); iApply "Ht".
    + iApply sem_typed_match.
      * destruct x; [|eapply ctx_dom_env_dom]; apply H. 
      * destruct x; [|eapply ctx_dom_env_dom]; apply H0. 
      * destruct y; [|eapply ctx_dom_env_dom]; apply H1. 
      * destruct y; [|eapply ctx_dom_env_dom]; apply H2. 
      * apply fundamental in Ht1. 
        iPoseProof Ht1 as "Ht"; iSpecialize ("Ht" $! _ _ _ _ _ _); iApply "Ht". 
      * apply fundamental in Ht2. 
        iPoseProof Ht2 as "Ht"; iSpecialize ("Ht" $! _ _ _ _ _ _). destruct x; iApply "Ht". 
      * apply fundamental in Ht3. 
        iPoseProof Ht3 as "Ht"; iSpecialize ("Ht" $! _ _ _ _ _ _). destruct y; iApply "Ht". 
Admitted. 

End fundamental.

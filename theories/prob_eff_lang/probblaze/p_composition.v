From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import agree excl auth frac excl_auth.
From iris.algebra.lib Require Import dfrac_agree.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode
 spec_rules spec_ra class_instances.
From clutch.prob_eff_lang.probblaze Require Import tactics.
From clutch.prob_eff_lang.probblaze Require Import sem_types sem_row sem_sig sem_judgement sem_def valgroup.

(*Import fingroup.

Import fingroup.fingroup.


*)
Import valgroup_tactics.
Section parallel_composition.
  Context `{probblazeRGS Σ}.

  (*Fixpoint list_args_app (f : val) (op_l : list val) : val :=
    match: op_l with
    | nil => f
    | op_x :: op_{xs} => (f op_x)
    end.*)
  
  
(*Definition left_composition (f_x f_y : val) : val := λ: "f" "op_x1" "op_x2" "op_y1" "op_y2",
                                                                                                       f_x (f_y "f" "op_y1" "op_y2") "op_x1" "op_x2".*)

  (*Definition left_composition (f_x f_y : val) : val := λ: "f", f_x (λ: "op_x1" "op_x2", (f_y (λ: "op_y1" "op_y2", ("f" "op_x1" "op_x2" "op_y1" "op_y2")))).*)

  (*Definition left_composition (f_x f_y : val) "e1" "e2" "e3" :=
    λ: "f" "op_x1" "op_x2" "op_y1" "op_y2",
    effect*)

  (*Definition s_chan_composition (f_x f_y : val) :=
    λ: "f" "op_x1" "op_x2" "op_y1" "op_y2",
      effect "channel"
      let: "doSend" := (λ: "m", do: (EffName "channel") (Send "m")) in
      let: "doRecv" := (λ: "m", do: (EffName "channel") (Recv "m")) in
      (*effect "schannel"
      let: "doSecSend" := (λ: "m", do: (EffName "schannel") (Send "m")) in
      let: "doSecRecv" := (λ: "m", do: (EffName "schannel") (Recv "m")) in *)
      effect "getKey"
      let: "doGK" := (λ: "party", do: (EffName "getKey") "party") in
      f_x "channel" "doSend" "doRecv" (f_y "getKey" "doGK" "f" "op_y1" "op_y2") "op_x1" "op_x2".*)

  (* r_x are effect operations raised by the functionality f_x, and c_x are effect operations
     handled by f_x.*) 
  Definition left_composition : val :=
    λ: "F₁" "F₂" "f" "r₁" "r₂",
      "F₁" (λ: "h₁",
             "F₂" (λ: "h₂", "f" "h₁" "h₂") "r₂") "r₁".
  
 
  Definition right_composition : val :=
    λ: "F₁" "F₂" "f" "r₁" "r₂",
      (left_composition "F₂" "F₁" "f" "r₂" "r₁").
  
 Notation " F₁ ||ₗ F₂" := (left_composition F₁ F₂)%V (at level 10).

 Notation "F₁ ||ᵣ F₂" := (right_composition F₁ F₂)%V (at level 10).

  About sem_ty_row_forall.
  About sem_ty_type_forall.
  Definition τ := ( ∀ᵣ θ, ∀ₜ α ,α ⊸ 𝟙)%T.
  
  Definition τ__f := (∀ᵣ θ₁, ∀ᵣ θ₂, ∀ₜ τ₁, ∀ₜ τ₂, τ₁ ⊸ τ₂ -{ sem_row_union θ₁ θ₂ }-> 𝟙)%T.
  Definition τ__F :=  (∀ᵣ θ₁, ∀ᵣ θ₂, ∀ₜ τ₁, τ₁ ⊸ (∀ᵣ θ₃,  ∀ₜ τ₂, τ₂ -{ θ₃ }-> 𝟙))%T.
  Definition τₚ :=  (τ__F ⊸ τ__F ⊸ τ__f ⊸ (∀ᵣ θ₁,  ∀ₜ τ₁, τ₁ ⊸ (∀ᵣ θ₂,  ∀ₜ τ₂ , τ₂ -{sem_row_union θ₁ θ₂}-> 𝟙)))%T.
  Lemma brel_left_comp (F₁ F₂ F : val) :
   (* ⊢ sem_val_typed f₁ f₂ τ__f  -∗*)
    ⊢ sem_val_typed F₁ F₂ τ__F -∗
    sem_val_typed F F τ__F -∗
    sem_typed [] (F ||ₗ F₁) (F ||ₗ F₂) ⊥ (τ__f ⊸ (∀ᵣ θ₁,  ∀ₜ τ₁, τ₁ ⊸ (∀ᵣ θ₂,  ∀ₜ τ₂ , τ₂ -{sem_row_union θ₁ θ₂}-> 𝟙)))%T [].
  Proof.
  Admitted.
  
  Lemma func_comp_left (F1 F2 : expr) (F : val) τ τ' τ'':
    is_closed_expr ∅ F1 →
    is_closed_expr ∅ F2 →
    ⊢ (∀ θ : sem_row Σ, sem_typed [] F1 F2 ⊥ (τ θ ⊸ τ' θ)%T []) -∗
    (∀ θ : sem_row Σ, sem_val_typed F F (τ'' θ ⊸ τ θ)%T) -∗
    sem_val_typed (λ: "f", F1 (F "f")) (λ: "f", F2 (F "f")) (∀ᵣ θ, τ'' θ ⊸ τ' θ)%T.
  Proof.
    iIntros (HF1closed HF2closed) "#HFF #HF". rewrite /sem_val_typed /sem_typed //=.
    iIntros (???) "!# Hτ'' /=".
    (* iDestruct ("HF" $! θ ∅) as "#HFθ". *)
    iDestruct ("HF" with "Hτ''") as "HFτ".
    brel_pures'.
    erewrite !subst_is_closed; try done.
    iApply (brel_bind' [_] [_]); [iApply traversable_to_iThy_nil|].
    iApply (brel_wand with "HFτ").
    iIntros (??) "!# Hvv".
    iApply (brel_bind' [_] [_]); [iApply traversable_to_iThy_nil|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS _ _ [] [] with "[][HFF]");
      [iApply to_iThy_le_bot| |].
    { iDestruct ("HFF" $! θ ∅) as "#HFθ". rewrite !subst_map_empty.
      by iApply "HFθ". }
    simpl. iIntros (??) "(Hff&_)". by iApply "Hff".
  Qed. 
    

End parallel_composition.

Notation " F₁ ||ₗ F₂" := (left_composition F₁ F₂) (at level 10).

Notation "F₁ ||ᵣ F₂" := (right_composition F₁ F₂) (at level 10).

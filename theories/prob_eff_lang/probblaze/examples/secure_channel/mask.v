From clutch Require Import base.
From clutch.prob_eff_lang.probblaze Require Import logic proofmode. 
From clutch.prob_eff_lang.probblaze.typing Require Import types.

Class Mask (car : Type) (dval : car → val) :=
  { mask : val
  ; τmask : type
  ; mask_typed : ⊢ᵥ mask : (τmask ⇾ τmask ⇾ τmask)%ty
  ; dval_inj : Inj eq eq dval
  ; mask_sem : car → car → car
  ; mask_closed : is_closed_val mask
  } .

#[export] Hint Resolve mask_closed : core.

Class Mask_struc `{!probblazeRGS Σ} `{Mask} :=
  { MASK_CORRECT_L := ∀ E K (k m : car) e X R,
      (BREL (fill K (of_val (dval (mask_sem k m)))) ≤ e @ E <|X|> {{R}})
      -∗ BREL (fill K (mask (dval k) (dval m))) ≤ e @ E <|X|> {{R}}
  ; MASK_CORRECT_R := ∀ E K (k m : car) e X R,
      (BREL e ≤ (fill K (of_val (dval (mask_sem k m)))) @ E <|X|> {{R}})
      -∗ BREL e ≤ (fill K (mask (dval k) (dval m))) @ E <|X|> {{R}}
  ; mask_correct_l : MASK_CORRECT_L
  ; mask_correct_r : MASK_CORRECT_R
  ; mask_bij (m : car) :: Bij (λ k, mask_sem k m)
  ; mask_involutive (k : car) : Involutive eq (mask_sem k)
  }.

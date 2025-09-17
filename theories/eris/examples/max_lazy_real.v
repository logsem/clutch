From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt RInt_analysis AutoDerive.
From clutch.eris Require Import infinite_tape lazy_real.
Set Default Proof Using "Type*".
#[local] Open Scope R.

Section max_lazy_real.
Import Hierarchy.

Context `{!erisGS Σ}.


(* Triangle integral argument *)
Lemma max_presample_RInt ε (F : R → R) (Hint : is_RInt (λ x : R, 2 * x * F x) 0 1 ε) :
    is_RInt (λ r : R, RInt (λ x : R, F (Rmax r x)) 0 1) 0 1 ε.
Proof. Admitted.

(* Composition with a continuous function etc. *)
Lemma comp_max_integrability (r1 : R) (F : R → R) (H : ex_RInt F 0 1) (Hr1 : (0 <= r1 <= 1)%R) :
  ex_RInt (F ∘ Rmax r1) 0 1.
Proof. Admitted.

(* TODO: Can I reduce away the integrability of F? *)
Lemma wp_lazy_real_presample_max_adv_comp E e v1 v2 Φ (ε : R) (F : R -> R) (HF : ex_RInt F 0 1) :
  to_val e = None →
  (forall r, 0 <= r <= 1 → (0 <= F r)%R) ->
  is_RInt (fun x => 2 * x * F x)%R 0 1 ε →
  lazy_real_uninit v1 ∗
  lazy_real_uninit v2 ∗
  ↯ ε ∗
  (∀ r1 r2 : R, ↯ (F (Rmax r1 r2)%R) ∗ lazy_real v1 r1 ∗ lazy_real v2 r2 -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
Proof.
  (* First: do the proof but without the integration lemma to get the right form. *)
  iIntros (Hv Hr Hint) "(Hv1 & Hv2 & Hε & Hwp)".
  iDestruct "Hv1" as (l1 α1) "(-> & Hchunk1 & Htape1)".
  iDestruct "Hv2" as (l2 α2) "(-> & Hchunk2 & Htape2)".
  set ε1 : R → R := fun r => (RInt (F ∘ (Rmax r)) 0 1).
  set ε2 : R → R → R := fun x y => F (Rmax x y).
  wp_apply (wp_presample_unif_adv_comp _ _ α1 _ ε ε1 with "[-]"); first done.
  { intros x Hx.
    apply RInt_ge_0; first nra.
    { apply comp_max_integrability; done. }
    intros y Hy.
    apply Hr; constructor.
    { apply <- Rmax_Rle; nra. }
    { apply Rmax_lub; nra. }
  }
  { apply max_presample_RInt; done. }
  iFrame "∗".
  iIntros (r1) "(Hε & (% & Hα1 & %))".
  wp_apply (wp_presample_unif_adv_comp _ _ α2 _ (ε1 r1) (ε2 r1) with "[-]"); first done.
  { intros x Hx.
    apply Hr; constructor.
    { apply <- Rmax_Rle; nra. }
    { apply Rmax_lub; last nra.
      rewrite -H.
      have Hrange := seq_bin_to_R_range f.
      nra.
    }
  }
  { apply (RInt_correct (ε2 r1) 0 1).
    (* Integrability side condition *)
    unfold ε2.
    replace (λ y : R, F (Rmax r1 y)) with (F ∘ (Rmax r1)); last done.
    apply comp_max_integrability; first done.
    have Hrange := seq_bin_to_R_range f.
    nra. }
  iFrame.
  iIntros (r2) "(Hε & (% & Hα2 & %))".
  iApply ("Hwp" $! r1 r2); iSplitL "Hε"; first iFrame.
  iSplitL "Hchunk1 Hα1"; iFrame; iExists _; iPureIntro; split_and!; eauto.
Qed.

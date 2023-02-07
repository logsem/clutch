From stdpp Require Import namespaces.
From iris.base_logic Require Import invariants na_invariants.
From self.program_logic Require Import weakestpre ectxi_language.
From self.prob_lang Require Import proofmode primitive_laws spec_rules lang notation lang.
From self.logrel Require Import model rel_rules rel_tactics adequacy.
From self.typing Require Import types contextual_refinement soundness.
From self.prelude Require Import base stdpp_ext.
Set Default Proof Using "Type*".

Definition xor b1 b2 : expr :=
  let not b := (if: b then #false else #true)%E in
  if: b1 then not b2 else b2.
Definition xor_sem b1 b2 :=
  if b1 then negb b2 else b2.

Definition ideal : expr := λ:"msg", flip #().
Definition real : expr := λ:"msg", let: "k" := flip #() in xor "k" "msg".

Section logical_ref.
  Context `{!prelogrelGS Σ}.

  Lemma refines_couple_flips_lr f `{Bij bool bool f} K K' E A :
      (∀ (b : bool), REL fill K (Val #b) << fill K' (Val #(f b)) @ E : A)
    ⊢ REL fill K (flip #()) << fill K' (flip #()) @ E : A.
  Proof.
    iIntros "Hcnt".
    rewrite refines_eq /refines_def.
    iIntros (K2) "[#Hs Hspec] Hnais /=".
    wp_apply wp_bind.
    wp_apply wp_couple_flip_flip; [done|].
    rewrite -fill_app.
    iFrame "Hs Hspec".
    iIntros (b) "Hspec".
    iApply wp_value.
    rewrite /= fill_app.
    iSpecialize ("Hcnt" with "[$Hspec $Hs] Hnais").
    wp_apply (wp_mono with "Hcnt").
    iIntros (v) "[% ([? ?] &?&?)]".
    iExists _. iFrame.
  Qed.

  Global Instance xor_inj_1 : forall b, Inj (=) (=) (xor_sem b).
  Proof. intros [] [] [] ; auto. Qed.

  Global Instance xor_surj_1 : forall b, Surj (=) (xor_sem b).
  Proof. intros [] [] ; (by exists true) || by exists false. Qed.

  Global Instance bij_xor : forall b, Bij (xor_sem b).
  Proof. constructor ; apply _. Qed.

  Lemma real_ideal_rel :
    ⊢ REL real << ideal : lrel_bool → lrel_bool.
  Proof.
    rewrite /real /ideal.
    rel_arrow_val.
    iIntros (msg1 msg2) "Hmsg".
    rel_pures_l. rel_pures_r.
    iDestruct "Hmsg" as "[%b [-> ->]]".
    rel_bind_r (flip _)%E.
    rel_bind_l (flip _)%E.
    unshelve iApply (refines_couple_flips_lr (xor_sem b)).
    simpl.
    iIntros (k).
    rel_pures_l.
    rewrite /xor_sem.
    destruct k ; rel_pures_l.
    all: destruct b; rel_pures_l. all: rel_values.
  Qed.

  Lemma ideal_real_rel :
    ⊢ REL ideal << real : lrel_bool → lrel_bool.
  Proof.
    rewrite /real /ideal.
    rel_arrow_val.
    iIntros (msg1 msg2) "Hmsg".
    rel_pures_l. rel_pures_r.
    iDestruct "Hmsg" as "[%b [-> ->]]".
    rel_bind_r (flip _)%E.
    rel_bind_l (flip _)%E.
    unshelve iApply (refines_couple_flips_lr (xor_sem b)).
    simpl.
    iIntros (k).
    rel_pures_r.
    rewrite /xor_sem.
    destruct k ; rel_pures_r.
    all: destruct b; rel_pures_r. all: rel_values.
  Qed.
End logical_ref.

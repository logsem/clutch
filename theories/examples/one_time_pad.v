From clutch.program_logic Require Import weakestpre ectxi_language.
From clutch.prob_lang Require Import proofmode spec_ra spec_rules spec_tactics lang notation.
From clutch.logrel Require Import model rel_rules rel_tactics.
From clutch.prelude Require Import base stdpp_ext.
From clutch.lib Require Import flip. 
Set Default Proof Using "Type*".

Definition xor b1 b2 : expr :=
  let not b := (if: b then #false else #true)%E in
  if: b1 then not b2 else b2.
Definition xor_sem b1 b2 :=
  if b1 then negb b2 else b2.

Ltac foldxor := assert (forall b2, (if: _ then (if: b2 then #false else #true) else b2)%E = (xor _ _)) as -> by easy.

Definition ideal : expr := λ:"msg", flip.
Definition real : expr := λ:"msg", let: "k" := flip in xor "msg" "k".

Section logical_ref.
  Context `{!clutchRGS Σ}.

  Global Instance xor_invol_1 : forall b, Involutive eq (xor_sem b) | 2.
  Proof. intros [] [] => //. Qed.

  Global Instance xor_inj_1 : forall b, Inj (=) (=) (xor_sem b) | 2.
  Proof. intros. apply cancel_inj. Qed.

  Global Instance xor_surj_1 : forall b, Surj (=) (xor_sem b) | 2.
  Proof. intros. apply cancel_surj. Qed.

  Global Instance bij_xor : forall b, Bij (xor_sem b) | 2.
  Proof. constructor ; apply _. Qed.

  Lemma xor_tp E (b1 b2 : bool) :
    ↑specN ⊆ E → ⊢ ∀ K, refines_right K (xor #b1 #b2) ={E}=∗ refines_right K (#(xor_sem b1 b2)).
  Proof.
    destruct b1, b2 ; iIntros ; tp_pures ; iModIntro ; done.
  Qed.

  Lemma xor_wp (b1 b2 : bool) :
    ⊢ (WP xor #b1 #b2 {{v, ⌜v = #(xor_sem b1 b2)⌝}})%I.
  Proof.
    rewrite /xor /xor_sem /negb. destruct b1, b2 ; wp_pures ; done.
  Qed.

  Lemma xor_xor_sem (b1 b2 : bool) :
    ⊢ REL xor #b1 #b2 << #(xor_sem b1 b2) : lrel_bool.
  Proof.
    rewrite /xor /xor_sem /negb. destruct b1, b2 ; rel_pures_l ; rel_values ; done.
  Qed.

  Lemma real_ideal_rel :
    ⊢ REL real << ideal : lrel_bool → lrel_bool.
  Proof.
    rewrite /real /ideal.
    rel_arrow_val.
    iIntros (msg1 msg2) "Hmsg".
    rel_pures_l. rel_pures_r.
    foldxor.
    iDestruct "Hmsg" as "[%b [-> ->]]".
    rel_apply (refines_couple_flip_flip (xor_sem b)).
    simpl.
    iIntros (k).
    rel_pures_l.
    foldxor.
    iApply xor_xor_sem.
  Qed.

  Lemma ideal_real_rel :
    ⊢ REL ideal << real : lrel_bool → lrel_bool.
  Proof.
    rewrite /real /ideal.
    rel_arrow_val.
    iIntros (msg1 msg2) "Hmsg".
    rel_pures_l. rel_pures_r.
    iDestruct "Hmsg" as "[%msg [-> ->]]".
    rel_apply (refines_couple_flip_flip (xor_sem msg)) => /=.
    iIntros (k).
    rel_pures_r.
    foldxor.
    unshelve rel_apply_r (refines_steps_r $! (xor_tp _ _ _ _)) ; [easy|].
    rewrite cancel.
    rel_values.
  Qed.

End logical_ref.

(** * Derived laws for a fair coin flip *)
From stdpp Require Import namespaces.
From iris.proofmode Require Import
  coq_tactics ltac_tactics sel_patterns environments reduction proofmode.
From clutch.coneris Require Import coneris lib.conversion.

Definition flipL : val := λ: "e", int_to_bool (rand("e") #1%nat).
Definition flip : expr := (flipL #()).
Definition allocB := alloc #1%nat.

Definition tapeB (bs : list bool) : tape := (1; bool_to_fin <$> bs).
Definition bool_tape `{conerisGS Σ} l bs : iProp Σ := l ↪ tapeB bs.

Notation "l ↪B bs" := (bool_tape l bs)
  (at level 20, format "l  ↪B  bs") : bi_scope.

Section specs.
  Context `{conerisGS Σ}.
  
  Lemma tape_conversion_bool_nat α bs:
    α ↪B (bs) ⊣⊢ α ↪N (1; (λ b:bool, if b then 1 else 0) <$> bs).
  Proof.
    rewrite /bool_tape/tapeB.
    iSplit.
    - iIntros. iExists (bool_to_fin <$> bs).
      iFrame.
      iPureIntro.
      rewrite -list_fmap_compose.
      f_equal.
      apply functional_extensionality_dep; intros []; done.
    - iIntros "[%[%?]]".
      replace fs with (bool_to_fin <$> bs); first done.
      generalize dependent fs.
      induction bs as [|a].
      + simpl. intros.
        by erewrite fmap_nil_inv.
      + intros fs H0. destruct fs; first done.
        * rewrite !fmap_cons in H0.
          simplify_eq.
          apply IHbs in H1.
          rewrite fmap_cons.
          f_equal; last done.
          destruct a; subst.
          -- inv_fin t; first done; intros t.
             by inv_fin t.
          -- inv_fin t; first done; intros t; by inv_fin t.
  Qed.
  
  Lemma tape_conversion_nat_bool α ns:
    α ↪N (1;ns) ⊢ α ↪B ((λ n, n=?1) <$> ns).
  Proof.
    iIntros "[%fs [%?]]".
    rewrite tape_conversion_bool_nat.
    iExists fs.
    iFrame.
    subst.
    iPureIntro.
    rewrite -!list_fmap_compose.
    induction fs as [|x]; first done.
    rewrite !fmap_cons. f_equal; last done.
    inv_fin x; first done; intros x.
    inv_fin x; first done; intros x.
    inv_fin x.
  Qed. 

  Lemma wp_allocB_tape E :
    {{{ True }}} allocB @ E {{{ α, RET #lbl:α; α ↪B [] }}}.
  Proof. iIntros (Φ) "_ HΦ". iApply wp_alloc_tape; first done.
         iModIntro. iIntros. erewrite tape_conversion_nat_bool. simpl.
         by iApply "HΦ".
  Qed.

  Lemma wp_flip E :
    {{{ True }}} flip @ E {{{ (b : bool), RET #(LitBool b); True }}}.
  Proof.
    iIntros (Φ) "_ HΦ". rewrite /flip/flipL.
    wp_pures.
    wp_bind (rand(_) _)%E.
    wp_apply (wp_rand 1 with "[//]").
    iIntros (?) "_ /=".
    wp_apply (wp_int_to_bool with "[//]").
    iIntros "_".
    by iApply "HΦ".
  Qed.

  Lemma wp_flipL E α b bs :
    {{{ ▷ α ↪B (b :: bs) }}} flipL #lbl:α @ E {{{ RET #(LitBool b); α ↪B bs }}}.
  Proof.
    iIntros (Φ) ">Hl HΦ". rewrite /flip/flipL.
    wp_pures.
    wp_bind (rand(_) _)%E.
    rewrite tape_conversion_bool_nat; simpl.
    wp_apply (wp_rand_tape 1 with "Hl").
    iIntros "[Hl _] /=".
    wp_apply (wp_int_to_bool with "[//]").
    iIntros "_".
    destruct b; rewrite Z_to_bool_of_nat.
    - rewrite nat_to_bool_neq_0; last lia.
      iApply "HΦ".
      rewrite tape_conversion_bool_nat. iFrame.
    - rewrite nat_to_bool_eq_0.
      iApply "HΦ".
      rewrite tape_conversion_bool_nat. iFrame.
  Qed.


  Lemma wp_flipL_empty E α :
    {{{ ▷ α ↪B [] }}} flipL #lbl:α @ E {{{ b, RET #(LitBool b); α ↪B [] }}}.
  Proof.
    iIntros (Φ) ">Hl HΦ". rewrite /flip/flipL.
    wp_pures.
    wp_bind (rand(_) _)%E.
    erewrite tape_conversion_bool_nat.
    wp_apply (wp_rand_tape_empty with "Hl").
    iIntros (n) "[Hl _] /=".
    wp_apply (wp_int_to_bool with "[//]").
    iIntros "_".
    iApply "HΦ".
    by rewrite tape_conversion_nat_bool. 
  Qed.


Global Opaque tapeB.
End specs.

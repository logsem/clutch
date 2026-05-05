From iris.proofmode Require Import proofmode.
From clutch.delay_prob_lang Require Import notation urn_subst. 
From clutch.elton Require Import weakestpre primitive_laws.

Set Default Proof Using "Type".

Section rupd_lemmas.
  Context `{!eltonGS Σ}.

  Lemma promote_urn_label (l:loc) (z:Z):
    l ↪ urn_unif {[z]} -∗
    rupd (λ x, x = LitV $ LitInt z) (l ↪ urn_unif {[z]}) (LitV $ LitLbl l).
  Proof.
    iIntros "H".
    rewrite rupd_unseal/rupd_def.
    iIntros (?) "[? Hu]".
    iSplit; last iFrame.
    iDestruct (ghost_map_lookup with "Hu [$H]") as "%Hlookup_b".
    iIntros (? Hlookup).
    eapply urns_f_distr_lookup in Hlookup as [?[H1 H2]] ; last done; last done.
    iPureIntro. destruct!/=.
    simpl. eexists _; split; last done.
    rewrite H1. simpl. set_unfold in H2. by subst.
  Qed. 
  
  Lemma promote_simple v P:
    is_simple_val v = true -> P -∗
    rupd (λ x, x = v) (P) v.
  Proof.
    iIntros (Hsimple) "HP".
    rewrite rupd_unseal/rupd_def.
    iIntros (?) "[? Hu]".
    iSplit; last iFrame.
    iPureIntro.
    intros.
    eexists _; split; last done.
    by apply  is_simple_val_urn_subst.
  Qed.

  Lemma promote_frame P Q v ϕ :
    rupd ϕ P v -∗ Q -∗ rupd ϕ (P ∗ Q) v.
  Proof.
    iIntros "H1 H2".
    rewrite rupd_unseal/rupd_def.
    iIntros (?) "?".
    iDestruct ("H1" with "[$]") as "[% [??]]".
    by iFrame.
  Qed.

  Lemma promote_add P (z1 z2: Z) v1 v2:
    (P -∗ rupd (λ x, x= LitV (z1)%Z) P (LitV (v1)%V)) -∗
    (P -∗ rupd (λ x, x= LitV (z2)%Z) P (LitV (v2)%V)) -∗
    P -∗
    rupd (λ x, x= LitV (z1 +z2)%Z) P (LitV (v1 +ᵥ v2)%V).
  Proof.
    iIntros "H1 H2 HP".
    rewrite rupd_unseal/rupd_def.
    iIntros (?) "?".
    iDestruct ("H1" with "[$][$]") as "[%H1 [??]]".
    iDestruct ("H2" with "[$][$]") as "[%H2 [??]]".
    iFrame.
    iPureIntro.
    intros ? Hlookup.
    apply H1 in Hlookup as H1'.
    destruct H1' as [? [H1' ?]].
    rewrite bind_Some in H1'.
    destruct H1' as [? [H1' ?]].
    apply H2 in Hlookup as H2'.
    destruct H2' as [? [H2' ?]].
    rewrite bind_Some in H2'.
    destruct H2' as [? [H2' ?]].
    destruct!/=.
    eexists _; split; last done.
    by rewrite H1' H2'.
  Qed.
  
  Lemma promote_neg P (b: bool) v:
    (P -∗ rupd (λ x, x= LitV (b)%Z) P (LitV (v)%V)) -∗
    P -∗
    rupd (λ x, x= LitV (negb b)%Z) P (LitV (NegOp' v)%V).
  Proof. 
    iIntros "H1 HP".
    rewrite rupd_unseal/rupd_def.
    iIntros (?) "?".
    iDestruct ("H1" with "[$][$]") as "[%H1 [??]]".
    iFrame.
    iPureIntro.
    intros ? Hlookup.
    apply H1 in Hlookup as H1'.
    destruct H1' as [? [H1' ?]].
    rewrite bind_Some in H1'.
    destruct H1' as [? [H1' ?]].
    destruct!/=.
    eexists _; split; last done.
    by rewrite H1'.
  Qed.

  Lemma promote_prod P v1 v2 v1' v2':
    (P -∗ rupd (λ x, x= v1') P ((v1)%V)) -∗
    (P -∗ rupd (λ x, x= v2') P ( (v2)%V)) -∗
    P -∗
    rupd (λ x, x=  (v1', v2')%V) P (v1, v2).
  Proof. 
    iIntros "H1 H2 HP".
    rewrite rupd_unseal/rupd_def.
    iIntros (?) "?".
    iDestruct ("H1" with "[$][$]") as "[%H1 [??]]".
    iDestruct ("H2" with "[$][$]") as "[%H2 [??]]".
    iFrame.
    iPureIntro.
    intros ? Hlookup.
    apply H1 in Hlookup as H1'.
    destruct H1' as [? [H1' ?]].
    apply H2 in Hlookup as H2'.
    destruct H2' as [? [H2' ?]].
    destruct!/=.
    eexists _; split; last done.
    by rewrite H1' H2'.
  Qed.

  
  (* We dont have a rupd for expression, since we dont
     have examples using it.
     But here below is what promote-rec would possibly look like
   *)
  Definition rupd_expr (P: _ -> Prop) Q e : iProp Σ:=
    (∀ σ1, state_interp σ1 -∗ 
           ⌜∀ f, (urns_f_distr (urns σ1) f > 0)%R -> ∃ e', urn_subst_expr f e = Some e' /\ P e'⌝ ∗ (Q ∗ state_interp σ1)).
  
  Lemma promote_rec P e e' f x:
    (P -∗ rupd_expr (λ x, x= e') P (e)) -∗
    P -∗
    rupd (λ x', x'= RecV f x e') P (RecV f x e).
  Proof. 
    iIntros "H1 HP".
    rewrite rupd_unseal/rupd_def.
    rewrite /rupd_expr.
    iIntros (?) "?".
    iDestruct ("H1" with "[$][$]") as "[%H1 [??]]".
    iFrame.
    iPureIntro.
    intros ? Hlookup.
    apply H1 in Hlookup as H1'.
    destruct H1' as [? [H1' ?]].
    subst. 
    destruct!/=.
    eexists _; split; last done.
    by rewrite H1'.
  Qed. 
End rupd_lemmas. 

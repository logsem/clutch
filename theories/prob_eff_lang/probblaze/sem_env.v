
From iris.proofmode Require Import base tactics classes.

From stdpp Require Import base gmap.

From clutch.prob_eff_lang.probblaze Require Import sem_def mode sem_row sem_types syntax primitive_laws notation.


Definition env_mbang {Σ} (m : mode) (Γ : env Σ) := map (λ xτ, (xτ.1, sem_ty_mbang m xτ.2)) Γ.

Notation "![ m ] Γ" := (env_mbang m Γ) (at level 10) : sem_env_scope.

Section env_lemmas_base.
  
  Context {Σ : gFunctors}.

  Implicit Types Γ Γ₁ Γ₂ Γ₃ Δ : env Σ.
  Implicit Types τ τ₁ τ₂ : sem_ty Σ.

  Lemma env_dom_nil :
    env_dom (Σ:= Σ) [] = [].
  Proof. done. Qed.

  Lemma env_dom_cons x τ Γ :
    env_dom ((x, τ) :: Γ) = x :: env_dom Γ.
  Proof. done. Qed.
  
  Lemma env_dom_app Γ₁ Γ₂ :
    env_dom (Γ₁ ++ Γ₂) = env_dom Γ₁ ++ env_dom Γ₂.
  Proof. by rewrite -map_app. Qed.
  
  Lemma env_sem_typed_empty γ : ([] : env Σ) ⊨ₑ γ = True%I.
  Proof. done. Qed.
  
  Lemma env_sem_typed_cons  x τ Γ' γ : 
    (x, τ) :: Γ' ⊨ₑ γ = ((∃ v1 v2, ⌜ γ !! x = Some (v1, v2) ⌝ ∗ τ v1 v2) ∗ Γ' ⊨ₑ γ)%I.
  Proof. done. Qed.

  Lemma env_sem_typed_insert Γ γ (x : string) v :
    x ∉ (env_dom Γ) →
     Γ ⊨ₑ γ ⊣⊢  Γ ⊨ₑ (binder_insert x v γ).
  Proof.
    intros Helem. 
    iInduction Γ as [|[y τ] Γ'] "IH";
      first (iSplit; iIntros; by rewrite env_sem_typed_empty).
    assert (x ≠ y).
    { rewrite env_dom_cons in Helem.
      destruct (not_elem_of_cons (env_dom Γ') x y) as [[ ] _]; done. }
    rewrite !env_sem_typed_cons; iSplit; iIntros "Henv";
    iDestruct ("Henv") as "((% & % & %Hγ & Hw) & HΓ')".
    - iSplitL "Hw".
      + iExists _. iIntros "{$Hw} !%". 
        destruct (decide (y = x)) as [->|]. 
        { destruct Helem. rewrite env_dom_cons. apply elem_of_list_here. }
        by rewrite lookup_insert_ne.
      + iApply "IH"; last done. iPureIntro. 
        destruct (not_elem_of_cons (env_dom Γ') x y) as [[ ] _]; done.
    - iSplitL "Hw".
      + iExists _,_.  iIntros "{$Hw} !%". 
        destruct (decide (y = x)) as [->|]. 
        { destruct Helem. rewrite env_dom_cons. apply elem_of_list_here. }
        by rewrite lookup_insert_ne in Hγ.
      + iApply "IH"; last done. iPureIntro. 
        destruct (not_elem_of_cons (env_dom Γ') x y) as [[ ] _]; done.
  Qed.
  
  Lemma env_sem_typed_delete Γ γ (x : string) :
    x ∉ (env_dom Γ) →
     Γ ⊨ₑ γ ⊣⊢ Γ ⊨ₑ (binder_delete x γ).
  Proof.
    intros Helem. 
    iInduction Γ as [|[y τ] Γ'] "IH";
      first (iSplit; iIntros; by rewrite env_sem_typed_empty).
    assert (x ≠ y).
    { rewrite env_dom_cons in Helem.
      destruct (not_elem_of_cons (env_dom Γ') x y) as [[ ] _]; done. }
    rewrite !env_sem_typed_cons; iSplit; iIntros "Henv";
    iDestruct ("Henv") as "((% & % & %Hγ & Hw) & HΓ')".
    - iSplitL "Hw".
      + iExists _. iIntros "{$Hw} !% /=". 
        by rewrite lookup_delete_ne.
      + iApply "IH"; last done. iPureIntro. 
        destruct (not_elem_of_cons (env_dom Γ') x y) as [[ ] _]; done.
    - iSplitL "Hw".
      + iExists _,_.  iIntros "{$Hw} !%". 
        destruct (decide (y = x)) as [->|]. 
        { destruct Helem. rewrite env_dom_cons. apply elem_of_list_here. }
        simpl in Hγ.
        by rewrite lookup_delete_ne in Hγ.
      + iApply "IH"; last done. iPureIntro. 
        destruct (not_elem_of_cons (env_dom Γ') x y) as [[ ] _]; done.
  Qed.
  
  Lemma env_sem_typed_app Γ₁ Γ₂ γ :
     Γ₁ ++ Γ₂ ⊨ₑ γ ⊣⊢  Γ₁ ⊨ₑ γ ∗ Γ₂ ⊨ₑ γ.
  Proof. 
    iInduction Γ₁ as [|[y τ] Γ₁'] "IH". 
    { iSplit; [iIntros; by iFrame|iIntros "[_ H] {$H}"]. }
    iSplit; rewrite !env_sem_typed_cons; iIntros "HΓ₁₂". 
    - iDestruct "HΓ₁₂" as "($ & HΓ₁'₂)". by iApply "IH".
    - iDestruct ("HΓ₁₂") as "[[Hτ HΓ₁'] HΓ₂]".
      rewrite -/app. iFrame. iApply ("IH" with "[HΓ₁' HΓ₂]").
      iFrame.
  Qed.

End env_lemmas_base.

Global Ltac solve_sem_typed_insert :=
  rewrite env_sem_typed_insert; try (simplify_eq; done); progress iFrame "%#∗".

Global Ltac solve_sem_typed_insert_inv :=
  rewrite -env_sem_typed_insert; try (simplify_eq; done); progress iFrame "%#∗".

Global Ltac solve_env := 
  repeat (
    done ||
    iIntros || 
    iExists _ || 
    iPureIntro ||
    iSplit || 
    (progress iFrame "%#∗") ||
    (progress simpl) ||
    apply lookup_insert || 
    rewrite lookup_insert_ne || 
    apply lookup_delete ||
    rewrite env_sem_typed_empty ||
    rewrite env_sem_typed_cons ||
    solve_sem_typed_insert ||
    solve_sem_typed_insert_inv
    ).

Section env_lemmas_set_operations.

  Context {Σ : gFunctors}.

  Implicit Types Γ Γ₁ Γ₂ Γ₃ Δ : env Σ.
  Implicit Types τ τ₁ τ₂ : sem_ty Σ.

  Lemma env_sem_typed_union Γ ws γ :
     Γ ⊨ₑ γ ⊢  Γ ⊨ₑ (γ ∪ ws).
  Proof. 
    iIntros "HΓ". iInduction Γ as [|[x τ] Γ'] "IH"; first done.
    rewrite !env_sem_typed_cons.
    iDestruct "HΓ" as "[(% & % & %Hrw & Hx) HΓ']".
    rewrite -/env_sem_typed. 
    iSplitL "Hx"; [|by iApply "IH"].
    iExists _,_; iFrame; iPureIntro.
    by apply lookup_union_Some_l.
  Qed.
  (* TODO: move to an appropriate file -- all from base.v in Affect*)
  (* ------------------------------------------------------------ *)
  Global Instance delete_gmap_multiple K A `{ Countable K, EqDecision K, Delete K (gmap K A) } : 
  Delete (list K) (gmap K A) :=
  (fix delete_mult xs vs :=
      match xs with
        [] => vs
      | x :: xxs => delete x (delete_mult xxs vs)
      end).

  Lemma delete_list_nil {A} (vs : gmap string A) :
    delete [] vs = vs.
  Proof. done. Qed.

  Lemma delete_list_cons {A} x (xs : list string) (vs : gmap string A) :
    delete (x :: xs) vs = delete x (delete xs vs).
  Proof. done. Qed.

  Lemma delete_list_elem_of {K} (Γ : list string) x (vs : gmap string K) :
    x ∈ Γ → delete Γ vs = delete x (delete Γ vs).
  Proof.
    intros Helem. induction Γ.
    { by destruct (not_elem_of_nil x). }
    destruct (decide (a = x)); first subst. 
    { by rewrite delete_idemp. }
    rewrite delete_commute -IHΓ; first done.
    by destruct (elem_of_cons Γ x a) as [[] _].
  Qed.
  

  Lemma subset_cons_elem {A} (x : A) xs ys : 
    x :: xs ⊆ ys → x ∈ ys.
  Proof.
    intros ?.
    destruct (elem_of_subseteq (x :: xs) ys) as [H' _].
    apply H'; first done. rewrite elem_of_cons; by left. 
  Qed.
  
  Lemma subset_cons {A} (x : A) xs ys : 
    x :: xs ⊆ ys → xs ⊆ ys.
  Proof.
    intros Hseq. 
    apply (elem_of_subseteq xs ys). intros z Hz.
    apply (elem_of_subseteq (x :: xs) ys); first done.
    apply elem_of_cons. by right.
  Qed.

  Lemma lookup_difference_delete {A} z (vs ws : gmap string A) :
    (vs ∖ delete z ws) !! z = vs !! z.
  Proof.
    destruct (vs !! z) eqn:H.
    - rewrite (difference_delete _ _ _ a); last done.
      by rewrite lookup_insert.
    - apply lookup_difference_None; auto.
  Qed.

  Lemma disjoint_cons_not_elem {A} (x : A) xs ys : 
    x :: xs ## ys → x ∉ ys.
  Proof.
    intros ?.
    destruct (elem_of_disjoint (x :: xs) ys) as [H' _].
    intros ?. eapply H'; try done. 
    rewrite elem_of_cons; by left. 
  Qed.

  Lemma disjoint_cons {A} (x : A) xs ys : 
    x :: xs ## ys → xs ## ys.
  Proof.
    intros Hseq. 
    apply (elem_of_disjoint xs ys). intros z Hz.
    apply (elem_of_disjoint (x :: xs) ys); first done.
    apply elem_of_cons. by right.
  Qed.

  Lemma lookup_delete_not_elem {A} (ys : list string) x (vs : gmap string A) : 
    x ∉ ys → delete ys vs !! x = vs !! x.
  Proof.
    intros ?.
    induction ys; first done.
    rewrite delete_list_cons.
    edestruct (not_elem_of_cons ys) as [[] _]; first done.
    rewrite lookup_delete_ne; last done.
    by apply IHys. 
  Qed.

  Lemma lookup_difference_delete_ne {A} i j (vs ws : gmap string A) :
    i ≠ j → (vs ∖ ws) !! j = (vs ∖ delete i ws) !! j.
  Proof.
    intros H. destruct (ws !! j) eqn:H'.
    - destruct (lookup_difference_None vs ws j) as [_ ->]; last auto. 
      destruct (lookup_difference_None vs (delete i ws) j) as [_ ->]; first done.
      right. rewrite lookup_delete_ne; auto.
    - destruct (vs !! j) eqn:?.
      { destruct (lookup_difference_Some vs ws j a) as [_ ->]; auto.
        destruct (lookup_difference_Some vs (delete i ws) j a) as [_ ->]; first done.
        split; first done. rewrite lookup_delete_ne; auto. }
      destruct (lookup_difference_None vs ws j) as [_ ->]; auto.
      destruct (lookup_difference_None vs (delete i ws) j) as [_ ->]; auto.
  Qed.

  Lemma lookup_union_delete_disjoint {A} (xs : list string) x (vs ws : gmap string A) :
    x ∉ xs → (vs ∪ ws ∖ delete xs ws) !! x = vs !! x.
  Proof.
    intros ?.
    induction xs.
    { by rewrite delete_list_nil map_difference_diag map_union_empty. }
    edestruct (not_elem_of_cons xs) as [[] _]; first done. 
    rewrite delete_list_cons. 
    specialize (IHxs H1).
    destruct (vs !! x) eqn:H'.
    { by apply lookup_union_Some_l. }
    apply lookup_union_None; split; first done.
    rewrite -lookup_difference_delete_ne; last done.
    erewrite lookup_union_None in IHxs. tauto.
  Qed.
  
  (* ------------------------------------------------------------ *)

  Lemma env_sem_typed_delete_union Γ Δ ws γ :
    env_dom Γ ⊆ env_dom Δ →
     Γ ⊨ₑ γ ⊣⊢ Γ ⊨ₑ (delete (env_dom Δ) ws ∪ γ).
  Proof.
    intros ?. iSplit.
    - iInduction Γ as [|[x τ] Γ'] "IH"; first solve_env. 
      rewrite !env_sem_typed_cons.
      iIntros "/= [(% & % & %Hrw & Hw) HΓ']".
      assert (Hseq' : env_dom Γ' ⊆ env_dom Δ). 
      { eapply subset_cons. by erewrite <- env_dom_cons. }
      assert (x ∈ (env_dom Δ)).
      { eapply subset_cons_elem. by erewrite <- env_dom_cons. }
      iSplitL "Hw";[| iApply ("IH" with "[] HΓ'"); by iPureIntro].
      iExists _,_. iFrame. iPureIntro. 
      rewrite (delete_list_elem_of _ x); last done.
      rewrite lookup_union_r; first done.
      apply lookup_delete.
    - iInduction Γ as [|[x τ] Γ'] "IH"; first solve_env.
      rewrite !env_sem_typed_cons.
      iIntros "[(% & % & %Hrw & Hτ) HΓ']".
      iSplitL "Hτ".
      + iExists _, _. iIntros "{$Hτ} !%".
        rewrite -(lookup_union_r (delete (env_dom Δ) ws)); first done.
        rewrite (delete_list_elem_of _ x); first (apply lookup_delete).
        eapply subset_cons_elem. by erewrite <- env_dom_cons.
      + iApply "IH"; last done.
        iPureIntro. eapply subset_cons. by erewrite <- env_dom_cons.
  Qed.

  Lemma env_sem_typed_difference_delete Γ Δ γ ws :
    env_dom Γ ⊆ env_dom Δ → Γ ⊨ₑ γ ⊣⊢ Γ ⊨ₑ (γ ∖ delete (env_dom Δ) ws).
  Proof.
    intros ?.
    iInduction Γ as [|[x τ] Γ'] "IH"; first (iSplit; solve_env).
    assert (Hseq' : env_dom Γ' ⊆ env_dom Δ).
    { eapply subset_cons. by erewrite <- env_dom_cons. }
    assert (x ∈ (env_dom Δ)).
    { eapply subset_cons_elem. by erewrite <- env_dom_cons. }
    rewrite !env_sem_typed_cons; iSplit;
    iIntros "/= [(% & % & %Hrw & Hτ) HΓ']".
    - iSplitL "Hτ".
      + iExists _,_. iFrame. iPureIntro. 
        rewrite (delete_list_elem_of _ x); last done. 
        by rewrite lookup_difference_delete. 
      + iApply ("IH" with "[] HΓ'"); eauto. 
    - iSplitL "Hτ".
      + iExists _,_. iFrame. iPureIntro. 
        rewrite (delete_list_elem_of _ x) in Hrw; 
          [|eapply subset_cons_elem; by erewrite <- env_dom_cons].
        by rewrite lookup_difference_delete in Hrw.
      + iApply ("IH" with "[] HΓ'"); eauto. 
  Qed.

  Lemma env_sem_typed_delete_disjoint Γ Δ γ  :
    env_dom Γ ## env_dom Δ → Γ ⊨ₑ γ ⊣⊢ Γ ⊨ₑ (delete (env_dom Δ) γ).
  Proof. 
    iIntros (?).
    iInduction Γ as [|[x τ] Γ'] "IH"; first (iSplit; solve_env).
    assert (Hseq' : env_dom Γ' ## env_dom Δ)
      by (eapply disjoint_cons; by erewrite <- env_dom_cons);
      assert (x ∉ (env_dom Δ)) by 
        (eapply disjoint_cons_not_elem; by erewrite <- env_dom_cons).
    rewrite !env_sem_typed_cons; iSplit;
    iIntros "/= [(% & % & %Hrw & Hτ) HΓ']".
    - iSplitL "Hτ".
      + iExists _,_. iIntros "{$Hτ} !%".
        by rewrite lookup_delete_not_elem.
      + by iApply "IH".
    - iSplitL "Hτ".
      + iExists _,_. iIntros "{$Hτ} !%".
        by rewrite lookup_delete_not_elem in Hrw.
      + by iApply "IH".
  Qed.

  Lemma env_sem_typed_union_difference_delete Γ Δ γ ws :
    env_dom Γ ## env_dom Δ → Γ ⊨ₑ (γ ∪ ws ∖ (delete (env_dom Δ) ws)) ⊢ Γ ⊨ₑ γ.
  Proof. 
    intros ?.
    iInduction Γ as [|[x τ] Γ'] "IH"; first solve_env.
    rewrite !env_sem_typed_cons.
    iIntros "/= [(% & % & %Hrw & Hτ) HΓ']".
    assert (Hseq' : env_dom Γ' ## env_dom Δ)
      by (eapply disjoint_cons; by erewrite <- env_dom_cons).
    assert (x ∉ (env_dom Δ)) by 
      (eapply disjoint_cons_not_elem; by erewrite <- env_dom_cons).
    iSplitL "Hτ".
    + iExists _,_. iIntros "{$Hτ} !%".
      by rewrite lookup_union_delete_disjoint in Hrw.
    + by iApply "IH".
  Qed.
  
End env_lemmas_set_operations.

Section multi_env.
  
  Context `{!probblazeGS Σ}.

  Class MultiE {Σ} (Γ : env Σ) := {
    multi_env : ⊢ Γ ≤ₑ (![ MS ] Γ%E)
  }.

  Global Instance multi_env_persistent (Γ : env Σ) `{! MultiE Γ } :
    ∀ γ, Persistent (Γ ⊨ₑ γ).
  Proof. 
    intros ?. rewrite /Persistent. iIntros "HΓ". 
    inv MultiE0. iDestruct (multi_env0 with "HΓ") as "H!Γ". clear multi_env0.
    iInduction Γ as [|[x τ] Γ'] "IH".
    { iIntros "!# //". }
    rewrite /env_mbang map_cons /= -/(env_mbang MS Γ').
    iDestruct "H!Γ" as "(% & %Heq & Hτ. & HΓ'.)".
    iDestruct ("IH" with "HΓ'.") as "#HΓ'".
    rewrite /sem_ty_mbang /=. iDestruct "Hτ." as "#Hτ".
    iModIntro. iExists vv. iSplit; first done. iFrame "#".
  Qed.

  Lemma multi_env_persistent_inv (Γ : env Σ) :
    □ (∀ γ, Γ ⊨ₑ γ -∗ □ (Γ ⊨ₑ γ)) -∗ Γ ≤ₑ (![MS ] Γ).
  Proof. 
    iIntros "#H !# % HΓ.".
    iDestruct ("H" with "HΓ.") as "#HΓ". iClear "HΓ. H".
    iInduction Γ as [|[x τ] Γ'] "IH".
    { rewrite /env_mbang //. }
    rewrite /env_mbang map_cons /= -/(env_mbang MS Γ').
    iDestruct "HΓ" as "(% & %Heq & Hτ. & HΓ'.)".
    iDestruct ("IH" with "HΓ'.") as "#HΓ'".
    rewrite /sem_ty_mbang /=. iDestruct "Hτ." as "#Hτ". simpl.
    iExists vv. iSplit; first done. iFrame "#".
  Qed.

  Global Instance multi_env_nil : @MultiE Σ [].
  Proof. constructor. iIntros "!# % #$". Qed.
  
  Global Instance multi_env_cons (Γ : env Σ) x τ `{! MultiE Γ } `{! MultiT τ }:
    MultiE ((x, τ) :: Γ).
  Proof. 
    constructor. iIntros "% !# (% & %Heq & #Hτ & #HΓ)".
    iApply (multi_env_persistent_inv with "[]").
    - iClear "Hτ HΓ". iIntros "!# % (% & %Heq' & #Hτ & #HΓ)". 
      iModIntro. iExists vv0. iSplit; first done. iFrame "#".
    - iExists vv. iSplit; first done. iFrame "#".
  Qed.

End multi_env.

Section env_sub_typing.

  Context {Σ : gFunctors}.

  Implicit Types Γ Γ₁ Γ₂ Γ₃ : env Σ.
  Implicit Types τ τ₁ τ₂ : sem_ty Σ.

  Lemma env_le_refl Γ : ⊢ Γ ≤ₑ Γ.
  Proof. iIntros "!# % $". Qed.
  
  Lemma env_le_trans Γ₁ Γ₂ Γ₃ : 
    Γ₁ ≤ₑ Γ₂ -∗
    Γ₂ ≤ₑ Γ₃ -∗
    Γ₁ ≤ₑ Γ₃.
  Proof.
    iIntros "#HΓ₁₂ #HΓ₂₃ !# %γ HΓ₁ //=".  
    iApply "HΓ₂₃". by iApply "HΓ₁₂".
  Qed.
  
  Lemma env_le_cons Γ₁ Γ₂ τ₁ τ₂ x :
    Γ₁ ≤ₑ Γ₂ -∗
    τ₁ ≤ₜ τ₂ -∗
    (x, τ₁) :: Γ₁ ≤ₑ (x, τ₂) :: Γ₂.
  Proof.
    iIntros "#HΓ₁₂ #Hτ₁₂ !# %γ [%v (Hlookup & Hv & HΓ₁)]".
    iExists v. iFrame. iSplitR "HΓ₁"; last (by iApply "HΓ₁₂").
    by iApply "Hτ₁₂".
  Qed.
  
  Lemma env_le_contraction Γ x τ `{! MultiT τ } :
    ⊢ (x, τ) :: Γ ≤ₑ (x, τ) :: (x, τ) :: Γ.
  Proof.
    iIntros "!# %γ".
    iIntros "//= [%w (%Hrw & #Hτ & HΓ)]". 
    by do 2 (iExists w; iFrame "%#").
  Qed.
  
  Lemma env_le_bring_forth Γ n x τ :
    nth_error Γ n = Some (x, τ) →
    ⊢ Γ ≤ₑ (x, τ) :: (list_delete n Γ) .
  Proof.
    iInduction n as [|] "IH" forall (Γ); iIntros (Hnth γ);
    iIntros "!# HΓ"; simpl in Hnth; destruct Γ; first done; simplify_eq; first done.
    destruct p; simpl. rewrite !env_sem_typed_cons.
    iDestruct "HΓ" as "[$ HΓ]". rewrite -env_sem_typed_cons.
    by iApply "IH". 
  Qed.
  
  Lemma env_le_bring_forth_rev Γ n x τ :
    nth_error Γ n = Some (x, τ) →
    ⊢ (x, τ) :: (list_delete n Γ) ≤ₑ Γ.
  Proof.
    iInduction n as [|] "IH" forall (Γ); iIntros (Hnth γ);
    simpl in Hnth; 
    destruct Γ as [|[y κ] Γ']; first done; 
    simplify_eq; simpl; first (iIntros "!# $").
    iIntros "!# [%v (? & ? & [%w (? & ? & ?)])]". 
    iExists w. iFrame. iApply "IH"; first done.
    iExists v. iFrame.
  Qed.
  
  Lemma env_le_swap_second Γ x y τ₁ τ₂ : 
    ⊢ (y, τ₂) :: (x, τ₁) :: Γ ≤ₑ (x, τ₁) :: (y, τ₂) :: Γ.
  Proof.
    pose proof (env_le_bring_forth_rev ((x, τ₁) :: (y, τ₂) :: Γ) 1 y τ₂).
    by apply H.
  Qed.
  
  Lemma env_le_swap_third Γ x y z τ₁ τ₂ τ₃: 
    ⊢ (z, τ₃) :: (x, τ₁) :: (y, τ₂) :: Γ ≤ₑ (x, τ₁) :: (y, τ₂) :: (z, τ₃) :: Γ.
  Proof.
    pose proof (env_le_bring_forth_rev ((x, τ₁) :: (y, τ₂) :: (z, τ₃) :: Γ) 2 z τ₃).
    by apply H.
  Qed.
  
  Lemma env_le_swap_fourth Γ x y z z' τ₁ τ₂ τ₃ τ₄: 
    ⊢ (z', τ₄) :: (x, τ₁) :: (y, τ₂) :: (z, τ₃) :: Γ ≤ₑ (x, τ₁) :: (y, τ₂) :: (z, τ₃) :: (z', τ₄) :: Γ.
  Proof.
    pose proof (env_le_bring_forth_rev ((x, τ₁) :: (y, τ₂) :: (z, τ₃) :: (z', τ₄) :: Γ) 3 z' τ₄).
    by apply H.
  Qed.
  
  Lemma env_le_swap_env_sing Γ x τ : 
    ⊢ (x, τ) :: Γ ≤ₑ Γ ++ [(x, τ)].
  Proof.
    induction Γ as [|[y κ] Γ'].
    { simpl. iIntros "!# % $". }
    rewrite -app_comm_cons.
    iApply env_le_trans; [iApply env_le_swap_second|].
    iApply env_le_cons; last (iIntros "!# % % $").
    iApply IHΓ'.
  Qed.
  
  Lemma env_le_weaken Γ x τ :
    ⊢ (x, τ) :: Γ ≤ₑ Γ.
  Proof. iIntros "!# % [% (? & ? & $)]". Qed.

End env_sub_typing.

Section row_env_sub.

  Global Instance row_env_sub_nil {Σ} (ρ : sem_row Σ) : ρ ᵣ⪯ₑ ([] : env Σ).
  Proof. 
    constructor. iIntros "% % % % !# Hρ _". 
    iApply (sem_row_mono _ ρ with "[] Hρ").
    iIntros "!# % % $".
  Qed.

  Global Instance row_env_sub_cons {Σ} (ρ : sem_row Σ) x τ (Γ : env Σ) : 
    ρ ᵣ⪯ₑ Γ → ρ ᵣ⪯ₜ τ → ρ ᵣ⪯ₑ ((x, τ) :: Γ).
  Proof.
    intros HρΓ Hρτ. constructor.
    iIntros "%γ % % %Φ !# Hρ (% & %Heq & Hτ & HΓ)".
    inv HρΓ. iDestruct (row_env_sub with "Hρ HΓ") as "HρΓ".
    inv Hρτ. iDestruct (row_type_sub with "HρΓ Hτ") as "Hρτ".
    iApply (sem_row_mono Σ ρ with "[] Hρτ"). 
    iIntros "!# % % [[$ HΓ] Hτ]".
    iExists vv. by iFrame.
  Qed.

  Global Instance row_env_sub_copy {Σ} (ρ : sem_row Σ) (Γ : env Σ) `{! MultiE Γ } : ρ ᵣ⪯ₑ Γ.
  Proof.
    constructor. iIntros "%γ % % %Φ !# Hρ #HΓ".
    iApply (sem_row_mono Σ ρ); last iApply "Hρ".  
    iIntros "!# % % $ //".
  Qed.

End row_env_sub.

Section mode_env_sub.

  Global Instance mode_env_sub_nil {Σ} m : m ₘ⪯ₑ ([] : env Σ).
  Proof. 
    constructor. iIntros "% _". 
    iApply bi.intuitionistically_intuitionistically_if. iIntros "!# //".
  Qed.
  
  Global Instance mode_env_sub_cons {Σ} m x τ (Γ : env Σ) `{ m ₘ⪯ₑ Γ } `{ m ₘ⪯ₜ τ } : 
    m ₘ⪯ₑ ((x, τ) :: Γ).
  Proof.
    constructor. iIntros "%γ (% & %Heq & Hτ & HΓ)".
    inv H. iDestruct (mode_env_sub with "HΓ") as "HmΓ".
    inv H0. iDestruct (mode_type_sub with "Hτ") as "Hmτ".
    iDestruct (bi.intuitionistically_if_sep_2 m (Γ ⊨ₑ γ) (τ vv.1 vv.2) with "[HmΓ Hmτ]") as "HmΓτ".
    { iFrame. }
    iApply (bi.intuitionistically_if_mono with "HmΓτ").
    iIntros "[HΓ Hτ]". 
    iExists vv. by iFrame.
  Qed.

  Global Instance mode_env_sub_ms {Σ} m (Γ : env Σ) `{! MultiE Γ } : m ₘ⪯ₑ Γ.
  Proof. 
    constructor. iIntros "% #HΓ". 
    by iApply bi.intuitionistically_intuitionistically_if.
  Qed.

End mode_env_sub.

From iris.algebra   Require Export list gmap.
From iris.proofmode Require Export base tactics classes.

From clutch.prob_eff_lang.hazel_prob Require Import typed_lang model spec_ra metatheory.

From Stdlib Require Import PeanoNat.
(* interp.v *)

(* Mentions:

     Most of the material is borrowed from the project ReLoC:

         https://gitlab.mpi-sws.org/iris/reloc

*)

(** * Interpretation of types *)
Section semtypes.
  Context `{probeffRGS Σ}.

  Fixpoint interp (α : ty) (ρ : list (semEffSig Σ)) : valRel Σ :=
    match α with
    | TUnit => ()%valRel
    | TBool => valRel_bool
    | TInt => valRel_int
    | TNat => valRel_nat
    | TBot => ⊥%valRel
    | TTape => valRel_tape
    | TForall α =>
       (∀ R, interp α (R :: ρ))%valRel
    | TArr α (TEff (TSig β1 β2) β) =>
       let E := eff_refines (interp β1 ρ) (interp β2 ρ) in
       ((interp α ρ) → (expr_refines E (interp β ρ)))%valRel
    | TArr α (TEff (TVar n) β) =>
       let E := semEffSig_car (default inhabitant (ρ !! n)) in
       ((interp α ρ) → (expr_refines E (interp β ρ)))%valRel
    | TRef α => valRel_ref (interp α ρ)
    end.

  Definition interp_eff_sig (θ : eff_sig) (ρ : list (semEffSig Σ)) : semEffSig Σ :=
    match θ with
    | TSig β1 β2 => eff_refines' (interp β1 ρ) (interp β2 ρ)
    | TVar n => default inhabitant (ρ !! n)
    end%I.

  Definition interp_eff_ty (τ : eff_ty) (ρ : list (semEffSig Σ)) : exprRel Σ :=
    match τ with
    | TEff θ β => expr_refines (interp_eff_sig θ ρ) (interp β ρ)
    end%I.

  Definition env_ltyped2
    (Γ : gmap string (valRel Σ))
    (vs : gmap string (val * val)) : iProp Σ :=
    ([∗ map] i ↦ A;vv ∈ Γ;vs, valRel_car A vv.1 vv.2)%I.

  Definition interp_env
    (Γ : gmap string ty)
    (ρ : list (semEffSig Σ)) : gmap string (valRel Σ) :=
    (flip interp ρ) <$> Γ.

End semtypes.

Notation "⟦ α ⟧"  := (interp α).
Notation "⟦ τ ⟧ₑ" := (interp_eff_ty τ).
Notation "⟦ Γ ⟧*" := (λ ρ, env_ltyped2 (interp_env Γ ρ)).

(** * The semantic typing judgement *)
Section bin_log_related.
  Context `{probeffRGS Σ}.

  Definition bin_log_related
    (Γ : gmap string ty) (e e' : expr) (τ : eff_ty) : iProp Σ :=
    (∀ ρ vs,
       ⟦ Γ ⟧* ρ vs -∗
         (subst_map (fst <$> vs) e) <<{ ⟦ τ ⟧ₑ ρ }<<
         (subst_map (snd <$> vs) e')).

End bin_log_related.

Notation "Γ ⊨ e1 '≤log≤' e2 : τ" := (bin_log_related Γ e1 e2 τ)
  (at level 74, e1, e2, τ at next level) : bi_scope.

(** * Properties of the interpretation of types *)
Section properties.
  Context `{probeffRGS Σ}.
  Implicit Types A B : valRel Σ.
  Implicit Types Γ : gmap string (valRel Σ).

  (* TODO: make a separate instance for big_sepM2 *)
  Global Instance env_ltyped2_ne n :
    Proper (dist n ==> (=) ==> dist n) (env_ltyped2 (Σ:=Σ)).
  Proof.
    intros Γ Γ' HΓ ? vvs ->. apply big_sepM2_ne_2; [done..|solve_proper].
  Qed.

  Global Instance env_ltyped2_proper :
    Proper ((≡) ==> (=) ==> (≡)) (env_ltyped2 (Σ:=Σ)).
  Proof.
    intros ??? ??->. apply equiv_dist=> n.
    by apply env_ltyped2_ne; first apply equiv_dist.
  Qed.

  Lemma env_ltyped2_lookup Γ vs x A :
    Γ !! x = Some A →
    env_ltyped2 Γ vs -∗ ∃ v1 v2, ⌜ vs !! x = Some (v1,v2) ⌝ ∧ A v1 v2.
  Proof.
    intros ?. rewrite /env_ltyped2 big_sepM2_lookup_l //.
    iIntros "H".
    iDestruct "H" as ([v1 v2] ?) "H". eauto with iFrame.
  Qed.

  Lemma env_ltyped2_insert Γ vs x A v1 v2 :
    A v1 v2 -∗ env_ltyped2 Γ vs -∗
    env_ltyped2 (binder_insert x A Γ) (binder_insert x (v1,v2) vs).
  Proof.
    destruct x as [|x]=> /=; first by auto.
    rewrite /env_ltyped2. iIntros "HA HΓ".
    (* TODO! WTF? *)
    iApply (big_sepM2_insert_2 with "[HA] [$HΓ]"); done. 
  Qed.

  Lemma env_ltyped2_empty :
    ⊢ env_ltyped2 (Σ:=Σ) ∅ ∅.
  Proof. apply (big_sepM2_empty' _). Qed.

  Lemma env_ltyped2_empty_inv vs :
    env_ltyped2 (Σ:=Σ) ∅ vs -∗ ⌜vs = ∅⌝.
  Proof. iApply big_sepM2_empty_r. Qed.

  Global Instance env_ltyped2_persistent Γ vs :
    Persistent (env_ltyped2 Γ vs).
  Proof. apply _. Qed.

  Lemma interp_ty_lift (n : nat) α ρ :
    (n ≤ length ρ)%nat →
    ⟦ ty_lift n α ⟧ ρ ≡ ⟦ α ⟧ (delete n ρ).
  Proof.
    revert α n ρ. apply (ty_ind' (λ α, ∀ n ρ, _ → _ ≡ _)); try done.
    - intros α β₁ β₂ β IHα IHβ₁ IHβ₂ IHβ n ρ Hlen. simpl.
      rewrite (IHα _ _ Hlen).
      rewrite (IHβ₁ _ _ Hlen).
      rewrite (IHβ₂ _ _ Hlen).
      rewrite (IHβ _ _ Hlen). done.
    - intros α m β IHα IHβ n ρ Hlen. simpl.
      rewrite (IHα _ _ Hlen).
      rewrite (IHβ _ _ Hlen).
      destruct (m <? n) eqn:Heq.
      + rewrite lookup_delete_lt; [done|simpl]. by apply Coq.Arith.PeanoNat.Nat.ltb_lt. 
      + rewrite lookup_delete_ge; try done. by apply Coq.Arith.PeanoNat.Nat.ltb_ge. 
    - intros α IHα n ρ Hlen. simpl.
      apply valRel_forall_proper=> R R' ->.
      rewrite IHα; simpl; try done; simpl; lia.
    - intros α IHα n ρ Hlen. simpl.
      rewrite (IHα _ _ Hlen). done.
  Qed.

  Lemma interp_ty_lift_0 α R ρ : ⟦ ty_lift 0 α ⟧ (R :: ρ) ≡ ⟦ α ⟧ ρ.
  Proof. apply interp_ty_lift; simpl; lia. Qed.

  Lemma interp_env_ty_lift (n : nat) (Γ : gmap string ty) ρ :
    (n ≤ length ρ)%nat →
    interp_env (ty_lift n <$> Γ) ρ ≡ interp_env Γ (delete n ρ).
  Proof.
    intros. rewrite /interp_env -map_fmap_compose.
    apply map_fmap_equiv_ext=> x A _ /=. by rewrite interp_ty_lift.
  Qed.
  Lemma interp_env_ty_lift_0 (Γ : gmap string ty) R ρ :
    interp_env (ty_lift 0 <$> Γ) (R :: ρ) ≡ interp_env Γ ρ.
  Proof. apply interp_env_ty_lift; simpl; lia. Qed.

  Global Instance interp_ne α : NonExpansive ⟦ α ⟧.
  Proof. revert α. apply (ty_ind' (λ α, ∀ n, Proper _ _)); solve_proper. Qed.

  Global Instance interp_proper α : Proper ((≡) ==> (≡)) ⟦ α ⟧.
  Proof. intros ???. apply equiv_dist=>n. by apply interp_ne, equiv_dist. Qed.

  Lemma interp_ty_subst (i : nat) α α₁ α₂ ρ :
    (i ≤ length ρ)%nat →
    ⟦ ty_subst i α α₁ α₂ ⟧ ρ ≡
    ⟦ α ⟧ (take i ρ ++ interp_eff_sig (TSig α₁ α₂) ρ :: drop i ρ).
  Proof.
    revert α α₁ α₂ i ρ. apply (ty_ind' (λ α, ∀ α₁ α₂ i ρ, _ → _ ≡ _)); try done.
    - intros α β₁ β₂ β IHα IHβ₁ IHβ₂ IHβ α₁ α₂ n ρ Hlen. simpl.
      rewrite (IHα  _ _ _ _ Hlen) (IHβ₁ _ _ _ _ Hlen).
      rewrite (IHβ₂ _ _ _ _ Hlen) (IHβ  _ _ _ _ Hlen). done.
    - intros α m β IHα IHβ α₁ α₂ n ρ Hlen. simpl.
      destruct (m <? n) eqn:Heq.
      + rewrite lookup_app_l.
        2 : { rewrite take_length. rewrite min_l; [| done]. by apply Coq.Arith.PeanoNat.Nat.ltb_lt. }
        rewrite lookup_take; last by apply Coq.Arith.PeanoNat.Nat.ltb_lt. 
        rewrite (IHα _ _ _ _ Hlen) (IHβ _ _ _ _ Hlen). done.
      + destruct (m =? n) eqn:Heq'.
        * rewrite list_lookup_middle.
          2 : { rewrite take_length. rewrite min_l; [| done]. by apply Coq.Arith.PeanoNat.Nat.eqb_eq.  }
          rewrite (IHα _ _ _ _ Hlen) (IHβ _ _ _ _ Hlen). done.
        * rewrite lookup_app_r.
          2 : { rewrite take_length. rewrite min_l; [|done]. by apply Coq.Arith.PeanoNat.Nat.ltb_ge. }
          rewrite take_length lookup_cons_ne_0.
          2 : { rewrite min_l; [| done]. apply ArithProp.minus_neq_O. apply Coq.Arith.PeanoNat.Nat.ltb_ge in Heq. apply Coq.Arith.PeanoNat.Nat.eqb_neq in Heq'. lia. }
          rewrite lookup_drop. 
          rewrite (IHα _ _ _ _ Hlen) (IHβ _ _ _ _ Hlen). do 3 f_equiv; try done.
          rewrite (_ : Init.Nat.pred m = (n + Init.Nat.pred (m - n `min` length ρ))%nat); try done.
          apply Coq.Arith.PeanoNat.Nat.ltb_ge in Heq. apply Coq.Arith.PeanoNat.Nat.eqb_neq in Heq'. 
          lia.
    - intros α IHα α₁ α₂ n ρ Hlen. simpl.
      apply valRel_forall_proper=> R R' ->.
      rewrite IHα; [|simpl; lia]. simpl.
      by rewrite !interp_ty_lift_0.
  - intros α IHα α₁ α₂ n ρ Hlen. simpl.
    rewrite (IHα  _ _ _ _ Hlen). done.
  Qed.
  Lemma interp_ty_subst_0 α α₁ α₂ ρ :
    ⟦ ty_subst 0 α α₁ α₂ ⟧ ρ ≡ ⟦ α ⟧ (interp_eff_sig (TSig α₁ α₂) ρ :: ρ).
  Proof. apply interp_ty_subst; simpl; lia. Qed.

  Lemma interp_arrow α θ β ρ :
    ⟦ α → (TEff θ β) ⟧ ρ = 
      (⟦ α ⟧ ρ → (expr_refines (interp_eff_sig θ ρ) (⟦ β ⟧ ρ)))%valRel.
  Proof. by case θ as [??|?]. Qed.

  Lemma interp_pure α ρ :
    ⟦ .<> α ⟧ₑ ρ = expr_refines noEffs (⟦ α ⟧ ρ).
  Proof. done. Qed.

End properties.

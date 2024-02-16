From iris.algebra Require Export list.
From iris.proofmode Require Import proofmode.
From clutch.prob_lang Require Import metatheory lang.
From clutch.prelude Require Import asubst properness.
From clutch.ctx_logic Require Import primitive_laws model.
From clutch.typing Require Export types.

(** * Interpretation of types *)
Section semtypes.
  Context `{!clutchRGS Σ}.

  Program Definition ctx_lookup (x : var) : listO (lrelC Σ) -n> (lrelC Σ)
    := λne Δ, (from_option id lrel_true (Δ !! x))%I.
  Next Obligation.
    intros x n Δ Δ' HΔ.
    destruct (Δ !! x) as [P|] eqn:HP; cbn in *.
    - eapply (Forall2_lookup_l _ _ _ x P) in HΔ; last done.
      destruct HΔ as (Q & HQ & HΔ).
      rewrite HQ /= //.
    - destruct (Δ' !! x) as [Q|] eqn:HQ; last reflexivity.
      eapply (Forall2_lookup_r _ _ _ x Q) in HΔ; last done.
      destruct HΔ as (P & HP' & HΔ). exfalso.
      rewrite HP in HP'. inversion HP'.
  Qed.

  Program Fixpoint interp (τ : type) : listO (lrelC Σ) -n> lrelC Σ :=
    match τ as _ return listO (lrelC Σ) -n> lrelC Σ with
    | TUnit => λne _, lrel_unit
    | TNat => λne _, lrel_nat
    | TInt => λne _, lrel_int
    | TBool => λne _, lrel_bool
    | TProd τ1 τ2 => λne Δ, lrel_prod (interp τ1 Δ) (interp τ2 Δ)
    | TSum τ1 τ2 => λne Δ, lrel_sum (interp τ1 Δ) (interp τ2 Δ)
    | TArrow τ1 τ2 => λne Δ, lrel_arr (interp τ1 Δ) (interp τ2 Δ)
    | TRec τ' => λne Δ, lrel_rec (λne τ, interp τ' (τ::Δ))
    | TVar x => ctx_lookup x
    | TForall τ' => λne Δ, lrel_forall (λ τ, interp τ' (τ::Δ))
    | TExists τ' => λne Δ, lrel_exists (λ τ, interp τ' (τ::Δ))
    | TRef τ => λne Δ, lrel_ref (interp τ Δ)
    | TTape => λne Δ, lrel_tape
    end.
  Solve Obligations with (intros I τ τ' n Δ Δ' HΔ' ??; try solve_proper).
  Next Obligation.
    intros I τ τ' n Δ Δ' HΔ' ??.
    apply lrel_rec_ne=> X /=.
    apply I. by f_equiv.
  Defined.

  Lemma unboxed_type_sound τ Δ v v' :
    UnboxedType τ →
    interp τ Δ v v' ⊢ ⌜val_is_unboxed v ∧ val_is_unboxed v'⌝.
  Proof.
    induction 1; simpl;
    first [iDestruct 1 as (? ?) "[% [% ?]]"
          |iDestruct 1 as (?) "[% %]"
          |iIntros "[% %]"];
    simplify_eq/=; eauto with iFrame.
  Qed.

  Lemma eq_type_sound τ Δ v v' :
    EqType τ →
    interp τ Δ v v' ⊢ ⌜v = v'⌝.
  Proof.
    intros Hτ; revert v v'; induction Hτ; iIntros (v v') "#H1 /=".
    - by iDestruct "H1" as %[-> ->].
    - by iDestruct "H1" as (n) "[% %]"; subst.
    - by iDestruct "H1" as (n) "[% %]"; subst.
    - by iDestruct "H1" as (b) "[% %]"; subst.
    - iDestruct "H1" as (?? ??) "[% [% [H1 H2]]]"; simplify_eq/=.
      rewrite IHHτ1 IHHτ2.
      by iDestruct "H1" as "%"; iDestruct "H2" as "%"; subst.
    - iDestruct "H1" as (??) "[H1|H1]".
      + iDestruct "H1" as "[% [% H1]]"; simplify_eq/=.
        rewrite IHHτ1. by iDestruct "H1" as "%"; subst.
      + iDestruct "H1" as "[% [% H1]]"; simplify_eq/=.
        rewrite IHHτ2. by iDestruct "H1" as "%"; subst.
  Qed.

  Lemma unboxed_type_eq τ Δ v1 v2 w1 w2 :
    UnboxedType τ →
    interp τ Δ v1 v2 ⊢
    interp τ Δ w1 w2 -∗
    |={⊤}=> ⌜v1 = w1 ↔ v2 = w2⌝.
  Proof.
    intros Hunboxed.
    cut (EqType τ ∨ (∃ τ', τ = TRef τ') ∨ τ = TTape).
    { intros [Hτ | [[τ' ->] | ->]].
      - rewrite !eq_type_sound //.
        iIntros "% %". iModIntro.
        iPureIntro. naive_solver.
      - rewrite /lrel_car /=.
        iDestruct 1 as (l1 l2 -> ->) "Hl".
        iDestruct 1 as (r1 r2 -> ->) "Hr".
        destruct (decide (l1 = r1)); subst.
        + destruct (decide (l2 = r2)); subst; first by eauto.
          iInv (logN.@(r1, l2)) as (v1 v2) "(>Hr1 & >Hr2 & Hinv1)".
          iInv (logN.@(r1, r2)) as (w1 w2) "(>Hr1' & >Hr2' & Hinv2)".
          iExFalso. by iDestruct (ghost_map_elem_valid_2 with "Hr1 Hr1'") as %[].
        + destruct (decide (l2 = r2)); subst; last first.
          { iModIntro. iPureIntro. naive_solver. }
          iInv (logN.@(r1, r2)) as (v1 v2) "(>Hr1 & >Hr2 & Hinv1)".
          iInv (logN.@(l1, r2)) as (w1 w2) "(>Hr1' & >Hr2' & Hinv2)".
          iExFalso. by iDestruct (ghost_map_elem_valid_2 with "Hr2 Hr2'") as %[].
      - rewrite /lrel_car /=.
        iDestruct 1 as (l1 l2 n -> ->) "Hl".
        iDestruct 1 as (r1 r2 m -> ->) "Hr".
        destruct (decide (l1 = r1)); subst.
        + destruct (decide (l2 = r2)); subst; first by eauto.
          iInv (logN.@(r1, l2)) as "> (Hr1 & Hl2)".
          iInv (logN.@(r1, r2)) as "> (Hr1' & Hr2')".
          iExFalso. by iDestruct (ghost_map_elem_valid_2 with "Hr1 Hr1'") as %[].
        + destruct (decide (l2 = r2)); subst; last first.
          { iModIntro. iPureIntro. naive_solver. }
          iInv (logN.@(r1, r2)) as "> (Hr1 & Hr2)".
          iInv (logN.@(l1, r2)) as "> (Hl1 & Hr2')".
          iExFalso. by iDestruct (ghost_map_elem_valid_2 with "Hr2 Hr2'") as %[]. }
    by apply unboxed_type_ref_or_eqtype.
  Qed.

End semtypes.

(** ** Properties of the type inrpretation w.r.t. the substitutions *)
Section interp_ren.
  Context `{!clutchRGS Σ}.
  Implicit Types Δ : list (lrel Σ).

  (* TODO: why do I need to unfold lrel_car here? *)
  Lemma interp_ren_up (Δ1 Δ2 : list (lrel Σ)) τ τi :
    interp τ (Δ1 ++ Δ2) ≡ interp (τ.[upn (length Δ1) (ren (+1))]) (Δ1 ++ τi :: Δ2).
  Proof.
    revert Δ1 Δ2. induction τ => Δ1 Δ2; simpl; eauto;
    try by
      (intros ? ?; unfold lrel_car; simpl; properness; repeat f_equiv=>//).
    - apply fixpoint_proper=> τ' w1 w2 /=.
      unfold lrel_car. simpl.
      properness; auto. apply (IHτ (_ :: _)).
    - intros v1 v2; unfold lrel_car; simpl;
        simpl; properness; auto.
      rewrite /lrel_car /=. properness; auto.
      apply refines_proper=> //. apply (IHτ (_ :: _)).
    - intros ??; unfold lrel_car; simpl; properness; auto. apply (IHτ (_ :: _)).
    - intros v1 v2; simpl.
      rewrite iter_up. case_decide; simpl; properness.
      { by rewrite !lookup_app_l. }
      change (bi_ofeO (uPredI (iResUR Σ))) with (uPredO (iResUR Σ)).
      rewrite !lookup_app_r; [|lia..].
      assert (∀ x, (length Δ1 + S (x - length Δ1) - length Δ1) = S (x - length Δ1)) as Hwat.
      { lia. }
      rewrite Hwat. simpl. done.
  Qed.

  Lemma interp_ren A Δ (Γ : gmap string type) :
    ((λ τ, interp τ (A::Δ)) <$> ⤉Γ) ≡ ((λ τ, interp τ Δ) <$> Γ).
  Proof.
    rewrite -map_fmap_compose => x /=.
    rewrite !lookup_fmap.
    destruct (Γ !! x); auto; simpl. f_equiv.
    symmetry. apply (interp_ren_up []).
  Qed.

  Lemma interp_weaken (Δ1 Π Δ2 : list (lrel Σ)) τ :
    interp (τ.[upn (length Δ1) (ren (+ length Π))]) (Δ1 ++ Π ++ Δ2)
    ≡ interp τ (Δ1 ++ Δ2).
  Proof.
    revert Δ1 Π Δ2. induction τ=> Δ1 Π Δ2; simpl; eauto;
    try by
      (intros ? ?; simpl; unfold lrel_car; simpl; repeat f_equiv =>//).
    - apply fixpoint_proper=> τi ?? /=.
      unfold lrel_car; simpl.
      properness; auto. apply (IHτ (_ :: _)).
    - intros ??; simpl; unfold lrel_car; simpl;
      properness; auto.
      rewrite /lrel_car /=. properness; auto.
      apply refines_proper=> //. apply (IHτ (_ :: _)).
    - intros ??; unfold lrel_car; simpl; properness; auto.
        by apply (IHτ (_ :: _)).
    - intros ??; simpl; properness; auto.
      rewrite iter_up; case_decide; properness; simpl.
      { by rewrite !lookup_app_l. }
      rewrite !lookup_app_r ;[| lia ..]. do 3 f_equiv. lia.
  Qed.

  Lemma interp_subst_up (Δ1 Δ2 : list (lrel Σ)) τ τ' :
    interp τ (Δ1 ++ interp τ' Δ2 :: Δ2)
    ≡ interp (τ.[upn (length Δ1) (τ' .: ids)]) (Δ1 ++ Δ2).
  Proof.
    revert Δ1 Δ2; induction τ=> Δ1 Δ2; simpl; eauto;
    try by
      (intros ? ?; unfold lrel_car; simpl; properness; repeat f_equiv=>//).
    - apply fixpoint_proper=> τi ?? /=.
      unfold lrel_car. simpl.
      properness; auto. apply (IHτ (_ :: _)).
    - intros ??. unfold lrel_car; simpl;
      properness; auto.
      rewrite /lrel_car /=. properness; auto.
      apply refines_proper=>//. apply (IHτ (_ :: _)).
    - intros ??; unfold lrel_car; simpl; properness; auto. apply (IHτ (_ :: _)).
    - intros w1 w2; simpl.
      rewrite iter_up; case_decide; simpl; properness.
      { by rewrite !lookup_app_l. }
      rewrite !lookup_app_r; [|lia..].
      case EQ: (_ - length Δ1)=> [|n]; simpl.
      { symmetry.
        pose (HW := interp_weaken [] Δ1 Δ2 τ' w1 w2).
        etrans; last by apply HW.
        asimpl. reflexivity. }
      rewrite !lookup_app_r; [|lia ..]. repeat f_equiv. lia.
  Qed.

  Lemma interp_subst Δ2 τ τ' :
    interp τ (interp τ' Δ2 :: Δ2) ≡ interp (τ.[τ'/]) Δ2.
  Proof. apply (interp_subst_up []). Qed.
End interp_ren.

(** * Interpretation of the environments *)
Section env_typed.
  Context `{!clutchRGS Σ}.
  Implicit Types A B : lrel Σ.
  Implicit Types Γ : gmap string (lrel Σ).

  (** Substitution [vs] is well-typed w.r.t. [Γ] *)
  Definition env_ltyped2 (Γ : gmap string (lrel Σ))
    (vs : gmap string (val*val)) : iProp Σ :=
    ([∗ map] i ↦ A;vv ∈ Γ;vs, lrel_car A vv.1 vv.2)%I.

  Notation "⟦ Γ ⟧*" := (env_ltyped2 Γ).

  (* TODO: make a separate instance for big_sepM2 *)
  Global Instance env_ltyped2_ne n :
    Proper (dist n ==> (=) ==> dist n) env_ltyped2.
  Proof.
    intros Γ Γ' HΓ ? vvs ->. apply big_sepM2_ne_2; [done..|solve_proper].
  Qed.

  Global Instance env_ltyped2_proper :
    Proper ((≡) ==> (=) ==> (≡)) env_ltyped2.
  Proof. solve_proper_from_ne. Qed.

  Lemma env_ltyped2_lookup Γ vs x A :
    Γ !! x = Some A →
    ⟦ Γ ⟧* vs ⊢ ∃ v1 v2, ⌜ vs !! x = Some (v1,v2) ⌝ ∧ A v1 v2.
  Proof.
    intros ?. rewrite /env_ltyped2 big_sepM2_lookup_l //.
    iDestruct 1 as ([v1 v2] ?) "H". eauto with iFrame.
  Qed.

  Lemma env_ltyped2_insert Γ vs x A v1 v2 :
    A v1 v2 ⊢ ⟦ Γ ⟧* vs -∗
    ⟦ (binder_insert x A Γ) ⟧* (binder_insert x (v1,v2) vs).
  Proof.
    destruct x as [|x]=> /=; first by auto.
    rewrite /env_ltyped2. iIntros "HA HΓ".
    now iApply (big_sepM2_insert_2 with "[HA] [HΓ]").
  Qed.

  Lemma env_ltyped2_empty :
    ⊢ ⟦ ∅ ⟧* ∅.
  Proof. apply (big_sepM2_empty' _). Qed.

  Lemma env_ltyped2_empty_inv vs :
    ⟦ ∅ ⟧* vs ⊢ ⌜vs = ∅⌝.
  Proof. apply big_sepM2_empty_r. Qed.

  Global Instance env_ltyped2_persistent Γ vs : Persistent (⟦ Γ ⟧* vs).
  Proof. apply _. Qed.
End env_typed.

Notation "⟦ Γ ⟧*" := (env_ltyped2 Γ).

(** * The semantic typing judgement *)
Section bin_log_related.
  Context `{!clutchRGS Σ}.

  Definition bin_log_related (E : coPset)
             (Δ : list (lrel Σ)) (Γ : stringmap type)
             (e e' : expr) (τ : type) : iProp Σ :=
    (∀ vs, ⟦ (λ τ, interp τ Δ) <$> Γ ⟧* vs -∗
           REL (subst_map (fst <$> vs) e)
            << (subst_map (snd <$> vs) e') @ E : (interp τ Δ))%I.

End bin_log_related.

Notation "〈 E ';' Δ ';' Γ 〉 ⊨ e '≤log≤' e' : τ" :=
  (bin_log_related E Δ Γ e%E e'%E (τ)%ty)
  (at level 100, E at next level, Δ at next level, Γ at next level, e, e' at next level,
   τ at level 200,
   format "'[hv' 〈 E ';'  Δ ';'  Γ 〉  ⊨  '/  ' e  '/' '≤log≤'  '/  ' e'  :  τ ']'").
Notation "〈 Δ ';' Γ 〉 ⊨ e '≤log≤' e' : τ" :=
  (bin_log_related ⊤ Δ Γ e%E e'%E (τ)%ty)
  (at level 100, Δ at next level, Γ at next level, e, e' at next level,
   τ at level 200,
   format "'[hv' 〈 Δ ';'  Γ 〉  ⊨  '/  ' e  '/' '≤log≤'  '/  ' e'  :  τ ']'").

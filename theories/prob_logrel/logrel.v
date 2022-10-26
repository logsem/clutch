(** A binary logical relation for System F_mu_ref with tapes *)

From stdpp Require Export binders strings stringmap fin_map_dom gmap.
From iris.base_logic Require Import invariants.
From iris.algebra Require Import list.
From self.prob_lang Require Import lang types.
From self.program_logic Require Import weakestpre.
From self.prob_logrel Require Import persistent_pred spec_ra.

Import uPred.
(* Import language. *)
Import prob_lang.
Definition logN : namespace := nroot .@ "logN".

(** interp : is a unary logical relation. *)
Section logrel.
  Context `{!stateIG Σ, cfgSG Σ}.
  Notation D := (persistent_predO (val * val) (iPropI Σ)).
  Implicit Types τi : D.
  Implicit Types Δ : listO D.
  Implicit Types interp : listO D -n> D.

  Local Arguments ofe_car !_.

  (* PGH: interp_expr blocked until we have the right CMRA's  *)

  Definition interp_expr (τi : listO D -n> D) (Δ : listO D)
      (ee : expr * expr) : iProp Σ := (∀ K,
    (⤇ fill K (ee.2)) -∗
    WP ee.1 {{ v, ∃ v', ⤇ fill K (of_val v') ∗ τi Δ (v, v') }})%I.
  Global Instance interp_expr_ne n :
    Proper (dist n ==> dist n ==> (=) ==> dist n) interp_expr.
  Proof. unfold interp_expr; solve_proper. Qed.

  Global Instance interp_expr_proper :
    Proper ((≡) ==> (≡) ==> (=) ==> (≡)) interp_expr.
  Proof. unfold interp_expr; solve_proper. Qed.

  (* PGH: ctx_lookup not required until we have type variables *)

  (* Program Definition ctx_lookup (x : var) : listO D -n> D := *)
  (*   λne Δ, PersPred (default (inhabitant : persistent_pred _ _) (Δ !! x)). *)
  (* Solve Obligations with solve_proper. *)

  Program Definition interp_unit : listO D -n> D :=
    λne Δ, PersPred (λ ww, ⌜ww.1 = #uv⌝ ∧ ⌜ww.2 = #uv⌝)%I.
  Program Definition interp_int : listO D -n> D :=
    λne Δ, PersPred (λ ww, ∃ n : Z, ⌜ww.1 = #nv n⌝ ∧ ⌜ww.2 = #nv n⌝)%I.

  Program Definition interp_bool : listO D -n> D :=
    λne Δ, PersPred (λ ww, ∃ b : bool, ⌜ww.1 = #bv b⌝ ∧ ⌜ww.2 = #bv b⌝)%I.

  Program Definition interp_prod
      (interp1 interp2 : listO D -n> D) : listO D -n> D :=
    λne Δ,
      PersPred (λ ww, ∃ vv1 vv2,
                 ⌜ww = (PairV (vv1.1) (vv2.1), PairV (vv1.2) (vv2.2))⌝ ∧
                 interp1 Δ vv1 ∧ interp2 Δ vv2)%I.
  Solve Obligations with solve_proper.

  Program Definition interp_sum
      (interp1 interp2 : listO D -n> D) : listO D -n> D :=
    λne Δ, PersPred
             (λ ww,
              (∃ vv, ⌜ww = (InjLV (vv.1), InjLV (vv.2))⌝ ∧ interp1 Δ vv) ∨
              (∃ vv, ⌜ww = (InjRV (vv.1), InjRV (vv.2))⌝ ∧ interp2 Δ vv))%I.
  Solve Obligations with solve_proper.

  Program Definition interp_arrow
          (interp1 interp2 : listO D -n> D) : listO D -n> D :=
    λne Δ,
    PersPred
      (λ ww, □ ∀ vv, interp1 Δ vv →
                      interp_expr
                        interp2 Δ (App (of_val (ww.1)) (of_val (vv.1)),
                                   App (of_val (ww.2)) (of_val (vv.2))))%I.
  Solve Obligations with solve_proper.

  (* Program Definition interp_forall *)
  (*     (interp : listO D -n> D) : listO D -n> D := *)
  (*   λne Δ, *)
  (*   PersPred *)
  (*     (λ ww, *)
  (*      □ ∀ τi, *)
  (*          interp_expr *)
  (*            interp (τi :: Δ) (TApp (of_val (ww.1)), TApp (of_val (ww.2))))%I. *)
  (* Solve Obligations with solve_proper. *)

  (* Program Definition interp_exist (interp : listO D -n> D) : listO D -n> D := *)
  (*   λne Δ, *)
  (*   PersPred *)
  (*     (λ ww, ∃ (τi : D) vv, ⌜ww = (PackV vv.1, PackV vv.2)⌝ ∗ *)
  (*              interp (τi :: Δ) vv)%I. *)
  (* Solve Obligations with repeat intros ?; simpl; solve_proper. *)

  (* Program Definition interp_rec1 *)
  (*     (interp : listO D -n> D) (Δ : listO D) (τi : D) : D := *)
  (*   PersPred (λ ww, □ ∃ vv, ⌜ww = (FoldV (vv.1), FoldV (vv.2))⌝ ∧ *)
  (*                         ▷ interp (τi :: Δ) vv)%I. *)

  (* Global Instance interp_rec1_contractive *)
  (*   (interp : listO D -n> D) (Δ : listO D) : Contractive (interp_rec1 interp Δ). *)
  (* Proof. solve_contractive. Qed. *)

  (* Lemma fixpoint_interp_rec1_eq (interp : listO D -n> D) Δ x : *)
  (*   fixpoint (interp_rec1 interp Δ) x ≡ *)
  (*   interp_rec1 interp Δ (fixpoint (interp_rec1 interp Δ)) x. *)
  (* Proof. exact: (fixpoint_unfold (interp_rec1 interp Δ) x). Qed. *)

  (* Program Definition interp_rec (interp : listO D -n> D) : listO D -n> D := *)
  (*   λne Δ, fixpoint (interp_rec1 interp Δ). *)
  (* Next Obligation. *)
  (*   intros interp n Δ1 Δ2 HΔ ?; simpl. *)
  (*   rewrite fixpoint_ne; first done. *)
  (*   solve_proper. *)
  (* Qed. *)

  Program Definition interp_ref_inv (ll : loc * loc) : D -n> iPropO Σ := λne τi,
    (∃ vv, ll.1 ↦ᵢ vv.1 ∗ ll.2 ↦ₛ vv.2 ∗ τi vv)%I.
  Solve Obligations with solve_proper.

  Program Definition interp_ref
      (interp : listO D -n> D) : listO D -n> D :=
    λne Δ,
    PersPred (λ ww,
            ∃ ll, ⌜ww = (LitV (LitLoc ll.1), LitV (LitLoc ll.2))⌝ ∧
                  inv (logN .@ ll) (interp_ref_inv ll (interp Δ)))%I.
  Solve Obligations with solve_proper.

  (* Program Definition interp_tape : listO D -n> D := *)
  (*   λne Δ, PersPred (λ ww, ∃ n : Z, ⌜ww.1 = #nv n⌝ ∧ ⌜ww.2 = #nv n⌝)%I. *)

  Fixpoint interp (τ : type) : listO D -n> D :=
    match τ return _ with
    | TUnit => interp_unit
    | TInt => interp_int
    | TBool => interp_bool
    | TProd τ1 τ2 => interp_prod (interp τ1) (interp τ2)
    | TSum τ1 τ2 => interp_sum (interp τ1) (interp τ2)
    | TArrow τ1 τ2 => interp_arrow (interp τ1) (interp τ2)
    (* PGH: TODO: use ctx_loopup instead! *)
    | TVar x => interp_unit
    (* | TForall τ' => interp_forall (interp τ') *)
    (* | TExist τ' => interp_exist (interp τ') *)
    (* | TRec τ' => interp_rec (interp τ') *)
    | TRef τ' => interp_ref (interp τ')
    (* PGH: TODO: use interp_tape instead! *)
    | TTape => (* interp_tape *) interp_unit
    end.
  Notation "⟦ τ ⟧" := (interp τ).

  Definition interp_env (Γ : list type)
      (Δ : listO D) (vvs : list (val * val)) : iProp Σ :=
    (⌜length Γ = length vvs⌝ ∗ [∗] zip_with (λ τ, ⟦ τ ⟧ Δ) Γ vvs)%I.
  Notation "⟦ Γ ⟧*" := (interp_env Γ).

  Global Instance interp_env_base_persistent Δ Γ vs :
    TCForall Persistent (zip_with (λ τ, ⟦ τ ⟧ Δ) Γ vs).
  Proof.
    revert vs.
    induction Γ => vs; simpl; destruct vs; constructor; apply _.
  Qed.
  Global Instance interp_env_persistent Γ Δ vvs :
    Persistent (⟦ Γ ⟧* Δ vvs) := _.

(*
  Lemma interp_weaken Δ1 Π Δ2 τ :
    ⟦ τ.[upn (length Δ1) (ren (+ length Π))] ⟧ (Δ1 ++ Π ++ Δ2)
    ≡ ⟦ τ ⟧ (Δ1 ++ Δ2).
  Proof.
    revert Δ1 Π Δ2. induction τ=> Δ1 Π Δ2 vv; simpl; auto.
    - by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply IH end).
    - by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply IH end).
    - unfold interp_expr.
      by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply IH end).
    - rewrite fixpoint_proper; first done. intros τi ww; simpl.
      by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply (IH (_ :: _)) end).
    - rewrite iter_up; destruct lt_dec as [Hl | Hl]; simpl.
      { by rewrite !lookup_app_l. }
      rewrite !lookup_app_r; [|lia..]. do 3 f_equiv. lia.
    - unfold interp_expr.
      by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply (IH (_ :: _)) end).
    - by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply (IH (_ :: _)) end).
    - by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply IH end).
  Qed.

  Lemma interp_subst_up Δ1 Δ2 τ τ' :
    ⟦ τ ⟧ (Δ1 ++ interp τ' Δ2 :: Δ2)
    ≡ ⟦ τ.[upn (length Δ1) (τ' .: ids)] ⟧ (Δ1 ++ Δ2).
  Proof.
    revert Δ1 Δ2; induction τ=> Δ1 Δ2 vv; simpl; auto.
    - by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply IH end).
    - by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply IH end).
    - unfold interp_expr.
      by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply IH end).
    - rewrite fixpoint_proper; first done; intros τi ww; simpl.
      by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply (IH (_ :: _)) end).
    - match goal with |- context [_ !! ?x] => rename x into idx end.
      rewrite iter_up; destruct lt_dec as [Hl | Hl]; simpl.
      { by rewrite !lookup_app_l. }
      rewrite !lookup_app_r; [|lia ..].
      case EQ: (idx - length Δ1) => [|n]; simpl.
      { symmetry. asimpl. apply (interp_weaken [] Δ1 Δ2 τ'). }
      rewrite !lookup_app_r; [|lia ..]. do 3 f_equiv. lia.
    - unfold interp_expr.
      by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply (IH (_ :: _)) end).
    - by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply (IH (_ :: _)) end).
    - by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply IH end).
  Qed.

  Lemma interp_subst Δ2 τ τ' v : ⟦ τ ⟧ (⟦ τ' ⟧ Δ2 :: Δ2) v ≡ ⟦ τ.[τ'/] ⟧ Δ2 v.
  Proof. apply (interp_subst_up []). Qed.

  Lemma interp_env_length Δ Γ vvs : ⟦ Γ ⟧* Δ vvs ⊢ ⌜length Γ = length vvs⌝.
  Proof. by iIntros "[% ?]". Qed.

  Lemma interp_env_Some_l Δ Γ vvs x τ :
    Γ !! x = Some τ → ⟦ Γ ⟧* Δ vvs ⊢ ∃ vv, ⌜vvs !! x = Some vv⌝ ∧ ⟦ τ ⟧ Δ vv.
  Proof.
    iIntros (?) "[Hlen HΓ]"; iDestruct "Hlen" as %Hlen.
    destruct (lookup_lt_is_Some_2 vvs x) as [v Hv].
    { by rewrite -Hlen; apply lookup_lt_Some with τ. }
    iExists v; iSplit; first done. iApply (big_sepL_elem_of with "HΓ").
    apply elem_of_list_lookup_2 with x.
    rewrite lookup_zip_with; by simplify_option_eq.
  Qed.

  Lemma interp_env_nil Δ : ⊢ ⟦ [] ⟧* Δ [].
  Proof. iSplit; simpl; auto. Qed.
  Lemma interp_env_cons Δ Γ vvs τ vv :
    ⟦ τ :: Γ ⟧* Δ (vv :: vvs) ⊣⊢ ⟦ τ ⟧ Δ vv ∗ ⟦ Γ ⟧* Δ vvs.
  Proof.
    rewrite /interp_env /= (assoc _ (⟦ _ ⟧ _ _)) -(comm _ ⌜(_ = _)⌝%I) -assoc.
    by apply sep_proper; [apply pure_proper; lia|].
  Qed.

  Lemma interp_env_ren Δ (Γ : list type) vvs τi :
    ⟦ subst (ren (+1)) <$> Γ ⟧* (τi :: Δ) vvs ⊣⊢ ⟦ Γ ⟧* Δ vvs.
  Proof.
    apply sep_proper; [apply pure_proper; by rewrite fmap_length|].
    revert Δ vvs τi; induction Γ=> Δ [|v vs] τi; csimpl; auto.
    apply sep_proper; auto. apply (interp_weaken [] [τi] Δ).
  Qed.

  Lemma interp_EqType_one_to_one Δ τ l l' u u' v v' w w' :
    EqType τ →
    l ↦ᵢ u -∗
    l' ↦ₛ u' -∗
    ⟦ τ ⟧ Δ (v, v') -∗
    ⟦ τ ⟧ Δ (w, w') ={⊤ ∖ ↑logN.@(l, l')}=∗
    l ↦ᵢ u ∗ l' ↦ₛ u' ∗ ⌜v = w ↔ v' = w'⌝.
  Proof.
    iIntros (Heqt) "Hl Hl' Hvv Hww".
    destruct τ; inversion Heqt; simplify_eq/=.
    { iDestruct "Hvv"as "[% %]"; simplify_eq.
      iDestruct "Hww"as "[% %]"; simplify_eq.
      by iFrame. }
    { iDestruct "Hvv"as "(%&%&%)"; simplify_eq.
      iDestruct "Hww"as "(%&%&%)"; simplify_eq.
      by iFrame. }
    { iDestruct "Hvv"as "(%&%&%)"; simplify_eq.
      iDestruct "Hww"as "(%&%&%)"; simplify_eq.
      by iFrame. }
    iDestruct "Hvv"as ([l1 l1']) "[% Hll1]"; simplify_eq.
    iDestruct "Hww"as ([l2 l2']) "[% Hll2]"; simplify_eq.
    simpl.
    destruct (decide (l1 = l)); simplify_eq.
    - destruct (decide (l1' = l')); simplify_eq.
      + destruct (decide (l2 = l)); simplify_eq.
        * destruct (decide (l2' = l')); simplify_eq; first by iFrame.
          iInv (logN.@(l, l2')) as ([v v']) "(>Hlx & >Hlx' & Hvv) /=" "Hclose".
          iDestruct (mapsto_valid_2 with "Hl Hlx") as %[? ?]; done.
        * destruct (decide (l2' = l')); simplify_eq; last first.
          { iModIntro; iFrame; iPureIntro; intuition simplify_eq. }
          iInv (logN.@(l2, l')) as ([v v']) "(>Hlx & >Hlx' & Hvv) /=" "Hclose".
          iDestruct (mapstoS_valid_2 with "Hl' Hlx'") as %?; done.
      + iInv (logN.@(l, l1')) as ([v v']) "(>Hlx & >Hlx' & Hvv) /=" "Hclose".
          iDestruct (mapsto_valid_2 with "Hl Hlx") as %[? ?]; done.
    - destruct (decide (l1 = l2)); simplify_eq.
      + destruct (decide (l1' = l2')); simplify_eq; first by iFrame.
        iInv (logN.@(l2, l1')) as ([v v']) "(>Hlx & >Hlx' & Hvv) /=" "Hclose".
        iInv (logN.@(l2, l2')) as ([w w']) "(>Hly & >Hly' & Hww) /=" "Hclose'".
        iDestruct (mapsto_valid_2 with "Hly Hlx") as %[? ?]; done.
      + destruct (decide (l1' = l2')); simplify_eq; last first.
        { iModIntro; iFrame; iPureIntro; intuition simplify_eq. }
        destruct (decide (l2' = l')); simplify_eq.
        * iInv (logN.@(l1, l')) as ([v v']) "(>Hlx & >Hlx' & Hvv) /=" "Hclose".
          iDestruct (mapstoS_valid_2 with "Hl' Hlx'") as %?; done.
        * iInv (logN.@(l1, l2')) as ([v v']) "(>Hlx & >Hlx' & Hvv) /=" "Hclose".
          iInv (logN.@(l2, l2')) as ([w w']) "(>Hly & >Hly' & Hww) /=" "Hclose'".
          iDestruct (mapstoS_valid_2 with "Hly' Hlx'") as %?; done.
  Qed.
*)
End logrel.

(* Global Typeclasses Opaque interp_env. *)
Notation "⟦ τ ⟧" := (interp τ).
Notation "⟦ τ ⟧ₑ" := (interp_expr (interp τ)).
(* Notation "⟦ Γ ⟧*" := (interp_env Γ). *)

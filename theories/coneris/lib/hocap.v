(** * Hocap specs *)
From stdpp Require Import namespaces.
From iris Require Import excl_auth invariants list.
From clutch.coneris Require Import coneris.

Set Default Proof Using "Type*".

(* Definition hocap_error_nroot:= nroot.@ "error". *)
(* Definition hocap_error_RA := authR nonnegrealR. *)

(* Class hocap_errorGS (Σ : gFunctors) := Hocap_errorGS { *)
(*   hocap_errorGS_inG :: inG Σ (hocap_error_RA); *)
(* }. *)


(* Definition hocap_errorΣ := #[GFunctor (hocap_error_RA)]. *)

(* Notation "'●↯' ε '@' γ" := (∃ (x : nonnegreal), ⌜x.(nonneg) = ε%R⌝ ∗ own γ (● x))%I *)
(*                          (at level 1). *)
(* Notation "'◯↯' ε '@' γ" := (∃ (x : nonnegreal), ⌜x.(nonneg) = ε%R⌝ ∗ own γ (◯ x))%I *)
(*                              (at level 1). *)


(* Section error_lemmas. *)
(*   Context `{!conerisGS Σ, !hocap_errorGS Σ}. *)

(*   Lemma hocap_error_auth_exclusive b b' γ: *)
(*     ●↯ b @ γ -∗ ●↯ b' @ γ -∗ False. *)
(*   Proof. *)
(*     iIntros "[%[% H1]] [%[% H2]]". *)
(*     iCombine "H1 H2" gives "%H1". *)
(*     compute in H1. destruct H1. *)
(*     exfalso. *)
(*     apply H1. done. *)
(*   Qed. *)

(*   Lemma hocap_error_frag_split (b b':nonnegreal) γ: *)
(*     ◯↯ b @ γ ∗ ◯↯ b' @ γ ⊣⊢ ◯↯ (b+b') @ γ. *)
(*   Proof. *)
(*     iSplit. *)
(*     - iIntros "[[%x1[% H1]] [%x2[% H2]]]". *)
(*       iExists (x1 + x2)%NNR. *)
(*       iSplit; [simpl; simpl in *; iPureIntro; lra|]. *)
(*       rewrite auth_frag_op own_op. iFrame. *)
(*     - iIntros "[%x [% H]]". *)
(*       simpl in *. *)
(*       replace x with (b+b')%NNR; last (apply nnreal_ext; simpl; lra). *)
(*       rewrite auth_frag_op own_op. *)
(*       by iDestruct "H" as "[$ $]". *)
(*   Qed. *)
  
(*   (* Helpful lemmas *) *)
(*   Lemma hocap_error_auth_valid (b:R) γ: *)
(*     (●↯ b @ γ) -∗ ⌜(0<=b<1)%R⌝. *)
(*   Proof. *)
(*     iIntros "[%x[<- H]]". *)
(*     iDestruct (own_valid with "[$]") as "%H". *)
(*     iPureIntro. *)
(*     rewrite auth_auth_valid in H. *)
(*     destruct x. *)
(*     compute in H. *)
(*     split; simpl; lra. *)
(*   Qed.  *)

(*   Lemma hocap_error_frag_valid (b:R) γ: *)
(*     (◯↯ b @ γ) -∗ ⌜(0<=b<1)%R⌝. *)
(*   Proof. *)
(*     iIntros "[%[<- H]]". *)
(*     iDestruct (own_valid with "[$]") as "%H". *)
(*     iPureIntro. *)
(*     rewrite auth_frag_valid in H. *)
(*     destruct x. *)
(*     compute in H. *)
(*     split; simpl; lra. *)
(*   Qed.  *)
  
(*   Lemma hocap_error_alloc (ε:nonnegreal): *)
(*     (ε<1)%R -> ⊢ |==>∃ γ, (●↯ ε @ γ) ∗ (◯↯ ε @ γ). *)
(*   Proof. *)
(*     intros H. *)
(*     iMod (own_alloc (● ε ⋅ ◯ ε)) as "[% [??]]". *)
(*     - apply auth_both_valid_2. *)
(*       + compute. destruct ε; simpl in H. lra. *)
(*       + apply nonnegreal_included; lra. *)
(*     - by eauto with iFrame. *)
(*   Qed. *)

(*   Lemma hocap_error_ineq γ (b c:R) : *)
(*     (●↯ b @ γ) -∗ (◯↯ c @ γ) -∗ ⌜ (c<=b)%R ⌝. *)
(*   Proof. *)
(*     iIntros "[% [<- Hγ●]] [% [<-Hγ◯]]". *)
(*     iCombine "Hγ● Hγ◯" gives "%Hop". *)
(*     by eapply auth_both_valid_discrete in Hop as [Hlt%nonnegreal_included ?].  *)
(*   Qed. *)

(*   Lemma hocap_error_decrease γ (b' b:R) : *)
(*      (●↯ (b) @ γ) -∗ (◯↯ b' @ γ) ==∗ (●↯ (b-b') @ γ). *)
(*   Proof. *)
(*     iIntros "H1 H2". *)
(*     simpl. *)
(*     iDestruct (hocap_error_ineq with "[$][$]") as "%". *)
(*     iDestruct "H1" as "[%x [% H1]]". *)
(*     iDestruct "H2" as "[%x' [% H2]]". *)
(*     iMod (own_update_2 with "H1 H2") as "Hown". *)
(*     { unshelve eapply (auth_update_dealloc _ _ ((x-x') _)%NNR), nonnegreal_local_update. *)
(*       - lra. *)
(*       - apply cond_nonneg. *)
(*       - apply nnreal_ext =>/=. lra. } *)
(*     iFrame. simpl. iPureIntro. *)
(*     by subst.  *)
(*   Qed. *)
   

(*   Lemma hocap_error_increase γ (b:R) (b':nonnegreal) : *)
(*      (b+b'<1)%R -> ⊢ (●↯ b @ γ) ==∗ (●↯ (b+b')%R @ γ) ∗ (◯↯ b' @ γ). *)
(*   Proof. *)
(*     iIntros (Hineq) "[%x [% H]]". *)
(*     iMod (own_update with "H") as "[$ $]"; last (iPureIntro; split; last done). *)
(*     - apply auth_update_alloc. *)
(*       apply (local_update_unital_discrete _ _ (x+b')%NNR) => z H1 H2. *)
(*       split. *)
(*       + destruct x, b'. compute. simpl in *. lra. *)
(*       + apply nnreal_ext. simpl. *)
(*         rewrite Rplus_comm. *)
(*         apply Rplus_eq_compat_l. *)
(*         simpl in *. rewrite H2. simpl. lra. *)
(*     - simpl. lra.  *)
(*   Qed. *)
  
(*   Lemma hocap_error_auth_irrel γ (b c:R) : *)
(*     (b=c)%R -> (●↯ b @ γ) -∗ (●↯ c @ γ). *)
(*   Proof. *)
(*     iIntros (->) "$". *)
(*   Qed. *)
  
(*   Lemma hocap_error_frag_irrel γ (b c:R) : *)
(*     (b=c)%R -> (◯↯ b @ γ) -∗ (◯↯ c @ γ). *)
(*   Proof. *)
(*     iIntros (->) "$". *)
(*   Qed. *)

(* End error_lemmas. *)


Section hocap_error_coupl.
  Context `{conerisGS Σ}.
  Context (tb:nat).
  Local Canonical Structure finO := leibnizO (fin (S tb)).
  Local Canonical Structure RO := leibnizO R.
  Local Canonical Structure ε2O := leibnizO (list (fin(S tb))->R).


  Definition hocap_error_coupl_pre Z Φ : (R * R * list (nat * (list (fin (S tb)) -> R) * (list (fin (S tb)))) -> iProp Σ) :=
    (λ x,
       let '(ε, ε_initial, ls) := x in
       (Z ε ε_initial ls)∨
       ∃ num ε2,
         ⌜(∀ l, 0<=ε2 l)%R⌝ ∗
         ⌜(SeriesC (λ l, if bool_decide (length l = num) then ε2 l else 0)/((S tb)^num) <= ε)%R⌝ ∗
         (∀ ns, Φ (ε2 ns, ε_initial, ls ++ [(num, ε2, ns)]))
    )%I.
  
  Local Instance hocap_error_coupl_pre_ne Z Φ :
    NonExpansive (hocap_error_coupl_pre Z Φ).
  Proof.
    solve_contractive.
  Qed.

  Local Instance hocap_error_coupl_pre_mono Z : BiMonoPred (hocap_error_coupl_pre Z).
  Proof.
    split; last apply _.
    iIntros (Φ Ψ HNEΦ HNEΨ) "#Hwand".
    iIntros ([[??]?]) "[H|(%&%&%&%&H)]".
    - by iLeft.
    - iRight.
      iExists _, _.
      repeat iSplit; try done.
      iIntros. by iApply "Hwand".
  Qed.

  Definition hocap_error_coupl' Z := bi_least_fixpoint (hocap_error_coupl_pre Z).
  Definition hocap_error_coupl ε_current ε_initial ls Z := hocap_error_coupl' Z (ε_current, ε_initial, ls).

  Lemma hocap_error_coupl_unfold ε ε_initial ls Z :
    hocap_error_coupl ε ε_initial ls Z ≡
      ((Z ε ε_initial ls)∨
      ∃ num ε2,
        ⌜(∀ l, 0<=ε2 l)%R⌝ ∗
        ⌜(SeriesC (λ l, if bool_decide (length l = num) then ε2 l else 0)/((S tb)^num) <= ε)%R⌝ ∗
        (∀ ns, hocap_error_coupl (ε2 ns) ε_initial (ls ++ [(num, ε2, ns)]) Z))%I.
  Proof.
    rewrite /hocap_error_coupl/hocap_error_coupl' least_fixpoint_unfold//. Qed.

  Lemma hocap_error_coupl_ret ε ε_initial ls Z:
    Z ε ε_initial ls -∗  hocap_error_coupl ε ε_initial ls Z.
  Proof.
    iIntros. rewrite hocap_error_coupl_unfold. by iLeft.
  Qed.

  Lemma hocap_error_coupl_rec ε ε_initial ls Z:
    (∃ num ε2,
        ⌜(∀ l, 0<=ε2 l)%R⌝ ∗
        ⌜(SeriesC (λ l, if bool_decide (length l = num) then ε2 l else 0)/((S tb)^num) <= ε)%R⌝ ∗
        (∀ ns, hocap_error_coupl (ε2 ns) ε_initial (ls ++ [(num, ε2, ns)]) Z)) -∗  hocap_error_coupl ε ε_initial ls Z.
  Proof.
    iIntros. rewrite hocap_error_coupl_unfold. by iRight.
  Qed.

  Lemma hocap_error_coupl_ind (Ψ Z : R -> R -> list (nat * (list (fin (S tb)) -> R) * (list (fin (S tb))))->iProp Σ):
    ⊢ (□ (∀ ε ε_initial ls,
             hocap_error_coupl_pre Z (λ '(ε', ε_initial', ls'),
                 Ψ ε' ε_initial' ls' ∧ hocap_error_coupl ε' ε_initial' ls' Z)%I (ε, ε_initial, ls) -∗ Ψ ε ε_initial ls) →
       ∀ ε ε_initial ls, hocap_error_coupl ε ε_initial ls Z -∗ Ψ ε ε_initial ls)%I.
  Proof.
    iIntros "#IH" (ε ε_initial ls) "H".
    set (Ψ' := (λ '(ε, ε_initial, ls), Ψ ε ε_initial ls) : (prodO _ _->iProp Σ)).
    assert (NonExpansive Ψ') by solve_contractive.
    iApply (least_fixpoint_ind _ Ψ' with "[] H").
    iIntros "!#" ([[??]?]) "H". by iApply "IH".
  Qed.

  Lemma hocap_error_coupl_bind ε ε_initial ls Z1 Z2 :
    (∀ ε' ε_initial' ls', Z1 ε' ε_initial' ls' -∗ hocap_error_coupl ε' ε_initial' ls' Z2) -∗
    hocap_error_coupl ε ε_initial ls Z1 -∗
    hocap_error_coupl ε ε_initial ls Z2.
  Proof.
    iIntros "HZ H".
    iRevert "HZ".
    iRevert (ε ε_initial ls) "H".
    iApply hocap_error_coupl_ind.
    iIntros "!#" (ε ε_initial ls) "[H|H] HZ".
    - by iApply "HZ".
    - iApply hocap_error_coupl_rec.
      iDestruct "H" as "(%&%&%&%&Hrest)".
      iExists _,_. repeat iSplit; try done.
      iIntros (?).
      iDestruct ("Hrest" $! _) as "[Hrest _]".
      by iApply "Hrest".
  Qed.
      
End hocap_error_coupl.
  
Definition hocap_tapes_nroot:=nroot.@"tapes".
Class hocap_tapesGS (Σ : gFunctors) := Hocap_tapesGS {
  hocap_tapesGS_inG :: ghost_mapG Σ loc (nat*list nat)
                                         }.
Definition hocap_tapesΣ := ghost_mapΣ loc (nat*list nat).

Notation "α ◯↪N ( M ; ns ) @ γ":= (α ↪[ γ ] (M,ns))%I
                                    (at level 20, format "α ◯↪N ( M ; ns ) @ γ") : bi_scope.

Notation "● m @ γ" := (ghost_map_auth γ 1 m) (at level 20) : bi_scope.

Section tapes_lemmas.
  Context `{!conerisGS Σ, !hocap_tapesGS Σ}.

  Lemma hocap_tapes_alloc m:
    ⊢ |==>∃ γ, (● m @ γ) ∗ [∗ map] k↦v ∈ m, (k ◯↪N (v.1; v.2) @ γ).
  Proof.
    iMod ghost_map_alloc as (γ) "[??]".
    iFrame. iModIntro.
    iApply big_sepM_mono; last done.
    by iIntros (?[??]).
  Qed.

  Lemma hocap_tapes_agree m γ k N ns:
    (● m @ γ) -∗ (k ◯↪N (N; ns) @ γ) -∗ ⌜ m!!k = Some (N, ns) ⌝.
  Proof.
    iIntros "H1 H2".
    by iCombine "H1 H2" gives "%".
  Qed.

  Lemma hocap_tapes_new γ m k N ns :
    m!!k=None -> ⊢ (● m @ γ) ==∗ (● (<[k:=(N,ns)]>m) @ γ) ∗ (k ◯↪N (N; ns) @ γ).
  Proof.
    iIntros (Hlookup) "H".
    by iApply ghost_map_insert.
  Qed.

  Lemma hocap_tapes_update γ m k N N' ns ns':
    (● m @ γ) -∗ (k ◯↪N (N; ns) @ γ) ==∗ (● (<[k:=(N',ns')]>m) @ γ) ∗ (k ◯↪N (N'; ns') @ γ).
  Proof.
    iIntros "H1 H2".
    iApply (ghost_map_update with "[$][$]").
  Qed.
  

End tapes_lemmas.


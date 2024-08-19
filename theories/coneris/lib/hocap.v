(** * Hocap specs *)
From stdpp Require Import namespaces.
From iris Require Import excl_auth invariants.
From clutch.coneris Require Import coneris flip.

Set Default Proof Using "Type*".

Definition hocap_error_nroot:= nroot.@ "error".
Definition hocap_error_RA := excl_authR NNRO.

Class hocap_errorGS (Σ : gFunctors) := Hocap_errorGS {
  hocap_errorGS_inG :: inG Σ (hocap_error_RA);
}.


Definition hocap_errorΣ := #[GFunctor (excl_authR (nonnegrealUR))].

Notation "'●↯' ε '@' γ" := (∃ (x : nonnegreal), ⌜x.(nonneg) = ε%R⌝ ∗ own γ (●E x))%I
                         (at level 1).
Notation "'◯↯' ε '@' γ" := (∃ (x : nonnegreal), ⌜x.(nonneg) = ε%R⌝ ∗ own γ (◯E x))%I
                          (at level 1).
Section lemmas.
  Context `{!conerisGS Σ, !hocap_errorGS Σ}.
  (* Helpful lemmas *)
  Lemma hocap_error_alloc (ε:nonnegreal):
    ⊢ |==>∃ γ, (●↯ ε @ γ) ∗ (◯↯ ε @ γ).
  Proof.
    iMod (own_alloc (●E ε ⋅ ◯E ε)) as "[% [??]]". 
    - by apply excl_auth_valid.
    - by eauto with iFrame.
  Qed.

  Lemma hocap_error_agree γ b c :
    (●↯ b @ γ) -∗ (◯↯ c @ γ) -∗ ⌜ b = c ⌝.
  Proof.
    iIntros "[% [<- Hγ●]] [% [<-Hγ◯]]".
    by iCombine "Hγ● Hγ◯" gives %<-%excl_auth_agree_L.
  Qed.

  Lemma hocap_error_update γ (b':nonnegreal) b c :
    (●↯ b @ γ) -∗ (◯↯ c @ γ) ==∗ (●↯ b' @ γ) ∗ (◯↯ b' @ γ).
  Proof.
    iIntros "[% [<- Hγ●]] [% [<-Hγ◯]]".
    iMod (own_update_2 _ _ _ (_ ⋅ _) with "Hγ● Hγ◯") as "[$$]".
    { by apply excl_auth_update. }
    done.
  Qed. 
End lemmas.

Section HOCAP.

  Context `{!conerisGS Σ, !hocap_errorGS Σ}.
  
  Definition error_inv (γ :gname):=
    inv hocap_error_nroot (∃ (ε:nonnegreal), ↯ ε ∗ ●↯ ε @ γ).

  Lemma wp_hocap_rand_adv_comp (N : nat) z E
     (ε2 : nonnegreal -> fin (S N) -> nonnegreal)
    (P : iProp Σ) (Q : (fin (S N)) -> iProp Σ) γ:
    TCEq N (Z.to_nat z) →
    ↑hocap_error_nroot ⊆ E ->
    (∀ (ε:nonnegreal), SeriesC (λ n, (1 / (S N)) * nonneg (ε2 ε n))%R <= (nonneg ε))%R →
    {{{ error_inv γ∗
        (∀ (ε:nonnegreal) (n : fin (S N)), P ∗ ●↯ ε @ γ ={E∖↑hocap_error_nroot}=∗ ●↯ (ε2 ε n) @ γ ∗ Q (n) ) ∗
        P }}} rand #z @ E {{{ n, RET #n; Q (n)}}}.
  Proof.
    iIntros (-> Hsubset Hineq) "%Φ [#Hinv [Hchange HP]] HΦ".
    iInv "Hinv" as ">(%ε & Hε & Hauth)" "Hclose".
    wp_apply (wp_couple_rand_adv_comp1' with "[$]"); first apply Hineq.
    iIntros (n) "Hε".
    iMod ("Hchange" $! _ n with "[$]") as "[Hauth HQ]".
    iMod ("Hclose" with "[Hauth Hε]") as "_"; first iFrame.
    by iApply "HΦ".
  Qed.

  Lemma wp_hocap_flip_adv_comp E
    (ε2 : nonnegreal -> bool -> nonnegreal)
    (P : iProp Σ) (Q : bool -> iProp Σ) γ:
    ↑hocap_error_nroot ⊆ E ->
    (∀ (ε:nonnegreal),  ((nonneg (ε2 ε true) + nonneg (ε2 ε false))/2 <= (nonneg ε))%R) →
    {{{ error_inv γ∗
        □(∀ (ε:nonnegreal) (b : bool), P ∗ ●↯ ε @ γ ={E∖↑hocap_error_nroot}=∗ ●↯ (ε2 ε b) @ γ ∗ Q (b) ) ∗
        P }}} flip @ E {{{ (b:bool), RET #b; Q (b)}}}.
  Proof.
    iIntros (Hsubset Hineq) "%Φ [#Hinv [#Hchange HP]] HΦ".
    rewrite /flip/flipL.
    wp_pures.
    wp_apply (wp_hocap_rand_adv_comp _ _ _ (λ ε x, if fin_to_nat x =? 1%nat then ε2 ε true else ε2 ε false) P (λ x, Q (fin_to_nat x =? 1%nat)) with "[-HΦ]"); [done|..].
    - intros ε. rewrite SeriesC_finite_foldr; simpl. specialize (Hineq ε). lra.
    - iFrame. iSplitR; first iExact "Hinv".
      iIntros (ε n) "H".
      iMod ("Hchange" with "[$]") as "[Hε HQ]".
      iModIntro. iSplitL "Hε"; last done.
      by case_match.
    - iIntros.
      wp_apply (conversion.wp_int_to_bool); first done.
      iIntros "_".
      iApply "HΦ".
      inv_fin n; simpl; first done.
      intros n; inv_fin n; simpl; first done.
      intros n; inv_fin n.
  Qed.

  (* Lemma wp_hocap_flip_flip_adv_comp E *)
  (*   (ε2 : nonnegreal -> (bool*bool) -> nonnegreal) *)
  (*   (P : iProp Σ) (Q : (bool*bool) -> iProp Σ) γ: *)
  (*   ↑hocap_error_nroot ⊆ E -> *)
  (*   (∀ (ε:nonnegreal),  ((nonneg (ε2 ε (true, true)) + nonneg (ε2 ε (true, false)) + *)
  (*                           (nonneg (ε2 ε (false, true)) + nonneg (ε2 ε (false, false)) *)
  (*                        ))/4 <= (nonneg ε))%R) → *)
  (*   {{{ error_inv γ∗ *)
  (*      □ (∀ (ε:nonnegreal) (b : (bool*bool)), P ∗ ●↯ ε @ γ ={E∖↑hocap_error_nroot}=∗ ●↯ (ε2 ε b) @ γ ∗ Q (b) ) ∗ *)
  (*       P }}} (flip, flip) @ E {{{ (b:bool*bool), RET (#b.1,#b.2); Q (b)}}}. *)
  (* Proof. *)
  (*   iIntros (Hsubset Hineq) "%Φ [#Hinv [#Hchange HP]] HΦ". *)
  (*   wp_apply (wp_hocap_flip_adv_comp _ (λ x b, nnreal_div (ε2 x (false, b) + ε2 x (true, b))%NNR (mknonnegreal 2 _)) P with "[-HΦ]"); [done|..]. *)
  (*   - intros ε. simpl. specialize (Hineq ε). lra. *)
  (*   - iFrame. *)
  (*     iSplit; first done. *)
  (*     admit. *)
  (* Abort. *)
    
End HOCAP.


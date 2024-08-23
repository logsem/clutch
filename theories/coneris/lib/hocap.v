(** * Hocap specs *)
From stdpp Require Import namespaces.
From iris Require Import excl_auth invariants list.
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

Definition hocap_tapes_nroot:=nroot.@"tapes".
Class hocap_tapesGS (Σ : gFunctors) := Hocal_tapesGS {
  hocap_tapesGS_inG :: ghost_mapG Σ loc (nat*list nat)
                                         }.
Definition hocap_tapesΣ := ghost_mapΣ loc (nat*list nat).

Notation "α ◯↪N ( M ; ns ) @ γ":= (α ↪[ γ ] (M,ns))%I
                                    (at level 20, format "α ◯↪N ( M ; ns ) @ γ") : bi_scope.

Notation "● m @ γ" := (ghost_map_auth γ 1 m) (at level 20) : bi_scope.

Section error_lemmas.
  Context `{!conerisGS Σ, !hocap_errorGS Σ}.
  (* Helpful lemmas *)
  Lemma hocap_error_alloc (ε:nonnegreal):
    ⊢ |==>∃ γ, (●↯ ε @ γ) ∗ (◯↯ ε @ γ).
  Proof.
    iMod (own_alloc (●E ε ⋅ ◯E ε)) as "[% [??]]".
    - by apply excl_auth_valid.
    - by eauto with iFrame.
  Qed.

  Lemma hocap_error_agree γ (b c:R) :
    (●↯ b @ γ) -∗ (◯↯ c @ γ) -∗ ⌜ b = c ⌝.
  Proof.
    iIntros "[% [<- Hγ●]] [% [<-Hγ◯]]".
    by iCombine "Hγ● Hγ◯" gives %<-%excl_auth_agree_L.
  Qed.

  Lemma hocap_error_update γ (b':nonnegreal) (b c:R) :
    (●↯ b @ γ) -∗ (◯↯ c @ γ) ==∗ (●↯ b' @ γ) ∗ (◯↯ b' @ γ).
  Proof.
    iIntros "[% [<- Hγ●]] [% [<-Hγ◯]]".
    iMod (own_update_2 _ _ _ (_ ⋅ _) with "Hγ● Hγ◯") as "[$$]".
    { by apply excl_auth_update. }
    done.
  Qed.

  Lemma hocap_error_irrel γ (b c:R) :
    (b=c)%R -> (●↯ b @ γ) -∗ (●↯ c @ γ).
  Proof.
    iIntros (->) "$".
  Qed.

End error_lemmas.

Section tapes_lemmas.
  Context `{!conerisGS Σ, !hocap_tapesGS Σ}.

  (** * TODO add*)
End tapes_lemmas.

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
        □(∀ (ε:nonnegreal) (n : fin (S N)), P ∗ ●↯ ε @ γ ={E∖↑hocap_error_nroot}=∗
                                           (⌜(1<=ε2 ε n)%R⌝ ∨(●↯ (ε2 ε n) @ γ ∗ Q (n))) ) ∗
        P }}} rand #z @ E {{{ n, RET #n; Q (n)}}}.
  Proof.
    iIntros (-> Hsubset Hineq) "%Φ [#Hinv [#Hchange HP]] HΦ".
    iInv "Hinv" as ">(%ε & Hε & Hauth)" "Hclose".
    wp_apply (wp_couple_rand_adv_comp1' with "[$]"); first apply Hineq.
    iIntros (n) "Hε".
    iMod ("Hchange" $! _ n with "[$]") as "[%|[Hauth HQ]]"; last first.
    { iMod ("Hclose" with "[Hauth Hε]") as "_"; first iFrame.
      by iApply "HΦ". }
    iExFalso.
    by iApply (ec_contradict with "[$]").
  Qed.

  Lemma wp_hocap_flip_adv_comp E
    (ε2 : nonnegreal -> bool -> nonnegreal)
    (P : iProp Σ) (Q : bool -> iProp Σ) γ:
    ↑hocap_error_nroot ⊆ E ->
    (∀ (ε:nonnegreal),  ((nonneg (ε2 ε true) + nonneg (ε2 ε false))/2 <= (nonneg ε))%R) →
    {{{ error_inv γ∗
        □(∀ (ε:nonnegreal) (b : bool), P ∗ ●↯ ε @ γ ={E∖↑hocap_error_nroot}=∗ (⌜(1<=ε2 ε b)%R⌝ ∨ ●↯ (ε2 ε b) @ γ ∗ Q (b)) ) ∗
        P }}} flip @ E {{{ (b:bool), RET #b; Q (b)}}}.
  Proof.
    iIntros (Hsubset Hineq) "%Φ [#Hinv [#Hchange HP]] HΦ".
    rewrite /flip/flipL.
    wp_pures.
    wp_apply (wp_hocap_rand_adv_comp _ _ _ (λ ε x, if fin_to_nat x =? 1%nat then ε2 ε true else ε2 ε false) P (λ x, Q (fin_to_nat x =? 1%nat)) with "[-HΦ]"); [done|..].
    - intros ε. rewrite SeriesC_finite_foldr; simpl. specialize (Hineq ε). lra.
    - iFrame. iSplitR; first iExact "Hinv".
      iModIntro.
      iIntros (ε n) "H".
      iMod ("Hchange" $! _ (fin_to_nat n =? 1%nat)with "[$]") as "[%|[Hε HQ]]".
      + iModIntro. iLeft. iPureIntro. by case_match.
      + iModIntro. iRight. iFrame. by case_match.
    - iIntros.
      wp_apply (conversion.wp_int_to_bool); first done.
      iIntros "_".
      iApply "HΦ".
      inv_fin n; simpl; first done.
      intros n; inv_fin n; simpl; first done.
      intros n; inv_fin n.
  Qed.

  (** With tapes *)
  Context `{!hocap_tapesGS Σ}.

  Definition tapes_inv (γ :gname):=
    inv hocap_tapes_nroot (∃ m, ●m@γ ∗ [∗ map] α ↦ t ∈ m, α ↪N ( t.1 ; t.2 )  ).
  Lemma wp_hocap_presample_adv_comp (N : nat)  z E e ns α
     (ε2 : nonnegreal -> fin (S N) -> nonnegreal)
    (P : iProp Σ) (Q : val-> iProp Σ) R γ γ':
    TCEq N (Z.to_nat z) →
    TCEq (to_val e) None ->
    ↑hocap_error_nroot ⊆ E ->
    ↑hocap_tapes_nroot ⊆ E ->
    (∀ (ε:nonnegreal), SeriesC (λ n, (1 / (S N)) * nonneg (ε2 ε n))%R <= (nonneg ε))%R →
    error_inv γ -∗ tapes_inv γ' -∗
    (□∀ (ε:nonnegreal) (n : fin (S N)) m, (⌜m!!α = Some (N, ns)⌝ -∗ P ∗ ●↯ ε @ γ ∗ ●m@γ') 
                                                ={E∖↑hocap_error_nroot∖↑hocap_tapes_nroot}=∗
        (⌜(1<=ε2 ε n)%R⌝ ∨(●↯ (ε2 ε n) @ γ ∗ ●(<[α := (N, ns ++ [fin_to_nat n])]>m) @ γ' ∗ R (n))))
        -∗ P -∗ α ◯↪N (N; ns) @ γ' -∗
        wp_update E (∃ n, R (n) ∗ α◯↪N (N; ns++[fin_to_nat n]) @ γ').
  Proof.
    iIntros (-> Hval Hsubset Hubset' Hineq) "#Hinv #Hinv' #Hshift HP Htape".
    iApply fupd_wp_update.
    iInv "Hinv" as ">(%ε' & Hε & Hauth)" "Hclose".
    iInv "Hinv'" as ">(%m & Hm & Hmauth)" "Hclose'".
  Abort. 
    
  (*   iApply (wp_presample_adv_comp); [done|exact|..]. *)
  (*   iApply fupd_frame_l. *)
  (*   - *)
  (* Abort. *)



End HOCAP.

Section HOCAP_alt.
  Context `{!conerisGS Σ}.

  Lemma wp_flip_exp_hocap  (P : iProp Σ) (Q : bool → iProp Σ) E1 E2 :
    □ (P ={E1, E2}=∗
        ∃ ε1 ε2, ⌜((nonneg (ε2 true) + nonneg (ε2 false))/2 <= nonneg ε1)%R⌝ ∗
                 ↯ ε1 ∗ (∀ (b : bool), ↯ (ε2 b) ={E2, E1}=∗ Q b)) -∗
    {{{ P }}} flip @ E1 {{{ (b : bool), RET #b; Q b}}}.
  Proof.
    iIntros "#Hvs". iIntros (Ψ) "!# HP HΨ".
    rewrite /flip /flipL.
    wp_pures.
    wp_bind (rand _)%E.
    iMod ("Hvs" with "HP") as (ε1 ε2) "(% & Hε1 & HQ)".
    set (ε2' := ε2 ∘ fin_to_bool).
    iApply (wp_couple_rand_adv_comp1' _ _ _ _  ε2' with "Hε1").
    { rewrite SeriesC_finite_foldr /ε2' /=. lra. }
    iIntros "!>" (n) "Hε2".
    assert (ε2' n = ε2 (Z_to_bool n)) as ->.
    { inv_fin n; [eauto|]. intros n. inv_fin n; [eauto|]. intros n. inv_fin n. }
    iMod ("HQ" with "Hε2") as "HQ". iModIntro.
    wp_apply (conversion.wp_int_to_bool); [done|].
    iIntros "_".
    by iApply "HΨ".
  Qed.

End HOCAP_alt.
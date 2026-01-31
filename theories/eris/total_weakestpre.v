From iris.proofmode Require Import base proofmode.
From clutch.eris Require Export weakestpre.

Import uPred.

(** * The total weakest precondition *)
Definition tgl_wp_pre `{!erisWpGS Λ Σ}
  (wp : coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
    coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
  match to_val e1 with
  | Some v => |={E}=> Φ v
  | None => ∀ σ1 ε1,
      state_interp σ1 ∗ err_interp ε1 ={E,∅}=∗
      glm e1 σ1 ε1 (λ '(e2, σ2) ε2,
        |={∅,E}=> state_interp σ2 ∗ err_interp ε2 ∗ wp E e2 Φ)
end%I.

Local Lemma tgl_wp_pre_mono `{!erisWpGS Λ Σ}
  (wp1 wp2 : coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
  ⊢ (□ ∀ E e Φ, wp1 E e Φ -∗ wp2 E e Φ) →
    ∀ E e Φ, tgl_wp_pre wp1 E e Φ -∗ tgl_wp_pre wp2 E e Φ.
Proof.
  iIntros "#H".
  iIntros (E e Φ) "Hwp". rewrite /tgl_wp_pre.
  case_match; first done.
  iIntros (σ ε) "He". iMod ("Hwp" with "He") as "Hwp".
  iModIntro. iApply (glm_mono_pred with "[][$Hwp]").
  iIntros ([e' s] ε') "He".
  iApply (fupd_wand_l with "[H He]").
  iFrame. iIntros "[?[??]]". iFrame.
  by iApply "H".
Qed.

Local Definition tgl_wp_pre' `{!erisWpGS Λ Σ} :
  (prodO (prodO (leibnizO coPset) (exprO Λ)) (val Λ -d> iPropO Σ) → iPropO Σ) →
  prodO (prodO (leibnizO coPset) (exprO Λ)) (val Λ -d> iPropO Σ) → iPropO Σ :=
  uncurry3 ∘ tgl_wp_pre ∘ curry3.

Local Instance tgl_wp_pre_mono' `{!erisWpGS Λ Σ} :
  BiMonoPred (tgl_wp_pre').
Proof.
  constructor.
  - iIntros (wp1 wp2 ??) "#H"; iIntros ([[E e1] Φ]); iRevert (E e1 Φ).
    iApply tgl_wp_pre_mono. iIntros "!>" (E e Φ). iApply ("H" $! (E,e,Φ)).
  - intros wp Hwp n [[E1 e1] Φ1] [[E2 e2] Φ2]
      [[?%leibniz_equiv ?%leibniz_equiv] ?]; simplify_eq/=.
    rewrite /curry3 /tgl_wp_pre. do 7 (f_equiv).
    rewrite /glm /glm'.
    f_equiv.
    intros Φ e. unfold glm_pre.
    do 19 f_equiv.
    rewrite /exec_stutter. do 14 f_equiv. by apply pair_ne.
Qed.

Local Definition tgl_wp_def `{!erisWpGS Λ Σ} : Twp (iProp Σ) (expr Λ) (val Λ) () :=
  {| twp := λ (_ : ()) E e Φ, (bi_least_fixpoint tgl_wp_pre') (E, e, Φ); twp_default := () |}.
Local Definition tgl_wp_aux : seal (@tgl_wp_def). Proof. by eexists. Qed.
Definition tgl_wp' := tgl_wp_aux.(unseal).
Global Arguments tgl_wp' {Λ Σ _}.
Global Existing Instance tgl_wp'.
Local Lemma tgl_wp_unseal `{!erisWpGS Λ Σ} : twp = (@tgl_wp_def Λ Σ _).(twp).
Proof. rewrite -tgl_wp_aux.(seal_eq) //. Qed.

Section tgl_wp.
  Context `{!erisWpGS Λ Σ}.
  Implicit Types P : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.
  Implicit Types σ : state Λ.
  Implicit Types ρ : cfg Λ.
  Implicit Types ε : R.

  (* Total Wekaest pre *)
  Lemma tgl_wp_unfold s E e Φ : WP e @ s; E [{ Φ }] ⊣⊢ tgl_wp_pre (twp (PROP:=iProp Σ) s) E e Φ.
  Proof. rewrite tgl_wp_unseal /tgl_wp_def. simpl. rewrite least_fixpoint_unfold. done. Qed.

  Lemma tgl_wp_ind s Ψ :
  (∀ n E e, Proper (pointwise_relation _ (dist n) ==> dist n) (Ψ E e)) →
  □ (∀ e E Φ, tgl_wp_pre (λ E e Φ, Ψ E e Φ ∧ WP e @ s; E [{ Φ }]) E e Φ -∗ Ψ E e Φ) -∗
  ∀ e E Φ, WP e @ s; E [{ Φ }] -∗ Ψ E e Φ.
  Proof.
    iIntros (HΨ). iIntros "#IH" (e E Φ) "H". rewrite tgl_wp_unseal.
    set (Ψ' := uncurry3 Ψ :
           prodO (prodO (leibnizO coPset) (exprO Λ)) (val Λ -d> iPropO Σ) → iPropO Σ).
    assert (NonExpansive Ψ').
    { intros n [[E1 e1] Φ1] [[E2 e2] Φ2]
        [[?%leibniz_equiv ?%leibniz_equiv] ?]; simplify_eq/=. by apply HΨ. }
    iApply (least_fixpoint_ind _ Ψ' with "[] H").
    iIntros "!>" ([[??] ?]) "H". by iApply "IH".
  Qed.

  Global Instance tgl_wp_ne s E e n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (twp (PROP:=iProp Σ) s E e).
  Proof.
    intros Φ1 Φ2 HΦ. rewrite !tgl_wp_unseal. by apply (least_fixpoint_ne _), pair_ne, HΦ.
  Qed.
  Global Instance tgl_wp_proper s E e :
    Proper (pointwise_relation _ (≡) ==> (≡)) (twp (PROP:=iProp Σ) s E e).
  Proof.
    by intros Φ Φ' ?; apply equiv_dist=>n; apply tgl_wp_ne=>v; apply equiv_dist.
  Qed.

  Lemma tgl_wp_ind' E s Ψ :
  (∀ n e, Proper (pointwise_relation _ (dist n) ==> dist n) (Ψ e)) →
  □ (∀ e Φ, tgl_wp_pre (λ E e Φ, Ψ e Φ ∧ WP e @ s; E [{ Φ }]) E e Φ -∗ Ψ e Φ) -∗
  ∀ e Φ, WP e @ s; E [{ Φ }] -∗ Ψ e Φ.
  Proof.
    iIntros (Hp) "#IH". iIntros (e Φ) "Hwp".
    iRevert "IH".
    iApply (tgl_wp_ind _ (λ E e Φ, _) with "[][$]").
    - intros. intros ???. repeat f_equiv.
    - iModIntro.
      clear. iIntros (e E Φ) "H #IH".
      iApply "IH".
      rewrite {2 4}/tgl_wp_pre. case_match; first done.
      iIntros (σ ε) "[Hs He]".
      iMod ("H" with "[$]") as "H".
      iModIntro.
      iApply (glm_mono_pred with "[]H").
      iIntros ([] []) "H".
      iMod "H". iModIntro. iDestruct "H" as "(?&?&H)".
      iFrame. iSplit.
      { by iApply "H". }
      by iDestruct "H" as "[_?]".
  Qed.

  Lemma tgl_wp_ind_simple E s Ψ Φ e:
  (∀ n e, Proper (dist n) (Ψ e)) →
  □ (∀ e, tgl_wp_pre (λ _ e _, Ψ e) E e Φ -∗ Ψ e) -∗
  WP e @ s; E [{ Φ }] -∗ Ψ e.
  Proof.
    iIntros (HΨ) "#IH Htwp".
    iRevert "IH".
    iApply (tgl_wp_ind _ (λ E e Φ, _)  with "[]Htwp").
    { intros. intros ???.
      rewrite /tgl_wp_pre. repeat f_equiv.
    }
    clear.
    iModIntro.
    iIntros (e E Φ) "H #IH".
    iApply "IH".
    rewrite {2 4}/tgl_wp_pre. case_match; first done.
    iIntros (σ ε) "[Hs He]".
    iMod ("H" with "[$]") as "H".
    iModIntro.
    iApply (glm_mono_pred with "[]H").
    iIntros ([] []) "H".
    iMod "H". iModIntro. iDestruct "H" as "(?&?&H)".
    iFrame. iApply "H". done.
  Qed.
  
  Lemma tgl_wp_value_fupd' s E Φ v : WP of_val v @ s; E [{ Φ }] ⊣⊢ |={E}=> Φ v.
  Proof. rewrite tgl_wp_unfold /tgl_wp_pre to_of_val. auto. Qed.

  Lemma tgl_wp_strong_mono s1 s2 E1 E2 e Φ Ψ :
    E1 ⊆ E2 →
    WP e @ s1; E1 [{ Φ }] -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ WP e @ s2; E2 [{ Ψ }].
  Proof.
    iIntros (HE) "H HΦ". iRevert (E2 Ψ HE) "HΦ"; iRevert (e E1 Φ) "H".
    iApply tgl_wp_ind; first solve_proper.
    iIntros "!>" (e E1 Φ) "IH"; iIntros (E2 Ψ HE) "HΦ".
    rewrite !tgl_wp_unfold /tgl_wp_pre. destruct (to_val e) as [v|] eqn:?.
    { iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _). }    
    iIntros (σ1 ε1) "[Hs He]".
    iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
    iMod ("IH" with "[$Hs $He]") as "IH".
    iModIntro.
    iApply (glm_mono_pred with "[Hclose HΦ] IH").
    iIntros ([e' s] ε) "H".
    iMod "H". iMod "Hclose". iModIntro.
    iDestruct "H" as "[Hs[He Hk]]".
    iFrame. by iApply "Hk".
  Qed.

  
  Lemma fupd_tgl_wp s E e Φ : (|={E}=> WP e @ s; E [{ Φ }]) ⊢ WP e @ s; E [{ Φ }].
  Proof.
    rewrite tgl_wp_unfold /tgl_wp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?.
    { by iMod "H". }
    iIntros (s' ε) "[Hs He]".
    iMod "H". iApply "H". iFrame.
  Qed.
  Lemma tgl_wp_fupd s E e Φ : WP e @ s; E [{ v, |={E}=> Φ v }] ⊢ WP e @ s; E [{ Φ }].
  Proof. iIntros "H". iApply (tgl_wp_strong_mono with "H"); auto. Qed.

  Lemma tgl_wp_atomic s E1 E2 e Φ `{!Atomic StronglyAtomic e} :
    (|={E1,E2}=> WP e @ s; E2 [{ v, |={E2,E1}=> Φ v }]) ⊢ WP e @ s; E1 [{ Φ }].
  Proof.
    iIntros "H". rewrite !tgl_wp_unfold /tgl_wp_pre /=.
    destruct (to_val e) as [v|] eqn:He.
    { by iDestruct "H" as ">>> $". }
    iIntros (σ1 ε) "[Hs He]". iMod "H". iMod ("H" $! σ1 ε with "[$Hs $He]") as "H".
  iModIntro. iApply (glm_strong_mono with "[][]H"); [done|].
  iIntros (e2 σ2 ε2) "([%σ' %Hstep]&H)".
  iMod "H" as "(Hσ&Hε&Hwp)".
  rewrite !tgl_wp_unfold /tgl_wp_pre.
  destruct (to_val e2) as [?|] eqn:He2.
    + iFrame. do 2 (iMod "Hwp"). by do 2 iModIntro.
    + iMod ("Hwp" $! _ _ with "[Hσ Hε]") as "Hwp"; [iFrame|].
      specialize (atomic _ _ _ Hstep) as Hatomic. (* key step *)
      destruct Hatomic.
      congruence. (* how do we do this "by hand"? Not obvious to me *)
  Qed.

  Lemma tgl_wp_bind K `{!LanguageCtx K} s E e Φ :
    WP e @ s; E [{ v, WP K (of_val v) @ s; E [{ Φ }] }] ⊢ WP K e @ s; E [{ Φ }].
  Proof.
    revert Φ. cut (∀ Φ', WP e @ s; E [{ Φ' }] -∗ ∀ Φ,
                     (∀ v, Φ' v -∗ WP K (of_val v) @ s; E [{ Φ }]) -∗ WP K e @ s; E [{ Φ }]).
    { iIntros (help Φ) "H". iApply (help with "H"); auto. }
    iIntros (Φ') "H". iRevert (e E Φ') "H". iApply tgl_wp_ind; first solve_proper.
    iIntros "!>" (e E1 Φ') "IH". iIntros (Φ) "HΦ".
    rewrite /tgl_wp_pre. destruct (to_val e) as [v|] eqn:He.
    { apply of_to_val in He as <-. iApply fupd_tgl_wp. by iApply "HΦ". }
    rewrite tgl_wp_unfold /tgl_wp_pre fill_not_val //.
    iIntros (σ1 ε1) "[Hσ Hε]". iMod ("IH" with "[$]") as "IH".
    iModIntro.
    iApply glm_bind; [done|].
    iApply (glm_mono with "[][HΦ][$]"); first done.
    iIntros ([e' σ] ε) "H".
    iMod "H". iModIntro. iDestruct "H" as "[?[?K]]".
    iFrame. by iApply "K".
  Qed.

  Lemma tgl_wp_pgl_wp s E e Φ : WP e @ s; E [{ Φ }] -∗ WP e @ s; E {{ Φ }}.
  Proof.
    iIntros "H". iLöb as "IH" forall (E e Φ).
    rewrite pgl_wp_unfold tgl_wp_unfold /pgl_wp_pre /tgl_wp_pre. destruct (to_val e) as [v|]=>//=.
    iIntros (σ1 ε) "[Hσ Hε]". iMod ("H" with "[$Hσ $Hε]") as "H".
    iIntros "!>".
    iApply glm_mono_pred; last iFrame.
    iIntros ([e' s'] ε').
    iIntros "H". iNext. iMod "H" as "[?[?H]]".
    iModIntro. iFrame. iApply "IH". done.
  Qed.

  Lemma tgl_wp_pgl_wp' E e Φ : WP e @ E [{ Φ }] -∗ WP e @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iApply tgl_wp_pgl_wp.
    by destruct wp_default, twp_default.
  Qed.

  Lemma tgl_wp_pgl_wp_step s E e P Φ :
    TCEq (to_val e) None →
    ▷ P -∗
    WP e @ s; E [{ v, P ={E}=∗ Φ v }] -∗ WP e @ s; E {{ Φ }}.
  Proof.
    iIntros (?) "HP Hwp".
    iApply (pgl_wp_step_fupd _ _ E _ P with "[HP]"); [auto..|]. by iApply tgl_wp_pgl_wp.
  Qed.

  Lemma tgl_wp_pgl_wp_step' E e P Φ :
    TCEq (to_val e) None →
    ▷ P -∗
    WP e @ E [{ v, P ={E}=∗ Φ v }] -∗ WP e @ E {{ Φ }}.
  Proof.
    iIntros (?) "HP Hwp".
    iApply (pgl_wp_step_fupd _ _ E _ P with "[HP]"); [auto..|]. by iApply tgl_wp_pgl_wp'.
  Qed.
  

  (** * Derived rules *)
  Lemma tgl_wp_mono s E e Φ Ψ :
    (∀ v, Φ v ⊢ Ψ v) → WP e @ s; E [{ Φ }] ⊢ WP e @ s; E [{ Ψ }].
  Proof.
    iIntros (HΦ) "H"; iApply (tgl_wp_strong_mono with "H"); auto.
    iIntros (v) "?". by iApply HΦ.
  Qed.
  Lemma tgl_wp_mask_mono s E1 E2 e Φ :
    E1 ⊆ E2 → WP e @ s; E1 [{ Φ }] -∗ WP e @ s; E2 [{ Φ }].
  Proof. iIntros (?) "H"; iApply (tgl_wp_strong_mono with "H"); auto. Qed.
  Global Instance tgl_wp_mono' s E e :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) (twp (PROP:=iProp Σ) s E e).
  Proof. by intros Φ Φ' ?; apply tgl_wp_mono. Qed.

  Lemma tgl_wp_value_fupd s E Φ e v : IntoVal e v → WP e @ s; E [{ Φ }] ⊣⊢ |={E}=> Φ v.
  Proof. intros <-. by apply tgl_wp_value_fupd'. Qed.
  Lemma tgl_wp_value' s E Φ v : Φ v ⊢ WP (of_val v) @ s; E [{ Φ }].
  Proof. rewrite tgl_wp_value_fupd'. auto. Qed.
  Lemma tgl_wp_value s E Φ e v : IntoVal e v → Φ v ⊢ WP e @ s; E [{ Φ }].
  Proof. intros <-. apply tgl_wp_value'. Qed.

  Lemma tgl_wp_frame_l s E e Φ R : R ∗ WP e @ s; E [{ Φ }] ⊢ WP e @ s; E [{ v, R ∗ Φ v }].
  Proof. iIntros "[? H]". iApply (tgl_wp_strong_mono with "H"); auto with iFrame. Qed.
  Lemma tgl_wp_frame_r s E e Φ R : WP e @ s; E [{ Φ }] ∗ R ⊢ WP e @ s; E [{ v, Φ v ∗ R }].
  Proof. iIntros "[H ?]". iApply (tgl_wp_strong_mono with "H"); auto with iFrame. Qed.

  Lemma tgl_wp_wand s E e Φ Ψ :
    WP e @ s; E [{ Φ }] -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E [{ Ψ }].
  Proof.
    iIntros "H HΦ". iApply (tgl_wp_strong_mono with "H"); auto.
    iIntros (?) "?". by iApply "HΦ".
  Qed.
  Lemma tgl_wp_wand_l s E e Φ Ψ :
    (∀ v, Φ v -∗ Ψ v) ∗ WP e @ s; E [{ Φ }] -∗ WP e @ s; E [{ Ψ }].
  Proof. iIntros "[H Hwp]". iApply (tgl_wp_wand with "Hwp H"). Qed.
  Lemma tgl_wp_wand_r s E e Φ Ψ :
    WP e @ s; E [{ Φ }] ∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E [{ Ψ }].
  Proof. iIntros "[Hwp H]". iApply (tgl_wp_wand with "Hwp H"). Qed.
  Lemma tgl_wp_frame_wand s E e Φ R :
    R -∗ WP e @ s; E [{ v, R -∗ Φ v }] -∗ WP e @ s; E [{ Φ }].
  Proof.
    iIntros "HR HWP". iApply (tgl_wp_wand with "HWP").
    iIntros (v) "HΦ". by iApply "HΦ".
  Qed.

  Lemma tgl_wp_wp_step s E e P Φ :
    TCEq (to_val e) None →
    ▷ P -∗
    WP e @ s; E [{ v, P ={E}=∗ Φ v }] -∗ WP e @ s; E {{ Φ }}.
  Proof.
    iIntros (?) "HP Hwp".
    iApply (pgl_wp_step_fupd _ _ E _ P with "[HP]"); [auto..|]. by iApply tgl_wp_pgl_wp.
  Qed.
  
End tgl_wp.


(** Proofmode class instances *)
Section proofmode_classes.
  Context `{!erisWpGS Λ Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  Global Instance frame_tgl_wp p s E e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (WP e @ s; E [{ Φ }]) (WP e @ s; E [{ Ψ }]) | 2.
  Proof. rewrite /Frame=> HR. rewrite tgl_wp_frame_l. apply tgl_wp_mono, HR. Qed.

  Global Instance is_except_0_tgl_wp s E e Φ : IsExcept0 (WP e @ s; E [{ Φ }]).
  Proof. by rewrite /IsExcept0 -{2}fupd_tgl_wp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_tgl_wp p s E e P Φ :
    ElimModal True p false (|==> P) P (WP e @ s; E [{ Φ }]) (WP e @ s; E [{ Φ }]).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r wand_elim_r fupd_tgl_wp.
  Qed.

  Global Instance elim_modal_fupd_tgl_wp p s E e P Φ :
    ElimModal True p false (|={E}=> P) P (WP e @ s; E [{ Φ }]) (WP e @ s; E [{ Φ }]).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_tgl_wp.
  Qed.

  Global Instance elim_modal_fupd_tgl_wp_atomic p s E1 E2 e P Φ :
    ElimModal (Atomic StronglyAtomic e) p false
      (|={E1,E2}=> P) P
      (WP e @ s; E1 [{ Φ }]) (WP e @ s; E2 [{ v, |={E2,E1}=> Φ v }])%I | 100.
  Proof.
    intros ?. by rewrite intuitionistically_if_elim
                fupd_frame_r wand_elim_r tgl_wp_atomic.
  Qed.

  Global Instance add_modal_fupd_tgl_wp s E e P Φ :
    AddModal (|={E}=> P) P (WP e @ s; E [{ Φ }]).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_tgl_wp. Qed.
End proofmode_classes.

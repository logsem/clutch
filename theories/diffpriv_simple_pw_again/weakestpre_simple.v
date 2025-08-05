From Coq Require Export Reals Psatz.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre fixpoint big_op.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext NNRbar.
From clutch.common Require Export language erasable.
From clutch.base_logic Require Export spec_update.
From clutch.prob Require Export couplings_dp distribution.

From clutch.prob_lang.spec Require Export spec_ra.
From clutch.prob_lang Require Export class_instances.
From clutch.prob_lang Require Import tactics lang notation metatheory.

Import uPred.

Local Open Scope R.

Class diffprivWpGS (Σ : gFunctors) `{(* !spec_updateGS (lang_markov prob_lang) Σ,  *)!specG_prob_lang Σ} := DiffprivWpGS {
  #[global] diffprivWpGS_invGS :: invGS_gen HasNoLc Σ;

  state_interp : state → iProp Σ;
  err_interp : nonnegreal → nonnegreal -> iProp Σ;
}.
Global Opaque diffprivWpGS_invGS.
Global Arguments DiffprivWpGS {Σ _}.

Canonical Structure NNRO := leibnizO nonnegreal.
#[global] Hint Resolve cond_nonneg : core.


(** * The weakest precondition  *)
Definition wp_pre `{!specG_prob_lang Σ, !diffprivWpGS Σ}
    (wp : coPset -d> expr -d> (val -d> iPropO Σ) -d> iPropO Σ) :
     coPset -d> expr -d> (val -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
  (match to_val e1 with
   | Some v => |={E}=> Φ v
   | None =>
       ∀ σ1 e1' σ1' ε δ,
         state_interp σ1 ∗ spec_interp (e1', σ1') ∗ err_interp ε δ ={E,∅}=∗
         ⌜reducible (e1, σ1)⌝ ∗
         (* do good things happen if we require S to be reflexive? *)
         (∃ (S : cfg → cfg → Prop) (ε1 ε2 δ1 δ2 : nonnegreal) (k : nat),
           ⌜DPcoupl (prim_step e1 σ1) (pexec k (e1', σ1')) S ε1 δ1⌝ ∗
            ⌜ε1 + ε2 <= ε⌝ ∗ ⌜δ1 + δ2 <= δ⌝ ∗
            (∀ e2 σ2 e2' σ2',
                (⌜S (e2, σ2) (e2', σ2')⌝ ={∅}=∗
                 (▷ (|={∅,E}=> state_interp σ2 ∗ spec_interp (e2', σ2') ∗ err_interp ε2 δ2 ∗ wp E e2 Φ))
                (*  ∨
                   (∃ δ2' : val → nonnegreal, (⌜(∀ RES, 0 <= δ2' RES) ∧ ex_seriesC δ2' ∧ nonneg δ2 = SeriesC δ2'⌝ ∗ ▷ |={∅,E}=>
                     ∀ RES : val,
                       state_interp σ2 ∗ spec_interp (e2', σ2') ∗ err_interp ε2 (δ2' RES) ∗
                     wp E e2 (λ v, ∃ v' : val, ⤇ (of_val v') ∗ ⌜v = RES → v' = RES⌝))) *))))
           ∨
            (∃ e2, ⌜pure_step e1 e2⌝ ∗
             ∃ δ2' : val → nonnegreal,
                (⌜(∀ RES, 0 <= δ2' RES) ∧ ex_seriesC δ2'⌝ ∗
                 ▷ |={∅,E}=>
                   ∀ RES : val,
                     state_interp σ1 ∗ spec_interp (e1', σ1') ∗ err_interp ε (δ2' RES) ∗
                     wp E e2 (λ v, ∃ v' : val, ⤇ (of_val v') ∗ ⌜v = RES → v' = RES⌝)))
      end)%I.

Local Instance wp_pre_contractive `{!specG_prob_lang Σ, !diffprivWpGS Σ} :
  Contractive wp_pre.
Proof.
  rewrite /wp_pre /= => n wp wp' Hwp E e1 Φ.
  do 20 f_equiv. 1: do 20 f_equiv. all: f_contractive ; repeat f_equiv ; apply Hwp.
Qed.

Local Definition wp_def `{!specG_prob_lang Σ, !diffprivWpGS Σ} :
  Wp (iProp Σ) (expr) (val) () :=
  {| wp := λ _ : (), fixpoint (wp_pre); wp_default := () |}.
Local Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp' := wp_aux.(unseal).
Global Arguments wp' {Σ _}.
Global Existing Instance wp'.
Local Lemma wp_unseal `{!specG_prob_lang Σ, !diffprivWpGS Σ} : wp =
  (@wp_def Σ _ _).(wp).
Proof. rewrite -wp_aux.(seal_eq) //. Qed.

Section wp.
Context `{!specG_prob_lang Σ, !diffprivWpGS Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types v : val.
Implicit Types e : expr.
Implicit Types σ : state.
Implicit Types ρ : cfg.

(* Weakest pre *)
Lemma wp_unfold E e Φ s :
  WP e @ s; E {{ Φ }} ⊣⊢ wp_pre (wp (PROP:=iProp Σ) s) E e Φ.
Proof. rewrite wp_unseal. apply (fixpoint_unfold wp_pre). Qed.

Global Instance wp_ne E e n s :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp (PROP:=iProp Σ) s E e).
Proof.
  revert e. induction (lt_wf n) as [n _ IH]=> e Φ Ψ HΦ.
  rewrite !wp_unfold /wp_pre /=.
  do 40 f_equiv.
  f_contractive_fin.
  do 2 f_equiv. rewrite IH ; [done | lia |].
  intros ?. apply dist_S, HΦ.
Qed.
Global Instance wp_proper E e s :
  Proper (pointwise_relation _ (≡) ==> (≡)) (wp (PROP:=iProp Σ) s E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne=>v; apply equiv_dist.
Qed.
Global Instance wp_contractive E e n s :
  TCEq (to_val e) None →
  Proper (pointwise_relation _ (dist_later n) ==> dist n) (wp (PROP:=iProp Σ) s E e).
Proof.
  intros He Φ Ψ HΦ. rewrite !wp_unfold /wp_pre He /=.
  do 39 f_equiv.
  f_contractive.
  repeat f_equiv.
Qed.

Lemma wp_strong_mono E1 E2 e Φ Ψ s :
  E1 ⊆ E2 →
  WP e @ s; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ WP e @ s; E2 {{ Ψ }}.
Proof.
  intros ; iRevert (e Φ Ψ). iLöb as "IH". iIntros "%e1 %Φ %Ψ H HΦ".
  rewrite !wp_unfold /wp_pre /=.
  destruct (to_val e1) as [v|] eqn:?.
  { iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _). }
  iIntros (σ1 e1' σ1' ε δ) "[Hσ [Hs He]]".
  iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  (* feed resources to H *)
  iMod ("H" with "[$]") as "(red & %R & % & % & % & % & % & % & % & % & H)". iModIntro. iFrame "red".
  (* keep the same coupling (relation, errors) *)
  repeat iExists _ ; repeat (iSplit ; [done|]).
  (* assuming R... *)
  iIntros (???? HR). iSpecialize ("H" $! _ _ _ _ HR).
  (* ...we get a proof of the recursive WP from H *)
  iMod "H". iModIntro.
  iDestruct "H" as "[H|H]".
  - iLeft. iNext. iMod "H" as "(?&?&?& Hrec)". iFrame.
    iMod "Hclose" as "_". iModIntro.
    (* By IH, we can rewrite Ψ to Φ for WP e2. *)
    iApply ("IH" with "Hrec HΦ").
  - iRight. iDestruct "H" as "(%δ2' & hδ2 & H)". iExists δ2'. iFrame.
    iNext.
    iMod "H" as "H".
    iMod "Hclose" as "_". iModIntro.
    iIntros (RES). iDestruct ("H" $! RES) as "($&$&$&H)".
    iApply ("IH" with "H [HΦ]").
    iIntros "%v (%v' & rhs & %pw)". iFrame. done.
Qed.

Lemma fupd_wp E e Φ s: (|={E}=> WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre. iIntros "H".
  destruct (to_val e) as [v|] eqn:?. 1: by iMod "H".
  iIntros (?????) "(?&?&?)". by iMod ("H" with "[$]").
Qed.

(* Lemma wp_bind K `{!LanguageCtx K} E e Φ s :
     WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }} ⊢ WP K e @ s; E {{ Φ }}.
   Proof.
     iRevert (e). iLöb as "IH". iIntros (e1) "H".
     rewrite {1}wp_unfold /wp_pre. destruct (to_val e1) as [v|] eqn:He.
     { iApply fupd_wp. apply of_to_val in He as <-. iAssumption. }
     (* Non-value case. We have to show that there exists a coupling for K e1 and e1' and that WP holds for K v. *)
     rewrite {1}wp_unfold /wp_pre. ; rewrite fill_not_val /= ; [|done] ; iIntros (σ1 e1' σ1' ε δ) "Hs".
     (* Feed {state,spec,error} interpretation resources into H. *)
     iMod ("H" with "[$]") as "(%red & %R & % & % & % & % & %n & %HCR & %hε & %hδ & Hrec)".
     (* (K e1, σ1) is reducible because (e1, σ1) is. *)
     iModIntro ; iSplit ; [eauto using reducible_fill|].
     (* R' := the R-coupling from H "post-composed" with `fill K e1` *)
     iExists (λ '(e2, σ2) ρ', ∃ e2', e2 = K e2' ∧ R (e2', σ2) ρ').
     (* Keep the same error split. *)
     iExists ε1,ε2,δ1,δ2,n.
     (* Build the R'-coupling for K e1 & e1' from the R-coupling for e1 & e1' we got from H. *)
     repeat iSplit => //.
     { iPureIntro. rewrite fill_dmap //=.
       rewrite -(dret_id_right (pexec _ _)). rewrite /dmap.
       eapply (DPcoupl_dbind' ε1 0 _ δ1 0) ; [lra | done | lra | lra | | exact HCR ].
       intros [] ?? => /=. apply DPcoupl_dret; [done|done|]. eauto. }
     (* Assuming R' for K e2 (& e2'), we now show the recursive call: `▷ WP K e2 Φ` *)
     iIntros (Ke2 σ2 e2' σ2') "(%e2 & -> & %HR)".
     (* Get back resources from Hrec and strip later. *)
     iSpecialize ("Hrec" $! _ _ _ _ HR). iMod "Hrec" ; iModIntro.
     iNext. iMod "Hrec" as "($&$&$&Hrec)". iModIntro.
     (* By IH, we can push K into the postcondition... *)
     iApply "IH".
     (* and that's exactly what the recursive occurrence of WP in Hrec gives us. *)
     iApply "Hrec".
   Qed. *)

Lemma wp_value_fupd' E Φ v s : (|={E}=> Φ v) ⊢ WP of_val v @ s; E {{ Φ }}.
Proof. rewrite wp_unfold /wp_pre to_of_val. done. Qed.

Lemma wp_fupd s E e Φ : WP e @ s; E {{ v, |={E}=> Φ v }} ⊢ WP e @ s; E {{ Φ }}.
Proof. iIntros "H". iApply (wp_strong_mono E with "H"); auto. Qed.

(* Lemma wp_step_fupd s E1 E2 e P Φ :
     TCEq (to_val e) None → E2 ⊆ E1 →
     (|={E1}[E2]▷=> P) -∗ WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ s; E1 {{ Φ }}.
   Proof.
     rewrite !wp_unfold /wp_pre. iIntros (-> ?) "HR H".
     iIntros (σ1 e1' σ1' ??) "[Hσ [Hs He]]". iMod "HR".
     iMod ("H" with "[$]") as "(red & %R & % & % & % & % & % & % & % & % & H)".
     iModIntro. iFrame "red".
     iExists _,_,_,_,_,_. repeat iSplit => //.
     iIntros (???? HR).
     iMod ("H" $! _ _ _ _ HR) as "H". iModIntro. iNext.
     iMod "H" as "(?&?&?& Hwp)". iFrame.
     iMod "HR".
     iApply (wp_strong_mono E2 with "Hwp"); [done..|].
     iIntros "!>" (v) "H". by iApply "H".
   Qed. *)

(** * Derived rules *)
Lemma wp_mono E e Φ Ψ s : (∀ v, Φ v ⊢ Ψ v) → WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (wp_strong_mono with "H"); auto. iIntros. by iApply HΦ.
Qed.
Lemma wp_mask_mono E1 E2 e Φ s : E1 ⊆ E2 → WP e @ s; E1 {{ Φ }} ⊢ WP e @ s; E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (wp_strong_mono with "H"); auto. Qed.
Global Instance wp_mono' E e s :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.
Global Instance wp_flip_mono' E e s :
  Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (wp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.
Lemma wp_strong_mono'' e Φ Ψ :
  WP e {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e {{ Ψ }}.
Proof.
  iIntros "Hwp Hw". iApply (wp_strong_mono with "Hwp"); [done|]. iIntros. iApply "Hw". done.
Qed.

Lemma wp_value_fupd E Φ e v s : IntoVal e v → (|={E}=> Φ v) ⊢ WP e @ s; E {{ Φ }}.
Proof. intros <-. by apply wp_value_fupd'. Qed.
Lemma wp_value' E Φ v s : Φ v ⊢ WP (of_val v) @ s; E {{ Φ }}.
Proof. iIntros. by iApply wp_value_fupd. Qed.
Lemma wp_value E Φ e v s : IntoVal e v → Φ v ⊢ WP e @ s; E {{ Φ }}.
Proof. intros <-. apply wp_value'. Qed.

Lemma wp_frame_l E e Φ R s : R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof.
  iIntros "[? H]".
  iApply (wp_strong_mono with "H"); [done|]. iIntros. by iFrame.
Qed.
Lemma wp_frame_r E e Φ R s : WP e @ s; E {{ Φ }} ∗ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros "[H ?]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.


(* Lemma wp_frame_step_l E1 E2 e Φ R s :
     TCEq (to_val e) None → E2 ⊆ E1 →
     (|={E1}[E2]▷=> R) ∗ WP e @ s; E2 {{ Φ }} ⊢ WP e @ s; E1 {{ v, R ∗ Φ v }}.
   Proof.
     iIntros (??) "[Hu Hwp]". iApply (wp_step_fupd with "Hu"); try done.
     iApply (wp_mono with "Hwp"). by iIntros (?) "$$".
   Qed.
   Lemma wp_frame_step_r E1 E2 e Φ R s :
     TCEq (to_val e) None → E2 ⊆ E1 →
     WP e @ s; E2 {{ Φ }} ∗ (|={E1}[E2]▷=> R) ⊢ WP e @ s; E1 {{ v, Φ v ∗ R }}.
   Proof.
     rewrite [(WP _ @ _; _ {{ _ }} ∗ _)%I]comm.
     setoid_rewrite (comm _ _ R).
     apply wp_frame_step_l.
   Qed.
   Lemma wp_frame_step_l' E e Φ R s :
     TCEq (to_val e) None → ▷ R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
   Proof. iIntros (?) "[??]". iApply (wp_frame_step_l E E); try iFrame; eauto. Qed.
   Lemma wp_frame_step_r' E e Φ R s :
     TCEq (to_val e) None → WP e @ s; E {{ Φ }} ∗ ▷ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
   Proof. iIntros (?) "[??]". iApply (wp_frame_step_r E E); try iFrame; eauto. Qed. *)

Lemma wp_wand E e Φ Ψ s :
  WP e @ s; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (wp_strong_mono with "Hwp"); auto.
  iIntros. by iApply "H".
Qed.
Lemma wp_wand_l E e Φ Ψ s :
  (∀ v, Φ v -∗ Ψ v) ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_wand_r E e Φ Ψ s :
  WP e @ s; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_frame_wand E e Φ R s :
  R -∗ WP e @ s; E {{ v, R -∗ Φ v }} -∗ WP e @ s; E {{ Φ }}.
Proof.
  iIntros "HR HWP". iApply (wp_wand with "HWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.

End wp.

#[global] Hint Extern 0 (to_val _ = None) => assumption : typeclass_instances.
#[global] Hint Extern 0 (to_val _ = None) => reflexivity : typeclass_instances.

(** * Proofmode class instances *)
Section proofmode_classes.
  Context `{!specG_prob_lang Σ, !diffprivWpGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types v : val.
  Implicit Types e : expr.

  Global Instance frame_wp p E e R Φ Ψ s :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Ψ }}) | 2.
  Proof. rewrite /Frame=> HR. rewrite wp_frame_l. apply wp_mono, HR. Qed.

  Global Instance is_except_0_wp E e Φ s : IsExcept0 (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_wp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_wp p E e P Φ s :
    ElimModal True p false (|==> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r wand_elim_r fupd_wp.
  Qed.

  Global Instance elim_modal_fupd_wp p E e P Φ s :
    ElimModal True p false (|={E}=> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_wp.
  Qed.

  Global Instance add_modal_fupd_wp E e P Φ s :
    AddModal (|={E}=> P) P (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_wp. Qed.

  Global Instance elim_acc_wp_nonatomic {X} E α β γ e Φ s :
    ElimAcc (X:=X) True (fupd E E) (fupd E E)
            α β γ (WP e @ s; E {{ Φ }})
            (λ x, WP e @ s; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply wp_fupd.
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

Lemma spec_update_wp E e Φ a (He : to_val e = None) :
  spec_update E (WP e @ a; E {{ Φ }}) ⊢ WP e @ a; E {{ Φ }}.
Proof.
  iIntros "Hspec".
  iEval (rewrite !wp_unfold /wp_pre /=). rewrite He.
  iIntros (σ1 e1' σ1' ε δ) "(Hσ & Hs & Hε)".
  rewrite spec_update_unseal.
  iMod ("Hspec" with "Hs")
    as ([e2' σ2'] n Hstep%stepN_pexec_det) "(Hs & Hwp)".
  iEval (rewrite !wp_unfold /wp_pre /= He) in "Hwp".
  iMod ("Hwp" with "[$]") as "(% & %&%&%&%&%&%n'&%&%&%&h)".
  iModIntro. iSplit ; [done|]. iExists _,ε1,ε2,δ1,δ2,(n+n')%nat.
  iSplit.
  { iPureIntro. rewrite pexec_plus.
    apply pmf_1_eq_dret in Hstep.
    rewrite Hstep.
    rewrite dret_id_left. done.
  }
  iFrame. done.
Qed.


  #[global] Instance elim_modal_spec_update_wp P E e Ψ (_ : (to_val e = None)) :
    ElimModal True false false (spec_update E P) P (WP e @ E {{ Ψ }}) (WP e @ E {{ Ψ }}).
  Proof.
    iIntros (?) "[HP Hcnt]".
    iApply spec_update_wp => //.
    iMod "HP". iModIntro. by iApply "Hcnt".
  Qed.

  #[global] Instance elim_modal_spec_updateN_wp P E n e Ψ (_ : (to_val e = None)) :
    ElimModal True false false (spec_updateN n E P) P (WP e @ E {{ Ψ }}) (WP e @ E {{ Ψ }}).
  Proof.
    iIntros (?) "[HP Hcnt]".
    iDestruct (spec_updateN_implies_spec_update with "HP") as "> HP".
    by iApply "Hcnt".
  Qed.

End proofmode_classes.

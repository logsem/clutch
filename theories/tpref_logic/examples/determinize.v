From Coq Require Import Reals Psatz.
From clutch.prob_lang Require Import lang notation.
From clutch.tpref_logic Require Import weakestpre spec primitive_laws proofmode adequacy.
From clutch.prob Require Import distribution markov.
From clutch.tpref_logic.examples Require Import flip.
#[local] Open Scope R.

Definition determinize : val :=
  rec: "determinize" "f" "x" :=
    match: "f" "x" with
    | NONE => "determinize" "f" "x"
    | SOME "r" => "r"
    end.

(** * Higher-order spec w/model construction *)
Section backedge_markov.
  Context (δ : markov).
  Context (initial : mstate δ).
  Context (has_backedge : mstate δ → Prop).
  Context `{!∀ s, Decision (has_backedge s)}.
  Definition backedge_step (s : mstate δ) : distr (mstate δ) :=
    if bool_decide (has_backedge s) then dret initial else step s.
  Definition backedge_to_final (s : mstate δ) : option (mstate_ret δ) :=
    if bool_decide (has_backedge s) then None else to_final s.

  #[local] Definition model_mixin : MarkovMixin backedge_step backedge_to_final.
  Proof.
    rewrite /backedge_step /backedge_to_final.
    constructor. intros ? [] ?.
    case_bool_decide; [simplify_eq|by eapply to_final_is_final].
  Qed.

  Canonical Structure backedge_markov : markov := Markov _ _ model_mixin.

  Lemma backedge_markov_terminates :
    SeriesC (lim_exec (δ := δ) initial) = 1 →
    (∃ s a, ¬ has_backedge s ∧ to_final s = Some a → lim_exec (δ := δ) initial a > 0) →
    SeriesC (lim_exec (δ := backedge_markov) initial) = 1.
  Proof. Admitted.

End backedge_markov.

Section determinize_spec.
  Context (δ : markov).
  Context (initial : mstate δ).
  Context (has_backedge : mstate δ → Prop).
  Context `{!∀ s, Decision (has_backedge s)}.

  Notation model := (backedge_markov δ initial has_backedge).

  Context `{!tprG model Σ}.

  Lemma spec_backedge s E :
    has_backedge s →
    specF (s : mstate model) -∗ spec_update 1 E (specF (initial : mstate model)).
  Proof.
    iIntros (Hedge) "Hspec"; iIntros (s') "Hs".
    iDestruct (spec_auth_agree with "Hs Hspec") as %->.
    iExists initial.
    iMod (spec_auth_update with "Hs Hspec") as "[$ $]".
    iModIntro. iPureIntro.
    rewrite stepN_Sn /=.
    rewrite /backedge_step.
    rewrite bool_decide_eq_true_2 //.
    rewrite dret_id_left /=.
    by apply dret_1.
  Qed.

  Lemma wp_determinize (f v : val) :
    (∀ (w : val) ,
        ⟨⟨⟨ specF (initial : mstate model) ⟩⟩⟩
          f w
        ⟨⟨⟨ w s', RET w;
            specF (s' : mstate model) ∗
              ((⌜w = NONEV⌝ ∗ ⌜has_backedge s'⌝) ∨
          (∃ u, ⌜w = SOMEV u⌝ ∗ ⌜is_final s'⌝)) ⟩⟩⟩) -∗
    ⟨⟨⟨ specF (initial : mstate model) ⟩⟩⟩ determinize f v ⟨⟨⟨ w s', RET w; specF s' ∗ ⌜is_final s'⌝ ⟩⟩⟩.
  Proof.
    iIntros "#Hf".
    iLöb as "IH".
    iIntros (Ψ) "!# Hspec HΨ".
    wp_rec; wp_pures.
    wp_apply ("Hf" with "Hspec").
    iIntros (w s') "(Hspec & [[-> %] | (% & -> & %)])".
    - wp_pures.
      wp_apply rwp_spec_steps'.
      iSplitR "Hspec"; [|by iApply (spec_backedge with "Hspec")].
      iIntros "Hspec !>".
      by wp_apply ("IH" with "Hspec").
    - wp_pures. iApply "HΨ". iFrame. done.
  Qed.

End determinize_spec.

Section determinize_flip_spec.

  Definition flip_step (s : option bool) : distr (option bool) :=
    match s with
    | None => dmap Some fair_coin
    | Some _ => dzero
    end.

  Definition flip_to_final (s : option bool) : option bool := s.

  #[local] Definition flip_model_mixin : MarkovMixin flip_step flip_to_final.
  Proof. constructor. by intros [] [] []; simplify_eq=>/=. Qed.

  Canonical Structure flip_markov : markov := Markov _ _ flip_model_mixin.

  Lemma flip_markov_terminates :
    SeriesC (lim_exec None) = 1.
  Proof.
    rewrite lim_exec_step.
    rewrite step_or_final_no_final; [|auto].
    rewrite dbind_mass /=.
    rewrite SeriesC_finite_foldr /=.
    rewrite dmap_elem_ne; [|intros (?&?& [=])].
    rewrite Rmult_0_l.
    do 2 (erewrite dmap_elem_eq; [|apply _|done]).
    rewrite 2!fair_coin_pmf.
    do 2 (erewrite lim_exec_final; [|done]).
    rewrite 2!dret_mass.
    lra.
  Qed.

  Definition flip_has_backedge (s : option bool) := s = Some true.

  Instance flip_has_backedge_dec s : Decision (flip_has_backedge s).
  Proof. destruct s as [[]|]=>/=; [left|right|right]; done. Qed.

  Notation model := (backedge_markov flip_markov None flip_has_backedge).

  Lemma flip_couple :
    Rcoupl fair_coin (step (m := model) None)
      (λ b s, match s with Some b' => b = b' | None => False end).
  Proof.
    rewrite /= /backedge_step /=.
    rewrite bool_decide_eq_false_2; [|intros [=]].
    rewrite /dmap /=.
    rewrite -{1}(dret_id_right fair_coin).
    eapply Rcoupl_dbind; [|eapply Rcoupl_eq].
    intros ? [] ->; by eapply Rcoupl_dret.
  Qed.

  Context `{!tprG model Σ}.

  Lemma wp_determinize_flip :
    ⟨⟨⟨ specF (None : mstate model) ⟩⟩⟩
      determinize (λ: <>, if: flip then NONE else SOME #())%V #()
    ⟨⟨⟨ w, RET w; True ⟩⟩⟩.
  Proof.
    iIntros (Ψ1) "Hs HΨ1".
    wp_apply (wp_determinize with "[] Hs"); last first.
    { iIntros (? s) "[Hspec %Hf]". by iApply "HΨ1". }
    iIntros (w Ψ2) "!# Hspec HΨ2".
    wp_pures.
    wp_apply (rwp_couple_flip with "Hspec").
    { eapply flip_couple. }
    iIntros (? [bb |]) "[Hspec %]"; [|done]; subst.
    destruct bb; wp_pures.
    - iModIntro. iApply "HΨ2". iFrame. eauto.
    - iModIntro. iApply "HΨ2". iFrame. iRight.
      iExists _. iSplit; [done|]. iPureIntro.
      rewrite /is_final /= /backedge_to_final /=.
      rewrite bool_decide_eq_false_2 //; eauto.
  Qed.

End determinize_flip_spec.

(** * Higher-order spec w/o model construction *)
Section determinize_spec.
  Context `{tprG δ Σ}.

  Lemma wp_determinize' (f v : val) (s : mstate δ) :
    (∀ (P : iProp Σ) (w : val) (s : mstate δ),
        ⟨⟨⟨ specF s ∗ ⌜¬ is_final s⌝ ∗ ▷ P ⟩⟩⟩
          f w
        ⟨⟨⟨ w s', RET w; specF s' ∗ P ∗ ((⌜w = NONEV⌝ ∗ ⌜¬ is_final s'⌝) ∨ (∃ u, ⌜w = SOMEV u⌝ ∗ ⌜is_final s'⌝)) ⟩⟩⟩) -∗
    ⟨⟨⟨ specF s ∗ ⌜¬ is_final s⌝ ⟩⟩⟩ determinize f v ⟨⟨⟨ w s', RET w; specF s' ∗ ⌜is_final s'⌝ ⟩⟩⟩.
  Proof.
    iIntros "#Hf".
    iLöb as "IH" forall (s).
    iIntros (Ψ) "!# [Hspec %] HΨ".
    wp_rec; wp_pures.
    wp_apply ("Hf" with "[$Hspec $IH //]").
    iIntros (w s') "(Hspec & #IH' & [(-> & %) | (% & -> & %)])".
    - wp_pures. by iApply ("IH'" with "[$Hspec //]").
    - wp_pures. iApply "HΨ". iFrame. done.
  Qed.

End determinize_spec.

From clutch.tpref_logic.examples Require Import coin_random_walk.

Section determinize_flip_spec.
  (** We pick the simple coin-flipping model from the [coin_random_walk.v] *)
  Context `{!tprG random_walk Σ}.

  Lemma wp_determinize_flip' :
    ⟨⟨⟨ specF true ⟩⟩⟩
      determinize (λ: <>, if: flip then NONE else SOME #())%V #()
    ⟨⟨⟨ w, RET w; True ⟩⟩⟩.
  Proof.
    iIntros (Ψ1) "Hs HΨ1".
    wp_apply (wp_determinize' with "[] [$Hs]"); [|eauto|]; last first.
    { iIntros (? s) "[Hspec %Hf]". by iApply "HΨ1". }
    iIntros (P w s) "!#". iIntros (Ψ2) "(Hspec & % & HP) HΨ2".
    wp_pures.
    destruct s; [|exfalso; eauto].
    wp_apply (rwp_couple_flip _ (=) with "Hspec").
    { rewrite /= /rw_step. apply Rcoupl_eq. }
    iIntros ([] a2) "[Ha <-]"; wp_pures.
    - iModIntro. iApply "HΨ2". iFrame. eauto.
    - iModIntro. iApply "HΨ2". iFrame. eauto.
  Qed.

End determinize_flip_spec.

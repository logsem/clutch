(** * Derived laws for a fair coin flip *)
From iris.base_logic Require Import invariants na_invariants.
From iris.proofmode Require Import coq_tactics ltac_tactics sel_patterns environments reduction proofmode.
From self.prob_lang Require Import notation proofmode primitive_laws spec_rules spec_tactics.
From self.logrel Require Import model rel_rules rel_tactics.
From self.prelude Require Import base.
From self.examples.lib Require Import conversion.

Definition flipL : val := λ: "e", (int_to_bool (rand #1%nat from "e")).
Definition flip : expr := flipL #().
Definition allocB := alloc #1%nat.

Definition tapeB (bs : list bool) : tape := (1; bool_to_fin <$> bs).

Notation "l ↪B bs" := (l ↪ tapeB bs)%I
  (at level 20, format "l  ↪B  bs") : bi_scope.
Notation "l ↪ₛB bs" := (l ↪ₛ tapeB bs)%I
  (at level 20, format "l  ↪ₛB  bs") : bi_scope.

Section specs.
  Context `{clutchRGS Σ}.

  Lemma wp_allocB_tape E :
    {{{ True }}} allocB @ E {{{ α, RET #lbl:α; α ↪B [] }}}.
  Proof. iIntros (Φ) "_ HΦ". by iApply wp_alloc_tape. Qed.

  Lemma wp_flip E :
    {{{ True }}} flip @ E {{{ (b : bool), RET #(LitBool b); True }}}.
  Proof.
    iIntros (Φ) "_ HΦ". rewrite /flip /flipL.
    wp_pures.
    wp_bind (rand _ from _)%E.
    wp_apply (wp_rand 1 with "[//]").
    iIntros (?) "_ /=".
    wp_apply (wp_int_to_bool with "[//]").
    iIntros "_".
    by iApply "HΦ".
  Qed.

  Lemma wp_flip_tape E α b bs :
    {{{ ▷ α ↪B (b :: bs) }}} flipL #lbl:α @ E {{{ RET #(LitBool b); α ↪B bs }}}.
  Proof.
    iIntros (Φ) ">Hl HΦ". rewrite /flip /flipL.
    wp_pures.
    wp_bind (rand _ from _)%E.
    wp_apply (wp_rand_tape 1 with "Hl").
    iIntros "Hl /=".
    wp_apply (wp_int_to_bool with "[//]").
    iIntros "_".
    rewrite Z_to_bool_of_nat bool_to_fin_to_nat_inv.
    by iApply "HΦ".
  Qed.

  Lemma wp_flip_tape_empty E α :
    {{{ ▷ α ↪B [] }}} flipL #lbl:α @ E {{{ b, RET #(LitBool b); α ↪B [] }}}.
  Proof.
    iIntros (Φ) ">Hl HΦ". rewrite /flip /flipL.
    wp_pures.
    wp_bind (rand _ from _)%E.
    wp_apply (wp_rand_tape_empty with "Hl").
    iIntros (n) "Hl /=".
    wp_apply (wp_int_to_bool with "[//]").
    iIntros "_".
    by iApply "HΦ".
  Qed.

  Lemma refines_right_allocB_tape E K :
    nclose specN ⊆ E →
    refines_right K allocB ={E}=∗ ∃ α, refines_right K (#lbl: α) ∗ α ↪ₛB [].
  Proof.
    iIntros (?) "(?&?)".
    iMod (step_alloctape with "[$]") as (α) "[? ?]"; [done|].
    iModIntro; iExists _; iFrame. done.
  Qed.

  Lemma refines_right_flip_tape E K α (b : bool) bs :
    nclose specN ⊆ E →
    α ↪ₛB (b :: bs) -∗
    refines_right K (flipL #lbl:α) ={E}=∗ refines_right K #(LitBool b) ∗ α ↪ₛB bs.
  Proof.
    iIntros (?) "Hα Hr". rewrite /flipL.
    tp_pures.
    tp_bind (rand _ from _ )%E.
    rewrite refines_right_bind.
    iDestruct "Hr" as "[#Hinv Hr]".
    iMod (step_rand with "[$]") as "(_ & Hj & Hl) /="; [done|].
    iMod (refines_right_int_to_bool with "[$Hinv $Hj]") as "Hr"; [done|].
    rewrite Z_to_bool_of_nat bool_to_fin_to_nat_inv.
    by iFrame "Hr Hl".
  Qed.

  (** * Tape allocation  *)
  Lemma refines_allocB_tape_l K E t A :
    (▷ (∀ α : loc, α ↪B [] -∗ REL fill K (of_val #lbl:α) << t @ E : A))%I
    -∗ REL fill K allocB << t @ E : A.
  Proof. iIntros "?". by iApply refines_alloctape_l. Qed.

  Lemma refines_allocB_tape_r E K t A :
    (∀ α : loc, α ↪ₛB [] -∗ REL t << fill K (of_val #lbl:α) @ E : A)%I
    -∗ REL t << fill K allocB @ E : A.
  Proof. iIntros "?". by iApply refines_alloctape_r. Qed.

  (** * Unlabelled flip *)
  Lemma refines_flip_l E K t A :
     ▷ (∀ (b : bool), REL fill K (of_val #b) << t @ E : A)
    -∗ REL fill K flip << t @ E : A.
  Proof.
    iIntros "Hlog".
    iApply refines_wp_l.
    wp_apply (wp_flip with "[//]").
    eauto.
  Qed.

  (* TODO: [refines_flip_r] *)

  (** * Labelled flip  *)
  Lemma refines_flipL_empty_l K E α A e :
    α ↪B [] ∗
      (∀ (b : bool), α ↪B [] -∗ REL fill K (Val #b) << e @ E : A)
    ⊢ REL fill K (flipL #lbl:α) << e @ E : A.
  Proof.
    iIntros "[Hα H]".
    iApply refines_wp_l.
    by wp_apply (wp_flip_tape_empty with "Hα").
  Qed.

  Lemma refines_flipL_empty_r K E α A e :
    nclose specN ⊆ E →
    to_val e = None →
    α ↪ₛB [] ∗
      (∀ b : bool, α ↪ₛB [] -∗ REL e << fill K (Val #b) @ E : A)
    ⊢ REL e << fill K (flipL #lbl:α) @ E : A.
  Proof.
    iIntros (? ev) "[Hα H]". rewrite /flipL.
    rel_pures_r.
    rel_apply_r refines_rand_empty_r; [done|].
    iFrame.
    iIntros (n) "Hα".
    rel_apply_r refines_step_r.
    iIntros (K') "Hr".
    iMod (refines_right_int_to_bool with "[$]"); [done|].
    iModIntro; iExists _; iFrame.
    by iApply "H".
  Qed.

  Lemma refines_flipL_l E K α b bs t A :
    (▷ α ↪B (b :: bs) ∗
     ▷ (α ↪B bs -∗ REL fill K (of_val #b) << t @ E : A))
    -∗ REL fill K (flipL #lbl:α) << t @ E : A.
  Proof.
    iIntros "[Hα Hlog]".
    iApply refines_wp_l.
    by wp_apply (wp_flip_tape with "Hα").
  Qed.

  Lemma refines_flipL_r E K α b bs t A :
    α ↪ₛB (b :: bs)
    -∗ (α ↪ₛB bs -∗ REL t << fill K (of_val #b) @ E : A)
    -∗ REL t << (fill K (flipL #lbl:α)) @ E : A.
  Proof.
    iIntros "Hα Hlog".
    iApply refines_step_r.
    iIntros (k) "Hk".
    iMod (refines_right_flip_tape with "[$] [$]") as "[? ?]"; [done|].
    iModIntro; iExists _; iFrame. iApply ("Hlog" with "[$]").
  Qed.

  (** * Coupling rules (equality) *)
  Lemma refines_couple_flip_tapes E e1 e2 A α αₛ bs bsₛ :
    to_val e1 = None →
    (αₛ ↪ₛB bsₛ ∗ α ↪B bs ∗
       (∀ b, αₛ ↪ₛB (bsₛ ++ [b]) ∗ α ↪B (bs ++ [b]) -∗ REL e1 << e2 @ E : A))
    ⊢ REL e1 << e2 @ E : A.
  Proof.
    iIntros (?) "(Hαs & Hα & Hlog)".
    iApply refines_couple_tapes; [done|iFrame].
    iIntros (n) "[? ?]".
    destruct (bool_to_fin_surj n) as [b <-].
    rewrite -list_fmap_singleton -!fmap_app.
    iApply ("Hlog" $! b). iFrame.
  Qed.

  Lemma refines_couple_tape_flip K' E α A bs e :
    nclose specN ⊆ E →
    to_val e = None →
    α ↪B bs ∗
      (∀ b, α ↪B (bs ++ [b]) -∗ REL e << fill K' (of_val #b) @ E : A)
    ⊢ REL e << fill K' flip @ E : A.
  Proof.
    iIntros (??) "[Hα Hcnt]". rewrite /flip/flipL.
    rel_pures_r.
    rel_apply_r refines_couple_tape_rand; [done|iFrame].
    iIntros (n) "Hα".
    destruct (bool_to_fin_surj n) as [b <-].
    rewrite -list_fmap_singleton -!fmap_app.
    iSpecialize ("Hcnt" with "Hα").
    rel_apply_r refines_step_r.
    iIntros (K'') "Hr".
    iMod (refines_right_int_to_bool with "[$]"); [done|].
    iModIntro; iExists _; iFrame.
    rewrite Z_to_bool_of_nat bool_to_fin_to_nat_inv //.
  Qed.

  Lemma refines_couple_flip_tape K E α A bs e :
    α ↪ₛB bs ∗
      (∀ b, α ↪ₛB (bs ++ [b]) -∗ REL fill K (of_val #b) << e @ E : A)
    ⊢ REL fill K flip << e @ E : A.
  Proof.
    iIntros "[Hαs Hcnt]". rewrite /flip/flipL.
    rel_pures_l.
    rel_apply_l refines_couple_rand_tape; iFrame.
    iIntros (n) "Hα".
    destruct (bool_to_fin_surj n) as [b <-].
    rewrite -list_fmap_singleton -!fmap_app.
    iSpecialize ("Hcnt" with "Hα").
    iApply refines_wp_l.
    wp_apply (wp_int_to_bool with "[//]").
    iIntros "_".
    rewrite Z_to_bool_of_nat bool_to_fin_to_nat_inv //.
  Qed.

  Lemma refines_couple_flipL_flip K K' E α A :
    nclose specN ⊆ E →
    α ↪B [] ∗
      (∀ b : bool, α ↪B [] -∗ REL fill K (of_val #b) << fill K' (of_val #b) @ E : A)
    ⊢ REL fill K (flipL #lbl:α) << fill K' flip @ E : A.
  Proof.
    iIntros (?) "(Hα & H)".
    rel_pures_l.
    iApply refines_couple_tape_flip; [done| |].
    { rewrite fill_not_val //. }
    iFrame => /=. iIntros (b) "Hα".
    iApply (refines_flipL_l _ _ _ b []).
    iFrame. iApply "H".
  Qed.

  Lemma refines_couple_flip_flipL K K' E α A :
    α ↪ₛB [] ∗
      (∀ b : bool, α ↪ₛB [] -∗ REL fill K (of_val #b) << fill K' (of_val #b) @ E : A)
    ⊢ REL fill K flip << fill K' (flipL #lbl:α) @ E : A.
  Proof.
    iIntros "(Hα & H)".
    iApply refines_couple_flip_tape.
    iFrame.
    iIntros (n) "Hα".
    iApply (refines_flipL_r with "Hα").
    iIntros "α". by iApply "H".
  Qed.

  Lemma refines_couple_flip_flip K K' E A :
    nclose specN ⊆ E →
    (∀ b : bool, REL fill K (of_val #b) << fill K' (of_val #b) @ E : A)
    ⊢ REL fill K flip << fill K' flip @ E : A.
  Proof.
    iIntros (?) "Hcnt". rewrite /flip/flipL.
    rel_pures_l. rel_pures_r.
    rel_bind_l (rand _ from _)%E.
    rel_bind_r (rand _ from _)%E.
    rel_apply_l refines_couple_rands_lr.
    iIntros (n).
    iApply refines_wp_l.
    wp_apply (wp_int_to_bool with "[//]").
    iIntros "_".
    rel_apply_r refines_step_r.
    iIntros (K'') "Hr".
    iMod (refines_right_int_to_bool with "[$]"); [done|].
    iModIntro; iExists _; iFrame.
    done.
  Qed.

  (* TODO: non-equality couplings *)

End specs.

Lemma tac_rel_allocBtape_l_simpl `{!clutchRGS Σ} K ℶ1 ℶ2 e t A E :
  e = fill K allocB →
  MaybeIntoLaterNEnvs 1 ℶ1 ℶ2 →
  (envs_entails ℶ2 (∀ (α : loc),
     (α ↪B [] -∗ refines E (fill K (of_val #lbl:α)) t A))) →
  envs_entails ℶ1 (refines E e t A).
Proof. intros ???. by eapply tac_rel_alloctape_l_simpl. Qed.

Tactic Notation "rel_allocBtape_l" ident(l) "as" constr(H) :=
  rel_pures_l;
  first
    [rel_reshape_cont_l ltac:(fun K e' =>
       eapply (tac_rel_allocBtape_l_simpl K);
       [reflexivity (** e = fill K (Alloc e') *)
       |idtac..])
    |fail 1 "rel_allocBtape_l: cannot find 'allocB'"];
  [iSolveTC        (** IntoLaters *)
  |iIntros (l) H; rel_finish  (** new goal *)].

Lemma tac_rel_allocBtape_r `{!clutchRGS Σ} K' ℶ E e t A :
  t = fill K' allocB →
  nclose specN ⊆ E →
  envs_entails ℶ (∀ α, α ↪ₛB [] -∗ refines E e (fill K' #lbl:α) A) →
  envs_entails ℶ (refines E e t A).
Proof. intros ???. by eapply tac_rel_alloctape_r. Qed.

Tactic Notation "rel_allocBtape_r" ident(l) "as" constr(H) :=
  rel_pures_r;
  first
    [rel_reshape_cont_r ltac:(fun K e' =>
       eapply (tac_rel_allocBtape_r K);
       [reflexivity  (** t = K'[alloc t'] *)
       |idtac..])
    |fail 1 "rel_allocBtape_r: cannot find 'allocB'"];
  [solve_ndisj || fail "rel_allocBtape_r: cannot prove 'nclose specN ⊆ ?'"
  |iIntros (l) H; rel_finish  (** new goal *)].

Tactic Notation "rel_allocBtape_r" :=
  let l := fresh in
  let H := iFresh "H" in
  rel_alloctape_r l as H.

Tactic Notation "rel_allocBtape_l" :=
  let l := fresh in
  let H := iFresh "H" in
  rel_alloctape_l l as H.

Lemma tac_rel_flip_l `{!clutchRGS Σ} K ℶ1 ℶ2 i1 (α : loc) n ns e t tres A E :
  t = fill K (flipL #lbl:α) →
  envs_lookup i1 ℶ1 = Some (false, α ↪B (n::ns))%I →
  envs_simple_replace i1 false (Esnoc Enil i1 (α ↪B ns)) ℶ1 = Some ℶ2 →
  tres = fill K (of_val #n) →
  envs_entails ℶ2 (refines E tres e A) →
  envs_entails ℶ1 (refines E t e A).
Proof.
  rewrite envs_entails_unseal.
  intros ???? Hg.
  subst t tres.
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id.
  rewrite Hg.
  rewrite -(refines_flipL_l _ K).
  rewrite -bi.later_sep.
  apply bi.later_intro.
Qed.

Lemma tac_rel_flip_r `{!clutchRGS Σ} K ℶ1 ℶ2 E i1 (α : loc) n ns e t tres A :
  t = fill K (flipL (#lbl:α)) →
  nclose specN ⊆ E →
  envs_lookup i1 ℶ1 = Some (false, α ↪ₛB (n::ns))%I →
  envs_simple_replace i1 false (Esnoc Enil i1 (α ↪ₛB ns)) ℶ1 = Some ℶ2 →
  tres = fill K (of_val #n) →
  envs_entails ℶ2 (refines E e tres A) →
  envs_entails ℶ1 (refines E e t A).
Proof.
  rewrite envs_entails_unseal.
  intros ????? Hg.
  subst t tres.
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id.
  rewrite (refines_flipL_r _ K) //.
  rewrite Hg.
  apply bi.wand_elim_l.
Qed.

Tactic Notation "rel_flipL_l" :=
  let solve_mapsto _ :=
    let α := match goal with |- _ = Some (_, (?α ↪B _)%I) => α end in
    iAssumptionCore || fail "rel_flip_l: cannot find" α "↪B ?" in
  rel_pures_l;
  first
    [rel_reshape_cont_l ltac:(fun K e' =>
       eapply (tac_rel_flip_l K); [reflexivity|..])
    |fail 1 "rel_flip_l: cannot find 'flip'"];
  (* the remaining goals are from tac_rel_flip_l (except for the first one, which has already been solved by this point) *)
  [solve_mapsto ()
  |pm_reflexivity || fail "rel_flip_l: this should not happen O-:"
  |reflexivity
  |rel_finish  (** new goal *)].

Tactic Notation "rel_flipL_r" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↪ₛB _)%I) => l end in
    iAssumptionCore || fail "rel_flip_r: cannot find" l "↪ₛB ?" in
  rel_pures_r;
  first
    [rel_reshape_cont_r ltac:(fun K e' =>
       eapply (tac_rel_flip_r K); [reflexivity|..])
    |fail 1 "rel_flip_r: cannot find 'flip'"];
  (* the remaining goals are from tac_rel_flip_r (except for the first one, which has already been solved by this point) *)
  [solve_ndisj || fail "rel_flip_r: cannot prove 'nclose specN ⊆ ?'"
  |solve_mapsto ()
  |pm_reflexivity || fail "rel_flip_r: this should not happen O-:"
  |reflexivity
  |rel_finish  (** new goal *)].

Global Opaque flip flipL allocB tapeB.


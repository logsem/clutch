(** * The tapes of [DH_KE] are a proof device

    [DH_KE] presamples its exponents on tapes; [DH_KE_tapeless] samples them
    directly.  The two refine each other at the interface of [DH_KE].  Both
    share the core [dh_core], typed once in [dhke_typing] for any type of the
    tape variables; here the tape variables relate a tape of one program,
    which stays empty, to the unit of the other ([rand #n] is
    [rand(#()) #n]). *)
From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import primitive_laws proofmode spec_rules spec_ra
  class_instances tactics metatheory logic.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_row sem_sig sem_env
  sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze.uc Require Import comp_operators uc_systems.
From clutch.prob_eff_lang.probblaze.examples Require Import dhke_common dhke_typing.
From clutch.prob_eff_lang.probblaze.examples.dhke Require Import dhke_def.

Section dhke_tapeless.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.

  Import valgroup_notation.
  Import typed_hint_modes.
  #[local] Notation n := (S n'').

  Definition tapeN : namespace := nroot .@ "tapeless".

  (* A tape of the left program, which stays empty, against the unit. *)
  Definition tape_l : sem_ty Σ := λ v1 v2,
    (∃ α : loc, ⌜v1 = #lbl:α⌝ ∗ ⌜v2 = #()%V⌝ ∗ na_invP (tapeN .@ α) (α ↪N (n; [])))%I.
  (* The mirror image: a tape of the right program. *)
  Definition tape_r : sem_ty Σ := λ v1 v2,
    (∃ α : loc, ⌜v1 = #()%V⌝ ∗ ⌜v2 = #lbl:α⌝ ∗ na_invP (tapeN .@ α) (α ↪ₛN (n; [])))%I.

  Global Instance tape_l_multi : MultiT tape_l.
  Proof. constructor. iIntros "!#" (v1 v2) "#H". rewrite /sem_ty_mbang /=. by iModIntro. Qed.
  Global Instance tape_r_multi : MultiT tape_r.
  Proof. constructor. iIntros "!#" (v1 v2) "#H". rewrite /sem_ty_mbang /=. by iModIntro. Qed.

  Lemma sem_typed_alloctape_l Γ ρ : ⊢ sem_typed Γ (alloc #n) #()%V ρ tape_l Γ.
  Proof.
    iIntros "!# %γ HΓ /=".
    iApply (brel_alloctape_l [] n). iIntros "!> %α Hα".
    iApply (brel_na_alloc (α ↪N (n; [])) (tapeN .@ α)). iFrame "Hα". iIntros "#Hinv".
    iApply brel_value. iIntros "$ !>". iFrame. iExists α. by iFrame "Hinv".
  Qed.

  Lemma sem_typed_alloctape_r Γ ρ : ⊢ sem_typed Γ #()%V (alloc #n) ρ tape_r Γ.
  Proof.
    iIntros "!# %γ HΓ /=".
    iApply (brel_alloctape_r [] n). iIntros "%α Hα".
    iApply (brel_na_alloc (α ↪ₛN (n; [])) (tapeN .@ α)).
    iSplitL "Hα"; first by iApply empty_to_spec_tapeN. iIntros "#Hinv".
    iApply brel_value. iIntros "$ !>". iFrame. iExists α. by iFrame "Hinv".
  Qed.

  (* Reading the empty tape of the left program against an untaped [rand]:
     presample onto the tape, coupled with the right [rand], then read. *)
  Lemma sem_typed_rand_tape_l Γ1 Γ2 ρ e e' :
    ⊢ sem_typed Γ1 e e' ρ tape_l Γ2 -∗ sem_typed Γ1 (rand(e) #n) (rand(e') #n) ρ ℕ Γ2.
  Proof.
    iIntros "#He !# %γ HΓ1 /=".
    iApply (brel_bind [RandRCtx _] [RandRCtx _]); [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
    iApply (brel_wand with "[HΓ1]"); first by iApply "He".
    iIntros "!# % % ((%α & -> & -> & #Hinv) & HΓ2) /=".
    iApply (brel_na_inv _ _ (tapeN .@ α)); [done|]. iFrame "Hinv".
    iIntros "(>Hα & Hclose)".
    iDestruct (tapeN_to_empty with "Hα") as "Hα".
    iApply (brel_couple_TU _ _ _ []); [done|]. iFrame "Hα". iIntros (k) "Hα /=".
    iAssert (α ↪N (n; [fin_to_nat k]))%I with "[Hα]" as "Hα".
    { iExists [k]. by iFrame. }
    brel_rand_l.
    iApply brel_na_close. iFrame "Hclose Hα".
    iApply brel_value. iIntros "$ !>". iFrame. by iExists _.
  Qed.

  Lemma sem_typed_rand_tape_r Γ1 Γ2 ρ e e' :
    ⊢ sem_typed Γ1 e e' ρ tape_r Γ2 -∗ sem_typed Γ1 (rand(e) #n) (rand(e') #n) ρ ℕ Γ2.
  Proof.
    iIntros "#He !# %γ HΓ1 /=".
    iApply (brel_bind [RandRCtx _] [RandRCtx _]); [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
    iApply (brel_wand with "[HΓ1]"); first by iApply "He".
    iIntros "!# % % ((%α & -> & -> & #Hinv) & HΓ2) /=".
    iApply (brel_na_inv _ _ (tapeN .@ α)); [done|]. iFrame "Hinv".
    iIntros "(>Hα & Hclose)".
    iApply (brel_couple_UT _ _ (λ k : nat, k) []); [done|]. iFrame "Hα".
    iIntros "!>" (k) "% Hα /=".
    brel_rand_r.
    iApply brel_na_close. iFrame "Hclose Hα".
    iApply brel_value. iIntros "$ !>". iFrame. by iExists _.
  Qed.

  Lemma tape_l_sampler_typed : ⊢ sampler_typed tape_l.
  Proof using All.
    iIntros "!>" (x Γ) "#Hx". rewrite /samplelbl.
    iApplyT sem_typed_let; first iApplyT sem_typed_unit'.
    by iApply sem_typed_rand_tape_l.
    Unshelve. all: solve_typed_side.
  Qed.

  Lemma tape_r_sampler_typed : ⊢ sampler_typed tape_r.
  Proof using All.
    iIntros "!>" (x Γ) "#Hx". rewrite /samplelbl.
    iApplyT sem_typed_let; first iApplyT sem_typed_unit'.
    by iApply sem_typed_rand_tape_r.
    Unshelve. all: solve_typed_side.
  Qed.

  (* The setup of the two programs, then the shared core at the tape type
     [τt]: [DH_KE_typed] with the tape allocations replaced. *)
  Local Ltac tapeless_rel alloc_rule sampler :=
    rewrite DH_KE_core_eq /DH_KE_tapeless; iApply fac_closure;
    do 2 (iApplyT sem_typed_let; first iApply alloc_rule);
    do 2 (iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_none));
    iApply sem_typed_sub_nil; iApply (sem_typed_oval _ [_; _; _; _]); iApply sem_typed_RLam; iIntros (θ);
    iApplyT sem_oval_typed_afun;
    iApply (sem_typed_oval _ [_; _; _; _; _]); iApply sem_typed_RLam; iIntros (θ₂);
    iApplyT sem_oval_typed_afun; simpl;
    iApplyT (sem_typed_sub_env _ [("f", _); ("effs", _); ("α", _); ("β", _); ("l1", _); ("l2", _)]);
    [simpl; env_solve16|];
    iApply dh_core_typed; iApply sampler.

  Lemma DH_KE_DH_KE_tapeless m : ⊢ ⊨ᵥ DH_KE ≤ DH_KE_tapeless : fac m (τ__F chan gk).
  Proof using All.
    tapeless_rel sem_typed_alloctape_l tape_l_sampler_typed.
    Unshelve. all: solve_typed_side.
  Qed.

  Lemma DH_KE_tapeless_DH_KE m : ⊢ ⊨ᵥ DH_KE_tapeless ≤ DH_KE : fac m (τ__F chan gk).
  Proof using All.
    tapeless_rel sem_typed_alloctape_r tape_r_sampler_typed.
    Unshelve. all: solve_typed_side.
  Qed.

End dhke_tapeless.

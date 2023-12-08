From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Import fancy_updates.
From iris.base_logic.lib Require Export ghost_map.

From clutch.tpref_logic Require Import weakestpre spec ectx_lifting.
From clutch.prob_lang Require Export class_instances.
From clutch.prob_lang Require Import tactics lang notation.
From clutch.prob Require Import distribution.

Class tprGpreS δ Σ := TprGpreS {
  tprGpre_iris  : invGpreS Σ;
  tprGpre_heap  : ghost_mapG Σ loc val;
  tprGpre_tapes : ghost_mapG Σ loc tape;
  tprGpre_spec  : specPreG δ Σ;
}.

#[export] Existing Instance tprGpre_iris.
#[export] Existing Instance tprGpre_heap.
#[export] Existing Instance tprGpre_tapes.
#[export] Existing Instance tprGpre_spec.

Definition tprΣ δ : gFunctors :=
  #[invΣ;
    ghost_mapΣ loc val;
    ghost_mapΣ loc tape;
    specΣ δ].
#[export] Instance subG_tprGPreS {δ Σ} : subG (tprΣ δ) Σ → tprGpreS δ Σ.
Proof. solve_inG. Qed.

Class tprG (δ : markov) (Σ : gFunctors) := TprG {
  tprG_invG : invGS_gen HasNoLc Σ;
  tprG_heap  : ghost_mapG Σ loc val;
  tprG_tapes : ghost_mapG Σ loc tape;
  tprG_heap_name : gname;
  tprG_tapes_name : gname;
  tprG_specG : specG δ Σ;
}.
#[export] Existing Instance tprG_specG.

Definition heap_auth `{tprG δ Σ} :=
  @ghost_map_auth _ _ _ _ _ tprG_heap tprG_heap_name.
Definition tapes_auth `{tprG δ Σ} :=
  @ghost_map_auth _ _ _ _ _ tprG_tapes tprG_tapes_name.

#[export] Instance tprG_tprwpG `{tprG δ Σ} : tprwpG prob_lang Σ := {
  iris_invGS := tprG_invG;
  state_interp σ := (heap_auth 1 σ.(heap) ∗ tapes_auth 1 σ.(tapes))%I;
}.

(** Heap *)
Notation "l ↦{ dq } v" := (@ghost_map_elem _ _ _ _ _ tprG_heap tprG_heap_name l dq v)
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Notation "l ↦□ v" := (l ↦{ DfracDiscarded } v)%I
  (at level 20, format "l  ↦□  v") : bi_scope.
Notation "l ↦{# q } v" := (l ↦{ DfracOwn q } v)%I
  (at level 20, format "l  ↦{# q }  v") : bi_scope.
Notation "l ↦ v" := (l ↦{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↦  v") : bi_scope.

(** Tapes *)
Notation "l ↪{ dq } v" := (@ghost_map_elem _ _ _ _ _ tprG_tapes tprG_tapes_name l dq (v : tape))
  (at level 20, format "l  ↪{ dq }  v") : bi_scope.
Notation "l ↪□ v" := (l ↪{ DfracDiscarded } v)%I
  (at level 20, format "l  ↪□  v") : bi_scope.
Notation "l ↪{# q } v" := (l ↪{ DfracOwn q } v)%I
  (at level 20, format "l  ↪{# q }  v") : bi_scope.
Notation "l ↪ v" := (l ↪{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↪  v") : bi_scope.

#[export] Existing Instance spec_auth_spec.

Section rwp.
  Context `{!tprG δ Σ}.

  (** * RSWP  *)
  Lemma rswp_alloc k E v a :
    ⟨⟨⟨ True ⟩⟩⟩ ref v at k @ a; E ⟨⟨⟨ l, RET #l; l ↦ v  ⟩⟩⟩.
  Proof.
    iIntros (Φ) "_ HΦ".
    iApply rswp_lift_atomic_head_step.
    iIntros (σ1) "[Hh Ht] !# !>".
    iSplit; [by eauto with head_step|].
    iIntros (e2 σ2 Hs); inv_head_step.
    iMod ((ghost_map_insert (fresh_loc σ1.(heap)) v) with "Hh") as "[$ Hl]".
    { apply not_elem_of_dom, fresh_loc_is_fresh. }
    iIntros "!>". iFrame. by iApply "HΦ".
  Qed.

  Lemma rswp_load k E l q v a :
    ⟨⟨⟨ ▷ l ↦{q} v ⟩⟩⟩ ! #l at k @ a; E ⟨⟨⟨ RET v; l ↦{q} v ⟩⟩⟩.
  Proof.
    iIntros (Φ) ">Hl HΦ". iApply rswp_lift_atomic_head_step.
    iIntros (σ1) "[Hh Ht] !> !>".
    iDestruct (ghost_map_lookup with "Hh Hl") as %?.
    iSplit; [by eauto with head_step|].
    iIntros (v2 σ2 Hstep); inv_head_step.
    iModIntro. iFrame. by iApply "HΦ".
  Qed.

  Lemma rswp_store k E l v' v a :
    ⟨⟨⟨ ▷ l ↦ v' ⟩⟩⟩ #l <- v at k @ a; E ⟨⟨⟨ RET #(); l ↦ v ⟩⟩⟩.
  Proof.
    iIntros (Φ) ">Hl HΦ".
    iApply rswp_lift_atomic_head_step.
    iIntros (σ1) "[Hh Ht] !>".
    iDestruct (ghost_map_lookup with "Hh Hl") as %?.
    iSplit; [by eauto with head_step|].
    iIntros "!> /=" (e2 σ2 Hs); inv_head_step.
    iMod (ghost_map_update with "Hh Hl") as "[$ Hl]".
    iFrame. iModIntro. by iApply "HΦ".
  Qed.

  Lemma rswp_rand (N : nat) (z : Z) k E a :
    TCEq N (Z.to_nat z) →
    ⟨⟨⟨ True ⟩⟩⟩ rand #z at k @ a; E ⟨⟨⟨ (n : fin (S N)), RET #n; True ⟩⟩⟩.
  Proof.
    iIntros (-> Φ) "_ HΦ".
    iApply rswp_lift_atomic_head_step.
    iIntros (σ1) "Hσ !#".
    iSplit; [eauto with head_step|].
    Unshelve.
    2 : { apply 0%fin . }
    iIntros "!>" (e2 σ2 Hs).
    inv_head_step.
    iFrame.
    by iApply ("HΦ" $! x) .
  Qed.

  (** Tapes  *)
  Lemma rswp_alloc_tape N z E s k :
    TCEq N (Z.to_nat z) →
    ⟨⟨⟨ True ⟩⟩⟩ alloc #z at k @ s; E ⟨⟨⟨ α, RET #lbl:α; α ↪ (N; []) ⟩⟩⟩.
  Proof.
    iIntros (-> Φ) "_ HΦ".
    iApply rswp_lift_atomic_head_step.
    iIntros (σ1) "(Hh & Ht) !# /=".
    iSplit; [by eauto with head_step|].
    iIntros "!>" (e2 σ2 Hs); inv_head_step.
    iMod (ghost_map_insert (fresh_loc σ1.(tapes)) with "Ht") as "[$ Hl]".
    { apply not_elem_of_dom, fresh_loc_is_fresh. }
    iFrame. iModIntro.
    by iApply "HΦ".
  Qed.

  Lemma rswp_rand_tape N α n ns z E s k :
    TCEq N (Z.to_nat z) →
    ⟨⟨⟨ ▷ α ↪ (N; n :: ns) ⟩⟩⟩ rand(#lbl: α) #z at k @ s; E ⟨⟨⟨ RET #(LitInt n); α ↪ (N; ns) ⟩⟩⟩.
  Proof.
    iIntros (-> Φ) ">Hl HΦ".
    iApply rswp_lift_atomic_head_step.
    iIntros (σ1) "(Hh & Ht) !#".
    iDestruct (ghost_map_lookup with "Ht Hl") as %?.
    iSplit; [eauto with head_step|].
    iIntros "!>" (e2 σ2 Hs).
    inv_head_step.
    iMod (ghost_map_update with "Ht Hl") as "[$ Hl]".
    iFrame. iModIntro.
    by iApply "HΦ".
  Qed.

  Lemma rswp_rand_tape_empty N z α E s k :
    TCEq N (Z.to_nat z) →
    ⟨⟨⟨ ▷ α ↪ (N; []) ⟩⟩⟩ rand(#lbl:α) #z at k @ s; E ⟨⟨⟨ (n : fin (S N)), RET #(LitInt n); α ↪ (N; []) ⟩⟩⟩.
  Proof.
    iIntros (-> Φ) ">Hl HΦ".
    iApply rswp_lift_atomic_head_step.
    iIntros (σ1) "(Hh & Ht) !#".
    iDestruct (ghost_map_lookup with "Ht Hl") as %?.
    iSplit; [by eauto with head_step|].
    Unshelve.
    2 : { apply 0%fin. }
    iIntros "!>" (e2 σ2 Hs).
    inv_head_step.
    iFrame.
    iModIntro. iApply ("HΦ" with "[$Hl //]").
  Qed.

  Lemma rswp_rand_tape_wrong_bound N M z α E ns s k :
    TCEq N (Z.to_nat z) →
    N ≠ M →
    ⟨⟨⟨ ▷ α ↪ (M; ns) ⟩⟩⟩ rand(#lbl:α) #z at k @ s; E ⟨⟨⟨ (n : fin (S N)), RET #(LitInt n); α ↪ (M; ns) ⟩⟩⟩.
  Proof.
    iIntros (-> ? Φ) ">Hl HΦ".
    iApply rswp_lift_atomic_head_step.
    iIntros (σ1) "(Hh & Ht) !#".
    iDestruct (ghost_map_lookup with "Ht Hl") as %?.
    iSplit; [by eauto with head_step|].
    Unshelve.
    2 : { apply 0%fin. }
    iIntros "!>" (e2 σ2 Hs).
    inv_head_step.
    iFrame.
    iModIntro.
    iApply ("HΦ" with "[$Hl //]").
  Qed.

  (** * RWP  *)
  Lemma rwp_alloc E v a :
    ⟨⟨⟨ True ⟩⟩⟩ ref v @ a; E ⟨⟨⟨ l, RET #l; l ↦ v ⟩⟩⟩.
  Proof.
    iIntros (Φ) "H HΦ".
    iApply rwp_no_step.
    by iApply (rswp_alloc with "H HΦ").
  Qed.

  Lemma rwp_load E l q v a :
    ⟨⟨⟨ ▷ l ↦{q} v ⟩⟩⟩ ! #l @ a; E ⟨⟨⟨ RET v; l ↦{q} v ⟩⟩⟩.
  Proof.
    iIntros (Φ) "H HΦ".
    iApply rwp_no_step.
    by iApply (rswp_load with "H HΦ").
  Qed.

  Lemma rwp_store E l v' v a :
    ⟨⟨⟨ ▷ l ↦ v' ⟩⟩⟩ #l <- v @ a; E ⟨⟨⟨ RET #(); l ↦ v ⟩⟩⟩.
  Proof.
    iIntros (Φ) "H HΦ".
    iApply rwp_no_step.
    by iApply (rswp_store with "H HΦ").
  Qed.

  Lemma rwp_rand (N : nat) (z : Z) E a :
    TCEq N (Z.to_nat z) →
    ⟨⟨⟨ True ⟩⟩⟩ rand #z @ a; E ⟨⟨⟨ (n : fin (S N)), RET #n; True ⟩⟩⟩.
  Proof.
    iIntros (? Φ) "H HΦ".
    iApply rwp_no_step.
    by iApply (rswp_rand with "H HΦ").
  Qed.

  Lemma rwp_alloc_tape N z E s :
    TCEq N (Z.to_nat z) →
    ⟨⟨⟨ True ⟩⟩⟩ alloc #z @ s; E ⟨⟨⟨ α, RET #lbl:α; α ↪ (N; []) ⟩⟩⟩.
  Proof.
    iIntros (? Φ) "H HΦ".
    iApply rwp_no_step.
    by iApply (rswp_alloc_tape with "H HΦ").
  Qed.

  Lemma rwp_rand_tape N α n ns z E s :
    TCEq N (Z.to_nat z) →
    ⟨⟨⟨ ▷ α ↪ (N; n :: ns) ⟩⟩⟩ rand(#lbl: α) #z @ s; E ⟨⟨⟨ RET #(LitInt n); α ↪ (N; ns) ⟩⟩⟩.
  Proof.
    iIntros (-> Φ) ">Hl HΦ".
    iApply rwp_no_step.
    by iApply (rswp_rand_tape with "Hl HΦ").
  Qed.

  Lemma rwp_rand_tape_empty N z α E s :
    TCEq N (Z.to_nat z) →
    ⟨⟨⟨ ▷ α ↪ (N; []) ⟩⟩⟩ rand(#lbl:α) #z @ s; E ⟨⟨⟨ (n : fin (S N)), RET #(LitInt n); α ↪ (N; []) ⟩⟩⟩.
  Proof.
    iIntros (-> Φ) ">Hl HΦ".
    iApply rwp_no_step.
    by iApply (rswp_rand_tape_empty with "Hl HΦ").
  Qed.

  Lemma rwp_rand_tape_wrong_bound N M z α E ns s :
    TCEq N (Z.to_nat z) →
    N ≠ M →
    ⟨⟨⟨ ▷ α ↪ (M; ns) ⟩⟩⟩ rand(#lbl:α) #z @ s; E ⟨⟨⟨ (n : fin (S N)), RET #(LitInt n); α ↪ (M; ns) ⟩⟩⟩.
  Proof.
    iIntros (-> ? Φ) ">Hl HΦ".
    iApply rwp_no_step.
    by iApply (rswp_rand_tape_wrong_bound with "Hl HΦ").
  Qed.

End rwp.

Section coupl.
  Context `{!tprG δ Σ}.

  Lemma rwp_couple (N : nat) (z : Z) E R a1 a :
    TCEq N (Z.to_nat z) →
    Rcoupl (dunifP N) (step a1) R →
    {{{ specF a1 }}} rand #z @ a; E {{{ (n : fin (S N)) a2, RET #n; specF a2 ∗ ⌜R n a2⌝ }}}.
  Proof.
    iIntros (-> ? Φ) "Ha HΦ /=".
    iApply rwp_lift_step_fupd_coupl; [done|].
    iIntros (σ1 m) "[Hσ1 HaA]".
    iDestruct (spec_auth_agree with "HaA Ha") as %->.
    iApply fupd_mask_intro; [set_solver|].
    iIntros "Hclose".
    assert (head_reducible (rand #z) σ1) as hr.
    { eexists (_, _).
      apply head_step_support_equiv_rel.
      by eapply (RandNoTapeS _ _ 0%fin). }
    iApply rwp_coupl_steps.
    iExists (λ '(e2, σ2) a2, ∃ (n : fin _), e2 = Val #n ∧ σ2 = σ1 ∧ R n a2).
    iSplit.
    { iPureIntro. by apply head_prim_reducible. }
    iSplit.
    { iPureIntro. simpl.
      rewrite head_prim_step_eq //=.
      rewrite -(dret_id_right (step _)).
      eapply Rcoupl_dbind; [|done].
      intros n a2 HR.
      apply Rcoupl_dret. eauto. }
    iIntros ([? ?] a2) "[%n (-> & -> & %)] !> !> !>".
    iMod (spec_auth_update a2 with "HaA Ha") as "[HaA Ha]".
    iMod "Hclose" as "_".
    iModIntro.
    iFrame.
    iApply rwp_value.
    iApply "HΦ".
    eauto.
  Qed.

  Lemma rwp_couple_tape N R ns α e m a E Φ :
    TCEq (to_val e) None →
    (∀ σ, σ.(tapes) !! α = Some ((N; ns) : tape) →
          Rcoupl
            (state_step σ α)
            (step m)
            (λ σ' m', ∃ n,
                R n m' ∧
                σ' = (state_upd_tapes (<[α := (N; ns ++ [n])]>) σ))) →
    α ↪ (N; ns) ∗
    specF m ∗
    ▷ (∀ n m', ⌜R n m'⌝ -∗ specF m' -∗ α ↪ (N; ns ++ [n]) -∗ WP e @ a; E {{ Φ }})
    ⊢ WP e @ a; E {{ Φ }}.
  Proof.
    iIntros (He Hcpl) "(Hα & HmF & Hcnt)".
    iApply rwp_lift_step_fupd_coupl; [rewrite /= He //|].
    iIntros (σ1 m1') "[[Hh Ht] HmA]".
    iDestruct (spec_auth_agree with "HmA HmF") as %->.
    iDestruct (ghost_map_lookup with "Ht Hα") as %?.
    iApply fupd_mask_intro; [set_solver|].
    iIntros "Hclose".
    iApply (rwp_coupl_state_step _ _ _ _ α).
    { rewrite /= /get_active. apply elem_of_elements, elem_of_dom; auto. }
    iExists _. iSplit; [eauto|].
    iIntros (σ2 m2 (n & ? & ->)).
    iMod (spec_auth_update m2 with "HmA HmF") as "[HmA HmF]".
    iMod (ghost_map_update ((N; ns ++ [n]) : tape) with "Ht Hα") as "[Ht Hα]".
    do 2 iModIntro.
    iMod "Hclose" as "_".
    iSpecialize ("Hcnt" with "[//] HmF Hα").
    rewrite !rwp_unfold /rwp_pre [language.to_val _]/= He.
    iApply "Hcnt". iFrame.
  Qed.

  Lemma rwp_couple_two_tapes N1 N2 R ns1 ns2 α1 α2 e m1 a E Φ :
    TCEq (to_val e) None →
    (∀ σ, α1 ≠ α2 →
          σ.(tapes) !! α1 = Some ((N1; ns1) : tape) →
          σ.(tapes) !! α2 = Some ((N2; ns2) : tape) →
          Rcoupl
            (state_step σ α1 ≫= (λ σ', state_step σ' α2))
            (step m1)
            (λ σ' m2, ∃ n1 n2,
                R (n1, n2) m2 ∧
                σ' = (state_upd_tapes (<[α1 := (N1; ns1 ++ [n1])]>)
                     (state_upd_tapes (<[α2 := (N2; ns2 ++ [n2])]>) σ)))) →
    α1 ↪ (N1; ns1) ∗
    α2 ↪ (N2; ns2) ∗
    specF m1 ∗
    ▷ (∀ n1 n2 m2, ⌜R (n1, n2) m2⌝ -∗ specF m2 -∗
                   α1 ↪ (N1; ns1 ++ [n1]) -∗ α2 ↪ (N2; ns2 ++ [n2]) -∗ WP e @ a; E {{ Φ }})
    ⊢ WP e @ a; E {{ Φ }}.
  Proof.
    iIntros (He Hcpl) "(Hα1 & Hα2 & Hm1F & Hcnt)".
    iApply rwp_lift_step_fupd_coupl; [rewrite /= He //|].
    iIntros (σ1 m1') "[[Hh1 Ht1] Hm1A]".
    iDestruct (spec_auth_agree with "Hm1A Hm1F") as %->.
    iDestruct (ghost_map_lookup with "Ht1 Hα1") as %?.
    iDestruct (ghost_map_lookup with "Ht1 Hα2") as %?.
    iDestruct (ghost_map_elem_ne with "Hα1 Hα2") as %?.
    iApply fupd_mask_intro; [set_solver|].
    iIntros "Hclose".
    iApply (rwp_coupl_double_state_step _ _ _ _ α1 α2).
    { rewrite /= /get_active. apply elem_of_elements, elem_of_dom; auto. }
    { rewrite /= /get_active. apply elem_of_elements, elem_of_dom; auto. }
    iExists _. iSplit; [eauto|].
    iIntros (σ2 m2 (n1 & n2 & ? & ->)).
    iMod (spec_auth_update m2 with "Hm1A Hm1F") as "[HmA HmF]".
    iMod (ghost_map_update ((N2; ns2 ++ [n2]) : tape) with "Ht1 Hα2") as "[Ht2 Hα2]".
    iMod (ghost_map_update ((N1; ns1 ++ [n1]) : tape) with "Ht2 Hα1") as "[Ht2 Hα1]".
    do 2 iModIntro.
    iMod "Hclose" as "_".
    iSpecialize ("Hcnt" with "[//] HmF Hα1 Hα2").
    rewrite !rwp_unfold /rwp_pre [language.to_val _]/= He.
    iApply "Hcnt". iFrame.
  Qed.

End coupl.

#[export] Hint Extern 0 (TCEq _ (Z.to_nat _ )) => rewrite Nat2Z.id : typeclass_instances.

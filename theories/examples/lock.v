From stdpp Require Import namespaces.
From iris Require Import invariants.
From iris.algebra Require Import excl.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From self Require Import spec_rules rel_rules rel_tactics notation types proofmode model spec_tactics.
Set Default Proof Using "Type".


Definition newlock : val := λ: <>, ref #false.
Axiom acquire : val. (*  := rec: "acquire" "x" := *)
  (* if: CAS "x" #false #true *)
  (* then #() *)
  (* else "acquire" "x". *)

Definition release : val := λ: "x", "x" <- #false.
Definition with_lock : val := λ: "e" "l" "x",
  acquire "l";;
  let: "v" := "e" "x" in
  release "l";; "v".

Class lockG Σ := LockG { lock_tokG :> inG Σ (exclR unitO) }.
Definition lockΣ : gFunctors := #[GFunctor (exclR unitO)].

Global Instance subG_lockΣ {Σ} : subG lockΣ Σ → lockG Σ.
Proof. solve_inG. Qed.

Section lockG_rules.
  Context `{!lockG Σ, !prelocGS Σ} (N: namespace).

  Definition lock_inv (γ : gname) (l : loc) (R : iProp Σ) : iProp Σ :=
    (∃ b : bool, l ↦ #b ∗ if b then True else own γ (Excl ()) ∗ R)%I.

  Definition is_lock (γ : gname) (lk : val) (R : iProp Σ) : iProp Σ :=
    (∃ l: loc, ⌜lk = #l⌝ ∧ inv N (lock_inv γ l R))%I.

  Definition locked (γ : gname) : iProp Σ := own γ (Excl ()).

  Lemma locked_exclusive (γ : gname) : locked γ -∗ locked γ -∗ False.
  Proof. iIntros "H1 H2". by iDestruct (own_valid_2 with "H1 H2") as %?. Qed.

  Global Instance lock_inv_ne γ l : NonExpansive (lock_inv γ l).
  Proof. solve_proper. Qed.
  Global Instance is_lock_ne γ l : NonExpansive (is_lock γ l).
  Proof. solve_proper. Qed.

  Global Instance is_lock_persistent γ l R : Persistent (is_lock γ l R).
  Proof. apply _. Qed.
  Global Instance locked_timeless γ : Timeless (locked γ).
  Proof. apply _. Qed.

  Lemma refines_newlock_l (R : iProp Σ) K t A :
    R -∗
    ▷(∀ (lk : loc) γ, is_lock γ #lk R
      -∗ (REL fill K (of_val #lk) << t: A)) -∗
    REL fill K (newlock #()) << t: A.
  Proof.
    iIntros "HR Hlog".
    rel_rec_l.
    rel_alloc_l l as "Hl".
    iMod (own_alloc (Excl ())) as (γ) "Hγ"; first done.
    iMod (inv_alloc N _ (lock_inv γ l R) with "[-Hlog]") as "#?".
    { iIntros "!>". iExists false. by iFrame. }
    iApply "Hlog". iExists l. eauto.
  Qed.

  Lemma refines_release_l (R : iProp Σ) (lk : val) γ K t A :
    is_lock γ lk R -∗
    locked γ -∗
    R -∗
    ▷(REL fill K (#() : expr) << t : A) -∗
    REL fill K (release lk) << t: A.
  Proof.
    iIntros "Hlock Hlocked HR Hlog".
    iDestruct "Hlock" as (l) "[% #?]"; simplify_eq.
    rel_rec_l. rel_store_l_atomic.
    iInv N as (b) "[Hl _]" "Hclose".
    iModIntro. iExists _. iFrame.
    iNext. iIntros "Hl".
    iMod ("Hclose" with "[-Hlog]").
    { iNext. iExists false. by iFrame. }
    iApply "Hlog".
  Qed.

  Lemma refines_acquire_l (R : iProp Σ) (lk : val) γ K t A :
    is_lock γ lk R -∗
    ▷(locked γ -∗ R -∗ REL fill K (of_val #()) << t: A) -∗
    REL fill K (acquire lk) << t: A.
  Admitted.

End lockG_rules.

Section lock_rules_r.
  Context `{prelocGS Σ}.
  Variable (E : coPset).

  Definition is_locked_r v (b : bool) :=
    (∃ lk : loc, ⌜v = #lk⌝ ∗ lk ↦ₛ #b)%I.

  Lemma refines_newlock_r K t A
    (Hcl : nclose specN ⊆ E) :
    (∀ v, is_locked_r v false -∗ REL t << fill K (of_val v) @ E : A) -∗
    REL t << fill K (newlock #()) @ E : A.
  Proof.
    iIntros "Hlog".
    rel_rec_r.
    rel_alloc_r l as "Hl".
    iApply ("Hlog" with "[Hl]").
    iExists _. by iFrame.
  Qed.

  Lemma refines_acquire_r K v t A
    (Hcl : nclose specN ⊆ E) :
    is_locked_r v false -∗
    (is_locked_r v true -∗ REL t << fill K (of_val #()) @ E : A) -∗
    REL t << fill K (acquire v) @ E : A.
  Admitted.

  Lemma refines_release_r K v t A st
    (Hcl : nclose specN ⊆ E) :
    is_locked_r v st -∗
    (is_locked_r v false -∗ REL t << fill K (of_val #()) @ E : A) -∗
    REL t << fill K (release v) @ E : A.
  Proof.
    iIntros "Hl Hlog".
    iDestruct "Hl" as (lk ->) "Hl".
    rel_rec_r.
    rel_store_r.
    iApply "Hlog". iExists _. by iFrame.
  Qed.

End lock_rules_r.

Opaque acquire release newlock.

From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import lib.token.
From coneris Require Import coneris.
From coneris.coneris.lib Require Export lock.
From iris.prelude Require Import options.

Local Definition newlock : val := λ: <>, ref #false.
Local Definition try_acquire : val := λ: "l", CAS "l" #false #true.
Local Definition acquire : val :=
  rec: "acquire" "l" := if: try_acquire "l" then #() else "acquire" "l".
Local Definition release : val := λ: "l", "l" <- #false.
(** The CMRA we need. *)
Class spin_lockG Σ := LockG { lock_tokG : tokenG Σ }.
Local Existing Instance lock_tokG.
Definition spin_lockΣ : gFunctors := #[tokenΣ].
Global Instance subG_spin_lockΣ {Σ} : subG spin_lockΣ Σ → spin_lockG Σ.
Proof. solve_inG. Qed.
Section proof.
  Context `{!conerisGS Σ, !spin_lockG Σ}.
  Let N := nroot .@ "spin_lock".
  Local Definition lock_inv (γ : gname) (l : loc) (R : iProp Σ) : iProp Σ :=
    ∃ b : bool, l ↦ #b ∗ if b then True else token γ ∗ R.
  Local Definition is_lock (γ : gname) (lk : val) (R : iProp Σ) : iProp Σ :=
    ∃ l: loc, ⌜lk = #l⌝ ∧ inv N (lock_inv γ l R).
  Local Definition locked (γ : gname) : iProp Σ := token γ.
  Local Lemma locked_exclusive (γ : gname) : locked γ -∗ locked γ -∗ False.
  Proof. iIntros "H1 H2". by iCombine "H1 H2" gives %?. Qed.
  (** The main proofs. *)
  Local Lemma is_lock_iff γ lk R1 R2 :
    is_lock γ lk R1 -∗ ▷ □ (R1 ∗-∗ R2) -∗ is_lock γ lk R2.
  Proof.
    iDestruct 1 as (l ->) "#Hinv"; iIntros "#HR".
    iExists l; iSplit; [done|]. iApply (inv_iff with "Hinv").
    iIntros "!> !>"; iSplit; iDestruct 1 as (b) "[Hl H]";
      iExists b; iFrame "Hl"; destruct b;
      first [done|iDestruct "H" as "[$ ?]"; by iApply "HR"].
  Qed.
  Local Lemma newlock_spec (R : iProp Σ):
    {{{ R }}} newlock #() {{{ lk γ, RET lk; is_lock γ lk R }}}.
  Proof.
    iIntros (Φ) "HR HΦ". rewrite /newlock /=.
    wp_lam. wp_alloc l as "Hl".
    iMod token_alloc as (γ) "Hγ".
    iMod (inv_alloc N _ (lock_inv γ l R) with "[-HΦ]") as "#?".
    { iIntros "!>". iExists false. by iFrame. }
    iModIntro. iApply "HΦ". iExists l. eauto.
  Qed.
  Local Lemma try_acquire_spec γ lk R :
    {{{ is_lock γ lk R }}} try_acquire lk
    {{{ b, RET #b; if b is true then locked γ ∗ R else True }}}.
  Proof.
    iIntros (Φ) "#Hl HΦ". iDestruct "Hl" as (l ->) "#Hinv".
    wp_rec. wp_bind (CmpXchg _ _ _). iInv N as ([]) "[Hl HR]".
    - wp_cmpxchg_fail. iModIntro. iSplitL "Hl". { iNext. iExists true; eauto. }
      wp_pures. iApply ("HΦ" $! false). done.
    - wp_cmpxchg_suc. iDestruct "HR" as "[Hγ HR]".
      iModIntro. iSplitL "Hl". { iNext; iExists true; eauto. }
      rewrite /locked. wp_pures. by iApply ("HΦ" $! true with "[$Hγ $HR]").
  Qed.
  Local Lemma acquire_spec γ lk R :
    {{{ is_lock γ lk R }}} acquire lk {{{ RET #(); locked γ ∗ R }}}.
  Proof.
    iIntros (Φ) "#Hl HΦ". iLöb as "IH". wp_rec.
    wp_apply (try_acquire_spec with "Hl"). iIntros ([]).
    - iIntros "[Hlked HR]". wp_if. iApply "HΦ"; auto with iFrame.
    - iIntros "_". wp_if. iApply ("IH" with "[HΦ]"). auto.
  Qed.
  Local Lemma release_spec γ lk R :
    {{{ is_lock γ lk R ∗ locked γ ∗ R }}} release lk {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(Hlock & Hlocked & HR) HΦ".
    iDestruct "Hlock" as (l ->) "#Hinv".
    rewrite /release /=. wp_lam. iInv N as (b) "[Hl _]".
    wp_store. iSplitR "HΦ"; last by iApply "HΦ".
    iModIntro. iNext. iExists false. by iFrame.
  Qed.
End proof.
(* NOT an instance because users should choose explicitly to use it
     (using [Explicit Instance]). *)
Definition spin_lock : lock :=
  {| lock.lockG := spin_lockG;
     lock.locked_exclusive _ _ _ := locked_exclusive;
     lock.is_lock_iff _ _ _ := is_lock_iff;
     lock.newlock_spec _ _ _ := newlock_spec;
     lock.acquire_spec _ _ _ := acquire_spec;
     lock.release_spec _ _ _ := release_spec |}.

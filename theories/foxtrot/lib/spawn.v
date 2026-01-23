From iris.prelude Require Import options.
From clutch.foxtrot Require Import foxtrot.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Export invariants.
From iris.proofmode Require Import proofmode.

Definition spawn : val :=
  λ: "f",
    let: "c" := ref NONE in
    Fork ("c" <- SOME ("f" #())) ;; "c".
Definition join : val :=
  rec: "join" "c" :=
    match: !"c" with
      SOME "x" => "x"
    | NONE => "join" "c"
    end.

(** The CMRA & functor we need. *)
(* Not bundling heapGS, as it may be shared with other users. *)
Class spawnG Σ := SpawnG { spawn_tokG : inG Σ (exclR unitO) }.
Local Existing Instance spawn_tokG.

Definition spawnΣ : gFunctors := #[GFunctor (exclR unitO)].

Global Instance subG_spawnΣ {Σ} : subG spawnΣ Σ → spawnG Σ.
Proof. solve_inG. Qed.

(** Now we come to the Iris part of the proof. *)
Section proof.
Context `{!foxtrotGS Σ, !spawnG Σ} (N : namespace).

Definition spawn_inv (γ : gname) (l : loc) (Ψ : val → iProp Σ) : iProp Σ :=
  ∃ lv, l ↦ lv ∗ (⌜lv = NONEV⌝ ∨
                  ∃ w, ⌜lv = SOMEV w⌝ ∗ (Ψ w ∨ own γ (Excl ()))).

Definition join_handle (l : loc) (Ψ : val → iProp Σ) : iProp Σ :=
  ∃ γ, own γ (Excl ()) ∗ inv N (spawn_inv γ l Ψ).

Global Instance spawn_inv_ne n γ l :
  Proper (pointwise_relation val (dist n) ==> dist n) (spawn_inv γ l).
Proof. solve_proper. Qed.
Global Instance join_handle_ne n l :
  Proper (pointwise_relation val (dist n) ==> dist n) (join_handle l).
Proof. solve_proper. Qed.

(** The main proofs. *)
Lemma spawn_spec (Ψ : val → iProp Σ) (f : val) :
  {{{ WP f #() {{ Ψ }} }}} spawn f {{{ l, RET #l; join_handle l Ψ }}}.
Proof.
  iIntros (Φ) "Hf HΦ". rewrite /spawn /=. wp_lam.
  wp_alloc l as "Hl".
  iMod (own_alloc (Excl ())) as (γ) "Hγ"; first done.
  iMod (inv_alloc N _ (spawn_inv γ l Ψ) with "[Hl]") as "#?".
  { iNext. iExists NONEV. iFrame; eauto. }
  wp_smart_apply (wp_fork with "[Hf]").
  - iNext. wp_bind (f _). iApply (wp_wand with "Hf"); iIntros (v) "Hv".
    wp_inj. iInv N as (v') "[Hl _]".
    wp_store. iSplitL; last done. iIntros "!> !>". iExists (SOMEV v). iFrame. eauto.
  - wp_pures. iApply "HΦ". rewrite /join_handle. eauto.
Qed.

Lemma join_spec (Ψ : val → iProp Σ) l :
  {{{ join_handle l Ψ }}} join #l {{{ v, RET v; Ψ v }}}.
Proof.
  iIntros (Φ) "H HΦ". iDestruct "H" as (γ) "[Hγ #?]".
  iLöb as "IH". wp_rec. wp_bind (! _)%E. iInv N as (v) "[Hl Hinv]".
  wp_load. iDestruct "Hinv" as "[%|Hinv]"; subst.
  - iModIntro. iSplitL "Hl"; [iNext; iExists _; iFrame; eauto|].
    wp_smart_apply ("IH" with "Hγ [HΦ]"). auto.
  - iDestruct "Hinv" as (v' ->) "[HΨ|Hγ']".
    + iModIntro. iSplitL "Hl Hγ"; [iNext; iExists _; iFrame; eauto|].
      wp_pures. by iApply "HΦ".
    + iCombine "Hγ Hγ'" gives %[].
Qed.
End proof.

Global Typeclasses Opaque join_handle.

(** This file extends the Clutch program logic with some derived laws (not
using the lifting lemmas) about arrays

For utility functions on arrays (e.g., freeing/copying an array), see
[lib.array].  *)

From stdpp Require Import fin_maps.
From iris.bi Require Import lib.fractional.
From iris.proofmode Require Import proofmode.
From clutch.prob_lang Require Import tactics lang notation.
From clutch.tpref_logic Require Import weakestpre ectx_lifting primitive_laws.
From iris.prelude Require Import options.

(** The [array] connective is a version of [pointsto] that works
with lists of values. *)


Definition array `{!tprG δ Σ} (l : loc) (dq : dfrac) (vs : list val) : iProp Σ :=
  [∗ list] i ↦ v ∈ vs, (l +ₗ i) ↦{dq} v.

(*
Notation "l ↦∗{ dq } vs" := (array l dq vs)
  (at level 20, dq custom dfrac at level 1, format "l  ↦∗{ dq } vs") : bi_scope.
*)

Notation "l ↦∗{ dq } vs" := (array l dq vs)
  (at level 20, format "l  ↦∗{ dq }  vs") : bi_scope.

Notation "l ↦∗ v" := (l ↦∗{ DfracOwn 1 } v)%I
                      (at level 20, format "l  ↦∗  v") : bi_scope.

(** We have [FromSep] and [IntoSep] instances to split the fraction (via the
[AsFractional] instance below), but not for splitting the list, as that would
lead to overlapping instances. *)

Section lifting.

  Context `{!tprG δ Σ}.
  Implicit Types Φ Ψ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types v : val.
  Implicit Types l : loc.
  Implicit Types vs : list val.
  Implicit Types sz off : nat.

  (*
Global Instance array_timeless l q vs : Timeless (array l q vs) := _.

Global Instance array_fractional l vs : Fractional (λ q, l ↦∗{#q} vs)%I := _.
Global Instance array_as_fractional l q vs :
  AsFractional (l ↦∗{#q} vs) (λ q, l ↦∗{#q} vs)%I q.
Proof. split; done || apply _. Qed.
*)

Lemma array_nil l dq : l ↦∗{dq} [] ⊣⊢ emp.
Proof. by rewrite /array. Qed.

Lemma array_singleton l dq v : l ↦∗{dq} [v] ⊣⊢ l ↦{dq} v.
Proof. by rewrite /array /= right_id loc_add_0. Qed.

Lemma array_app l dq vs ws :
  l ↦∗{dq} (vs ++ ws) ⊣⊢ l ↦∗{dq} vs ∗ (l +ₗ length vs) ↦∗{dq} ws.
Proof.
  rewrite /array big_sepL_app.
  setoid_rewrite Nat2Z.inj_add.
  by setoid_rewrite loc_add_assoc.
Qed.

Lemma array_cons l dq v vs : l ↦∗{dq} (v :: vs) ⊣⊢ l ↦{dq} v ∗ (l +ₗ 1) ↦∗{dq} vs.
Proof.
  rewrite /array big_sepL_cons loc_add_0.
  setoid_rewrite loc_add_assoc.
  setoid_rewrite Nat2Z.inj_succ.
  by setoid_rewrite Z.add_1_l.
Qed.

Global Instance array_cons_frame l dq v vs R Q :
  Frame false R (l ↦{dq} v ∗ (l +ₗ 1) ↦∗{dq} vs) Q →
  Frame false R (l ↦∗{dq} (v :: vs)) Q | 2.
Proof. by rewrite /Frame array_cons. Qed.

Lemma update_array l dq vs off v :
  vs !! off = Some v →
  ⊢ l ↦∗{dq} vs -∗ ((l +ₗ off) ↦{dq} v ∗ ∀ v', (l +ₗ off) ↦{dq} v' -∗ l ↦∗{dq} <[off:=v']>vs).
Proof.
  iIntros (Hlookup) "Hl".
  rewrite -[X in (l ↦∗{_} X)%I](take_drop_middle _ off v); last done.
  iDestruct (array_app with "Hl") as "[Hl1 Hl]".
  iDestruct (array_cons with "Hl") as "[Hl2 Hl3]".
  assert (off < length vs)%nat as H.
  { apply lookup_lt_is_Some. by eexists. }
  rewrite take_length min_l; [ | lia].
  iFrame "Hl2".
  iIntros (w) "Hl2".
  clear Hlookup. assert (<[off:=w]> vs !! off = Some w) as Hlookup.
  { apply list_lookup_insert. lia. }
  rewrite -[in (l ↦∗{_} <[off:=w]> vs)%I](take_drop_middle (<[off:=w]> vs) off w Hlookup).
  iApply array_app. rewrite take_insert; last by lia. iFrame.
  iApply array_cons. rewrite take_length min_l; last by lia. iFrame.
  rewrite drop_insert_gt; last by lia. done.
Qed.

(** * Rules for allocation *)
Lemma pointsto_seq_array l dq v n :
  ([∗ list] i ∈ seq 0 n, (l +ₗ (i : nat)) ↦{dq} v) -∗
  l ↦∗{dq} replicate n v.
Proof.
  rewrite /array. iInduction n as [|n'] "IH" forall (l); simpl.
  { done. }
  iIntros "[$ Hl]". rewrite -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-loc_add_assoc. iApply "IH". done.
Qed.

Lemma rswp_allocN k E v a n:
  (0 < n)%Z →
  ⟨⟨⟨ True ⟩⟩⟩ AllocN (Val $ LitV $ LitInt $ n) (Val v) at k @ a; E
  ⟨⟨⟨ l, RET LitV (LitLoc l); l ↦∗ replicate (Z.to_nat n) v ⟩⟩⟩.
  Proof.
    iIntros (? Φ) "_ HΦ".
    iApply rswp_allocN_seq; auto; try lia.
    iModIntro.
    iIntros (l) "Hlm".
    iApply "HΦ".
    by iApply pointsto_seq_array.
  Qed.


  Lemma rswp_allocN_vec k E v a n :
    (0 < n)%Z →
    ⟨⟨⟨ True ⟩⟩⟩
      AllocN #n v at k @ a; E
                          ⟨⟨⟨ l, RET #l; l ↦∗ vreplicate (Z.to_nat n) v ⟩⟩⟩.
  Proof.
    iIntros (? Φ) "_ HΦ".
    iApply (rswp_allocN with "[//] [HΦ]"); try lia.
    iModIntro.
    iIntros (l) "Hl".
    iApply "HΦ". by rewrite vec_to_list_replicate.
  Qed.


(** * Rules for accessing array elements *)


Lemma rswp_load_offset k E a l dq off vs v :
  vs !! off = Some v →
  ⟨⟨⟨ ▷ l ↦∗{dq} vs ⟩⟩⟩ ! #(l +ₗ off) at k @ a; E  ⟨⟨⟨ RET v; l ↦∗{dq} vs ⟩⟩⟩.
Proof.
  iIntros (Hlookup Φ) ">Hl HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (rswp_load with "Hl1").
  iModIntro.
  iIntros "Hl1".
  iApply "HΦ".
  iDestruct ("Hl2" $! v) as "Hl2". rewrite list_insert_id; last done.
  iApply "Hl2".
  iApply "Hl1".
Qed.

Lemma rswp_load_offset_vec k E a l dq sz (off : fin sz) (vs : vec val sz) :
  ⟨⟨⟨  ▷ l ↦∗{dq} vs ⟩⟩⟩ ! #(l +ₗ off) at k @ a; E ⟨⟨⟨ RET vs !!! off; l ↦∗{dq} vs ⟩⟩⟩.
  Proof. apply rswp_load_offset. by apply vlookup_lookup. Qed.


Lemma rswp_store_offset k E a l off vs v :
  is_Some (vs !! off) →
  ⟨⟨⟨ ▷ l ↦∗ vs ⟩⟩⟩ #(l +ₗ off) <- v at k @ a; E ⟨⟨⟨ RET #(); l ↦∗ <[off:=v]> vs ⟩⟩⟩.
Proof.
  iIntros ([w Hlookup] Φ) ">Hl HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (rswp_store with "Hl1").
  iModIntro.
  iIntros "Hl1".
  iApply "HΦ". iApply "Hl2". iApply "Hl1".
Qed.


Lemma rswp_store_offset_vec k E a l sz (off : fin sz) (vs : vec val sz) v :
  ⟨⟨⟨ ▷ l ↦∗ vs ⟩⟩⟩ #(l +ₗ off) <- v at k @ a; E ⟨⟨⟨ RET #(); l ↦∗ vinsert off v vs ⟩⟩⟩.
Proof.
  setoid_rewrite vec_to_list_insert. apply rswp_store_offset.
  eexists. by apply vlookup_lookup.
Qed.


(** RWP *)
(** * Rules for allocation *)

Lemma rwp_allocN E v a n:
  (0 < n)%Z →
  ⟨⟨⟨ True ⟩⟩⟩ AllocN (Val $ LitV $ LitInt $ n) (Val v) @ a; E
  ⟨⟨⟨ l, RET LitV (LitLoc l); l ↦∗ replicate (Z.to_nat n) v ⟩⟩⟩.
  Proof.
    intros Hn.
    iIntros (Φ) "H HΦ".
    iApply rwp_no_step.
    by iApply (rswp_allocN with "H HΦ").
  Qed.


  Lemma rwp_allocN_vec E v a n :
    (0 < n)%Z →
    ⟨⟨⟨ True ⟩⟩⟩
      AllocN #n v @ a; E
                         ⟨⟨⟨ l, RET #l; l ↦∗ vreplicate (Z.to_nat n) v ⟩⟩⟩.

  Proof.
    intros Hn.
    iIntros (Φ) "H HΦ".
    iApply rwp_no_step.
    by iApply (rswp_allocN_vec with "H HΦ").
  Qed.


(** * Rules for accessing array elements *)


Lemma rwp_load_offset E a l dq off vs v :
  vs !! off = Some v →
  ⟨⟨⟨ ▷ l ↦∗{dq} vs ⟩⟩⟩ ! #(l +ₗ off) @ a; E  ⟨⟨⟨ RET v; l ↦∗{dq} vs ⟩⟩⟩.
Proof.
    intros Hv.
    iIntros (Φ) "H HΦ".
    iApply rwp_no_step.
    by iApply (rswp_load_offset with "H HΦ").
Qed.


Lemma rwp_load_offset_vec E a l dq sz (off : fin sz) (vs : vec val sz) :
  ⟨⟨⟨  ▷ l ↦∗{dq} vs ⟩⟩⟩ ! #(l +ₗ off) @ a; E ⟨⟨⟨ RET vs !!! off; l ↦∗{dq} vs ⟩⟩⟩.
  Proof. apply rwp_load_offset. by apply vlookup_lookup. Qed.


Lemma rwp_store_offset E a l off vs v :
  is_Some (vs !! off) →
  ⟨⟨⟨ ▷ l ↦∗ vs ⟩⟩⟩ #(l +ₗ off) <- v @ a; E ⟨⟨⟨ RET #(); l ↦∗ <[off:=v]> vs ⟩⟩⟩.
Proof.
    intros Hv.
    iIntros (Φ) "H HΦ".
    iApply rwp_no_step.
    by iApply (rswp_store_offset with "H HΦ").
Qed.


Lemma rwp_store_offset_vec E a l sz (off : fin sz) (vs : vec val sz) v :
  ⟨⟨⟨ ▷ l ↦∗ vs ⟩⟩⟩ #(l +ₗ off) <- v @ a; E ⟨⟨⟨ RET #(); l ↦∗ vinsert off v vs ⟩⟩⟩.
Proof.
  setoid_rewrite vec_to_list_insert. apply rwp_store_offset.
  eexists. by apply vlookup_lookup.
Qed.

End lifting.

Global Typeclasses Opaque array.

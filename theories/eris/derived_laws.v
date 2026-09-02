(** This file extends the Clutch program logic with some derived laws (not
using the lifting lemmas) about arrays

For utility functions on arrays (e.g., freeing/copying an array), see
[lib.array].  *)

From stdpp Require Import fin_maps.
From iris.bi Require Import lib.fractional.
From iris.proofmode Require Import proofmode.
From clutch.prob_lang Require Import tactics lang notation.
From clutch.eris Require Export primitive_laws array_laws.
From iris.prelude Require Import options.

Section lifting.

  Context `{!erisGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ Ψ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types v : val.
  Implicit Types l : loc.
  Implicit Types vs : list val.
  Implicit Types sz off : nat.


Lemma wp_allocN E v n s :
  (0 < n)%Z →
  {{{ True }}} AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; E
  {{{ l, RET LitV (LitLoc l);
          l ↦∗ replicate (Z.to_nat n) v }}}.
  Proof.
    iIntros (? Φ) "_ HΦ".
    iApply wp_allocN_seq; auto; try lia.
    iModIntro.
    iIntros (l) "Hlm".
    iApply "HΦ".
    by iApply pointsto_seq_array.
  Qed.


  Lemma wp_allocN_vec E v n s :
    (0 < n)%Z →
    {{{ True }}}
      AllocN #n v @ s; E
                          {{{ l, RET #l; l ↦∗ vreplicate (Z.to_nat n) v  }}}.
  Proof.
    iIntros (? Φ) "_ HΦ".
    iApply (wp_allocN with "[//] [HΦ]"); try lia.
    iModIntro.
    iIntros (l) "Hl".
    iApply "HΦ". by rewrite vec_to_list_replicate.
  Qed.


(** * Rules for accessing array elements *)


Lemma wp_load_offset E l dq off vs v s :
  vs !! off = Some v →
  {{{ ▷ l ↦∗{dq} vs }}} ! #(l +ₗ off) @ s; E {{{ RET v; l ↦∗{dq} vs }}}.
Proof.
  iIntros (Hlookup Φ) ">Hl HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (wp_load with "Hl1").
  iModIntro.
  iIntros "Hl1".
  iApply "HΦ".
  iDestruct ("Hl2" $! v) as "Hl2". rewrite list_insert_id; last done.
  iApply "Hl2".
  iApply "Hl1".
Qed.

Lemma wp_load_offset_vec E l dq sz (off : fin sz) (vs : vec val sz) s :
  {{{ ▷ l ↦∗{dq} vs }}} ! #(l +ₗ off) @ s; E {{{ RET vs !!! off; l ↦∗{dq} vs }}}.
  Proof. apply wp_load_offset. by apply vlookup_lookup. Qed.


Lemma wp_store_offset E l off vs v s :
  is_Some (vs !! off) →
  {{{ ▷ l ↦∗ vs }}} #(l +ₗ off) <- v @ s; E {{{ RET #(); l ↦∗ <[off:=v]> vs }}}.
Proof.
  iIntros ([w Hlookup] Φ) ">Hl HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (wp_store with "Hl1").
  iModIntro.
  iIntros "Hl1".
  iApply "HΦ". iApply "Hl2". iApply "Hl1".
Qed.


Lemma wp_store_offset_vec E l sz (off : fin sz) (vs : vec val sz) v s :
  {{{ ▷ l ↦∗ vs }}} #(l +ₗ off) <- v @ s; E {{{ RET #(); l ↦∗ vinsert off v vs }}}.
Proof.
  setoid_rewrite vec_to_list_insert. apply wp_store_offset.
  eexists. by apply vlookup_lookup.
Qed.



End lifting.

Global Typeclasses Opaque array.

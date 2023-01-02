From stdpp Require Import namespaces.
From iris.base_logic Require Import invariants na_invariants.
From self.prob_lang Require Import notation proofmode primitive_laws spec_rules spec_tactics.
From self.logrel Require Import model rel_rules rel_tactics.
From iris.algebra Require Import auth gmap excl frac agree.
From self.prelude Require Import base.
From self.examples Require Import sample_int.

Section lazy_int.
  
  Context (PRED_CHUNK_BITS: nat).
  Definition CHUNK_BITS := S (PRED_CHUNK_BITS).
  Definition MAX_CHUNK := Z.ones CHUNK_BITS.
  
  Context (PRED_NUM_CHUNKS: nat).
  Definition NUM_CHUNKS := S (PRED_NUM_CHUNKS).
  
  Definition get_chunk : val :=
    λ: "α" "chnk",
      match: !"chnk" with
        | NONE => 
            let: "z" := sample_int PRED_CHUNK_BITS "α" in
            let: "next" := ref NONE in
            let: "val" := ("z", "next") in
            "chnk" <- SOME "val";;
            "val"
      | SOME "val" => "val"
      end.

  Context `{!prelogrelGS Σ}.
  
  Fixpoint chunk_list l (zs : list Z) : iProp Σ :=
    match zs with
    | [] => l ↦ NONEV
    | z :: zs =>
        ∃ l' : loc, l ↦ SOMEV (#z, #l') ∗ chunk_list l' zs
  end.

  Definition chunk_and_tape_list α l zs : iProp Σ :=
    ∃ zs1 zs2, ⌜ zs = zs1 ++ zs2 ⌝ ∗ chunk_list l zs1 ∗ int_tape PRED_CHUNK_BITS α zs2.

  Lemma chunk_and_tape_list_cons_chunk (l l' : loc) (z: Z) zs α :
    l ↦ SOMEV (#z, #l') -∗
    chunk_and_tape_list α l' zs -∗
    chunk_and_tape_list α l (z :: zs).
  Proof.
    iIntros "Hl Htape". iDestruct "Htape" as (zs1 zs2 Heq) "(Hchunks&Hlist)".
    iExists (z :: zs1), zs2.
    iSplit.
    { rewrite Heq /=//. }
    iSplitL "Hl Hchunks".
    { rewrite /=. iExists l'. iFrame. }
    iFrame.
  Qed.

  Lemma wp_get_chunk α l (z: Z) (zs: list Z) E :
    {{{ chunk_and_tape_list α l (z :: zs) }}}
      get_chunk #lbl:α #l @ E
    {{{ l', RET (#z, #l'); chunk_and_tape_list α l' zs ∗
                   (chunk_and_tape_list α l' zs -∗ chunk_and_tape_list α l (z :: zs)) }}}.
  Proof.
    iIntros (Φ) "Htape HΦ".
    rewrite /get_chunk.
    iDestruct "Htape" as (zs1 zs2 Heq) "(Hchunks&Htape)".
    destruct zs1 as [| z' zs1'].
    - (* Everything on the tape; sample z and update head *)
      wp_pures. iEval (rewrite /=) in "Hchunks".
      wp_load. wp_pures.
      rewrite /= in Heq. rewrite -?Heq.
      wp_apply (wp_sample_int with "Htape").
      iIntros "Htape". wp_pures.
      wp_alloc l' as "Hl'". wp_pures.
      wp_store. iApply "HΦ". iModIntro. iSplitL "Htape Hl'".
      { iExists nil, zs. rewrite /=. iSplit; first done. iFrame. }
      { iIntros "Htail". iApply (chunk_and_tape_list_cons_chunk with "[$] [$]"). }
    - (* Already sampled, just return what we read *)
      wp_pures. iEval (rewrite /=) in "Hchunks". iDestruct "Hchunks" as (l') "(Hl&Hrec)".
      wp_load. wp_pures. inversion Heq; subst. iApply "HΦ".
      iModIntro. iSplitL "Hrec Htape".
      { iExists _, _. iFrame. eauto. }
      { iIntros "Htail". iApply (chunk_and_tape_list_cons_chunk with "[$] [$]"). }
  Qed.

End lazy_int.

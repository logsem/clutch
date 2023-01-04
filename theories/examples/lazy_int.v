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

  Definition cmpZ : val :=
    λ: "z1" "z2",
      if: "z1" < "z2" then #(-1)
      else
        if: "z2" < "z1" then #1
        else #0.

  Definition cmp_list : val :=
    rec: "cmp_list" "n" "α1" "cl1" "α2" "cl2" :=
      if: "n" = #0 then
        #0
      else
        let: "c1n" := get_chunk "α1" "cl1" in
        let: "c2n" := get_chunk "α2" "cl2" in
        let: "res" := cmpZ (Fst "c1n") (Fst "c2n") in
        if: "res" = #0 then
          "cmp_list" ("n" - #1) "α1" (Snd "c1n") "α2" (Snd "c2n")
        else
          "res".

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

  Definition comparison2z c : Z :=
    match c with
    | Eq => 0
    | Lt => -1
    | Gt => 1
    end.


  Lemma wp_cmpZ (z1 z2 : Z) E :
    {{{ True }}}
      cmpZ #z1 #z2 @ E
    {{{ RET #(comparison2z (Z.compare z1 z2)); True%I }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite /cmpZ.
    destruct (Z.compare_spec z1 z2).
    - wp_pures; case_bool_decide; try lia.
      wp_pures; case_bool_decide; try lia.
      wp_pures. iApply "HΦ"; eauto.
    - wp_pures; case_bool_decide; try lia.
      wp_pures. iApply "HΦ"; eauto.
    - wp_pures; case_bool_decide; try lia.
      wp_pures; case_bool_decide; try lia.
      wp_pures. iApply "HΦ"; eauto.
  Qed.

  Lemma wp_cmp_list n α1 α2 l1 l2 zs1 zs2 E :
    n = length zs1 →
    n = length zs2 →
    {{{ chunk_and_tape_list α1 l1 zs1 ∗ chunk_and_tape_list α2 l2 zs2 }}}
      cmp_list #n #lbl:α1 #l1 #lbl:α2 #l2 @ E
    {{{ (z : Z), RET #z;
        ⌜ z = comparison2z (digit_list_cmp zs1 zs2) ⌝ ∗
        chunk_and_tape_list α1 l1 zs1 ∗ chunk_and_tape_list α2 l2 zs2 }}}.
  Proof.
    rewrite /cmp_list.
    iIntros (Hlen1 Hlen2 Φ) "(Hzs1&Hzs2) HΦ".
    iInduction n as [| n] "IH" forall (zs1 zs2 Hlen1 Hlen2 l1 l2).
    - destruct zs1; last by (simpl in Hlen1; inversion Hlen1).
      destruct zs2; last by (simpl in Hlen2; inversion Hlen2).
      wp_pures. iModIntro. iApply "HΦ". iFrame. simpl; eauto.
    - destruct zs1 as [| z1 zs1]; first by (simpl in Hlen1; inversion Hlen1).
      destruct zs2 as [| z2 zs2]; first by (simpl in Hlen2; inversion Hlen2).
      wp_pures.
      wp_apply (wp_get_chunk with "Hzs1").
      iIntros (l1') "(Hzs1'&Hclo1)".
      wp_pures.
      wp_apply (wp_get_chunk with "Hzs2").
      iIntros (l2') "(Hzs2'&Hclo2)".
      wp_pures. wp_apply (wp_cmpZ with "[//]").
      iIntros "_". wp_pures.
      case_bool_decide as Hcase.
      { assert (z1 ?= z2 = Eq)%Z as Hzcmp.
        { destruct (z1 ?= z2)%Z; try simpl in Hcase; try inversion Hcase. auto. }
        wp_pure. wp_pure. wp_pure. wp_pure.
        replace (Z.of_nat (S n) - 1)%Z with (Z.of_nat n); last by lia.
        wp_apply ("IH" $! zs1 zs2 with "[] [] Hzs1' Hzs2'").
        { eauto. }
        { eauto. }
        iIntros (res) "(%Heq&Hzs1&Hzs2)".
        iDestruct ("Hclo1" with "Hzs1") as "Hzs1".
        iDestruct ("Hclo2" with "Hzs2") as "Hzs2".
        iApply "HΦ". iFrame.
        iPureIntro. simpl. rewrite Hzcmp. eauto. }
      { wp_pures.
        iDestruct ("Hclo1" with "Hzs1'") as "Hzs1".
        iDestruct ("Hclo2" with "Hzs2'") as "Hzs2".
        iModIntro. iApply "HΦ"; iFrame.
        iPureIntro. simpl. destruct (z1 ?= z2)%Z; try eauto.
        simpl in Hcase; congruence.
      }
  Qed.

End lazy_int.

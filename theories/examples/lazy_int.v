From clutch Require Export clutch lib.flip.
From clutch.examples Require Export sample_int.

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

  Definition sample_lazy_int : val :=
    λ: "_",
      let: "hd" := ref NONEV in
      let: "α" := allocB in
      ("α", "hd").

  Definition sample_eager_int : val :=
    λ: "_",
      let: "α" := allocB in
      sample_wide_int PRED_NUM_CHUNKS PRED_CHUNK_BITS ("α").

  Definition cmp_lazy_int : val :=
    λ: "p",
      let: "lz1" := Fst "p" in
      let: "lz2" := Snd "p" in
      (* We short-circuit if the two ints are physically equal to avoid forcing sampling *)
      if: (Snd "lz1") = (Snd "lz2") then
        #0
      else
        cmp_list #NUM_CHUNKS (Fst "lz1" )(Snd "lz1") (Fst "lz2" )(Snd "lz2").

  Definition cmp_eager_int : val :=
    λ: "p",
      let: "z1" := Fst "p" in
      let: "z2" := Snd "p" in
      cmpZ "z1" "z2".

  Context `{!clutchRGS Σ}.

  Fixpoint chunk_list l (zs : list Z) : iProp Σ :=
    match zs with
    | [] => l ↦ NONEV
    | z :: zs =>
        ∃ l' : loc, l ↦ SOMEV (#z, #l') ∗ chunk_list l' zs
  end.

  Fixpoint spec_chunk_list l (zs : list Z) : iProp Σ :=
    match zs with
    | [] => l ↦ₛ NONEV
    | z :: zs =>
        ∃ l' : loc, l ↦ₛ SOMEV (#z, #l') ∗ spec_chunk_list l' zs
  end.

  Definition chunk_and_tape_list α l zs : iProp Σ :=
    ∃ zs1 zs2, ⌜ zs = zs1 ++ zs2 ⌝ ∗ chunk_list l zs1 ∗ int_tape PRED_CHUNK_BITS α zs2.

  Definition spec_chunk_and_tape_list α l zs : iProp Σ :=
    ∃ zs1 zs2, ⌜ zs = zs1 ++ zs2 ⌝ ∗ spec_chunk_list l zs1 ∗ spec_int_tape PRED_CHUNK_BITS α zs2.

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

  Lemma spec_chunk_and_tape_list_cons_chunk (l l' : loc) (z: Z) zs α :
    l ↦ₛ SOMEV (#z, #l') -∗
    spec_chunk_and_tape_list α l' zs -∗
    spec_chunk_and_tape_list α l (z :: zs).
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

  Lemma spec_get_chunk α l (z: Z) (zs: list Z) K E :
    ↑specN ⊆ E →
    spec_chunk_and_tape_list α l (z :: zs) -∗
    refines_right K (get_chunk #lbl:α #l) ={E}=∗
    ∃ l' : loc, refines_right K (of_val (#z, #l')) ∗
          spec_chunk_and_tape_list α l' zs ∗
          (spec_chunk_and_tape_list α l' zs -∗ spec_chunk_and_tape_list α l (z :: zs)).
  Proof.
    iIntros (?) "Htape HK".
    rewrite /get_chunk.
    iDestruct "Htape" as (zs1 zs2 Heq) "(Hchunks&Htape)".
    destruct zs1 as [| z' zs1'].
    - (* Everything on the tape; sample z and update head *)
      tp_pures. iEval (rewrite /=) in "Hchunks".
      tp_load. tp_pures.
      rewrite /= in Heq. rewrite -?Heq.
      tp_bind (sample_int _ _)%E.
      rewrite refines_right_bind.
      iMod (spec_sample_int with "[$] [$]") as "(HK&Htape)"; first done.
      rewrite -refines_right_bind /=.
      tp_pures.
      tp_alloc as l' "Hl'". tp_pures.
      tp_store. tp_pures. iModIntro. iExists _. iFrame "HK". iSplitL "Htape Hl'".
      { iExists nil, zs. rewrite /=. iSplit; first done. iFrame. }
      { iIntros "Htail". iApply (spec_chunk_and_tape_list_cons_chunk with "[$] [$]"). }
    - (* Already sampled, just return what we read *)
      tp_pures. iEval (rewrite /=) in "Hchunks". iDestruct "Hchunks" as (l') "(Hl&Hrec)".
      tp_load. tp_pures. inversion Heq; subst. iExists _; iFrame "HK".
      iModIntro. iSplitL "Hrec Htape".
      { iExists _, _. iFrame. eauto. }
      { iIntros "Htail". iApply (spec_chunk_and_tape_list_cons_chunk with "[$] [$]"). }
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

  Lemma spec_cmpZ (z1 z2 : Z) E K :
    ↑specN ⊆ E →
    refines_right K (cmpZ #z1 #z2) ={E}=∗
    refines_right K (of_val #(comparison2z (Z.compare z1 z2))).
  Proof.
    iIntros (?) "HK".
    rewrite /cmpZ.
    destruct (Z.compare_spec z1 z2).
    - tp_pures; case_bool_decide; try lia.
      tp_pures; case_bool_decide; try lia.
      tp_pures. by iFrame.
    - tp_pures; case_bool_decide; try lia.
      tp_pures. by iFrame.
    - tp_pures; case_bool_decide; try lia.
      tp_pures; case_bool_decide; try lia.
      tp_pures. by iFrame.
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

  Lemma spec_cmp_list n α1 α2 (l1 l2 : loc) zs1 zs2 E K :
    ↑specN ⊆ E →
    n = length zs1 →
    n = length zs2 →
    refines_right K (cmp_list #n #lbl:α1 #l1 #lbl:α2 #l2) -∗
    spec_chunk_and_tape_list α1 l1 zs1 -∗
    spec_chunk_and_tape_list α2 l2 zs2 ={E}=∗
    ∃ z : Z, refines_right K (of_val #z) ∗
             ⌜ z = comparison2z (digit_list_cmp zs1 zs2) ⌝ ∗
             spec_chunk_and_tape_list α1 l1 zs1 ∗ spec_chunk_and_tape_list α2 l2 zs2.
  Proof.
    rewrite /cmp_list.
    iIntros (HE Hlen1 Hlen2) "HK Hzs1 Hzs2".
    iInduction n as [| n] "IH" forall (zs1 zs2 Hlen1 Hlen2 l1 l2).
    - destruct zs1; last by (simpl in Hlen1; inversion Hlen1).
      destruct zs2; last by (simpl in Hlen2; inversion Hlen2).
      tp_pures; first solve_vals_compare_safe.
      iModIntro. iExists _. iFrame. simpl; eauto.
    - destruct zs1 as [| z1 zs1]; first by (simpl in Hlen1; inversion Hlen1).
      destruct zs2 as [| z2 zs2]; first by (simpl in Hlen2; inversion Hlen2).
      tp_pures; first solve_vals_compare_safe.
      tp_bind (get_chunk _ _)%E.
      rewrite refines_right_bind.
      iMod (spec_get_chunk with "Hzs1 [$]") as (l1') "(HK&Hzs1'&Hclo1)"; first done.
      rewrite -refines_right_bind /=.
      tp_pures.
      tp_bind (get_chunk _ _)%E.
      rewrite refines_right_bind.
      iMod (spec_get_chunk with "Hzs2 [$]") as (l2') "(HK&Hzs2'&Hclo2)"; first done.
      rewrite -refines_right_bind /=.
      tp_pures.
      tp_bind (cmpZ _ _).
      rewrite refines_right_bind.
      iMod (spec_cmpZ with "[$]") as "HK"; first done.
      rewrite -refines_right_bind /=.
      tp_pures; first solve_vals_compare_safe.
      case_bool_decide as Hcase.
      { assert (z1 ?= z2 = Eq)%Z as Hzcmp.
        { destruct (z1 ?= z2)%Z; try simpl in Hcase; try inversion Hcase. auto. }
        tp_pure. tp_pure. tp_pure. tp_pure.
        replace (Z.of_nat (S n) - 1)%Z with (Z.of_nat n); last by lia.
        iMod ("IH" $! zs1 zs2 with "[] [] [$] Hzs1' Hzs2'") as (z) "(HK&%Heq&Hzs1&Hzs2)"; eauto.
        iDestruct ("Hclo1" with "Hzs1") as "Hzs1".
        iDestruct ("Hclo2" with "Hzs2") as "Hzs2".
        iExists _. iFrame.
        iPureIntro. simpl. rewrite Hzcmp. eauto. }
      { tp_pures.
        iDestruct ("Hclo1" with "Hzs1'") as "Hzs1".
        iDestruct ("Hclo2" with "Hzs2'") as "Hzs2".
        iModIntro. iExists _. iFrame.
        iPureIntro. simpl. destruct (z1 ?= z2)%Z; try eauto.
        simpl in Hcase; congruence.
      }
  Qed.

  Definition lazy_int (z: Z) (v: val) : iProp Σ :=
    ∃ (α l : loc) zs, ⌜ v = (#lbl:α, #l)%V ⌝ ∗
                      ⌜ z = digit_list_to_Z PRED_CHUNK_BITS zs ⌝ ∗
                      ⌜ length zs = NUM_CHUNKS ⌝ ∗
                      ⌜ wf_digit_list PRED_CHUNK_BITS zs ⌝ ∗
                      chunk_and_tape_list α l zs.

  Definition spec_lazy_int (z: Z) (v: val) : iProp Σ :=
    ∃ (α l : loc) zs, ⌜ v = (#lbl:α, #l)%V ⌝ ∗
                      ⌜ z = digit_list_to_Z PRED_CHUNK_BITS zs ⌝ ∗
                      ⌜ length zs = NUM_CHUNKS ⌝ ∗
                      ⌜ wf_digit_list PRED_CHUNK_BITS zs ⌝ ∗
                      spec_chunk_and_tape_list α l zs.

  Lemma wp_sample_lazy_eager_couple K E :
    ↑ specN ⊆ E →
    {{{ refines_right K (sample_eager_int #()) }}}
      sample_lazy_int #() @ E
    {{{ v, RET v; ∃ z, lazy_int z v ∗ refines_right K (of_val #z) }}}.
  Proof.
    iIntros (? Φ) "HK HΦ".
    rewrite /sample_lazy_int.
    wp_pures.
    wp_alloc l as "Hl".
    wp_pures.
    wp_apply (wp_alloc_tape with "[//]").
    iIntros (α) "Hα".

    rewrite /sample_eager_int.
    tp_pures.
    tp_alloctape as αₛ "Hαₛ".
    tp_pures.
    iApply (wp_couple_int_tapesN_eq PRED_CHUNK_BITS _ _ NUM_CHUNKS).
    { eauto. }
    { eauto. }
    iSplit.
    { iDestruct "HK" as "($&_)". }
    iSplitL "Hαₛ".
    { iApply spec_int_tape_intro. iFrame. }
    iSplitL "Hα".
    { iApply int_tape_intro. iFrame. }
    iDestruct 1 as (zs Hrange Hlegnth) "(Hspec_tape&Htape)".
    iMod (spec_sample_wide_int _ _ _ _ _ _ [] with "[Hspec_tape] [$]") as (z) "(HK&%Hz&_)"; auto.
    { eauto. }
    { rewrite app_nil_l app_nil_r. iFrame. }
    wp_pures. iApply "HΦ". iExists _. iFrame.
    iModIntro. iExists _, _, _.
    iSplit; first eauto.
    iSplit; first eauto.
    iSplit; first eauto.
    iSplit.
    { iPureIntro. rewrite /wf_digit_list. eapply Forall_impl; try eassumption.
      intros x => /=. rewrite /MAX_INT Z.ones_equiv/NUM_BITS.
      lia. }
    iExists [], zs.
    rewrite app_nil_l. iFrame.
    eauto.
  Qed.

  Lemma wp_sample_eager_lazy_couple K E :
    ↑ specN ⊆ E →
    {{{ refines_right K (sample_lazy_int #()) }}}
      sample_eager_int #() @ E
    {{{ (z : Z), RET #z; ∃ v, spec_lazy_int z v ∗ refines_right K (of_val v) }}}.
  Proof.
    iIntros (? Φ) "HK HΦ".
    rewrite /sample_lazy_int.
    rewrite /sample_eager_int.

    tp_pures.
    tp_alloc as l "Hl".
    tp_pures.
    tp_alloctape as αₛ "Hαₛ".

    wp_pures.
    wp_apply (wp_alloc_tape with "[//]"). iIntros (α) "Hα".
    wp_pures.
    iApply (wp_couple_int_tapesN_eq PRED_CHUNK_BITS _ _ NUM_CHUNKS).
    { eauto. }
    { eauto. }
    iSplit.
    { iDestruct "HK" as "($&_)". }
    iSplitL "Hαₛ".
    { iApply spec_int_tape_intro. iFrame. }
    iSplitL "Hα".
    { iApply int_tape_intro. iFrame. }
    iDestruct 1 as (zs Hrange Hlegnth) "(Hspec_tape&Htape)".
    tp_pures.
    wp_apply (wp_sample_wide_int _ _ _ _ _ [] with "[Htape]"); eauto.
    { rewrite app_nil_l app_nil_r. iFrame. }
    iIntros (z) "(%Hz&_)"; auto.
    iApply "HΦ". iExists _. iFrame.
    iExists _, _, _.
    iSplit; first eauto.
    iSplit; first eauto.
    iSplit; first eauto.
    iSplit.
    { iPureIntro. rewrite /wf_digit_list. eapply Forall_impl; try eassumption.
      intros x => /=. rewrite /MAX_INT Z.ones_equiv/NUM_BITS.
      lia. }
    iExists [], zs.
    rewrite app_nil_l. iFrame.
    eauto.
  Qed.

  Lemma chunk_list_hd_acc l zs :
    chunk_list l zs -∗
    (∃ v, l ↦ v ∗ (l ↦ v -∗ chunk_list l zs)).
  Proof.
    destruct zs.
    - simpl. iIntros. iExists _. iFrame. eauto.
    - simpl. iDestruct 1 as (?) "(H1&H2)". iExists _. iFrame.
      iIntros "H". iExists _. iFrame.
  Qed.

  Lemma spec_chunk_list_hd_acc l zs :
    spec_chunk_list l zs -∗
    (∃ v, l ↦ₛ v ∗ (l ↦ₛ v -∗ spec_chunk_list l zs)).
  Proof.
    destruct zs.
    - simpl. iIntros. iExists _. iFrame. eauto.
    - simpl. iDestruct 1 as (?) "(H1&H2)". iExists _. iFrame.
      iIntros "H". iExists _. iFrame.
  Qed.

  Lemma chunk_list_sep_no_alias l1 l2 zs1 zs2 :
    chunk_list l1 zs1 -∗
    chunk_list l2 zs2 -∗
    ⌜ l1 ≠ l2 ⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (chunk_list_hd_acc with "H1") as (?) "(H1&_)".
    iDestruct (chunk_list_hd_acc with "H2") as (?) "(H2&_)".
    destruct (decide (l1 = l2)); auto; subst.
    iDestruct (@ghost_map_elem_valid_2 with "H1 H2") as %[Hval _].
    iPureIntro. apply dfrac_valid_own_l in Hval. inversion Hval.
  Qed.

  Lemma chunk_and_tape_list_sep_no_alias α1 α2 l1 l2 zs1 zs2 :
    chunk_and_tape_list α1 l1 zs1 -∗
    chunk_and_tape_list α2 l2 zs2 -∗
    ⌜ l1 ≠ l2 ⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct "H1" as (???) "(H1&_)".
    iDestruct "H2" as (???) "(H2&_)".
    iApply (chunk_list_sep_no_alias with "H1 H2").
  Qed.

  Lemma spec_chunk_list_sep_no_alias l1 l2 zs1 zs2 :
    spec_chunk_list l1 zs1 -∗
    spec_chunk_list l2 zs2 -∗
    ⌜ l1 ≠ l2 ⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (spec_chunk_list_hd_acc with "H1") as (?) "(H1&_)".
    iDestruct (spec_chunk_list_hd_acc with "H2") as (?) "(H2&_)".
    destruct (decide (l1 = l2)); auto; subst.
    iDestruct (@ghost_map_elem_valid_2 with "H1 H2") as %[Hval _].
    iPureIntro. apply dfrac_valid_own_l in Hval. inversion Hval.
  Qed.

  Lemma spec_chunk_and_tape_list_sep_no_alias α1 α2 l1 l2 zs1 zs2 :
    spec_chunk_and_tape_list α1 l1 zs1 -∗
    spec_chunk_and_tape_list α2 l2 zs2 -∗
    ⌜ l1 ≠ l2 ⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct "H1" as (???) "(H1&_)".
    iDestruct "H2" as (???) "(H2&_)".
    iApply (spec_chunk_list_sep_no_alias with "H1 H2").
  Qed.

  Lemma wp_cmp_lazy_int z1 z2 v1 v2 E :
    {{{ ▷ lazy_int z1 v1 ∗ ▷ lazy_int z2 v2 }}}
      cmp_lazy_int (v1, v2)%V @ E
    {{{ zret, RET #zret ;
        ⌜ zret = (comparison2z (Z.compare z1 z2)) ⌝ ∗
        lazy_int z1 v1 ∗ lazy_int z2 v2 }}}.
  Proof.
    iIntros (Φ) "(Hv1&Hv2) HΦ".
    rewrite /cmp_lazy_int. wp_pures.
    iDestruct "Hv1" as (α1 l1 zs1 -> Hz1 Hlen1 Hwf1) "H1".
    iDestruct "Hv2" as (α2 l2 zs2 -> Hz2 Hlen2 Hwf2) "H2".
    wp_pures.
    case_bool_decide.
    { iDestruct (chunk_and_tape_list_sep_no_alias with "[$] [$]") as %Hneq; congruence. }
    wp_pures.
    wp_apply (wp_cmp_list with "[$H1 $H2]"); try done.
    iIntros (zret) "(%Hret&H1&H2)".
    iApply "HΦ".
    assert (zret = comparison2z (z1 ?= z2)%Z) as Hreteq.
    { rewrite Hret. f_equal.
      rewrite Hz1 Hz2.
      eapply digit_list_cmp_spec; eauto.
      lia. }
    iSplit; first eauto.
    iSplitL "H1".
    { iExists _, _, _. iFrame. eauto. }
    { iExists _, _, _. iFrame. eauto. }
  Qed.

  Lemma spec_cmp_lazy_int z1 z2 v1 v2 K E :
    ↑specN ⊆ E →
    refines_right K (cmp_lazy_int (v1, v2)%V) -∗
    spec_lazy_int z1 v1 -∗
    spec_lazy_int z2 v2 ={E}=∗
    ∃ zret: Z, refines_right K (of_val #zret) ∗
        ⌜ zret = (comparison2z (Z.compare z1 z2)) ⌝ ∗
        spec_lazy_int z1 v1 ∗ spec_lazy_int z2 v2.
  Proof.
    iIntros (?) "HK Hv1 Hv2".
    rewrite /cmp_lazy_int. tp_pures.
    iDestruct "Hv1" as (α1 l1 zs1 -> Hz1 Hlen1 Hwf1) "H1".
    iDestruct "Hv2" as (α2 l2 zs2 -> Hz2 Hlen2 Hwf2) "H2".
    tp_pures; first solve_vals_compare_safe.
    case_bool_decide.
    { iDestruct (spec_chunk_and_tape_list_sep_no_alias with "[$] [$]") as %Hneq; congruence. }
    tp_pures.
    iMod (spec_cmp_list with "HK H1 H2") as (zret) "(HK&%Hret&H1&H2)"; try done.
    assert (zret = comparison2z (z1 ?= z2)%Z) as Hreteq.
    { rewrite Hret. f_equal.
      rewrite Hz1 Hz2.
      eapply digit_list_cmp_spec; eauto.
      lia. }
    iModIntro; iExists _; iFrame.
    iSplit; first eauto.
    iSplitL "H1".
    { iExists _, _, _. iFrame. eauto. }
    { iExists _, _, _. iFrame. eauto. }
  Qed.

  Lemma wp_cmp_lazy_int_cmp_clutch z1 v1 E :
    {{{ ▷ lazy_int z1 v1  }}}
      cmp_lazy_int (v1, v1)%V @ E
    {{{ zret, RET #zret ;
        ⌜ zret = (comparison2z (Z.compare z1 z1)) ⌝ ∗
        lazy_int z1 v1 }}}.
  Proof.
    iIntros (Φ) "Hv1 HΦ".
    rewrite /cmp_lazy_int. wp_pures.
    iDestruct "Hv1" as (α1 l1 zs1 -> Hz1 Hlen1 Hwf1) "H1".
    wp_pures.
    case_bool_decide; last by congruence.
    wp_pures. iApply "HΦ". rewrite Z.compare_refl //. iModIntro; iSplit; first eauto.
    iExists _, _, _. eauto.
  Qed.

  Lemma spec_cmp_lazy_int_cmp_clutch z1 v1 E K :
    ↑specN ⊆ E →
    refines_right K (cmp_lazy_int (v1, v1)%V) -∗
    spec_lazy_int z1 v1 ={E}=∗
    ∃ zret: Z, refines_right K (of_val #zret) ∗
        ⌜ zret = (comparison2z (Z.compare z1 z1)) ⌝ ∗
        spec_lazy_int z1 v1.
  Proof.
    iIntros (?) "HK Hv1".
    rewrite /cmp_lazy_int. tp_pures.
    iDestruct "Hv1" as (α1 l1 zs1 -> Hz1 Hlen1 Hwf1) "H1".
    tp_pures; first solve_vals_compare_safe.
    case_bool_decide; last by congruence.
    tp_pures. rewrite Z.compare_refl //. iModIntro; iExists _; iFrame "HK". iSplit; first eauto.
    iExists _, _, _. eauto.
  Qed.

  Lemma wp_cmp_lazy_eager_refine z1 z2 v1 v2 K E :
    ↑ specN ⊆ E →
    {{{ ▷ lazy_int z1 v1 ∗ ▷ lazy_int z2 v2 ∗ refines_right K (cmp_eager_int (#z1, #z2)%V) }}}
      cmp_lazy_int (v1, v2)%V @ E
    {{{ zret, RET #zret ;
        ⌜ zret = (comparison2z (Z.compare z1 z2)) ⌝ ∗
        lazy_int z1 v1 ∗ lazy_int z2 v2 ∗ refines_right K (of_val #zret) }}}.
  Proof.
    iIntros (HE Φ) "(Hv1&Hv2&HK) HΦ".
    rewrite /cmp_eager_int.
    tp_pures.
    iMod (spec_cmpZ with "[$]") as "HK"; first done.
    wp_apply (wp_cmp_lazy_int with "[$Hv1 $Hv2]").
    iIntros (zret) "(%Hret&H1&H2)".
    iApply "HΦ". iFrame; eauto. rewrite Hret. eauto.
  Qed.

  Lemma wp_cmp_eager_lazy_refine z1 z2 v1 v2 K E :
    ↑ specN ⊆ E →
    {{{ ▷ spec_lazy_int z1 v1 ∗ ▷ spec_lazy_int z2 v2 ∗ refines_right K (cmp_lazy_int (v1, v2)%V) }}}
      cmp_eager_int (#z1, #z2)%V @ E
    {{{ zret, RET #zret ;
        ⌜ zret = (comparison2z (Z.compare z1 z2)) ⌝ ∗
        spec_lazy_int z1 v1 ∗ spec_lazy_int z2 v2 ∗ refines_right K (of_val #zret) }}}.
  Proof.
    iIntros (HE Φ) "(Hv1&Hv2&HK) HΦ".
    rewrite /cmp_eager_int.
    wp_pures.
    iMod (spec_cmp_lazy_int with "HK [$] [$]") as (zret) "(HK&%Heq&Hv1&Hv2)"; first done.
    wp_apply (wp_cmpZ with "[//]"). iIntros "_".
    iApply "HΦ". iFrame; eauto. rewrite Heq. eauto.
  Qed.

  Lemma wp_cmp_lazy_eager_refine_cmp_clutch z1 v1 K E :
    ↑ specN ⊆ E →
    {{{ ▷ lazy_int z1 v1 ∗ refines_right K (cmp_eager_int (#z1, #z1)%V) }}}
      cmp_lazy_int (v1, v1)%V @ E
    {{{ zret, RET #zret ;
        ⌜ zret = (comparison2z (Z.compare z1 z1)) ⌝ ∗
        lazy_int z1 v1 ∗ refines_right K (of_val #zret) }}}.
  Proof.
    iIntros (HE Φ) "(Hv1&HK) HΦ".
    rewrite /cmp_eager_int.
    tp_pures.
    iMod (spec_cmpZ with "[$]") as "HK"; first done.
    wp_apply (wp_cmp_lazy_int_cmp_clutch with "[$Hv1]").
    iIntros (zret) "(%Hret&H1)".
    iApply "HΦ". iFrame; eauto. rewrite Hret. eauto.
  Qed.

  Lemma wp_cmp_eager_lazy_refine_cmp_clutch z1 v1 K E :
    ↑ specN ⊆ E →
    {{{ ▷ spec_lazy_int z1 v1 ∗ refines_right K (cmp_lazy_int (v1, v1)%V) }}}
      cmp_eager_int (#z1, #z1)%V @ E
    {{{ zret, RET #zret ;
        ⌜ zret = (comparison2z (Z.compare z1 z1)) ⌝ ∗
        spec_lazy_int z1 v1 ∗ refines_right K (of_val #zret) }}}.
  Proof.
    iIntros (HE Φ) "(Hv1&HK) HΦ".
    rewrite /cmp_eager_int.
    wp_pures.
    iMod (spec_cmp_lazy_int_cmp_clutch with "[$] [$]") as (?) "(HK&%Hret&Hv1)"; first done.
    wp_apply (wp_cmpZ with "[//]").
    iIntros "_".
    iApply "HΦ". iFrame; eauto. rewrite Hret. iFrame "HK". eauto.
  Qed.

  Definition intτ : type := ∃: (TUnit → #0) * ((#0 * #0) → TInt).

  Definition lazy_int_pack : val :=
    (sample_lazy_int, cmp_lazy_int).

  Definition eager_int_pack : val :=
    (sample_eager_int, cmp_eager_int).

  Definition lrootN := nroot.@"lazy_int".

  Definition R : lrel Σ :=
    LRel (λ v1 v2, ∃ (z : Z),
          ⌜ v2 = #z ⌝ ∗ na_inv clutchRGS_nais (lrootN.@(v1, z)) (lazy_int z v1))%I.

  Lemma lazy_int_eager_int_refinement Δ : ⊢ REL lazy_int_pack << eager_int_pack : interp intτ Δ.
  Proof.
    iApply (refines_pack R).
    rewrite refines_eq. iIntros (K) "HK Hown".
    wp_pures.
    iModIntro. iExists _; iFrame. simpl.
    iExists _, _, _, _.
    iSplit; eauto.
    iSplit; eauto.
    clear K Δ.
    iSplit.
    - iIntros (v1 v2 (->&->)) "!>".
      rewrite refines_eq. iIntros (K) "HK Hown".
      iApply wp_fupd.
      wp_apply (wp_sample_lazy_eager_couple with "HK"); first done.
      iIntros (?) "H".
      iDestruct "H" as (z) "(Hlazy&HK)".
      iMod (na_inv_alloc clutchRGS_nais _ (lrootN.@(v, z)) (lazy_int z v) with "Hlazy") as "#Hinv".
      iModIntro. iExists _. iFrame. iExists z; eauto.
    - iIntros (vp svp) "!> #HR".
      iDestruct "HR" as (v1 v1' v2 v2' -> ->) "(HR1&HR2)".
      iDestruct "HR1" as (z1 ->) "HR1".
      iDestruct "HR2" as (z2 ->) "HR2".
      rewrite refines_eq. iIntros (K) "HK Hown".
      destruct (decide ((v1, z1) = (v2, z2))) as [Heq|Hne].
      { iMod (na_inv_acc with "HR1 Hown") as "(Hint&Hrest&Hclo)"; try set_solver.
        inversion Heq; subst.
        iApply wp_fupd.
        wp_apply (wp_cmp_lazy_eager_refine_cmp_clutch with "[$]"); first auto.
        iIntros (zret) "(%Heq'&Hint&HK)".
        iMod ("Hclo" with "[$]").
        iExists _. iFrame. eauto. }
      { iMod (na_inv_acc with "HR1 Hown") as "(Hint1&Hrest1&Hclo1)"; try set_solver.
        iMod (na_inv_acc with "HR2 Hrest1") as "(Hint2&Hrest2&Hclo2)"; try set_solver.
        { solve_ndisj. }
        iApply wp_fupd.
        wp_apply (wp_cmp_lazy_eager_refine with "[Hint1 Hint2 HK]"); first auto.
        { iFrame. }
        iIntros (zret) "(%Heq'&Hint1&Hint2&HK)".
        iMod ("Hclo2" with "[$]").
        iMod ("Hclo1" with "[$]").
        iExists _. iFrame. eauto. }
  Qed.

  Definition R' : lrel Σ :=
    LRel (λ v1 v2, ∃ (z : Z),
          ⌜ v1 = #z ⌝ ∗ na_inv clutchRGS_nais (lrootN.@(v2, z)) (spec_lazy_int z v2))%I.

  Lemma eager_int_lazy_int_refinement Δ : ⊢ REL eager_int_pack << lazy_int_pack : interp intτ Δ.
  Proof.
    iApply (refines_pack R').
    rewrite refines_eq. iIntros (K) "HK Hown".
    wp_pures.
    iModIntro. iExists _; iFrame. simpl.
    iExists _, _, _, _.
    iSplit; eauto.
    iSplit; eauto.
    clear K Δ.
    iSplit.
    - iIntros (v1 v2 (->&->)) "!>".
      rewrite refines_eq. iIntros (K) "HK Hown".
      iApply wp_fupd.
      wp_apply (wp_sample_eager_lazy_couple with "HK"); first done.
      iIntros (?) "H".
      iDestruct "H" as (v) "(Hlazy&HK)".
      iMod (na_inv_alloc clutchRGS_nais _ (lrootN.@(v, z)) (spec_lazy_int z v) with "Hlazy") as "#Hinv".
      iModIntro. iExists _. iFrame. iExists z; eauto.
    - iIntros (vp svp) "!> #HR".
      iDestruct "HR" as (v1 v1' v2 v2' -> ->) "(HR1&HR2)".
      iDestruct "HR1" as (z1 ->) "HR1".
      iDestruct "HR2" as (z2 ->) "HR2".
      rewrite refines_eq. iIntros (K) "HK Hown".
      destruct (decide ((v1', z1) = (v2', z2))) as [Heq|Hne].
      { iMod (na_inv_acc with "HR1 Hown") as "(Hint&Hrest&Hclo)"; try set_solver.
        inversion Heq; subst.
        iApply wp_fupd.
        wp_apply (wp_cmp_eager_lazy_refine_cmp_clutch with "[$]"); first auto.
        iIntros (zret) "(%Heq'&Hint&HK)".
        iMod ("Hclo" with "[$]").
        iExists _. iFrame. eauto. }
      { iMod (na_inv_acc with "HR1 Hown") as "(Hint1&Hrest1&Hclo1)"; try set_solver.
        iMod (na_inv_acc with "HR2 Hrest1") as "(Hint2&Hrest2&Hclo2)"; try set_solver.
        { solve_ndisj. }
        iApply wp_fupd.
        wp_apply (wp_cmp_eager_lazy_refine with "[Hint1 Hint2 HK]"); first auto.
        { iFrame. }
        iIntros (zret) "(%Heq'&Hint1&Hint2&HK)".
        iMod ("Hclo2" with "[$]").
        iMod ("Hclo1" with "[$]").
        iExists _. iFrame. eauto. }
  Qed.

End lazy_int.

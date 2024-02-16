From clutch.ub_logic Require Export ub_clutch hash lib.map.
Import Hierarchy.

Section faulty_allocator.

  Context `{!ub_clutchGS Σ}.
  Context (ε : nonnegreal).


  (** Here we implement a faulty memory allocator, whose operations can fail
      with some probability ε
   *)


  Definition extend_spec (f : val) :=
    forall (n : nat) l (vs : list val),
      (0 < n)%Z →
      {{{ € (nnreal_mult (nnreal_nat n) ε) ∗ ▷ l ↦∗ vs }}} f (Val $ LitV $ LitInt $ n) #l
      {{{ RET #();
          l ↦∗ (vs ++ (replicate (Z.to_nat n) #())) }}}.

  Definition store_spec (f : val) :=
    forall (l : loc) (off : nat) (vs : list val) (v : val),
      is_Some (vs !! off) →
      {{{ € ε ∗ ▷ l ↦∗ vs }}} f #l #off v {{{ RET #(); l ↦∗ <[off:=v]> vs }}}.

  Definition load_spec (f : val) :=
    forall (l : loc) (off : nat) (vs : list val) (v : val),
    vs !! off = Some v →
  {{{ € ε ∗ ▷ l ↦∗ vs }}} f #l {{{ RET v; l ↦∗ vs }}}.

  Definition vec_push_back (ext str: val) : val :=
    λ: "s" "r" "l" "v",
      str "l" !"s" "v" ;;
      "s" <- !"s"+#1 ;;
      if: !"s" = !"r" then
        "r" <- #2 * !"r";;
        ext !"s" "l";;
        #()
      else #().

  Definition vec_push_back_sp (ext str : val) s r : val :=
    λ: "l" "v",
      str "l" !s "v" ;;
      s <- !s+#1 ;;
      if: !s = !r then
        r <- #2 * !r;;
        ext !s "l" ;;
        #()
      else #().


  Definition vec_spec vs pb ext str (sval rval : nat) : iProp Σ :=
    ∃ (l s r : loc) xs p,
      (* The potential of error credits *)
      € p ∗
      s ↦ #sval ∗ r ↦ #rval ∗
      l ↦∗ (vs ++ xs) ∗
      ⌜ sval < rval ⌝ ∗
      ⌜ sval = (length vs) ⌝ ∗
      ⌜ rval = (length (vs ++ xs)) ⌝ ∗
                 ⌜ pb = vec_push_back ext str #s #r #l⌝ ∗
                          (* The current potential plus the expected potential
                             is equal to the length
                             of the vector times the error cost of allocation.
                             This ensures we can resize "for free".
                           *)
                          ⌜ (nonneg p + (2 * length xs * ε) = rval * ε)%R ⌝.


  Lemma wp_push_back pb vs ext str (vsval sval rval: nat) (v : val) :
    extend_spec ext ->
    store_spec str ->
    (sval + 1 < rval)%nat ->
    {{{ vec_spec vs pb ext str sval rval ∗ € (nnreal_mult (nnreal_nat 3) ε) }}}
      pb v
      {{{ RET #(); vec_spec (vs ++ (cons v nil)) pb ext str (sval+1) rval }}}.
  Proof.
    rewrite /extend_spec /store_spec.
    iIntros (Hext Hstr Hineq Φ) "(Hvec & Herr) HΦ".
    iDestruct "Hvec" as (l s r xs p)
                          "(Herr2 & Hs & Hr & Hl & %Hleq & %Hlen1 & %Hlen2 & -> & %Hpot)".
    rewrite /vec_push_back.
    assert ((nnreal_nat 3 * ε = ε + (nnreal_nat 2) * ε)%NNR) as Hrw.
    {
      apply nnreal_ext. simpl.
      lra.
    }
    rewrite Hrw.
    iPoseProof (ec_split _ _ with "Herr") as "(Herr3 & Herr4)".
    wp_pures.
    wp_load.
    wp_pures.
    wp_bind (str _ _ _).
    wp_apply (Hstr with "[$Herr3 Hl //]").
    { apply lookup_lt_is_Some_2.
      rewrite -Hlen2.
      by apply INR_lt.
    }
    iIntros.
    wp_pures.
    wp_load.
    wp_store.
    wp_load.
    wp_load.
    wp_pure.
    rewrite bool_decide_eq_false_2; last first.
    {
      intro H.
      inversion H.
      lia.
    }
    wp_pures.
    iModIntro.
    iApply "HΦ".
    rewrite /vec_spec.
    iExists l, s, r.
    destruct xs as [| x xs].
    {
      rewrite app_length /= in Hlen2.
      lia.
    }
    iExists xs, (nnreal_plus p (nnreal_mult (nnreal_nat 2) ε)).
    assert (#(sval + 1)%nat = #(sval + 1)) as Hsval.
    {
      do 2 f_equal. lia.
    }
    rewrite Hsval.
    iFrame.
    iSplitL "Herr2 Herr4".
    { iApply ec_split. iFrame. }
    iSplit.
    {
      rewrite cons_middle app_assoc insert_app_l.
      - rewrite -(Nat.add_0_r sval) Hlen1.
        rewrite insert_app_r //.
      - rewrite app_length /=.
        lia.
    }
    iSplit.
    {
      iPureIntro.
      by apply lt_INR in Hineq.
    }
    iSplit.
    {
      iPureIntro.
      rewrite app_length Hlen1 /= //.
    }
    iSplit.
    {
      iPureIntro.
      rewrite Hlen2.
      do 3 rewrite app_length /=.
      lia.
    }
    iSplit.
    { done. }
    iPureIntro.
    simpl.
    rewrite -Hpot cons_length S_INR.
    rewrite Rmult_plus_distr_r Rmult_1_l.
    rewrite Rplus_assoc.
    rewrite Rmult_plus_distr_r Rmult_1_l.
    rewrite Rmult_plus_distr_l Rmult_1_r /=.
    lra.
  Qed.

  Lemma wp_push_back_resize pb vs ext str (vsval sval rval: nat) (v : val) :
    extend_spec ext ->
    store_spec str ->
    (sval + 1 = rval)%nat ->
    {{{ vec_spec vs pb ext str sval rval ∗ € (nnreal_mult (nnreal_nat 3) ε) }}}
      pb v
      {{{ RET #(); vec_spec (vs ++ (cons v nil)) pb ext str (sval+1) (2*rval) }}}.
  Proof.
    rewrite /extend_spec /store_spec.
    iIntros (Hext Hstr Heq Φ) "(Hvec & Herr) HΦ".
    iDestruct "Hvec" as (l s r xs p)
                          "(Herr2 & Hs & Hr & Hl & %Hleq & %Hlen1 & %Hlen2 & -> & %Hpot)".
    rewrite /vec_push_back.
    assert ((nnreal_nat 3 * ε = ε + (nnreal_nat 2) * ε)%NNR) as Hrw.
    {
      apply nnreal_ext. simpl.
      lra.
    }
    assert (length xs = 1%nat) as Hxs.
    {
      rewrite app_length -Hlen1 -Heq in Hlen2. lia.
    }
    rewrite Hrw.
    iPoseProof (ec_split _ _ with "Herr") as "(Herr3 & Herr4)".
    wp_pures.
    wp_load.
    wp_pures.
    wp_bind (str _ _ _).
    wp_apply (Hstr with "[$Herr3 Hl //]").
    { apply lookup_lt_is_Some_2.
      apply INR_lt.
      rewrite -Hlen2 //.
    }
    iIntros "Hl".
    wp_pures.
    wp_load.
    wp_store.
    wp_load.
    wp_load.
    wp_pure.
    assert (#(sval + 1)%nat = #(sval + 1)) as Hsval.
    {
      do 2 f_equal. lia.
    }
    rewrite bool_decide_eq_true_2; last first.
    {
      do 2 f_equal; lia.
    }
    wp_pures.
    wp_load.
    wp_store.
    wp_load.
    wp_bind (ext _ _)%E.
    rewrite -Hsval.
    wp_apply (Hext (Init.Nat.add sval (S O)) l with "[Herr2 Herr4 Hl]").
    { simpl; lia. }
    { iFrame.
      replace (nnreal_nat (sval + 1) * ε)%NNR with
        (nnreal_plus p (nnreal_nat 2 * ε))%NNR.
      - iApply ec_split; iFrame.
      - apply nnreal_ext. simpl.
        rewrite Heq -Hpot Hxs.
        simpl. lra.
    }
    iIntros "Hl".
    wp_pures.
    iApply "HΦ".
    iMod (ec_zero).
    iModIntro.
    rewrite /vec_spec.
    iExists l, s, r.
    rewrite Hsval.
    iExists (replicate (Z.to_nat (sval + 1)%nat) #()), (nnreal_zero).
    iFrame.
    iSplitL "Hr".
    {
      assert (#(2 * rval)%nat = #(2 * rval)) as ->; try iFrame.
      do 2 f_equal. lia.
    }
    iSplitL "Hl".
    {
      destruct xs as [| x xs]; [simpl in Hxs; done |].
      destruct xs as [| x' xs]; [ | simpl in Hxs; done].
      rewrite cons_middle app_assoc insert_app_l.
      - rewrite -(Nat.add_0_r sval) Hlen1 /=.
        rewrite insert_app_r /=.
        rewrite app_nil_r. iFrame.
      - rewrite app_length /=.
        lia.
    }
    iSplit.
    {
      iPureIntro.
      rewrite Heq mult_INR /=.
      assert (0 < rval); [ | lra].
      eapply Rle_lt_trans; eauto.
      apply pos_INR.
    }
    iSplit.
    {
      iPureIntro.
      rewrite app_length /=.
      apply INR_eq.
      do 2 rewrite plus_INR.
      rewrite Hlen1. lra.
    }
    iSplit.
    {
      iPureIntro.
      do 2 rewrite app_length /=.
      rewrite -Heq.
      rewrite replicate_length /=.
      rewrite -Hlen1.
      apply INR_eq.
      rewrite Nat2Z.id.
      do 6 rewrite plus_INR /=.
      lra.
    }
    iSplit.
    {
      iPureIntro.
      done.
    }
    iPureIntro.
    simpl.
    rewrite Heq replicate_length /=.
    rewrite Nat2Z.id.
    do 2 rewrite plus_INR /=.
    lra.
  Qed.


End faulty_allocator.



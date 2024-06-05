From clutch.eris Require Export eris hash lib.map.
Import Hierarchy.

Section faulty_allocator.

  Context `{!erisGS Σ}.
  Context (ε : nonnegreal).


  (** Here we implement a faulty memory allocator, whose operations can fail
      with some probability ε
   *)


  Definition extend_spec (f : val) :=
    forall (n : nat) l (vs : list val),
      (0 < n)%Z →
      {{{ ↯ (nnreal_mult (nnreal_nat n) ε) ∗ ▷ l ↦∗ vs }}} f (Val $ LitV $ LitInt $ n) #l
      {{{ l', RET #l';
          l' ↦∗ (vs ++ (replicate (Z.to_nat n) #())) }}}.

  Definition store_spec (f : val) :=
    forall (l : loc) (off : nat) (vs : list val) (v : val),
      is_Some (vs !! off) →
      {{{ ↯ ε ∗ l ↦∗ vs }}} f #l #off v {{{ RET #(); l ↦∗ <[off:=v]> vs }}}.

  Definition load_spec (f : val) :=
    forall (l : loc) (off : nat) (vs : list val) (v : val),
    vs !! off = Some v →
  {{{ ↯ ε ∗ l ↦∗ vs }}} f #l {{{ RET v; l ↦∗ vs }}}.



  Definition vec_push_back (ext str: val) : val :=
    λ: "vec" "v",
      let, ( "l", "s", "r" ) := "vec" in
      str "l" "s" "v" ;;
      if: "s" + #1 = "r" then
        let: "l'" := ext "r" "l" in
        ( "l'", "s" + #1, #2 * "r" )
      else ( "l", "s" + #1, "r" ).


  Definition vec_spec (vec : val) (vs : list val) : iProp Σ :=
    ∃ (l : loc) (sval rval : nat) xs p,
      ⌜ vec = ( #l, #sval, #rval )%V ⌝ ∗
      (* The potential of error credits *)
      ↯ p ∗
      l ↦∗ (vs ++ xs) ∗
      ⌜ sval < rval ⌝ ∗
      ⌜ sval = (length vs) ⌝ ∗
      ⌜ rval = (length (vs ++ xs)) ⌝ ∗
       (* The current potential plus the expected potential
         is equal to the length
         of the vector times the error cost of allocation.
         This ensures we can resize "for free".
       *)
      ⌜ (nonneg p + (2 * length xs * ε) = rval * ε)%R ⌝.


  Lemma wp_push_back vs ext str (vec v : val) :
    extend_spec ext ->
    store_spec str ->
    {{{ vec_spec vec vs ∗ ↯ (nnreal_mult (nnreal_nat 3) ε) }}}
      vec_push_back ext str vec v
    {{{ vec', RET vec' ; vec_spec vec' (vs ++ (cons v nil)) }}}.
  Proof.
    rewrite /extend_spec /store_spec.
    iIntros (Hext Hstr Φ) "(Hvec & Herr) HΦ".
    iDestruct "Hvec" as (l sval rval xs p) "(-> &Herr2 & Hl & %Hleq & %Hlen1 & %Hlen2 & %Hpot)".
    rewrite /vec_push_back.
    assert ((nnreal_nat 3 * ε = ε + (nnreal_nat 2) * ε)%NNR) as ->.
    {
      apply nnreal_ext. simpl.
      lra.
    }
    assert ((sval + 1 < rval)%nat \/ (sval + 1 = rval)%nat) as [Hno | Hyes].
    {
      apply INR_lt in Hleq.
      inversion Hleq.
      - right. lia.
      - left. lia.
    }
    (* Case: No resizing *)
    - wp_pures.
      iPoseProof (ec_split _ _ with "Herr") as "(Herr3 & Herr4)".
      wp_bind (str _ _ _).
      wp_apply (Hstr with "[$Herr3 Hl //]").
      { apply lookup_lt_is_Some_2.
        rewrite -Hlen2.
        by apply INR_lt.
      }
      iIntros "Hl".
      wp_pures.
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
      iExists l, (sval + 1)%nat, rval.
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
      iSplit; auto.
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
        by apply lt_INR in Hno.
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
      iPureIntro.
      simpl.
      rewrite -Hpot cons_length S_INR.
      rewrite Rmult_plus_distr_r Rmult_1_l.
      rewrite Rplus_assoc.
      rewrite Rmult_plus_distr_r Rmult_1_l.
      rewrite Rmult_plus_distr_l Rmult_1_r /=.
      lra.
    (* Case : Resizing *)
    - wp_pures.
      iPoseProof (ec_split _ _ with "Herr") as "(Herr3 & Herr4)".
      wp_bind (str _ _ _).
      wp_apply (Hstr with "[$Herr3 Hl //]").
      { apply lookup_lt_is_Some_2.
        apply INR_lt.
        rewrite -Hlen2 //.
      }
      iIntros "Hl".
      wp_pures.
      assert (#(sval + 1)%nat = #(sval + 1)) as Hsval.
      {
        do 2 f_equal. lia.
      }
      assert (length xs = 1%nat) as Hxs.
      {
        rewrite app_length -Hlen1 in Hlen2. lia.
      }
      rewrite bool_decide_eq_true_2; last first.
      {
        do 2 f_equal; lia.
      }
      wp_pures.
      wp_bind (ext _ _)%E.
      wp_apply (Hext rval l with "[Herr2 Herr4 Hl]").
      { simpl; lia. }
      {
        iFrame.
        replace (nnreal_nat rval * ε)%NNR with
          (nnreal_plus p (nnreal_nat 2 * ε))%NNR.
        - iApply ec_split; iFrame.
        - apply nnreal_ext. simpl.
          rewrite -Hpot Hxs.
          simpl. lra.
      }
      iIntros (l') "Hl'".
      wp_pures.
      iApply "HΦ".
      iMod (ec_zero).
      iModIntro.
      rewrite /vec_spec.
      iExists l', (sval + 1)%nat, (2*rval)%nat.
      rewrite Hsval.
      iExists (replicate (Z.to_nat (sval + 1)%nat) #()), (nnreal_zero).
      iFrame.
      iSplit.
      {
        assert (#(2 * rval)%nat = #(2 * rval)) as ->; auto.
        do 2 f_equal. lia.
      }
      iSplitL "Hl'".
      {
        destruct xs as [| x xs]; [simpl in Hxs; done |].
        destruct xs as [| x' xs]; [ | simpl in Hxs; done].
        rewrite cons_middle app_assoc insert_app_l.
        - rewrite Hyes.
          rewrite -(Nat.add_0_r sval) Hlen1 /=.
          rewrite insert_app_r /=.
          rewrite app_nil_r.
          iFrame.
        - rewrite app_length /=.
          lia.
      }
      iSplit.
      {
        iPureIntro.
        rewrite Hyes mult_INR /=.
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
        rewrite -Hyes.
        rewrite replicate_length /=.
        rewrite -Hlen1.
        apply INR_eq.
        rewrite Nat2Z.id.
        do 6 rewrite plus_INR /=.
        lra.
      }
      iPureIntro.
      simpl.
      rewrite Hyes replicate_length /=.
      rewrite Nat2Z.id.
      do 2 rewrite plus_INR /=.
      lra.
  Qed.


End faulty_allocator.



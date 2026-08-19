From Coq Require Import Arith.PeanoNat Lists.List Reals Psatz Lia.
From clutch.eris Require Import eris.
From clutch.common Require Import inject.
From clutch.eris.lib Require Import list.
From clutch.eris.lib.sampling Require Import utils.
From clutch.eris.lib.sampling.fldr Require Import implementation model walk pure distribution list_total preprocessing walk_spec round tape presample loop.
Import ListNotations.
#[local] Open Scope R.

Section FldrPresampleOutput.
  Context `{!erisGS Σ}.

  Definition rejected_round (ws : list nat) (bs : list (fin 2)) : Prop :=
    exists j, round_ok ws bs j /\ rejected ws j.

  Lemma twp_fldr_presample_output_aux E (ws : list nat) (α : loc)
      (outs : list nat) (raw : list (fin 2)) (rej : list (list (fin 2)))
      (e : expr) (Φ : val -> iProp Σ) (D : nat -> R) (L ε : R) :
    admissible ws -> nondegenerate ws -> to_val e = None ->
    (forall i, (0 <= D i <= L)%R) ->
    SeriesC (fun i => target_mass ws i * D i)%R = ε ->
    ⌜is_fldr_translation ws raw outs⌝ ∗
    ⌜Forall (rejected_round ws) rej⌝ ∗
    α ↪ (1%nat; raw ++ concat rej) ∗ ↯ ε ∗
    (∀ (i : nat), ⌜(i < length ws)%nat⌝ ∗
      own_fldr_tape ws α (outs ++ [i]) ∗ ↯ (D i) -∗ WP e @ E [{ Φ }])
    ⊢ WP e @ E [{ Φ }].
  Proof.
    intros Hadm Hnd He HD HSum.
    set (n := length ws).
    set (a := (INR (weight_sum ws) / INR (denominator ws))%R).
    set (r := proposal_mass ws n).
    pose proof (facts ws Hadm) as Hfacts.
    simpl in Hfacts.
    destruct Hfacts as (Ha & Ha1 & Hr & Hr1 & Har).
    destruct (Req_dec r 0) as [Hr0|Hrne].
    - set (D' := fun i => if i <? n then D i else 1%R).
      assert (Hsum' : SeriesC (fun i => proposal_mass ws i * D' i)%R = ε).
      { unfold D'. rewrite (proposal_split ws D 1 Hadm).
        rewrite HSum.
        unfold r in Hr0.
        rewrite Hr0.
        unfold a, r in Har.
        rewrite Hr0 in Har.
        rewrite Rplus_0_r in Har.
        rewrite Har. ring. }
      assert (HL0 : (0 <= L)%R).
      { pose proof (proj2 (HD 0%nat)) as HD0U.
        pose proof (proj1 (HD 0%nat)) as HD0. lra. }
      assert (HD' : forall i, (0 <= D' i <= L + 1)%R).
      { intros i. unfold D'. destruct (i <? n).
        - destruct (HD i) as [HDi0 HDiL]. split; [exact HDi0|lra].
        - split; lra. }
      iIntros "(Htrans & Hrej & Hα & Herr & Hnext)".
      iDestruct "Htrans" as %Htrans.
      iDestruct "Hrej" as %Hrej.
      iApply (twp_fldr_presample_round E ws α (raw ++ concat rej)
        e Φ D' (L+1) ε Hadm Hnd He HD' Hsum').
      iSplitL "Hα"; [iExact "Hα"|].
      iSplitL "Herr"; [iExact "Herr"|].
      iIntros (i bs) "(%Hround & %Hi & Htape & Hcredit)".
      destruct (decide ((i < n)%nat)) as [Hacc|Hacc].
      + assert (Hacc_ws : (i < length ws)%nat) by (unfold n in Hacc; lia).
iApply "Hnext".
        iSplitL "".
        * iPureIntro. exact Hacc_ws.
        * iSplitL "Htape".
          -- iExists (raw ++ concat rej ++ bs). iSplitL "Htape".
             ++ rewrite <- (app_assoc raw (concat rej) bs). iExact "Htape".
             ++ iPureIntro.
                apply is_fldr_translation_snoc.
                --- exact Htrans.
                --- exact Hrej.
                --- exact Hround.
                --- exact Hacc_ws.
          -- iApply (ec_eq with "Hcredit"). unfold D'. assert (Hacc' : (i <? n) = true) by (apply Nat.ltb_lt; exact Hacc). rewrite Hacc'. reflexivity.
      +
        assert (Hlen : length (extended_weights ws) = S n).
        { unfold extended_weights. rewrite app_length. simpl. lia. }
        rewrite Hlen in Hi.
        assert (HiEq : i = n) by lia.
        assert (HDone : D' i = 1%R).
        { unfold D'. rewrite HiEq. rewrite Nat.ltb_irrefl. reflexivity. }
        iPoseProof (ec_eq (D' i) 1%R HDone with "Hcredit") as "Hone".
        iDestruct (ec_contradict 1%R with "Hone") as "[]". lra.
    - unfold r, n in Hrne.
      assert (Hrpos : (0 < r)%R).
      { unfold r, n.
        pose proof (pm_nonneg ws (length ws)) as Hnonneg.
        destruct (Req_dec (proposal_mass ws (length ws)) 0) as [Hz|Hz].
        - exfalso. apply Hrne. exact Hz.
        - lra. }
      assert (Hr_inv : (1 < / r)%R).
      { replace 1%R with (/1)%R by apply Rinv_1.
        apply (Rinv_0_lt_contravar r 1 Hrpos). exact Hr1. }
      assert (HL0 : (0 <= L)%R).
      { pose proof (proj2 (HD 0%nat)) as HD0U.
        pose proof (proj1 (HD 0%nat)) as HD0. lra. }
      iIntros "(Htrans & Hrej & Hα & Herr & Hnext)".
      iApply twp_rand_err_pos; auto.
      iIntros (εterm Hεterm) "Hterm".
      iRevert (rej D ε HD HSum) "Htrans Hrej Hα Herr Hnext".
      iApply (ec_ind_amp _ (/ r) with "[] Hterm"); try done.
      iModIntro.
      iIntros (ε' Hε') "IH Hterm".
      iIntros (rej D ε HD HSum) "Htrans Hrej Hα Herr Hnext".
      assert (Heps0 : (0 <= ε)%R).
      { rewrite <- HSum. apply SeriesC_ge_0'. intros i.
        apply Rmult_le_pos; [apply target_mass_pos; exact Hadm|apply (proj1 (HD i))]. }
      set (q := (ε + (/ r) * ε')%R).
      set (D' := fun i => if i <? n then D i else q).
      assert (Hq0 : (0 <= q)%R).
      { unfold q. apply Rplus_le_le_0_compat; [exact Heps0|].
        apply Rmult_le_pos; [apply Rlt_le; apply Rinv_0_lt_compat; lra|lra]. }
      assert (HD' : forall i, (0 <= D' i <= L + q)%R).
      { intros i. unfold D'. destruct (i <? n).
        - destruct (HD i) as [HDi0 HDiL]. split; [exact HDi0|lra].
        - split; lra. }
      assert (Hsum' : SeriesC (fun i => proposal_mass ws i * D' i)%R = ε + ε').
      { unfold D'. rewrite (proposal_split ws D q Hadm).
        rewrite HSum.
        fold n. fold r. fold a.
        unfold q.
        rewrite Rmult_plus_distr_l.
        rewrite <- Rmult_assoc.
        rewrite Rmult_inv_r; [|lra].
        replace (a * ε + (r * ε + 1 * ε'))%R with ((a+r)*ε + ε')%R by ring.
        rewrite Har. ring. }
      iAssert (∀ (i : nat) (bs : list (fin 2)),
          ⌜round_ok ws bs i⌝ ∗
          ⌜(i < length (extended_weights ws))%nat⌝ ∗
          α ↪ (1%nat; raw ++ concat rej ++ bs) ∗ ↯ (D' i) -∗
          WP e @ E [{ Φ }])%I with "[Hnext Htrans Hrej IH]" as "Hroundnext".
      { iDestruct "Htrans" as %Htrans.
        iDestruct "Hrej" as %Hrej.
        iIntros (i bs) "(%Hround & %Hi & Htape & Hcredit)".
        destruct (decide ((i < n)%nat)) as [Hacc|Hacc].
        - assert (Hacc_ws : (i < length ws)%nat) by (unfold n in Hacc; lia).
          iApply "Hnext".
          iSplitL "".
          + iPureIntro. exact Hacc_ws.
          + iSplitL "Htape".
            * iExists (raw ++ concat rej ++ bs). iSplitL "Htape".
              -- rewrite (app_assoc raw (concat rej) bs). iExact "Htape".
              -- iPureIntro. apply is_fldr_translation_snoc.
                 --- exact Htrans.
                 --- exact Hrej.
                 --- exact Hround.
                 --- exact Hacc_ws.
            * iApply (ec_eq with "Hcredit"). unfold D'. assert (Hacc' : (i <? n) = true) by (apply Nat.ltb_lt; exact Hacc). rewrite Hacc'. reflexivity.
        -
          assert (Hlen : length (extended_weights ws) = S n).
          { unfold extended_weights. rewrite app_length. simpl. lia. }
          rewrite Hlen in Hi.
          assert (HiEq : i = n) by lia.
          assert (HDone : D' i = q).
          { unfold D'. rewrite HiEq. rewrite Nat.ltb_irrefl. reflexivity. }
          iPoseProof (ec_eq (D' i) q HDone with "Hcredit") as "Hrejcredit".
          assert (Hamp0 : (0 <= (/ r * ε'))%R).
          { apply Rmult_le_pos; [apply Rlt_le; apply Rinv_0_lt_compat; lra|lra]. }
          iDestruct (ec_split with "Hrejcredit") as "[HerrMain HerrAmp]"; [exact Heps0|exact Hamp0|].
          iSpecialize ("IH" with "HerrAmp").
          assert (Hrej' : Forall (rejected_round ws) (rej ++ [bs])).
          { apply Forall_app. split; [exact Hrej|].
            constructor.
            + exists i. split; [exact Hround|].
              unfold rejected. intro Hil. unfold n in HiEq. lia.
            + constructor. }
          iAssert (⌜concat (rej ++ [bs]) = concat rej ++ bs⌝)%I as "Hconcat".
          { iPureIntro. rewrite concat_app. simpl. rewrite app_nil_r. reflexivity. }
          iDestruct "Hconcat" as %Hconcat.
          iPoseProof ("IH" $! (rej ++ [bs]) D ε) as "IH'".
          iEval (rewrite Hconcat) in "IH'".
          iApply ("IH'" with "[] [] [] [] Htape HerrMain Hnext").
          + iPureIntro. exact HD.
          + iPureIntro. exact HSum.
          + iPureIntro. exact Htrans.
          + iPureIntro. exact Hrej'.
      }
      iAssert (∀ (i : nat) (bs : list (fin 2)),
          ⌜round_ok ws bs i⌝ ∗
          ⌜(i < length (extended_weights ws))%nat⌝ ∗
          α ↪ (1%nat; (raw ++ concat rej) ++ bs) ∗ ↯ (D' i) -∗
          WP e @ E [{ Φ }])%I with "[Hroundnext]" as "Hroundnext'".
      { iIntros (i bs) "(%Hround & %Hi & Htape & Hcredit)".
        iApply ("Hroundnext" $! i bs).
        iSplitL "".
        - iPureIntro. exact Hround.
        - iSplitL "".
          + iPureIntro. exact Hi.
          + iSplitL "Htape".
            * rewrite <- (app_assoc raw (concat rej) bs). iExact "Htape".
            * iExact "Hcredit". }
      iApply (twp_fldr_presample_round E ws α (raw ++ concat rej)
        e Φ D' (L+q) (ε+ε') Hadm Hnd He HD' Hsum').
      iSplitL "Hα"; [iExact "Hα"|].
      iSplitL "Hterm Herr"; [iPoseProof (ec_combine with "[$Hterm $Herr]") as "Hec"; iApply (ec_eq (ε' + ε) (ε + ε') ltac:(ring) with "Hec")|iExact "Hroundnext'"].
  Qed.

  Lemma twp_fldr_presample_output E (ws : list nat) (α : loc)
        (outs : list nat) (e : expr) (Φ : val -> iProp Σ)
        (D : nat -> R) (L ε : R) :
    admissible ws -> nondegenerate ws -> to_val e = None ->
    (forall i, (0 <= D i <= L)%R) ->
    SeriesC (fun i => target_mass ws i * D i)%R = ε ->
    own_fldr_tape ws α outs ∗ ↯ ε ∗
    (∀ (i : nat), ⌜(i < length ws)%nat⌝ ∗
      own_fldr_tape ws α (outs ++ [i]) ∗ ↯ (D i) -∗ WP e @ E [{ Φ }])
    ⊢ WP e @ E [{ Φ }].
  Proof.
    intros Hadm Hnd He HD HSum.
    iIntros "(Htape & Herr & Hnext)".
    iDestruct "Htape" as "(%raw & Hα & %Htrans)".
    iApply (twp_fldr_presample_output_aux E ws α outs raw [] e Φ D L ε
      Hadm Hnd He HD HSum).
    iSplitL "".
    - iPureIntro. exact Htrans.
    - iSplitL "".
      + iPureIntro. constructor.
      + iSplitL "Hα".
        * rewrite app_nil_r. iExact "Hα".
        * iSplitL "Herr"; [iExact "Herr"|iExact "Hnext"].
  Qed.
End FldrPresampleOutput.

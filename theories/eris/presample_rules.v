(** * Rules for presampling to tapes  *)
From stdpp Require Import namespaces finite.
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext.
From clutch.prob_lang Require Import notation tactics metatheory.
From clutch.prob_lang Require Export lang.
From clutch.eris Require Export lifting proofmode ectx_lifting primitive_laws seq_amplification.
From clutch.eris Require Export total_lifting total_ectx_lifting total_primitive_laws.



Section rules.
  Context `{!erisGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types v : val.
  Implicit Types l : loc.


  (** * Approximate Lifting *)

  Lemma pgl_state (N : nat) 𝜎 𝛼 ns :
    𝜎.(tapes) !! 𝛼 = Some (N; ns) →
    pgl
      (state_step 𝜎 𝛼)
      (λ 𝜎', ∃ (n : fin (S N)), 𝜎' = state_upd_tapes <[𝛼 := (N; ns ++ [n])]> 𝜎)
      nnreal_zero.
  Proof.
    rewrite /pgl. intros Htapes.
    apply Req_le_sym; simpl.
    rewrite /prob SeriesC_0; auto.
    intros 𝜎'.
    case_bool_decide; auto.
    rewrite /state_step.
    case_bool_decide.
    2: { exfalso. apply H0. by apply elem_of_dom. }
    intros.
    replace (lookup_total 𝛼 (tapes 𝜎)) with (N; ns).
    2: { rewrite (lookup_total_correct _ _ (existT N ns)); auto.  }
    apply dmap_unif_zero.
    intros n Hcont.
    apply H.
    naive_solver.
  Qed.

  (** adapted from wp_couple_tapes in the relational logic *)
  Lemma twp_presample (N : nat) E e 𝛼 Φ ns :
    to_val e = None →
    𝛼 ↪ (N; ns) ∗
      (∀ (n : fin (S N)), 𝛼 ↪ (N; ns ++ [n]) -∗ WP e @ E [{ Φ }])
      ⊢ WP e @ E [{ Φ }].
  Proof.
    iIntros (He) "(H𝛼&Hwp)".
    iApply twp_lift_step_fupd_glm; [done|].
    iIntros (𝜎 ε) "((Hheap&Htapes)&Hε)".
    iDestruct (ghost_map_lookup with "Htapes H𝛼") as %Hlookup.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    replace ε with (nnreal_zero + ε)%NNR by (apply nnreal_ext; simpl; lra).
    iApply glm_state_step.
    { rewrite /= /get_active.
      by apply elem_of_list_In, elem_of_list_In, elem_of_elements, elem_of_dom. }
    iExists _.
    iSplitR.
    { iPureIntro. apply pgl_state, Hlookup. }
    iIntros (𝜎') "[%n %H𝜎']".
    iDestruct (ghost_map_lookup with "Htapes H𝛼") as %?%lookup_total_correct.
    iMod (ghost_map_update ((N; ns ++ [n]) : tape) with "Htapes H𝛼") as "[Htapes H𝛼]".
    iMod "Hclose'" as "_".
    iSpecialize ("Hwp" $! n with "H𝛼").
    rewrite !tgl_wp_unfold /tgl_wp_pre /= He.
    iSpecialize ("Hwp" $! 𝜎' ε).
    iMod ("Hwp" with "[Hheap Htapes Hε]") as "Hwp".
    { replace (nnreal_zero + ε)%NNR with ε by (apply nnreal_ext; simpl; lra).
      rewrite H𝜎'.
      iFrame.
    }
    iModIntro. iApply "Hwp".
  Qed.

  Lemma wp_presample (N : nat) E e 𝛼 Φ ns :
    to_val e = None →
    ▷ 𝛼 ↪ (N; ns) ∗
      (∀ (n : fin (S N)), 𝛼 ↪ (N; ns ++ [n]) -∗ WP e @ E {{ Φ }})
      ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (He) "(>H𝛼&Hwp)".
    iApply wp_lift_step_fupd_glm; [done|].
    iIntros (𝜎 ε) "((Hheap&Htapes)&Hε)".
    iDestruct (ghost_map_lookup with "Htapes H𝛼") as %Hlookup.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    replace ε with (nnreal_zero + ε)%NNR by (apply nnreal_ext; simpl; lra).
    iApply glm_state_step.
    { rewrite /= /get_active.
      by apply elem_of_list_In, elem_of_list_In, elem_of_elements, elem_of_dom. }
    iExists _.
    iSplitR.
    { iPureIntro. apply pgl_state, Hlookup. }
    iIntros (𝜎') "[%n %H𝜎']".
    iDestruct (ghost_map_lookup with "Htapes H𝛼") as %?%lookup_total_correct.
    iMod (ghost_map_update ((N; ns ++ [n]) : tape) with "Htapes H𝛼") as "[Htapes H𝛼]".
    iMod "Hclose'" as "_".
    iSpecialize ("Hwp" $! n with "H𝛼").
    rewrite !pgl_wp_unfold /pgl_wp_pre /= He.
    iSpecialize ("Hwp" $! 𝜎' ε).
    iMod ("Hwp" with "[Hheap Htapes Hε]") as "Hwp".
    { replace (nnreal_zero + ε)%NNR with ε by (apply nnreal_ext; simpl; lra).
      rewrite H𝜎'.
      iFrame.
    }
    iModIntro. iApply "Hwp".
  Qed.

  Lemma twp_presample_adv_comp (N : nat) z E e α Φ ns (ε1 : R) (ε2 : fin (S N) -> R) :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (forall n, (0 <= ε2 n)%R) ->
    SeriesC (λ n, (1 / (S N)) * ε2 n)%R = ε1 →
    α ↪ (N; ns) ∗
      ↯ ε1 ∗
      (∀ (n : fin (S N)), ↯ (ε2 n) ∗ α ↪ (N; ns ++ [n]) -∗ WP e @ E [{ Φ }])
      ⊢ WP e @ E [{ Φ }].
  Proof.
    iIntros (-> Hσ_red Hε2pos Hsum) "(Hα & Hε & Hwp)".
    destruct (fin_function_bounded (S (Z.to_nat z)) ε2) as [r Hr_ub].
    assert (0 <= r)%R as Hrpos.
    {
      transitivity (ε2 0%fin); auto.
    }
    iApply twp_lift_step_fupd_glm; [done|].
    iIntros (σ1 ε_now) "[(Hheap&Htapes) Hε_supply]".
    iDestruct (ghost_map_lookup with "Htapes Hα") as %Hlookup.
    iDestruct (ec_supply_bound with "Hε_supply Hε") as %Hε1_ub.

    iMod (ec_supply_decrease with "Hε_supply Hε") as (ε1' ε_rem -> Hε1') "Hε_supply".
    iApply fupd_mask_intro; [set_solver|].
    iIntros "Hclose".
    iApply (glm_state_adv_comp' α); simpl.
    { rewrite /get_active.
      apply elem_of_list_In, elem_of_list_In, elem_of_elements, elem_of_dom.
      done. }
    (* iDestruct (ec_supply_ec_inv with "Hε_supply Hε") as %(ε1' & ε_rem & -> & Hε1'). *)


    (* R: predicate should hold iff tapes σ' at α is ns ++ [n] *)
    iExists
      (fun σ' : state => exists n : fin _, σ' = (state_upd_tapes <[α:=(_; ns ++ [n]) : tape]> σ1)),
      (fun ρ => (ε_rem +
                   match finite.find (fun s => state_upd_tapes <[α:=(_; ns ++ [s]) : tape]> σ1 = snd ρ) with
                   | Some s => mknonnegreal _ (Hε2pos s)
                   | None => nnreal_zero
                   end))%NNR.

    (* upper bound on ε2 *)
    iSplit.
    { iPureIntro.
      assert (Hr_nnonneg : (0 <= r)%R).
      { eapply Rle_trans; [|apply (Hr_ub 0%fin)].
        auto.
      }
      exists (ε_rem + r)%R.
      intros [e' σ'].
      apply Rplus_le_compat_l.
      destruct (finite.find _); auto; apply Hr_ub.
    }

    (* upper bound on total error *)
    iSplit.
    { iPureIntro. simpl.
      rewrite Hε1'.
      rewrite -Hsum.
      setoid_rewrite Rmult_plus_distr_l.
      rewrite SeriesC_plus.
      (* existence *)
      2: { apply ex_seriesC_scal_r, pmf_ex_seriesC. }
      2: { apply pmf_ex_seriesC_mult_fn.
           exists r; intros; split.
           - apply cond_nonneg.
           - destruct (finite.find _); [apply Hr_ub | simpl; auto]. }

      apply Rplus_le_compat.
      { (* holds because state_step is a pmf so is lt 1 *)
        rewrite SeriesC_scal_r -{2}(Rmult_1_l (nonneg ε_rem)).
        apply Rmult_le_compat; try auto; lra. }

      (* rewrite to a form for SeriesC_le *)
      pose f := (fun n : fin _ => 1 / S (Z.to_nat z) * ε2 n)%R.
      rewrite (SeriesC_ext
                 (λ x : state, state_step σ1 α x * _)%R
                 (fun x : state => from_option f 0
                                     (finite.find (fun n => state_upd_tapes <[α:=(_; ns ++ [n]) : tape]> σ1 = x ))%R));
        last first.
      { intros n.
        destruct (finite.find _) as [sf|] eqn:HeqF.
        - Opaque INR.
          apply find_Some in HeqF.
          simpl in HeqF; rewrite -HeqF.
          rewrite /from_option /f.
          apply Rmult_eq_compat_r.
          rewrite /state_upd_tapes /=.
          rewrite /pmf /state_step.
          rewrite bool_decide_true; last first.
          { rewrite elem_of_dom Hlookup /= /is_Some; by exists (Z.to_nat z; ns). }
          rewrite (lookup_total_correct _ _ (Z.to_nat z; ns)); auto.
          rewrite /dmap /dbind /dbind_pmf /pmf.
          rewrite /= SeriesC_scal_l -{1}(Rmult_1_r (1 / _))%R.
          rewrite /Rdiv Rmult_1_l; apply Rmult_eq_compat_l.
          (* this series is 0 unless a = sf *)
          rewrite /dret /dret_pmf.
          rewrite -{2}(SeriesC_singleton sf 1%R).
          apply SeriesC_ext; intros.
          symmetry.
          case_bool_decide; simplify_eq.
          + rewrite bool_decide_true; auto.
          + rewrite bool_decide_false; auto.
            rewrite /not; intros Hcont.
            rewrite /not in H; apply H.
            rewrite /state_upd_tapes in Hcont.
            assert (R1 : ((Z.to_nat z; ns ++ [sf]) : tape) = (Z.to_nat z; ns ++ [n0])).
            { apply (insert_inv (tapes σ1) α). by inversion Hcont. }
            apply Eqdep_dec.inj_pair2_eq_dec in R1; [|apply PeanoNat.Nat.eq_dec].
            apply app_inv_head in R1.
            by inversion R1.
            Transparent INR.
        - rewrite /from_option /INR /=. lra.
      }

      apply SeriesC_le_inj.
      - (* f is nonnegative *)
        intros.
        apply Rmult_le_pos.
        + rewrite /Rdiv.
          apply Rmult_le_pos; try lra.
          apply Rlt_le, Rinv_0_lt_compat, pos_INR_S.
        + auto.
      - (* injection *)
        intros ? ? ? HF1 HF2.
        apply find_Some in HF1.
        apply find_Some in HF2.
        by rewrite -HF1 -HF2.
      - (* existence *)
        apply ex_seriesC_finite.
    }

    (* lifted lookup on tapes *)
    iSplit.
    {
      iPureIntro.
      eapply pgl_mon_pred; last first.
      - apply pgl_state. apply Hlookup.
      - done.
    }

    iIntros ((heap2 & tapes2)) "[%sample %Hsample]".

    rewrite /= Hsample.
    destruct (@find_is_Some _ _ _
                (λ s : fin (S (Z.to_nat z)), state_upd_tapes <[α:=(Z.to_nat z; ns ++ [s])]> σ1 = state_upd_tapes <[α:=(Z.to_nat z; ns ++ [sample])]> σ1)
                _ sample eq_refl)
      as [r' [Hfind Hr']].
    rewrite Hfind.
    replace r' with sample; last first.
    { rewrite /state_upd_tapes in Hr'.
      inversion Hr' as [Heqt].
      apply (insert_inv (tapes σ1) α) in Heqt.
      apply Eqdep_dec.inj_pair2_eq_dec in Heqt; [|apply PeanoNat.Nat.eq_dec].
      apply app_inv_head in Heqt.
      by inversion Heqt. }
    destruct (Rlt_decision (nonneg ε_rem + (ε2 sample))%R 1%R) as [Hdec|Hdec]; last first.
    { apply Rnot_lt_ge, Rge_le in Hdec.
      iApply exec_stutter_spend.
      iPureIntro.
      simpl ; lra.
    }
    (* replace (nonneg ε_rem + nonneg (ε2 sample))%R with (nonneg (ε_rem + ε2 sample)%NNR); [|by simpl]. *)
    iApply exec_stutter_free.
    iMod (ec_supply_increase _ (mknonnegreal _ (Hε2pos sample)) with "[$Hε_supply]") as "[Hε_supply Hε]".
    { simplify_eq. simpl. lra. }


    iMod (ghost_map_update ((Z.to_nat z; ns ++ [sample]) : tape) with "Htapes Hα") as "[Htapes Hα]".
    iSpecialize ("Hwp" $! sample).
    rewrite tgl_wp_unfold /tgl_wp_pre.
    simpl.
    remember {| heap := heap2; tapes := tapes2 |} as σ2.
    rewrite Hσ_red.
    iSpecialize ("Hwp" with "[Hε Hα]"); first iFrame.
    iSpecialize ("Hwp" $! σ2 _).
    iSpecialize ("Hwp" with "[Hheap Htapes Hε_supply]").
    { iSplitL "Hheap Htapes".
      - rewrite /tapes_auth.
        rewrite Heqσ2 in Hsample. inversion Hsample.
        simplify_eq. simpl. iFrame.
      - iFrame. }
    rewrite -Hsample.
    iMod "Hclose"; iMod "Hwp"; iModIntro.
    simplify_eq.
    done.
  Qed.

  Lemma wp_presample_adv_comp (N : nat) z E e α Φ ns (ε1 : R) (ε2 : fin (S N) -> R) :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (forall n, (0 <= ε2 n)%R) ->
    SeriesC (λ n, (1 / (S N)) * ε2 n)%R = ε1 →
    α ↪ (N; ns) ∗
      ↯ ε1 ∗
      (∀ (n : fin (S N)), ↯ (ε2 n) ∗ α ↪ (N; ns ++ [n]) -∗ WP e @ E {{ Φ }})
      ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (-> Hσ_red Hε2pos Hsum) "(Hα & Hε & Hwp)".
    destruct (fin_function_bounded (S (Z.to_nat z)) ε2) as [r Hr_ub].
    assert (0 <= r)%R as Hrpos.
    {
      transitivity (ε2 0%fin); auto.
    }
    iApply wp_lift_step_fupd_glm; [done|].
    iIntros (σ1 ε_now) "[(Hheap&Htapes) Hε_supply]".
    iDestruct (ghost_map_lookup with "Htapes Hα") as %Hlookup.
    iDestruct (ec_supply_bound with "Hε_supply Hε") as %Hε1_ub.
    iMod (ec_supply_decrease with "Hε_supply Hε") as (ε1' ε_rem -> Hε1') "Hε_supply".
    iApply fupd_mask_intro; [set_solver|].
    iIntros "Hclose".
    iApply (glm_state_adv_comp' α); simpl.
    { rewrite /get_active.
      apply elem_of_list_In, elem_of_list_In, elem_of_elements, elem_of_dom.
      done. }

    (* R: predicate should hold iff tapes σ' at α is ns ++ [n] *)
    iExists
      (fun σ' : state => exists n : fin _, σ' = (state_upd_tapes <[α:=(_; ns ++ [n]) : tape]> σ1)),
      (fun ρ => (ε_rem +
                   match finite.find (fun s => state_upd_tapes <[α:=(_; ns ++ [s]) : tape]> σ1 = snd ρ) with
                   | Some s => mknonnegreal _ (Hε2pos s)
                   | None => nnreal_zero
                   end))%NNR.

    (* upper bound on ε2 *)
    iSplit.
    { iPureIntro.
      exists (ε_rem + r)%R.
      intros [e' σ'].
      apply Rplus_le_compat_l.
      destruct (finite.find _); auto; apply Hr_ub.
    }

    (* upper bound on total error *)
    iSplit.
    { iPureIntro. simpl.
      rewrite Hε1'.
      rewrite -Hsum.
      setoid_rewrite Rmult_plus_distr_l.
      rewrite SeriesC_plus.
      (* existence *)
      2: { apply ex_seriesC_scal_r, pmf_ex_seriesC. }
      2: { apply pmf_ex_seriesC_mult_fn.
           exists r; intros; split.
           - apply cond_nonneg.
           - destruct (finite.find _); [apply Hr_ub | simpl; auto ]. }

      apply Rplus_le_compat.
      { (* holds because state_step is a pmf so is lt 1 *)
        rewrite SeriesC_scal_r -{2}(Rmult_1_l (nonneg ε_rem)).
        apply Rmult_le_compat; try auto; lra. }

      (* rewrite to a form for SeriesC_le *)
      pose f := (fun n : fin _ => 1 / S (Z.to_nat z) * ε2 n)%R.
      rewrite (SeriesC_ext
                 (λ x : state, state_step σ1 α x * _)%R
                 (fun x : state => from_option f 0
                                     (finite.find (fun n => state_upd_tapes <[α:=(_; ns ++ [n]) : tape]> σ1 = x ))%R));
        last first.
      { intros n.
        destruct (finite.find _) as [sf|] eqn:HeqF.
        - Opaque INR.
          apply find_Some in HeqF.
          simpl in HeqF; rewrite -HeqF.
          rewrite /from_option /f.
          apply Rmult_eq_compat_r.
          rewrite /state_upd_tapes /=.
          rewrite /pmf /state_step.
          rewrite bool_decide_true; last first.
          { rewrite elem_of_dom Hlookup /= /is_Some; by exists (Z.to_nat z; ns). }
          rewrite (lookup_total_correct _ _ (Z.to_nat z; ns)); auto.
          rewrite /dmap /dbind /dbind_pmf /pmf.
          rewrite /= SeriesC_scal_l -{1}(Rmult_1_r (1 / _))%R.
          rewrite /Rdiv Rmult_1_l; apply Rmult_eq_compat_l.
          (* this series is 0 unless a = sf *)
          rewrite /dret /dret_pmf.
          rewrite -{2}(SeriesC_singleton sf 1%R).
          apply SeriesC_ext; intros.
          symmetry.
          case_bool_decide; simplify_eq.
          + rewrite bool_decide_true; auto.
          + rewrite bool_decide_false; auto.
            rewrite /not; intros Hcont.
            rewrite /not in H; apply H.
            rewrite /state_upd_tapes in Hcont.
            assert (R1 : ((Z.to_nat z; ns ++ [sf]) : tape) = (Z.to_nat z; ns ++ [n0])).
            { apply (insert_inv (tapes σ1) α). by inversion Hcont. }
            apply Eqdep_dec.inj_pair2_eq_dec in R1; [|apply PeanoNat.Nat.eq_dec].
            apply app_inv_head in R1.
            by inversion R1.
            Transparent INR.
        - rewrite /from_option /INR /=. lra.
      }

      apply SeriesC_le_inj.
      - (* f is nonnegative *)
        intros.
        apply Rmult_le_pos.
        + rewrite /Rdiv.
          apply Rmult_le_pos; try lra.
          apply Rlt_le, Rinv_0_lt_compat, pos_INR_S.
        + auto.
      - (* injection *)
        intros ? ? ? HF1 HF2.
        apply find_Some in HF1.
        apply find_Some in HF2.
        by rewrite -HF1 -HF2.
      - (* existence *)
        apply ex_seriesC_finite.
    }

    (* lifted lookup on tapes *)
    iSplit.
    {
      iPureIntro.
      eapply pgl_mon_pred; last first.
      - apply pgl_state. apply Hlookup.
      - done.
    }

    iIntros ((heap2 & tapes2)) "[%sample %Hsample]".

    rewrite Hsample /=.
    destruct (@find_is_Some _ _ _
                (λ s : fin (S (Z.to_nat z)), state_upd_tapes <[α:=(Z.to_nat z; ns ++ [s])]> σ1 = state_upd_tapes <[α:=(Z.to_nat z; ns ++ [sample])]> σ1)
                _ sample eq_refl)
      as [r' [Hfind Hr']].
    rewrite Hfind.
    replace r' with sample; last first.
    { rewrite /state_upd_tapes in Hr'.
      inversion Hr' as [Heqt].
      apply (insert_inv (tapes σ1) α) in Heqt.
      apply Eqdep_dec.inj_pair2_eq_dec in Heqt; [|apply PeanoNat.Nat.eq_dec].
      apply app_inv_head in Heqt.
      by inversion Heqt. }
    destruct (Rlt_decision (nonneg ε_rem + (ε2 sample))%R 1%R) as [Hdec|Hdec]; last first.
    { apply Rnot_lt_ge, Rge_le in Hdec.
      iApply exec_stutter_spend.
      iPureIntro.
      simpl ; lra.
    }
    iMod (ec_supply_increase _ (mknonnegreal _ (Hε2pos sample)) with "Hε_supply") as "[Hε_supply Hε]".
    { simplify_eq. simpl. lra. }
    iMod (ghost_map_update ((Z.to_nat z; ns ++ [sample]) : tape) with "Htapes Hα") as "[Htapes Hα]".
    iSpecialize ("Hwp" $! sample).
    rewrite pgl_wp_unfold /pgl_wp_pre.
    remember {| heap := heap2; tapes := tapes2 |} as σ2.
    rewrite /= Hσ_red /=.
    iSpecialize ("Hwp" with "[Hε Hα]"); first iFrame.
    iSpecialize ("Hwp" $! σ2 _).
    iSpecialize ("Hwp" with "[Hheap Htapes Hε_supply]").
    { iSplitL "Hheap Htapes".
      - rewrite /tapes_auth.
        rewrite Heqσ2 in Hsample. inversion Hsample.
        simplify_eq. simpl. iFrame.
      - iFrame. }
    rewrite -Hsample.
    iMod "Hclose"; iMod "Hwp"; iModIntro.
    (* replace (nonneg ε_rem + nonneg (ε2 sample))%R with (nonneg (ε_rem + ε2 sample)%NNR); [|by simpl]. *)
    iApply exec_stutter_free.
    iFrame.
  Qed.


  Lemma twp_presample_adv_comp_leq (N : nat) z E e α Φ ns (ε1 : R) (ε2 : fin (S N) -> R) :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (forall n, (0 <= ε2 n)%R) ->
    (SeriesC (λ n, (1 / (S N)) * ε2 n) <= ε1)%R →
    α ↪ (N; ns) ∗
      ↯ ε1 ∗
      (∀ (n : fin (S N)), ↯ (ε2 n) ∗ α ↪ (N; ns ++ [n]) -∗ WP e @ E [{ Φ }])
      ⊢ WP e @ E [{ Φ }].
  Proof.
    set (ε3 := SeriesC (λ n, (1 / (S N)) * ε2 n)%R).
    iIntros (-> Hσ_red Hε2pos Hsum) "(Hα & Hε & Hwp)".
    iPoseProof (ec_weaken with "Hε") as "Hε".
    { split; last apply Hsum.
      apply SeriesC_ge_0'.
      intros x.
      real_solver.
    }
    iApply twp_presample_adv_comp; eauto; iFrame.
  Qed.

  Lemma wp_presample_adv_comp_leq (N : nat) z E e α Φ ns (ε1 : R) (ε2 : fin (S N) -> R) :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (forall n, (0 <= ε2 n)%R) ->
    (SeriesC (λ n, (1 / (S N)) * ε2 n) <= ε1)%R →
    α ↪ (N; ns) ∗
      ↯ ε1 ∗
      (∀ (n : fin (S N)), ↯ (ε2 n) ∗ α ↪ (N; ns ++ [n]) -∗ WP e @ E {{ Φ }})
      ⊢ WP e @ E {{ Φ }}.
  Proof.
    set (ε3 := SeriesC (λ n, (1 / (S N)) * ε2 n)%R).
    iIntros (-> Hσ_red Hε2pos Hsum) "(Hα & Hε & Hwp)".
    iPoseProof (ec_weaken with "Hε") as "Hε".
    { split; last apply Hsum.
      apply SeriesC_ge_0'.
      intros x.
      real_solver.
    }
    iApply wp_presample_adv_comp; eauto; iFrame.
  Qed.

  Lemma twp_presample_adv_comp_leq_double (N : nat) z E e α Φ ns (ε11 ε12 : R) (ε21 ε22 : fin (S N) -> R) :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (forall n, (0 <= ε21 n)%R) ->
    (forall n, (0 <= ε22 n)%R) ->
    (SeriesC (λ n, (1 / (S N)) * ε21 n) <= ε11)%R →
    (SeriesC (λ n, (1 / (S N)) * ε22 n)%R <= ε12)%R →
    α ↪ (N; ns) ∗
      ↯ ε11 ∗ ↯ ε12 ∗
      (∀ (n : fin (S N)), ↯ (ε21 n) ∗ ↯ (ε22 n) ∗ α ↪ (N; ns ++ [n]) -∗ WP e @ E [{ Φ }])
      ⊢ WP e @ E [{ Φ }].
  Proof.
    iIntros (-> Hσ_red Hε21pos Hε22pos Hsum1 Hsum2) "(Hα & Hε11 & Hε12 & Hwp)".
    set (bigε := λ j, (ε21 j + ε22 j)%R ).
    iPoseProof (ec_combine with "[$]") as "Hε".
    iApply (twp_presample_adv_comp_leq _ _ _ _ _ _ _ _ bigε with "[$Hα $Hε Hwp]"); eauto.
    { intros n.
      rewrite /bigε.
      apply Rplus_le_le_0_compat; auto.
    }
    - rewrite /bigε.
      setoid_rewrite Rmult_plus_distr_l.
      rewrite SeriesC_plus; [ |apply ex_seriesC_finite| apply ex_seriesC_finite].
      rewrite Rplus_comm.
      apply Rplus_le_compat; auto.
    - iIntros (n) "(Hε & Hα)".
      rewrite /bigε.
      iPoseProof (ec_split with "Hε") as "(?&?)"; auto.
      iApply ("Hwp" with "[$]").
  Qed.

  Lemma wp_presample_adv_comp_leq_double (N : nat) z E e α Φ ns (ε11 ε12 : R) (ε21 ε22 : fin (S N) -> R) :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (forall n, (0 <= ε21 n)%R) ->
    (forall n, (0 <= ε22 n)%R) ->
    (SeriesC (λ n, (1 / (S N)) * ε21 n) <= ε11)%R →
    (SeriesC (λ n, (1 / (S N)) * ε22 n)%R <= ε12)%R →
    α ↪ (N; ns) ∗
      ↯ ε11 ∗ ↯ ε12 ∗
      (∀ (n : fin (S N)), ↯ (ε21 n) ∗ ↯ (ε22 n) ∗ α ↪ (N; ns ++ [n]) -∗ WP e @ E {{ Φ }})
      ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (-> Hσ_red Hε21pos Hε22pos Hsum1 Hsum2) "(Hα & Hε11 & Hε12 & Hwp)".
    set (bigε := λ j, (ε21 j + ε22 j)%R ).
    iPoseProof (ec_combine with "[$]") as "Hε".
    iApply (wp_presample_adv_comp_leq _ _ _ _ _ _ _ _ bigε with "[$Hα $Hε Hwp]"); eauto.
    { intros n.
      rewrite /bigε.
      apply Rplus_le_le_0_compat; auto.
    }
    - rewrite /bigε.
      setoid_rewrite Rmult_plus_distr_l.
      rewrite SeriesC_plus; [ |apply ex_seriesC_finite| apply ex_seriesC_finite].
      rewrite Rplus_comm.
      apply Rplus_le_compat; auto.
    - iIntros (n) "(Hε & Hα)".
      rewrite /bigε.
      iPoseProof (ec_split with "Hε") as "(?&?)"; auto.
      iApply ("Hwp" with "[$]").
  Qed.


  Lemma wp_1_err e E Φ :
    to_val e = None -> (forall σ, reducible (e, σ)) -> ↯ nnreal_one ⊢ WP e @ E {{Φ}}.
  Proof.
    iIntros (H1 H2) "He".
    iApply wp_lift_step_fupd_glm; first done.
    iIntros (σ1 ε) "[Hσ Hε]".
    iApply fupd_mask_intro; [set_solver|].
    iIntros "Hclose'".
    iDestruct (ec_supply_bound with "Hε He ") as %Hle.
    iApply glm_prim_step.
    iExists (λ _, False), nnreal_one, nnreal_zero.
    iSplitR.
    { iPureIntro. eauto. }
    iSplitR.
    { iPureIntro.
      assert (nnreal_one + nnreal_zero = nnreal_one)%R as Heq; last by rewrite Heq.
      simpl. lra.
    }
    iSplitR.
    { iPureIntro. unfold pgl. intros.
      by epose proof prob_le_1 as K.
    }
    by iIntros (? Hfalse) "%".
  Qed.

  (* FIXME: remove me *)
  Lemma twp_ec_spend e E Φ ε :
    (1 <= ε.(nonneg))%R →
    (to_val e = None) ->
    ↯ ε -∗ WP e @ E [{ Φ }].
  Proof.
    iIntros (? ?) "?".
    iExFalso.
    by iApply ec_contradict.
  Qed.

  (* FIXME: remove me *)
  Lemma wp_ec_spend e E Φ ε :
    (1 <= ε.(nonneg))%R →
    (to_val e = None) ->
    ↯ ε -∗ WP e @ E {{ Φ }}.
  Proof.
    iIntros.
    iApply tgl_wp_pgl_wp'.
    iApply twp_ec_spend; try done.
  Qed.


  Lemma amplification_depth N L (kwf : kwf N L) (ε : posreal) :
    exists n : nat, (1 <= ε * (k N L kwf) ^ n)%R.
  Proof.
    destruct kwf.
    intros.
    remember (1 + 1 / (S N ^ L - 1))%R as β.
    assert (H1 : Lim_seq.is_lim_seq (fun n => (β ^ n)%R) Rbar.p_infty).
    { eapply Lim_seq.is_lim_seq_geom_p.
      rewrite Heqβ.
      apply (Rplus_lt_reg_l (-1)%R).
      rewrite -Rplus_assoc Rplus_opp_l Rplus_0_l.
      rewrite /Rdiv Rmult_1_l.
      apply Rinv_0_lt_compat.
      apply (Rplus_lt_reg_r 1%R).
      rewrite Rplus_assoc Rplus_opp_l Rplus_0_r Rplus_0_l.
      apply Rlt_pow_R1; auto.
      apply lt_1_INR; lia.
    }
    rewrite /Lim_seq.is_lim_seq
      /Hierarchy.filterlim
      /Hierarchy.filter_le
      /Hierarchy.eventually
      /Hierarchy.filtermap
      /= in H1.
    destruct (H1 (fun r : R => (/ ε <= r)%R)); simpl.
    - exists (/ε)%R; intros; by apply Rlt_le.
    - exists x.
      apply (Rmult_le_reg_l (/ ε)%R).
      + apply Rinv_0_lt_compat, cond_pos.
      + rewrite -Rmult_assoc Rinv_l; last first.
        { pose (cond_pos ε); lra. }
        rewrite Rmult_1_l Rmult_1_r /k -Heqβ.
        by apply H.
  Qed.

  (* FIXME: relocate? *)
  Lemma lookup_ex {A} (n : nat) (L : list A) : (n < length L)%nat -> exists x, (L !! n) = Some x.
  Proof.
    intros HL.
    destruct L as [|h H]; [simpl in HL; lia|].
    generalize dependent H. generalize dependent h.
    induction n as [|n' IH].
    - intros h ? ?. exists h; by simpl.
    - intros h H HL.
      rewrite length_cons in HL. apply PeanoNat.lt_S_n in HL.
      destruct H as [|h' H']; [simpl in HL; lia|].
      replace ((h :: h' :: H') !! S n') with ((h' :: H') !! n'); last by simpl.
      by apply IH.
  Qed.


  Lemma twp_presample_amplify' N z e E α Φ (ε : posreal) L kwf prefix suffix_total (suffix_remaining : list (fin (S N))) :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    L = length suffix_total ->
    (0 < L)%nat ->
    (α ↪ (N; prefix) ∗
       (↯ (pos_to_nn ε))
       ⊢ (∀ (i : nat) (HL : (i <= L)%nat),
           (((∃ junk, α ↪ (N; prefix ++ junk) ∗ ↯(εAmp N L ε kwf)) ∨
               (α ↪ (N; prefix ++ (take i suffix_total)) ∗ ↯ (εR N L i ε (mk_fRwf N L i kwf HL))))
            -∗ WP e @ E [{ Φ }])
           -∗ WP e @ E [{ Φ }]))%I.
  Proof.
    iIntros (? ? Htotal HLpos) "(Htape & Hcr_initial)".
    iIntros (i HL).
    iInduction i as [|i'] "IH" forall (suffix_remaining).
                                      - iIntros "Hwp"; iApply "Hwp".
                                        iRight. iSplitL "Htape".
                                        + rewrite take_0. rewrite app_nil_r. iFrame.
                                        + rewrite /εR /fR /pos_to_nn /=.
                                          rewrite Rmult_1_r //.
                                      - iIntros "Hwand".
                                        assert (HL' : (i' <= L)%nat) by lia.
                                        iSpecialize ("IH" $! HL' _ with "Htape Hcr_initial").
                                        iApply "IH". iIntros "[[%junk(Htape&Hcr)]|(Htape&Hcr)]".
                                        + iApply "Hwand".
                                          iLeft; iExists junk. iFrame.
                                        + assert (Hi' : (i' < length suffix_total)%nat) by lia.
                                          destruct (lookup_ex i' suffix_total Hi') as [target Htarget].
                                          rewrite (take_S_r _ _ target); [|apply Htarget].
                                          pose HMean := (εDistr_mean N L i' ε target (mk_fRwf N L (S i') kwf HL)).
                                          wp_apply twp_presample_adv_comp; [done | | apply HMean | ].
                                          {
                                            intros i.
                                            apply cond_nonneg.
                                          }
                                          replace {| k_wf := kwf; i_ub := HL' |} with
                                            (fRwf_dec_i N L i' {| k_wf := kwf; i_ub := HL |}); [|apply fRwf_ext].
                                          iFrame.
                                          iIntros (s) "(Htape&Hcr)".
                                          iApply "Hwand".
                                          rewrite /εDistr.
                                          case_bool_decide.
                                          * iRight. simplify_eq; rewrite app_assoc; iFrame.
                                          * iLeft. iExists (take i' suffix_total ++ [s]).
                                            replace (k_wf N L (S i') {| k_wf := kwf; i_ub := HL |}) with kwf; last by apply kwf_ext.
                                            rewrite -app_assoc; iFrame.
                                            Unshelve. auto.
  Qed.

  Lemma presample_amplify' N z e E α Φ (ε : posreal) L kwf prefix suffix_total (suffix_remaining : list (fin (S N))) :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    L = length suffix_total ->
    (0 < L)%nat ->
    (α ↪ (N; prefix) ∗
       (↯ (pos_to_nn ε))
       ⊢ (∀ (i : nat) (HL : (i <= L)%nat),
           (((∃ junk, α ↪ (N; prefix ++ junk) ∗ ↯(εAmp N L ε kwf)) ∨
               (α ↪ (N; prefix ++ (take i suffix_total)) ∗ ↯ (εR N L i ε (mk_fRwf N L i kwf HL))))
            -∗ WP e @ E {{ Φ }})
           -∗ WP e @ E {{ Φ }}))%I.
  Proof.
    iIntros (? ? Htotal HLpos) "(Htape & Hcr_initial)".
    iIntros (i HL).
    iInduction i as [|i'] "IH" forall (suffix_remaining).
                                      - iIntros "Hwp"; iApply "Hwp".
                                        iRight. iSplitL "Htape".
                                        + rewrite take_0 app_nil_r. iFrame.
                                        + rewrite /εR /fR /pos_to_nn /=.
                                          rewrite Rmult_1_r //.
                                      - iIntros "Hwand".
                                        assert (HL' : (i' <= L)%nat) by lia.
                                        iSpecialize ("IH" $! HL' _ with "Htape Hcr_initial").
                                        iApply "IH". iIntros "[[%junk(Htape&Hcr)]|(Htape&Hcr)]".
                                        + iApply "Hwand".
                                          iLeft; iExists junk. iFrame.
                                        + assert (Hi' : (i' < length suffix_total)%nat) by lia.
                                          destruct (lookup_ex i' suffix_total Hi') as [target Htarget].
                                          rewrite (take_S_r _ _ target); [|apply Htarget].
                                          pose HMean := (εDistr_mean N L i' ε target (mk_fRwf N L (S i') kwf HL)).
                                          wp_apply wp_presample_adv_comp; [done | | apply HMean | ].
                                          {
                                            intros; apply cond_nonneg.
                                          }
                                          replace {| k_wf := kwf; i_ub := HL' |} with
                                            (fRwf_dec_i N L i' {| k_wf := kwf; i_ub := HL |}); [|apply fRwf_ext].
                                          iFrame.
                                          iIntros (s) "(Htape&Hcr)".
                                          iApply "Hwand".
                                          rewrite /εDistr.
                                          case_bool_decide.
                                          * iRight. simplify_eq; rewrite app_assoc; iFrame.
                                          * iLeft. iExists (take i' suffix_total ++ [s]).
                                            replace (k_wf N L (S i') {| k_wf := kwf; i_ub := HL |}) with kwf; last by apply kwf_ext.
                                            rewrite -app_assoc; iFrame.
                                            Unshelve. auto.
  Qed.

  (* do one step in the amplification sequence *)
  Lemma twp_presample_amplify N z e E α Φ (ε : posreal) L (kwf: kwf N L) prefix suffix :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    L = (length suffix) ->
    ↯ (pos_to_nn ε) ∗
      (α ↪ (N; prefix)) ∗
      ((α ↪ (N; prefix ++ suffix) ∨ (∃ junk, α ↪ (N; prefix ++ junk) ∗ ↯(εAmp N L ε kwf))) -∗ WP e @ E [{ Φ }])
      ⊢ WP e @ E [{ Φ }].
  Proof.
    iIntros (? ? Hl) "(Hcr & Htape & Hwp)".
    destruct suffix as [|s0 sr].
    - iApply "Hwp". iLeft. rewrite app_nil_r. iFrame.
    - remember (s0 :: sr) as suffix.
      assert (Hl_pos : (0 < L)%nat).
      { rewrite Hl Heqsuffix length_cons. lia. }
      iApply (twp_presample_amplify' with "[Htape Hcr]"); eauto; [iFrame|].
      iIntros "[H|(H&_)]"; iApply "Hwp".
      + iRight. by iFrame.
      + iLeft. erewrite firstn_all; iFrame.
        Unshelve. lia.
  Qed.

  (* do one step in the amplification sequence *)
  Lemma wp_presample_amplify N z e E α Φ (ε : posreal) L (kwf: kwf N L) prefix suffix :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    L = (length suffix) ->
    ↯ (pos_to_nn ε) ∗
      (α ↪ (N; prefix)) ∗
      ((α ↪ (N; prefix ++ suffix) ∨ (∃ junk, α ↪ (N; prefix ++ junk) ∗ ↯(εAmp N L ε kwf))) -∗ WP e @ E {{ Φ }})
      ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (? ? Hl) "(Hcr & Htape & Hwp)".
    destruct suffix as [|s0 sr].
    - iApply "Hwp". iLeft. rewrite app_nil_r. iFrame.
    - remember (s0 :: sr) as suffix'.
      assert (Hl_pos : (0 < L)%nat).
      { rewrite Hl Heqsuffix' length_cons. lia. }
      iApply (presample_amplify' with "[Htape Hcr]"); eauto; [iFrame|].
      iIntros "[H|(H&_)]"; iApply "Hwp".
      + iRight. by iFrame.
      + iLeft. erewrite firstn_all; iFrame.
        Unshelve. lia.
  Qed.

  Lemma twp_seq_amplify N z e E α Φ (ε : posreal) L (kwf: kwf N L) prefix suffix d :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (forall junk, 0 < (length (suffix (prefix ++ junk))) <= L)%nat ->
    ↯ (pos_to_nn ε) ∗
      (α ↪ (N; prefix)) ∗
      ((∃ junk, α ↪ (N; prefix ++ junk ++ (suffix (prefix ++ junk))) ∨ α ↪ (N; prefix ++ junk) ∗ ↯(pos_to_nn (εAmp_iter N L d ε kwf)))
       -∗ WP e @ E [{ Φ }])
      ⊢ WP e @ E [{ Φ }].
  Proof.
    iIntros (? ? HL) "(Hcr&Htape&Hwp)".
    iInduction (d) as [|d'] "IH".
    - iApply "Hwp".
      iExists []; rewrite app_nil_r. iRight. iFrame.
      rewrite /εAmp_iter /pos_to_nn /= Rmult_1_r //.
    - iApply ("IH" with "Hcr Htape").
      iIntros "[%junk [Hlucky|(Htape&Hcr)]]".
      + iApply "Hwp". iExists junk; iLeft; iFrame.
      + pose L' := (length (suffix (prefix ++ junk))).
        iApply (twp_presample_amplify _ _ _ _ _ _ _ L'); eauto; iFrame.
        iIntros "[?|[%junk' (Htape&Hcr)]]"; iApply "Hwp".
        * iExists _; iLeft.
          rewrite -app_assoc; iFrame.
        * iExists _; iRight.
          rewrite -app_assoc -εAmp_iter_cmp; iFrame.
          iApply (ec_weaken with "Hcr").
          rewrite /εAmp /=.
          split.
          { apply Rmult_le_pos.
            - apply Rmult_le_pos; [apply Rlt_le, cond_pos | apply pow_le, Rlt_le, k_pos].
            - apply Rlt_le, k_pos. }
          apply Rmult_le_compat_l.
          { apply Rmult_le_pos; [apply Rlt_le, cond_pos | apply pow_le, Rlt_le, k_pos]. }
          apply Rplus_le_compat_l.
          rewrite /Rdiv Rmult_1_l Rmult_1_l.
          apply Rinv_le_contravar.
          -- apply (Rplus_lt_reg_r 1%R).
             rewrite /Rminus Rplus_assoc Rplus_opp_l Rplus_0_l Rplus_0_r.
             apply Rlt_pow_R1.
             --- apply lt_1_INR; destruct kwf; lia.
             --- rewrite /L'. by destruct (HL junk).
          -- apply Rplus_le_compat_r, Rle_pow.
             --- rewrite S_INR. pose P := (pos_INR N); lra.
             --- rewrite /L'. by destruct (HL junk).
                 Unshelve.
                 destruct kwf.
                 destruct (HL junk).
                 rewrite /L'.
                 constructor; try lia.
  Qed.

  Lemma seq_amplify N z e E α Φ (ε : posreal) L (kwf: kwf N L) prefix suffix d :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (forall junk, 0 < (length (suffix (prefix ++ junk))) <= L)%nat ->
    ↯ (pos_to_nn ε) ∗
      (α ↪ (N; prefix)) ∗
      ((∃ junk, α ↪ (N; prefix ++ junk ++ (suffix (prefix ++ junk))) ∨ α ↪ (N; prefix ++ junk) ∗ ↯(pos_to_nn (εAmp_iter N L d ε kwf)))
       -∗ WP e @ E {{ Φ }})
      ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (? ? HL) "(Hcr&Htape&Hwp)".
    iInduction (d) as [|d'] "IH".
    - iApply "Hwp".
      iExists []; rewrite app_nil_r. iRight. iFrame.
      iApply ec_eq; last auto.
      by rewrite /εAmp_iter /pos_to_nn /= Rmult_1_r.
    - iApply ("IH" with "Hcr Htape").
      iIntros "[%junk [Hlucky|(Htape&Hcr)]]".
      + iApply "Hwp". iExists junk; iLeft; iFrame.
      + pose L' := (length (suffix (prefix ++ junk))).
        iApply (wp_presample_amplify _ _ _ _ _ _ _ L'); eauto; iFrame.
        iIntros "[?|[%junk' (Htape&Hcr)]]"; iApply "Hwp".
        * iExists _; iLeft.
          rewrite -app_assoc; iFrame.
        * iExists _; iRight.
          rewrite -app_assoc -εAmp_iter_cmp; iFrame.
          iApply (ec_weaken with "Hcr").
          split.
          { apply Rmult_le_pos.
            - apply Rmult_le_pos; [apply Rlt_le, cond_pos | apply pow_le, Rlt_le, k_pos].
            - apply Rlt_le, k_pos. }
          rewrite /εAmp /=.
          apply Rmult_le_compat_l.
          { apply Rmult_le_pos; [apply Rlt_le, cond_pos | apply pow_le, Rlt_le, k_pos]. }
          apply Rplus_le_compat_l.
          rewrite /Rdiv Rmult_1_l Rmult_1_l.
          apply Rinv_le_contravar.
          -- apply (Rplus_lt_reg_r 1%R).
             rewrite /Rminus Rplus_assoc Rplus_opp_l Rplus_0_l Rplus_0_r.
             apply Rlt_pow_R1.
             --- apply lt_1_INR; destruct kwf; lia.
             --- rewrite /L'. by destruct (HL junk).
          -- apply Rplus_le_compat_r, Rle_pow.
             --- rewrite S_INR. pose P := (pos_INR N); lra.
             --- rewrite /L'. by destruct (HL junk).
                 Unshelve.
                 destruct kwf.
                 destruct (HL junk).
                 rewrite /L'.
                 constructor; try lia.
  Qed.

  Lemma twp_presample_planner_pos N z e E α Φ (ε : nonnegreal) L prefix suffix :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (0 < N)%nat ->
    (forall junk, 0 < (length (suffix (prefix ++ junk))) <= L)%nat ->
    (0 < ε)%R ->
    ↯ ε ∗
      (α ↪ (N; prefix)) ∗
      ((∃ junk, α ↪ (N; prefix ++ junk ++ (suffix (prefix ++ junk)))) -∗ WP e @ E [{ Φ }])
      ⊢ WP e @ E [{ Φ }].
  Proof.
    iIntros (? ? ? ? Hε) "(Hcr & Htape & Hwp)".
    assert (kwf : kwf N L). {
      apply mk_kwf; try lia.
      destruct (H2 []) as [H2' H2''].
      eapply Nat.lt_le_trans; eauto. }
    pose ε' := mkposreal ε.(nonneg) Hε.
    replace ε with (pos_to_nn ε'); last first.
    { rewrite /ε' /pos_to_nn. by apply nnreal_ext. }
    destruct (amplification_depth N L kwf ε') as [d Hdepth].
    iApply twp_seq_amplify; eauto; iFrame.
    iIntros "[%junk [?|(_&Hcr)]]".
    + iApply "Hwp"; iExists _; iFrame.
    + iApply (twp_ec_spend with "Hcr"); auto.
      rewrite /pos_to_nn /εAmp_iter /=.
      replace (nonneg ε) with (pos ε') by auto.
      done.
  Qed.

  Lemma presample_planner_pos N z e E α Φ (ε : nonnegreal) L prefix suffix :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (0 < N)%nat ->
    (forall junk, 0 < (length (suffix (prefix ++ junk))) <= L)%nat ->
    (0 < ε)%R ->
    ↯ ε ∗
      (α ↪ (N; prefix)) ∗
      ((∃ junk, α ↪ (N; prefix ++ junk ++ (suffix (prefix ++ junk)))) -∗ WP e @ E {{ Φ }})
      ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (? ? ? ? Hε) "(Hcr & Htape & Hwp)".
    assert (kwf : kwf N L). {
      apply mk_kwf; try lia.
      destruct (H2 []) as [H2' H2''].
      eapply Nat.lt_le_trans; eauto. }
    pose ε' := mkposreal ε.(nonneg) Hε.
    replace ε with (pos_to_nn ε'); last first.
    { rewrite /ε' /pos_to_nn. by apply nnreal_ext. }
    destruct (amplification_depth N L kwf ε') as [d Hdepth].
    iApply seq_amplify; eauto; iFrame.
    iIntros "[%junk [?|(_&Hcr)]]".
    + iApply "Hwp"; iExists _; iFrame.
    + iApply (wp_ec_spend with "Hcr"); auto.
      rewrite /pos_to_nn /εAmp_iter /=.
      replace (nonneg ε) with (pos ε') by auto.
      done.
  Qed.

  (* general planner rule, with bounded synchronization strings *)
  Lemma twp_presample_planner_sync N z e E α Φ (ε : nonnegreal) L prefix suffix :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (0 < ε)%R ->
    (forall junk, 0 < (length (suffix (prefix ++ junk))) <= L)%nat ->
    ↯ ε ∗
      (α ↪ (S N; prefix)) ∗
      ((∃ junk, α ↪ (S N; prefix ++ junk ++ suffix (prefix ++ junk))) -∗ WP e @ E [{ Φ }])
      ⊢ WP e @ E [{ Φ }].
  Proof.
    iIntros (? ? ? ?).
    destruct (suffix prefix) as [|h R] eqn:Hsp.
    - iIntros "(_ & Htape & Hwp)".
      iApply "Hwp".
      iExists [].
      rewrite app_nil_r app_assoc app_nil_r Hsp app_nil_r.
      iFrame.
    - iApply (twp_presample_planner_pos); eauto; try lia.
      by erewrite Nat2Z.id.
  Qed.

  (* general planner rule, with bounded synchronization strings *)
  Lemma presample_planner_sync N z e E α Φ (ε : nonnegreal) L prefix suffix :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (0 < ε)%R ->
    (forall junk, 0 < (length (suffix (prefix ++ junk))) <= L)%nat ->
    ↯ ε ∗
      (α ↪ (S N; prefix)) ∗
      ((∃ junk, α ↪ (S N; prefix ++ junk ++ suffix (prefix ++ junk))) -∗ WP e @ E {{ Φ }})
      ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (? ? ? ?).
    destruct (suffix prefix) as [|h R] eqn:Hsp.
    - iIntros "(_ & Htape & Hwp)".
      iApply "Hwp".
      iExists [].
      rewrite app_nil_r app_assoc app_nil_r Hsp app_nil_r.
      iFrame.
    - iApply (presample_planner_pos); eauto; try lia.
      by erewrite Nat2Z.id.
  Qed.


  (* classic version *)
  Lemma twp_presample_planner N z e E α Φ (ε : nonnegreal) prefix suffix :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (0 < ε)%R ->
    ↯ ε ∗
      (α ↪ (S N; prefix)) ∗
      ((∃ junk, α ↪ (S N; prefix ++ junk ++ suffix)) -∗ WP e @ E [{ Φ }])
      ⊢ WP e @ E [{ Φ }].
  Proof.
    iIntros (? ? ?) "(Hcr&Htape&Hwp)".
    destruct suffix as [|] eqn:HS.
    - iApply "Hwp".
      iExists [].
      do 2 rewrite app_nil_r; iFrame.
    - iApply (twp_presample_planner_sync _ _ _ _ _ _ _ (length suffix) _ (fun _ => suffix)); eauto.
      + intros; rewrite HS /=. lia.
      + rewrite HS. iFrame.
  Qed.

  Lemma presample_planner N z e E α Φ (ε : nonnegreal) prefix suffix :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (0 < ε)%R ->
    ↯ ε ∗
      (α ↪ (S N; prefix)) ∗
      ((∃ junk, α ↪ (S N; prefix ++ junk ++ suffix)) -∗ WP e @ E {{ Φ }})
      ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (? ? ?) "(Hcr&Htape&Hwp)".
    destruct suffix as [|] eqn:HS.
    - iApply "Hwp".
      iExists [].
      do 2 rewrite app_nil_r; iFrame.
    - iApply (presample_planner_sync _ _ _ _ _ _ _ (length suffix) _ (fun _ => suffix)); eauto.
      + intros; rewrite HS /=. lia.
      + rewrite HS. iFrame.
  Qed.

  (* pads the junk up to a multiple of blocksize *)
  Definition block_pad N blocksize : list (fin (S (S N))) -> list (fin (S (S N))) :=
    fun junk => repeat 0%fin ((blocksize - (length junk mod blocksize)) mod blocksize)%nat.

  Lemma blocks_aligned N blocksize : (0 < blocksize) -> forall junk, (length junk + length (block_pad N blocksize junk)) mod blocksize = 0%nat.
  Proof.
    intros Hblocksize junk.
    rewrite /block_pad.
    rewrite repeat_length.
    rewrite -Nat.Div0.add_mod_idemp_l.
    rewrite -Nat.Div0.add_mod.
    rewrite -Nat.Div0.add_mod_idemp_l.
    rewrite -Nat.le_add_sub; [apply Nat.Div0.mod_same|].
    apply Nat.lt_le_incl.
    apply Nat.mod_bound_pos; [apply Nat.le_0_l | done].
  Qed.

  Lemma block_pad_ub N blocksize : (0 < blocksize) -> forall junk, (length (block_pad N blocksize junk) <= blocksize)%nat.
  Proof.
    intros. rewrite /block_pad repeat_length.
    edestruct Nat.mod_bound_pos; last first.
    - eapply Nat.lt_le_incl, H1.
    - lia.
    - lia.
  Qed.

  (* version where junk is a mipltple of sample length *)
  Lemma twp_presample_planner_aligned N z e E α Φ (ε : nonnegreal) prefix suffix :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (0 < ε)%R ->
    ↯ ε ∗
      (α ↪ (S N; prefix)) ∗
      ((∃ junk, α ↪ (S N; prefix ++ junk ++ (block_pad N (length suffix) (prefix ++ junk)) ++ suffix)) -∗ WP e @ E [{ Φ }])
      ⊢ WP e @ E [{ Φ }].
  Proof.
    iIntros (? ? ?) "(Hcr&Htape&Hwp)".
    destruct suffix as [|] eqn:HS.
    - iApply "Hwp".
      iExists [].
      do 2 rewrite app_nil_r; iFrame.
    - iApply (twp_presample_planner_sync _ _ _ _ _ _ _ (length suffix + length suffix) _ (fun samples => block_pad N (length suffix) samples ++ suffix)); eauto.
      + intros. split.
        * rewrite length_app HS /=. lia.
        * rewrite length_app /=.
          apply Nat.add_le_mono_r, block_pad_ub.
          rewrite HS /=. lia.
      + rewrite HS.
        iFrame.
  Qed.

  Lemma presample_planner_aligned N z e E α Φ (ε : nonnegreal) prefix suffix :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (0 < ε)%R ->
    ↯ ε ∗
      (α ↪ (S N; prefix)) ∗
      ((∃ junk, α ↪ (S N; prefix ++ junk ++ (block_pad N (length suffix) (prefix ++ junk)) ++ suffix)) -∗ WP e @ E {{ Φ }})
      ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (? ? ?) "(Hcr&Htape&Hwp)".
    destruct suffix as [|] eqn:HS.
    - iApply "Hwp".
      iExists [].
      do 2 rewrite app_nil_r; iFrame.
    - iApply (presample_planner_sync _ _ _ _ _ _ _ (length suffix + length suffix) _ (fun samples => block_pad N (length suffix) samples ++ suffix)); eauto.
      + intros. split.
        * rewrite length_app HS /=. lia.
        * rewrite length_app /=.
          apply Nat.add_le_mono_r, block_pad_ub.
          rewrite HS /=. lia.
      + rewrite HS.
        iFrame.
  Qed.


  Lemma twp_presample_amplify_variant_aux N z e E α Φ Ψ (ε : posreal) li (U : list (fin (S N)) -> nat) (L : nat) kwf :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (forall l : list (fin (S N)), U(l) <= L)%R ->
    (forall l : list (fin (S N)), Ψ l <-> U(l) = 0) ->
    (forall l : list (fin (S N)), ¬ Ψ l ->
      exists c : (fin (S N)), (U(l++[c]) < U(l))%R)  ->
    (0 < U li) ->
    (α ↪ (N; li) ∗
       (↯ (pos_to_nn ε))
       ⊢ (∀ (i : nat) (HL : (i <= L)%nat),
           (((∃ lf1, α ↪ (N; lf1) ∗ ↯(εAmp N L ε kwf)) ∨
               (∃ lf2, α ↪ (N; lf2) ∗  ⌜ U(lf2) + i <= L ⌝ ∗ ↯ (εR N L i ε (mk_fRwf N L i kwf HL))))
            -∗ WP e @ E [{ Φ }])
           -∗ WP e @ E [{ Φ }]))%I.
  Proof.
    iIntros (? ? HUL HU0 HUdec HUli) "(Htape & Hcr_initial)".
    iIntros (i HL).
    iInduction i as [|i'] "IH".
        - iIntros "Hwp".
          iApply "Hwp".
          iRight.
          iExists li.
          iFrame.
          iSplit.
          { iPureIntro.
            rewrite Nat.add_0_r.
            by apply INR_le.
          }
          iFrame.
          rewrite /εR /fR /pos_to_nn /=.
          rewrite Rmult_1_r //.
        - iIntros "Hwand".
          assert (HL' : (i' <= L)%nat) by lia.
          iSpecialize ("IH" $! HL' with "Htape Hcr_initial").
          iApply "IH".
          iIntros  "[[%lf1 [Htape Hcr]]|[%lf2 [Htape (%HUi' & Hcr)]]]".
          + iApply "Hwand".
            iLeft; iExists lf1; iFrame.
          + assert (Hi' : (i' < L)%nat) by lia.
            assert (0 = U lf2 \/ 0 < U lf2)%nat as [HUlf2 | HUlf2 ]by lia.
            * iApply "Hwand".
              iRight.
              iExists lf2.
              iFrame.
              iSplit.
              {
                iPureIntro.
                lia.
              }
              iApply ec_weaken; last by iFrame.
              split; [apply cond_nonneg |].
              rewrite /εR.
              apply Rmult_le_compat_l; [left; apply cond_pos |].
              apply fR_mon_dec.

           * assert (¬ Ψ lf2) as HnΨlf2.
             {
               intros HΨlf2.
               specialize (HU0 lf2) as [HU0 ?].
               specialize (HU0 HΨlf2).
               lia.
             }
             destruct (HUdec lf2 HnΨlf2) as [target Htarget].
             pose HMean := (εDistr_mean N L i' ε target (mk_fRwf N L (S i') kwf HL)).
             wp_apply twp_presample_adv_comp; [done | | apply HMean | ].
             {
               intros; apply cond_nonneg.
             }
             replace {| k_wf := kwf; i_ub := HL' |} with
               (fRwf_dec_i N L i' {| k_wf := kwf; i_ub := HL |}); [|apply fRwf_ext].
             iFrame.
             iIntros (s) "(Hcr&Htape)".
             iApply "Hwand".
             rewrite /εDistr.
             case_bool_decide.
             ** iRight. iFrame. simplify_eq.
                iPureIntro.
                apply INR_lt in Htarget.
                lia.
             ** iLeft. iFrame.
  Qed.

  Lemma presample_amplify_variant_aux N z e E α Φ Ψ (ε : posreal) li (U : list (fin (S N)) -> nat) (L : nat) kwf :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (forall l : list (fin (S N)), U(l) <= L)%R ->
    (forall l : list (fin (S N)), Ψ l <-> U(l) = 0) ->
    (forall l : list (fin (S N)), ¬ Ψ l ->
      exists c : (fin (S N)), (U(l++[c]) < U(l))%R)  ->
    (0 < U li) ->
    (α ↪ (N; li) ∗
       (↯ (pos_to_nn ε))
       ⊢ (∀ (i : nat) (HL : (i <= L)%nat),
           (((∃ lf1, α ↪ (N; lf1) ∗ ↯(εAmp N L ε kwf)) ∨
               (∃ lf2, α ↪ (N; lf2) ∗  ⌜ U(lf2) + i <= L ⌝ ∗ ↯ (εR N L i ε (mk_fRwf N L i kwf HL))))
            -∗ WP e @ E {{ Φ }})
           -∗ WP e @ E {{ Φ }}))%I.
  Proof.
    iIntros (? ? HUL HU0 HUdec HUli) "(Htape & Hcr_initial)".
    iIntros (i HL).
    iInduction i as [|i'] "IH".
        - iIntros "Hwp".
          iApply "Hwp".
          iRight.
          iExists li.
          iFrame.
          iSplit.
          { iPureIntro.
            rewrite Nat.add_0_r.
            by apply INR_le.
          }
          iFrame.
          rewrite /εR /fR /pos_to_nn /=.
          rewrite Rmult_1_r //.
        - iIntros "Hwand".
          assert (HL' : (i' <= L)%nat) by lia.
          iSpecialize ("IH" $! HL' with "Htape Hcr_initial").
          iApply "IH".
          iIntros  "[[%lf1 [Htape Hcr]]|[%lf2 [Htape (%HUi' & Hcr)]]]".
          + iApply "Hwand".
            iLeft; iExists lf1; iFrame.
          + assert (Hi' : (i' < L)%nat) by lia.
            assert (0 = U lf2 \/ 0 < U lf2)%nat as [HUlf2 | HUlf2 ]by lia.
            * iApply "Hwand".
              iRight.
              iExists lf2.
              iFrame.
              iSplit.
              {
                iPureIntro.
                lia.
              }
              iApply ec_weaken; last by iFrame.
              split; [apply cond_nonneg |].
              rewrite /εR.
              apply Rmult_le_compat_l; [left; apply cond_pos |].
              apply fR_mon_dec.

           * assert (¬ Ψ lf2) as HnΨlf2.
             {
               intros HΨlf2.
               specialize (HU0 lf2) as [HU0 ?].
               specialize (HU0 HΨlf2).
               lia.
             }
             destruct (HUdec lf2 HnΨlf2) as [target Htarget].
             pose HMean := (εDistr_mean N L i' ε target (mk_fRwf N L (S i') kwf HL)).
             wp_apply wp_presample_adv_comp; [done | | apply HMean | ].
             {
               intros; apply cond_nonneg.
             }
             replace {| k_wf := kwf; i_ub := HL' |} with
               (fRwf_dec_i N L i' {| k_wf := kwf; i_ub := HL |}); [|apply fRwf_ext].
             iFrame.
             iIntros (s) "(Hcr&Htape)".
             iApply "Hwand".
             rewrite /εDistr.
             case_bool_decide.
             ** iRight. iFrame. simplify_eq.
                iPureIntro.
                apply INR_lt in Htarget.
                lia.
             ** iLeft. iFrame.
  Qed.


  (* do one step in the amplification sequence *)
  Lemma twp_presample_amplify_variant N z e E α Φ Ψ (ε : posreal) li (U : list (fin (S N)) -> nat) L (kwf: kwf N L) :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (forall l : list (fin (S N)), U(l) <= L)%R ->
    (forall l : list (fin (S N)), Ψ l <-> U(l) = 0) ->
    (forall l : list (fin (S N)), ¬ Ψ l ->
      exists c : (fin (S N)), (U(l++[c]) < U(l))%R)  ->
    ↯ (pos_to_nn ε) ∗
      (α ↪ (N; li)) ∗
      (((∃ lf, ⌜ Ψ lf ⌝ ∗ α ↪ (N; lf)) ∨ (∃ junk, α ↪ (N; junk) ∗ ↯(εAmp N L ε kwf))) -∗ WP e @ E [{ Φ }])
      ⊢ WP e @ E [{ Φ }].
  Proof.
    iIntros (? ? HUL HU0 HUdec) "(Hcr & Htape & Hwp)".
    destruct (U li) as [|u] eqn:Hu.
    - iApply "Hwp".
      iLeft.
      iExists li.
      iFrame.
      iPureIntro.
      destruct (decide (Ψ li)) as [?|HnΨli]; auto.
      specialize (HUdec li HnΨli) as [c Hc].
      apply INR_lt in Hc.
      lia.
    - assert (0 < U li) by lia.
      iApply (twp_presample_amplify_variant_aux with "[Htape Hcr]"); eauto; [iFrame|].
      iIntros  "[[%lf1 [Htape Hcr]]|[%lf2 [Htape (%HUlf2 & Hcr)]]]"; iApply "Hwp".
      + iRight. by iFrame.
      + iLeft. iFrame.
        Unshelve.
        2: exact L.
        2: lia.
        iPureIntro.
        apply HU0.
        lia.
  Qed.


  (* do one step in the amplification sequence *)
  Lemma wp_presample_amplify_variant N z e E α Φ Ψ (ε : posreal) li (U : list (fin (S N)) -> nat) L (kwf: kwf N L) :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (forall l : list (fin (S N)), U(l) <= L)%R ->
    (forall l : list (fin (S N)), Ψ l <-> U(l) = 0) ->
    (forall l : list (fin (S N)), ¬ Ψ l ->
      exists c : (fin (S N)), (U(l++[c]) < U(l))%R)  ->
    ↯ (pos_to_nn ε) ∗
      (α ↪ (N; li)) ∗
      (((∃ lf, ⌜ Ψ lf ⌝ ∗ α ↪ (N; lf)) ∨ (∃ junk, α ↪ (N; junk) ∗ ↯(εAmp N L ε kwf))) -∗ WP e @ E {{ Φ }})
      ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (? ? HUL HU0 HUdec) "(Hcr & Htape & Hwp)".
    destruct (U li) as [|u] eqn:Hu.
    - iApply "Hwp".
      iLeft.
      iExists li.
      iFrame.
      iPureIntro.
      destruct (decide (Ψ li)) as [?|HnΨli]; auto.
      specialize (HUdec li HnΨli) as [c Hc].
      apply INR_lt in Hc.
      lia.
    - assert (0 < U li) by lia.
      iApply (presample_amplify_variant_aux with "[Htape Hcr]"); eauto; [iFrame|].
      iIntros  "[[%lf1 [Htape Hcr]]|[%lf2 [Htape (%HUlf2 & Hcr)]]]"; iApply "Hwp".
      + iRight. by iFrame.
      + iLeft. iFrame.
        Unshelve.
        2: exact L.
        2: lia.
        iPureIntro.
        apply HU0.
        lia.
  Qed.


  Lemma twp_presample_variant N z e E α Φ Ψ (ε : nonnegreal) li (U : list (fin (S N)) -> nat) (M : nat) :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (0 < ε)%R ->
    (forall l : list (fin (S N)), U(l) <= M)%R ->
    (forall l : list (fin (S N)), Ψ l <-> U(l) = 0) ->
    (forall l : list (fin (S N)), ¬ Ψ l ->
                             exists c : (fin (S N)), (U(l++[c]) < U(l))%R)  ->
    ↯ (ε) ∗
      (α ↪ (N; li)) ∗
      (∀ lf, ⌜ Ψ lf ⌝ ∗ α ↪ (N; lf) -∗ WP e @ E [{ Φ }])
      ⊢ WP e @ E [{ Φ }].
  Proof.
    iIntros (? ? Hε HUL HU0 HUdec) "(Hcr & Htape & Hwp)".
    assert (N = 0 \/ 0 < N) as [-> | HN] by lia.
    (* Corner case: N = 0 *)
    {
      assert (exists n, U li <= n) as [n Hn].
      {
        exists M.
        by apply INR_le.
      }
      iInduction (n) as [|?] "IH" forall (li Hn).
      - iApply "Hwp".
        iFrame.
        iPureIntro.
        apply HU0.
        lia.
      - destruct (decide (U li = 0)) as [HUli0 | HUlin0].
        + iApply "Hwp".
          iFrame.
          iPureIntro.
          by apply HU0.
        + assert (¬ Ψ li) as HnΨ.
          {
            intros HΨ.
            apply HUlin0.
            by apply HU0.
          }
          iApply twp_presample; auto; iFrame.
          iIntros (n0) "Hα".
          destruct (HUdec _ HnΨ) as [c Hc].
          assert (n0 = 0%fin) as ->.
          {
            inv_fin n0; auto.
            intros i.
            inv_fin i.
          }
          assert (c = 0%fin) as ->.
          {
            inv_fin c; auto.
            intros i ?.
            inv_fin i.
          }
          iApply ("IH" with "[][$][$]").
          * iPureIntro.
            apply INR_lt in Hc.
            lia.
          * iIntros (lf) "(%Hlf & Hα)".
            iApply "Hwp"; iFrame; done.
    }
    assert (M = 0 \/ 0 < M) as [-> | HL] by lia.
    (* Corner case: M = 0 *)
    {
      iApply "Hwp"; iFrame.
      iPureIntro.
      apply HU0.
      specialize (HUL li).
      apply INR_le in HUL.
      lia.
    }
    pose kwf := mk_kwf _ _ HN HL.
    pose ε' := mkposreal ε.(nonneg) Hε.
    replace ε with (pos_to_nn ε'); last first.
    { rewrite /ε' /pos_to_nn. by apply nnreal_ext. }
    iRevert (li) "Htape Hwp".
    iApply (ec_ind_incr _ ((εAmp N M ε' _)) with "[] Hcr").
    - apply cond_pos.
    - rewrite /εAmp /=.
      rewrite -{1}(Rmult_1_r (nonneg ε)).
      apply Rmult_lt_compat_l; [real_solver|].
      apply lt_1_k.
    - iModIntro.
      iIntros "[Hind Herr]".
      iIntros (li) "Hα Hcont".
      iApply twp_presample_amplify_variant; eauto.
      iFrame.
      iIntros  "[[%lf1 [HΨ Htape]]|[%lf2 [Htape Hcr]]]".
      + iApply "Hcont".
        iFrame.
      + iApply ("Hind" with "[Hcr] [$Htape]").
        * iFrame.
        * iIntros (?) "(?&?)".
          iApply ("Hcont" with "[$]").
     Unshelve. auto.
  Qed.

  Lemma presample_variant N z e E α Φ Ψ (ε : nonnegreal) li (U : list (fin (S N)) -> nat) (M : nat) :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (0 < ε)%R ->
    (forall l : list (fin (S N)), U(l) <= M)%R ->
    (forall l : list (fin (S N)), Ψ l <-> U(l) = 0) ->
    (forall l : list (fin (S N)), ¬ Ψ l ->
                             exists c : (fin (S N)), (U(l++[c]) < U(l))%R)  ->
    ↯ (ε) ∗
      (α ↪ (N; li)) ∗
      (∀ lf, ⌜ Ψ lf ⌝ ∗ α ↪ (N; lf) -∗ WP e @ E {{ Φ }})
      ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (? ? Hε HUL HU0 HUdec) "(Hcr & Htape & Hwp)".
    assert (N = 0 \/ 0 < N) as [-> | HN] by lia.
    (* Corner case: N = 0 *)
    {
      assert (exists n, U li <= n) as [n Hn].
      {
        exists M.
        by apply INR_le.
      }
      iInduction (n) as [|?] "IH" forall (li Hn).
      - iApply "Hwp".
        iFrame.
        iPureIntro.
        apply HU0.
        lia.
      - destruct (decide (U li = 0)) as [HUli0 | HUlin0].
        + iApply "Hwp".
          iFrame.
          iPureIntro.
          by apply HU0.
        + assert (¬ Ψ li) as HnΨ.
          {
            intros HΨ.
            apply HUlin0.
            by apply HU0.
          }
          iApply wp_presample; auto; iFrame.
          iIntros (n0) "Hα".
          destruct (HUdec _ HnΨ) as [c Hc].
          assert (n0 = 0%fin) as ->.
          {
            inv_fin n0; auto.
            intros i.
            inv_fin i.
          }
          assert (c = 0%fin) as ->.
          {
            inv_fin c; auto.
            intros i ?.
            inv_fin i.
          }
          iApply ("IH" with "[][$][$]").
          * iPureIntro.
            apply INR_lt in Hc.
            lia.
          * iIntros (lf) "(%Hlf & Hα)".
            iApply "Hwp"; iFrame; done.
    }
    assert (M = 0 \/ 0 < M) as [-> | HL] by lia.
    (* Corner case: M = 0 *)
    {
      iApply "Hwp"; iFrame.
      iPureIntro.
      apply HU0.
      specialize (HUL li).
      apply INR_le in HUL.
      lia.
    }
    pose kwf := mk_kwf _ _ HN HL.
    pose ε' := mkposreal ε.(nonneg) Hε.
    replace ε with (pos_to_nn ε'); last first.
    { rewrite /ε' /pos_to_nn. by apply nnreal_ext. }
    iRevert (li) "Htape Hwp".
    iApply (ec_ind_incr _ ((εAmp N M ε' _)) with "[] Hcr").
    - apply cond_pos.
    - rewrite /εAmp /=.
      rewrite -{1}(Rmult_1_r (nonneg ε)).
      apply Rmult_lt_compat_l; [real_solver|].
      apply lt_1_k.
    - iModIntro.
      iIntros "[Hind Herr]".
      iIntros (li) "Hα Hcont".
      iApply wp_presample_amplify_variant; eauto.
      iFrame.
      iIntros  "[[%lf1 [HΨ Htape]]|[%lf2 [Htape Hcr]]]".
      + iApply "Hcont".
        iFrame.
      + iApply ("Hind" with "[Hcr] [$Htape]").
        * iFrame.
        * iIntros (?) "(?&?)".
          iApply ("Hcont" with "[$]").
     Unshelve. auto.
  Qed.



  (*
     Below we prove a version of the almost sure termination rule from
     Majumdar and Sathiyanarayana, POPL 25. The idea is to have two functions
     U : list -> nat (called the variant) and V : list -> [0,∞) such that:
     (1) For every list l, there exists a c such that U(l++[c]) < U(l), i.e. U
     decreases with strictly positive probability
     (2) V is a supermartingale, i.e. E[U(l++[c])] <= U(l)
     (3) For a given fixed maximum value r of V(l), there exists a maximum value L of V.

     If these conditions are satisfied, one can prove that eventually one will presample
     a tape lf such that U(lf) = 0. The way we realize this in our setting is the
     following. Suppose we start with a positive amount of error credits ↯ε and an initial
     tape li. We can then split the credits into two positive halves ↯ε/2 and ↯ε/2. Since
     V is a supermartingale, we can use the expectation-preserving presampling rules to ensure
     that at all times we have a list lc and ↯(ε/2)*V(lc)/V(li). This allows us to set a maximum
     value for V, since once it grows enough this amount of error credits will amount to 1.
     By condition (3) above, this also sets a maximum value L of U. Now it becomes an easier
     problem. By condition (1), there always is at least one value that makes U decrease,
     and we are done whenever we succeed to sample it L times in a row. This can be proven
     using very similar techniques as the planner rule, i.e. by building an amplification
     sequence and using error induction.

   *)


   (*

     The lemma below describes what happens after a single presampling step. Instead
     of V, we have a function Vε assigning to every list its appropriate amount of
     error credits. The supermartingale condition ensures that presampling preserves
     the expected value of this function.

     Suppose we have an initial list li, and ↯ε ∗ ↯(Vε li). After presampling, one
     of two outcomes can happen:
     - We sample an element that decreases U, in which case we have a new list lf1,
     our first credit component will decrease and our second credit component will
     be ↯(Vε lf1)
     - We fail, in which case we have a new list lf2, our first credit component is
     amplified, and the second component is ↯(Vε lf2)

   *)


  Lemma twp_presample_amplify_rsm_aux N z e E α Φ Ψ (ε : posreal) li (Vε : list (fin (S N)) -> R) (U : list (fin (S N)) -> nat) (L : nat) kwf :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (forall l : list (fin (S N)), Ψ l <-> U(l) = 0) ->
    (forall l : list (fin (S N)), 0 <= Vε l)%R ->
    (forall l : list (fin (S N)), (SeriesC (λ (i : fin (S N)), 1/(S N) * Vε(l ++ [i]) ) <= Vε(l))%R ) ->
    (forall l : list (fin (S N)), ¬ Ψ l ->
      exists c : (fin (S N)), (U(l++[c]) < U(l))%R)  ->
    (0 < U li) ->
    (U li <= L) ->
    (α ↪ (N; li) ∗
       (↯ (pos_to_nn ε) ∗ ↯ (Vε li) )
       ⊢ (∀ (i : nat) (HL : (i <= L)%nat),
           (((∃ lf1, α ↪ (N; lf1) ∗ ↯(εAmp N L ε kwf) ∗ ↯ (Vε lf1)) ∨
               (∃ lf2, α ↪ (N; lf2) ∗  ⌜ U(lf2) + i <= L ⌝ ∗ ↯ (εR N L i ε (mk_fRwf N L i kwf HL)) ∗ ↯ (Vε lf2)  ))
            -∗ WP e @ E [{ Φ }])
           -∗ WP e @ E [{ Φ }]))%I.
  Proof.
    iIntros (? ? HU0 HVεpos Hrsm HUdec H0Uli HUliL) "(Htape & Hcr_initial)".
    iIntros (i HL).
    iInduction i as [|i'] "IH".
        - iIntros "Hwp".
          iApply "Hwp".
          iRight.
          iExists li.
          iFrame.
          iSplit.
          { iPureIntro.
            rewrite Nat.add_0_r //.
          }
          rewrite /εR /fR /pos_to_nn /=.
          rewrite Rmult_1_r //.
        - iIntros "Hwand".
          assert (HL' : (i' <= L)%nat) by lia.
          iSpecialize ("IH" $! HL' with "Htape Hcr_initial").
          iApply "IH".
          iIntros  "[[%lf1 [Htape Hcr]]|[%lf2 [Htape (%HUi' & Hcr1 & Hcr2)]]]".
          + iApply "Hwand".
            iLeft; iExists lf1; iFrame.
          + assert (Hi' : (i' < L)%nat) by lia.
            assert (0 = U lf2 \/ 0 < U lf2)%nat as [HUlf2 | HUlf2 ]by lia.
            * iApply "Hwand".
              iRight.
              iExists lf2.
              iFrame.
              iSplit.
              {
                iPureIntro.
                lia.
              }
              iApply ec_weaken; last by iFrame.
              split; [apply cond_nonneg |].
              rewrite /εR.
              apply Rmult_le_compat_l; [left; apply cond_pos |].
              apply fR_mon_dec.

            * assert (¬ Ψ lf2) as HnΨlf2.
              {
                intros HΨlf2.
                specialize (HU0 lf2) as [HU0 ?].
                specialize (HU0 HΨlf2).
                lia.
              }
             destruct (HUdec lf2 HnΨlf2) as [target Htarget].
             pose HMean := (εDistr_mean N L i' ε target (mk_fRwf N L (S i') kwf HL)).
             wp_apply twp_presample_adv_comp_leq_double ; [done | | | right; apply HMean | apply Hrsm | ].
             {
               intros; apply cond_nonneg.
             }
             {
               intros; apply HVεpos.
             }
             replace {| k_wf := kwf; i_ub := HL' |} with
               (fRwf_dec_i N L i' {| k_wf := kwf; i_ub := HL |}); [|apply fRwf_ext].
             iFrame.
             iIntros (s) "(Hcr1 & Hcr2 & Htape)".
             iApply "Hwand".
             rewrite /εDistr.
             case_bool_decide.
             ** iRight. iFrame. simplify_eq.
                iPureIntro.
                apply INR_lt in Htarget.
                lia.
             ** iLeft. iFrame.
  Qed.

  Lemma presample_amplify_rsm_aux N z e E α Φ Ψ (ε : posreal) li (Vε : list (fin (S N)) -> R) (U : list (fin (S N)) -> nat) (L : nat) kwf :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (forall l : list (fin (S N)), Ψ l <-> U(l) = 0) ->
    (forall l : list (fin (S N)), 0 <= Vε l)%R ->
    (forall l : list (fin (S N)), (SeriesC (λ (i : fin (S N)), 1/(S N) * Vε(l ++ [i]) ) <= Vε(l))%R ) ->
    (forall l : list (fin (S N)), ¬ Ψ l ->
      exists c : (fin (S N)), (U(l++[c]) < U(l))%R)  ->
    (0 < U li) ->
    (U li <= L) ->
    (α ↪ (N; li) ∗
       (↯ (pos_to_nn ε) ∗ ↯ (Vε li) )
       ⊢ (∀ (i : nat) (HL : (i <= L)%nat),
           (((∃ lf1, α ↪ (N; lf1) ∗ ↯(εAmp N L ε kwf) ∗ ↯ (Vε lf1)) ∨
               (∃ lf2, α ↪ (N; lf2) ∗  ⌜ U(lf2) + i <= L ⌝ ∗ ↯ (εR N L i ε (mk_fRwf N L i kwf HL)) ∗ ↯ (Vε lf2)  ))
            -∗ WP e @ E {{ Φ }})
           -∗ WP e @ E {{ Φ }}))%I.
  Proof.
    iIntros (? ? HU0 HVεpos Hrsm HUdec H0Uli HUliL) "(Htape & Hcr_initial)".
    iIntros (i HL).
    iInduction i as [|i'] "IH".
        - iIntros "Hwp".
          iApply "Hwp".
          iRight.
          iExists li.
          iFrame.
          iSplit.
          { iPureIntro.
            rewrite Nat.add_0_r //.
          }
          rewrite /εR /fR /pos_to_nn /=.
          rewrite Rmult_1_r //.
        - iIntros "Hwand".
          assert (HL' : (i' <= L)%nat) by lia.
          iSpecialize ("IH" $! HL' with "Htape Hcr_initial").
          iApply "IH".
          iIntros  "[[%lf1 [Htape Hcr]]|[%lf2 [Htape (%HUi' & Hcr1 & Hcr2)]]]".
          + iApply "Hwand".
            iLeft; iExists lf1; iFrame.
          + assert (Hi' : (i' < L)%nat) by lia.
            assert (0 = U lf2 \/ 0 < U lf2)%nat as [HUlf2 | HUlf2 ]by lia.
            * iApply "Hwand".
              iRight.
              iExists lf2.
              iFrame.
              iSplit.
              {
                iPureIntro.
                lia.
              }
              iApply ec_weaken; last by iFrame.
              split; [apply cond_nonneg |].
              rewrite /εR.
              apply Rmult_le_compat_l; [left; apply cond_pos |].
              apply fR_mon_dec.

            * assert (¬ Ψ lf2) as HnΨlf2.
              {
                intros HΨlf2.
                specialize (HU0 lf2) as [HU0 ?].
                specialize (HU0 HΨlf2).
                lia.
              }
             destruct (HUdec lf2 HnΨlf2) as [target Htarget].
             pose HMean := (εDistr_mean N L i' ε target (mk_fRwf N L (S i') kwf HL)).
             wp_apply wp_presample_adv_comp_leq_double ; [done | | | right; apply HMean | apply Hrsm | ].
             {
               intros; apply cond_nonneg.
             }
             {
               intros; apply HVεpos.
             }
             replace {| k_wf := kwf; i_ub := HL' |} with
               (fRwf_dec_i N L i' {| k_wf := kwf; i_ub := HL |}); [|apply fRwf_ext].
             iFrame.
             iIntros (s) "(Hcr1 & Hcr2 & Htape)".
             iApply "Hwand".
             rewrite /εDistr.
             case_bool_decide.
             ** iRight. iFrame. simplify_eq.
                iPureIntro.
                apply INR_lt in Htarget.
                lia.
             ** iLeft. iFrame.
  Qed.


   (*
      The lemma below describes one round of presampling i.e., keep presampling elements until we
      reach a tape l for which U(l)=0, or we fail to sample the decreasing element, and get an
      amplified amount of credits
   *)

  Lemma twp_presample_amplify_rsm N z e E α Φ Ψ (ε : posreal) li (Vε : list (fin (S N)) -> R) (U : list (fin (S N)) -> nat) L (kwf: kwf N L) :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (forall l : list (fin (S N)), Ψ l <-> U(l) = 0) ->
    (forall l : list (fin (S N)), 0 <= Vε l)%R ->
    (forall l : list (fin (S N)), (SeriesC (λ (i : fin (S N)), 1/(S N) * Vε(l ++ [i]) ) <= Vε(l))%R ) ->
    (forall l : list (fin (S N)), ¬ Ψ l ->
      exists c : (fin (S N)), (U(l++[c]) < U(l))%R)  ->
    (forall l : list (fin (S N)), (L < U l)%nat -> (1 <= Vε l)%R) ->
      ↯ (pos_to_nn ε) ∗
      ↯ (Vε li) ∗
      (α ↪ (N; li)) ∗
      (((∃ lf, ⌜ Ψ lf ⌝ ∗ α ↪ (N; lf)) ∨
          (∃ junk, α ↪ (N; junk) ∗ ↯(εAmp N L ε kwf) ∗ ↯(Vε junk))) -∗ WP e @ E [{ Φ }])
      ⊢ WP e @ E [{ Φ }].
  Proof.
    iIntros (? ? HU0 HVεpos Hrsm HUdec HVbd) "(Hcr1 & Hcr2 & Htape & Hwp)".
    destruct (U li) as [|u] eqn:Hu.
    - iApply "Hwp".
      iLeft.
      iExists li.
      iFrame.
      iPureIntro.
      destruct (decide (Ψ li)) as [?|HnΨli]; auto.
      specialize (HUdec li HnΨli) as [c Hc].
      apply INR_lt in Hc.
      lia.
    - assert (0 < U li) by lia.
      assert (U li <= L \/ L < U li) as [HUliL | HLUli ] by lia; last first.
      {
        iPoseProof (ec_contradict with "Hcr2") as "?"; auto.
      }
      iApply (twp_presample_amplify_rsm_aux with "[Htape Hcr1 Hcr2]"); eauto; [iFrame|].
      iIntros  "[[%lf1 (Htape & Hcr1 & Hcr2) ]|[%lf2 [Htape (%HUlf2 & Hcr)]]]"; iApply "Hwp".
      + iRight.
        iExists lf1.
        iFrame.
      + iLeft. iFrame.
        Unshelve.
        2: exact L.
        2: lia.
        iPureIntro.
        assert (U lf2 = 0) by lia.
        destruct (decide (Ψ lf2)) as [? | HnΨlf2]; auto.
        specialize (HUdec lf2 HnΨlf2) as [c Hc].
        apply INR_lt in Hc.
        lia.
  Qed.

  (* do one step in the amplification sequence *)
  Lemma wp_presample_amplify_rsm N z e E α Φ Ψ (ε : posreal) li (Vε : list (fin (S N)) -> R) (U : list (fin (S N)) -> nat) L (kwf: kwf N L) :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    (forall l : list (fin (S N)), Ψ l <-> U(l) = 0) ->
    (forall l : list (fin (S N)), 0 <= Vε l)%R ->
    (forall l : list (fin (S N)), (SeriesC (λ (i : fin (S N)), 1/(S N) * Vε(l ++ [i]) ) <= Vε(l))%R ) ->
    (forall l : list (fin (S N)), ¬ Ψ l ->
      exists c : (fin (S N)), (U(l++[c]) < U(l))%R)  ->
    (forall l : list (fin (S N)), (L < U l)%nat -> (1 <= Vε l)%R) ->
      ↯ (pos_to_nn ε) ∗
      ↯ (Vε li) ∗
      (α ↪ (N; li)) ∗
      (((∃ lf, ⌜ Ψ lf ⌝ ∗ α ↪ (N; lf)) ∨
          (∃ junk, α ↪ (N; junk) ∗ ↯(εAmp N L ε kwf) ∗ ↯(Vε junk))) -∗ WP e @ E {{ Φ }})
      ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (? ? HU0 HVεpos Hrsm HUdec HVbd) "(Hcr1 & Hcr2 & Htape & Hwp)".
    destruct (U li) as [|u] eqn:Hu.
    - iApply "Hwp".
      iLeft.
      iExists li.
      iFrame.
      iPureIntro.
      destruct (decide (Ψ li)) as [?|HnΨli]; auto.
      specialize (HUdec li HnΨli) as [c Hc].
      apply INR_lt in Hc.
      lia.
    - assert (0 < U li) by lia.
      assert (U li <= L \/ L < U li) as [HUliL | HLUli ] by lia; last first.
      {
        iPoseProof (ec_contradict with "Hcr2") as "?"; auto.
      }
      iApply (presample_amplify_rsm_aux with "[Htape Hcr1 Hcr2]"); eauto; [iFrame|].
      iIntros  "[[%lf1 (Htape & Hcr1 & Hcr2) ]|[%lf2 [Htape (%HUlf2 & Hcr)]]]"; iApply "Hwp".
      + iRight.
        iExists lf1.
        iFrame.
      + iLeft. iFrame.
        Unshelve.
        2: exact L.
        2: lia.
        iPureIntro.
        assert (U lf2 = 0) by lia.
        destruct (decide (Ψ lf2)) as [? | HnΨlf2]; auto.
        specialize (HUdec lf2 HnΨlf2) as [c Hc].
        apply INR_lt in Hc.
        lia.
  Qed.

   (*
      Main lemma below implementing the variant+supermartingale rule
   *)

  Lemma twp_presample_rsm N z e E α Φ Ψ (ε : nonnegreal) li (V : list (fin (S N)) -> R) (U : list (fin (S N)) -> nat) :
    TCEq N (Z.to_nat z) →
    to_val e = None ->
    (forall l : list (fin (S N)), 0 <= V(l))%R ->
    (forall l : list (fin (S N)), Ψ l <-> V(l) = 0) ->
    (forall l : list (fin (S N)), Ψ l <-> U(l) = 0) ->
    (* U is bounded in downsets of V *)
    (forall r : R, exists n : nat, forall l : list (fin (S N)), V(l) <= r -> U(l) ≤ n)%R ->
    (* U decreases with non-zero probability *)
    (forall l : list (fin (S N)), ¬ Ψ l ->
           exists c : (fin (S N)), (U(l++[c]) < U(l))%R)  ->
    (* V is a supermartingale *)
    (forall l : list (fin (S N)), (SeriesC (λ (i : fin (S N)), 1/(S N) * V(l ++ [i]) ) <= V(l))%R ) ->
    (0 < ε)%R ->
    ↯ (ε) ∗
      (α ↪ (N; li)) ∗
    (∀ lf, ⌜ Ψ lf ⌝ ∗ α ↪ (N; lf) -∗ WP e @ E [{ Φ }])
      ⊢ WP e @ E [{ Φ }].
  Proof.
    iIntros (? ? HVpos HΨV HΨU HUbd HUdec HVsm Hε) "(Hcr & Hα & Hcont)".
    (*
        We treat the corner case where V li = 0 separately
    *)
    destruct (decide (V li = 0)) as [HVli0 | HVlin0].
    {
      iApply "Hcont".
      iFrame.
      iPureIntro.
      by apply HΨV.
    }
    assert (0 < V li)%R as HVlipos.
    {
      specialize (HVpos li).
      destruct (Rle_lt_or_eq_dec _ _ HVpos); done.
    }
    assert (N = 0 \/ 0 < N) as [-> | HN] by lia.
    (* Corner case: N = 0 *)
    {
      assert (exists n, U li <= n) as [n Hn].
      {
        exists (U li).
        by lia.
      }
      clear HVlipos.
      clear HVlin0.
      iInduction (n) as [|?] "IH" forall (li Hn).
      - iApply "Hcont".
        iFrame.
        iPureIntro.
        apply HΨU.
        lia.
      - destruct (decide (U li = 0)) as [HUli0 | HUlin0].
        + iApply "Hcont".
          iFrame.
          iPureIntro.
          by apply HΨU.
        + assert (¬ Ψ li) as HnΨ.
          {
            intros HΨ.
            apply HUlin0.
            by apply HΨU.
          }
          iApply twp_presample; auto; iFrame.
          iIntros (n0) "Hα".
          destruct (HUdec _ HnΨ) as [c Hc].
          assert (n0 = 0%fin) as ->.
          {
            inv_fin n0; auto.
            intros i.
            inv_fin i.
          }
          assert (c = 0%fin) as ->.
          {
            inv_fin c; auto.
            intros i ?.
            inv_fin i.
          }
          iApply ("IH" with "[][$][$]").
          * iPureIntro.
            apply INR_lt in Hc.
            lia.
          * iIntros (lf) "(%Hlf & Hα)".
            iApply "Hcont"; iFrame; done.
    }
    (*
       Main case below. We begin by splitting our credits in half
    *)
    set (εhalf := (ε/2)%NNR).
    replace ε with (εhalf + εhalf)%NNR; last first.
    {
      apply nnreal_ext.
      rewrite /εhalf /=.
      lra.
    }
    assert (0 < εhalf)%R as Hεhalf.
    {
      simpl.
      apply Rcomplements.Rdiv_lt_0_compat; auto.
      lra.
    }
    iPoseProof (ec_split with "Hcr") as "[HcrU HcrV]".
    { apply cond_nonneg. }
    { apply cond_nonneg. }

    (*
        Since we will always own ↯(ε/2)*(V l)/(V li), we
        only need to consider V when it is below (2/ε * V li).
        We use this to set a max value for U
    *)
    specialize (HUbd (2/ε * V li)%R) as [L HL].
    assert (0 < S L) as HSL by lia.
    pose kwf := mk_kwf _ _ HN HSL.

    (*
        We define the Vε function mapping to every value of V is
        right amount of credits
    *)
    set (Vε := λ (l : list (fin (S N))), ((ε / 2) * (V l / V li))%R).
    iDestruct (ec_eq _ (Vε li) with "HcrV") as "HcrV".
    {
      rewrite /εhalf /Vε /=.
      rewrite /Rdiv Rmult_inv_r //.
      lra.
    }

    pose εhalf' := mkposreal εhalf.(nonneg) Hεhalf.
    replace εhalf with (pos_to_nn εhalf'); last first.
    { rewrite /εhalf' /pos_to_nn. by apply nnreal_ext. }

    (*
       In order to use error induction on HcrU, we need to create an "invariant"
       containing the rest of the hypotheses, and revert it
    *)
    set (Hinv_pre :=
           (∃ (Wε : list (fin (S N)) -> R) (lc : list (fin (S N))),
               ⌜ forall l : list (fin (S N)), (0 <= Wε l)%R ⌝ ∗
             ⌜ forall l : list (fin (S N)), (SeriesC (λ (i : fin (S N)), 1/(S N) * Wε(l ++ [i]) ) <= Wε(l))%R ⌝ ∗
            ⌜ forall l : list (fin (S N)), (S L < U l)%nat -> (1 <= Wε l)%R ⌝ ∗
            α ↪ (N; lc) ∗ ↯ (Wε lc)
           )%I : iProp Σ
        ).
    iAssert Hinv_pre with "[Hα HcrV]" as "Hinv".
    {
      rewrite /Hinv_pre.
      iExists Vε, li.
      rewrite /Vε.
      iSplit.
      {
        iPureIntro.
        intros Hlc.
        apply Rmult_le_pos; [real_solver |].
        apply Rcomplements.Rdiv_le_0_compat; eauto.
      }
      iSplit.
      {
        iPureIntro.
        intros Hlc.
        setoid_rewrite <- (Rmult_assoc _ (ε/2)).
        setoid_rewrite (Rmult_comm _ (ε/2)).
        setoid_rewrite (Rmult_assoc (ε/2)).
        rewrite SeriesC_scal_l.
        apply Rmult_le_compat_l; [real_solver |].
        setoid_rewrite <- (Rmult_assoc (1 / (S N))).
        rewrite SeriesC_scal_r.
        apply Rmult_le_compat_r; auto.
        left.
        by apply Rinv_0_lt_compat.
      }
      iSplit.
      {
        iPureIntro.
        intros lc Hlc.
        destruct (Rle_lt_dec 1 (ε / 2 * (V lc / V li))%R) as [Hle | Hnle]; auto.
        assert (U lc <= L); last by lia.
        apply HL.
        apply Rlt_le in Hnle.
        apply Rcomplements.Rle_div_l; [lra|].
        apply (Rcomplements.Rle_div_r _ _ ε); auto.
        lra.
      }
      iFrame.
    }
    clear Vε.
    iRevert "Hcont Hinv".

    (*
         We now use error induction
    *)
    iApply (ec_ind_incr _ (εAmp N (S L) εhalf' _) with "[] HcrU").
    - apply cond_pos.
    - rewrite /εAmp /=.
      rewrite -{1}(Rmult_1_r (ε * / (1 + 1))).
      apply Rmult_lt_compat_l; [real_solver|].
      apply lt_1_k.

    - iModIntro.
      iIntros "[Hind Herr] Hcont".
      iIntros "(%W & %lc & %HWpos & %HWsm & %HWbd & Hβ & HεW)".
      iApply (twp_presample_amplify_rsm); eauto.
      iSplitL "Herr"; [iFrame|].
      iFrame.
      iIntros  "[[%lf1 [HΨ Htape]]|[%lf2 [Htape [HcrU HcrW]]]]".
      + iApply "Hcont".
        iFrame.
      + iApply ("Hind" with "[HcrU] [Hcont] [Htape HcrW]").
        * iFrame.
        * iIntros (?) "(?&?)".
          iApply ("Hcont" with "[$]").
        * iExists _,_.
          iSplit; auto.
          iSplit; auto.
          iSplit; auto.
           iFrame.
     Unshelve. auto.
  Qed.


  Lemma presample_rsm N z e E α Φ Ψ (ε : nonnegreal) li (V : list (fin (S N)) -> R) (U : list (fin (S N)) -> nat) :
    TCEq N (Z.to_nat z) →
    to_val e = None ->
    (forall l : list (fin (S N)), 0 <= V(l))%R ->
    (forall l : list (fin (S N)), Ψ l <-> V(l) = 0) ->
    (forall l : list (fin (S N)), Ψ l <-> U(l) = 0) ->
    (* U is bounded in downsets of V *)
    (forall r : R, exists n : nat, forall l : list (fin (S N)), V(l) <= r -> U(l) ≤ n)%R ->
    (* U decreases with non-zero probability *)
    (forall l : list (fin (S N)), ¬ Ψ l ->
           exists c : (fin (S N)), (U(l++[c]) < U(l))%R)  ->
    (* V is a supermartingale *)
    (forall l : list (fin (S N)), (SeriesC (λ (i : fin (S N)), 1/(S N) * V(l ++ [i]) ) <= V(l))%R ) ->
    (0 < ε)%R ->
    ↯ (ε) ∗
      (α ↪ (N; li)) ∗
    (∀ lf, ⌜ Ψ lf ⌝ ∗ α ↪ (N; lf) -∗ WP e @ E {{ Φ }})
      ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (? ? HVpos HΨV HΨU HUbd HUdec HVsm Hε) "(Hcr & Hα & Hcont)".
    destruct (decide (V li = 0)) as [HVli0 | HVlin0].
    {
      iApply "Hcont".
      iFrame.
      iPureIntro.
      by apply HΨV.
    }
    assert (0 < V li)%R as HVlipos.
    {
      specialize (HVpos li).
      destruct (Rle_lt_or_eq_dec _ _ HVpos); done.
    }
    assert (N = 0 \/ 0 < N) as [-> | HN] by lia.
    (* Corner case: N = 0 *)
    {
      assert (exists n, U li <= n) as [n Hn].
      {
        exists (U li).
        by lia.
      }
      clear HVlipos.
      clear HVlin0.
      iInduction (n) as [|?] "IH" forall (li Hn).
      - iApply "Hcont".
        iFrame.
        iPureIntro.
        apply HΨU.
        lia.
      - destruct (decide (U li = 0)) as [HUli0 | HUlin0].
        + iApply "Hcont".
          iFrame.
          iPureIntro.
          by apply HΨU.
        + assert (¬ Ψ li) as HnΨ.
          {
            intros HΨ.
            apply HUlin0.
            by apply HΨU.
          }
          iApply wp_presample; auto; iFrame.
          iIntros (n0) "Hα".
          destruct (HUdec _ HnΨ) as [c Hc].
          assert (n0 = 0%fin) as ->.
          {
            inv_fin n0; auto.
            intros i.
            inv_fin i.
          }
          assert (c = 0%fin) as ->.
          {
            inv_fin c; auto.
            intros i ?.
            inv_fin i.
          }
          iApply ("IH" with "[][$][$]").
          * iPureIntro.
            apply INR_lt in Hc.
            lia.
          * iIntros (lf) "(%Hlf & Hα)".
            iApply "Hcont"; iFrame; done.
    }
    set (εhalf := (ε/2)%NNR).
    replace ε with (εhalf + εhalf)%NNR; last first.
    {
      apply nnreal_ext.
      rewrite /εhalf /=.
      lra.
    }
    assert (0 < εhalf)%R as Hεhalf.
    {
      simpl.
      apply Rcomplements.Rdiv_lt_0_compat; auto.
      lra.
    }
    iPoseProof (ec_split with "Hcr") as "[HcrU HcrV]".
    { apply cond_nonneg. }
    { apply cond_nonneg. }

    specialize (HUbd (2/ε * V li)%R) as [L HL].
    assert (0 < S L) as HSL by lia.
    pose kwf := mk_kwf _ _ HN HSL.

    set (Vε := λ (l : list (fin (S N))), ((ε / 2) * (V l / V li))%R).
    iDestruct (ec_eq _ (Vε li) with "HcrV") as "HcrV".
    {
      rewrite /εhalf /Vε /=.
      rewrite /Rdiv Rmult_inv_r //.
      lra.
    }

    pose εhalf' := mkposreal εhalf.(nonneg) Hεhalf.
    replace εhalf with (pos_to_nn εhalf'); last first.
    { rewrite /εhalf' /pos_to_nn. by apply nnreal_ext. }
    set (Hinv_pre :=
           (∃ (Wε : list (fin (S N)) -> R) (lc : list (fin (S N))),
               ⌜ forall l : list (fin (S N)), (0 <= Wε l)%R ⌝ ∗
             ⌜ forall l : list (fin (S N)), (SeriesC (λ (i : fin (S N)), 1/(S N) * Wε(l ++ [i]) ) <= Wε(l))%R ⌝ ∗
            ⌜ forall l : list (fin (S N)), (S L < U l)%nat -> (1 <= Wε l)%R ⌝ ∗
            α ↪ (N; lc) ∗ ↯ (Wε lc)
           )%I : iProp Σ
        ).
    iAssert Hinv_pre with "[Hα HcrV]" as "Hinv".
    {
      rewrite /Hinv_pre.
      iExists Vε, li.
      rewrite /Vε.
      iSplit.
      {
        iPureIntro.
        intros Hlc.
        apply Rmult_le_pos; [real_solver |].
        apply Rcomplements.Rdiv_le_0_compat; eauto.
      }
      iSplit.
      {
        iPureIntro.
        intros Hlc.
        setoid_rewrite <- (Rmult_assoc _ (ε/2)).
        setoid_rewrite (Rmult_comm _ (ε/2)).
        setoid_rewrite (Rmult_assoc (ε/2)).
        rewrite SeriesC_scal_l.
        apply Rmult_le_compat_l; [real_solver |].
        setoid_rewrite <- (Rmult_assoc (1 / (S N))).
        rewrite SeriesC_scal_r.
        apply Rmult_le_compat_r; auto.
        left.
        by apply Rinv_0_lt_compat.
      }
      iSplit.
      {
        iPureIntro.
        intros lc Hlc.
        destruct (Rle_lt_dec 1 (ε / 2 * (V lc / V li))%R) as [Hle | Hnle]; auto.
        assert (U lc <= L); last by lia.
        apply HL.
        apply Rlt_le in Hnle.
        apply Rcomplements.Rle_div_l; [lra|].
        apply (Rcomplements.Rle_div_r _ _ ε); auto.
        lra.
      }
      iFrame.
    }
    clear Vε.
    iRevert "Hcont Hinv".
    iApply (ec_ind_incr _ (εAmp N (S L) εhalf' _) with "[] HcrU").
    - apply cond_pos.
    - rewrite /εAmp /=.
      rewrite -{1}(Rmult_1_r (ε * / (1 + 1))).
      apply Rmult_lt_compat_l; [real_solver|].
      apply lt_1_k.

    - iModIntro.
      iIntros "[Hind Herr] Hcont".
      iIntros "(%W & %lc & %HWpos & %HWsm & %HWbd & Hβ & HεW)".
      iApply (wp_presample_amplify_rsm); eauto.
      iSplitL "Herr"; [iFrame|].
      iFrame.
      iIntros  "[[%lf1 [HΨ Htape]]|[%lf2 [Htape [HcrU HcrW]]]]".
      + iApply "Hcont".
        iFrame.
      + iApply ("Hind" with "[HcrU] [Hcont] [Htape HcrW]").
        * iFrame.
        * iIntros (?) "(?&?)".
          iApply ("Hcont" with "[$]").
        * iExists _,_.
          iSplit; auto.
          iSplit; auto.
          iSplit; auto.
           iFrame.
     Unshelve. auto.
  Qed.


End rules.

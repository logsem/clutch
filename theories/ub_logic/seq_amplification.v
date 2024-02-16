(** * Calculation for the Sequential Amplification Rile *)
From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext NNRbar.
From clutch.app_rel_logic Require Import lifting ectx_lifting.
From clutch.prob_lang Require Import lang notation tactics metatheory.
Require Import Lra.


Section seq_ampl.
  Local Open Scope R.
  Implicit Types N l i : nat.
  Implicit Types ε : nonnegreal.


  Lemma pow_pos N : (0 < N)%nat -> forall w, (0 < w)%nat -> 0 < ((S N)^w - 1).
  Proof.
    intros w HN Hw.
    apply (Rplus_lt_reg_r 1).
    rewrite Rplus_assoc Rplus_opp_l Rplus_0_l Rplus_0_r.
    apply Rlt_pow_R1; [apply lt_1_INR|]; lia.
  Qed.

  Lemma pow_nz N : (0 < N)%nat -> forall w, (w > 0)%nat -> ((S N)^w - 1) ≠ 0.
  Proof.
    intros.
    apply Rgt_not_eq; apply Rlt_gt.
    apply pow_pos; lia.
  Qed.


  (* well-formedness for k *)
  (* well-formedness of k doesn't depend on the proof => OK to use proof irrelevence *)
  Record kwf N l : Set := mk_kwf { N_lb : (0 < N)%nat; l_lb: (0 < l)%nat }.
  Lemma kwf_ext N l (x : kwf N l) (y : kwf N l) : x = y.
  Proof.
    destruct x; destruct y.
    f_equal; apply proof_irrelevance.
  Qed.

  (** amplification factor on our error *)
  Definition k N l (kwf : kwf N l) : R := 1 + 1 / ((S N)^l - 1).


  Lemma lt_1_k N l kwf : 1 < k N l kwf.
  Proof.
    destruct kwf as [Hn Hl].
    remember {| N_lb := _; l_lb := _|} as kwf.
    rewrite /k /Rdiv.
    apply (Rmult_lt_reg_r ((S N)^l-1)); [by apply pow_pos|].
    rewrite Rmult_plus_distr_r Rmult_assoc Rinv_l; [|by apply pow_nz].
    lra.
  Qed.

  Lemma k_pos N l kwf : 0 < k N l kwf.
  Proof. apply (Rlt_trans _ 1); [lra|apply lt_1_k; auto]. Qed.


  (* well-formedness for fR *)
  Record fRwf N l i : Set := mk_fRwf { k_wf : (kwf N l) ; i_ub : (i <= l)%nat }.
  Lemma fRwf_dec_i N l i (fRbS : fRwf N l (S i)) : fRwf N l i.
  Proof. destruct fRbS. apply mk_fRwf; auto; lia. Qed.
  Lemma fRwf_upper N l : kwf N l -> fRwf N l l.
  Proof. intros. apply mk_fRwf; auto. Qed.
  Lemma fRwf_lower N l : kwf N l -> fRwf N l 0.
  Proof. intros. apply mk_fRwf; auto. lia. Qed.
  Lemma fRwf_ext N l i (x : fRwf N l i) (y : fRwf N l i) : x = y.
  Proof. destruct x; destruct y. f_equal; [apply kwf_ext | apply proof_irrelevance]. Qed.


  (** remainder factor on error after step i *)
  Fixpoint fR N l i (fRwf : fRwf N l i) : R.
    refine ((match i as m return (i = m) -> R with
              0%nat    => fun _ => 1%nat
            | (S i') => fun H => ((S N) * (fR N l i' _) - (k N l (fRwf.(k_wf N l i))) * N)
            end) (eq_refl i)).
    apply fRwf_dec_i; by rewrite -H.
  Defined.

  (* closed form 1: easy to do induction over i *)
  Lemma fR_closed_1 N l i fRwf: (fR N l i fRwf) = (1 - (k N l (fRwf.(k_wf N l i)))) * (S N)^i + (k N l (fRwf.(k_wf N l i))).
  Proof.
    destruct fRwf as [[Hn Hl] Hi].
    remember {| k_wf := _; i_ub := _|} as fRwf.
    induction i as [|i' IH].
    - simpl; lra.
    - Opaque INR.
      simpl fR. rewrite IH; [|lia|intros; apply fRwf_ext].
      remember (k N l (k_wf N l i' (fRwf_dec_i N l i' fRwf))) as K.
      replace (k N l (k_wf N l (S i') fRwf)) with K.
      rewrite Rmult_plus_distr_l.
      rewrite Rmult_comm Rmult_assoc (Rmult_comm  _ (S _)) tech_pow_Rmult.
      rewrite /Rminus Rplus_assoc.
      apply Rplus_eq_compat_l.
      rewrite S_INR.
      lra.
  Qed.

  (* closed forn 2: easy to bound *)
  Lemma fR_closed_2 N l i fRwf: (fR N l i fRwf) = 1 - (((S N)^i - 1) / ((S N)^l - 1)).
  Proof.
    destruct fRwf as [[Hn Hl] Hi].
    remember {| k_wf := _; i_ub := _|} as fRwf.
    rewrite fR_closed_1.
    rewrite /k /=. lra.
  Qed.

  (* much easier to prove this using closed form 2 *)
  Lemma fR_nonneg N l i fRwf : 0 <= (fR N l i fRwf).
  Proof.
    destruct fRwf as [[Hn Hl] Hi].
    remember {| k_wf := _; i_ub := _ |} as fRwf.
    rewrite fR_closed_2.
    rewrite /Rdiv.
    apply (Rmult_le_reg_r (S N^l - 1)).
    - rewrite /Rminus.
      apply (Rplus_lt_reg_r 1).
      rewrite Rplus_0_l Rplus_assoc Rplus_opp_l Rplus_0_r.
      apply Rlt_pow_R1; [apply lt_1_INR|]; lia.
    - rewrite Rmult_0_l.
      rewrite Rmult_plus_distr_r /Rdiv Rmult_1_l.
      rewrite Ropp_mult_distr_l_reverse.
      rewrite Rmult_assoc Rinv_l; [|apply pow_nz; lia].
      rewrite Rmult_1_r.
      apply (Rplus_le_reg_r (S N^i - 1)).
      rewrite Rplus_assoc Rplus_opp_l Rplus_0_l Rplus_0_r.
      apply Rplus_le_compat_r.
      apply Rle_pow; try lia.
      apply Rlt_le.
      apply lt_1_INR.
      lia.
  Qed.

  Lemma fR_lt_1 N1 L i fRwf : (fR N1 L i fRwf <= 1)%R.
  Proof.
    destruct fRwf as [kwf ?]; destruct kwf.
    rewrite fR_closed_2.
    apply Rcomplements.Rle_minus_l.
    rewrite -{1}(Rplus_0_r 1%R); apply Rplus_le_compat_l.
    apply Rcomplements.Rdiv_le_0_compat; [apply -> Rcomplements.Rminus_le_0 | apply Rlt_0_minus ].
    - apply pow_R1_Rle.
      pose (pos_INR N1).
      rewrite S_INR.
      lra.
    - apply Rlt_pow_R1; try lia.
      apply lt_1_INR. lia.
  Qed.

  (* fR will have the mean property we need *)
  Lemma fR_mean N l i fRwf :
    (S N) * (fR N l i (fRwf_dec_i N l i fRwf)) = N * (k N l (fRwf.(k_wf N l (S i)))) +  fR N l (S i) fRwf .
  Proof. intros. rewrite /fR /=. lra. Qed.

  (** Remaining error at each step *)
  Program Definition εR N l i (ε : posreal) fRwf : nonnegreal
    := mknonnegreal (ε * fR N l i fRwf) _.
  Next Obligation.
    intros.
    apply Rmult_le_pos.
      - apply Rlt_le. apply cond_pos.
      - by apply fR_nonneg.
  Qed.

  Lemma εR_ext N l i (ε : posreal) fRwf1 fRwf2 : (εR N l i ε fRwf1 = εR N l i ε fRwf2).
  Proof. f_equal. apply fRwf_ext. Qed.

  Program Definition εAmp N l (ε : posreal) kwf : nonnegreal
    := mknonnegreal (ε.(pos) * k N l kwf) _.
  Next Obligation.
    intros; simpl.
    destruct ε; rewrite /RIneq.nonneg.
    apply Rmult_le_pos.
    - apply Rlt_le. auto.
    - apply Rlt_le. apply k_pos.
  Qed.

  Program Definition εAmp_iter N l d (ε : posreal) kwf : posreal
    := mkposreal (ε.(pos) * (k N l kwf)^d) _.
  Next Obligation.
    intros; simpl.
    destruct ε; rewrite /RIneq.nonneg.
    apply Rmult_lt_0_compat.
    - auto.
    - apply pow_lt. apply k_pos.
  Qed.

  Lemma εAmp_iter_cmp N l d (ε : posreal) kwf :
    εAmp N l (εAmp_iter N l d ε kwf) kwf = pos_to_nn (εAmp_iter N l (S d) ε kwf).
  Proof.
    apply nnreal_ext.
    rewrite /εAmp_iter /εAmp /pos_to_nn /=.
    lra.
  Qed.

  Lemma εAmp_amplification N l (ε : posreal) kwf : ε < (εAmp N l ε kwf).
  Proof.
    rewrite /εAmp /=.
    replace (pos ε) with (pos ε * 1) by apply Rmult_1_r.
    rewrite Rmult_assoc.
    apply Rmult_lt_compat_l.
    - apply cond_pos.
    - rewrite Rmult_1_l. apply lt_1_k; auto.
  Qed.


  (** Distribution for amplification at step i *)
  Definition εDistr N l i (ε : posreal) target fRwf : (fin (S N)) -> nonnegreal
    := fun sample => if (bool_decide (sample = target))
                    then (εR N l (S i) ε fRwf)
                    else (εAmp N l ε (fRwf.(k_wf N l (S i)))).


  (** Mean lemma for calls to amplification *)
  Lemma εDistr_mean N l i (ε : posreal) target fRwf :
       SeriesC (λ n : fin (S N), (1 / INR (S N) * nonneg (εDistr N l i ε target fRwf n))%R)
    = (εR N l i ε (fRwf_dec_i N l i fRwf)).
  Proof.
    destruct fRwf as [[Hn Hl] Hi].
    remember {| k_wf := _; i_ub := _ |} as fRwf.
    remember (fun n : fin _ => 1 / INR (S N) * nonneg (εDistr N l i ε target fRwf n))%R as body.
    (* we want to exclude the n=target case, and then it's a constant *)
    assert (body_pos : ∀ a : fin _, 0 <= body a).
    { intro a.
      rewrite Heqbody.
      apply Rmult_le_pos.
      - apply Rle_mult_inv_pos; [lra|apply lt_0_INR; lia].
      - destruct εDistr. simpl; lra. }
    rewrite (SeriesC_split_elem body target body_pos) /=; try (apply ex_seriesC_finite).
    assert (HSN : not (@eq R (INR (S N)) (IZR Z0))).
    { rewrite S_INR. apply Rgt_not_eq. apply Rcomplements.INRp1_pos. }

    (* Evaluate the first series *)
    replace (SeriesC (λ a : fin _, if bool_decide (a = target) then body a else 0))
       with (1 / INR (S N) * (εR N l (S i) ε fRwf)); last first.
    { rewrite SeriesC_singleton_dependent.
      rewrite Heqbody /εDistr.
      rewrite bool_decide_true; try auto. }

    (* Evaluate the second series *)
    replace (SeriesC (λ a : fin _, if bool_decide (not (a = target)) then body a else 0))
       with (N  * / INR (S N) * (εAmp N l ε (fRwf.(k_wf N l (S i))))); last first.
    { apply (Rplus_eq_reg_l (1 * / INR (S N) * (εAmp N l ε (fRwf.(k_wf N l (S i)))))).

      (* simplify the LHS *)
      do 2 rewrite Rmult_assoc.
      rewrite -Rmult_plus_distr_r.
      rewrite Rplus_comm -S_INR -Rmult_assoc Rinv_r; try auto.
      do 2 rewrite Rmult_1_l.

      (* turn the first term on the RHS into a singleton series, and combine into constant series *)
      rewrite -(SeriesC_singleton target  (/ INR (S N) * _)).
      rewrite -SeriesC_plus; try (apply ex_seriesC_finite).
      rewrite -(SeriesC_ext (fun x : fin (S N) => / INR (S N) * (εAmp N l ε (fRwf.(k_wf N l (S i)))))); last first.
      { intros n.
        case_bool_decide.
        - rewrite bool_decide_false; auto; lra.
        - rewrite bool_decide_true; auto.
          rewrite Heqbody /εDistr.
          rewrite bool_decide_false; auto.
          rewrite Rplus_0_l /Rdiv Rmult_1_l.
          apply Rmult_eq_compat_l.
          by simpl nonneg. }

      (* evaluate the finite series *)
      rewrite SeriesC_finite_mass fin_card.
      rewrite -Rmult_assoc Rinv_r; try auto.
      lra.
    }

    (* Multiply everything by S N*)
    apply (Rmult_eq_reg_l (INR (S N))); [| apply not_0_INR;lia].
    rewrite Rmult_plus_distr_l -Rmult_assoc /Rdiv.
    rewrite Rmult_1_l Rinv_r; [| apply not_0_INR;lia].
    rewrite Rmult_1_l.
    rewrite -Rmult_assoc (Rmult_comm _ ( / INR (S N))) -Rmult_assoc.
    rewrite Rinv_r; [| apply not_0_INR;lia].
    rewrite Rmult_1_l.

    (* Divide by 𝜀 *)
    rewrite /εR. Opaque fR. simpl nonneg.
    do 2 rewrite (Rmult_comm (INR _)) Rmult_assoc.
    rewrite -Rmult_plus_distr_l.
    apply Rmult_eq_compat_l.

    (* apply fR_mean and conclude *)
    rewrite (Rmult_comm _ (INR (S N))).
    rewrite (fR_mean N); try lia.
    lra.
  Qed.


  Program Definition Δε (ε : posreal) N L kwf : posreal := mkposreal (εAmp N L ε kwf - ε) _.
  Next Obligation. intros. pose (εAmp_amplification N L ε kwf0). lra. Qed.

  Lemma εAmp_excess (ε : posreal) N1 L kwf :
    forall i fRwf, ((εR N1 L i ε fRwf) + (Δε ε N1 L kwf) <= εAmp N1 L ε kwf)%R.
  Proof.
    intros.
    rewrite -(Rplus_0_r (εAmp _ _ _ _)).
    rewrite /Δε /=.
    rewrite Rplus_comm Rplus_assoc; apply Rplus_le_compat_l.
    apply (Rplus_le_reg_l ε).
    rewrite -Rplus_assoc Rplus_opp_r Rplus_0_l Rplus_0_r.
    rewrite -{2}(Rmult_1_r ε).
    apply Rmult_le_compat_l; [apply Rlt_le, cond_pos|].
    apply fR_lt_1.
  Qed.


End seq_ampl.

From clutch.eris Require Import adequacy.
From clutch.eris Require Import weakestpre total_weakestpre total_adequacy primitive_laws proofmode.

Lemma prob_ext {A : Type} `{Countable A} (μ : distr A) (φ ψ : A → bool) :
  (∀ (a : A), (μ a ≠ 0)%R → φ a = ψ a) →
  prob μ φ = prob μ ψ.
Proof.
  move=>ext.
  unfold prob.
  apply SeriesC_ext=>a.
  destruct (decide (μ a = 0)); subst;
    first by destruct (φ a), (ψ a).
  rewrite ext //.
Qed.

Section NonASTDistributionAdequacy.

  Set Default Proof Using "Type*".
  
  Context (μ : distr val).
  Context (μ_impl : expr).
  Local Definition μ_div := (1 - SeriesC μ)%R. 
  Hypothesis (twp_μ_terminate :
               ∀ `{erisGS Σ},
                [[{ ↯ μ_div }]] μ_impl [[{ w, RET w; True }]]
             ).
  Hypothesis (wp_μ_adv_comp :
               ∀ `{erisGS Σ} (ε : R) (D : val → R) L,
                (0 <= ε)%R →
                (∀ (v : val), 0 <= D v <= L)%R →
                SeriesC (λ (v : val), D v * μ v)%R = ε →
                ⊢ {{{ ↯ ε }}} μ_impl {{{ v, RET v; ↯ (D v)}}}
             ).

  
  Definition pmf_sum : R := SeriesC μ.
  
  (* Lemma twp_eq : *)
  (*   ∀ `{erisGS Σ} (v : val), *)
  (*   [[{ ↯ (1 - μ v) }]] μ_impl [[{ RET v; True }]]. *)
  (* Proof. *)
  (*   iIntros (Σ erisGS0 v Φ) "Herr HΦ". *)
  (*   iPoseProof ("HΦ" with "[$]") as "HΦ". *)
  (*   wp_apply (twp_μ_terminate with "Herr"). *)
  (*   by iIntros (?) "->". *)
  (* Qed. *)

  Lemma twp_neq :
    ∀ `{erisGS Σ} (v : val),
    {{{ ↯ (μ v) }}} μ_impl {{{ w, RET w; ⌜v ≠ w⌝ }}}.
  Proof.
    iIntros (Σ erisGS0 v Φ) "Herr HΦ".
    set (D w := if bool_decide (v = w) then 1%R else 0%R).
    wp_apply (wp_μ_adv_comp (μ v) D with "Herr").
    { apply pmf_pos. }
    { move=>w.
      instantiate (1:=1%R).
      unfold D.
      case_bool_decide;
        lra.
    }
    { rewrite (SeriesC_ext _ (λ (w : val), if bool_decide (w = v) then μ v else 0)%R); last first.
      { move=>w.
        unfold D.
        do 2 case_bool_decide;
        subst;
        try done;
        lra.
      }
      apply SeriesC_singleton.
    }
    unfold D.
    iIntros (w) "Herr".
    case_bool_decide; subst.
    { iDestruct (ec_contradict with "Herr") as "[]". reflexivity. }
    by iApply "HΦ".
  Qed.

  Lemma μ_tgl : ∀ `{erisGpreS Σ} (σ : state),
    (SeriesC μ <= SeriesC (lim_exec (μ_impl, σ)))%R.
  Proof.
    iIntros (Σ erisGpreS0 σ).
    epose proof (@twp_tgl Σ erisGpreS0 μ_impl σ μ_div (λ _, True) _ _) as H.
    Unshelve.
    2: { rewrite /μ_div.
         pose proof pmf_SeriesC μ.
         lra. 
    }
    2:{ iIntros. by iApply (twp_μ_terminate with "[$]"). }
    unfold tgl, prob in H.
    replace (1-μ_div)%R with (SeriesC μ) in H; last (unfold μ_div; lra).
    etrans; first apply: H.
    right.
    apply SeriesC_ext. intros. by case_bool_decide.
  Qed. 

  (* Lemma μ_tgl : ∀ `{erisGpreS Σ} (σ : state) (v : val), *)
  (*   tgl (lim_exec (μ_impl, σ)) (λ w, v = w) (1 - μ v). *)
  (* Proof. *)
  (*   iIntros (Σ erisGpreS0 σ v). *)
  (*   move=>[:pmf_sum_minus_pos]. *)
  (*   apply (@twp_tgl Σ erisGpreS0). *)
  (*   { abstract: pmf_sum_minus_pos. apply Rle_0_le_minus. apply pmf_le_1. } *)
  (*   (* { abstract: pmf_sum_minus_pos. *) *)
  (* (*        apply Rplus_le_le_0_compat.  *) *)
  (* (*        - apply Rle_0_le_minus, pmf_le_SeriesC.  *) *)
  (* (*        - apply Rle_0_le_minus, pmf_SeriesC. } *) *)
  (*   iIntros (erisGS0) "Herr". *)
  (*   by wp_apply (twp_eq v with "Herr"). *)
  (* Qed. *)

  Lemma μ_pgl : ∀ `{erisGpreS Σ} (σ : state) (v : val),
    pgl (lim_exec (μ_impl, σ)) (λ w, v ≠ w) (μ v).
  Proof.
    iIntros (Σ erisGpreS0 σ v).
    apply (@wp_pgl_lim Σ erisGpreS0); [done |].
    iIntros (erisGS0) "Herr".
    by wp_apply (twp_neq with "Herr") as (w) "$".
  Qed.

  Lemma pmf_sum_μ_div :
    (pmf_sum + μ_div = 1)%R.
  Proof. 
    unfold pmf_sum, μ_div. lra.
  Qed. 
 
  Lemma μ_impl_is_μ :
    ∀ `{erisGpreS Σ} (σ : state) (v : val),
    prob (lim_exec (μ_impl, σ)) (λ w, bool_decide (v = w)) = μ v.
  Proof.
    move=>Σ erisGpreS0 σ v.
    specialize (μ_tgl σ) as μ_tgl0.
    specialize (μ_pgl σ) as μ_pgl0.
    
    (* unfold tgl in μ_tgl0. *)
    unfold pgl in μ_pgl0.
    assert (∀ v : val,
      (prob (lim_exec (μ_impl, σ))
         (λ w, bool_decide (v = w)) <=
       μ v)%R
           ) as μ_pgl1.
    { intros. etrans; last eapply μ_pgl0.
      rewrite /prob.
      right.
      apply SeriesC_ext.
      intros. do 2 case_bool_decide; naive_solver.
    }
    apply Rle_antisym; first done.
    apply Rnot_gt_le.
    intros Hcontra. apply Rgt_lt in Hcontra.
    assert (SeriesC (lim_exec (μ_impl, σ))< SeriesC μ)%R; last lra.
    apply SeriesC_lt.
    - intros. split; first done.
      etrans; last apply μ_pgl1.
      rewrite /prob.
      erewrite (SeriesC_ext _ (λ a : mstate_ret (lang_markov prob_lang),
        if bool_decide (a = n)
        then lim_exec (μ_impl, σ) a
        else 0))%R; last (intros; do 2 case_bool_decide; naive_solver).
      by rewrite SeriesC_singleton_dependent.
    - exists v. unfold prob in Hcontra.
      erewrite (SeriesC_ext _ (λ a : mstate_ret (lang_markov prob_lang),
        if bool_decide (a = v)
        then lim_exec (μ_impl, σ) a
        else 0))%R in Hcontra; last (intros; do 2 case_bool_decide; naive_solver).
      by rewrite SeriesC_singleton_dependent in Hcontra.
    - done.
  Qed. 
End NonASTDistributionAdequacy.

From Coq Require Import Reals Psatz.
From stdpp Require Export binders strings.
From stdpp Require Import gmap fin_maps countable fin.
From iris.algebra Require Export ofe.
From clutch.prelude Require Export stdpp_ext.
From clutch.common Require Export language ectx_language ectxi_language.
From clutch.prob_lang Require Export locations lang.
From iris.prelude Require Import options.
From clutch.prob Require Export distribution.

Set Default Proof Using "Type*".
Local Open Scope R.

Section rejection_sampler_distr.
  Fixpoint rej_samp_distr_f (N:nat) (s:gset (fin(S N))) (l:list (fin (S N))) :=
    match l with
    | [] => 0
    | x::xs => if bool_decide(xs = [])
             then (if bool_decide(x ∈ s) then size (s)/S N else 0)
             else (if bool_decide(x ∈ s) then 0 else (S N-size s)/S N*rej_samp_distr_f N s xs)
    end.

  Local Hint Resolve pos_INR:core.
  Local Hint Resolve pos_INR_S: core.
  Lemma rej_samp_distr_f_nonneg (N:nat) s l: 0<= rej_samp_distr_f N s l.
  Proof.
    induction l; simpl; first done.
    repeat case_bool_decide; try done.
    all: rewrite -/(INR (S _)).
    - apply Rcomplements.Rdiv_le_0_compat; auto.
    - apply Rmult_le_pos; auto. apply Rcomplements.Rdiv_le_0_compat; auto.
      apply Rle_0_le_minus.
      apply le_INR.
      etrans; first eapply subseteq_size.
      + instantiate (1:=list_to_set (fin_enum (S N))).
        intros ??. rewrite elem_of_list_to_set.
        replace (fin_enum _) with (enum (fin (S N))) by done.
        apply elem_of_enum.
      + replace (fin_enum _) with (enum (fin (S N))) by done.
        rewrite size_list_to_set; last apply NoDup_enum.
        rewrite fin.length_enum_fin. done.
  Qed.

  Lemma rej_samp_distr_f_emptyset (N:nat) : is_seriesC (rej_samp_distr_f N ∅) 0.
  Proof.
  Admitted.

  Lemma rej_samp_distr_f_is_seriesC (N:nat) s: s≠∅ -> is_seriesC (rej_samp_distr_f N s) 1.
  Proof.
  Admitted.
  
  Lemma rej_samp_distr_f_ex_seriesC (N:nat) s: ex_seriesC (rej_samp_distr_f N s).
  Proof.
    rewrite /rej_samp_distr_f.
    destruct (decide (s=∅)); eexists _.
    - subst. apply rej_samp_distr_f_emptyset.
    - by apply rej_samp_distr_f_is_seriesC.
  Qed.
  
  Lemma rej_samp_distr_f_le_1 (N:nat) s: SeriesC (rej_samp_distr_f N s) <=1.
  Proof.
    destruct (decide(s=∅)).
    - trans 0; last lra.  
      apply Req_le_sym.
      symmetry.
      apply is_seriesC_unique.
      subst.
      apply rej_samp_distr_f_emptyset .
    - apply Req_le_sym.
      symmetry.
      apply is_seriesC_unique.
      apply rej_samp_distr_f_is_seriesC. done.
  Qed.
  
  Program Definition rej_samp_distr (N:nat) (s:gset (fin(S N))) :=
    MkDistr (rej_samp_distr_f N s) _ _ _.
  Next Obligation.
    apply rej_samp_distr_f_nonneg.
    Qed.
  Next Obligation.
    apply rej_samp_distr_f_ex_seriesC.
  Qed.
  Next Obligation.
    apply rej_samp_distr_f_le_1.
  Qed.

  Definition rej_samp_state_f σ α N (ns: list (fin (S N))) (Hfound:(σ.(tapes)!!α = Some (N;ns))) :=
    (λ l,
       state_upd_tapes <[α := (N; ns ++ l)]> σ).

  Definition rej_samp_state_distr N σ α s (ns : list (fin (S N))) (Hfound:(σ.(tapes)!!α = Some (N;ns))) :=
    rej_samp_distr N s ≫= (λ l, dret (rej_samp_state_f σ α N ns Hfound l)).
  
    
End rejection_sampler_distr.

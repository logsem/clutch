(* FIXME stop being such a hoarder *)
From clutch.app_rel_logic Require Export app_weakestpre primitive_laws.
From clutch.ub_logic Require Export ub_clutch.

(* Require Import clutch.ub_logic.ub_clutch.
From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext.
From clutch.app_rel_logic Require Import lifting ectx_lifting.
From clutch.prob_lang Require Import lang notation tactics metatheory.
From clutch.rel_logic Require Export spec_ra.
*)

Set Default Proof Using "Type*".

(* equivalence between the control flow in the bounded rejection sampler,
   and the unbounded rejection sampler with error credits *)

Context (PRED_MAX_VALUE: nat).
Definition MAX_VALUE: nat := S PRED_MAX_VALUE.

Section proofs.
  Local Open Scope R.
  Context `{!clutchGS Σ}.

  (** tapes
  Definition tapeN ns : tape := (PRED_MAX_VALUE; ns).
  Definition nat_tape l ns : iProp Σ := l ↪ tapeN ns.
  Notation "l ↪N ns" := (nat_tape l ns) (at level 20, format "l  ↪N  ns") : bi_scope.
   *)

  (* None when the sampler is in a bad case, SOME #() when in good case *)
  Definition bdd_cf_rejection_sampler (n m : nat) : val :=
    λ: "depth",
      (* let: "𝛽" := alloc #m in *)
      let: "do_sample" :=
        (rec: "f" "tries_left" :=
           if: ("tries_left" - #1) < #0
            then NONE
            else let: "next_sample" := (rand #m from #()) in
                if: (BinOp LtOp "next_sample" #n)
                then SOME #()
                else "f" ("tries_left" - #1))
      in "do_sample" "depth".

  (* rejection sampler control flow *)
  Definition ubdd_cf_rejection_sampler (n m : nat) : val :=
    λ: "_",
      (* let: "𝛽" := alloc #m in *)
      let: "do_sample" :=
        (rec: "f" "_" :=
           let: "next_sample" := (rand #m from #()) in
           if: (BinOp LtOp "next_sample" #n)
            then SOME #()
            else "f" #())
      in "do_sample" #().

  (* PROBLEM 1: can we prove that unbounded_rejection_samlper_cf always returns Some #()? *)
  Definition ubdd_cf_safe (n m : nat) E :
    {{{ True }}} ubdd_cf_rejection_sampler  n m #() @ E {{{ v, RET v ; ⌜ v = SOMEV #()⌝ }}}.
  Proof.
    iIntros (Φ) "_ HΦ". rewrite /ubdd_cf_rejection_sampler.
    (* when we add tapes, why does wp_alloc_tape work? Why can we combine rules from the UB and rel logic? *)
    (* are they two different logics? are they extensions of the same logic? *)
    (* wp_apply wp_alloc_tape; [done|]; iIntros (𝛽) "H𝛽". *)
    do 4 wp_pure.
    iLöb as "IH"; wp_pures.

    (* this is a regular lob induction proof, we never need to spend any error credits *)
    wp_apply wp_rand; [done|]; iIntros (n0) "_".
    wp_pures.
    case_bool_decide.
    - wp_pures; by iApply "HΦ".
    - wp_pure; by wp_apply ("IH" with "HΦ").
  Qed.

  (* PROBLEM 2: prove that bounded_rejection_samlper_cf returns Some #() with error *)

  Print nat.

  Fixpoint nnreal_nat_exp (r : nonnegreal) (n : nat) : nonnegreal :=
    match n with
    | O    => nnreal_one
    | S n' => nnreal_mult r (nnreal_nat_exp r n')
    end.

  Definition err_factor n m := (nnreal_div (nnreal_nat (m - n)%nat) (nnreal_nat (S m)%nat)).

  Lemma err_factor_lt1 n m : err_factor n m < 1.
  Proof. Admitted.

  (* error for the bounded sampler at a given depth *)
  Definition bdd_cf_error n m depth := nnreal_nat_exp (err_factor n m) depth.

  (* for proofs which iterate to the very end
     ie, doing 0 samples requires error tolerance of 1
   *)
  Lemma bdd_cd_error_final n m : bdd_cf_error n m 0 = nnreal_one.
  Proof. by rewrite /bdd_cf_error /nnreal_nat_exp. Qed.

  (* for proofs which iterate up until the last sample
     ie, a rejection sampler to exclude the final recursive step *)
  Lemma bdd_cd_error_penultimate n m : bdd_cf_error n m 1 = err_factor n m.
  Proof. rewrite /bdd_cf_error /nnreal_nat_exp. (* nnreal: _ * 1 = _ *) Admitted.

  (* how much mass to give to each possibility *)
  Definition bdd_cf_sampling_error n m 𝜀₁ : (fin (S m)) -> nonnegreal
    := fun sample =>
         if (sample <? n)%nat
            (* good case: needs no error *)
            then nnreal_zero
            (* recursive case: splits the total mass*)
            else (nnreal_div 𝜀₁ (err_factor n m)).

  (* simplify the accumulated error at a given step *)
  Lemma simplify_accum_err (n m d': nat) (s : fin (S m))  :
    (s <? n)%nat = false -> bdd_cf_sampling_error n m (bdd_cf_error n m (S d')) s = (bdd_cf_error n m d' ).
  Proof.
    intros Hcase.
    rewrite /bdd_cf_sampling_error Hcase /bdd_cf_error {1}/nnreal_nat_exp -/nnreal_nat_exp.
    remember (err_factor n m) as X.
    remember (nnreal_nat_exp X d') as Y.
    (* nnreal: X * Y  / X = Y *)
  Admitted.


  (* each sample is <= 1 provided d > 1 (and the total mass is chosed appropriately) *)
  Lemma sample_err_wf n m d (s : fin (S m)) : bdd_cf_sampling_error n m (bdd_cf_error n m (S d)) s <= 1.
  Proof.
    (* it is either 1, or epsilon times something at most 1 *)
    rewrite /bdd_cf_sampling_error.
    remember (s <? n)%nat as H.
    destruct H.
    - admit. (* nnreal: 0 < 1 *)
    - rewrite /bdd_cf_error.
      (* nnreal: this is true because we can pull out a factor from the exponent, and the remainder is
         a natural power of a number less than 1. *)
      admit.
  Admitted.

  (* mean mass is preserved *)
  Lemma sample_err_mean n m 𝜀₁ :
    SeriesC (λ s : fin (S m), 1 / S m * bdd_cf_sampling_error n m 𝜀₁ s) = 𝜀₁.
  Proof.
    rewrite /bdd_cf_sampling_error /err_factor.
    (* split the sum into the elements less than n and those greater *)
    (* sum of constant zero is zero *)
    (* after simplification, the other sum has m-n elements at constant (𝜀₁/m-n) *)
  Admitted.



  (* no induction: just see if I can correctly use wp_couple_rand_adv_comp to increase the amount of credit *)
  Definition bdd_cf_approx_safe_example (n m depth : nat) (Hnm : n <= m) E :
    (depth = 3%nat) ->
    {{{ € (bdd_cf_error n m depth) }}} bdd_cf_rejection_sampler n m #depth @ E {{{ v, RET v ; ⌜ v = SOMEV #() ⌝ }}}.
  Proof.
    iIntros (-> Φ) "Hcr HΦ"; rewrite /bdd_cf_rejection_sampler.
    wp_pures.

    (* FIXME somewhere in here is shelves some goals, don't do that. *)

    (* depth=3 sample *)
    wp_apply (wp_couple_rand_adv_comp _ _ _ _ _ (bdd_cf_sampling_error _ _ _) with "Hcr"); [apply sample_err_wf|apply sample_err_mean|].
    iIntros (sample) "Hcr".
    wp_pures.
    case_bool_decide; wp_pures; first by iApply "HΦ".
    rewrite (simplify_accum_err _); last (apply Nat.ltb_nlt; rewrite /not; intro H'; by apply Nat2Z.inj_lt in H').

    (* depth=2 sample *)
    wp_apply (wp_couple_rand_adv_comp _ _ _ _ _ (bdd_cf_sampling_error _ _ _) with "Hcr"); [apply sample_err_wf|apply sample_err_mean|].
    iIntros (sample') "Hcr".
    wp_pures.
    case_bool_decide; wp_pures; first by iApply "HΦ".
    rewrite (simplify_accum_err _); last (apply Nat.ltb_nlt; rewrite /not; intro H'; by apply Nat2Z.inj_lt in H').


    (* depth=1 sample *)
    rewrite bdd_cd_error_penultimate.

    wp_apply (wp_rand_err_list_nat _ m (seq n (m - n))).
    iSplitL "Hcr".
    - (* yeesh *)
      rewrite /err_factor.
      replace (length (seq _ _)) with (m - n)%nat by (symmetry; apply seq_length).
      replace (S m) with (m + 1)%nat by lia.
      done.
    - iIntros (sample'') "%Hsample''".
      wp_pures.
      case_bool_decide; wp_pures.
      + iApply "HΦ". auto.
      + exfalso; apply H1.
        remember (sample'' <? n)%nat as P.
        destruct P.
        * apply inj_lt; apply Nat.ltb_lt; done.
        * (* I don't know if that made it any easier lol *)
          (* anyways, it's true, but I think the rand_err_list_nat needs to be strengthened
             since we lost the fact that sample'' : fin (S m) along the way *)
          admit.
  Admitted.



  Definition bdd_cf_approx_safe (n m depth: nat) (Hnm : n <= m) E :
    {{{ € (bdd_cf_error n m depth Hnm) }}} bdd_cf_rejection_sampler n m #depth @ E {{{ v, RET v ; ⌜ v = SOMEV #() ⌝ }}}.
  Proof.
    iIntros (Φ) "Hcr HΦ"; rewrite /bdd_cf_rejection_sampler.
    do 4 wp_pure.
    (* invariant: (bdd_cf_error n m depth Hnm) *  ??? = ??? *)
    iLöb as "IH".
  Admitted.



End proofs.


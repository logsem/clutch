From clutch.eris Require Import eris tutorial.eris_rules.
From clutch.eris.tutorial Require Import eris_rules.

(* ###################################################################### *)
(** * Geometric distribution *)

Section geometric_total.
  Context `{!erisGS Σ}.

  (** Before, we have mentioned that we are working with a partial correctness
       version of Eris. That is, we consider non-termination as a valid
       behavior. In particular a diverging program satisfies any specification.
       Let's show this more concretely *)

  Definition loop : val :=
    rec: "loop" "n" := if: rand #0 = #0 then "loop" "n" else #42.


  Lemma loop_false :
    {{{ True }}} loop #() {{{ m, RET #m; False }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    iLöb as "IH".
    (** There is a later modality in front of our IH *)
    (** Let's take a single execution step *)
    unfold loop.
    wp_pure.
    (** Two things have happened. First, the program has taken an execution
        Second, the ▷ in front of our IH has been removed.
        We continue the execution *)
    wp_apply (wp_rand_nat); auto.
    iIntros (n) "%Hn".
    inversion Hn; [|nat_solver].
    do 2 wp_pure.
    (** We now apply the IH and conclude *)
    iApply "IH".
    iModIntro.
    iApply "HΦ".
  Qed.


  (** Eris defines a second version of the logic to reason about total correctness.
      In this case, divergence is considered an erroneous behavior.

      Triples for total correctness use the syntax

             [[{ P }]] e [[{ v, RET #v; Q }]]

      Total correctness triples have a different soundness result. Suppose we
      prove
             [[{ ↯ ε }]] e [[{ v, RET #v; Q }]]

      Then, the probability that the program diverges or terminates in a value v
      that does not satisfy Q is at most [ε]. In other words, with probability
      at least 1-ε, [e] will terminate in a result that satisfies Q. In
      particular,

             [[{ True }]] e [[{ v, RET #v; Q }]]

      implies that the program terminates with probability 1, and all possible
      results satisfy Q.

      Let us now try to prove the specification above with a total triple, and
      show what happenens
   *)


  Lemma loop_false_total :
    [[{ True }]] loop #() [[{ m, RET #m; False }]].
  Proof.
    iIntros (Φ) "_ HΦ".
    (** Total correcntness triples unfold into a total correctness WP, which is
        indicated with the square brackets [{ }] in the postcondition *)
    iLöb as "IH".
    (** So far everything looks the same. Let's step our program  *)
    unfold loop.
    wp_pures.
    (** Note now that the ▷ is still in front of the IH *)
    (** Let's continue the proof *)
    (** Eris lemmas sampling in the total correctness version of
        the logic are analogous, and have the same name, with thei
        prefix twp *)
    wp_apply (twp_rand_nat); auto.
    iIntros (n) "%Hn".
    inversion Hn; [|nat_solver].
    do 2 wp_pure.
    (** We would now like to use the IH. However, the ▷ in front of it
        prevents us from using it. In fact, we cannot finish this proof *)
    Fail iApply "IH".
  Abort.

  (** Recall the definition of the geometric process *)

  Definition geometric : val :=
    rec: "geo" "n" :=
      if: rand #2 <= #0 then #0 else "geo" "n" + #1.

  (** Let's now show that it terminates with probability 1, and when it
      does it returns a non-negative number. We will first try the proof
      technique we used in the partial correctness version, although by
      now it should be clear that it will not work *)

  Lemma geo_nonneg_fail :
    [[{ True }]] geometric #() [[{ m, RET #m; ⌜0 ≤ m⌝%Z }]].
  Proof.
    iLöb as "IH".
    iIntros (Φ) "_ HΦ".
    wp_lam.
    wp_apply twp_rand_nat; auto.
    iIntros (n) "%Hn".
    destruct n.
    - wp_pures.
      iModIntro.
      by iApply ("HΦ").
    - do 2 wp_pure.
      wp_bind (geometric #()).
      (** We are now unable to use the IH *)
      Fail iApply "IH".
  Abort.

  (** One now might wonder how to prove the specification above. In the
      determinstic setting, we can use some form of induction on the argument of
      a recursive function to prove that it terminates, but [geometric] does not
      have an argument, and it is not clear what to induct on.

      Eris introduces a new kind of induction we call "error induction". Namely,
      we can induct on the amount of error credits we own. In it simplest form,
      the rule looks like:

         ⌜ 0 < ε ⌝ ∗ ⌜ ε < ε' ⌝ ∗ (↯ ε' -∗ P) ∗ ↯ ε ⊢ P
        ---------------------------------------------------
                              ↯ ε ⊢ P

      Let's explain this step by step. Suppose we own [↯ ε] for a strictly
      positive [ε], and we are trying to prove P. Then it is sound to choose
      another [ε'] such that [ε < ε'], and assume that (↯ ε' -∗ P). One can think of
      this as an inductive hypothesis that is "guarded" by some amount of error
      credits, in a similar manner as our inductive hypothesis from [iLöb] was
      guarded by ▷. Instead of taking program steps, the way we can get access
      to the hypothesis is by amplifying [ε] into [ε'], which we can do by using the
      sampling rules.
   *)

  (** Let's now try to prove the previous specification again. First let's assume
      that we start by owning some arbitrary but positive amount of error credits
   *)
  Lemma geo_nonneg_pos_err (ε : R) :
    [[{ ⌜0 < ε⌝%R ∗ ↯ ε }]] geometric #() [[{ m, RET #m; ⌜0 ≤ m⌝%Z }]].
  Proof.
    iIntros (Φ) "(%Hε & Herr)".
    (**  Error induction can be used through the rule [ec_induction]. At
         this point, we have to choose ε'. We now from previous examples
         that the inductive hypothesis will be used in the case where
         [rand #1] returns 1, which happens with probability 1/2. By using
         the sampling rules, we can actually get [↯(3/2)*ε] in that branch,
         so let us try that.
     *)
    iRevert (Φ).
    iApply (ec_induction ε ((3/2)*ε)); auto.
    {
      (** We are required to show that the amount of error credits guarding the
          inductive hypothesis is strictly larger than the amount we own *)
      real_solver.
    }
    iIntros "(IH & Herr)".
    iIntros (Φ) "HΦ".
    wp_lam.
    (**  We choose the same error distribution function *)
    set (F (n:nat) := if bool_decide (n=0) then 0%R else ((3/2)*ε)%R).
    wp_apply (twp_rand_exp F 2 with "Herr").
    { intro n.
      unfold F.
      real_solver. }
    { unfold F.
      simpl.
      real_solver. }
    iIntros (n) "[%Hn Herr]".
    unfold F.
    destruct n.
    - (** The case n=0 does not make any recursive call, so we can conclude
          by symbolic execution *)
      wp_pures.
      iModIntro.
      by iApply ("HΦ").
    - do 2 wp_pure.
      (** The case 1 <= n calls #geometric recursively *)
      wp_bind (geometric #()).
      simpl.
      (** Note that now, we have amplified our error credits to [3/2 * ε],
          so we have enough credits to apply IH *)
      iApply ("IH" with "Herr [HΦ]").
      iIntros (m) "%Hm".
      wp_pures.
      iApply "HΦ".
      iPureIntro.
      real_solver.
  Qed.

  (** The specification above assumed initial ownership of a strictly positive
      amount of error credits [↯ε]. By the soundness result for total Hoare
      triples, we get that the probability of returning a non-negative number is
      at least 1-ε. Since ε is arbitrary, we can use a limiting argument to
      conclude that the probability is actually 1. However, this is not entirely
      satisfactory, because this is only proven in the ambient logic (Rocq), and
      outside of Eris. It would be better to be able to write and prove the spec
      entirely within Eris. Fortunately, it is sound in Eris to assume ownership
      of an arbitrary positive amount of error credits whenever we are proving a
      WP (either total or partial). Indeed, the following rules are sound:

         (∀ ε, ⌜ 0 < ε ⌝ ∗ ↯ ε -∗ WP e {{ Φ }}) -∗ WP e {{ Φ }})

         (∀ ε, ⌜ 0 < ε ⌝ ∗ ↯ ε -∗ WP e [{ Φ }]) -∗ WP e [{ Φ }])

      There is a technical side condition that e must not be a value, but this
      is easily discharged.

   *)

  (**  We can use this principle to prove the final spec *)
  Lemma geo_nonneg :
    [[{ True }]] geometric #() [[{ m, RET #m; ⌜0 ≤ m⌝%Z }]].
  Proof.
    iIntros (Φ) "_ HΦ".
    (** A positive amount of error credits can be obtained with [twp_err_pos]  *)
    iApply twp_err_pos; auto.
    iIntros (ε) "%Hε Herr".
    (** We can now use the specification proven above *)
    iApply (geo_nonneg_pos_err with "[$Herr]"); auto.
  Qed.


  (** Correctness of geometric sampler *)

  Lemma geo_correct (F : nat -> R):
    (forall n, 0 <= F n <= 1)%R ->
    [[{ ↯ (SeriesC (λ n, (1/3)*(2/3)^n*(F n)))%R }]]
      geometric #()
      [[{ m, RET #m; ↯(F m) }]].
  Proof.
    iIntros (HF Φ) "Herr HΦ".
    iApply twp_err_pos; auto.
    iIntros (ε) "%Hε Herr2".
    iRevert (Φ F HF) "Herr HΦ".
    iApply (ec_induction ε ((3/2)*ε)); auto.
    {
      real_solver.
    }
    iIntros "(IH & Herr2)".
    iIntros (Φ F HF) "Herr HΦ".
    rewrite /geometric.
    iPoseProof (ec_combine with "[$Herr $Herr2]") as "Herr".
    wp_pures.
    set G := (λ n, if bool_decide (n = 0)
                   then F(0)
                   else ((3/2)*(SeriesC (λ k, 1 / 3 * (2 / 3) ^ (S k) * F (S k)) + ε))%R
             ).
    wp_apply (twp_rand_exp G 2 with "Herr").
    { unfold G.
      intros n.
      series.
      apply Rplus_le_le_0_compat; [|real_solver].
      series.
      apply pow_le.
      real_solver.
    }
    { unfold G.
      simpl.
      rewrite Rplus_0_r.
      assert (forall (x: R), 3 / 2 * x + 3 / 2 * x = 3 * x)%R as Haux;
       [intros; lra |].
      rewrite Haux.
      rewrite (SeriesC_split_first (λ n : nat, 1 / 3 * (2 / 3) ^ n * F n)%R);
             first last.
      - setoid_rewrite Rmult_assoc.
        apply ex_seriesC_scal_l.
        apply (ex_seriesC_le _ (λ x : nat, ((2 / 3) ^ x)%R)).
        + intros n; split.
          * apply Rmult_le_pos; [|real_solver].
            apply pow_le; real_solver.
          * rewrite <- (Rmult_1_r ((2 / 3) ^ n)%R) at 2.
            apply Rmult_le_compat_l; [|real_solver].
            apply pow_le; real_solver.
        + rewrite <- ex_seriesC_nat.
          apply Series.ex_series_geom.
          apply Rabs_def1; real_solver.
      - intros m.
        apply Rmult_le_pos; [|real_solver].
        apply Rmult_le_pos; [real_solver|].
        apply pow_le; real_solver.
      - rewrite Rmult_plus_distr_l.
        rewrite Rmult_plus_distr_l.
        rewrite Rmult_plus_distr_l.
        rewrite Rplus_assoc.
        apply Rplus_le_compat; [real_solver|].
        apply Rplus_le_compat; [|real_solver].
        replace (1+1+1)%R with 3%R by lra.
        apply Rmult_le_compat_l; [real_solver|].
        right.
        apply SeriesC_ext.
        real_solver.
      }
     iIntros (n) "(%Hn & Herr)".
     unfold G.
     destruct n.
     - simpl.
       wp_pures.
       iApply "HΦ".
       auto.
     - simpl.
       rewrite Rmult_plus_distr_l.
       iPoseProof (ec_split with "Herr") as "(Herr1 & Herr2)".
       {
         apply Rmult_le_pos; [real_solver|].
         series.
         apply pow_le.
         real_solver.
       }
       {
         real_solver.
       }
       do 2 wp_pure.
       wp_bind (geometric _).
       iSpecialize ("IH" with "Herr2").

       set H := (λ (n:nat), F (S n)).
       wp_apply ("IH" $! _ H with "[][Herr1]").
       + iPureIntro.
         unfold H.
         real_solver.
       + iApply (ec_eq with "Herr1").
         rewrite <- SeriesC_scal_l.
         apply SeriesC_ext.
         intros k.
         unfold H.
         real_solver.
       + iIntros (m) "Herr".
         wp_pures.
         iModIntro.
         simpl.
         replace (Z.add (Z.of_nat m) (Z.of_nat (S O)))
           with (Z.of_nat (S m)) by lia.
         iApply ("HΦ" with "[Herr]").
         unfold H.
         iFrame.
  Qed.

End geometric_total.

From stdpp Require Import namespaces.
From iris.base_logic Require Import invariants na_invariants.
From self.prob_lang Require Import notation proofmode primitive_laws spec_rules spec_tactics.
From self.logrel Require Import model rel_rules rel_tactics.
From iris.algebra Require Import auth gmap excl frac agree.
From self.prelude Require Import base.


(* This is a library for sampling integers in the set {0, ..., 2^n-1}
   for some natural number n > 0.

   It works by just sampling n individual bits and shifting them to
   form the integer. The sampler is parameterized by a tape to use.
   One can see the bits on the tape as giving a (possibly prefix) of a
   big endian encoding of integers to be sampled.

   Currently we only support using the built-in flip
   () as the primitive for sampling bits, though in principle one
   could paramterize by a function for generating bits.

 *)

Section int.

  (* To use the library, one specifies the bit width n by setting PRED_NUM_BITS to be n - 1.
     This is a cheap way to ensure n > 0 *)
  Context (PRED_NUM_BITS: nat).

  Definition NUM_BITS := S PRED_NUM_BITS.

  Definition MAX_INT := Z.ones (NUM_BITS).

  Definition bool_to_int : val :=
    λ: "b",
      if: "b" = #false then
        #0
      else #1.

  Definition sample_int_aux : val :=
    (rec: "sample_int_aux" "α" "n" :=
        if: "n" = #0 then
          #0
        else
          let: "b" := bool_to_int (flip "α") in
          let: "rest" := "sample_int_aux" "α" ("n" - #1) in
          "b" ≪ ("n" - #1) + "rest").

  Definition sample_int : val :=
    λ: "α", sample_int_aux "α" #NUM_BITS.

  Fixpoint Z_to_bool_list z n : list bool :=
    match n with
    | O => []
    | S n' => (Z.testbit z n') :: (Z_to_bool_list z n')
    end.

  (*
  Compute (Z_to_bool_list 0 5).
  Compute (Z_to_bool_list 3 5).
  Compute (Z_to_bool_list 5 5).
  *)

  Context `{!prelogrelGS Σ}.

  Lemma wp_bool_to_int (b: bool) E :
    {{{ True }}}
      bool_to_int #b @ E
    {{{ RET #(Z.b2z b); True%I}}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite /bool_to_int.
    wp_pures. destruct b; case_bool_decide as Heq; try congruence; wp_pures; by iApply "HΦ".
  Qed.

  Lemma spec_bool_to_int E K (b : bool) :
    ↑specN ⊆ E →
    refines_right K (bool_to_int #b) ={E}=∗
    refines_right K (of_val #(Z.b2z b)).
  Proof.
    rewrite /bool_to_int.
    iIntros (?) "HK".
    tp_pures K; first solve_vals_compare_safe.
    destruct b; case_bool_decide as Heq; try congruence; tp_pures K; eauto.
  Qed.

  Lemma Z_to_bool_list_helper (z : Z) (n' : nat):
    (Z.b2z (Z.testbit z (Z.of_nat n')) ≪ Z.of_nat n' + Z.land z (Z.ones (Z.of_nat n')))%Z =
      Z.land z (Z.ones (Z.of_nat (S n'))).
  Proof.
    rewrite Z.land_ones; last by lia.
    rewrite Z.land_ones; last by lia.

    replace (2 ^ (S n')%Z)%Z with (2^n' * 2)%Z; last first.
    { replace (Z.of_nat (S n')) with (1 + Z.of_nat n')%Z by lia.
      rewrite Z.pow_add_r //; try lia. }
    rewrite Z.rem_mul_r; try lia.
    rewrite Z.add_comm.
    f_equal.
    rewrite Z.shiftl_mul_pow2; last by lia.
    rewrite Z.mul_comm. f_equal.
    apply Z.testbit_spec'; lia.
  Qed.

  Definition int_tape α (zs: list Z) : iProp Σ :=
    ⌜ Forall (λ z, 0 ≤ z < 2 ^ NUM_BITS)%Z zs ⌝ ∗
    α ↪ (flat_map (λ z, Z_to_bool_list z NUM_BITS) zs).

  Definition spec_int_tape α (zs: list Z) : iProp Σ :=
    ⌜ Forall (λ z, 0 ≤ z < 2 ^ NUM_BITS)%Z zs ⌝ ∗
    α ↪ₛ (flat_map (λ z, Z_to_bool_list z NUM_BITS) zs).

  Lemma wp_sample_int_aux E α z n bs :
    (0 ≤ z)%Z →
    {{{ α ↪ (Z_to_bool_list z n ++ bs) }}}
      sample_int_aux (#lbl:α) #n @ E
    {{{ z', RET #z' ; ⌜ z' = Z.land z (Z.ones n) ⌝ ∗ α ↪ bs }}}.
  Proof.
    rewrite /sample_int_aux.
    iInduction n as [| n'] "IH";
    iIntros (Hle Φ) "Hα HΦ".
    - wp_pures. iModIntro. iApply "HΦ". iFrame.
      iPureIntro.
      rewrite Z.land_ones //=. rewrite Z.mod_1_r //.
    - wp_pures. simpl.
      wp_apply (wp_flip with "Hα"); iIntros "Hα".
      wp_apply (wp_bool_to_int with "[//]"); iIntros "_".
      wp_pure _. wp_pure _.
      wp_pure _. replace (Z.of_nat (S n') - 1)%Z with (Z.of_nat n'); last by lia.
      wp_apply ("IH" with "[//] Hα").
      iIntros (z') "(%Heq&Hα)".
      wp_pures.
      iModIntro. iApply "HΦ". iFrame. iPureIntro.
      replace (S n' - 1)%Z with (n' : Z) by lia.
      rewrite Heq.
      apply Z_to_bool_list_helper.
  Qed.

  Lemma spec_sample_int_aux E K α z n bs :
    ↑specN ⊆ E →
    (0 ≤ z)%Z →
    α ↪ₛ (Z_to_bool_list z n ++ bs) -∗
    refines_right K (sample_int_aux (#lbl:α) #n) ={E}=∗ ∃ z', ⌜ z' = Z.land z (Z.ones n) ⌝ ∗
    refines_right K (of_val #z') ∗ α ↪ₛ bs.
  Proof.
    intros HE Hle.
    iInduction n as [| n'] "IH" forall (K); rewrite /sample_int_aux; iIntros "Hα HK".
    - tp_pures K; first solve_vals_compare_safe. rewrite Z.land_ones //= Z.mod_1_r //.
      iExists _; eauto with iFrame.
    - tp_pures K; first solve_vals_compare_safe. simpl.
      tp_flip K.
      tp_bind K (bool_to_int _).
      rewrite refines_right_bind.
      iMod (spec_bool_to_int with "[$]") as "HK"; first done.
      rewrite -refines_right_bind /=.
      tp_pure K _. tp_pure K _.
      tp_pure K _.
      rewrite -/sample_int_aux.
      tp_bind K (sample_int_aux _ _).
      replace (Z.of_nat (S n') - 1)%Z with (Z.of_nat n'); last by lia.
      rewrite refines_right_bind.
      iMod ("IH" with "[$] [$]") as (z' Heqz') "(HK&Hα)".
      rewrite -refines_right_bind /=.
      tp_pures K.
      iModIntro. iFrame.
      iExists _. iFrame.
      replace (S n' - 1)%Z with (n' : Z) by lia.
      iPureIntro.
      rewrite Heqz'.
      apply Z_to_bool_list_helper.
  Qed.

  Lemma flat_map_cons {A B: Type} (f: A → list B) (x: A) (l: list A):
    flat_map f (x :: l) = (f x) ++ flat_map f l.
  Proof. rewrite //=. Qed.

  Lemma Zland_ones_small (z: Z) (n : nat):
    (0 ≤ z < 2 ^ n)%Z →
    Z.land z (Z.ones n) = z.
  Proof.
    intros. rewrite Z.land_ones; last lia. apply Z.mod_small. auto.
  Qed.

  Lemma wp_sample_int E α z zs :
    {{{ int_tape α (z :: zs) }}}
      sample_int (#lbl:α) @ E
    {{{ RET #z ; int_tape α zs }}}.
  Proof.
    iIntros (Φ) "Htape HΦ".
    rewrite /sample_int.
    wp_pures.
    iDestruct "Htape" as "(%Hforall&Htape)".
    rewrite flat_map_cons.
    inversion Hforall.
    wp_apply (wp_sample_int_aux with "Htape").
    { lia. }
    iIntros (z') "(%Heq&Hα)".
    rewrite Zland_ones_small in Heq; last auto.
    rewrite Heq.
    iApply "HΦ". iSplit; iFrame. auto.
  Qed.

  Lemma spec_sample_int E K α z zs :
    ↑specN ⊆ E →
    spec_int_tape α (z :: zs) -∗
    refines_right K (sample_int (#lbl:α)) ={E}=∗ refines_right K (of_val #z) ∗ spec_int_tape α zs.
  Proof.
    iIntros (HE) "Htape HK".
    rewrite /sample_int.
    tp_pures K.
    iDestruct "Htape" as "(%Hforall&Htape)".
    rewrite flat_map_cons.
    inversion Hforall.
    iMod (spec_sample_int_aux with "Htape HK") as (z' Heq) "(HK&Hα)"; first done.
    { lia. }
    rewrite Zland_ones_small in Heq; last auto.
    rewrite Heq.
    iFrame. eauto.
  Qed.

End int.

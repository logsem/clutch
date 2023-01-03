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
   One can see the bits on the tape as giving a
   big endian encoding of integers to be sampled (or a partial prefix thereof).

   Currently we only support using the built-in flip as the primitive
   for sampling bits, though in principle one could paramterize by a
   function for generating bits.

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

  Fixpoint bool_list_to_Z (bs : list bool) : Z :=
    match bs with
    | [] => 0
    | b :: bs =>
        Z.shiftl (Z.b2z b) (length bs) + bool_list_to_Z bs
    end.

  Lemma pow2_nonzero: ∀ x, 0 < 2 ^ x.
  Proof.
    intros x. induction x => /=; try lia.
  Qed.

  Lemma bool_list_to_Z_lower_bound bs :
    (0 ≤ bool_list_to_Z bs)%Z.
  Proof.
    induction bs as [| b bs] => //=.
    rewrite Z.shiftl_mul_pow2; last by lia.
    specialize (pow2_nonzero (length bs)).
    destruct b => //=; try lia.
  Qed.

  Lemma bool_list_to_Z_upper_bound bs :
    (bool_list_to_Z bs < 2 ^ length bs)%Z.
  Proof.
    induction bs as [| b bs] => //=.
    rewrite Z.shiftl_mul_pow2; last by lia.
    remember (length bs) as n.
    replace (2 ^ (S n)%Z)%Z with (2^n * 2)%Z; last first.
    { replace (Z.of_nat (S n)) with (1 + Z.of_nat n)%Z by lia.
      rewrite Z.pow_add_r //; try lia. }
    destruct b => //=; try lia.
  Qed.

  Lemma bool_list_to_Z_upper_bound' bs :
    (bool_list_to_Z bs ≤ Z.ones (length bs))%Z.
  Proof.
    specialize (bool_list_to_Z_upper_bound bs).
    rewrite Z.ones_equiv; lia.
  Qed.

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

  Instance b2z_inj :
    Inj eq eq (Z.b2z).
  Proof. intros [|] [|] => //=. Qed.

  Lemma Z_to_bool_list_mod_pow2 z n :
    Z_to_bool_list z n =
    Z_to_bool_list (z `mod` 2^n) n.
  Proof.
    revert z.
    induction n => //= z.
    f_equal; last first.
    { rewrite IHn. rewrite [a in _ = a]IHn.
      f_equal. symmetry.
      replace (2 ^ (S n)%Z)%Z with (2^n * 2)%Z; last first.
      { replace (Z.of_nat (S n)) with (1 + Z.of_nat n)%Z by lia.
        rewrite Z.pow_add_r //; try lia. }
      rewrite Z.rem_mul_r; try lia.
      rewrite Z.mul_comm.
      rewrite Z.mod_add; last by lia.
      rewrite Zmod_mod //.
    }
    symmetry. apply Z.mod_pow2_bits_low; lia.
  Qed.

  Lemma bool_list_to_Z_to_bool_list bs :
    Z_to_bool_list (bool_list_to_Z bs) (length bs) = bs.
  Proof.
    induction bs as [| b bs IH] => //=.
    f_equal.
    - apply (inj Z.b2z).
      rewrite Z.testbit_spec'; last by lia.
      rewrite Z.shiftl_mul_pow2; last by lia.
      specialize (pow2_nonzero (length bs)) => ?.
      rewrite Z.div_add_l; last by lia.
      rewrite Z.div_small; last first.
      { split; auto using bool_list_to_Z_lower_bound, bool_list_to_Z_upper_bound. }
      destruct b => //=.
    - rewrite -[a in _ = a]IH.
      rewrite Z_to_bool_list_mod_pow2. f_equal.
      rewrite Z.shiftl_mul_pow2; last by lia.
      rewrite Z.add_comm Z_mod_plus; last by lia.
      apply Z.mod_small.
      { split; auto using bool_list_to_Z_lower_bound, bool_list_to_Z_upper_bound. }
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

  Lemma flat_map_singleton {A B: Type} (f: A → list B) (x: A) :
    flat_map f [x] = (f x).
  Proof. rewrite /= app_nil_r //. Qed.

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

  Lemma wp_couple_int_tapes_eq E e α αₛ zs zsₛ Φ:
    to_val e = None →
    nclose specN ⊆ E →
    spec_ctx ∗ spec_int_tape αₛ zsₛ ∗ int_tape α zs ∗
    ((∃ z: Z, (⌜ 0 ≤ z ≤ MAX_INT ⌝%Z ∗ spec_int_tape αₛ (zsₛ ++ [z]) ∗ int_tape α (zs ++ [z])))
              -∗ WP e @ E {{ Φ }}) -∗
    WP e @ E {{ Φ }}.
  Proof.
    iIntros (Hnv HN) "(#Hctx&Hαₛ&Hα&Hwp)".
    iDestruct "Hα" as (?) "Hα".
    iDestruct "Hαₛ" as (?) "Hαₛ".
    iApply (wp_couple_tapesN_eq _ (NUM_BITS)); try done.
    iFrame "Hα Hαₛ Hctx".
    iDestruct 1 as (bs Hlen) "(Hαₛ&Hα)".
    iApply "Hwp".

    assert (Hrange: (0 ≤ bool_list_to_Z bs ≤ MAX_INT)%Z).
    { split.
      - apply bool_list_to_Z_lower_bound.
      - rewrite /MAX_INT -Hlen. apply bool_list_to_Z_upper_bound'.
    }
    iExists (bool_list_to_Z bs). iSplit; first done.
    iSplitL "Hαₛ".
    { rewrite /spec_int_tape.
      rewrite ?flat_map_app ?flat_map_singleton.
      iSplit.
      { iPureIntro; apply Forall_app; split; auto. econstructor; eauto.
        rewrite /MAX_INT ?Z.ones_equiv in Hrange. lia. }
      rewrite -Hlen bool_list_to_Z_to_bool_list.
      iFrame.
    }
    { rewrite /int_tape.
      rewrite ?flat_map_app ?flat_map_singleton.
      iSplit.
      { iPureIntro; apply Forall_app; split; auto. econstructor; eauto.
        rewrite /MAX_INT ?Z.ones_equiv in Hrange. lia. }
      rewrite -Hlen bool_list_to_Z_to_bool_list.
      iFrame.
    }
  Qed.

End int.

Section base_conversion.

  Context `{!prelogrelGS Σ}.

  (* A "digit list" is a list of integers encoding a number in base
    2^(n+1), written in big-endian form *)

  Definition wf_digit_list (n : nat) (zs : list Z) :=
    Forall (λ z, 0 ≤ z < 2 ^ (S n))%Z zs.

  Fixpoint digit_list_to_Z (n: nat) (zs : list Z) : Z :=
    match zs with
    | [] => 0
    | z :: zs =>
        (Z.shiftl z (length zs * (S n)) + digit_list_to_Z n zs)%Z
    end.

  Definition testdigit (n : nat) (z: Z) (pos: nat) :=
    Z.land (Z.shiftr z (pos * (S n))) (Z.ones (S n)).

  Fixpoint Z_to_digit_list n z pos : list Z :=
    match pos with
    | O => []
    | S pos' => (testdigit n z pos') :: (Z_to_digit_list n z pos')
    end.

  Lemma ones_shiftr (m k : Z) :
    (k ≤ m)%Z →
    (0 ≤ k)%Z →
    Z.shiftr (Z.ones m) k = Z.ones (m - k)%Z.
  Proof.
    intros Hle1 Hle2.
    rewrite ?Z.shiftr_div_pow2; try lia.
    rewrite Z.ones_div_pow2; lia.
  Qed.

  Lemma Z_land_ones_min (z1 z2: Z) :
    (0 ≤ z1)%Z ->
    (0 ≤ z2)%Z ->
    Z.land (Z.ones z1) (Z.ones z2) = Z.ones (Z.min z1 z2).
  Proof.
    intros Hle1 Hle2.
    apply Z.bits_inj.
    intros k. rewrite Z.land_spec.
    rewrite ?Z.testbit_ones; try lia.
  Qed.

  Lemma mod_pow2_digits_low :
    ∀ (w : nat) (a : Z) (n m : nat), (m < n)%nat → testdigit w (a `mod` 2 ^ (S w * n)) m = testdigit w a m.
  Proof.
    intros w a n m Hlt.
    rewrite /testdigit.
    assert ((a `mod` 2 ^ (S w * n) = Z.land a (Z.ones (S w * n))))%Z as ->.
    { rewrite -Z.land_ones; last lia. auto. }
    rewrite Z.shiftr_land.
    rewrite -Z.land_assoc.
    f_equal.
    assert ((S w * n - m * S w) >= S w).
    { rewrite -Nat.mul_comm. ring_simplify.
      transitivity ((S m) * (w + 1) - m * (w + 1)).
      { apply Nat.sub_le_mono_r.
        apply Nat.mul_le_mono_r. lia.
      }
      lia.
    }
    rewrite ones_shiftr; try lia.
    rewrite Z_land_ones_min; try lia.
    { f_equal. lia. }
  Qed.

  Lemma Z_to_digit_list_mod_pow2 w z n :
    Z_to_digit_list w z n =
    Z_to_digit_list w (z `mod` 2^(S w * n)) n.
  Proof.
    revert z.
    induction n => //= z.
    f_equal; last first.
    { rewrite IHn. rewrite [a in _ = a]IHn.
      f_equal. symmetry.
      replace (2 ^ (S w * S n)%Z)%Z with (2^(S w * n) * 2 ^ (S w))%Z; last first.
      { replace (Z.of_nat (S n)) with (1 + Z.of_nat n)%Z by lia.
        rewrite -Z.pow_add_r //; try lia. f_equal. lia. }
      rewrite Z.rem_mul_r; try lia.
      rewrite (Z.mul_comm (2 ^ (S w * n))).
      rewrite Z.mod_add; last by lia.
      rewrite Zmod_mod //.
    }
    symmetry. apply mod_pow2_digits_low; lia.
  Qed.

  Lemma testdigit_spec' w a n :
    testdigit w a n = ((a `div` 2 ^ (n * S w) `mod` 2 ^ S w))%Z.
  Proof.
    rewrite /testdigit.
    rewrite Z.land_ones; last by lia.
    rewrite ?Z.shiftr_div_pow2; try lia.
  Qed.

  Lemma digit_list_to_Z_lower_bound w bs :
    wf_digit_list w bs →
    (0 ≤ digit_list_to_Z w bs)%Z.
  Proof.
    induction bs as [| b bs] => //= Hwf.
    rewrite Z.shiftl_mul_pow2; last by lia.
    specialize (pow2_nonzero (length bs * S w)).
    intros Hnz.
    inversion Hwf. subst.
    unshelve (epose proof (IHbs _)); eauto. lia.
  Qed.

  Lemma digit_list_to_Z_upper_bound w bs :
    wf_digit_list w bs →
    (digit_list_to_Z w bs < 2 ^ (length bs * S w))%Z.
  Proof.
    induction bs as [| b bs] => //= Hwf.
    inversion Hwf; subst.
    rewrite Z.shiftl_mul_pow2; last by lia.
    replace (Z.of_nat (S (length bs))) with (1 + Z.of_nat (length bs))%Z by lia.
    rewrite Z.mul_add_distr_r.
    rewrite Z.mul_1_l.
    rewrite Z.pow_add_r; try lia; [].
    eapply (Z.lt_le_trans _ (b * 2 ^ (length bs * S w) + 1 * 2 ^ (length bs * S w))).
    { unshelve (epose proof (IHbs _)); eauto. lia. }
    rewrite -Z.mul_add_distr_r.
    apply Z.mul_le_mono_nonneg_r; lia.
  Qed.

  Lemma digit_list_to_Z_upper_bound' w bs :
    wf_digit_list w bs →
    (digit_list_to_Z w bs ≤ Z.ones (length bs * S w))%Z.
  Proof.
    intros Hwf.
    specialize (digit_list_to_Z_upper_bound w bs Hwf).
    intros. rewrite Z.ones_equiv. lia.
  Qed.

  Lemma digit_list_to_Z_to_digit_list w bs :
    wf_digit_list w bs →
    Z_to_digit_list w (digit_list_to_Z w bs) (length bs) = bs.
  Proof.
    intros Hwf.
    induction bs as [| b bs IH] => //=.
    inversion Hwf.
    f_equal.
    - rewrite testdigit_spec'.
      rewrite Z.shiftl_mul_pow2; last by lia.
      specialize (pow2_nonzero (length bs * S w)) => ?.
      rewrite Z.div_add_l; last by lia.
      rewrite Z.div_small; last first.
      { split; auto using digit_list_to_Z_lower_bound, digit_list_to_Z_upper_bound. }
      rewrite Z.add_0_r.
      apply Z.mod_small. lia.
    - rewrite -[a in _ = a]IH; auto.
      rewrite Z_to_digit_list_mod_pow2. f_equal.
      rewrite Z.shiftl_mul_pow2; last by lia.
      rewrite (Z.mul_comm (length bs)).
      rewrite Z.add_comm Z_mod_plus; last by lia.
      rewrite Z.mul_comm.
      apply Z.mod_small.
      { split; auto using digit_list_to_Z_lower_bound, digit_list_to_Z_upper_bound.  }
  Qed.

  Lemma int_tape_base_conversion (n nc k: nat) (z : Z) α :
    S n = (S nc) * k →
    int_tape n α [z] -∗
    ∃ (zs: list Z), ⌜ wf_digit_list nc zs ∧ digit_list_to_Z nc zs = z ⌝ ∗ int_tape nc α zs.
  Proof.
    iIntros (Heq) "Htape".
    iDestruct "Htape" as (Hwf) "Hα".
    inversion Hwf; subst.
    rewrite flat_map_singleton.
    iExists (Z_to_digit_list nc z k).
    iSplit.
    { iPureIntro. admit. }
    rewrite /int_tape.
  Abort.

End base_conversion.

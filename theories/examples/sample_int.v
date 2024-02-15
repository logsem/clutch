From clutch Require Export clutch lib.flip lib.conversion.

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

(* TODO: should this be adopted to make use of the new [rand n] primitive?  *)
Section int.

  (* To use the library, one specifies the bit width n by setting PRED_NUM_BITS to be n - 1.
     This is a cheap way to ensure n > 0 *)
  Context (PRED_NUM_BITS: nat).

  Definition NUM_BITS := S PRED_NUM_BITS.

  Definition MAX_INT := Z.ones (NUM_BITS).

  Definition sample_int_aux : val :=
    (rec: "sample_int_aux" "α" "n" :=
        if: "n" = #0 then
          #0
        else
          let: "b" := bool_to_int (flipL "α") in
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

  Context `{!clutchRGS Σ}.

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
    α ↪B (flat_map (λ z, Z_to_bool_list z NUM_BITS) zs).

  Definition spec_int_tape α (zs: list Z) : iProp Σ :=
    ⌜ Forall (λ z, 0 ≤ z < 2 ^ NUM_BITS)%Z zs ⌝ ∗
    α ↪ₛB (flat_map (λ z, Z_to_bool_list z NUM_BITS) zs).

  Lemma wp_sample_int_aux E α z n bs :
    (0 ≤ z)%Z →
    {{{ α ↪B (Z_to_bool_list z n ++ bs) }}}
      sample_int_aux (#lbl:α) #n @ E
    {{{ z', RET #z' ; ⌜ z' = Z.land z (Z.ones n) ⌝ ∗ α ↪B bs }}}.
  Proof.
    rewrite /sample_int_aux.
    iInduction n as [| n'] "IH";
    iIntros (Hle Φ) "Hα HΦ".
    - wp_pures. iModIntro. iApply "HΦ". iFrame.
      iPureIntro.
      rewrite Z.land_ones //=. rewrite Z.mod_1_r //.
    - wp_pures. simpl.
      wp_apply (wp_flipL with "Hα"); iIntros "Hα".
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
    α ↪ₛB (Z_to_bool_list z n ++ bs) -∗
    refines_right K (sample_int_aux (#lbl:α) #n) ={E}=∗ ∃ z', ⌜ z' = Z.land z (Z.ones n) ⌝ ∗
    refines_right K (of_val #z') ∗ α ↪ₛB bs.
  Proof.
    intros HE Hle.
    iInduction n as [| n'] "IH" forall (K); rewrite /sample_int_aux; iIntros "Hα HK".
    - tp_pures; first solve_vals_compare_safe. rewrite Z.land_ones //= Z.mod_1_r //.
      iExists _; eauto with iFrame.
    - tp_pures; first solve_vals_compare_safe. simpl.
      tp_bind (flipL _ )%E.
      rewrite refines_right_bind.
      iMod (refines_right_flipL with "Hα HK") as "[HK Hα]"; [solve_ndisj|].
      rewrite -refines_right_bind /=.
      tp_bind (bool_to_int _).
      rewrite refines_right_bind.
      iMod (refines_right_bool_to_int with "[$]") as "HK"; first done.
      rewrite -refines_right_bind /=.
      tp_pure. tp_pure.
      tp_pure.
      rewrite -/sample_int_aux.
      tp_bind (sample_int_aux _ _).
      replace (Z.of_nat (S n') - 1)%Z with (Z.of_nat n'); last by lia.
      rewrite refines_right_bind.
      iMod ("IH" with "[$] [$]") as (z' Heqz') "(HK&Hα)".
      rewrite -refines_right_bind /=.
      tp_pures.
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
    tp_pures.
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
    iApply (wp_couple_bool_tapeN_tapeN_eq (NUM_BITS)); try done.
    iFrame "Hα Hαₛ Hctx".
    iIntros (bs) "(%Hlen&Hαₛ&Hα)".
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

  Lemma wp_couple_int_tapesN_eq E e n α αₛ zs zsₛ Φ:
    to_val e = None →
    nclose specN ⊆ E →
    spec_ctx ∗ spec_int_tape αₛ zsₛ ∗ int_tape α zs ∗
    ((∃ zsnew: list Z,
         (⌜ Forall (λ z, 0 ≤ z ≤ MAX_INT) zsnew ⌝%Z ∗ ⌜ length zsnew = n ⌝ ∗
          spec_int_tape αₛ (zsₛ ++ zsnew) ∗ int_tape α (zs ++ zsnew)))
          -∗ WP e @ E {{ Φ }}) -∗
    WP e @ E {{ Φ }}.
  Proof.
    iIntros (Hnv HE).
    iInduction n as [| n] "IH" forall (zsₛ zs).
    { iIntros "(H1&H2&H3&Hwp)". iApply "Hwp". iExists []. rewrite ?app_nil_r; iFrame.
      iPureIntro; eauto. }
    iIntros "(#H1&H2&H3&Hwp)".
    iApply "IH". iFrame "#∗".
    iDestruct 1 as (zsnew Hforall Hlen) "(Hαₛ&Hα)".
    iApply wp_couple_int_tapes_eq; auto. iFrame "#∗".
    iDestruct 1 as (z Hrange) "(H2&H3)".
    iApply "Hwp". iExists (zsnew ++ [z]). rewrite ?app_assoc; iFrame.
    iPureIntro. rewrite ?app_length /=; split; last by lia.
    apply Forall_app; auto.
  Qed.

  Lemma spec_int_tape_intro α :
    α ↪ₛB [] -∗ spec_int_tape α [].
  Proof. iIntros "H". rewrite /spec_int_tape/=. iFrame. eauto. Qed.

  Lemma int_tape_intro α :
    α ↪B [] -∗ int_tape α [].
  Proof. iIntros "H". rewrite /int_tape/=. iFrame. eauto. Qed.

End int.

Section sample_wide.

  Context `{!clutchRGS Σ}.

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
      eapply (Nat.le_trans _ ((S m) * (w + 1) - m * (w + 1))); last first.
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

  Fixpoint digit_list_cmp bs1 bs2 :=
    match bs1, bs2 with
    | [], [] => Eq
    | _, [] => Gt
    | [], _ => Lt
    | b1 :: bs1, b2 :: bs2 =>
        match Z.compare b1 b2 with
        | Lt => Lt
        | Gt => Gt
        | Eq => digit_list_cmp bs1 bs2
        end
    end.

  Lemma digit_list_cmp_spec w bs1 bs2 :
    wf_digit_list w bs1 →
    wf_digit_list w bs2 →
    length bs1 = length bs2 →
    digit_list_cmp bs1 bs2 = Z.compare (digit_list_to_Z w bs1) (digit_list_to_Z w bs2).
  Proof.
    intros Hwf1.
    revert bs2.
    induction bs1 as [| b1 bs1 IH] => bs2 Hwf2 Hlen.
    - destruct bs2 as [| b2 bs2] => //=.
    - destruct bs2 as [| b2 bs2] => //=.
      inversion Hwf1. inversion Hwf2. subst. inversion Hlen as [Hlen']. subst.
      destruct (Z.compare_spec b1 b2) as [Heq|Hlt|Hgt].
      * subst. rewrite IH //.
        rewrite Z.add_compare_mono_l //.
      * symmetry; apply Z.compare_lt_iff.
        rewrite ?Z.shiftl_mul_pow2; try lia.
        inversion Hwf1.
        opose proof (digit_list_to_Z_upper_bound w bs1) as Hub1; eauto.
        opose proof (digit_list_to_Z_upper_bound w bs2) as Hub2; eauto.
        unshelve opose proof (digit_list_to_Z_lower_bound w bs1 _); eauto.
        unshelve opose proof (digit_list_to_Z_lower_bound w bs2 _); eauto.
        subst.
        rewrite -Hlen' in Hub2.
        remember (length bs1 * S w)%Z as k.
        assert (0 ≤ k)%Z by lia.
        eapply (Z.lt_le_trans _ ((b1 + 1) * 2 ^ k + 0)%Z).
        { ring_simplify.
          rewrite (@Z.sub_lt_mono_r _ _ (b1 * 2 ^ k)).
          ring_simplify. auto. }
        { apply Z.add_le_mono; last by lia.
          apply Z.mul_le_mono_nonneg_r; lia. }
      * symmetry; apply Z.compare_gt_iff.
        rewrite ?Z.shiftl_mul_pow2; try lia.
        inversion Hwf1.
        opose proof (digit_list_to_Z_upper_bound w bs1) as Hub1; eauto.
        opose proof (digit_list_to_Z_upper_bound w bs2) as Hub2; eauto.
        opose proof (digit_list_to_Z_lower_bound w bs1 _); eauto.
        opose proof (digit_list_to_Z_lower_bound w bs2 _); eauto.
        subst.
        rewrite -Hlen' in Hub2.
        remember (length bs1 * S w)%Z as k.
        assert (0 ≤ k)%Z by lia.
        eapply (Z.lt_le_trans _ ((b2 + 1) * 2 ^ k + 0)%Z).
        { ring_simplify.
          rewrite (@Z.sub_lt_mono_r _ _ (b2 * 2 ^ k)).
          ring_simplify. auto. }
        { apply Z.add_le_mono; last by lia.
          apply Z.mul_le_mono_nonneg_r; lia. }
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
  Abort.

  Context (PRED_NUM_DIGITS : nat).
  Context (PRED_NUM_DIGIT_BITS : nat).

  Definition NUM_DIGITS := S PRED_NUM_DIGITS.
  Definition NUM_DIGIT_BITS := S PRED_NUM_DIGIT_BITS.

  Definition sample_wide_aux : val :=
    (rec: "sample_wide_aux" "α" "n" :=
        if: "n" = #0 then
          #0
        else
          let: "d" := sample_int PRED_NUM_DIGIT_BITS "α" in
          let: "rest" := "sample_wide_aux" "α" ("n" - #1) in
          "d" ≪ (("n" - #1) * #NUM_DIGIT_BITS) + "rest").

  Definition sample_wide_int : val :=
    λ: "α", sample_wide_aux "α" #NUM_DIGITS.

  Lemma wp_sample_wide_aux E (α : loc) n zs1 zs2 :
    (length zs1 = n) →
    {{{ int_tape PRED_NUM_DIGIT_BITS α (zs1 ++ zs2) }}}
      sample_wide_aux (#lbl:α) #n @ E
    {{{ z, RET #z ; ⌜ z = digit_list_to_Z PRED_NUM_DIGIT_BITS zs1 ⌝ ∗
                      int_tape PRED_NUM_DIGIT_BITS α zs2 }}}.
  Proof.
    rewrite /sample_wide_aux.
    iInduction n as [| n'] "IH" forall (zs1);
    iIntros (Hlength Φ) "Hα HΦ".
    - wp_pures. iModIntro. iApply "HΦ". destruct zs1; inversion Hlength => /=. iFrame.
      eauto.
    - wp_pures.
      destruct zs1 as [| z1 zs1]; first by inversion Hlength.
      iEval (simpl) in "Hα".
      wp_apply (wp_sample_int with "[$]").
      iIntros "Hα".
      wp_pure _. wp_pure _. wp_pure.
      replace (Z.of_nat (S n') - 1)%Z with (Z.of_nat n'); last by lia.
      inversion Hlength.
      wp_apply ("IH" $! _ with "[//] Hα").
      iIntros (z') "(%Heq&Hα)".
      wp_pures.
      iModIntro. iApply "HΦ". iFrame. iPureIntro.
      replace (S (length zs1) - 1)%Z with (length zs1 : Z) by lia.
      rewrite /=/NUM_DIGIT_BITS Heq //.
  Qed.

  Lemma spec_sample_wide_aux K E (α : loc) n zs1 zs2 :
    ↑specN ⊆ E →
    (length zs1 = n) →
    spec_int_tape PRED_NUM_DIGIT_BITS α (zs1 ++ zs2) -∗
    refines_right K (sample_wide_aux (#lbl:α) #n) ={E}=∗
    ∃ z : Z, refines_right K (of_val #z) ∗ ⌜ z = digit_list_to_Z PRED_NUM_DIGIT_BITS zs1 ⌝ ∗
             spec_int_tape PRED_NUM_DIGIT_BITS α zs2.
  Proof.
    iIntros (HE).
    rewrite /sample_wide_aux.
    iInduction n as [| n] "IH" forall (K zs1); iIntros (Hlength) "Hα HK".
    - tp_pures; first solve_vals_compare_safe.
      iModIntro. iExists _. iFrame. destruct zs1; last by inversion Hlength.
      iFrame. eauto.
    - tp_pures; first solve_vals_compare_safe.
      destruct zs1 as [| z1 zs1]; first by inversion Hlength.
      iEval (simpl) in "Hα".
      tp_bind (sample_int _ _)%E.
      rewrite refines_right_bind.
      iMod (spec_sample_int with "[$] [$]") as "(HK&Hα)"; first done.
      rewrite -refines_right_bind /=.
      tp_pure. tp_pure. tp_pure.
      replace (Z.of_nat (S n) - 1)%Z with (Z.of_nat n); last by lia.
      inversion Hlength. subst.
      rewrite -/sample_wide_aux.
      tp_bind (sample_wide_aux _ _).
      rewrite refines_right_bind.
      iMod ("IH" with "[//] Hα HK") as (z') "(HK&%Heq&Hα)".
      rewrite -refines_right_bind/=.
      tp_pures.
      replace (S (length zs1) - 1)%Z with (length zs1 : Z) by lia.
      iModIntro. iExists _. iFrame. rewrite /=/NUM_DIGIT_BITS Heq //.
  Qed.

  Lemma wp_sample_wide_int E (α : loc) zs1 zs2 :
    (length zs1 = NUM_DIGITS) →
    {{{ int_tape PRED_NUM_DIGIT_BITS α (zs1 ++ zs2) }}}
      sample_wide_int (#lbl:α) @ E
    {{{ z, RET #z ; ⌜ z = digit_list_to_Z PRED_NUM_DIGIT_BITS zs1 ⌝ ∗
                      int_tape PRED_NUM_DIGIT_BITS α zs2 }}}.
  Proof.
    rewrite /sample_wide_int.
    iIntros (? Φ) "H HΦ".
    wp_pures.
    wp_apply (wp_sample_wide_aux with "H"); eauto.
  Qed.

  Lemma spec_sample_wide_int K E (α : loc) zs1 zs2 :
    ↑specN ⊆ E →
    (length zs1 = NUM_DIGITS) →
    spec_int_tape PRED_NUM_DIGIT_BITS α (zs1 ++ zs2) -∗
    refines_right K (sample_wide_int (#lbl:α)) ={E}=∗
    ∃ z : Z, refines_right K (of_val #z) ∗ ⌜ z = digit_list_to_Z PRED_NUM_DIGIT_BITS zs1 ⌝ ∗
             spec_int_tape PRED_NUM_DIGIT_BITS α zs2.
  Proof.
    rewrite /sample_wide_int.
    iIntros (? Hlen) "Hα HK".
    tp_pures.
    iMod (spec_sample_wide_aux with "Hα HK"); auto.
  Qed.

End sample_wide.

From clutch.eris Require Export eris adequacy total_adequacy.
From clutch.eris Require Import infinite_tape.
From clutch.eris.examples Require Import lazy_real_programs.
From clutch.eris.examples Require Import lazy_real lazy_real_expr lazy_real_adequacy.
From clutch.eris.examples Require Import math.
From Coquelicot Require Import RInt RInt_gen.
Import Hierarchy.
Set Default Proof Using "Type*".
#[local] Open Scope R.

(** Determine if a presampled bitstring keeps the comparison "in the gap",
    i.e., neither comparison resolves for any of the bits.
    - [cx]: accumulated integer from cached bits (the prefix)
    - [B]:  threshold base
    - [s]:  current shift amount (initially C + n)
    - [bs]: presampled bitstring *)
Fixpoint in_gap (cx : Z) (B s : Z) (bs : list (fin 2)) : bool :=
  match bs with
  | [] => true
  | b :: bs' =>
    let cx' := (2 * cx + Z.of_nat (fin_to_nat b))%Z in
    let cy := Z.shiftr B s in
    negb (cx' + 2 <? cy)%Z && negb (cy + 2 <? cx')%Z && in_gap cx' B (s - 1) bs'
  end.

(** Integer encoded by a bitstring with accumulator (MSB first) *)
Definition bits_to_Z_acc (acc : Z) (bs : list (fin 2)) : Z :=
  fold_left (fun a (b : fin 2) => 2 * a + Z.of_nat (fin_to_nat b))%Z bs acc.

(** Integer encoded by a bitstring (MSB first) *)
Definition bits_to_Z (bs : list (fin 2)) : Z := bits_to_Z_acc 0 bs.

Lemma bits_to_Z_acc_cons acc (b : fin 2) bs :
  bits_to_Z_acc acc (b :: bs) = bits_to_Z_acc (2 * acc + Z.of_nat (fin_to_nat b))%Z bs.
Proof. done. Qed.

Lemma bits_to_Z_acc_shift acc bs :
  bits_to_Z_acc acc bs = (2 ^ Z.of_nat (length bs) * acc + bits_to_Z bs)%Z.
Proof.
  revert acc.
  induction bs as [|b bs' IH]; intros acc.
  - simpl. rewrite /bits_to_Z//=. lia.
  - rewrite bits_to_Z_acc_cons /bits_to_Z bits_to_Z_acc_cons.
    rewrite IH.
    rewrite (IH (Z.of_nat (fin_to_nat b))).
    simpl length. rewrite Nat2Z.inj_succ Z.pow_succ_r; [|lia]. lia.
Qed.

(** in_gap implies the last step's gap condition holds.
    Stated via bits_to_Z_acc which equals the final cx. *)
Lemma in_gap_last_step cx B s b bs' :
  in_gap cx B s (b :: bs') = true →
  let cx_final := bits_to_Z_acc (2 * cx + Z.of_nat (fin_to_nat b))%Z bs' in
  let cy_final := Z.shiftr B (s - Z.of_nat (length bs')) in
  (cy_final - 2 ≤ cx_final ∧ cx_final ≤ cy_final + 2)%Z.
Proof.
  revert cx s b.
  induction bs' as [|b' bs'' IH]; intros cx s b Hgap.
  + simpl in Hgap.
    rewrite andb_true_r in Hgap.
    apply andb_true_iff in Hgap as [H1 H2].
    apply negb_true_iff in H1. apply Z.ltb_nlt in H1.
    apply negb_true_iff in H2. apply Z.ltb_nlt in H2.
    simpl. rewrite Z.sub_0_r. lia.
  + simpl in Hgap.
    apply andb_true_iff in Hgap as [_ Hrest].
    simpl length.
    replace (s - Z.of_nat (S (length bs'')))%Z
      with (s - 1 - Z.of_nat (length bs''))%Z by lia.
    simpl.
    apply (IH (2 * cx + Z.of_nat (fin_to_nat b))%Z (s - 1)%Z b').
    exact Hrest.
Qed.

(** Necessary condition: bits_to_Z is constrained to a 5-element range *)
Lemma in_gap_necessary cx B s b bs' :
  in_gap cx B s (b :: bs') = true →
  let N := Z.of_nat (length (b :: bs')) in
  let cx_final := (2 ^ N * cx + bits_to_Z (b :: bs'))%Z in
  let cy_final := Z.shiftr B (s - Z.of_nat (length bs')) in
  (cy_final - 2 ≤ cx_final ∧ cx_final ≤ cy_final + 2)%Z.
Proof.
  intros Hgap. simpl.
  pose proof (in_gap_last_step cx B s b bs' Hgap) as H.
  simpl in H.
  rewrite /bits_to_Z bits_to_Z_acc_cons.
  rewrite bits_to_Z_acc_shift in H |- *.
  rewrite bits_to_Z_acc_shift.
  rewrite Nat2Z.inj_succ Z.pow_succ_r; [|lia]. lia.
Qed.

(** Range of bits_to_Z *)
Lemma bits_to_Z_range bs :
  (0 ≤ bits_to_Z bs < 2 ^ Z.of_nat (length bs))%Z.
Proof.
  induction bs as [|b bs' IH].
  + rewrite /bits_to_Z /bits_to_Z_acc /=. lia.
  + rewrite /bits_to_Z bits_to_Z_acc_cons bits_to_Z_acc_shift.
    simpl length. rewrite Nat2Z.inj_succ Z.pow_succ_r; [|lia].
    assert (Hb : (0 ≤ Z.of_nat (fin_to_nat b) ≤ 1)%Z).
    { pose proof (fin.fin_to_nat_lt b). lia. }
    nia.
Qed.

(** bits_to_Z is injective on same-length lists *)
Lemma bits_to_Z_inj bs1 bs2 :
  length bs1 = length bs2 →
  bits_to_Z bs1 = bits_to_Z bs2 →
  bs1 = bs2.
Proof.
  revert bs2.
  induction bs1 as [|b1 bs1' IH]; intros [|b2 bs2'] Hlen Heq;
    try discriminate; try done.
  simpl in Hlen. injection Hlen as Hlen.
  rewrite /bits_to_Z !bits_to_Z_acc_cons !bits_to_Z_acc_shift in Heq.
  pose proof (bits_to_Z_range bs1') as [Hr1a Hr1b].
  pose proof (bits_to_Z_range bs2') as [Hr2a Hr2b].
  assert (Hb1 : (0 ≤ Z.of_nat (fin_to_nat b1) ≤ 1)%Z)
    by (pose proof (fin.fin_to_nat_lt b1); lia).
  assert (Hb2 : (0 ≤ Z.of_nat (fin_to_nat b2) ≤ 1)%Z)
    by (pose proof (fin.fin_to_nat_lt b2); lia).
  rewrite Hlen in Heq Hr1b.
  assert (Hbeq : Z.of_nat (fin_to_nat b1) = Z.of_nat (fin_to_nat b2)) by nia.
  assert (Hbseq : bits_to_Z bs1' = bits_to_Z bs2') by nia.
  f_equal.
  + apply fin_to_nat_inj. lia.
  + apply IH; assumption.
Qed.

(** NoDup preserved by map when function is injective on list elements *)
Lemma NoDup_map_inj_on {A B} (f : A → B) (l : list A) :
  NoDup l →
  (∀ x y, x ∈ l → y ∈ l → f x = f y → x = y) →
  NoDup (map f l).
Proof.
  induction l as [|a l' IH]; intros Hnd Hinj.
  + constructor.
  + simpl. constructor.
    * inversion Hnd; subst.
      rewrite elem_of_list_fmap.
      intros [y [Hfy Hy]].
      assert (a = y) by (apply Hinj; [left|right; exact Hy|exact Hfy]).
      subst. contradiction.
    * apply IH.
      { inversion Hnd; assumption. }
      { intros x y Hx Hy. apply Hinj; right; assumption. }
Qed.

(** All elements of enum_uniform_fin_list have the specified length *)
Lemma enum_uniform_fin_list_length_elem N p bs :
  bs ∈ enum_uniform_fin_list N p → length bs = p.
Proof. rewrite elem_of_enum_uniform_fin_list. done. Qed.

(** At most 5 bitstrings of length N are in the gap *)
Lemma in_gap_count cx B s N :
  length (filter (fun bs => in_gap cx B s bs) (enum_uniform_fin_list 1 N)) ≤ 5.
Proof.
  destruct N as [|N'].
  + simpl. lia.
  + set (filtered := filter _ _).
    set (C := (Z.shiftr B (s - Z.of_nat N') - 2 ^ Z.of_nat (S N') * cx)%Z).
    enough (Hsub : map bits_to_Z filtered ⊆+ [C - 2; C - 1; C; C + 1; C + 2]%Z).
    { rewrite -(map_length bits_to_Z filtered).
      apply submseteq_length in Hsub. simpl in Hsub. lia. }
    apply NoDup_submseteq.
    * apply NoDup_map_inj_on.
      { subst filtered. apply NoDup_filter, NoDup_enum_uniform_fin_list. }
      { intros x y Hx Hy Hfxy.
        apply bits_to_Z_inj; [|exact Hfxy].
        subst filtered.
        apply elem_of_list_filter in Hx as [_ Hx].
        apply elem_of_list_filter in Hy as [_ Hy].
        apply enum_uniform_fin_list_length_elem in Hx.
        apply enum_uniform_fin_list_length_elem in Hy.
        lia. }
    * intros z Hz.
      apply elem_of_list_fmap in Hz as [bs [Hzeq Hbs]].
      subst filtered.
      apply elem_of_list_filter in Hbs as [Hgap Helem].
      apply Is_true_eq_true in Hgap.
      apply elem_of_enum_uniform_fin_list in Helem.
      destruct bs as [|b bs']; [discriminate|].
      simpl in Helem. injection Helem as Helem.
      pose proof (in_gap_necessary cx B s b bs' Hgap) as [Hlo Hhi].
      simpl in Hlo, Hhi. rewrite Helem in Hlo, Hhi.
      subst z C.
      (* bits_to_Z (b :: bs') ∈ {C-2, C-1, C, C+1, C+2} where
         C = B ≫ (s - N') - 2^(S N') * cx
         Hlo: C - 2 ≤ bits_to_Z (b :: bs')
         Hhi: bits_to_Z (b :: bs') ≤ C + 2 *)
      assert (Hv : bits_to_Z (b :: bs') = (B ≫ (s - N') - 2 ^ Z.of_nat (S N') * cx - 2)%Z ∨
                   bits_to_Z (b :: bs') = (B ≫ (s - N') - 2 ^ Z.of_nat (S N') * cx - 1)%Z ∨
                   bits_to_Z (b :: bs') = (B ≫ (s - N') - 2 ^ Z.of_nat (S N') * cx)%Z ∨
                   bits_to_Z (b :: bs') = (B ≫ (s - N') - 2 ^ Z.of_nat (S N') * cx + 1)%Z ∨
                   bits_to_Z (b :: bs') = (B ≫ (s - N') - 2 ^ Z.of_nat (S N') * cx + 2)%Z) by lia.
      destruct Hv as [-> | [-> | [-> | [-> | ->]]]]; set_solver.
Qed.

(** The uniform sampler: sample a lazy real and convert to approximation sequence *)
Definition UnifSampler : expr := R_ofUnif (init #()).

Section uniform_total.
  Context `{!erisGS Σ}.

  (** TWP for init: allocate a lazy real *)
  Lemma twp_init E :
    ⊢ WP init #() @ E [{ v, lazy_real_uninit v }].
  Proof.
    rewrite /init.
    wp_pures.
    wp_alloc l as "Hl".
    wp_pures.
    wp_apply (twp_alloc_tape); [done|].
    iIntros (α) "Hα".
    wp_pures.
    iModIntro.
    iExists _, _. iSplit; [done|].
    iFrame.
  Qed.

  (** TWP for get_chunk on a cached chunk *)
  Lemma twp_get_chunk_cached (z : fin 2) α (l l' : loc) zs E ns :
    l ↦ SOMEV (#(fin_to_nat z), #l') ∗ chunk_list l' zs ∗ α ↪ (1%nat; ns)
    ⊢ WP get_chunk #lbl:α #l @ E
      [{ v, ⌜v = (#(fin_to_nat z), #l')%V⌝ ∗
            l ↦ SOMEV (#(fin_to_nat z), #l') ∗ chunk_list l' zs ∗ α ↪ (1%nat; ns) }].
  Proof.
    iIntros "(Hl & Hcl & Ha)".
    rewrite /get_chunk. wp_pures. wp_load. wp_pures.
    iModIntro. iFrame. done.
  Qed.

  (** TWP for get_chunk on a fresh chunk with one presampled bit *)
  Lemma twp_get_chunk_fresh (b : fin (S 1)) α (l : loc) E :
    l ↦ NONEV ∗ α ↪ (1%nat; cons b nil)
    ⊢ WP get_chunk #lbl:α #l @ E
      [{ v, ∃ l' : loc, ⌜v = (#(fin_to_nat b), #l')%V⌝ ∗
            l ↦ SOMEV (#(fin_to_nat b), #l') ∗ l' ↦ NONEV ∗ α ↪ (1%nat; []) }].
  Proof.
    iIntros "(Hl & Ha)".
    rewrite /get_chunk. wp_pures. wp_load. wp_pures.
    wp_apply (twp_rand_tape with "Ha").
    iIntros "Ha". wp_pures.
    wp_alloc l' as "Hl'". wp_pures.
    wp_store. iModIntro.
    iExists l'. iFrame. done.
  Qed.

  (** TWP for get_chunk on a fresh chunk with remaining bits on tape *)
  Lemma twp_get_chunk_fresh_remaining (b : fin (S 1)) (remaining : list (fin (S 1))) α (l : loc) E :
    l ↦ NONEV ∗ α ↪ (1%nat; b :: remaining)
    ⊢ WP get_chunk #lbl:α #l @ E
      [{ v, ∃ l' : loc, ⌜v = (#(fin_to_nat b), #l')%V⌝ ∗
            l ↦ SOMEV (#(fin_to_nat b), #l') ∗ l' ↦ NONEV ∗ α ↪ (1%nat; remaining) }].
  Proof.
    iIntros "(Hl & Ha)".
    rewrite /get_chunk. wp_pures. wp_load. wp_pures.
    wp_apply (twp_rand_tape with "Ha").
    iIntros "Ha". wp_pures.
    wp_alloc l' as "Hl'". wp_pures.
    wp_store. iModIntro.
    iExists l'. iFrame. done.
  Qed.

  Definition of_bits (zs : list (fin (S 1))) (acc : Z) : Z :=
    (fold_left (fun a z => 2*a + fin_to_nat z) zs acc)%Z.

  (** TWP for get_bits with remaining bits on tape *)
  Lemma twp_get_bits α l zs E (b : fin (S 1)) (remaining : list (fin (S 1)))
      (X : Z) (Hx : X = length zs) (acc : Z) :
    chunk_list l zs ∗ α ↪ (1%nat; b :: remaining)
    ⊢ WP get_bits (#lbl:α, #l)%V #X #acc @ E
      [{ v, ⌜v = #(of_bits zs acc)⌝ ∗ chunk_list l (zs ++ cons b nil) ∗ α ↪ (1%nat; remaining) }].
  Proof.
    rewrite Hx; clear Hx X.
    iRevert (l acc).
    iInduction zs as [|z zs] "IH".
    - (* Base case: zs = [], digitsLeft = 0 *)
      (* get_chunk reads the fresh bit b, then digitsLeft = 0, return acc *)
      iIntros (l acc) "[Hl Ha]".
      simpl. rewrite /get_bits. wp_pures.
      wp_bind (get_chunk _ _)%E.
      iApply (tgl_wp_wand with "[Hl Ha]").
      { iApply (twp_get_chunk_fresh_remaining with "[$Hl $Ha]"). }
      iIntros (v) "(%l' & -> & Hl & Hl' & Ha)".
      wp_pures.
      (* digitsLeft = 0, return approxSoFar *)
      iModIntro.
      iSplitR.
      2: { simpl. iSplitL "Hl Hl'". { iExists l'. iFrame. } iFrame. }
      { done. }
    - (* Inductive case: traverse cached chunk z, then continue *)
      iIntros (l acc) "[Hl Ha]".
      simpl.
      iDestruct "Hl" as (l') "[Hl Hcl]".
      rewrite /get_bits. wp_pures.
      (* After wp_pures, the first get_chunk on l is inlined. Bind and handle it. *)
      wp_bind (get_chunk _ _)%E.
      iApply (tgl_wp_wand with "[Hl Hcl Ha]").
      { iApply (twp_get_chunk_cached with "[$Hl $Hcl $Ha]"). }
      iIntros (v) "(-> & Hl & Hcl & Ha)".
      do 11 wp_pure.
      (* Goal: (rec: "force" ...) (#lbl:α, #l')%V #(S (length zs) - 1) #(2 * acc + z) *)
      change (rec: "force" "lazyR" "digitsLeft" "approxSoFar" :=
        let: "cn" := get_chunk (Fst "lazyR") (Snd "lazyR") in
        if: "digitsLeft" = #0 then "approxSoFar"
        else "force" (Fst "lazyR", Snd "cn") ("digitsLeft" - #1)
              (#2 * "approxSoFar" + Fst "cn"))%V with get_bits.
      replace (Z.of_nat (S (length zs)) - 1)%Z with (Z.of_nat (length zs)) by lia.
      iApply (tgl_wp_wand with "[Hcl Ha]").
      { iApply ("IH" $! l' with "[$Hcl $Ha]"). }
      iIntros (v) "(-> & Hc & Ha)".
      iFrame.
      done.
  Qed.

  (** If the presampled bitstring is NOT in the gap, the comparison terminates
      without error credits. *)
  Lemma twp_cmp_not_in_gap E (B C n : Z) (zs : list (fin 2)) (bs : list (fin 2)) a l :
    (n < 0)%Z →
    (-1 * n)%Z = Z.of_nat (length zs) →
    in_gap (of_bits zs 0) B (C + n) bs = false →
    chunk_list l zs ∗ a ↪ (1%nat; bs)
    ⊢ WP (rec: "cmp" "x" "y" "n" :=
            let: "cx" := "x" "n" in
            let: "cy" := "y" "n" in
            if: "cx" + #2 < "cy" then #(-1)
            else if: "cy" + #2 < "cx" then #1
            else "cmp" "x" "y" ("n" - #1))%V
        (λ: "prec", if: #0 ≤ "prec" then #0
           else get_bits (#lbl:a, #l)%V (#(-1) * "prec") #0)%V
        (λ: "prec", (λ: "prec", #B ≫ "prec")%V (#C + "prec"))%V
        #n @ E [{ _, True }].
  Proof.
    iIntros (Hn Hinv Hgap) "[Hcl Ha]".
    iRevert (n zs Hn Hinv Hgap) "Hcl Ha".
    iInduction bs as [|b bs'] "IH".
    - (* bs = []: in_gap _ _ _ [] = true, contradiction *)
      iIntros (n zs Hn Hinv Hgap) "Hcl Ha". simpl in Hgap. discriminate.
    - (* bs = b :: bs' *)
      iIntros (n zs Hn Hinv Hgap) "Hcl Ha".
      simpl in Hgap.
      (* Step through one iteration of the cmp loop *)
      wp_pures.
      (* Evaluate x(n): since n < 0, we go to get_bits *)
      case_bool_decide; [lia|].
      wp_pures.
      (* Call get_bits *)
      wp_bind (get_bits _ _ _).
      iApply (tgl_wp_wand with "[Hcl Ha]").
      { iApply (twp_get_bits _ _ zs _ b bs').
        { lia. }
        iFrame. }
      iIntros (v) "(-> & Hcl & Ha)".
      wp_pures.
      case_bool_decide.
      { wp_pures. done. }
      wp_pures.
      case_bool_decide.
      { wp_pures. done. }
      do 2 wp_pure.
      iApply ("IH" $! (n-1)%Z with "[] [] [] Hcl Ha").
      { iPureIntro. lia. }
      { iPureIntro. rewrite app_length //=. lia. }
      { iPureIntro.

(*  
  Σ : gFunctors
  erisGS0 : erisGS Σ
  E : coPset
  B, C : Z
  b : fin 2
  bs' : list (fin 2)
  a, l : loc
  n : Z
  zs : list (fin 2)
  Hn : (n < 0)%Z
  Hinv : (-1 * n)%Z = length zs
  Hgap : negb (2 * of_bits zs 0 + b + 2 <? B ≫ (C + n))%Z && negb (B ≫ (C + n) + 2 <? 2 * of_bits zs 0 + b)%Z &&
         in_gap (2 * of_bits zs 0 + b) B (C + n - 1) bs' = false
  H : ¬ (0 <= n)%Z
  H0 : ¬ (of_bits zs 0 + 2 < B ≫ (C + n))%Z
  H1 : ¬ (B ≫ (C + n) + 2 < of_bits zs 0)%Z
  ============================
  in_gap (of_bits (zs ++ [b]) 0) B (C + (n - 1)) bs' = false
*)

        admit. }
  Admitted.

  (** Total WP for the checker — the key new result using total Eris *)
  Lemma twp_lazy_real_cdf_checker E (ε : R) (B C : Z) :
    (0 < ε)%R →
    ⊢ ↯ ε -∗ WP lazy_real_cdf_checker UnifSampler B C @ E [{ v, ⌜ True ⌝ }].
  Proof.
    iIntros (Hε) "Hε".
    rewrite /UnifSampler /lazy_real_cdf_checker.
    wp_bind (init _)%E.
    iApply (tgl_wp_wand with "[]").
    { iApply twp_init. }
    iIntros (v) "Hv".
    rewrite /R_ofUnif.
    wp_pures.
    rewrite /R_ofZ.
    wp_pures.
    rewrite /R_mulPow.
    wp_pures.
    rewrite /lazy_real_uninit.
    rewrite /R_cmp.
    wp_pures.
    case_bool_decide.
    { by wp_pures. }
    wp_pures.
    case_bool_decide.
    { by wp_pures. }
    wp_pure.
    iDestruct "Hv" as (l a) "(-> & Hl & Ha)".
    wp_pure.



    (*  Old proof: Ignore but do not delete
    clear H H0.
    iAssert (∀ n : Z, ⌜(n < 0)%Z⌝ -∗
      ↯ ε -∗
      (∃ zs, ⌜((-1) * n = Z.of_nat (S (length zs)))%Z⌝ ∗ chunk_list l zs ∗ a ↪ (1%nat; [])) -∗
      WP (rec: "cmp" "x" "y" "n" :=
            let: "cx" := "x" "n" in
            let: "cy" := "y" "n" in
            if: "cx" + #2 < "cy" then #(-1)
            else if: "cy" + #2 < "cx" then #1
            else "cmp" "x" "y" ("n" - #1))%V
        (λ: "prec", if: #0 ≤ "prec" then #0
           else get_bits (#lbl:a, #l)%V (#(-1) * "prec") #0)%V
        (λ: "prec", (λ: "prec", #B ≫ "prec")%V (#C + "prec"))%V
        #n @ E [{ _, True }])%I as "Hgen".
    2: { (* Sufficiency *)
      iApply ("Hgen" with "[] Hε [Hl Ha]"); [iPureIntro; lia|].
      iExists []. simpl. iFrame. iPureIntro. lia. }
    (* Main proof: ∀ n, ... *)
    iIntros (n) "%Hn Hε (%zs & %Hinv & Hcl & Ha)".
    iRevert (n Hn Hinv) "Hcl Ha".
    iApply (ec_ind_amp _ 2 with "[] Hε"); [lra|lra|].
    iModIntro.
    iIntros (ε') "%Hε' #IH Hε'".
    iIntros (n Hn Hinv) "Hcl Ha".

    (* Presample one bit onto the tape a.
        f(0) = 0
        f(1) = 2 * ε'
     *)
    set (ε2 := fun (b : fin 2) => if (fin_to_nat b =? 0)%nat then 0%R else (2 * ε')%R).
    wp_apply (twp_presample_adv_comp 1 1 E _ a _ [] ε' ε2 with "[$Ha $Hε' Hcl]").
    { done. }
    { intros b'. subst ε2. simpl. destruct (fin_to_nat b' =? 0)%nat eqn:E'; [lra|lra]. }
    { subst ε2. rewrite SeriesC_finite_foldr. simpl. lra. }
    iIntros (b) "[Hε2 Ha]".

    wp_pures.
    case_bool_decide; [lia|].
    wp_pures.

    wp_bind (get_bits _ _ _).
    iApply (tgl_wp_wand with "[Hcl Ha]").
    {
      iApply (twp_get_bits _ _ zs).
      (* Stuck due to this side condition... we will revisit. *)
      { admit. }
      iFrame.
    }
    iIntros (?) "(-> & Hcl & Ha)".
    wp_pures.
    *)
    admit.
  Admitted.

End uniform_total.

(** Termination: tgl from total Eris *)
Theorem uniform_cdf_checker_tgl Σ `{erisGpreS Σ} (σ : state) (ε : R) (B C : Z) :
  (0 < ε)%R →
  tgl (lim_exec (lazy_real_cdf_checker UnifSampler B C, σ)) (λ _, True) ε.
Proof.
  intros Hε.
  eapply (twp_tgl _ _ _ ε); [lra|].
  intros.
  iIntros "Hε".
  iApply twp_lazy_real_cdf_checker; [done|].
  iFrame.
Qed.

(** Hterm: the checker terminates with probability 1 *)
Theorem uniform_cdf_checker_terminates Σ `{erisGpreS Σ} (σ : state) (B C : Z) :
  prob (lim_exec (lazy_real_cdf_checker UnifSampler B C, σ)) (fun _ => true) = 1.
Proof.
  rewrite /prob.
  erewrite SeriesC_ext; [|intros; simpl; done].
  apply Rle_antisym; [apply pmf_SeriesC|].
  replace 1 with (1 - 0) by lra.
  eapply (twp_mass_lim_exec_limit _ _ _ 0 (fun _ => True)); [lra|].
  intros ? ε' Hε'.
  iIntros "Hε".
  iApply (twp_lazy_real_cdf_checker with "Hε"); lra.
Qed.

(** Uniform density: Iverson bracket on [0,1] *)
Definition uniform_density : R → R := Iverson (Icc 0 1).

(** IPCts for the uniform density *)
Lemma uniform_density_eq x :
  uniform_density x = Iverson (Ici 0) x * Iverson (Iic 1) x.
Proof.
  rewrite /uniform_density /Iverson /Icc /Ici /Iic.
  rewrite Rmin_left; [|lra]. rewrite Rmax_right; [|lra].
  repeat case_decide; lra.
Qed.

Lemma IPCts_uniform : IPCts uniform_density.
Proof.
  have H : IPCts (fun x => Iverson (Ici 0) x + Iverson (Iic 1) x + -1 * 1).
  { apply IPCts_plus.
    - apply IPCts_plus; [apply IPCts_Ici|apply IPCts_Iic].
    - apply (IPCts_scal_mult (c := -1)). apply IPCts_cts. intros. apply Continuity.continuous_const. }
  destruct H as [f0 [L [Hext [Hcts Hf0]]]].
  exists f0, L. split; [|done].
  intros x.
  have Heq : uniform_density x = Iverson (Ici 0) x + Iverson (Iic 1) x + -1 * 1.
  { rewrite uniform_density_eq /Iverson /Ici /Iic. repeat case_decide; lra. }
  rewrite Heq. apply Hext.
Qed.

(** Integrability on the left half-line *)
Lemma ex_RInt_gen_uniform_neg :
  ex_RInt_gen uniform_density (Rbar_locally Rbar.m_infty) (at_point 0).
Proof.
  eapply ex_RInt_gen_ext_eq_Iio; last first.
  { eapply ex_RInt_gen_neg_change_of_var_rev.
    - intros b Hb. apply ex_RInt_const.
    - apply ex_RInt_gen_0. }
  intros x Hx. rewrite /uniform_density /Iverson.
  case_decide as H; [|done].
  rewrite /Icc in H. exfalso.
  rewrite Rmin_left in H; lra.
Qed.

(** Integrability on the right half-line *)
Lemma ex_RInt_gen_uniform_pos :
  ex_RInt_gen uniform_density (at_point 0) (Rbar_locally Rbar.p_infty).
Proof.
  have Htail : ex_RInt_gen uniform_density (at_point 1) (Rbar_locally Rbar.p_infty).
  { eapply ex_RInt_gen_ext_eq_Ioi; last apply (ex_RInt_gen_0 1).
    intros x Hx. rewrite /uniform_density /Iverson.
    case_decide as H; [|done].
    rewrite /Icc in H. exfalso.
    rewrite Rmin_left in H; [|lra].
    rewrite Rmax_right in H; [|lra]. lra. }
  have Hfin : ex_RInt_gen uniform_density (at_point 0) (at_point 1).
  { rewrite ex_RInt_gen_at_point. apply IPCts_RInt. apply IPCts_uniform. }
  destruct Htail as [lt Hlt].
  destruct Hfin as [lf Hlf].
  exists (plus lf lt).
  eapply is_RInt_gen_Chasles; eassumption.
Qed.

(** Boundedness *)
Lemma uniform_density_range : ∀ x, 0 <= uniform_density x <= 1.
Proof.
  intros x. rewrite /uniform_density /Iverson.
  case_decide; lra.
Qed.

(** Total mass is 1 *)
Lemma uniform_density_zero_left x : x < 0 → uniform_density x = 0.
Proof.
  intros. rewrite /uniform_density /Iverson /Icc.
  rewrite Rmin_left; [|lra]. rewrite Rmax_right; [|lra].
  case_decide; lra.
Qed.

Lemma uniform_density_zero_right x : 1 < x → uniform_density x = 0.
Proof.
  intros. rewrite /uniform_density /Iverson /Icc.
  rewrite Rmin_left; [|lra]. rewrite Rmax_right; [|lra].
  case_decide; lra.
Qed.

Lemma uniform_density_one x : 0 <= x <= 1 → uniform_density x = 1.
Proof.
  intros. rewrite /uniform_density /Iverson /Icc.
  rewrite Rmin_left; [|lra]. rewrite Rmax_right; [|lra].
  case_decide; lra.
Qed.

Lemma RInt_gen_0_neg :
  RInt_gen (λ _ : R, 0) (Rbar_locally Rbar.m_infty) (at_point 0) = 0.
Proof.
  rewrite -(@RInt_gen_neg_change_of_var (λ _, 0)).
  - apply RInt_gen_0.
  - intros. apply ex_RInt_const.
  - intros. apply ex_RInt_const.
  - eapply (@ex_RInt_gen_neg_change_of_var_rev (fun _ : R => 0)).
    + intros. apply ex_RInt_const.
    + apply ex_RInt_gen_0.
Qed.

Lemma uniform_density_mass :
  RInt_gen uniform_density (Rbar_locally Rbar.m_infty) (Rbar_locally Rbar.p_infty) = 1.
Proof.
  rewrite -(@RInt_gen_Chasles R_CompleteNormedModule
    (Rbar_locally Rbar.m_infty) (Rbar_locally Rbar.p_infty) _ _
    uniform_density 0).
  3: { apply ex_RInt_gen_uniform_pos. }
  2: { apply ex_RInt_gen_uniform_neg. }
  rewrite (RInt_gen_ext_eq_Iio (f := uniform_density) (g := fun _ => 0)).
  3: { apply ex_RInt_gen_uniform_neg. }
  2: { intros. apply uniform_density_zero_left. done. }
  rewrite -(@RInt_gen_Chasles R_CompleteNormedModule
    (at_point 0) (Rbar_locally Rbar.p_infty) _ _
    uniform_density 1).
  3: { eapply ex_RInt_gen_ext_eq_Ioi;
       [intros; symmetry; apply uniform_density_zero_right; done
       |apply (ex_RInt_gen_0 1)]. }
  2: { rewrite ex_RInt_gen_at_point. apply IPCts_RInt, IPCts_uniform. }
  rewrite (RInt_gen_ext_eq_Ioi (f := uniform_density) (g := fun _ => 0)).
  3: { eapply ex_RInt_gen_ext_eq_Ioi;
       [intros; symmetry; apply uniform_density_zero_right; done
       |apply (ex_RInt_gen_0 1)]. }
  2: { intros. apply uniform_density_zero_right. done. }
  rewrite RInt_gen_0 RInt_gen_0_neg RInt_gen_at_point.
  2: { apply IPCts_RInt, IPCts_uniform. }
  rewrite (RInt_ext uniform_density (fun _ => 1)).
  2: { intros x [Hx1 Hx2]. apply uniform_density_one.
       rewrite Rmin_left in Hx1; [|lra]. rewrite Rmax_right in Hx2; [|lra]. lra. }
  rewrite RInt_const /scal /= /mult /plus /=. lra.
Qed.

Lemma uniform_density_RInt_gen_eq (F : R → R) {M}
    (Hnn : ∀ x, 0 <= F x <= M) (HP : IPCts F) :
  RInt_gen (fun x => uniform_density x * F x)
    (Rbar_locally Rbar.m_infty) (Rbar_locally Rbar.p_infty) = RInt F 0 1.
Proof.
  rewrite -(@RInt_gen_Chasles R_CompleteNormedModule
    (Rbar_locally Rbar.m_infty) (Rbar_locally Rbar.p_infty) _ _
    (fun x => uniform_density x * F x) 0).
  3: { (* ex_RInt_gen pos half *)
       have Htail : ex_RInt_gen (fun x => uniform_density x * F x) (at_point 1) (Rbar_locally Rbar.p_infty).
       { eapply ex_RInt_gen_ext_eq_Ioi; last apply (ex_RInt_gen_0 1).
         intros x Hx. rewrite uniform_density_zero_right; [ring|done]. }
       have Hfin : ex_RInt_gen (fun x => uniform_density x * F x) (at_point 0) (at_point 1).
       { rewrite ex_RInt_gen_at_point. apply ex_RInt_mult.
         { apply IPCts_RInt, IPCts_uniform. } { apply IPCts_RInt. done. } }
       destruct Htail as [lt Hlt]. destruct Hfin as [lf Hlf].
       exists (plus lf lt). eapply is_RInt_gen_Chasles; eassumption. }
  2: { (* ex_RInt_gen neg half *)
       eapply ex_RInt_gen_ext_eq_Iio; last first.
       { eapply ex_RInt_gen_neg_change_of_var_rev.
         - intros b Hb. apply ex_RInt_const.
         - apply ex_RInt_gen_0. }
       intros x Hx. rewrite uniform_density_zero_left; [ring|done]. }
  rewrite (RInt_gen_ext_eq_Iio
    (f := fun x => uniform_density x * F x) (g := fun _ => 0)).
  3: { eapply ex_RInt_gen_ext_eq_Iio; last first.
       { eapply ex_RInt_gen_neg_change_of_var_rev.
         - intros b Hb. apply ex_RInt_const.
         - apply ex_RInt_gen_0. }
       intros x Hx. rewrite uniform_density_zero_left; [ring|done]. }
  2: { intros x Hx. rewrite uniform_density_zero_left; [ring|done]. }
  rewrite -(@RInt_gen_Chasles R_CompleteNormedModule
    (at_point 0) (Rbar_locally Rbar.p_infty) _ _
    (fun x => uniform_density x * F x) 1).
  3: { eapply ex_RInt_gen_ext_eq_Ioi; last apply (ex_RInt_gen_0 1).
       intros x Hx. rewrite uniform_density_zero_right; [ring|done]. }
  2: { rewrite ex_RInt_gen_at_point. apply ex_RInt_mult.
       { apply IPCts_RInt, IPCts_uniform. } { apply IPCts_RInt. done. } }
  rewrite (RInt_gen_ext_eq_Ioi
    (f := fun x => uniform_density x * F x) (g := fun _ => 0)).
  3: { eapply ex_RInt_gen_ext_eq_Ioi; last apply (ex_RInt_gen_0 1).
       intros x Hx. rewrite uniform_density_zero_right; [ring|done]. }
  2: { intros x Hx. rewrite uniform_density_zero_right; [ring|done]. }
  rewrite RInt_gen_0 RInt_gen_0_neg RInt_gen_at_point.
  2: { apply ex_RInt_mult. { apply IPCts_RInt, IPCts_uniform. } { apply IPCts_RInt. done. } }
  rewrite (RInt_ext (fun x => uniform_density x * F x) F).
  2: { intros x [Hx1 Hx2].
       rewrite Rmin_left in Hx1; [|lra]. rewrite Rmax_right in Hx2; [|lra].
       rewrite /uniform_density/Iverson/=.
       case_decide; try lra.
       exfalso.
       revert H.
       rewrite /Icc//=.
       rewrite Rmin_left; OK.
       rewrite Rmax_right; OK.
  }
  rewrite /plus//=.
  OK.
Qed.

(** Main theorem: the uniform sampler correctly implements the CDF *)
Theorem uniform_cdf_prob Σ `{erisGpreS Σ} (σ : state) :
  ∀ B C : Z,
    prob (lim_exec (lazy_real_cdf_checker UnifSampler B C, σ))
      (fun x => bool_decide (x = #(-1)%Z)) =
    RInt_gen uniform_density (Rbar_locally Rbar.m_infty) (at_point (IZR B / powerRZ 2 C)).
Proof.
  intros B C.
  apply (@lazy_real_expr_adequacy_cdf_prob _ _ 1 UnifSampler σ uniform_density).
  - apply uniform_density_range.
  - apply IPCts_uniform.
  - apply ex_RInt_gen_uniform_neg.
  - apply ex_RInt_gen_uniform_pos.
  - iIntros (?? F [M HM] HI) "Hε".
    unfold UnifSampler.
    wp_bind (init _)%E.
    iApply wp_init; [done|].
    iIntros (v) "Hv".
    iApply (wp_lazy_real_presample_adv_comp E (R_ofUnif v) v _ (RInt F 0 1) F with "[-]"); auto.
    { intros r Hr. apply HM. }
    { apply (@RInt_correct R_CompleteNormedModule F 0 1), IPCts_RInt. done. }
    iFrame "Hv".
    iSplitL "Hε".
    { iApply ec_eq. { apply (@uniform_density_RInt_gen_eq F M). { intros; apply HM. } done. } iFrame. }
    iIntros (r) "(%Hr & Hε & Hr)".
    iApply (pgl_wp_wand with "[Hr]").
    { iApply (wp_R_ofUnif r with "Hr"). }
    iIntros (cont) "Happrox".
    iExists r. iFrame.
  - apply uniform_density_mass.
  - intros B' C'. apply (uniform_cdf_checker_terminates Σ σ B' C').
Qed.

(** Closed theorem: instantiate with erisΣ *)
Theorem uniform_cdf_prob_closed (σ : state) :
  ∀ B C : Z,
    prob (lim_exec (lazy_real_cdf_checker UnifSampler B C, σ))
      (fun x => bool_decide (x = #(-1)%Z)) =
    RInt_gen uniform_density (Rbar_locally Rbar.m_infty) (at_point (IZR B / powerRZ 2 C)).
Proof.
  apply (uniform_cdf_prob erisΣ).
Qed.

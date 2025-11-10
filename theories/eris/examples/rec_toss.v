From clutch.eris Require Export eris error_rules.
From Coquelicot Require Import Series.
Require Import Lra.

Section toss_rec.
  Context `{!erisGS Σ}.

  (* Taped version in case we need it *)
  Definition toss_rec_tape : expr :=
    rec: "toss" "a" "α" :=
      let: "x" := rand("α") #2 in
      if: ("x" ≤ #0) (* or just "x" = #0 *)
        then #()
        else "toss" #() "α" ;; "toss" #() "α".
  
  Definition prog_tape : expr :=
    let: "α" := alloc #1 in
    toss_rec_tape #() "α".

  Definition toss_rec : val :=
    rec: "toss" "a" :=
      let: "x" := rand #2 in
      if: ("x" ≤ #0) (* or just "x" = #0 *)
        then #()
        else "toss" #() ;; "toss" #().
  
  Definition prog : expr :=
    toss_rec #().

  (* Equivalent random walk:
   *   x = 1
   *   while x > 0:
   *      with prob 1/3: x := x - 1
   *      with prob 2/3: x := x + 1
   *)

  (* make termination probability of `toss` to be `x` 
   * then we have `x = 1/3 + 2/3 x^2, which has 2 roots: 1, 1/2
   *)

  (* To have enough error credits for the second recursive call to toss, we need to amplify
   * the error credits from the first recursive call. If we can normalize the thin air credit
   * by the termination probability, then we have enough credits.
    *)
  (* in general: [{ ↯(y) * ↯(r) }] prog () [{ ↯( r * 1/(1-y) ) }] *)
  (* where `y` is the non-termination probability solution of `prog` *)
  (* We are not able to prove this... *)

  (* 
   * In recursive second branch, we have `3/4 + (1/2) * r` credits
   * (we need to spend `2/3 * r` credit for the first branch)
   * If we rearrange the error credits to `1/2 + ((1/4 + r/2))`, then
   * after the first recursive call, we get `1/2 + r` back
   *)
  Lemma toss_rec_spec_aux r E:
    ⊢ [[{ ↯ (1/2) ∗ ↯(r) }]] prog @ E [[{ (v : val), RET v; ↯(r * 2) }]].
  Proof.
    iIntros.
    rewrite /prog /toss_rec.
    iIntros "!>".
    (* merge the error credits together *)
    iIntros (Φ) "[Herr Herr1] Hwp".
    iApply (twp_rand_err_pos).
    { done. }
    iIntros (ε) "%Hεge0 Hε".
    (* We want to use the toss_rec_spec_aux for induction *)
    iAssert (
     (□
     ∀ r Φ,
     ↯ (1 / 2) -∗
     ↯ r -∗
     (∀ v : val, ↯ (r * 2) -∗ Φ v) -∗
     WP (rec: "toss" "a" :=
        let: "x" := rand #2 in if: "x" ≤ #0 then #() else "toss" #();; "toss" #())%V
        #()
      @ E
      [{ v, Φ v }]) %I
    ) with "[Herr Herr1 Hε]" as "#Hrec".
    {
    iApply (ec_ind_amp ε (3/ 2) ) .
     * done.
     * real_solver.
     * iIntros "!>".
       iIntros (ε') "He #He1 He'".
       iIntros "!>". (* We lost ε' and we can't do induction *)
       clear r. clear Φ.
       iIntros (r Φ) "He Hr HΦ".
       give_up.
      * done.
    }
    iApply ("Hrec" with "Herr Herr1 Hwp").
  Admitted.

  (* Caveat: this means prog non-termination is upper bounded by 1/2 *)
  Lemma toss_rec_spec E :
    ⊢ ↯ (1 / 2) -∗ WP prog @ E [{ _, True%I }].
  Proof.
    iIntros "Herr".
    wp_rec.
    set (ε2 := λ n : fin (S 2), if (fin_to_nat n <=? 0) then 0%R else (3 / 4)%R).
    wp_apply (twp_couple_rand_adv_comp1 _ _ _ _ ε2 with "[$]").
    { intros; rewrite /ε2; case_match; lra. }
    { rewrite SeriesC_finite_foldr /ε2. simpl. lra. }
    iIntros (n) "Herr".
    wp_pures.
    case_bool_decide; wp_pures; first done.
    - wp_apply (toss_rec_spec_aux (1/4)%R _ with "[Herr]").
      * rewrite /ε2.
        assert (n <=? 0 = false) as ->.
        { apply Nat.leb_gt. lia. }
        iApply ec_split; [lra|lra|]. replace (3/4)%R with (1/2 + 1/4)%R by lra. iFrame.
      * iIntros (v) "Herr".
        wp_pures.
        wp_apply (toss_rec_spec_aux (0)%R _ with "[Herr]").
        -- replace (1/4*2)%R with (1/2)%R by lra. iApply ec_split; [lra|lra|]. replace (1/2)%R with (1/2 + 0)%R by lra. iFrame.
           replace (1/2+0+0)%R with (1/2+0)%R by lra. iFrame.
        -- iIntros (v') "Herr". done.
  Qed.


End toss_rec.
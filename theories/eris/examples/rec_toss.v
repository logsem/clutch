From clutch.eris Require Export eris error_rules.
From Coquelicot Require Import Series.
Require Import Lra.

Section toss_rec.
  Context `{!erisGS Σ}.

  (* simpler version of `golden_toss` *)
  (* TODO: i don't think i need tape? (unless i really need to use the Planner Rule) *)
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

  (* TODO: what is the E for again? *)
  (* in general: [{ ↯(y) * ↯(r) }] prog () [{ ↯( r * 1/(1-y) ) }] *)
  (* where `y` is the non-termination probability solution of `prog` *)

  Lemma toss_rec_spec_aux r E:
    ⊢ [[{ ↯ (1/2) ∗ ↯(r) }]] prog @ E [[{ (v : val), RET v; ↯(r * 2) }]].
  Proof.
    iIntros.
    rewrite /prog /toss_rec.
    iIntros "!>".
    (* merge the error credits together *)
    iIntros (Φ) "[Herr Herr1] Hwp".
    iApply (twp_rand_err_incr _ 0 _ _ _).
    { done. }
    iSplitL "".
    * admit.
    * iIntros (ε) "He He1".
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
    ) with "[-]" as "H".
    {
    iApply (ec_ind_amp ε (3/ 2) ).
     * admit.
     * real_solver.
     * iIntros "!>".
       iIntros (ε') "He #He1 He'".
       iIntros "!>".
       clear r. clear Φ. clear ε.
       iIntros (r Φ) "He Hr HΦ".
       admit.
      * admit.
    }
    admit.
    (* iAssert (↯ (1/2 + r)) with "[Herr Herr1]" as "Herr2".
    (* twp_rand_err_incr *)
    (* TODO: check whether we can prove this using error amplification rule... *)
    { iApply ec_combine. iFrame. }
    (* iSpecialize (twp_rand_err_incr) as "A". *)
    wp_rec. 
    fold toss_rec. fold prog. *)
  Admitted.

  (* Caveat, this means prog non-termination is upper bounded by 1/2 *)
  (* The annoying part is 1 - 1/2 is also 1/2 which makes error credit kinda dubious *)
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
    (* Oh, the recursion is not value dependent so I wouldn't need to know n = 1 or n = 2... *)
    (* pose proof (fin_to_nat_lt n).
    eassert (n=nat_to_fin (_:1<3) \/ n = nat_to_fin (_ :2<3)) as [-> | ->].
    { Unshelve.
      all: try lia.
      simpl.
      destruct (fin_to_nat n) as [|[|[|[|]]]] eqn:Hn; [lia|left|right| lia| lia].
      - by repeat (inv_fin n; [done|intros n ?]).
      - by repeat (inv_fin n; [done|intros n ?]).
    } *)
    (* TODO (above): how to make this readable.... *)
    (* TODO: Why `Herr` needs to be in square brackets... *)
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
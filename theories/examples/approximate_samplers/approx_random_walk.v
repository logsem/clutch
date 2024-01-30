(** * Error credit proof that an unbounded integer walk returns to the origin *)
From clutch.ub_logic Require Export ub_clutch ub_rules.
From clutch Require Export examples.approximate_samplers.approx_sampler_lib.
From Coquelicot Require Import Series.
Require Import Lra.

Set Default Proof Using "Type*".

Section integer_walk.
  (** Random walk: Sampler increments or decrements a value, checker accepts when that value is negative *)

  (* This might fit into the higher-order spec, the problem is our error and progress are linked.
     We don't really get "excess error" in the same way that we do with eg. WalkSAT. *)

  Context `{!ub_clutchGS Σ, cinvG Σ}. (* inG Σ (authR natUR)}. *)

  Definition int_walk_sampler : val :=
    (λ: "l",
       if: (rand #1 = #1)
        then "l" <- (!"l" + #1%nat)
        else "l" <- (!"l" - #1%nat))%V.

  Definition int_walk_checker : val :=
    (λ: "l", (!"l" < #0))%V.



  (** Credit accounting for the invariant *)

  Definition L (εᵢ : nonnegreal) : nat := Z.to_nat (up (1 / εᵢ)%R - 1)%Z.

  Program Definition IC εᵢ : Z -> nonnegreal := fun n => mknonnegreal (Rmax 0 (nonneg εᵢ * IZR (n + 1)%Z))%R _.
  Next Obligation. intros; apply Rmax_l. Defined.

  Lemma IC_neg εᵢ : forall (z : Z), (z < 0)%Z -> (nonneg (IC εᵢ z) = 0)%R.
  Proof.
    intros. rewrite /IC /=.
    apply Rmax_left.
    apply Rcomplements.Rmult_le_0_l; [apply cond_nonneg|].
    rewrite /IZR.
    (* true but annoying *)
  Admitted.

  Lemma IC_ge_L εᵢ : forall (z : Z), (z >= (L εᵢ))%Z -> (nonneg (IC εᵢ z) >= 1)%R.
  Proof.
    intros. rewrite /IC /=.
    rewrite Rmax_right; last first.
    { apply Rmult_le_pos; [apply cond_nonneg|].
      (* FIXME: IZR of pos is pos *)
      admit.
    }
    (* rewrite /L in H0. *)
    (* yep *)
  Admitted.

  Lemma IC_mean εᵢ : forall (z : Z), (z >= 0)%Z ->
                       (nonneg (IC εᵢ (z - 1)%Z) + nonneg (IC εᵢ (z + 1)%Z) = 2 * nonneg (IC εᵢ z))%R.
  Proof.
    (* It's linear for z ∈ [-1, ∞)
       this is unused atm *)
  Admitted.

  (* Credit to amplify within the sequence *)
  Definition AC (εᵢ : nonnegreal) (εₐ : posreal) (p : nat) pwf kwf : nonnegreal :=
    εR 2 (L εᵢ) p εₐ (mk_fRwf _ _ _ kwf pwf).

  Program Definition I (εᵢ : nonnegreal) εₐ (l : loc) kwf : nat -> iProp Σ :=
    fun p => (∃ z: Z, l ↦ #z ∗ € (IC εᵢ p) ∗ ⌜(z < p - 1)%Z⌝ ∗ € (AC εᵢ εₐ ((L εᵢ) - p) _ kwf))%I.
  Next Obligation. intros. lia. Qed.

  (** Credit accounting for the amplifcation *)

  Program Definition kwf_L εᵢ (Hεᵢ : (nonneg εᵢ < 1)%R) : kwf 2 (L εᵢ) := mk_kwf _ _ _ _.
  Next Obligation. intros; lia. Qed.
  Next Obligation. intros. rewrite /L. Admitted. (* doable, unused atm though *)

  Program Definition Δε (εᵢ : nonnegreal) (εₐ : posreal) kwf : nonnegreal :=
    mknonnegreal (εAmp 2 (L εᵢ) εₐ kwf - εₐ)%R _.
  Next Obligation. intros. pose P := (εAmp_amplification 2 (L εᵢ) εₐ kwf). lra. Qed.

  Lemma Δε_exchange (εᵢ : nonnegreal) (εₐ : posreal) kwf :
    € (εAmp 2 (L εᵢ) εₐ kwf) -∗ (€ (Δε εᵢ εₐ kwf) ∗ € (pos_to_nn εₐ)).
  Proof.
    iIntros.
    iApply ec_split.
    iApply ec_spend_irrel; [|iFrame].
    rewrite /Δε /=.
    lra.
  Qed.

  (* This is easy to initialize for sufficiently large i! *)
  Program Definition AX (εᵢ : nonnegreal) (εₐ : posreal) kwf : nat -> nonnegreal :=
    (fun i => mknonnegreal (Rmax 0 (1 - i * (Δε εᵢ εₐ kwf))%R) _).
  Next Obligation. intros; apply Rmax_l. Defined.

  (* Error credit distribution at each amplifications step *)

  Program Definition integer_walk_distr εᵢ εₐ (p : nat) kwf : fin 2 -> nonnegreal :=
    (fun v => if (Fin.eqb v (1 : fin 2))%fin
              then (εAmp 2 (L εᵢ) εₐ kwf        + IC εᵢ (p + 1))%NNR  (* moves right; amplification *)
              else (AC εᵢ εₐ ((L εᵢ) - (p - 1)) _ kwf + IC εᵢ (p - 1))%NNR  (* moves left; progress *)).
  Next Obligation. intros. apply PeanoNat.Nat.le_sub_l. Qed.


  (* sampler either gives us progress or amplifies our error *)
  Lemma wp_sampler_amp εᵢ εₐ l p i kwf E :
    ⊢ I εᵢ εₐ l kwf (S p) ∗ € (AX εᵢ εₐ kwf (S i)) -∗
      WP (int_walk_sampler #l) @ E {{ fun _ => ((I εᵢ εₐ l kwf p ∗ € (AX εᵢ εₐ kwf (S i))) ∨
                                     (I εᵢ εₐ l kwf (S (S p)) ∗ € (AX εᵢ εₐ kwf i)))}}.
  Proof.
    iIntros "([%z (Hl & HcrIC & %Hz & HcrAC)] & HcrAX)".
    rewrite /int_walk_sampler.
    wp_pures.
    wp_bind (rand _)%E.

    (* I think we need a special case for z < 0?
       IC (-3) = 0
       IC (-2) = 0
       IC (-1) = 0
       IC (0)  =  εᵢ
       IC (0)  = 2εᵢ
       IC (0)  = 3εᵢ

      The mean proerty does _not_ hold at z = -1!

      My intuition is that this should be fixable by strengthening the spec, though, since we only ever
      get to z = -1 once the checker has already passed and the program has already terminated.

      Maybe I move the progress measure backwards to hit 0 at -2 or -3? If I do this, I can change it to
      quantify over nat instead of Z... the same problem will arise at the left endpoint, but that should be
      excluded by virtue of the (S p) in the amp spec.

     *)
    wp_apply (wp_couple_rand_adv_comp1 _ _ _
                ((IC εᵢ (S p)) + (AC εᵢ εₐ (L εᵢ - S p) (I_obligation_1 εᵢ (S p)) kwf))%NNR
                (integer_walk_distr εᵢ εₐ (S p) kwf) with "[HcrAC HcrIC]").
    { (* Series mean *)
      rewrite SeriesC_fin2.
      admit.
    }
    { (* credit total *)
      iApply ec_split; iFrame. }
    iIntros (s) "Hcr".
    wp_pures.
    destruct (fin_to_bool s) as [|] eqn:sB; last first.
    - assert (Hs : s = 0%fin) by admit.  (* FIXME fin 2 nonsense *)
      rewrite Hs.
      wp_pures; wp_load; wp_pures; wp_store.
      iModIntro.
      iLeft.
      iFrame.
      iExists _; iFrame.
      rewrite /integer_walk_distr /=.
      iAssert (€ (AC εᵢ εₐ (L εᵢ - (p - 0)) (integer_walk_distr_obligation_1 εᵢ (S p)) kwf) ∗ € (IC εᵢ (S p - 1)))%I with "[Hcr]" as "[HcrAmp HcrIC]".
      { iApply ec_split; iFrame. }
      iSplitL "HcrIC".
      { iApply ec_spend_irrel; [|iFrame]. f_equal. f_equal. lia. }
      iSplitR.
      { iPureIntro. lia. }
      iApply ec_spend_irrel; [|iFrame].
      (* some kind of proof irrelevance here, same as the kwf stuff. *)
      admit.
    - assert (Hs : s = 1%fin) by admit.  (* FIXME fin 2 nonsense *)
      rewrite Hs.
      wp_pures; wp_load; wp_pures; wp_store.
      iModIntro.
      (* moved right: amplification *)
      iRight.
      rewrite /integer_walk_distr /=.
      iAssert (€ (εAmp 2 (L εᵢ) εₐ kwf) ∗ € (IC εᵢ (S p + 1)))%I with "[Hcr]" as "[HcrAmp HcrIC]".
      { iApply ec_split; iFrame. }

      assert (HAX: ((AX εᵢ εₐ kwf (S i)) + (Δε εᵢ εₐ kwf) = (AX εᵢ εₐ kwf i))%NNR).
      { Opaque INR.
        rewrite /AX.
        apply nnreal_ext. simpl.
        (* True because (εₐ * k 2 (L εᵢ) kwf - εₐ) > 0*)
        admit.
      }
      iDestruct (Δε_exchange with "HcrAmp") as "(HΔε&Hεₐ)".
      rewrite -HAX.

      iSplitR "HcrAX HΔε"; [|iApply ec_split; iFrame].
      rewrite /I.
      iExists _.
      iFrame.
      iSplitL "HcrIC".
      { iApply ec_spend_irrel; [|iFrame].
        simpl; do 3 f_equal.
        lia. }
      iSplitR.
      { iPureIntro. lia. }
      iApply ec_spend_le_irrel; [|iFrame].
      rewrite /AC.
      simpl nonneg.
      (* holds because fR is <= 1 *)
      admit.

  Admitted.


  (* We can always run the checker with any bound on it's position (with no loss in progress) *)
  Lemma wp_checker_triv εᵢ εₐ l kwf E : forall p, I εᵢ εₐ l kwf p -∗ WP int_walk_checker #l @ E {{fun v => I εᵢ εₐ l kwf p ∗ ∃ b: bool, ⌜v = #b⌝}}.
  Proof.
    iIntros (p) "[%z (Hl & HcrIC & %Hz & HcrAC)]".
    rewrite /int_walk_checker.
    wp_pures; wp_load; wp_pures.
    iModIntro.
    iSplitL.
    - iFrame. eauto.
    - eauto.
  Qed.

  Lemma integer_walk_sampling_scheme (l : loc) εᵢ εₐ kwf E B:
    ⊢ (* ⌜(0 < nonneg ε0)%R ⌝ -∗ *)
      incr_sampling_scheme_spec
        (λ: "_", int_walk_sampler #l)
        (λ: "_", int_walk_checker #l)
        (I εᵢ εₐ l kwf)
        (AX εᵢ εₐ kwf)
        (L εᵢ)
        B
        E.
  Proof.
    iSplit.
    - (* Spending rules *)
      iIntros "[Hcr | [%z (Hl & _ & %Hz & _)]]".
      + (* Credit spending rule *)
        wp_apply (wp_ec_spend _ _ _ nnreal_one); simpl; [lra|eauto|].
        iApply (ec_spend_le_irrel with "Hcr"); simpl.
        rewrite Rmult_0_l Rminus_0_r.
        apply Rmax_r.
      + (* Progress spending rule *)
        rewrite /int_walk_sampler; wp_pures.
        wp_bind (rand _)%E; wp_apply wp_rand; eauto.
        iIntros (n) "_"; wp_pures.
        rewrite /int_walk_checker.
        (* the rest of the symbolic execution doesn't change depeding on the value.  *)
        case_bool_decide; repeat (try wp_pures; try wp_load; try wp_store).
        * (* l ↦ -3 *)
          iModIntro. iPureIntro. f_equal. f_equal.
          apply bool_decide_eq_true_2. lia.
        * (* l ↦ -1 *)
          iModIntro. iPureIntro. f_equal. f_equal.
          apply bool_decide_eq_true_2. lia.
    - iModIntro.
      iIntros (i p) "(%Hpwf&%Hb&HcrAX&HI)".
      wp_pure.
      wp_apply (ub_wp_wand with "[HcrAX HI]"); first iApply (wp_sampler_amp with "[$]").
      iIntros (s) "[(HI&HAX)|(HI&HAX)]".
      + (* progress *)
        iLeft; iFrame.
        admit.
        (* iIntros "?"; wp_pure.
        iApply (wp_checker_triv with "[$]"). *)
      + (* amplification *)
        iRight; iFrame.
        admit.
        (* S (S p) may or may not be less than (L εᵢ), but if it isn't, we have € 1.
        destruct (le_lt_eq_dec _ _ Hpwf) as [Hp|Hp].
        * iExists (S (S p)).
          iSplitR; [iPureIntro; lia|].
          iFrame.
          iIntros "?"; wp_pure.
          iApply (wp_checker_triv with "[$]").
        * iExFalso.
          iDestruct "HI" as "[%z (_& HIC &_&_)]".
          assert (Hk :  (Z.of_nat (S (L εᵢ)) >= Z.of_nat (L εᵢ))%Z) by lia.
          (* Check (IC_ge_L εᵢ (S (L εᵢ)) Hk). *)
          (* We have an amount of credit greater than or equal to 1, so we conclude *) *)
  Admitted.


  (* TODO: a spec which actually gives the resources for the higher order thing for any € ε and (l ↦ 0).
      - Split the credit in half
        - ((AX εᵢ εₐ kwf) p) is 0 for even relatively small values of p (depends on ε), so this is free.
        - IC is quantified over εᵢ, and AC goes to 0 in the limit of p, so this should exist.
          + We need p <= L, could this be a culprit for not generalizing to unbiased coins?
            Unfold the definitions of (εR L) to see.

  Lemma wp_checker_init

   *)
End integer_walk.

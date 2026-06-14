(** A LOCAL differential-privacy example on the GENERIC language: RANDOMISED
    RESPONSE releases a private bit ε-differentially-privately.

    This is the canonical coin-based local-DP mechanism, and the VALIDATING
    example for the [RR_coin] foundation (previously only canary-tested in
    [lib/coin.v] / [lib/randomized_response.v]).  The mechanism is

        RR_release(x)  :=  x XOR c,   c ~ RR_coin(num, den),

    i.e. it XOR-perturbs the input bit [x] with a noisy coin [c] that is [true]
    with probability [exp(ε)/(exp(ε)+1)], [ε = num/den].  Equivalently it reports
    [x] truthfully with probability [p = exp(ε)/(exp(ε)+1)] and flips with
    probability [1 − p]; the ratio between the two output probabilities is
    [p/(1−p) = exp(ε)], so releasing the bit is [ε]-DP with ZERO additive [δ]
    (a purely MULTIPLICATIVE guarantee) on the discrete bit metric [dbool].

    All the per-distribution machinery (the [RR] notation, the [wp_couple_RR]
    coupling rules, their soundness) lives in the reusable library
    [gen_diffpriv.lib.randomized_response].  A client "enables" RR for its
    development by declaring a signature containing [RR_coin] and providing a
    one-line [SampleIn RR_coin _] instance; after that the section needs nothing
    but [Context `{!diffprivGS Srr Σ}]. *)
From Stdlib Require Import ZArith Reals Psatz.
From clutch.gen_diffpriv Require Import primitive_laws adequacy distance diffpriv_rules.
From clutch.gen_diffpriv.lib Require Import randomized_response.
From clutch.gen_prob_lang Require Import families.
From iris.prelude Require Import options.

Local Open Scope R.

Section randomized_response_example.
  Context {Sg : Sig} `{!SampleIn RR_coin Sg} `{!diffprivGS Sg Σ}.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Sg)).

  (** The randomised-response release program: XOR the private input bit with a
      noisy [RR_coin] draw at privacy rate [ε = num/den]. *)
  Definition RR_release (num den : Z) : val :=
    (λ: "x", BinOp XorOp "x" (RR #num #den #()))%V.

  (** The RR MECHANISM is ε-DP on the bit metric: releasing a private bit via
      randomised response is [(ε, 0)]-differentially-private, [ε = num/den ≥ 0].
      For adjacent inputs (bits at distance 1) the spec coin flips — costing the
      full [ε] — so that the two XOR-released bits agree; for identical inputs the
      release is coupled exactly at zero cost.  This is the canonical local-DP
      guarantee, validating the coin foundation on a real DP proof. *)
  Fact hoare_RR_diffpriv (num den : Z) :
    ⌜0 <= IZR num / IZR den⌝ -∗
    hoare_diffpriv_metric Sg (RR_release num den) (IZR num / IZR den) 0 dbool bool.
  Proof.
    iIntros "%Hpos". rewrite /hoare_diffpriv_metric /RR_release.
    iIntros (K c x x' adj).
    iIntros (Φ) "!> (Hr & Hε & _) HΦ".
    (* [inject x = #x], [inject x' = #x']; β-reduce both releases. *)
    tp_pures. wp_pures.
    tp_bind (Sample _ _ _). wp_bind (Sample _ _ _).
    destruct (bool_decide (x = x')) eqn:Hxx'.
    - (* identical inputs (distance 0): EXACT coupling, no cost. *)
      apply bool_decide_eq_true in Hxx' as ->.
      iApply (wp_couple_RR_exact num den _ ⊤ with "Hr").
      iIntros "!>" (b) "Hr".
      (* Expose the spec redex [BinOp XorOp #x' #b] (folded into the eval
         context by [tp_bind]) at the [fill K _] head, then step the spec while
         the goal is still a WP, and reduce the impl. *)
      iEval (simpl ectx_language.fill) in "Hr".
      tp_pures. wp_pures.
      iModIntro. iApply ("HΦ" $! (xorb x' b)). iFrame.
    - (* adjacent inputs (distance 1): FLIP coupling, cost ε. *)
      apply bool_decide_eq_false in Hxx'.
      (* the bit metric gives [dbool x x' = 1 ≤ c], so [c·ε ≥ 1·ε = ε]. *)
      assert (Hc : 1 <= c).
      { move: adj. rewrite /dbool /distance bool_decide_eq_false_2 //. }
      iDestruct (ecm_weaken _ (IZR num / IZR den) with "Hε") as "Hε".
      { split; [exact Hpos|]. rewrite -{1}(Rmult_1_l (IZR num / IZR den)).
        apply Rmult_le_compat_r; [exact Hpos | exact Hc]. }
      iApply (wp_couple_RR num den (IZR num / IZR den) _ ⊤ eq_refl Hpos
                with "[$Hr $Hε]").
      iIntros "!>" (b) "Hr".
      (* impl outputs [xorb x b]; spec outputs [xorb x' (negb b)]; equal since
         [x' ≠ x] (a 2-valued type, so [x' = negb x]) and the coin flipped. *)
      assert (xorb x' (negb b) = xorb x b) as Hxnb.
      { destruct x, x', b; simpl in *; try done; exfalso; by apply Hxx'. }
      iEval (simpl ectx_language.fill) in "Hr".
      tp_pures. wp_pures.
      rewrite Hxnb. iModIntro. iApply ("HΦ" $! (xorb x b)). iFrame.
  Qed.

End randomized_response_example.

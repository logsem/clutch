(** Total-Eris specification connecting [papa_2sat] to [err_papa].

    What lives here is just the *probabilistic* reasoning: the loop
    invariant tying the [err] recurrence to the random walk on Hamming
    distance, and the headline theorem that uses the [err_papa] bound to
    discharge the [↯ (1/2)] precondition.
*)

From clutch.eris Require Import eris.
From clutch.eris.tutorial Require Import two_sat two_sat_err_rec two_sat_helpers.

Set Default Proof Using "Type*".

Section proof.
  Context `{!erisGS Σ}.

  (** ** Loop specification

      Given [↯ (err nvars iter (hamming bs w))] credits, the loop converges
      to a satisfying assignment within [iter] iterations.  The Hamming
      distance [hamming bs w] to the witness is the random walk's state;
      [err] is the failure-probability bound from [two_sat_err_rec.v].
  *)

  Lemma papa_loop_spec a (cls : list clause) (clsv : val)
        (nvars : nat) (w : list bool) :
    formula_well_formed nvars cls ->
    is_formula cls clsv ->
    length w = nvars ->
    satisfies w cls ->
    forall (iter : nat) (bs : list bool),
    length bs = nvars ->
    [[{ bool_array a bs ∗ ↯ (err nvars iter (hamming bs w)) }]]
      papa_loop #a clsv #iter
    [[{ bs', RET #true;
         bool_array a bs' ∗
         ⌜length bs' = nvars⌝ ∗ ⌜satisfies bs' cls⌝ }]].
  Proof.
    intros Hwf Hform Hwlen Hsatw.
    induction iter as [|iter IH]; intros bs Hlen Φ; iIntros "[Hba Herr] HΦ";
      rewrite /papa_loop; wp_pures; fold papa_loop.
    - (* Base case [iter = 0]: find_unsat must return [None] (otherwise the
         credit [↯ (err nvars 0 k)] is at least [1], a contradiction). *)
      wp_apply (twp_find_unsat with "Hba") as
        (res resv) "(Hba & %Hres & %Hpost)"; try done.
      destruct res as [c|]; last first.
      { simpl in Hres; subst resv. wp_pures;
        iApply ("HΦ" $! bs); iFrame; iPureIntro; by split. }
      destruct Hres as (cv & -> & Hcv). wp_pures.
      destruct Hpost as [Hin Hbad].
      iExFalso. iApply (ec_contradict with "Herr"). eauto.

    - (* Inductive case: find an unsatisfied clause, flip a random literal of
         it via [twp_flip_step], and recurse. *)
      wp_apply (twp_find_unsat with "Hba") as
        (res resv) "(Hba & %Hres & %Hpost)"; try done.
      destruct res as [c|]; last (
        simpl in Hres; subst resv; wp_pures;
        iApply ("HΦ" $! bs); iFrame; iPureIntro; by split).
      destruct Hres as (cv & -> & Hcv). wp_pures.
      destruct Hpost as [Hin Hbad].
      wp_apply (twp_flip_step _ _ c cv cls w nvars iter
                 with "[$Hba $Herr]") as (bs') "(Hba & %Hlen' & Herr)";
        try done.
      wp_pures.
      replace (Z.of_nat (S iter) - 1)%Z with (Z.of_nat iter) by lia.
      wp_apply (IH bs' Hlen' with "[$Hba $Herr]") as (bs'') "?".
      by iApply ("HΦ" $! bs'').
  Qed.

  (** ** Main theorem

      With [↯ (1/2)] error credits and a satisfiable formula, [papa_2sat]
      terminates with [(#true, #a)] where [a] points to a satisfying
      assignment.
  *)

  Theorem papa_2sat_correct (nvars : nat) (cls : list clause) (clsv : val) :
    (1 <= nvars)%nat ->
    formula_well_formed nvars cls ->
    is_formula cls clsv ->
    is_satisfiable nvars cls ->
    [[{ ↯ (1 / 2) }]]
      papa_2sat #nvars clsv #(2 * nvars * nvars)
    [[{ a bs, RET (#true, #a);
         bool_array a bs ∗
         ⌜length bs = nvars⌝ ∗ ⌜satisfies bs cls⌝ }]].
  Proof.
    iIntros (Hnv1 Hwf Hform [w [Hwlen Hsatw]] Φ) "Herr HΦ".
    rewrite /papa_2sat. wp_pures.
    (* Step 1: allocate a uniformly random initial assignment. *)
    wp_apply (twp_init_rand with "[//]"); first done.
    iIntros (a bs) "[Hba %Hbslen]".
    (* Step 2: weaken [↯ (1/2)] to the loop's required budget via [err_papa]. *)
    iAssert (↯ (err nvars (2 * nvars * nvars) (hamming bs w)))
              with "[Herr]" as "Herr".
    { iApply (ec_weaken with "Herr"). split; auto. }
    (* Step 3: run the loop. *)
    wp_pures.
    assert ((2 * nvars * nvars)%Z = (2 * nvars * nvars)%nat) as -> by lia.
    wp_apply (papa_loop_spec _ _ _ _ _ Hwf Hform Hwlen Hsatw _ _ Hbslen
              with "[$Hba $Herr]").
    iIntros (bs') "(Hba & %Hlen' & %Hsat')". wp_pures.
    iApply ("HΦ" $! a bs'). by iFrame.
  Qed.

End proof.

(** * Expected flip-cost of FLDR as a Tachis triple.

    This file states and proves the first "Tachis for FLDR" theorem: at
    Tachis's entropy cost model, the expected number of fair-bit flips
    consumed by the FLDR rejection sampler is at most the table-derived
    rational [flip_cost ws] (which is in fact the exact expectation; only the
    upper bound is mechanized).
    [entropy_entry.v] extends this to FLDR's real entry points (which must
    first build the DDG table), and [entropy_bound.v] bounds [flip_cost ws]
    itself by the Shannon entropy of [ws].

    Scope discipline: Tachis + Eris only (this development targets the
    Tachis-FLDR paper's minimal dependencies).

    We reuse this codebase's own pure DDG-table layer ([model.v], [walk.v],
    [pure.v]) wherever the underlying combinatorics coincide (in particular
    [walk.cnt], the bitstring-acceptance count, which we repurpose as the
    reject-probability numerator via the identity [reject_mass = cnt/2^k]).
    The *depth*-weighted quantity needed for the cost side ([step_mass]) has
    no counterpart in the existing pure layer (that layer only ever counts
    occupancy, never accumulates depth), so it is new content here, but it
    is deliberately shaped as a structural mirror of [walk.cnt]/[pure.dcnt]-
    style recursion so that the two fit into one [node_budget] invariant. *)

From Coq Require Import Arith.PeanoNat Lists.List Reals Psatz Lia.
From clutch.tachis Require Import expected_time_credits ert_weakestpre
  problang_wp proofmode derived_laws ert_rules cost_models adequacy.
From clutch.prob_lang Require Import notation tactics metatheory lang.
From clutch.eris.lib Require Import list.
From clutch.eris.lib.sampling.fldr Require Import model implementation walk pure distribution.
From Coquelicot Require Import Rbar.
Import ListNotations.

Set Default Proof Using "Type*".
#[local] Open Scope R.

(** * 1. Cost model.

    [CostEntropy] already exists in [tachis/cost_models.v]: it charges
    [Rlog base (N+1)] to a redex [rand #N] and 0 to everything else.  With
    [base := 2] this is a genuine "number of fair bits consumed" model:
    [cost (rand #1) = Rlog 2 2 = 1] exactly (a flip costs one bit), and more
    generally [cost (rand #(2^j - 1)) = j] (so the buffered-flip variant,
    [rand #(2^30 - 1)], costs exactly 30, as it should for a model that
    counts fair bits rather than [rand]-calls).  We only need to discharge
    the [1 < base] side condition once, exactly as [batchsampling.v] does
    for its own toy rejection sampler. *)
Program Definition CostEntropy_2 := CostEntropy 2 _.
Next Obligation. lra. Qed.

Section CostFacts.
  Context `{!tachisGS Σ CostEntropy_2}.

  (** The flip primitive of FLDR is untaped [rand #1]; it costs exactly 1. *)
  Lemma cost_rand1 : cost (rand #1)%E = 1.
  Proof.
    simpl. replace (1 + 1) with 2 by lra.
    replace 1 with (INR 1) by done.
    erewrite <-Rlog_pow; first f_equal; lra.
  Qed.
End CostFacts.

(** * 2. The pure cost quantities.

    [step_mass rows c] is the expected number of *additional* flips to
    reach some leaf, starting the walk at row [rows] with counter [c]
    (relative depth 0).  [reject_mass rows c i] is the probability that the
    walk starting there returns label [i].  [node_budget] combines them:
    the expected further cost, given a flat toll [F] must be paid whenever
    the walk lands on label [i] (the reject label, for us).

    Both quantities satisfy, *by construction*, the same one-step unfolding
    equation that [wp_couple_rand_adv_comp] wants for [rand #1]: this is
    what lets the walk's Iris proof recurse without any combinatorial lemma
    at every step -- the only combinatorial fact we still need
    ([reject_mass_cnt] below) is proved once, by reusing [walk.cnt]
    directly, not re-derived. *)

Fixpoint step_mass (rows : list (list nat)) (c : nat) : R :=
  match rows with
  | [] => 0
  | row :: rest =>
      let h := length row in
      let c0 := (2 * c)%nat in
      let c1 := (2 * c + 1)%nat in
      1 + (1/2) * (if c0 <? h then 0 else step_mass rest (c0 - h)%nat)
        + (1/2) * (if c1 <? h then 0 else step_mass rest (c1 - h)%nat)
  end.

Definition reject_mass (rows : list (list nat)) (c i : nat) : R :=
  INR (cnt rows c i) / INR (2 ^ length rows).

Definition node_budget (rows : list (list nat)) (c i : nat) (F : R) : R :=
  step_mass rows c + reject_mass rows c i * F.

Lemma step_mass_nonneg rows c : 0 <= step_mass rows c.
Proof.
  induction rows as [|row rest IH] in c |- *; simpl; [lra|].
  pose proof (IH (2 * c - length row)%nat) as IH0.
  pose proof (IH (2 * c + 1 - length row)%nat) as IH1.
  repeat case_match; simpl in *; lra.
Qed.

Lemma reject_mass_bounds rows c i : 0 <= reject_mass rows c i <= 1.
Proof.
  unfold reject_mass.
  assert (Hpow : (0 < 2 ^ length rows)%nat) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
  assert (Hle : (cnt rows c i <= 2 ^ length rows)%nat).
  { rewrite (cnt_naccept rows c i). unfold naccept.
    rewrite <- (all_bits_length (length rows)).
    apply filter_length_le. }
  assert (Hden : 0 < INR (2 ^ length rows)) by (apply lt_0_INR; lia).
  split.
  - apply Rcomplements.Rdiv_le_0_compat; [apply pos_INR | exact Hden].
  - apply (Rmult_le_reg_r (INR (2 ^ length rows))); [exact Hden|].
    rewrite Rmult_1_l. unfold Rdiv. rewrite Rmult_assoc.
    rewrite Rinv_l; [|lra].
    rewrite Rmult_1_r.
    apply le_INR. exact Hle.
Qed.

(** The one combinatorial fact we need for [reject_mass]: it satisfies the
    same one-step branch-splitting equation as [step_mass], gotten *for
    free* by dividing [walk.cnt]'s own recursive equation through by
    [2 ^ length rows] -- no new induction, this reuses [cnt] verbatim. *)
Lemma reject_mass_cons row rest c i :
  reject_mass (row :: rest) c i =
    (1/2) * (if (2 * c)%nat <? length row then
               (if (nth (2 * c) row 0 =? i)%nat then 1 else 0)
             else reject_mass rest (2 * c - length row)%nat i)
  + (1/2) * (if (2 * c + 1)%nat <? length row then
               (if (nth (2 * c + 1) row 0 =? i)%nat then 1 else 0)
             else reject_mass rest (2 * c + 1 - length row)%nat i).
Proof.
  pose proof (not_0_INR (2 ^ length rest) (Nat.pow_nonzero 2 (length rest) ltac:(lia))) as HD.
  set (D := INR (2 ^ length rest)) in *.
  assert (Hratio : forall c' : nat,
      INR (if (c' <? length row)%nat then leafval row c' i (length rest)
           else cnt rest (c' - length row)%nat i) =
      D * (if (c' <? length row)%nat then (if (nth c' row 0 =? i)%nat then 1 else 0)
           else reject_mass rest (c' - length row)%nat i)).
  { intros c'. destruct (c' <? length row)%nat eqn:Hfit.
    - unfold leafval. destruct (nth c' row 0 =? i)%nat; simpl; fold D; lra.
    - unfold reject_mass. fold D. field. exact HD. }
  unfold reject_mass at 1.
  replace (length (row :: rest)) with (S (length rest)) by reflexivity.
  assert (Hpow2 : (2 ^ (S (length rest)) = 2 ^ length rest + 2 ^ length rest)%nat).
  { rewrite Nat.pow_succ_r'. lia. }
  rewrite Hpow2.
  rewrite plus_INR.
  fold D.
  cbn [cnt].
  rewrite plus_INR.
  rewrite (Hratio (2 * c)%nat).
  rewrite (Hratio (2 * c + 1)%nat).
  replace (D + D) with (2 * D) by lra.
  field. exact HD.
Qed.

(** The combined WP invariant unfolds by the same branch equation. *)
Lemma node_budget_cons row rest c i F :
  node_budget (row :: rest) c i F =
    1 + (1/2) * (if (2 * c)%nat <? length row then
                   (if (nth (2 * c) row 0 =? i)%nat then F else 0)
                 else node_budget rest (2 * c - length row)%nat i F)
      + (1/2) * (if (2 * c + 1)%nat <? length row then
                   (if (nth (2 * c + 1) row 0 =? i)%nat then F else 0)
                 else node_budget rest (2 * c + 1 - length row)%nat i F).
Proof.
  unfold node_budget at 1.
  cbn [step_mass].
  rewrite (reject_mass_cons row rest c i).
  unfold node_budget.
  repeat case_match; lra.
Qed.

(** * 3. [flip_cost]: the fixed point.

    Rather than defining [flip_cost] via the paper's row-length formula
    [(2^k/m) * Sum (j+1) h_j 2^-(j+1)] directly (which would need a second,
    independent combinatorial theorem -- a "sum over all A entering
    counters" lemma in the style of [walk.walk_count], ported to a
    depth-weighted payload -- to connect it back to [step_mass]/[reject_mass]
    at every intermediate walk state, not just the table root), we define it
    *as* the fixed point of the walk's own recursion at the root.  This is
    the same number as the row-length formula gives (checked below on
    [3;2;1] by hand), it is what makes the Löb argument for the rejection
    loop a one-line [field] computation instead of a second induction, and
    the connection to the paper's closed form [Eq/(1-r)] is established in
    [entropy_bound.v] ([step_mass_leaf_form] rewrites [step_mass] at the root
    as the row-length sum [Sum_j (j+1) h_j / 2^(j+1)]). *)
Definition flip_cost (ws : list nat) : R :=
  step_mass (ddg_table ws) 0 / (1 - reject_mass (ddg_table ws) 0 (length ws)).

(** The reject probability of a full round, computed via the walk-based
    [reject_mass], coincides with the pure model's [rejection_weight /
    denominator] -- reusing [walk.cnt_naccept], [pure.fldr_round_count] and
    [model.ddg_table_occupancy_exact] from the pure DDG-table layer
    verbatim, without re-deriving them. *)
Lemma reject_mass_ddg_table ws :
  admissible ws -> nondegenerate ws ->
  reject_mass (ddg_table ws) 0 (length ws) =
    INR (rejection_weight ws) / INR (denominator ws).
Proof.
  intros Hadm Hnd.
  unfold reject_mass.
  rewrite (cnt_naccept (ddg_table ws) 0 (length ws)).
  rewrite (fldr_round_count ws (length ws) Hadm).
  assert (Hi : (length ws < length (extended_weights ws))%nat).
  { unfold extended_weights. rewrite length_app. cbn [length]. lia. }
  assert (Hlt : (nth (length ws) (extended_weights ws) 0 < denominator ws)%nat).
  { apply Hnd. exact Hi. }
  rewrite (ddg_table_occupancy_exact ws (length ws) Hi Hlt).
  assert (Hnth : (nth (length ws) (extended_weights ws) 0 = rejection_weight ws)%nat).
  { unfold extended_weights. apply nth_middle. }
  rewrite Hnth.
  rewrite (ddg_table_depth ws).
  reflexivity.
Qed.

Lemma reject_mass_ddg_table_lt1 ws :
  admissible ws -> nondegenerate ws ->
  reject_mass (ddg_table ws) 0 (length ws) < 1.
Proof.
  intros Hadm Hnd.
  rewrite (reject_mass_ddg_table ws Hadm Hnd).
  pose proof (admissible_weight_sum_pos ws Hadm) as Hsum.
  pose proof (rejection_weight_nonnegative ws Hadm) as Heq.
  pose proof (denominator_pos ws) as Hdenpos.
  apply (Rmult_lt_reg_r (INR (denominator ws))); [apply lt_0_INR; lia|].
  unfold Rdiv. rewrite Rmult_assoc.
  rewrite (Rinv_l (INR (denominator ws))); [|apply not_0_INR; lia].
  rewrite Rmult_1_r Rmult_1_l.
  apply lt_INR. lia.
Qed.

Lemma flip_cost_nonneg ws :
  admissible ws -> nondegenerate ws -> 0 <= flip_cost ws.
Proof.
  intros Hadm Hnd. unfold flip_cost.
  pose proof (reject_mass_ddg_table_lt1 ws Hadm Hnd) as Hlt.
  apply Rcomplements.Rdiv_le_0_compat; [apply step_mass_nonneg | lra].
Qed.

(** The headline fixed-point identity: [flip_cost] closes the Löb loop. *)
Lemma flip_cost_fixed_point ws :
  admissible ws -> nondegenerate ws ->
  node_budget (ddg_table ws) 0 (length ws) (flip_cost ws) = flip_cost ws.
Proof.
  intros Hadm Hnd.
  pose proof (reject_mass_ddg_table_lt1 ws Hadm Hnd) as Hlt.
  unfold node_budget, flip_cost.
  field. lra.
Qed.

(** Sanity check: [flip_cost [3;2;1] = 3] exactly, matching the by-hand
    computation via [Eq = 9/4], [r = 1/4], [Eq/(1-r) = 3]. *)
Lemma flip_cost_321 : flip_cost [3; 2; 1]%nat = 3.
Proof.
  unfold flip_cost.
  rewrite check_321.
  unfold reject_mass.
  simpl.
  lra.
Qed.

(** * 4. Representation of DDG tables as [val]s.

    Deliberately self-contained (no [Inject]/[is_list] typeclass machinery):
    both the Eris-side ([eris/lib/list.v]) and the Tachis-side
    ([tachis/examples/lib/list.v]) generic list libraries package their
    [is_list] predicate inside a GS-parametrized section (erisGS,
    tachisGS CostTick respectively), so importing either one for its
    [is_list] would either need an ambient [erisGS] instance we have no use
    for, or lock us into the wrong cost model.  [fldr_walk] itself (in
    [implementation.v]) is untouched here and still calls Eris's
    [list_length]/[list_nth] (imported above for the closed terms only);
    [is_row]/[is_rows] match their representation ([list_cons a l] ~>
    [SOME (a, l)]) exactly. *)
Fixpoint is_row (l : list nat) (v : val) : Prop :=
  match l with
  | [] => v = NONEV
  | n :: l' => exists lv, v = SOMEV (#n, lv) /\ is_row l' lv
  end.

Fixpoint is_rows (l : list (list nat)) (v : val) : Prop :=
  match l with
  | [] => v = NONEV
  | r :: l' => exists vr vl, v = SOMEV (vr, vl) /\ is_row r vr /\ is_rows l' vl
  end.

Section ListHelpers.
  Context `{!tachisGS Σ CostEntropy_2}.

  (** Ports of [tachis/examples/lib/list.v]'s [wp_list_length]/[wp_list_nth]
      proof scripts verbatim (cost-model agnostic: [list_length]/[list_nth]
      never touch [rand], so every step here is a [CostEntropy]-0 step; the
      tactics already handle that bookkeeping implicitly, exactly as they do
      for [CostTick] there), specialized to [is_row] and to Eris's
      [list_length]/[list_nth] (the closed terms [fldr_walk] actually
      calls). *)
  Lemma wp_list_length_row E (l : list nat) (lv : val) :
    {{{ ⌜is_row l lv⌝ }}}
      list_length lv @ E
    {{{ v, RET #v; ⌜v = length l⌝ }}}.
  Proof.
    iIntros (Φ) "Ha HΦ".
    iInduction l as [|a l'] "IH" forall (lv Φ);
    iDestruct "Ha" as %Ha; simpl in Ha; subst; wp_rec.
    - wp_match. iApply ("HΦ" $! 0%nat); done.
    - destruct Ha as [lv' [Hlv Hlcoh]]; subst.
      wp_match. wp_proj. wp_bind (list_length _).
      iApply ("IH" $! _ _ Hlcoh). iNext. iIntros; simpl.
      wp_op. iSpecialize ("HΦ" $! (1 + v)%nat).
      rewrite Nat2Z.inj_add. iApply "HΦ"; by auto.
  Qed.

  Lemma wp_list_nth_row E (i : nat) l lv :
    {{{ ⌜is_row l lv⌝ }}}
      list_nth lv #i @ E
    {{{ v, RET v; (⌜v = NONEV⌝ ∧ ⌜(length l <= i)%nat⌝) ∨
              ⌜exists r : nat, v = SOMEV #r /\ nth_error l i = Some r⌝ }}}.
  Proof.
    iIntros (Φ) "Ha HΦ".
    iInduction l as [|a l'] "IH" forall (i lv Φ);
    iDestruct "Ha" as %Ha; simpl in Ha; subst; wp_rec; wp_let.
    - wp_match. wp_pures.
      iApply ("HΦ" $! (InjLV #())). iLeft. simpl. eauto with lia.
    - destruct Ha as [lv' [Hlv Hlcoh]]; subst.
      wp_match. wp_pures. case_bool_decide; wp_pures.
      + iApply "HΦ". iRight. simpl. iExists a. by destruct i.
      + destruct i; first done.
        assert ((S i - 1)%Z = i) as -> by lia.
        iApply ("IH" $! i lv' _  Hlcoh).
        iNext. iIntros (v [ (Hv & Hs) | Hps]); simpl.
        * iApply "HΦ"; try eauto with lia.
        * iApply "HΦ"; try eauto with lia.
  Qed.

  Lemma wp_list_nth_row_some E (i : nat) l lv :
    (i < length l)%nat ->
    {{{ ⌜is_row l lv⌝ }}}
      list_nth lv #i @ E
    {{{ v, RET v; ⌜exists r : nat, v = SOMEV #r /\ nth_error l i = Some r⌝ }}}.
  Proof.
    iIntros (Hi Φ) "Ha HΦ".
    wp_apply (wp_list_nth_row with "Ha").
    iIntros (v) "[[-> %Hle] | H]"; [lia|]. by iApply "HΦ".
  Qed.
End ListHelpers.

(** * 5. The walk: [wp_fldr_walk_gen].

    Statement, proof sketch:

    {{{ ⌜is_rows rows vrows⌝ ∗ ⧖ (node_budget rows c n F) }}}
      fldr_walk #() vrows #c
    {{{ i, RET SOMEV #i; ⌜i <= n⌝ ∗ ⧖ (if i =? n then F else 0) }}}

    under [capacity_ok rows A], [cap_final rows A = 0], [c < A] (the
    well-formedness invariant threaded exactly as in [distribution.walk_total]
    -- same three hypotheses, same role: they rule out the [rows = []]-with-
    [c]-still-live dead end, i.e. [fldr_walk] returning [NONE], which cannot
    happen under them), and [n] a bound on every label actually stored in
    [rows] (so the walk's [SOME i] leaf, wherever it lands, always satisfies
    [i <= n]).

    Proof: induction on [rows], generalizing [c], [A], [vrows] (mirrors
    [walk_total]'s own induction shape verbatim, only replacing the
    existential-bitstring conclusion with a WP judgment).

    - [rows = []]: [cap_final [] A = A] by definition, so [Hfin : A = 0%nat];
      with [Hc : c < A] this is [False] -- exfalso/lia, no further work
      (this is exactly why [fldr_walk]'s [NONE => NONE] branch is dead code
      under the invariant: the induction never reaches it).

    - [rows = row :: rest]: unfold [is_rows] to get [vr]/[vl] with
      [vrows = SOMEV (vr, vl)]; [wp_pures] through the [rec]/[match]/[let]s
      down to the [rand("α") #1] redex (["α"] is literally [#()] throughout,
      since [fldr_walk #() vrows #c]'s "α" parameter never changes across
      recursive calls -- so this really is untaped [rand #1], and the
      [wp_couple_rand_adv_comp] rule applies directly, with no taped-rand
      machinery needed).

      Split the budget via [wp_couple_rand_adv_comp] with per-branch payouts
      [x0]/[x1] read off [node_budget_cons]'s RHS at [b := 0]/[b := 1]: this
      is *definitional* (the equation IS [node_budget_cons], so the
      [wp_couple_rand_adv_comp] side condition [cost (rand #1) + ((1/2)*x0 +
      (1/2)*x1) = node_budget (row::rest) c n F] is exactly [cost_rand1] plus
      [node_budget_cons] plus [lra] -- no new arithmetic).

      For each returned bit [b : fin 2] (case [b = 0%fin] / [b = 1%fin],
      enumerated the same way [walk_spec.twp_fldr_walk_tape] does since
      [inv_fin] isn't used in this codebase's house style): [wp_pures]
      computes [c' := 2*c+b] concretely; [wp_bind]/[wp_apply
      wp_list_length_row] gets [h := length row]; [case_bool_decide] on
      [c' < h] exactly mirrors the [x0]/[x1] "if" branch:

      + leaf ([c' < h]): [wp_apply wp_list_nth_row_some] returns
        [i := nth c' row 0]; [Hbound] gives [i <= n]; case on [i =? n] to
        match the promised credit ([F] if [i = n], matching [x0]/[x1]'s
        leaf value by construction; [0] otherwise, and the leftover credit
        from [x0]/[x1]'s leaf value literally *is* [if i=?n then F else 0]
        already, no re-derivation).

      + continue ([c' >= h]): recurse via the induction hypothesis on
        [rest], [c' - h], residual capacity [2*A - h] (from [Hcap]'s second
        component); the credit [x0]/[x1]'s continue-branch value is
        [node_budget rest (c'-h) n F] by construction, exactly what the IH
        wants.

    Sub-lemmas needed along the way: [node_budget_nonneg] (just below, for
    [wp_couple_rand_adv_comp]'s nonnegativity/boundedness side conditions),
    and a [fin 2]-enumeration fact (inlined in the proof below, the same way
    [walk_spec.v] does it, not worth a standalone lemma). *)

Lemma node_budget_nonneg rows c i F :
  0 <= F -> 0 <= node_budget rows c i F.
Proof.
  intros HF. unfold node_budget.
  pose proof (step_mass_nonneg rows c).
  pose proof (reject_mass_bounds rows c i) as [? ?].
  nra.
Qed.

Section Walk.
  Context `{!tachisGS Σ CostEntropy_2}.

  Lemma wp_fldr_walk_gen E (rows : list (list nat)) (vrows : val) (c A n : nat) (F : R) :
    capacity_ok rows A ->
    cap_final rows A = 0%nat ->
    (c < A)%nat ->
    (forall row, In row rows -> forall j, In j row -> (j <= n)%nat) ->
    0 <= F ->
    {{{ ⌜is_rows rows vrows⌝ ∗ ⧖ (node_budget rows c n F) }}}
      fldr_walk #() vrows #c @ E
    {{{ i, RET SOMEV #i; ⌜(i <= n)%nat⌝ ∗ ⧖ (if (i =? n)%nat then F else 0) }}}.
  Proof.
    iIntros (Hcap Hfin Hc Hbound HFnn Φ) "[%Hrows Hx] HΦ".
    iInduction rows as [|row rest IH] "IH" forall (c A vrows Hcap Hfin Hc Hbound Hrows).
    - exfalso. simpl in Hfin. lia.
    - destruct Hrows as (vr & vl & -> & Hvr & Hvl).
      destruct Hcap as [Hrow Hcap'].
      rewrite /fldr_walk. wp_pures.
      pose proof (node_budget_cons row rest c n F) as Hunfold.
      set (x0 := if (2 * c)%nat <? length row then
                   (if (nth (2 * c) row 0 =? n)%nat then F else 0)
                 else node_budget rest (2 * c - length row)%nat n F).
      set (x1 := if (2 * c + 1)%nat <? length row then
                   (if (nth (2 * c + 1) row 0 =? n)%nat then F else 0)
                 else node_budget rest (2 * c + 1 - length row)%nat n F).
      fold x0 in Hunfold. fold x1 in Hunfold.
      assert (Hx0 : 0 <= x0).
      { unfold x0. case_match; [case_match; lra | apply node_budget_nonneg; lra]. }
      assert (Hx1 : 0 <= x1).
      { unfold x1. case_match; [case_match; lra | apply node_budget_nonneg; lra]. }
      wp_bind (rand(#()) #1)%E.
      wp_apply (wp_couple_rand_adv_comp _ _ _ _ _
                  (fun b : fin 2 => if (fin_to_nat b =? 0)%nat then x0 else x1)
                  with "Hx").
      + intros b'. case_match; lra.
      + exists (Rmax x0 x1). intros b'. case_match; [apply Rmax_l | apply Rmax_r].
      + rewrite cost_rand1. rewrite SeriesC_finite_foldr. simpl. rewrite Hunfold. lra.
      + iIntros (bval) "Hx".
        assert (Hbval : bval = 0%fin \/ bval = 1%fin).
        { pose proof (fin_to_nat_lt bval) as Hlt.
          destruct (fin_to_nat bval) as [|[|]] eqn:Hbn.
          - left. apply fin_to_nat_inj. by rewrite Hbn.
          - right. apply fin_to_nat_inj. by rewrite Hbn.
          - lia. }
        destruct Hbval as [-> | ->].
        * simpl. wp_pures.
          wp_bind (list_length _).
          wp_apply (wp_list_length_row with "[//]").
          iIntros (h) "%Hh".
          wp_pures.
          case_bool_decide as Hfit.
          -- (* leaf: 2c+0 < h *)
             wp_if.
             assert (Hfit_nat : (2 * c < length row)%nat) by lia.
             assert (Hidx : #(Z.add (Z.mul 2 (Z.of_nat c)) (Z.of_nat 0)) = #(2 * c)%nat).
             { f_equal. f_equal. lia. }
             rewrite Hidx.
             wp_bind (list_nth _ _)%E.
             wp_apply (wp_list_nth_row with "[//]").
             iIntros (v) "[[-> %Hle]|%Hv]"; [lia|]. destruct Hv as (i & -> & Hnth).
             iApply "HΦ". iSplit.
             ++ iPureIntro. apply (Hbound row); [left; reflexivity|].
                eapply nth_error_In. exact Hnth.
             ++ iEval (rewrite /x0) in "Hx".
                assert (Hb0 : ((2 * c)%nat <? length row)%nat = true).
                { apply Nat.ltb_lt. lia. }
                iEval (rewrite Hb0) in "Hx".
                assert (Hnth' : (nth (2 * c) row 0 = i)%nat).
                { pose proof (nth_error_nth' row 0%nat Hfit_nat) as Hne.
                  rewrite Hnth in Hne. congruence. }
                rewrite Hnth'. iExact "Hx".
          -- (* continue *)
             wp_if.
             assert (Hfit_nat2 : (length row <= 2 * c)%nat) by lia.
             wp_pure _.
             assert (Hidx2 :
               #(Z.sub (Z.add (Z.mul 2 (Z.of_nat c)) (Z.of_nat 0)) (Z.of_nat h)) =
               #(2 * c - length row)%nat).
             { f_equal. f_equal. lia. }
             rewrite Hidx2.
             cbn [cap_final] in Hfin.
             iEval (rewrite /x0) in "Hx".
             assert (Hb0' : ((2 * c)%nat <? length row)%nat = false).
             { apply Nat.ltb_ge. lia. }
             iEval (rewrite Hb0') in "Hx".
             assert (Hlt_cA : (2 * c - length row < 2 * A - length row)%nat) by lia.
             assert (Hbound' : forall row0 : list nat,
                        In row0 rest -> forall j : nat, In j row0 -> (j <= n)%nat).
             { intros row0 Hin j Hj. apply (Hbound row0); [right; exact Hin | exact Hj]. }
             iSpecialize ("IH" $! (2 * c - length row)%nat (2 * A - length row)%nat vl
                            Hcap' Hfin Hlt_cA Hbound' Hvl).
             wp_apply ("IH" with "Hx").
             iIntros (i) "[%Hi Hcred]".
             iApply "HΦ". iFrame. done.
        * simpl. wp_pures.
          wp_bind (list_length _).
          wp_apply (wp_list_length_row with "[//]").
          iIntros (h) "%Hh".
          wp_pures.
          case_bool_decide as Hfit.
          -- (* leaf: 2c+1 < h *)
             wp_if.
             assert (Hfit_nat : (2 * c + 1 < length row)%nat) by lia.
             assert (Hidx : #(Z.add (Z.mul 2 (Z.of_nat c)) (Z.of_nat 1)) = #(2 * c + 1)%nat).
             { f_equal. f_equal. lia. }
             rewrite Hidx.
             wp_bind (list_nth _ _)%E.
             wp_apply (wp_list_nth_row with "[//]").
             iIntros (v) "[[-> %Hle]|%Hv]"; [lia|]. destruct Hv as (i & -> & Hnth).
             iApply "HΦ". iSplit.
             ++ iPureIntro. apply (Hbound row); [left; reflexivity|].
                eapply nth_error_In. exact Hnth.
             ++ iEval (rewrite /x1) in "Hx".
                assert (Hb1 : ((2 * c + 1)%nat <? length row)%nat = true).
                { apply Nat.ltb_lt. lia. }
                iEval (rewrite Hb1) in "Hx".
                assert (Hnth' : (nth (2 * c + 1) row 0 = i)%nat).
                { pose proof (nth_error_nth' row 0%nat Hfit_nat) as Hne.
                  rewrite Hnth in Hne. congruence. }
                rewrite Hnth'. iExact "Hx".
          -- (* continue *)
             wp_if.
             assert (Hfit_nat2 : (length row <= 2 * c + 1)%nat) by lia.
             wp_pure _.
             assert (Hidx2 :
               #(Z.sub (Z.add (Z.mul 2 (Z.of_nat c)) (Z.of_nat 1)) (Z.of_nat h)) =
               #(2 * c + 1 - length row)%nat).
             { f_equal. f_equal. lia. }
             rewrite Hidx2.
             cbn [cap_final] in Hfin.
             iEval (rewrite /x1) in "Hx".
             assert (Hb1' : ((2 * c + 1)%nat <? length row)%nat = false).
             { apply Nat.ltb_ge. lia. }
             iEval (rewrite Hb1') in "Hx".
             assert (Hlt_cA : (2 * c + 1 - length row < 2 * A - length row)%nat) by lia.
             assert (Hbound' : forall row0 : list nat,
                        In row0 rest -> forall j : nat, In j row0 -> (j <= n)%nat).
             { intros row0 Hin j Hj. apply (Hbound row0); [right; exact Hin | exact Hj]. }
             iSpecialize ("IH" $! (2 * c + 1 - length row)%nat (2 * A - length row)%nat vl
                            Hcap' Hfin Hlt_cA Hbound' Hvl).
             wp_apply ("IH" with "Hx").
             iIntros (i) "[%Hi Hcred]".
             iApply "HΦ". iFrame. done.
  Qed.
End Walk.

(** * 6. The rejection loop: Löb, closed by [flip_cost_fixed_point].

    Statement, proof sketch:

    {{{ ⌜is_rows rows vrows⌝ ∗ ⧖ F }}}
      fldr_loop #() vrows #n
    {{{ i, RET #i; ⌜i < n⌝ }}}

    given the SAME well-formedness triple at [A := 1] (matching
    [ddg_table_capacity]/[ddg_table_cap_final] for a real table), [Hbound]
    at this [n], and the ONE extra hypothesis that closes the loop:
    [node_budget rows 0 n F = F] -- i.e. [F] is a fixed point of the walk's
    own recursion at the root.  For [F := flip_cost ws], [rows := ddg_table
    ws], [n := length ws], this is exactly [flip_cost_fixed_point] (proved
    above by [field], from the definition [flip_cost := step_mass/(1-
    reject_mass)] -- no combinatorial argument needed, unlike a row-length-
    formula-based [flip_cost] would have required).

    Proof: [iLöb], [wp_bind] the [fldr_walk] call, feed it [⧖ F] rewritten
    (via the fixed-point equation) to [⧖ (node_budget rows 0 n F)] --
    exactly [wp_fldr_walk_gen]'s precondition at [c := 0], [A := 1].  Get
    back [i <= n] with credit [if i=?n then F else 0].  Case on [i <? n]
    (matching the *program*'s own test): [i < n] is the accept leaf,
    return; [i = n] (the only remaining case, since [i <= n]) is the reject
    leaf, and the returned credit is exactly [F] again -- close with the
    Löb hypothesis.  [fldr_walk]'s [NONE] case never arises (per
    [wp_fldr_walk_gen]'s postcondition, unconditionally [SOME]), so
    [fldr_loop]'s [NONE => loop] branch is dead code under these
    hypotheses, exactly as [distribution.walk_total_table] already
    establishes at the pure level. *)

Section Loop.
  Context `{!tachisGS Σ CostEntropy_2}.

  Lemma wp_fldr_loop E (rows : list (list nat)) (vrows : val) (n : nat) (F : R) :
    capacity_ok rows 1 ->
    cap_final rows 1 = 0%nat ->
    (forall row, In row rows -> forall j, In j row -> (j <= n)%nat) ->
    0 <= F ->
    node_budget rows 0 n F = F ->
    {{{ ⌜is_rows rows vrows⌝ ∗ ⧖ F }}}
      fldr_loop #() vrows #n @ E
    {{{ i, RET #i; ⌜(i < n)%nat⌝ }}}.
  Proof.
    iIntros (Hcap Hfin Hbound HFnn Hfix Φ) "[%Hrows Hx] HΦ".
    iLöb as "IH" forall (Φ) "Hx HΦ".
    rewrite /fldr_loop. wp_pures.
    wp_bind (fldr_walk _ _ _)%E.
    iAssert (⌜is_rows rows vrows⌝ ∗ ⧖ (node_budget rows 0 n F))%I with "[Hx]" as "Hpre".
    { iSplit; [done|]. iApply (etc_irrel with "Hx"). by symmetry. }
    wp_apply (wp_fldr_walk_gen E rows vrows 0 1 n F Hcap Hfin ltac:(lia) Hbound HFnn with "Hpre").
    iIntros (i) "[%Hi Hcred]".
    wp_pures.
    case_bool_decide as Hlt.
    - wp_pures. iApply "HΦ". iPureIntro. lia.
    - assert (Heq : i = n) by lia.
      subst i.
      rewrite Nat.eqb_refl.
      wp_if.
      iApply ("IH" with "Hcred HΦ").
  Qed.
End Loop.

(** * 7. Specializing to FLDR, and the ERT adequacy corollary.

    [wp_fldr_loop_flip_cost] instantiates the generic loop triple at
    [rows := ddg_table ws], [n := length ws], [F := flip_cost ws]: the
    well-formedness hypotheses come straight from
    [model.ddg_table_capacity]/[distribution.ddg_table_cap_final]/
    [model.ddg_table_index_bound] (ported verbatim, without re-deriving
    them), and the fixed-point hypothesis is exactly [flip_cost_fixed_point].
    This gives the [fldr_walk]/[fldr_loop] half of the flip-cost bound,
    GIVEN an already-built DDG table.  Closing the remaining gap to the real
    entry points [fldr]/[fldr_sample] -- which must first call the
    *preprocessing* function [fldr_table] to build that table -- needs its
    own Tachis-side functional-correctness proof of [preprocessing.v]'s
    construction, since Eris's total-WP judgment and Tachis's partial-WP
    judgment are built over different resource algebras and there is no
    generic lemma turning one triple into the other; [entropy_entry.v]
    supplies that proof.

    [fldr_loop_ERT_bound]/[_lim] then discharge Tachis's own [wp_ERT]/
    [wp_ERT_lim] against [wp_fldr_loop_flip_cost], giving the honest
    reading: *given* a constructed table [vrows], the expected number of
    fair-bit flips the rejection loop consumes, at every finite horizon and
    in the limit, is at most [flip_cost ws]. *)

Corollary wp_fldr_loop_flip_cost `{!tachisGS Σ CostEntropy_2} E (ws : list nat) (vrows : val) :
  admissible ws -> nondegenerate ws ->
  {{{ ⌜is_rows (ddg_table ws) vrows⌝ ∗ ⧖ (flip_cost ws) }}}
    fldr_loop #() vrows #(length ws) @ E
  {{{ i, RET #i; ⌜(i < length ws)%nat⌝ }}}.
Proof.
  intros Hadm Hnd.
  apply wp_fldr_loop.
  - apply ddg_table_capacity. exact Hadm.
  - apply ddg_table_cap_final; assumption.
  - intros row Hin j Hj.
    pose proof (ddg_table_index_bound ws row j Hin Hj) as Hb.
    unfold extended_weights in Hb. rewrite length_app in Hb. cbn [length] in Hb. lia.
  - apply flip_cost_nonneg; assumption.
  - apply flip_cost_fixed_point; assumption.
Qed.

Corollary fldr_loop_ERT_bound Σ `{!tachisGpreS Σ} (ws : list nat) (vrows : val) (σ : state) (k : nat) :
  admissible ws -> nondegenerate ws -> is_rows (ddg_table ws) vrows ->
  ERT (costfun := CostEntropy_2) k (fldr_loop #() vrows #(length ws), σ) <= flip_cost ws.
Proof.
  intros Hadm Hnd Hrows.
  pose proof (flip_cost_nonneg ws Hadm Hnd) as Hnn.
  apply (wp_ERT CostEntropy_2 Σ _ σ k (mknonnegreal (flip_cost ws) Hnn)
           (fun v => exists i : nat, v = #i /\ (i < length ws)%nat)).
  iIntros (?) "Hx".
  wp_apply (wp_fldr_loop_flip_cost with "[Hx]"); [exact Hadm|exact Hnd| |].
  - iSplit; [done|iExact "Hx"].
  - iIntros (i) "%Hi". iPureIntro. eauto.
Qed.

Corollary fldr_loop_ERT_bound_lim Σ `{!tachisGpreS Σ} (ws : list nat) (vrows : val) (σ : state) :
  admissible ws -> nondegenerate ws -> is_rows (ddg_table ws) vrows ->
  lim_ERT (costfun := CostEntropy_2) (fldr_loop #() vrows #(length ws), σ) <= flip_cost ws.
Proof.
  intros Hadm Hnd Hrows.
  pose proof (flip_cost_nonneg ws Hadm Hnd) as Hnn.
  unshelve epose proof (wp_ERT_lim CostEntropy_2 Σ
           (fldr_loop #() vrows #(length ws)) σ (mknonnegreal (flip_cost ws) Hnn)
           (fun v => exists i : nat, v = #i /\ (i < length ws)%nat) _) as H.
  { iIntros (?) "Hx".
    wp_apply (wp_fldr_loop_flip_cost with "[Hx]"); [exact Hadm|exact Hnd| |].
    - iSplit; [done|iExact "Hx"].
    - iIntros (i) "%Hi". iPureIntro. eauto. }
  apply H.
Qed.

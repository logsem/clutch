(** The Sparse Vector Technique (SVT) DP case study, ported from
    [clutch.diffpriv.examples.sparse_vector_technique] to the GENERIC language.
    "Enable" the Laplace distribution (one signature + one [SampleIn] instance),
    pin the spec-context [fill], and the proofs go through with the standard
    proof-mode tactics and the library Laplace coupling rules (VALUE-FORM variants)
    [wp_couple_laplace] / [wp_couple_laplace_choice].  See
    [report_noisy_max_pointwise] for the gen-specific spec-tactic fixes that we
    replicate here. *)
From iris.base_logic Require Export na_invariants.
From clutch.prelude Require Import tactics.
From clutch.prob Require Import differential_privacy.
From clutch.gen_diffpriv Require Import all.
From clutch.gen_diffpriv.lib Require Import laplace laplace_choice.
From clutch.gen_prob_lang Require Import inject families.
From clutch.gen_diffpriv.examples Require Import list.
From iris.prelude Require Import options.

(** This development is PARAMETRIC over any signature [Sg] that contains
    [laplace_family] (recovered via the ambient [SampleIn laplace_family Sg]
    instance) — so SVT composes with any other mechanism (e.g. exponential RNM)
    whose program samples from a richer signature.  A client picks the concrete
    [Sg] only when closing the development at adequacy.  ([Sg], not [S], to avoid
    shadowing the nat successor [S] used in the proofs.) *)

(** [inject x] at type [expr] is not [Val]-headed in [gen_prob_lang]; expose the
    [Val] head without [simpl]ing the abstract spec context [fill K]. *)
Lemma inject_expr_Val {A} `{!Inject A val} (x : A) :
  (inject x : expr) = Val (inject x).
Proof. reflexivity. Qed.

Lemma inject_Z_val (z : Z) : (inject z : val) = LitV (LitInt z).
Proof. reflexivity. Qed.

(** Keep the family index [sample_idx] folded so the [Laplace] surface notation
    matches the library coupling rules syntactically. *)
#[global] Opaque sample_idx.

Section svt.
  Context {Sg : Sig} `{!SampleIn laplace_family Sg} `{!diffprivGS Sg Σ}.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Sg)).

  #[local] Open Scope R.

  (** Spec heap tactics leave the spec hyp FOCUSED in [gen]; re-fold with
      [tp_normalise] so following [tp_pures] sees the surrounding redex.  Cf.
      [report_noisy_max_pointwise]. *)
  (** Fully reduce both sides (including any BinOp [#k * #den] and the [Pair]
      parameter) to value form, then bind the [Sample] on both sides.  The
      value-form coupling rules [wp_couple_laplace] / [wp_couple_laplace_choice]
      expect [Sample lidx (Val (PairV ...)) (Val #())] which is exactly what
      [tp_pures; wp_pures] produce. *)
  Ltac lap_focus :=
    tp_normalise; rewrite ?inject_Z_val;
    tp_pures; wp_pures;
    tp_bind (Sample _ _ _); wp_bind (Sample _ _ _).
  Ltac tpload  := tp_load;  tp_normalise.
  Ltac tpstore := tp_store; tp_normalise.

  Lemma Rdiv_pos_pos x y a (div_pos: 0 < x/y) (den_pos : 0 < a) : 0 < x / (a*y).
  Proof.
    destruct (Rdiv_pos_cases _ _ div_pos) as [[]|[]].
    - apply Rdiv_pos_pos ; real_solver.
    - apply Rdiv_neg_neg ; try real_solver.
      rewrite Rmult_comm.
      apply Rmult_neg_pos => //.
  Qed.

  Lemma Rdiv_nneg_nneg x y a (div_nneg: 0 <= x/y) (den_nneg : 0 <= a) : 0 <= x / (a*y).
  Proof.
    destruct (Rle_lt_or_eq _ _ div_nneg) as [|h].
    - destruct (Rle_lt_or_eq _ _ den_nneg).
      + left. apply Rdiv_pos_pos => //.
      + subst. rewrite Rmult_0_l. rewrite Rdiv_0_r. done.
    - rewrite Rmult_comm. rewrite Rdiv_mult_distr. rewrite -h. rewrite /Rdiv. lra.
  Qed.

  Lemma Rdiv_pos_den_0 x y (div_pos : 0 < x/y) : ¬ y = 0.
  Proof.
    intro d0. rewrite d0 in div_pos. rewrite Rdiv_0_r in div_pos. lra.
  Qed.


  (* If we add a flag to track whether an above-threshold query has been found, we can remain
  private (and return AUTH) even after finding such a query by returning None. Probably not very
  useful in practice. *)
  Definition above_threshold_reset : val :=
    λ:"num" "den" "T",
      let: "T'" := Laplace "num" (#2*"den") "T" #() in
      let: "reset" := ref #false in
      λ:"db",
        let: "f" :=
          (λ: "qi",
             if: ! "reset" then
               NONE
             else
               (let: "vi" := Laplace "num" (#4*"den") ("qi" "db") #() in
                (if: "T'" ≤ "vi" then
                   "reset" <- #true ;;
                   SOME #true
                 else
                   SOME #false)))
        in "f".

  (* We don't actually need `reset` since it is always set to `false` so long as a client holds AUTH. *)
  Definition above_threshold : val :=
    λ:"num" "den" "T",
      let: "T'" := Laplace "num" (#2*"den") "T" #() in
      λ:"db" "qi",
        let: "vi" := Laplace "num" (#4*"den") ("qi" "db") #() in
        "T'" ≤ "vi".

  (* The spec that AT satisfies after initialising T'.  Parametric over the
     query sensitivity [Δ ≥ 1]; with [Δ = 1] this is exactly the original
     sensitivity-1 spec ([wp_sensitive Sg q 1 dDB dZ]). *)
  Definition AT_spec (Δ : Z) (c : R) (AUTH : iProp Σ) (f f' : val) : iProp Σ :=
    □ ∀ `(dDB : Distance DB) (db db' : DB) (_ : dDB db db' <= c) (q : val) (K0 : list ectx_item),
      wp_sensitive Sg q (IZR Δ) dDB dZ -∗
      AUTH -∗
      ⤇ fill K0 (f' (inject db') q) -∗
      WP f (inject db) q
        {{ v, ∃ (b : bool), ⌜v = #b⌝ ∗ ⤇ fill K0 #b ∗
                            (⌜b = false⌝ -∗ AUTH) }}.

  Definition SVT_spec (Δ : Z) (C : Z) (f f' : val) (iSVT : nat → iProp Σ) : iProp Σ :=
    (∀ `(dDB : Distance DB) (db db' : DB) (adj : dDB db db' <= IZR C) (q : val) K,
          wp_sensitive Sg (Val q) (IZR Δ) dDB dZ -∗
          ⤇ fill K (Val f' (inject db') q) -∗
          ∀ n, iSVT (S n) -∗
               WP Val f (inject db) q
                 {{v, ⤇ fill K (Val v) ∗
                      ∃ b : bool, ⌜v = #b⌝ ∗ iSVT (if b then n else S n) }}
      ).

  Definition SVT_online_AT_inlined (num den : Z) : val :=
    λ:"T" "c",
      let: "found_above_T" := ref #true in
      let: "T'" := ref "T" in
      let: "count" := ref #0 in
      let: "f" :=
        λ:"db" "qi",
          if: "c" < !"count" then NONEV else
            SOME
              ((if: ! "found_above_T" then
                  (* need to reset T' from T with fresh noise *)
                  "T'" <- Laplace #num ("c" * #(2*den)) "T" #() else #()) ;;
               let: "vi" := Laplace #num #(4*den) ("qi" "db") #() in
               if: "T'" ≤ "vi" then
                 "found_above_T" <- #true ;;
                 "count" <- !"count"+#1 ;;
                 #true
               else
                 #false)
      in "f".

  Definition oSVT : val :=
    λ:"num" "den" "T" "N",
      let: "count" := ref ("N" - #1) in
      let: "AT" := ref (above_threshold "num" "den" "T") in
      λ:"db" "qi",
        let: "bq" := !"AT" "db" "qi" in
        (if: #0 < !"count" `and` "bq" then
           ("AT" <- (above_threshold "num" "den" "T") ;;
            "count" <- !"count" - #1)
         else #()) ;;
        "bq".


  (* We prove the (non-pw) spec for oAT from hoare_couple_laplace_choice.
     Generalised to query sensitivity [Δ ≥ 1] AND integer adjacency radius
     [C ≥ 1] (group privacy / k-adjacency): the adjacency bound enters only via
     the Lipschitz query gap, so at radius [C] the per-query gap is [Δ·C] and the
     integer-shift threshold/choice couplings run at effective sensitivity [Δ·C].
     The noise budget scales to [C·Δ·(num/den)], with [C = 1] recovering the
     original [Δ·(num/den)] bound (since [IZR 1 * x = x] and [Δ*1 = Δ]). *)
  Lemma above_threshold_online_AT_spec (Δ : Z) (HΔ : (1 <= Δ)%Z) (C : Z) (HC : (1 <= C)%Z) (num den T : Z)
    (εpos : 0 < IZR num / IZR den) K :
    ↯m (IZR C * (IZR Δ * (IZR num / IZR den))) -∗
    ⤇ fill K ((Val above_threshold) #num #den #T)
    -∗ WP (Val above_threshold) #num #den #T
         {{ f, ∃ (f' : val) (AUTH : iProp Σ),
               ⤇ fill K (Val f') ∗ AUTH ∗ AT_spec Δ (IZR C) AUTH f f' }}.
  Proof with (tp_pures ; wp_pures).
    iIntros "ε rhs". rewrite /above_threshold.
    tp_pures. tp_normalise. wp_pures.
    tp_bind (Sample _ _ _). wp_bind (Sample _ _ _).
    assert (HΔpos : (0 <= IZR Δ)%R) by (apply IZR_le; lia).
    assert (HCpos : (0 <= IZR C)%R) by (apply IZR_le; lia).
    set (ε := (IZR num / IZR den)).
    replace (IZR C * (IZR Δ * ε))%R with (IZR C * (IZR Δ * ε) / 2 + IZR C * (IZR Δ * ε) / 2)%R by real_solver.
    fold ε in εpos.
    iDestruct (ecm_split with "ε") as "[ε ε']". 1,2: real_solver.
    (* effective per-query sensitivity is [Δ*C]; init the threshold with shift [Δ*C].
       INTERLEAVED site: the [wp_bind]/[tp_bind] above (line ~185), then the
       [set ε]/[replace]/[ecm_split] setup, happen BEFORE this apply — so the
       bundled [couple_laplace]/[couple_laplace_cost] (which fuse bind+apply
       atomically) cannot be used here.  The APPLY-ONLY [couple_laplace_apply]
       does ONLY the rule apply + side-condition discharge, routing the credit
       [ε'] (unframed) for the [ecm_eq] reconciliation below.  ([Δ*C] annotated
       [%Z] because the args are parsed as [uconstr] under the ambient [Open
       Scope R], so a bare [*] would parse as [Rmult].) *)
    couple_laplace_apply (Δ*C)%Z (Δ*C)%Z with "[$rhs ε']".
    (* apply-only leaves the NON-TRIVIAL side-conditions for the caller, in order:
       (1) the positivity [εpos] of the [2*den]-scaled rate, (2) the
       multiplicative-credit goal (reconciled by [ecm_eq]), (3) the postcondition.
       (The trivial [Hε]/[Hε']/[Hdist] were auto-discharged by the tactic.) *)
    { rewrite mult_IZR ; apply Rdiv_pos_pos. 1,2: real_solver. }
    { iApply ecm_eq. 2: iFrame. subst ε. rewrite mult_IZR. replace (IZR (2 * den)) with (2 * IZR den).
      2: qify_r ; zify_q ; lia.
      field. eapply Rdiv_pos_den_0 => //. }
    iIntros (T') "!> rhs". tp_normalise...
    iModIntro. iExists _. iFrame "rhs".
    iExists (↯m (IZR C * (IZR Δ * ε) / 2))%I. iFrame "ε". clear K.
    iModIntro. iIntros (DB dDB db db' adj q K) "q_sens ε rhs"...
    tp_bind (q _) ; wp_bind (q _). rewrite /wp_sensitive.
    iSpecialize ("q_sens" $! HΔpos _ db db' with "rhs").
    iApply (wp_strong_mono'' with "q_sens [ε]") => //.
    iIntros (?) "(%vq_l & %vq_r & -> & rhs & %adj')".
    assert (- (Δ*C) <= vq_l - vq_r <= Δ*C)%Z as [].
    {
      assert (dZ vq_l vq_r <= IZR Δ * IZR C) as h.
      { etrans; first apply adj'.
        apply Rmult_le_compat_l; [exact HΔpos|]. exact adj. }
      revert h. rewrite /dZ/distance Rabs_Zabs -mult_IZR.
      apply Zabs_ind ; intros ? h; split.
      all: pose proof (le_IZR _ _ h) ; lia.
    }
    lap_focus.
    iApply (wp_couple_laplace_choice (S:=Sg) (Δ*C) ltac:(lia) vq_l (vq_r) T' with "[$]") => //.
    1: apply Zabs_ind ; lia.
    1: rewrite mult_IZR ; apply Rdiv_pos_pos. 1,2: real_solver.
    { subst ε. rewrite !mult_IZR. field. eapply Rdiv_pos_den_0 => //. }
    iIntros "%z !> (%z' & rhs & hh)".
    iDestruct "hh" as "[%h_above | [%h_below ε]]".
    - tp_normalise... case_bool_decide.
      + iFrame. iModIntro. case_bool_decide. 2: lia. iSplit => //. by iIntros (?).
      + lia.
    - tp_normalise... destruct h_below. case_bool_decide.
      + lia.
      + iModIntro. iFrame. case_bool_decide ; try lia. repeat iSplitR => //.
    Unshelve. all: try exact Sg.
  Qed.


  (* We can now prove the non-pw spec for oSVT without much pain.
     Generalised to query sensitivity [Δ ≥ 1] and integer adjacency radius
     [C ≥ 1] (group privacy / k-adjacency); the noise budget scales to
     [N·C·Δ·ε], with [C = 1] recovering the [N·Δ·ε] bound. *)
  Lemma SVT_online_diffpriv (Δ : Z) (HΔ : (1 <= Δ)%Z) (C : Z) (HC : (1 <= C)%Z) (num den T : Z) (N : nat) (Npos : (0 < N)%nat) K :
    let ε := IZR num / IZR den in
    ∀ (εpos : 0 < ε),
      ↯m (N * (IZR C * (IZR Δ * ε))) -∗
      ⤇ fill K (oSVT #num #den #T #N) -∗
      WP oSVT #num #den #T #N
        {{ f,
             ∃ (f' : val) (iSVT : nat → iProp Σ),
              ⤇ fill K f' ∗
              iSVT N ∗
             □ SVT_spec Δ C f f' iSVT
        }}.
  Proof with (tp_pures ; wp_pures).
    (* make sure we have at least enough credit to initialise AT once *)
    destruct N as [|N'] ; [lia|] ; clear Npos.
    iIntros (??) "SNε rhs". rewrite /oSVT...
    assert (HΔpos : (0 <= IZR Δ)%R) by (apply IZR_le; lia).
    assert (HCpos : (0 <= IZR C)%R) by (apply IZR_le; lia).
    tp_alloc as count_r "count_r". wp_alloc count_l as "count_l". tp_normalise...
    tp_bind (above_threshold _ _ _) ; wp_bind (above_threshold _ _ _).
    assert (INR (N'+1)%nat ≠ 0). { replace 0 with (INR 0) => //. intros ?%INR_eq. lia. }
    replace (S N' * (IZR C * (IZR Δ * ε)))%R with (IZR C * (IZR Δ * ε) + N' * (IZR C * (IZR Δ * ε)))%R.
    2:{ replace (S N') with (N'+1)%nat by lia. replace (INR (N'+1)) with (N' + 1) by real_solver. lra. }
    iDestruct (ecm_split with "SNε") as "[ε Nε]". 1,2: real_solver.
    opose proof (above_threshold_online_AT_spec Δ HΔ C HC num den T _) as AT.
    1: done.
    iPoseProof (AT with "[ε] [rhs]") as "AT" => // ; clear AT.
    iApply (wp_strong_mono'' with "AT").
    replace (S N') with (N'+1)%nat by lia.
    iIntros "%f (%f' & %AUTH & rhs & auth & AT)".
    tp_normalise. tp_bind (AllocN _ _).
    iMod (step_alloc with "rhs") as (ref_f') "[rhs ref_f']". tp_normalise.
    wp_alloc ref_f as "ref_f"...
    iModIntro. iExists _. iFrame "rhs".
    set (iSVT := (λ n : nat,
                    if Nat.ltb 0%nat n then
                      let n' := (n-1)%nat in
                      count_l ↦ #n' ∗ count_r ↦ₛ #n' ∗
                      ↯m (n' * (IZR C * (IZR Δ * ε))) ∗ ∃ token f f',
                          token ∗ ref_f ↦ f ∗ ref_f' ↦ₛ f' ∗ AT_spec Δ (IZR C) token f f'
                    else emp
                 )%I). iExists iSVT.
    iSplitL.
    { rewrite /iSVT. destruct (0 <? N'+1)%nat => //.
      replace ((N'+1)%nat-1)%Z with (Z.of_nat N') by lia.
      replace (N'+1-1)%nat with N' by lia. iFrame. }
    clear f f'.
    iIntros "!>" (???????) "q_sens rhs %n (count_l & count_r & nε & (%TOKEN & %f & %f' & auth & ref_f & ref_f' & #AT))"...
    tpload ; wp_load. tp_bind (f' _ _) ; wp_bind (f _ _).
    iCombine "AT" as "AT_cpy".
    iSpecialize ("AT" $! _ _ _ _ adj) as #.
    iSpecialize ("AT" with "q_sens auth rhs").
    iApply (wp_strong_mono'' with "AT").
    iIntros "%vq (%b & -> & rhs & maybe_auth)".
    tp_normalise...
    destruct b eqn:case_bq.
    - tpload ; wp_load...
      rewrite /= !Nat.sub_0_r.
      destruct n as [|n']...
      { rewrite /iSVT. iFrame. iExists _. iSplitR. 1: done. simpl. done. }
      replace (S n' * (IZR C * (IZR Δ * ε)))%R with (IZR C * (IZR Δ * ε) + n' * (IZR C * (IZR Δ * ε)))%R.
      2:{ replace (S n') with (n'+1)%nat by lia. replace (INR (n'+1)) with (n' + 1) by real_solver. lra. }
      iDestruct (ecm_split with "nε") as "[ε n'ε]". 1,2: real_solver.
      simplify_eq...
      tp_bind (above_threshold _ _ _) ; wp_bind (above_threshold _ _ _).
      opose proof (above_threshold_online_AT_spec Δ HΔ C HC num den T _) as AT_pw.
      1: done.
      iPoseProof (AT_pw with "[ε] [rhs]") as "AT_pw" => // ; clear AT_pw.
      iApply (wp_strong_mono'' with "AT_pw [-]").
      iIntros "%g (%g' & %AUTH' & rhs & auth & AT')". iClear "AT_cpy". tp_normalise...
      tp_bind (Store _ _). iMod (step_store with "[$rhs $ref_f']") as "[rhs ref_f']".
      tp_normalise. wp_store... tpload... tpstore ; wp_load... wp_store.
      iModIntro. iFrame "rhs". iExists true. iSplitR. 1: done.
      rewrite /iSVT.
      replace (0 <? S n')%nat with true by (symmetry; apply Nat.ltb_lt; lia).
      replace (Z.of_nat (S n' - 1)) with (Z.of_nat (S n') - 1)%Z by lia.
      iFrame "count_l count_r".
      replace (S n' - 1)%nat with n' by lia.
      iFrame "n'ε". iExists AUTH', g, g'. iFrame "auth ref_f ref_f' AT'".
    - tp_normalise... rewrite ?Nat.sub_0_r. simplify_eq.
      iSpecialize ("maybe_auth" $! eq_refl).
      tp_bind (Deref _). iMod (step_load with "[$rhs $count_r]") as "[rhs count_r]".
      tp_normalise. wp_load...
      destruct n as [|n']...
      { rewrite /iSVT. iFrame.
        iExists false. iSplitR => //. simpl. iFrame.
        iExists TOKEN. iFrame. done.
      }
      iFrame. iExists _ ; iSplitR => //. iSimpl. iFrame. iExists TOKEN. iFrame. done.
  Qed.


  (* Iterate online SVT over a list of queries. *)
  Definition SVT_list : val :=
    λ:"num" "den" "T" "N" "db" "qs",
      let: "f" := oSVT "num" "den" "T" "N" in
      (rec: "SVT" "i" "bs" :=
         if: "i" = "N" then "bs" else
           match: list_nth "i" "qs" with
           | NONE => "bs"
           | SOME "q" =>
               let: "b" := "f" "db" "q" in
               "SVT" ("i" + #1) (list_cons "b" "bs")
           end) #0 list_nil.

  (* oSVT interacting with A to get queries until N results above T' have been found in db. *)
  Definition SVT_stream : val :=
    λ:"num" "den" "T" "N" "stream_qs" "db",
      let: "f" := oSVT "num" "den" "T" "N" in
      (rec: "SVT" "i" "bs" :=
         if: "i" = "N" then "bs" else
           match: "stream_qs" "bs" with
           | NONE => "bs"
           | SOME "q" =>
               let: "b" := "f" "db" "q" in
               "SVT" (if: "b" then ("i" + #1) else "i") (list_cons "b" "bs")
           end) #0 list_nil.

  (* turn a list into a stream of queries *)
  Definition stream_list : val :=
    λ:"xs", let: "qs" := ref "xs" in
            λ:"_bs", match: !"qs" with
                     | NONE => NONE
                     | SOME "x_xs'" => "qs" <- Snd "x_xs'" ;; SOME (Fst "x_xs'")
                     end.

  (* enumerate queries provided by QS : int -> query *)
  Definition stream_nat : val :=
    λ:"QS", let: "count" := ref #0 in
            λ:"_bs", let: "i" := !"count" in
                     "count" <- "i"+#1 ;;
                     SOME ("QS" "i").

  (* SVT with cache? *)
  Definition SVT_cached : val :=
    λ:"num" "den" "T" "N" "qs" "db",
      let: "f" := oSVT "num" "den" "T" "N" in
      (rec: "SVT" "i" "bs" :=
         if: "i" = "N" then "bs" else
           let: "q" := list_nth "qs" "i" in
           let: "b" := "f" "db" "q" in
           "SVT" (if: "b" then ("i" + #1) else "i") (list_cons "b" "bs")
      ) #0 list_nil.

  #[local] Definition SVT_stream_body (N : nat) (stream_qs : val) {DB} {_ : Inject DB val} (db : DB) (f : val) := (rec: "SVT" "i" "bs" :=
        if: "i" = #N then "bs"
        else match: stream_qs "bs" with
               InjL <> => "bs"
             | InjR "q" =>
               let: "b" := f (Val (inject db)) "q" in
               "SVT" (if: "b" then "i" + #1 else "i") (list_cons "b" "bs")
             end)%V.

  Lemma SVT_stream_diffpriv (Δ : Z) (HΔ : (1 <= Δ)%Z) (C : Z) (HC : (1 <= C)%Z) (num den T : Z) (N : nat) (Npos : (0 < N)%nat) (stream_qs : val) `(dDB : Distance DB) :
    let ε := IZR num / IZR den in
    ∀ (εpos : 0 < ε),
      □ (∀ K (bs : val),
            ⤇ fill K (stream_qs bs) -∗
            WP stream_qs bs
              {{ qopt, ⤇ fill K (Val qopt) ∗
                       (⌜qopt = NONEV⌝ ∨ ∃ q : val, ⌜qopt = SOMEV q⌝ ∗ wp_sensitive Sg q (IZR Δ) dDB dZ) }}) -∗
      ∀ (db db' : DB) (adj : dDB db db' <= IZR C) K,
      ↯m (N * (IZR C * (IZR Δ * ε))) -∗
      ⤇ fill K (SVT_stream #num #den #T #N stream_qs (Val (inject db'))) -∗
      WP SVT_stream #num #den #T #N stream_qs (Val (inject db))
        {{ v, ⤇ fill K (Val v) }}.
  Proof with (tp_pures ; wp_pures).
    iIntros (ε εpos) "#sens % % % % Nε rhs". rewrite /SVT_stream...
    tp_bind (oSVT _ _ _ _) ; wp_bind (oSVT _ _ _ _).
    iPoseProof (SVT_online_diffpriv Δ HΔ C HC with "Nε rhs") as "spec" => //.
    iApply (wp_strong_mono'' with "spec"). iIntros "%f (%f' & % & rhs & iSVT & spec)". tp_normalise.
    do 4 tp_pure. tp_normalise. do 4 wp_pure. rewrite -!/(SVT_stream_body _ _ _ _).
    set (i := 0%Z). set (N' := N). rewrite {1 3}/N'.
    assert (0 <= i)%Z as ipos by lia. assert (N' + i = N)%Z as hi by lia.
    set (bs := InjLV #()). rewrite {1}/bs. generalize i N' bs hi ipos. clear i N' hi ipos bs.
    intros. iRevert (i N' bs hi ipos) "rhs iSVT spec". iLöb as "IH". iIntros (i N' bs hi ipos) "rhs iSVT #spec".
    rewrite {3 4}/SVT_stream_body...
    case_bool_decide... 1: done. tp_bind (stream_qs _) ; wp_bind (stream_qs _).
    iPoseProof ("sens" $! _ bs with "rhs") as "sens_bs".
    iApply (wp_strong_mono'' with "sens_bs").
    iIntros "%qopt (rhs & [->|(%q & -> & sens_q)])".
    { tp_normalise... iModIntro. iFrame. }
    tp_normalise...
    tp_bind (f' _ _) ; wp_bind (f _ _).
    iCombine "spec" as "spec_i".
    assert (not (i = N)). 1: intros h ; subst ; auto.
    assert (∃ N'', N' = S N'') as [? ->]. { destruct N'. 1: lia. eauto. }
    iEval (rewrite /SVT_spec) in "spec_i".
    iSpecialize ("spec_i" $! _ _ db db' adj with "sens_q rhs iSVT") => //.
    iApply (wp_strong_mono'' with "spec_i").
    iIntros "% (rhs & %b & -> & iSVT)". tp_normalise...
    rewrite -!/(SVT_stream_body _ _ _ _).
    destruct b ; rewrite /list_cons...
    - iApply ("IH" with "[] [] rhs iSVT"). 3: done. 1,2: iPureIntro. 2: lia. lia.
    - iApply ("IH" with "[] [] rhs [iSVT]"). 3,4: done. 1,2: iPureIntro. 2: lia. lia.
  Qed.

  Fact list_stream_sens (Δ : Z)
    (qs : list val) (QS : val) (is_qs : is_list qs QS) `(dDB : Distance DB)
    (sens : Forall (λ q : val, ⊢ wp_sensitive Sg q (IZR Δ) dDB dZ) qs) :
    let list_stream_qs := (λ:"_bs", stream_list QS "_bs")%V in
    ⊢
      □ (∀ K (bs : val),
            ⤇ fill K (list_stream_qs bs) -∗
            WP list_stream_qs bs
              {{ qopt, ⤇ fill K (Val qopt) ∗
                       (⌜qopt = NONEV⌝ ∨ ∃ q : val, ⌜qopt = SOMEV q⌝ ∗ wp_sensitive Sg q (IZR Δ) dDB dZ) }})
  .
  Proof with (tp_pures ; wp_pures).
    iIntros.
    iModIntro. iIntros. subst list_stream_qs.
    rewrite /stream_list...
    tp_alloc as qs_r "qs_r". wp_alloc qs_l as "qs_l". tp_normalise...
    tpload ; wp_load...
    destruct qs ; simpl in is_qs ; subst...
    - iFrame. iModIntro. iLeft. done.
    - destruct is_qs as [?[]]. simplify_eq...
      tpstore ; wp_store... iFrame. iModIntro. iRight. iExists v. iSplit. 1: done.
      destruct (Forall_cons_1 _ _ _ sens) as [sens_q' sens_qs'].
      iApply sens_q'.
  Qed.

  Corollary SVT_list_diffpriv (Δ : Z) (HΔ : (1 <= Δ)%Z) (C : Z) (HC : (1 <= C)%Z) (num den T : Z) (N : nat) (Npos : (0 < N)%nat) `(dDB : Distance DB)
    (qs : list val) (QS : val) (is_qs : is_list qs QS)
    (sens : Forall (λ q : val, ⊢ wp_sensitive Sg q (IZR Δ) dDB dZ) qs)
    :
    let ε := IZR num / IZR den in
    let list_stream_qs := (λ:"_bs", stream_list QS "_bs")%V in
    ∀ (εpos : 0 < ε),
    ∀ (db db' : DB) (adj : dDB db db' <= IZR C) K,
      ↯m (N * (IZR C * (IZR Δ * ε))) -∗
      ⤇ fill K (SVT_stream #num #den #T #N list_stream_qs (Val (inject db'))) -∗
      WP SVT_stream #num #den #T #N list_stream_qs (Val (inject db))
        {{ v, ⤇ fill K (Val v) }}.
  Proof with (tp_pures ; wp_pures).
    intros. iIntros "ε rhs".
    iPoseProof (list_stream_sens Δ _ _ is_qs) as "qs" => //.
    iPoseProof (SVT_stream_diffpriv Δ HΔ C HC num den T N Npos with "qs") as "h" => //.
    iSpecialize ("h" with " [] ε rhs") => //.
  Qed.

End svt.

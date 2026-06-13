(** Sum-queries / "auto-average" DP case study, ported from
    [clutch.diffpriv.examples.sum_queries] to the GENERIC language.  "Enable" the
    Laplace distribution (one signature + one [SampleIn] instance), pin the
    spec-context [fill], and the proofs go through with the standard proof-mode
    tactics, the library Laplace coupling rules ([hoare_couple_laplace] /
    [hoare_couple_laplace_exact]), and the ported sparse-vector-technique
    ([above_threshold] / [above_threshold_online_AT_spec]).

    Most of the file is pure list arithmetic ([clip]/[clipZ]/[sum_list_*]) that
    ports verbatim.  The DP-relevant differences vs. the monomorphic original:
      - the proof section is PARAMETRIC over a signature [Sg] containing
        [laplace_family] (cf. [laplace_dp] / [sparse_vector_technique]);
      - the sensitivity/DP combinators [wp_sensitive]/[hoare_sensitive] take the
        signature [Sg] as an explicit first argument in [gen];
      - [gen_prob_lang]'s spec layer ships no spec-side [GenWp], so we build the
        spec-side [gwp_spec] locally from the generic spec step rules (the exact
        analogue of [prob_lang.spec.spec_rules.gwp_spec]; cf.
        [report_noisy_max_generic]).
*)
From iris.base_logic Require Export na_invariants.
From clutch.common Require Import inject.
From clutch.prob Require Import differential_privacy.
From clutch.gen_diffpriv Require Import adequacy all.
From clutch.gen_diffpriv.lib Require Import laplace laplace_choice.
From clutch.gen_prob_lang Require Import inject families.
From clutch.gen_prob_lang.spec Require Import spec_ra spec_rules.
From clutch.gen_diffpriv.examples Require Import sparse_vector_technique.
From clutch.gen_prob_lang.gwp Require Import gen_weakestpre arith list.
From clutch.prelude Require Import stdpp_ext.
From iris.prelude Require Import options.

(** Keep the family index [sample_idx] folded so the [Laplace] surface notation
    matches the library coupling rules syntactically (cf.
    [sparse_vector_technique]). *)
#[global] Opaque sample_idx.

(** Dataset operators *)

Definition list_clip : val :=
  λ: "lower" "upper",
    list_map (λ: "z", Arith.min (Arith.max "lower" "z") "upper").

Definition list_sum : val :=
  rec: "list_sum" "zs" :=
    match: "zs" with
      NONE => #0
    | SOME "x" =>
        let, ("z", "zs") := "x" in
        "z" + "list_sum" "zs"
    end.

#[local] Open Scope Z.

(** Spec-side [GenWp] instance: the [gwp]-based dataset operators
    ([gwp_clip]/[gwp_sum]/[gwp_age_sum_query]) are also run on the SPEC program
    (via [(g:=gwp_spec)]).  [gen_prob_lang]'s spec layer does not ship a
    spec-side [GenWp] (only the impl-side [gwp_wpre] in [derived_laws]), so we
    build it here from the generic spec step rules ([step_pure]/[step_alloc]/
    [step_load]/[step_store]) — the exact analogue of
    [prob_lang.spec.spec_rules.gwp_spec].  Cf. [report_noisy_max_generic]. *)
Section spec_gwp.
  Context {Sg : Sig} `{!specG_prob_lang Σ, invGS_gen hl Σ}.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Sg)).
  Local Notation spec_update :=
    (@spec_update (lang_markov (gen_lang Sg)) Σ _ _ _).

  Notation spec_wp :=
    (λ E e Ψ, ∀ K,
        ⤇ fill K e -∗ spec_update E (∃ (v : val), ⤇ fill K v ∗ Ψ v))%I.

  Lemma gwp_mixin_spec :
    GenWpMixin (S := Sg) false spec_wp (λ l dq v, l ↦ₛ{dq} v)%I.
  Proof.
    constructor; intros.
    - apply _.
    - by iIntros "H" (?) "$".
    - iIntros "H" (?) "Hs". by iMod ("H" with "[$Hs //]") as (?) "[$ >$]".
    - iIntros "H" (?) "Hs". rewrite fill_comp.
      iMod ("H" with "[$Hs //]") as (?) "[Hs Hcnt]". rewrite -fill_comp.
      by iMod ("Hcnt" with "[$Hs //]").
    - iIntros "H" (?) "Hs".
      iMod (step_pure with "Hs") as "Hs"; [done|].
      by iMod ("H" with "[$Hs //]").
    - iIntros "H" (?) "Hs".
      iMod (step_alloc with "Hs") as (l) "($ & Hl)".
      by iApply "H".
    - iIntros "Hl H" (?) "Hs".
      iMod (step_load with "[$Hl $Hs]") as "($ & Hl)".
      by iApply "H".
    - iIntros "Hl H" (?) "Hs".
      iMod (step_store with "[$Hl $Hs]") as "($ & Hl)".
      by iApply "H".
  Qed.

  Canonical Structure gwp_spec := Build_GenWp gwp_mixin_spec.
End spec_gwp.

Section dataset_operators.
  Context {Sg : Sig} `{invGS_gen hlc Σ} (g : GenWp Sg Σ).

  Definition clipZ (lower upper z : Z) := Z.min (Z.max lower z) upper.

  Definition clip (lower upper : Z) (zs : list Z) :=
    (clipZ lower upper) <$> zs.

  Lemma clip_app zs1 zs2 l b:
    clip l b (zs1 ++ zs2) = clip l b zs1 ++ clip l b zs2.
  Proof. induction zs1; [done|]. rewrite /= IHzs1 app_comm_cons //. Qed.

  Lemma elem_of_clip_fun lower upper zs z :
    lower ≤ upper → z ∈ clip lower upper zs → lower ≤ z ≤ upper.
  Proof. intros ? (?&->&?)%list_elem_of_fmap. rewrite /clipZ. lia. Qed.

  Lemma gwp_clip (zs : list Z) v (lower upper : Z) E :
    lower ≤ upper →
    G{{{ ⌜is_list zs v⌝ }}}
      list_clip #lower #upper v @ g ; E
    {{{ w, RET w; ⌜is_list (clip lower upper zs) w⌝ }}}.
  Proof.
    iIntros (? Φ) "Hzs HΦ".
    gwp_rec; gwp_pures.
    gwp_apply (gwp_list_map with "[$Hzs] HΦ").
    iIntros (z Ψ) "!# _ HΨ".
    gwp_pures.
    gwp_apply gwp_max.
    gwp_apply gwp_min.
    by iApply "HΨ".
  Qed.

  Lemma sum_list_clip_le b zs :
    sum_list (clip 0 b zs) ≤ b * length zs.
  Proof. induction zs => /=; [lia|]. rewrite /clipZ. lia. Qed.

  Lemma sum_list_clip_pos b zs :
    0 ≤ b → 0 ≤ sum_list (clip 0 b zs).
  Proof. induction zs => /=; [lia|]. rewrite /clipZ. lia. Qed.

  (* TODO: move *)
  Lemma sum_list_app zs1 zs2 :
    sum_list (zs1 ++ zs2) = sum_list zs1 + sum_list zs2.
  Proof. induction zs1; [done|]. rewrite /= IHzs1. lia. Qed.

  Lemma sum_list_clip_Z_le (b : nat) (zs1 : list Z) :
    Z.abs (sum_list (clip 0 b zs1) - sum_list (clip 0 (b + 1) zs1)) ≤ length zs1.
  Proof. induction zs1 => /=; [lia|]. rewrite /clipZ. lia. Qed.

  Lemma clipZ_le (b : nat) z :
    0 ≤ clipZ 0 b z ≤ b.
  Proof. rewrite /clipZ. lia. Qed.

  Lemma sum_list_upper_bound b zs :
    (∀ z, z ∈ zs → z ≤ b) → sum_list zs ≤ b * length zs.
  Proof.
    induction zs as [|z zs' IH]  => /= Hz ; [lia|].
    pose proof (Hz z (list_elem_of_here _ _)).
    assert (∀ z : Z, z ∈ zs' → z ≤ b) as Hin.
    { intros ??. apply Hz. by right. }
    specialize (IH Hin). lia.
  Qed.

  Lemma sum_list_lower_bound b zs :
    (∀ z, z ∈ zs → b ≤ z) → b * length zs ≤ sum_list zs.
  Proof.
    induction zs as [|z zs' IH]  => /= Hz ; [lia|].
    pose proof (Hz z (list_elem_of_here _ _)).
    assert (∀ z : Z, z ∈ zs' → b ≤ z) as Hin.
    { intros ??. apply Hz. by right. }
    specialize (IH Hin). lia.
  Qed.

  Lemma clip_length l b zs :
    length (clip l b zs) = length zs.
  Proof. induction zs => /=; lia. Qed.

  Lemma elem_of_drop `{Countable A} (x : A) (xs : list A) n :
    x ∈ drop n xs → x ∈ xs.
  Proof. apply subseteq_drop. Qed.

  Lemma sum_list_drop_clip (b : nat) zs1 zs2 :
    sum_list (drop (length (clip 0 b zs2)) (clip 0 b zs1)) ≤ b * (length zs1 - length zs2)%nat.
  Proof.
    etrans.
    { eapply (sum_list_upper_bound b) => z. intros ?%elem_of_drop%elem_of_clip_fun; lia. }
    rewrite length_drop !clip_length.
    lia.
  Qed.

  Lemma sum_list_drop_clip_le (b : nat) zs1 zs2 :
    length zs2 ≤ length zs1 →
    sum_list (drop (length (clip 0 b zs1)) (clip 0 b zs2)) = 0.
  Proof.
    induction zs2 in zs1 |-* => /=.
    { rewrite drop_nil //. }
    destruct zs1 => /=; [done|].
    intros Hlen.
    apply IHzs2. lia.
  Qed.

  Lemma gwp_sum (zs : list Z) v E Φ :
    is_list zs v →
    Φ #(sum_list zs) -∗
    GWP list_sum v @ g ; E {{ Φ }}.
  Proof.
    iIntros (Hzs) "HΦ".
    iInduction zs as [|z zs] "IH" forall (v Hzs Φ); gwp_rec; gwp_pures.
    - rewrite Hzs /=. gwp_pures. by iApply "HΦ".
    - destruct Hzs as (w & -> & Hzs'). gwp_pures.
      gwp_bind (list_sum _).
      gwp_apply ("IH" with "[//]").
      gwp_pures. by iApply "HΦ".
  Qed.

End dataset_operators.


(** See [https://programming-dp.com/chapter10.html#applying-the-sparse-vector-technique] *)
Definition age_sum_query : val :=
  λ: "b" "df", list_sum (list_clip #0 "b" "df").

Definition create_query : val :=
  λ: "b" "df", (age_sum_query "b" "df") - (age_sum_query ("b" + #1) "df").

Definition list_find_default : val :=
  λ: "p" "xs" "default", match: list_find "p" "xs" with
                         | NONE => "default"
                         | SOME "res" => "res" end.

(* a candidate stream *)
Definition range : val :=
  λ: "start" "stop" "step",
    let: "current" := ref "start" in
    λ:"_",
      let: "x" := !"current" in
      if: "stop" < "x" then NONE
      else ("current" <- "x" + "step" ;; SOME "x").

(** The remaining program definitions sample from the Laplace family (directly,
    or transitively via [above_threshold]).  In [gen] the [Laplace] notation
    desugars to [Sample sample_idx ...] with [sample_idx] depending on the
    signature [Sg] and its [SampleIn laplace_family Sg] instance, so — unlike the
    monomorphic original — these definitions are NOT closed [val]s and must live
    in a section carrying [Sg].  [above_threshold] (from the ported SVT) likewise
    uses these section variables. *)
Section laplace_programs.
  Context {Sg : Sig} `{!SampleIn laplace_family Sg}.

  Definition above_threshold_list : val :=
    λ: "num" "den" "T" "ds" "queries" "default",
      let: "AT" := above_threshold "num" "den" "T" in
      list_find_default (λ: "b_q", let, ("b", "q") := "b_q" in "AT" "ds" "q") "queries" ("default", "default").

  (* bs could be a stream of integers instead of a pre-computed list. *)
  Definition compute_summation_clip_bound : val :=
    λ: "bs" "num" "den" "ds",
      let: "queries" := list_map (λ: "b", ("b", create_query "b")) "bs" in
      let, ("b_res", "q_res") := above_threshold_list "num" "den" #0%Z "ds" "queries" #0%Z in
      "b_res".

  (* bs as a stream of integers instead of a pre-computed list. *)
  Definition compute_summation_clip_bound_stream : val :=
    λ: "bs" "num" "den" "ds",
      let: "f" := rec: "g" "x" :=
          match: "bs" #() with
          | NONE => #0
          | SOME "b" =>
              let: "q" := create_query "b" in
              if: above_threshold "num" "den" #0%Z "ds" "q"
              then "b"
              else "g" #()
          end in
      "f" #().

  (* 3num/den dipr *)
  Definition auto_avg : val :=
    λ: "bs" "num" "den" "ds",
      (* costs num/den *)
      let: "final_b" := compute_summation_clip_bound "bs" "num" "den" "ds" in
      (* is final_b-sensitive, hence exact_sum and exact_sum' are at most final_b apart *)
      let: "exact_sum" := age_sum_query "final_b" "ds" in
      (* by hoare_couple_laplace, this is num/den private for
         final_b * (num / (final_b * final_b)) = num/den credits. *)
      let: "noisy_sum" := Laplace "num" ("final_b" * "den") "exact_sum" #() in
      (* again num/den-private because list_length is 1-sensitive *)
      let: "noisy_count" := Laplace "num" "den" (list_length "ds") #() in
      (* post-processing *)
      "noisy_sum" `quot` "noisy_count".

End laplace_programs.


Section gwp_queries.
  Context {Sg : Sig} `{invGS_gen hlc Σ} (g : GenWp Sg Σ).

  Lemma gwp_age_sum_query zs v z E Φ :
    0 ≤ z →
    is_list zs v →
    ▷? (gwp_laters g) Φ #(sum_list (clip 0 z zs)) -∗
    GWP age_sum_query #z v @ g ; E {{ Φ }}.
  Proof.
    iIntros (Hz Hzs) "HΦ". gwp_rec. gwp_pures.
    gwp_apply gwp_clip; [done|done|].
    iIntros (??).
    by gwp_apply gwp_sum.
  Qed.

End gwp_queries.

Section queries.
  Context {Sg : Sig} `{!SampleIn laplace_family Sg} `{!diffprivGS Sg Σ}.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Sg)).
  Local Notation lidx := (@sample_idx laplace_family Sg _).

  (** A VALUE-FORM exact (zero-cost reflexive) Laplace coupling.  After
      [tp_pures]/[wp_pures] the [Laplace] parameter [(num,den,loc)] is reduced to
      a [Val (PairV ...)], so the surface [hoare_couple_laplace_exact] (whose
      precondition is the un-reduced [Pair]-form) no longer matches the goal.
      This is the same value-form seam used by [wp_couple_laplace] in
      [gen_diffpriv.lib.laplace]; we specialise it to the reflexive coupling so
      that — unlike the cost-bearing rule — it needs NO [0 < num/den] (the [den]
      parameter is degenerate when the clip bound is [0]). *)
  Lemma wp_couple_laplace_exact_val (loc num den : Z) K E :
    {{{ ⤇ fill K (Sample lidx
                    (Val (PairV (LitV (LitInt num))
                            (PairV (LitV (LitInt den)) (LitV (LitInt loc)))))
                    (Val (LitV LitUnit))) }}}
      Sample lidx
        (Val (PairV (LitV (LitInt num))
                (PairV (LitV (LitInt den)) (LitV (LitInt loc)))))
        (Val (LitV LitUnit)) @ E
      {{{ (z : Z), RET #z; ⤇ fill K #z }}}.
  Proof.
    iIntros (Φ) "Hr HΦ".
    iMod ecm_zero as "Hε".
    iApply (wp_couple_sample_gen Sg lidx
              (sf_param_to_val laplace_family (num, den, loc))
              (sf_param_to_val laplace_family (num, den, loc))
              (dmap (sf_inj laplace_family) (sf_sample laplace_family (num, den, loc)))
              (dmap (sf_inj laplace_family) (sf_sample laplace_family (num, den, loc)))
              (λ v v', ∃ z : Z, v = #z ∧ v' = #z) K E 0
              (sig_sample_at laplace_family Sg (num, den, loc))
              (sig_sample_at laplace_family Sg (num, den, loc)) _ with "[$Hr $Hε]").
    { iIntros "!>" (v v') "(Hspec & %HR)". destruct HR as (z & -> & ->).
      iApply ("HΦ" $! z with "Hspec"). }
    Unshelve.
    apply (DPcoupl_map (sf_inj laplace_family) (sf_inj laplace_family)
             (sf_sample laplace_family (num, den, loc)) (sf_sample laplace_family (num, den, loc))
             (λ v v', ∃ z : Z, v = #z ∧ v' = #z) 0 0); [lra | lra | ].
    eapply (DPcoupl_mono (sf_sample laplace_family (num, den, loc))
              (sf_sample laplace_family (num, den, loc))
              (sf_sample laplace_family (num, den, loc))
              (sf_sample laplace_family (num, den, loc))
              (=) (λ a a', ∃ z : Z, sf_inj laplace_family a = #z ∧ sf_inj laplace_family a' = #z)
              0 0 0 0);
      [ intros; reflexivity | intros; reflexivity
      | intros a a' ->; by exists a' | lra | lra
      | apply ARcoupl_to_DPcoupl, ARcoupl_eq ].
  Qed.

  Lemma list_dist_clipped_le b zs1 zs2 :
    list_dist (clip 0 b zs1) (clip 0 b zs2) ≤ list_dist zs1 zs2.
  Proof. apply list_dist_fmap_le. Qed.

  Lemma age_sum_query_bound (b : nat) zs1 zs2 :
    sum_list (clip 0 b zs1) - sum_list (clip 0 b zs2) ≤ b * list_dist zs1 zs2.
  Proof.
    etrans; last first.
    { apply Z.mul_le_mono_nonneg_l; [lia|]. apply (list_dist_clipped_le b). }
    etrans; [apply (sum_difference_multiplicity' b)|].
    { intros ? [? | ?]%elem_of_app; eapply elem_of_clip_fun; done || lia. }
    apply Z.mul_le_mono_nonneg_l; [lia|].
    eapply sum_list_with_le.
    lia.
  Qed.

  Lemma age_sum_query_bound_abs (b : nat) zs1 zs2 :
    Z.abs (sum_list (clip 0 b zs1) - sum_list (clip 0 b zs2)) ≤ b * list_dist zs1 zs2.
  Proof.
    apply Z.abs_le.
    split; [|apply age_sum_query_bound].
    rewrite Z.opp_le_mono Z.opp_sub_distr Z.opp_involutive.
    rewrite (comm (list_dist)).
    rewrite Z.add_comm Z.add_opp_r.
    apply age_sum_query_bound.
  Qed.

  Lemma age_sum_query_sensitivity (b : nat) :
    ⊢ hoare_sensitive Sg (age_sum_query #b) b (dlist Z) dZ.
  Proof.
    iIntros (?? zs1 zs2 Φ) "!# Hspec HΦ".
    iMod (gwp_age_sum_query gwp_spec _ _ _ _ (λ v, ⌜v = #(sum_list (clip 0 b zs2))⌝%I)
           with "[//] Hspec") as (?) "[Hspec ->]".
    { lia. }
    { rewrite is_list_inject //. }
    wp_apply gwp_age_sum_query.
    { lia. }
    { rewrite is_list_inject //. }
    iApply "HΦ". iFrame "Hspec". iPureIntro.
    eexists. split; [done|]. simpl.
    rewrite Rabs_Zabs INR_IZR_INZ -mult_IZR; apply IZR_le.
    apply age_sum_query_bound_abs.
  Qed.

  Lemma sum_list_with_clip_diff (b : nat) zs :
    sum_list (clip 0 b zs) - sum_list (clip 0 (b + 1) zs) =
    sum_list_with (λ z, clipZ 0 b z - clipZ 0 (b + 1) z) zs.
  Proof.
    induction zs => /=; [done|].
    rewrite sum_list_with_cons. lia.
  Qed.

  Lemma clips_count zs1 zs2 (b : nat) :
    sum_list_with (λ z, clipZ 0 b z - clipZ 0 (b + 1) z) zs1 =
    sum_list_with (λ z, (clipZ 0 b z - clipZ 0 (b + 1) z) * list_count z zs1) (remove_dups (zs1 ++ zs2)).
  Proof. rewrite (sum_list_with_multiplicity _ zs2) //. Qed.

  Lemma clip_diff_bounds (b : nat) z :
    (clipZ 0 b z - clipZ 0 (b + 1) z) = -1 ∨
    (clipZ 0 b z - clipZ 0 (b + 1) z) = 0.
  Proof. rewrite /clipZ. lia. Qed.

  Lemma create_query_bound (b : nat) zs1 zs2 :
     (sum_list (clip 0 b zs1) - sum_list (clip 0 (b + 1) zs1) -
     (sum_list (clip 0 b zs2) - sum_list (clip 0 (b + 1) zs2))) ≤ list_dist zs1 zs2.
  Proof.
    rewrite 2!sum_list_with_clip_diff.
    rewrite (clips_count zs1 zs2) (clips_count zs2 zs1).
    rewrite (Permutation_app_comm zs2 zs1).
    rewrite -sum_list_with_sub.
    rewrite /list_dist.
    eapply sum_list_with_le => z ?.
    destruct (clip_diff_bounds b z) as [-> | ->]; lia.
  Qed.

  Lemma create_query_bound_abs (b : nat) zs1 zs2 :
     Z.abs (sum_list (clip 0 b zs1) - sum_list (clip 0 (b + 1) zs1) -
           (sum_list (clip 0 b zs2) - sum_list (clip 0 (b + 1) zs2))) ≤ list_dist zs1 zs2.
  Proof.
    apply Z.abs_le.
    split; [|apply create_query_bound].
    rewrite Z.opp_le_mono Z.opp_sub_distr Z.opp_involutive.
    rewrite (comm (list_dist)).
    rewrite Z.add_comm Z.add_opp_r.
    apply create_query_bound.
  Qed.

  Lemma create_query_sensitivity_partial (b : nat) :
    ⊢ hoare_sensitive Sg (λ: "df", age_sum_query #b "df" - age_sum_query (#b + #1) "df")%V 1 (dlist Z) dZ.
  Proof.
    iIntros (?? zs1 zs2 Φ) "!# Hspec HΦ".
    wp_rec; wp_pures.
    tp_rec; tp_pures.
    assert (#(b + 1) = #(b + 1)%nat) as ->.
    { do 2 f_equal. lia. }
    tp_bind (age_sum_query _ _).
    iMod (gwp_age_sum_query gwp_spec _ _ _ _
           (λ v, ⌜v = #(sum_list (clip 0 (b + 1)%nat zs2))⌝%I)
           with "[//] Hspec") as (?) "[Hspec ->] /=".
    { lia. }
    { rewrite is_list_inject //. }
    tp_bind (age_sum_query _ _).
    iMod (gwp_age_sum_query gwp_spec _ _ _ _
           (λ v, ⌜v = #(sum_list (clip 0 b zs2))⌝%I)
           with "[//] Hspec") as (?) "[Hspec ->] /=".
    { lia. }
    { rewrite is_list_inject //. }
    tp_pures.
    wp_apply gwp_age_sum_query.
    { lia. }
    { rewrite is_list_inject //. }
    wp_pures.
    wp_apply gwp_age_sum_query.
    { lia. }
    { rewrite is_list_inject //. }
    wp_pures. iModIntro.
    iApply "HΦ". iFrame.
    iExists _. iSplit; [done|]. iPureIntro.
    rewrite Rabs_Zabs -mult_IZR; apply IZR_le.
    rewrite Z.mul_1_l Nat2Z.inj_add.
    apply create_query_bound_abs.
  Qed.

  Lemma create_query_sensitivity (b : nat) K :
    ⤇ fill K (create_query #b) -∗
    WP create_query #b {{ v, ⤇ fill K (of_val v) ∗
                               hoare_sensitive Sg (of_val v) 1 (dlist Z) dZ }}.
  Proof.
    iIntros "Hs".
    tp_rec; tp_pures. wp_rec; wp_pures.
    iFrame. iModIntro.
    iApply create_query_sensitivity_partial.
  Qed.

  Lemma wp_above_threshold_list (num den T : Z) (default : nat) `{dA : Distance A} a a' qv qs K :
    (0 < IZR num / IZR den)%R →
    is_list qs qv →
    (dA a a' <= 1)%R →
    ([∗ list] b_q ∈ qs, ∃ (b : nat) (q : val), ⌜b_q = (#b, q)%V⌝ ∗ wp_sensitive Sg (of_val q) 1 dA dZ) -∗
    ↯m (IZR num / IZR den) -∗
    ⤇ fill K (above_threshold_list #num #den #T (inject a' : val) qv #default) -∗
    WP above_threshold_list #num #den #T (inject a : val) qv #default {{ v, ∃ (bound : nat) (q : val), ⌜v = (#bound, q)%V⌝ ∗ ⤇ fill K (of_val v) }}.
  Proof.
    iIntros (Hε Hqs Hdist) "Hqs Hε Hs".
    wp_rec; wp_pures. tp_rec. tp_pures.
    tp_bind (above_threshold _ _ _).
    wp_bind (above_threshold _ _ _).
    wp_apply (wp_wand with "[Hε Hs]").
    { wp_apply (above_threshold_online_AT_spec 1 (ltac:(lia)) with "[Hε] Hs"); [done|].
      replace (IZR 1) with 1%R by (simpl; lra). rewrite Rmult_1_l //. }
    iIntros (q) "(%f' & %AUTH & Hs & HAUTH & #AT_spec) /=".
    rewrite /list_find_default.
    tp_pures. wp_pures.
    iInduction qs as [|qi qs] "IH" forall (qv Hqs).
    - rewrite Hqs.
      tp_rec. tp_pures.
      wp_rec. wp_pures. iFrame. by iExists _,_.
    - destruct Hqs as [qv' [-> Hqs']].
      iDestruct "Hqs" as "[Hqi Hqs']".
      iDestruct "Hqi" as "(% & % & -> & Hqi)".
      tp_rec. tp_pures. tp_bind (f' _ _).
      wp_rec. wp_pures. wp_bind (q _ _).
      wp_apply (wp_wand with "[Hqi Hs HAUTH] [Hqs']").
      { iApply ("AT_spec" with "[//] Hqi HAUTH Hs") . }
      iIntros (v) "(%bb & -> & Hs & Hcnt) /=".
      destruct bb; tp_pures; wp_pures; [iExists _,_ ; iFrame ; try done|].
      iApply ("IH" with "[//] Hqs' Hs").
      by iApply "Hcnt".
  Qed.

  Lemma list_iter_create_query K (bs : list nat) bsv :
    is_list bs bsv →
    ⤇ fill K (list_map (λ: "b", ("b", create_query "b"))%V bsv) -∗
    WP list_map (λ: "b", ("b", create_query "b"))%V bsv {{ qv,
        ∃ qs, ⌜is_list qs qv⌝ ∗
              ([∗ list] b_q ∈ qs, ∃ (bound : nat) (q : val), ⌜b_q = (#bound, q)%V⌝ ∗ wp_sensitive Sg (of_val q) 1 (dlist Z) dZ) ∗
              ⤇ fill K (of_val qv) }}.
  Proof.
    iInduction bs as [|b bs] "IH" forall (bsv K).
    - iIntros (->) "Hs".
      tp_rec; tp_pures. wp_rec; wp_pures.
      iFrame. iExists []. iModIntro. iSplit ; done.
    - iIntros ((bs' & -> & Hbs)) "Hs".
      tp_rec; tp_pures. wp_rec; wp_pures.
      tp_bind (list_map _ _). wp_bind (list_map _ _).
      wp_apply (wp_wand with "[Hs]").
      { wp_apply ("IH" with "[//] Hs"). }
      iIntros (qsv') "(%qs' & %Hqs' & Hqs' & Hs) /=".
      tp_pures. wp_pures.
      tp_bind (create_query _). wp_bind (create_query _).
      wp_apply (wp_wand with "[Hs]").
      { wp_apply (create_query_sensitivity with "Hs"). }
      iIntros (q) "[Hs Hq] /=". rewrite /list_cons.
      tp_pures.
      wp_pures.
      iModIntro. iExists ((#b, q)%V :: qs').
      iFrame. iSplit; [iExists _; eauto|]. iExists _,_; iSplit ; eauto.
      iIntros (????) "Hs".
      iApply ("Hq" with "[%] [$Hs //]"); [lra|].
      auto.
  Qed.

  Lemma wp_compute_summation_clip_bound (ds1 ds2 : list Z) (bs : list nat) dsv1 dsv2 bsv (num den : Z) K :
    (0 < IZR num / IZR den)%R →
    is_list bs bsv →
    neighbour ds1 ds2 →
    is_list ds1 dsv1 →
    is_list ds2 dsv2 →
    ↯m (IZR num / IZR den) -∗
    ⤇ fill K (compute_summation_clip_bound bsv #num #den dsv2) -∗
    WP compute_summation_clip_bound bsv #num #den dsv1 {{ v, ∃ bound : nat, ⌜v = #bound⌝ ∗ ⤇ fill K (of_val v) }}.
  Proof.
    iIntros (Hε Hbs Hneigh Hds1 Hds2) "Hε Hs".
    tp_rec; tp_pures. wp_rec; wp_pures.
    tp_bind (list_map _ _).
    wp_bind (list_map _ _).
    wp_apply (wp_wand with "[Hs]").
    { by wp_apply (list_iter_create_query with "Hs"). }
    iIntros (qs) "(%qv & %Hqs & Hqs & Hs) /=".
    tp_pures. wp_pures.
    tp_bind (above_threshold_list _ _ _ _ _ _).
    wp_bind (above_threshold_list _ _ _ _ _ _).
    wp_apply (wp_wand with "[-]").
    { apply is_list_inject in Hds1 as ->, Hds2 as ->. replace 0%Z with (Z.of_nat 0%nat) by lia.
      wp_apply (wp_above_threshold_list num den 0 with "Hqs Hε Hs"); auto.
      rewrite /= neighbour_dist //. }
    iIntros (?) "(%&%&->&Hs) /=".
    tp_pures; wp_pures.
    iFrame.
    iExists _; done.
  Qed.


  Lemma wp_auto_avg (ds1 ds2 : list Z) (bs : list nat) dsv1 dsv2 bsv (num den : Z) K :
    (0 < IZR num / IZR den)%R →
    is_list bs bsv →
    neighbour ds1 ds2 →
    is_list ds1 dsv1 →
    is_list ds2 dsv2 →
    ↯m (IZR num / IZR den) -∗
    ↯m (IZR num / IZR den) -∗
    ↯m (IZR num / IZR den) -∗
    ⤇ fill K (auto_avg bsv #num #den dsv2) -∗
    WP auto_avg bsv #num #den dsv1 {{ v, ⤇ fill K (of_val v) }}.
  Proof.
    iIntros (Hε Hbs Hneigh Hds1 Hds2) "ε1 ε2 ε3 Hs".
    rewrite /auto_avg. tp_pures ; wp_pures.

    (* private clip bound for ε *)
    tp_bind (compute_summation_clip_bound _ _ _ _) ; wp_bind (compute_summation_clip_bound _ _ _ _).
    iPoseProof (wp_compute_summation_clip_bound with "ε1 Hs") as "H" => //.
    iApply (wp_wand with "H"). iIntros "* (%bound&->&rhs)" => //=. tp_pures. wp_pures.

    (* the sum is bound-sensitive *)
    tp_bind (age_sum_query _ _) ; wp_bind (age_sum_query _ _).
    apply is_list_inject in Hds1 as ->, Hds2 as ->.
    iApply (age_sum_query_sensitivity bound with "[] [rhs]") => //.
    1: iPureIntro ; real_solver.
    iIntros "!> * (%sum&%sum'&->&rhs&%res_close)".
    simpl. tp_pures. wp_pures.

    (* first deal with the somewhat pathological case where both sums are exactly the same *)
    (* this is done simply because it allows us to avoid reasoning about a division by 0 in the interesting case. *)
    destruct bound as [|bound'] eqn:case_bound.
    -
      assert (sum = sum') as ->.
      {
        revert res_close. simpl. rewrite Rmult_0_l. rewrite -abs_IZR. apply Zabs_ind.
        - intros. apply le_IZR in res_close. lia.
        - intros. apply le_IZR in res_close. lia.
      }
      tp_bind (Sample _ _ _).
      wp_apply (wp_couple_laplace_exact_val _ num _ with "[$rhs] [-]") ; try done.
      iIntros "!> * rhs" => /=. tp_pures ; wp_pures.

      tp_bind (list_length _). wp_bind (list_length _).
      wp_apply gwp_list_length ; [iPureIntro ; by rewrite is_list_inject|]. iIntros.
      iMod (gwp_list_length (g:=gwp_spec (Sg:=Sg)) (A:=Z) _ _ _ (λ v : val, ⌜v = #(length ds2)⌝)%I with "[] [] rhs") as "(%&rhs&%)".
      1: iPureIntro ; by rewrite is_list_inject.
      1: simpl ; iIntros ; simplify_eq ; done.
      simplify_eq. tp_normalise. tp_pures. wp_pures.
      tp_bind (Sample _ _ _). wp_bind (Sample _ _ _).
      assert ((Z.abs (length ds1 - length ds2)) <= 1).
      { destruct Hneigh; simplify_eq.
        - apply Z.eq_le_incl.
          rewrite !length_app. simpl. apply Zabs_ind ; intros ; lia.
        - apply Z.eq_le_incl.
          rewrite !length_app. simpl. apply Zabs_ind ; intros ; lia. }
      iApply (wp_couple_laplace (S:=Sg) _ _ 0%Z 1%Z with "[$rhs ε3]").
      1: apply Zabs_ind ; lia.
      1: reflexivity.
      1: done.
      1: rewrite Rmult_1_l //.
      1: iFrame "ε3".
      iIntros "!> %z2 rhs". simpl ; tp_pures ; wp_pures.
      rewrite Z.add_0_r /=. done.

    -
      (* Laplace num (bound*den) sum ~ Laplace num (bound*den) sum'   for  ↯ num/den   because   |sum-sum'| ≤ bound   *)
      tp_bind (Sample _ _ _). wp_apply (wp_couple_laplace _ _ 0 with "[$rhs ε2] [-]") ; try done.
      { rewrite mult_IZR. eapply Rdiv_pos_pos ; auto. real_solver. }
      {
        rewrite Z.add_0_l.
        rewrite /dZ/dlist/distance in res_close.
        rewrite neighbour_dist in res_close ; auto.
        rewrite Rmult_1_r in res_close.
        rewrite -abs_IZR in res_close.
        iApply ecm_weaken. 2: iFrame. split.
        - apply Rmult_le_pos. 2: rewrite mult_IZR ; eapply Rdiv_nneg_nneg ; try left ; try real_solver.
          apply IZR_le. lia.
        -
          etrans.
          1: eapply Rmult_le_compat_r. 2: apply res_close.
          1: rewrite mult_IZR ; eapply Rdiv_nneg_nneg ; try left ; try real_solver.
          right. rewrite mult_IZR. rewrite INR_IZR_INZ.
          pose proof (Rdiv_pos_cases _ _ Hε).
          field. split ; real_solver.
      }
      iIntros "!> * rhs" => /=. tp_pures. wp_pures.

      (* length is 1-sensitive *)
      tp_bind (list_length _). wp_bind (list_length _).
      wp_apply gwp_list_length ; [iPureIntro ; by rewrite is_list_inject|]. iIntros.
      iMod (gwp_list_length (g:=gwp_spec (Sg:=Sg)) (A:=Z) _ _ _ (λ v : val, ⌜v = #(length ds2)⌝)%I with "[] [] rhs") as "(%&rhs&%)".
      1: iPureIntro ; by rewrite is_list_inject.
      1: simpl ; iIntros ; simplify_eq ; done.
      ring_simplify (z + 0).
      simplify_eq.
      assert ((Z.abs (length ds1 - length ds2)) <= 1).
      1: destruct Hneigh ; simplify_eq ; rewrite !length_app /= ; lia.
      (* private length for ε *)
      tp_normalise. tp_pures. wp_pures.
      tp_bind (Sample _ _ _). wp_bind (Sample _ _ _).
      iApply (wp_couple_laplace (S:=Sg) _ _ 0%Z 1%Z with "[$rhs ε3]").
      1: apply Zabs_ind ; lia.
      1: reflexivity.
      1: done.
      1: rewrite Rmult_1_l //.
      1: iFrame "ε3".
      iIntros "!> %z3 rhs". simpl ; do 2 tp_pure ; do 2 wp_pure.
      rewrite Zplus_0_r.
      (* postprocessing *)
      tp_pures. wp_pures. done.
  Qed.

End queries.

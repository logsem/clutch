From iris.base_logic Require Export na_invariants.
From clutch.common Require Import inject.
From clutch.prelude Require Import tactics.
From clutch.prob Require Import differential_privacy.
From clutch.diffpriv Require Import adequacy diffpriv proofmode derived_laws.
From clutch.diffpriv.examples Require Import sparse_vector_technique.
From clutch.prob_lang.gwp Require Import gen_weakestpre arith list.

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

Section dataset_operators.
  Context `{invGS_gen hlc Σ} (g : GenWp Σ).

  Definition clipZ (lower upper z : Z) := Z.min (Z.max lower z) upper.

  Definition clip (lower upper : Z) (zs : list Z) :=
    (clipZ lower upper) <$> zs.

  Lemma clip_app zs1 zs2 l b:
    clip l b (zs1 ++ zs2) = clip l b zs1 ++ clip l b zs2.
  Proof. induction zs1; [done|]. rewrite /= IHzs1 app_comm_cons //. Qed.

  Lemma elem_of_clip_fun lower upper zs z :
    lower ≤ upper → z ∈ clip lower upper zs → lower ≤ z ≤ upper.
  Proof. intros ? (?&->&?)%elem_of_list_fmap. rewrite /clipZ. lia. Qed.

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

  Definition sum_list (zs : list Z) : Z := foldr Z.add 0 zs.

  Lemma sum_list_clip_le b zs :
    sum_list (clip 0 b zs) ≤ b * length zs.
  Proof. induction zs => /=; [lia|]. rewrite /clipZ. lia. Qed.

  Lemma sum_list_clip_pos b zs :
    0 ≤ b → 0 ≤ sum_list (clip 0 b zs).
  Proof. induction zs => /=; [lia|]. rewrite /clipZ. lia. Qed.

  Lemma sum_list_app zs1 zs2 :
    sum_list (zs1 ++ zs2) = sum_list zs1 + sum_list zs2.
  Proof. induction zs1; [done|]. rewrite /= IHzs1. lia. Qed.

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


(** See [https://programming-dp.com/ch10.html#applying-the-sparse-vector-technique] *)
Definition age_sum_query : val :=
  λ: "b" "df", list_sum (list_clip #0 "b" "df").

Definition create_query : val :=
  λ: "b" "df", (age_sum_query "b" "df") - (age_sum_query ("b" + #1) "df").

Definition above_threshold_list : val :=
  λ: "num" "den" "T" "ds" "queries",
    let: "AT" := above_threshold "num" "den" "T" in
    list_find (λ: "q", "AT" "ds" "q") "queries".

Definition compute_summation_clip_bound : val :=
  λ: "bs" "num" "den" "ds",
    let: "queries" := list_map (λ: "b", create_query "b") "bs" in
    let: "res" := above_threshold_list "num" "den" #0%Z "ds" "queries" in
    "res".

Section gwp_queries.
  Context `{invGS_gen hlc Σ} (g : GenWp Σ).

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
  Context `{!diffprivGS Σ}.

  Lemma age_sum_query_sensitivity (b : nat) :
    ⊢ hoare_sensitive_cond (age_sum_query #b) b (dlist Z) neighbour dZ.
  Proof.
    iIntros (?? zs1 zs2 Φ) "!# [Hspec %Hcond] HΦ".
    iMod (gwp_age_sum_query gwp_spec _ _ _ _ (λ v, ⌜v = #(sum_list (clip 0 b zs2))⌝%I)
           with "[//] Hspec") as (?) "[Hspec ->]".
    { lia. }
    { rewrite is_list_inject //. }
    wp_apply gwp_age_sum_query.
    { lia. }
    { rewrite is_list_inject //. }
    iApply "HΦ". iFrame "Hspec". iPureIntro.
    eexists. split; [done|]. simpl.
    rewrite Rabs_Zabs -mult_INR INR_IZR_INZ. apply IZR_le.
    rewrite neighbour_dist //.
    destruct Hcond; simplify_eq.
    - rewrite !clip_app !sum_list_app.
      transitivity (clipZ 0 b n); rewrite /= /clipZ; lia.
    - rewrite !clip_app !sum_list_app.
      transitivity (clipZ 0 b n); rewrite /= /clipZ; lia.
  Qed.

  Lemma create_query_sensitivity_partial (b : nat) :
    ⊢ hoare_sensitive_cond (λ: "df", age_sum_query #b "df" - age_sum_query (#b + #1) "df")%V 1 (dlist Z) neighbour dZ.
  Proof.
    iIntros (?? zs1 zs2 Φ) "!# [Hspec %Hcond] HΦ".
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
    rewrite neighbour_dist //=.
    rewrite Rabs_Zabs Rmult_1_l. apply IZR_le.
    destruct Hcond; simplify_eq/=;
      rewrite !clip_app !sum_list_app /= /clipZ; lia.
  Qed.

  Lemma create_query_sensitivity (b : nat) K :
    ⤇ fill K (create_query #b) -∗
    WP create_query #b {{ v, ⤇ fill K (of_val v) ∗
                               hoare_sensitive_cond (of_val v) 1 (dlist Z) neighbour dZ }}.
  Proof.
    iIntros "Hs".
    tp_rec; tp_pures. wp_rec; wp_pures.
    iFrame. iModIntro.
    iApply create_query_sensitivity_partial.
  Qed.

  Lemma wp_above_threshold_list (num den T : Z) `{dA : Distance A} a a' qv qs K cond :
    (0 < IZR num / IZR den)%R →
    is_list qs qv →
    (dA a a' <= 1)%R →
    cond a a' →
    ([∗ list] q ∈ qs, wp_sensitive_cond (of_val q) 1 dA cond dZ) -∗
    ↯m (IZR num / IZR den) -∗
    ⤇ fill K (above_threshold_list #num #den #T (inject a' : val) qv) -∗
    WP above_threshold_list #num #den #T (inject a : val) qv {{ v, ⤇ fill K (of_val v) }}.
  Proof.
    iIntros (Hε Hqs Hdist Hcond) "Hqs Hε Hs".
    wp_rec; wp_pures. tp_rec. tp_pures.
    tp_bind (above_threshold _ _ _).
    wp_bind (above_threshold _ _ _).
    wp_apply (wp_wand with "[Hε Hs]").
    { wp_apply (above_threshold_online_AT_spec with "[Hε] Hs"); [done|].
      rewrite Rmult_1_l //. }
    iIntros (q) "(%f' & %AUTH & Hs & HAUTH & #AT_spec) /=".
    tp_pures. wp_pures.
    iInduction qs as [|qi qs] "IH" forall (qv Hqs).
    - rewrite Hqs.
      tp_rec. tp_pures.
      wp_rec. wp_pures. by iFrame.
    - destruct Hqs as [qv' [-> Hqs']].
      tp_rec. tp_pures. tp_bind (f' _ _).
      wp_rec. wp_pures. wp_bind (q _ _).
      iDestruct "Hqs" as "[Hqi Hqs']".
      wp_apply (wp_wand with "[Hqi Hs HAUTH] [Hqs']").
      { iApply ("AT_spec" with "[//] [//] Hqi HAUTH Hs") . }
      iIntros (v) "(%b & -> & Hs & Hcnt) /=".
      destruct b; tp_pures; wp_pures; [done|].
      iApply ("IH" with "[//] Hqs' Hs").
      by iApply "Hcnt".
  Qed.

  Lemma list_iter_create_query K (bs : list nat) bsv :
    is_list bs bsv →
    ⤇ fill K (list_map (λ: "b", create_query "b")%V bsv) -∗
    WP list_map (λ: "b", create_query "b")%V bsv {{ qv,
        ∃ qs, ⌜is_list qs qv⌝ ∗
              ([∗ list] q ∈ qs, wp_sensitive_cond (of_val q) 1 (dlist Z) neighbour dZ) ∗
              ⤇ fill K (of_val qv) }}.
  Proof.
    iInduction bs as [|b bs] "IH" forall (bsv K).
    - iIntros (->) "Hs".
      tp_rec; tp_pures. wp_rec; wp_pures.
      iFrame. iExists []. iModIntro. iSplit; done.
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
      iIntros (q) "[Hs Hq] /=".
      tp_rec; tp_pures.
      wp_rec; wp_pures.
      iModIntro. iExists (q :: qs').
      iFrame. iSplit; [iExists _; eauto|].
      iIntros (?????) "Hs".
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
    WP compute_summation_clip_bound bsv #num #den dsv1 {{ v, ⤇ fill K (of_val v) }}.
  Proof.
    iIntros (Hε Hbs Hneigh Hds1 Hds2) "Hε Hs".
    tp_rec; tp_pures. wp_rec; wp_pures.
    tp_bind (list_map _ _).
    wp_bind (list_map _ _).
    wp_apply (wp_wand with "[Hs]").
    { by wp_apply (list_iter_create_query with "Hs"). }
    iIntros (qs) "(%qv & %Hqs & Hqs & Hs) /=".
    tp_pures. wp_pures.
    tp_bind (above_threshold_list _ _ _ _ _).
    wp_bind (above_threshold_list _ _ _ _ _).
    wp_apply (wp_wand with "[-]").
    { apply is_list_inject in Hds1 as ->, Hds2 as ->.
      wp_apply (wp_above_threshold_list num den 0  with "Hqs Hε Hs"); auto.
      rewrite /= neighbour_dist //. }
    iIntros (?) "Hs /=".
    tp_pures; wp_pures.
    done.
  Qed.

End queries.

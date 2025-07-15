From iris.base_logic Require Export na_invariants.
From clutch.common Require Import inject.
From clutch.prelude Require Import tactics.
From clutch.prob Require Import differential_privacy.
From clutch.diffpriv Require Import adequacy diffpriv proofmode derived_laws.
From clutch.diffpriv.examples Require Import sparse_vector_technique.
From clutch.prob_lang.gwp Require Import gen_weakestpre list arith.

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

Section queries.
  Context `{invGS_gen hlc Σ} (g : GenWp Σ).

  Lemma gwp_age_sum_query zs v (b : nat) E Φ :
    is_list zs v →
    ▷? (gwp_laters g) Φ #(sum_list (clip 0 b zs)) -∗
    GWP age_sum_query #b v @ g ; E {{ Φ }}.
  Proof.
    iIntros (Hzs) "HΦ". gwp_rec. gwp_pures.
    gwp_apply gwp_clip; [lia|done|].
    iIntros (??).
    by gwp_apply gwp_sum.
  Qed.

End queries.

Section queries.
  Context `{diffprivGS Σ}.

  Lemma wp_age_sum_query_sensitivity (b : nat) :
    ⊢ hoare_sensitive_cond (age_sum_query #b) b (dlist Z) neighbour dZ.
  Proof.
    iIntros (?? zs1 zs2 Φ) "!# [Hspec %Hcond] HΦ".
    iMod (gwp_age_sum_query gwp_spec _ _ _ _ (λ v, ⌜v = #(sum_list (clip 0 b zs2))⌝%I)
           with "[//] Hspec") as (?) "[Hspec ->]".
    { rewrite is_list_inject //. }
    wp_apply gwp_age_sum_query.
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

  Lemma wp_create_query_sensitivity (b : nat) :
    ⊢ hoare_sensitive_cond (create_query #b) 1 (dlist Z) neighbour dZ.
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
    { rewrite is_list_inject //. }
    tp_bind (age_sum_query _ _).
    iMod (gwp_age_sum_query gwp_spec _ _ _ _
           (λ v, ⌜v = #(sum_list (clip 0 b zs2))⌝%I)
           with "[//] Hspec") as (?) "[Hspec ->] /=".
    { rewrite is_list_inject //. }
    tp_pures.
    wp_apply gwp_age_sum_query.
    { rewrite is_list_inject //. }
    wp_pures.
    wp_apply gwp_age_sum_query.
    { rewrite is_list_inject //. }
    wp_pures. iModIntro.
    iApply "HΦ". iFrame.
    iExists _. iSplit; [done|]. iPureIntro.
    rewrite neighbour_dist //=.
    rewrite Rabs_Zabs Rmult_1_l. apply IZR_le.
    destruct Hcond; simplify_eq/=;
      rewrite !clip_app !sum_list_app /= /clipZ; lia.
  Qed.

End queries.

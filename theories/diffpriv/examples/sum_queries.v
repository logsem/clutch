From iris.base_logic Require Export na_invariants.
From clutch.common Require Import inject.
From clutch.prelude Require Import tactics.
From clutch.prob Require Import differential_privacy.
From clutch.diffpriv Require Import adequacy diffpriv proofmode.
From clutch.diffpriv.examples Require Import list sparse_vector_technique.

Definition max : val :=
  λ: "n" "m",
    if: "m" ≤ "n" then "n" else "m".

Definition min : val :=
  λ: "n" "m",
    if: "n" ≤ "m" then "n" else "m".

#[local] Open Scope Z.

(* TODO: move and generalize to GWP *)
Section Z_theory.
  Context `{diffprivGS Σ}.

  Lemma wp_max (z1 z2 : Z) :
    {{{ True }}} max #z1 #z2 {{{ z, RET #z; ⌜z = z1 `max` z2⌝ }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_rec. wp_pures.
    case_bool_decide; simplify_eq; wp_pures;
      iApply "HΦ"; iPureIntro; lia.
  Qed.

  Lemma wp_min (z1 z2 : Z) :
    {{{ True }}} min #z1 #z2 {{{ z, RET #z; ⌜z = z1 `min` z2⌝ }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_rec. wp_pures.
    case_bool_decide; simplify_eq; wp_pures;
      iApply "HΦ"; iPureIntro; lia.
  Qed.

End Z_theory.

(** Dataset operators *)

Definition list_clip : val :=
  λ: "lower" "upper",
    list_map (λ: "z", min (max "lower" "z") "upper").

Definition list_sum : val :=
  rec: "list_sum" "zs" :=
    match: "zs" with
      NONE => #0
    | SOME "x" =>
        let, ("z", "zs") := "x" in
        "z" + "list_sum" "zs"
    end.

Section dataset_operators.
  Context `{!diffprivGS Σ}.

  Definition clipZ (lower upper z : Z) := Z.min (Z.max lower z) upper.

  Definition clip (lower upper : Z) (zs : list Z) :=
    (clipZ lower upper) <$> zs.

  Lemma clip_app zs1 zs2 l b:
    clip l b (zs1 ++ zs2) = clip l b zs1 ++ clip l b zs2.
  Proof. induction zs1; [done|]. rewrite /= IHzs1 app_comm_cons //. Qed.

  Lemma elem_of_clip_fun lower upper zs z :
    lower ≤ upper → z ∈ clip lower upper zs → lower ≤ z ≤ upper.
  Proof. intros ? (?&->&?)%elem_of_list_fmap. rewrite /clipZ. lia. Qed.

  Lemma wp_clip (zs : list Z) v (lower upper : Z) :
    lower ≤ upper →
    {{{ ⌜is_list zs v⌝ }}}
      list_clip #lower #upper v
    {{{ w, RET w; ⌜is_list (clip lower upper zs) w⌝ }}}.
  Proof.
    iIntros (? Φ) "Hzs HΦ".
    wp_rec; wp_pures.
    wp_apply (wp_list_map with "[$Hzs] HΦ").
    iIntros (z Ψ) "!# _ HΨ".
    wp_pures.
    wp_apply wp_max; [done|].
    iIntros (z' ->).
    wp_apply wp_min; [done|].
    iIntros (z'' ->).
    by iApply "HΨ".
  Qed.

  Lemma spec_clip (zs : list Z) v (lower upper : Z) K E :
    lower ≤ upper →
    is_list zs v →
    ⤇ fill K (list_clip #lower #upper v) ⊢
    spec_update E (∃ (w : val), ⤇ fill K w ∗ ⌜is_list (clip lower upper zs) w⌝).
  Proof.
    iIntros (??) "Hspec". tp_rec; tp_pures.
    iMod (spec_list_map _ _ (λ z, Z.min (Z.max lower z) upper)
           with "[] [//] Hspec") as (?) "[Hspec %]".
    { iIntros "!#" (??) "Hs". tp_pures.
      tp_rec. tp_pures.
      case_bool_decide; simplify_eq => /=;
        tp_pures; tp_rec; tp_pures;
        case_bool_decide; tp_pures;
        iFrame; iModIntro; iPureIntro; do 3 f_equal; lia. }
    by iFrame.
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

  Lemma wp_sum (zs : list Z) v :
    {{{ ⌜is_list zs v⌝ }}} list_sum v {{{ RET #(sum_list zs); True }}}.
  Proof.
    iIntros (Φ Hzs) "HΦ".
    iInduction zs as [|z zs] "IH" forall (v Hzs Φ); wp_rec; wp_pures.
    - rewrite Hzs /=. wp_pures. by iApply "HΦ".
    - destruct Hzs as (w & -> & Hzs'). wp_pures.
      wp_bind (list_sum _).
      wp_apply ("IH" with "[//]").
      iIntros "_". wp_pures. by iApply "HΦ".
  Qed.

  Lemma spec_sum (zs : list Z) v K E :
    is_list zs v →
    ⤇ fill K (list_sum v) ⊢ spec_update E (⤇ fill K #(sum_list zs)).
  Proof.
    iIntros (Hzs) "Hs".
    iInduction zs as [|z zs] "IH" forall (v Hzs K); tp_rec; tp_pures.
    - rewrite Hzs /=. tp_pures. by iFrame.
    - destruct Hzs as (w & -> & Hzs'). tp_pures.
      tp_bind (list_sum _).
      iMod ("IH" with "[//] Hs") as "Hs /=".
      tp_pures. done.
  Qed.

End dataset_operators.


(** See [https://programming-dp.com/ch10.html#applying-the-sparse-vector-technique] *)
Definition age_sum_query : val :=
  λ: "b" "df", list_sum (list_clip #0 "b" "df").

Definition create_query : val :=
  λ: "b" "df", (age_sum_query "b" "df") - (age_sum_query ("b" + #1) "df").

Section queries.
  Context `{!diffprivGS Σ}.

  Lemma wp_age_sum_query zs v (b : nat) :
    {{{ ⌜is_list zs v⌝ }}}
      age_sum_query #b v
    {{{ RET #(sum_list (clip 0 b zs)); True }}}.
  Proof.
    iIntros (Φ?) "HΦ". wp_rec. wp_pures.
    wp_apply wp_clip; [lia|done|].
    iIntros (??).
    by wp_apply wp_sum.
  Qed.

  Lemma tp_age_sum_query zs v (b : nat) K E :
    is_list zs v →
    ⤇ fill K (age_sum_query #b v) ⊢ spec_update E (⤇ fill K #(sum_list (clip 0 b zs))).
  Proof.
    iIntros (Hzs) "Hspec". tp_rec. tp_pures.
    tp_bind (list_clip _ _ _).
    iMod (spec_clip with "Hspec") as (w) "[Hspec %] /="; [lia|done|].
    iMod (spec_sum with "Hspec") as "Hspec"; [done|].
    done.
  Qed.

  Lemma wp_age_sum_query_sensitivity (b : nat) :
    ⊢ hoare_sensitive_cond (age_sum_query #b) b (dlist Z) neighbour dZ.
  Proof.
    iIntros (?? zs1 zs2 Φ) "!# [Hspec %Hcond] HΦ".
    iApply wp_spec_update.
    wp_apply wp_age_sum_query.
    { rewrite is_list_inject //. }
    iIntros "_".
    iMod (tp_age_sum_query with "Hspec") as "Hspec".
    { rewrite is_list_inject //. }
    iModIntro.
    iApply "HΦ". iFrame. iPureIntro.
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
    tp_bind (age_sum_query _ _).
    assert (#(b + 1) = #(b + 1)%nat) as ->.
    { do 2 f_equal. lia. }
    wp_apply (wp_age_sum_query_sensitivity (b + 1) with "[%] [$Hspec //]").
    { real_solver. }
    iIntros (?) "/= (%z1 & %z1' & -> & Hspec & %Hd1)".
    tp_bind (age_sum_query _ _).
    wp_apply (wp_age_sum_query_sensitivity b with "[%] [$Hspec //]").
    { real_solver. }
    iIntros (?) "/= (%z2 & %z2' & -> & Hspec & %Hd2)".
    tp_pures. wp_pures.
    iApply "HΦ".
    iModIntro. iFrame. iExists _. iPureIntro.
    split; [done|].
    move: Hd1 Hd2.
    rewrite neighbour_dist //=.
    rewrite !Rabs_Zabs Rmult_1_l !INR_IZR_INZ -!mult_IZR !Z.mul_1_r Nat2Z.inj_add /=.
    intros ?%le_IZR ?%le_IZR. apply IZR_le.
    assert (z2 - z1 - (z2' - z1') = z2 - z2' - (z1 - z1')) as -> by lia.

    (* ehhh....  *)

  Admitted.


End queries.

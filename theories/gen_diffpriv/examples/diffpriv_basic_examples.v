(** Basic differential-privacy case studies on the GENERIC language, ported from
    [clutch.diffpriv.examples.diffpriv_basic_examples].  Demonstrates that a
    [prob_lang] DP case study ports to [gen_prob_lang] essentially unchanged:
    "enable" the Laplace distribution (one signature + one [SampleIn] instance),
    then write [Laplace] / apply [hoare_couple_laplace] / conclude meta-level
    privacy via [wp_diffpriv_Z] as before. *)
From clutch.gen_prob_lang Require Import inject.
From clutch.prob Require Import differential_privacy.
From clutch.gen_diffpriv Require Import adequacy diffpriv_rules proofmode.
From clutch.gen_diffpriv.lib Require Import laplace.
From clutch.gen_prob_lang Require Import families.
From iris.prelude Require Import options.

Section wp_example.
  Context {Sg : Sig} `{!SampleIn laplace_family Sg} `{!diffprivGS Sg Σ}.
  #[local] Open Scope R.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Sg)).

  (** [(λ loc, Laplace(num/den, loc))] couples on adjacent inputs at cost
      [|loc - loc'|·ε].  In gen, [wp_pures]/[tp_pures] reduce the (now [Pair]-
      encoded) parameter of [Laplace] to a value, after which the reduced-form
      [wp_couple_laplace] applies directly (the program is the whole sample, so
      no [wp_bind] is needed). *)
  Fact wp_laplace_diffpriv (loc loc' : Z) (num den : Z) K :
    0 < IZR num / IZR den →
    let e := (λ: "loc", Laplace #num #den "loc" #())%E in
    {{{ ⤇ fill K (e #loc') ∗ ↯m (IZR (Z.abs (loc - loc')) * (IZR num / IZR den)) }}}
      (e #loc)%E
      {{{ (z : Z), RET #z; ⤇ fill K (Val #z) }}}.
  Proof.
    iIntros (Hpos e Φ) "(f' & ε) post". subst e.
    tp_pures. wp_pures.
    iApply (wp_couple_laplace loc loc' 0%Z (Z.abs (loc - loc')) _ num den
              (IZR num / IZR den) (IZR (Z.abs (loc - loc')) * (IZR num / IZR den))
              K _ eq_refl Hpos eq_refl with "[$f' $ε]").
    iModIntro. iIntros (z) "f'". rewrite Z.add_0_r. iApply ("post" with "f'").
    Unshelve. rewrite Z.add_0_l. lia.
  Qed.

End wp_example.

(* The program (λ z . L(ε, z)) is ε-differentially private for ε = num/den. *)
Fact Laplace_diffpriv (Sg : Sig) `{!SampleIn laplace_family Sg} σ (num den : Z) :
  let ε := (IZR num / IZR den)%R in
  (0 < ε)%R →
  diffpriv_pure
    (λ x y, IZR (Z.abs (x - y)))
    (λ x, lim_exec (δ := lang_markov (gen_lang Sg))
            ((λ:"loc", Laplace #num #den "loc" #())%E #x, σ))
    ε.
Proof.
  intros ε εpos.
  eapply diffpriv_approx_pure.
  eapply (wp_diffpriv_Z Sg diffprivΣ) ; eauto ; try lra.
  iIntros (????) "f' ε ?".
  iApply (wp_laplace_diffpriv _ _ _ _ [] with "[f' ε]") => //.
  2: eauto.
  iFrame.
  iApply ecm_weaken. 2: iFrame.
  split.
  - apply Rmult_le_pos. 2: subst ε ; lra. apply IZR_le. lia.
  - etrans. 2: right ; apply Rmult_1_l. apply Rmult_le_compat_r. 1: lra. done.
Qed.

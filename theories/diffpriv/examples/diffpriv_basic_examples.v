From clutch Require Import prob_lang.class_instances.
From clutch.prob Require Import differential_privacy.
From clutch.diffpriv Require Import adequacy diffpriv proofmode.

Section wp_example.
  Context `{!diffprivGS Σ}.

  #[local] Open Scope R.

  Fact wp_laplace_diffpriv (loc loc' k' : Z)
    (num den : Z) :
    0 < IZR num / IZR den →
    let e := (λ: "loc", Laplace #num #den "loc")%E in
    {{{ ⤇ (e #loc') ∗ ↯ (IZR (Z.abs (loc - loc')) * (IZR num / IZR den)) }}}
      (e #loc)%E
      {{{ (z : Z), RET #z; ⤇ (Val #z) }}}.
  Proof.
    iIntros (???) "(f' & ε) post". subst e.
    tp_pures.
    wp_pures.
    tp_bind (Laplace _ _ _).
    iApply (wp_couple_laplace _ _ 0%Z with "[$]") => //.
    setoid_rewrite Z.add_0_r. done.
  Qed.

End wp_example.

(* The program (λ z . L(ε, z)) is ε-differentially private for ε = num/den. *)
Fact Laplace_diffpriv σ (num den : Z) :
  let ε := (IZR num / IZR den)%R in
  (0 < ε)%R →
  diffpriv_pure
    (λ x y, IZR (Z.abs (x - y)))
    (λ x, lim_exec ((λ:"loc", Laplace #num #den "loc")%E #x, σ))
    ε.
Proof.
  intros ε εpos.
  eapply (wp_diffpriv diffprivΣ) ; eauto ; try lra.
  iIntros (????) "f' ε".
  iApply (wp_laplace_diffpriv with "[f' ε]") => //.
  2: eauto.
  iFrame.
  iApply ec_weaken. 2: iFrame.
  split.
  - apply Rmult_le_pos. 2: subst ε ; lra. apply IZR_le. lia.
  - etrans. 2: right ; apply Rmult_1_l. apply Rmult_le_compat_r. 1: lra. done.
Qed.

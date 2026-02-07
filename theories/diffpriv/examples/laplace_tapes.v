From clutch.common Require Import inject.
From clutch.prob Require Import differential_privacy.
From clutch.diffpriv Require Import (* adequacy *) diffpriv proofmode.

Section wp_example.
  Context `{!diffprivGS Σ}.

  #[local] Open Scope R.

  Fact wp_laplace_diffpriv (loc loc' : Z)
    (num den : Z) K :
    0 < IZR num / IZR den →
    let e := (λ: "loc", let: "α" := AllocTapeLaplace #num #den "loc" in Laplace #num #den "loc" "α")%E in
    {{{ ⤇ fill K (e #loc') ∗ ↯m (IZR (Z.abs (loc - loc')) * (IZR num / IZR den)) }}}
      (e #loc)%E
      {{{ (z : Z), RET #z; ⤇ fill K (Val #z) }}}.
  Proof.
    iIntros (???) "(f' & ε) post". subst e.
    tp_pures.
    wp_pures.
    tp_bind (AllocTapeLaplace _ _ _).
    wp_apply (wp_alloc_tape_laplace) => //.
    iIntros "%α α". wp_pures.
    wp_apply (wp_rand_tape_laplace_empty with "α").
    iIntros "%z α".

    iApply (hoare_couple_laplace _ _ 0%Z with "[$]") => //.
    setoid_rewrite Z.add_0_r. done.
  Qed.

From clutch.common Require Import inject.
From clutch.prob Require Import differential_privacy.
From clutch.diffpriv Require Import (* adequacy *) diffpriv proofmode.

Section wp_example.
  Context `{!diffprivGS Σ}.

  #[local] Open Scope R.


  Fact wp_alloctape_safe (N : nat) :
    ⌜True⌝ ⊢ WP AllocTape #N {{ λ _, emp }}.
  Proof.
    iIntros "?".
    wp_alloctape α as "α".
    done.
  Qed.

  Fact tp_alloctape_safe (N : nat) :
    ⤇ (AllocTape #N) ⊢ WP #1+#1 {{ λ _, emp }}.
  Proof.
    iIntros "?".
    tp_alloctape as α "α".
    wp_pures. done.
  Qed.

  Fact wp_alloctape_laplace_safe (num den mean : Z) :
    ⌜True⌝ ⊢ WP AllocTapeLaplace #num #den #mean {{ λ _, emp }}.
  Proof.
    iIntros "?".
    wp_alloctape_laplace α as "α".
    done.
  Qed.

  Fact wp_laplace_safe (loc loc' : Z)
    (num den : Z) K :
    0 < IZR num / IZR den →
    let e := (λ: "loc", let: "α" := AllocTapeLaplace #num #den "loc" in Laplace #num #den "loc" "α")%E in
    {{{ ⤇ fill K (e #loc') ∗ ↯m (IZR (Z.abs (loc - loc')) * (IZR num / IZR den)) }}}
      (e #loc)%E
      {{{ (z : Z), RET #z; ∃ (z' : Z), ⤇ fill K (Val #z') }}}.
  Proof.
    iIntros (???) "(f' & ε) post". subst e.
    tp_pures.
    wp_pures.
    wp_alloctape_laplace α as "α".
    tp_alloctape_laplace α' as "α'".
    tp_pures. wp_pures.
    wp_apply (wp_laplace_empty_r with "[-]"). iFrame. iIntros "%z' [α' f]".
    wp_apply (wp_laplace_tape_empty with "α"). iIntros "%z α".
    iApply "post".
    iExists _.
    done.
  Qed.

  Fact wp_laplace_diffpriv (loc loc' : Z)
    (num den : Z) K :
    0 < IZR num / IZR den →
    let e := (λ: "loc", let: "α" := AllocTapeLaplace #num #den "loc" in Laplace #num #den "loc" "α")%E in
    {{{ ⤇ fill K (e #loc') ∗ ↯m (IZR (Z.abs (loc - loc')) * (IZR num / IZR den)) }}}
      (e #loc)%E
      {{{ (z : Z), RET #z; ⤇ fill K (Val #z) }}}.
  Proof.
    iIntros (???) "(rhs & ε) post". subst e.
    tp_pures.
    wp_pures.
    tp_alloctape_laplace α' as "α'".
    wp_alloctape_laplace α as "α".
    tp_pures ; wp_pures.
    wp_apply (wp_couple_tapes_laplace with "[ε $α $α']") => //.
    { iApply ecm_eq. 2: iFrame.
      Unshelve. 2: exact 0%Z. rewrite Zplus_0_l. reflexivity. }
    iIntros "%z [α α']". rewrite Zplus_0_r.
    (* TODO Why doesn't this work? Also, this tactic needs a better name. *)
    Fail wp_randtape_laplace.
    tp_laplace. wp_apply (wp_laplace_tape with "α").
    iIntros "α". iApply "post".
    done.
  Qed.

End wp_example.

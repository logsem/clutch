(** Tape-based Laplace example, ported from [diffpriv.examples.laplace_tapes]
    onto [gen_prob_lang] / [gen_diffpriv].  Demonstrates the presampling
    interface: allocate Laplace tapes on both sides, couple them (shifting the
    spec draw by [k]), then read the presampled values deterministically.

    A client only declares the signature [Slap] and a [SampleIn] instance; the
    Laplace tape API ([AllocTapeLaplace], [↪L]/[↪Lₛ], [wp_couple_tapes_laplace])
    comes from [lib.laplace_tapes].

    Note the [#[global] Opaque sample_idx]: in a *concrete* signature the index
    projection [sample_idx] is convertible to a numeral, and [wp_pures]/[tp_pures]
    would reduce it — after which the tape predicates ([↪L], written with the
    [sample_idx] projection) no longer *syntactically* [iFrame] against the
    reduced hypotheses.  Sealing [sample_idx] keeps the projection folded so the
    generic sample-tape tactics' output frames against the Laplace tape views. *)
From clutch.prob Require Import differential_privacy.
From clutch.gen_diffpriv Require Import all.
From clutch.gen_diffpriv.lib Require Import laplace laplace_tapes.

#[global] Opaque sample_idx.

Section wp_example.
  Context {Sg : Sig} `{!SampleIn laplace_family Sg} `{!diffprivGS Sg Σ}.
  #[local] Open Scope R.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Sg)).

  (** The differentially-private use of tapes: presample-couple the two tapes so
      the spec draw equals the impl draw (shift [k = 0]) at error
      [|loc − loc'|·ε], then read both off deterministically. *)
  Fact wp_laplace_diffpriv (loc loc' : Z) (num den : Z) K :
    0 < IZR num / IZR den →
    let e := (λ: "loc", let: "α" := AllocTapeLaplace #num #den "loc" in
                        Laplace #num #den "loc" "α")%E in
    {{{ ⤇ fill K (e #loc') ∗ ↯m (IZR (Z.abs (loc - loc')) * (IZR num / IZR den)) }}}
      (e #loc)%E
      {{{ (z : Z), RET #z; ⤇ fill K (Val #z) }}}.
  Proof.
    iIntros (Hpos ? ?) "(rhs & ε) post". subst e.
    tp_pures. wp_pures.
    tp_alloc_sample_tape as α' "α'".
    wp_alloc_sample_tape α as "α".
    tp_pures; wp_pures.
    iApply (wp_couple_tapes_laplace loc loc' 0%Z (Z.abs (loc - loc')) α α' [] []
              _ _ ltac:(rewrite Z.add_0_l; apply Z.le_refl) num den (IZR num / IZR den)
              (IZR (Z.abs (loc - loc')) * (IZR num / IZR den)) ⊤
              eq_refl Hpos eq_refl with "[$α $α' $ε]").
    iIntros "%z [α α']". rewrite Z.add_0_r.
    tp_sample_tape.
    wp_apply (wp_sample_tape with "α").
    iIntros "α". iApply "post". done.
  Qed.

End wp_example.

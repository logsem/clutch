(** A little case study for the extensible sampler typing rules.

    Two small *randomized* programs that interleave sampling with the rest of
    the type system (functions, arithmetic, let-binding, tapes, equality test).
    For each we show:
      (1) it is well-typed, exercising the new [Sample]/[Sample]-tape/
          [AllocSampleTape] rules *composed* with [Rec]/[BinOp]/[App]; and
      (2) it is contextually sound — [ctx_refines] of the program against
          itself — obtained purely from the fundamental theorem
          ([refines_typed]) via [refines_sound].  Before this work the
          fundamental theorem covered no sampling program, so (2) was simply
          out of reach for anything that draws randomness. *)
From iris.proofmode Require Import proofmode.
From clutch.gen_diffpriv Require Import model interp fundamental soundness.
From clutch.gen_prob_lang Require Import lang notation families.
From clutch.gen_prob_lang.typing Require Import types contextual_refinement.
From iris.prelude Require Import options.

Section case_study.
  (* Work over any signature that provides the uniform and Laplace families. *)
  Context (Sg : Sig).
  Context `{!SampleIn uniform_family Sg, !SampleIn laplace_family Sg}.

  Notation unif := (sample_idx (D := uniform_family)).
  Notation lap  := (sample_idx (D := laplace_family)).

  (* ----------------------------------------------------------------- *)
  (* 1. [noisy_add]: add a discrete-Laplace draw to an integer input.   *)
  (*    The Laplace parameter is the (num, den, mean) triple (0, 1, 0). *)
  (* ----------------------------------------------------------------- *)
  Definition noisy_add : expr :=
    (λ: "x", "x" + Sample lap (#0, (#1, #0)) #())%E.

  Lemma noisy_add_typed : typed Sg ∅ noisy_add (TInt → TInt)%ty.
  Proof.
    apply Rec_typed. eapply BinOp_typed_int; [ | | reflexivity ].
    - apply Var_typed. by simplify_map_eq.
    - eapply Sample_typed.
      + apply (sample_idx_S (D := laplace_family)).
      + apply _.
      + apply Pair_typed; [ apply Val_typed, Int_val_typed | ].
        apply Pair_typed; apply Val_typed, Int_val_typed.
      + apply Val_typed, Unit_val_typed.
  Qed.

  (* ----------------------------------------------------------------- *)
  (* 2. [collide]: allocate a uniform tape on [0, n], draw twice, and    *)
  (*    test the two draws for equality — a [TNat → TBool] function that *)
  (*    exercises tape allocation, two tape reads, and an unboxed [=].   *)
  (* ----------------------------------------------------------------- *)
  Definition collide : expr :=
    (λ: "n",
       let: "α" := AllocSampleTape unif "n" in
       (Sample unif "n" "α") = (Sample unif "n" "α"))%E.

  Lemma collide_typed : typed Sg ∅ collide (TNat → TBool)%ty.
  Proof.
    apply Rec_typed. eapply App_typed.
    - apply Rec_typed. eapply UnboxedEq_typed; [ apply UnboxedTInt | | ].
      + eapply Sample_tape_typed.
        * apply (sample_idx_S (D := uniform_family)).
        * apply _.
        * apply Var_typed. by simplify_map_eq.
        * apply Var_typed. by simplify_map_eq.
      + eapply Sample_tape_typed.
        * apply (sample_idx_S (D := uniform_family)).
        * apply _.
        * apply Var_typed. by simplify_map_eq.
        * apply Var_typed. by simplify_map_eq.
    - eapply AllocSampleTape_typed.
      + apply (sample_idx_S (D := uniform_family)).
      + apply _.
      + apply Var_typed. by simplify_map_eq.
  Qed.

  (* ----------------------------------------------------------------- *)
  (* Contextual soundness, for free, from the fundamental theorem.       *)
  (* ----------------------------------------------------------------- *)
  Lemma noisy_add_ctx_sound Σ `{!diffprivRGpreS Σ} :
    ctx_refines Sg ∅ noisy_add noisy_add (TInt → TInt)%ty.
  Proof.
    apply (refines_sound Sg Σ). intros ? Δ.
    iApply refines_typed. apply noisy_add_typed.
  Qed.

  Lemma collide_ctx_sound Σ `{!diffprivRGpreS Σ} :
    ctx_refines Sg ∅ collide collide (TNat → TBool)%ty.
  Proof.
    apply (refines_sound Sg Σ). intros ? Δ.
    iApply refines_typed. apply collide_typed.
  Qed.

End case_study.

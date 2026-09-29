(** Canary: the extensible sampler typing rules ([Sample_typed],
    [Sample_tape_typed], [AllocSampleTape_typed]) fire for the concrete families
    via their [SampleTyping] instances, plug into the fundamental theorem
    ([refines_typed]), and the matching context-typing items ([TP_CTX_Sample*])
    are derivable.  Everything is generic over the ambient signature [Sg]: we
    only assume the families are members ([SampleIn]). *)
From iris.proofmode Require Import proofmode.
From clutch.gen_diffpriv Require Import model interp fundamental.
From clutch.gen_prob_lang Require Import lang notation families.
From clutch.gen_prob_lang.typing Require Import types contextual_refinement.
From iris.prelude Require Import options.

Section canary.
  Context `{!diffprivRGS Sg Σ}.
  Context `{!SampleIn uniform_family Sg,
            !SampleIn laplace_family Sg,
            !SampleIn coin_family Sg}.

  (** Direct sampling is well-typed: uniform [: TNat → TInt]. *)
  Example uniform_typed (e1 : expr) :
    typed Sg ∅ e1 TNat →
    typed Sg ∅ (Sample (sample_idx (D := uniform_family)) e1 (Val #())) TInt.
  Proof.
    intros He1.
    eapply Sample_typed;
      [ apply (sample_idx_S (D := uniform_family)) | apply _
      | exact He1 | apply Val_typed, Unit_val_typed ].
  Qed.

  (** Laplace [: (TInt*(TInt*TInt)) → TInt]. *)
  Example laplace_typed (e1 : expr) :
    typed Sg ∅ e1 (TInt * (TInt * TInt)) →
    typed Sg ∅ (Sample (sample_idx (D := laplace_family)) e1 (Val #())) TInt.
  Proof.
    intros He1.
    eapply Sample_typed;
      [ apply (sample_idx_S (D := laplace_family)) | apply _
      | exact He1 | apply Val_typed, Unit_val_typed ].
  Qed.

  (** Coin [: (TInt*TInt) → TBool]. *)
  Example coin_typed (e1 : expr) :
    typed Sg ∅ e1 (TInt * TInt) →
    typed Sg ∅ (Sample (sample_idx (D := coin_family)) e1 (Val #())) TBool.
  Proof.
    intros He1.
    eapply Sample_typed;
      [ apply (sample_idx_S (D := coin_family)) | apply _
      | exact He1 | apply Val_typed, Unit_val_typed ].
  Qed.

  (** Tape-based sampling: allocate a uniform tape and read from it. *)
  Example uniform_tape_typed (e1 : expr) :
    typed Sg ∅ e1 TNat →
    typed Sg ∅
      (Sample (sample_idx (D := uniform_family)) e1
              (AllocSampleTape (sample_idx (D := uniform_family)) e1)) TInt.
  Proof.
    intros He1.
    eapply Sample_tape_typed;
      [ apply (sample_idx_S (D := uniform_family)) | apply _ | exact He1 | ].
    eapply AllocSampleTape_typed;
      [ apply (sample_idx_S (D := uniform_family)) | apply _ | exact He1 ].
  Qed.

  (** The typing rules plug into the fundamental theorem: a well-typed sampling
      program self-refines in the logical relation. *)
  Example uniform_refines Δ (e1 : expr) :
    typed Sg ∅ e1 TNat →
    ⊢ REL (Sample (sample_idx (D := uniform_family)) e1 (Val #()))
       << (Sample (sample_idx (D := uniform_family)) e1 (Val #()))
        : interp TInt Δ.
  Proof. intros He1. iApply refines_typed. by apply uniform_typed. Qed.

  (** Context typing: a [Sample] frame with the hole in the parameter position
      is a well-typed context [TNat ⤳ TInt]. *)
  Example ctx_sample_typed :
    typed_ctx Sg [CTX_SampleL (sample_idx (D := uniform_family)) (Val #())]
              ∅ TNat ∅ TInt.
  Proof.
    eapply TPCTX_cons; [ | apply TPCTX_nil ].
    eapply TP_CTX_SampleL_unit;
      [ apply (sample_idx_S (D := uniform_family)) | apply _
      | apply Val_typed, Unit_val_typed ].
  Qed.

End canary.

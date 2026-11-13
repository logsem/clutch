From Autosubst Require Import Autosubst.
From iris.proofmode Require Import base proofmode.
From clutch.prob_eff_lang.probblaze Require Import syntax semantics notation logic
  sem_def sem_types sem_row sem_sig sem_env sem_judgement mode compatibility.
From clutch.prob_eff_lang.probblaze.typing Require Import types tychk interp
  fundamental interp_simp.

(** * End-to-end conversion of a semantic typing lemma (PLAN.md, Stage F)

    The send handler of F_OAUTH (the body of [oauth_send_handler_typed] in
    examples/secure_channel/sec_channel_typing.v and its SKE copy in
    ske_sec_chan_typing.v) is typed syntactically by [tychk], at a payload
    type variable made copyable, [![MS] (TVar 0)].  The derivation is
    transported by [fundamental] and instantiated with an arbitrary
    copyable semantic type [τ] ([MultiT τ]); since [![MS] τ ≡ τ] for such a
    [τ], the interpreted contexts are equivalent to the ones of the semantic
    statement.  The two example files instantiate [τ] with [𝔾] and [Cph].

    Syntactic row variables: [RVar 0] is the ambient row [ρ], [RVar 1] the
    leak row [θ₂]; the handler runs at [¡[OS] (RVar 1) ∪ᵣ RVar 0], the
    mirror of [sem_row_union (¡ θ₂) ρ]. *)

(** The handler body, as in the two example files. *)
Definition oauth_send_body : expr :=
  (let, ("m", "dst") := "payload" in
   match: !"message" with
   | NONE => "message" <- SOME "m" ;; ("doLeakSend" ("m", "dst"));; "k" #()%V
   | SOME "stored" => "k" #()%V
   end)%E.

Local Notation G := (![MS] (TVar 0))%ty.

(** One annotation: the leak function is used at the row [¡[OS] (RVar 1)]
    instead of its own [RVar 1].  Its call happens while the one-shot [k] is
    live, so the latent row of the call must be [OnceR] (premise
    [ρ'' R⪯C Γ3] of [App_typed]); without the annotation [tychk] leaves the
    underivable residual [RVar 1 R⪯C Γ]. *)
Definition oauth_send_body_ann : expr :=
  (let, ("m", "dst") := "payload" in
   match: !"message" with
   | NONE => "message" <- SOME "m" ;;
             (tyann ((G * (() + ())) -{ ¡[OS] (RVar 1) }-> ())%ty "doLeakSend" ("m", "dst"));;
             "k" #()%V
   | SOME "stored" => "k" #()%V
   end)%E.

Lemma oauth_send_handler_syn :
  ∅ .| [("payload", (G * (() + ()))%ty);
        ("k", (() -{ ¡[OS] (RVar 1) ∪ᵣ RVar 0 }-[OS]-> ())%ty);
        ("message", (refᶜ (() + G))%ty);
        ("doLeakSend", ((G * (() + ())) -{ RVar 1 }-> ())%ty)]
    ⊢ₜ oauth_send_body : (¡[OS] (RVar 1) ∪ᵣ RVar 0)%ty : ()
    ⊣ [("message", (refᶜ (() + G))%ty);
       ("doLeakSend", ((G * (() + ())) -{ RVar 1 }-> ())%ty)].
Proof. change oauth_send_body with oauth_send_body_ann. unfold oauth_send_body_ann. tychk. Qed.

Section stagef.
  Context `{!probblazeRGS Σ}.

  (** General facts used by the bridge. *)
  Lemma ty_le_of_equiv (τ τ' : sem_ty Σ) : τ ≡ τ' → ⊢ τ ≤ₜ τ'.
  Proof. iIntros (Heq) "!#". iIntros (v1 v2) "H". by rewrite (Heq v1 v2). Qed.

  Lemma mbang_MS_equiv (τ : sem_ty Σ) `{!MultiT τ} : sem_ty_mbang syntax.MS τ ≡ τ.
  Proof.
    intros v1 v2. iSplit.
    - iIntros "H". rewrite /sem_ty_mbang /=. by iDestruct "H" as "#H".
    - iIntros "H". iPoseProof (@multi_ty Σ τ _) as "#Hm". by iApply "Hm".
  Qed.

  (** The semantic send handler at any copyable payload type [τ]. *)
  Lemma oauth_send_handler_sem (τ : sem_ty Σ) `{!MultiT τ} (θ₂ ρ : sem_row Σ) :
    ⊢ sem_typed [("payload", (τ × (𝟙 + 𝟙))%T); ("k", (𝟙 -{ sem_row_union (¡ θ₂) ρ }-[syntax.OS]-> 𝟙)%T);
                 ("message", Refᶜ (Option τ)); ("doLeakSend", ((τ × (𝟙 + 𝟙)) -{ θ₂ }-> 𝟙)%T)]
        oauth_send_body oauth_send_body (sem_row_union (¡ θ₂) ρ) 𝟙
        [("message", Refᶜ (Option τ)); ("doLeakSend", ((τ × (𝟙 + 𝟙)) -{ θ₂ }-> 𝟙)%T)].
  Proof.
    pose proof oauth_send_handler_syn as Hsyn.
    iPoseProof (fundamental _ _ _ _ _ _ Hsyn) as "H".
    rewrite /bin_log_related.
    (* [TVar 0 ↦ τ], [RVar 0 ↦ ρ], [RVar 1 ↦ θ₂]; no effect names. *)
    iSpecialize ("H" $! [τ] [] ∅ [ρ; θ₂] with "[]"); first by iPureIntro.
    rewrite !(typed_lbl_resolve_id _ _ _ _ _ _ Hsyn);
      [|by rewrite dom_empty_L; apply disjoint_empty_r..].
    iApply (sem_typed_sub with "[] [] [] [] H").
    all: iClear "H"; cbn [fmap list_fmap]; interp_simp.
    3: iApply row_le_refl.
    3: iApply ty_le_refl.
    (* Contexts: entry-wise equivalent, as [![MS] τ ≡ τ]. *)
    all: repeat iApply env_le_cons; try iApply env_le_refl;
      iApply ty_le_of_equiv; by rewrite ?(mbang_MS_equiv τ).
  Qed.
End stagef.

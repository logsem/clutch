(** A SOUND SAMPLING TYPING / REFINEMENT RULE for the generic DP logical
    relation.

    The generic language adds a single sampling primitive [Sample i e1 e2].
    This file isolates *sufficient syntactic conditions* under which sampling
    from a family [D] (at the index it occupies in the signature) is a sound
    extension of the binary logical relation — i.e. satisfies the compatibility
    lemma [refines_sample], hence can be added to the fundamental theorem.

    The conditions, for a family [D] sampled at type [τp → τo]:
      (1) [EqType τp]                         — the parameter type is "discrete",
          so logically-related parameters are equal (the two sides sample the
          SAME distribution, coupled reflexively at zero cost);
      (2) decoding succeeds on [τp]-values    — [sf_param_of_val D] is defined on
          every value of type [τp] (the sample never gets stuck);
      (3) [sf_inj D] lands in [⟦τo⟧]          — every outcome, embedded into a
          value, is related to itself at [τo].

    The three concrete families satisfy these (see the instantiations at the
    bottom): uniform [: TNat → TInt], laplace [: TInt*(TInt*TInt) → TInt],
    coin [: TInt*TInt → TBool]. *)
From iris.proofmode Require Import proofmode.
From clutch.prob Require Import distribution couplings couplings_app couplings_dp.
From clutch.gen_prob_lang Require Import lang notation families.
From clutch.gen_diffpriv Require Import primitive_laws coupling_rules model interp
  app_rel_rules rel_tactics proofmode.
From clutch.gen_prob_lang.typing Require Import types.
From iris.prelude Require Import options.

#[local] Open Scope R.

(** The reflexive coupling: any distribution couples with itself along equality
    at zero multiplicative and additive cost. *)
Lemma DPcoupl_refl `{Countable A} (μ : distr A) : DPcoupl μ μ (=) 0 0.
Proof. apply ARcoupl_to_DPcoupl, ARcoupl_eq. Qed.

Section sample.
  Context `{!diffprivRGS Sg Σ}.

  (** [sig_sample] at the index of [D] decodes [v] to [p] and samples [D p]. *)
  Lemma sig_sample_decode (D : SampleFamily) `{!SampleIn D Sg} (v : val) (p : sf_param D) :
    sf_param_of_val D v = Some p →
    sig_sample Sg (sample_idx (D := D)) v = Some (dmap (sf_inj D) (sf_sample D p)).
  Proof. intros Hp. unfold sig_sample. rewrite sample_idx_S /= Hp /=. reflexivity. Qed.

  (** ** The compatibility lemma for sampling. *)
  Lemma refines_sample (D : SampleFamily) `{!SampleIn D Sg} (τp τo : type) Δ e1 e1' :
    EqType τp →
    (∀ v1 v1', interp τp Δ v1 v1' -∗ ⌜∃ p, sf_param_of_val D v1 = Some p⌝) →
    (∀ o : sf_out D, ⊢ interp τo Δ (sf_inj D o) (sf_inj D o)) →
    (REL e1 << e1' : interp τp Δ) -∗
    REL Sample (sample_idx (D := D)) e1 (Val (LitV LitUnit))
     << Sample (sample_idx (D := D)) e1' (Val (LitV LitUnit)) : interp τo Δ.
  Proof.
    iIntros (HeqP Hdec Hout) "Hrel".
    rel_bind_l e1; rel_bind_r e1';
    iApply (refines_bind with "Hrel");
    iIntros (v1 v1') "Hvv"; simpl.
    iDestruct (eq_type_sound _ _ _ _ HeqP with "Hvv") as %<-.
    iDestruct (Hdec _ _ with "Hvv") as %[p Hp].
    rewrite refines_eq /refines_def.
    iIntros (K ε) "Hspec Hna Herr %Hε".
    iMod ecm_zero as "Hm".
    iApply (wp_couple_sample_gen Sg (sample_idx (D := D)) v1 v1
              (dmap (sf_inj D) (sf_sample D p))
              (dmap (sf_inj D) (sf_sample D p))
              (λ w w', ∃ o : sf_out D, w = sf_inj D o ∧ w' = sf_inj D o) K ⊤ 0
              (sig_sample_decode D v1 p Hp) (sig_sample_decode D v1 p Hp) _
              with "[$Hspec $Hm]").
    { iIntros "!>" (w w') "(Hspec & %HR)". destruct HR as (o & -> & ->).
      iExists (sf_inj D o), ε. iFrame "Hspec Hna Herr".
      iSplitR; [done|]. iApply Hout. }
    (* the coupling obligation: reflexive coupling of [D p] lifted through sf_inj *)
    Unshelve.
    apply (DPcoupl_map (sf_inj D) (sf_inj D) (sf_sample D p) (sf_sample D p)
             (λ w w', ∃ o : sf_out D, w = sf_inj D o ∧ w' = sf_inj D o) 0 0);
      [lra | lra | ].
    eapply (DPcoupl_mono (sf_sample D p) (sf_sample D p) (sf_sample D p) (sf_sample D p)
              (=) (λ a a', ∃ o : sf_out D, sf_inj D a = sf_inj D o ∧ sf_inj D a' = sf_inj D o)
              0 0 0 0);
      [ intros; reflexivity | intros; reflexivity
      | intros a a' ->; by exists a' | lra | lra | apply DPcoupl_refl ].
  Qed.

  (** ** Instantiations: the three concrete families are typeable.

      Each discharges the three side conditions of [refines_sample], confirming
      the conditions are realistic.  These are the sound sampling typing rules:
        uniform : TNat            → TInt
        laplace : TInt*(TInt*TInt) → TInt
        coin    : TInt*TInt        → TBool          *)

  Lemma refines_uniform `{!SampleIn uniform_family Sg} Δ e1 e1' :
    (REL e1 << e1' : interp TNat Δ) -∗
    REL Sample (sample_idx (D := uniform_family)) e1 (Val (LitV LitUnit))
     << Sample (sample_idx (D := uniform_family)) e1' (Val (LitV LitUnit)) : interp TInt Δ.
  Proof.
    iApply (refines_sample uniform_family TNat TInt).
    - constructor.
    - iIntros (v1 v1') "H /=". iDestruct "H" as (n) "[-> _]". iPureIntro. by eexists.
    - iIntros (o). iExists o. done.
  Qed.

  Lemma refines_laplace `{!SampleIn laplace_family Sg} Δ e1 e1' :
    (REL e1 << e1' : interp (TInt * (TInt * TInt)) Δ) -∗
    REL Sample (sample_idx (D := laplace_family)) e1 (Val (LitV LitUnit))
     << Sample (sample_idx (D := laplace_family)) e1' (Val (LitV LitUnit)) : interp TInt Δ.
  Proof.
    iApply (refines_sample laplace_family (TInt * (TInt * TInt))%ty TInt).
    - repeat constructor.
    - iIntros (v1 v1') "H /=".
      iDestruct "H" as (?? ??) "(-> & -> & H1 & H2)".
      iDestruct "H1" as (?) "[-> _]". iDestruct "H2" as (?? ??) "(-> & -> & H3 & H4)".
      iDestruct "H3" as (?) "[-> _]". iDestruct "H4" as (?) "[-> _]".
      iPureIntro. by eexists.
    - iIntros (o). iExists o. done.
  Qed.

  Lemma refines_coin `{!SampleIn coin_family Sg} Δ e1 e1' :
    (REL e1 << e1' : interp (TInt * TInt) Δ) -∗
    REL Sample (sample_idx (D := coin_family)) e1 (Val (LitV LitUnit))
     << Sample (sample_idx (D := coin_family)) e1' (Val (LitV LitUnit)) : interp TBool Δ.
  Proof.
    iApply (refines_sample coin_family (TInt * TInt)%ty TBool).
    - repeat constructor.
    - iIntros (v1 v1') "H /=".
      iDestruct "H" as (?? ??) "(-> & -> & H1 & H2)".
      iDestruct "H1" as (?) "[-> _]". iDestruct "H2" as (?) "[-> _]".
      iPureIntro. by eexists.
    - iIntros (o). iExists o. done.
  Qed.

End sample.

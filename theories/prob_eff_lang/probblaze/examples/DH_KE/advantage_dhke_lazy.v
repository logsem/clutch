From clutch.prob_eff_lang.probblaze.typing Require Import types interp.
From Coq.Logic Require Import FunctionalExtensionality.
From clutch.prob_eff_lang.probblaze Require Import advantage.
From iris.algebra Require Import excl.
From iris.algebra.lib Require Import dfrac_agree.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_judgement sem_row syntax semantics proofmode valgroup.
From clutch.prob_eff_lang.probblaze Require Import 
  dhke_channel_lazy_results 
  dhke_channel_lazy_authchan
  def_dhke adequacy.

(* [interp._ty]/[interp._row]/[interp._mode] are fixpoints returning OFE
   morphisms ([_ -n> _]); [cbn]/[simpl] fail to reduce them (they choke on the
   [ofe_mor_car] / [NonExpansive] proof terms).  These one-step unfolding
   equations hold by [reflexivity] (they are definitional) and let us drive the
   interpretation of a closed type by [rewrite] instead. *)
Section interp_unfold.
  Context `{!probblazeRGS Σ}.
  Lemma interp_TForallR η μ δ (τ : type) ξ :
    interp._ty η μ δ (TForallR τ) ξ
    = sem_ty_row_forall (λ ρ, interp._ty η μ δ τ (ρ :: ξ)).
  Proof. reflexivity. Qed.
  Lemma interp_TArrow η μ δ α ρ β ξ :
    interp._ty η μ δ (TArrow α ρ β) ξ
    = sem_ty_arr (interp._row η μ δ ρ ξ) (interp._ty η μ δ α ξ) (interp._ty η μ δ β ξ).
  Proof. reflexivity. Qed.
  Lemma interp_TBang η μ δ m τ ξ :
    interp._ty η μ δ (TBang m τ) ξ = sem_ty_mbang (interp._mode μ m) (interp._ty η μ δ τ ξ).
  Proof. reflexivity. Qed.
  Lemma interp_TProd η μ δ τ1 τ2 ξ :
    interp._ty η μ δ (TProd τ1 τ2) ξ
    = sem_ty_prod (interp._ty η μ δ τ1 ξ) (interp._ty η μ δ τ2 ξ).
  Proof. reflexivity. Qed.
  Lemma interp_TSum η μ δ τ1 τ2 ξ :
    interp._ty η μ δ (TSum τ1 τ2) ξ
    = sem_ty_sum (interp._ty η μ δ τ1 ξ) (interp._ty η μ δ τ2 ξ).
  Proof. reflexivity. Qed.
  Lemma interp_TUnit η μ δ ξ : interp._ty η μ δ TUnit ξ = sem_ty_unit.
  Proof. reflexivity. Qed.
  Lemma interp_RVar η μ δ i ξ : interp._row η μ δ (RVar i) ξ = ξ !!! i.
  Proof. reflexivity. Qed.
  Lemma interp_RUnion η μ δ ρ1 ρ2 ξ :
    interp._row η μ δ (RUnion ρ1 ρ2) ξ
    = sem_row_union (interp._row η μ δ ρ1 ξ) (interp._row η μ δ ρ2 ξ).
  Proof. reflexivity. Qed.
  Lemma interp_RNil η μ δ ξ : interp._row η μ δ RNil ξ = sem_row_nil.
  Proof. reflexivity. Qed.
  Lemma interp_mode_MS μ : interp._mode μ MS = syntax.MS.
  Proof. reflexivity. Qed.
End interp_unfold.

Section adv_dhke.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.
  Context `{probblazeRGpreS Σ}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.
  Context {la1 la2 : label}.     (* TODO can be removed once dhke_channel.v has been cleaned up *)

  Import valgroup_notation.

  Definition τ_DH `{!probblazeRGS Σ}
    := (∀ᵣ θ__L, (∀ᵣ θₕ, ((sem_ty_sum 𝟙 𝟙) -{ θₕ }-> (Option 𝔾)) -{ sem_row_union θₕ θ__L }-∘ 𝟙)%T 
                 ⊸ ((∀ᵣ θₗ, (((𝔾 × (𝟙 + 𝟙)) -{ θₗ }-> 𝟙) × ((𝟙 + 𝟙) -{ θₗ }-> Option 𝔾))
                            -{ sem_row_union θₗ θ__L }-∘ 𝟙)))%T.

  (* Syntactic type whose interpretation is [τ_DH].  De Bruijn indices: inside
     [∀ᵣ θ__L] then [∀ᵣ θₕ] (resp. [∀ᵣ θₗ]) the inner bound row is [RVar 0] and
     [θ__L] is [RVar 1], so the effect [sem_row_union θₕ θ__L] is [RUnion (RVar 0%nat)
     (RVar 1%nat)].  Leaves: [𝟙+𝟙 = TSum TUnit TUnit], [Option 𝔾 = TSum TUnit τG],
     [𝔾×(𝟙+𝟙) = TProd τG (TSum TUnit TUnit)], [𝔾 = interp τG] via [τG_lrel]. *)
  Definition T_DH : type :=
    TForallR (
      TArrow
        (TForallR (
           TArrow (TBang MS (TArrow (TSum TUnit TUnit) (RVar 0%nat) (TSum TUnit τG)))
                  (RUnion (RVar 0%nat) (RVar 1%nat)) TUnit))
        RNil
        (TForallR (
           TArrow (TProd (TBang MS (TArrow (TProd τG (TSum TUnit TUnit)) (RVar 0%nat) TUnit))
                         (TBang MS (TArrow (TSum TUnit TUnit) (RVar 0%nat) (TSum TUnit τG))))
                  (RUnion (RVar 0%nat) (RVar 1%nat)) TUnit))).

  Lemma T_DH_interp `{!probblazeRGS Σ} η μ δ ξ :
    interp._ty η μ δ T_DH ξ = τ_DH.
  Proof using All.
    (* Only the group leaves are non-definitional; [HG] bridges them via
       [τG_lrel] (instance supplied by the section's [G]). *)
    assert (HG : ∀ ζ, interp._ty η μ δ τG ζ = sem_ty_group) by
      (intros ζ; extensionality v1; extensionality v2; symmetry;
       apply (τG_lrel (clutch_group := G _ _))).
    rewrite /T_DH /τ_DH /sem_ty_option.
    (* Peel the interpretation constructor-by-constructor: [rewrite] the
       reflexivity-unfolding lemmas at the head, then a congruence step
       (targeted [f_equal]/[functional_extensionality], since generic [f_equal]
       is too slow on these OFE terms), closing group leaves with [HG]. *)
    repeat (
      rewrite ?interp_TForallR ?interp_TArrow ?interp_TBang ?interp_TProd ?interp_TSum
              ?interp_TUnit ?interp_RVar ?interp_RUnion ?interp_RNil ?interp_mode_MS;
      first [ apply HG
            | reflexivity
            | apply (f_equal sem_ty_row_forall)
            | apply (f_equal3 sem_ty_arr)
            | apply (f_equal2 sem_ty_prod)
            | apply (f_equal2 sem_ty_sum)
            | apply (f_equal2 sem_ty_mbang)
            | apply (f_equal2 sem_row_union)
            | (apply functional_extensionality; intros ?) ]).
  Qed.

  Lemma adv_DHKE_DH_real  A :
    (∀ `{!probblazeRGS Σ}, 
       ⊢ sem_val_typed A A (τ_DH → 𝔹)%T) →
    nonneg (advantage A (λ: "f", F_AUTH (DH_KE "f"))%V ((λ: "DH" "f", F_AUTH (C_lazy "DH" "f"))%V DH_real) #true) = 0%R.
  Proof using H inG0 inG1 inG2 la2 G. (* also debris from dhke_channel *)
    intros. eapply sem_typed_advantage; eauto. split.
    - intros Hrgs. apply DHKE_RED; eauto. 
    - intros Hrgs. apply RED_DHKE; eauto.
  Qed. 

  Lemma adv_DH_rand_FKE  A :
    (∀ `{!probblazeRGS Σ},⊢ sem_val_typed A A (τ_DH → 𝔹)%T) →
    nonneg (advantage A ((λ: "DH" "f", F_AUTH (C_lazy "DH" "f"))%V DH_rand) (λ: "f", F_AUTH (DH_SIM (F_KE_lazy_alice "f")))%V  #true) = 0%R.
  Proof using H inG0 inG1 inG2 G la2. 
    intros. eapply sem_typed_advantage; eauto. split.
    - intros Hrgs. apply RED_DHSIM; eauto.
    - intros Hrgs. apply DHSIM_RED; eauto.
  Qed. 

  Theorem adv_DHKE A (ε : R) :
    (∀ `{!probblazeRGS Σ},⊢ sem_val_typed A A (τ_DH → 𝔹)%T) →
    advantage A ((λ: "DH" "f", F_AUTH (C_lazy "DH" "f"))%V DH_real) ((λ: "DH" "f", F_AUTH (C_lazy "DH" "f"))%V DH_rand) #true <= ε →
    advantage A (λ: "f", F_AUTH (DH_KE "f"))%V (λ: "f", F_AUTH (DH_SIM (F_KE_lazy_alice "f")))%V #true <= ε.
  Proof using H inG0 inG1 inG2 G la2. 
    intros HA HAadv.
    eapply advantage_triangle.
    - right. by apply adv_DHKE_DH_real.
    - eapply advantage_triangle. 
      + apply HAadv.
      + right. by apply adv_DH_rand_FKE.
      + done.
    - lra.
  Qed.

  Corollary adv_DHKE_no_epsilon  A :
    (∀ `{!probblazeRGS Σ},⊢ sem_val_typed A A (τ_DH → 𝔹)%T) →
    advantage A (λ: "f", F_AUTH (DH_KE "f"))%V (λ: "f", F_AUTH (DH_SIM (F_KE_lazy_alice "f")))%V #true 
    <= advantage A ((λ: "DH" "f", F_AUTH (C_lazy "DH" "f"))%V DH_real) ((λ: "DH" "f", F_AUTH (C_lazy "DH" "f"))%V DH_rand) #true.
  Proof using H inG0 inG1 inG2 G la2. 
    intros. eapply adv_DHKE; eauto; lra.
  Qed.
    
  Theorem adv_DHKE_real A :
    (∀ `{!probblazeRGS Σ},⊢ sem_val_typed A A (τ_DH → 𝔹)%T) →
    advantage A (λ: "f", F_AUTH (DH_KE "f"))%V (λ: "f", F_AUTH (DH_SIM (F_KE_lazy_alice "f")))%V #true <=
      advantage (λ: "v", A (((λ: "DH", (λ: "f", F_AUTH (C_lazy "DH" "f")))%V "v")))%V DH_real DH_rand #true.
  Proof using H inG0 inG1 inG2 G la2.  
    intros.
    etrans. 
    - apply adv_DHKE_no_epsilon; eauto.
    - eapply advantage_reduction. 
      intros ?. eexists _,_.
      split; try done.
      split.
      + admit.                  (* F_AUTH ∘ C is well-typed *)
      + admit.                  (* DH_real and DH_rand are well-typed *)
  Admitted. 

End adv_dhke.

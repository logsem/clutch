From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import agree excl auth frac excl_auth.
From iris.algebra.lib Require Import dfrac_agree.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import
  logic primitive_laws proofmode
  spec_rules spec_ra class_instances tactics notation valgroup metatheory
  sem_types sem_row sem_sig sem_judgement sem_def
  def_dhke sec_channel_def xor sec_channel_prf dhke_channel_lazy_results dhke_channel_lazy_authchan.
From clutch.prob_eff_lang.probblaze.typing Require Import fundamental.
From clutch.prob_eff_lang.probblaze.examples.DH_KE Require Import
  new_composition_defs new_composition_closed new_composition_typing.

Import fingroup.
Import fingroup.fingroup.

Import valgroup_tactics.

(* Top-level semantic-typing results: each composite program is related to
   itself (or to the next in the chain) at the target type [τ].  The proofs
   are complete modulo the building-block typing lemmas admitted in
   [new_composition_typing.v]. *)

Section new_comp_verification.
  Context `{probblazeRGS Σ}.


  Lemma functionality_comp_func_comp_assoc_curried (F G : expr) (J : expr) (f x y : string) τ1 τ2 τ1' τJ τJ' τF :
    (BNamed f) ≠ (BNamed x) →
    (BNamed f) ≠ (BNamed y) →
    (BNamed x) ≠ (BNamed y) →
     is_closed_expr ∅ F →
     is_closed_expr ∅ G →
    ⊢ sem_typed [] F F ⊥ (∀ᵣ θ, (∀ᵣ θF, τF θF -{ sem_row_union θF θ}-∘ 𝟙) ⊸ ∀ᵣ θ1, τ2 θ1 -{ sem_row_union θ1 θ }-∘ 𝟙)%T [] -∗

    sem_typed [] G G ⊥ (∀ᵣ θ, (∀ᵣ θJ, τJ θJ ⊸ τJ' θJ -{ sem_row_union θJ θ}-∘ 𝟙) ⊸ ∀ᵣ θ1, τ1 θ1 ⊸ ∀ᵣ θ2, τF θ2 -{ sem_row_union θ1 (sem_row_union θ2 θ)}-∘ 𝟙)%T [] -∗

    (∀ θ θJ, sem_typed [(f, τ1' θ); (x, τJ θJ); (y, τJ' θJ)] J J (sem_row_union θJ θ) (𝟙)%T []) -∗

    sem_val_typed ((F ∘F G) ∘f (λ: f x y, J)%V) (F ∘F (G ∘f (λ: f x y, J)%V))
      (∀ᵣ θ, (τ1' θ) ⊸ (∀ᵣ θ1, ∀ᵣ θ2, (τ1 θ1) ⊸ (τ2 θ2) -{ sem_row_union θ1 (sem_row_union θ2 θ) }-∘ 𝟙))%T.
  Admitted.

  Lemma functionality_comp_func_comp_assoc_rev_curried (F G : expr) (J : expr) (f x y : string) τ1 τ2 τ1' τJ τJ' τF :
    (BNamed f) ≠ (BNamed x) →
    (BNamed f) ≠ (BNamed y) →
    (BNamed x) ≠ (BNamed y) →
     is_closed_expr ∅ F →
     is_closed_expr ∅ G →
    ⊢ sem_typed [] F F ⊥ (∀ᵣ θ, (∀ᵣ θF, τF θF -{ sem_row_union θF θ}-∘ 𝟙) ⊸ ∀ᵣ θ1, τ2 θ1 -{ sem_row_union θ1 θ }-∘ 𝟙)%T [] -∗

    sem_typed [] G G ⊥ (∀ᵣ θ, (∀ᵣ θJ, τJ θJ ⊸ τJ' θJ -{ sem_row_union θJ θ}-∘ 𝟙) ⊸ ∀ᵣ θ1, τ1 θ1 ⊸ ∀ᵣ θ2, τF θ2 -{ sem_row_union θ1 (sem_row_union θ2 θ)}-∘ 𝟙)%T [] -∗

    (∀ θ θJ, sem_typed [(f, τ1' θ); (x, τJ θJ); (y, τJ' θJ)] J J (sem_row_union θJ θ) (𝟙)%T []) -∗

    sem_val_typed (F ∘F (G ∘f (λ: f x y, J)%V)) ((F ∘F G) ∘f (λ: f x y, J)%V)
      (∀ᵣ θ, (τ1' θ) ⊸ (∀ᵣ θ1, ∀ᵣ θ2, (τ1 θ1) ⊸ (τ2 θ2) -{ sem_row_union θ1 (sem_row_union θ2 θ) }-∘ 𝟙))%T.
  Admitted.


  Context (channel leaksec channel1 channel2 getKey1 getKey2 leakauth1 leakauth2 keyleak1 keyleak2 schannel1 schannel2 l1 l2 l2': label).
  Context {vg: val_group}.
  Context {cg: clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg: @val_group_generator vg}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO,!inG Σ (dfrac_agreeR valO)}.
  Let Key := S (S n'').
  Let Support := S (S n'').
  Variable xor_struct : XOR (Key := Key) (Support := Support).
  Context `{!XOR_spec (Key := Key) (Support := Support) (H := xor_struct)}.

  (* The composites that mention [CHAN xor] / [R_CHAN] depend on the section
     variable [xor_struct] (via the [XOR] projection [xor]); once the
     definitions live in a separate file they are generalised over it, so we
     re-fix [xor_struct] here to read them back as plain values.  ([SIMSIMFCHAN]
     and [τ] do not mention [xor], so they need no re-fixing; the [iApply]-ed
     typing/closedness lemmas infer [xor_struct] from the goal.) *)
  Local Notation REAL_CHAN_DHKE := (REAL_CHAN_DHKE xor_struct).
  Local Notation REAL_CHAN_DH_REAL := (REAL_CHAN_DH_REAL xor_struct).
  Local Notation REAL_CHAN_DH_RAND := (REAL_CHAN_DH_RAND xor_struct).
  Local Notation DHSIM_FKE_CHAN1 := (DHSIM_FKE_CHAN1 xor_struct).
  Local Notation DHSIM_FKE_CHAN2 := (DHSIM_FKE_CHAN2 xor_struct).
  Local Notation DHSIM_FKE_CHAN3 := (DHSIM_FKE_CHAN3 xor_struct).
  Local Notation DHSIM_FKE_CHAN4 := (DHSIM_FKE_CHAN4 xor_struct).

  (* F_OAUTH[ F_AUTH [DH_KE [CHAN []]]] ≤ F_OAUTH[ F_AUTH [C[DH_real][CHAN []]]] *)
  (*---------------------------------------------------------------------------*)
  Lemma F_OAUTH_DHKE_C_REAL :
    ⊢ sem_val_typed REAL_CHAN_DHKE REAL_CHAN_DH_REAL τ.
  Proof using All.
    iApply func_comp_left.
    - apply F_AUTH_DHKE_closed.
    - apply F_AUTH_C_DDH_real_closed.
    - iIntros (θ). iApply parallel_comp_right.
      + unfold τ__F. unshelve iApply F_AUTH_DH_KE_FAUTH_C_DH_real; try done.
      + iApply F_OAUTH_typed.   (* F_OAUTH well-typed *)
    - iApply CHAN_typed.        (* CHAN well-typed *)
  Qed.

  Lemma C_REAL_DHKE_F_OAUTH :
     ⊢ sem_val_typed REAL_CHAN_DH_REAL REAL_CHAN_DHKE τ.
  Proof using All.
    iApply func_comp_left.
    - apply F_AUTH_C_DDH_real_closed.
    - apply F_AUTH_DHKE_closed.
    - iIntros (θ). iApply parallel_comp_right.
      + unfold τ__F. iApply F_AUTH_C_DH_real_FAUTH_DH_KE; try done.
      + iApply F_OAUTH_typed.   (* F_OAUTH well-typed *)
    - iApply CHAN_typed.        (* CHAN well-typed *)
  Qed.

  Lemma REAL_CHAN_DH_RAND_DHSIM_FKE_CHAN1 :
    ⊢ sem_val_typed REAL_CHAN_DH_RAND DHSIM_FKE_CHAN1 τ.
  Proof using All.
    iApply func_comp_left.
    - apply F_AUTH_C_DDH_rand_closed.
    - apply DHSIM_FKE_CHAN1_closed.
    - iIntros (θ). iApply parallel_comp_right.
      + iApply F_AUTH_C_DH_rand_FAUTH_DH_SIM_F_KE; try done.
      + iApply F_OAUTH_typed.
    - iApply CHAN_typed.
  Qed.

  Lemma DHSIM_FKE_CHAN1_REAL_CHAN_DH_RAND :
    ⊢ sem_val_typed DHSIM_FKE_CHAN1 REAL_CHAN_DH_RAND τ.
  Proof using All.
    iApply func_comp_left.
    - apply DHSIM_FKE_CHAN1_closed.
    - apply F_AUTH_C_DDH_rand_closed.
    - iIntros (θ). iApply parallel_comp_right.
      + iApply F_AUTH_DH_SIM_F_KE_FAUTH_C_DH_rand; try done.
      + iApply F_OAUTH_typed.
    - iApply CHAN_typed.
  Qed.

  Lemma DHSIM_FKE_CHAN1_DHSIM_FKE_CHAN2 :
    ⊢ sem_val_typed  DHSIM_FKE_CHAN1 DHSIM_FKE_CHAN2 τ.
  Proof using All.
    iApply func_comp_left.
    - apply DHSIM_FKE_CHAN1_closed.
    - apply DHSIM_FKE_CHAN2_closed.
    - iIntros (θ). iApply parallel_comp_right.
      + unfold τ__F. iApply func_comp_assoc.
        * iApply F_AUTH_typed.
        * iApply DH_SIM_typed.
        * iApply F_KE_lazy_alice_typed.
      + iApply F_OAUTH_typed.
    - iApply CHAN_typed.
  Qed.

  Lemma DHSIM_FKE_CHAN2_DHSIM_FKE_CHAN1 :
    ⊢ sem_val_typed DHSIM_FKE_CHAN2 DHSIM_FKE_CHAN1 τ.
  Proof using All.
    iApply func_comp_left.
    - apply DHSIM_FKE_CHAN2_closed.
    - apply DHSIM_FKE_CHAN1_closed.
    - iIntros (θ). iApply parallel_comp_right.
      + unfold τ__F. iApply func_comp_assoc_rev.
        * iApply F_AUTH_typed.
        * iApply DH_SIM_typed.
        * iApply F_KE_lazy_alice_typed.
      + iApply F_OAUTH_typed.
    - iApply CHAN_typed.
  Qed.

  Lemma DHSIM_FKE_CHAN2_DHSIM_FKE_CHAN3 :
    ⊢ sem_val_typed DHSIM_FKE_CHAN2 DHSIM_FKE_CHAN3 τ.
  Proof using All.
    iApply func_comp_left.
    - apply DHSIM_FKE_CHAN2_closed.
    - apply DHSIM_FKE_CHAN3_closed.
    - iIntros (θ). iApply func_comp_parallel_comp_assoc; try done.
      + iApply F_AUTH_DH_SIM_typed_val.
      + iApply F_KE_body_typed.
      + iApply F_OAUTH_typed.
    - iApply CHAN_typed.
  Qed.

  Lemma DHSIM_FKE_CHAN3_DHSIM_FKE_CHAN2 :
    ⊢ sem_val_typed DHSIM_FKE_CHAN3 DHSIM_FKE_CHAN2 τ.
  Proof using All.
    iApply func_comp_left.
    - apply DHSIM_FKE_CHAN3_closed.
    - apply DHSIM_FKE_CHAN2_closed.
    - iIntros (θ). iApply func_comp_parallel_comp_assoc_rev; try done.
      + iApply F_AUTH_DH_SIM_typed_val.
      + iApply F_KE_body_typed.
      + iApply F_OAUTH_typed.
    - iApply CHAN_typed.
  Qed.


  Lemma DHSIM_FKE_CHAN3_DHSIM_FKE_CHAN4 :
    ⊢ sem_val_typed DHSIM_FKE_CHAN3 DHSIM_FKE_CHAN4 τ.
  Proof using All.
    iApply functionality_comp_func_comp_assoc_curried; first done ; first done ; first done.
    - apply F_AUTH_DH_SIM_closed.
    - apply F_KE_lazy_alice_F_OAUTH_closed.
    - iApply F_AUTH_DH_SIM_typed.
    - iApply F_KE_F_OAUTH_typed.
    - iApply CHAN_body_typed.
  Qed.

  Lemma DHSIM_FKE_CHAN4_DHSIM_FKE_CHAN3 :
    ⊢ sem_val_typed DHSIM_FKE_CHAN4 DHSIM_FKE_CHAN3 τ.
  Proof using All.
    iApply functionality_comp_func_comp_assoc_rev_curried; first done.
    - apply F_AUTH_DH_SIM_closed.
    - apply F_KE_lazy_alice_F_OAUTH_closed.
    - iApply F_AUTH_DH_SIM_typed.
    - iApply F_KE_F_OAUTH_typed.
    - iApply CHAN_body_typed.
  Qed.

  Lemma DHSIM_FKE_CHAN4_SIMFCHAN :
    ⊢ sem_val_typed DHSIM_FKE_CHAN4 SIMSIMFCHAN τ.
  Proof using All.
    iApply functionality_comp_cong.
    - apply F_AUTH_DH_SIM_closed.
    - apply R_CHAN_closed.
    - apply CHAN_SIM_lazy_F_CHAN_closed.
    - unshelve iApply R_I_SCHAN; done.                    (* security of secure channel  *)
    - iApply F_AUTH_DH_SIM_typed.                         (* well-typedness *)
  Qed.

  Lemma SIMFCHAN_DHSIM_FKE_CHAN4 :
    ⊢ sem_val_typed SIMSIMFCHAN DHSIM_FKE_CHAN4 τ.
  Proof using All.
    iApply functionality_comp_cong.
    - apply F_AUTH_DH_SIM_closed.
    - apply CHAN_SIM_lazy_F_CHAN_closed.
    - apply R_CHAN_closed.
    - unshelve iApply I_R_SCHAN; done.                    (* security of secure channel *)
    - iApply F_AUTH_DH_SIM_typed.
  Qed.

End new_comp_verification.

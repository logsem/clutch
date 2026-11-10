(* Semantic typing of the MAC instances, of the protocol [AUTH_of M] and of
   the simulator [S_AUTH], in the style of [dhke_typing] / [sec_channel_typing]. *)

From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze.uc Require Import comp_operators.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory logic.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_row sem_sig sem_env sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze.examples.dhke Require Import dhke_def dhke_common.
From clutch.prob_eff_lang.probblaze.examples.auth Require Import auth_def.
From clutch.prob_eff_lang.probblaze.uc Require Import uc_systems.
From clutch.prob_eff_lang.probblaze.examples Require Export dhke_typing.

Import fingroup.
Import fingroup.fingroup.

Section auth_typing.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.

  Import valgroup_notation.
  Import typed_hint_modes.
  #[local] Existing Instance multi_ty_group.
  #[local] Notation n := (S n'').

  (* ------------------------------------------------------------------ *)
  (* Group operations.                                                   *)
  (* ------------------------------------------------------------------ *)

  (* [tag e1 e2 e3]: the arguments are evaluated right to left. *)
  Lemma sem_typed_tag Γ1 Γ2 Γ3 Γ4 ρ e1 e1' e2 e2' e3 e3' :
    ⊢ sem_typed Γ1 e3 e3' ρ 𝔾 Γ2 -∗ sem_typed Γ2 e2 e2' ρ ℕ Γ3 -∗ sem_typed Γ3 e1 e1' ρ ℕ Γ4 -∗
      sem_typed Γ1 (tag e1 e2 e3) (tag e1' e2' e3') ρ 𝔾 Γ4.
  Proof using G vgg.
    iIntros "#He3 #He2 #He1 !# %γ HΓ1 /=".
    iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
    iApply (brel_wand with "[HΓ1]"); first by iApply "He3".
    iIntros "!# % % ((%m & -> & ->) & HΓ2) /=".
    iApply (brel_bind [AppLCtx _; AppRCtx _] [AppLCtx _; AppRCtx _]); [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
    iApply (brel_wand with "[HΓ2]"); first by iApply "He2".
    iIntros "!# % % ((%k2 & -> & ->) & HΓ3) /=".
    iApply (brel_bind [AppLCtx _; AppLCtx _; AppRCtx _] [AppLCtx _; AppLCtx _; AppRCtx _]); [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
    iApply (brel_wand with "[HΓ3]"); first by iApply "He1".
    iIntros "!# % % ((%k1 & -> & ->) & HΓ4) /=".
    rewrite /tag. brel_pures_l. brel_pures_r.
    iApply (brel_exp_l [AppRCtx _]). iApply (brel_exp_r [AppRCtx _]).
    iApply (brel_exp_l [AppLCtx _; AppRCtx _]). iApply (brel_exp_r [AppLCtx _; AppRCtx _]).
    iApply (brel_mult_l []). iApply (brel_mult_r []).
    iApply brel_value. iIntros "$ !>". iFrame. by iExists _.
  Qed.

  Lemma sem_typed_vinv_gen Γ1 Γ2 e e' ρ :
    ⊢ sem_typed Γ1 e e' ρ 𝔾 Γ2 -∗ sem_typed Γ1 (vinv e) (vinv e') ρ 𝔾 Γ2.
  Proof using G vgg.
    iIntros "#He !# %γ HΓ1 /=".
    iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
    iApply (brel_wand with "[HΓ1]"); first by iApply "He".
    iIntros "!# % % ((%b & -> & ->) & HΓ2) /=".
    iApply (brel_inv_l []). iApply (brel_inv_r []).
    iApply brel_value. iIntros "$ !>". iFrame. by iExists _.
  Qed.

  (* [g ^ e] *)
  Lemma sem_typed_gexp Γ1 Γ2 e e' ρ :
    ⊢ sem_typed Γ1 e e' ρ ℕ Γ2 -∗ sem_typed Γ1 (vexp g e) (vexp g e') ρ 𝔾 Γ2.
  Proof using G vgg.
    iIntros "#He". iApply (sem_typed_vexp_gen with "He"). iApply sem_typed_vgval.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Interface types.                                                    *)
  (* ------------------------------------------------------------------ *)

  (* A one-time MAC instance: [tag] and [verify]. *)
  Definition tagT : sem_ty Σ := (𝔾 -{ ⟨⟩ }-> Option 𝔾)%T.
  Definition verifyT : sem_ty Σ := ((𝔾 × 𝔾) -{ ⟨⟩ }-> 𝔹)%T.
  Definition MACT : sem_ty Σ := (tagT × verifyT)%T.

  (* The raw network: tagged messages go out, tagged messages (chosen by the
     environment) come in. *)
  Definition raw (θ : sem_row Σ) : sem_ty Σ :=
    ((((𝔾 × 𝔾) × (𝟙 + 𝟙)) -{ θ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ }-> Option (𝔾 × 𝔾)))%T.

  (* ------------------------------------------------------------------ *)
  (* The MAC instances.                                                  *)
  (* ------------------------------------------------------------------ *)

  (* Two tape reads, in either MAC. *)
  Lemma sem_typed_sample2 (α β : string) e e' Γ ρ τ `{!MultiE Γ} :
    "k1" ∉ env_dom Γ → "k2" ∉ env_dom Γ →
    ⊢ sem_typed Γ α α ρ sem_ty_tape Γ -∗
      sem_typed Γ β β ρ sem_ty_tape Γ -∗
      sem_typed (("k2", ℕ) :: ("k1", ℕ) :: Γ) e e' ρ τ Γ -∗
      sem_typed Γ (let: "k1" := rand(α) #n in let: "k2" := rand(β) #n in e)
                  (let: "k1" := rand(α) #n in let: "k2" := rand(β) #n in e') ρ τ Γ.
  Proof using All.
    iIntros (??) "#Hα #Hβ #He".
    iApplyT sem_typed_let; first (iApplyT sem_typed_rand; [iApply "Hα"|iApplyT sem_typed_int']).
    iApplyT sem_typed_let.
    { iApplyT sem_typed_rand; last iApplyT sem_typed_int'.
      iApply (sem_typed_frame_env_gen _ [_]). iApply "Hβ". }
    iApply "He".
    Unshelve. all: try solve_typed_side.
    rewrite env_dom_app env_dom_cons /=. apply not_elem_of_cons. by split.
  Qed.

  Definition mac_key_env : env Σ :=
    [("key", Refᶜ (Option (ℕ × ℕ))); ("β", sem_ty_tape); ("α", sem_ty_tape)].

  (* A leaf of a typing derivation that returns a copyable variable, in a
     scope that ends with the empty environment. *)
  Ltac tleaf := iApplyT sem_typed_sub_env_final; first iApply env_le_nil.
  (* [match] whose branches end with the empty environment. *)
  Ltac tmatch0 := iApplyT (sem_typed_match_split [] [] _ _ _ _ _ _ _ [] _ []).

  Lemma mac_getkey_typed :
    ⊢ sem_typed mac_key_env
        (λ: <>, match: !"key" with
                  NONE => let: "k1" := rand("α") #n in let: "k2" := rand("β") #n in
                          "key" <- SOME ("k1", "k2");; ("k1", "k2")
                | SOME "k" => "k" end)
        (λ: <>, match: !"key" with
                  NONE => let: "k1" := rand("α") #n in let: "k2" := rand("β") #n in
                          "key" <- SOME ("k1", "k2");; ("k1", "k2")
                | SOME "k" => "k" end)
        ⟨⟩ (𝟙 -{ ⟨⟩ }-> (ℕ × ℕ)) [].
  Proof using All.
    rewrite /mac_key_env.
    iApply (sem_typed_oval _ [_; _; _]). iApplyT sem_oval_typed_ufun. simpl.
    tmatch0.
    - iApplyT sem_typed_load_cpy. tvar_copy.
    - iApply env_le_refl.
    - tleaf. iApply (sem_typed_sample2 "α" "β"); [solve_env_dom|solve_env_dom|tvar_copy|tvar_copy|].
      iApplyT sem_typed_seq.
      { iApplyT sem_typed_store_cpy_gen; last (iApplyT sem_typed_injr; iApplyT sem_typed_pair; tvar_copy).
        tvar_copy. }
      iApplyT sem_typed_sub_env_final; last (iApplyT sem_typed_pair; tvar_copy). env_solve16.
    - iApply env_le_nil.
    - iApply env_le_refl.
    - tleaf. tvar.
    - iApply env_le_nil.
      Unshelve. all: solve_typed_side.
  Qed.

  Lemma MAC_typed : ⊢ ⊨ᵥ MAC ≤ MAC : fac MS MACT.
  Proof using All.
    iApply fac_closure.
    do 2 (iApplyT sem_typed_let; first (iApplyT sem_typed_alloctape; iApplyT sem_typed_int')).
    iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_none).
    iApplyT sem_typed_let.
    { iApply sem_typed_sub_nil. simpl. iApply mac_getkey_typed. }
    iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_bool').
    iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_none).
    iApply sem_typed_sub_nil.
    iApplyT sem_typed_pair.
    - (* verify *)
      iApplyT (sem_typed_sub_env _ ([("getkey", (𝟙 -{ ⟨⟩ }-> (ℕ × ℕ))%T); ("tagged", Refᶜ 𝔹)] ++
                                    [("getkey", (𝟙 -{ ⟨⟩ }-> (ℕ × ℕ))%T); ("verdict", Refᶜ (Option 𝔹))]));
        first (simpl; env_solve16).
      iApply (sem_typed_frame_env_gen _ [_; _]).
      iApply (sem_typed_oval _ [_; _]).
      iApplyT sem_oval_typed_ufun. simpl.
      tmatch0.
      + iApplyT sem_typed_load_cpy. tvar_copy.
      + iApply env_le_refl.
      + iApplyT sem_typed_pair_elim; first tvar.
        iApplyT sem_typed_pair_elim;
          first (iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_unit'|tufun]).
        iApplyT sem_typed_let.
        { iApplyT sem_typed_veq_gen; [iApplyT sem_typed_tag; tvar_copy|tvar_copy]. }
        iApplyT sem_typed_seq.
        { iApplyT sem_typed_store_cpy_gen; last (iApplyT sem_typed_injr; tvar_copy). tvar_copy. }
        tleaf. tvar_copy.
      + iApply env_le_nil.
      + iApply env_le_refl.
      + tleaf. tvar.
      + iApply env_le_nil.
    - (* tag *)
      iApplyT (sem_typed_sub_env _ [("getkey", (𝟙 -{ ⟨⟩ }-> (ℕ × ℕ))%T); ("tagged", Refᶜ 𝔹)]);
        first (simpl; env_solve16).
      iApply (sem_typed_oval _ [_; _]).
      iApplyT sem_oval_typed_ufun. simpl.
      iApplyT sem_typed_if; first (iApplyT sem_typed_load_cpy; tvar_copy).
      + tleaf. iApplyT sem_typed_none.
      + iApplyT sem_typed_seq.
        { iApplyT sem_typed_store_cpy_gen; last iApplyT sem_typed_bool'. tvar_copy. }
        iApplyT sem_typed_pair_elim;
          first (iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_unit'|tufun]).
        tleaf. iApplyT sem_typed_injr. iApplyT sem_typed_tag; tvar_copy.
        Unshelve. all: solve_typed_side.
  Qed.

  (* The tag of [MAC_pad] and [MAC_ideal]. *)
  Definition mac_pad_tag : expr :=
    (λ: "m",
       match: !"tg" with
         SOME <> => NONEV
       | NONE =>
           let: "t" := match: !"key" with
                         SOME "k" => let, ("k1", "k2") := "k" in tag "k1" "k2" "m"
                       | NONE => g ^ (rand("β") #n)
                       end in
           "tg" <- SOME ("m", "t");; SOME "t"
       end)%E.

  Definition mac_pad_env : env Σ :=
    [("verdict", Refᶜ (Option 𝔹)); ("tg", Refᶜ (Option (𝔾 × 𝔾)));
     ("key", Refᶜ (Option (ℕ × ℕ))); ("β", sem_ty_tape); ("α", sem_ty_tape)].

  Definition mac_pad_env_m : env Σ := ("m", 𝔾) :: mac_pad_env.

  Lemma mac_pad_tag_typed :
    ⊢ sem_typed mac_pad_env mac_pad_tag mac_pad_tag ⟨⟩ (𝔾 -{ ⟨⟩ }-> Option 𝔾) [].
  Proof using All.
    rewrite /mac_pad_env /mac_pad_tag.
    iApply (sem_typed_oval _ [_; _; _; _; _]). iApplyT sem_oval_typed_ufun. simpl.
    tmatch0.
    - iApplyT sem_typed_load_cpy. tvar_copy.
    - iApply env_le_refl.
    - iApplyT sem_typed_let.
      { simpl. rewrite -/mac_pad_env -/mac_pad_env_m.
        iApplyT (sem_typed_match_split [] [] _ _ _ _ _ _ _ mac_pad_env_m _ mac_pad_env_m).
        + iApplyT sem_typed_load_cpy. rewrite /mac_pad_env_m /mac_pad_env. tvar_copy.
        + iApply env_le_refl.
        + rewrite /mac_pad_env_m /mac_pad_env.
          iApplyT sem_typed_gexp. iApplyT sem_typed_rand; [tvar_copy|iApplyT sem_typed_int'].
        + iApply env_le_refl.
        + iApply env_le_refl.
        + iApplyT sem_typed_pair_elim; first tvar.
          rewrite /mac_pad_env_m /mac_pad_env.
          iApplyT sem_typed_sub_env_final; last (iApplyT sem_typed_tag; tvar_copy). env_solve16.
        + iApply env_le_refl. }
      rewrite /mac_pad_env_m /mac_pad_env.
      iApplyT sem_typed_seq.
      { iApplyT sem_typed_store_cpy_gen; last (iApplyT sem_typed_injr; iApplyT sem_typed_pair; tvar_copy).
        tvar_copy. }
      tleaf. iApplyT sem_typed_injr. tvar_copy.
    - iApply env_le_nil.
    - iApply env_le_refl.
    - tleaf. iApplyT sem_typed_none.
    - iApply env_le_nil.
      Unshelve. all: solve_typed_side.
  Qed.

  (* The verdict of [MAC_pad] and [MAC_ideal], under the common wrapper. *)
  Lemma mac_pad_verify_typed (b : expr) :
    ⊢ sem_typed (("m'", 𝔾) :: ("t'", 𝔾) :: mac_pad_env) b b ⟨⟩ 𝔹 (("m'", 𝔾) :: ("t'", 𝔾) :: mac_pad_env) -∗
      sem_typed mac_pad_env
        (λ: "p", match: !"verdict" with
                   SOME "b" => "b"
                 | NONE => let, ("m'", "t'") := "p" in
                           let: "b" := b in "verdict" <- SOME "b";; "b"
                 end)
        (λ: "p", match: !"verdict" with
                   SOME "b" => "b"
                 | NONE => let, ("m'", "t'") := "p" in
                           let: "b" := b in "verdict" <- SOME "b";; "b"
                 end)
        ⟨⟩ ((𝔾 × 𝔾) -{ ⟨⟩ }-> 𝔹) [].
  Proof using All.
    iIntros "#Hb". rewrite /mac_pad_env.
    iApply (sem_typed_oval _ [_; _; _; _; _]). iApplyT sem_oval_typed_ufun. simpl.
    tmatch0.
    - iApplyT sem_typed_load_cpy. tvar_copy.
    - iApply env_le_refl.
    - iApplyT sem_typed_pair_elim; first tvar.
      iApplyT sem_typed_let; first (simpl; iApply "Hb").
      iApplyT sem_typed_seq.
      { iApplyT sem_typed_store_cpy_gen; last (iApplyT sem_typed_injr; tvar_copy). tvar_copy. }
      tleaf. tvar_copy.
    - iApply env_le_nil.
    - iApply env_le_refl.
    - tleaf. tvar.
    - iApply env_le_nil.
      Unshelve. all: solve_typed_side.
  Qed.

  Lemma mac_pad_setup_typed (verify : expr) :
    ⊢ sem_typed mac_pad_env verify verify ⟨⟩ ((𝔾 × 𝔾) -{ ⟨⟩ }-> 𝔹) [] -∗
      ⊨ᵥ (λ: <>,
            let: "α" := alloc #n in let: "β" := alloc #n in
            let: "key" := ref NONEV in
            let: "tg" := ref NONEV in
            let: "verdict" := ref NONEV in
            (mac_pad_tag, verify))%V
        ≤ (λ: <>,
            let: "α" := alloc #n in let: "β" := alloc #n in
            let: "key" := ref NONEV in
            let: "tg" := ref NONEV in
            let: "verdict" := ref NONEV in
            (mac_pad_tag, verify))%V : fac MS MACT.
  Proof using All.
    iIntros "#Hv".
    iApply fac_closure.
    do 2 (iApplyT sem_typed_let; first (iApplyT sem_typed_alloctape; iApplyT sem_typed_int')).
    do 3 (iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_none)).
    iApply sem_typed_sub_nil. simpl.
    iApplyT sem_typed_pair.
    - iApplyT (sem_typed_sub_env _ (mac_pad_env ++ mac_pad_env)); first (rewrite /mac_pad_env; env_solve16).
      iApply (sem_typed_frame_env_gen _ mac_pad_env). iApply "Hv".
    - rewrite app_nil_r. iApply mac_pad_tag_typed.
      Unshelve. all: solve_typed_side.
  Qed.

  (* The verdict computations, at the environment of the wrapper. *)
  Definition mac_verdict_env : env Σ := ("m'", 𝔾) :: ("t'", 𝔾) :: mac_pad_env.

  Lemma MAC_pad_typed : ⊢ ⊨ᵥ MAC_pad ≤ MAC_pad : fac MS MACT.
  Proof using All.
    iApply mac_pad_setup_typed. iApply mac_pad_verify_typed.
    rewrite -/mac_verdict_env.
    iApplyT (sem_typed_match_split [] [] _ _ _ _ _ _ _ mac_verdict_env _ mac_verdict_env).
    - iApplyT sem_typed_load_cpy. rewrite /mac_verdict_env /mac_pad_env. tvar_copy.
    - iApply env_le_refl.
    - rewrite /mac_verdict_env /mac_pad_env.
      iApply (sem_typed_sample2 "α" "β"); [solve_env_dom|solve_env_dom|tvar_copy|tvar_copy|].
      iApplyT sem_typed_seq.
      { iApplyT sem_typed_store_cpy_gen; last (iApplyT sem_typed_injr; iApplyT sem_typed_pair; tvar_copy).
        tvar_copy. }
      iApplyT sem_typed_sub_env_final;
        last (iApplyT sem_typed_veq_gen; [iApplyT sem_typed_tag; tvar_copy|tvar_copy]).
      env_solve16.
    - iApply env_le_refl.
    - iApply env_le_refl.
    - iApplyT sem_typed_pair_elim; first tvar.
      rewrite /mac_verdict_env /mac_pad_env.
      iApplyT sem_typed_if; first (iApplyT sem_typed_veq_gen; tvar_copy).
      + iApplyT sem_typed_sub_env_final; last (iApplyT sem_typed_veq_gen; tvar_copy). env_solve16.
      + iApplyT sem_typed_let; first (iApplyT sem_typed_rand; [tvar_copy|iApplyT sem_typed_int']).
        iApplyT sem_typed_sub_env_final; last first.
        { iApplyT sem_typed_veq_gen.
          - iApplyT sem_typed_vmult_gen.
            + iApplyT sem_typed_vexp_gen; first tvar_copy.
              iApplyT sem_typed_vmult_gen; first (iApplyT sem_typed_vinv_gen; tvar_copy).
              tvar_copy.
            + tvar_copy.
          - tvar_copy. }
        env_solve16.
    - iApply env_le_refl.
      Unshelve. all: solve_typed_side.
  Qed.

  Lemma MAC_ideal_typed : ⊢ ⊨ᵥ MAC_ideal ≤ MAC_ideal : fac MS MACT.
  Proof using All.
    iApply mac_pad_setup_typed. iApply mac_pad_verify_typed.
    rewrite -/mac_verdict_env.
    iApplyT (sem_typed_match_split [] [] _ _ _ _ _ _ _ mac_verdict_env _ mac_verdict_env).
    - iApplyT sem_typed_load_cpy. rewrite /mac_verdict_env /mac_pad_env. tvar_copy.
    - iApply env_le_refl.
    - rewrite /mac_verdict_env /mac_pad_env.
      iApply (sem_typed_sample2 "α" "β"); [solve_env_dom|solve_env_dom|tvar_copy|tvar_copy|].
      iApplyT sem_typed_seq.
      { iApplyT sem_typed_store_cpy_gen; last (iApplyT sem_typed_injr; iApplyT sem_typed_pair; tvar_copy).
        tvar_copy. }
      iApplyT sem_typed_sub_env_final; last iApplyT sem_typed_bool'. env_solve16.
    - iApply env_le_refl.
    - iApply env_le_refl.
    - iApplyT sem_typed_pair_elim; first tvar.
      rewrite /mac_verdict_env /mac_pad_env.
      iApplyT sem_typed_if; first (iApplyT sem_typed_veq_gen; tvar_copy).
      + iApplyT sem_typed_sub_env_final; last (iApplyT sem_typed_veq_gen; tvar_copy). env_solve16.
      + iApplyT sem_typed_sub_env_final; last iApplyT sem_typed_bool'. env_solve16.
    - iApply env_le_refl.
      Unshelve. all: solve_typed_side.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* The protocol.                                                       *)
  (* ------------------------------------------------------------------ *)

  (* What the send handler captures. *)
  Definition auth_send_env (θ : sem_row Σ) : env Σ :=
    [("maca", MACT); ("macb", MACT);
     ("doLeakSend", (((𝔾 × 𝔾) × (𝟙 + 𝟙)) -{ θ }-> 𝟙)%T)].

  (* What the receive handler captures. *)
  Definition auth_recv_env (θ : sem_row Σ) : env Σ :=
    [("maca", MACT); ("macb", MACT);
     ("dec1", Refᶜ 𝔹); ("dec2", Refᶜ 𝔹);
     ("res1", Refᶜ (Option 𝔾)); ("res2", Refᶜ (Option 𝔾));
     ("doLeakRecv", ((𝟙 + 𝟙) -{ θ }-> Option (𝔾 × 𝔾))%T)].

  Definition auth_send_body : expr := auth_send_h "maca" "macb".
  Definition auth_recv_body : expr := auth_recv_h "maca" "macb" "dec1" "dec2" "res1" "res2".

  (* Selecting one of two copyable entries by a sum. *)
  Lemma sem_typed_select (x a b : string) τ Γ ρ `{!MultiT τ} :
    ⊢ sem_typed Γ x x ρ (𝟙 + 𝟙)%T Γ -∗
      sem_typed Γ a a ρ τ Γ -∗ sem_typed Γ b b ρ τ Γ -∗
      sem_typed Γ (match: x with InjL <> => a | InjR <> => b end)
                  (match: x with InjL <> => a | InjR <> => b end) ρ τ Γ.
  Proof using All.
    iIntros "#Hx #Ha #Hb".
    iApplyT (sem_typed_match_split [] []);
      [iApply "Hx"|iApply env_le_refl|iApply "Ha"|iApply env_le_refl
      |iApply env_le_refl|iApply "Hb"|iApply env_le_refl].
    Unshelve. all: solve_typed_side.
  Qed.

  Lemma auth_send_handler_typed (θ ρh : sem_row Σ) :
    ⊢ (¡ θ)%R ≤ᵣ ρh -∗
    sem_typed (("message", (𝔾 × (𝟙 + 𝟙))%T) :: ("k", (𝟙 -{ ρh }-[OS]-> 𝟙)%T) :: auth_send_env θ)
      auth_send_body auth_send_body ρh 𝟙 (auth_send_env θ).
  Proof using All.
    iIntros "#Hρ". rewrite /auth_send_env /auth_send_body /auth_send_h.
    iApplyT sem_typed_pair_elim; first tvar.
    iApplyT sem_typed_let; first (iApplyT sem_typed_select; tvar_copy).
    simpl.
    iApplyT sem_typed_seq.
    { set (Γ0 := [("mac", MACT); ("m", 𝔾); ("dst", (𝟙 + 𝟙)%T); ("k", (𝟙 -{ ρh }-[OS]-> 𝟙)%T);
                  ("maca", MACT); ("macb", MACT); ("doLeakSend", (((𝔾 × 𝔾) × (𝟙 + 𝟙)) -{ θ }-> 𝟙)%T)]).
      iApplyT (sem_typed_match_split [] [] _ _ _ _ _ _ _ Γ0 _ Γ0 Γ0); rewrite /Γ0.
      - iApplyT sem_typed_app_fun_nil; first iApply row_le_nil; first tvar_copy.
        iApplyT sem_typed_sub_ty; first iApply ty_le_u2aarr.
        iApplyT (sem_typed_fst_gen (𝔾 -{ ⟨⟩ }-> Option 𝔾)%T ((𝔾 × 𝔾) -{ ⟨⟩ }-> 𝔹)%T). tvar_copy.
      - iApply env_le_refl.
      - iApplyT sem_typed_unit'.
      - iApply env_le_refl.
      - iApply env_le_refl.
      - iApplyT sem_typed_sub_env_final; last first.
        { iApplyT sem_typed_app_fun_nil; first iApply "Hρ".
          + iApplyT sem_typed_pair; first tvar_copy. iApplyT sem_typed_pair; tvar_copy.
          + tleak_fun. }
        env_solve16.
      - iApply env_le_refl. }
    iApplyT sem_typed_sub_env_final.
    2: { iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_unit'|tcont]. }
    env_solve16.
    Unshelve. all: solve_typed_side.
  Qed.

  Lemma auth_recv_handler_typed (θ ρh : sem_row Σ) :
    ⊢ (¡ θ)%R ≤ᵣ ρh -∗
    sem_typed (("from", (𝟙 + 𝟙)%T) :: ("k", (Option 𝔾 -{ ρh }-[OS]-> 𝟙)%T) :: auth_recv_env θ)
      auth_recv_body auth_recv_body ρh 𝟙 (auth_recv_env θ).
  Proof using All.
    iIntros "#Hρ". rewrite /auth_recv_env /auth_recv_body /auth_recv_h.
    do 3 (iApplyT sem_typed_let; first (iApplyT sem_typed_select; tvar_copy)).
    simpl.
    set (Γ0 := [("res", Refᶜ (Option 𝔾)); ("dec", Refᶜ 𝔹); ("mac", MACT); ("from", (𝟙 + 𝟙)%T);
                ("maca", MACT); ("macb", MACT); ("dec1", Refᶜ 𝔹); ("dec2", Refᶜ 𝔹);
                ("res1", Refᶜ (Option 𝔾)); ("res2", Refᶜ (Option 𝔾));
                ("doLeakRecv", ((𝟙 + 𝟙) -{ θ }-> Option (𝔾 × 𝔾))%T)]).
    iApplyT (sem_typed_sub_env_final _ _ Γ0); first (rewrite /Γ0; env_solve16).
    iApplyT sem_typed_if.
    { iApplyT sem_typed_load_cpy. tvar_copy. }
    - (* already decided *)
      rewrite /Γ0.
      iApplyT sem_typed_app_fun_nil; first iApply row_le_refl.
      + iApplyT sem_typed_load_cpy. tvar_copy.
      + tcont.
    - iApplyT (sem_typed_match_split [] [] _ _ _ _ _ _ _ Γ0 _ Γ0 Γ0); rewrite /Γ0.
      + iApplyT sem_typed_app_fun_nil; [iApply "Hρ"|tvar_copy|tleak_fun].
      + iApply env_le_refl.
      + iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_none|tcont].
      + iApply env_le_refl.
      + iApply env_le_refl.
      + iApplyT sem_typed_if; first (iApplyT sem_typed_load_cpy; tvar_copy).
        { iApplyT sem_typed_sub_env_final; last first.
          { iApplyT sem_typed_app_fun_nil; first iApply row_le_refl.
            - iApplyT sem_typed_load_cpy. tvar_copy.
            - tcont. }
          env_solve16. }
        iApplyT sem_typed_pair_elim; first tvar.
        iApplyT sem_typed_let.
        { iApplyT sem_typed_if.
          - iApplyT sem_typed_app_fun_nil; first iApply row_le_nil.
            + iApplyT sem_typed_pair; tvar_copy.
            + iApplyT sem_typed_sub_ty; first iApply ty_le_u2aarr.
              iApplyT (sem_typed_snd_gen tagT verifyT). tvar_copy.
          - iApplyT sem_typed_injr. tvar_copy.
          - iApplyT sem_typed_none. }
        iApplyT sem_typed_seq.
        { iApplyT sem_typed_store_cpy_gen. 2: iApplyT sem_typed_bool'. tvar_copy. }
        iApplyT sem_typed_seq.
        { iApplyT sem_typed_store_cpy_gen. 2: tvar_copy. tvar_copy. }
        iApplyT sem_typed_sub_env_final; last first.
        { iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|tvar|tcont]. }
        env_solve16.
      + iApply env_le_refl.
      Unshelve. all: solve_typed_side.
  Qed.

  (* The session, over two MAC instances and the receivers' state. *)
  Lemma auth_sess_typed :
    ⊢ sem_typed [("maca", MACT); ("macb", MACT); ("dec1", Refᶜ 𝔹); ("dec2", Refᶜ 𝔹);
                 ("res1", Refᶜ (Option 𝔾)); ("res2", Refᶜ (Option 𝔾))]
        (auth_sess "maca" "macb" "dec1" "dec2" "res1" "res2")
        (auth_sess "maca" "macb" "dec1" "dec2" "res1" "res2") ⟨⟩ (τ__F raw chan) [].
  Proof using All.
    rewrite /auth_sess /auth_skel /auth_skel'.
    iApply (sem_typed_oval _ [_; _; _; _; _; _]).
    iApply sem_typed_RLam. iIntros (θ).
    (* the client-taking closure captures only copyable state *)
    iApplyT sem_oval_typed_ufun.
    iApply (sem_typed_oval _ [_; _; _; _; _; _; _]). iApply sem_typed_RLam. iIntros (θ₂).
    iApplyT sem_oval_typed_afun. simpl.
    iApplyT sem_typed_pair_elim; first tvar.
    iApply sem_typed_effect_gen. iIntros (ls1 ls2).
    iApply sem_typed_effect_gen. iIntros (lr1 lr2). simpl.
    iApplyT sem_typed_let.
    { iApply sem_typed_sub_nil. iApply (sem_typed_oval _ []).
      iApplyT sem_oval_typed_ufun.
      iApply (sem_typed_do_const OS _ (ls1, ls2) (𝔾 × (𝟙 + 𝟙))%T 𝟙%T).
      iApply sem_typed_sub_nil. iApply sem_typed_var. }
    iApplyT sem_typed_let.
    { iApply sem_typed_sub_nil. iApply (sem_typed_oval _ []).
      iApplyT sem_oval_typed_ufun.
      iApplyT sem_typed_sub_row; first iApply row_le_cons_extend.
      iApply (sem_typed_do_const OS ⟨⟩%R (lr1, lr2) (𝟙 + 𝟙)%T (Option 𝔾)%T).
      iApply sem_typed_sub_nil. iApply sem_typed_var. }
    iApplyT sem_typed_sub_env_final; first iApply env_le_nil.
    iApplyT (sem_typed_sub_env _ (([("doRecv", _); ("doSend", _); ("f", _)] ++ auth_send_env θ₂)
                                    ++ auth_recv_env θ₂)).
    { rewrite /auth_send_env /auth_recv_env. simpl. env_solve16. }
    (* Outer handler: recv. *)
    iApplyT (sem_typed_deep_handler_OS (lr1, lr2) (λ _, 𝟙 + 𝟙)%T (λ _, Option 𝔾)%T).
    - (* Inner handler: send. *)
      iApplyT sem_typed_sub_row; first iApply row_le_swap_second.
      iApplyT (sem_typed_sub_env _ ([_; _; _] ++ auth_send_env θ₂)); first iApply env_le_refl.
      iApplyT (sem_typed_deep_handler_OS (ls1, ls2) (λ _, 𝔾 × (𝟙 + 𝟙))%T (λ _, 𝟙)%T).
      + (* the client call [f (doASend, doARecv)] *)
        iApplyT sem_typed_app_fun_nil.
        2: { iApplyT sem_typed_pair; tvar. }
        2: { iApplyT sem_typed_sub_ty; last tvar. iApply ty_le_row_forall_inst. }
        iApply row_le_trans; first iApplyT row_le_union'.
        * iApply row_le_mfbang_elim.
        * iApply row_le_refl.
        * row_le_submseteq.
      + iIntros (?). iApply auth_send_handler_typed; row_le_submseteq.
      + iApplyT sem_typed_sub_env_final; last iApplyT sem_typed_unit'. rewrite /auth_send_env. env_solve16.
    - iIntros (?). iApply auth_recv_handler_typed; row_le_submseteq.
    - iApplyT sem_typed_sub_env_final; last iApplyT sem_typed_unit'. rewrite /auth_recv_env. env_solve16.
      Unshelve. all: solve_typed_side.
  Qed.

  (* The protocol over any two related MAC instances, at any mode. *)
  Lemma AUTH_of_typed (M M' : val) (m : mode) :
    ⊢ ⊨ᵥ M ≤ M' : fac MS MACT -∗ ⊨ᵥ AUTH_of M ≤ AUTH_of M' : fac m (τ__F raw chan).
  Proof using All.
    iIntros "#HM". rewrite /AUTH_of.
    iApply fac_closure.
    do 2 (iApplyT sem_typed_let; first (iApply sem_typed_fac_call; iApply sem_typed_val; iApply "HM")).
    do 2 (iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_bool')).
    do 2 (iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_none)).
    iApply sem_typed_sub_nil.
    iApplyT (sem_typed_sub_env _ [("maca", MACT); ("macb", MACT); ("dec1", Refᶜ 𝔹); ("dec2", Refᶜ 𝔹);
                                  ("res1", Refᶜ (Option 𝔾)); ("res2", Refᶜ (Option 𝔾))]);
      first (simpl; env_solve16).
    iApply auth_sess_typed.
    Unshelve. all: solve_typed_side.
  Qed.

  Lemma AUTH_typed m : ⊢ ⊨ᵥ AUTH ≤ AUTH : fac m (τ__F raw chan).
  Proof using All. iApply AUTH_of_typed. iApply MAC_typed. Qed.

  (* ------------------------------------------------------------------ *)
  (* The simulator.                                                      *)
  (* ------------------------------------------------------------------ *)

  (* What the two port closures of the simulator capture. *)
  Definition sauth_env (θ : sem_row Σ) : env Σ :=
    [("doSend", (((𝔾 × 𝔾) × (𝟙 + 𝟙)) -{ θ }-> 𝟙)%T);
     ("doRecv", ((𝟙 + 𝟙) -{ θ }-> Option (𝔾 × 𝔾))%T);
     ("maca", MACT); ("macb", MACT);
     ("dec1", Refᶜ 𝔹); ("dec2", Refᶜ 𝔹); ("acc1", Refᶜ 𝔹); ("acc2", Refᶜ 𝔹)].

  Definition sauth_send_body : expr := sauth_send_b "maca" "macb" "doSend".
  Definition sauth_recv_body : expr :=
    sauth_recv_b "maca" "macb" "dec1" "dec2" "acc1" "acc2" "doRecv".

  Lemma sauth_send_body_typed (θ : sem_row Σ) :
    ⊢ sem_typed (("payload", (𝔾 × (𝟙 + 𝟙))%T) :: sauth_env θ) sauth_send_body sauth_send_body θ 𝟙 [].
  Proof using All.
    rewrite /sauth_env /sauth_send_body /sauth_send_b.
    iApplyT sem_typed_pair_elim; first tvar.
    iApplyT sem_typed_let; first (iApplyT sem_typed_select; tvar_copy).
    iApplyT (sem_typed_match_split [] []).
    - iApplyT sem_typed_app_fun_nil; first iApply row_le_nil; first tvar_copy.
      iApplyT sem_typed_sub_ty; first iApply ty_le_u2aarr.
      iApplyT (sem_typed_fst_gen tagT verifyT). tvar_copy.
    - iApply env_le_refl.
    - iApplyT sem_typed_sub_env_final; first iApply env_le_nil. iApplyT sem_typed_unit'.
    - iApply env_le_nil.
    - iApply env_le_refl.
    - iApplyT sem_typed_sub_env_final; first iApply env_le_nil.
      iApplyT sem_typed_app_fun_nil; first iApply row_le_refl.
      + iApplyT sem_typed_pair; first tvar_copy. iApplyT sem_typed_pair; tvar_copy.
      + tufun.
    - iApply env_le_nil.
      Unshelve. all: solve_typed_side.
  Qed.

  Lemma sauth_recv_body_typed (θ : sem_row Σ) :
    ⊢ sem_typed (("from", (𝟙 + 𝟙)%T) :: sauth_env θ) sauth_recv_body sauth_recv_body θ (Option ℕ) [].
  Proof using All.
    rewrite /sauth_env /sauth_recv_body /sauth_recv_b.
    do 3 (iApplyT sem_typed_let; first (iApplyT sem_typed_select; tvar_copy)).
    iApplyT sem_typed_if.
    { iApplyT sem_typed_load_cpy. tvar_copy. }
    - iApplyT sem_typed_sub_env_final; first iApply env_le_nil.
      iApplyT sem_typed_if.
      { iApplyT sem_typed_load_cpy. tvar_copy. }
      + iApplyT sem_typed_injr. iApply sem_typed_nat'.
      + iApplyT sem_typed_none.
    - iApplyT (sem_typed_match_split [] []).
      + iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|tvar_copy|tufun].
      + iApply env_le_refl.
      + iApplyT sem_typed_sub_env_final; first iApply env_le_nil. iApplyT sem_typed_none.
      + iApply env_le_nil.
      + iApply env_le_refl.
      + iApplyT sem_typed_if; first (iApplyT sem_typed_load_cpy; tvar_copy).
        { iApplyT sem_typed_sub_env_final; first iApply env_le_nil.
          iApplyT sem_typed_if; first (iApplyT sem_typed_load_cpy; tvar_copy).
          - iApplyT sem_typed_injr. iApply sem_typed_nat'.
          - iApplyT sem_typed_none. }
        iApplyT sem_typed_let.
        { iApplyT sem_typed_app_fun_nil; first iApply row_le_nil; first tvar_copy.
          iApplyT sem_typed_sub_ty; first iApply ty_le_u2aarr.
          iApplyT (sem_typed_snd_gen tagT verifyT). tvar_copy. }
        iApplyT sem_typed_seq.
        { iApplyT sem_typed_store_cpy_gen. 2: iApplyT sem_typed_bool'. tvar_copy. }
        iApplyT sem_typed_seq.
        { iApplyT sem_typed_store_cpy_gen. 2: tvar_copy. tvar_copy. }
        iApplyT sem_typed_sub_env_final; first iApply env_le_nil.
        iApplyT sem_typed_if; first tvar_copy.
        * iApplyT sem_typed_injr. iApply sem_typed_nat'.
        * iApplyT sem_typed_none.
      + iApply env_le_nil.
      Unshelve. all: solve_typed_side.
  Qed.

  Lemma S_AUTH_typed m : ⊢ ⊨ᵥ S_AUTH ≤ S_AUTH : fac m (τ__F raw aleak).
  Proof using All.
    iApply fac_closure.
    do 2 (iApplyT sem_typed_let; first (iApply sem_typed_fac_call; iApply sem_typed_val; iApply MAC_ideal_typed)).
    do 4 (iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_bool')).
    iApply sem_typed_sub_nil. iApply (sem_typed_oval _ [_; _; _; _; _; _]).
    iApply sem_typed_RLam. iIntros (θ).
    (* the client-taking closure captures only copyable state *)
    iApplyT sem_oval_typed_ufun.
    iApply (sem_typed_oval _ [_; _; _; _; _; _; _]). iApply sem_typed_RLam. iIntros (θ₂).
    iApplyT sem_oval_typed_afun. simpl.
    iApplyT sem_typed_pair_elim; first tvar.
    (* [f (send closure, receive closure)], with [f] instantiated at [¡θ₂] *)
    iApplyT sem_typed_app_fun_nil.
    2: { iApplyT (sem_typed_sub_env _ (sauth_env θ₂ ++ sauth_env θ₂ ++ [("f", _)])).
         { rewrite /sauth_env. simpl. env_solve16. }
         iApplyT sem_typed_pair.
         - iApply sem_typed_sub_nil. iApply (sem_typed_oval _ (sauth_env θ₂)).
           iApplyT sem_oval_typed_ufun. simpl. iApply sauth_recv_body_typed.
         - iApply sem_typed_sub_nil. iApply (sem_typed_oval _ (sauth_env θ₂)).
           iApplyT sem_oval_typed_ufun. simpl. iApply sauth_send_body_typed. }
    2: { iApplyT sem_typed_sub_ty; last tvar. iApply ty_le_row_forall_inst. }
    first [iApply row_le_refl | row_le_submseteq
          | (iApply row_le_trans; first iApplyT row_le_union';
             [iApply row_le_mfbang_elim|iApply row_le_refl|row_le_submseteq])].
      Unshelve. all: solve_typed_side.
  Qed.

End auth_typing.

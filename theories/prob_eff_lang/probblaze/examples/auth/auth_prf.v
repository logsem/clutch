(* The ideal protocol [AUTH_ideal] (both directions over the ideal MAC) and
   the simulated functionality [S_AUTH ∘f F_AUTH] are equivalent, exactly.

   Both sessions have the same handler skeleton ([auth_skel], [F_AUTH_eq]);
   [auth_skel_rel] relates two such sessions from relations between their
   handler bodies, so only the bodies are compared here, under an invariant
   per message slot that ties the protocol's MAC instance to the simulator's
   and [F_AUTH]'s stored message to the tagged one.

   The comparison is one proof in the logic for equivalences ([eq_logic]),
   with the protocol as the program [l] and the simulated functionality as
   [r]; the two typing judgements are its instances. *)

From iris.bi Require Import monpred.
From iris.proofmode Require Import base proofmode classes monpred.
From iris.base_logic.lib Require Import na_invariants.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_row sem_sig sem_env sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze.uc Require Import comp_operators uc_systems.
From clutch.prob_eff_lang.probblaze.examples.dhke Require Import dhke_def.
From clutch.prob_eff_lang.probblaze.examples Require Import dhke_typing.
From clutch.prob_eff_lang.probblaze.examples.auth Require Import auth_def auth_typing.
From clutch.prob_eff_lang.probblaze.eq Require Import eq_logic eq_valgroup eq_compat.

Import fingroup.
Import fingroup.fingroup.

Section brel_typed.
  Context `{!probblazeRGS Σ}.

  Lemma subst_map_3 (γ : gmap string val) (x1 x2 x3 : string) (a b c : val) e :
    x1 ≠ x2 → x1 ≠ x3 → x2 ≠ x3 →
    γ !! x1 = Some a → γ !! x2 = Some b → γ !! x3 = Some c →
    is_closed_expr {[x1; x2; x3]} e →
    subst_map γ e = val_subst x1 a (val_subst x2 b (val_subst x3 c e)).
  Proof.
    intros ?????? Hcl.
    rewrite - {1}(insert_delete_id γ x1 a) // subst_map_insert delete_delete_eq.
    rewrite - {1}(insert_delete_id (delete x1 γ) x2 b); last by rewrite lookup_delete_ne.
    rewrite subst_map_insert delete_delete_eq.
    rewrite - {1}(insert_delete_id (delete x2 (delete x1 γ)) x3 c); last by rewrite !lookup_delete_ne.
    rewrite subst_map_insert delete_delete_eq.
    rewrite (subst_map_is_closed _ e _ Hcl) //.
    intros x Hx.
    assert (x = x1 ∨ x = x2 ∨ x = x3) as [Hx1|[Hx1|Hx1]] by set_solver; subst x; by simplify_map_eq.
  Qed.

  (* A relation between open expressions from the relations of their
     instances, for expressions closed but for three variables; the third
     variable is persistent and survives. *)
  Lemma sem_typed_of_brel3 (x1 x2 x3 : string) (T1 T2 T3 : sem_ty Σ) `{!MultiT T3} e e' (ρ : sem_row Σ) (τ : sem_ty Σ) :
    x1 ≠ x2 → x1 ≠ x3 → x2 ≠ x3 →
    is_closed_expr {[x1; x2; x3]} e → is_closed_expr {[x1; x2; x3]} e' →
    □ (∀ a1 a2 b1 b2 c1 c2, T1 a1 a2 -∗ T2 b1 b2 -∗ T3 c1 c2 -∗
        BREL val_subst x1 a1 (val_subst x2 b1 (val_subst x3 c1 e))
          ≤ val_subst x1 a2 (val_subst x2 b2 (val_subst x3 c2 e')) <|iLblSig_to_iLblThy ρ|> {{ τ }}) -∗
    sem_typed [(x1, T1); (x2, T2); (x3, T3)] e e' ρ τ [(x3, T3)].
  Proof.
    iIntros (?????) "#H". rewrite /sem_typed /tc_opaque. iIntros "!# %γ HΓ".
    rewrite !env_sem_typed_cons env_sem_typed_empty.
    iDestruct "HΓ" as "((%a1 & %a2 & %Ha & Ha) & (%b1 & %b2 & %Hb & Hb) & (%c1 & %c2 & %Hc & #Hc) & _)".
    rewrite (subst_map_3 (fst <$> γ) x1 x2 x3 a1 b1 c1); rewrite ?lookup_fmap ?Ha ?Hb ?Hc //.
    rewrite (subst_map_3 (snd <$> γ) x1 x2 x3 a2 b2 c2); rewrite ?lookup_fmap ?Ha ?Hb ?Hc //.
    iApply (brel_wand with "[Ha Hb]"); first iApply ("H" with "Ha Hb Hc").
    iIntros "!# % % Hτ". iSplitL "Hτ"; first done.
    iSplit; last done. iExists _, _. by iFrame "Hc".
  Qed.

End brel_typed.

Section skel.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  Import valgroup_notation.
  Import typed_hint_modes.
  #[local] Existing Instance multi_ty_group.

  (* The client of a session. *)
  Definition clientT (θ : sem_row Σ) : sem_ty Σ := (∀ᵣ θ₁, chan θ₁ -{ sem_row_union (¡θ₁) θ }-∘ 𝟙)%T.

  (* Two sessions of the [auth_skel'] shape are related when their handler
     bodies are, for ports related at [sT] and [rT].  The bodies are label
     free and closed but for the handler's binders and the port. *)
  Definition lbl_free (e : expr) : Prop := ∀ s l, lbl_subst s l e = e.

  Lemma auth_skel_rel (θ θ₂ : sem_row Σ) (sT rT : sem_ty Σ) `{!MultiT sT} `{!MultiT rT} hsL hsR hrL hrR :
    lbl_free hsL → lbl_free hsR → lbl_free hrL → lbl_free hrR →
    is_closed_expr {[ "message"; "k"; "doLeakSend" ]} hsL →
    is_closed_expr {[ "message"; "k"; "doLeakSend" ]} hsR →
    is_closed_expr {[ "from"; "k"; "doLeakRecv" ]} hrL →
    is_closed_expr {[ "from"; "k"; "doLeakRecv" ]} hrR →
    □ (∀ ρh, (¡ θ₂)%R ≤ᵣ ρh -∗ ∀ a1 a2 b1 b2 c1 c2,
        (𝔾 × (𝟙 + 𝟙))%T a1 a2 -∗ (𝟙 -{ ρh }-[OS]-> 𝟙)%T b1 b2 -∗ sT c1 c2 -∗
        BREL val_subst "message" a1 (val_subst "k" b1 (val_subst "doLeakSend" c1 hsL))
          ≤ val_subst "message" a2 (val_subst "k" b2 (val_subst "doLeakSend" c2 hsR))
          <|iLblSig_to_iLblThy ρh|> {{ 𝟙 }}) -∗
    □ (∀ ρh, (¡ θ₂)%R ≤ᵣ ρh -∗ ∀ a1 a2 b1 b2 c1 c2,
        (𝟙 + 𝟙)%T a1 a2 -∗ (Option 𝔾 -{ ρh }-[OS]-> 𝟙)%T b1 b2 -∗ rT c1 c2 -∗
        BREL val_subst "from" a1 (val_subst "k" b1 (val_subst "doLeakRecv" c1 hrL))
          ≤ val_subst "from" a2 (val_subst "k" b2 (val_subst "doLeakRecv" c2 hrR))
          <|iLblSig_to_iLblThy ρh|> {{ 𝟙 }}) -∗
    sem_typed [("doLeakSend", sT); ("doLeakRecv", rT); ("f", clientT θ)] (auth_skel' hsL hrL) (auth_skel' hsR hrR)
      (sem_row_union (¡ θ₂) θ) 𝟙 [].
  Proof using All.
    intros HsL HsR HrL HrR HcsL HcsR HcrL HcrR.
    iIntros "#Hs #Hr". rewrite /auth_skel'.
    iApply sem_typed_effect_gen. iIntros (ls1 ls2).
    iApply sem_typed_effect_gen. iIntros (lr1 lr2). cbn [lbl_subst].
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
    iApplyT (sem_typed_sub_env _ (([("doRecv", _); ("doSend", _); ("f", _)] ++ [("doLeakSend", sT)])
                                    ++ [("doLeakRecv", rT)])).
    { simpl. env_solve16. }
    iApplyT (sem_typed_deep_handler_OS (lr1, lr2) (λ _, 𝟙 + 𝟙)%T (λ _, Option 𝔾)%T).
    - iApplyT sem_typed_sub_row; first iApply row_le_swap_second.
      iApplyT (sem_typed_sub_env _ ([_; _; _] ++ [("doLeakSend", sT)])); first iApply env_le_refl.
      iApplyT (sem_typed_deep_handler_OS (ls1, ls2) (λ _, 𝔾 × (𝟙 + 𝟙))%T (λ _, 𝟙)%T).
      + iApplyT sem_typed_app_fun_nil.
        2: { iApplyT sem_typed_pair; tvar. }
        2: { iApplyT sem_typed_sub_ty; last tvar. iApply ty_le_row_forall_inst. }
        iApply row_le_trans; first iApplyT row_le_union'.
        * iApply row_le_mfbang_elim.
        * iApply row_le_refl.
        * row_le_submseteq.
      + iIntros (?). rewrite HsL HsL HsR HsR.
        iApply sem_typed_of_brel3; [done|done|done|done|done|].
        iIntros "!>" (a1 a2 b1 b2 c1 c2) "Ha Hb Hc". iApply ("Hs" with "[] Ha Hb Hc"). row_le_submseteq.
      + iApplyT sem_typed_sub_env_final; last iApplyT sem_typed_unit'. env_solve16.
    - iIntros (?). rewrite HrL HrL HrR HrR.
      iApply sem_typed_of_brel3; [done|done|done|done|done|].
      iIntros "!>" (a1 a2 b1 b2 c1 c2) "Ha Hb Hc". iApply ("Hr" with "[] Ha Hb Hc"). row_le_submseteq.
    - iApplyT sem_typed_sub_env_final; last iApplyT sem_typed_unit'. env_solve16.
      Unshelve. all: solve_typed_side.
  Qed.

End skel.

Section skel_inst.
  Context `{!probblazeRGS Σ}.

  (* Instantiating a relation between open expressions at concrete ports
     and client. *)
  Lemma sem_typed_inst3 (x1 x2 x3 : string) (T1 T2 T3 : sem_ty Σ) e e' ρ τ (a1 a2 b1 b2 c1 c2 : val) :
    x1 ≠ x2 → x1 ≠ x3 → x2 ≠ x3 →
    sem_typed [(x1, T1); (x2, T2); (x3, T3)] e e' ρ τ [] -∗ T1 a1 a2 -∗ T2 b1 b2 -∗ T3 c1 c2 -∗
    BREL val_subst x2 b1 (val_subst x1 a1 (val_subst x3 c1 e))
      ≤ val_subst x2 b2 (val_subst x1 a2 (val_subst x3 c2 e')) <|iLblSig_to_iLblThy ρ|> {{ τ }}.
  Proof.
    iIntros (H12 H13 H23) "#He Ha Hb Hc". rewrite /sem_typed /tc_opaque.
    iDestruct ("He" $! (<[x2:=(b1,b2)]> (<[x1:=(a1,a2)]> (<[x3:=(c1,c2)]> ∅))) with "[Ha Hb Hc]") as "H".
    { rewrite !env_sem_typed_cons env_sem_typed_empty.
      iSplitL "Ha"; first (iExists _, _; iFrame; by simplify_map_eq).
      iSplitL "Hb"; first (iExists _, _; iFrame; by simplify_map_eq).
      iSplitL "Hc"; first (iExists _, _; iFrame; by simplify_map_eq). done. }
    iRevert "H". rewrite !fmap_insert !fmap_empty /=.
    repeat first [rewrite subst_map_insert | rewrite delete_insert_ne; last done
                 | rewrite delete_empty | rewrite subst_map_empty].
    iIntros "H".
    iApply (brel_wand with "H"). iIntros "!# % % [$ _]".
  Qed.

End skel_inst.


Section rel.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  Import valgroup_notation.
  Import valgroup_tactics.
  #[local] Notation n := (S n'').
  #[local] Open Scope bi_scope.

  Definition pure_ty (P : val → val → Prop) : sem_ty Σ := (λ v1 v2, ⌜P v1 v2⌝)%I.
  Global Instance pure_ty_multi P : MultiT (pure_ty P).
  Proof. constructor. iIntros "!#" (v1 v2) "%HP". rewrite /sem_ty_mbang /=. by iModIntro. Qed.

  Definition keyv (key : option (nat * nat)) : val :=
    match key with None => NONEV | Some (a, b) => SOMEV (#a, #b) end.
  Definition tgv (tg : option (fingroup.FinGroup.sort vgG * fingroup.FinGroup.sort vgG)) : val :=
    match tg with None => NONEV | Some (m, t) => SOMEV (vgval m, vgval t) end.
  Definition verv (v : option bool) : val :=
    match v with None => NONEV | Some b => SOMEV #b end.
  Definition decb (v : option bool) : bool := match v with None => false | Some _ => true end.
  Definition accb (v : option bool) : bool := match v with Some true => true | _ => false end.
  Definition msgv (tg : option (fingroup.FinGroup.sort vgG * fingroup.FinGroup.sort vgG)) : val :=
    match tg with None => NONEV | Some (m, _) => SOMEV (vgval m) end.
  Definition resv (tg : option (fingroup.FinGroup.sort vgG * fingroup.FinGroup.sort vgG)) (v : option bool) : val :=
    if accb v then msgv tg else NONEV.

  (* One message slot: the protocol's MAC instance and receiver state ([l]),
     the simulator's MAC instance and receiver state and [F_AUTH]'s stored
     message ([r]).  Both MAC instances are in the same state; the protocol
     receiver's result is the simulator's permission applied to the stored
     message. *)
  Definition slot_inv (αl βl keyl tgl verl decl resl αr βr keyr tgr verr decr accr mr : loc) : iPropD Σ :=
    ∃ (key : option (nat * nat)) (tg : option (fingroup.FinGroup.sort vgG * fingroup.FinGroup.sort vgG)) (v : option bool),
      ⌜accb v = true → is_Some tg⌝ ∗
      αl ↪ₗN (n; []) ∗ βl ↪ₗN (n; []) ∗ αr ↪ᵣN (n; []) ∗ βr ↪ᵣN (n; []) ∗
      keyl ↦ₗ keyv key ∗ keyr ↦ᵣ keyv key ∗ tgl ↦ₗ tgv tg ∗ tgr ↦ᵣ tgv tg ∗
      verl ↦ₗ verv v ∗ verr ↦ᵣ verv v ∗
      decl ↦ₗ #(decb v) ∗ decr ↦ᵣ #(decb v) ∗ resl ↦ₗ resv tg v ∗ accr ↦ᵣ #(accb v) ∗
      mr ↦ᵣ msgv tg.

  Definition slot1N : namespace := nroot .@ "slot1".
  Definition slot2N : namespace := nroot .@ "slot2".

  (* The packet put on the network by a send. *)
  Lemma packet_typed (m t : fingroup.FinGroup.sort vgG) (d : val) :
    d = InjLV #()%V ∨ d = InjRV #()%V →
    ⊢ ((𝔾 × 𝔾) × (𝟙 + 𝟙))%T ((vgval m, vgval t), d)%V ((vgval m, vgval t), d)%V.
  Proof.
    iIntros (Hd). iExists _, _, _, _. iSplit; first done. iSplit; first done. iSplit.
    - iExists _, _, _, _. iSplit; first done. iSplit; first done. iSplit; by iExists _.
    - iExists #()%V, #()%V. destruct Hd as [->| ->]; [iLeft|iRight]; by repeat iSplit.
  Qed.


  Lemma opt_none : ⊢ (Option 𝔾)%T NONEV NONEV.
  Proof. iExists #()%V, #()%V. iLeft. by repeat iSplit. Qed.
  Lemma opt_some (m : fingroup.FinGroup.sort vgG) : ⊢ (Option 𝔾)%T (SOMEV (vgval m)) (SOMEV (vgval m)).
  Proof. iExists _, _. iRight. iSplit; first done. iSplit; first done. by iExists _. Qed.
  Lemma from_typed (d : val) : d = InjLV #()%V ∨ d = InjRV #()%V → ⊢ ((𝟙 + 𝟙)%T : sem_ty Σ) d d.
  Proof. iIntros (Hd). iExists #()%V, #()%V. destruct Hd as [->| ->]; [iLeft|iRight]; by repeat iSplit. Qed.

  (* [auth_skel_rel], instantiated: two sessions of the [auth_skel'] shape
     are equivalent if their send and receive bodies are. *)
  Lemma eq_auth_skel (θ θ₂ : sem_row Σ) hsl hsr hrl hrr (sl sr rl rr fl fr : val) :
    lbl_free hsl → lbl_free hsr → lbl_free hrl → lbl_free hrr →
    is_closed_expr {[ "message"; "k"; "doLeakSend" ]} hsl →
    is_closed_expr {[ "message"; "k"; "doLeakSend" ]} hsr →
    is_closed_expr {[ "from"; "k"; "doLeakRecv" ]} hrl →
    is_closed_expr {[ "from"; "k"; "doLeakRecv" ]} hrr →
    ⊢ □ (∀ ρh, ⎡(¡ θ₂)%R ≤ᵣ ρh⎤ -∗ ∀ al ar bl br,
          ⟪ 𝔾 × (𝟙 + 𝟙) ⟫ al ar -∗ ⟪ 𝟙 -{ ρh }-[OS]-> 𝟙 ⟫ bl br -∗
          EQ val_subst "message" al (val_subst "k" bl (val_subst "doLeakSend" sl hsl))
           ≈ val_subst "message" ar (val_subst "k" br (val_subst "doLeakSend" sr hsr))
           <|iLblSig_to_iLblThy ρh|> {{ ⟪ 𝟙 ⟫ }}) -∗
      □ (∀ ρh, ⎡(¡ θ₂)%R ≤ᵣ ρh⎤ -∗ ∀ al ar bl br,
          ⟪ 𝟙 + 𝟙 ⟫ al ar -∗ ⟪ Option 𝔾 -{ ρh }-[OS]-> 𝟙 ⟫ bl br -∗
          EQ val_subst "from" al (val_subst "k" bl (val_subst "doLeakRecv" rl hrl))
           ≈ val_subst "from" ar (val_subst "k" br (val_subst "doLeakRecv" rr hrr))
           <|iLblSig_to_iLblThy ρh|> {{ ⟪ 𝟙 ⟫ }}) -∗
      ⟪ clientT θ ⟫ fl fr -∗
      EQ val_subst "doLeakRecv" rl (val_subst "doLeakSend" sl (val_subst "f" fl (auth_skel' hsl hrl)))
       ≈ val_subst "doLeakRecv" rr (val_subst "doLeakSend" sr (val_subst "f" fr (auth_skel' hsr hrr)))
       <|iLblSig_to_iLblThy (sem_row_union (¡ θ₂) θ)|> {{ ⟪ 𝟙 ⟫ }}.
  Proof using All.
    intros ????????. iStartProof (iProp _). iIntros (d) "#Hs #Hr Hf".
    destruct d; rewrite eq_rel_at eq_lift_at /pick /=;
      iApply (brel_wand' _ _ _ 𝟙%T with "[]"); try (iIntros "!> % % H"; by rewrite eq_lift_at).
    - iApply (sem_typed_inst3 "doLeakSend" "doLeakRecv" "f"
                (pure_ty (λ v1 v2, v1 = sl ∧ v2 = sr)%type) (pure_ty (λ v1 v2, v1 = rl ∧ v2 = rr)%type) (clientT θ)
                (auth_skel' hsl hrl) (auth_skel' hsr hrr) _ _ sl sr rl rr fl fr
              with "[] [] [] Hf"); [done|done|done| |done|done].
      iApply (auth_skel_rel with "[] []"); try done.
      + iIntros "!>" (ρh) "#Hρ". iIntros (a1 a2 b1 b2 c1 c2) "Ha Hk %Hc". destruct Hc as [-> ->].
        iApply (brel_wand with "[-]"); first (iApply (eq_rel_at_elim_const Fwd); iApply ("Hs" $! ρh with "[] [Ha] [Hk]");
          [iExact "Hρ"|rewrite eq_lift_at; iExact "Ha"|rewrite eq_lift_at; iExact "Hk"]).
        iIntros "!> % % H". by rewrite eq_lift_at.
      + iIntros "!>" (ρh) "#Hρ". iIntros (a1 a2 b1 b2 c1 c2) "Ha Hk %Hc". destruct Hc as [-> ->].
        iApply (brel_wand with "[-]"); first (iApply (eq_rel_at_elim_const Fwd); iApply ("Hr" $! ρh with "[] [Ha] [Hk]");
          [iExact "Hρ"|rewrite eq_lift_at; iExact "Ha"|rewrite eq_lift_at; iExact "Hk"]).
        iIntros "!> % % H". by rewrite eq_lift_at.
    - iApply (sem_typed_inst3 "doLeakSend" "doLeakRecv" "f"
                (pure_ty (λ v1 v2, v1 = sr ∧ v2 = sl)%type) (pure_ty (λ v1 v2, v1 = rr ∧ v2 = rl)%type) (clientT θ)
                (auth_skel' hsr hrr) (auth_skel' hsl hrl) _ _ sr sl rr rl fr fl
              with "[] [] [] Hf"); [done|done|done| |done|done].
      iApply (auth_skel_rel with "[] []"); try done.
      + iIntros "!>" (ρh) "#Hρ". iIntros (a1 a2 b1 b2 c1 c2) "Ha Hk %Hc". destruct Hc as [-> ->].
        iApply (brel_wand with "[-]"); first (iApply (eq_rel_at_elim_const Bwd); iApply ("Hs" $! ρh with "[] [Ha] [Hk]");
          [iExact "Hρ"|rewrite eq_lift_at; iExact "Ha"|rewrite eq_lift_at; iExact "Hk"]).
        iIntros "!> % % H". by rewrite eq_lift_at.
      + iIntros "!>" (ρh) "#Hρ". iIntros (a1 a2 b1 b2 c1 c2) "Ha Hk %Hc". destruct Hc as [-> ->].
        iApply (brel_wand with "[-]"); first (iApply (eq_rel_at_elim_const Bwd); iApply ("Hr" $! ρh with "[] [Ha] [Hk]");
          [iExact "Hρ"|rewrite eq_lift_at; iExact "Ha"|rewrite eq_lift_at; iExact "Hk"]).
        iIntros "!> % % H". by rewrite eq_lift_at.
  Qed.

  Lemma AUTH_SIM_EQ :
    ⊢ EQ AUTH_ideal ≈ (S_AUTH ∘f F_AUTH)%fac <|iLblSig_to_iLblThy (⊥ : sem_row Σ)|> {{ ⟪ fac MS (τ__F raw chan) ⟫ }}.
  Proof using All.
    iApply eq_value. iModIntro. rewrite /fac. iModIntro.
    iApply eq_lift_arr. iIntros (u1 u2) "Hu". rewrite eq_lift_unit. iDestruct "Hu" as %[-> ->].
    rewrite /AUTH_ideal /AUTH_of /S_AUTH F_AUTH_eq.
    eq_pures_l.
    (* [l]: two MAC instances and the receivers' state *)
    eq_alloctape_l αa as "Hαa". eq_pures_l. eq_alloctape_l βa as "Hβa". eq_pures_l.
    eq_alloc_l keya as "Hkeya". eq_pures_l. eq_alloc_l tga as "Htga". eq_pures_l.
    eq_alloc_l vera as "Hvera". eq_pures_l.
    eq_alloctape_l αb as "Hαb". eq_pures_l. eq_alloctape_l βb as "Hβb". eq_pures_l.
    eq_alloc_l keyb as "Hkeyb". eq_pures_l. eq_alloc_l tgb as "Htgb". eq_pures_l.
    eq_alloc_l verb as "Hverb". eq_pures_l.
    eq_alloc_l dec1 as "Hdec1". eq_pures_l. eq_alloc_l dec2 as "Hdec2". eq_pures_l.
    eq_alloc_l res1 as "Hres1". eq_pures_l. eq_alloc_l res2 as "Hres2". eq_pures_l.
    (* [r]: [F_AUTH]'s slots, then the simulator's state *)
    eq_pures_r.
    eq_alloc_r m1 as "Hm1". eq_pures_r. eq_alloc_r m2 as "Hm2". eq_pures_r.
    eq_alloctape_r αa' as "Hαa'". eq_pures_r. eq_alloctape_r βa' as "Hβa'". eq_pures_r.
    eq_alloc_r keya' as "Hkeya'". eq_pures_r. eq_alloc_r tga' as "Htga'". eq_pures_r.
    eq_alloc_r vera' as "Hvera'". eq_pures_r.
    eq_alloctape_r αb' as "Hαb'". eq_pures_r. eq_alloctape_r βb' as "Hβb'". eq_pures_r.
    eq_alloc_r keyb' as "Hkeyb'". eq_pures_r. eq_alloc_r tgb' as "Htgb'". eq_pures_r.
    eq_alloc_r verb' as "Hverb'". eq_pures_r.
    eq_alloc_r dec1' as "Hdec1'". eq_pures_r. eq_alloc_r dec2' as "Hdec2'". eq_pures_r.
    eq_alloc_r acc1 as "Hacc1". eq_pures_r. eq_alloc_r acc2 as "Hacc2".
    rewrite ?Nat2Z.id.
    iApply (eq_na_alloc (slot_inv αa βa keya tga vera dec1 res1 αa' βa' keya' tga' vera' dec1' acc1 m1) slot1N).
    iSplitL "Hαa Hβa Hkeya Htga Hvera Hdec1 Hres1 Hαa' Hβa' Hkeya' Htga' Hvera' Hdec1' Hacc1 Hm1".
    { iNext. iExists None, None, None. by iFrame. }
    iIntros "#Hinv1".
    iApply (eq_na_alloc (slot_inv αb βb keyb tgb verb dec2 res2 αb' βb' keyb' tgb' verb' dec2' acc2 m2) slot2N).
    iSplitL "Hαb Hβb Hkeyb Htgb Hverb Hdec2 Hres2 Hαb' Hβb' Hkeyb' Htgb' Hverb' Hdec2' Hacc2 Hm2".
    { iNext. iExists None, None, None. by iFrame. }
    iIntros "#Hinv2".
    eq_pures_r.
    iApply eq_value. iModIntro. rewrite /τ__F eq_lift_forall. iIntros (θ).
    iApply eq_lift_arr. iIntros (f1 f2) "Hf". eq_pures_l. eq_pures_r.
    iApply eq_value. iModIntro. iEval (rewrite eq_lift_forall). iIntros (θ₂).
    iApply eq_lift_arr. iIntros (e1 e2) "He". iEval (rewrite /raw eq_lift_prod) in "He".
    iDestruct "He" as (w1 w1' w2 w2') "(-> & -> & #Hsnd & #Hrcv)".
    eq_pures_l. eq_pures_r.
    set (va := mac_ideal_v αa βa keya tga vera). set (vb := mac_ideal_v αb βb keyb tgb verb).
    set (va' := mac_ideal_v αa' βa' keya' tga' vera'). set (vb' := mac_ideal_v αb' βb' keyb' tgb' verb').
    set (sc := (λ: "payload", sauth_send_b va' vb' w1')%V).
    set (rc := (λ: "from", sauth_recv_b va' vb' #dec1' #dec2' #acc1 #acc2 w2')%V).
    iApply (eq_auth_skel θ θ₂
              (auth_send_h va vb) (fauth_send_h #m1 #m2)
              (auth_recv_h va vb #dec1 #dec2 #res1 #res2) (fauth_recv_h #m1 #m2)
              w1 sc w2 rc f1 f2 with "[] [] Hf");
      try (intros ??; reflexivity);
      try (rewrite /auth_send_h /auth_recv_h /fauth_send_h /fauth_recv_h /va /vb /mac_ideal_v
                   /ideal_tag_b /ideal_verify_b /tag; is_closed; fail).
    - (* send *)
      iIntros "!>" (ρh) "#Hρ". iIntros (a1 a2 b1 b2) "Ha Hk".
      iEval (rewrite eq_lift_prod) in "Ha". iDestruct "Ha" as (x1 x1' y1 y1') "(-> & -> & Hm & Hd)".
      iEval (rewrite eq_lift_group) in "Hm". iDestruct "Hm" as %(m & -> & ->).
      iEval (rewrite eq_lift_sum) in "Hd". iDestruct "Hd" as (d1 d2) "[(-> & -> & Hu)|(-> & -> & Hu)]";
        iEval (rewrite eq_lift_unit) in "Hu"; iDestruct "Hu" as %[-> ->].
      all: rewrite /auth_send_h /fauth_send_h /sc /rc /va /vb /va' /vb' /mac_ideal_v /sauth_send_b /ideal_tag_b; simpl; eq_pures_l; eq_pures_r.
      + 
        iApply (eq_na_open _ _ slot1N); [set_solver|]. iFrame "Hinv1". iIntros "(>HI & Hclose)".
        iDestruct "HI" as (key tg v) "(%Hacc & Hα & Hβ & Hα' & Hβ' & Hkey & Hkey' & Htg & Htg' & Hv & Hv' & Hd & Hd' & Hr & Hac & Hm)".
        destruct tg as [[m0 t0]|]; simpl.
        * (* the slot was used: nothing is sent *)
          eq_load_l. eq_pures_l. eq_load_r. eq_pures_r.
          iApply eq_na_close_rule. iFrame "Hclose". iSplitR "Hk".
          { iNext. iExists key, (Some (m0, t0)), v. by iFrame. }
          iApply (eq_lift_app with "Hk"); by rewrite eq_lift_unit.
        * assert (accb v = false) as Hv0 by (destruct (accb v); [by destruct Hacc|done]).
          eq_load_l. eq_pures_l. eq_load_r. eq_pures_r. eq_store_r. eq_pures_r.
          eq_load_r. eq_pures_r.
          destruct key as [[k1 k2]|]; simpl.
          -- eq_load_l. eq_pures_l. eq_load_r. eq_pures_r. rewrite /tag. eq_pures_l. eq_pures_r.
             eq_exp_l. eq_exp_l. eq_mult_l. eq_pures_l. eq_store_l. eq_pures_l.
             eq_exp_r. eq_exp_r. eq_mult_r. eq_pures_r. eq_store_r. eq_pures_r.
             iApply eq_na_close_rule. iFrame "Hclose". iSplitR "Hk".
             { iNext. iExists (Some (k1, k2)), (Some (m, (m ^+ k1 * g ^+ k2)%g)), v. rewrite /resv Hv0. iFrame.
               iPureIntro. by eexists. }
             iApply (eq_call_frame θ₂ ρh _ 𝟙 _ _ _ _ _ [AppRCtx _] [AppRCtx _] with "Hρ Hsnd [] Hk"); try (intros; apply _).
             { iApply eq_lift_same. iApply packet_typed. by (left + right). }
             iIntros "!>" (v1 v2) "Hv Hk". iEval (rewrite eq_lift_unit) in "Hv". iDestruct "Hv" as %[-> ->]. eq_pures_l. eq_pures_r. iApply (eq_lift_app with "Hk"); by rewrite eq_lift_unit.
          -- iApply (eq_couple_tapes _ _ _ _ _ _ _ _ [] []).
             iFrame "Hβ Hβ'". iIntros (r) "[Hβ Hβ']". simpl.
             eq_load_l. eq_pures_l. eq_rand_l as "%Hr". eq_exp_l. eq_pures_l. eq_store_l. eq_pures_l.
             eq_load_r. eq_pures_r. eq_rand_r as "%Hr'". eq_exp_r. eq_pures_r. eq_store_r. eq_pures_r.
             iApply eq_na_close_rule. iFrame "Hclose". iSplitR "Hk".
             { iNext. iExists None, (Some (m, (g ^+ r)%g)), v. rewrite /resv Hv0. iFrame.
               iPureIntro. by eexists. }
             iApply (eq_call_frame θ₂ ρh _ 𝟙 _ _ _ _ _ [AppRCtx _] [AppRCtx _] with "Hρ Hsnd [] Hk"); try (intros; apply _).
             { iApply eq_lift_same. iApply packet_typed. by (left + right). }
             iIntros "!>" (v1 v2) "Hv Hk". iEval (rewrite eq_lift_unit) in "Hv". iDestruct "Hv" as %[-> ->]. eq_pures_l. eq_pures_r. iApply (eq_lift_app with "Hk"); by rewrite eq_lift_unit.
      + 
        iApply (eq_na_open _ _ slot2N); [set_solver|]. iFrame "Hinv2". iIntros "(>HI & Hclose)".
        iDestruct "HI" as (key tg v) "(%Hacc & Hα & Hβ & Hα' & Hβ' & Hkey & Hkey' & Htg & Htg' & Hv & Hv' & Hd & Hd' & Hr & Hac & Hm)".
        destruct tg as [[m0 t0]|]; simpl.
        * (* the slot was used: nothing is sent *)
          eq_load_l. eq_pures_l. eq_load_r. eq_pures_r.
          iApply eq_na_close_rule. iFrame "Hclose". iSplitR "Hk".
          { iNext. iExists key, (Some (m0, t0)), v. by iFrame. }
          iApply (eq_lift_app with "Hk"); by rewrite eq_lift_unit.
        * assert (accb v = false) as Hv0 by (destruct (accb v); [by destruct Hacc|done]).
          eq_load_l. eq_pures_l. eq_load_r. eq_pures_r. eq_store_r. eq_pures_r.
          eq_load_r. eq_pures_r.
          destruct key as [[k1 k2]|]; simpl.
          -- eq_load_l. eq_pures_l. eq_load_r. eq_pures_r. rewrite /tag. eq_pures_l. eq_pures_r.
             eq_exp_l. eq_exp_l. eq_mult_l. eq_pures_l. eq_store_l. eq_pures_l.
             eq_exp_r. eq_exp_r. eq_mult_r. eq_pures_r. eq_store_r. eq_pures_r.
             iApply eq_na_close_rule. iFrame "Hclose". iSplitR "Hk".
             { iNext. iExists (Some (k1, k2)), (Some (m, (m ^+ k1 * g ^+ k2)%g)), v. rewrite /resv Hv0. iFrame.
               iPureIntro. by eexists. }
             iApply (eq_call_frame θ₂ ρh _ 𝟙 _ _ _ _ _ [AppRCtx _] [AppRCtx _] with "Hρ Hsnd [] Hk"); try (intros; apply _).
             { iApply eq_lift_same. iApply packet_typed. by (left + right). }
             iIntros "!>" (v1 v2) "Hv Hk". iEval (rewrite eq_lift_unit) in "Hv". iDestruct "Hv" as %[-> ->]. eq_pures_l. eq_pures_r. iApply (eq_lift_app with "Hk"); by rewrite eq_lift_unit.
          -- iApply (eq_couple_tapes _ _ _ _ _ _ _ _ [] []).
             iFrame "Hβ Hβ'". iIntros (r) "[Hβ Hβ']". simpl.
             eq_load_l. eq_pures_l. eq_rand_l as "%Hr". eq_exp_l. eq_pures_l. eq_store_l. eq_pures_l.
             eq_load_r. eq_pures_r. eq_rand_r as "%Hr'". eq_exp_r. eq_pures_r. eq_store_r. eq_pures_r.
             iApply eq_na_close_rule. iFrame "Hclose". iSplitR "Hk".
             { iNext. iExists None, (Some (m, (g ^+ r)%g)), v. rewrite /resv Hv0. iFrame.
               iPureIntro. by eexists. }
             iApply (eq_call_frame θ₂ ρh _ 𝟙 _ _ _ _ _ [AppRCtx _] [AppRCtx _] with "Hρ Hsnd [] Hk"); try (intros; apply _).
             { iApply eq_lift_same. iApply packet_typed. by (left + right). }
             iIntros "!>" (v1 v2) "Hv Hk". iEval (rewrite eq_lift_unit) in "Hv". iDestruct "Hv" as %[-> ->]. eq_pures_l. eq_pures_r. iApply (eq_lift_app with "Hk"); by rewrite eq_lift_unit.
    - (* recv *)
      iIntros "!>" (ρh) "#Hρ". iIntros (a1 a2 b1 b2) "Ha Hk".
      iEval (rewrite eq_lift_sum) in "Ha". iDestruct "Ha" as (d1 d2) "[(-> & -> & Hu)|(-> & -> & Hu)]";
        iEval (rewrite eq_lift_unit) in "Hu"; iDestruct "Hu" as %[-> ->].
      all: rewrite /auth_recv_h /fauth_recv_h /sc /rc /va /vb /va' /vb' /mac_ideal_v /sauth_recv_b /ideal_verify_b;
        simpl; eq_pures_l; eq_pures_r.
      + (* a receiver [InjL] reads slot 2 *)
        iApply (eq_na_open _ _ slot2N); [set_solver|]. iFrame "Hinv2". iIntros "(>HI & Hclose)".
        iDestruct "HI" as (key tg v) "(%Hacc & Hα & Hβ & Hα' & Hβ' & Hkey & Hkey' & Htg & Htg' & Hv & Hv' & Hd & Hd' & Hr & Hac & Hm)".
        destruct v as [b|]; simpl.
        * (* already decided *)
          destruct b.
          { destruct tg as [[m0 t0]|]; last by destruct Hacc. simpl.
            eq_load_l. eq_pures_l. eq_load_l.
            eq_load_r. eq_pures_r. eq_load_r. eq_pures_r. eq_load_r. eq_pures_r.
            iApply eq_na_close_rule. iFrame "Hclose". iSplitR "Hk".
            { iNext. iExists key, (Some (m0, t0)), (Some true). by iFrame. }
            iApply (eq_lift_app with "Hk"). iApply eq_lift_same. iApply opt_some. }
          { eq_load_l. eq_pures_l. eq_load_l.
            eq_load_r. eq_pures_r. eq_load_r. eq_pures_r.
            iApply eq_na_close_rule. iFrame "Hclose". iSplitR "Hk".
            { iNext. iExists key, tg, (Some false). by iFrame. }
            iApply (eq_lift_app with "Hk"). iApply eq_lift_same. iApply opt_none. }
        * eq_load_l. eq_pures_l. eq_load_r. eq_pures_r.
          iApply eq_na_close_rule. iFrame "Hclose". iSplitR "Hk".
          { iNext. iExists key, tg, None. by iFrame. }
          iApply (eq_call_frame θ₂ ρh _ (Option (𝔾 × 𝔾))%T _ _ _ _ _ [CaseCtx _ _] [AppRCtx _; CaseCtx _ _]
                    with "Hρ Hrcv [] Hk"); try (intros; apply _).
          { iApply eq_lift_same. iApply from_typed. by (left + right). }
          iIntros "!>" (r1 r2) "Hv Hk". iEval (rewrite eq_lift_sum) in "Hv".
          iDestruct "Hv" as (p1 p2) "[(-> & -> & Hu)|(-> & -> & Hp)]";
            [iEval (rewrite eq_lift_unit) in "Hu"; iDestruct "Hu" as %[-> ->]|].
          -- (* nothing delivered *)
             eq_pures_l. eq_pures_r. iApply (eq_lift_app with "Hk"). iApply eq_lift_same. iApply opt_none.
          -- iEval (rewrite eq_lift_prod) in "Hp". iDestruct "Hp" as (q1 q1' q2 q2') "(-> & -> & Hm' & Ht')".
             iEval (rewrite eq_lift_group) in "Hm' Ht'". iDestruct "Hm'" as %(m' & -> & ->). iDestruct "Ht'" as %(t' & -> & ->).
             eq_pures_l. eq_pures_r.
             clear key tg Hacc.
             iApply (eq_na_open _ _ slot2N); [set_solver|]. iFrame "Hinv2". iIntros "(>HI & Hclose)".
             iDestruct "HI" as (key tg v) "(%Hacc & Hα & Hβ & Hα' & Hβ' & Hkey & Hkey' & Htg & Htg' & Hv & Hv' & Hd & Hd' & Hr & Hac & Hm)".
             destruct v as [b|]; simpl.
             ++ (* decided meanwhile *)
                destruct b.
                { destruct tg as [[m0 t0]|]; last by destruct Hacc. simpl.
                  eq_load_l. eq_pures_l. eq_load_l.
                  eq_load_r. eq_pures_r. eq_load_r. eq_pures_r. eq_load_r. eq_pures_r.
                  iApply eq_na_close_rule. iFrame "Hclose". iSplitR "Hk".
                  { iNext. iExists key, (Some (m0, t0)), (Some true). by iFrame. }
                  iApply (eq_lift_app with "Hk"). iApply eq_lift_same. iApply opt_some. }
                { eq_load_l. eq_pures_l. eq_load_l.
                  eq_load_r. eq_pures_r. eq_load_r. eq_pures_r.
                  iApply eq_na_close_rule. iFrame "Hclose". iSplitR "Hk".
                  { iNext. iExists key, tg, (Some false). by iFrame. }
                  iApply (eq_lift_app with "Hk"). iApply eq_lift_same. iApply opt_none. }
             ++ eq_load_l. eq_pures_l. eq_load_r. eq_pures_r.
                eq_load_l. eq_pures_l. eq_load_r. eq_pures_r.
                destruct tg as [[m0 t0]|]; simpl.
                ** (* tagged: accept iff the pair is the tagged one *)
                   eq_load_l. eq_pures_l. eq_load_r. eq_pures_r.
                   eq_eq_l. eq_eq_r.
                   destruct (decide (m' = m0)) as [<-|Hne].
                   --- rewrite bool_decide_eq_true_2 //. eq_pures_l. eq_pures_r. eq_eq_l. eq_eq_r.
                       destruct (decide (t' = t0)) as [<-|Hne'].
                       +++ rewrite bool_decide_eq_true_2 //. eq_pures_l. eq_pures_r.
                           eq_store_l. eq_pures_l. eq_store_l. eq_pures_l. eq_store_l. eq_pures_l.
                           eq_store_r. eq_pures_r. eq_store_r. eq_pures_r. eq_store_r. eq_pures_r.
                           eq_load_r. eq_pures_r.
                           iApply eq_na_close_rule. iFrame "Hclose". iSplitR "Hk".
                           { iNext. iExists key, (Some (m', t')), (Some true). iFrame. iPureIntro. by eexists. }
                           iApply (eq_lift_app with "Hk"). iApply eq_lift_same. iApply opt_some.
                       +++ rewrite bool_decide_eq_false_2 //. eq_pures_l. eq_pures_r.
                           eq_store_l. eq_pures_l. eq_store_l. eq_pures_l. eq_store_l. eq_pures_l.
                           eq_store_r. eq_pures_r. eq_store_r. eq_pures_r. eq_store_r. eq_pures_r.
                           iApply eq_na_close_rule. iFrame "Hclose". iSplitR "Hk".
                           { iNext. iExists key, (Some (m', t0)), (Some false). by iFrame. }
                           iApply (eq_lift_app with "Hk"). iApply eq_lift_same. iApply opt_none.
                   --- rewrite bool_decide_eq_false_2 //. eq_pures_l. eq_pures_r.
                       eq_store_l. eq_pures_l. eq_store_l. eq_pures_l. eq_store_l. eq_pures_l.
                       eq_store_r. eq_pures_r. eq_store_r. eq_pures_r. eq_store_r. eq_pures_r.
                       iApply eq_na_close_rule. iFrame "Hclose". iSplitR "Hk".
                       { iNext. iExists key, (Some (m0, t0)), (Some false). by iFrame. }
                       iApply (eq_lift_app with "Hk"). iApply eq_lift_same. iApply opt_none.
                ** (* untagged: the key is sampled (in sync) and the pair rejected *)
                   eq_load_l. eq_pures_l. eq_load_r. eq_pures_r.
                   iApply (eq_couple_tapes _ _ _ _ _ _ _ _ [] []).
                   iFrame "Hα Hα'". iIntros (k1) "[Hα Hα']". simpl.
                   iApply (eq_couple_tapes _ _ _ _ _ _ _ _ [] []).
                   iFrame "Hβ Hβ'". iIntros (k2) "[Hβ Hβ']". simpl.
                   eq_rand_l as "%Hk1". eq_pures_l. eq_rand_l as "%Hk2". eq_pures_l.
                   eq_rand_r as "%Hk1'". eq_pures_r. eq_rand_r as "%Hk2'". eq_pures_r.
                   eq_store_l. eq_pures_l. eq_store_r. eq_pures_r.
                   eq_store_l. eq_pures_l. eq_store_l. eq_pures_l. eq_store_l. eq_pures_l.
                   eq_store_r. eq_pures_r. eq_store_r. eq_pures_r. eq_store_r. eq_pures_r.
                   iApply eq_na_close_rule. iFrame "Hclose". iSplitR "Hk".
                   { iNext. iExists (Some (k1, k2)), None, (Some false). by iFrame. }
                   iApply (eq_lift_app with "Hk"). iApply eq_lift_same. iApply opt_none.
      + (* a receiver [InjR] reads slot 1 *)
        iApply (eq_na_open _ _ slot1N); [set_solver|]. iFrame "Hinv1". iIntros "(>HI & Hclose)".
        iDestruct "HI" as (key tg v) "(%Hacc & Hα & Hβ & Hα' & Hβ' & Hkey & Hkey' & Htg & Htg' & Hv & Hv' & Hd & Hd' & Hr & Hac & Hm)".
        destruct v as [b|]; simpl.
        * (* already decided *)
          destruct b.
          { destruct tg as [[m0 t0]|]; last by destruct Hacc. simpl.
            eq_load_l. eq_pures_l. eq_load_l.
            eq_load_r. eq_pures_r. eq_load_r. eq_pures_r. eq_load_r. eq_pures_r.
            iApply eq_na_close_rule. iFrame "Hclose". iSplitR "Hk".
            { iNext. iExists key, (Some (m0, t0)), (Some true). by iFrame. }
            iApply (eq_lift_app with "Hk"). iApply eq_lift_same. iApply opt_some. }
          { eq_load_l. eq_pures_l. eq_load_l.
            eq_load_r. eq_pures_r. eq_load_r. eq_pures_r.
            iApply eq_na_close_rule. iFrame "Hclose". iSplitR "Hk".
            { iNext. iExists key, tg, (Some false). by iFrame. }
            iApply (eq_lift_app with "Hk"). iApply eq_lift_same. iApply opt_none. }
        * eq_load_l. eq_pures_l. eq_load_r. eq_pures_r.
          iApply eq_na_close_rule. iFrame "Hclose". iSplitR "Hk".
          { iNext. iExists key, tg, None. by iFrame. }
          iApply (eq_call_frame θ₂ ρh _ (Option (𝔾 × 𝔾))%T _ _ _ _ _ [CaseCtx _ _] [AppRCtx _; CaseCtx _ _]
                    with "Hρ Hrcv [] Hk"); try (intros; apply _).
          { iApply eq_lift_same. iApply from_typed. by (left + right). }
          iIntros "!>" (r1 r2) "Hv Hk". iEval (rewrite eq_lift_sum) in "Hv".
          iDestruct "Hv" as (p1 p2) "[(-> & -> & Hu)|(-> & -> & Hp)]";
            [iEval (rewrite eq_lift_unit) in "Hu"; iDestruct "Hu" as %[-> ->]|].
          -- (* nothing delivered *)
             eq_pures_l. eq_pures_r. iApply (eq_lift_app with "Hk"). iApply eq_lift_same. iApply opt_none.
          -- iEval (rewrite eq_lift_prod) in "Hp". iDestruct "Hp" as (q1 q1' q2 q2') "(-> & -> & Hm' & Ht')".
             iEval (rewrite eq_lift_group) in "Hm' Ht'". iDestruct "Hm'" as %(m' & -> & ->). iDestruct "Ht'" as %(t' & -> & ->).
             eq_pures_l. eq_pures_r.
             clear key tg Hacc.
             iApply (eq_na_open _ _ slot1N); [set_solver|]. iFrame "Hinv1". iIntros "(>HI & Hclose)".
             iDestruct "HI" as (key tg v) "(%Hacc & Hα & Hβ & Hα' & Hβ' & Hkey & Hkey' & Htg & Htg' & Hv & Hv' & Hd & Hd' & Hr & Hac & Hm)".
             destruct v as [b|]; simpl.
             ++ (* decided meanwhile *)
                destruct b.
                { destruct tg as [[m0 t0]|]; last by destruct Hacc. simpl.
                  eq_load_l. eq_pures_l. eq_load_l.
                  eq_load_r. eq_pures_r. eq_load_r. eq_pures_r. eq_load_r. eq_pures_r.
                  iApply eq_na_close_rule. iFrame "Hclose". iSplitR "Hk".
                  { iNext. iExists key, (Some (m0, t0)), (Some true). by iFrame. }
                  iApply (eq_lift_app with "Hk"). iApply eq_lift_same. iApply opt_some. }
                { eq_load_l. eq_pures_l. eq_load_l.
                  eq_load_r. eq_pures_r. eq_load_r. eq_pures_r.
                  iApply eq_na_close_rule. iFrame "Hclose". iSplitR "Hk".
                  { iNext. iExists key, tg, (Some false). by iFrame. }
                  iApply (eq_lift_app with "Hk"). iApply eq_lift_same. iApply opt_none. }
             ++ eq_load_l. eq_pures_l. eq_load_r. eq_pures_r.
                eq_load_l. eq_pures_l. eq_load_r. eq_pures_r.
                destruct tg as [[m0 t0]|]; simpl.
                ** (* tagged: accept iff the pair is the tagged one *)
                   eq_load_l. eq_pures_l. eq_load_r. eq_pures_r.
                   eq_eq_l. eq_eq_r.
                   destruct (decide (m' = m0)) as [<-|Hne].
                   --- rewrite bool_decide_eq_true_2 //. eq_pures_l. eq_pures_r. eq_eq_l. eq_eq_r.
                       destruct (decide (t' = t0)) as [<-|Hne'].
                       +++ rewrite bool_decide_eq_true_2 //. eq_pures_l. eq_pures_r.
                           eq_store_l. eq_pures_l. eq_store_l. eq_pures_l. eq_store_l. eq_pures_l.
                           eq_store_r. eq_pures_r. eq_store_r. eq_pures_r. eq_store_r. eq_pures_r.
                           eq_load_r. eq_pures_r.
                           iApply eq_na_close_rule. iFrame "Hclose". iSplitR "Hk".
                           { iNext. iExists key, (Some (m', t')), (Some true). iFrame. iPureIntro. by eexists. }
                           iApply (eq_lift_app with "Hk"). iApply eq_lift_same. iApply opt_some.
                       +++ rewrite bool_decide_eq_false_2 //. eq_pures_l. eq_pures_r.
                           eq_store_l. eq_pures_l. eq_store_l. eq_pures_l. eq_store_l. eq_pures_l.
                           eq_store_r. eq_pures_r. eq_store_r. eq_pures_r. eq_store_r. eq_pures_r.
                           iApply eq_na_close_rule. iFrame "Hclose". iSplitR "Hk".
                           { iNext. iExists key, (Some (m', t0)), (Some false). by iFrame. }
                           iApply (eq_lift_app with "Hk"). iApply eq_lift_same. iApply opt_none.
                   --- rewrite bool_decide_eq_false_2 //. eq_pures_l. eq_pures_r.
                       eq_store_l. eq_pures_l. eq_store_l. eq_pures_l. eq_store_l. eq_pures_l.
                       eq_store_r. eq_pures_r. eq_store_r. eq_pures_r. eq_store_r. eq_pures_r.
                       iApply eq_na_close_rule. iFrame "Hclose". iSplitR "Hk".
                       { iNext. iExists key, (Some (m0, t0)), (Some false). by iFrame. }
                       iApply (eq_lift_app with "Hk"). iApply eq_lift_same. iApply opt_none.
                ** (* untagged: the key is sampled (in sync) and the pair rejected *)
                   eq_load_l. eq_pures_l. eq_load_r. eq_pures_r.
                   iApply (eq_couple_tapes _ _ _ _ _ _ _ _ [] []).
                   iFrame "Hα Hα'". iIntros (k1) "[Hα Hα']". simpl.
                   iApply (eq_couple_tapes _ _ _ _ _ _ _ _ [] []).
                   iFrame "Hβ Hβ'". iIntros (k2) "[Hβ Hβ']". simpl.
                   eq_rand_l as "%Hk1". eq_pures_l. eq_rand_l as "%Hk2". eq_pures_l.
                   eq_rand_r as "%Hk1'". eq_pures_r. eq_rand_r as "%Hk2'". eq_pures_r.
                   eq_store_l. eq_pures_l. eq_store_r. eq_pures_r.
                   eq_store_l. eq_pures_l. eq_store_l. eq_pures_l. eq_store_l. eq_pures_l.
                   eq_store_r. eq_pures_r. eq_store_r. eq_pures_r. eq_store_r. eq_pures_r.
                   iApply eq_na_close_rule. iFrame "Hclose". iSplitR "Hk".
                   { iNext. iExists (Some (k1, k2)), None, (Some false). by iFrame. }
                   iApply (eq_lift_app with "Hk"). iApply eq_lift_same. iApply opt_none.
  Qed.

  Lemma AUTH_ideal_SIM_F : ⊢ sem_typed [] AUTH_ideal (S_AUTH ∘f F_AUTH)%fac ⊥ (fac MS (τ__F raw chan)) [].
  Proof using All. apply (EQ_sem_typed _ _ _ _ AUTH_SIM_EQ Fwd). Qed.

  Lemma SIM_F_AUTH_ideal : ⊢ sem_typed [] (S_AUTH ∘f F_AUTH)%fac AUTH_ideal ⊥ (fac MS (τ__F raw chan)) [].
  Proof using All. apply (EQ_sem_typed _ _ _ _ AUTH_SIM_EQ Bwd). Qed.
End rel.

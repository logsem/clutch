(* The ideal protocol [AUTH_ideal] (both directions over the ideal MAC) and
   the simulated functionality [S_AUTH ∘f F_AUTH] are related, in both
   directions, exactly.

   Both sessions have the same handler skeleton ([auth_skel], [F_AUTH_eq]);
   [auth_skel_rel] relates two such sessions from relations between their
   handler bodies, so only the bodies are compared here, under an invariant
   per message slot that ties the left MAC instance to the right one and
   [F_AUTH]'s stored message to the tagged one. *)

From iris.proofmode Require Import base proofmode classes.
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

  (* One message slot: the left MAC instance and receiver state, the right
     (simulator's) MAC instance and receiver state, and [F_AUTH]'s stored
     message.  Both MAC instances are in the same state; the left receiver's
     result is the right one's permission applied to the stored message. *)
  Definition slot_inv (αL βL keyL tgL verL decL resL αR βR keyR tgR verR decR accR mR : loc) : iProp Σ :=
    ∃ (key : option (nat * nat)) (tg : option (fingroup.FinGroup.sort vgG * fingroup.FinGroup.sort vgG)) (v : option bool),
      ⌜accb v = true → is_Some tg⌝ ∗
      αL ↪N (n; []) ∗ βL ↪N (n; []) ∗ αR ↪ₛN (n; []) ∗ βR ↪ₛN (n; []) ∗
      keyL ↦ keyv key ∗ keyR ↦ₛ keyv key ∗ tgL ↦ tgv tg ∗ tgR ↦ₛ tgv tg ∗
      verL ↦ verv v ∗ verR ↦ₛ verv v ∗
      decL ↦ #(decb v) ∗ decR ↦ₛ #(decb v) ∗ resL ↦ resv tg v ∗ accR ↦ₛ #(accb v) ∗
      mR ↦ₛ msgv tg.

  (* Calling a port of the network from a handler body at row [ρh]. *)
  Lemma raw_call (θ' ρh : sem_row Σ) (A B : sem_ty Σ) (f1 f2 w1 w2 : val) :
    ⊢ (¡ θ')%R ≤ᵣ ρh -∗ (A -{ θ' }-> B)%T f1 f2 -∗ A w1 w2 -∗
      BREL (f1 w1) ≤ (f2 w2) <|iLblSig_to_iLblThy ρh|> {{ B }}.
  Proof.
    iIntros "#Hρ #Hf Hw".
    iPoseProof (sem_typed_app_fun_nil A B ρh (¡ θ')%R [("w", A)] [] [] (Val f1) (Val f2) "w" "w"
                  with "Hρ [] []") as "#H".
    { iApply sem_typed_sub_nil. iApply sem_typed_var. }
    { iApply sem_typed_val. iModIntro. by iApply ty_le_uarr_mfbang. }
    rewrite /sem_typed /tc_opaque.
    iDestruct ("H" $! {["w" := (w1, w2)]} with "[Hw]") as "H'".
    { rewrite env_sem_typed_cons env_sem_typed_empty. iSplitL; last done.
      iExists _, _. iFrame. by simplify_map_eq. }
    iRevert "H'". rewrite !fmap_insert !fmap_empty /= !lookup_insert /=. iIntros "H'".
    iApply (brel_wand with "H'"). iIntros "!# % % [$ _]".
  Qed.

  (* The same, under evaluation contexts, framing a resource [P] (e.g. the
     handler's continuation) through the call. *)
  Lemma raw_call_k (θ' ρh : sem_row Σ) (A B : sem_ty Σ) (P : iProp Σ) (f1 f2 w1 w2 : val) K1 K2 R :
    (∀ l1s, NeutralEctx l1s K1) → (∀ l2s, NeutralEctx l2s K2) →
    ⊢ (¡ θ')%R ≤ᵣ ρh -∗ (A -{ θ' }-> B)%T f1 f2 -∗ A w1 w2 -∗ P -∗
      □ (∀ v1 v2, B v1 v2 -∗ P -∗ BREL fill K1 (Val v1) ≤ fill K2 (Val v2) <|iLblSig_to_iLblThy ρh|> {{ R }}) -∗
      BREL fill K1 (f1 w1) ≤ fill K2 (f2 w2) <|iLblSig_to_iLblThy ρh|> {{ R }}.
  Proof.
    iIntros (HK1 HK2) "#Hρ #Hf Hw HP #Hc".
    iApply (brel_bind K1 K2); [by iApply traversable_to_iThy|iApply to_iThy_le_refl|].
    iApply (brel_wand _ _ _ (λ v1 v2, B v1 v2 ∗ P)%I with "[Hw HP]"); last first.
    { iIntros "!# % % [HB HP]". iApply ("Hc" with "HB HP"). }
    iApply brel_introduction_mono; first iApply "Hρ".
    iApply (brel_mono_on_prop _ _ _ P with "[] HP").
    { iApply (row_type_sub (ρ := (¡ θ')%R) (τ := λ _ _, P) $! #()%V #()%V). }
    iDestruct (ty_le_uarr_mfbang A B θ' $! f1 f2 with "Hf") as "Hf'".
    rewrite /sem_ty_arr /=. iApply ("Hf'" with "Hw").
  Qed.

  (* The mirrored slot invariant: the simulator and [F_AUTH] on the left,
     the protocol on the right. *)
  Definition slot_inv' (αL βL keyL tgL verL decL accL mL αR βR keyR tgR verR decR resR : loc) : iProp Σ :=
    ∃ (key : option (nat * nat)) (tg : option (fingroup.FinGroup.sort vgG * fingroup.FinGroup.sort vgG)) (v : option bool),
      ⌜accb v = true → is_Some tg⌝ ∗
      αL ↪N (n; []) ∗ βL ↪N (n; []) ∗ αR ↪ₛN (n; []) ∗ βR ↪ₛN (n; []) ∗
      keyL ↦ keyv key ∗ keyR ↦ₛ keyv key ∗ tgL ↦ tgv tg ∗ tgR ↦ₛ tgv tg ∗
      verL ↦ verv v ∗ verR ↦ₛ verv v ∗
      decL ↦ #(decb v) ∗ decR ↦ₛ #(decb v) ∗ resR ↦ₛ resv tg v ∗ accL ↦ #(accb v) ∗
      mL ↦ msgv tg.

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

  Lemma AUTH_ideal_SIM_F : ⊢ sem_typed [] AUTH_ideal (S_AUTH ∘f F_AUTH)%fac ⊥ (fac MS (τ__F raw chan)) [].
  Proof using All.
    iIntros (vs) "!> _". simpl.
    iApply brel_value. iIntros "$ !>". iSplit; last done.
    rewrite /fac /sem_ty_mbang /sem_ty_arr /=. iModIntro.
    iIntros (u1 u2) "[-> ->]".
    rewrite /AUTH_ideal /AUTH_of /S_AUTH F_AUTH_eq.
    brel_pures_l.
    (* the left setup: two MAC instances and the receivers' state *)
    brel_alloctape_l αa as "Hαa". brel_pures_l. brel_alloctape_l βa as "Hβa". brel_pures_l.
    brel_alloc_l keya as "Hkeya". brel_pures_l. brel_alloc_l tga as "Htga". brel_pures_l.
    brel_alloc_l vera as "Hvera". brel_pures_l.
    brel_alloctape_l αb as "Hαb". brel_pures_l. brel_alloctape_l βb as "Hβb". brel_pures_l.
    brel_alloc_l keyb as "Hkeyb". brel_pures_l. brel_alloc_l tgb as "Htgb". brel_pures_l.
    brel_alloc_l verb as "Hverb". brel_pures_l.
    brel_alloc_l dec1 as "Hdec1". brel_pures_l. brel_alloc_l dec2 as "Hdec2". brel_pures_l.
    brel_alloc_l res1 as "Hres1". brel_pures_l. brel_alloc_l res2 as "Hres2". brel_pures_l.
    (* the right setup: [F_AUTH]'s slots, then the simulator's state *)
    brel_pures_r.
    brel_alloc_r m1 as "Hm1". brel_pures_r. brel_alloc_r m2 as "Hm2". brel_pures_r.
    brel_alloctape_r αa' as "Hαa'". brel_pures_r. brel_alloctape_r βa' as "Hβa'". brel_pures_r.
    brel_alloc_r keya' as "Hkeya'". brel_pures_r. brel_alloc_r tga' as "Htga'". brel_pures_r.
    brel_alloc_r vera' as "Hvera'". brel_pures_r.
    brel_alloctape_r αb' as "Hαb'". brel_pures_r. brel_alloctape_r βb' as "Hβb'". brel_pures_r.
    brel_alloc_r keyb' as "Hkeyb'". brel_pures_r. brel_alloc_r tgb' as "Htgb'". brel_pures_r.
    brel_alloc_r verb' as "Hverb'". brel_pures_r.
    brel_alloc_r dec1' as "Hdec1'". brel_pures_r. brel_alloc_r dec2' as "Hdec2'". brel_pures_r.
    brel_alloc_r acc1 as "Hacc1". brel_pures_r. brel_alloc_r acc2 as "Hacc2".
    rewrite !Nat2Z.id.
    iAssert (αa' ↪ₛN (n; []))%I with "[Hαa']" as "Hαa'"; first (iExists []; by iFrame).
    iAssert (βa' ↪ₛN (n; []))%I with "[Hβa']" as "Hβa'"; first (iExists []; by iFrame).
    iAssert (αb' ↪ₛN (n; []))%I with "[Hαb']" as "Hαb'"; first (iExists []; by iFrame).
    iAssert (βb' ↪ₛN (n; []))%I with "[Hβb']" as "Hβb'"; first (iExists []; by iFrame).
    iApply (brel_na_alloc (slot_inv αa βa keya tga vera dec1 res1 αa' βa' keya' tga' vera' dec1' acc1 m1) slot1N).
    iSplitL "Hαa Hβa Hkeya Htga Hvera Hdec1 Hres1 Hαa' Hβa' Hkeya' Htga' Hvera' Hdec1' Hacc1 Hm1".
    { iNext. iExists None, None, None. by iFrame. }
    iIntros "#Hinv1".
    iApply (brel_na_alloc (slot_inv αb βb keyb tgb verb dec2 res2 αb' βb' keyb' tgb' verb' dec2' acc2 m2) slot2N).
    iSplitL "Hαb Hβb Hkeyb Htgb Hverb Hdec2 Hres2 Hαb' Hβb' Hkeyb' Htgb' Hverb' Hdec2' Hacc2 Hm2".
    { iNext. iExists None, None, None. by iFrame. }
    iIntros "#Hinv2".
    brel_pures_r.
    iModIntro. iIntros (θ f1 f2) "Hf".
    brel_pures_l. brel_pures_r.
    iModIntro. iIntros (θ₂ e1 e2) "He". rewrite /raw /sem_ty_prod.
    iDestruct "He" as (w1 w1' w2 w2') "(-> & -> & #Hsnd & #Hrcv)".
    brel_pures_l. brel_pures_r.
    set (va := mac_ideal_v αa βa keya tga vera). set (vb := mac_ideal_v αb βb keyb tgb verb).
    set (va' := mac_ideal_v αa' βa' keya' tga' vera'). set (vb' := mac_ideal_v αb' βb' keyb' tgb' verb').
    set (sc := (λ: "payload", sauth_send_b va' vb' w1')%V).
    set (rc := (λ: "from", sauth_recv_b va' vb' #dec1' #dec2' #acc1 #acc2 w2')%V).
    iApply (sem_typed_inst3 "doLeakSend" "doLeakRecv" "f"
              (pure_ty (λ v1 v2, v1 = w1 ∧ v2 = sc)%type) (pure_ty (λ v1 v2, v1 = w2 ∧ v2 = rc)%type) (clientT θ)
              (auth_skel' (auth_send_h va vb) (auth_recv_h va vb #dec1 #dec2 #res1 #res2))
              (auth_skel' (fauth_send_h #m1 #m2) (fauth_recv_h #m1 #m2))
            with "[] [] [] Hf"); [done|done|done| | done | done].
    iApply (auth_skel_rel with "[] []"); try (intros ??; reflexivity);
      try (rewrite /auth_send_h /auth_recv_h /fauth_send_h /fauth_recv_h /va /vb /mac_ideal_v /ideal_tag_b /ideal_verify_b /tag; is_closed; fail).
    - (* send *)
      iIntros "!>" (ρh) "#Hρ". iIntros (a1 a2 b1 b2 c1 c2) "Ha Hk %Hc". destruct Hc as [-> ->].
      iEval (rewrite /sem_ty_mbang /sem_ty_arr /=) in "Hk".
      iDestruct "Ha" as (x1 x1' y1 y1') "(-> & -> & (%m & -> & ->) & (%d1 & %d2 & [(-> & -> & -> & ->)|(-> & -> & -> & ->)]))".
      all: rewrite /auth_send_h /fauth_send_h /sc /rc /va /vb /va' /vb' /mac_ideal_v /sauth_send_b /ideal_tag_b; simpl; brel_pures_l; brel_pures_r.
      + 
        iApply (brel_na_inv _ _ slot1N); [set_solver|]. iFrame "Hinv1". iIntros "(>HI & Hclose)".
        iDestruct "HI" as (key tg v) "(%Hacc & Hα & Hβ & Hα' & Hβ' & Hkey & Hkey' & Htg & Htg' & Hv & Hv' & Hd & Hd' & Hr & Hac & Hm)".
        destruct tg as [[m0 t0]|]; simpl.
        * (* the slot was used: nothing is sent *)
          brel_load_l. brel_pures_l. brel_load_r. brel_pures_r.
          iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
          { iNext. iExists key, (Some (m0, t0)), v. by iFrame. }
          iApply ("Hk" with "[//]").
        * assert (accb v = false) as Hv0 by (destruct (accb v); [by destruct Hacc|done]).
          brel_load_l. brel_pures_l. brel_load_r. brel_pures_r. brel_store_r. brel_pures_r.
          brel_load_r. brel_pures_r.
          destruct key as [[k1 k2]|]; simpl.
          -- brel_load_l. brel_pures_l. brel_load_r. brel_pures_r. rewrite /tag. brel_pures_l. brel_pures_r.
             brel_exp_l. brel_exp_l. brel_mult_l. brel_pures_l. brel_store_l. brel_pures_l.
             brel_exp_r. brel_exp_r. brel_mult_r. brel_pures_r. brel_store_r. brel_pures_r.
             iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
             { iNext. iExists (Some (k1, k2)), (Some (m, (m ^+ k1 * g ^+ k2)%g)), v. rewrite /resv Hv0. iFrame.
               iPureIntro. by eexists. }
             iApply (raw_call_k θ₂ ρh _ 𝟙 _ _ _ _ _ [AppRCtx _] [AppRCtx _] with "Hρ Hsnd [] Hk"); try (intros; apply _).
             { iApply packet_typed. by (left + right). }
             iIntros "!>" (v1 v2) "[-> ->] Hk". brel_pures_l. brel_pures_r. iApply ("Hk" with "[//]").
          -- iApply (brel_couple_TT _ _ (λ x, x) _ _ _ _ _ _ [] []); first done.
             iFrame "Hβ Hβ'". iIntros (r) "[Hβ Hβ']". simpl.
             brel_load_l. brel_pures_l. brel_rand_l as "%Hr". brel_exp_l. brel_pures_l. brel_store_l. brel_pures_l.
             brel_load_r. brel_pures_r. brel_rand_r as "%Hr'". brel_exp_r. brel_pures_r. brel_store_r. brel_pures_r.
             iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
             { iNext. iExists None, (Some (m, (g ^+ r)%g)), v. rewrite /resv Hv0. iFrame.
               iPureIntro. by eexists. }
             iApply (raw_call_k θ₂ ρh _ 𝟙 _ _ _ _ _ [AppRCtx _] [AppRCtx _] with "Hρ Hsnd [] Hk"); try (intros; apply _).
             { iApply packet_typed. by (left + right). }
             iIntros "!>" (v1 v2) "[-> ->] Hk". brel_pures_l. brel_pures_r. iApply ("Hk" with "[//]").
      + 
        iApply (brel_na_inv _ _ slot2N); [set_solver|]. iFrame "Hinv2". iIntros "(>HI & Hclose)".
        iDestruct "HI" as (key tg v) "(%Hacc & Hα & Hβ & Hα' & Hβ' & Hkey & Hkey' & Htg & Htg' & Hv & Hv' & Hd & Hd' & Hr & Hac & Hm)".
        destruct tg as [[m0 t0]|]; simpl.
        * (* the slot was used: nothing is sent *)
          brel_load_l. brel_pures_l. brel_load_r. brel_pures_r.
          iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
          { iNext. iExists key, (Some (m0, t0)), v. by iFrame. }
          iApply ("Hk" with "[//]").
        * assert (accb v = false) as Hv0 by (destruct (accb v); [by destruct Hacc|done]).
          brel_load_l. brel_pures_l. brel_load_r. brel_pures_r. brel_store_r. brel_pures_r.
          brel_load_r. brel_pures_r.
          destruct key as [[k1 k2]|]; simpl.
          -- brel_load_l. brel_pures_l. brel_load_r. brel_pures_r. rewrite /tag. brel_pures_l. brel_pures_r.
             brel_exp_l. brel_exp_l. brel_mult_l. brel_pures_l. brel_store_l. brel_pures_l.
             brel_exp_r. brel_exp_r. brel_mult_r. brel_pures_r. brel_store_r. brel_pures_r.
             iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
             { iNext. iExists (Some (k1, k2)), (Some (m, (m ^+ k1 * g ^+ k2)%g)), v. rewrite /resv Hv0. iFrame.
               iPureIntro. by eexists. }
             iApply (raw_call_k θ₂ ρh _ 𝟙 _ _ _ _ _ [AppRCtx _] [AppRCtx _] with "Hρ Hsnd [] Hk"); try (intros; apply _).
             { iApply packet_typed. by (left + right). }
             iIntros "!>" (v1 v2) "[-> ->] Hk". brel_pures_l. brel_pures_r. iApply ("Hk" with "[//]").
          -- iApply (brel_couple_TT _ _ (λ x, x) _ _ _ _ _ _ [] []); first done.
             iFrame "Hβ Hβ'". iIntros (r) "[Hβ Hβ']". simpl.
             brel_load_l. brel_pures_l. brel_rand_l as "%Hr". brel_exp_l. brel_pures_l. brel_store_l. brel_pures_l.
             brel_load_r. brel_pures_r. brel_rand_r as "%Hr'". brel_exp_r. brel_pures_r. brel_store_r. brel_pures_r.
             iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
             { iNext. iExists None, (Some (m, (g ^+ r)%g)), v. rewrite /resv Hv0. iFrame.
               iPureIntro. by eexists. }
             iApply (raw_call_k θ₂ ρh _ 𝟙 _ _ _ _ _ [AppRCtx _] [AppRCtx _] with "Hρ Hsnd [] Hk"); try (intros; apply _).
             { iApply packet_typed. by (left + right). }
             iIntros "!>" (v1 v2) "[-> ->] Hk". brel_pures_l. brel_pures_r. iApply ("Hk" with "[//]").
    - (* recv *)
      iIntros "!>" (ρh) "#Hρ". iIntros (a1 a2 b1 b2 c1 c2) "Ha Hk %Hc". destruct Hc as [-> ->].
      iEval (rewrite /sem_ty_mbang /sem_ty_arr /=) in "Hk".
      iDestruct "Ha" as (d1 d2) "[(-> & -> & -> & ->)|(-> & -> & -> & ->)]".
      all: rewrite /auth_recv_h /fauth_recv_h /sc /rc /va /vb /va' /vb' /mac_ideal_v /sauth_recv_b /ideal_verify_b;
        simpl; brel_pures_l; brel_pures_r.
      + (* a receiver [InjL] reads slot 2 *)
        iApply (brel_na_inv _ _ slot2N); [set_solver|]. iFrame "Hinv2". iIntros "(>HI & Hclose)".
        iDestruct "HI" as (key tg v) "(%Hacc & Hα & Hβ & Hα' & Hβ' & Hkey & Hkey' & Htg & Htg' & Hv & Hv' & Hd & Hd' & Hr & Hac & Hm)".
        destruct v as [b|]; simpl.
        * (* already decided *)
          destruct b.
          { destruct tg as [[m0 t0]|]; last by destruct Hacc. simpl.
            brel_load_l. brel_pures_l. brel_load_l.
            brel_load_r. brel_pures_r. brel_load_r. brel_pures_r. brel_load_r. brel_pures_r.
            iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
            { iNext. iExists key, (Some (m0, t0)), (Some true). by iFrame. }
            iApply "Hk". iApply opt_some. }
          { brel_load_l. brel_pures_l. brel_load_l.
            brel_load_r. brel_pures_r. brel_load_r. brel_pures_r.
            iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
            { iNext. iExists key, tg, (Some false). by iFrame. }
            iApply "Hk". iApply opt_none. }
        * brel_load_l. brel_pures_l. brel_load_r. brel_pures_r.
          iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
          { iNext. iExists key, tg, None. by iFrame. }
          iApply (raw_call_k θ₂ ρh _ (Option (𝔾 × 𝔾))%T _ _ _ _ _ [CaseCtx _ _] [AppRCtx _; CaseCtx _ _]
                    with "Hρ Hrcv [] Hk"); try (intros; apply _).
          { iApply from_typed. by (left + right). }
          iIntros "!>" (r1 r2) "(%p1 & %p2 & [(-> & -> & -> & ->)|(-> & -> & Hp)]) Hk".
          -- (* nothing delivered *)
             brel_pures_l. brel_pures_r. iApply "Hk". iApply opt_none.
          -- iDestruct "Hp" as (q1 q1' q2 q2') "(-> & -> & (%m' & -> & ->) & (%t' & -> & ->))".
             brel_pures_l. brel_pures_r.
             clear key tg Hacc.
             iApply (brel_na_inv _ _ slot2N); [set_solver|]. iFrame "Hinv2". iIntros "(>HI & Hclose)".
             iDestruct "HI" as (key tg v) "(%Hacc & Hα & Hβ & Hα' & Hβ' & Hkey & Hkey' & Htg & Htg' & Hv & Hv' & Hd & Hd' & Hr & Hac & Hm)".
             destruct v as [b|]; simpl.
             ++ (* decided meanwhile *)
                destruct b.
                { destruct tg as [[m0 t0]|]; last by destruct Hacc. simpl.
                  brel_load_l. brel_pures_l. brel_load_l.
                  brel_load_r. brel_pures_r. brel_load_r. brel_pures_r. brel_load_r. brel_pures_r.
                  iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
                  { iNext. iExists key, (Some (m0, t0)), (Some true). by iFrame. }
                  iApply "Hk". iApply opt_some. }
                { brel_load_l. brel_pures_l. brel_load_l.
                  brel_load_r. brel_pures_r. brel_load_r. brel_pures_r.
                  iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
                  { iNext. iExists key, tg, (Some false). by iFrame. }
                  iApply "Hk". iApply opt_none. }
             ++ brel_load_l. brel_pures_l. brel_load_r. brel_pures_r.
                brel_load_l. brel_pures_l. brel_load_r. brel_pures_r.
                destruct tg as [[m0 t0]|]; simpl.
                ** (* tagged: accept iff the pair is the tagged one *)
                   brel_load_l. brel_pures_l. brel_load_r. brel_pures_r.
                   brel_eq_l. brel_eq_r.
                   destruct (decide (m' = m0)) as [<-|Hne].
                   --- rewrite bool_decide_eq_true_2 //. brel_pures_l. brel_pures_r. brel_eq_l. brel_eq_r.
                       destruct (decide (t' = t0)) as [<-|Hne'].
                       +++ rewrite bool_decide_eq_true_2 //. brel_pures_l. brel_pures_r.
                           brel_store_l. brel_pures_l. brel_store_l. brel_pures_l. brel_store_l. brel_pures_l.
                           brel_store_r. brel_pures_r. brel_store_r. brel_pures_r. brel_store_r. brel_pures_r.
                           brel_load_r. brel_pures_r.
                           iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
                           { iNext. iExists key, (Some (m', t')), (Some true). iFrame. iPureIntro. by eexists. }
                           iApply "Hk". iApply opt_some.
                       +++ rewrite bool_decide_eq_false_2 //. brel_pures_l. brel_pures_r.
                           brel_store_l. brel_pures_l. brel_store_l. brel_pures_l. brel_store_l. brel_pures_l.
                           brel_store_r. brel_pures_r. brel_store_r. brel_pures_r. brel_store_r. brel_pures_r.
                           iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
                           { iNext. iExists key, (Some (m', t0)), (Some false). by iFrame. }
                           iApply "Hk". iApply opt_none.
                   --- rewrite bool_decide_eq_false_2 //. brel_pures_l. brel_pures_r.
                       brel_store_l. brel_pures_l. brel_store_l. brel_pures_l. brel_store_l. brel_pures_l.
                       brel_store_r. brel_pures_r. brel_store_r. brel_pures_r. brel_store_r. brel_pures_r.
                       iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
                       { iNext. iExists key, (Some (m0, t0)), (Some false). by iFrame. }
                       iApply "Hk". iApply opt_none.
                ** (* untagged: the key is sampled (in sync) and the pair rejected *)
                   brel_load_l. brel_pures_l. brel_load_r. brel_pures_r.
                   iApply (brel_couple_TT _ _ (λ x, x) _ _ _ _ _ _ [] []); first done.
                   iFrame "Hα Hα'". iIntros (k1) "[Hα Hα']". simpl.
                   iApply (brel_couple_TT _ _ (λ x, x) _ _ _ _ _ _ [] []); first done.
                   iFrame "Hβ Hβ'". iIntros (k2) "[Hβ Hβ']". simpl.
                   brel_rand_l as "%Hk1". brel_pures_l. brel_rand_l as "%Hk2". brel_pures_l.
                   brel_rand_r as "%Hk1'". brel_pures_r. brel_rand_r as "%Hk2'". brel_pures_r.
                   brel_store_l. brel_pures_l. brel_store_r. brel_pures_r.
                   brel_store_l. brel_pures_l. brel_store_l. brel_pures_l. brel_store_l. brel_pures_l.
                   brel_store_r. brel_pures_r. brel_store_r. brel_pures_r. brel_store_r. brel_pures_r.
                   iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
                   { iNext. iExists (Some (k1, k2)), None, (Some false). by iFrame. }
                   iApply "Hk". iApply opt_none.
      + (* a receiver [InjR] reads slot 1 *)
        iApply (brel_na_inv _ _ slot1N); [set_solver|]. iFrame "Hinv1". iIntros "(>HI & Hclose)".
        iDestruct "HI" as (key tg v) "(%Hacc & Hα & Hβ & Hα' & Hβ' & Hkey & Hkey' & Htg & Htg' & Hv & Hv' & Hd & Hd' & Hr & Hac & Hm)".
        destruct v as [b|]; simpl.
        * (* already decided *)
          destruct b.
          { destruct tg as [[m0 t0]|]; last by destruct Hacc. simpl.
            brel_load_l. brel_pures_l. brel_load_l.
            brel_load_r. brel_pures_r. brel_load_r. brel_pures_r. brel_load_r. brel_pures_r.
            iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
            { iNext. iExists key, (Some (m0, t0)), (Some true). by iFrame. }
            iApply "Hk". iApply opt_some. }
          { brel_load_l. brel_pures_l. brel_load_l.
            brel_load_r. brel_pures_r. brel_load_r. brel_pures_r.
            iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
            { iNext. iExists key, tg, (Some false). by iFrame. }
            iApply "Hk". iApply opt_none. }
        * brel_load_l. brel_pures_l. brel_load_r. brel_pures_r.
          iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
          { iNext. iExists key, tg, None. by iFrame. }
          iApply (raw_call_k θ₂ ρh _ (Option (𝔾 × 𝔾))%T _ _ _ _ _ [CaseCtx _ _] [AppRCtx _; CaseCtx _ _]
                    with "Hρ Hrcv [] Hk"); try (intros; apply _).
          { iApply from_typed. by (left + right). }
          iIntros "!>" (r1 r2) "(%p1 & %p2 & [(-> & -> & -> & ->)|(-> & -> & Hp)]) Hk".
          -- (* nothing delivered *)
             brel_pures_l. brel_pures_r. iApply "Hk". iApply opt_none.
          -- iDestruct "Hp" as (q1 q1' q2 q2') "(-> & -> & (%m' & -> & ->) & (%t' & -> & ->))".
             brel_pures_l. brel_pures_r.
             clear key tg Hacc.
             iApply (brel_na_inv _ _ slot1N); [set_solver|]. iFrame "Hinv1". iIntros "(>HI & Hclose)".
             iDestruct "HI" as (key tg v) "(%Hacc & Hα & Hβ & Hα' & Hβ' & Hkey & Hkey' & Htg & Htg' & Hv & Hv' & Hd & Hd' & Hr & Hac & Hm)".
             destruct v as [b|]; simpl.
             ++ (* decided meanwhile *)
                destruct b.
                { destruct tg as [[m0 t0]|]; last by destruct Hacc. simpl.
                  brel_load_l. brel_pures_l. brel_load_l.
                  brel_load_r. brel_pures_r. brel_load_r. brel_pures_r. brel_load_r. brel_pures_r.
                  iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
                  { iNext. iExists key, (Some (m0, t0)), (Some true). by iFrame. }
                  iApply "Hk". iApply opt_some. }
                { brel_load_l. brel_pures_l. brel_load_l.
                  brel_load_r. brel_pures_r. brel_load_r. brel_pures_r.
                  iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
                  { iNext. iExists key, tg, (Some false). by iFrame. }
                  iApply "Hk". iApply opt_none. }
             ++ brel_load_l. brel_pures_l. brel_load_r. brel_pures_r.
                brel_load_l. brel_pures_l. brel_load_r. brel_pures_r.
                destruct tg as [[m0 t0]|]; simpl.
                ** (* tagged: accept iff the pair is the tagged one *)
                   brel_load_l. brel_pures_l. brel_load_r. brel_pures_r.
                   brel_eq_l. brel_eq_r.
                   destruct (decide (m' = m0)) as [<-|Hne].
                   --- rewrite bool_decide_eq_true_2 //. brel_pures_l. brel_pures_r. brel_eq_l. brel_eq_r.
                       destruct (decide (t' = t0)) as [<-|Hne'].
                       +++ rewrite bool_decide_eq_true_2 //. brel_pures_l. brel_pures_r.
                           brel_store_l. brel_pures_l. brel_store_l. brel_pures_l. brel_store_l. brel_pures_l.
                           brel_store_r. brel_pures_r. brel_store_r. brel_pures_r. brel_store_r. brel_pures_r.
                           brel_load_r. brel_pures_r.
                           iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
                           { iNext. iExists key, (Some (m', t')), (Some true). iFrame. iPureIntro. by eexists. }
                           iApply "Hk". iApply opt_some.
                       +++ rewrite bool_decide_eq_false_2 //. brel_pures_l. brel_pures_r.
                           brel_store_l. brel_pures_l. brel_store_l. brel_pures_l. brel_store_l. brel_pures_l.
                           brel_store_r. brel_pures_r. brel_store_r. brel_pures_r. brel_store_r. brel_pures_r.
                           iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
                           { iNext. iExists key, (Some (m', t0)), (Some false). by iFrame. }
                           iApply "Hk". iApply opt_none.
                   --- rewrite bool_decide_eq_false_2 //. brel_pures_l. brel_pures_r.
                       brel_store_l. brel_pures_l. brel_store_l. brel_pures_l. brel_store_l. brel_pures_l.
                       brel_store_r. brel_pures_r. brel_store_r. brel_pures_r. brel_store_r. brel_pures_r.
                       iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
                       { iNext. iExists key, (Some (m0, t0)), (Some false). by iFrame. }
                       iApply "Hk". iApply opt_none.
                ** (* untagged: the key is sampled (in sync) and the pair rejected *)
                   brel_load_l. brel_pures_l. brel_load_r. brel_pures_r.
                   iApply (brel_couple_TT _ _ (λ x, x) _ _ _ _ _ _ [] []); first done.
                   iFrame "Hα Hα'". iIntros (k1) "[Hα Hα']". simpl.
                   iApply (brel_couple_TT _ _ (λ x, x) _ _ _ _ _ _ [] []); first done.
                   iFrame "Hβ Hβ'". iIntros (k2) "[Hβ Hβ']". simpl.
                   brel_rand_l as "%Hk1". brel_pures_l. brel_rand_l as "%Hk2". brel_pures_l.
                   brel_rand_r as "%Hk1'". brel_pures_r. brel_rand_r as "%Hk2'". brel_pures_r.
                   brel_store_l. brel_pures_l. brel_store_r. brel_pures_r.
                   brel_store_l. brel_pures_l. brel_store_l. brel_pures_l. brel_store_l. brel_pures_l.
                   brel_store_r. brel_pures_r. brel_store_r. brel_pures_r. brel_store_r. brel_pures_r.
                   iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
                   { iNext. iExists (Some (k1, k2)), None, (Some false). by iFrame. }
                   iApply "Hk". iApply opt_none.
  Qed.

  Lemma SIM_F_AUTH_ideal : ⊢ sem_typed [] (S_AUTH ∘f F_AUTH)%fac AUTH_ideal ⊥ (fac MS (τ__F raw chan)) [].
  Proof using All.
    iIntros (vs) "!> _". simpl.
    iApply brel_value. iIntros "$ !>". iSplit; last done.
    rewrite /fac /sem_ty_mbang /sem_ty_arr /=. iModIntro.
    iIntros (u1 u2) "[-> ->]".
    rewrite /AUTH_ideal /AUTH_of /S_AUTH F_AUTH_eq.
    brel_pures_r.
    (* the left setup: two MAC instances and the receivers' state *)
    brel_alloctape_r αa as "Hαa". brel_pures_r. brel_alloctape_r βa as "Hβa". brel_pures_r.
    brel_alloc_r keya as "Hkeya". brel_pures_r. brel_alloc_r tga as "Htga". brel_pures_r.
    brel_alloc_r vera as "Hvera". brel_pures_r.
    brel_alloctape_r αb as "Hαb". brel_pures_r. brel_alloctape_r βb as "Hβb". brel_pures_r.
    brel_alloc_r keyb as "Hkeyb". brel_pures_r. brel_alloc_r tgb as "Htgb". brel_pures_r.
    brel_alloc_r verb as "Hverb". brel_pures_r.
    brel_alloc_r dec1 as "Hdec1". brel_pures_r. brel_alloc_r dec2 as "Hdec2". brel_pures_r.
    brel_alloc_r res1 as "Hres1". brel_pures_r. brel_alloc_r res2 as "Hres2". brel_pures_r.
    (* the right setup: [F_AUTH]'s slots, then the simulator's state *)
    brel_pures_l.
    brel_alloc_l m1 as "Hm1". brel_pures_l. brel_alloc_l m2 as "Hm2". brel_pures_l.
    brel_alloctape_l αa' as "Hαa'". brel_pures_l. brel_alloctape_l βa' as "Hβa'". brel_pures_l.
    brel_alloc_l keya' as "Hkeya'". brel_pures_l. brel_alloc_l tga' as "Htga'". brel_pures_l.
    brel_alloc_l vera' as "Hvera'". brel_pures_l.
    brel_alloctape_l αb' as "Hαb'". brel_pures_l. brel_alloctape_l βb' as "Hβb'". brel_pures_l.
    brel_alloc_l keyb' as "Hkeyb'". brel_pures_l. brel_alloc_l tgb' as "Htgb'". brel_pures_l.
    brel_alloc_l verb' as "Hverb'". brel_pures_l.
    brel_alloc_l dec1' as "Hdec1'". brel_pures_l. brel_alloc_l dec2' as "Hdec2'". brel_pures_l.
    brel_alloc_l acc1 as "Hacc1". brel_pures_l. brel_alloc_l acc2 as "Hacc2".
    rewrite !Nat2Z.id.
    iAssert (αa ↪ₛN (n; []))%I with "[Hαa]" as "Hαa"; first (iExists []; by iFrame).
    iAssert (βa ↪ₛN (n; []))%I with "[Hβa]" as "Hβa"; first (iExists []; by iFrame).
    iAssert (αb ↪ₛN (n; []))%I with "[Hαb]" as "Hαb"; first (iExists []; by iFrame).
    iAssert (βb ↪ₛN (n; []))%I with "[Hβb]" as "Hβb"; first (iExists []; by iFrame).
    iApply (brel_na_alloc (slot_inv' αa' βa' keya' tga' vera' dec1' acc1 m1 αa βa keya tga vera dec1 res1) slot1N).
    iSplitL "Hαa Hβa Hkeya Htga Hvera Hdec1 Hres1 Hαa' Hβa' Hkeya' Htga' Hvera' Hdec1' Hacc1 Hm1".
    { iNext. iExists None, None, None. by iFrame. }
    iIntros "#Hinv1".
    iApply (brel_na_alloc (slot_inv' αb' βb' keyb' tgb' verb' dec2' acc2 m2 αb βb keyb tgb verb dec2 res2) slot2N).
    iSplitL "Hαb Hβb Hkeyb Htgb Hverb Hdec2 Hres2 Hαb' Hβb' Hkeyb' Htgb' Hverb' Hdec2' Hacc2 Hm2".
    { iNext. iExists None, None, None. by iFrame. }
    iIntros "#Hinv2".
    brel_pures_l.
    iModIntro. iIntros (θ f1 f2) "Hf".
    brel_pures_r. brel_pures_l.
    iModIntro. iIntros (θ₂ e1 e2) "He". rewrite /raw /sem_ty_prod.
    iDestruct "He" as (w1 w1' w2 w2') "(-> & -> & #Hsnd & #Hrcv)".
    brel_pures_r. brel_pures_l.
    set (va := mac_ideal_v αa βa keya tga vera). set (vb := mac_ideal_v αb βb keyb tgb verb).
    set (va' := mac_ideal_v αa' βa' keya' tga' vera'). set (vb' := mac_ideal_v αb' βb' keyb' tgb' verb').
    set (sc := (λ: "payload", sauth_send_b va' vb' w1)%V).
    set (rc := (λ: "from", sauth_recv_b va' vb' #dec1' #dec2' #acc1 #acc2 w2)%V).
    iApply (sem_typed_inst3 "doLeakSend" "doLeakRecv" "f"
              (pure_ty (λ v1 v2, v1 = sc ∧ v2 = w1')%type) (pure_ty (λ v1 v2, v1 = rc ∧ v2 = w2')%type) (clientT θ)
              (auth_skel' (fauth_send_h #m1 #m2) (fauth_recv_h #m1 #m2))
              (auth_skel' (auth_send_h va vb) (auth_recv_h va vb #dec1 #dec2 #res1 #res2))
            with "[] [] [] Hf"); [done|done|done| | done | done].
    iApply (auth_skel_rel with "[] []"); try (intros ??; reflexivity);
      try (rewrite /auth_send_h /auth_recv_h /fauth_send_h /fauth_recv_h /va /vb /mac_ideal_v /ideal_tag_b /ideal_verify_b /tag; is_closed; fail).
    - (* send *)
      iIntros "!>" (ρh) "#Hρ". iIntros (a1 a2 b1 b2 c1 c2) "Ha Hk %Hc". destruct Hc as [-> ->].
      iEval (rewrite /sem_ty_mbang /sem_ty_arr /=) in "Hk".
      iDestruct "Ha" as (x1 x1' y1 y1') "(-> & -> & (%m & -> & ->) & (%d1 & %d2 & [(-> & -> & -> & ->)|(-> & -> & -> & ->)]))".
      all: rewrite /auth_send_h /fauth_send_h /sc /rc /va /vb /va' /vb' /mac_ideal_v /sauth_send_b /ideal_tag_b; simpl; brel_pures_r; brel_pures_l.
      + 
        iApply (brel_na_inv _ _ slot1N); [set_solver|]. iFrame "Hinv1". iIntros "(>HI & Hclose)".
        iDestruct "HI" as (key tg v) "(%Hacc & Hα & Hβ & Hα' & Hβ' & Hkey & Hkey' & Htg & Htg' & Hv & Hv' & Hd & Hd' & Hr & Hac & Hm)".
        destruct tg as [[m0 t0]|]; simpl.
        * (* the slot was used: nothing is sent *)
          brel_load_r. brel_pures_r. brel_load_l. brel_pures_l.
          iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
          { iNext. iExists key, (Some (m0, t0)), v. by iFrame. }
          iApply ("Hk" with "[//]").
        * assert (accb v = false) as Hv0 by (destruct (accb v); [by destruct Hacc|done]).
          brel_load_r. brel_pures_r. brel_load_l. brel_pures_l. brel_store_l. brel_pures_l.
          brel_load_l. brel_pures_l.
          destruct key as [[k1 k2]|]; simpl.
          -- brel_load_r. brel_pures_r. brel_load_l. brel_pures_l. rewrite /tag. brel_pures_r. brel_pures_l.
             brel_exp_r. brel_exp_r. brel_mult_r. brel_pures_r. brel_store_r. brel_pures_r.
             brel_exp_l. brel_exp_l. brel_mult_l. brel_pures_l. brel_store_l. brel_pures_l.
             iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
             { iNext. iExists (Some (k1, k2)), (Some (m, (m ^+ k1 * g ^+ k2)%g)), v. rewrite /resv Hv0. iFrame.
               iPureIntro. by eexists. }
             iApply (raw_call_k θ₂ ρh _ 𝟙 _ _ _ _ _ [AppRCtx _] [AppRCtx _] with "Hρ Hsnd [] Hk"); try (intros; apply _).
             { iApply packet_typed. by (left + right). }
             iIntros "!>" (v1 v2) "[-> ->] Hk". brel_pures_r. brel_pures_l. iApply ("Hk" with "[//]").
          -- iApply (brel_couple_TT _ _ (λ x, x) _ _ _ _ _ _ [] []); first done.
             iFrame "Hβ Hβ'". iIntros (r) "[Hβ Hβ']". simpl.
             brel_load_r. brel_pures_r. brel_rand_r as "%Hr". brel_exp_r. brel_pures_r. brel_store_r. brel_pures_r.
             brel_load_l. brel_pures_l. brel_rand_l as "%Hr'". brel_exp_l. brel_pures_l. brel_store_l. brel_pures_l.
             iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
             { iNext. iExists None, (Some (m, (g ^+ r)%g)), v. rewrite /resv Hv0. iFrame.
               iPureIntro. by eexists. }
             iApply (raw_call_k θ₂ ρh _ 𝟙 _ _ _ _ _ [AppRCtx _] [AppRCtx _] with "Hρ Hsnd [] Hk"); try (intros; apply _).
             { iApply packet_typed. by (left + right). }
             iIntros "!>" (v1 v2) "[-> ->] Hk". brel_pures_r. brel_pures_l. iApply ("Hk" with "[//]").
      + 
        iApply (brel_na_inv _ _ slot2N); [set_solver|]. iFrame "Hinv2". iIntros "(>HI & Hclose)".
        iDestruct "HI" as (key tg v) "(%Hacc & Hα & Hβ & Hα' & Hβ' & Hkey & Hkey' & Htg & Htg' & Hv & Hv' & Hd & Hd' & Hr & Hac & Hm)".
        destruct tg as [[m0 t0]|]; simpl.
        * (* the slot was used: nothing is sent *)
          brel_load_r. brel_pures_r. brel_load_l. brel_pures_l.
          iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
          { iNext. iExists key, (Some (m0, t0)), v. by iFrame. }
          iApply ("Hk" with "[//]").
        * assert (accb v = false) as Hv0 by (destruct (accb v); [by destruct Hacc|done]).
          brel_load_r. brel_pures_r. brel_load_l. brel_pures_l. brel_store_l. brel_pures_l.
          brel_load_l. brel_pures_l.
          destruct key as [[k1 k2]|]; simpl.
          -- brel_load_r. brel_pures_r. brel_load_l. brel_pures_l. rewrite /tag. brel_pures_r. brel_pures_l.
             brel_exp_r. brel_exp_r. brel_mult_r. brel_pures_r. brel_store_r. brel_pures_r.
             brel_exp_l. brel_exp_l. brel_mult_l. brel_pures_l. brel_store_l. brel_pures_l.
             iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
             { iNext. iExists (Some (k1, k2)), (Some (m, (m ^+ k1 * g ^+ k2)%g)), v. rewrite /resv Hv0. iFrame.
               iPureIntro. by eexists. }
             iApply (raw_call_k θ₂ ρh _ 𝟙 _ _ _ _ _ [AppRCtx _] [AppRCtx _] with "Hρ Hsnd [] Hk"); try (intros; apply _).
             { iApply packet_typed. by (left + right). }
             iIntros "!>" (v1 v2) "[-> ->] Hk". brel_pures_r. brel_pures_l. iApply ("Hk" with "[//]").
          -- iApply (brel_couple_TT _ _ (λ x, x) _ _ _ _ _ _ [] []); first done.
             iFrame "Hβ Hβ'". iIntros (r) "[Hβ Hβ']". simpl.
             brel_load_r. brel_pures_r. brel_rand_r as "%Hr". brel_exp_r. brel_pures_r. brel_store_r. brel_pures_r.
             brel_load_l. brel_pures_l. brel_rand_l as "%Hr'". brel_exp_l. brel_pures_l. brel_store_l. brel_pures_l.
             iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
             { iNext. iExists None, (Some (m, (g ^+ r)%g)), v. rewrite /resv Hv0. iFrame.
               iPureIntro. by eexists. }
             iApply (raw_call_k θ₂ ρh _ 𝟙 _ _ _ _ _ [AppRCtx _] [AppRCtx _] with "Hρ Hsnd [] Hk"); try (intros; apply _).
             { iApply packet_typed. by (left + right). }
             iIntros "!>" (v1 v2) "[-> ->] Hk". brel_pures_r. brel_pures_l. iApply ("Hk" with "[//]").
    - (* recv *)
      iIntros "!>" (ρh) "#Hρ". iIntros (a1 a2 b1 b2 c1 c2) "Ha Hk %Hc". destruct Hc as [-> ->].
      iEval (rewrite /sem_ty_mbang /sem_ty_arr /=) in "Hk".
      iDestruct "Ha" as (d1 d2) "[(-> & -> & -> & ->)|(-> & -> & -> & ->)]".
      all: rewrite /auth_recv_h /fauth_recv_h /sc /rc /va /vb /va' /vb' /mac_ideal_v /sauth_recv_b /ideal_verify_b;
        simpl; brel_pures_r; brel_pures_l.
      + (* a receiver [InjL] reads slot 2 *)
        iApply (brel_na_inv _ _ slot2N); [set_solver|]. iFrame "Hinv2". iIntros "(>HI & Hclose)".
        iDestruct "HI" as (key tg v) "(%Hacc & Hα & Hβ & Hα' & Hβ' & Hkey & Hkey' & Htg & Htg' & Hv & Hv' & Hd & Hd' & Hr & Hac & Hm)".
        destruct v as [b|]; simpl.
        * (* already decided *)
          destruct b.
          { destruct tg as [[m0 t0]|]; last by destruct Hacc. simpl.
            brel_load_r. brel_pures_r. brel_load_r.
            brel_load_l. brel_pures_l. brel_load_l. brel_pures_l. brel_load_l. brel_pures_l.
            iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
            { iNext. iExists key, (Some (m0, t0)), (Some true). by iFrame. }
            iApply "Hk". iApply opt_some. }
          { brel_load_r. brel_pures_r. brel_load_r.
            brel_load_l. brel_pures_l. brel_load_l. brel_pures_l.
            iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
            { iNext. iExists key, tg, (Some false). by iFrame. }
            iApply "Hk". iApply opt_none. }
        * brel_load_r. brel_pures_r. brel_load_l. brel_pures_l.
          iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
          { iNext. iExists key, tg, None. by iFrame. }
          iApply (raw_call_k θ₂ ρh _ (Option (𝔾 × 𝔾))%T _ _ _ _ _ [AppRCtx _; CaseCtx _ _] [CaseCtx _ _]
                    with "Hρ Hrcv [] Hk"); try (intros; apply _).
          { iApply from_typed. by (left + right). }
          iIntros "!>" (r1 r2) "(%p1 & %p2 & [(-> & -> & -> & ->)|(-> & -> & Hp)]) Hk".
          -- (* nothing delivered *)
             brel_pures_r. brel_pures_l. iApply "Hk". iApply opt_none.
          -- iDestruct "Hp" as (q1 q1' q2 q2') "(-> & -> & (%m' & -> & ->) & (%t' & -> & ->))".
             brel_pures_r. brel_pures_l.
             clear key tg Hacc.
             iApply (brel_na_inv _ _ slot2N); [set_solver|]. iFrame "Hinv2". iIntros "(>HI & Hclose)".
             iDestruct "HI" as (key tg v) "(%Hacc & Hα & Hβ & Hα' & Hβ' & Hkey & Hkey' & Htg & Htg' & Hv & Hv' & Hd & Hd' & Hr & Hac & Hm)".
             destruct v as [b|]; simpl.
             ++ (* decided meanwhile *)
                destruct b.
                { destruct tg as [[m0 t0]|]; last by destruct Hacc. simpl.
                  brel_load_r. brel_pures_r. brel_load_r.
                  brel_load_l. brel_pures_l. brel_load_l. brel_pures_l. brel_load_l. brel_pures_l.
                  iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
                  { iNext. iExists key, (Some (m0, t0)), (Some true). by iFrame. }
                  iApply "Hk". iApply opt_some. }
                { brel_load_r. brel_pures_r. brel_load_r.
                  brel_load_l. brel_pures_l. brel_load_l. brel_pures_l.
                  iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
                  { iNext. iExists key, tg, (Some false). by iFrame. }
                  iApply "Hk". iApply opt_none. }
             ++ brel_load_r. brel_pures_r. brel_load_l. brel_pures_l.
                brel_load_r. brel_pures_r. brel_load_l. brel_pures_l.
                destruct tg as [[m0 t0]|]; simpl.
                ** (* tagged: accept iff the pair is the tagged one *)
                   brel_load_r. brel_pures_r. brel_load_l. brel_pures_l.
                   brel_eq_r. brel_eq_l.
                   destruct (decide (m' = m0)) as [<-|Hne].
                   --- rewrite bool_decide_eq_true_2 //. brel_pures_r. brel_pures_l. brel_eq_r. brel_eq_l.
                       destruct (decide (t' = t0)) as [<-|Hne'].
                       +++ rewrite bool_decide_eq_true_2 //. brel_pures_r. brel_pures_l.
                           brel_store_r. brel_pures_r. brel_store_r. brel_pures_r. brel_store_r. brel_pures_r.
                           brel_store_l. brel_pures_l. brel_store_l. brel_pures_l. brel_store_l. brel_pures_l.
                           brel_load_l. brel_pures_l.
                           iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
                           { iNext. iExists key, (Some (m', t')), (Some true). iFrame. iPureIntro. by eexists. }
                           iApply "Hk". iApply opt_some.
                       +++ rewrite bool_decide_eq_false_2 //. brel_pures_r. brel_pures_l.
                           brel_store_r. brel_pures_r. brel_store_r. brel_pures_r. brel_store_r. brel_pures_r.
                           brel_store_l. brel_pures_l. brel_store_l. brel_pures_l. brel_store_l. brel_pures_l.
                           iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
                           { iNext. iExists key, (Some (m', t0)), (Some false). by iFrame. }
                           iApply "Hk". iApply opt_none.
                   --- rewrite bool_decide_eq_false_2 //. brel_pures_r. brel_pures_l.
                       brel_store_r. brel_pures_r. brel_store_r. brel_pures_r. brel_store_r. brel_pures_r.
                       brel_store_l. brel_pures_l. brel_store_l. brel_pures_l. brel_store_l. brel_pures_l.
                       iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
                       { iNext. iExists key, (Some (m0, t0)), (Some false). by iFrame. }
                       iApply "Hk". iApply opt_none.
                ** (* untagged: the key is sampled (in sync) and the pair rejected *)
                   brel_load_r. brel_pures_r. brel_load_l. brel_pures_l.
                   iApply (brel_couple_TT _ _ (λ x, x) _ _ _ _ _ _ [] []); first done.
                   iFrame "Hα Hα'". iIntros (k1) "[Hα Hα']". simpl.
                   iApply (brel_couple_TT _ _ (λ x, x) _ _ _ _ _ _ [] []); first done.
                   iFrame "Hβ Hβ'". iIntros (k2) "[Hβ Hβ']". simpl.
                   brel_rand_r as "%Hk1". brel_pures_r. brel_rand_r as "%Hk2". brel_pures_r.
                   brel_rand_l as "%Hk1'". brel_pures_l. brel_rand_l as "%Hk2'". brel_pures_l.
                   brel_store_r. brel_pures_r. brel_store_l. brel_pures_l.
                   brel_store_r. brel_pures_r. brel_store_r. brel_pures_r. brel_store_r. brel_pures_r.
                   brel_store_l. brel_pures_l. brel_store_l. brel_pures_l. brel_store_l. brel_pures_l.
                   iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
                   { iNext. iExists (Some (k1, k2)), None, (Some false). by iFrame. }
                   iApply "Hk". iApply opt_none.
      + (* a receiver [InjR] reads slot 1 *)
        iApply (brel_na_inv _ _ slot1N); [set_solver|]. iFrame "Hinv1". iIntros "(>HI & Hclose)".
        iDestruct "HI" as (key tg v) "(%Hacc & Hα & Hβ & Hα' & Hβ' & Hkey & Hkey' & Htg & Htg' & Hv & Hv' & Hd & Hd' & Hr & Hac & Hm)".
        destruct v as [b|]; simpl.
        * (* already decided *)
          destruct b.
          { destruct tg as [[m0 t0]|]; last by destruct Hacc. simpl.
            brel_load_r. brel_pures_r. brel_load_r.
            brel_load_l. brel_pures_l. brel_load_l. brel_pures_l. brel_load_l. brel_pures_l.
            iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
            { iNext. iExists key, (Some (m0, t0)), (Some true). by iFrame. }
            iApply "Hk". iApply opt_some. }
          { brel_load_r. brel_pures_r. brel_load_r.
            brel_load_l. brel_pures_l. brel_load_l. brel_pures_l.
            iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
            { iNext. iExists key, tg, (Some false). by iFrame. }
            iApply "Hk". iApply opt_none. }
        * brel_load_r. brel_pures_r. brel_load_l. brel_pures_l.
          iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
          { iNext. iExists key, tg, None. by iFrame. }
          iApply (raw_call_k θ₂ ρh _ (Option (𝔾 × 𝔾))%T _ _ _ _ _ [AppRCtx _; CaseCtx _ _] [CaseCtx _ _]
                    with "Hρ Hrcv [] Hk"); try (intros; apply _).
          { iApply from_typed. by (left + right). }
          iIntros "!>" (r1 r2) "(%p1 & %p2 & [(-> & -> & -> & ->)|(-> & -> & Hp)]) Hk".
          -- (* nothing delivered *)
             brel_pures_r. brel_pures_l. iApply "Hk". iApply opt_none.
          -- iDestruct "Hp" as (q1 q1' q2 q2') "(-> & -> & (%m' & -> & ->) & (%t' & -> & ->))".
             brel_pures_r. brel_pures_l.
             clear key tg Hacc.
             iApply (brel_na_inv _ _ slot1N); [set_solver|]. iFrame "Hinv1". iIntros "(>HI & Hclose)".
             iDestruct "HI" as (key tg v) "(%Hacc & Hα & Hβ & Hα' & Hβ' & Hkey & Hkey' & Htg & Htg' & Hv & Hv' & Hd & Hd' & Hr & Hac & Hm)".
             destruct v as [b|]; simpl.
             ++ (* decided meanwhile *)
                destruct b.
                { destruct tg as [[m0 t0]|]; last by destruct Hacc. simpl.
                  brel_load_r. brel_pures_r. brel_load_r.
                  brel_load_l. brel_pures_l. brel_load_l. brel_pures_l. brel_load_l. brel_pures_l.
                  iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
                  { iNext. iExists key, (Some (m0, t0)), (Some true). by iFrame. }
                  iApply "Hk". iApply opt_some. }
                { brel_load_r. brel_pures_r. brel_load_r.
                  brel_load_l. brel_pures_l. brel_load_l. brel_pures_l.
                  iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
                  { iNext. iExists key, tg, (Some false). by iFrame. }
                  iApply "Hk". iApply opt_none. }
             ++ brel_load_r. brel_pures_r. brel_load_l. brel_pures_l.
                brel_load_r. brel_pures_r. brel_load_l. brel_pures_l.
                destruct tg as [[m0 t0]|]; simpl.
                ** (* tagged: accept iff the pair is the tagged one *)
                   brel_load_r. brel_pures_r. brel_load_l. brel_pures_l.
                   brel_eq_r. brel_eq_l.
                   destruct (decide (m' = m0)) as [<-|Hne].
                   --- rewrite bool_decide_eq_true_2 //. brel_pures_r. brel_pures_l. brel_eq_r. brel_eq_l.
                       destruct (decide (t' = t0)) as [<-|Hne'].
                       +++ rewrite bool_decide_eq_true_2 //. brel_pures_r. brel_pures_l.
                           brel_store_r. brel_pures_r. brel_store_r. brel_pures_r. brel_store_r. brel_pures_r.
                           brel_store_l. brel_pures_l. brel_store_l. brel_pures_l. brel_store_l. brel_pures_l.
                           brel_load_l. brel_pures_l.
                           iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
                           { iNext. iExists key, (Some (m', t')), (Some true). iFrame. iPureIntro. by eexists. }
                           iApply "Hk". iApply opt_some.
                       +++ rewrite bool_decide_eq_false_2 //. brel_pures_r. brel_pures_l.
                           brel_store_r. brel_pures_r. brel_store_r. brel_pures_r. brel_store_r. brel_pures_r.
                           brel_store_l. brel_pures_l. brel_store_l. brel_pures_l. brel_store_l. brel_pures_l.
                           iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
                           { iNext. iExists key, (Some (m', t0)), (Some false). by iFrame. }
                           iApply "Hk". iApply opt_none.
                   --- rewrite bool_decide_eq_false_2 //. brel_pures_r. brel_pures_l.
                       brel_store_r. brel_pures_r. brel_store_r. brel_pures_r. brel_store_r. brel_pures_r.
                       brel_store_l. brel_pures_l. brel_store_l. brel_pures_l. brel_store_l. brel_pures_l.
                       iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
                       { iNext. iExists key, (Some (m0, t0)), (Some false). by iFrame. }
                       iApply "Hk". iApply opt_none.
                ** (* untagged: the key is sampled (in sync) and the pair rejected *)
                   brel_load_r. brel_pures_r. brel_load_l. brel_pures_l.
                   iApply (brel_couple_TT _ _ (λ x, x) _ _ _ _ _ _ [] []); first done.
                   iFrame "Hα Hα'". iIntros (k1) "[Hα Hα']". simpl.
                   iApply (brel_couple_TT _ _ (λ x, x) _ _ _ _ _ _ [] []); first done.
                   iFrame "Hβ Hβ'". iIntros (k2) "[Hβ Hβ']". simpl.
                   brel_rand_r as "%Hk1". brel_pures_r. brel_rand_r as "%Hk2". brel_pures_r.
                   brel_rand_l as "%Hk1'". brel_pures_l. brel_rand_l as "%Hk2'". brel_pures_l.
                   brel_store_r. brel_pures_r. brel_store_l. brel_pures_l.
                   brel_store_r. brel_pures_r. brel_store_r. brel_pures_r. brel_store_r. brel_pures_r.
                   brel_store_l. brel_pures_l. brel_store_l. brel_pures_l. brel_store_l. brel_pures_l.
                   iApply brel_na_close. iFrame "Hclose". iSplitR "Hk".
                   { iNext. iExists (Some (k1, k2)), None, (Some false). by iFrame. }
                   iApply "Hk". iApply opt_none.
  Qed.
End rel.

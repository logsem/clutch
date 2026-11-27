(* Rules of the equivalence logic ([eq/]) used to reason about modules:
   reading values of base types, calling the operations of an interface,
   and turning a self-equivalence into a typing. *)

From iris.proofmode Require Import base proofmode classes.
From iris.bi Require Import monpred.
From iris.proofmode Require Import monpred.
From clutch.prelude Require Import fin.
From clutch.prob_eff_lang.probblaze Require Import primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory semantics logic adequacy mode.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_row sem_sig sem_env sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze Require Import valgroup.
From clutch.prob_eff_lang.probblaze.eq Require Import eq_logic eq_valgroup eq_compat.
From clutch.prob_eff_lang.probblaze.uc_eff Require Import modules.

Import fingroup.
Import fingroup.fingroup.
Import valgroup_notation.

#[local] Set Default Proof Using "All".

Section eq_modules.
  Context `{!probblazeRGS Σ}.
  #[local] Open Scope bi_scope.

  Lemma eq_lift_bool vl vr :
    eq_lift (Σ := Σ) sem_ty_bool vl vr ⊣⊢ ∃ b : bool, ⌜vl = #b ∧ vr = #b⌝.
  Proof.
    split=> d. rewrite monPred_at_exist eq_lift_at. setoid_rewrite monPred_at_pure.
    destruct d; rewrite /pick /sem_ty_bool /=; iSplit; iIntros "[%b %H]"; iExists b;
      iPureIntro; naive_solver.
  Qed.

  Lemma eq_lift_option (τ : sem_ty Σ) vl vr :
    ⟪ Option τ ⟫ vl vr ⊣⊢
      ⌜vl = NONEV ∧ vr = NONEV⌝ ∨ ∃ wl wr, ⌜vl = SOMEV wl ∧ vr = SOMEV wr⌝ ∗ ⟪ τ ⟫ wl wr.
  Proof.
    rewrite /sem_ty_option eq_lift_sum. iSplit.
    - iIntros "(%wl & %wr & [(-> & -> & H)|(-> & -> & H)])".
      + iEval (rewrite eq_lift_unit) in "H". iDestruct "H" as %[-> ->]. by iLeft.
      + iRight. iExists _, _. by iFrame.
    - iIntros "[[-> ->]|(%wl & %wr & [-> ->] & H)]".
      + iExists #()%V, #()%V. iLeft. do 2 (iSplit; first done). by iEval (rewrite eq_lift_unit).
      + iExists _, _. iRight. by iFrame.
  Qed.

  Lemma eq_bool (b : bool) : ⊢ ⟪ (𝔹 : sem_ty Σ) ⟫ #b #b.
  Proof. iEval (rewrite eq_lift_bool). by iExists b. Qed.

  (* Both programs diverge. *)
  Lemma eq_loop X R : ⊢ EQ loop #()%V ≈ loop #()%V <|X|> {{ R }}.
  Proof.
    (* One beta step through the definition of [loop] on each side (as
       [wp_rec] does); [eq_pures] would reduce forever. *)
    assert (AsRecV loop "loop" BAnon ("loop" #()%V)%E) as Hrec by done.
    iLöb as "IH".
    iApply (eq_pure_lr _ _ _ _ _ _ _ True True 0 0
              (pure_beta _ _ _ _ _ (AsRecV0 := Hrec)) I
              (pure_beta _ _ _ _ _ (AsRecV0 := Hrec)) I).
    simpl. iApply "IH".
  Qed.

  Lemma eq_loop_ctx Kl Kr X R : ⊢ EQ fill Kl (loop #()%V) ≈ fill Kr (loop #()%V) <|X|> {{ R }}.
  Proof. iApply eq_bind_nil. iApply eq_loop. Qed.

  (* A persistent operation can be used as a one-shot one. *)
  Lemma eq_arr_aff (θ : sem_row Σ) (τ κ : sem_ty Σ) (fl fr : val) :
    ⟪ τ -{ θ }-> κ ⟫ fl fr ⊢ ⟪ τ -{ ¡ θ }-∘ κ ⟫ fl fr.
  Proof.
    iIntros "Hf". iApply eq_lift_arr. iIntros (wl wr) "Hw".
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    iApply (eq_call_frame θ (¡ θ)%R τ κ emp%I fl fr wl wr [] [] with "Hρ Hf Hw []");
      try (intros; apply _); first done.
    iIntros "!>" (vl vr) "H _". iApply eq_value. by iModIntro.
  Qed.

  (* A first-order type: related values are equal and satisfy [φ].  Such
     values can be kept in an invariant as a pure fact. *)
  Definition eq_ground (τ : sem_ty Σ) (φ : val → Prop) : Prop :=
    ∀ vl vr, ⟪ τ ⟫ vl vr ⊣⊢ ⌜vl = vr ∧ φ vl⌝.

  Lemma eq_ground_bool : eq_ground 𝔹 (λ v, ∃ b : bool, v = #b)%type.
  Proof.
    intros vl vr. rewrite eq_lift_bool. iSplit.
    - iIntros "(%b & -> & ->)". iPureIntro. eauto.
    - iIntros "(-> & %b & ->)". by iExists b.
  Qed.

  Lemma eq_ground_prod τ κ φ ψ :
    eq_ground τ φ → eq_ground κ ψ →
    eq_ground (τ × κ) (λ v, ∃ a b, v = (a, b)%V ∧ φ a ∧ ψ b)%type.
  Proof.
    intros Hτ Hκ vl vr. rewrite eq_lift_prod. setoid_rewrite Hτ. setoid_rewrite Hκ. iSplit.
    - iIntros "(%al & %ar & %bl & %br & -> & -> & [-> %Ha] & [-> %Hb])".
      iPureIntro. split; first done. eauto.
    - iIntros "(-> & %a & %b & -> & %Ha & %Hb)".
      iExists a, a, b, b. eauto.
  Qed.

  (* A message box holding a value of a first-order type. *)
  Definition box_rel_gen (φ : val → Prop) (m m' : loc) : iPropD Σ :=
    (m ↦ₗ NONEV ∗ m' ↦ᵣ NONEV) ∨ ∃ x, ⌜φ x⌝ ∗ m ↦ₗ SOMEV x ∗ m' ↦ᵣ SOMEV x.

  (* A Boolean flag, the same on both sides. *)
  Definition bool_ref (l l' : loc) : iPropD Σ := ∃ b : bool, l ↦ₗ #b ∗ l' ↦ᵣ #b.

  (* Reading and writing a flag or a box kept in a non-atomic invariant,
     in one go: open, access, close. *)
  Lemma eq_na_load_bool N l l' Kl Kr X R :
    ⊢ eq_na_inv N (bool_ref l l') -∗
    (∀ b : bool, EQ fill Kl #b ≈ fill Kr #b <|X|> {{ R }}) -∗
    EQ fill Kl (! #l) ≈ fill Kr (! #l') <|X|> {{ R }}.
  Proof.
    iIntros "#Hinv H". iApply (eq_na_open _ _ N); first done. iFrame "Hinv".
    iIntros "[>(%b & Hl & Hl') Hclose]".
    iApply eq_load_l. iFrame "Hl". iIntros "Hl". iApply eq_load_r. iFrame "Hl'". iIntros "Hl'".
    iApply eq_na_close_rule. iFrame "Hclose". iSplitL "Hl Hl'"; first (iNext; iExists b; iFrame).
    iApply "H".
  Qed.

  Lemma eq_na_store_bool N l l' (b : bool) Kl Kr X R :
    ⊢ eq_na_inv N (bool_ref l l') -∗
    EQ fill Kl #()%V ≈ fill Kr #()%V <|X|> {{ R }} -∗
    EQ fill Kl (#l <- #b) ≈ fill Kr (#l' <- #b) <|X|> {{ R }}.
  Proof.
    iIntros "#Hinv H". iApply (eq_na_open _ _ N); first done. iFrame "Hinv".
    iIntros "[>(%b' & Hl & Hl') Hclose]".
    iApply eq_store_l. iFrame "Hl". iIntros "Hl". iApply eq_store_r. iFrame "Hl'". iIntros "Hl'".
    iApply eq_na_close_rule. iFrame "Hclose". iSplitL "Hl Hl'"; first (iNext; iExists b; iFrame).
    iApply "H".
  Qed.

  Lemma eq_na_load_box N φ m m' Kl Kr X R :
    ⊢ eq_na_inv N (box_rel_gen φ m m') -∗
    (∀ w, ⌜w = NONEV ∨ ∃ x, φ x ∧ w = SOMEV x⌝ -∗ EQ fill Kl w ≈ fill Kr w <|X|> {{ R }}) -∗
    EQ fill Kl (! #m) ≈ fill Kr (! #m') <|X|> {{ R }}.
  Proof.
    iIntros "#Hinv H". iApply (eq_na_open _ _ N); first done. iFrame "Hinv".
    iIntros "[>Hb Hclose]".
    iDestruct "Hb" as "[[Hl Hl']|(%x & %Hx & Hl & Hl')]";
      iApply eq_load_l; iFrame "Hl"; iIntros "Hl"; iApply eq_load_r; iFrame "Hl'"; iIntros "Hl'";
      iApply eq_na_close_rule; iFrame "Hclose".
    - iSplitL "Hl Hl'"; first (iNext; iLeft; iFrame). iApply "H". by iLeft.
    - iSplitL "Hl Hl'"; first (iNext; iRight; iExists x; by iFrame). iApply "H". iRight. eauto.
  Qed.

  Lemma eq_na_store_box N φ m m' x Kl Kr X R :
    φ x →
    ⊢ eq_na_inv N (box_rel_gen φ m m') -∗
    EQ fill Kl #()%V ≈ fill Kr #()%V <|X|> {{ R }} -∗
    EQ fill Kl (#m <- SOMEV x) ≈ fill Kr (#m' <- SOMEV x) <|X|> {{ R }}.
  Proof.
    iIntros (Hx) "#Hinv H". iApply (eq_na_open _ _ N); first done. iFrame "Hinv".
    iIntros "[>Hb Hclose]".
    iAssert (∃ v v', m ↦ₗ v ∗ m' ↦ᵣ v')%I with "[Hb]" as (v v') "[Hl Hl']".
    { iDestruct "Hb" as "[[??]|(% & _ & ? & ?)]"; iExists _, _; iFrame. }
    iApply eq_store_l. iFrame "Hl". iIntros "Hl". iApply eq_store_r. iFrame "Hl'". iIntros "Hl'".
    iApply eq_na_close_rule. iFrame "Hclose".
    iSplitL "Hl Hl'"; first (iNext; iRight; iExists x; by iFrame).
    iApply "H".
  Qed.

  (* A points-to of the right-hand program in two halves: one half can
     serve as a token that the location has not yet been written by its
     owner. *)
  Lemma eq_pt_r_half ℓ v : ℓ ↦ᵣ v ⊣⊢ ℓ ↦ᵣ{DfracOwn (1/2)} v ∗ ℓ ↦ᵣ{DfracOwn (1/2)} v.
  Proof.
    split=> d. rewrite monPred_at_sep.
    destruct d; rewrite /eq_pt_r /=; iSplit.
    - iIntros "H". by iDestruct "H" as "[$ $]".
    - iIntros "[H1 H2]". by iCombine "H1 H2" as "H".
    - iIntros "H". by iDestruct "H" as "[$ $]".
    - iIntros "[H1 H2]". by iCombine "H1 H2" as "H".
  Qed.

  (* Related state of the two programs: a flag, and a pair of empty tapes. *)
  Definition flag_rel (s s' : loc) : iPropD Σ := ∃ b : bool, s ↦ₗ #b ∗ s' ↦ᵣ #b.
  Definition tape_rel (N : nat) (α α' : loc) : iPropD Σ := α ↪ₗN (N; []) ∗ α' ↪ᵣN (N; []).

  (* A self-equivalence is a typing. *)
  Lemma eq_val_typed (v : val) (τ : sem_ty Σ) : (⊢ ⟪ τ ⟫ v v) → ⊢ ⊨ᵥ v ≤ v : τ.
  Proof.
    intros [H]. specialize (H Fwd). rewrite monPred_at_emp eq_lift_at /pick /= in H.
    rewrite /sem_val_typed /tc_opaque. iModIntro. by iApply H.
  Qed.

  (* Calling an operation in evaluation contexts, without a frame: at the
     row of the operation itself. *)
  Lemma eq_call m (θ : sem_row Σ) (A B : sem_ty Σ) (fl fr wl wr : val) Kl Kr R :
    (∀ l1s, NeutralEctx l1s Kl) → (∀ l2s, NeutralEctx l2s Kr) →
    ⊢ ⟪ A -{ θ }-[m]-> B ⟫ fl fr -∗ ⟪ A ⟫ wl wr -∗
      □ (∀ vl vr, ⟪ B ⟫ vl vr -∗
           EQ fill Kl (Val vl) ≈ fill Kr (Val vr) <|iLblSig_to_iLblThy θ|> {{ R }}) -∗
      EQ fill Kl (fl wl) ≈ fill Kr (fr wr) <|iLblSig_to_iLblThy θ|> {{ R }}.
  Proof.
    intros ??. iStartProof (iProp _). iIntros (d) "Hf Hw #Hc".
    iEval (rewrite eq_lift_at /sem_ty_mbang) in "Hf". iEval (rewrite eq_lift_at) in "Hw".
    iDestruct (bi.intuitionistically_if_elim with "Hf") as "Hf".
    destruct d; rewrite eq_rel_at /pick /=.
    - iApply brel_bind'; first by iApply traversable_to_iThy.
      rewrite /sem_ty_arr /=. iApply (brel_wand with "[Hf Hw]"); first by iApply "Hf".
      iIntros "!>" (v1 v2) "HB". iApply (eq_rel_at_elim_const Fwd).
      iApply ("Hc" $! v1 v2 with "[HB]"). by rewrite eq_lift_at.
    - iApply brel_bind'; first by iApply traversable_to_iThy.
      rewrite /sem_ty_arr /=. iApply (brel_wand with "[Hf Hw]"); first by iApply "Hf".
      iIntros "!>" (v1 v2) "HB". iApply (eq_rel_at_elim_const Bwd).
      iApply ("Hc" $! v2 v1 with "[HB]"). by rewrite eq_lift_at.
  Qed.

  (* Calling a one-shot (affine) operation, typed at row [¡ θ'], in
     evaluation contexts, keeping a frame [P] across the call. *)
  Lemma brel_call_frame_aff (θ' ρ : sem_row Σ) (A B : sem_ty Σ) (P : iProp Σ)
      (f1 f2 w1 w2 : val) K1 K2 R :
    (∀ l1s, NeutralEctx l1s K1) → (∀ l2s, NeutralEctx l2s K2) →
    ⊢ (¡ θ')%R ≤ᵣ ρ -∗ (A -{ ¡ θ' }-∘ B)%T f1 f2 -∗ A w1 w2 -∗ P -∗
      □ (∀ v1 v2, B v1 v2 -∗ P -∗
           BREL fill K1 (Val v1) ≤ fill K2 (Val v2) <|iLblSig_to_iLblThy ρ|> {{ R }}) -∗
      BREL fill K1 (f1 w1) ≤ fill K2 (f2 w2) <|iLblSig_to_iLblThy ρ|> {{ R }}.
  Proof.
    iIntros (HK1 HK2) "#Hρ Hf Hw HP #Hc".
    iApply (brel_bind K1 K2); [by iApply traversable_to_iThy|iApply to_iThy_le_refl|].
    iApply (brel_wand _ _ _ (λ v1 v2, B v1 v2 ∗ P)%I with "[Hf Hw HP]"); last first.
    { iIntros "!# % % [HB HP]". iApply ("Hc" with "HB HP"). }
    iApply brel_introduction_mono; first iApply "Hρ".
    iApply (brel_mono_on_prop _ _ _ P with "[] HP").
    { iApply (row_type_sub (ρ := (¡ θ')%R) (τ := λ _ _, P) $! #()%V #()%V). }
    rewrite /sem_ty_arr /=. iApply ("Hf" with "Hw").
  Qed.

  Lemma eq_call_frame_aff (θ' ρ : sem_row Σ) (A B : sem_ty Σ) (P : iPropD Σ)
      (fl fr wl wr : val) Kl Kr R :
    (∀ l1s, NeutralEctx l1s Kl) → (∀ l2s, NeutralEctx l2s Kr) →
    ⊢ ⎡(¡ θ')%R ≤ᵣ ρ⎤ -∗ ⟪ A -{ ¡ θ' }-∘ B ⟫ fl fr -∗ ⟪ A ⟫ wl wr -∗ P -∗
      □ (∀ vl vr, ⟪ B ⟫ vl vr -∗ P -∗
           EQ fill Kl (Val vl) ≈ fill Kr (Val vr) <|iLblSig_to_iLblThy ρ|> {{ R }}) -∗
      EQ fill Kl (fl wl) ≈ fill Kr (fr wr) <|iLblSig_to_iLblThy ρ|> {{ R }}.
  Proof.
    intros ??. iStartProof (iProp _). iIntros (d) "#Hρ Hf Hw HP #Hc".
    iEval (rewrite eq_lift_at) in "Hf". iEval (rewrite eq_lift_at) in "Hw".
    destruct d; rewrite eq_rel_at /pick /=.
    - iApply (brel_call_frame_aff θ' ρ A B (P Fwd) with "Hρ Hf Hw HP").
      iIntros "!>" (v1 v2) "HB HP". iApply (eq_rel_at_elim_const Fwd).
      iApply ("Hc" $! v1 v2 with "[HB] HP"). by rewrite eq_lift_at.
    - iApply (brel_call_frame_aff θ' ρ A B (P Bwd) with "Hρ Hf Hw HP").
      iIntros "!>" (v1 v2) "HB HP". iApply (eq_rel_at_elim_const Bwd).
      iApply ("Hc" $! v2 v1 with "[HB] HP"). by rewrite eq_lift_at.
  Qed.

  (* Coupling a [rand] of [l] with a [rand] of [r] along a bijection [f],
     except on one value [a] of [l], at the price of an error credit. *)
  Lemma eq_couple_rand_rand_avoid E N (a : nat) f `{!Bij f} Kl Kr X R z :
    TCEq N (Z.to_nat z) → (∀ n, n < S N → f n < S N)%nat%type → (a < S N)%nat →
    ⎡↯ (1 / S N)⎤ ∗
    (∀ n, ⌜n ≤ N⌝ -∗ ⌜n ≠ a⌝ -∗ EQ fill Kl #n ≈ fill Kr #(f n) @ E <|X|> {{ R }})
    ⊢ EQ fill Kl (rand #z) ≈ fill Kr (rand #z) @ E <|X|> {{ R }}.
  Proof.
    intros HN Hdom Ha. split=> d.
    rewrite monPred_at_sep monPred_at_embed monPred_at_forall eq_rel_at. iIntros "[Herr H]".
    destruct d; rewrite /pick /=.
    - iApply (brel_couple_couple_avoid _ _ [nat_to_fin Ha] f); [apply NoDup_singleton|done|].
      iFrame "Herr". iIntros "!>" (n Hn). iSpecialize ("H" $! (fin_to_nat n)).
      iApply (eq_rel_at_elim Fwd). iApply "H"; iPureIntro.
      + pose proof (fin_to_nat_lt n). lia.
      + intros Heq. apply Hn. assert (n = nat_to_fin Ha) as ->; last by constructor.
        apply fin_to_nat_inj. by rewrite fin_to_nat_to_fin.
    - pose proof (f_inv_bij f).
      iApply (brel_couple_couple_avoid _ _ [nat_to_fin (Hdom a Ha)] (f_inv f));
        [apply NoDup_singleton|intros n Hn; apply (f_inv_restr (S N) f Hdom n Hn)|].
      iFrame "Herr". iIntros "!>" (m Hm). iSpecialize ("H" $! (f_inv f (fin_to_nat m))).
      rewrite f_inv_cancel_r.
      iApply (eq_rel_at_elim Bwd). iApply "H"; iPureIntro.
      + pose proof (f_inv_restr (S N) f Hdom m (fin_to_nat_lt m)). lia.
      + intros Heq. apply Hm. assert (m = nat_to_fin (Hdom a Ha)) as ->; last by constructor.
        apply fin_to_nat_inj. by rewrite fin_to_nat_to_fin -Heq f_inv_cancel_r.
  Qed.

End eq_modules.

Section eq_modules_group.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  #[local] Open Scope bi_scope.

  (* A message box: empty, or holding the same group element. *)
  Definition box_rel (m m' : loc) : iPropD Σ :=
    (m ↦ₗ NONEV ∗ m' ↦ᵣ NONEV) ∨ ∃ x : vgG, m ↦ₗ SOMEV (vgval x) ∗ m' ↦ᵣ SOMEV (vgval x).

  Lemma eq_none : ⊢ ⟪ Option 𝔾 ⟫ NONEV NONEV.
  Proof. iApply eq_lift_option. by iLeft. Qed.

  Lemma eq_some (x y : vgG) : x = y → ⊢ ⟪ Option 𝔾 ⟫ (SOMEV (vgval x)) (SOMEV (vgval y)).
  Proof.
    intros ->. iApply eq_lift_option. iRight. iExists _, _. iSplit; first done.
    iApply eq_lift_group. by iExists y.
  Qed.

  Lemma eq_group_val (x y : vgG) : x = y → ⊢ ⟪ 𝔾 ⟫ (vgval x) (vgval y).
  Proof. intros ->. iApply eq_lift_group. by iExists y. Qed.

  Lemma eq_ground_group : eq_ground 𝔾 (λ v, ∃ x : vgG, v = vgval x)%type.
  Proof.
    intros vl vr. rewrite eq_lift_group. iSplit.
    - iIntros "(%x & -> & ->)". iPureIntro. eauto.
    - iIntros "(-> & %x & ->)". by iExists x.
  Qed.

End eq_modules_group.

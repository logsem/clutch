(* Oblivious transfer reversal with both parties honest is perfect.

   The simulator runs the real parties on dummy inputs, so both programs
   run the same party code against the same OT and channel, with Alice's
   bits and Bob's choice replaced on the right.  The proof relates the
   two runs location by location: one invariant for each location that
   one party writes once (the OT's [ch] and [mm], the channel's [box]),
   either not yet written on both sides or written with related values.
   The writer proves it has not written yet with half of the right-hand
   points-to ([eq_pt_r_half]).  Bob's mask is coupled with the dummy Bob's
   mask, so that the dummy Alice's message is Alice's. *)

From iris.proofmode Require Import base proofmode classes.
From iris.bi Require Import monpred.
From iris.proofmode Require Import monpred.
From clutch Require Import stdpp_ext.
From iris.base_logic.lib Require Import na_invariants.
From clutch.prob_eff_lang.probblaze Require Import primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory semantics logic adequacy mode.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_row sem_sig sem_env sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze.eq Require Import eq_logic eq_valgroup eq_compat.
From clutch.prob_eff_lang.probblaze.uc Require Import advantage uc_advantage.
From clutch.prob_eff_lang.probblaze.uc_eff Require Import modules eq_modules auth ot ot_rev.

Import fingroup.
Import fingroup.fingroup.
Import valgroup_notation.

#[local] Set Default Proof Using "All".

Section ot_rev_eq.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  #[local] Open Scope bi_scope.

  Definition NT : namespace := nroot .@ "to".

  Definition gb (b : bool) : vgG := if b then g else 1%g.

  Lemma bd_gg : bool_decide ((g : vgG) = g) = true.
  Proof. by apply bool_decide_eq_true_2. Qed.
  Lemma bd_1g : bool_decide ((1%g : vgG) = g) = false.
  Proof.
    apply bool_decide_eq_false_2. intros H.
    have Hg := @g_nontriv _ vgg. rewrite -H order1 in Hg. done.
  Qed.
  Lemma bd_gb b : bool_decide (gb b = g) = b.
  Proof. destruct b; [apply bd_gg|apply bd_1g]. Qed.

  (* Alice's message, [x0 ⊕ r ⊕ (s ∧ c)] for [s = x0 ⊕ x1]: the
     channel's content on both sides, and the dummy Bob's mask. *)
  Definition tmsg (x0 x1 r c : bool) : bool := xorb x0 (xorb r (xorb x0 x1 && c)).

  (* Alice has chosen in the OT; then her bits are recorded. *)
  Definition inv_ch (ch ch' xs : loc) : iPropD Σ :=
    (ch ↦ₗ #false ∗ ch' ↦ᵣ{DfracOwn (1/2)} #false) ∨
    (ch ↦ₗ□ #true ∗ ch' ↦ᵣ□ #true ∗ ∃ x0 x1 : bool, xs ↦ᵣ□ SOMEV (#x0, #x1)%V).

  (* The invariants quantify over the values in the heap, with a pure
     condition on them, so that closing them frames the points-to facts
     and leaves the condition to [solve_ok]. *)

  (* Bob's OT messages [(v0, v1) = (gbit r, gbit r1)], for his mask [r]
     and choice [r ⊕ r1], and the dummy Bob's [(w, w) = (gbit ρ, gbit ρ)]
     for [ρ] Alice's message. *)
  Definition mm_ok (x0 x1 : bool) (v0 v1 w : val) : Prop :=
    (∃ r r1 : bool, v0 = vgval (gb r) ∧ v1 = vgval (gb r1) ∧
      w = vgval (gb (tmsg x0 x1 r (xorb r r1))))%type.

  Definition inv_mm (mm mm' xs : loc) : iPropD Σ :=
    (mm ↦ₗ NONEV ∗ mm' ↦ᵣ{DfracOwn (1/2)} NONEV) ∨
    (∃ (x0 x1 : bool) (v0 v1 w : val), xs ↦ᵣ□ SOMEV (#x0, #x1)%V ∗
       mm ↦ₗ□ SOMEV (v0, v1)%V ∗ mm' ↦ᵣ□ SOMEV (w, w)%V ∗ ⌜mm_ok x0 x1 v0 v1 w⌝).

  (* Alice's message [m], the same on both sides. *)
  Definition box_ok (x0 x1 : bool) (v0 v1 : val) (m : bool) : Prop :=
    (∃ r r1 : bool, v0 = vgval (gb r) ∧ v1 = vgval (gb r1) ∧ m = tmsg x0 x1 r (xorb r r1))%type.

  Definition inv_box (box box' xs mm : loc) : iPropD Σ :=
    (box ↦ₗ NONEV ∗ box' ↦ᵣ{DfracOwn (1/2)} NONEV) ∨
    (∃ (x0 x1 : bool) (v0 v1 : val) (m : bool), xs ↦ᵣ□ SOMEV (#x0, #x1)%V ∗
       mm ↦ₗ□ SOMEV (v0, v1)%V ∗ box ↦ₗ□ SOMEV #m ∗ box' ↦ᵣ□ SOMEV #m ∗
       ⌜box_ok x0 x1 v0 v1 m⌝).

  (* The conditions for concrete bits: try the four pairs [(r, r1)]. *)
  Ltac solve_ok :=
    rewrite /mm_ok /box_ok;
    first [ exists true, true; split_and!; done
          | exists true, false; split_and!; done
          | exists false, true; split_and!; done
          | exists false, false; split_and!; done ].

  Lemma gb_val_inj a b : vgval (gb a) = vgval (gb b) → a = b.
  Proof. intros H%vgval_inj. rewrite -(bd_gb a) -(bd_gb b) H //. Qed.

  Lemma gb_true : g = gb true.
  Proof. done. Qed.
  Lemma gb_false : 1%g = gb false.
  Proof. done. Qed.
  Lemma gbv_true : vgval g = vgval (gb true).
  Proof. done. Qed.
  Lemma gbv_false : vgval 1 = vgval (gb false).
  Proof. done. Qed.

  Lemma hyb_ideal_TO_H_EQ :
    ⊢ EQ HYB_TO_H ≈ IDEAL_TO_H <|iLblSig_to_iLblThy (⊥ : sem_row Σ)|>
        {{ ⟪ Mod TOHNet TPorts ⟫ }}.
  Proof.
    iApply eq_value. iModIntro. rewrite /Mod /ModM. iEval (rewrite eq_lift_forall). iIntros (θ).
    iModIntro. iApply eq_lift_arr. iIntros (advl advr) "Hadv".
    rewrite /TOHNet /OTHAdv /LNet. iEval (rewrite eq_lift_prod) in "Hadv".
    iDestruct "Hadv" as (otl otr nl nr) "(-> & -> & Hot & Hnet)".
    iEval (rewrite eq_lift_prod) in "Hnet".
    iDestruct "Hnet" as (lkl lkr dll dlr) "(-> & -> & #Hleak & #Hdeliver)".
    iEval (rewrite eq_lift_prod) in "Hot".
    iDestruct "Hot" as (ysl ysr yrl yrr) "(-> & -> & Hrun_s & Hrun_r)".
    rewrite /IDEAL_TO_H /S_TO_H /HYB_TO_H /comp_op /tens_op /PARTIES_TO /F_OT_H /F_OAUTH
      /F_TO_H /DUMMY_TO /TO_S /TO_R /bxor /ungbit /gbit /ot_rev.flip is_unit.
    eq_pures_l. eq_alloc_l ch as "Hch". eq_pures_l. eq_alloc_l mm as "Hmm". eq_pures_l.
    eq_alloc_l box as "Hbox". eq_pures_l.
    eq_pures_r. eq_alloc_r ch' as "Hch'". eq_pures_r. eq_alloc_r mm' as "Hmm'". eq_pures_r.
    eq_alloc_r box' as "Hbox'". eq_pures_r. eq_alloc_r xs as "Hxs". eq_pures_r.
    iDestruct (eq_pt_r_half with "Hch'") as "[Hch' HchA]".
    iDestruct (eq_pt_r_half with "Hmm'") as "[Hmm' HmmB]".
    iDestruct (eq_pt_r_half with "Hbox'") as "[Hbox' HboxA]".
    iApply (eq_na_alloc (inv_ch ch ch' xs) (NT .@ "ch")).
    iSplitL "Hch Hch'"; first (iNext; iLeft; iFrame). iIntros "#Ich".
    iApply (eq_na_alloc (inv_mm mm mm' xs) (NT .@ "mm")).
    iSplitL "Hmm Hmm'"; first (iNext; iLeft; iFrame). iIntros "#Imm".
    iApply (eq_na_alloc (inv_box box box' xs mm) (NT .@ "box")).
    iSplitL "Hbox Hbox'"; first (iNext; iLeft; iFrame). iIntros "#Ibox".
    iApply eq_value. iModIntro. rewrite /TPorts /TSPort /TPort. iEval (rewrite eq_lift_prod).
    iExists _, _, _, _. do 2 (iSplit; first done).
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    iSplitL "HchA HboxA Hxs Hrun_r".
    - (* Alice: her bits; the dummy Alice's are [(false, false)] *)
      iApply eq_lift_arr. iIntros (xl xr) "Hx".
      iEval (rewrite eq_lift_prod) in "Hx".
      iDestruct "Hx" as (x0l x0r x1l x1r) "(-> & -> & Hx0 & Hx1)".
      iEval (rewrite eq_lift_bool) in "Hx0". iDestruct "Hx0" as %(x0 & -> & ->).
      iEval (rewrite eq_lift_bool) in "Hx1". iDestruct "Hx1" as %(x1 & -> & ->).
      destruct x0, x1; (eq_pures';
        (* the functionality records her bits *)
        eq_store_r; iMod (eq_pt_r_persist with "Hxs") as "#Hxs"; eq_pures';
        (* her OT choice *)
        iApply (eq_na_open _ _ (NT .@ "ch")); try done; iFrame "Ich"; iIntros "[>H Hclose]";
        (iDestruct "H" as "[[Hch Hch'] | (_ & #Hch' & _)]";
           [|by iDestruct (eq_pt_r_agree with "HchA Hch'") as %?]);
        iDestruct (eq_pt_r_half with "[$Hch' $HchA]") as "Hch'";
        eq_store_l; eq_store_r;
        iMod (eq_pt_l_persist with "Hch") as "#Hch"; iMod (eq_pt_r_persist with "Hch'") as "#Hch'";
        iApply eq_na_close_rule; iFrame "Hclose";
        (iSplitR; [iNext; iRight; iFrame "Hch Hch'"; iExists _, _; iFrame "Hxs"|]);
        eq_pures';
        (* the OT runs her until Bob's OT messages are there *)
        eq_reshape_l (yrl _); eq_reshape_r (yrr _);
        (iApply (eq_call_frame_aff θ (¡ θ)%R 𝟙%T 𝟙%T (box' ↦ᵣ{DfracOwn (1/2)} NONEV)%I
                   with "Hρ Hrun_r [] HboxA");
           try (intros; apply _); [by iEval (rewrite eq_lift_unit)|]);
        iIntros "!>" (??) "Hu HboxA"; iEval (rewrite eq_lift_unit) in "Hu";
        iDestruct "Hu" as %[-> ->];
        eq_pures';
        iApply (eq_na_open _ _ (NT .@ "mm")); try done; iFrame "Imm"; iIntros "[>H Hclose]";
        iDestruct "H" as "[[Hmm Hmm'] | (%y0 & %y1 & %v0 & %v1 & %w & #Hxs' & #Hmm & #Hmm' & %Hok)]";
        [ (* not yet: both diverge *)
          eq_load_l; eq_load_r; iApply eq_na_close_rule; iFrame "Hclose";
          iSplitL "Hmm Hmm'"; [iNext; iLeft; iFrame|];
          eq_pures'; eq_reshape_l (loop _); eq_reshape_r (loop _); iApply eq_loop_ctx
        | (* Bob has sent: Alice sends her message *)
          iDestruct (eq_pt_r_agree with "Hxs Hxs'") as %?; simplify_eq;
          eq_load_l; eq_load_r; iApply eq_na_close_rule; iFrame "Hclose";
          iSplitR; [iNext; iRight; iExists _, _, _, _, _; iFrame "Hxs' Hmm Hmm'"; done|];
          destruct Hok as (r & r1 & -> & -> & ->); destruct r, r1;
          (eq_pures'; rewrite ?bd_gb ?bd_gg ?bd_1g; cbn [tmsg xorb andb negb]; eq_pures';
           iApply (eq_na_open _ _ (NT .@ "box")); try done; iFrame "Ibox"; iIntros "[>H Hclose]";
           (iDestruct "H" as "[[Hbox Hbox'] | (% & % & % & % & % & _ & _ & _ & #Hbox' & _)]";
              [|by iDestruct (eq_pt_r_agree with "HboxA Hbox'") as %?]);
           iDestruct (eq_pt_r_half with "[$Hbox' $HboxA]") as "Hbox'";
           eq_store_l; eq_store_r;
           iMod (eq_pt_l_persist with "Hbox") as "#Hbox"; iMod (eq_pt_r_persist with "Hbox'") as "#Hbox'";
           iApply eq_na_close_rule; iFrame "Hclose";
           (iSplitR; [iNext; iRight; iExists _, _, _, _, _; iFrame "Hxs' Hmm Hbox Hbox'";
                      iPureIntro; solve_ok|]);
           eq_pures';
           eq_reshape_l (lkl _); eq_reshape_r (lkr _);
           (iApply (eq_call_frame θ (¡ θ)%R 𝔹%T 𝟙%T emp%I with "Hρ Hleak [] []");
              try (intros; apply _); [iApply eq_bool|done|]);
           iIntros "!>" (??) "Hu _"; by iApply eq_value) ]).
    - (* Bob: his choice; the dummy Bob's is [false] *)
      iApply eq_lift_arr. iIntros (cvl cvr) "Hc".
      iEval (rewrite eq_lift_bool) in "Hc". iDestruct "Hc" as %(c & -> & ->).
      eq_pures'.
      (* the OT runs him until Alice has chosen *)
      eq_reshape_l (ysl _). eq_reshape_r (ysr _).
      iApply (eq_call_frame_aff θ (¡ θ)%R 𝟙%T (𝟙 -{ ¡ θ }-∘ 𝟙)%T (mm' ↦ᵣ{DfracOwn (1/2)} NONEV)%I
                with "Hρ Hrun_s [] HmmB");
        try (intros; apply _); first by iEval (rewrite eq_lift_unit).
      iIntros "!>" (s2l s2r) "Hs2 HmmB".
      eq_pures'.
      iApply (eq_na_open _ _ (NT .@ "ch")); first done. iFrame "Ich". iIntros "[>H Hclose]".
      iDestruct "H" as "[[Hch Hch'] | (#Hch & #Hch' & %x0 & %x1 & #Hxs)]".
      { (* not yet: both diverge *)
        eq_load_l. eq_load_r. iApply eq_na_close_rule. iFrame "Hclose".
        iSplitL "Hch Hch'"; first (iNext; iLeft; iFrame).
        eq_pures'. eq_reshape_l (loop _). eq_reshape_r (loop _). iApply eq_loop_ctx. }
      eq_load_l. eq_load_r. iApply eq_na_close_rule. iFrame "Hclose".
      iSplitR; first (iNext; iRight; iFrame "Hch Hch'"; iExists _, _; iFrame "Hxs").
      eq_pures'.
      (* his mask, coupled with the dummy Bob's *)
      eq_focus_l (rand #_)%E; eq_focus_r (rand #_)%E.
      iApply (eq_couple_rand_rand_bij _ _ (bmask (xorb x0 (xorb x0 x1 && c)))); first by apply bmask_lt.
      iIntros (k Hk).
      assert (k = 0%nat ∨ k = 1%nat)%type as [-> | ->] by (simpl in Hk; lia); destruct x0, x1, c;
        (simpl; eq_pures';
         (* his OT messages *)
         iApply (eq_na_open _ _ (NT .@ "mm")); try done; iFrame "Imm"; iIntros "[>H Hclose]";
         (iDestruct "H" as "[[Hmm Hmm'] | (% & % & % & % & % & _ & _ & #Hmm' & _)]";
            [|by iDestruct (eq_pt_r_agree with "HmmB Hmm'") as %?]);
         iDestruct (eq_pt_r_half with "[$Hmm' $HmmB]") as "Hmm'";
         eq_store_l; eq_store_r;
         iMod (eq_pt_l_persist with "Hmm") as "#Hmm"; iMod (eq_pt_r_persist with "Hmm'") as "#Hmm'";
         iApply eq_na_close_rule; iFrame "Hclose";
         (iSplitR; [iNext; iRight; iExists _, _, _, _, _; iFrame "Hxs Hmm Hmm'"; iPureIntro; solve_ok|]);
         eq_pures';
         eq_reshape_l (s2l _); eq_reshape_r (s2r _);
         (iApply (eq_call_frame_aff θ (¡ θ)%R 𝟙%T 𝟙%T emp%I with "Hρ Hs2 [] []");
            try (intros; apply _); [by iEval (rewrite eq_lift_unit)|done|]);
         iIntros "!>" (??) "Hu _"; iEval (rewrite eq_lift_unit) in "Hu"; iDestruct "Hu" as %[-> ->];
         eq_pures';
         (* wait for Alice's message *)
         iLöb as "IH";
         eq_reshape_l (dll _); eq_reshape_r (dlr _);
         (iApply (eq_call_frame θ (¡ θ)%R 𝟙%T 𝟙%T emp%I with "Hρ Hdeliver [] []");
            try (intros; apply _); [by iEval (rewrite eq_lift_unit)|done|]);
         iIntros "!>" (??) "Hu _"; iEval (rewrite eq_lift_unit) in "Hu"; iDestruct "Hu" as %[-> ->];
         eq_pures';
         iApply (eq_na_open _ _ (NT .@ "box")); try done; iFrame "Ibox"; iIntros "[>H Hclose]";
         iDestruct "H" as "[[Hbox Hbox'] | (%y0 & %y1 & %v0 & %v1 & %m & #Hxs' & #Hmmq & #Hbox & #Hbox' & %Hok)]";
         [ (* not yet *)
           eq_load_l; eq_load_r; iApply eq_na_close_rule; iFrame "Hclose";
           iSplitL "Hbox Hbox'"; [iNext; iLeft; iFrame|];
           eq_pures_lr; try (try eq_pures_l); try (try eq_pures_r); iApply "IH"
         | (* Alice has sent: Bob unmasks her message *)
           iDestruct (eq_pt_r_agree with "Hxs Hxs'") as %?; simplify_eq;
           iDestruct (eq_pt_l_agree with "Hmm Hmmq") as %?; simplify_eq;
           eq_load_l; eq_load_r; iApply eq_na_close_rule; iFrame "Hclose";
           iSplitR; [iNext; iRight; iExists _, _, _, _, _; iFrame "Hxs' Hmmq Hbox Hbox'"; done|];
           destruct Hok as (q & q1 & Hq & Hq1 & ->);
           rewrite ?gbv_false ?gb_true in Hq Hq1; apply gb_val_inj in Hq, Hq1; subst;
           simpl; eq_pures'; eq_load_r; eq_pures';
           iApply eq_value; iModIntro; iApply eq_bool ]).
  Qed.

End ot_rev_eq.

Section ot_rev_security.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context `{Hpre : probblazeRGpreS Σ}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.

  Theorem to_h_security : to_h_secure.
  Proof.
    intros A HA.
    apply (advantage_zero _ _ _ _ (λ H : probblazeRGS Σ, Mod TOHNet TPorts));
      [exact HA| |]; intros HRGS;
      [apply (EQ_sem_typed _ _ ⊥ _ hyb_ideal_TO_H_EQ Fwd)
      |apply (EQ_sem_typed _ _ ⊥ _ hyb_ideal_TO_H_EQ Bwd)].
  Qed.

End ot_rev_security.

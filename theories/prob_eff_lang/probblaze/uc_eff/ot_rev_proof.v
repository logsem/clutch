(* Oblivious transfer reversal with both parties honest is perfect
   (uc_eff/DESIGN.md, section 6).

   The two ports share state, so the proof is an invariant over four
   stages; Bob's mask is coupled with the bit the simulator leaks as
   Alice's message.  A party proves it has not yet made its move with half
   of a points-to it alone writes ([eq_pt_r_half]). *)

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

  (* The state of the two programs.  Left: the OT's [ch] and [mm], the
     channel's [box].  Right: the simulator's [rho] (Alice's message),
     [ain] (Alice has her input), [bsent] (Bob has sent), and the
     transfer's [xs], [cs], [fin].  The simulator's [alast] (Alice's next
     move is her last) and [bgo] (Bob's next move is to send) are owned by
     Alice and Bob.  Alice holds half of [xs] and of [fin], Bob half of
     [cs], until they write them: the other half is in the invariant.
     The stages: nobody has started; Alice has her input [(x0, x1)]; Bob
     has sent his OT messages [(gbit r, gbit r1)], for his mask [r] and
     choice [r ⊕ r1]; Alice has sent her message. *)
  Definition to_inv (ch mm box rho ain bsent xs cs fin : loc) : iPropD Σ :=
    (ch ↦ₗ #false ∗ mm ↦ₗ NONEV ∗ box ↦ₗ NONEV ∗ (∃ v, rho ↦ᵣ v) ∗
       ain ↦ᵣ #false ∗ bsent ↦ᵣ #false ∗
       xs ↦ᵣ{DfracOwn (1/2)} NONEV ∗ cs ↦ᵣ{DfracOwn (1/2)} #false ∗ fin ↦ᵣ{DfracOwn (1/2)} #false) ∨
    (∃ x0 x1 : bool, ch ↦ₗ□ #true ∗ xs ↦ᵣ□ SOMEV (#x0, #x1)%V ∗ ain ↦ᵣ #true ∗
      ((mm ↦ₗ NONEV ∗ box ↦ₗ NONEV ∗ (∃ v, rho ↦ᵣ v) ∗ bsent ↦ᵣ #false ∗
          cs ↦ᵣ{DfracOwn (1/2)} #false ∗ fin ↦ᵣ{DfracOwn (1/2)} #false) ∨
       (∃ r r1 : bool,
          mm ↦ₗ□ SOMEV (vgval (gb r), vgval (gb r1))%V ∗ cs ↦ᵣ□ #true ∗ bsent ↦ᵣ□ #true ∗
          (∃ ρ : bool, rho ↦ᵣ□ #ρ ∗ ⌜ρ = xorb (xorb x0 (xorb x0 x1 && xorb r r1)) r⌝) ∗
          ((box ↦ₗ NONEV ∗ fin ↦ᵣ{DfracOwn (1/2)} #false) ∨
           ((∃ m : bool, box ↦ₗ□ SOMEV #m ∗ ⌜m = xorb (xorb x0 (xorb x0 x1 && xorb r r1)) r⌝) ∗
              fin ↦ᵣ□ #true))))).

  (* Before Bob has sent, [bsent] is [false], whatever Alice has done. *)
  Lemma to_inv_bsent ch mm box rho ain bsent xs cs fin :
    ⊢ to_inv ch mm box rho ain bsent xs cs fin -∗ cs ↦ᵣ{DfracOwn (1/2)} #false -∗
    bsent ↦ᵣ #false ∗ cs ↦ᵣ{DfracOwn (1/2)} #false ∗
    (bsent ↦ᵣ #false -∗ to_inv ch mm box rho ain bsent xs cs fin).
  Proof.
    iIntros "H HcsB".
    iDestruct "H" as "[(Hch & Hmm & Hbox & Hrho & Hain & Hbs & Hxs & Hcs & Hfin)|(%x0 & %x1 & #Hch & #Hxs & Hain & [(Hmm & Hbox & Hrho & Hbs & Hcs & Hfin)|(%r & %r1 & _ & #Hcs & _)])]".
    - iFrame "Hbs HcsB". iIntros "Hbs". iLeft. iFrame.
    - iFrame "Hbs HcsB". iIntros "Hbs". iRight. iExists _, _. iFrame "Hch Hxs Hain". iLeft. iFrame.
    - by iDestruct (eq_pt_r_agree with "HcsB Hcs") as %?.
  Qed.

  Lemma gb_val_inj a b : vgval (gb a) = vgval (gb b) → a = b.
  Proof. intros H%vgval_inj. rewrite -(bd_gb a) -(bd_gb b) H //. Qed.

  Lemma gb_true : g = gb true.
  Proof. done. Qed.
  Lemma gb_false : 1%g = gb false.
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
    iDestruct "Hot" as (ysl ysr yrl yrr) "(-> & -> & #Hyield_s & #Hyield_r)".
    rewrite /HYB_TO_H /IDEAL_TO_H /comp_op /tens_op /PARTIES_TO /F_OT_H /F_OAUTH /F_TO_H /S_TO_H
      /TO_S /TO_R /bxor /ungbit /gbit /ot_rev.flip is_unit.
    eq_pures_l. eq_alloc_l ch as "Hch". eq_pures_l. eq_alloc_l mm as "Hmm". eq_pures_l.
    eq_alloc_l box as "Hbox". eq_pures_l.
    eq_pures_r. eq_alloc_r rho as "Hrho". eq_pures_r. eq_alloc_r ain as "Hain". eq_pures_r.
    eq_alloc_r alast as "Halast". eq_pures_r. eq_alloc_r bgo as "Hbgo". eq_pures_r.
    eq_alloc_r bsent as "Hbs". eq_pures_r.
    eq_alloc_r xs as "Hxs". eq_pures_r.
    eq_alloc_r cs as "Hcs". eq_pures_r. eq_alloc_r fin as "Hfin". eq_pures_r.
    iDestruct (eq_pt_r_half with "Hxs") as "[Hxs HxsA]".
    iDestruct (eq_pt_r_half with "Hcs") as "[Hcs HcsB]".
    iDestruct (eq_pt_r_half with "Hfin") as "[Hfin HfinA]".
    iApply (eq_na_alloc (to_inv ch mm box rho ain bsent xs cs fin) NT).
    iSplitL "Hch Hmm Hbox Hrho Hain Hbs Hxs Hcs Hfin"; first (iNext; iLeft; iFrame).
    iIntros "#Hinv".
    iApply eq_value. iModIntro. rewrite /TPorts /TSPort /TPort. iEval (rewrite eq_lift_prod).
    iExists _, _, _, _. do 2 (iSplit; first done).
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    iSplitL "HxsA HfinA Halast".
    - (* Alice: her input *)
      iApply eq_lift_arr. iIntros (xl xr) "Hx".
      iEval (rewrite eq_lift_prod) in "Hx".
      iDestruct "Hx" as (x0l x0r x1l x1r) "(-> & -> & Hx0 & Hx1)".
      iEval (rewrite eq_lift_bool) in "Hx0". iDestruct "Hx0" as %(x0 & -> & ->).
      iEval (rewrite eq_lift_bool) in "Hx1". iDestruct "Hx1" as %(x1 & -> & ->).
      destruct x0, x1; (eq_pures';
        iApply (eq_na_open _ _ NT); try done; iFrame "Hinv"; iIntros "[>H Hclose]";
        (iDestruct "H" as "[(Hch & Hmm & Hbox & Hrho & Hain & Hbs & Hxs & Hcs & Hfin)|(%y0 & %y1 & _ & #Hxs' & _)]";
           [|by iDestruct (eq_pt_r_agree with "HxsA Hxs'") as %?]);
        iDestruct (eq_pt_r_half with "[$Hxs $HxsA]") as "Hxs";
        eq_store_l; eq_store_r;
        iMod (eq_pt_l_persist with "Hch") as "#Hch"; iMod (eq_pt_r_persist with "Hxs") as "#Hxs";
        (* her first move: the simulator records her input *)
        eq_pures'; eq_load_r; eq_pures'; eq_store_r; eq_pures';
        iApply eq_na_close_rule; iFrame "Hclose";
        (iSplitL "Hmm Hbox Hrho Hain Hbs Hcs Hfin";
           [iNext; iRight; iExists _, _; iFrame "Hch Hxs Hain"; iLeft; iFrame|]);
        (* wait for Bob's OT messages *)
        iLöb as "IH";
        eq_reshape_l (yrl _); eq_reshape_r (yrr _);
        (iApply (eq_call_frame θ (¡ θ)%R 𝟙%T 𝟙%T
                   (fin ↦ᵣ{DfracOwn (1/2)} #false ∗ alast ↦ᵣ #false)%I
                   with "Hρ Hyield_r [] [$HfinA $Halast]");
           try (intros; apply _); [by iEval (rewrite eq_lift_unit)|]);
        iIntros "!>" (??) "Hu [HfinA Halast]"; iEval (rewrite eq_lift_unit) in "Hu";
        iDestruct "Hu" as %[-> ->];
        eq_pures';
        iApply (eq_na_open _ _ NT); try done; iFrame "Hinv"; iIntros "[>H Hclose]";
        iDestruct "H" as "[(Hch' & _)|(%y0 & %y1 & _ & #Hxs' & Hain & [(Hmm & Hbox & Hrho & Hbs & Hcs & Hfin)|(%r & %r1 & #Hmm & #Hcs & #Hbs & #Hrho & [(Hbox & Hfin)|(_ & #Hfin)])])]";
        [ (* nobody has started: no, Alice has *)
          by iDestruct (eq_pt_l_agree with "Hch Hch'") as %?
        | (* Bob has not sent yet: Alice's next move is to wait again *)
          eq_load_r; eq_pures'; eq_load_r; eq_load_l;
          eq_pures_lr; eq_pures'; eq_load_r; eq_pures'; eq_store_r; eq_pures';
          iApply eq_na_close_rule; iFrame "Hclose";
          iSplitL "Hmm Hbox Hrho Hain Hbs Hcs Hfin";
          [iNext; iRight; iExists _, _; iFrame "Hch Hxs' Hain"; iLeft; iFrame
          |iApply ("IH" with "HfinA Halast")]
        | (* Bob has sent: Alice sends her message *)
          iDestruct (eq_pt_r_agree with "Hxs Hxs'") as %?; simplify_eq;
          eq_load_r; eq_pures'; eq_store_r; eq_pures'; eq_load_r; eq_load_l;
          eq_pures'; rewrite bd_gb; eq_pures';
          iDestruct (eq_pt_r_half with "[$Hfin $HfinA]") as "Hfin";
          eq_store_l; eq_store_r;
          iMod (eq_pt_l_persist with "Hbox") as "#Hbox"; iMod (eq_pt_r_persist with "Hfin") as "#Hfin";
          iDestruct "Hrho" as (ρ) "[#Hrho' %Hρ]";
          eq_pures'; eq_load_r; eq_pures'; eq_load_r; eq_pures';
          iApply eq_na_close_rule; iFrame "Hclose";
          iSplitL "Hain";
          [iNext; iRight; iExists _, _; iFrame "Hch Hxs' Hain"; iRight; iExists r, r1;
           iFrame "Hmm Hcs Hbs"; iSplitR; [by iExists ρ; iFrame "Hrho'"|];
           iRight; iFrame "Hfin"; iExists _; iFrame "Hbox";
           iPureIntro; by destruct r, r1
          |eq_reshape_l (lkl _); eq_reshape_r (lkr _);
           (iApply (eq_call_frame θ (¡ θ)%R 𝔹%T 𝟙%T emp%I with "Hρ Hleak [] []");
              try (intros; apply _);
              [iEval (rewrite eq_lift_bool); iExists _; iPureIntro; split; [done|rewrite Hρ; by destruct r, r1]
              |done|]);
           iIntros "!>" (??) "Hu _"; by iApply eq_value]
        | (* Alice has sent: no, she has not *)
          by iDestruct (eq_pt_r_agree with "HfinA Hfin") as %? ]).
    - (* Bob: his choice *)
      iApply eq_lift_arr. iIntros (cvl cvr) "Hc".
      iEval (rewrite eq_lift_bool) in "Hc". iDestruct "Hc" as %(c & -> & ->).
      eq_pures'.
      (* wait for Alice's input *)
      iLöb as "IH".
      iApply (eq_na_open _ _ NT); first done. iFrame "Hinv". iIntros "[>H Hclose]".
      iDestruct (to_inv_bsent with "H HcsB") as "(Hbs & HcsB & Hback)".
      eq_load_r. iDestruct ("Hback" with "Hbs") as "H".
      iApply eq_na_close_rule. iFrame "Hclose". iSplitL "H"; first by iNext.
      eq_pures'. eq_load_r. eq_pures'.
      eq_reshape_l (ysl _). eq_reshape_r (ysr _).
      iApply (eq_call_frame θ (¡ θ)%R 𝟙%T 𝟙%T
                (cs ↦ᵣ{DfracOwn (1/2)} #false ∗ bgo ↦ᵣ #false)%I
                with "Hρ Hyield_s [] [$HcsB $Hbgo]");
        try (intros; apply _); first by iEval (rewrite eq_lift_unit).
      iIntros "!>" (??) "Hu [HcsB Hbgo]". iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
      eq_pures'.
      iApply (eq_na_open _ _ NT); first done. iFrame "Hinv". iIntros "[>H Hclose]".
      iDestruct "H" as "[(Hch & Hmm & Hbox & Hrho & Hain & Hbs & Hxs & Hcs & Hfin)|(%x0 & %x1 & #Hch & #Hxs & Hain & [(Hmm & Hbox & Hrho & Hbs & Hcs & Hfin)|(%r & %r1 & _ & #Hcs & _)])]";
        [ (* not yet *)
          eq_load_r; eq_pures'; eq_load_r; eq_load_l; iApply eq_na_close_rule; iFrame "Hclose";
          iSplitL "Hch Hmm Hbox Hrho Hain Hbs Hxs Hcs Hfin"; [iNext; iLeft; iFrame|];
          eq_pures_lr; eq_pures'; iApply ("IH" with "Hbgo HcsB")
        |
        | (* Bob has sent already: no *)
          by iDestruct (eq_pt_r_agree with "HcsB Hcs") as %? ].
      (* Alice has her input: Bob's next move is to send his OT messages *)
      eq_load_r. eq_pures'. eq_store_r. eq_pures'. eq_load_r. eq_load_l. eq_pures'.
      iDestruct (eq_pt_r_half with "[$Hcs $HcsB]") as "Hcs".
      eq_store_r. iMod (eq_pt_r_persist with "Hcs") as "#Hcs". eq_pures'.
      eq_load_r. eq_pures'. eq_load_r. eq_pures'.
      eq_focus_l (rand #_)%E; eq_focus_r (rand #_)%E.
      iApply (eq_couple_rand_rand_bij _ _ (bmask (xorb x0 (xorb x0 x1 && c)))); first by apply bmask_lt.
      iIntros (k Hk). iDestruct "Hrho" as (v) "Hrho".
      assert (k = 0%nat ∨ k = 1%nat)%type as [-> | ->] by (simpl in Hk; lia); destruct c;
        (simpl; eq_pures';
         eq_store_l; eq_store_r; eq_pures'; eq_store_r;
         iEval (rewrite ?gb_true ?gb_false) in "Hmm";
         iMod (eq_pt_l_persist with "Hmm") as "#Hmm"; iMod (eq_pt_r_persist with "Hrho") as "#Hrho";
         iMod (eq_pt_r_persist with "Hbs") as "#Hbs";
         iApply eq_na_close_rule; iFrame "Hclose";
         iSplitL "Hain Hbox Hfin";
         [iNext; iRight; iExists _, _; iFrame "Hch Hxs Hain"; iRight; iExists _, _; iFrame "Hmm Hcs Hbs";
          iSplitR; [iExists _; iFrame "Hrho"; iPureIntro; by destruct x0, x1|iLeft; iFrame]|];
         eq_pures';
         (* the OT messages go out *)
         eq_reshape_l (ysl _); eq_reshape_r (ysr _);
         (iApply (eq_call_frame θ (¡ θ)%R 𝟙%T 𝟙%T emp%I with "Hρ Hyield_s [] []");
            try (intros; apply _); [by iEval (rewrite eq_lift_unit)|done|]);
         iIntros "!>" (??) "Hu _"; iEval (rewrite eq_lift_unit) in "Hu"; iDestruct "Hu" as %[-> ->];
         eq_pures'; eq_load_r; eq_pures';
         (* wait for Alice's message *)
         iClear "IH"; iLöb as "IH";
         eq_reshape_l (dll _); eq_reshape_r (dlr _);
         (iApply (eq_call_frame θ (¡ θ)%R 𝟙%T 𝟙%T emp%I with "Hρ Hdeliver [] []");
            try (intros; apply _); [by iEval (rewrite eq_lift_unit)|done|]);
         iIntros "!>" (??) "Hu _"; iEval (rewrite eq_lift_unit) in "Hu"; iDestruct "Hu" as %[-> ->];
         eq_pures';
         iApply (eq_na_open _ _ NT); try done; iFrame "Hinv"; iIntros "[>H Hclose]";
         iDestruct "H" as "[(_ & _ & _ & _ & _ & _ & Hxs0 & _)|(%y0 & %y1 & #Hch' & #Hxs' & Hain & [(Hmm0 & _)|(%r' & %r1' & #Hmm' & #Hcs' & #Hbs' & #Hrho' & [(Hbox & Hfin)|(#Hbox & #Hfin)])])]";
         [ (* nobody has started: no *)
           by iDestruct (eq_pt_r_agree with "Hxs Hxs0") as %?
         | (* Bob has not sent: no *)
           by iDestruct (eq_pt_l_agree with "Hmm Hmm0") as %?
         | (* Alice has not sent yet *)
           eq_load_l; eq_load_r; iApply eq_na_close_rule; iFrame "Hclose";
           iSplitL "Hain Hbox Hfin";
           [iNext; iRight; iExists y0, y1; iFrame "Hch' Hxs' Hain"; iRight; iExists r', r1';
            iFrame "Hmm' Hcs' Hbs' Hrho'"; iLeft; iFrame
           |eq_pures_lr; eq_pures'; eq_load_r; eq_pures'; iApply "IH"]
         | (* Alice has sent: Bob unmasks her message *)
           iDestruct "Hbox" as (m) "[#Hbox' %Hm]";
           eq_load_l; eq_load_r; iApply eq_na_close_rule; iFrame "Hclose";
           iSplitL "Hain";
           [iNext; iRight; iExists y0, y1; iFrame "Hch' Hxs' Hain"; iRight; iExists r', r1';
            iFrame "Hmm' Hcs' Hbs' Hrho'"; iRight; iFrame "Hfin"; iExists m; by iFrame "Hbox'"
           |];
           iDestruct (eq_pt_r_agree with "Hxs Hxs'") as %?; simplify_eq;
           iDestruct (eq_pt_l_agree with "Hmm Hmm'") as %Hmmeq;
           injection Hmmeq as Hr Hr1; rewrite ?gb_true ?gb_false in Hr Hr1; apply gb_val_inj in Hr, Hr1; subst;
           destruct y0, y1; simpl; eq_pures'; iApply eq_value; iApply eq_bool ]).
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

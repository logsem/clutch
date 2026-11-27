(* Security of oblivious transfer with both parties honest
   (uc_eff/DESIGN.md, section 6).

   Four steps from the real module [REAL_OT_H = HYB1_OT_H DDH_rand] to the
   ideal module [F_OT_H ⊳ S_OT_H]:

   A. [hyb1_ddh]: the real reference string, a random DDH tuple, against a
      real one (decryption mode): the DDH advantage of [RED1_OT_H A].
   B. [hyb1_hyb2_EQ]: in decryption mode, the real parties are the hybrid
      whose receiver's message and ciphertexts are built from one DDH
      tuple by rerandomisation, when [y ≠ 0]: [1/n].
   C. [hyb2_ddh]: that tuple real against random: the DDH advantage of
      [RED2_OT_H A].
   D. [hyb2_ideal_EQ]: with a random tuple the ciphertexts are encryptions
      of random elements, which the simulator produces, when the tuple's
      [p ≠ 0] (so [u ≠ 1]) and [c ≠ p q]: [2/n]. *)

From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From iris.bi Require Import monpred.
From iris.proofmode Require Import monpred.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory semantics logic adequacy mode.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_row sem_sig sem_env sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze.eq Require Import eq_logic eq_valgroup eq_compat.
From clutch.prob_eff_lang.probblaze.uc Require Import advantage uc_advantage.
From clutch.prob_eff_lang.probblaze.uc_eff Require Import modules eq_modules auth ot ot_eq ot_arith.

Import fingroup.
Import fingroup.fingroup.
Import valgroup_notation.

#[local] Set Default Proof Using "All".

Section hyb2_pure.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.

Lemma HYB2_app_pure (dh : val) : rtc pure_step (HYB2_app dh) (HYB2_OT_H dh).
Proof.
  rewrite /HYB2_app /HYB2_OT_H.
  eapply rtc_l.
  { apply nsteps_once_inv, (pure_exec (φ := True)); done. }
  simpl. eapply rtc_l.
  { apply nsteps_once_inv, (pure_exec (φ := True)); done. }
  done.
Qed.

End hyb2_pure.

Section ot_h_eq.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.

  #[local] Notation n := (S (S n'')).
  Context `{n_prime : is_true (prime.prime n)}.
  #[local] Open Scope bi_scope.

  Definition NB : namespace := nroot .@ "otB".

  (* The state of step B.  Left: the boxes of the channels [brs_l] (the
     receiver's message) and [bsr_l] (the ciphertexts); right: the same,
     the tuple [tup] and the sender's messages [mm].  The receiver holds
     half of [tup], the sender half of [mm], until they write them.  The
     stages: nothing sent; the receiver has sent [u = g^P], [v = u^x] and
     the tuple is [(g^(P Q), g^Q, g^P)]; the sender has also sent the
     ciphertexts, [(g^t0, m0 u^t0)] and [(g1^t1, m1 u^t1)] (or, if
     [u = 1], nothing). *)
  Definition inv_B (X Y : Fn) (brs_l bsr_l brs_r bsr_r tup mm : loc) : iPropD Σ :=
    (brs_l ↦ₗ NONEV ∗ brs_r ↦ᵣ NONEV ∗ bsr_l ↦ₗ NONEV ∗ bsr_r ↦ᵣ NONEV ∗
       tup ↦ᵣ{DfracOwn (1/2)} NONEV ∗ mm ↦ᵣ{DfracOwn (1/2)} NONEV) ∨
    (∃ (u v C B A : vgG) (P Q : Fn),
       brs_l ↦ₗ□ SOMEV (vgval u, vgval v)%V ∗ brs_r ↦ᵣ□ SOMEV (vgval u, vgval v)%V ∗
       tup ↦ᵣ□ SOMEV (vgval C, vgval B, vgval A)%V ∗
       ⌜u = gexp P ∧ v = gexp (Fmul P X) ∧ A = gexp P ∧ B = gexp Q ∧ C = gexp (Fmul P Q)⌝ ∗
       ((bsr_l ↦ₗ NONEV ∗ bsr_r ↦ᵣ NONEV ∗
           (mm ↦ᵣ{DfracOwn (1/2)} NONEV ∨ ∃ w, mm ↦ᵣ□ SOMEV w)) ∨
        (∃ (m0 m1 c0 d0 c1 d1 : vgG) (t0 t1 : Fn),
           bsr_l ↦ₗ□ SOMEV (vgval c0, vgval d0, (vgval c1, vgval d1))%V ∗
           bsr_r ↦ᵣ□ SOMEV (vgval c0, vgval d0, (vgval c1, vgval d1))%V ∗
           mm ↦ᵣ□ SOMEV (vgval m0, vgval m1)%V ∗
           ⌜c0 = gexp t0 ∧ d0 = (m0 * gexp (Fmul P t0))%g ∧
            c1 = gexp (Fmul Y t1) ∧ d1 = (m1 * gexp (Fmul P t1))%g⌝))).

  (* Step B. *)
  Lemma hyb1_hyb2_EQ :
    ⎡↯ (1 / n)⎤ ⊢ ⟪ ModA OTHNet OTPorts ⟫ (HYB1_OT_H DDH_real) (HYB2_OT_H DDH_real).
  Proof.
    iIntros "He". rewrite /ModA /ModM. iEval (rewrite eq_lift_forall). iIntros (θ).
    rewrite eq_lift_mbang /=.
    iApply eq_lift_arr. iIntros (advl advr) "Hadv".
    rewrite /OTHNet /Pub /LNet. iEval (rewrite eq_lift_prod) in "Hadv".
    iDestruct "Hadv" as (pl pr nl nr) "(-> & -> & #Hpub & Hnets)".
    iEval (rewrite eq_lift_prod) in "Hnets".
    iDestruct "Hnets" as (rsl rsr srl srr) "(-> & -> & Hrs & Hsr)".
    iEval (rewrite eq_lift_prod) in "Hrs".
    iDestruct "Hrs" as (lrsl lrsr drsl drsr) "(-> & -> & #Hleak_rs & #Hdeliver_rs)".
    iEval (rewrite eq_lift_prod) in "Hsr".
    iDestruct "Hsr" as (lsrl lsrr dsrl dsrr) "(-> & -> & #Hleak_sr & #Hdeliver_sr)".
    rewrite /HYB1_OT_H /HYB2_OT_H /HYB2_body /comp_op /tens_op /PARTIES_OT /F_CRS_DH /DDH_real
      /F_OAUTH /OT_S /OT_R /sample /dec /enc is_unit.
    eq_pures_l. eq_pures_r.
    (* The reference string, the same on both sides, with [y ≠ 0]. *)
    couple_along (λ x : nat, x) avoiding 0%nat; [intros; lia|lia|].
    iFrame "He". iIntros (y Hy Hnz). simpl. eq_pures'.
    eq_couple_rand_rand. iIntros (x Hx). simpl. eq_pures'.
    (* Publish it; the channels and the hybrid's state. *)
    eq_reshape_l (pl _). eq_reshape_r (pr _).
    iApply (eq_call MS ⟨⟩%R Crs 𝟙%T with "Hpub"); try (intros; apply _); first iApply eq_crs.
    iIntros "!>" (wl wr) "_". simpl. eq_pures'.
    eq_alloc_l brs_l as "Hbrs_l". eq_pures_l. eq_alloc_l bsr_l as "Hbsr_l". eq_pures_l.
    eq_alloc_r brs_r as "Hbrs_r". eq_pures_r. eq_alloc_r bsr_r as "Hbsr_r". eq_pures_r.
    eq_alloc_r tup as "Htup". eq_pures_r. eq_alloc_r mm as "Hmm". eq_pures_r.
    iDestruct (eq_pt_r_half with "Htup") as "[Htup HtupR]".
    iDestruct (eq_pt_r_half with "Hmm") as "[Hmm HmmS]".
    iApply (eq_na_alloc (inv_B (expF x) (expF y) brs_l bsr_l brs_r bsr_r tup mm) NB).
    iSplitL "Hbrs_l Hbrs_r Hbsr_l Hbsr_r Htup Hmm"; first (iNext; iLeft; iFrame).
    iIntros "#Hinv".
    iApply eq_value. iModIntro. rewrite /OTPorts /SPort /RPort. iEval (rewrite eq_lift_prod).
    iExists _, _, _, _. do 2 (iSplit; first done).
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    iSplitL "HmmS".
    - (* The sender. *)
      iApply eq_lift_arr. iIntros (wl' wr') "Hw".
      iEval (rewrite eq_lift_unit) in "Hw". iDestruct "Hw" as %[-> ->].
      eq_pures'.
      (* Wait for the receiver's message. *)
      iLöb as "IH".
      eq_reshape_l (drsl _). eq_reshape_r (drsr _).
      iApply (eq_call_frame θ (¡ θ)%R 𝟙%T 𝟙%T (mm ↦ᵣ{DfracOwn (1/2)} NONEV)%I
                with "Hρ Hdeliver_rs [] HmmS");
        try (intros; apply _); first by iEval (rewrite eq_lift_unit).
      iIntros "!>" (??) "Hu HmmS". iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
      eq_pures'.
      iApply (eq_na_open _ _ NB); first done. iFrame "Hinv". iIntros "[>H Hclose]".
      iDestruct "H" as "[(Hbrs_l & Hbrs_r & Hrest)|(%u & %v & %C & %B & %A & %P & %Q & #Hbrs_l & #Hbrs_r & #Htup & %Hf & Hrest)]".
      { (* not yet *)
        eq_load_l. eq_load_r. iApply eq_na_close_rule. iFrame "Hclose".
        iSplitL "Hbrs_l Hbrs_r Hrest"; first (iNext; iLeft; iFrame).
        eq_pures_lr. eq_pures'. iApply ("IH" with "HmmS"). }
      eq_load_l. eq_load_r. iApply eq_na_close_rule. iFrame "Hclose".
      iSplitL "Hrest".
      { iNext. iRight. iExists u, v, C, B, A, P, Q. iFrame "Hbrs_l Hbrs_r Htup Hrest". by iPureIntro. }
      eq_pures'.
      (* Second phase: the messages. *)
      iApply eq_value. iModIntro. iApply eq_lift_arr. iIntros (ml mr) "Hm".
      iEval (rewrite eq_lift_prod) in "Hm".
      iDestruct "Hm" as (m0l m0r m1l m1r) "(-> & -> & Hm0 & Hm1)".
      iEval (rewrite eq_lift_group) in "Hm0". iDestruct "Hm0" as (m0) "[-> ->]".
      iEval (rewrite eq_lift_group) in "Hm1". iDestruct "Hm1" as (m1) "[-> ->]".
      eq_pures'.
      destruct Hf as (-> & -> & -> & -> & ->).
      iApply (eq_na_open _ _ NB); first done. iFrame "Hinv". iIntros "[>H Hclose]".
      iDestruct "H" as "[(Hbrs_l' & _)|(%u' & %v' & %C' & %B' & %A' & %P' & %Q' & #Hbrs_l' & _ & _ & %Hf' & [(Hbsr_l & Hbsr_r & [Hmm|(%w & #Hmm)])|(%m0' & %m1' & %c0 & %d0 & %c1 & %d1 & %t0 & %t1 & _ & _ & #Hmm & _)])]";
        [ (* nothing sent: no, the receiver has *)
          by iDestruct (eq_pt_l_agree with "Hbrs_l Hbrs_l'") as %?
        |
        | (* the sender has sent: no *)
          by iDestruct (eq_pt_r_agree with "HmmS Hmm") as %?
        | by iDestruct (eq_pt_r_agree with "HmmS Hmm") as %? ].
      iClear "Hbrs_l'".
      iDestruct (eq_pt_r_half with "[$Hmm $HmmS]") as "Hmm".
      eq_store_r. iMod (eq_pt_r_persist with "Hmm") as "#Hmm". eq_pures'.
      destruct (decide (gexp P = 1%g)) as [H1|H1].
      { (* [u = 1]: the sender stays silent *)
        rewrite !(bool_decide_eq_true_2 _ H1). eq_pures'.
        iApply eq_na_close_rule. iFrame "Hclose".
        iSplitL "Hbsr_l Hbsr_r".
        { iNext. iRight. iExists _, _, _, _, _, P, Q. iFrame "Hbrs_l Hbrs_r Htup".
          iSplitR; first by iPureIntro. iLeft. iFrame. iRight. by iExists _. }
        iApply eq_value. by iEval (rewrite eq_lift_unit). }
      rewrite !(bool_decide_eq_false_2 _ H1). eq_pures'.
      eq_load_r. eq_pures'.
      (* The samples: [s_i] against [α_i], [r_i] against [β_i = r_i + (x - q) s_i]. *)
      eq_couple_rand_rand. iIntros (s1 Hs1). eq_pures'.
      assert (Bij (shiftB (expF x) Q s1)) as Hb1 by apply (shiftB_bij n_prime).
      couple_along (shiftB (expF x) Q s1); first by apply (shiftB_lt n_prime).
      iIntros (r1 Hr1). eq_pures'.
      eq_couple_rand_rand. iIntros (s0 Hs0). eq_pures'.
      assert (Bij (shiftB (expF x) Q s0)) as Hb0 by apply (shiftB_bij n_prime).
      couple_along (shiftB (expF x) Q s0); first by apply (shiftB_lt n_prime).
      iIntros (r0 Hr0). eq_pures'.
      (* Both sides send [(g^t0, m0 u^t0)], [(g1^t1, m1 u^t1)], for
         [t_i = r_i + x s_i]. *)
      assert (r0 < n)%nat as Hr0' by lia. assert (r1 < n)%nat as Hr1' by lia.
      rewrite (encB_fst0 n_prime x r0 s0) (encB_fst1 n_prime y x r1 s1).
      rewrite (encB_snd n_prime r0 s0 eq_refl eq_refl) (encB_snd n_prime r1 s1 eq_refl eq_refl).
      rewrite (encB_fst0' n_prime (expF x) s0 Hr0' eq_refl) (encB_fst1' n_prime (expF x) y s1 Hr1' eq_refl).
      rewrite (encB_snd' n_prime (expF x) s0 Hr0' eq_refl eq_refl)
        (encB_snd' n_prime (expF x) s1 Hr1' eq_refl eq_refl).
      eq_store_l. eq_store_r.
      iMod (eq_pt_l_persist with "Hbsr_l") as "#Hbsr_l". iMod (eq_pt_r_persist with "Hbsr_r") as "#Hbsr_r".
      eq_pures'.
      iApply eq_na_close_rule. iFrame "Hclose".
      iSplitL "".
      { iNext. iRight. iExists _, _, _, _, _, P, Q. iFrame "Hbrs_l Hbrs_r Htup".
        iSplitR; first by iPureIntro. iRight. iExists m0, m1, _, _, _, _, _, _.
        iFrame "Hbsr_l Hbsr_r Hmm". by iPureIntro. }
      eq_reshape_l (lsrl _). eq_reshape_r (lsrr _).
      iApply (eq_call_frame θ (¡ θ)%R ((𝔾 × 𝔾) × (𝔾 × 𝔾))%T 𝟙%T emp%I with "Hρ Hleak_sr [] []");
        try (intros; apply _); [by iApply eq_ctxts|done|].
      iIntros "!>" (??) "Hu _". by iApply eq_value.
    - (* The receiver: its choice. *)
      iApply eq_lift_arr. iIntros (bl br) "Hb".
      iEval (rewrite eq_lift_bool) in "Hb". iDestruct "Hb" as %(b & -> & ->).
      eq_pures'.
      (* Its [z] against the tuple's [p = y_b z]; the tuple's [q] on the right only. *)
      destruct b;
        [ assert (Bij (aff (expF y) F0)) as Hbij
            by (apply (aff_bij n_prime); apply (expF_nz n_prime Hy Hnz));
          couple_along (aff (expF y) F0); [by apply (aff_lt n_prime)|];
          iIntros (z Hz); eq_pures';
          eq_focus_r (rand #_)%E; iApply eq_randU_r; iIntros (q Hq); eq_pures';
          assert (z < n)%nat as Hz' by lia;
          rewrite (recvB_aff n_prime y Hz') (recvB_powAC n_prime y x z) (recvB_pow n_prime y z)
            !(gexp_pow n_prime) (gexp_nat n_prime q)
        | eq_couple_rand_rand; iIntros (z Hz); eq_pures';
          eq_focus_r (rand #_)%E; iApply eq_randU_r; iIntros (q Hq); eq_pures';
          rewrite (expgAC g x z) (gexp_nat n_prime z) !(gexp_pow n_prime) (gexp_nat n_prime q) ];
        (* Send [u = g^P], [v = u^x]; the tuple. *)
        (iApply (eq_na_open _ _ NB); [done|]; iFrame "Hinv"; iIntros "[>H Hclose]";
         iDestruct "H" as "[(Hbrs_l & Hbrs_r & Hbsr_l & Hbsr_r & Htup & Hmm)|(%u' & %v' & %C' & %B' & %A' & %P' & %Q' & _ & _ & #Htup' & _)]";
         [|by iDestruct (eq_pt_r_agree with "HtupR Htup'") as %?];
         eq_store_l; iDestruct (eq_pt_r_half with "[$Htup $HtupR]") as "Htup"; eq_store_r; eq_pures';
         eq_store_r; rewrite ?(gexp_pow n_prime);
         iMod (eq_pt_l_persist with "Hbrs_l") as "#Hbrs_l"; iMod (eq_pt_r_persist with "Hbrs_r") as "#Hbrs_r";
         iMod (eq_pt_r_persist with "Htup") as "#Htup";
         iApply eq_na_close_rule; iFrame "Hclose";
         iSplitL "Hbsr_l Hbsr_r Hmm";
         [iNext; iRight; iExists _, _, _, _, _, _, _; iFrame "Hbrs_l Hbrs_r Htup";
          iSplitR; [by iPureIntro|]; iLeft; iFrame "Hbsr_l Hbsr_r"; iLeft; iFrame "Hmm"|];
         eq_pures';
         eq_reshape_l (lrsl _); eq_reshape_r (lrsr _);
         (iApply (eq_call_frame θ (¡ θ)%R (𝔾 × 𝔾)%T 𝟙%T emp%I with "Hρ Hleak_rs [] []");
            try (intros; apply _); [by iApply eq_pair|done|]);
         iIntros "!>" (??) "Hu _"; iEval (rewrite eq_lift_unit) in "Hu"; iDestruct "Hu" as %[-> ->];
         eq_pures';
         (* Wait for the ciphertexts, and decrypt the chosen one. *)
         iLöb as "IH";
         eq_reshape_l (dsrl _); eq_reshape_r (dsrr _);
         (iApply (eq_call_frame θ (¡ θ)%R 𝟙%T 𝟙%T emp%I with "Hρ Hdeliver_sr [] []");
            try (intros; apply _); [by iEval (rewrite eq_lift_unit)|done|]);
         iIntros "!>" (??) "Hu _"; iEval (rewrite eq_lift_unit) in "Hu"; iDestruct "Hu" as %[-> ->];
         eq_pures';
         iApply (eq_na_open _ _ NB); [done|]; iFrame "Hinv"; iIntros "[>H Hclose]";
         iDestruct "H" as "[(Hbrs_l' & _)|(%u' & %v' & %C' & %B' & %A' & %P' & %Q' & #Hbrs_l' & #Hbrs_r' & #Htup' & %Hf' & [(Hbsr_l & Hbsr_r & Hmmst)|(%m0 & %m1 & %c0 & %d0 & %c1 & %d1 & %t0 & %t1 & #Hbsr_l & #Hbsr_r & #Hmm & %Hct)])]";
         [ (* nothing sent: no, the receiver has *)
           by iDestruct (eq_pt_l_agree with "Hbrs_l Hbrs_l'") as %?
         | (* not yet *)
           eq_load_l; eq_load_r; iApply eq_na_close_rule; iFrame "Hclose";
           iSplitL "Hbsr_l Hbsr_r Hmmst";
           [iNext; iRight; iExists u', v', C', B', A', P', Q'; iFrame "Hbrs_l' Hbrs_r' Htup'";
            iSplitR; [by iPureIntro|]; iLeft; iFrame
           |eq_pures_lr; eq_pures'; iApply "IH"]
         | (* the ciphertexts *)
           eq_load_l; eq_load_r; iApply eq_na_close_rule; iFrame "Hclose";
           iSplitL "";
           [iNext; iRight; iExists u', v', C', B', A', P', Q'; iFrame "Hbrs_l' Hbrs_r' Htup'";
            iSplitR; [by iPureIntro|]; iRight; iExists m0, m1, c0, d0, c1, d1, t0, t1;
            iFrame "Hbsr_l Hbsr_r Hmm"; by iPureIntro
           |];
           eq_pures'; eq_load_r; eq_pures';
           iDestruct (eq_pt_l_agree with "Hbrs_l Hbrs_l'") as %Heq;
           injection Heq as Hu' Hv'; apply vgval_inj in Hu';
           destruct Hf' as (Hu'' & _); rewrite Hu'' in Hu';
           destruct Hct as (-> & -> & -> & ->);
           iApply eq_value; iApply eq_group_val;
           first [ apply (decB0 n_prime); by rewrite Hu'
                 | apply (decB n_prime (P0 := Fmul (expF y) (expF z))); [by rewrite Hu'|done] ] ]).
  Qed.

  Definition ND : namespace := nroot .@ "otD".

  (* The state of step D.  Left: the channels' boxes [brs], [bsr], the
     tuple [tup] and the sender's messages [mmL]; right: the simulator's
     [uu] and the functionality's [ch] and [mmR].  The receiver holds half
     of [ch], the sender half of [mmR] and all of the simulator's [s_go].
     The stages: nothing; the receiver has sent [(g^p, g^(p x))], the
     tuple is [(g^c, g^q, g^p)] with [p ≠ 0] and [c ≠ p q]; the sender has
     also sent. *)
  Definition inv_D (brs bsr tup mmL uu ch mmR : loc) : iPropD Σ :=
    (brs ↦ₗ NONEV ∗ bsr ↦ₗ NONEV ∗ tup ↦ₗ NONEV ∗ mmL ↦ₗ NONEV ∗ uu ↦ᵣ NONEV ∗
       ch ↦ᵣ{DfracOwn (1/2)} #false ∗ mmR ↦ᵣ{DfracOwn (1/2)} NONEV) ∨
    (∃ (p q c : nat) (wv : val),
       brs ↦ₗ□ SOMEV (vgval (g ^+ p), wv)%V ∗
       tup ↦ₗ□ SOMEV (vgval (g ^+ c), vgval (g ^+ q), vgval (g ^+ p))%V ∗
       uu ↦ᵣ□ SOMEV (vgval (g ^+ p)) ∗ ch ↦ᵣ□ #true ∗
       ⌜p ≤ S n'' ∧ p ≠ 0%nat ∧ c ≤ S n'' ∧ c ≠ pqval p q⌝ ∗
       ((bsr ↦ₗ NONEV ∗ mmL ↦ₗ NONEV ∗ mmR ↦ᵣ{DfracOwn (1/2)} NONEV) ∨
        (∃ (m0 m1 : vgG) (e : val), bsr ↦ₗ□ SOMEV e ∗
           mmL ↦ₗ□ SOMEV (vgval m0, vgval m1)%V ∗ mmR ↦ᵣ□ SOMEV (vgval m0, vgval m1)%V))).

  (* Step D. *)
  Lemma hyb2_ideal_EQ :
    ⎡↯ (1 / n)⎤ ∗ ⎡↯ (1 / n)⎤ ⊢ ⟪ ModA OTHNet OTPorts ⟫ (HYB2_OT_H DDH_rand) IDEAL_OT_H.
  Proof.
    iIntros "[He1 He2]". rewrite /ModA /ModM. iEval (rewrite eq_lift_forall). iIntros (θ).
    rewrite eq_lift_mbang /=.
    iApply eq_lift_arr. iIntros (advl advr) "Hadv".
    rewrite /OTHNet /Pub /LNet. iEval (rewrite eq_lift_prod) in "Hadv".
    iDestruct "Hadv" as (pl pr nl nr) "(-> & -> & #Hpub & Hnets)".
    iEval (rewrite eq_lift_prod) in "Hnets".
    iDestruct "Hnets" as (rsl rsr srl srr) "(-> & -> & Hrs & Hsr)".
    iEval (rewrite eq_lift_prod) in "Hrs".
    iDestruct "Hrs" as (lrsl lrsr drsl drsr) "(-> & -> & #Hleak_rs & #Hdeliver_rs)".
    iEval (rewrite eq_lift_prod) in "Hsr".
    iDestruct "Hsr" as (lsrl lsrr dsrl dsrr) "(-> & -> & #Hleak_sr & #Hdeliver_sr)".
    rewrite /IDEAL_OT_H /HYB2_OT_H /HYB2_body /comp_op /F_OT_H /S_OT_H /DDH_rand
      /F_OAUTH /sample is_unit.
    eq_pures_l. eq_pures_r.
    (* The reference string, the same on both sides. *)
    eq_couple_rand_rand. iIntros (y Hy). simpl. eq_pures'.
    eq_couple_rand_rand. iIntros (x Hx). simpl. eq_pures'.
    (* Publish it, keeping the credits for the receiver. *)
    iAssert (⎡(¡ ⟨⟩)%R ≤ᵣ (⟨⟩%R : sem_row Σ)⎤)%I as "#H0"; first by iApply row_le_mfbang_elim_nil.
    eq_reshape_l (pl _). eq_reshape_r (pr _).
    iApply (eq_call_frame ⟨⟩%R ⟨⟩%R Crs 𝟙%T (⎡↯ (1 / n)⎤ ∗ ⎡↯ (1 / n)⎤)%I
              with "H0 Hpub [] [$He1 $He2]"); try (intros; apply _); first iApply eq_crs.
    iIntros "!>" (wl wr) "_ [He1 He2]". simpl. eq_pures'.
    eq_alloc_l brs as "Hbrs". eq_pures_l. eq_alloc_l bsr as "Hbsr". eq_pures_l.
    eq_alloc_l tup as "Htup". eq_pures_l. eq_alloc_l mmL as "HmmL". eq_pures_l.
    eq_alloc_r uu as "Huu". eq_pures_r. eq_alloc_r sgo as "Hsgo". eq_pures_r.
    eq_alloc_r ch as "Hch". eq_pures_r. eq_alloc_r mmR as "HmmR". eq_pures_r.
    iDestruct (eq_pt_r_half with "Hch") as "[Hch HchR]".
    iDestruct (eq_pt_r_half with "HmmR") as "[HmmR HmmS]".
    iApply (eq_na_alloc (inv_D brs bsr tup mmL uu ch mmR) ND).
    iSplitL "Hbrs Hbsr Htup HmmL Huu Hch HmmR"; first (iNext; iLeft; iFrame).
    iIntros "#Hinv".
    iApply eq_value. iModIntro. rewrite /OTPorts /SPort /RPort. iEval (rewrite eq_lift_prod).
    iExists _, _, _, _. do 2 (iSplit; first done).
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    iSplitL "HmmS Hsgo".
    - (* The sender: wait for the receiver's message. *)
      iApply eq_lift_arr. iIntros (wl' wr') "Hw".
      iEval (rewrite eq_lift_unit) in "Hw". iDestruct "Hw" as %[-> ->].
      eq_pures'. eq_load_r. eq_pures'.
      iLöb as "IH".
      eq_reshape_l (drsl _). eq_reshape_r (drsr _).
      iApply (eq_call_frame θ (¡ θ)%R 𝟙%T 𝟙%T (mmR ↦ᵣ{DfracOwn (1/2)} NONEV ∗ sgo ↦ᵣ #false)%I
                with "Hρ Hdeliver_rs [] [$HmmS $Hsgo]");
        try (intros; apply _); first by iEval (rewrite eq_lift_unit).
      iIntros "!>" (??) "Hu [HmmS Hsgo]". iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
      eq_pures'.
      iApply (eq_na_open _ _ ND); first done. iFrame "Hinv". iIntros "[>H Hclose]".
      iDestruct "H" as "[(Hbrs & Hbsr & Htup & HmmL & Huu & Hch & HmmR)|(%p & %q & %c & %wv & #Hbrs & #Htup & #Huu & #Hch & %Hf & Hrest)]".
      { (* not yet *)
        eq_load_l. eq_load_r. eq_pures_r. eq_load_r. iApply eq_na_close_rule. iFrame "Hclose".
        iSplitL "Hbrs Hbsr Htup HmmL Huu Hch HmmR"; first (iNext; iLeft; iFrame).
        eq_pures_lr. eq_pures'. eq_load_r. eq_pures'. iApply ("IH" with "HmmS Hsgo"). }
      eq_load_l. eq_load_r. eq_pures'. eq_store_r. eq_pures'. eq_load_r.
      iApply eq_na_close_rule. iFrame "Hclose".
      iSplitL "Hrest".
      { iNext. iRight. iExists p, q, c, wv. iFrame "Hbrs Htup Huu Hch Hrest". by iPureIntro. }
      eq_pures'.
      destruct Hf as (Hp & Hp0 & _).
      (* Second phase: the messages [m_i = g^l_i]. *)
      iApply eq_value. iModIntro. iApply eq_lift_arr. iIntros (ml mr) "Hm".
      iEval (rewrite eq_lift_prod) in "Hm".
      iDestruct "Hm" as (m0l m0r m1l m1r) "(-> & -> & Hm0 & Hm1)".
      iEval (rewrite eq_lift_group) in "Hm0". iDestruct "Hm0" as (m0) "[-> ->]".
      iEval (rewrite eq_lift_group) in "Hm1". iDestruct "Hm1" as (m1) "[-> ->]".
      destruct (log_g_nat n_prime m0) as (l0 & Hl0 & ->).
      destruct (log_g_nat n_prime m1) as (l1 & Hl1 & ->).
      eq_pures'.
      iClear "Htup Huu".
      iApply (eq_na_open _ _ ND); first done. iFrame "Hinv". iIntros "[>H Hclose]".
      iDestruct "H" as "[(Hbrs0 & _)|(%p' & %q' & %c' & %wv' & #Hbrs' & #Htup' & #Huu' & #Hch' & %Hf' & [(Hbsr & HmmL & HmmR)|(%m0' & %m1' & %e & _ & _ & #HmmR)])]";
        [ by iDestruct (eq_pt_l_agree with "Hbrs Hbrs0") as %?
        |
        | by iDestruct (eq_pt_r_agree with "HmmS HmmR") as %? ].
      destruct Hf' as (Hp' & Hp0' & Hc' & Hcne').
      eq_store_l. iDestruct (eq_pt_r_half with "[$HmmR $HmmS]") as "HmmR". eq_store_r.
      iMod (eq_pt_l_persist with "HmmL") as "#HmmL". iMod (eq_pt_r_persist with "HmmR") as "#HmmR".
      eq_pures'.
      rewrite (bool_decide_eq_false_2 _ (gpow_ne1 n_prime Hp Hp0)). eq_pures'.
      eq_load_l. eq_pures'. eq_load_r. eq_pures'. eq_load_r. eq_pures'.
      (* The samples: [α_i] against [d_i = (c - p q) α_i + l_i], [β_i] against
         [t_i = β_i + q α_i]. *)
      assert (Bij (aff (dcoef c' p' q') (expF l1))) as Hb1 by (apply (dcoef_bij n_prime); assumption).
      couple_along (aff (dcoef c' p' q') (expF l1)); first by apply (aff_lt n_prime).
      iIntros (a1 Ha1). eq_pures'.
      assert (Bij (aff F1 (tshift q' a1))) as Hb1' by apply (tshift_bij n_prime).
      couple_along (aff F1 (tshift q' a1)); first by apply (aff_lt n_prime).
      iIntros (b1 Hb1v). eq_pures'.
      assert (Bij (aff (dcoef c' p' q') (expF l0))) as Hb0 by (apply (dcoef_bij n_prime); assumption).
      couple_along (aff (dcoef c' p' q') (expF l0)); first by apply (aff_lt n_prime).
      iIntros (a0 Ha0). eq_pures'.
      assert (Bij (aff F1 (tshift q' a0))) as Hb0' by apply (tshift_bij n_prime).
      couple_along (aff F1 (tshift q' a0)); first by apply (aff_lt n_prime).
      iIntros (b0 Hb0v). eq_pures'.
      (* The simulator's ciphertexts are the hybrid's. *)
      assert (a0 < n)%nat as Ha0' by lia. assert (a1 < n)%nat as Ha1' by lia.
      assert (b0 < n)%nat as Hb0'' by lia. assert (b1 < n)%nat as Hb1'' by lia.
      rewrite !(encD_snd n_prime) // !(encD_fst1 n_prime) // !(encD_fst0 n_prime) //.
      eq_store_l. iMod (eq_pt_l_persist with "Hbsr") as "#Hbsr". eq_pures'.
      iApply eq_na_close_rule. iFrame "Hclose".
      iSplitL "".
      { iNext. iRight. iExists p', q', c', wv'. iFrame "Hbrs' Htup' Huu' Hch'".
        iSplitR; first by iPureIntro. iRight. iExists _, _, _. iFrame "Hbsr HmmL HmmR". }
      eq_reshape_l (lsrl _). eq_reshape_r (lsrr _).
      iApply (eq_call_frame θ (¡ θ)%R ((𝔾 × 𝔾) × (𝔾 × 𝔾))%T 𝟙%T emp%I with "Hρ Hleak_sr [] []");
        try (intros; apply _); [by iApply eq_ctxts|done|].
      iIntros "!>" (??) "Hu _". by iApply eq_value.
    - (* The receiver: its choice. *)
      iApply eq_lift_arr. iIntros (bl br) "Hb".
      iEval (rewrite eq_lift_bool) in "Hb". iDestruct "Hb" as %(b & -> & ->).
      eq_pures'.
      iApply (eq_na_open _ _ ND); first done. iFrame "Hinv". iIntros "[>H Hclose]".
      iDestruct "H" as "[(Hbrs & Hbsr & Htup & HmmL & Huu & Hch & HmmR)|(%p' & %q' & %c' & %wv' & _ & _ & _ & #Hch' & _)]";
        last by iDestruct (eq_pt_r_agree with "HchR Hch'") as %?.
      iDestruct (eq_pt_r_half with "[$Hch $HchR]") as "Hch".
      eq_store_r. iMod (eq_pt_r_persist with "Hch") as "#Hch". eq_pures'.
      eq_load_r. eq_pures'.
      (* The tuple's [p ≠ 0] against the simulator's [a]; [q] and [c ≠ p q]
         on the left only. *)
      couple_along (λ k : nat, k) avoiding 0%nat; [intros; lia|lia|].
      iFrame "He1". iIntros (p Hp Hp0). simpl. eq_pures'.
      eq_focus_l (rand #_)%E. iApply eq_randU_l. iIntros (q Hq). eq_pures'.
      eq_focus_l (rand #_)%E. iApply (eq_rand_avoid_l _ _ _ _ (pqval p q)).
      iFrame "He2". iIntros (c Hcne Hc). eq_pures'.
      (* Its message, [(g^p, g^(p x))] on both sides. *)
      eq_store_l. eq_pures'. eq_store_l. eq_store_r. eq_pures'.
      rewrite (expgAC g x p).
      iMod (eq_pt_l_persist with "Htup") as "#Htup". iMod (eq_pt_l_persist with "Hbrs") as "#Hbrs".
      iMod (eq_pt_r_persist with "Huu") as "#Huu".
      iApply eq_na_close_rule. iFrame "Hclose".
      iSplitL "Hbsr HmmL HmmR".
      { iNext. iRight. iExists p, q, c, _. iFrame "Hbrs Htup Huu Hch".
        iSplitR; first by iPureIntro. iLeft. iFrame. }
      eq_reshape_l (lrsl _). eq_reshape_r (lrsr _).
      iApply (eq_call_frame θ (¡ θ)%R (𝔾 × 𝔾)%T 𝟙%T emp%I with "Hρ Hleak_rs [] []");
        try (intros; apply _); [by iApply eq_pair|done|].
      iIntros "!>" (??) "Hu _". iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
      eq_pures'.
      (* Wait for the sender. *)
      iLöb as "IH".
      eq_reshape_l (dsrl _). eq_reshape_r (dsrr _).
      iApply (eq_call_frame θ (¡ θ)%R 𝟙%T 𝟙%T emp%I with "Hρ Hdeliver_sr [] []");
        try (intros; apply _); [by iEval (rewrite eq_lift_unit)|done|].
      iIntros "!>" (??) "Hu _". iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
      eq_pures'.
      iApply (eq_na_open _ _ ND); first done. iFrame "Hinv". iIntros "[>H Hclose]".
      iDestruct "H" as "[(_ & _ & _ & _ & _ & Hch0 & _)|(%p' & %q' & %c' & %wv' & #Hbrs' & #Htup' & #Huu' & _ & %Hf' & [(Hbsr & HmmL & HmmR)|(%m0 & %m1 & %e & #Hbsr & #HmmL & #HmmR)])]";
        [ by iDestruct (eq_pt_r_agree with "Hch Hch0") as %?
        | (* not yet *)
          eq_load_l; eq_load_r; iApply eq_na_close_rule; iFrame "Hclose";
          iSplitL "Hbsr HmmL HmmR";
          [iNext; iRight; iExists p', q', c', wv'; iFrame "Hbrs' Htup' Huu' Hch";
           iSplitR; [by iPureIntro|]; iLeft; iFrame
          |eq_pures_lr; eq_pures'; eq_load_r; eq_pures'; iApply "IH"]
        | (* the sender has sent: the chosen message on both sides *)
          eq_load_l; eq_load_r; iApply eq_na_close_rule; iFrame "Hclose";
          iSplitL "";
          [iNext; iRight; iExists p', q', c', wv'; iFrame "Hbrs' Htup' Huu' Hch";
           iSplitR; [by iPureIntro|]; iRight; iExists m0, m1, e; iFrame "Hbsr HmmL HmmR"
          |];
          eq_pures'; eq_load_l; eq_pures';
          destruct b; eq_pures'; iApply eq_value; by iApply eq_group_val ].
  Qed.

End ot_h_eq.

(* ------------------------------------------------------------------ *)
(* The security theorem.                                               *)
(* ------------------------------------------------------------------ *)

Section ot_h_security.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context `{Hpre : probblazeRGpreS Σ}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.

  #[local] Notation n := (S (S n'')).
  Context `{n_prime : is_true (prime.prime n)}.

  Lemma one_n_nonneg' : (0 <= 1 / n)%R.
  Proof. apply Rcomplements.Rdiv_le_0_compat; first lra. apply lt_0_INR. lia. Qed.

  (* Step A. *)
  Lemma hyb1_ddh (A : val) (b : bool) :
    (advantage A (HYB1_OT_H DDH_rand) (HYB1_OT_H DDH_real) #b
       <= advantage (RED1_OT_H A) DDH_rand DDH_real #b)%R.
  Proof.
    rewrite /HYB1_OT_H.
    set (FA := (F_OAUTH ⊗ F_OAUTH)%md).
    etrans; first apply (advantage_pure_l_rev _ []
      (comp_app PARTIES_OT (tens_op (F_CRS_DH DDH_rand) FA)) _ _); [done|apply comp_app_pure|].
    etrans; first apply (advantage_pure_r_rev _ [] _
      (comp_app PARTIES_OT (tens_op (F_CRS_DH DDH_real) FA)) _); [done|apply comp_app_pure|].
    etrans; first apply (advantage_pure_l_rev _ [AppRCtx (comp_app PARTIES_OT)]
      (tens_app (F_CRS_DH DDH_rand) FA) _ _); [done|apply tens_app_pure|].
    etrans; first apply (advantage_pure_r_rev _ [AppRCtx (comp_app PARTIES_OT)] _
      (tens_app (F_CRS_DH DDH_real) FA) _); [done|apply tens_app_pure|].
    etrans; first apply (advantage_pure_l_rev _ [AppRCtx (comp_app PARTIES_OT); AppLCtx FA; AppRCtx tens_app]
      (F_CRS_DH_app DDH_rand) _ _); [done|apply F_CRS_DH_app_pure|].
    etrans; first apply (advantage_pure_r_rev _ [AppRCtx (comp_app PARTIES_OT); AppLCtx FA; AppRCtx tens_app] _
      (F_CRS_DH_app DDH_real) _); [done|apply F_CRS_DH_app_pure|].
    etrans; first apply (advantage_reduction_ctx A
      [AppRCtx (comp_app PARTIES_OT); AppLCtx FA; AppRCtx tens_app; AppRCtx F_CRS_DH_app]).
    { done. }
    { intros vs w Hw. simpl. by rewrite Hw. }
    apply Rle_refl.
  Qed.

  (* Step C. *)
  Lemma hyb2_ddh (A : val) (b : bool) :
    (advantage A (HYB2_OT_H DDH_real) (HYB2_OT_H DDH_rand) #b
       <= advantage (RED2_OT_H A) DDH_real DDH_rand #b)%R.
  Proof.
    etrans; first apply (advantage_pure_l_rev _ [] (HYB2_app DDH_real) _ _);
      [done|apply HYB2_app_pure|].
    etrans; first apply (advantage_pure_r_rev _ [] _ (HYB2_app DDH_rand) _);
      [done|apply HYB2_app_pure|].
    etrans; first apply (advantage_reduction_ctx A [AppRCtx HYB2_app]).
    { done. }
    { intros vs w Hw. simpl. by rewrite Hw. }
    apply Rle_refl.
  Qed.

  Lemma ot_h_credits `{!probblazeRGS Σ} :
    ↯ (2 / n) ⊢ ↯ (1 / n) ∗ ↯ (1 / n).
  Proof.
    have Hn := one_n_nonneg'.
    assert (2 / n = 1 / n + 1 / n)%R as -> by lra.
    iIntros "H". by iDestruct (ec_split with "H") as "[$ $]".
  Qed.

  Theorem ot_h_security : ot_h_secure.
  Proof.
    intros A HA.
    set (τ := λ H : probblazeRGS Σ, ModA OTHNet OTPorts).
    change REAL_OT_H with (HYB1_OT_H DDH_rand).
    apply (advantage_triangle _ _ (HYB1_OT_H DDH_real) _ _
             (advantage (RED1_OT_H A) DDH_rand DDH_real #true)
             (advantage (RED2_OT_H A) DDH_real DDH_rand #true + 3 / n)); [| |lra].
    { apply hyb1_ddh. }
    apply (advantage_triangle _ _ (HYB2_OT_H DDH_real) _ _ (1 / n)
             (advantage (RED2_OT_H A) DDH_real DDH_rand #true + 2 / n)); [| |lra].
    { apply (sem_typed_advantage_aff A _ _ τ (1 / n) one_n_nonneg'); first exact HA.
      split; intros HRGS; iIntros "Herr".
      - pose proof (hyb1_hyb2_EQ (n_prime := n_prime)) as [H]. specialize (H Fwd).
        rewrite !monPred_at_embed eq_lift_at /pick /= in H. by iApply H.
      - pose proof (hyb1_hyb2_EQ (n_prime := n_prime)) as [H]. specialize (H Bwd).
        rewrite !monPred_at_embed eq_lift_at /pick /= in H. by iApply H. }
    apply (advantage_triangle _ _ (HYB2_OT_H DDH_rand) _ _
             (advantage (RED2_OT_H A) DDH_real DDH_rand #true) (2 / n)); [| |lra].
    { apply hyb2_ddh. }
    apply (sem_typed_advantage_aff A _ _ τ (2 / n)); [|exact HA|].
    { apply Rcomplements.Rdiv_le_0_compat; first lra. apply lt_0_INR. lia. }
    split; intros HRGS; iIntros "Herr"; iDestruct (ot_h_credits with "Herr") as "Herr".
    - pose proof (hyb2_ideal_EQ (n_prime := n_prime)) as [H]. specialize (H Fwd).
      rewrite !monPred_at_sep !monPred_at_embed eq_lift_at /pick /= in H. by iApply H.
    - pose proof (hyb2_ideal_EQ (n_prime := n_prime)) as [H]. specialize (H Bwd).
      rewrite !monPred_at_sep !monPred_at_embed eq_lift_at /pick /= in H. by iApply H.
  Qed.

End ot_h_security.

From iris.proofmode Require Import base proofmode classes.                                           
From iris.base_logic.lib Require Import  na_invariants.   
From iris.algebra Require Import agree excl auth frac excl_auth. 
From iris.algebra.lib Require Import dfrac_agree.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode
  spec_rules spec_ra 
  class_instances.
From clutch.prob_eff_lang.probblaze Require Import tactics.
From clutch.prob_eff_lang.probblaze Require Import def_dhke.
From clutch.prob_eff_lang.probblaze Require Import dhke_channel.
From clutch.prob_eff_lang.probblaze Require Import sem_types sem_row sem_sig sem_judgement sem_def.
From clutch.prob_eff_lang.probblaze Require Import p_composition.    
From clutch.prob_eff_lang.probblaze Require Import xor sec_channel_def. 

Import fingroup.

Import fingroup.fingroup.

(*Import valgroup_notation.*)
Import valgroup_tactics.


Section schan_security.
  Context `{probblazeRGS Σ}.
  Context (lka1 lka2 klk1 klk2 : label).
  Context {vg: val_group}.
  Context {cg: clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.
  Context {Key Support : nat}.
  Variable xor_struct : XOR (Key := Key) (Support := Support).
  Variable bij_group_xor_sem : vgG -> vgG -> vgG.
  Hypothesis Bij_xor_sem : ∀ g1 g2 : vgG, bij_group_xor_sem (bij_group_xor_sem g1 g2) g2 = g1.
  Context `{!XOR_spec (Key := Key) (Support := Support) (H := xor_struct)}. 


  Definition atokN' : namespace := nroot .@ "atokN1".
  Definition btokN' : namespace := nroot .@ "btokN1".

    (*Theories for the interaction of the secure channel with the environment*)
  (*-------------------------------------------------------------*)

  (* Theories for the authenticated channel leaks *)
  (*-------------------------------------------------------------*)
   (* Sent BY Bob TO Alice*)
   Program Definition LASendBob (leakauth1 leakauth2 : label) : iThy Σ :=
  λ e1 e2, (λne Q,
              ∃ m1 m2 : val,
                ⌜e1 = (do: leakauth1 (SendV (m1, alice)))⌝%E ∗ 
                           ⌜ e2 = do: leakauth2 (SendV (m2, alice)) ⌝%E ∗
                                      □ Q (Val #()%V) (Val #()%V))%I.
  Next Obligation. solve_proper. Qed.
  (* Sent BY Alice TO Bob*)
  Program Definition LASendAlice (leakauth1 leakauth2 : label) : iThy Σ :=
  λ e1 e2, (λne Q,
              ∃ m1 m2 : val,
                ⌜e1 = (do: leakauth1 (SendV (m1, bob)))⌝%E ∗ 
                           ⌜ e2 = do: leakauth2 (SendV (m2, bob)) ⌝%E ∗
                                      □ Q (Val #()%V) (Val #()%V))%I.
  Next Obligation. solve_proper. Qed.
  (*Recv FROM bob*) 
  Program Definition LARecvBob (leakauth1 leakauth2 : label) : iThy Σ :=
   λ e1 e2, (λne Q,
                ⌜ e1 = do: leakauth1 (RecvV bob) ⌝%E ∗
                ⌜ e2 = do: leakauth2 (RecvV bob) ⌝%E ∗
                □ ((∀ b1 b2 : nat, Q (SOMEV #b1) (SOMEV #b2)) ∧ Q NONEV NONEV)
             )%I.
  Next Obligation. solve_proper. Qed.
 (* Recv FROM Alice *)
  Program Definition LARecvAlice (leakauth1 leakauth2 : label) : iThy Σ :=
     λ e1 e2, (λne Q,
                ⌜ e1 = do: leakauth1 (RecvV alice) ⌝%E ∗
                ⌜ e2 = do: leakauth2 (RecvV alice) ⌝%E ∗
                □ ((∀ b1 b2 : nat, Q (SOMEV #b1) (SOMEV #b2)) ∧ Q NONEV NONEV)
             )%I.
  Next Obligation. solve_proper. Qed.

  
  (* Theories for the key exchange leaks*)
  (*---------------------------------------------------------*)
  (*Send TO Alice*)
  Program Definition KLeakSendAlice (keyleak1 keyleak2 : label) : iThy Σ :=
    λ e1 e2, (λne Q,
                ⌜ e1 = do: keyleak1 (SendV alice) ⌝%E ∗
                           ⌜ e2 = do: keyleak2 (SendV alice) ⌝%E ∗
                                      □ Q (Val #()%V) (Val #()%V))%I.
  Next Obligation. solve_proper. Qed.
  (* Send TO Bob *)
  Program Definition KLeakSendBob (keyleak1 keyleak2 : label) : iThy Σ :=
    λ e1 e2, (λne Q,
                ⌜ e1 = do: keyleak1 (SendV bob) ⌝%E ∗
                           ⌜ e2 = do: keyleak2 (SendV bob) ⌝%E ∗
                                      □ Q (Val #()%V) (Val #()%V))%I.
  Next Obligation. solve_proper. Qed.


  (*Program Definition KLeakRecvAlice : iThy Σ :=
    λ e1 e2, (λne Q,
                ⌜ e1 = do: keyleak1 (RecvV alice) ⌝%E ∗
                           ⌜ e2 = do: keyleak2 (RecvV alice) ⌝%E ∗
                                      □ Q (Val #()%V) (Val #()%V))%I.
  Next Obligation. solve_proper. Qed.*) 
  (* Recv FROM Alice *)
   Program Definition KLeakRecvAlice (keyleak1 keyleak2 : label) : iThy Σ :=
    λ e1 e2, (λne Q,
                ⌜ e1 = do: keyleak1 (RecvV alice) ⌝%E ∗
                           ⌜ e2 = do: keyleak2 (RecvV alice) ⌝%E ∗
                                      □ (Q NONEV NONEV ∗ Q (SOMEV #0) (SOMEV #0)))%I.
  Next Obligation. solve_proper. Qed.
 (* Recv FROM Bob *)
  Program Definition KLeakRecvBob (keyleak1 keyleak2 : label) : iThy Σ :=
    λ e1 e2, (λne Q,
                ⌜ e1 = do: keyleak1 (RecvV bob) ⌝%E ∗
                           ⌜ e2 = do: keyleak2 (RecvV bob) ⌝%E ∗
                                      □ (Q NONEV NONEV ∗ Q (SOMEV #0) (SOMEV #0)))%I.
  Next Obligation. solve_proper. Qed.
  
  (* Theories relating the authenticated channel with the secure channel leak*)
  (*-----------------------------------------------------------------------------*)
  Program Definition SendALSAlice (channel leaksec : label) : iThy Σ :=
    λ e1 e2, (λne Q,
                ∃ m : val,
                  (⌜ e1 = do: channel (SendV (m, alice)) ⌝%E ∗
                  ⌜  e2 = do: leaksec (SendV alice)⌝%E) ∗ □ (Q (Val #()%V) (Val #()%V)))%I.
  Next Obligation. solve_proper. Qed.

  Program Definition SendALSBob (channel leaksec : label) : iThy Σ :=
    λ e1 e2, (λne Q,
                ∃ m : val,
                  (⌜ e1 = do: channel (SendV (m, bob)) ⌝%E ∗
                  ⌜  e2 = do: leaksec (SendV bob)⌝%E) ∗ □ (Q (Val #()%V) (Val #()%V)))%I.
  Next Obligation. solve_proper. Qed. 

  Program Definition RecvALSAlice (channel leaksec : label) : iThy Σ :=
    λ e1 e2, (λne Q,
                  (⌜ e1 = do: channel (RecvV alice) ⌝%E ∗
                  ⌜  e2 = do: leaksec (RecvV alice)⌝%E) ∗ □ (Q (Val #()%V) (Val #()%V)))%I.
  Next Obligation. solve_proper. Qed.    

  Program Definition RecvALSBob (channel leaksec : label) : iThy Σ := 
    λ e1 e2, (λne Q,
                  (⌜ e1 = do: channel (RecvV bob) ⌝%E ∗
                  ⌜  e2 = do: leaksec (RecvV bob)⌝%E) ∗ □ (Q (Val #()%V) (Val #()%V)))%I.
  Next Obligation. solve_proper. Qed.  


  (*Theories relating the secure channel effects for the client*)
  (*---------------------------------------------------------*)

  Program Definition SendSec (schannel1 schannel2 : label) : iThy Σ :=
     λ e1 e2, (λne Q,
                ∃ m : vgG, 
                            (⌜ e1 = do: schannel1 (SendV (vgval m)) ⌝%E ∗
                             ⌜ e2 = do: schannel2 (SendV (vgval m)) ⌝%E)  ∗ 
                            □ (Q (Val #()%V) (Val #()%V))
             )%I.
  Next Obligation. solve_proper. Qed.

  Program Definition RecvSecB (schannel1 schannel2 : label) : iThy Σ :=
     λ e1 e2, (λne Q,
                ⌜ e1 = do: schannel1 (RecvV bob) ⌝%E ∗
                ⌜ e2 = do: schannel2 (RecvV bob) ⌝%E ∗
                □ ((∀ g : vgG, Q (SOMEV (vgval g)) (SOMEV (vgval g))) ∧ Q NONEV NONEV)
             )%I.
  Next Obligation. solve_proper. Qed. 
     
  
 (* Program Definition SendSecBob (schannel1 schannel2 : label) : iThy Σ :=
     λ e1 e2, (λne Q,
                ∃ m : vgG, 
                            (⌜ e1 = do: schannel1 (SendV (vgval m, alice)) ⌝%E ∗
                             ⌜ e2 = do: schannel2 (SendV (vgval m, alice)) ⌝%E)  ∗ 
                            □ (Q (Val #()%V) (Val #()%V))
             )%I.
  Next Obligation. solve_proper. Qed.*)
  
  
   (*Program Definition SendSecBobImpl γtok γfrac γsec ℓ : iThy Σ :=
     λ e1 e2, (λne Q,
                ∃ m m': val, ((|={⊤, ⊤ ∖ ↑ℓ }=> ((own γfrac DfracDiscarded -∗ (|={⊤ ∖ ↑ℓ, ⊤}=> token γtok ∗ own γsec (to_dfrac_agree DfracDiscarded m) ∗ ⌜m = m'⌝)) ∨ |={⊤ ∖ ↑ℓ , ⊤}=> own γfrac DfracDiscarded)) ∗  
                            (⌜ e1 = do: schannel1 (SendV (m, alice)) ⌝%E ∗
                             ⌜ e2 = do: schannel2 (SendV (m', alice)) ⌝%E)  ∗ 
                            □ (Q (Val #()%V) (Val #()%V)))
             )%I.
  Next Obligation. solve_proper. Qed.*)
  
  (*Program Definition SendSecAlice (schannel1 schannel2 : label) : iThy Σ :=
     λ e1 e2, (λne Q,
                ∃ m : vgG, 
                            (⌜ e1 = do: schannel1 (SendV (vgval m, alice)) ⌝%E ∗
                             ⌜ e2 = do: schannel2 (SendV (vgval m, alice)) ⌝%E)  ∗ 
                            □ (Q (Val #()%V) (Val #()%V))
             )%I.
  Next Obligation. solve_proper. Qed.*)

   (* Program Definition SendSecAliceImpl γtok γfrac γsec ℓ : iThy Σ :=
     λ e1 e2, (λne Q,
                ∃ m m' : val, ((|={⊤, ⊤ ∖ ↑ℓ }=> ((own γfrac DfracDiscarded -∗ (|={⊤ ∖ ↑ℓ, ⊤}=> token γtok ∗ own γsec (to_dfrac_agree DfracDiscarded m) ∗ ⌜m = m'⌝)) ∨ |={⊤ ∖ ↑ℓ , ⊤}=> own γfrac DfracDiscarded)) ∗  
                             (⌜ e1 = do: schannel1 (SendV (m, bob)) ⌝%E ∗
                              ⌜ e2 = do: schannel2 (SendV (m', bob)) ⌝%E)  ∗ 
                             □ (Q (Val #()%V) (Val #()%V)))
             )%I.
  Next Obligation. solve_proper. Qed.*)
  
 (* Program Definition RecvSecBob (schannel1 schannel2 : label) : iThy Σ :=
     λ e1 e2, (λne Q,
                ⌜ e1 = do: schannel1 (RecvV bob) ⌝%E ∗
                ⌜ e2 = do: schannel2 (RecvV bob) ⌝%E ∗
                □ ((∀ v1 v2 : val, Q (SOMEV v1) (SOMEV v2)) ∧ Q NONEV NONEV)
             )%I.
  Next Obligation. solve_proper. Qed. *)
    
 (* Program Definition RecvSecAlice (schannel1 schannel2 : label) : iThy Σ :=
     λ e1 e2, (λne Q,
                 ⌜ e1 = do: schannel1 (RecvV alice) ⌝%E ∗
                 ⌜ e2 = do: schannel2 (RecvV alice) ⌝%E ∗
                 □ ((∀ v1 v2 : val, Q (SOMEV v1) (SOMEV v2)) ∧ Q NONEV NONEV )
             )%I.
  Next Obligation. solve_proper. Qed.*)


   (* semantic types*)
  (*----------------------------------------------------------------------------*)

   Definition sem_ty_group : sem_ty Σ := (λ v1 v2, ∃ g : vgG, ⌜ v1 = vgval g ⌝ ∗ ⌜ v2 = vgval g ⌝)%I.
   Notation "'𝔾'" := sem_ty_group.
  
 (* Program Definition bot_mono := {| pmono_prot_car := iThyBot ; pmono_prot_prop := _ |}.
  Next Obligation. iIntros (?). Defined.
 
  Definition empty_thy (l1 l2 : label) := @SemSig Σ bot_mono (l1,l2).
  Program Definition empty_thy_row (channel leaksec getKey1 getKey2 schannel1 schannel2 : label) :=
    SemRow [([channel; getKey1; schannel1] , [leaksec; getKey2; schannel2] , bot_mono)] _.*)
  Program Definition keyleak_mono (keyleak1 keyleak2 : label) := {| pmono_prot_car := iThySum (iThySum (KLeakSendAlice keyleak1 keyleak2) (KLeakRecvAlice keyleak1 keyleak2)) (iThySum (KLeakSendBob keyleak1 keyleak2) (KLeakRecvBob keyleak1 keyleak2)) ; pmono_prot_prop := _|}.
  Next Obligation.
   iIntros (????).
   iIntros (??) "#HΦ [[HS | HR] | [HS | HR]]".
   1: iLeft; iLeft. 2: iLeft; iRight. 3: iRight; iLeft. 4: iRight; iRight.
   1,3 : iDestruct "HS" as (??) "#H"; simpl; iSplit; first done; iSplit; first done; iModIntro; by iApply "HΦ".
   all: iDestruct "HR" as (??) "(#H1 & #H2)"; simpl; iSplit; first done; iSplit; first done; iModIntro; iSplitL " "; iApply "HΦ"; try (iApply "H1"); try (iApply "H2").
  Qed.
  Definition keyleak (keyleak1 keyleak2 : label) := @SemSig Σ (keyleak_mono keyleak1 keyleak2) (keyleak1, keyleak2).
  Lemma keyleak_pers_mono_row (keyleak1 keyleak2 : label) : ⊢ pers_mono_row (iLblSig_to_iLblThy [([keyleak1] , [keyleak2] , keyleak keyleak1 keyleak2)]).
  Proof. Admitted.
  Definition keyleak_row (keyleak1 keyleak2 : label) := SemRow [([keyleak1] , [keyleak2] , keyleak keyleak1 keyleak2)] (keyleak_pers_mono_row keyleak1 keyleak2).
 
  Program Definition leakauth_mono (leakauth1 leakauth2 : label) := {| pmono_prot_car := iThySum (iThySum (LASendAlice leakauth1 leakauth2) (LASendBob leakauth1 leakauth2)) (iThySum (LARecvAlice leakauth1 leakauth2) (LARecvBob leakauth1 leakauth2)) ; pmono_prot_prop := _ |}.
  Next Obligation.
    iIntros (??????) "#HΦ [[HS | HS] | [HR | HR]]".
    1: iLeft; iLeft. 2: iLeft; iRight. 3: iRight; iLeft. 4: iRight; iRight.
    1,2 : iDestruct "HS" as (??) "(#H1 & #H2 & #H3)"; simpl; iExists m1, m2; iSplit; first done; iSplit; first done;
                                                                         iModIntro; by iApply "HΦ". 
    all : iDestruct "HR" as "(#H1 & #H2 & #H3)"; simpl; iSplit; first done; iSplit; first done; iModIntro;
    iDestruct "H3" as "[Hs Hn]"; iSplitL " "; try (iIntros (??)); iApply "HΦ"; try (iApply "Hs"); try (iApply "Hn").
  Qed.

  Definition leakauth (leakauth1 leakauth2 : label) := @SemSig Σ (leakauth_mono leakauth1 leakauth2) (leakauth1, leakauth2).
  Lemma leakauth_pers_mono_row (leakauth1 leakauth2 : label) : ⊢ pers_mono_row (iLblSig_to_iLblThy [([leakauth1], [leakauth2], leakauth leakauth1 leakauth2)]).
  Proof. Admitted.
  Definition leakauth_row (leakauth1 leakauth2 : label) := SemRow [([leakauth1],[leakauth2] , leakauth leakauth1 leakauth2 )] (leakauth_pers_mono_row leakauth1 leakauth2).
  Program Definition envsec_row (keyleak1 keyleak2 leakauth1 leakauth2 : label) :=
    sem_row_union (keyleak_row keyleak1 keyleak2) (leakauth_row leakauth1 leakauth2).

  Program Definition sec_channel_mono (schannel1 schannel2 : label) := {| pmono_prot_car := iThySum (SendSec schannel1 schannel2) (RecvSecB schannel1 schannel2) ; pmono_prot_prop := _ |}.
  Next Obligation.
  Admitted.

  Definition sec_channel (schannel1 schannel2 : label) := @SemSig Σ (sec_channel_mono schannel1 schannel2) (schannel1, schannel2).

  Lemma client_pers_mono_row (channel leaksec getKey1 schannel1 schannel2 : label) : ⊢ pers_mono_row (iLblSig_to_iLblThy [([channel; getKey1; schannel1] , [leaksec; schannel2] , sec_channel schannel1 schannel2)]).
  Proof.
  Admitted.

  Lemma sec_channel_pers_mono_row (schannel1 schannel2 : label) : ⊢ pers_mono_row (iLblSig_to_iLblThy [([schannel1] , [schannel2], sec_channel schannel1 schannel2)]).
  Proof.
  Admitted.
  
  Program Definition sec_channel_row (schannel1 schannel2 : label) := SemRow [([schannel1], [schannel2], sec_channel schannel1 schannel2)] (sec_channel_pers_mono_row schannel1 schannel2).
  Program Definition client_row (channel leaksec getKey1 schannel1 schannel2 : label) := SemRow [([channel; getKey1; schannel1], [leaksec; schannel2], sec_channel schannel1 schannel2)] (client_pers_mono_row channel leaksec getKey1 schannel1 schannel2) .
  
   Definition REAL_CHAN : val :=
    λ: "f",
      (F_OAUTH ||ₗ F_KE_lazy_alice) (CHAN xor "f").
   About CHAN.

   (* we have assumed that the secure channel only provides a fixed direction message passing from Alice to Bob, so this needs to reflect in the types of the thunks given to the secure channel client to raise the secure channel effect*)
   Lemma SEM_TYPED_EFF : ∀ channel leaksec getKey schannel_l schannel_r : label,
    let θ := client_row channel leaksec getKey schannel_l schannel_r in
    ⊢
    (sem_val_typed  ((λ: "m", do: schannel_l InjL "m"), (λ: <>, do: schannel_l InjR bob))%V ((λ: "m", do: schannel_r InjL "m") , (λ: <>, do: schannel_r InjR bob))%V (((𝔾)%T -{ θ }-> 𝟙) × (𝟙 -{ θ }-> (Option 𝔾)))%T)%I.
  Proof.
    unfold sem_val_typed. simpl. intros. 
    iModIntro. rewrite /sem_ty_arr /sem_ty_mbang /sem_ty_option /sem_ty_sum //=. rewrite /sem_ty_prod. 
    iExists (λ: "m", do: schannel_l InjL "m")%V , (λ: "m", do: schannel_r InjL "m")%V , (λ: <>, do: schannel_l InjR bob)%V , (λ: <>, do: schannel_r InjR bob)%V.  repeat iSplit; try iPureIntro; try auto.
    + iModIntro. iIntros (??) "Hw1w1". brel_pures.
      iApply brel_introduction'; try constructor;
      iExists _,_,[],[],_; do 2 (iSplit; [by iPureIntro|]; iSplit; [iPureIntro; apply NeutralEctx_nil|]);
      iSplit; try (iIntros (??) "!# H"; iApply "H").
      simpl. iLeft. unfold sem_ty_group.  
      iDestruct "Hw1w1" as (g) "[%Hw1 %Hw2]".  
      iExists _. repeat iSplit; try iPureIntro; try auto; unfold SendV; try rewrite -> Hw1;
      try rewrite -> Hw2; try reflexivity.
      iModIntro. iApply brel_value. iIntros "$ !>".
      unfold sem_ty_unit; iPureIntro.
      split; reflexivity.
    + iModIntro. iIntros (??) "Hw1w1". unfold sem_ty_unit. 
      iDestruct "Hw1w1" as "[%Hw1 %Hw2]". unfold bob. rewrite -> Hw1. rewrite -> Hw2.
      brel_pures.
      iApply brel_introduction'; try constructor. 
      iExists _,_,[],[],_; do 2 (iSplit; [by iPureIntro|]; iSplit; [iPureIntro; apply NeutralEctx_nil|]);
      iSplit; try (iIntros (??) "!# H"; iApply "H").     simpl. iRight.
      repeat iSplit; try iPureIntro; try auto; unfold RecvV; unfold bob; try rewrite -> Hw1;
        try rewrite -> Hw2; try simpl; try reflexivity.
      iModIntro. iSplit.  
      { iIntros (?). iApply brel_value. iIntros "$ !>".
        iExists _,_; iRight; iPureIntro; repeat (split; first done). exists g. split; reflexivity. }
      { iApply brel_value. iIntros "$ !>".
        iExists _,_; iLeft; iPureIntro; repeat (split; first done); reflexivity. }
    
Qed.

  Lemma G_XOR_CORRECT_l (g1 g2 : vgG) E K X e R :
    let g := (bij_group_xor_sem g1 g2) in
    (* vg_of_int_sem (xor_sem (int_of_vg_sem g1) (int_of_vg_sem g2)) = Some g1 ->*)
     vg_of_int_sem (xor_sem (int_of_vg_sem g1) (int_of_vg_sem g2)) = Some g ->
        (BREL (fill K (SOMEV (vgval g))) ≤ e @ E <|X|> {{R}}) -∗ 
     (BREL (fill K (G_XOR xor (vgval g1) (vgval g2))) ≤ e @ E <|X|> {{R}}).
  Proof. 
    simpl.
    intro Hg1g2.
    iIntros "Hrelxor".
    unfold G_XOR.
    brel_pures. 
   assert (fill (K ++  [AppRCtx vg_of_int  ; AppRCtx (App xor (int_of_vg (vgval g1)))]) (int_of_vg (vgval g2)) = fill K (fill [AppRCtx vg_of_int  ; AppRCtx (App xor (int_of_vg (vgval g1)))] (int_of_vg (vgval g2)))) as Hectxappg2.
   { rewrite fill_app. auto. }
   rewrite -Hectxappg2.
   iApply (brel_int_of_vg_sem_correct_l _ _ g2).
   simpl.
   rewrite fill_app. simpl.
   assert (fill (K ++  [AppRCtx vg_of_int  ; AppLCtx #(int_of_vg_sem g2); AppRCtx xor]) (int_of_vg (vgval g1)) = fill K (fill [AppRCtx vg_of_int  ; AppLCtx #(int_of_vg_sem g2); AppRCtx xor] (int_of_vg (vgval g1)))) as Hectxappg1.
   { rewrite fill_app. auto. }
   rewrite -Hectxappg1.
   iApply (brel_int_of_vg_sem_correct_l _ _ g1).
   rewrite fill_app. simpl.
   assert (fill (K ++ [AppRCtx vg_of_int ]) (xor #(int_of_vg_sem g1) #(int_of_vg_sem g2)) = fill K (fill [AppRCtx vg_of_int] (xor #(int_of_vg_sem g1) #(int_of_vg_sem g2)))) as Hectxxor.
   { rewrite fill_app. auto. }
   rewrite -Hectxxor.
   iApply xor_correct_l.
   { admit. }
   { admit. }
   rewrite fill_app. simpl.
   iApply brel_vg_of_int_correct_l.
   { apply Hg1g2. }
   { simpl. iApply "Hrelxor". }
  Admitted.

(*secure channel only assumes a fixed direction of messag epassing, so this needs to relfect in the type of the thunks that its client receives*)
(*Verification of F_OAUTH[F_KE_L[CHAN[]]] ≤ CHAN_SIM[F_CHAN[]]*)
(*----------------------------------------------------------*)
Lemma F_KE_CHAN_SIM (f1 f2 : val) (L : sem_row Σ) :
 (*(∀ᵣ θₕ, (((𝔾 × 𝟙 + 𝟙) -{ θₕ }-> 𝟙) × 𝟙 + 𝟙 -{ θₕ }-> Option 𝔾) -{ sem_row_union θₕ L }-∘ 𝟙)%T
                 f1 f2 -∗*)
   (∀ᵣ θₕ, ((𝔾 -{ θₕ }-> 𝟙) × (𝟙 -{ θₕ }-> Option 𝔾)) -{ sem_row_union θₕ L }-∘ 𝟙)%T
                 f1 f2 -∗
    BREL REAL_CHAN f1
      ≤ CHAN_SIM_lazy (F_CHAN f2) <|⊥|> {{λ v1 v2,
                                       ∀ (leakauth1 leakauth2 keyleak1 keyleak2 : label),
                                       BREL v1 ((λ: "m", do: leakauth1 (Send "m")), (λ: "m", do: leakauth1 (Recv "m")))%V ((λ: "m", do: keyleak1 (Send "m")), (λ: "m", do: keyleak1 (Recv "m")))%V ≤ v2 ((λ: "m", do: leakauth2 (Send "m")), (λ: "m", do: leakauth2 (Recv "m")))%V ((λ: "m", do: keyleak2 (Send "m")), (λ: "m", do: keyleak2 (Recv "m")))%V <| (iLblSig_to_iLblThy (envsec_row keyleak1 keyleak2 leakauth1 leakauth2 )) ++ (iLblSig_to_iLblThy L) |> {{ (λ w1 w2, 𝟙%T w1 w2)}}}}.
Proof with (repeat foldkont) using G H cg inG0 inG1 inG2 klk1 klk2 lka1 lka2 vg vgg Σ Key Support.
(*  iIntros "Hrelf1f2". 
  repeat simpl.
  unfold REAL_CHAN. brel_pures.
  unfold left_composition. brel_pures. 
  unfold CHAN.
  repeat simpl. brel_pures'.
  
  (*unfold CHAN_SIM, F_OAUTH.*)
  unfold F_KE, F_OAUTH. simpl.   
  
  (*iApply (xor_correct_l ⊤ _ _ _ (CHAN_SIM (F_CHAN f2)) ⊥ _).*)
  unfold F_CHAN, CHAN_SIM, F_KE, F_OAUTH.
 
  
  repeat simpl. brel_pures. iModIntro. iIntros (????).
  brel_pures.
  iApply brel_alloctape_r. iIntros (α) "Hα". brel_pures_r. 
  iApply brel_alloc_r. iIntros (l_sim) "Hl_sim". brel_pures_r. 
  iApply brel_alloc_l. iIntros (l_auth) "!>Hl_auth". brel_pures_l.
  iApply brel_effect_l. iIntros (channel') "!> Hchannel !>". brel_pures_l.
  iApply brel_couple_UT. 1: auto.
  simpl. iFrame "Hα". iSplit => //.
  iIntros (n ?) "!> Hα". brel_pures.
  brel_exp_l. brel_pures.
  iApply brel_effect_l. iIntros (getKey') "!> HgK !>". brel_pures_l.
  iApply brel_effect_r. iIntros (leaksec') "Hleaksec !>". brel_pures.
  iApply brel_alloc_r. iIntros (l_fchan) "Hlfchan". brel_pures_r.
  iApply brel_effect_r. iIntros (schannel_r) "Hschannel_r !>". brel_pures_r.
  brel_pures'. repeat simpl. brel_pures'.
  iApply brel_alloc_l. iIntros (l_rchan) "!>Hlrchan". brel_pures_l.
  iApply brel_effect_l. iIntros (schannel_l) "!> Hschannel_l !>". brel_pures_l.
  set (kl1 := ( match: "payload" with
         InjL "m" =>
           match: ! #l_rchan with
             InjL <> =>
               #l_rchan <- InjR "m";; 
               let: "key" := (λ: "party", do: getKey' "party")%V bob in
               match: "key" with
                 InjL <> => "k" #()%V
               | InjR "x" =>
                 match: G_XOR xor "m" "x" with
                   InjL <> => "k" #()%V
                 | InjR "mg" => (λ: "m", do: channel' InjL "m")%V ("mg", bob);; "k" #()%V
                 end
               end
           | InjR "m" => "k" #()%V
           end
       | InjR <> =>
         let: "key" := (λ: "party", do: getKey' "party")%V alice in
         match: "key" with
           InjL <> => "k" (InjLV #()%V)
         | InjR "key" =>
           let: "r" := (λ: "m", do: channel' InjR "m")%V alice in
           match: "r" with
             InjL <> => "k" (InjLV #()%V)
           | InjR "x" =>
             match: G_XOR xor "x" "key" with
               InjL <> => "k" (InjL #()%V)
             | InjR "mg" => "k" (InjR "mg")
             end
           end
         end
       end )%E ).
  set (kl2 := ( match: "p" with
         InjL <> =>
           (λ: "m", do: keyleak1 Send "m")%V bob;; 
           let: "r" := (λ: "m", do: keyleak1 Recv "m")%V bob in
           match: "r" with
             InjL <> => "k" (InjLV #()%V)
           | InjR "w" => "k" (InjR (vgval (g ^+ n)))
           end
       | InjR <> =>
         let: "r" := (λ: "m", do: keyleak1 Recv "m")%V alice in
         match: "r" with
           InjL <> => "k" (InjLV #()%V)
         | InjR "w" => (λ: "m", do: keyleak1 Send "m")%V alice;; "k" (InjR (vgval (g ^+ n)))
         end
       end )%E).
 set (kl3 := (match: "payload" with
         InjL "payload" =>
           let: "dst" := "payload" in
           let: "m" := Fst "dst" in
           let: "dst" := Snd "dst" in
           match: ! #l_auth with
             InjL <> =>
               #l_auth <- InjR "m";; 
               (λ: "m", do: leakauth1 Send "m")%V ("m", "dst");; "k" #()%V
           | InjR "message" => "k" #()%V
           end
       | InjR "from" =>
         let: "r" := (λ: "m", do: leakauth1 Recv "m")%V "from" in
         match: "r" with
           InjL <> => "k" (InjLV #()%V)
         | InjR "x" => "k" ! #l_auth
         end
              end)%E).
 set (kr1 := ( match: "payload" with
         InjL "m" =>
           match: ! #l_fchan with
             InjL <> =>
               #l_fchan <- InjR "m";; (λ: "m", do: leaksec' InjL "m")%V alice;; "k" #()%V
           | InjR "x" => "k" #()%V
           end
       | InjR <> =>
         let: "r" := (λ: "m", do: leaksec' InjR "m")%V bob in
         match: "r" with
           InjL <> => "k" (InjLV #()%V)
         | InjR "x" => "k" (InjR ! #l_fchan)
         end
       end )%E).
 set (kr2 := ( match: "payload" with
         InjL <> =>
           (λ: "m", do: keyleak2 Send "m")%V bob;; 
           let: "r" := (λ: "m", do: keyleak2 Recv "m")%V bob in
           match: "r" with
             InjL <> => "k" (InjLV #()%V)
           | InjR "x" =>
             match: ! #l_sim with
               InjL <> =>
                 let: "m'" := #()%V;; rand(#lbl:α) #(S n'') in
                 let: "mA" := vexp g "m'" in
                 #l_sim <- InjR "m'";; 
                 (λ: "m", do: leakauth2 Send "m")%V ("mA", bob);; "k" #()%V
             | InjR "m" => "k" #()%V
             end
           end
       | InjR <> =>
         let: "r" := (λ: "m", do: keyleak2 Recv "m")%V alice in
         match: "r" with
           InjL <> => "k" (InjLV #()%V)
         | InjR "x" =>
           "doKeyLeakSend" alice;; 
           let: "rla" := (λ: "m", do: leakauth2 Recv "m")%V bob in
           match: "rla" with InjL <> => "k" (InjLV #()%V) | InjR "x" => "k" ! #l_sim end
         end
       end )%E).
  set (θ := client_row channel' leaksec' getKey' schannel_l schannel_r).
  iSpecialize ("Hrelf1f2" $! θ).
  unfold sem_ty_arr, sem_ty_mbang. simpl.
  iAssert (sem_val_typed  ((λ: "m", do: schannel_l InjL "m"), (λ: "from", do: schannel_l InjR "from"))%V ((λ: "m", do: schannel_r InjL "m") , (λ: "from", do: schannel_r InjR "from"))%V (((𝔾 ×(𝟙 + 𝟙))%T -{ θ }-> 𝟙) × ((𝟙 + 𝟙)%T -{ θ }-> (Option 𝔾)))%T) as "Hschn".
  { iApply SEM_TYPED_EFF. }
  unfold sem_val_typed. simpl.
  iDestruct "Hschn" as "#Hschn".
  iSpecialize ("Hrelf1f2" with "Hschn"). simpl.  
  set (d1 := ((α ↪ₛN (S n''; [n])) ∗ l_sim ↦ₛ NONEV ∗ l_auth ↦ NONEV ∗ l_fchan ↦ₛ NONEV ∗ l_rchan ↦ NONEV)%I).
  (*set (d2 := ((∃ g m, α ↪ₛ□ (S n''; []) ∗ l_sim ↦ₛ□ SOMEV #n ∗
                  l_auth ↦□ SOMEV (vgval
                                     (bij_group_xor_sem m (g ^+ n)))%V ∗  l_fchan ↦ₛ□ SOMEV (vgval g) ∗  l_rchan ↦□ SOMEV (vgval g))%I)).*)
  set (d2 := ((∃ g m, α ↪ₛ□ (S n''; []) ∗ l_sim ↦ₛ□ SOMEV #n ∗
                  l_auth ↦□ SOMEV (vgval
                                     (bij_group_xor_sem m (g ^+ n)))%V ∗  l_fchan ↦ₛ□ SOMEV (vgval m) ∗  l_rchan ↦□ SOMEV (vgval m))%I)).

  set (d3 := (∃ g, (α ↪ₛN (S n''; [n])) ∗ l_fchan ↦ₛ□ SOMEV (vgval g) ∗  l_rchan ↦□ SOMEV (vgval g) ∗  l_sim ↦ₛ NONEV ∗ l_auth ↦ NONEV)%I).
  (* set (d3 := (∃ m, (α ↪ₛN (S n''; [n])) ∗ l_fchan ↦ₛ□ SOMEV m ∗  l_rchan ↦□ SOMEV m ∗  l_sim ↦ₛ NONEV ∗ l_auth ↦ NONEV)%I).*)


  (* TODO: actually define f parametrised by m and n. *)
  set (f m n := 42).
  (* Proposed new invariant: *)
    set (new_inv :=  (
 (l_sim ↦ₛ NONEV ∗ l_auth ↦ NONEV ∗ l_fchan ↦ₛ NONEV ∗ l_rchan ↦ NONEV ∗ l_key ↦□ None ∗ l_m' ↦ₛ□ None)
 ∨
 (∃ m n,
     (* l_rchan  ↦□ Some m ∗ l_fchan ↦□ Some m ∗ l_key ↦ None l_m' ↦ None l_sim ↦ None ∗ l_auth ↦ None
        ∨ *)
     (* Sender provided the message, the key is sampled (and coupled to the random ciphertext) *)
     l_rchan  ↦□ Some m ∗ l_fchan ↦ₛ□ Some m ∗ l_key ↦□ Some g^(f m n) ∗ l_m' ↦ₛ□ Some n ∗ l_sim ↦ₛ None ∗ l_auth ↦ None
     ∨
     l_rchan  ↦□ Some m ∗ l_fchan ↦ₛ□ Some m ∗ l_key ↦□ Some g^(f m n) ∗ l_m' ↦ₛ□ Some n ∗ l_auth ↦□ Some (xor m (g^n)) ∗ l_sim ↦ₛ□ Some n
        ))%I).


  iApply (brel_na_alloc (d1 ∨ (d2 ∨ d3))%I alphaN).
   iSplitL "Hα Hl_sim Hl_auth Hlfchan Hlrchan"; [iNext; iLeft; iFrame|].
   iIntros "#Hinvα".
   iApply brel_new_theory.
   iApply (brel_add_label_l with "Hschannel_l").
   iApply (brel_add_label_r with "Hschannel_r").
   iApply (brel_add_label_l with "HgK").
   iApply (brel_add_label_l with "Hchannel").
   iApply (brel_add_label_r with "Hleaksec").
   set (X :=  iLblSig_to_iLblThy [([schannel_l] , [schannel_r] , sec_channel schannel_l schannel_r)]).
   set (R := (λ u1 u2 : val, 𝟙%T u1 u2)).
   set (X' := sec_channel schannel_l schannel_r).
   iApply brel_learn. iIntros "%Hdist' _".
   About brel_exhaustion.
   iApply ((brel_exhaustion (f1 ((λ: "m", do: schannel_l InjL "m"),(λ: "from", do: schannel_l InjR "from"))%V) (f2 ((λ: "m", do: schannel_r InjL "m"),(λ: "from", do: schannel_r InjR "from"))%V) _ _ X' _ _ R _ _ _) with "[Hrelf1f2]"); try simpl; try auto; try (apply sublist_subseteq); try (apply singleton_sublist_l);
     try (apply list_elem_of_In); try simpl; try auto; try (repeat (eapply sublist_skip)) ; try eapply sublist_nil_l.
   {
     set clt := ([channel'; getKey'; schannel_l], [leaksec'; schannel_r], X').
     set cltheory := iLblSig_to_iLblThy [([channel'; getKey'; schannel_l] , [leaksec'; schannel_r] , X')].
     set (L' := cltheory ++ (iLblSig_to_iLblThy L)).
     set (keytheory := iLblSig_to_iLblThy [([keyleak1], [keyleak2], keyleak keyleak1 keyleak2)]).
     set (leaktheory := (iLblSig_to_iLblThy [([leakauth1], [leakauth2], leakauth leakauth1 leakauth2)])).
     set (M := cltheory ++ keytheory ++ leaktheory ++ (iLblSig_to_iLblThy L)).
      iApply (brel_introduction_mono L' M).
     + simpl.
       iApply to_iThy_le_intro'.
       unfold L'. unfold M.  
       set (l := cltheory ++ keytheory ++ leaktheory).
      
       apply (submseteq_skips_r (iLblSig_to_iLblThy L) (cltheory) (cltheory ++ keytheory ++ leaktheory)).
       eapply submseteq_inserts_r. eapply Permutation_submseteq. auto.
     + unfold L'. iApply "Hrelf1f2". } 
    iLöb as "IH".
   unfold kl1.
   iSplit; [iIntros (v1 v2) "%Hv1v2"; iModIntro; brel_pures; iModIntro; done |].  
   iIntros (?????) "!# %Hk1 %Hk2 HXQ #Hrel".  
   iDestruct "HXQ" as "[HSendAlice | HRecvBob]".
   (* Send a message using the secure channel from Alice To Bob *)
   + iDestruct "HSendAlice" as (?m) "[[%He1 %He2] #HmQ]".
      rewrite -> He1. rewrite -> He2. brel_pures.
         { apply -> NeutralEctx_ectx_labels_singleton.
           do 2 (eapply NeutralEctx_label_cons_inv_2 in Hk1). eapply Hk1. }
         {  apply -> NeutralEctx_ectx_labels_singleton.
            eapply NeutralEctx_label_cons_inv_2 in Hk2.
            eapply NeutralEctx_label_cons_inv_1 in Hk2. eapply Hk2. } 
         iApply (brel_na_inv _ _ alphaN); first set_solver.
         iFrame "Hinvα".
         iIntros "([(>Hα & >Hl_sim & >Hl_auth & >Hl_fchan & >Hl_rchan) | [>Hd2 | >Hd3 ]] & Hclose)".
         (*iIntros "([(>Hα & >Hl_sim & >Hl_auth & >Hl_fchan & >Hl_rchan) | #>Hpersrfsa] & Hclose)".*)
         (*iFrame "Hinvβ".
         iIntros "([(>Hl_fchan  & >Hl_rchan) | #>Hrfchan] & Hclose)".*)
          (* First message to be sent by the secure channel*)
        ++ About brel_load_r.
           iApply (brel_load_r _ _ _ _ [HandleCtx _ _ _ _ _ ; CaseCtx _ _] with "Hl_fchan").
           iIntros "Hl_fchan".
           iApply (brel_load_l _ _ _  [HandleCtx Deep MS channel' _ _ ; HandleCtx Deep MS getKey' _ _; CaseCtx _ _] with "Hl_rchan").
           iIntros "!>Hl_rchan". brel_pures.
           simpl. brel_pures. 
           iApply (brel_store_r _ _ _ _ [HandleCtx _ _ _ _ _ ; AppRCtx _] with "Hl_fchan"). iIntros "Hl_fchan".
           simpl.
           brel_pures.
           { simpl. apply not_elem_of_nil. }
           iApply (brel_store_l _ _ _  [HandleCtx _ _ _ _ _ ; HandleCtx _ _ _ _ _ ; AppRCtx _] with "Hl_rchan"). 
           iIntros "!>Hl_rchan". brel_pures; try (simpl); try (apply not_elem_of_nil).
           repeat foldkont.
            set (keytheory := iLblSig_to_iLblThy [([keyleak1], [keyleak2], keyleak keyleak1 keyleak2)]).
            set (leaktheory := (iLblSig_to_iLblThy [([leakauth1], [leakauth2], leakauth leakauth1 leakauth2)])).
            set (M := [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)] ++ leaktheory ++ (iLblSig_to_iLblThy L)).
            set (N := [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)] ++ keytheory ++ leaktheory ++ (iLblSig_to_iLblThy L)).
            iApply fupd_brel.
             iMod (ghost_map_elem_persist with "Hl_fchan") as "#Hl_fchan".
             iMod (ghost_map_elem_persist with "Hl_rchan") as "#Hl_rchan".
             iModIntro.
             iApply brel_na_close. iFrame.
             iSplitL.
             { iModIntro. iRight. iRight. unfold d3. iExists _. iFrame "Hα Hl_fchan Hl_rchan Hl_sim Hl_auth". } 
             iApply (brel_bind'' [HandleCtx Deep _ _ _ _; AppRCtx _] [AppRCtx _] keytheory M N (𝟙%T) (Do keyleak1 (InjLV bob)) (Do keyleak2 (InjLV bob))).
             { simpl. set_solver. }
             { simpl. set_solver. }
             { simpl. unfold M. unfold N. iApply to_iThy_le_intro'. eapply Permutation_submseteq.
               eapply perm_swap. }
             {  iApply (brel_introduction' [keyleak1] [keyleak2]).
                1: { unfold keytheory.
                     eapply list_elem_of_here. }
                iExists _, _, [], [],_.
                do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
                iSplitL;  [|by iIntros "!>" (??) "H"; iApply "H"].
                iRight. iLeft. simpl. 
                repeat (iSplit; try (iPureIntro); try (unfold SendV); try reflexivity).
                iModIntro.
                 iApply brel_value.
                 iIntros "$ !>". brel_pures.
                 iAssert (distinct' N) as "%Hdistinct".
                { unfold N. unfold keytheory. unfold leaktheory. simpl.
                  unfold distinct'. iPureIntro. apply Hdist'. }
                iApply (brel_bind'' _ _ keytheory M N 𝟙%T (Do keyleak1 (InjRV bob)) (Do keyleak2 (InjRV bob))).
                { simpl. unfold M.  repeat (rewrite -> labels_l_cons). set_solver. }
                { simpl. apply list_subseteq_nil. }
                { simpl. unfold M. unfold N. iApply to_iThy_le_intro'. eapply Permutation_submseteq.
               eapply perm_swap. }
                { iApply (brel_introduction' [keyleak1] [keyleak2]).
                1: { unfold keytheory.
                     eapply list_elem_of_here. }
                iExists _, _, [], [],_.
                do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
                iSplitL;  [|by iIntros "!>" (??) "H"; iApply "H"].
                iRight. iRight. simpl.
                repeat (iSplit; try (iPureIntro); try (unfold RecvV); try reflexivity);
                  try (iModIntro); simpl. iSplitL.
               +++    iApply brel_value.
                      iIntros "$ !>". brel_pures.
                      simpl. brel_pures.
                      iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)). 
                      { simpl. auto. }
                      { simpl. repeat (eapply list_subseteq_skip). eapply list_subseteq_nil. }
                      { iApply "Hrel". iApply "HmQ". }
                      { iApply "IH". }
                  +++ iApply brel_value.
                      iIntros "$ !>".
                      unfold kont.
                      brel_pures. 
                      iApply (G_XOR_CORRECT_l m (g ^+ n) _ _ _ _).
                      {admit. }
                      brel_pures.
                       { simpl. unfold distinct in Hdistinct. destruct Hdistinct.
                        unfold distinct_l in H1. (*unfold LblClients in H1. simpl in H1.*)
                        unfold N in H1. simpl in H1.
                        repeat (rewrite -> labels_l_cons in H1).
                        eapply NoDup_app in H1.
                        Print val.
                        eapply NoDup_cons_1_1. destruct H1 as [H1' H2'].
                        apply (NoDup_app [channel'; getKey'] [schannel_l]) in H1'.
                        destruct H1' as [H1' H2'']. apply H1'.  }
                       {  simpl.
                        iApply (brel_na_inv _ _ alphaN); first set_solver.
                        iFrame "Hinvα".  
                        iIntros "([ (>Hα & >Hl_sim & >Hl_auth & >Hl_fchan' & >Hl_rchan') | [>Hd2 | >Hd3]] & Hclose)".
                         (*contradiction branch as the first message has been sent and stored*)
                          -
                            Search (_ ↦ₛ _)%I.
                            admit.
                          -
                            unfold d2.
                            iDestruct "Hd2" as (?g ?m) "(Hα & (Hl_sim & (Hl_auth & (Hl_fchan' & Hl_rchan'))))".
                            iApply (brel_load_l _ _ _ [CaseCtx _ _] with "Hl_auth").                                          
                          iIntros "!> Hl_auth".
                          simpl. brel_pures_l.
                          iApply (brel_load_r _ _ _ _ [CaseCtx _ _] with "Hl_sim").
                          iIntros "Hl_sim". brel_pures. simpl.
                          iApply fupd_brel.
                          iModIntro.
                          iApply brel_na_close. iFrame.
                          iSplitL.
                          { iModIntro. iRight. iLeft. iFrame "Hα Hl_sim Hl_auth Hl_fchan' Hl_rchan'". }
                         
                brel_pures. 
                iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)).
                            { simpl. auto. }
                            { simpl. auto. (*admit.*) }
                            { iApply "Hrel". iApply "HmQ". }
                            { iApply "IH". }
                          - unfold d3.
                            iDestruct "Hd3" as (?g) "(Hα & (Hl_fchan' & (Hl_rchan' & (Hl_sim & Hl_auth))))".
                            iApply (brel_load_l _ _ _ [CaseCtx _ _] with "Hl_auth").                                          
                          iIntros "!> Hl_auth".
                          simpl. brel_pures_l.
                          iApply (brel_load_r _ _ _ _ [CaseCtx _ _] with "Hl_sim").
                          iIntros "Hl_sim". brel_pures. simpl.
                          iApply (brel_randT_r _ [AppRCtx _ ] with "Hα").
                          iIntros "Hα %Hn".
                          brel_pures.
                          repeat foldkont.
                          iApply (brel_exp_r [AppRCtx _]).
                          brel_pures. 
                          iApply (brel_store_r _ _ _ _ [AppRCtx _] with "Hl_sim").
                          iIntros "Hl_sim". rel_pures. 
                          iApply (brel_store_l _ _ _ [AppRCtx _] with "Hl_auth").
                          iIntros "!> Hl_auth". brel_pures.
                          iApply fupd_brel.
                          iMod (ghost_map_elem_persist with "Hl_sim") as "#Hl_sim".
                          iMod (ghost_map_elem_persist with "Hl_auth") as "#Hl_auth".
                          iDestruct "Hα" as (ns) "(%Hf & Hα)".
                          apply map_eq_nil in Hf. simplify_eq.
                          iMod (ghost_map_elem_persist with "Hα") as "#Hα".
                          iModIntro.
                          iApply brel_na_close. iFrame.
                          iSplitL; [iModIntro; iRight; iLeft; iFrame "#" |].
                          simpl. brel_pures.
                          set (g_sem := (bij_group_xor_sem m (valgroup.g ^+ n))).
                          About brel_bind. 
                           iPoseProof (brel_bind [AppRCtx (λ: <>, kont1 #()%V)]
                      [AppRCtx (λ: <>, kont0 #()%V)]
                      ⊤ leaktheory N  𝟙%T
                      (Do leakauth1 (InjLV (vgval g_sem, bob)))
                      (Do leakauth2 (InjLV (vgval (valgroup.g ^+ n), bob)))) as "Hbind".
                      iApply "Hbind".
                         { simpl. unfold leaktheory. auto.
                            iApply (traversable_ectx_labels _ _ [] [] iThyBot _).
                            + unfold kont1. simpl. auto.
                            + unfold kont0. simpl. auto.
                            + simpl. unfold distinct.
                              unfold distinct_l, distinct_r.
                              unfold labels_l, labels_r. simpl.
                              split; eapply NoDup_singleton.
                            }
                            { simpl. unfold N. iApply to_iThy_le_intro'. 
                              set (k1 :=  [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], iThyBot)] ++ keytheory).
                              apply (submseteq_middle leaktheory k1 (iLblSig_to_iLblThy L)). }
                          { iApply (brel_introduction' [leakauth1] [leakauth2]); try (unfold leaktheory);
                            try (apply list_elem_of_here).
                           iExists _, _, [], [],_.
                do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
                iSplitL;  [|by iIntros "!>" (??) "H"; iApply "H"].
                iLeft. iLeft. simpl.
                iExists _,_. repeat (iSplit; try (iPureIntro); try (unfold SendV); try reflexivity). 
                iModIntro. iApply brel_value. iIntros "$ !>".
                brel_pures. 
                iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)).
                            { simpl. auto. }
                            { simpl. auto. (*admit.*) }
                            { iApply "Hrel". iApply "HmQ". }
                            { iApply "IH". }          }  }  }  }
        (* A message has already been sent by the secure channel *)     
        ++ unfold d2.
           iDestruct "Hd2" as (?g ?m) "(Hα & (Hl_sim & (Hl_auth & (Hl_fchan & Hl_rchan)))) ".
           iDestruct "Hl_fchan" as "#Hl_fchan".
           iDestruct "Hl_rchan" as "#Hl_rchan".
           iApply (brel_load_l _ _ _  [HandleCtx _ _ _ _ _ ; HandleCtx _ _ _ _ _ ; CaseCtx _ _] with "Hl_rchan").
           iIntros "!> Hl_rchan'".
           brel_pures.
           iApply (brel_load_r _ _ _ _  [HandleCtx _ _ _ _ _ ; CaseCtx _ _] with "Hl_fchan").
           iIntros "Hl_fchan'".
           brel_pures.
           iApply brel_na_close. iFrame.
           iSplitL.
           { iModIntro. iRight. iLeft. iFrame. }
           iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)).
           { simpl. auto. }
           { simpl. auto. (*admit.*) }
           { iApply "Hrel". iApply "HmQ". }
           { iApply "IH". }         
        ++ unfold d3.
           iDestruct "Hd3" as (?g) "(Hα & (Hl_fchan & (Hl_rchan & (Hl_sim & Hl_auth))))".                iApply (brel_load_l _ _ _  [HandleCtx _ _ _ _ _ ; HandleCtx _ _ _ _ _ ; CaseCtx _ _] with "Hl_rchan").
           iIntros "!> Hl_rchan'".
           brel_pures.
           iApply (brel_load_r _ _ _ _  [HandleCtx _ _ _ _ _ ; CaseCtx _ _] with "Hl_fchan").
           iIntros "Hl_fchan'".
           brel_pures.
           iApply brel_na_close. iFrame.
           iSplitL.
           { iModIntro. iRight. iRight. iFrame. }
           iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)).
           { simpl. auto. }
           { simpl. auto. (*admit.*) }
           { iApply "Hrel". iApply "HmQ". }
           { iApply "IH". }      
           (* Bob receives the message *) 
   + iDestruct "HRecvBob" as "[%He1 [%He2 #HmQ]]". 
     rewrite -> He1. rewrite -> He2. brel_pures.
     { split.
       + apply -> NeutralEctx_ectx_labels_singleton.
         do 2 (eapply NeutralEctx_label_cons_inv_2 in Hk1). eapply Hk1.
       + simpl. set_solver. }
     { split.
       + apply -> NeutralEctx_ectx_labels_singleton.
            eapply NeutralEctx_label_cons_inv_2 in Hk2.
            eapply NeutralEctx_label_cons_inv_1 in Hk2. eapply Hk2.
       + simpl. set_solver. }
     brel_pures.
      set (keytheory := iLblSig_to_iLblThy [([keyleak1], [keyleak2], keyleak keyleak1 keyleak2)]).
         set (leaktheory := (iLblSig_to_iLblThy [([leakauth1], [leakauth2], leakauth leakauth1 leakauth2)])).
         set (M := [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)]).
         set (N := [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)] ++ keytheory ++ leaktheory ++ (iLblSig_to_iLblThy L)).
         iApply (brel_bind'' _ _ keytheory M N _ (Do keyleak1 (InjRV alice)) (Do keyleak2 (InjRV alice))).
          { simpl. unfold M. unfold labels_l. simpl.  apply (list_subseteq_skip channel' [] [getKey'; schannel_l]). set_solver. }
        { simpl. unfold M. unfold labels_r. simpl. set_solver. }
        { iApply to_iThy_le_intro'. unfold M. unfold N.
          eapply submseteq_sublist_r.
          exists ([([channel'; getKey'; schannel_l], [leaksec'; schannel_r],
                 iThyBot)] ++ keytheory). split.
          + repeat simpl. unfold keytheory. simpl. eapply Permutation_swap.
          + set (l1 :=  [([channel'; getKey'; schannel_l], [leaksec'; schannel_r],
                            iThyBot)] ++ keytheory).
            set (l2 := leaktheory ++ iLblSig_to_iLblThy L).
            apply (sublist_inserts_r l2 l1 l1). auto. }
        {  iApply (brel_introduction' [keyleak1] [keyleak2]).
           { unfold keytheory. eapply list_elem_of_here. }
           { iExists _, _, [], [],_.
             do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
             iSplitL;  [|by iIntros "!>" (??) "H"; iApply "H"].
             iLeft. iRight. simpl.
             repeat (iSplit; try (iPureIntro); try (unfold RecvV); try reflexivity).
              iModIntro.
              iSplitL.
              { repeat foldkont.
                iApply brel_value. 
                iIntros "$ !>". brel_pures.
                 iApply (brel_exhaustion (fill k1' (InjLV #()%V)) (fill k2' (InjLV #()%V))).
                          { simpl. set_solver. }
                          { simpl. set_solver. }
                          { iApply "Hrel".  iDestruct "HmQ" as "[Hsome Hnone]". iApply "Hnone". }
                          {iApply "IH". } }
              { repeat foldkont.
                iApply brel_value. iIntros "$ !>". brel_pures.
                iApply (brel_bind'' _ _ keytheory M N _ (Do keyleak1 (InjLV alice)) (Do keyleak2 (InjLV alice))).
                { simpl. unfold M. unfold labels_l. simpl. apply (list_subseteq_skip channel' [] [getKey'; schannel_l]). set_solver. }
                { simpl. unfold M. unfold labels_r. simpl. set_solver. }
                {  iApply to_iThy_le_intro'. unfold M. unfold N. solve_submseteq. }
                iApply (brel_introduction' [keyleak1] [keyleak2]).
                1: { unfold keytheory.
                     eapply list_elem_of_here. }
                iExists _, _, [], [],_.
                do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
                iSplitL;  [|by iIntros "!>" (??) "H"; iApply "H"].
                iLeft. iLeft. simpl.
                repeat (iSplit; try (iPureIntro); try (unfold SendV); try reflexivity).
                iModIntro. iApply brel_value. 
                iIntros "$ !>". brel_pures.
                { simpl. unfold distinct in Hdist'. destruct Hdist' as [Hdl HdR].
                       unfold distinct_l in Hdl. unfold labels_l in Hdl. simpl in Hdl.
                       Search "NoDup".
                       assert (HNoDup : NoDup [channel'; getKey']).
                       { About sublist_NoDup. eapply sublist_NoDup; [eapply Hdl| auto].
                         eapply (sublist_inserts_r _ [channel'; getKey'] [channel'; getKey']). auto. }
                       Search "NoDup". apply NoDup_cons_1_1 in HNoDup. auto. }
                brel_pures.
                repeat foldkont.
                iApply (brel_bind'' _ _ leaktheory M N _ (Do leakauth1 (InjRV bob)) (Do leakauth2 (InjRV bob))).
                      { simpl. unfold M. unfold labels_l. simpl. set_solver. }
                      { simpl. unfold M. unfold labels_r. simpl. set_solver. }
                      {  iApply to_iThy_le_intro'. unfold M. unfold N. Search "⊆+".
          eapply submseteq_sublist_r.
          exists ([([channel'; getKey'; schannel_l], [leaksec'; schannel_r],
                 iThyBot)] ++ leaktheory). split.
          + repeat simpl. unfold leaktheory. simpl. eapply Permutation_swap.
          + eapply sublist_skip. eapply sublist_inserts_l. eapply sublist_inserts_r. auto. }
                      { iApply (brel_introduction' [leakauth1] [leakauth2]).
                        1: { unfold leaktheory.
                             eapply list_elem_of_here. }
                        simpl.
                        iExists _, _, [], [],_.
                        do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
                        iSplitL;  [|by iIntros "!>" (??) "H"; iApply "H"].
                        iRight. iRight. simpl.
                        repeat (iSplit; try (iPureIntro); try (unfold RecvV); try reflexivity).
                        iModIntro. iSplit.
                        (* leakauth returns successfully with a value *)
                        -  iIntros (b1 b2). iApply brel_value. iIntros "$ !>".
                           brel_pures. simpl.
                           iApply (brel_na_inv _ _ alphaN); first set_solver.
                           iFrame "Hinvα".
                           iIntros "([(>Hα & >Hl_sim & >Hl_auth & >Hl_fchan & >Hl_rchan) | [>Hd2 | >Hd3 ]] & Hclose)".
                           (*no message has been sent by the secure channel yet*)
                           ++ simpl. brel_pures.
                              iApply (brel_load_r _ _ _ _ [AppRCtx _] with "Hl_sim").
                              iIntros "Hl_sim".
                              iApply (brel_load_l _ _ _ [AppRCtx _] with "Hl_auth").
                              iIntros "!>Hl_auth".
                              simpl.
                              brel_pures.
                              repeat foldkont.
                              iApply brel_na_close. iFrame.
                              iSplitL; [iModIntro; iLeft; iFrame |].
                              iApply (brel_exhaustion (fill k1'(InjLV #()%V)) (fill k2' (InjLV #()%V))).
                               { simpl. auto. }
                               { simpl. set_solver. }
                               { iApply "Hrel". iDestruct "HmQ" as "[Hsome Hnone]". iApply "Hnone".  }
                               { iApply "IH". }
                               (* a message has  been sent by the secure channel and is yet to be receievd by the authenticated channel *)
                           ++ simpl. brel_pures. 
                              unfold d2.
                              iDestruct "Hd2" as (?g ?m) "(Hα & (Hl_sim & (Hl_auth & (Hl_fchan & Hl_rchan)))) ".
                              iApply (brel_load_r _ _ _ _ [AppRCtx _] with "Hl_sim").
                              iIntros "Hl_sim'".
                              iApply (brel_load_l _ _ _ [AppRCtx _] with "Hl_auth").
                              iIntros "!>Hl_auth'".
                              iDestruct "Hl_fchan" as "#Hl_fchan".
                               iApply brel_na_close. iFrame.
                               iSplitL; [iModIntro; iRight; iLeft; iFrame; iFrame "#" |].
                               brel_pures.
                               iApply G_XOR_CORRECT_l.
                               { admit. }
                               brel_pures.
                               Print ectx.
                               Print frame.
                               iApply (brel_load_r _ _ _ _ [HandleCtx _ _ _ _ _ ; AppRCtx _ ; InjRCtx ] with "Hl_fchan").
                               iIntros "Hl_fchan'".
                               brel_pures.
                                set (g_enc := (bij_group_xor_sem
                                        (bij_group_xor_sem m (g ^+ n))
                                        (valgroup.g ^+ n))).
                               iApply (brel_exhaustion (fill k1'((InjRV (vgval g_enc))%V)) (fill k2' ((InjRV (InjRV (vgval m)))%V))).
                               { simpl. auto. }
                                { simpl. set_solver. }
                               { unfold kont0. iApply "Hrel". iDestruct "HmQ" as "[Hsome Hnone]". unfold xor. iApply "Hsome". }
                               { iApply "IH". }
                               (* a message has been sent by both the secure channel and the authenticated channel*)
                           ++ simpl. brel_pures.
                              unfold d3.
                               iDestruct "Hd3" as (?g) "(Hα & (Hl_fchan & (Hl_rchan & (Hl_sim & Hl_auth)))) ".
                              iApply (brel_load_r _ _ _ _ [AppRCtx _] with "Hl_sim").
                              iIntros "Hl_sim'".
                              iApply (brel_load_l _ _ _ [AppRCtx _] with "Hl_auth").
                              iIntros "!>Hl_auth'".
                              iDestruct "Hl_fchan" as "#Hl_fchan".
                               iApply brel_na_close. iFrame.
                               iSplitL; [iModIntro; iRight; iRight; iFrame; iFrame "#" |].
                               brel_pures.
                               iApply (brel_exhaustion (fill k1' (InjLV #()%V)) (fill k2' (InjLV #()%V))).
                          { simpl. set_solver. }
                          { simpl. set_solver. }
                          { iApply "Hrel".  iDestruct "HmQ" as "[Hsome Hnone]". iApply "Hnone". }
                          {iApply "IH". }
                        - iApply brel_value.
                          iIntros "$ !>". brel_pures.
                          iApply (brel_exhaustion (fill k1' (InjLV #()%V)) (fill k2' (InjLV #()%V))).
                          { simpl. set_solver. }
                          { simpl. set_solver. }
                          { iApply "Hrel".  iDestruct "HmQ" as "[Hsome Hnone]". iApply "Hnone". }
                          {iApply "IH". } } } }}*)
Admitted.
                             
(*refinement in terms of semantic types for REAL_CHAN ≤ CHAN_SIM (F_CHAN) *)
(*-------------------------------------------------------------------*)

Lemma SEM_F_KE_CHAN_SIM (f1 f2 : val) (L : sem_row Σ) :
  (* (∀ᵣ θₕ, (((𝔾 × 𝟙 + 𝟙) -{ θₕ }-> 𝟙) × 𝟙 + 𝟙 -{ θₕ }-> Option 𝔾) -{ sem_row_union θₕ L }-∘ 𝟙)%T
                 f1 f2 -∗*)
    (∀ᵣ θₕ, ((𝔾 -{ θₕ }-> 𝟙) × (𝟙 -{ θₕ }-> Option 𝔾) -{ sem_row_union θₕ L }-∘ 𝟙))%T
                 f1 f2 -∗
    BREL REAL_CHAN f1
      ≤ CHAN_SIM_lazy (F_CHAN f2) <|⊥|> {{λ v1 v2,
                                       (∀ᵣ θ₁, ∀ᵣ θ₂,  (((𝔾 × (𝟙 + 𝟙)) -{ θ₁ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ₁ }-> Option 𝟙)) ⊸ ((((𝟙 + 𝟙) -{ θ₂ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ₂ }-> Option 𝟙)) -{ sem_row_union (sem_row_union θ₁ θ₂) L }-∘ 𝟙))%T v1 v2 }}.
                                      (* (∀ᵣ θ₁, ∀ᵣ θ₂,  (((𝔾 × (𝟙 + 𝟙)) -{ θ₁ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ₁ }-> Option 𝔾)) ⊸ (((𝔾 × (𝟙 + 𝟙)) -{ θ₂ }-> 𝟙) ×(𝟙 + 𝟙) -{ θ₂ }-> Option 𝔾) -{ sem_row_union (sem_row_union θ₁ θ₂) L }-∘ 𝟙)%T v1 v2 }}.*)
Proof with (repeat foldkont) using G.
 (* iIntros "Hrelf1f2". 
  repeat simpl. 
  unfold REAL_CHAN. brel_pures.
  unfold left_composition. brel_pures.
  unfold CHAN.
  repeat simpl. brel_pures'.
  
  (*unfold CHAN_SIM, F_OAUTH.*)
 
  (*iApply (xor_correct_l ⊤ _ _ _ (CHAN_SIM (F_CHAN f2)) ⊥ _).*)
  unfold F_CHAN, CHAN_SIM. (*F_KE, F_OAUTH.*) 
   
  repeat simpl. brel_pures. iModIntro. iIntros (autheff keyeff). 
  simpl.
  iIntros (autheff_l autheff_r) "Hautheff". 
  iDestruct "Hautheff" as (asnd_l asnd_r arcv_l arcv_r) "(%H1al & %H2al & (#Hasnd & #Harcv))".  
  brel_pures. iModIntro.
  iIntros (keyeff_l keyeff_r) "Hkeyeff".
  iDestruct "Hkeyeff" as (kysnd_l kysnd_r kyrcv_l kyrcv_r) "(%H1k & %H2k & (#Hkeysnd & #Hkeyrcv))".
  (*iDestruct "Hkeyeff" as "(%Hkeyeff_l & (%Hkeyeff_r & Hkeyeffrel))".
  rewrite Hkeyeff_l. rewrite Hkeyeff_r.*)
  rewrite H1al. rewrite H2al. rewrite H1k. rewrite H2k.
  brel_pures.
  unfold F_OAUTH, F_KE.
  brel_pures.  
 
  iApply brel_alloctape_r. iIntros (α) "Hα". brel_pures_r. 
  iApply brel_alloc_r. iIntros (l_sim) "Hl_sim". brel_pures_r. 
  iApply brel_alloc_l. iIntros (l_auth) "!>Hl_auth". brel_pures_l.
  iApply brel_effect_l. iIntros (channel') "!> Hchannel !>". brel_pures_l.
  iApply brel_couple_UT. 1: auto.
  simpl. iFrame "Hα". iSplit => //.
  iIntros (n ?) "!> Hα". brel_pures.
  brel_exp_l. brel_pures.
  iApply brel_effect_l. iIntros (getKey') "!> HgK !>". brel_pures_l.
  iApply brel_effect_r. iIntros (leaksec') "Hleaksec !>". brel_pures.
  iApply brel_alloc_r. iIntros (l_fchan) "Hlfchan". brel_pures_r.
  iApply brel_effect_r. iIntros (schannel_r) "Hschannel_r !>". brel_pures_r.
  brel_pures'. repeat simpl. brel_pures'.
  iApply brel_alloc_l. iIntros (l_rchan) "!>Hlrchan". brel_pures_l.
  iApply brel_effect_l. iIntros (schannel_l) "!> Hschannel_l !>". brel_pures_l.
  set (kl1 := ( match: "payload" with
         InjL "payload" =>
           let: "dst" := "payload" in
           let: "m" := Fst "dst" in
           let: "dst" := Snd "dst" in
           match: ! #l_rchan with
             InjL <> =>
               #l_rchan <- InjR "m";; 
               let: "key" := (λ: "party",
                                do: getKey' "party")%V
                               bob in
               match: "key" with
                 InjL <> => "k" #()%V
               | InjR "x" =>
                 match: G_XOR xor "m" "x" with
                   InjL <> => "k" #()%V
                 | InjR "mg" =>
                   (λ: "m", do: channel' InjL "m")%V
                     ("mg", bob);; 
                   "k" #()%V
                 end
               end
           | InjR "m" => "k" #()%V
           end
       | InjR <> =>
         let: "key" := (λ: "party",
                          do: getKey' "party")%V
                         alice in
         match: "key" with
           InjL <> => "k" (InjLV #()%V)
         | InjR "key" =>
           let: "r" := (λ: "m",
                          do: channel' InjR "m")%V
                         bob in
           match: "r" with
             InjL <> => "k" (InjLV #()%V)
           | InjR "x" =>
             match: G_XOR xor "x" "key" with
               InjL <> => "k" (InjL #()%V)
             | InjR "mg" => "k" (InjR "mg")
             end
           end
         end
       end)%E ).
  set (kl2 := ( match: "p" with
         InjL <> =>
           kysnd_l bob;; 
           let: "r" := kyrcv_l bob in
           match: "r" with
             InjL <> => "k" (InjLV #()%V)
           | InjR "w" => "k" (InjR (vgval (g ^+ n)))
           end
       | InjR <> =>
         let: "r" := kyrcv_l alice in
         match: "r" with
           InjL <> => "k" (InjLV #()%V)
         | InjR "w" =>
           kysnd_l alice;; "k" (InjR (vgval (g ^+ n)))
         end
       end )%E).
  set (kl3 := ( match: "payload" with
         InjL "payload" =>
           let: "dst" := "payload" in
           let: "m" := Fst "dst" in
           let: "dst" := Snd "dst" in
           match: ! #l_auth with
             InjL <> =>
               #l_auth <- InjR "m";; 
               asnd_l ("m", "dst");; "k" #()%V
           | InjR "message" => "k" #()%V
           end
       | InjR "from" =>
         let: "r" := arcv_l "from" in
         match: "r" with
           InjL <> => "k" (InjLV #()%V)
         | InjR "x" => "k" ! #l_auth
         end
       end  )%E).
  set (kr1 := ( match: "payload" with
         InjL "payload" =>
           let: "dst" := "payload" in
           let: "m" := Fst "dst" in
           let: "dst" := Snd "dst" in
           match: ! #l_fchan with
             InjL <> =>
               #l_fchan <- InjR "m";; 
               (λ: "m", do: leaksec' InjL "m")%V alice;; 
               "k" #()%V
           | InjR "x" => "k" #()%V
           end
       | InjR <> =>
         let: "r" := (λ: "m", do: leaksec' InjR "m")%V bob in
         match: "r" with
           InjL <> => "k" (InjLV #()%V)
         | InjR "x" => "k" (InjR ! #l_fchan)
         end
       end )%E).
  set (kr2 := ( match: "payload" with
         InjL <> =>
           kysnd_r bob;; 
           let: "r" := kyrcv_r bob in
           match: "r" with
             InjL <> => "k" (InjLV #()%V)
           | InjR "x" =>
             match: ! #l_sim with
               InjL <> =>
                 let: "m'" := #()%V;; rand(#lbl:α) #(S n'') in
                 let: "mA" := vexp g "m'" in
                 #l_sim <- InjR "m'";; 
                 asnd_r ("mA", bob);; "k" #()%V
             | InjR "m" => "k" #()%V
             end
           end
       | InjR <> =>
         let: "r" := kyrcv_r alice in
         match: "r" with
           InjL <> => "k" (InjLV #()%V)
         | InjR "x" =>
           kysnd_r alice;; 
           let: "rla" := arcv_r bob in
           match: "rla" with
             InjL <> => "k" (InjLV #()%V)
           | InjR "x" => "k" ! #l_sim
           end
         end
                end )%E).
   set (θ := client_row channel' leaksec' getKey' schannel_l schannel_r).
  iSpecialize ("Hrelf1f2" $! θ).
  unfold sem_ty_arr, sem_ty_mbang. simpl.
  (*iDestruct "Hrelf1f2" as "#Hrelf1f2".*)
  iAssert (sem_val_typed  ((λ: "m", do: schannel_l InjL "m"), (λ: "from", do: schannel_l InjR "from"))%V ((λ: "m", do: schannel_r InjL "m") , (λ: "from", do: schannel_r InjR "from"))%V (((𝔾 ×(𝟙 + 𝟙))%T -{ θ }-> 𝟙) × ((𝟙 + 𝟙)%T -{ θ }-> (Option 𝔾)))%T) as "Hschn".
  { iApply SEM_TYPED_EFF. }
  (*iAssert (sem_val_typed (λ: "m", do: schannel_l InjR "m") (λ: "m", do: schannel_r InjR "m") ((𝟙 + 𝟙)%T -{ θ }-> (Option 𝔾))%T) as "Hschnrcv".
  { admit. }*)
  unfold sem_val_typed. simpl.
  iDestruct "Hschn" as "#Hschn".
  (*iDestruct "Hschnrcv" as "#Hschnrcv".*)
  iSpecialize ("Hrelf1f2" with "Hschn"). simpl.
   set (d1 := ((α ↪ₛN (S n''; [n])) ∗ l_sim ↦ₛ NONEV ∗ l_auth ↦ NONEV ∗ l_fchan ↦ₛ NONEV ∗ l_rchan ↦ NONEV)%I).
  (*set (d2 := ((∃ g m, α ↪ₛ□ (S n''; []) ∗ l_sim ↦ₛ□ SOMEV #n ∗
                  l_auth ↦□ SOMEV (vgval
                                     (bij_group_xor_sem m (g ^+ n)))%V ∗  l_fchan ↦ₛ□ SOMEV (vgval g) ∗  l_rchan ↦□ SOMEV (vgval g))%I)).*)
  set (d2 := ((∃ g m, α ↪ₛ□ (S n''; []) ∗ l_sim ↦ₛ□ SOMEV #n ∗
                  l_auth ↦□ SOMEV (vgval
                                     (bij_group_xor_sem m (g ^+ n)))%V ∗  l_fchan ↦ₛ□ SOMEV (vgval m) ∗  l_rchan ↦□ SOMEV (vgval m))%I)).

  set (d3 := (∃ g, (α ↪ₛN (S n''; [n])) ∗ l_fchan ↦ₛ□ SOMEV (vgval g) ∗  l_rchan ↦□ SOMEV (vgval g) ∗  l_sim ↦ₛ NONEV ∗ l_auth ↦ NONEV)%I).
  (* set (d3 := (∃ m, (α ↪ₛN (S n''; [n])) ∗ l_fchan ↦ₛ□ SOMEV m ∗  l_rchan ↦□ SOMEV m ∗  l_sim ↦ₛ NONEV ∗ l_auth ↦ NONEV)%I).*)
  iApply (brel_na_alloc (d1 ∨ (d2 ∨ d3))%I alphaN).
   iSplitL "Hα Hl_sim Hl_auth Hlfchan Hlrchan"; [iNext; iLeft; iFrame|].
   iIntros "#Hinvα".
   iApply brel_new_theory.
   iApply (brel_add_label_l with "Hschannel_l").
   iApply (brel_add_label_r with "Hschannel_r").
   iApply (brel_add_label_l with "HgK").
   iApply (brel_add_label_l with "Hchannel").
   iApply (brel_add_label_r with "Hleaksec").
   set (X :=  iLblSig_to_iLblThy [([schannel_l] , [schannel_r] , sec_channel schannel_l schannel_r)]).
   set (R := (λ u1 u2 : val, 𝟙%T u1 u2)).
   set (X' := sec_channel schannel_l schannel_r).
   iApply brel_learn. iIntros "%Hdist' _".
   About brel_exhaustion.
   iApply ((brel_exhaustion (f1 ((λ: "m", do: schannel_l InjL "m"),(λ: "from", do: schannel_l InjR "from"))%V) (f2 ((λ: "m", do: schannel_r InjL "m"),(λ: "from", do: schannel_r InjR "from"))%V) _ _ X' _ _ R _ _ _) with "[Hrelf1f2]"); try simpl; try auto; try (apply sublist_subseteq); try (apply singleton_sublist_l);
     try (apply list_elem_of_In); try simpl; try auto; try (repeat (eapply sublist_skip)) ; try eapply sublist_nil_l.
   {
     set clt := ([channel'; getKey'; schannel_l], [leaksec'; schannel_r], X').
     set cltheory := iLblSig_to_iLblThy [([channel'; getKey'; schannel_l] , [leaksec'; schannel_r] , X')].
     set (L' := cltheory ++ (iLblSig_to_iLblThy L)).
     About sem_row_union.
     Print sem_row.
    (* set (keytheory := iLblSig_to_iLblThy [([keyleak1], [keyleak2], keyleak keyleak1 keyleak2)]).
     set (leaktheory := (iLblSig_to_iLblThy [([leakauth1], [leakauth2], leakauth leakauth1 leakauth2)])).*)
     set (keytheory := keyeff).
     set (leaktheory := autheff).
     set (M := cltheory ++ (iLblSig_to_iLblThy (sem_row_union (sem_row_union leaktheory keytheory) L))).
      iApply (brel_introduction_mono L' M).
     + simpl.
       iApply to_iThy_le_intro'.
       unfold L'. unfold M.
       set (l := cltheory ++ iLblSig_to_iLblThy (sem_row_union leaktheory keytheory)).
       Search iLblSig_to_iLblThy.
       (*rewrite -> iLblSig_to_iLblThy_app.
       apply (submseteq_skips_r (iLblSig_to_iLblThy L) (cltheory) (cltheory ++ keytheory ++ leaktheory)).
       eapply submseteq_inserts_r. eapply Permutation_submseteq. auto. *)
       admit.
     + unfold L'. unfold cltheory. simpl. iApply "Hrelf1f2". } 
    iLöb as "IH".
   unfold kl1.
   iSplit; [iIntros (v1 v2) "%Hv1v2"; iModIntro; brel_pures; iModIntro; done |].  
   iIntros (?????) "!# %Hk1 %Hk2 HXQ #Hrel".  
   iDestruct "HXQ" as "[HSendAlice | HRecvBob]".
   (* Send a message using the secure channel from Alice To Bob *)
   + iDestruct "HSendAlice" as (?m) "[[%He1 %He2] #HmQ]".
      rewrite -> He1. rewrite -> He2. brel_pures.
         { apply -> NeutralEctx_ectx_labels_singleton.
           do 2 (eapply NeutralEctx_label_cons_inv_2 in Hk1). eapply Hk1. }
         {  apply -> NeutralEctx_ectx_labels_singleton.
            eapply NeutralEctx_label_cons_inv_2 in Hk2.
            eapply NeutralEctx_label_cons_inv_1 in Hk2. eapply Hk2. } 
         iApply (brel_na_inv _ _ alphaN); first set_solver.
         iFrame "Hinvα".
         iIntros "([(>Hα & >Hl_sim & >Hl_auth & >Hl_fchan & >Hl_rchan) | [>Hd2 | >Hd3 ]] & Hclose)".
         (*iIntros "([(>Hα & >Hl_sim & >Hl_auth & >Hl_fchan & >Hl_rchan) | #>Hpersrfsa] & Hclose)".*)
         (*iFrame "Hinvβ".
         iIntros "([(>Hl_fchan  & >Hl_rchan) | #>Hrfchan] & Hclose)".*)
          (* First message to be sent by the secure channel*)
        ++ About brel_load_r.
           iApply (brel_load_r _ _ _ _ [HandleCtx _ _ _ _ _ ; CaseCtx _ _] with "Hl_fchan").
           iIntros "Hl_fchan".
           iApply (brel_load_l _ _ _  [HandleCtx Deep MS channel' _ _ ; HandleCtx Deep MS getKey' _ _; CaseCtx _ _] with "Hl_rchan").
           iIntros "!>Hl_rchan". brel_pures.
           simpl. brel_pures. 
           iApply (brel_store_r _ _ _ _ [HandleCtx _ _ _ _ _ ; AppRCtx _] with "Hl_fchan"). iIntros "Hl_fchan".
           simpl.
           brel_pures.
           { simpl. apply not_elem_of_nil. }
           iApply (brel_store_l _ _ _  [HandleCtx _ _ _ _ _ ; HandleCtx _ _ _ _ _ ; AppRCtx _] with "Hl_rchan"). 
           iIntros "!>Hl_rchan". brel_pures; try (simpl); try (apply not_elem_of_nil).
           repeat foldkont.
           (* set (keytheory := iLblSig_to_iLblThy [([keyleak1], [keyleak2], keyleak keyleak1 keyleak2)]).*)
            set (keytheory := keyeff).
            (* set (leaktheory := (iLblSig_to_iLblThy [([leakauth1], [leakauth2], leakauth leakauth1 leakauth2)])).*)
            set (leaktheory := autheff).
            set (M := [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)] ++ (iLblSig_to_iLblThy (sem_row_union leaktheory L))).
            set (N := [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)] ++ (iLblSig_to_iLblThy (sem_row_union (sem_row_union leaktheory keytheory) L))).
            iApply fupd_brel.
             iMod (ghost_map_elem_persist with "Hl_fchan") as "#Hl_fchan".
             iMod (ghost_map_elem_persist with "Hl_rchan") as "#Hl_rchan".
             iModIntro.
             iApply brel_na_close. iFrame.
             iSplitL.
             { iModIntro. iRight. iRight. unfold d3. iExists _. iFrame "Hα Hl_fchan Hl_rchan Hl_sim Hl_auth". }
             simpl.
             iApply (brel_bind'' [HandleCtx Deep _ _ _ _; AppRCtx _] [AppRCtx _] (iLblSig_to_iLblThy keytheory) M N (𝟙%T) (kysnd_l bob) (kysnd_r bob)).
             { simpl. set_solver. }
             { simpl. set_solver. }
             { simpl. unfold M. unfold N. iApply to_iThy_le_intro'. eapply Permutation_submseteq.
               (*eapply perm_swap.*) admit. }
             { About brel_wand.
               iApply (brel_wand _ _ _  R _ ).
               { iDestruct "Hkeysnd" as "#Hkeysnd".
                 iSpecialize ("Hkeysnd" $! bob bob).
                 iApply "Hkeysnd".
                 { unfold sem_ty_sum, sem_ty_unit. unfold bob. iExists #()%V, #()%V.
                   iLeft. repeat (iSplit); try (iPureIntro); try reflexivity. } }
               iModIntro. iIntros (v1 v2) "#HRv1v2".
               brel_pures.
                iApply (brel_bind'' _ _ (iLblSig_to_iLblThy keytheory) M N 𝟙%T (kyrcv_l bob) (kyrcv_r bob)).
                { simpl. unfold M.  repeat (rewrite -> labels_l_cons). set_solver. }
                { simpl. apply list_subseteq_nil. }
                { simpl. unfold M. unfold N. iApply to_iThy_le_intro'. eapply Permutation_submseteq.
               (*eapply perm_swap.*) admit. }
                (*iApply (brel_introduction' [keyleak1] [keyleak2]).*)
                iApply brel_wand.
                { iDestruct "Hkeyrcv" as "#Hkeyrcv".
                  iSpecialize ("Hkeyrcv" $! bob bob).
                  iApply "Hkeyrcv".
                  { unfold bob. unfold sem_ty_sum. iExists #()%V, #()%V.
                    repeat iSplit; try (iPureIntro); try reflexivity; try (left); repeat split;
                      try reflexivity. } }
                iModIntro. iIntros (v0 v3) "#Hv0v3".
                unfold sem_ty_group, sem_ty_option, sem_ty_sum.
                iDestruct "Hv0v3" as (?w1 ?w2) "#Hv0v3".
                iDestruct "Hv0v3" as "[Hsome | Hnone]".
               ++ iDestruct "Hsome" as "(%Hv0 & (%Hv3 & Hw1w2))".
                  rewrite -> Hv0. rewrite -> Hv3. unfold sem_ty_unit.
                  iDestruct "Hw1w2" as "(%Hw1 & %Hw2)".
                  rewrite -> Hw1. rewrite -> Hw2.
                  brel_pures.
                   iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)). 
                      { simpl. auto. }
                      { simpl. repeat (eapply list_subseteq_skip). eapply list_subseteq_nil. }
                      { iApply "Hrel". iApply "HmQ". }
                      { iApply "IH". }
               ++ iDestruct "Hnone" as "(%Hv0 & (%Hv3 &Hw1w2))".
                  rewrite -> Hv0. rewrite -> Hv3.
                  unfold sem_ty_unit.
                  iDestruct "Hw1w2" as "(%Hw1 & %Hw2)".
                  rewrite -> Hw1. rewrite -> Hw2.
                  brel_pures.
                  iApply G_XOR_CORRECT_l.
                  { admit. }
                  brel_pures.
                  { simpl. unfold distinct in Hdist'. destruct Hdist'.
                        unfold distinct_l in H1. (*unfold LblClients in H1. simpl in H1.*)
                        unfold N in H1. simpl in H1.
                        repeat (rewrite -> labels_l_cons in H1).
                        eapply NoDup_app in H1.
                        Print val.
                        eapply NoDup_cons_1_1. destruct H1 as [H1' H2'].
                        apply (NoDup_app [channel'; getKey'] [schannel_l]) in H1'.
                        destruct H1' as [H1' H2'']. apply H1'.  }
                          iApply (brel_na_inv _ _ alphaN); first set_solver.
                        iFrame "Hinvα".  
                        iIntros "([ (>Hα & >Hl_sim & >Hl_auth & >Hl_fchan' & >Hl_rchan') | [>Hd2 | >Hd3]] & Hclose)".
                         (*contradiction branch as the first message has been sent and stored*)
                          -
                            Search (_ ↦ₛ _)%I.
                            admit.
                          -
                            unfold d2.
                            iDestruct "Hd2" as (?g ?m) "(Hα & (Hl_sim & (Hl_auth & (Hl_fchan' & Hl_rchan'))))".
                            iApply (brel_load_l _ _ _ [CaseCtx _ _] with "Hl_auth").                                          
                          iIntros "!> Hl_auth".
                          simpl. brel_pures_l.
                          iApply (brel_load_r _ _ _ _ [CaseCtx _ _] with "Hl_sim").
                          iIntros "Hl_sim". brel_pures. simpl.
                          iApply fupd_brel.
                          iModIntro.
                          iApply brel_na_close. iFrame.
                          iSplitL.
                          { iModIntro. iRight. iLeft. iFrame "Hα Hl_sim Hl_auth Hl_fchan' Hl_rchan'". }
                         
                          brel_pures.
                            iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)).
                            { simpl. auto. }
                            { simpl. auto. (*admit.*) }
                            { iApply "Hrel". iApply "HmQ". }
                            { iApply "IH". }
                          - unfold d3.
                             iDestruct "Hd3" as (?g) "(Hα & (Hl_fchan' & (Hl_rchan' & (Hl_sim & Hl_auth))))".
                            iApply (brel_load_l _ _ _ [CaseCtx _ _] with "Hl_auth").                                          
                          iIntros "!> Hl_auth".
                          simpl. brel_pures_l.
                          iApply (brel_load_r _ _ _ _ [CaseCtx _ _] with "Hl_sim").
                          iIntros "Hl_sim". brel_pures. simpl.
                          iApply (brel_randT_r _ [AppRCtx _ ] with "Hα").
                          iIntros "Hα %Hn".
                          brel_pures.
                          repeat foldkont.
                          iApply (brel_exp_r [AppRCtx _]).
                          brel_pures. 
                          iApply (brel_store_r _ _ _ _ [AppRCtx _] with "Hl_sim").
                          iIntros "Hl_sim". rel_pures. 
                          iApply (brel_store_l _ _ _ [AppRCtx _] with "Hl_auth").
                          iIntros "!> Hl_auth". brel_pures.
                          iApply fupd_brel.
                          iMod (ghost_map_elem_persist with "Hl_sim") as "#Hl_sim".
                          iMod (ghost_map_elem_persist with "Hl_auth") as "#Hl_auth".
                           iDestruct "Hα" as (ns) "(%Hf & Hα)".
                          apply map_eq_nil in Hf. simplify_eq.
                          iMod (ghost_map_elem_persist with "Hα") as "#Hα".
                          iModIntro.
                          iApply brel_na_close. iFrame.
                          iSplitL; [iModIntro; iRight; iLeft; iFrame "#" |].
                          simpl. brel_pures.
                          set (g_sem := (bij_group_xor_sem m (valgroup.g ^+ n))).
                          About brel_bind.
                           iPoseProof (brel_bind [AppRCtx (λ: <>, kont1 #()%V)]
                      [AppRCtx (λ: <>, kont0 #()%V)]
                      ⊤ (iLblSig_to_iLblThy leaktheory) N  𝟙%T
                      (asnd_l (vgval g_sem, bob))%V
                      (asnd_r (vgval (valgroup.g ^+ n), bob))%V) as "Hbind".
                           iApply "Hbind".
                            { simpl. unfold leaktheory. auto.
                            iApply (traversable_ectx_labels _ _ [] [] iThyBot _).
                            + unfold kont1. simpl. auto.
                            + unfold kont0. simpl. auto.
                            + simpl. unfold distinct.
                              unfold distinct_l, distinct_r.
                              unfold labels_l, labels_r. simpl.
                              admit.
                              (*split; set_solver; eapply NoDup_singleton.*)
                            }
                            { simpl. unfold N. iApply to_iThy_le_intro'.
                              admit.
                             (* set (k1 :=  [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], iThyBot)] ++ keytheory).
                              apply (submseteq_middle leaktheory k1 (iLblSig_to_iLblThy L)).*) }
                            About brel_wand.
                            iApply (brel_wand _ _ _ R _).
                            {  iDestruct "Hasnd" as "#Hasnd".
                               iSpecialize ("Hasnd" $! (vgval g_sem, bob)%V).
                               iSpecialize ("Hasnd" $! (vgval (valgroup.g ^+n), bob)%V).
                               iApply "Hasnd".
                               unfold g_sem. simpl. unfold sem_ty_prod.
                               iExists ((bij_group_xor_sem m (valgroup.g ^+n))) , (vgval (valgroup.g ^+n)) , bob , bob.
                               repeat (iSplit); try (iPureIntro); try reflexivity.
                               + auto. admit.
                               + admit. }
                            iModIntro. iIntros (v0 v3) "#HRv0v3".
                            unfold R. unfold sem_ty_unit.
                            iDestruct "HRv0v3" as "(%Hv0 & %Hv3)".
                            rewrite -> Hv0. rewrite -> Hv3.
                            brel_pures.
                            iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)).
                            { simpl. auto. }
                            { simpl. auto. (*admit.*) }
                            { iApply "Hrel". iApply "HmQ". }
                            { iApply "IH". } }
             (* A message has already been sent by the secure channel *)
                         ++   unfold d2.
                             iDestruct "Hd2" as (?g ?m) "(Hα & (Hl_sim & (Hl_auth & (Hl_fchan & Hl_rchan)))) ".
           iDestruct "Hl_fchan" as "#Hl_fchan".
           iDestruct "Hl_rchan" as "#Hl_rchan".
           iApply (brel_load_l _ _ _  [HandleCtx _ _ _ _ _ ; HandleCtx _ _ _ _ _ ; CaseCtx _ _] with "Hl_rchan").
           iIntros "!> Hl_rchan'".
           brel_pures.
           iApply (brel_load_r _ _ _ _  [HandleCtx _ _ _ _ _ ; CaseCtx _ _] with "Hl_fchan").
           iIntros "Hl_fchan'".
           brel_pures.
           iApply brel_na_close. iFrame.
           iSplitL.
           { iModIntro. iRight. iLeft. iFrame. }
           iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)).
           { simpl. auto. }
           { simpl. auto. (*admit.*) }
           { iApply "Hrel". iApply "HmQ". }
           { iApply "IH". }
           ++  unfold d3.
           iDestruct "Hd3" as (?g) "(Hα & (Hl_fchan & (Hl_rchan & (Hl_sim & Hl_auth))))".                iApply (brel_load_l _ _ _  [HandleCtx _ _ _ _ _ ; HandleCtx _ _ _ _ _ ; CaseCtx _ _] with "Hl_rchan").
           iIntros "!> Hl_rchan'".
           brel_pures.
           iApply (brel_load_r _ _ _ _  [HandleCtx _ _ _ _ _ ; CaseCtx _ _] with "Hl_fchan").
           iIntros "Hl_fchan'".
           brel_pures.
           iApply brel_na_close. iFrame.
           iSplitL.
           { iModIntro. iRight. iRight. iFrame. }
           iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)).
           { simpl. auto. }
           { simpl. auto. (*admit.*) }
           { iApply "Hrel". iApply "HmQ". }
           { iApply "IH". }
              (* Bob receives the message *) 
   + iDestruct "HRecvBob" as "[%He1 [%He2 #HmQ]]". 
     rewrite -> He1. rewrite -> He2. brel_pures.
     { split.
       + apply -> NeutralEctx_ectx_labels_singleton.
         do 2 (eapply NeutralEctx_label_cons_inv_2 in Hk1). eapply Hk1.
       + simpl. set_solver. }
     { split.
       + apply -> NeutralEctx_ectx_labels_singleton.
            eapply NeutralEctx_label_cons_inv_2 in Hk2.
            eapply NeutralEctx_label_cons_inv_1 in Hk2. eapply Hk2.
       + simpl. set_solver. }
     brel_pures.
     (* set (keytheory := iLblSig_to_iLblThy [([keyleak1], [keyleak2], keyleak keyleak1 keyleak2)]).*)
     set (keytheory := keyeff).
     set (leaktheory := autheff).
        (* set (leaktheory := (iLblSig_to_iLblThy [([leakauth1], [leakauth2], leakauth leakauth1 leakauth2)])).*)
         set (M := [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)]).
         (* set (N := [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)] ++ keytheory ++ leaktheory ++ (iLblSig_to_iLblThy L)).*)
         set (N := [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)] ++
                     iLblSig_to_iLblThy (sem_row_union (sem_row_union keytheory leaktheory) L)).
         About brel_bind''.
         repeat foldkont.
         About brel_bind''.
         brel_pures.
         set (leftkontbind := ( match: "r" with
               InjL <> => kont (InjLV #()%V)
             | InjR "w" =>
               kysnd_l alice;; 
               kont (InjR (vgval (g ^+ n)))
                                end)%E).
         set (rightkontbind := ( match: "r" with
       InjL <> => kont0 (InjLV #()%V)
     | InjR "x" =>
       kysnd_r alice;; 
       let: "rla" := arcv_r bob in
       match: "rla" with
         InjL <> => kont0 (InjLV #()%V)
       | InjR "x" => kont0 ! #l_sim
       end
                                 end)%E).
         About brel_bind.
         unfold kl3.
         set (hbranchleft := (λ: "payload" "k",
                                 match: "payload" with
         InjL "payload" =>
           let: "dst" := "payload" in
           let: "m" := Fst "dst" in
           let: "dst" := Snd "dst" in
           match: ! #l_auth with
             InjL <> =>
               #l_auth <- InjR "m";; 
               asnd_l ("m", "dst");; "k" #()%V
           | InjR "message" => "k" #()%V
           end
       | InjR "from" =>
         let: "r" := arcv_l "from" in
         match: "r" with
           InjL <> => "k" (InjLV #()%V)
         | InjR "x" => "k" ! #l_auth
         end
       end )%E).
         iPoseProof (brel_bind'' [HandleCtx Deep MS channel' hbranchleft (λ: "y", "y") ; AppRCtx (λ: "r", leftkontbind)] [AppRCtx (λ: "r", rightkontbind)]  (iLblSig_to_iLblThy (keytheory))  [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)] (([channel'; getKey'; schannel_l], [leaksec'; schannel_r], iThyBot)
     :: iLblSig_to_iLblThy (sem_row_union (sem_row_union leaktheory keytheory) L)) (𝟙%T) (kyrcv_l alice) (kyrcv_r alice)) as "Hrelbind".
         { simpl. set_solver. }
         { simpl. set_solver. }
         iApply "Hrelbind".
         { simpl. unfold M. unfold labels_l. simpl. (*apply (list_subseteq_skip channel' [] [getKey'; schannel_l]). set_solver.*) admit. }
        (*{ simpl. unfold M. unfold labels_r. simpl. set_solver. }
        { iApply to_iThy_le_intro'. unfold M. unfold N.
          eapply submseteq_sublist_r.*)
         iApply brel_wand.
         {  iDestruct "Hkeyrcv" as "#Hkeyrcv".
            iSpecialize ("Hkeyrcv" $! alice alice).
            iApply "Hkeyrcv". unfold sem_ty_sum, sem_ty_unit.
            iExists #()%V, #()%V. unfold alice.
            repeat (iSplit); try (iPureIntro); try reflexivity.
            right. repeat split; try reflexivity. }
         iModIntro. iIntros (v1 v2) "#Hv1v2". brel_pures.
         unfold sem_ty_group, sem_ty_option, sem_ty_sum.
         iDestruct "Hv1v2" as (?w1 ?w2) "[#Hnone | #Hsome]".
         (*key receive didnt return successfully*)
          - iDestruct "Hnone" as "[%Hv1 [%Hv2 #Hw1w2]]".
            rewrite -> Hv1. rewrite -> Hv2. unfold sem_ty_unit.
            iDestruct "Hw1w2" as "(%Hw1 & %Hw2)".
            rewrite -> Hw1. rewrite -> Hw2. brel_pures.
            iApply (brel_exhaustion (fill k1'(InjLV #()%V)) (fill k2' (InjLV #()%V))).
            { simpl. auto. }
            { simpl. set_solver. }
            { iApply "Hrel". iDestruct "HmQ" as "[Hsome Hnone]". iApply "Hnone".  }
            { iApply "IH". }
          (*key receive returned successfully*)
           - iDestruct "Hsome" as "[%Hv1 [%Hv2 #Hw1w2]]". 
             rewrite -> Hv1. rewrite -> Hv2.
             iDestruct "Hw1w2" as "(%Hw1 & %Hw2)".
             rewrite -> Hw1. rewrite -> Hw2. brel_pures.
             (*iApply (brel_bind'' _ _ (iLblSig_to_iLblThy keytheory) M N 𝟙%T (kysnd_l alice) (kysnd_r alice)).*) 
             set (rightapp := ( match: "rla" with
                                 InjL <> => kont0 (InjLV #()%V)
                               | InjR "x" => kont0 ! #l_sim
                                end)%E).
             iPoseProof (brel_bind'' [HandleCtx Deep MS channel' hbranchleft (λ: "y", "y"); AppRCtx (λ: <>, kont (InjR (vgval (valgroup.g ^+ n))))] [AppRCtx (λ: <>, let: "rla" := arcv_r bob in rightapp)] (iLblSig_to_iLblThy keytheory)  [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)] ([([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)] ++
                     iLblSig_to_iLblThy (sem_row_union (sem_row_union leaktheory keytheory) L)) 𝟙%T (kysnd_l alice) (kysnd_r alice)) as "Hrelbind'".
             { simpl. set_solver. }
             { simpl. set_solver. }
             simpl.
             iApply "Hrelbind'".
             {  iApply to_iThy_le_intro'. unfold M. unfold N. admit. }
             iApply brel_wand.
             { iDestruct "Hkeysnd" as "#Hkeysnd".
               iSpecialize ("Hkeysnd" $! alice alice).
               iApply "Hkeysnd".
               iExists #()%V, #()%V. unfold alice.
               iRight. repeat (iSplit); try (iPureIntro); try reflexivity. }
             iModIntro. iIntros (v0 v3) "#HRv0v3".
             unfold R. unfold sem_ty_unit.
             iDestruct "HRv0v3" as "(%Hv0 & %Hv3)".
             rewrite -> Hv0. rewrite -> Hv3. brel_pures.
             { simpl. admit. }
             { repeat foldkont.
               iApply (brel_bind'' _ _  (iLblSig_to_iLblThy leaktheory)  [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)] ([([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)] ++
                                                                                                                                                   iLblSig_to_iLblThy (sem_row_union (sem_row_union leaktheory keytheory) L)) 𝟙%T (arcv_l bob) (arcv_r bob)).
               { simpl. set_solver. }
               { simpl. set_solver. }
               { iApply to_iThy_le_intro'. (*solve_submseteq.*) admit. }
               
               iApply brel_wand.
               { iDestruct "Harcv" as "#Harcv".
                 iSpecialize ("Harcv" $! bob bob).
                 iApply "Harcv".
                 iExists #()%V, #()%V. unfold bob.
                 iLeft. repeat (iSplit); try (iPureIntro); try reflexivity. }
               iModIntro. iIntros (v4 v5) "#Hv4v5".
               iDestruct "Hv4v5" as (?w0 ?w3) "Hv4v5".
               iDestruct "Hv4v5" as "[Hnone | Hsome]".
               (* leakauth doesnt return successfully *)
               - iDestruct "Hnone" as "(%Hv4 & (%Hv5 & (%Hw0 & %Hw3)))".
                 rewrite -> Hv4. rewrite -> Hv5. rewrite -> Hw0. rewrite -> Hw3.
                 brel_pures.
                   iApply (brel_exhaustion (fill k1' (InjLV #()%V)) (fill k2' (InjLV #()%V))).
                          { simpl. set_solver. }
                          { simpl. set_solver. }
                          { iApply "Hrel".  iDestruct "HmQ" as "[Hsome Hnone]". iApply "Hnone". }
                          {iApply "IH". }
               (* leakauth returns successfully *)
               - iDestruct "Hsome" as "(%Hv4 & (%Hv5 & (%Hw0 & %Hw3)))".
                  rewrite -> Hv4. rewrite -> Hv5. rewrite -> Hw0. rewrite -> Hw3.
                  brel_pures.
                  iApply (brel_na_inv _ _ alphaN); first set_solver.
                  iFrame "Hinvα".
                  iIntros "([(>Hα & >Hl_sim & >Hl_auth & >Hl_fchan & >Hl_rchan) | [>Hd2 | >Hd3 ]] & Hclose)".
                  (* no message has been sent by the secure channel yet*)
                 ++ simpl. brel_pures.
                     iApply (brel_load_r _ _ _ _ [AppRCtx _] with "Hl_sim").
                              iIntros "Hl_sim".
                              iApply (brel_load_l _ _ _ [AppRCtx _] with "Hl_auth").
                              iIntros "!>Hl_auth".
                              simpl.
                              brel_pures.
                              repeat foldkont.
                              iApply brel_na_close. iFrame.
                              iSplitL; [iModIntro; iLeft; iFrame |].
                              iApply (brel_exhaustion (fill k1'(InjLV #()%V)) (fill k2' (InjLV #()%V))).
                               { simpl. auto. }
                               { simpl. set_solver. }
                               { iApply "Hrel". iDestruct "HmQ" as "[Hsome Hnone]". iApply "Hnone".  }
                               { iApply "IH". }
                  (* a message has  been sent by the secure channel and is yet to be receievd by the authenticated channel *)
                           ++ simpl. brel_pures. 
                              unfold d2.
                              iDestruct "Hd2" as (?g ?m) "(Hα & (Hl_sim & (Hl_auth & (Hl_fchan & Hl_rchan)))) ".
                              iApply (brel_load_r _ _ _ _ [AppRCtx _] with "Hl_sim").
                              iIntros "Hl_sim'".
                              iApply (brel_load_l _ _ _ [AppRCtx _] with "Hl_auth").
                              iIntros "!>Hl_auth'".
                              iDestruct "Hl_fchan" as "#Hl_fchan".
                               iApply brel_na_close. iFrame.
                               iSplitL; [iModIntro; iRight; iLeft; iFrame; iFrame "#" |].
                               brel_pures.
                               iApply G_XOR_CORRECT_l.
                               { admit. }
                                brel_pures.
                               iApply (brel_load_r _ _ _ _ [HandleCtx _ _ _ _ _ ; AppRCtx _ ; InjRCtx ] with "Hl_fchan").
                               iIntros "Hl_fchan'".
                               brel_pures.
                                set (g_enc := (bij_group_xor_sem
                                        (bij_group_xor_sem m (g ^+ n))
                                        (valgroup.g ^+ n))).
                               iApply (brel_exhaustion (fill k1'((InjRV (vgval g_enc))%V)) (fill k2' ((InjRV (InjRV (vgval m)))%V))).
                               { simpl. auto. }
                                { simpl. set_solver. }
                               { unfold kont0. iApply "Hrel". iDestruct "HmQ" as "[Hsome Hnone]". unfold xor. iApply "Hsome". }
                               { iApply "IH". }
                               (* a message has been sent by both the secure channel and the authenticated channel *)
                                 ++ simpl. brel_pures.
                              unfold d3.
                               iDestruct "Hd3" as (?g) "(Hα & (Hl_fchan & (Hl_rchan & (Hl_sim & Hl_auth)))) ".
                              iApply (brel_load_r _ _ _ _ [AppRCtx _] with "Hl_sim").
                              iIntros "Hl_sim'".
                              iApply (brel_load_l _ _ _ [AppRCtx _] with "Hl_auth").
                              iIntros "!>Hl_auth'".
                              iDestruct "Hl_fchan" as "#Hl_fchan".
                               iApply brel_na_close. iFrame.
                               iSplitL; [iModIntro; iRight; iRight; iFrame; iFrame "#" |].
                               brel_pures.
                               iApply (brel_exhaustion (fill k1' (InjLV #()%V)) (fill k2' (InjLV #()%V))).
                          { simpl. set_solver. }
                          { simpl. set_solver. }
                          { iApply "Hrel".  iDestruct "HmQ" as "[Hsome Hnone]". iApply "Hnone". }
                          {iApply "IH". }*)
    Admitted.
                      
Lemma REAL_CHAN_CHAN_SIM_F_CHAN :
  ⊢ sem_val_typed (REAL_CHAN)%V (λ: "f", CHAN_SIM_lazy (F_CHAN "f"))%V
     (* (∀ᵣ θ__L ,(∀ᵣ θₕ, (((𝔾 × (sem_ty_sum 𝟙 𝟙)) -{ θₕ }->  𝟙) × ((sem_ty_sum 𝟙 𝟙) -{ θₕ }-> (Option 𝔾))) -{ sem_row_union  θₕ θ__L }-∘ 𝟙) ⊸ (*type of client*)*)                                                                                           (∀ᵣ θ__L ,(∀ᵣ θₕ, ((𝔾 -{ θₕ }->  𝟙) × (𝟙 -{ θₕ }-> (Option 𝔾))) -{ sem_row_union  θₕ θ__L }-∘ 𝟙) ⊸ (*type of client*) 
      (∀ᵣ θ₁, ∀ᵣ θ₂,  (((𝔾 × (𝟙 + 𝟙)) -{ θ₁ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ₁ }-> Option 𝟙)) ⊸ (((𝟙 + 𝟙) -{ θ₂ }-> 𝟙) × (𝟙 + 𝟙) -{ θ₂ }-> Option 𝟙) -{ sem_row_union (sem_row_union θ₁ θ₂) θ__L }-∘ 𝟙))%T.
Proof using G inG0 inG1 inG2.   
  iModIntro. iIntros (L).
  iIntros (f1 f2) "Hrelf1f2".
  brel_pures'.
  simpl.
  assert (to_iThyIfMono OS [] = []) as <- by done.
  iApply (brel_mono OS with "[][Hrelf1f2]");
  [iApply to_iThy_le_refl|simpl|simpl].
  +  iApply (SEM_F_KE_CHAN_SIM _ _ L).
     (*iApply "Hrelf1f2".*) admit.
  + iIntros (??) "$". 
Admitted. 
   
(*top level statements for the secure channel *)
(*----------------------------------------------------------------*)
Lemma REAL_IDEAL_SCHAN :
  ⊢ sem_typed [] REAL_CHAN (λ: "f", (CHAN_SIM_lazy (F_CHAN "f")))%V ⊥
       (∀ᵣ θ__L ,(∀ᵣ θₕ, ((𝔾 -{ θₕ }-> 𝟙) × ( 𝟙 -{ θₕ }-> (Option  𝔾))) -{ sem_row_union  θₕ θ__L }-∘ 𝟙)%T ⊸ (*type of client*)
                 (∀ᵣ θ₁, ∀ᵣ θ₂,  (((𝔾 × (𝟙 + 𝟙)) -{ θ₁ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ₁ }-> Option 𝟙)) ⊸ (((𝟙 + 𝟙) -{ θ₂ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ₂ }-> Option 𝟙)) -{ sem_row_union (sem_row_union θ₁ θ₂) θ__L }-∘ 𝟙))%T [].
Proof using G inG0 inG1 inG2 klk1 klk2 lka1 lka2. 
  iIntros (vs) "!# H". simpl.
  iApply brel_value.
  iIntros "$ !>".
  iSplit; try (done).  
  iPoseProof REAL_CHAN_CHAN_SIM_F_CHAN as "Hsemty".
  rewrite /sem_val_typed /=.
  iDestruct "Hsemty" as "#Hsemty".
  iApply "Hsemty".
Qed.
 
(*Lemma IDEAl_REAL_SCHAN :*)

Definition R_CHAN : val :=
   λ: "f",
     (F_KE_lazy_alice ||ᵣ F_OAUTH) (CHAN xor "f").

(*Verification of F_KE_L[F_OAUTH[CHAN[]]] ≤ CHAN_SIM[F_CHAN[]]*)
(*----------------------------------------------------------*)
Lemma F_OAUTH_CHAN_SIM (f1 f2 : val) (L : sem_row Σ) :
   (∀ᵣ θₕ, ((𝔾 -{ θₕ }-> 𝟙) × (𝟙 -{ θₕ }-> Option 𝔾)) -{ sem_row_union θₕ L }-∘ 𝟙)%T
                 f1 f2 -∗
    BREL R_CHAN f1
      ≤ CHAN_SIM_lazy (F_CHAN f2) <|⊥|> {{λ v1 v2,
                                       ∀ (leakauth1 leakauth2 keyleak1 keyleak2 : label),
                                       BREL v1 ((λ: "m", do: leakauth1 (Send "m")), (λ: "m", do: leakauth1 (Recv "m")))%V ((λ: "m", do: keyleak1 (Send "m")), (λ: "m", do: keyleak1 (Recv "m")))%V ≤ v2 ((λ: "m", do: leakauth2 (Send "m")), (λ: "m", do: leakauth2 (Recv "m")))%V ((λ: "m", do: keyleak2 (Send "m")), (λ: "m", do: keyleak2 (Recv "m")))%V  <| (iLblSig_to_iLblThy (envsec_row keyleak1 keyleak2 leakauth1 leakauth2 )) ++ (iLblSig_to_iLblThy L) |> {{ (λ w1 w2, 𝟙%T w1 w2)}}}}.
Proof with (repeat foldkont) using G H cg inG0 inG1 inG2 klk1 klk2 lka1 lka2 vg vgg Σ.
  iIntros "Hrelf1f2". 
  repeat simpl. 
  unfold R_CHAN.
  unfold CHAN, F_CHAN.
  brel_pures.
  unfold right_composition. brel_pures. 
  unfold CHAN.
  repeat simpl. brel_pures'.
  
  (*iApply (xor_correct_l ⊤ _ _ _ (CHAN_SIM (F_CHAN f2)) ⊥ _).*)
  unfold F_CHAN, CHAN_SIM_lazy, F_KE_lazy_alice, F_OAUTH.
 
  
  repeat simpl. brel_pures. iModIntro. iIntros (????).
  brel_pures.
  (*iApply brel_alloctape_r. iIntros (α) "Hα". brel_pures_r.*)
  iApply brel_alloc_r. iIntros (l_sim) "Hl_sim". brel_pures_r.
  iApply brel_alloc_r. iIntros (l_m'sim) "Hl_m'sim". brel_pures_r.
  (*iApply brel_couple_UT. 1: auto.
  simpl. iFrame "Hα". iSplit => //.
  iIntros (n ?) "!> Hα". brel_pures.
  brel_exp_l. brel_pures. *)
  About brel_alloctape_l.
  iApply brel_alloctape_l. iIntros (γ) "!> Hγ". brel_pures_l.
  iApply brel_alloc_l. iIntros (l_key) "!> Hl_key". brel_pures_l.
   iApply brel_effect_l. iIntros (getKey') "!> HgK !>". brel_pures_l.
  iApply brel_effect_r. iIntros (leaksec') "Hleaksec !>". brel_pures.
  iApply brel_alloc_l. iIntros (l_auth) "!>Hl_auth". brel_pures_l.
  iApply brel_effect_l. iIntros (channel') "!> Hchannel !>". brel_pures_l.
  
 
  iApply brel_alloc_r. iIntros (l_fchan) "Hlfchan". brel_pures_r.
  iApply brel_effect_r. iIntros (schannel_r) "Hschannel_r !>". brel_pures_r.
  brel_pures'. repeat simpl. brel_pures'.
  iApply brel_alloc_l. iIntros (l_rchan) "!>Hlrchan". brel_pures_l.
  iApply brel_effect_l. iIntros (schannel_l) "!> Hschannel_l !>". brel_pures_l.  
  set (kl1 := ( match: "payload" with
         InjL "m" =>
           match: ! #l_rchan with
             InjL <> =>
               #l_rchan <- InjR "m";; 
               let: "key" := (λ: "party", do: getKey' "party")%V bob in
               match: "key" with
                 InjL <> => "k" #()%V
               | InjR "x" =>
                 match: G_XOR xor "m" "x" with
                   InjL <> => "k" #()%V
                 | InjR "mg" =>
                   (λ: "m", do: channel' InjL "m")%V ("mg", bob);; "k" #()%V
                 end
               end
           | InjR "m" => "k" #()%V
           end
       | InjR <> =>
         let: "key" := (λ: "party", do: getKey' "party")%V alice in
         match: "key" with
           InjL <> => "k" (InjLV #()%V)
         | InjR "key" =>
           let: "r" := (λ: "m", do: channel' InjR "m")%V bob in
           match: "r" with
             InjL <> => "k" (InjLV #()%V)
           | InjR "x" =>
             match: G_XOR xor "x" "key" with
               InjL <> => "k" (InjL #()%V)
             | InjR "mg" => "k" (InjR "mg")
             end
           end
         end
       end )%E ).
  set (kl2 := ( match: "payload" with
         InjL "payload" =>
           let: "dst" := "payload" in
           let: "m" := Fst "dst" in
           let: "dst" := Snd "dst" in
           match: ! #l_auth with
             InjL <> =>
               #l_auth <- InjR "m";; 
               (λ: "m", do: leakauth1 Send "m")%V ("m", "dst");; "k" #()%V
           | InjR "message" => "k" #()%V
           end
       | InjR "from" =>
         let: "r" := (λ: "m", do: leakauth1 Recv "m")%V "from" in
         match: "r" with InjL <> => "k" (InjLV #()%V) | InjR "x" => "k" ! #l_auth end
       end )%E).
  set (kl3 := (match: "p" with
         InjL <> =>
           let: "key" := (λ: <>,
                            match: ! #l_key with
                              InjL <> =>
                                let: "c" := #();; rand(#lbl:γ) #(S n'') in
                                let: "key" := vexp g "c" in
                                #l_key <- InjR "key";; "key"
                            | InjR "key" => "key"
                            end)%V
                           #()%V in
           (λ: "m", do: keyleak1 Send "m")%V bob;; 
           let: "r" := (λ: "m", do: keyleak1 Recv "m")%V bob in
           match: "r" with
             InjL <> => "k" (InjLV #()%V)
           | InjR "w" => "k" (InjR "key")
           end
       | InjR <> =>
         let: "r" := (λ: "m", do: keyleak1 Recv "m")%V alice in
         match: "r" with
           InjL <> => "k" (InjLV #()%V)
         | InjR "w" =>
           (λ: "m", do: keyleak1 Send "m")%V alice;; 
           match: ! #l_key with
             InjL <> => "k" (InjLV #()%V)
           | InjR "key" => "k" (InjR "key")
           end
         end
       end)%E).
  set (kr1 := ( match: "payload" with
         InjL "m" =>
           match: ! #l_fchan with
             InjL <> =>
               #l_fchan <- InjR "m";; 
               (λ: "m", do: leaksec' InjL "m")%V alice;; "k" #()%V
           | InjR "x" => "k" #()%V
           end
       | InjR <> =>
         let: "r" := (λ: "m", do: leaksec' InjR "m")%V bob in
         match: "r" with
           InjL <> => "k" (InjLV #()%V)
         | InjR "x" => "k" (InjR ! #l_fchan)
         end
       end )%E).
  set (kr2 := ( match: "payload" with
         InjL <> =>
           let: "m'" := (λ: <>,
                           match: ! #l_m'sim with
                             InjL <> =>
                               let: "m'" := #();; rand #(S n'') in
                               #l_m'sim <- InjR "m'";; "m'"
                           | InjR "m'" => "m'"
                           end)%V
                          #()%V in
           (λ: "m", do: keyleak2 Send "m")%V bob;; 
           let: "r" := (λ: "m", do: keyleak2 Recv "m")%V bob in
           match: "r" with
             InjL <> => "k" (InjLV #()%V)
           | InjR "x" =>
             match: ! #l_sim with
               InjL <> =>
                 let: "mA" := vexp g "m'" in
                 #l_sim <- InjR "m'";; 
                 (λ: "m", do: leakauth2 Send "m")%V ("mA", bob);; "k" #()%V
             | InjR "m" => "k" #()%V
             end
           end
       | InjR <> =>
         let: "r" := (λ: "m", do: keyleak2 Recv "m")%V alice in
         match: "r" with
           InjL <> => "k" (InjLV #()%V)
         | InjR "x" =>
           (λ: "m", do: keyleak2 Send "m")%V alice;; 
           match: ! #l_m'sim with
             InjL <> => "k" (InjLV #()%V)
           | InjR "_" =>
             let: "rla" := (λ: "m", do: leakauth2 Recv "m")%V bob in
             match: "rla" with
               InjL <> => "k" (InjLV #()%V)
             | InjR "x" => "k" ! #l_sim
             end
           end
         end
       end )%E).
  set (θ := client_row channel' leaksec' getKey' schannel_l schannel_r).
  iSpecialize ("Hrelf1f2" $! θ).
  unfold sem_ty_arr, sem_ty_mbang. simpl.
  iAssert (sem_val_typed  ((λ: "m", do: schannel_l InjL "m"), (λ: <>, do: schannel_l InjR bob))%V ((λ: "m", do: schannel_r InjL "m") , (λ: <>, do: schannel_r InjR bob))%V (((𝔾 -{ θ }-> 𝟙) × (𝟙 -{ θ }-> (Option 𝔾)))%T)) as "Hschn".
  { iApply SEM_TYPED_EFF. }
  unfold sem_val_typed. simpl.
  iDestruct "Hschn" as "#Hschn".
  iSpecialize ("Hrelf1f2" with "Hschn"). simpl.
   set (f m := (λ x, int_of_vg_sem (bij_group_xor_sem m (g ^+x)))).
   assert (Hf : ∀ m : vgG, Bij (f m)).
   { admit. }
  set (d1 := (γ ↪N (S n''; []) ∗ l_m'sim ↦ₛ NONEV ∗ l_sim ↦ₛ NONEV ∗ l_auth ↦ NONEV ∗ l_fchan ↦ₛ NONEV ∗ l_rchan ↦ NONEV ∗  l_key ↦ NONEV)%I).
  set (d2 := ((∃ m : vgG, ∃ n : nat, γ ↪N (S n''; []) ∗ l_m'sim ↦ₛ□ SOMEV #(f m n) ∗ l_sim ↦ₛ□ SOMEV #(f m n) ∗
                  l_auth ↦□ SOMEV (vgval
                                     (bij_group_xor_sem m (g ^+ n)))%V ∗  l_fchan ↦ₛ□ SOMEV (vgval m) ∗  l_rchan ↦□ SOMEV (vgval m) ∗ l_key ↦□ SOMEV (vgval (g ^+n)))%I)).

  set (d3 := (∃ m : vgG, ∃ n : nat, γ ↪N (S n''; []) ∗ l_m'sim ↦ₛ□ SOMEV #(f m n) ∗ l_sim ↦ₛ NONEV ∗ l_auth ↦ NONEV ∗ l_fchan ↦ₛ□ SOMEV (vgval m) ∗  l_rchan ↦□ SOMEV (vgval m) ∗ l_key ↦□ SOMEV (vgval (g ^+n)))%I). 
  iApply (brel_na_alloc (d1 ∨ (d2 ∨ d3))%I alphaN).
   iSplitL "Hγ Hl_m'sim Hl_sim Hl_auth Hlfchan Hlrchan Hl_key"; [iNext; iLeft; iFrame|].
   iIntros "#Hinvα".
   iApply brel_new_theory.
   iApply (brel_add_label_l with "Hschannel_l").
   iApply (brel_add_label_r with "Hschannel_r").
   iApply (brel_add_label_l with "HgK").
   iApply (brel_add_label_l with "Hchannel").
   iApply (brel_add_label_r with "Hleaksec").
   set (X :=  iLblSig_to_iLblThy [([schannel_l] , [schannel_r] , sec_channel schannel_l schannel_r)]).
   set (R := (λ u1 u2 : val, 𝟙%T u1 u2)).
   set (X' := sec_channel schannel_l schannel_r).
   iApply brel_learn. iIntros "%Hdist' _".
   About brel_exhaustion.
   iApply ((brel_exhaustion (f1 ((λ: "m", do: schannel_l InjL "m"),(λ: <>, do: schannel_l InjR bob))%V) (f2 ((λ: "m", do: schannel_r InjL "m"),(λ: <>, do: schannel_r InjR bob))%V) _ _ X' _ _ R _ _ _) with "[Hrelf1f2]").
   { try simpl; try auto; try (apply sublist_subseteq); try (apply singleton_sublist_l);
       try (apply list_elem_of_In); try simpl; try auto; try (repeat (eapply sublist_skip)) ; try eapply sublist_nil_l. admit. }
   { simpl. auto. }
   {
     set clt := ([channel'; getKey'; schannel_l], [leaksec'; schannel_r], X').
     set cltheory := iLblSig_to_iLblThy [([channel'; getKey'; schannel_l] , [leaksec'; schannel_r] , X')].
     set (L' := cltheory ++ (iLblSig_to_iLblThy L)).
     set (keytheory := iLblSig_to_iLblThy [([keyleak1], [keyleak2], keyleak keyleak1 keyleak2)]).
     set (leaktheory := (iLblSig_to_iLblThy [([leakauth1], [leakauth2], leakauth leakauth1 leakauth2)])).
     set (M := cltheory ++ keytheory ++ leaktheory ++ (iLblSig_to_iLblThy L)).
      iApply (brel_introduction_mono L' M).
     + simpl.
       iApply to_iThy_le_intro'.
       unfold L'. unfold M.  
       set (l := cltheory ++ keytheory ++ leaktheory).
      
       apply (submseteq_skips_r (iLblSig_to_iLblThy L) (cltheory) (cltheory ++ keytheory ++ leaktheory)).
       eapply submseteq_inserts_r. eapply Permutation_submseteq. auto.
     + unfold L'. iApply "Hrelf1f2". } 
    iLöb as "IH".
   unfold kl1.
   iSplit; [iIntros (v1 v2) "%Hv1v2"; iModIntro; brel_pures; iModIntro; done |].  
   iIntros (?????) "!# %Hk1 %Hk2 HXQ #Hrel".  
   iDestruct "HXQ" as "[HSendAlice | HRecvBob]".
   (* Send a message using the secure channel from Alice To Bob *)
   + iDestruct "HSendAlice" as (?m) "[[%He1 %He2] #HmQ]".
      rewrite -> He1. rewrite -> He2. brel_pures.
         { apply -> NeutralEctx_ectx_labels_singleton.
           do 2 (eapply NeutralEctx_label_cons_inv_2 in Hk1). eapply Hk1. }
         {  apply -> NeutralEctx_ectx_labels_singleton.
            eapply NeutralEctx_label_cons_inv_2 in Hk2.
            eapply NeutralEctx_label_cons_inv_1 in Hk2. eapply Hk2. } 
         iApply (brel_na_inv _ _ alphaN); first set_solver. 
         iFrame "Hinvα".
         iIntros "([(>Hγ & >Hl_m'sim & >Hl_sim & >Hl_auth & >Hl_fchan & >Hl_rchan & >Hl_key) | [>Hd2 | >Hd3 ]] & Hclose)".
          (* First message to be sent by the secure channel*)
        ++ About brel_load_r.
           iApply (brel_load_r _ _ _ _ [HandleCtx _ _ _ _ _ ; CaseCtx _ _] with "Hl_fchan").
           iIntros "Hl_fchan".
           iApply (brel_load_l _ _ _  [HandleCtx Deep MS getKey' _ _ ; HandleCtx Deep MS channel' _ _; CaseCtx _ _] with "Hl_rchan").
           iIntros "!>Hl_rchan". brel_pures.
           simpl. brel_pures. 
           iApply (brel_store_r _ _ _ _ [HandleCtx _ _ _ _ _ ; AppRCtx _] with "Hl_fchan"). iIntros "Hl_fchan".
           simpl.
           brel_pures.
           { simpl. apply not_elem_of_nil. }
           iApply (brel_store_l _ _ _  [HandleCtx _ _ _ _ _ ; HandleCtx _ _ _ _ _ ; AppRCtx _] with "Hl_rchan"). 
           iIntros "!>Hl_rchan". brel_pures; try (simpl); try (apply not_elem_of_nil).
           { admit. }
           repeat foldkont.
           iApply (brel_load_l _ _ _ [AppRCtx _ ; CaseCtx _ _] with "Hl_key"). iIntros "!> Hl_key".
           brel_pures_l.
           iApply (brel_load_r _ _ _ _ [AppRCtx _ ; CaseCtx _ _] with "Hl_m'sim"). iIntros "Hl_m'sim".
           brel_pures.
           iDestruct "Hγ" as (ms) "(%Hf' & Hγ)". apply map_eq_nil in Hf'. simplify_eq.
           iApply (brel_couple_TU_gen _ _ (f m) [AppRCtx _; AppRCtx _] _ _ _ _ _ _); simpl; auto.
           { admit. }
           simpl. iSplitL "Hγ". {iModIntro ; iFrame "Hγ". }
          iIntros (c) "Hγ". 
          brel_pures.
          iApply (brel_randT_l _ [AppRCtx _ ; AppRCtx _] γ _ _ _ _); auto.
          simpl. iSplitL "Hγ"; [iFrame "Hγ"; auto |].
          iModIntro. iIntros "Hγ %Hc".
           brel_pures. 
           simpl.
           About brel_exp_l.
           iApply (brel_exp_l [AppRCtx _ ; AppRCtx _] _ _ _ g c _).
           brel_pures.
           iApply (brel_store_l _ _ _ [AppRCtx _; AppRCtx _ ] with "Hl_key"). iIntros "!> Hl_key".
           iApply (brel_store_r _ _ _ _ [AppRCtx _; AppRCtx _] with "Hl_m'sim").
           iIntros "Hl_m'sim". brel_pures. simpl. 
           iApply fupd_brel.
           iMod (ghost_map_elem_persist with "Hl_fchan") as "#Hl_fchan".
           iMod (ghost_map_elem_persist with "Hl_rchan") as "#Hl_rchan".
           iMod (ghost_map_elem_persist with "Hl_key") as "#Hl_key".
           iMod (ghost_map_elem_persist with "Hl_m'sim") as "#Hl_m'sim".
           iModIntro.
           iApply brel_na_close. iFrame.
           iSplitL.
           { iModIntro. iRight. iRight. unfold d3.  iExists m, c.
             iFrame "Hγ Hl_m'sim Hl_sim Hl_auth Hl_fchan Hl_rchan Hl_key". }


           
            set (keytheory := iLblSig_to_iLblThy [([keyleak1], [keyleak2], keyleak keyleak1 keyleak2)]).
            set (leaktheory := (iLblSig_to_iLblThy [([leakauth1], [leakauth2], leakauth leakauth1 leakauth2)])).
            set (M := [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)] ++ leaktheory ++ (iLblSig_to_iLblThy L)).
            set (N := [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)] ++ keytheory ++ leaktheory ++ (iLblSig_to_iLblThy L)).
            brel_pures. simpl.
             iApply (brel_bind'' [AppRCtx _] [AppRCtx _] keytheory M N (𝟙%T) (Do keyleak1 (InjLV bob)) (Do keyleak2 (InjLV bob))).
             { simpl. set_solver. }
             { simpl. set_solver. }
             { simpl. unfold M. unfold N. iApply to_iThy_le_intro'. eapply Permutation_submseteq.
               eapply perm_swap. }
             {  iApply (brel_introduction' [keyleak1] [keyleak2]).
                1: { unfold keytheory.
                     eapply list_elem_of_here. }
                iExists _, _, [], [],_.
                do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
                iSplitL;  [|by iIntros "!>" (??) "H"; iApply "H"].
                iRight. iLeft. simpl. 
                repeat (iSplit; try (iPureIntro); try (unfold SendV); try reflexivity).
                iModIntro.
                 iApply brel_value.
                 iIntros "$ !>". brel_pures.
                 iAssert (distinct' N) as "%Hdistinct".
                { unfold N. unfold keytheory. unfold leaktheory. simpl.
                  unfold distinct'. iPureIntro. apply Hdist'. }
                iApply (brel_bind'' _ _ keytheory M N 𝟙%T (Do keyleak1 (InjRV bob)) (Do keyleak2 (InjRV bob))).
                { simpl. unfold M.  repeat (rewrite -> labels_l_cons). set_solver. }
                { simpl. apply list_subseteq_nil. }
                { simpl. unfold M. unfold N. iApply to_iThy_le_intro'. eapply Permutation_submseteq.
               eapply perm_swap. }
                { iApply (brel_introduction' [keyleak1] [keyleak2]).
                1: { unfold keytheory.
                     eapply list_elem_of_here. }
                iExists _, _, [], [],_.
                do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
                iSplitL;  [|by iIntros "!>" (??) "H"; iApply "H"].
                iRight. iRight. simpl.
                repeat (iSplit; try (iPureIntro); try (unfold RecvV); try reflexivity);
                  try (iModIntro); simpl.                                                                  iSplitL.
               +++    iApply brel_value.
                      iIntros "$ !>". brel_pures.
                      simpl. brel_pures.
                      iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)). 
                      { simpl. auto. set_solver. }
                      { simpl. repeat (eapply list_subseteq_skip). eapply list_subseteq_nil. }
                      { iApply "Hrel". iApply "HmQ". }
                      { iApply "IH". }
                  +++ iApply brel_value.
                      iIntros "$ !>".
                      unfold kont.
                      brel_pures. 
                      iApply (G_XOR_CORRECT_l m (g ^+ c) _ _ _ _).
                      {admit. }
                      brel_pures.
                       { simpl. unfold distinct in Hdistinct. destruct Hdistinct.
                        unfold distinct_l in H1. (*unfold LblClients in H1. simpl in H1.*)
                        unfold N in H1. simpl in H1.
                        repeat (rewrite -> labels_l_cons in H1).
                        eapply NoDup_app in H1.
                        Print val.
                        eapply NoDup_cons_1_1. destruct H1 as [H1' H2'].
                       (* apply (NoDup_app [channel'; getKey'] [schannel_l]) in H1'.
                        destruct H1' as [H1' H2''].*) (*apply H1'.*) admit.  }
                       {  simpl.
                        iApply (brel_na_inv _ _ alphaN); first set_solver.
                        iFrame "Hinvα".  
                        iIntros "([ (>Hα & >Hl_sim & >Hl_auth & >Hl_fchan' & >Hl_rchan') | [>Hd2 | >Hd3]] & Hclose)".
                         (*contradiction branch as the first message has been sent and stored*)
                          -
                            Search (_ ↦ₛ _)%I.
                            admit.
                          -
                            unfold d2. 
                            iDestruct "Hd2" as (?m ?n) "(Hγ & (Hl_m'sim' & (Hl_sim & (Hl_auth & (Hl_fchan' & (Hl_rchan' & Hl_key'))))))". 
                            iApply (brel_load_l _ _ _ [HandleCtx _ _ _ _ _ ;CaseCtx _ _] with "Hl_auth").                                          
                          iIntros "!> Hl_auth".
                          simpl. brel_pures_l.
                          iApply (brel_load_r _ _ _ _ [CaseCtx _ _] with "Hl_sim").
                          iIntros "Hl_sim". brel_pures. simpl.
                          iApply fupd_brel.
                          iModIntro.
                          iApply brel_na_close. iFrame "Hclose".
                          iSplitL.
                          { iModIntro. iRight. iLeft. iFrame "Hγ Hl_m'sim' Hl_sim Hl_auth Hl_fchan' Hl_rchan' Hl_key'". }
                         
                brel_pures. 
                iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)).
                            { simpl. auto. admit. }
                            { simpl. auto. (*admit.*) }
                            { iApply "Hrel". iApply "HmQ". }
                            { iApply "IH". }
                          - unfold d3.
                            iDestruct "Hd3" as  (?m ?n) "(Hγ & (Hl_m'sim' & (Hl_sim & (Hl_auth & (Hl_fchan' & (Hl_rchan' & Hl_key'))))))". 
                            iApply (brel_load_l _ _ _ [HandleCtx _ _ _ _ _ ;CaseCtx _ _] with "Hl_auth").                                          
                          iIntros "!> Hl_auth".
                          simpl. brel_pures_l.
                          iApply (brel_load_r _ _ _ _ [CaseCtx _ _] with "Hl_sim").
                          iIntros "Hl_sim". brel_pures. simpl.
                          About brel_exp_r.
                          iApply (brel_exp_r [AppRCtx _]). brel_pures.                     
                          iApply (brel_store_r _ _ _ _ [AppRCtx _] with "Hl_sim").
                          iIntros "Hl_sim". rel_pures. 
                          iApply (brel_store_l _ _ _ [HandleCtx _ _ _ _ _ ; AppRCtx _] with "Hl_auth").
                          iIntros "!> Hl_auth". brel_pures.
                          iApply fupd_brel.
                          iMod (ghost_map_elem_persist with "Hl_sim") as "#Hl_sim".
                          iMod (ghost_map_elem_persist with "Hl_auth") as "#Hl_auth".
                          iDestruct "Hγ" as (ns) "(%Hfγ & Hγ)".
                          apply map_eq_nil in Hfγ. simplify_eq. 
                         (* iMod (ghost_map_elem_persist with "Hγ") as "#Hγ".*)
                          iModIntro.
                          iApply brel_na_close. iFrame. 
                          iSplitL; [iModIntro; iRight; iLeft; iFrame "#" |]; try auto.
                          simpl. brel_pures.
                          set (g_sem := (bij_group_xor_sem m (valgroup.g ^+ c))).
                          About brel_bind.
                          About HandleCtx.
                          iApply (brel_bind [HandleCtx _ _ _ _ _ ; AppRCtx _] [AppRCtx _] ⊤ leaktheory
                                    N _ (Do leakauth1 (InjLV (vgval g_sem, bob)))
                            (Do leakauth2 (InjLV (vgval (valgroup.g ^+ f m c), bob)))).
                         (*  iPoseProof (brel_bind [HandleCtx Deep MS getKey' kl2 (λ: "y", "y") ;AppRCtx (λ: <>, kont1 #()%V)]
                      [AppRCtx (λ: <>, kont0 #()%V)]
                      ⊤ leaktheory N  𝟙%T
                      (Do leakauth1 (InjLV (vgval g_sem, bob)))
                      (Do leakauth2 (InjLV (vgval (valgroup.g ^+ n), bob)))) as "Hbind".
                      iApply "Hbind".*)
                         { simpl. unfold leaktheory. auto.
                            iApply (traversable_ectx_labels _ _ [getKey'] [] iThyBot _).
                            + simpl. auto.
                            + unfold kont0. simpl. auto.
                            + simpl. unfold distinct.
                              unfold distinct_l, distinct_r.
                              unfold labels_l, labels_r. simpl.
                              (*split; eapply NoDup_singleton.*)
                              admit.
                            }
                            { simpl. unfold N. iApply to_iThy_le_intro'. 
                              set (k1 :=  [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], iThyBot)] ++ keytheory).
                              apply (submseteq_middle leaktheory k1 (iLblSig_to_iLblThy L)). }
                          { iApply (brel_introduction' [leakauth1] [leakauth2]); try (unfold leaktheory);
                            try (apply list_elem_of_here).
                           iExists _, _, [], [],_.
                do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
                iSplitL;  [|by iIntros "!>" (??) "H"; iApply "H"].
                iLeft. iLeft. simpl.
                iExists _,_. repeat (iSplit; try (iPureIntro); try (unfold SendV); try reflexivity). 
                iModIntro. iApply brel_value. iIntros "$ !>".
                brel_pures. 
                iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)).
                            { simpl. auto. admit. }
                            { simpl. auto. (*admit.*) }
                            { iApply "Hrel". iApply "HmQ". }
                            { iApply "IH". }          }  }  }  }
        (* A message has already been sent by the secure channel *)     
        ++ unfold d2.
           iDestruct "Hd2" as (?m ?n) "(Hγ & (Hl_m'sim & (Hl_sim & (Hl_auth & (Hl_fchan & (Hl_rchan & Hl_key))))))".
           iDestruct "Hl_fchan" as "#Hl_fchan".
           iDestruct "Hl_rchan" as "#Hl_rchan".
           iApply (brel_load_l _ _ _  [HandleCtx _ _ _ _ _ ; HandleCtx _ _ _ _ _ ; CaseCtx _ _] with "Hl_rchan").
           iIntros "!> Hl_rchan'".
           brel_pures.
           iApply (brel_load_r _ _ _ _  [HandleCtx _ _ _ _ _ ; CaseCtx _ _] with "Hl_fchan").
           iIntros "Hl_fchan'".
           brel_pures.
           iApply brel_na_close. iFrame.
           iSplitL.
           { iModIntro. iRight. iLeft. iFrame. }
           iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)).
           { simpl. auto. admit. }
           { simpl. auto. (*admit.*) }
           { iApply "Hrel". iApply "HmQ". }
           { iApply "IH". }         
        ++ unfold d3.
           iDestruct "Hd3" as (?m ?n) "(Hγ & (Hl_m'sim & (Hl_sim & (Hl_auth & (Hl_fchan & (Hl_rchan & Hl_key))))))".                iApply (brel_load_l _ _ _  [HandleCtx _ _ _ _ _ ; HandleCtx _ _ _ _ _ ; CaseCtx _ _] with "Hl_rchan").
           iIntros "!> Hl_rchan'".
           brel_pures.
           iApply (brel_load_r _ _ _ _  [HandleCtx _ _ _ _ _ ; CaseCtx _ _] with "Hl_fchan").
           iIntros "Hl_fchan'".
           brel_pures.
           iApply brel_na_close. iFrame.
           iSplitL.
           { iModIntro. iRight. iRight. iFrame. }
           iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)).
           { simpl. auto. admit. }
           { simpl. auto. (*admit.*) }
           { iApply "Hrel". iApply "HmQ". }
           { iApply "IH". }      
           (* Bob receives the message *) 
   + iDestruct "HRecvBob" as "[%He1 [%He2 #HmQ]]".  
     rewrite -> He1. rewrite -> He2. brel_pures.
     { split.
       + apply -> NeutralEctx_ectx_labels_singleton.
         do 2 (eapply NeutralEctx_label_cons_inv_2 in Hk1). eapply Hk1.
       + simpl. (*set_solver.*) admit. }
     { split.
       + apply -> NeutralEctx_ectx_labels_singleton.
            eapply NeutralEctx_label_cons_inv_2 in Hk2.
            eapply NeutralEctx_label_cons_inv_1 in Hk2. eapply Hk2.
       + simpl. set_solver. }
     brel_pures.
      set (keytheory := iLblSig_to_iLblThy [([keyleak1], [keyleak2], keyleak keyleak1 keyleak2)]).
         set (leaktheory := (iLblSig_to_iLblThy [([leakauth1], [leakauth2], leakauth leakauth1 leakauth2)])).
         set (M := [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)]).
         set (N := [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)] ++ keytheory ++ leaktheory ++ (iLblSig_to_iLblThy L)).
         iApply (brel_bind'' _ _ keytheory M N _ (Do keyleak1 (InjRV alice)) (Do keyleak2 (InjRV alice))).
         { simpl. unfold M. unfold labels_l. simpl. set_solver.
           (*apply (list_subseteq_skip channel' [] [getKey'; schannel_l]). set_solver.*) }
        { simpl. unfold M. unfold labels_r. simpl. set_solver. }
        { iApply to_iThy_le_intro'. unfold M. unfold N.
          eapply submseteq_sublist_r.
          exists ([([channel'; getKey'; schannel_l], [leaksec'; schannel_r],
                 iThyBot)] ++ keytheory). split.
          + repeat simpl. unfold keytheory. simpl. eapply Permutation_swap.
          + set (l1 :=  [([channel'; getKey'; schannel_l], [leaksec'; schannel_r],
                            iThyBot)] ++ keytheory).
            set (l2 := leaktheory ++ iLblSig_to_iLblThy L).
            apply (sublist_inserts_r l2 l1 l1). auto. }
        {  iApply (brel_introduction' [keyleak1] [keyleak2]).
           { unfold keytheory. eapply list_elem_of_here. }
           { iExists _, _, [], [],_.
             do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
             iSplitL;  [|by iIntros "!>" (??) "H"; iApply "H"].
             iLeft. iRight. simpl.
             repeat (iSplit; try (iPureIntro); try (unfold RecvV); try reflexivity).
             iModIntro.
             (* two cases now; either keyleakrecv alice returns without a value, or it returns with a value *)
              iSplitL.
              { (* keyleka recv alice returns without a value *)
                repeat foldkont.
                iApply brel_value. 
                iIntros "$ !>". brel_pures.
                 iApply (brel_exhaustion (fill k1' (InjLV #()%V)) (fill k2' (InjLV #()%V))).
                          { simpl. set_solver. }
                          { simpl. set_solver. }
                          { iApply "Hrel".  iDestruct "HmQ" as "[Hsome Hnone]". iApply "Hnone". }
                          {iApply "IH". } }
              { (*keyleak alice returns with a value *)
                repeat foldkont.
                iApply brel_value. iIntros "$ !>". brel_pures.
                iApply (brel_bind'' _ _ keytheory M N _ (Do keyleak1 (InjLV alice)) (Do keyleak2 (InjLV alice))).
                { simpl. unfold M. unfold labels_l. simpl. (*apply (list_subseteq_skip channel' [] [getKey'; schannel_l]).*) set_solver. }
                { simpl. unfold M. unfold labels_r. simpl. set_solver. }
                {  iApply to_iThy_le_intro'. unfold M. unfold N. solve_submseteq. }
                iApply (brel_introduction' [keyleak1] [keyleak2]).
                1: { unfold keytheory.
                     eapply list_elem_of_here. }
                iExists _, _, [], [],_.
                do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
                iSplitL;  [|by iIntros "!>" (??) "H"; iApply "H"].
                iLeft. iLeft. simpl.
                repeat (iSplit; try (iPureIntro); try (unfold SendV); try reflexivity).
                iModIntro. iApply brel_value. 
                iIntros "$ !>". brel_pures.
                { simpl. unfold distinct in Hdist'. destruct Hdist' as [Hdl HdR].
                       unfold distinct_l in Hdl. unfold labels_l in Hdl. simpl in Hdl.
                       Search "NoDup".
                       assert (HNoDup : NoDup [channel'; getKey']).
                       { About sublist_NoDup. eapply sublist_NoDup; [eapply Hdl| auto].
                         eapply (sublist_inserts_r _ [channel'; getKey'] [channel'; getKey']). auto. } 
                       (*Search "NoDup". apply NoDup_cons_1_1 in HNoDup. auto. set_solver. }*)
                brel_pures.
                       repeat foldkont.
                       (* open invariant for case analysis *)
                        iApply (brel_na_inv _ _ alphaN); first set_solver. 
         iFrame "Hinvα".
         iIntros "([(>Hγ & >Hl_m'sim & >Hl_sim & >Hl_auth & >Hl_fchan & >Hl_rchan & >Hl_key) | [>Hd2 | >Hd3 ]] & Hclose)".
                  (* no message has been sent yet by the secure channel*)
                  ++ About brel_load_l.
                     iApply (brel_load_l _ _ _ [CaseCtx _ _] with "Hl_key").
                     iIntros "!> Hl_key". brel_pures.
                     iApply (brel_load_r _ _ _ _ [CaseCtx _ _] with "Hl_m'sim").
                     iIntros "Hl_m'sim". brel_pures. simpl.
                       iApply brel_na_close. iFrame.
           iSplitL.
           { iModIntro. iLeft. iFrame. }
                     
                      iApply (brel_exhaustion (fill k1'(InjLV #()%V)) (fill k2' (InjLV #()%V))).
                               { simpl. auto. admit. }
                               { simpl. set_solver. }
                               { iApply "Hrel". iDestruct "HmQ" as "[Hsome Hnone]". iApply "Hnone".  }
                               { iApply "IH". }
                               (* a message has been sent by both the secure channel and the authenticated channel *)
                ++ unfold d2.
                   iDestruct "Hd2" as (?m ?n) "(Hγ & (Hl_m'sim & (Hl_sim & (Hl_auth & (Hl_fchan & (Hl_rchan & Hl_key))))))".
                    iApply (brel_load_l _ _ _ [CaseCtx _ _] with "Hl_key").
                    iIntros "!> Hl_key". brel_pures.
                    { simpl. set_solver. }
                     iApply (brel_load_r _ _ _ _ [CaseCtx _ _] with "Hl_m'sim").
                    iIntros "Hl_m'sim". brel_pures. simpl.
                    repeat foldkont.
                    iApply fupd_brel.
                    iMod (ghost_map_elem_persist with "Hl_fchan") as "#Hl_fchan".
                    iMod (ghost_map_elem_persist with "Hl_rchan") as "#Hl_rchan".
                    iMod (ghost_map_elem_persist with "Hl_key") as "#Hl_key".
                    iMod (ghost_map_elem_persist with "Hl_m'sim") as "#Hl_m'sim".
                    iMod (ghost_map_elem_persist with "Hl_auth") as "#Hl_auth".
                    iMod (ghost_map_elem_persist with "Hl_sim") as "#Hl_sim".
                    iModIntro.
                    
                    iApply brel_na_close. iFrame.
                    iSplitL.
                    { iModIntro. iRight. iLeft. iFrame "#". }
                    iApply (brel_bind'' _ _ leaktheory M N _ (Do leakauth1 (InjRV bob)) (Do leakauth2 (InjRV bob))).
                      { simpl. unfold M. unfold labels_l. simpl. set_solver. }
                      { simpl. unfold M. unfold labels_r. simpl. set_solver. }
                      {  iApply to_iThy_le_intro'. unfold M. unfold N. Search "⊆+".
          eapply submseteq_sublist_r.
          exists ([([channel'; getKey'; schannel_l], [leaksec'; schannel_r],
                 iThyBot)] ++ leaktheory). split.
          + repeat simpl. unfold leaktheory. simpl. eapply Permutation_swap.
          + eapply sublist_skip. eapply sublist_inserts_l. eapply sublist_inserts_r. auto. }
                      { iApply (brel_introduction' [leakauth1] [leakauth2]).
                        1: { unfold leaktheory.
                             eapply list_elem_of_here. }
                        simpl.
                        iExists _, _, [], [],_.
                        do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
                        iSplitL;  [|by iIntros "!>" (??) "H"; iApply "H"].
                        iRight. iRight. simpl.
                        repeat (iSplit; try (iPureIntro); try (unfold RecvV); try reflexivity).
                        iModIntro. iSplit.
                        (* leakauth returns successfully with a value *)
                        -  iIntros (b1 b2). iApply brel_value. iIntros "$ !>".
                           brel_pures. simpl. 
                              iApply (brel_load_r _ _ _ _ [AppRCtx _] with "Hl_sim").
                              iIntros "Hl_sim'".
                              iApply (brel_load_l _ _ _ [HandleCtx _ _ _ _ _ ; AppRCtx _] with "Hl_auth").
                              iIntros "!>Hl_auth'".
                              iDestruct "Hl_fchan" as "#Hl_fchan".
                              simpl. brel_pures.
                               (*iApply brel_na_close. iFrame.
                               iSplitL; [iModIntro; iRight; iLeft; iFrame; iFrame "#" |].
                               brel_pures.*)
                               iApply G_XOR_CORRECT_l.
                               { admit. }
                               brel_pures.
                               iApply (brel_load_r _ _ _ _ [HandleCtx _ _ _ _ _ ; AppRCtx _ ] with "Hl_fchan").
                               iIntros "Hl_fchan'".
                               brel_pures.
                                set (g_enc := (bij_group_xor_sem
                                        (bij_group_xor_sem m (g ^+ n))
                                        (g ^+ n))).
                               iApply (brel_exhaustion (fill k1'((InjRV (vgval g_enc))%V)) (fill k2' ((InjRV (vgval m))%V))).
                               { simpl. auto. set_solver. }
                                { simpl. set_solver. }
                               { unfold kont0. iApply "Hrel". iDestruct "HmQ" as "[Hsome Hnone]". unfold g_enc. rewrite -> Bij_xor_sem. iApply "Hsome". }
                               { iApply "IH". }
                           (* leakauth doesnt return with a value *)
                            -  iApply brel_value. iIntros "$ !>".
                           brel_pures. simpl. 
                              iApply (brel_exhaustion (fill k1' (InjLV #()%V)) (fill k2' (InjLV #()%V))).
                          { simpl. set_solver. }
                          { simpl. set_solver. }
                          { iApply "Hrel".  iDestruct "HmQ" as "[Hsome Hnone]". iApply "Hnone". }
                          {iApply "IH". } }
                               (* a message has been sent by the secure channel but not the authenticated channel*)
                           ++ simpl. brel_pures.
                              unfold d3.
                              iDestruct "Hd3" as (?m ?n) "(Hγ & (Hl_m'sim & (Hl_sim & (Hl_auth & (Hl_fchan & (Hl_rchan & Hl_key))))))". 
                               iApply (brel_load_l _ _ _ [CaseCtx _ _] with "Hl_key").
                               iIntros "!> Hl_key". brel_pures.
                               { simpl. set_solver. }
                        iApply (brel_load_r _ _ _ _ [CaseCtx _ _] with "Hl_m'sim").
                               iIntros "Hl_m'sim". brel_pures. simpl.
                               repeat foldkont.
                               iApply fupd_brel.
                               iMod (ghost_map_elem_persist with "Hl_fchan") as "#Hl_fchan".
                               iMod (ghost_map_elem_persist with "Hl_rchan") as "#Hl_rchan".
                              iMod (ghost_map_elem_persist with "Hl_key") as "#Hl_key".
                              iMod (ghost_map_elem_persist with "Hl_m'sim") as "#Hl_m'sim".
                              iModIntro.
                    
                       iApply brel_na_close. iFrame.
           iSplitL.
           { iModIntro. iRight. iRight. iFrame "#". iFrame. }
                       iApply (brel_bind'' _ _ leaktheory M N _ (Do leakauth1 (InjRV bob)) (Do leakauth2 (InjRV bob))).
                      { simpl. unfold M. unfold labels_l. simpl. set_solver. }
                      { simpl. unfold M. unfold labels_r. simpl. set_solver. }
                      {  iApply to_iThy_le_intro'. unfold M. unfold N.
          eapply submseteq_sublist_r.
          exists ([([channel'; getKey'; schannel_l], [leaksec'; schannel_r],
                 iThyBot)] ++ leaktheory). split.
          + repeat simpl. unfold leaktheory. simpl. eapply Permutation_swap.
          + eapply sublist_skip. eapply sublist_inserts_l. eapply sublist_inserts_r. auto. }
                      { iApply (brel_introduction' [leakauth1] [leakauth2]).
                        1: { unfold leaktheory.
                             eapply list_elem_of_here. }
                        simpl.
                        iExists _, _, [], [],_.
                        do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
                        iSplitL;  [|by iIntros "!>" (??) "H"; iApply "H"].
                        iRight. iRight. simpl.
                        repeat (iSplit; try (iPureIntro); try (unfold RecvV); try reflexivity).
                        iModIntro. iSplit.
                        (* leakauth returns successfully with a value *)
                        -  iIntros (b1 b2). iApply brel_value. iIntros "$ !>".
                           brel_pures. simpl.
                           (*another case analysis by opening the invariant again, since we need access to the pointers l_sim and l_auth *)
                            iApply (brel_na_inv _ _ alphaN); first set_solver.
                            iFrame "Hinvα".
                            iIntros "([(>Hγ & >Hl_m'sim' & >Hl_sim & >Hl_auth & >Hl_fchan' & >Hl_rchan' & >Hl_key') | [>Hd2 | >Hd3 ]] & Hclose)".
                            (*contradiction branch since we already know that a message has been sent by the secure channel *)
                           -- admit.
                            (*the next two brances will move the proof forward with a case analysis on l_auth and l_sim having been set or not *)
                           -- unfold d2. 
                              iDestruct "Hd2" as (?m ?n) "(Hγ & (Hl_m'sim' & (Hl_sim & (Hl_auth & (Hl_fchan' & (Hl_rchan' & Hl_key'))))))".
                              iApply (brel_load_r _ _ _ _ [AppRCtx _] with "Hl_sim").
                              iIntros "Hl_sim".
                              iApply (brel_load_l _ _ _ [HandleCtx _ _ _ _ _ ; AppRCtx _] with "Hl_auth").
                              iIntros "!> Hl_auth".
                              iApply fupd_brel.
                              iMod (ghost_map_elem_persist with "Hl_fchan'") as "#Hl_fchan'".
                              iMod (ghost_map_elem_persist with "Hl_rchan'") as "#Hl_rchan'".
                              iMod (ghost_map_elem_persist with "Hl_key'") as "#Hl_key'".
                              iMod (ghost_map_elem_persist with "Hl_m'sim'") as "#Hl_m'sim'".
                              iMod (ghost_map_elem_persist with "Hl_auth") as "#Hl_auth".
                              iMod (ghost_map_elem_persist with "Hl_sim") as "#Hl_sim".
                              iModIntro.
                    
                       iApply brel_na_close. iFrame.
           iSplitL.
           { iModIntro. iRight. iLeft. iFrame "#". }
                              simpl. brel_pures.
                               (*iApply brel_na_close. iFrame.
                               iSplitL; [iModIntro; iRight; iLeft; iFrame; iFrame "#" |].
                               brel_pures.*)
                               iApply G_XOR_CORRECT_l.
                               { admit. }
                               brel_pures.
                               Print ectx.
                               Print frame.
                               iApply (brel_load_r _ _ _ _ [HandleCtx _ _ _ _ _ ; AppRCtx _ ] with "Hl_fchan").
                               iIntros "Hl_fchan''".
                               brel_pures.
                                set (g_enc := (bij_group_xor_sem
                                        (bij_group_xor_sem m0 (g ^+ n0))
                                        (g ^+ n))).
                               iApply (brel_exhaustion (fill k1'((InjRV (vgval g_enc))%V)) (fill k2' ((InjRV (vgval m))%V))).
                               { simpl. auto. set_solver. }
                                { simpl. set_solver. }
                                { unfold kont0. iApply "Hrel". iDestruct "HmQ" as "[Hsome Hnone]". unfold xor. unfold g_enc.
                                   iCombine "Hl_fchan Hl_fchan'" gives %[Hval Hval2].
                                  inversion Hval2. apply vgval_inj in H1. rewrite -> H1.
                                  iCombine "Hl_m'sim Hl_m'sim'" gives %[Hsim Hsim2]. clear Hval Hsim.
                                  inversion Hsim2. specialize (Hf m0). destruct Hf as [Hfinj Hfsurj].
                                  apply Nat2Z.inj in H2.
                                  apply (@inj _ _ eq eq (f m0) Hfinj n n0) in H2. rewrite -> H2.
                                  rewrite -> Bij_xor_sem. iApply "Hsome". }
                               { iApply "IH". }
                           -- unfold d3.
                              iDestruct "Hd3" as (?m ?n) "(Hγ & (Hl_m'sim' & (Hl_sim & (Hl_auth & (Hl_fchan' & (Hl_rchan' & Hl_key'))))))".
                               iApply (brel_load_r _ _ _ _ [AppRCtx _] with "Hl_sim").
                              iIntros "Hl_sim".
                              iApply (brel_load_l _ _ _ [HandleCtx _ _ _ _ _ ; AppRCtx _] with "Hl_auth").
                              iIntros "!> Hl_auth".
                                 iApply fupd_brel.
           iMod (ghost_map_elem_persist with "Hl_fchan'") as "#Hl_fchan'".
           iMod (ghost_map_elem_persist with "Hl_rchan'") as "#Hl_rchan'".
           iMod (ghost_map_elem_persist with "Hl_key'") as "#Hl_key'".
           iMod (ghost_map_elem_persist with "Hl_m'sim'") as "#Hl_m'sim'".
           iModIntro.
                    
                       iApply brel_na_close. iFrame.
           iSplitL.
           { iModIntro. iRight. iRight. iFrame "#". iFrame. }
           simpl. brel_pures.
            iApply (brel_exhaustion (fill k1' (InjLV #()%V)) (fill k2' (InjLV #()%V))).
                          { simpl. set_solver. }
                          { simpl. set_solver. }
                          { iApply "Hrel".  iDestruct "HmQ" as "[Hsome Hnone]". iApply "Hnone". }
                          {iApply "IH". }
                           (* leakauth doesnt return with a value *)
                            -  iApply brel_value. iIntros "$ !>".
                           brel_pures. simpl. 
                              iApply (brel_exhaustion (fill k1' (InjLV #()%V)) (fill k2' (InjLV #()%V))).
                          { simpl. set_solver. }
                          { simpl. set_solver. }
                          { iApply "Hrel".  iDestruct "HmQ" as "[Hsome Hnone]". iApply "Hnone". }
                          {iApply "IH". } }
Admitted.


Lemma SEM_R_CHAN_SIM (f1 f2 : val) (L : sem_row Σ) :
  (* sem_val_typed f1 f2 ((∀ᵣ θₕ, (((⊤ × (sem_ty_sum 𝟙 𝟙)) -{ θₕ }-> (Option ⊤)) × ((sem_ty_sum 𝟙 𝟙) -{ θₕ }-> (Option ⊤))) -{ sem_row_union  θₕ L }-∘ 𝟙))%T -∗*)
   (∀ᵣ θₕ, (((𝔾 -{ θₕ }-> 𝟙) × (𝟙 -{ θₕ }-> Option 𝔾)) -{ sem_row_union θₕ L }-∘ 𝟙))%T
                 f1 f2 -∗
    BREL R_CHAN f1
      ≤ CHAN_SIM_lazy (F_CHAN f2) <|⊥|> {{λ v1 v2,
                                       (* (∀ᵣ θ₁,  (((⊤ × (𝟙 + 𝟙)) -{ θ₁ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ₁ }-> Option ⊤)) ⊸ ((𝟙 + 𝟙) -{ θ₁ }-> Option ⊤) -{ sem_row_union θ₁ L }-∘ 𝟙)%T v1 v2 }}.*)
                                       (∀ᵣ θ₁, ∀ᵣ θ₂,  (((𝔾 × (𝟙 + 𝟙)) -{ θ₁ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ₁ }-> Option 𝟙)) ⊸ (((𝟙 + 𝟙) -{ θ₂ }-> 𝟙) ×(𝟙 + 𝟙) -{ θ₂ }-> Option 𝟙) -{ sem_row_union (sem_row_union θ₁ θ₂) L }-∘ 𝟙)%T v1 v2 }}.
Proof with (repeat foldkont) using G.
 iIntros "Hrelf1f2". 
  repeat simpl. 
  unfold R_CHAN. brel_pures.
  unfold right_composition. brel_pures.
  unfold CHAN.
  repeat simpl. brel_pures'.
  
  (*unfold CHAN_SIM, F_OAUTH.*)
 
  (*iApply (xor_correct_l ⊤ _ _ _ (CHAN_SIM (F_CHAN f2)) ⊥ _).*)
  unfold F_CHAN, CHAN_SIM_lazy. (*F_KE, F_OAUTH.*) 
   
  repeat simpl. brel_pures. iModIntro. iIntros (autheff keyeff). 
  simpl.
  iIntros (autheff_l autheff_r) "Hautheff".
  iDestruct "Hautheff" as (asnd_l asnd_r arcv_l arcv_r) "(%H1al & %H2al & (#Hasnd & #Harcv))".
  brel_pures. iModIntro.
  iIntros (keyeff_l keyeff_r) "Hkeyeff".
  iDestruct "Hkeyeff" as (kysnd_l kysnd_r kyrcv_l kyrcv_r) "(%H1k & %H2k & (#Hkeysnd & #Hkeyrcv))".
  (*iDestruct "Hkeyeff" as "(%Hkeyeff_l & (%Hkeyeff_r & Hkeyeffrel))".
  rewrite Hkeyeff_l. rewrite Hkeyeff_r.*)
  rewrite H1al. rewrite H2al. rewrite H1k. rewrite H2k.
  brel_pures.
  unfold F_OAUTH, F_KE_lazy_alice.
  brel_pures.  

   iApply brel_alloc_r. iIntros (l_sim) "Hl_sim". brel_pures_r.
  iApply brel_alloc_r. iIntros (l_m'sim) "Hl_m'sim". brel_pures_r.
  iApply brel_alloctape_l. iIntros (γ) "!> Hγ". brel_pures_l.
  iApply brel_alloc_l. iIntros (l_key) "!> Hl_key". brel_pures_l.
   iApply brel_effect_l. iIntros (getKey') "!> HgK !>". brel_pures_l.
  iApply brel_effect_r. iIntros (leaksec') "Hleaksec !>". brel_pures.
  iApply brel_alloc_l. iIntros (l_auth) "!>Hl_auth". brel_pures_l.
  iApply brel_effect_l. iIntros (channel') "!> Hchannel !>". brel_pures_l.
  
 
  iApply brel_alloc_r. iIntros (l_fchan) "Hlfchan". brel_pures_r.
  iApply brel_effect_r. iIntros (schannel_r) "Hschannel_r !>". brel_pures_r.
  brel_pures'. repeat simpl. brel_pures'.
  iApply brel_alloc_l. iIntros (l_rchan) "!>Hlrchan". brel_pures_l.
  iApply brel_effect_l. iIntros (schannel_l) "!> Hschannel_l !>". brel_pures_l.  
  set (kl1 := ( match: "payload" with
         InjL "m" =>
           match: ! #l_rchan with
             InjL <> =>
               #l_rchan <- InjR "m";; 
               let: "key" := (λ: "party", do: getKey' "party")%V bob in
               match: "key" with
                 InjL <> => "k" #()%V
               | InjR "x" =>
                 match: G_XOR xor "m" "x" with
                   InjL <> => "k" #()%V
                 | InjR "mg" =>
                   (λ: "m", do: channel' InjL "m")%V ("mg", bob);; "k" #()%V
                 end
               end
           | InjR "m" => "k" #()%V
           end
       | InjR <> =>
         let: "key" := (λ: "party", do: getKey' "party")%V alice in
         match: "key" with
           InjL <> => "k" (InjLV #()%V)
         | InjR "key" =>
           let: "r" := (λ: "m", do: channel' InjR "m")%V bob in
           match: "r" with
             InjL <> => "k" (InjLV #()%V)
           | InjR "x" =>
             match: G_XOR xor "x" "key" with
               InjL <> => "k" (InjL #()%V)
             | InjR "mg" => "k" (InjR "mg")
             end
           end
         end
       end )%E ).
  set (kl2 := ( match: "payload" with
         InjL "payload" =>
           let: "dst" := "payload" in
           let: "m" := Fst "dst" in
           let: "dst" := Snd "dst" in
           match: ! #l_auth with
             InjL <> => #l_auth <- InjR "m";; asnd_l ("m", "dst");; "k" #()%V
           | InjR "message" => "k" #()%V
           end
       | InjR "from" =>
         let: "r" := arcv_l "from" in
         match: "r" with
           InjL <> => "k" (InjLV #()%V)
         | InjR "x" => "k" ! #l_auth
         end
       end )%E).
  set (kl3 := ( match: "p" with
         InjL <> =>
           let: "key" := (λ: <>,
                            match: ! #l_key with
                              InjL <> =>
                                let: "c" := #();; rand(#lbl:γ) #(S n'') in
                                let: "key" := vexp g "c" in
                                #l_key <- InjR "key";; "key"
                            | InjR "key" => "key"
                            end)%V
                           #()%V in
           kysnd_l bob;; 
           let: "r" := kyrcv_l bob in
           match: "r" with
             InjL <> => "k" (InjLV #()%V)
           | InjR "w" => "k" (InjR "key")
           end
       | InjR <> =>
         let: "r" := kyrcv_l alice in
         match: "r" with
           InjL <> => "k" (InjLV #()%V)
         | InjR "w" =>
           kysnd_l alice;; 
           match: ! #l_key with
             InjL <> => "k" (InjLV #()%V)
           | InjR "key" => "k" (InjR "key")
           end
         end
       end )%E).
  set (kr1 := ( match: "payload" with
         InjL "m" =>
           match: ! #l_fchan with
             InjL <> =>
               #l_fchan <- InjR "m";; 
               (λ: "m", do: leaksec' InjL "m")%V alice;; "k" #()%V
           | InjR "x" => "k" #()%V
           end
       | InjR <> =>
         let: "r" := (λ: "m", do: leaksec' InjR "m")%V bob in
         match: "r" with
           InjL <> => "k" (InjLV #()%V)
         | InjR "x" => "k" (InjR ! #l_fchan)
         end
       end )%E).
  set (kr2 := ( match: "payload" with
         InjL <> =>
           let: "m'" := (λ: <>,
                           match: ! #l_m'sim with
                             InjL <> =>
                               let: "m'" := #();; rand #(S n'') in
                               #l_m'sim <- InjR "m'";; "m'"
                           | InjR "m'" => "m'"
                           end)%V
                          #()%V in
           kysnd_r bob;; 
           let: "r" := kyrcv_r bob in
           match: "r" with
             InjL <> => "k" (InjLV #()%V)
           | InjR "x" =>
             match: ! #l_sim with
               InjL <> =>
                 let: "mA" := vexp g "m'" in
                 #l_sim <- InjR "m'";; asnd_r ("mA", bob);; "k" #()%V
             | InjR "m" => "k" #()%V
             end
           end
       | InjR <> =>
         let: "r" := kyrcv_r alice in
         match: "r" with
           InjL <> => "k" (InjLV #()%V)
         | InjR "x" =>
           kysnd_r alice;; 
           match: ! #l_m'sim with
             InjL <> => "k" (InjLV #()%V)
           | InjR "_" =>
             let: "rla" := arcv_r bob in
             match: "rla" with
               InjL <> => "k" (InjLV #()%V)
             | InjR "x" => "k" ! #l_sim
             end
           end
         end
       end )%E).
  set (θ := client_row channel' leaksec' getKey' schannel_l schannel_r).
  iSpecialize ("Hrelf1f2" $! θ).
  unfold sem_ty_arr, sem_ty_mbang. simpl.
  iAssert (sem_val_typed  ((λ: "m", do: schannel_l InjL "m"), (λ: <>, do: schannel_l InjR bob))%V ((λ: "m", do: schannel_r InjL "m") , (λ: <>, do: schannel_r InjR bob))%V (((𝔾 -{ θ }-> 𝟙) × (𝟙 -{ θ }-> (Option 𝔾)))%T)) as "Hschn".
  { iApply SEM_TYPED_EFF. }
  unfold sem_val_typed. simpl.
  iDestruct "Hschn" as "#Hschn".
  iSpecialize ("Hrelf1f2" with "Hschn"). simpl.
   set (f m := (λ x, int_of_vg_sem (bij_group_xor_sem m (g ^+x)))).
   assert (Hf : ∀ m : vgG, Bij (f m)).
   { admit. }
  set (d1 := (γ ↪N (S n''; []) ∗ l_m'sim ↦ₛ NONEV ∗ l_sim ↦ₛ NONEV ∗ l_auth ↦ NONEV ∗ l_fchan ↦ₛ NONEV ∗ l_rchan ↦ NONEV ∗  l_key ↦ NONEV)%I).
  set (d2 := ((∃ m : vgG, ∃ n : nat, γ ↪N (S n''; []) ∗ l_m'sim ↦ₛ□ SOMEV #(f m n) ∗ l_sim ↦ₛ□ SOMEV #(f m n) ∗
                  l_auth ↦□ SOMEV (vgval
                                     (bij_group_xor_sem m (g ^+ n)))%V ∗  l_fchan ↦ₛ□ SOMEV (vgval m) ∗  l_rchan ↦□ SOMEV (vgval m) ∗ l_key ↦□ SOMEV (vgval (g ^+n)))%I)).

  set (d3 := (∃ m : vgG, ∃ n : nat, γ ↪N (S n''; []) ∗ l_m'sim ↦ₛ□ SOMEV #(f m n) ∗ l_sim ↦ₛ NONEV ∗ l_auth ↦ NONEV ∗ l_fchan ↦ₛ□ SOMEV (vgval m) ∗  l_rchan ↦□ SOMEV (vgval m) ∗ l_key ↦□ SOMEV (vgval (g ^+n)))%I). 
  iApply (brel_na_alloc (d1 ∨ (d2 ∨ d3))%I alphaN).
   iSplitL "Hγ Hl_m'sim Hl_sim Hl_auth Hlfchan Hlrchan Hl_key"; [iNext; iLeft; iFrame|].
   iIntros "#Hinvα".
   iApply brel_new_theory.
   iApply (brel_add_label_l with "Hschannel_l").
   iApply (brel_add_label_r with "Hschannel_r").
   iApply (brel_add_label_l with "HgK").
   iApply (brel_add_label_l with "Hchannel").
   iApply (brel_add_label_r with "Hleaksec").
   set (X :=  iLblSig_to_iLblThy [([schannel_l] , [schannel_r] , sec_channel schannel_l schannel_r)]).
   set (R := (λ u1 u2 : val, 𝟙%T u1 u2)).
   set (X' := sec_channel schannel_l schannel_r).
   iApply brel_learn. iIntros "%Hdist' _".
   About brel_exhaustion.
   iApply ((brel_exhaustion (f1 ((λ: "m", do: schannel_l InjL "m"),(λ: <>, do: schannel_l InjR bob))%V) (f2 ((λ: "m", do: schannel_r InjL "m"),(λ: <>, do: schannel_r InjR bob))%V) _ _ X' _ _ R _ _ _) with "[Hrelf1f2]").
   { try simpl; try auto; try (apply sublist_subseteq); try (apply singleton_sublist_l);
       try (apply list_elem_of_In); try simpl; try auto; try (repeat (eapply sublist_skip)) ; try eapply sublist_nil_l. admit. }
   { simpl. set_solver. }   
   {
     set clt := ([channel'; getKey'; schannel_l], [leaksec'; schannel_r], X').
     set cltheory := iLblSig_to_iLblThy [([channel'; getKey'; schannel_l] , [leaksec'; schannel_r] , X')].
     set (L' := cltheory ++ (iLblSig_to_iLblThy L)).
     About sem_row_union.
     Print sem_row.
    (* set (keytheory := iLblSig_to_iLblThy [([keyleak1], [keyleak2], keyleak keyleak1 keyleak2)]).
     set (leaktheory := (iLblSig_to_iLblThy [([leakauth1], [leakauth2], leakauth leakauth1 leakauth2)])).*)
     set (keytheory := keyeff).
     set (leaktheory := autheff).
     set (M := cltheory ++ (iLblSig_to_iLblThy (sem_row_union (sem_row_union leaktheory keytheory) L))).
      iApply (brel_introduction_mono L' M).
     + simpl.
       iApply to_iThy_le_intro'.
       unfold L'. unfold M.
       set (l := cltheory ++ iLblSig_to_iLblThy (sem_row_union leaktheory keytheory)).
       Search iLblSig_to_iLblThy.
       (*rewrite -> iLblSig_to_iLblThy_app.
       apply (submseteq_skips_r (iLblSig_to_iLblThy L) (cltheory) (cltheory ++ keytheory ++ leaktheory)).
       eapply submseteq_inserts_r. eapply Permutation_submseteq. auto. *)
       admit.
     + unfold L'. unfold cltheory. simpl. iApply "Hrelf1f2". } 
    iLöb as "IH".
   unfold kl1.
   iSplit; [iIntros (v1 v2) "%Hv1v2"; iModIntro; brel_pures; iModIntro; done |].  
   iIntros (?????) "!# %Hk1 %Hk2 HXQ #Hrel".  
   iDestruct "HXQ" as "[HSendAlice | HRecvBob]".
   (* Send a message using the secure channel from Alice To Bob *)
   + iDestruct "HSendAlice" as (?m) "[[%He1 %He2] #HmQ]".
      rewrite -> He1. rewrite -> He2. brel_pures.
         { apply -> NeutralEctx_ectx_labels_singleton.
           do 2 (eapply NeutralEctx_label_cons_inv_2 in Hk1). eapply Hk1. }
         {  apply -> NeutralEctx_ectx_labels_singleton.
            eapply NeutralEctx_label_cons_inv_2 in Hk2.
            eapply NeutralEctx_label_cons_inv_1 in Hk2. eapply Hk2. } 
         iApply (brel_na_inv _ _ alphaN); first set_solver.
         iFrame "Hinvα".
           iIntros "([(>Hγ & >Hl_m'sim & >Hl_sim & >Hl_auth & >Hl_fchan & >Hl_rchan & >Hl_key) | [>Hd2 | >Hd3 ]] & Hclose)".
          (* First message to be sent by the secure channel*)
        ++ About brel_load_r.
           iApply (brel_load_r _ _ _ _ [HandleCtx _ _ _ _ _ ; CaseCtx _ _] with "Hl_fchan").
           iIntros "Hl_fchan".
           iApply (brel_load_l _ _ _  [HandleCtx Deep MS getKey' _ _ ; HandleCtx Deep MS channel' _ _; CaseCtx _ _] with "Hl_rchan").
           iIntros "!>Hl_rchan". brel_pures.
           simpl. brel_pures. 
           iApply (brel_store_r _ _ _ _ [HandleCtx _ _ _ _ _ ; AppRCtx _] with "Hl_fchan"). iIntros "Hl_fchan".
           simpl.
           brel_pures.
           { simpl. apply not_elem_of_nil. }
           iApply (brel_store_l _ _ _  [HandleCtx _ _ _ _ _ ; HandleCtx _ _ _ _ _ ; AppRCtx _] with "Hl_rchan"). 
           iIntros "!>Hl_rchan". brel_pures; try (simpl); try (apply not_elem_of_nil).
           { admit. }
           repeat foldkont.
           iApply (brel_load_l _ _ _ [AppRCtx _ ; CaseCtx _ _] with "Hl_key"). iIntros "!> Hl_key".
           brel_pures_l.
           iApply (brel_load_r _ _ _ _ [AppRCtx _ ; CaseCtx _ _] with "Hl_m'sim"). iIntros "Hl_m'sim".
           brel_pures.
           iDestruct "Hγ" as (ms) "(%Hf' & Hγ)". apply map_eq_nil in Hf'. simplify_eq.
          iApply (brel_couple_TU_gen _ _ (f m) [AppRCtx _; AppRCtx _] _ _ _ _ _ _); simpl; auto.
          { admit. }
          simpl. iSplitL "Hγ". {iModIntro ; iFrame "Hγ". }
          iIntros (c) "Hγ". 
          brel_pures.
          iApply (brel_randT_l _ [AppRCtx _ ; AppRCtx _] γ _ _ _ _); auto.
          simpl. iSplitL "Hγ"; [iFrame "Hγ"; auto |].
          iModIntro. iIntros "Hγ %Hc".
           brel_pures. 
           simpl.
           About brel_exp_l.
           iApply (brel_exp_l [AppRCtx _ ; AppRCtx _] _ _ _ g c _).
           brel_pures.
           iApply (brel_store_l _ _ _ [AppRCtx _; AppRCtx _ ] with "Hl_key"). iIntros "!> Hl_key".
           iApply (brel_store_r _ _ _ _ [AppRCtx _; AppRCtx _] with "Hl_m'sim").
           iIntros "Hl_m'sim". brel_pures. simpl. 
           iApply fupd_brel.
           iMod (ghost_map_elem_persist with "Hl_fchan") as "#Hl_fchan".
           iMod (ghost_map_elem_persist with "Hl_rchan") as "#Hl_rchan".
           iMod (ghost_map_elem_persist with "Hl_key") as "#Hl_key".
           iMod (ghost_map_elem_persist with "Hl_m'sim") as "#Hl_m'sim".
           iModIntro.
           iApply brel_na_close. iFrame.
           iSplitL.
           { iModIntro. iRight. iRight. unfold d3.  iExists m, c.
             iFrame "Hγ Hl_m'sim Hl_sim Hl_auth Hl_fchan Hl_rchan Hl_key". }
           (* set (keytheory := iLblSig_to_iLblThy [([keyleak1], [keyleak2], keyleak keyleak1 keyleak2)]).*)
            set (keytheory := keyeff).
            (* set (leaktheory := (iLblSig_to_iLblThy [([leakauth1], [leakauth2], leakauth leakauth1 leakauth2)])).*)
            set (leaktheory := autheff).
            set (M := [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)] ++ (iLblSig_to_iLblThy (sem_row_union leaktheory L))).
            set (N := [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)] ++ (iLblSig_to_iLblThy (sem_row_union (sem_row_union leaktheory keytheory) L))).
             iApply (brel_bind'' [ AppRCtx _] [AppRCtx _] (iLblSig_to_iLblThy keytheory) M N (𝟙%T) (kysnd_l bob) (kysnd_r bob)).
             { simpl. set_solver. }
             { simpl. set_solver. }
             { simpl. unfold M. unfold N. iApply to_iThy_le_intro'. eapply Permutation_submseteq.
               (*eapply perm_swap.*) admit. }
             { About brel_wand.
               iApply (brel_wand _ _ _  R _ ).
               { iDestruct "Hkeysnd" as "#Hkeysnd".
                 iSpecialize ("Hkeysnd" $! bob bob).
                 iApply "Hkeysnd".
                 { unfold sem_ty_sum, sem_ty_unit. unfold bob. iExists #()%V, #()%V.
                   iLeft. repeat (iSplit); try (iPureIntro); try reflexivity. } }
               iModIntro. iIntros (v1 v2) "#HRv1v2".
               brel_pures.
                iApply (brel_bind'' _ _ (iLblSig_to_iLblThy keytheory) M N 𝟙%T (kyrcv_l bob) (kyrcv_r bob)).
                { simpl. unfold M.  repeat (rewrite -> labels_l_cons). set_solver. }
                { simpl. apply list_subseteq_nil. }
                { simpl. unfold M. unfold N. iApply to_iThy_le_intro'. eapply Permutation_submseteq.
               (*eapply perm_swap.*) admit. }
                (*iApply (brel_introduction' [keyleak1] [keyleak2]).*)
                iApply brel_wand.
                { iDestruct "Hkeyrcv" as "#Hkeyrcv".
                  iSpecialize ("Hkeyrcv" $! bob bob).
                  iApply "Hkeyrcv".
                  { unfold bob. unfold sem_ty_sum. iExists #()%V, #()%V.
                    repeat iSplit; try (iPureIntro); try reflexivity; try (left); repeat split;
                      try reflexivity. } }
                iModIntro. iIntros (v0 v3) "#Hv0v3".
                unfold sem_ty_group, sem_ty_option, sem_ty_sum.
                iDestruct "Hv0v3" as (?w1 ?w2) "#Hv0v3".
                (* keyleak recv returns succesfully or not *)
                iDestruct "Hv0v3" as "[Hnone | Hsome]".
               ++ iDestruct "Hnone" as "(%Hv0 & (%Hv3 & Hw1w2))".
                  rewrite -> Hv0. rewrite -> Hv3. unfold sem_ty_unit.
                  iDestruct "Hw1w2" as "(%Hw1 & %Hw2)".
                  rewrite -> Hw1. rewrite -> Hw2.
                  brel_pures.
                   iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)). 
                      { simpl. auto. set_solver. }
                      { simpl. repeat (eapply list_subseteq_skip). eapply list_subseteq_nil. }
                      { iApply "Hrel". iApply "HmQ". }
                      { iApply "IH". }
               ++ iDestruct "Hsome" as "(%Hv0 & (%Hv3 &Hw1w2))".
                  rewrite -> Hv0. rewrite -> Hv3.
                  unfold sem_ty_unit.
                  iDestruct "Hw1w2" as "(%Hw1 & %Hw2)".
                  rewrite -> Hw1. rewrite -> Hw2.
                  brel_pures.
                  iApply G_XOR_CORRECT_l.
                  { admit. }
                  brel_pures.
                  { simpl. unfold distinct in Hdist'. destruct Hdist'.
                        unfold distinct_l in H1. (*unfold LblClients in H1. simpl in H1.*)
                        unfold N in H1. simpl in H1.
                        repeat (rewrite -> labels_l_cons in H1).
                        eapply NoDup_app in H1.
                        Print val.
                        eapply NoDup_cons_1_1. destruct H1 as [H1' H2'].
                        (*apply (NoDup_app [channel'; getKey'] [schannel_l]) in H1'.
                        destruct H1' as [H1' H2'']. (*apply H1'.*)*) admit.  }
                          iApply (brel_na_inv _ _ alphaN); first set_solver.
                  iFrame "Hinvα".
                        iIntros "([ (>Hα & >Hl_sim & >Hl_auth & >Hl_fchan' & >Hl_rchan') | [>Hd2 | >Hd3]] & Hclose)".
                         (*contradiction branch as the first message has been sent and stored*)
                          -
                            Search (_ ↦ₛ _)%I.
                            admit.
                          -
                            unfold d2. 
                            iDestruct "Hd2" as (?m ?n) "(Hγ & (Hl_m'sim' & (Hl_sim & (Hl_auth & (Hl_fchan' & (Hl_rchan' & Hl_key'))))))". 
                            iApply (brel_load_l _ _ _ [HandleCtx _ _ _ _ _ ;CaseCtx _ _] with "Hl_auth").                                          
                          iIntros "!> Hl_auth".
                          simpl. brel_pures_l.
                          iApply (brel_load_r _ _ _ _ [CaseCtx _ _] with "Hl_sim").
                          iIntros "Hl_sim". brel_pures. simpl.
                          iApply fupd_brel.
                          iModIntro.
                          iApply brel_na_close. iFrame "Hclose".
                          iSplitL.
                          { iModIntro. iRight. iLeft. iFrame "Hγ Hl_m'sim' Hl_sim Hl_auth Hl_fchan' Hl_rchan' Hl_key'". }
                         
                brel_pures. 
                iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)).
                            { simpl. auto. admit. }
                            { simpl. auto. (*admit.*) }
                            { iApply "Hrel". iApply "HmQ". }
                            { iApply "IH". }
                          - unfold d3.
                            iDestruct "Hd3" as (?m ?n) "(Hγ & (Hl_m'sim' & (Hl_sim & (Hl_auth & (Hl_fchan' & (Hl_rchan' & Hl_key'))))))". 
                            iApply (brel_load_l _ _ _ [HandleCtx _ _ _ _ _ ;CaseCtx _ _] with "Hl_auth").                                          
                          iIntros "!> Hl_auth".
                          simpl. brel_pures_l.
                          iApply (brel_load_r _ _ _ _ [CaseCtx _ _] with "Hl_sim").
                          iIntros "Hl_sim". brel_pures. simpl.
                          iApply (brel_exp_r [AppRCtx _]). brel_pures.                     
                          iApply (brel_store_r _ _ _ _ [AppRCtx _] with "Hl_sim").
                          iIntros "Hl_sim". rel_pures. 
                          iApply (brel_store_l _ _ _ [HandleCtx _ _ _ _ _ ; AppRCtx _] with "Hl_auth").
                          iIntros "!> Hl_auth". brel_pures.
                          iApply fupd_brel.
                          iMod (ghost_map_elem_persist with "Hl_sim") as "#Hl_sim".
                          iMod (ghost_map_elem_persist with "Hl_auth") as "#Hl_auth".
                          iDestruct "Hγ" as (ns) "(%Hfγ & Hγ)".
                          apply map_eq_nil in Hfγ. simplify_eq. 
                         (* iMod (ghost_map_elem_persist with "Hγ") as "#Hγ".*)
                          iModIntro.
                          iApply brel_na_close. iFrame. 
                          iSplitL; [iModIntro; iRight; iLeft; iFrame "#" |]; try auto.
                          simpl. brel_pures.
                          set (g_sem := (bij_group_xor_sem m (valgroup.g ^+ c))).
                          repeat foldkont.
                          unfold kl3.
                          set (hbranchleft := (λ: "p" "k",
                                               match: "p" with
                              InjL <> =>
                              let: "key" := (λ: <>,
                            match: ! #l_key with
                              InjL <> =>
                                let: "c" := 
                                #();; rand(#lbl:γ) #(S n'') in
                                let: "key" := 
                                vexp valgroup.g "c" in
                                #l_key <- InjR "key";; "key"
                            | InjR "key" => "key"
                            end)%V
                           #()%V in
                           kysnd_l bob;; 
                          let: "r" := kyrcv_l bob in
                          match: "r" with
                           InjL <> => "k" (InjLV #()%V)
                         | InjR "w" => "k" (InjR "key")
                         end
                         | InjR <> =>
                           let: "r" := kyrcv_l alice in
                           match: "r" with
                            InjL <> => "k" (InjLV #()%V)
                          | InjR "w" =>
                          kysnd_l alice;; 
                         match: ! #l_key with
                          InjL <> => "k" (InjLV #()%V)
                        | InjR "key" => "k" (InjR "key")
                        end
                        end
                        end)%E).
             
                          iPoseProof (brel_bind [HandleCtx Deep MS getKey' hbranchleft (λ: "y", "y"); AppRCtx (λ: <>, kont1 #()%V)]
                      [AppRCtx (λ: <>, kont0 #()%V)]
                      ⊤ (iLblSig_to_iLblThy leaktheory) N  𝟙%T
                      (asnd_l (vgval g_sem, bob))%V
                      (asnd_r (vgval (valgroup.g ^+ f m c), bob))%V) as "Hbind".
                           iApply "Hbind".
                         (* iApply (brel_bind [HandleCtx _ _ _ _ _ ; AppRCtx _] [AppRCtx _] ⊤ (iLblSig_to_iLblThy leaktheory)
                                    N _ (asnd_l (InjLV (vgval g_sem, bob)))
                            (asnd_r (InjLV (vgval (valgroup.g ^+ f m c), bob)))).*)
                         { simpl. unfold leaktheory. auto.
                            iApply (traversable_ectx_labels _ _ [getKey'] [] iThyBot _).
                            + simpl. auto.
                            + unfold kont0. simpl. auto.
                            + simpl. unfold distinct.
                              unfold distinct_l, distinct_r.
                              unfold labels_l, labels_r. simpl.
                              (*split; eapply NoDup_singleton.*)
                              admit.
                            }
                            { simpl. unfold N. iApply to_iThy_le_intro'. 
                             (* set (k1 :=  [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], iThyBot)] ++ keytheory).
                              apply (submseteq_middle leaktheory k1 (iLblSig_to_iLblThy L)).*) admit. }
                            {   iApply (brel_wand _ _ _ R _).
                            {  iDestruct "Hasnd" as "#Hasnd".
                               iSpecialize ("Hasnd" $! (vgval g_sem, bob)%V).
                               iSpecialize ("Hasnd" $! (vgval (valgroup.g ^+ f m c), bob)%V).
                               iApply "Hasnd".
                               unfold g_sem. simpl. unfold sem_ty_prod.
                               iExists ((bij_group_xor_sem m (valgroup.g ^+ c))) , (vgval (valgroup.g ^+ f m c)) , bob , bob.
                               repeat (iSplit); try (iPureIntro); try reflexivity.
                               + auto. admit.
                               + admit. }
                            iModIntro. iIntros (v0 v3) "#HRv0v3".
                            unfold R. unfold sem_ty_unit.
                            iDestruct "HRv0v3" as "(%Hv0 & %Hv3)".
                            rewrite -> Hv0. rewrite -> Hv3.
                            brel_pures.
                            iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)).
                            { simpl. auto. set_solver. }
                            { simpl. auto. (*admit.*) }
                            { iApply "Hrel". iApply "HmQ". }
                            { iApply "IH". } } }
        (* A message has already been sent by the secure channel *)     
        ++ unfold d2.
           iDestruct "Hd2" as (?m ?n) "(Hγ & (Hl_m'sim & (Hl_sim & (Hl_auth & (Hl_fchan & (Hl_rchan & Hl_key))))))".
           iDestruct "Hl_fchan" as "#Hl_fchan".
           iDestruct "Hl_rchan" as "#Hl_rchan".
           iApply (brel_load_l _ _ _  [HandleCtx _ _ _ _ _ ; HandleCtx _ _ _ _ _ ; CaseCtx _ _] with "Hl_rchan").
           iIntros "!> Hl_rchan'".
           brel_pures.
           iApply (brel_load_r _ _ _ _  [HandleCtx _ _ _ _ _ ; CaseCtx _ _] with "Hl_fchan").
           iIntros "Hl_fchan'".
           brel_pures.
           iApply brel_na_close. iFrame.
           iSplitL.
           { iModIntro. iRight. iLeft. iFrame. }
           iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)).
           { simpl. auto. admit. }
           { simpl. auto. (*admit.*) }
           { iApply "Hrel". iApply "HmQ". }
           { iApply "IH". }         
        ++ unfold d3.
           iDestruct "Hd3" as (?m ?n) "(Hγ & (Hl_m'sim & (Hl_sim & (Hl_auth & (Hl_fchan & (Hl_rchan & Hl_key))))))".                iApply (brel_load_l _ _ _  [HandleCtx _ _ _ _ _ ; HandleCtx _ _ _ _ _ ; CaseCtx _ _] with "Hl_rchan").
           iIntros "!> Hl_rchan'".
           brel_pures.
           iApply (brel_load_r _ _ _ _  [HandleCtx _ _ _ _ _ ; CaseCtx _ _] with "Hl_fchan").
           iIntros "Hl_fchan'".
           brel_pures.
           iApply brel_na_close. iFrame.
           iSplitL.
           { iModIntro. iRight. iRight. iFrame. }
           iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)).
           { simpl. auto. admit. }
           { simpl. auto. (*admit.*) }
           { iApply "Hrel". iApply "HmQ". }
           { iApply "IH". }

           
        + iDestruct "HRecvBob" as "[%He1 [%He2 #HmQ]]".  
     rewrite -> He1. rewrite -> He2. brel_pures.
     { split.
       + apply -> NeutralEctx_ectx_labels_singleton.
         do 2 (eapply NeutralEctx_label_cons_inv_2 in Hk1). eapply Hk1.
       + simpl. (*set_solver.*) admit. }
     { split.
       + apply -> NeutralEctx_ectx_labels_singleton.
            eapply NeutralEctx_label_cons_inv_2 in Hk2.
            eapply NeutralEctx_label_cons_inv_1 in Hk2. eapply Hk2.
       + simpl. set_solver. }
     brel_pures.
       (* set (keytheory := iLblSig_to_iLblThy [([keyleak1], [keyleak2], keyleak keyleak1 keyleak2)]).*)
     set (keytheory := keyeff).
     set (leaktheory := autheff).
        (* set (leaktheory := (iLblSig_to_iLblThy [([leakauth1], [leakauth2], leakauth leakauth1 leakauth2)])).*)
         set (M := [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)]).
         (* set (N := [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)] ++ keytheory ++ leaktheory ++ (iLblSig_to_iLblThy L)).*)
         set (N := [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)] ++
                     iLblSig_to_iLblThy (sem_row_union (sem_row_union keytheory leaktheory) L)).
         repeat foldkont.
         brel_pures.
         set (leftkontbind := ( match: "r" with
       InjL <> => kont (InjLV #()%V)
     | InjR "w" =>
       kysnd_l alice;; 
       match: ! #l_key with
         InjL <> => kont (InjLV #()%V)
       | InjR "key" => kont (InjR "key")
       end
     end )%E).
         set (rightkontbind := ( match: "r" with
       InjL <> => kont0 (InjLV #()%V)
     | InjR "x" =>
       kysnd_r alice;; 
       match: ! #l_m'sim with
         InjL <> => kont0 (InjLV #()%V)
       | InjR "_" =>
         let: "rla" := arcv_r bob in
         match: "rla" with
           InjL <> => kont0 (InjLV #()%V)
         | InjR "x" => kont0 ! #l_sim
         end
       end
                                 end )%E).
          iApply (brel_bind'' _ _  (iLblSig_to_iLblThy (keytheory))  [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)] (([channel'; getKey'; schannel_l], [leaksec'; schannel_r], iThyBot)
     :: iLblSig_to_iLblThy (sem_row_union (sem_row_union leaktheory keytheory) L)) (𝟙%T) (kyrcv_l alice) (kyrcv_r alice)).
         { simpl. unfold M. unfold labels_l. simpl. (*apply (list_subseteq_skip channel' [] [getKey'; schannel_l]). set_solver.*) admit. }
        { simpl. unfold M. unfold labels_r. simpl. set_solver. }
        { iApply to_iThy_le_intro'. unfold M. unfold N. admit. (*  eapply submseteq_sublist_r.  *) }
        iApply brel_wand.
          {  iDestruct "Hkeyrcv" as "#Hkeyrcv".
            iSpecialize ("Hkeyrcv" $! alice alice).
            iApply "Hkeyrcv". unfold sem_ty_sum, sem_ty_unit.
            iExists #()%V, #()%V. unfold alice.
            repeat (iSplit); try (iPureIntro); try reflexivity.
            right. repeat split; try reflexivity. }
         iModIntro. iIntros (v1 v2) "#Hv1v2". brel_pures.
         unfold sem_ty_group, sem_ty_option, sem_ty_sum.
         iDestruct "Hv1v2" as (?w1 ?w2) "[#Hnone | #Hsome]".
         (*key receive didnt return successfully*)
          - iDestruct "Hnone" as "[%Hv1 [%Hv2 #Hw1w2]]".
            rewrite -> Hv1. rewrite -> Hv2. unfold sem_ty_unit.
            iDestruct "Hw1w2" as "(%Hw1 & %Hw2)".
            rewrite -> Hw1. rewrite -> Hw2. brel_pures.
            iApply (brel_exhaustion (fill k1'(InjLV #()%V)) (fill k2' (InjLV #()%V))).
            { simpl. auto. set_solver. }
            { simpl. set_solver. }
            { iApply "Hrel". iDestruct "HmQ" as "[Hsome Hnone]". iApply "Hnone".  }
            { iApply "IH". }
          (*key receive returned successfully*)
           - iDestruct "Hsome" as "[%Hv1 [%Hv2 #Hw1w2]]". 
             rewrite -> Hv1. rewrite -> Hv2.
             iDestruct "Hw1w2" as "(%Hw1 & %Hw2)".
             rewrite -> Hw1. rewrite -> Hw2. brel_pures.
             (*iApply (brel_bind'' _ _ (iLblSig_to_iLblThy keytheory) M N 𝟙%T (kysnd_l alice) (kysnd_r alice)).*) 
             set (rightapp := ( match: "rla" with
                                 InjL <> => kont0 (InjLV #()%V)
                               | InjR "x" => kont0 ! #l_sim
                                end)%E).
              iApply (brel_bind'' _ _ (iLblSig_to_iLblThy keytheory)  [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)] ([([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)] ++
                     iLblSig_to_iLblThy (sem_row_union (sem_row_union leaktheory keytheory) L)) 𝟙%T (kysnd_l alice) (kysnd_r alice)).
             { simpl. set_solver. }
             { simpl. set_solver. }
             { iApply to_iThy_le_intro'. unfold M. unfold N. admit. } 
             iApply brel_wand.
             { iDestruct "Hkeysnd" as "#Hkeysnd".
               iSpecialize ("Hkeysnd" $! alice alice).
               iApply "Hkeysnd".
               iExists #()%V, #()%V. unfold alice.
               iRight. repeat (iSplit); try (iPureIntro); try reflexivity. }
             iModIntro. iIntros (v0 v3) "#HRv0v3".
             unfold R. unfold sem_ty_unit.
             iDestruct "HRv0v3" as "(%Hv0 & %Hv3)".
             rewrite -> Hv0. rewrite -> Hv3. brel_pures.
             repeat foldkont.
               iApply (brel_na_inv _ _ alphaN); first set_solver. 
         iFrame "Hinvα".
         iIntros "([(>Hγ & >Hl_m'sim & >Hl_sim & >Hl_auth & >Hl_fchan & >Hl_rchan & >Hl_key) | [>Hd2 | >Hd3 ]] & Hclose)".
                  (* no message has been sent yet by the secure channel*)
                  ++ About brel_load_l.
                     iApply (brel_load_l _ _ _ [CaseCtx _ _] with "Hl_key").
                     iIntros "!> Hl_key". brel_pures.
                     iApply (brel_load_r _ _ _ _ [CaseCtx _ _] with "Hl_m'sim").
                     iIntros "Hl_m'sim". brel_pures. simpl.
                       iApply brel_na_close. iFrame.
           iSplitL.
           { iModIntro. iLeft. iFrame. }
                     
                      iApply (brel_exhaustion (fill k1'(InjLV #()%V)) (fill k2' (InjLV #()%V))).
                               { simpl. auto. admit. }
                               { simpl. set_solver. }
                               { iApply "Hrel". iDestruct "HmQ" as "[Hsome Hnone]". iApply "Hnone".  }
                               { iApply "IH". }
                               (* a message has been sent by both the secure channel and the authenticated channel *)
                ++ unfold d2.
                   iDestruct "Hd2" as (?m ?n) "(Hγ & (Hl_m'sim & (Hl_sim & (Hl_auth & (Hl_fchan & (Hl_rchan & Hl_key))))))".
                    iApply (brel_load_l _ _ _ [CaseCtx _ _] with "Hl_key").
                    iIntros "!> Hl_key". brel_pures.
                    { simpl. set_solver. }
                     iApply (brel_load_r _ _ _ _ [CaseCtx _ _] with "Hl_m'sim").
                    iIntros "Hl_m'sim". brel_pures. simpl.
                    repeat foldkont.
                    iApply fupd_brel.
                    iMod (ghost_map_elem_persist with "Hl_fchan") as "#Hl_fchan".
                    iMod (ghost_map_elem_persist with "Hl_rchan") as "#Hl_rchan".
                    iMod (ghost_map_elem_persist with "Hl_key") as "#Hl_key".
                    iMod (ghost_map_elem_persist with "Hl_m'sim") as "#Hl_m'sim".
                    iMod (ghost_map_elem_persist with "Hl_auth") as "#Hl_auth".
                    iMod (ghost_map_elem_persist with "Hl_sim") as "#Hl_sim".
                    iModIntro.
                    
                    iApply brel_na_close. iFrame.
                    iSplitL.
                    { iModIntro. iRight. iLeft. iFrame "#". }
                     iApply (brel_bind'' _ _  (iLblSig_to_iLblThy leaktheory)  [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)] ([([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)] ++
                                                                                                                                                   iLblSig_to_iLblThy (sem_row_union (sem_row_union leaktheory keytheory) L)) 𝟙%T (arcv_l bob) (arcv_r bob)).
               { simpl. set_solver. }
               { simpl. set_solver. }
               { iApply to_iThy_le_intro'. (*solve_submseteq.*) admit. }
               
               iApply brel_wand.
               { iDestruct "Harcv" as "#Harcv".
                 iSpecialize ("Harcv" $! bob bob).
                 iApply "Harcv".
                 iExists #()%V, #()%V. unfold bob.
                 iLeft. repeat (iSplit); try (iPureIntro); try reflexivity. }
               iModIntro. iIntros (v4 v5) "#Hv4v5".
               iDestruct "Hv4v5" as (?w0 ?w3) "Hv4v5".
               iDestruct "Hv4v5" as "[Hnone | Hsome]".
               +++ (* leakauth doesnt return successfully *)
                 iDestruct "Hnone" as "(%Hv4 & (%Hv5 & (%Hw0 & %Hw3)))".
                 rewrite -> Hv4. rewrite -> Hv5. rewrite -> Hw0. rewrite -> Hw3.
                 brel_pures.
                   iApply (brel_exhaustion (fill k1' (InjLV #()%V)) (fill k2' (InjLV #()%V))).
                          { simpl. set_solver. }
                          { simpl. set_solver. }
                          { iApply "Hrel".  iDestruct "HmQ" as "[Hsome Hnone]". iApply "Hnone". }
                          {iApply "IH". }
               +++ (* leakauth returns successfully with a value *)
                   iDestruct "Hsome" as "(%Hv4 & (%Hv5 & (%Hw0 & %Hw3)))".
                   rewrite -> Hv4. rewrite -> Hv5. rewrite -> Hw0. rewrite -> Hw3.
                   brel_pures.
                              iApply (brel_load_r _ _ _ _ [AppRCtx _] with "Hl_sim").
                              iIntros "Hl_sim'".
                              iApply (brel_load_l _ _ _ [HandleCtx _ _ _ _ _ ; AppRCtx _] with "Hl_auth").
                              iIntros "!>Hl_auth'".
                              iDestruct "Hl_fchan" as "#Hl_fchan".
                              simpl. brel_pures.
                               (*iApply brel_na_close. iFrame.
                               iSplitL; [iModIntro; iRight; iLeft; iFrame; iFrame "#" |].
                               brel_pures.*)
                               iApply G_XOR_CORRECT_l.
                               { admit. }
                               brel_pures.
                               Print ectx.
                               Print frame.
                               iApply (brel_load_r _ _ _ _ [HandleCtx _ _ _ _ _ ; AppRCtx _ ] with "Hl_fchan").
                               iIntros "Hl_fchan'".
                               brel_pures.
                                set (g_enc := (bij_group_xor_sem
                                        (bij_group_xor_sem m (g ^+ n))
                                        (g ^+ n))).
                               iApply (brel_exhaustion (fill k1'((InjRV (vgval g_enc))%V)) (fill k2' ((InjRV (vgval m)))%V)).
                               { simpl. auto. set_solver. }
                                { simpl. set_solver. }
                               { unfold kont0. iApply "Hrel". iDestruct "HmQ" as "[Hsome Hnone]".unfold g_enc. rewrite -> Bij_xor_sem. iApply "Hsome". }
                               { iApply "IH". }
                               (* a message has been sent by the secure channel but not the authenticated channel*)
                           ++ simpl. brel_pures.
                              unfold d3.
                              iDestruct "Hd3" as (?m ?n) "(Hγ & (Hl_m'sim & (Hl_sim & (Hl_auth & (Hl_fchan & (Hl_rchan & Hl_key))))))". 
                               iApply (brel_load_l _ _ _ [CaseCtx _ _] with "Hl_key").
                               iIntros "!> Hl_key". brel_pures.
                               { simpl. set_solver. }
                        iApply (brel_load_r _ _ _ _ [CaseCtx _ _] with "Hl_m'sim").
                               iIntros "Hl_m'sim". brel_pures. simpl.
                               repeat foldkont.
                               iApply fupd_brel.
                               iMod (ghost_map_elem_persist with "Hl_fchan") as "#Hl_fchan".
                               iMod (ghost_map_elem_persist with "Hl_rchan") as "#Hl_rchan".
                              iMod (ghost_map_elem_persist with "Hl_key") as "#Hl_key".
                              iMod (ghost_map_elem_persist with "Hl_m'sim") as "#Hl_m'sim".
                              iModIntro.
                    
                       iApply brel_na_close. iFrame.
           iSplitL.
           { iModIntro. iRight. iRight. iFrame "#". iFrame. }
           iApply (brel_bind'' _ _  (iLblSig_to_iLblThy leaktheory)  [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)] ([([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)] ++
                                                                                                                                                   iLblSig_to_iLblThy (sem_row_union (sem_row_union leaktheory keytheory) L)) 𝟙%T (arcv_l bob) (arcv_r bob)).
               { simpl. set_solver. }
               { simpl. set_solver. }
               { iApply to_iThy_le_intro'. (*solve_submseteq.*) admit. }
               
               iApply brel_wand.
               { iDestruct "Harcv" as "#Harcv".
                 iSpecialize ("Harcv" $! bob bob).
                 iApply "Harcv".
                 iExists #()%V, #()%V. unfold bob.
                 iLeft. repeat (iSplit); try (iPureIntro); try reflexivity. }
               iModIntro. iIntros (v4 v5) "#Hv4v5".
               iDestruct "Hv4v5" as (?w0 ?w3) "Hv4v5".
               iDestruct "Hv4v5" as "[Hnone | Hsome]".
               (* leakauth doesnt return successfully *)
               +++ iDestruct "Hnone" as "(%Hv4 & (%Hv5 & (%Hw0 & %Hw3)))".
                 rewrite -> Hv4. rewrite -> Hv5. rewrite -> Hw0. rewrite -> Hw3.
                 brel_pures.
                   iApply (brel_exhaustion (fill k1' (InjLV #()%V)) (fill k2' (InjLV #()%V))).
                          { simpl. set_solver. }
                          { simpl. set_solver. }
                          { iApply "Hrel".  iDestruct "HmQ" as "[Hsome Hnone]". iApply "Hnone". }
                          {iApply "IH". }
              (* leakauth returns successfully with a value *)
               +++ iDestruct "Hsome" as "(%Hv4 & (%Hv5 & (%Hw0 & %Hw3)))".
                  rewrite -> Hv4. rewrite -> Hv5. rewrite -> Hw0. rewrite -> Hw3.
                  brel_pures.
                           (*another case analysis by opening the invariant again, since we need access to the pointers l_sim and l_auth *)
                            iApply (brel_na_inv _ _ alphaN); first set_solver. 
                            iFrame "Hinvα".
                            iIntros "([(>Hγ & >Hl_m'sim' & >Hl_sim & >Hl_auth & >Hl_fchan' & >Hl_rchan' & >Hl_key') | [>Hd2 | >Hd3 ]] & Hclose)".
                            (*contradiction branch since we already know that a message has been sent by the secure channel *)
                           -- admit.
                            (*the next two brances will move the proof forward with a case analysis on l_auth and l_sim having been set or not *)
                           -- unfold d2. 
                              iDestruct "Hd2" as (?m ?n) "(Hγ & (Hl_m'sim' & (Hl_sim & (Hl_auth & (Hl_fchan' & (Hl_rchan' & Hl_key'))))))".
                              iApply (brel_load_r _ _ _ _ [AppRCtx _] with "Hl_sim").
                              iIntros "Hl_sim".
                              iApply (brel_load_l _ _ _ [HandleCtx _ _ _ _ _ ; AppRCtx _] with "Hl_auth").
                              iIntros "!> Hl_auth".
                              iApply fupd_brel.
                              iMod (ghost_map_elem_persist with "Hl_fchan'") as "#Hl_fchan'".
                              iMod (ghost_map_elem_persist with "Hl_rchan'") as "#Hl_rchan'".
                              iMod (ghost_map_elem_persist with "Hl_key'") as "#Hl_key'".
                              iMod (ghost_map_elem_persist with "Hl_m'sim'") as "#Hl_m'sim'".
                              iMod (ghost_map_elem_persist with "Hl_auth") as "#Hl_auth".
                              iMod (ghost_map_elem_persist with "Hl_sim") as "#Hl_sim".
                              iModIntro.
                    
                       iApply brel_na_close. iFrame.
           iSplitL.
           { iModIntro. iRight. iLeft. iFrame "#". }
                              simpl. brel_pures.
                               (*iApply brel_na_close. iFrame.
                               iSplitL; [iModIntro; iRight; iLeft; iFrame; iFrame "#" |].
                               brel_pures.*)
                               iApply G_XOR_CORRECT_l.
                               { admit. }
                               brel_pures.
                               Print ectx.
                               Print frame.
                               iApply (brel_load_r _ _ _ _ [HandleCtx _ _ _ _ _ ; AppRCtx _ ] with "Hl_fchan").
                               iIntros "Hl_fchan''".
                               brel_pures.
                                set (g_enc := (bij_group_xor_sem
                                        (bij_group_xor_sem m0 (g ^+ n0))
                                        (g ^+ n))).
                               iApply (brel_exhaustion (fill k1'((InjRV (vgval g_enc))%V)) (fill k2' ((InjRV (vgval m)))%V)).
                               { simpl. auto. set_solver. }
                                { simpl. set_solver. }
                                { unfold kont0. iApply "Hrel". iDestruct "HmQ" as "[Hsome Hnone]".
                                   unfold g_enc.
                                  iCombine "Hl_fchan Hl_fchan'" gives %[Hval Hval2].
                                  inversion Hval2. apply vgval_inj in H1. rewrite -> H1.
                                  iCombine "Hl_m'sim Hl_m'sim'" gives %[Hsim Hsim2]. clear Hval Hsim.
                                  inversion Hsim2. specialize (Hf m0). destruct Hf as [Hfinj Hfsurj].
                                  apply Nat2Z.inj in H2.
                                  apply (@inj _ _ eq eq (f m0) Hfinj n n0) in H2. rewrite -> H2.
                                  rewrite -> Bij_xor_sem. iApply "Hsome". }
                               { iApply "IH". }
                           -- unfold d3.
                              iDestruct "Hd3" as (?m ?n) "(Hγ & (Hl_m'sim' & (Hl_sim & (Hl_auth & (Hl_fchan' & (Hl_rchan' & Hl_key'))))))".
                               iApply (brel_load_r _ _ _ _ [AppRCtx _] with "Hl_sim").
                              iIntros "Hl_sim".
                              iApply (brel_load_l _ _ _ [HandleCtx _ _ _ _ _ ; AppRCtx _] with "Hl_auth").
                              iIntros "!> Hl_auth".
                                 iApply fupd_brel.
           iMod (ghost_map_elem_persist with "Hl_fchan'") as "#Hl_fchan'".
           iMod (ghost_map_elem_persist with "Hl_rchan'") as "#Hl_rchan'".
           iMod (ghost_map_elem_persist with "Hl_key'") as "#Hl_key'".
           iMod (ghost_map_elem_persist with "Hl_m'sim'") as "#Hl_m'sim'".
           iModIntro.
                    
                       iApply brel_na_close. iFrame.
           iSplitL.
           { iModIntro. iRight. iRight. iFrame "#". iFrame. }
           simpl. brel_pures.
            iApply (brel_exhaustion (fill k1' (InjLV #()%V)) (fill k2' (InjLV #()%V))).
                          { simpl. set_solver. }
                          { simpl. set_solver. }
                          { iApply "Hrel".  iDestruct "HmQ" as "[Hsome Hnone]". iApply "Hnone". }
                          { iApply "IH". }
Admitted.
 

Lemma R_CHAN_CHAN_SIM_F_CHAN :
  ⊢ sem_val_typed (R_CHAN)%V (λ: "f", CHAN_SIM_lazy (F_CHAN "f"))%V
      (∀ᵣ θ__L ,(∀ᵣ θₕ, (((𝔾 -{ θₕ }->  𝟙) × (𝟙 -{ θₕ }-> (Option  𝔾))) -{ sem_row_union  θₕ θ__L }-∘ 𝟙)) ⊸ (*type of client*)
      (∀ᵣ θ₁, ∀ᵣ θ₂,  (((𝔾 × (𝟙 + 𝟙)) -{ θ₁ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ₁ }-> Option 𝟙)) ⊸ (((𝟙 + 𝟙) -{ θ₂ }-> 𝟙) × (𝟙 + 𝟙) -{ θ₂ }-> Option 𝟙) -{ sem_row_union (sem_row_union θ₁ θ₂) θ__L }-∘ 𝟙))%T.
Proof using G inG0 inG1 inG2.   
  iModIntro. iIntros (L).
  iIntros (f1 f2) "Hrelf1f2".
  brel_pures'.
  simpl.
  assert (to_iThyIfMono OS [] = []) as <- by done.
  iApply (brel_mono OS with "[][Hrelf1f2]");
  [iApply to_iThy_le_refl|simpl|simpl].
  +  iApply (SEM_R_CHAN_SIM _ _ L).
     iApply "Hrelf1f2".
  +  iIntros (??) "$". 
Qed.
   

(*top level statements for the secure channel *)
(*----------------------------------------------------------------*)
Lemma R_I_SCHAN :
  ⊢ sem_typed [] R_CHAN (λ: "f", (CHAN_SIM_lazy (F_CHAN "f")))%V ⊥
       (∀ᵣ θ__L ,(∀ᵣ θₕ, (((𝔾 -{ θₕ }-> 𝟙) × (𝟙 -{ θₕ }-> (Option  𝔾))) -{ sem_row_union  θₕ θ__L }-∘ 𝟙)) ⊸ (*type of client*)
                 (∀ᵣ θ₁, ∀ᵣ θ₂,  (((𝔾 × (𝟙 + 𝟙)) -{ θ₁ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ₁ }-> Option 𝟙)) ⊸ (((𝟙 + 𝟙) -{ θ₂ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ₂ }-> Option 𝟙)) -{ sem_row_union (sem_row_union θ₁ θ₂) θ__L }-∘ 𝟙))%T [].
Proof using G inG0 inG1 inG2 klk1 klk2 lka1 lka2. 
  iIntros (vs) "!# H". simpl.
  iApply brel_value.
  iIntros "$ !>".
  iSplit; try (done).  
  iPoseProof R_CHAN_CHAN_SIM_F_CHAN as "Hsemty".
  rewrite /sem_val_typed /=.
  iDestruct "Hsemty" as "#Hsemty".
  iApply "Hsemty".
Qed.
 

  
End schan_security.

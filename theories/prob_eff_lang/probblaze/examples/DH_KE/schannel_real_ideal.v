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
From clutch.prob_eff_lang.probblaze Require Import def_schannel.
From clutch.prob_eff_lang.probblaze Require Import sem_types sem_row sem_sig sem_judgement sem_def.
From clutch.prob_eff_lang.probblaze Require Import p_composition.


Import fingroup.

Import fingroup.fingroup.

(*Import valgroup_notation.*)
Import valgroup_tactics.

Section s_channel_verification.
  Context `{probblazeRGS Σ}.
  Context (channel leaksec getKey1 getKey2 leakauth1 leakauth2 keyleak1 keyleak2 schannel1 schannel2: label).
  Context {vg: val_group}.
  Context {cg: clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.


  Definition atokN' : namespace := nroot .@ "atokN1".
  Definition btokN' : namespace := nroot .@ "btokN1".

  (*Theories for the interaction of the secure channel with the environment*)
  (*-------------------------------------------------------------*)

  (* Theories for the authenticated channel leaks *)
  (*-------------------------------------------------------------*)
   (* Send TO Bob*)
   Program Definition LASendBob : iThy Σ :=
  λ e1 e2, (λne Q,
              ∃ m1 m2 : val,
                ⌜e1 = (do: leakauth1 (SendV (m1, bob)))⌝%E ∗ 
                           ⌜ e2 = do: leakauth2 (SendV (m2, bob)) ⌝%E ∗
                                      □ Q (Val #()%V) (Val #()%V))%I.
  Next Obligation. solve_proper. Qed.
  (* Send TO Alice*)
  Program Definition LASendAlice : iThy Σ :=
  λ e1 e2, (λne Q,
              ∃ m1 m2 : val,
                ⌜e1 = (do: leakauth1 (SendV (m1, alice)))⌝%E ∗ 
                           ⌜ e2 = do: leakauth2 (SendV (m2, alice)) ⌝%E ∗
                                      □ Q (Val #()%V) (Val #()%V))%I.
  Next Obligation. solve_proper. Qed.
  (*Recv FROM bob*) 
  Program Definition LARecvBob : iThy Σ :=
   λ e1 e2, (λne Q,
                ⌜ e1 = do: leakauth1 (RecvV bob) ⌝%E ∗
                ⌜ e2 = do: leakauth2 (RecvV bob) ⌝%E ∗
                □ ((∀ b1 b2 : nat, Q (SOMEV #b1) (SOMEV #b2)) ∧ Q NONEV NONEV)
             )%I.
  Next Obligation. solve_proper. Qed.
 (* Recv FROM Alice *)
  Program Definition LARecvAlice : iThy Σ :=
     λ e1 e2, (λne Q,
                ⌜ e1 = do: leakauth1 (RecvV alice) ⌝%E ∗
                ⌜ e2 = do: leakauth2 (RecvV alice) ⌝%E ∗
                □ ((∀ b1 b2 : nat, Q (SOMEV #b1) (SOMEV #b2)) ∧ Q NONEV NONEV)
             )%I.
  Next Obligation. solve_proper. Qed.

  
  (* Theories for the key exchange leaks*)
  (*---------------------------------------------------------*)
  (*Send TO Alice*)
  Program Definition KLeakSendAlice : iThy Σ :=
    λ e1 e2, (λne Q,
                ⌜ e1 = do: keyleak1 (SendV alice) ⌝%E ∗
                           ⌜ e2 = do: keyleak2 (SendV alice) ⌝%E ∗
                                      □ Q (Val #()%V) (Val #()%V))%I.
  Next Obligation. solve_proper. Qed.
  (* Send TO Bob *)
  Program Definition KLeakSendBob : iThy Σ :=
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
   Program Definition KLeakRecvAlice : iThy Σ :=
    λ e1 e2, (λne Q,
                ⌜ e1 = do: keyleak1 (RecvV alice) ⌝%E ∗
                           ⌜ e2 = do: keyleak2 (RecvV alice) ⌝%E ∗
                                      □ (Q NONEV NONEV ∗ Q (SOMEV #0) (SOMEV #0)))%I.
  Next Obligation. solve_proper. Qed.
 (* Recv FROM Bob *)
  Program Definition KLeakRecvBob : iThy Σ :=
    λ e1 e2, (λne Q,
                ⌜ e1 = do: keyleak1 (RecvV bob) ⌝%E ∗
                           ⌜ e2 = do: keyleak2 (RecvV bob) ⌝%E ∗
                                      □ (Q NONEV NONEV ∗ Q (SOMEV #0) (SOMEV #0)))%I.
  Next Obligation. solve_proper. Qed.
  
  (* Theories relating the authenticated channel with the secure channel leak*)
  (*-----------------------------------------------------------------------------*)
  Program Definition SendALSAlice : iThy Σ :=
    λ e1 e2, (λne Q,
                ∃ m : val,
                  (⌜ e1 = do: channel (SendV (m, alice)) ⌝%E ∗
                  ⌜  e2 = do: leaksec (SendV alice)⌝%E) ∗ □ (Q (Val #()%V) (Val #()%V)))%I.
  Next Obligation. solve_proper. Qed.

  Program Definition SendALSBob : iThy Σ :=
    λ e1 e2, (λne Q,
                ∃ m : val,
                  (⌜ e1 = do: channel (SendV (m, bob)) ⌝%E ∗
                  ⌜  e2 = do: leaksec (SendV bob)⌝%E) ∗ □ (Q (Val #()%V) (Val #()%V)))%I.
  Next Obligation. solve_proper. Qed. 

  Program Definition RecvALSAlice : iThy Σ :=
    λ e1 e2, (λne Q,
                  (⌜ e1 = do: channel (RecvV alice) ⌝%E ∗
                  ⌜  e2 = do: leaksec (RecvV alice)⌝%E) ∗ □ (Q (Val #()%V) (Val #()%V)))%I.
  Next Obligation. solve_proper. Qed.    

  Program Definition RecvALSBob : iThy Σ := 
    λ e1 e2, (λne Q,
                  (⌜ e1 = do: channel (RecvV bob) ⌝%E ∗
                  ⌜  e2 = do: leaksec (RecvV bob)⌝%E) ∗ □ (Q (Val #()%V) (Val #()%V)))%I.
  Next Obligation. solve_proper. Qed.  

  (*Program Definition ChanLeakSec : iThy Σ := iThySum (iThySum SendALSAlice SendALSBob) (iThySum RecvALSAlice RecvALSBob). *)
(*  Program Definition ChanLeakSec : iThy Σ := (iThySum SendALSAlice RecvALSBob).
  
  Definition LblEnvSec := [ ([channel; getKey1; schannel1], [leaksec; schannel2; getKey2], iThyBot)    ;
                            ([keyleak1], [keyleak2],iThySum (iThySum KLeakSendAlice KLeakRecvAlice) (iThySum KLeakSendBob KLeakRecvBob));
                            ([leakauth1], [leakauth2], iThySum (iThySum LASendAlice LASendBob) (iThySum LARecvAlice LARecvBob))].

   Definition LblEnvSec' := [ ([leaksec; getKey1; schannel1], [channel; schannel2; getKey2], iThyBot)    ;
                            ([keyleak1], [keyleak2],iThySum (iThySum KLeakSendAlice KLeakRecvAlice) (iThySum KLeakSendBob KLeakRecvAlice));
                            ([leakauth1], [leakauth2], iThySum (iThySum LASendAlice LASendBob) (iThySum LARecvAlice LARecvBob))].
*)

  (*Theories relating the secure channel effects for the client*)
  (*---------------------------------------------------------*)
  Program Definition SendSecBob : iThy Σ :=
     λ e1 e2, (λne Q,
                ∃ m m': val, 
                            (⌜ e1 = do: schannel1 (SendV (m, alice)) ⌝%E ∗
                             ⌜ e2 = do: schannel2 (SendV (m', alice)) ⌝%E)  ∗ 
                            □ (Q (Val #()%V) (Val #()%V))
             )%I.
  Next Obligation. solve_proper. Qed.
  
  
   (*Program Definition SendSecBobImpl γtok γfrac γsec ℓ : iThy Σ :=
     λ e1 e2, (λne Q,
                ∃ m m': val, ((|={⊤, ⊤ ∖ ↑ℓ }=> ((own γfrac DfracDiscarded -∗ (|={⊤ ∖ ↑ℓ, ⊤}=> token γtok ∗ own γsec (to_dfrac_agree DfracDiscarded m) ∗ ⌜m = m'⌝)) ∨ |={⊤ ∖ ↑ℓ , ⊤}=> own γfrac DfracDiscarded)) ∗  
                            (⌜ e1 = do: schannel1 (SendV (m, alice)) ⌝%E ∗
                             ⌜ e2 = do: schannel2 (SendV (m', alice)) ⌝%E)  ∗ 
                            □ (Q (Val #()%V) (Val #()%V)))
             )%I.
  Next Obligation. solve_proper. Qed.*)
  
  Program Definition SendSecAlice : iThy Σ :=
     λ e1 e2, (λne Q,
                ∃ m m' : val,   
                             (⌜ e1 = do: schannel1 (SendV (#0, bob)) ⌝%E ∗
                              ⌜ e2 = do: schannel2 (SendV (#0, bob)) ⌝%E)  ∗ 
                             □ (Q (Val #()%V) (Val #()%V))
             )%I.
  Next Obligation. solve_proper. Qed.

   (* Program Definition SendSecAliceImpl γtok γfrac γsec ℓ : iThy Σ :=
     λ e1 e2, (λne Q,
                ∃ m m' : val, ((|={⊤, ⊤ ∖ ↑ℓ }=> ((own γfrac DfracDiscarded -∗ (|={⊤ ∖ ↑ℓ, ⊤}=> token γtok ∗ own γsec (to_dfrac_agree DfracDiscarded m) ∗ ⌜m = m'⌝)) ∨ |={⊤ ∖ ↑ℓ , ⊤}=> own γfrac DfracDiscarded)) ∗  
                             (⌜ e1 = do: schannel1 (SendV (m, bob)) ⌝%E ∗
                              ⌜ e2 = do: schannel2 (SendV (m', bob)) ⌝%E)  ∗ 
                             □ (Q (Val #()%V) (Val #()%V)))
             )%I.
  Next Obligation. solve_proper. Qed.*)
  
  Program Definition RecvSecBob : iThy Σ :=
     λ e1 e2, (λne Q,
                ⌜ e1 = do: schannel1 (RecvV bob) ⌝%E ∗
                ⌜ e2 = do: schannel2 (RecvV bob) ⌝%E ∗
                □ (Q NONEV NONEV)
             )%I.
  Next Obligation. solve_proper. Qed. 
    
  Program Definition RecvSecAlice : iThy Σ :=
     λ e1 e2, (λne Q,
                 ⌜ e1 = do: schannel1 (RecvV alice) ⌝%E ∗
                 ⌜ e2 = do: schannel2 (RecvV alice) ⌝%E ∗
                 □ (Q NONEV NONEV )
             )%I.
  Next Obligation. solve_proper. Qed.
  
 (* Definition SecChannelThy : iThy Σ :=
  (iThySum (SendSecAlice) (RecvSecBob)). *) 
   (*iThySum (iThySum (SendSecAlice) (RecvSecBob)) (iThySum (SendSecBob) (RecvSecAlice)).*)

  (*Program Definition SendAuthBobImpl γtok γfrac γauth ι : iThy Σ :=
    λ e1 e2, (λne Q,
                ∃ m m': val, ((|={⊤, ⊤ ∖ ↑ι }=> ((own γfrac DfracDiscarded -∗ (|={⊤ ∖ ↑ι, ⊤}=> token γtok ∗ own γauth (to_dfrac_agree DfracDiscarded m) ∗ ⌜m = m'⌝)) ∨ |={⊤ ∖ ↑ι , ⊤}=> own γfrac DfracDiscarded)) ∗  
                            (⌜ e1 = do: channel1 (SendV (m, alice)) ⌝%E ∗
                             ⌜ e2 = do: channel2 (SendV (m', alice)) ⌝%E)  ∗ 
                            □ (Q (Val #()%V) (Val #()%V)))
             )%I.
  Next Obligation. solve_proper. Qed.

  Program Definition RecvAuthAliceImpl γauth : iThy Σ :=
    λ e1 e2, (λne Q,
                 ⌜ e1 = do: channel1 (RecvV alice) ⌝%E ∗
                 ⌜ e2 = do: channel2 (RecvV alice) ⌝%E ∗
                 □ (Q NONEV NONEV ∗ (∀ m, own γauth (to_dfrac_agree DfracDiscarded m) -∗ Q (SOMEV m) (SOMEV m)))
             )%I.
  Next Obligation. solve_proper. Qed.

   Program Definition SendAuthAliceImpl γtok γfrac γauth ι : iThy Σ :=
    λ e1 e2, (λne Q,
                ∃ m m' : val, ((|={⊤, ⊤ ∖ ↑ι }=> ((own γfrac DfracDiscarded -∗ (|={⊤ ∖ ↑ι, ⊤}=> token γtok ∗ own γauth (to_dfrac_agree DfracDiscarded m) ∗ ⌜m = m'⌝)) ∨ |={⊤ ∖ ↑ι , ⊤}=> own γfrac DfracDiscarded)) ∗  
                             (⌜ e1 = do: channel1 (SendV (m, bob)) ⌝%E ∗
                              ⌜ e2 = do: channel2 (SendV (m', bob)) ⌝%E)  ∗ 
                             □ (Q (Val #()%V) (Val #()%V)))
             )%I.
   Next Obligation. solve_proper. Qed.


   Program Definition RecvAuthBobImpl γauth : iThy Σ :=
    λ e1 e2, (λne Q,
                ⌜ e1 = do: channel1 (RecvV bob) ⌝%E ∗
                ⌜ e2 = do: channel2 (RecvV bob) ⌝%E ∗
                □ (Q NONEV NONEV ∗ (∀ m, own γauth (to_dfrac_agree DfracDiscarded m) -∗ Q (SOMEV m) (SOMEV m)))
             )%I.
  Next Obligation. solve_proper. Qed. 

   
  Definition AuthChannelThy γtoka atokN γtokb btokN γfraca γfracb γautha γauthb : iThy Σ :=
    (iThySum (iThySum (SendAuthAliceImpl γtoka γfraca γautha atokN) (RecvAuthBobImpl γauthb))
       (iThySum (SendAuthBobImpl γtokb γfracb γauthb btokN) (RecvAuthAliceImpl γautha))).
  *)
  (*Definition ClientThy γtoka atokN γfraca γseca γsecb γtoka1 γtokb1 γfraca1 γfracb1 γautha γauthb atokN1 btokN1  : iThy Σ :=
    (iThySum (SecChannelThy γtoka atokN γfraca γseca γsecb) (AuthChannelThy γtoka1 atokN1 γtokb1 btokN1 γfraca1 γfracb1 γautha
    γauthb)).
  
  Definition LblClients γtoka atokN γfraca γseca γsecb γtoka1 γtokb1 γfraca1 γfracb1 γautha γauthb atokN1 btokN1 : iLblThy Σ :=
    [([schannel1; getKey1; channel1],[schannel2; channel2], ClientThy γtoka atokN γfraca γseca γsecb γtoka1 γtokb1 γfraca1 γfracb1 γautha γauthb atokN1 btokN1)].*)
 (* Definition GetKey1bot : iThy Σ :=
    λ e1 ex, (λne True, ⌜ e1 = do: getKey1 (ex) ⌝%E ∗ False)%I.

    
  Definition LblClients : iLblThy Σ :=
    [(([channel; getKey1; schannel1],[leaksec; schannel2; getKey2], (SecChannelThy)));
     ([keyleak1], [keyleak2],
         iThySum (iThySum KLeakSendAlice KLeakRecvAlice) (iThySum KLeakSendBob KLeakRecvBob));
         ([leakauth1], [leakauth2], iThySum (iThySum LASendAlice LASendBob) (iThySum LARecvAlice LARecvBob))].
  
  Definition LblClients' : iLblThy Σ :=
    [([schannel1; getKey1; leaksec],[schannel2; getKey2; channel], (SecChannelThy));   
     ([keyleak1], [keyleak2],
         iThySum (iThySum KLeakSendAlice KLeakRecvAlice) (iThySum KLeakSendBob KLeakRecvBob));
         ([leakauth1], [leakauth2], iThySum (iThySum LASendAlice LASendBob) (iThySum LARecvAlice LARecvBob))].*)
  (*[([schannel1; getKey1],[schannel2], (iThySum (GetKey1bot) (SecChannelThy)))].*)


  (* semantic types*)
  (*----------------------------------------------------------------------------*)

   Definition sem_ty_group : sem_ty Σ := (λ v1 v2, ∃ g : vgG, ⌜ v1 = g ⌝ ∗ ⌜ v2 = g ⌝)%I.
  Notation "'𝔾'" := sem_ty_group. 
  (*Program Definition bot_mono := {| pmono_prot_car := iThyBot ; pmono_prot_prop := _ |}.
  Next Obligation. solve_proper. Defined.
 
  Definition thy_sec_chan (l1 l2 : label) := @SemSig Σ bot_mono (l1,l2).
  Program Definition thy_sec_row (channel leaksec getKey1 getKey2 schannel1 schannel2 : label) :=
    SemRow [([channel; getKey1; schannel1] , [leaksec; getKey2; schannel2] , bot_mono)] _.*)
  Program Definition keyleak_mono := {| pmono_prot_car := iThySum (iThySum KLeakSendAlice KLeakRecvAlice) (iThySum KLeakSendBob KLeakRecvBob) ; pmono_prot_prop := _|}.
  Next Obligation.
   iIntros (??).
   iIntros (??) "#HΦ [[HS | HR] | [HS | HR]]".
   1: iLeft; iLeft. 2: iLeft; iRight. 3: iRight; iLeft. 4: iRight; iRight.
   1,3 : iDestruct "HS" as (??) "#H"; simpl; iSplit; first done; iSplit; first done; iModIntro; by iApply "HΦ".
   all: iDestruct "HR" as (??) "(#H1 & #H2)"; simpl; iSplit; first done; iSplit; first done; iModIntro; iSplitL " "; iApply "HΦ"; try (iApply "H1"); try (iApply "H2").
  Qed.
  Definition keyleak := @SemSig Σ keyleak_mono (keyleak1, keyleak2).
  Lemma keyleak_pers_mono_row : ⊢ pers_mono_row (iLblSig_to_iLblThy [([channel; getKey1; schannel1; keyleak1] , [leaksec; getKey2; schannel2; keyleak2] , keyleak)]).
  Proof. Admitted.
  Definition keyleak_row := SemRow [([channel; getKey1; schannel1; keyleak1] , [leaksec; getKey2; schannel2; keyleak2] , keyleak)] keyleak_pers_mono_row.
 
  Program Definition leakauth_mono := {| pmono_prot_car := iThySum (iThySum LASendAlice LASendBob) (iThySum LARecvAlice LARecvBob) ; pmono_prot_prop := _ |}.
  Next Obligation.
    iIntros (????) "#HΦ [[HS | HS] | [HR | HR]]".
    1: iLeft; iLeft. 2: iLeft; iRight. 3: iRight; iLeft. 4: iRight; iRight.
    1,2 : iDestruct "HS" as (??) "(#H1 & #H2 & #H3)"; simpl; iExists m1, m2; iSplit; first done; iSplit; first done;
                                                                         iModIntro; by iApply "HΦ". 
    all : iDestruct "HR" as "(#H1 & #H2 & #H3)"; simpl; iSplit; first done; iSplit; first done; iModIntro;
    iDestruct "H3" as "[Hs Hn]"; iSplitL " "; try (iIntros (??)); iApply "HΦ"; try (iApply "Hs"); try (iApply "Hn").
  Qed.

  Definition leakauth := @SemSig Σ leakauth_mono (leakauth1, leakauth2).
  Lemma leakauth_pers_mono_row : ⊢ pers_mono_row (iLblSig_to_iLblThy [([leakauth1], [leakauth2], leakauth)]).
  Proof. Admitted.
  Definition leakauth_row := SemRow [([leakauth1],[leakauth2] , leakauth)] leakauth_pers_mono_row.
  Program Definition envsec_row :=
    sem_row_union keyleak_row leakauth_row.

  Definition REAL_CHAN : val :=
    λ: "f" "doLeakSend" "doLeakRecv" "doKeyLeak" "unit",
      left_composition F_OAUTH F_KE_L "f" "doLeakSend" "doLeakRecv" "doKeyLeak" "unit".
  
(*Verification of F_OAUTH[F_KE_L[CHAN[]]] ≤ CHAN_SIM[F_CHAN[]]*)
(*----------------------------------------------------------*)
 (*Lemma F_KE_CHAN_SIM (f1 f2 : val) (L : sem_row Σ) :
    sem_val_typed f1 f2 ((∀ᵣ θₕ, (sem_ty_sum 𝟙 𝟙) -{ θₕ }-> (Option  𝔾) -{ sem_row_union  θₕ L }-> 𝟙))%T -∗ 
    BREL F_KE_L (F_OAUTH (CHAN f1))
      ≤ CHAN_SIM (F_CHAN f2) <|⊥|> {{λ v1 v2,
                                       ∀ (leakauth1 leakauth2 keyleak1 keyleak2 : label),
                                       BREL v1 (λ: "m", do: leakauth1 (Send "m"))%V (λ: "m", do: leakauth1 (Recv "m"))%V (λ: "m", do: keyleak1 "m")%V ≤ v2 (λ: "m", do: keyleak2 "m")%V (λ: "m", do: leakauth2 (Send "m"))%V (λ: "m", do: leakauth2 (Recv "m"))%V <| (iLblSig_to_iLblThy envsec_row) ++ (iLblSig_to_iLblThy L) |> {{ (λ w1 w2, 𝟙%T w1 w2)}}}}. *)
Lemma F_KE_CHAN_SIM (f1 f2 : val) (L : sem_row Σ) :
    sem_val_typed f1 f2 ((∀ᵣ θₕ, (sem_ty_sum 𝟙 𝟙) -{ θₕ }-> (Option  𝔾) -{ sem_row_union  θₕ L }-> 𝟙))%T -∗ 
    BREL REAL_CHAN (CHAN f1)
      ≤ CHAN_SIM (F_CHAN f2) <|⊥|> {{λ v1 v2,
                                       ∀ (leakauth1 leakauth2 keyleak1 keyleak2 : label),
                                       BREL v1 (λ: "m", do: leakauth1 (Send "m"))%V (λ: "m", do: leakauth1 (Recv "m"))%V (λ: "m", do: keyleak1 "m")%V (λ: <>, #())%V ≤ v2 (λ: "m", do: keyleak2 "m")%V (λ: "m", do: leakauth2 (Send "m"))%V (λ: "m", do: leakauth2 (Recv "m"))%V <| (iLblSig_to_iLblThy envsec_row) ++ (iLblSig_to_iLblThy L) |> {{ (λ w1 w2, 𝟙%T w1 w2)}}}}.
Proof with (repeat foldkont) using G.
  iIntros "Hrelf1f2".
  repeat simpl.
  (*unfold CHAN_SIM, F_OAUTH.*)
  unfold REAL_CHAN, CHAN, F_CHAN, CHAN_SIM, F_KE_L, F_OAUTH.
  
  repeat simpl. brel_pures. iModIntro. iIntros (????).
  brel_pures.
  iApply brel_alloctape_r. iIntros (α) "Hα". brel_pures_r. 
  iApply brel_alloc_r. iIntros (l_sim) "Hl_sim". brel_pures_r.
  iApply brel_couple_UT. 1: auto.
  simpl. iFrame "Hα". iSplit => //.
  iIntros (n ?) "!> Hα". brel_pures.
  (*rewrite subst_is_closed_empty; try done.*)
  brel_exp_l. brel_pures.
  iApply brel_effect_l. iIntros (getKey') "!> HgK !>". brel_pures_l.
  iApply brel_effect_r. iIntros (leaksec') "Hleaksec !>". brel_pures'.
  iApply brel_alloc_l. iIntros (l_auth) "!>Hl_auth". brel_pures_l.
  brel_pures'.
  iApply brel_effect_l. iIntros (channel') "!> Hchannel !>". brel_pures_l.
  iApply brel_alloc_l. iIntros (l_rchan) "!>Hlrchan". brel_pures_l.
  iApply brel_alloc_r. iIntros (l_fchan) "Hlfchan". brel_pures_r.
  iApply brel_effect_r. iIntros (schannel_r) "Hschannel_r !>". brel_pures_r.
  iApply brel_effect_l. iIntros (schannel_l) "!> Hschannel_l !>". brel_pures_l.
  brel_pures'.
  iApply brel_effect_r. iIntros (leaksec') "Hleaksec !>". brel_pures'.
  (*repeat (rewrite subst_is_closed_empty; try done).*)
  iApply brel_couple_UT. 1: auto.
  simpl. iFrame "Hα". iSplit => //.
  iIntros (n ?) "!> Hα". brel_pures.
  (*rewrite subst_is_closed_empty; try done.*)
  brel_exp_l. brel_pures.
  iApply brel_effect_l. iIntros (getKey') "!> HgetKey !>". brel_pures'.
  iApply brel_alloc_l. iIntros (l_rchan) "!>Hlrchan". brel_pures_l.
  (*simpl. repeat (rewrite subst_is_closed_empty; try done).*)
 
  rewrite subst_is_closed_empty; try done.
  set (kl1 :=  (match: "payload" with
         InjL "payload" =>
           let: "dst" := "payload" in
           let: "m" := Fst "dst" in
           let: "dst" := Snd "dst" in
           match: ! #l_rchan with
             InjL <> =>
               #l_rchan <- InjR "m";; 
               let: "key" := do: getKey1 "dst" in
               match: "key" with
                 InjL <> => "k" #()%V
               | InjR "x" =>
                 let: "enc_m" := xor "x" "m" in
                 (do: channel InjL ("enc_m", bob));; "k" #()%V
               end
           | InjR "m" => "k" #()%V
           end
       | InjR "from" =>
         let: "key" := do: getKey1 "from" in
         match: "key" with
           InjL <> => "k" (InjLV #()%V)
         | InjR "key" =>
           let: "r" := do: channel InjR "from" in
           match: "r" with
             InjL <> => "k" (InjLV #()%V)
           | InjR "x" =>
             let: "enc_m" := xor "key" "x" in "k" (InjR "enc_m")
           end
         end
       end)%E).
  set (kl2 := ( match: "p" with
         InjL <> =>
           (do: keyleak1 InjL bob);; 
           let: "r" := do: keyleak1 InjR bob in
           match: "r" with
             InjL <> => "k" (InjLV #()%V)
           | InjR "w" => "k" (InjR (vgval (g ^+ n)))
           end
       | InjR <> =>
         let: "r" := do: keyleak1 InjR alice in
         match: "r" with
           InjL <> => "k" (InjLV #()%V)
         | InjR "w" =>
           (do: keyleak1 InjL alice);; "k" (InjR (vgval (g ^+ n)))
         end
       end)%E).
  set (kl3 := ( match: "payload" with
         InjL "payload" =>
           let: "dst" := "payload" in
           let: "m" := Fst "dst" in
           let: "dst" := Snd "dst" in
           match: ! #l_auth with
             InjL <> => #l_auth <- InjR "m";; (do: leakauth1 InjL ("m", "dst"));; "k" #()%V
           | InjR "message" => "k" #()%V
           end
       | InjR "from" =>
         let: "r" := do: leakauth1 InjR "from" in
         match: "r" with InjL <> => "k" (InjLV #()%V) | InjR "x" => "k" ! #l_auth end
                       end)%E). 
  set (kr1 := ( match: "payload" with
         InjL "payload" =>
           let: "dst" := "payload" in
           let: "m" := Fst "dst" in
           let: "dst" := Snd "dst" in
           match: ! #l_fchan with
             InjL <> =>
               #l_fchan <- InjR "m";; 
               (do: leaksec InjL "dst");; "k" #()%V
           | InjR "x" => "k" #()%V
           end
       | InjR "from" =>
         let: "r" := do: leaksec InjR "from" in
         match: "r" with
           InjL <> => "k" (InjLV #()%V)
         | InjR "x" => "k" (InjR "x")
         end
       end)%E). 
  set (kr2 := ( match: "payload" with
         InjL "payload" =>
           (do: keyleak2 InjL "payload");; 
           let: "r" := do: keyleak2 
                       InjR bob in
           match: "r" with
             InjL <> => "k" (InjLV #()%V)
           | InjR "x" =>
             match: ! #l_sim with
               InjL <> =>
                 let: "m'" := 
                 #()%V;; 
                 rand(#lbl:α) #
                 (S n'') in
                 let: "mA" := 
                 g ^ "m'" in
                 #l_sim <- InjR "m'";; 
                 (do: leakauth2 
                  InjL ("mA", bob));; 
                 "k" #()%V
             | InjR "m" => "k" #()%V
             end
           end
       | InjR "from" =>
         (do: keyleak2 InjL "from");; 
         let: "r" := do: keyleak2 
                     InjR "from" in
         match: "r" with
           InjL <> => "k" (InjLV #()%V)
         | InjR "x" =>
           let: "rla" := do: leakauth2 
                         InjR "from" in
           match: "rla" with
             InjL <> => "k" (InjLV #()%V)
           | InjR "x" => "k" ! #l_sim
           end
         end
       end)%E).
  (*iAssert ( brel ⊤ f1 f2
    (([channel; getKey1; schannel1], [leaksec; schannel2; getKey2], SecChannelThy)
     :: ([keyleak1], [keyleak2],
         iThySum (iThySum KLeakSendAlice KLeakRecvAlice) (iThySum KLeakSendBob KLeakRecvBob))
        :: ([leakauth1], [leakauth2], iThySum (iThySum LASendAlice LASendBob) (iThySum LARecvAlice LARecvBob))
           :: L)
    (λ v1 v2 : val, ⌜v1 = v2⌝%I)) as "Hrelf1f2mono".
  { admit. }*)
   iApply (brel_na_alloc
              (((α ↪ₛN (S n''; [n])) ∗ l_sim ↦ₛ NONEV ∗ l_auth ↦ NONEV)
               ∨ (α ↪ₛ□ (S n''; []) ∗ l_sim ↦ₛ□ SOMEV #n ∗  l_auth ↦□ SOMEV (xor (vgval $ g ^+n)%g #0)))%I
              alphaN).
   iSplitL "Hα Hl_sim Hl_auth"; [iNext; iFrame; iLeft; iFrame|].
   iIntros "#Hinvα".
   iApply (brel_na_alloc
              ((l_fchan ↦ₛ NONEV ∗ l_rchan ↦ NONEV)
               ∨ (l_fchan ↦ₛ□ SOMEV #0 ∗  l_rchan ↦□ SOMEV #0))%I
              betaN).
   iSplitL  "Hlrchan Hlfchan"; [iNext; iFrame; iLeft; iFrame|].
   iIntros "#Hinvβ" .
   iApply ((brel_exhaustion f1 f2 _ _ _ _ _ _ _ _ _) with "[Hrelf1f2]"); try simpl; try auto; try (apply sublist_subseteq); try (apply singleton_sublist_l);
     try (apply list_elem_of_In); try simpl; try auto; try (repeat (eapply sublist_skip)) ; try eapply sublist_nil_l.
   iLöb as "IH".
   iSplit; [iIntros (v1 v2) "%Hv1v2"; iModIntro; brel_pures; iModIntro; done |]. 
   iIntros (?????) "!# %Hk1 %Hk2 HXQ #Hrel".
   iDestruct "HXQ" as "[HSendAlice | HRecvBob]".
   (* Send to Bob*) 
      + iDestruct "HSendAlice" as (?m ?m') "[[%He1 %He2] #HmQ]".         
         rewrite -> He1. rewrite -> He2. brel_pures.
         {  apply -> NeutralEctx_ectx_labels_singleton.
           do 2 (eapply NeutralEctx_label_cons_inv_2 in Hk1). eapply Hk1.}
         {  apply -> NeutralEctx_ectx_labels_singleton.
            eapply NeutralEctx_label_cons_inv_2 in Hk2.
            eapply NeutralEctx_label_cons_inv_1 in Hk2. eapply Hk2. } 
         iApply (brel_na_inv _ _ betaN); first set_solver.
         iFrame "Hinvβ".
         iIntros "([(>Hl_fchan  & >Hl_rchan) | (#>Hl_fchan & #>Hl_rchan)] & Hclose)".
         (* First message to be sent by the secure channel*)
        ++  iApply (brel_load_r _ _ _ _ [HandleCtx _ _ _ _ _ ; CaseCtx _ _] with "Hl_fchan").
             iIntros "Hl_fchan".
             iApply (brel_load_l _ _ _  [HandleCtx Deep MS channel _ _ ; HandleCtx Deep MS getKey1 _ _; CaseCtx _ _] with "Hl_rchan").
             iIntros "!>Hl_rchan". brel_pures.
             simpl. brel_pures. 
             iApply (brel_store_r _ _ _ _ [HandleCtx _ _ _ _ _ ; AppRCtx _] with "Hl_fchan"). iIntros "Hl_fchan".
             simpl.
             brel_pures.
             { simpl. apply not_elem_of_nil. }
             iApply (brel_store_l _ _ _  [HandleCtx _ _ _ _ _ ; HandleCtx _ _ _ _ _ ; AppRCtx _] with "Hl_rchan").
             iIntros "!>Hl_rchan". brel_pures; try (simpl); try (apply not_elem_of_nil).
             iApply fupd_brel.
             iMod (ghost_map_elem_persist with "Hl_fchan") as "#Hl_fchan".
             iMod (ghost_map_elem_persist with "Hl_rchan") as "#Hl_rchan".
             iModIntro.
             iApply brel_na_close. iFrame.
             iSplitL; [iModIntro; iRight; iFrame "#"|].
             set (keytheory := [([keyleak1], [keyleak2],
         iThySum (iThySum KLeakSendAlice KLeakRecvAlice)
           (iThySum KLeakSendBob KLeakRecvBob))]).
            set (M := (([channel; getKey1; schannel1], [leaksec; schannel2; getKey2], iThyBot)
        :: ([leakauth1], [leakauth2],
             iThySum (iThySum LASendAlice LASendBob) (iThySum LARecvAlice LARecvBob)) :: L)).
            set (N := (([channel; getKey1; schannel1], [leaksec; schannel2; getKey2], iThyBot)
     :: ([keyleak1], [keyleak2],
         iThySum (iThySum KLeakSendAlice KLeakRecvAlice)
           (iThySum KLeakSendBob KLeakRecvBob))
        :: ([leakauth1], [leakauth2],
             iThySum (iThySum LASendAlice LASendBob) (iThySum LARecvAlice LARecvBob)) :: L)).
            simpl.
            repeat foldkont.
            simpl.
             set (kontleftbind := (let: "r" := do: keyleak1 InjR bob in
             match: "r" with
               InjL <> => kont (InjLV #()%V)
             | InjR "w" => kont (InjR (vgval (g ^+ n)))
             end)%E).
           set (kontrightbind := (let: "r" := do: keyleak2 InjR bob in
     match: "r" with
       InjL <> => kont0 (InjLV #()%V)
     | InjR "x" =>
       match: ! #l_sim with
         InjL <> =>
           let: "m'" := #()%V;; rand(#lbl:α) #(S n'') in
           let: "mA" := g ^ "m'" in
           #l_sim <- InjR "m'";; 
           (do: leakauth2 InjL ("mA", bob));; kont0 #()%V
       | InjR "m" => kont0 #()%V
       end
     end)%E).
           iApply (brel_bind'' [HandleCtx Deep _ _ _ _; AppRCtx _] [AppRCtx _] keytheory M N  (λ v1 v2 : val, ⌜v1 = v2⌝%I) (Do keyleak1 (InjLV bob)) (Do keyleak2 (InjLV bob))).
             { simpl. unfold M. repeat (rewrite -> labels_l_cons). set_solver. }
             { simpl. apply list_subseteq_nil. }
             { simpl. unfold M. unfold N. iApply to_iThy_le_intro'. eapply Permutation_submseteq.
               eapply perm_swap. } 
             { iApply (brel_introduction' [keyleak1] [keyleak2]).
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
                About brel_learn.
                iAssert (distinct' (LblClients ++ L)) as "%Hdistinct".
                { unfold LblClients. admit. }
                iApply (brel_bind'' _ _ keytheory M N  (λ v1 v2 : val, ⌜v1 = v2⌝%I) (Do keyleak1 (InjRV bob)) (Do keyleak2 (InjRV bob))).
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
                  +++ iApply brel_value.
                      iIntros "$ !>". brel_pures.
                      simpl. brel_pures.
                      iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)). 
                      { simpl. auto. }
                      { simpl. repeat (eapply list_subseteq_skip). eapply list_subseteq_nil. }
                      { iApply "Hrel". iApply "HmQ". }
                      { iApply "IH". }
                  +++ iApply brel_value.
                      iIntros "$ !>". brel_pures.
                      { simpl. unfold distinct in Hdistinct. destruct Hdistinct.
                        unfold distinct_l in H1. unfold LblClients in H1. simpl in H1.
                        repeat (rewrite -> labels_l_cons in H1).
                        eapply NoDup_app in H1.
                        eapply NoDup_cons_1_1. destruct H1 as [H1' H2'].
                        apply (NoDup_app [channel; getKey1] [schannel1]) in H1'.
                        destruct H1' as [H1' H2'']. apply H1'.}
                      { simpl.
                        iApply (brel_na_inv _ _ alphaN); first set_solver.
                        iFrame "Hinvα".
                        iIntros "([ (>Hα & >Hl_sim & >Hl_auth) | (#>Hα & #>Hl_sim & #>Hl_auth) ] & Hclose)". 
                        (*first message ot be sent by the authenticated channel*)
                        - iApply (brel_load_l _ _ _ [CaseCtx _ _] with "Hl_auth"). 
                          (*iIntros "HvN HdN".
                          iApply (rel_load_l_mask [CaseCtx _ _]).*)                                          
                          iIntros "!> Hl_auth".
                          simpl. brel_pures_l.
                          (*iApply (rel_load_r_with_mask _ _ _ _ [CaseCtx _ _] with "Hl_sim").*) 
                          iApply (brel_load_r _ _ _ _ [CaseCtx _ _] with "Hl_sim").
                          iIntros "Hl_sim". rel_pures.
                          iApply (brel_store_l _ _ _ [AppRCtx _] with "Hl_auth").
                          iIntros "!> Hl_auth". brel_pures.
                          iApply (brel_randT_r _ [AppRCtx _ ] with "Hα").
                          iIntros "Hα %Hn".
                          brel_pures.
                          repeat foldkont.
                          iApply (brel_exp_r [AppRCtx _]).
                          brel_pures.
                          iApply (brel_store_r _ _ _ _ [AppRCtx _] with "Hl_sim").
                          iIntros "Hl_sim". rel_pures.
                          iApply fupd_brel.
                          iMod (ghost_map_elem_persist with "Hl_sim") as "#Hl_sim".
                          iMod (ghost_map_elem_persist with "Hl_auth") as "#Hl_auth".
                          (*iMod (ghost_map_elem_persist with "H") as "#Hl_fchan".*)
                          iDestruct "Hα" as (ns) "(%Hf & Hα)".
                          apply map_eq_nil in Hf. simplify_eq.
                          iMod (ghost_map_elem_persist with "Hα") as "#Hα".
                          iModIntro.
                          iApply brel_na_close. iFrame.
                          iSplitL; [iModIntro; iRight; iFrame "#"|].
                          simpl.
                          brel_pures.
                          set (leakatheory := [([leakauth1], [leakauth2],
           iThySum (iThySum LASendAlice LASendBob)
             (iThySum LARecvAlice LARecvBob))]).
                          iApply (brel_bind _ _ _ leakatheory N _ (Do leakauth1 (InjLV (xor "x" "m", bob))) (Do leakauth2 (InjLV (vgval (g ^+ n) , bob)))).
                          { simpl. unfold leakatheory. auto.
                            unfold traversable. simpl.
                            About brel_bind.
                            Search traversable.
                            iModIntro.
                            iIntros (e1 e2 Q0).
                             admit. }
                          { simpl. auto. admit. }
                          { iApply (brel_introduction' [leakauth1] [leakauth2]); try (unfold leakatheory);
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
                            { simpl. auto. admit. }
                            { iApply "Hrel". iApply "HmQ". }
                            { iApply "IH". }          }                                                   
                      (*a message has already been sent by the authenticated channel*)
                        -  iApply brel_na_close. iFrame.
                           iSplitL; [iModIntro; iRight; iFrame "#"|].
                            iApply (brel_load_l _ _ _  [CaseCtx _ _] with "Hl_auth").
                            iIntros "!> Hl_auth'".
                            brel_pures.
                            iApply (brel_load_r _ _ _ _  [CaseCtx _ _] with "Hl_sim").
                            iIntros "Hl_sim'".
                            brel_pures.
                            iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)).
                            { simpl. auto. }
                            { simpl. auto. admit. }
                            { iApply "Hrel". iApply "HmQ". }
                            { iApply "IH". } } } }
         (* A message has already been sent by the secure channel*)
        ++ iApply brel_na_close. iFrame.
           iSplitL; [iModIntro; iRight; iFrame "#"|].
           iApply (brel_load_l _ _ _  [HandleCtx _ _ _ _ _ ; HandleCtx _ _ _ _ _ ; CaseCtx _ _] with "Hl_rchan").
           iIntros "!> Hl_rchan'".
           brel_pures.
           iApply (brel_load_r _ _ _ _  [HandleCtx _ _ _ _ _ ; CaseCtx _ _] with "Hl_fchan").
           iIntros "Hl_fchan'".
           brel_pures.
           iApply (brel_exhaustion (fill k1' #()%V) (fill k2' #()%V)).
           { simpl. auto. }
           { simpl. auto. admit. }
           { iApply "Hrel". iApply "HmQ". }
           { iApply "IH". }
     (* Recieved by Bob *)
      + iDestruct "HRecvBob" as "[%He1 [%He2 #HmQ]]".
        rewrite -> He1. rewrite -> He2. brel_pures.
        { simpl. admit. }
        { simpl. admit. }
        set (N := (([channel; getKey1; schannel1], [leaksec; schannel2; getKey2],
      iThyBot)
     :: ([keyleak1], [keyleak2],
         iThySum (iThySum KLeakSendAlice KLeakRecvAlice)
           (iThySum KLeakSendBob KLeakRecvBob))
        :: ([leakauth1], [leakauth2],
            iThySum (iThySum LASendAlice LASendBob)
              (iThySum LARecvAlice LARecvBob))
        :: L)).
        set (keyleakthy := [([keyleak1], [keyleak2],
         iThySum (iThySum KLeakSendAlice KLeakRecvAlice)
           (iThySum KLeakSendBob KLeakRecvBob))]).
        set (M := [([channel; getKey1; schannel1],
                 [leaksec; schannel2; getKey2], SecChannelThy)]).
        iApply (brel_bind'' _ _ keyleakthy M N _ (Do keyleak1 (InjLV bob)) (Do keyleak2 (InjLV bob))).
        { simpl. unfold M. admit. }
        { simpl. admit. }
        { admit. }
        {  iApply (brel_introduction' [keyleak1] [keyleak2]).
                1: { unfold keyleakthy.
                     eapply list_elem_of_here. }
                iExists _, _, [], [],_.
                do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
                iSplitL;  [|by iIntros "!>" (??) "H"; iApply "H"].
                iRight. iLeft. simpl.
                repeat (iSplit; try (iPureIntro); try (unfold SendV); try reflexivity).
                iModIntro. iApply brel_value. 
                iIntros "$ !>". brel_pures.
                iApply (brel_bind'' _ _ keyleakthy M N _ (Do keyleak1 (InjRV bob)) (Do keyleak2 (InjRV bob))).
                { simpl. unfold M. admit. }
                { simpl. admit. }
                { admit. }
                {  iApply (brel_introduction' [keyleak1] [keyleak2]).
                1: { unfold keyleakthy.
                     eapply list_elem_of_here. }
                iExists _, _, [], [],_.
                do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
                iSplitL;  [|by iIntros "!>" (??) "H"; iApply "H"].
                iRight. iRight. simpl.
                repeat (iSplit; try (iPureIntro); try (unfold RecvV); try reflexivity).
                iModIntro. iSplitL; iApply brel_value; iIntros "$ !>" ; brel_pures.
                (* Key not received by Bob*)
                   ++ iApply (brel_exhaustion (fill k1'(InjLV #()%V)) (fill k2' (InjLV #()%V))). 
                      { simpl. auto. }
                      { simpl. admit. }
                      { iApply "Hrel". iApply "HmQ". }
                      { iApply "IH". }
                      (* Key received by Bob *)
                   ++  simpl. admit.
                   ++ set (leakauththy := [([leakauth1], [leakauth2],
                       iThySum (iThySum LASendAlice LASendBob) (iThySum LARecvAlice LARecvBob))]).
                      iApply (brel_bind'' _ _ leakauththy _ N _ (Do leakauth1 (InjRV bob)) (Do leakauth2 (InjRV bob))).
                      { simpl. admit. }
                      { simpl. admit. }
                      { admit. }
                      { iApply (brel_introduction' [leakauth1] [leakauth2]).
                        1: { unfold leakauththy.
                             eapply list_elem_of_here. }
                        simpl.
                        iExists _, _, [], [],_.
                        do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
                        iSplitL;  [|by iIntros "!>" (??) "H"; iApply "H"].
                        iRight. iRight. simpl.
                        repeat (iSplit; try (iPureIntro); try (unfold RecvV); try reflexivity).
                        iModIntro. iSplit.
                        (* leakauth returns successfully with a value*)
                        - iIntros (b1 b2). iApply brel_value. iIntros "$ !>".
                          brel_pures. simpl.
                          iApply (brel_na_inv _ _ alphaN); first set_solver.
                          iFrame "Hinvα".
                          iIntros "([ (>Hα & >Hl_sim & >Hl_auth) | (#>Hα & #>Hl_sim & #>Hl_auth) ] & Hclose)".
                          (* first case, when no message is stored in the authenticated channel*)
                          +++ simpl. brel_pures.
                              iApply (brel_load_r _ _ _ _ [AppRCtx _] with "Hl_sim").
                              iIntros "Hl_sim".
                              iApply (brel_load_l _ _ _ [AppRCtx _] with "Hl_auth").
                              iIntros "!>Hl_auth".
                              simpl.
                              brel_pures.
                              iApply brel_na_close. iFrame.
                              iSplitL; [iModIntro; iLeft; iFrame |].
                              iApply (brel_exhaustion (fill k1'(InjLV #()%V)) (fill k2' (InjLV #()%V))).
                               { simpl. auto. }
                               { simpl. admit. }
                               { iApply "Hrel". iApply "HmQ". }
                               { iApply "IH". }
                               (*second case for the invariant, when a message is stored in the authenticated channel*)
                          +++ simpl. brel_pures.
                              iApply (brel_load_r _ _ _ _ [AppRCtx _] with "Hl_sim").
                              iIntros "Hl_sim'".
                              iApply (brel_load_l _ _ _ [AppRCtx _] with "Hl_auth").
                              iIntros "!>Hl_auth'".
                              simpl.
                              brel_pures.
                              iApply brel_na_close. iFrame.
                              iSplitL; [iModIntro; iRight; iFrame "#" |].
                              iApply (brel_exhaustion (fill k1'((InjRV (xor "key" "x"))%V)) (fill k2' ((InjRV #n)%V))).
                               { simpl. auto. }
                               { simpl. admit. }
                               { iApply "Hrel". (*iApply "HmQ".*) admit. }
                               { iApply "IH". } 
                         (*leakauth doesnot return with a value*)                             
                        - brel_pures.
                          iApply brel_value.
                          iIntros "$ !>". brel_pures.
                          iApply (brel_exhaustion (fill k1' (InjLV #()%V)) (fill k2' (InjLV #()%V))).
                          { simpl. auto. }
                          { simpl. admit. }
                          { iApply "Hrel". iApply "HmQ". }
                          {iApply "IH". }

Admitted.




(*Verification of CHAN_SIM[F_CHAN[]] ≤ F_OAUTH[F_KE_L[CHAN[]]]*)
(*---------------------------------------------------------*)
(*Lemma SIM_F_KE_CHAN f1 f2 γtoka γfraca γseca γsecb L :
    let LblThy := LblSecChannel γtoka atokN γfraca γseca γsecb in
    is_closed_expr ∅ f1 ->
    is_closed_expr ∅ f2 ->
    token γtoka -∗ 
    (*token γtokb -**)
    own γseca (to_dfrac_agree (DfracOwn 1) #()%V) -∗ 
    own γsecb (to_dfrac_agree (DfracOwn 1) #()%V) -∗ 
    BREL f1 ≤ f2 <| LblThy ++ L |> {{ (λ v1 v2, ⌜ v1 = v2 ⌝)  }} -∗ 
    BREL (CHAN_SIM channel1 leak1 (F_CHAN channel1 f1))
    ≤ (F_OAUTH channel2 (F_KE_L getKey2 channel2 leak2 (CHAN getKey2 channel2 f2))) <| LblEnvSec ++ L |> {{ (λ v1 v2, ⌜ v1 = v2 ⌝) }}.
 *)
 Lemma SIM_F_KE_CHAN (f1 f2 : val) (L : sem_row Σ) :
   sem_val_typed f1 f2 ((∀ᵣ θₕ, (sem_ty_sum 𝟙 𝟙) -{ θₕ }-> (Option  𝔾) -{ sem_row_union  θₕ L }-> 𝟙))%T -∗
   BREL CHAN_SIM (F_CHAN f1) ≤ F_OAUTH (F_KE_L (CHAN f2)) <|⊥|> {{λ v1 v2,
                                       ∀ (channel leaksec getKey : label),
                                       BREL v1 (λ: "m", do: leaksec (Send "m"))%V (λ: "m", do: leaksec (Recv "m"))%V ≤ v2 (λ: "m", do: channel (Send "m"))%V (λ: "m", do: channel (Recv "m"))%V (λ: "dst", do: getKey "dst")%V <| (iLblSig_to_iLblThy envsec_row) ++ (iLblSig_to_iLblThy L) |> {{ (λ w1 w2, 𝟙%T w1 w2)}}}}.
Proof with (repeat foldkont) using G.
 Admitted.

  
  
End s_channel_verification.

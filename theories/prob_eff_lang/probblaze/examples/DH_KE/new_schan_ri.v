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
(*From clutch.prob_eff_lang.probblaze Require Import def_schannel.*)
From clutch.prob_eff_lang.probblaze Require Import sem_types sem_row sem_sig sem_judgement sem_def.
From clutch.prob_eff_lang.probblaze Require Import p_composition.
From clutch.prob_eff_lang.probblaze Require Import newdef_schan.

Import fingroup.

Import fingroup.fingroup.

(*Import valgroup_notation.*)
Import valgroup_tactics.


Section schan_security.
  Context `{probblazeRGS Σ}.
  Context {vg: val_group}.
  Context {cg: clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.


  Definition REAL_CHAN : val :=
    λ: "f" "doLeakSend" "doLeakRecv" "doKeyLeak",  
      effect "channel"
      let: "doSend" := (λ: "m", do: (EffName "channel") (Send "m")) in
      let: "doRecv" := (λ: "m", do: (EffName "channel") (Recv "m")) in
      (*effect "schannel"
      let: "doSecSend" := (λ: "m", do: (EffName "schannel") (Send "m")) in
      let: "doSecRecv" := (λ: "m", do: (EffName "schannel") (Recv "m")) in *)
      effect "getKey"
      let: "doGK" := (λ: "party", do: (EffName "getKey") "party") in
      F_OAUTH "channel" "doSend" "doRecv" (F_KE_L "getKey" "doGK" "f" "doKeyLeak") "doLeakSend" "doLeakRecv".  

  Definition atokN' : namespace := nroot .@ "atokN1".
  Definition btokN' : namespace := nroot .@ "btokN1".

   (*Theories for the interaction of the secure channel with the environment*)
  (*-------------------------------------------------------------*)

  (* Theories for the authenticated channel leaks *)
  (*-------------------------------------------------------------*)
   (* Send TO Bob*)
   Program Definition LASendBob (leakauth1 leakauth2 : label) : iThy Σ :=
  λ e1 e2, (λne Q,
              ∃ m1 m2 : val,
                ⌜e1 = (do: leakauth1 (SendV (m1, bob)))⌝%E ∗ 
                           ⌜ e2 = do: leakauth2 (SendV (m2, bob)) ⌝%E ∗
                                      □ Q (Val #()%V) (Val #()%V))%I.
  Next Obligation. solve_proper. Qed.
  (* Send TO Alice*)
  Program Definition LASendAlice (leakauth1 leakauth2 : label) : iThy Σ :=
  λ e1 e2, (λne Q,
              ∃ m1 m2 : val,
                ⌜e1 = (do: leakauth1 (SendV (m1, alice)))⌝%E ∗ 
                           ⌜ e2 = do: leakauth2 (SendV (m2, alice)) ⌝%E ∗
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
  Program Definition SendSecBob (schannel1 schannel2 : label) : iThy Σ :=
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
  
  Program Definition SendSecAlice (schannel1 schannel2 : label) : iThy Σ :=
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
  
  Program Definition RecvSecBob (schannel1 schannel2 : label) : iThy Σ :=
     λ e1 e2, (λne Q,
                ⌜ e1 = do: schannel1 (RecvV bob) ⌝%E ∗
                ⌜ e2 = do: schannel2 (RecvV bob) ⌝%E ∗
                □ (Q NONEV NONEV)
             )%I.
  Next Obligation. solve_proper. Qed. 
    
  Program Definition RecvSecAlice (schannel1 schannel2 : label) : iThy Σ :=
     λ e1 e2, (λne Q,
                 ⌜ e1 = do: schannel1 (RecvV alice) ⌝%E ∗
                 ⌜ e2 = do: schannel2 (RecvV alice) ⌝%E ∗
                 □ (Q NONEV NONEV )
             )%I.
  Next Obligation. solve_proper. Qed.


   (* semantic types*)
  (*----------------------------------------------------------------------------*)

   Definition sem_ty_group : sem_ty Σ := (λ v1 v2, ∃ g : vgG, ⌜ v1 = g ⌝ ∗ ⌜ v2 = g ⌝)%I.
  Notation "'𝔾'" := sem_ty_group. 
  (*Program Definition bot_mono := {| pmono_prot_car := iThyBot ; pmono_prot_prop := _ |}.
  Next Obligation. solve_proper. Defined.
 
  Definition thy_sec_chan (l1 l2 : label) := @SemSig Σ bot_mono (l1,l2).
  Program Definition thy_sec_row (channel leaksec getKey1 getKey2 schannel1 schannel2 : label) :=
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
  Lemma keyleak_pers_mono_row (channel leaksec getKey1 getKey2 schannel1 schannel2 keyleak1 keyleak2 : label) : ⊢ pers_mono_row (iLblSig_to_iLblThy [([channel; getKey1; schannel1; keyleak1] , [leaksec; getKey2; schannel2; keyleak2] , keyleak keyleak1 keyleak2)]).
  Proof. Admitted.
  Definition keyleak_row (channel leaksec getKey1 getKey2 schannel1 schannel2 keyleak1 keyleak2 : label) := SemRow [([channel; getKey1; schannel1; keyleak1] , [leaksec; getKey2; schannel2; keyleak2] , keyleak keyleak1 keyleak2)] (keyleak_pers_mono_row channel leaksec getKey1 getKey2 schannel1 schannel2 keyleak1 keyleak2).
 
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
  Program Definition envsec_row (channel leaksec getKey1 getKey2 schannel1 schannel2 keyleak1 keyleak2 leakauth1 leakauth2 : label) :=
    sem_row_union (keyleak_row channel leaksec getKey1 getKey2 schannel1 schannel2 keyleak1 keyleak2) (leakauth_row leakauth1 leakauth2).

(*Verification of F_OAUTH[F_KE_L[CHAN[]]] ≤ CHAN_SIM[F_CHAN[]]*)
(*----------------------------------------------------------*)
Lemma F_KE_CHAN_SIM (f1 f2 : val) (L : sem_row Σ) :
    sem_val_typed f1 f2 ((∀ᵣ θₕ, ((sem_ty_sum 𝟙 𝟙) -{ θₕ }-> (Option  𝔾)) -{ θₕ }-> ((sem_ty_sum 𝟙 𝟙) -{ θₕ }-> (Option  𝔾)) -{ sem_row_union  θₕ L }-> 𝟙))%T -∗ 
    BREL REAL_CHAN (CHAN f1)
      ≤ CHAN_SIM (F_CHAN f2) <|⊥|> {{λ v1 v2,
                                       ∀ (channel leaksec getKey1 getKey2 schannel1 schannel2 leakauth1 leakauth2 keyleak1 keyleak2 : label),
                                       BREL v1 (λ: "m", do: leakauth1 (Send "m"))%V (λ: "m", do: leakauth1 (Recv "m"))%V (λ: "m", do: keyleak1 "m")%V (λ: <>, #())%V ≤ v2 (λ: "m", do: keyleak2 "m")%V (λ: "m", do: leakauth2 (Send "m"))%V (λ: "m", do: leakauth2 (Recv "m"))%V <| (iLblSig_to_iLblThy (envsec_row channel leaksec getKey1 getKey2 schannel1 schannel2 leakauth1 leakauth2 keyleak1 keyleak2 )) ++ (iLblSig_to_iLblThy L) |> {{ (λ w1 w2, 𝟙%T w1 w2)}}}}.
Proof.
Admitted.
 
End schan_security.

From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import  na_invariants.
From iris.algebra Require Import agree excl auth frac excl_auth.
From iris.algebra.lib Require Import dfrac_agree.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode
  spec_rules spec_ra 
  class_instances.
From clutch.prob_eff_lang.probblaze Require Import tactics.
From clutch.prob_eff_lang.probblaze Require Import definition.
From clutch.prob_eff_lang.probblaze Require Import DH_channel.
From clutch.prob_eff_lang.probblaze Require Import s_channel.


Import fingroup.

Import fingroup.fingroup.

Import valgroup_notation.
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
   Program Definition LASendBob : iThy Σ :=
  λ e1 e2, (λne Q,
              ∃ m1 m2 : val,
                ⌜e1 = (do: leakauth1 (SendV (m1, bob)))⌝%E ∗ 
                           ⌜ e2 = do: leakauth2 (SendV (m2, bob)) ⌝%E ∗
                                      □ Q (Val #()%V) (Val #()%V))%I.
  Next Obligation. solve_proper. Qed.

  Program Definition LASendAlice : iThy Σ :=
  λ e1 e2, (λne Q,
              ∃ m1 m2 : val,
                ⌜e1 = (do: leakauth1 (SendV (m1, alice)))⌝%E ∗ 
                           ⌜ e2 = do: leakauth2 (SendV (m2, alice)) ⌝%E ∗
                                      □ Q (Val #()%V) (Val #()%V))%I.
  Next Obligation. solve_proper. Qed.

  Program Definition LARecvBob : iThy Σ :=
   λ e1 e2, (λne Q,
                ⌜ e1 = do: leakauth1 (RecvV bob) ⌝%E ∗
                ⌜ e2 = do: leakauth2 (RecvV bob) ⌝%E ∗
                □ ((∀ b1 b2 : nat, Q (SOMEV #b1) (SOMEV #b2)) ∧ Q NONEV NONEV)
             )%I.
  Next Obligation. solve_proper. Qed.

  Program Definition LARecvAlice : iThy Σ :=
     λ e1 e2, (λne Q,
                ⌜ e1 = do: leakauth1 (RecvV alice) ⌝%E ∗
                ⌜ e2 = do: leakauth2 (RecvV alice) ⌝%E ∗
                □ ((∀ b1 b2 : nat, Q (SOMEV #b1) (SOMEV #b2)) ∧ Q NONEV NONEV)
             )%I.
  Next Obligation. solve_proper. Qed.

  
  (* Theories for the key exchange leaks*)
  (*---------------------------------------------------------*)
  Program Definition KLeakSendAlice : iThy Σ :=
    λ e1 e2, (λne Q,
                ⌜ e1 = do: keyleak1 (SendV alice) ⌝%E ∗
                           ⌜ e2 = do: keyleak2 (SendV alice) ⌝%E ∗
                                      □ Q (Val #()%V) (Val #()%V))%I.
  Next Obligation. solve_proper. Qed.

  Program Definition KLeakSendBob : iThy Σ :=
    λ e1 e2, (λne Q,
                ⌜ e1 = do: keyleak1 (SendV bob) ⌝%E ∗
                           ⌜ e2 = do: keyleak2 (SendV bob) ⌝%E ∗
                                      □ Q (Val #()%V) (Val #()%V))%I.
  Next Obligation. solve_proper. Qed.


  Program Definition KLeakRecvAlice : iThy Σ :=
    λ e1 e2, (λne Q,
                ⌜ e1 = do: keyleak1 (RecvV alice) ⌝%E ∗
                           ⌜ e2 = do: keyleak2 (RecvV alice) ⌝%E ∗
                                      □ Q (Val #()%V) (Val #()%V))%I.
  Next Obligation. solve_proper. Qed.

  Program Definition KLeakRecvBob : iThy Σ :=
     λ e1 e2, (λne Q,
                ⌜ e1 = do: keyleak1 (RecvV bob) ⌝%E ∗
                           ⌜ e2 = do: keyleak2 (RecvV bob) ⌝%E ∗
                                      □ Q (Val #()%V) (Val #()%V))%I.
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

  Program Definition ChanLeakSec : iThy Σ := iThySum (iThySum SendALSAlice SendALSBob) (iThySum RecvALSAlice RecvALSBob).
  
  Definition LblEnvSec := [ ([channel; getKey1], [leaksec; getKey2], iThyBot)    ;
                            ([keyleak1], [keyleak2],iThySum (iThySum KLeakSendAlice KLeakRecvAlice) (iThySum KLeakSendBob KLeakRecvAlice));
                            ([leakauth1], [leakauth2], iThySum (iThySum LASendAlice LASendBob) (iThySum LARecvAlice LARecvBob))].

   Definition LblEnvSec' := [ ([leaksec; getKey1], [channel; getKey2], iThyBot)    ;
                            ([keyleak1], [keyleak2],iThySum (iThySum KLeakSendAlice KLeakRecvAlice) (iThySum KLeakSendBob KLeakRecvAlice));
                            ([leakauth1], [leakauth2], iThySum (iThySum LASendAlice LASendBob) (iThySum LARecvAlice LARecvBob))].

  
  (*Definition LblEnvSec := [([leak'1], [leak'2],iThySum (iThySum SendSecBob RecvSecAlice) (iThySum RecvSecBob RecvSecAlice)); ([leak1], [leak2], iThySum LeakAlice LeakBob)].*)

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
                             (⌜ e1 = do: schannel1 (SendV (m, bob)) ⌝%E ∗
                              ⌜ e2 = do: schannel2 (SendV (m', bob)) ⌝%E)  ∗ 
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
  
   Definition SecChannelThy : iThy Σ :=
   iThySum (iThySum (SendSecAlice) (RecvSecBob)) (iThySum (SendSecBob) (RecvSecAlice)).

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
  Definition GetKey1bot : iThy Σ :=
    λ e1 ex, (λne True, ⌜ e1 = do: getKey1 (ex) ⌝%E ∗ False)%I.

    
  Definition LblClients : iLblThy Σ :=
    [([schannel1; getKey1; channel],[schannel2; getKey2; leaksec], (SecChannelThy))].
  
  Definition LblClients' : iLblThy Σ :=
     [([schannel1; getKey1; leaksec],[schannel2; getKey2; channel], (SecChannelThy))].
    (*[([schannel1; getKey1],[schannel2], (iThySum (GetKey1bot) (SecChannelThy)))].*)
  
(*Verification of F_OAUTH[F_KE_L[CHAN[]]] ≤ CHAN_SIM[F_CHAN[]]*)
(*----------------------------------------------------------*)
(*Lemma F_KE_CHAN_SIM f1 f2 γtoka atokN γfraca γseca γsecb γtoka1 γtokb1 γfraca1 γfracb1 γautha γauthb atokN1 btokN1 L :
  let LblThy := LblClients γtoka atokN γfraca γseca γsecb γtoka1 γtokb1 γfraca1 γfracb1 γautha γauthb atokN1 btokN1 in
  let Xthy := iThySum (iThySum SendSecBob RecvSecAlice)
        (iThySum RecvSecBob RecvSecAlice) in 
    is_closed_expr ∅ f1 ->
    is_closed_expr ∅ f2 ->
    token γtoka -∗ 
    token γtoka1 -∗
    token γtokb1 -∗
    own γseca (to_dfrac_agree (DfracOwn 1) #()%V) -∗ 
    own γsecb (to_dfrac_agree (DfracOwn 1) #()%V) -∗
    own γautha (to_dfrac_agree (DfracOwn 1) #()%V) -∗ 
    own γauthb (to_dfrac_agree (DfracOwn 1) #()%V) -∗ 
    BREL f1 ≤ f2 <| LblThy ++ L |> {{ (λ v1 v2, ⌜ v1 = v2 ⌝)  }} -∗ 
    BREL (F_OAUTH leak'1 channel1 (F_KE_L getKey1 channel1 leak1 (CHAN getKey1 schannel1 channel1 f1)))
    ≤ CHAN_SIM leak'2 leak2 channel2 (F_CHAN schannel2 channel2 f2)<| LblEnvSec ++ L |> {{ (λ v1 v2, ⌜ v1 = v2 ⌝) }}.*)
  Lemma F_KE_CHAN_SIM f1 f2 L :
    is_closed_expr ∅ f1 ->
    is_closed_expr ∅ f2 ->
    BREL f1 ≤ f2 <| LblClients ++ L |> {{ (λ v1 v2, ⌜ v1 = v2 ⌝) }} -∗
    BREL (F_OAUTH leakauth1 channel (F_KE_L getKey1 keyleak1 (CHAN getKey1 schannel1 channel f1)))
    ≤ CHAN_SIM leakauth2 keyleak2 leaksec (F_CHAN schannel2 leaksec f2)<| LblEnvSec ++ L |> {{ (λ v1 v2, ⌜ v1 = v2 ⌝) }}.
Proof with (repeat foldkont) using G.
  iIntros (Hf1 Hf2)  "Hrelf1f2". repeat simpl.
  iApply brel_alloctape_r. iIntros (β) "Hβ". brel_pures_r. 
  iApply brel_alloc_r. iIntros (l2) "Hl2". brel_pures_r.
  iApply brel_alloc_l. iIntros (l1) "!>Hl1". brel_pures_l.
  rewrite subst_is_closed_empty; try done.
  iApply brel_couple_UT. 1: auto.
  simpl. iFrame "Hβ". iSplit => //.
  iIntros (n ?) "!> Hβ". brel_pures.
  rewrite subst_is_closed_empty; try done.
  brel_exp_l. brel_pures.
  iApply brel_alloc_l. iIntros (l3) "!>Hl3". brel_pures_l.
  simpl. do 2 rewrite subst_is_closed_empty; try done.
  iApply brel_alloc_r. iIntros (l0) "Hl0". brel_pures_r.
  rewrite subst_is_closed_empty; try done. 
  set (kl1 := (match: "payload" with
         InjL "payload" =>
           let: "dst" := "payload" in
           let: "m" := Fst "dst" in
           let: "dst" := Snd "dst" in
           match: ! #l3 with
             InjL <> =>
               #l3 <- InjR "m";; 
               let: "key" := do: getKey1 "dst" in
               match: "key" with
                 InjL <> => "k" (InjLV #()%V)
               | InjR "x" => let: "enc_m" := #()%V in (do: channel InjL ("enc_m", bob));; "k" #()%V
               end
           | InjR "message" => "k" (InjLV #()%V)
           end
       | InjR "from" =>
         let: "key" := do: getKey1 "from" in
         match: "key" with
           InjL <> => "k" (InjLV #()%V)
         | InjR "key" =>
           let: "r" := do: channel InjR "from" in
           match: "r" with
             InjL <> => "k" (InjLV #()%V)
           | InjR "x" => let: "enc_m" := #()%V in "k" (InjR "enc_m")
           end
         end
                         end)%E).
  set (kl2 := (match: "p" with
         InjL <> =>
           (do: keyleak1 InjL alice);; 
           let: "r" := do: keyleak1 InjR bob in
           match: "r" with InjL <> => "k" (InjLV #()%V) | InjR "w" => "k" (InjR (vgval (g ^+ n))) end
       | InjR <> =>
         let: "r" := do: keyleak1 InjR alice in
         match: "r" with
           InjL <> => "k" (InjLV #()%V)
         | InjR "w" => (do: keyleak1 InjL bob);; "k" (InjR (vgval (g ^+ n)))
         end
                       end)%E).
  set (kl3 := ( match: "payload" with
         InjL "payload" =>
           let: "dst" := "payload" in
           let: "m" := Fst "dst" in
           let: "dst" := Snd "dst" in
           match: ! #l1 with
             InjL <> => #l1 <- InjR "m";; (do: leakauth1 InjL ("m", "dst"));; "k" #()%V
           | InjR "message" => "k" #()%V
           end
       | InjR "from" =>
         let: "r" := do: leakauth1 InjR "from" in
         match: "r" with InjL <> => "k" (InjLV #()%V) | InjR "x" => "k" ! #l1 end
                       end)%E).
  set (kr1 := ( match: "payload" with
         InjL "payload" =>
           let: "dst" := "payload" in
           let: "m" := Fst "dst" in
           let: "dst" := Snd "dst" in
           match: ! #l0 with
             InjL <> => #l0 <- InjR "m";; (do: leaksec InjL "dst");; "k" #()%V
           | InjR "x" => "k" #()%V
           end
       | InjR "from" =>
         let: "r" := do: leaksec InjR "from" in
         match: "r" with InjL <> => "k" (InjLV #()%V) | InjR "x" => "k" ! #l0 end
                       end)%E).
  set (kr2 := ( match: "payload" with
         InjL "payload" =>
           let: "dst" := "payload" in
           let: "m" := Fst "dst" in
           let: "dst" := Snd "dst" in
           (do: keyleak2 InjL "dst");; 
           let: "r" := do: keyleak2 InjR bob in
           match: "r" with
             InjL <> => "k" (InjL #()%V)
           | InjR "x" =>
             let: "m" := match: ! #l2 with
                           InjL <> => let: "m" := #()%V;; rand(#lbl:β) #(S n'') in #l2 <- InjR "m";; "m"
                         | InjR "m" => "m"
                         end in
             let: "mA" := g ^ "m" in (do: leakauth2 InjL ("mA", alice));; "k" #()%V
           end
       | InjR "from" =>
         let: "r" := do: keyleak2 InjR "from" in
         match: "r" with
           InjL <> => "k" (InjL #()%V)
         | InjR "x" => (do: keyleak2 InjL bob);; (do: leakauth2 InjR "from");; "k" (InjR #0)
         end
                       end)%E).
  set (f1' :=  (handle: f1 with
     | effect schannel1 "payload", rec "k" as multi => kl1
     | return "y" => #()%V
                end)%E).
  set (f2' := ( handle: f2 with
     | effect schannel2 "payload", rec "k" as multi => kr1
     | return "y" => #()%V
                end)%E).
  iAssert ( brel ⊤ f1' f2'
    (([channel; getKey1], [leaksec; getKey2], ChanLeakSec)
     :: ([keyleak1], [keyleak2],
         iThySum (iThySum KLeakSendAlice KLeakRecvAlice) (iThySum KLeakSendBob KLeakRecvAlice))
        :: ([leakauth1], [leakauth2],
            iThySum (iThySum LASendAlice LASendBob) (iThySum LARecvAlice LARecvBob))
           :: L)
    (λ v1 v2 : val, ⌜v1 = v2⌝%I)) as "Hrelf1'f2'".
  { admit.}
  Search "_ ⊆ _".
  Search "sublist".
  About  "`sublist_of`".
  Search "∈".
  iApply (brel_exhaustion f1' f2'); try simpl; try auto; try (apply sublist_subseteq); try (apply singleton_sublist_l);
    try (apply list_elem_of_In); try simpl; try auto.
  { iSplit; [iIntros (v1 v2) "%Hv1v2"; iModIntro; brel_pures; iModIntro; done |].
   iIntros (?????) "!# %Hk1 %Hk2 HXQ #Hrel".
  
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
 Lemma SIM_F_KE_CHAN f1 f2 L :
    is_closed_expr ∅ f1 ->
    is_closed_expr ∅ f2 ->
    BREL f1 ≤ f2 <| LblClients' ++ L |> {{ (λ v1 v2, ⌜ v1 = v2 ⌝) }} -∗
    BREL (CHAN_SIM leakauth1 keyleak1 leaksec (F_CHAN schannel1 leaksec f1)) ≤
      (F_OAUTH leakauth2 channel (F_KE_L getKey2 keyleak2 (CHAN getKey2 schannel2 channel f1)))
      <| LblEnvSec' ++ L |> {{ (λ v1 v2, ⌜ v1 = v2 ⌝) }}.
 Proof.
 Admitted.

  
  
End s_channel_verification.

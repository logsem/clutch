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

  Print Grammar constr.

  (*Definition REAL_CHAN : val :=
    λ: "f" "doLeakSend" "doLeakRecv" "doKeyLeak",  
      effect "channel"
      let: "doSend" := (λ: "m", do: (EffName "channel") (Send "m")) in
      let: "doRecv" := (λ: "m", do: (EffName "channel") (Recv "m")) in
      (*effect "schannel"
      let: "doSecSend" := (λ: "m", do: (EffName "schannel") (Send "m")) in
      let: "doSecRecv" := (λ: "m", do: (EffName "schannel") (Recv "m")) in *)
      effect "getKey"
      let: "doGK" := (λ: "party", do: (EffName "getKey") "party") in
      F_OAUTH "channel" "doSend" "doRecv" (F_KE_L "getKey" "doGK" ("f" "doSend" "doRecv") "doKeyLeak") "doLeakSend" "doLeakRecv". *)

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

  Program Definition sec_channel_mono (schannel1 schannel2 : label) := {| pmono_prot_car := iThySum (SendSecAlice schannel1 schannel2) (RecvSecBob schannel1 schannel2) ; pmono_prot_prop := _ |}.
  Next Obligation.
  Admitted.

  Definition sec_channel (schannel1 schannel2 : label) := @SemSig Σ (sec_channel_mono schannel1 schannel2) (schannel1, schannel2).

  Lemma client_pers_mono_row (getKey1 schannel1 schannel2 : label) : ⊢ pers_mono_row (iLblSig_to_iLblThy [([getKey1; schannel1] , [schannel2] , sec_channel schannel1 schannel2)]).
  Proof.
  Admitted.

  Lemma sec_channel_pers_mono_row (schannel1 schannel2 : label) : ⊢ pers_mono_row (iLblSig_to_iLblThy [([schannel1] , [schannel2], sec_channel schannel1 schannel2)]).
  Proof.
  Admitted.
  
  Program Definition sec_channel_row (schannel1 schannel2 : label) := SemRow [([schannel1], [schannel2], sec_channel schannel1 schannel2)] (sec_channel_pers_mono_row schannel1 schannel2).
  Program Definition client_row (getKey1 schannel1 schannel2 : label) := SemRow [([getKey1; schannel1], [schannel2], sec_channel schannel1 schannel2)] (client_pers_mono_row getKey1 schannel1 schannel2) .
   Definition REAL_CHAN : val :=
    λ: "f",
    (F_OAUTH ||ₗ F_KE_L) (CHAN "f").

(*Verification of F_OAUTH[F_KE_L[CHAN[]]] ≤ CHAN_SIM[F_CHAN[]]*)
(*----------------------------------------------------------*)
Lemma F_KE_CHAN_SIM (f1 f2 : val) (L : sem_row Σ) :
    sem_val_typed f1 f2 ((∀ᵣ θₕ, (((sem_ty_sum 𝟙 𝟙) -{ θₕ }-> (Option  𝔾)) × ((sem_ty_sum 𝟙 𝟙) -{ θₕ }-> (Option  𝔾))) -{ sem_row_union  θₕ L }-> 𝟙))%T -∗ 
    BREL REAL_CHAN f1
      ≤ CHAN_SIM (F_CHAN f2) <|⊥|> {{λ v1 v2,
                                       ∀ (leakauth1 leakauth2 keyleak1 keyleak2 : label),
                                       BREL v1 ((λ: "m", do: leakauth1 (Send "m")), (λ: "m", do: leakauth1 (Recv "m")))%V (λ: "m", do: keyleak1 "m")%V ≤ v2 ((λ: "m", do: leakauth2 (Send "m")), (λ: "m", do: leakauth2 (Recv "m")))%V (λ: "m", do: keyleak2 "m")%V <| (iLblSig_to_iLblThy (envsec_row keyleak1 keyleak2 leakauth1 leakauth2 )) ++ (iLblSig_to_iLblThy L) |> {{ (λ w1 w2, 𝟙%T w1 w2)}}}}.
Proof with (repeat foldkont) using G.
  iIntros "Hrelf1f2".
  repeat simpl.
  unfold REAL_CHAN. brel_pures.
  unfold left_composition. brel_pures.
  unfold CHAN.
  repeat simpl. brel_pures'.
  
  (*unfold CHAN_SIM, F_OAUTH.*)
  unfold F_CHAN, CHAN_SIM, F_KE_L, F_OAUTH. 
   
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
           InjL "payload" =>
           let: "dst" := "payload" in
           let: "m" := Fst "dst" in
           let: "dst" := Snd "dst" in
           match: ! #l_rchan with
             InjL <> =>
               #l_rchan <- InjR "m";; 
               let: "key" := (λ: "party", do: getKey' "party")%V "dst" in
               match: "key" with
                 InjL <> => "k" #()%V
               | InjR "x" =>
                 let: "enc_m" := xor "x" "m" in
                 (λ: "m", do: channel' InjL "m")%V ("enc_m", bob);; "k" #()%V
               end
           | InjR "m" => "k" #()%V
           end
       | InjR "from" =>
         let: "key" := (λ: "party", do: getKey' "party")%V "from" in
         match: "key" with
           InjL <> => "k" (InjLV #()%V)
         | InjR "key" =>
           let: "r" := (λ: "m", do: channel' InjR "m")%V "from" in
           match: "r" with
             InjL <> => "k" (InjLV #()%V)
           | InjR "x" => let: "enc_m" := xor "key" "x" in "k" (InjR "enc_m")
           end
         end
       end)%E).
  set (kl2 := ( match: "p" with
         InjL <> =>
           (λ: "m", do: keyleak1 "m")%V (InjL bob);; 
           let: "r" := (λ: "m", do: keyleak1 "m")%V (InjR bob) in
           match: "r" with InjL <> => "k" (InjLV #()%V) | InjR "w" => "k" (InjR (vgval (g ^+ n))) end
       | InjR <> =>
         let: "r" := (λ: "m", do: keyleak1 "m")%V (InjR alice) in
         match: "r" with
           InjL <> => "k" (InjLV #()%V)
         | InjR "w" => (λ: "m", do: keyleak1 "m")%V (InjL alice);; "k" (InjR (vgval (g ^+ n)))
         end
                end)%E).
  set (kl3 := ( match: "payload" with
         InjL "payload" =>
           let: "dst" := "payload" in
           let: "m" := Fst "dst" in
           let: "dst" := Snd "dst" in
           match: ! #l_auth with
             InjL <> => #l_auth <- InjR "m";; (λ: "m", do: leakauth1 Send "m")%V ("m", "dst");; "k" #()%V
           | InjR "message" => "k" #()%V
           end
       | InjR "from" =>
         let: "r" := (λ: "m", do: leakauth1 Recv "m")%V "from" in
         match: "r" with InjL <> => "k" (InjLV #()%V) | InjR "x" => "k" ! #l_auth end
                end)%E).
  set (kr1 := (  match: "payload" with
         InjL "payload" =>
           let: "dst" := "payload" in
           let: "m" := Fst "dst" in
           let: "dst" := Snd "dst" in
           match: ! #l_fchan with
             InjL <> => #l_fchan <- InjR "m";; (λ: "m", do: leaksec' InjL "m")%V "dst";; "k" #()%V
           | InjR "x" => "k" #()%V
           end
       | InjR "from" =>
         let: "r" := (λ: "m", do: leaksec' InjR "m")%V "from" in
         match: "r" with InjL <> => "k" (InjLV #()%V) | InjR "x" => "k" (InjR "x") end
                 end)%E).
  set (kr2 := (  match: "payload" with
         InjL "payload" =>
           (λ: "m", do: keyleak2 "m")%V (InjL bob);; 
           let: "r" := (λ: "m", do: keyleak2 "m")%V (InjR bob) in
           match: "r" with
             InjL <> => "k" (InjLV #()%V)
           | InjR "x" =>
             match: ! #l_sim with
               InjL <> =>
                 let: "m'" := #()%V;; rand(#lbl:α) #(S n'') in
                 let: "mA" := vexp g "m'" in
                 #l_sim <- InjR "m'";; (λ: "m", do: leakauth2 Send "m")%V ("mA", bob);; "k" #()%V
             | InjR "m" => "k" #()%V
             end
           end
       | InjR "from" =>
         (λ: "m", do: keyleak2 "m")%V (InjL "from");; 
         let: "r" := (λ: "m", do: keyleak2 "m")%V (InjR "from") in
         match: "r" with
           InjL <> => "k" (InjLV #()%V)
         | InjR "x" =>
           let: "rla" := (λ: "m", do: leakauth2 Recv "m")%V "from" in
           match: "rla" with InjL <> => "k" (InjLV #()%V) | InjR "x" => "k" ! #l_sim end
         end
                 end )%E).
  
  unfold sem_val_typed. simpl.
  iDestruct "Hrelf1f2" as "#Hrelf1f2".
  set (θ := client_row getKey' schannel_l schannel_r).
  iSpecialize ("Hrelf1f2" $! θ).
  iDestruct "Hrelf1f2" as "#Hrelf1f2".
  unfold sem_ty_arr, sem_ty_mbang. simpl.
  iDestruct "Hrelf1f2" as "#Hrelf1f2".
  iAssert (sem_val_typed  ((λ: "m", do: schannel_l InjL "m"), (λ: "m", do: schannel_l InjR "m"))%V ((λ: "m", do: schannel_r InjL "m") , (λ: "m", do: schannel_r InjR "m"))%V (((𝟙 + 𝟙)%T -{ θ }-> (Option 𝔾)) × ((𝟙 + 𝟙)%T -{ θ }-> (Option 𝔾)))%T) as "Hschn".
  { admit. }
  (*iAssert (sem_val_typed (λ: "m", do: schannel_l InjR "m") (λ: "m", do: schannel_r InjR "m") ((𝟙 + 𝟙)%T -{ θ }-> (Option 𝔾))%T) as "Hschnrcv".
  { admit. }*)
  unfold sem_val_typed. simpl.
  iDestruct "Hschn" as "#Hschn".
  (*iDestruct "Hschnrcv" as "#Hschnrcv".*)
  iSpecialize ("Hrelf1f2" with "Hschn"). simpl.
  (*About brel_add_label_l.*)
  (*iSpecialize ("Hrelf1f2" with "Hschnrcv").
  brel_pures'.*)
 
  (*iAssert (brel ⊤ (f1 ((λ: "m", do: schannel_l InjL "m"),(λ: "m", do: schannel_l InjR "m"))%V)
              (f2 ((λ: "m", do: schannel_r InjL "m"),(λ: "m", do: schannel_r InjR "m"))%V)
    (([channel; getKey1; schannel1], [leaksec; schannel2], sec_channel schannel1 schannel2)
      :: iLblSig_to_iLblThy L) 𝟙%T) as "Hrelf1f2mono".
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
   (*set (f'1 := ( handle: f1 (λ: "m", do: schannel_l InjL "m", λ: "m", do: schannel_l InjR "m")%V with
     | effect schannel_l "payload", rec "k" as multi => kl1
               | return "y" => #()%V end)%E).
   set (f'2 := ( handle: f2 (λ: "m", do: schannel_r InjL "m", λ: "m", do: schannel_r InjR "m")%V with
     | effect schannel_r "payload", rec "k" as multi => kr1
     | return "y" => #()%V
                 end)%E).
   iApply brel_new_theory.
   iApply (brel_add_label_l with "HgK").
   iApply (brel_add_label_l with "Hchannel").
   iApply (brel_add_label_r with "Hleaksec").
   
   iApply ((brel_exhaustion f'1 f'2 _ _ _ _ _ _ _ _ _ )); try simpl.
   { admit.}
   { admit.}
   { 
   About brel_exhaustion.
   unfold f'1, f'2.*)
   iApply brel_new_theory.
   iApply (brel_add_label_l with "Hschannel_l").
   iApply (brel_add_label_r with "Hschannel_r").
   iApply (brel_add_label_l with "HgK").
   iApply (brel_add_label_l with "Hchannel").
   iApply (brel_add_label_r with "Hleaksec").
   set (X :=  iLblSig_to_iLblThy [([schannel_l] , [schannel_r] , sec_channel schannel_l schannel_r)]).
   set (R := (λ u1 u2 : val, 𝟙%T u1 u2)).
   set (X' := sec_channel schannel_l schannel_r).
   (*iAssert  (brel ⊤ (f1 (λ: "m", do: schannel_l InjL "m", λ: "m", do: schannel_l InjR "m")%V)
    (f2 (λ: "m", do: schannel_r InjL "m", λ: "m", do: schannel_r InjR "m")%V)
    (([channel'; getKey'; schannel_l], [leaksec'; schannel_r], X)
     :: ([keyleak1], [keyleak2], keyleak keyleak1 keyleak2)
        :: ([leakauth1], [leakauth2], leakauth leakauth1 leakauth2) :: iLblSig_to_iLblThy L)
    R) as "Hrelf1f2mono".*)
   About brel_exhaustion.
   iApply ((brel_exhaustion (f1 ((λ: "m", do: schannel_l InjL "m"),(λ: "m", do: schannel_l InjR "m"))%V) (f2 ((λ: "m", do: schannel_r InjL "m"),(λ: "m", do: schannel_r InjR "m"))%V) _ _ X' _ _ R _ _ _) with "[Hrelf1f2]"); try simpl; try auto; try (apply sublist_subseteq); try (apply singleton_sublist_l);
     try (apply list_elem_of_In); try simpl; try auto; try (repeat (eapply sublist_skip)) ; try eapply sublist_nil_l.
   { admit.}
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
             iApply (brel_load_l _ _ _  [HandleCtx Deep MS channel' _ _ ; HandleCtx Deep MS getKey' _ _; CaseCtx _ _] with "Hl_rchan").
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
            (* set (keytheory := [([keyleak1], [keyleak2],
         iThySum (iThySum KLeakSendAlice KLeakRecvAlice)
           (iThySum KLeakSendBob KLeakRecvBob))]).*)
             (*set (keytheory := [([keyleak1], [keyleak2], keyleak keyleak1 keyleak2)]).*)
            (*set (M := (([channel'; getKey'; schannel_l], [leaksec'; schannel_r], iThyBot)
        :: ([leakauth1], [leakauth2], leakauth leakauth1 leakauth2) :: (iLblSig_to_iLblThy L))).
            set (N := (([channel; getKey1; schannel1], [leaksec; schannel2; getKey2], iThyBot)
     :: ([keyleak1], [keyleak2],
         iThySum (iThySum KLeakSendAlice KLeakRecvAlice)
           (iThySum KLeakSendBob KLeakRecvBob))
        :: ([leakauth1], [leakauth2],
             iThySum (iThySum LASendAlice LASendBob) (iThySum LARecvAlice LARecvBob)) :: L)).*)
            simpl.
            repeat foldkont.
            simpl.
            set (kontleftbind :=
             (let: "r" := (λ: "m", do: keyleak1 "m")%V (InjR bob) in
             match: "r" with
               InjL <> => kont (InjLV #()%V)
             | InjR "w" => kont (InjR (vgval (g ^+ n)))
             end)%E).
            set (kontrightbind := (let: "r" := (λ: "m", do: keyleak2 "m")%V (InjR bob) in
     match: "r" with
       InjL <> => kont0 (InjLV #()%V)
     | InjR "x" =>
       match: ! #l_sim with
         InjL <> =>
           let: "m'" := #()%V;; rand(#lbl:α) #(S n'') in
           let: "mA" := vexp g "m'" in
           #l_sim <- InjR "m'";; 
           (λ: "m", do: leakauth2 Send "m")%V (InjL ("mA", bob));; kont0 #()%V
       | InjR "m" => kont0 #()%V
       end
     end)%E).
            About brel_bind''.
            set (keytheory := iLblSig_to_iLblThy [([keyleak1], [keyleak2], keyleak keyleak1 keyleak2)]).
            set (leaktheory := (iLblSig_to_iLblThy [([leakauth1], [leakauth2], leakauth leakauth1 leakauth2)])).
            About leaktheory.
            (*set (M := [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], iThyBot Σ)]).*)
            About brel_bind''.
            set (M := [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)] ++ leaktheory ++ (iLblSig_to_iLblThy L)).
            set (N := [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)] ++ keytheory ++ leaktheory ++ (iLblSig_to_iLblThy L)).
           (* iApply (brel_bind'' [HandleCtx Deep _ _ _ _; AppRCtx _] [AppRCtx _] keytheory [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], iThyBot)] (([leakauth1], [leakauth2], leakauth leakauth1 leakauth2) :: iLblSig_to_iLblThy L)  (λ v1 v2 : val, ⌜v1 = v2⌝%I) (Do keyleak1 (InjLV bob)) (Do keyleak2 (InjLV bob))).*)
            iApply (brel_bind'' [HandleCtx Deep _ _ _ _; AppRCtx _] [AppRCtx _] keytheory M N (𝟙%T) (Do keyleak1 (InjLV bob)) (Do keyleak2 (InjLV bob))).
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
                (*About brel_learn.*)
                About distinct'.
                (*iAssert (distinct' (LblClients ++ L)) as "%Hdistinct".*)
                iAssert (distinct' N) as "%Hdistinct".
                { unfold N. admit. }
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
                        unfold distinct_l in H1. (*unfold LblClients in H1. simpl in H1.*)
                        unfold N in H1. simpl in H1.
                        repeat (rewrite -> labels_l_cons in H1).
                        eapply NoDup_app in H1.
                        eapply NoDup_cons_1_1. destruct H1 as [H1' H2'].
                        apply (NoDup_app [channel'; getKey'] [schannel_l]) in H1'.
                        destruct H1' as [H1' H2'']. apply H1'.}
                      { simpl.
                        iApply (brel_na_inv _ _ alphaN); first set_solver.
                        iFrame "Hinvα".
                        iIntros "([ (>Hα & >Hl_sim & >Hl_auth) | (#>Hα & #>Hl_sim & #>Hl_auth) ] & Hclose)". 
                        (*first message to be sent by the authenticated channel*)
                        - 
                          iApply (brel_load_l _ _ _ [CaseCtx _ _] with "Hl_auth"). 
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
                         (* set (leakatheory := [([leakauth1], [leakauth2],
           iThySum (iThySum LASendAlice LASendBob)
             (iThySum LARecvAlice LARecvBob))]).*)
                          iApply (brel_bind _ _ _ leaktheory N _ (Do leakauth1 (InjLV (xor "x" "m", bob))) (Do leakauth2 (InjLV (vgval (g ^+ n) , bob)))).
                          { simpl. unfold leaktheory. auto.
                            unfold traversable. simpl.
                            About brel_bind.
                            Search traversable.
                            iModIntro.
                            iIntros (e1 e2 Q0).
                             admit. }
                          { simpl. auto. admit. }
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
                            { simpl. auto. (*admit.*) }
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
           { simpl. auto. (*admit.*) }
           { iApply "Hrel". iApply "HmQ". }
           { iApply "IH". }
     (* Recieved by Bob *)
      + iDestruct "HRecvBob" as "[%He1 [%He2 #HmQ]]".
        rewrite -> He1. rewrite -> He2. brel_pures.
        { simpl. admit. }
        { simpl. admit. }
         set (keytheory := iLblSig_to_iLblThy [([keyleak1], [keyleak2], keyleak keyleak1 keyleak2)]).
         set (leaktheory := (iLblSig_to_iLblThy [([leakauth1], [leakauth2], leakauth leakauth1 leakauth2)])).
         set (M := [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)]).
         (* ++ leaktheory ++ (iLblSig_to_iLblThy L)) *)
         set (N := [([channel'; getKey'; schannel_l], [leaksec'; schannel_r], @iThyBot Σ)] ++ keytheory ++ leaktheory ++ (iLblSig_to_iLblThy L)).
       (* set (N := (([channel; getKey1; schannel1], [leaksec; schannel2; getKey2],
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
                 [leaksec; schannel2; getKey2], SecChannelThy)]).*)
        iApply (brel_bind'' _ _ keytheory M N _ (Do keyleak1 (InjLV bob)) (Do keyleak2 (InjLV bob))).
        { simpl. unfold M. admit. }
        { simpl. admit. }
        { admit. }
        {  iApply (brel_introduction' [keyleak1] [keyleak2]).
                1: { unfold keytheory.
                     eapply list_elem_of_here. }
                iExists _, _, [], [],_.
                do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
                iSplitL;  [|by iIntros "!>" (??) "H"; iApply "H"].
                iRight. iLeft. simpl.
                repeat (iSplit; try (iPureIntro); try (unfold SendV); try reflexivity).
                iModIntro. iApply brel_value. 
                iIntros "$ !>". brel_pures.
                iApply (brel_bind'' _ _ keytheory M N _ (Do keyleak1 (InjRV bob)) (Do keyleak2 (InjRV bob))).
                { simpl. unfold M. admit. }
                { simpl. admit. }
                { admit. }
                {  iApply (brel_introduction' [keyleak1] [keyleak2]).
                1: { unfold keytheory.
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
                      { simpl. auto. (*admit.*) }
                      { iApply "Hrel". iApply "HmQ". }
                      { iApply "IH". }
                      (* Key received by Bob *)
                   ++  simpl. admit.
                   ++ (*set (leakauththy := [([leakauth1], [leakauth2],
                       iThySum (iThySum LASendAlice LASendBob) (iThySum LARecvAlice LARecvBob))]).*) 
                      iApply (brel_bind'' _ _ leaktheory M N _ (Do leakauth1 (InjRV bob)) (Do leakauth2 (InjRV bob))).
                      { simpl. admit. }
                      { simpl. admit. }
                      { admit. }
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

 
End schan_security.

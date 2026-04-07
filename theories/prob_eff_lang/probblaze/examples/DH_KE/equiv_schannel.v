From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import  na_invariants.
From iris.algebra Require Import agree excl auth frac excl_auth.
From iris.algebra.lib Require Import dfrac_agree.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode
  spec_rules spec_ra 
  class_instances.
From clutch.prob_eff_lang.probblaze Require Import definition.
From clutch.prob_eff_lang.probblaze Require Import DH_channel.
From clutch.prob_eff_lang.probblaze Require Import s_channel.


Import fingroup.

Import fingroup.fingroup.

Import valgroup_notation.
Import valgroup_tactics.

Section sec_channel_verification.
  Context `{probblazeRGS Σ}.
  Context (channel1 channel2 getKey1 getKey2 : label).
  Context {vg: val_group}.
  Context {cg: clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.
  
  (*Definition atokN : namespace := nroot .@ "atokN".
  Definition btokN : namespace := nroot .@ "btokN".*)



  (*Theories for the interaction of the secure channel with the environment*)
  (*---------------------------------------------------------*)
  Print Val.

 (* Program Definition SendSecBob : iThy Σ :=
  λ e1 e2, (λne Q,
              ∀ m1 m2 : nat,
                ⌜e1 = (do: channel1 (SendV (#m1, bob)))⌝%E ∗ 
                           ⌜ e2 = do: channel2 (SendV (#m2, bob)) ⌝%E ∗ 
                                    □ ((Q (SOMEV #m1) (SOMEV #m2)) /\ Q NONEV NONEV))%I.*)

  Print val.
  Print base_lit.
  Definition leak_or_broadcast (m1 m2 : val) : iProp Σ := ⌜True⌝.
  (*(□ (⌜((m1 = #0)%E /\ (m2 = #0)%E) \/ (∃ n1 n2 : nat, m1 == #(S n1)%E /\ m2 == #(S n2)%E)⌝))%I.*)  

  
  Program Definition SendSecBob : iThy Σ :=
  λ e1 e2, (λne Q,
              ∀ m1 m2 : val,
                ⌜e1 = (do: channel1 (SendV (m1, bob)))⌝%E ∗ 
                           ⌜ e2 = do: channel2 (SendV (m2, bob)) ⌝%E ∗ □ (leak_or_broadcast m1 m2) ∗ 
                                      □ Q (Val #()%V) (Val #()%V))%I.
  Next Obligation. solve_proper. Qed.

  Program Definition SendSecAlice : iThy Σ :=
  λ e1 e2, (λne Q,
              ∀ m1 m2 : val,
                ⌜e1 = (do: channel1 (SendV (m1, alice)))⌝%E ∗ 
                           ⌜ e2 = do: channel2 (SendV (m2, alice)) ⌝%E ∗ □ (leak_or_broadcast m1 m2) ∗ 
                                      □ Q (Val #()%V) (Val #()%V))%I.
  Next Obligation. solve_proper. Qed.
  
  Program Definition RecvSecBob : iThy Σ :=
   λ e1 e2, (λne Q,
                ⌜ e1 = do: channel1 (RecvV bob) ⌝%E ∗
                ⌜ e2 = do: channel2 (RecvV bob) ⌝%E ∗
                □ ((∀ b1 b2 : nat, Q (SOMEV #b1) (SOMEV #b2)) ∧ Q NONEV NONEV)
             )%I.
  Next Obligation. solve_proper. Qed.

  Program Definition RecvSecAlice : iThy Σ :=
     λ e1 e2, (λne Q,
                ⌜ e1 = do: channel1 (RecvV alice) ⌝%E ∗
                ⌜ e2 = do: channel2 (RecvV alice) ⌝%E ∗
                □ ((∀ b1 b2 : nat, Q (SOMEV #b1) (SOMEV #b2)) ∧ Q NONEV NONEV)
             )%I.
  Next Obligation. solve_proper. Qed.
  
  Definition LblEnvSec := [([channel1], [channel2],iThySum (iThySum SendSecBob RecvSecAlice) (iThySum RecvSecBob RecvSecAlice))].

(*Theories for the implementation of the secure channel*)
(*---------------------------------------------------------*)
  Program Definition SendSecBobImpl γtok γfrac γsec ℓ : iThy Σ :=
     λ e1 e2, (λne Q,
                ∃ m m': val, ((|={⊤, ⊤ ∖ ↑ℓ }=> ((own γfrac DfracDiscarded -∗ (|={⊤ ∖ ↑ℓ, ⊤}=> token γtok ∗ own γsec (to_dfrac_agree DfracDiscarded m) ∗ ⌜m = m'⌝)) ∨ |={⊤ ∖ ↑ℓ , ⊤}=> own γfrac DfracDiscarded)) ∗  
                            (⌜ e1 = do: channel1 (SendV (m, alice)) ⌝%E ∗
                             ⌜ e2 = do: channel2 (SendV (m', alice)) ⌝%E)  ∗ 
                            □ (Q (Val #()%V) (Val #()%V)))
             )%I.
  Next Obligation. solve_proper. Qed.
  
  Program Definition SendSecAliceImpl γtok γfrac γsec ℓ : iThy Σ :=
     λ e1 e2, (λne Q,
                ∃ m m' : val, ((|={⊤, ⊤ ∖ ↑ℓ }=> ((own γfrac DfracDiscarded -∗ (|={⊤ ∖ ↑ℓ, ⊤}=> token γtok ∗ own γsec (to_dfrac_agree DfracDiscarded m) ∗ ⌜m = m'⌝)) ∨ |={⊤ ∖ ↑ℓ , ⊤}=> own γfrac DfracDiscarded)) ∗  
                             (⌜ e1 = do: channel1 (SendV (m, bob)) ⌝%E ∗
                              ⌜ e2 = do: channel2 (SendV (m', bob)) ⌝%E)  ∗ 
                             □ (Q (Val #()%V) (Val #()%V)))
             )%I.
  Next Obligation. solve_proper. Qed.
  
  Program Definition RecvSecBobImpl γsec : iThy Σ :=
     λ e1 e2, (λne Q,
                ⌜ e1 = do: channel1 (RecvV bob) ⌝%E ∗
                ⌜ e2 = do: channel2 (RecvV bob) ⌝%E ∗
                □ (Q NONEV NONEV ∗ (∀ m, own γsec (to_dfrac_agree DfracDiscarded m) -∗ Q (SOMEV m) (SOMEV m)))
             )%I.
  Next Obligation. solve_proper. Qed. 
    
  Program Definition RecvSecAliceImpl γsec : iThy Σ :=
     λ e1 e2, (λne Q,
                 ⌜ e1 = do: channel1 (RecvV alice) ⌝%E ∗
                 ⌜ e2 = do: channel2 (RecvV alice) ⌝%E ∗
                 □ (Q NONEV NONEV ∗ (∀ m, own γsec (to_dfrac_agree DfracDiscarded m) -∗ Q (SOMEV m) (SOMEV m)))
             )%I.
  Next Obligation. solve_proper. Qed.



  Definition LblSecChannel γtoka atokN γfraca γseca γsecb : iLblThy Σ :=
    [([channel1],[channel2], (iThySum (SendSecAliceImpl γtoka γfraca γseca atokN) (RecvSecBobImpl γsecb)))].
                            (*    (iThySum (SendSecBobImpl γtokb γfracb γsecb btokN) (RecvSecAliceImpl γseca))))].*)

(*Verification of F_OAUTH[F_KE[CHAN[]]] ≤ CHAN_SIM[F_CHAN[]]*)
(*----------------------------------------------------------*)
Lemma F_KE_CHAN_SIM f1 f2 γtoka γfraca γseca γsecb L :
    let LblThy := LblSecChannel γtoka atokN γfraca γseca γsecb in
    is_closed_expr ∅ f1 ->
    is_closed_expr ∅ f2 ->
    token γtoka -∗ 
    (*token γtokb -**)
    own γseca (to_dfrac_agree (DfracOwn 1) #()%V) -∗ 
    own γsecb (to_dfrac_agree (DfracOwn 1) #()%V) -∗ 
    BREL f1 ≤ f2 <| LblThy ++ L |> {{ (λ v1 v2, ⌜ v1 = v2 ⌝)  }} -∗ 
    BREL (F_OAUTH channel1 (DH_KE getKey1 channel1 (CHAN getKey1 channel1 f1)))
    ≤ CHAN_SIM channel2 (F_CHAN channel2 f2)<| LblEnvSec ++ L |> {{ (λ v1 v2, ⌜ v1 = v2 ⌝) }}.
Proof.
Admitted.




(*Verification of CHAN_SIM[F_CHAN[]] ≤ F_OAUTH[F_KE[CHAN[]]]*)
(*---------------------------------------------------------*)
Lemma SIM_F_KE_CHAN f1 f2 γtoka γfraca γseca γsecb L :
    let LblThy := LblSecChannel γtoka atokN γfraca γseca γsecb in
    is_closed_expr ∅ f1 ->
    is_closed_expr ∅ f2 ->
    token γtoka -∗ 
    (*token γtokb -**)
    own γseca (to_dfrac_agree (DfracOwn 1) #()%V) -∗ 
    own γsecb (to_dfrac_agree (DfracOwn 1) #()%V) -∗ 
    BREL f1 ≤ f2 <| LblThy ++ L |> {{ (λ v1 v2, ⌜ v1 = v2 ⌝)  }} -∗ 
    BREL (CHAN_SIM channel1 (F_CHAN channel1 f1))
    ≤ (F_OAUTH channel2 (DH_KE getKey2 channel2 (CHAN getKey2 channel2 f2))) <| LblEnvSec ++ L |> {{ (λ v1 v2, ⌜ v1 = v2 ⌝) }}.
Proof.
Admitted.   

End sec_channel_verification.

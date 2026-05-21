From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import agree excl auth frac excl_auth.
From iris.algebra.lib Require Import dfrac_agree.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode
  spec_rules spec_ra class_instances.
From clutch.prob_eff_lang.probblaze Require Import tactics.
From clutch.prob_eff_lang.probblaze Require Export notation valgroup.
From clutch.prob_eff_lang.probblaze Require Export definition.
From clutch.prob_eff_lang.probblaze Require Export s_channel.
From clutch.prob_eff_lang.probblaze Require Export equiv_schannel.
From clutch.prob_eff_lang.probblaze Require Export DH_channel.

Import fingroup.
Import fingroup.fingroup.

Import valgroup_notation.
Import valgroup_tactics.

Section compositional_verification.
  Context `{probblazeRGS Σ}.
  Context (channel leaksec channel1 channel2 getKey1 getKey2 leakauth1 leakauth2 keyleak1 keyleak2 schannel1 schannel2 l1 l2 l2': label).
  Context {vg: val_group}.
  Context {cg: clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg: @val_group_generator vg}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO,!inG Σ (dfrac_agreeR valO)}.
  
  (* F_OAUTH[ F_AUTH [DH_KE [CHAN []]]] ≤ F_OAUTH[ F_AUTH [C[DH_real][CHAN []]]] *)
  (*---------------------------------------------------------------------------*)
  Lemma F_OAUTH_DHKE_C_REAL f1 f2 L :
    is_closed_expr ∅ f1 ->
    is_closed_expr ∅ f2 -> 
    BREL f1 ≤ f2 <| (LblClients channel1 channel2 getKey1 getKey2 schannel1 schannel2) ++ L |> {{ (λ v1 v2, ⌜ v1 = v2 ⌝)}} -∗
    BREL (F_OAUTH leakauth1 channel1 (F_AUTH l2 (DH_KE getKey1 l2 (CHAN getKey1 schannel1 channel1 f1)))) ≤ (F_OAUTH leakauth2 channel2 (F_AUTH l2' (C getKey2 l2' DH_real (CHAN getKey2 schannel2 channel2 f2)))) <| (LblEnvSec channel1 channel2 getKey1 getKey2 leakauth1 leakauth2 l2 l2' schannel1 schannel2) ++ L |> {{ (λ v1 v2, ⌜ v1 = v2 ⌝) }}.
  Proof.
  Admitted.

  (*F_OAUTH [ F_AUTH [C[DH_real][CHAN[]]]] ≤ F_OAUTH[ F_AUTH [DH_KE [CHAN []]]] *)
  (*----------------------------------------------------------------------------*)
  Lemma C_REAL_DHKE_F_OAUTH f1 f2 L :
    is_closed_expr ∅ f1 ->
    is_closed_expr ∅ f2 ->
    BREL f1 ≤ f2 <| (LblClients channel1 channel2 getKey1 getKey2 schannel1 schannel2) ++ L |> {{ (λ v1 v2, ⌜ v1 = v2 ⌝) }} -∗
    BREL (F_OAUTH leakauth1 channel1 (F_AUTH l2 (C getKey1 l2 DH_real (CHAN getKey1 schannel1 channel1 f1)))) ≤ (F_OAUTH leakauth2 channel2 (F_AUTH l2' (DH_KE getKey2 l2' (CHAN getKey2 schannel2 channel2 f2)))) <| (LblEnvSec channel1 channel2 getKey1 getKey2 leakauth1 leakauth2 l2 l2' schannel1 schannel2) ++ L |>{{ (λ v1 v2, ⌜ v1 = v2 ⌝) }}.
  Proof.
  Admitted.

  (*F_OAUTH [F_AUTH [C[DH_real][CHAN[]]]] ≤ F_OAUTH [F_AUTH [C[DH_rand][CHAN[]]]]*)
  (*-----------------------------------------------------------------------------*)
  Lemma C_REAL_DH_RAND f1 f2 L :
    is_closed_expr ∅ f1 ->
    is_closed_expr ∅ f2 ->
    BREL f1 ≤ f2 <| (LblClients channel1 channel2 getKey1 getKey2 schannel1 schannel2) ++ L |> {{ (λ v1 v2, ⌜ v1 = v2 ⌝)}} -∗
    BREL (F_OAUTH leakauth1 channel1 (F_AUTH l2 (C getKey1 l2 DH_real (CHAN getKey1 schannel1 channel1 f1)))) ≤
      (F_OAUTH leakauth2 channel2 (F_AUTH l2' (C getKey2 l2' DH_rand (CHAN getKey2 schannel2 channel2 f2)))) <| (LblEnvSec channel1 channel2 getKey1 getKey2 leakauth1 leakauth2 l2 l2' schannel1 schannel2) ++ L |> {{(λ v1 v2, ⌜ v1 = v2 ⌝) }}.
  Proof.
  Admitted.
  
  (*F_OAUTH [F_AUTH [C[DH_rand][CHAN[]]]] ≤ F_OAUTH [F_AUTH [C[DH_real][CHAN[]]]]*)
  (*----------------------------------------------------------------------------*)
  Lemma C_DH_RAND_REAL f1 f2 L :
    is_closed_expr ∅ f1 ->
    is_closed_expr ∅ f2 ->
    BREL f1 ≤ f2 <| (LblClients channel1 channel2 getKey1 getKey2 schannel1 schannel2) ++ L |> {{ (λ v1 v2, ⌜ v1 = v2 ⌝)}} -∗
    BREL (F_OAUTH leakauth1 channel1 (F_AUTH l2 (C getKey1 l2 DH_rand (CHAN getKey1 schannel1 channel1 f1)))) ≤
      (F_OAUTH leakauth2 channel2 (F_AUTH l2' (C getKey2 l2' DH_real (CHAN getKey2 schannel2 channel2 f2)))) <| (LblEnvSec channel1 channel2 getKey1 getKey2 leakauth1 leakauth2 l2 l2' schannel1 schannel2) ++ L |> {{(λ v1 v2, ⌜ v1 = v2 ⌝) }}.
  Proof.
  Admitted.


  

  (*F_OAUTH [F_AUTH [DH_KE [CHAN[]]]] ≤ F_AUTH [ DH_SIM [CHAN_SIM [F_CHAN[]]]]  *)
  (*---------------------------------------------------------------------------*)
  (*Note that DH_SIM and F_AUTH raise and catch the same effect, which in the setting of the secure channel can represent either a keyleak(if being caught) or a leak of the authenticated channel(if being raised). In the statement below they are ALL rperesented by the labels l2 and l2' on either side *)
  
Lemma SEC_CHAN_DH_KE f1 f2 L :
  is_closed_expr ∅ f1 ->
  is_closed_expr ∅ f2 ->
  BREL f1 ≤ f2 <| (LblClients channel leaksec getKey1 getKey2 schannel1 schannel2) ++ L |> {{ (λ v1 v2, ⌜ v1 = v2 ⌝) }} -∗
  BREL (F_OAUTH leakauth1 channel (F_AUTH l2 (DH_KE getKey1 l2 (CHAN getKey1 schannel1 channel f1) ) )) ≤ (F_AUTH l2' (DH_SIM l2' (CHAN_SIM leakauth2 l2' leaksec (F_CHAN schannel2 leaksec f2)))) <| (LblEnvSec channel leaksec getKey1 getKey2 leakauth1 leakauth2 l2 l2' schannel1 schannel2) ++ L |> {{ (λ v1 v2, ⌜ v1 = v2⌝) }}.
Proof.
  iIntros "%Hf1 %Hf2 Hrelf1f2".
  
Admitted.

(*F_AUTH[ DH_SIM [CHAN_SIM [F_CHAN[]]]] ≤ F_OAUTH [F_AUTH [DH_KE [CHAN[]]]] *)
(*--------------------------------------------------------------------------*)
Lemma DH_KE_SEC_CHAN f1 f2 L :
  is_closed_expr ∅ f1 ->
  is_closed_expr ∅ f2 ->
  BREL f1 ≤ f2 <| (LblClients' channel leaksec getKey1 getKey2 schannel1 schannel2) |> {{ (λ v1 v2, ⌜ v1 = v2 ⌝)}} -∗
  BREL (F_AUTH l2 (DH_SIM l2 (CHAN_SIM leakauth1 l2 leaksec (F_CHAN schannel1 leaksec f1)))) ≤ (F_OAUTH leakauth2 channel (F_AUTH l2' (DH_KE getKey2 l2' (CHAN getKey2 schannel2 channel f2))))  <| (LblEnvSec leaksec channel getKey1 getKey2 leakauth1 leakauth2 l2 l2' schannel1 schannel2) ++ L |> {{ (λ v1 v2, ⌜ v1 = v2⌝) }}.
Proof.
Admitted.

End compositional_verification.

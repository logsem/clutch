From iris.proofmode Require Import base proofmode classes. 
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import agree excl auth frac excl_auth.
From iris.algebra.lib Require Import dfrac_agree.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode
  spec_rules spec_ra class_instances.
From clutch.prob_eff_lang.probblaze Require Import tactics.
From clutch.prob_eff_lang.probblaze Require Export notation valgroup.
From clutch.prob_eff_lang.probblaze Require Export def_dhke.
From clutch.prob_eff_lang.probblaze Require Export newdef_schan.
From clutch.prob_eff_lang.probblaze Require Export new_schan_ri.
From clutch.prob_eff_lang.probblaze Require Export dhke_channel.
From clutch.prob_eff_lang.probblaze Require Import sem_types sem_row sem_sig sem_judgement sem_def.

Import fingroup.
Import fingroup.fingroup.



Import valgroup_tactics.

Section new_comp_verification.
  Context `{probblazeRGS Σ}.
  Context (channel leaksec channel1 channel2 getKey1 getKey2 leakauth1 leakauth2 keyleak1 keyleak2 schannel1 schannel2 l1 l2 l2': label).
  Context {vg: val_group}.
  Context {cg: clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg: @val_group_generator vg}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO,!inG Σ (dfrac_agreeR valO)}.

  Definition REAL_CHAN_DHKE : val :=
    λ: "f", ((λ: "f", F_AUTH (DH_KE "f"))%V ||ᵣ F_OAUTH) (CHAN "f").

  Definition REAL_CHAN_DH_REAL : val :=
    λ: "f", ( (λ: "f", F_AUTH (C DH_real "f"))%V ||ᵣ F_OAUTH) (CHAN "f").

  Definition REAL_CHAN_DH_RAND : val :=
    λ: "f", ((λ: "f", F_AUTH (C DH_rand "f"))%V ||ᵣ F_OAUTH) (CHAN "f").
  
   (* F_OAUTH[ F_AUTH [DH_KE [CHAN []]]] ≤ F_OAUTH[ F_AUTH [C[DH_real][CHAN []]]] *)
  (*---------------------------------------------------------------------------*)
  Lemma F_OAUTH_DHKE_C_REAL :
    ⊢ sem_val_typed REAL_CHAN_DHKE REAL_CHAN_DH_REAL 
        (* the type should match the program. Look carefully at the order of the incoming effects *)
        (* the type of the client needs to change to a linear function *)
        (∀ᵣ θ__L ,(∀ᵣ θₕ, (((⊤ × (sem_ty_sum 𝟙 𝟙)) -{ θₕ }-> 𝟙) × ((sem_ty_sum 𝟙 𝟙) -{ θₕ }-> (Option  ⊤))) 
                                                                   -{ sem_row_union  θₕ θ__L }-> 𝟙)
                  (* the product needs to be under a bang, since the effects can be used multiple times *)
                                                             ⊸ (∀ᵣ θ₁,∀ᵣ θ2, (((⊤ × (𝟙 + 𝟙)) -{ θ₁ }-> 𝟙) 
                                                                                 × ((𝟙 + 𝟙) -{ θ₁ }-> Option ⊤)) 
                                                                                 ⊸ (((⊤ × (𝟙 + 𝟙)) -{ θ2 }-> 𝟙) 
                                                                                 × ((𝟙 + 𝟙) -{ θ2 }-> Option ⊤)) -{ sem_row_union θ₁ (sem_row_union θ2 θ__L) }-∘ 𝟙))%T.
  Proof. 
    iApply func_comp_left.
    - admit.                    (* closed expressions *)
    - admit.                    (* closed expressions *)
    - iIntros (θ). iApply parallel_comp_right.
      + unfold τ__F. unshelve iApply F_AUTH_DH_KE_FAUTH_C_DH_real; try done. 
      + admit.                  (* F_OAUTH well-typed *)
    - admit.                    (* CHAN well-typed *)
  Admitted. 
   
 (* Lemma F_OAUTH_DHKE_C_REAL' (f1 f2 : val) (L : sem_row Σ) :
    sem_val_typed f1 f2 (∀ᵣ θₕ, (((⊤ × (sem_ty_sum 𝟙 𝟙)) -{ θₕ }-> (Option  ⊤)) × ((sem_ty_sum 𝟙 𝟙) -{ θₕ }-> (Option  ⊤))) -{ sem_row_union  θₕ L }-> 𝟙)%T -∗    
    BREL (REAL_CHAN_DHKE f1) ≤ (REAL_CHAN_DH_REAL f2)
     <|⊥|> {{λ v1 v2,
                                       ∀ (leakauth1 leakauth2 keyleak1 keyleak2 : label),
               BREL v1 ((λ: "m", do: leakauth1 (Send "m")), (λ: "m", do: leakauth1 (Recv "m")))%V (λ: "m", do: keyleak1 "m")%V ≤ v2 ((λ: "m", do: leakauth2 (Send "m")), (λ: "m", do: leakauth2 (Recv "m")))%V (λ: "m", do: keyleak2 "m")%V <| (iLblSig_to_iLblThy (envsec_row keyleak1 keyleak2 leakauth1 leakauth2 )) ++ (iLblSig_to_iLblThy L) |> {{ (λ w1 w2, 𝟙%T w1 w2)}}}}.
  Proof.
  Admitted.*)

   (*F_OAUTH [ F_AUTH [C[DH_real][CHAN[]]]] ≤ F_OAUTH[ F_AUTH [DH_KE [CHAN []]]] *)
  (*----------------------------------------------------------------------------*)
 (* Lemma C_REAL_DHKE_F_OAUTH (f1 f2 : val) (L : sem_row Σ) :
    sem_val_typed f1 f2 (∀ᵣ θₕ, (((⊤ × (sem_ty_sum 𝟙 𝟙)) -{ θₕ }-> (Option  ⊤)) × ((sem_ty_sum 𝟙 𝟙) -{ θₕ }-> (Option  ⊤))) -{ sem_row_union  θₕ L }-> 𝟙)%T -∗    
    BREL (REAL_CHAN_DH_REAL f1) ≤ (REAL_CHAN_DHKE f2)
     <|⊥|> {{λ v1 v2,
                                       ∀ (leakauth1 leakauth2 keyleak1 keyleak2 : label),
               BREL v1 ((λ: "m", do: leakauth1 (Send "m")), (λ: "m", do: leakauth1 (Recv "m")))%V (λ: "m", do: keyleak1 "m")%V ≤ v2 ((λ: "m", do: leakauth2 (Send "m")), (λ: "m", do: leakauth2 (Recv "m")))%V (λ: "m", do: keyleak2 "m")%V <| (iLblSig_to_iLblThy (envsec_row keyleak1 keyleak2 leakauth1 leakauth2 )) ++ (iLblSig_to_iLblThy L) |> {{ (λ w1 w2, 𝟙%T w1 w2)}}}}.
  Proof.
  Admitted.*)

  Lemma C_REAL_DHKE_F_OAUTH :
     ⊢ sem_val_typed REAL_CHAN_DH_REAL REAL_CHAN_DHKE (∀ᵣ θ__L ,(∀ᵣ θₕ, (((⊤ × (sem_ty_sum 𝟙 𝟙)) -{ θₕ }-> 𝟙) × ((sem_ty_sum 𝟙 𝟙) -{ θₕ }-> (Option  ⊤))) 
                                                                   -{ sem_row_union  θₕ θ__L }-> 𝟙)
                                                             ⊸ (∀ᵣ θ₁,∀ᵣ θ2, (((⊤ × (𝟙 + 𝟙)) -{ θ₁ }-> 𝟙) 
                                                                                 × ((𝟙 + 𝟙) -{ θ₁ }-> Option ⊤)) 
                                                                                 ⊸ (((⊤ × (𝟙 + 𝟙)) -{ θ2 }-> 𝟙) 
                                                                                 × ((𝟙 + 𝟙) -{ θ2 }-> Option ⊤)) -{ sem_row_union θ₁ (sem_row_union θ2 θ__L) }-∘ 𝟙))%T.
  Proof. 
    iApply func_comp_left.
    - admit.                    (* closed expressions *)
    - admit.                    (* closed expressions *)
    - iIntros (θ). iApply parallel_comp_right.
      + unfold τ__F. iApply F_AUTH_C_DH_real_FAUTH_DH_KE; try done.
      + admit.                  (* F_OAUTH well-typed *)
    - admit.                    (* CHAN well-typed *)
  Admitted. 

  (*F_OAUTH [F_AUTH [C[DH_real][CHAN[]]]] ≤ F_OAUTH [F_AUTH [C[DH_rand][CHAN[]]]]*)
  (*-----------------------------------------------------------------------------*)
  (* Lemma C_REAL_DH_RAND :
       ⊢ sem_val_typed REAL_CHAN_DH_REAL REAL_CHAN_DH_RAND (∀ᵣ θ__L ,(∀ᵣ θₕ, (((⊤ × (sem_ty_sum 𝟙 𝟙)) -{ θₕ }-> 𝟙) × ((sem_ty_sum 𝟙 𝟙) -{ θₕ }-> (Option  ⊤))) 
                                                                      -{ sem_row_union  θₕ θ__L }-> 𝟙)
                                                                ⊸ (∀ᵣ θ₁,∀ᵣ θ2, (((⊤ × (𝟙 + 𝟙)) -{ θ₁ }-> 𝟙) 
                                                                                    × ((𝟙 + 𝟙) -{ θ₁ }-> Option ⊤)) 
                                                                                    ⊸ (((⊤ × (𝟙 + 𝟙)) -{ θ2 }-> 𝟙) 
                                                                                    × ((𝟙 + 𝟙) -{ θ2 }-> Option ⊤)) -{ sem_row_union θ₁ (sem_row_union θ2 θ__L) }-∘ 𝟙))%T.
     Proof.
       iApply func_comp_left.
       - admit.
       - admit.
       - iIntros (θ). iApply parallel_comp_right. *)


  (*F_OAUTH [F_AUTH [C[DH_rand][CHAN[]]]] ≤ F_OAUTH [F_AUTH [C[DH_real][CHAN[]]]]*)
  (*----------------------------------------------------------------------------*)
  (* Lemma C_DH_RAND_REAL (f1 f2 : val) (L : sem_row Σ) :
       sem_val_typed f1 f2 (∀ᵣ θₕ, (((⊤ × (sem_ty_sum 𝟙 𝟙)) -{ θₕ }-> (Option  ⊤)) × ((sem_ty_sum 𝟙 𝟙) -{ θₕ }-> (Option  ⊤))) -{ sem_row_union  θₕ L }-> 𝟙)%T -∗    
       BREL (REAL_CHAN_DH_RAND f1) ≤ (REAL_CHAN_DH_REAL f2)
        <|⊥|> {{λ v1 v2,
                                          ∀ (leakauth1 leakauth2 keyleak1 keyleak2 : label),
                  BREL v1 ((λ: "m", do: leakauth1 (Send "m")), (λ: "m", do: leakauth1 (Recv "m")))%V (λ: "m", do: keyleak1 "m")%V ≤ v2 ((λ: "m", do: leakauth2 (Send "m")), (λ: "m", do: leakauth2 (Recv "m")))%V (λ: "m", do: keyleak2 "m")%V <| (iLblSig_to_iLblThy (envsec_row keyleak1 keyleak2 leakauth1 leakauth2 )) ++ (iLblSig_to_iLblThy L) |> {{ (λ w1 w2, 𝟙%T w1 w2)}}}}.
     Proof.
     Admitted. *)

 (*  Definition F_AUTH_DH_KE : val :=
       λ: "f",
         (F_AUTH ||ₗ DH_KE) (CHAN "f").
    
     
      (*F_OAUTH [F_AUTH [DH_KE [CHAN[]]]] ≤ F_AUTH [ DH_SIM [CHAN_SIM [F_CHAN[]]]]  *)
     (*---------------------------------------------------------------------------*)
    Lemma SEC_CHAN_DH_KE (f1 f2 : val) (L : sem_row Σ) :
       sem_val_typed f1 f2 (∀ᵣ θₕ, (((⊤ × (sem_ty_sum 𝟙 𝟙)) -{ θₕ }-> (Option  ⊤)) × ((sem_ty_sum 𝟙 𝟙) -{ θₕ }-> (Option  ⊤))) -{ sem_row_union  θₕ L }-> 𝟙)%T -∗    
       BREL (F_OAUTH (F_AUTH_DH_KE f1)) ≤ (F_AUTH (DH_SIM (CHAN_SIM (F_CHAN f2))))
        <|⊥|> {{λ v1 v2,
                                          ∀ (leakauth1 leakauth2 keyleak1 keyleak2 : label),
                  BREL v1 ((λ: "m", do: leakauth1 (Send "m")), (λ: "m", do: leakauth1 (Recv "m")))%V (λ: "m", do: keyleak1 "m")%V ≤ v2 ((λ: "m", do: leakauth2 (Send "m")), (λ: "m", do: leakauth2 (Recv "m")))%V (λ: "m", do: keyleak2 "m")%V <| (iLblSig_to_iLblThy (envsec_row keyleak1 keyleak2 leakauth1 leakauth2 )) ++ (iLblSig_to_iLblThy L) |> {{ (λ w1 w2, 𝟙%T w1 w2)}}}}.
     Proof.
     Admitted.
    
     (*F_AUTH[ DH_SIM [CHAN_SIM [F_CHAN[]]]] ≤ F_OAUTH [F_AUTH [DH_KE [CHAN[]]]] *)
     (*--------------------------------------------------------------------------*)
    Lemma DH_KE_SEC_CHAN  (f1 f2 : val) (L : sem_row Σ) :
       sem_val_typed f1 f2 (∀ᵣ θₕ, (((⊤ × (sem_ty_sum 𝟙 𝟙)) -{ θₕ }-> (Option  ⊤)) × ((sem_ty_sum 𝟙 𝟙) -{ θₕ }-> (Option  ⊤))) -{ sem_row_union  θₕ L }-> 𝟙)%T -∗    
       BREL (F_AUTH (DH_SIM (CHAN_SIM (F_CHAN f1)))) ≤  (F_OAUTH (F_AUTH_DH_KE f1))
        <|⊥|> {{λ v1 v2,
                                          ∀ (leakauth1 leakauth2 keyleak1 keyleak2 : label),
                  BREL v1 ((λ: "m", do: leakauth1 (Send "m")), (λ: "m", do: leakauth1 (Recv "m")))%V (λ: "m", do: keyleak1 "m")%V ≤ v2 ((λ: "m", do: leakauth2 (Send "m")), (λ: "m", do: leakauth2 (Recv "m")))%V (λ: "m", do: keyleak2 "m")%V <| (iLblSig_to_iLblThy (envsec_row keyleak1 keyleak2 leakauth1 leakauth2 )) ++ (iLblSig_to_iLblThy L) |> {{ (λ w1 w2, 𝟙%T w1 w2)}}}}.
     Proof.
     Admitted. *)

  Definition bla0 : val :=
    (λ: "f", ((λ: "f", F_AUTH (DH_SIM (F_KE "f")))%V ||ᵣ F_OAUTH) (CHAN "f")). 

  Definition bla1 : val :=
    (λ: "f", ((λ: "f", (λ: "f", F_AUTH (DH_SIM "f"))%V (F_KE "f"))%V ||ᵣ F_OAUTH) (CHAN "f")). 

  Definition bla2 : val :=
    (λ: "f", (λ: "f" "rF" "rH", (λ: "f", F_AUTH (DH_SIM "f"))%V (λ: "rG", (F_KE ||ᵣ F_OAUTH)%V "f" "rH" "rG") "rF") (CHAN "f")).

  Definition bla3 : val :=
    (λ: "f" "rF" "rH", (λ: "f", F_AUTH (DH_SIM "f"))%V (λ: "rG", (λ: "f", (F_KE ||ᵣ F_OAUTH)%V (CHAN "f")) "f" "rH" "rG") "rF"). 

  Lemma REAL_CHAN_DH_RAND_bla : 
    ⊢ sem_val_typed REAL_CHAN_DH_RAND bla0 (∀ᵣ θ__L ,(∀ᵣ θₕ, (((⊤ × (sem_ty_sum 𝟙 𝟙)) -{ θₕ }-> 𝟙) × ((sem_ty_sum 𝟙 𝟙) -{ θₕ }-> (Option  ⊤))) 
                                                                   -{ sem_row_union  θₕ θ__L }-> 𝟙)
                                                             ⊸ (∀ᵣ θ1,∀ᵣ θ2, (((⊤ × (𝟙 + 𝟙)) -{ θ1 }-> 𝟙) 
                                                                                 × ((𝟙 + 𝟙) -{ θ1 }-> Option ⊤)) 
                                                                                 ⊸ (((⊤ × (𝟙 + 𝟙)) -{ θ2 }-> 𝟙) 
                                                                                 × ((𝟙 + 𝟙) -{ θ2 }-> Option ⊤)) -{ sem_row_union θ1 (sem_row_union θ2 θ__L) }-∘ 𝟙))%T.
  Proof.
    iApply func_comp_left.
    - admit.
    - admit.
    - iIntros (θ). iApply parallel_comp_right. 
      + iApply F_AUTH_C_DH_rand_FAUTH_DH_SIM_F_KE; try done.
      + admit.
    - admit.
  Admitted. 
        
  Lemma bla0_bla1 : 
    ⊢ sem_val_typed bla0 bla1 (∀ᵣ θ__L ,(∀ᵣ θₕ, (((⊤ × (sem_ty_sum 𝟙 𝟙)) -{ θₕ }-> 𝟙) × ((sem_ty_sum 𝟙 𝟙) -{ θₕ }-> (Option  ⊤))) 
                                                                   -{ sem_row_union  θₕ θ__L }-> 𝟙)
                                                             ⊸ (∀ᵣ θ1,∀ᵣ θ2, (((⊤ × (𝟙 + 𝟙)) -{ θ1 }-> 𝟙) 
                                                                                 × ((𝟙 + 𝟙) -{ θ1 }-> Option ⊤)) 
                                                                                 ⊸ (((⊤ × (𝟙 + 𝟙)) -{ θ2 }-> 𝟙) 
                                                                                 × ((𝟙 + 𝟙) -{ θ2 }-> Option ⊤)) -{ sem_row_union θ1 (sem_row_union θ2 θ__L) }-∘ 𝟙))%T.
  Proof.
    iApply func_comp_left.
    - admit.
    - admit.
    - iIntros (θ). iApply parallel_comp_right.
      + unfold τ__F. iApply func_comp_assoc.
        * admit.
        * admit.
        * admit.
      + admit.
    - admit.
  Admitted. 
        
  Lemma bla1_bla2 :
    ⊢ sem_val_typed bla1 bla2 (∀ᵣ θ__L ,(∀ᵣ θₕ, (((⊤ × (sem_ty_sum 𝟙 𝟙)) -{ θₕ }-> 𝟙) × ((sem_ty_sum 𝟙 𝟙) -{ θₕ }-> (Option  ⊤))) 
                                                                   -{ sem_row_union  θₕ θ__L }-> 𝟙)
                                                             ⊸ (∀ᵣ θ1,∀ᵣ θ2, (((⊤ × (𝟙 + 𝟙)) -{ θ1 }-> 𝟙) 
                                                                                 × ((𝟙 + 𝟙) -{ θ1 }-> Option ⊤)) 
                                                                                 ⊸ (((⊤ × (𝟙 + 𝟙)) -{ θ2 }-> 𝟙) 
                                                                                 × ((𝟙 + 𝟙) -{ θ2 }-> Option ⊤)) -{ sem_row_union θ1 (sem_row_union θ2 θ__L) }-∘ 𝟙))%T.
  Proof.
    (* All admits are well-typedness *)
    iApply func_comp_left.
    - admit.                    (* closed expr *)
    - admit.                    (* closed expr *)
    - iIntros (θ). iApply func_comp_parallel_comp_assoc.
      + admit.
      + admit.
      + admit.
    - admit.
  Admitted.
  
  Lemma bla2_bla3 :
    ⊢ sem_val_typed bla2 bla3 (∀ᵣ θ__L ,(∀ᵣ θₕ, (((⊤ × (sem_ty_sum 𝟙 𝟙)) -{ θₕ }-> 𝟙) × ((sem_ty_sum 𝟙 𝟙) -{ θₕ }-> (Option  ⊤))) 
                                              -{ sem_row_union  θₕ θ__L }-> 𝟙)
                                        ⊸ (∀ᵣ θ1,∀ᵣ θ2, (((⊤ × (𝟙 + 𝟙)) -{ θ1 }-> 𝟙) 
                                                           × ((𝟙 + 𝟙) -{ θ1 }-> Option ⊤)) 
                                                          ⊸ (((⊤ × (𝟙 + 𝟙)) -{ θ2 }-> 𝟙) 
                                                               × ((𝟙 + 𝟙) -{ θ2 }-> Option ⊤)) -{ sem_row_union θ1 (sem_row_union θ2 θ__L) }-∘ 𝟙))%T.
  Proof. 
    unfold bla2, bla3.
    iApply functionality_comp_func_comp_assoc.
  Qed. 

  Lemma 

                      

End new_comp_verification.


From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From clutch.prob_eff_lang.hazel_prob Require Import interp model typed_lang spec_ra 
                            deep_handler iEff protocol_agreement
                            notation weakestpre lang spec_rules
                            primitive_laws spec_tactics class_instances
                            coupling_rules shallow_handler.
Set Default Proof Using "Type*".
  
Section eff_rand_ordering.
  Context `{probeffRGS Σ}.


  Definition prog1 (n : nat) : expr :=
    (deep_try_with
      (λ: <> , let: "a" := rand #n in do: "a")%V
      (λ:"v" "k", let b := do: "v" in "k" b)%V
      (λ: "v", "v")%V)%E.

  Definition prog2 (n : nat) : expr :=
    ( (* (let: "α" := alloc #n in *)
    deep_try_with
      (λ: <>, do: #())%V
      (λ: "v" "k", let b := do: (rand #n) in "k" b)%V
      (λ: "v", "v")%V).

  (* TODO: clean up proof and write ewp tactics *)
  Theorem eff_rand_reordering (n : nat) :
   ⊢ prog1 n <<{ ⟦ .< TNat ; TNat .> TNat ⟧ₑ [] }<< prog2 n .
  Proof. 
    iIntros (K K') "HKK". rewrite obs_refines_eq.
    iIntros (ε) "Hj". iIntros "Herr". iIntros (Hpos).
    unfold prog1, prog2.
    iApply ewp_pure_step. { apply pure_prim_step_fill. apply (pure_prim_step_fill [AppLCtx _; AppLCtx _]). apply pure_prim_step_beta. } simpl.
    iApply ewp_pure_step. { apply pure_prim_step_fill. apply (pure_prim_step_fill [AppLCtx _; AppLCtx _ ]). apply pure_prim_step_rec. } simpl.
    iApply ewp_pure_step. { apply pure_prim_step_fill. apply (pure_prim_step_fill [AppLCtx _ ]). apply pure_prim_step_beta. } simpl.
    iApply ewp_pure_step. { apply pure_prim_step_fill. apply (pure_prim_step_fill [AppLCtx _]). apply pure_prim_step_rec. } simpl.
    iApply ewp_pure_step. { apply pure_prim_step_fill. apply pure_prim_step_beta. } simpl.
    iApply ewp_pure_step. { apply pure_prim_step_fill. apply (pure_prim_step_fill [TryWithCtx _ _]). apply pure_prim_step_beta. } simpl.
    iApply (ewp_pure_bind ([AppRCtx _; TryWithCtx _ _] ++ K) _ _ _ (rand #n) ). { done. }
    unfold deep_try_with.
    iApply spec_update_ewp.
    tp_pures.
    iMod (step_pure _ ([TryWithCtx _ _] ++ K') with "[$Hj]") as "Hj"; [done|simpl].
    iMod (step_pure _ ([TryWithCtx _ _] ++ K') with "[$Hj]") as "Hj"; [done|simpl].
    tp_pures.
    iModIntro.
    iApply (ewp_couple_rand_rand _ _ _ ([DoCtx; AppRCtx _] ++ K') with "[$Hj]"); [done|].
    iNext.
    iIntros (m) "(%Hlt &Hj)". simpl.
    iApply spec_update_ewp.
    tp_pures.
    iMod (step_pure _ K' _ _ _ 1 with "[$Hj]") as "Hj"; [apply I| |].
    { apply (@pure_eff (AppRCtx _)). apply AppRCtx_neutral. }
    rewrite app_nil_l.
    iModIntro.
    fold deep_try_with.
    iApply ewp_pure_step. { apply pure_prim_step_fill. apply (pure_prim_step_fill [TryWithCtx _ _]).
                            apply (pure_prim_step_fill [AppLCtx _]). apply pure_prim_step_rec. }
    iApply ewp_pure_step. { apply pure_prim_step_fill. apply (pure_prim_step_fill [TryWithCtx _ _]). apply pure_prim_step_beta. } simpl.
    iApply ewp_pure_step. { apply pure_prim_step_fill. apply (pure_prim_step_fill [TryWithCtx _ _]). apply pure_prim_step_do. } simpl.
    iApply ewp_pure_step. { apply pure_prim_step_fill. apply pure_prim_step_try_with_eff. }
    iApply ewp_pure_step. { apply pure_prim_step_fill. apply (pure_prim_step_fill [AppLCtx _; AppLCtx _]). apply pure_prim_step_rec. }
    iApply ewp_pure_step. { apply pure_prim_step_fill. apply (pure_prim_step_fill [AppLCtx _]). apply pure_prim_step_beta. } simpl.
    iApply ewp_pure_step. { apply pure_prim_step_fill. apply (pure_prim_step_fill [AppLCtx _]). apply pure_prim_step_rec. }
    iApply ewp_pure_step. { apply pure_prim_step_fill. apply pure_prim_step_beta. } simpl.
    iApply ewp_pure_step. { apply pure_prim_step_fill. apply (pure_prim_step_fill [AppRCtx _]). apply pure_prim_step_rec. } simpl.
    iApply ewp_pure_step. { apply pure_prim_step_fill. apply (pure_prim_step_fill [AppLCtx _]). apply pure_prim_step_beta. } simpl.
    iApply ewp_pure_step. { apply pure_prim_step_fill. apply (pure_prim_step_fill [AppLCtx _]). apply pure_prim_step_rec. } simpl.
    iApply ewp_pure_step. { apply pure_prim_step_fill. apply pure_prim_step_beta. } simpl.
    iApply ewp_pure_step. { apply pure_prim_step_fill. apply (pure_prim_step_fill [AppRCtx _]). apply pure_prim_step_do. } simpl.
    iApply ewp_pure_step. { apply pure_prim_step_fill. apply (pure_prim_step_eff (AppRCtx _)). } rewrite app_nil_l.
    rewrite {1}/ectxRel_car //=.
    iDestruct "HKK" as "(_&HKK)".
    rewrite obs_refines_eq.
    iApply ("HKK" with "[][$Hj][$Herr]"); [|done].
    iApply (eff_refines_intro _ _ _ #m #m [AppRCtx _] [AppRCtx _]); [done|done|eauto|].
    iModIntro.
    iIntros (w w') "Hw !>". simpl. clear K K'.
    iIntros (K K') "HKK".
    
    iApply obs_refines_pure_l. { apply pure_prim_step_fill. apply pure_prim_step_beta. } iModIntro. simpl.
    iApply obs_refines_pure_r. { apply TCEq_eq. apply fill_not_eff; done. }
    { apply pure_prim_step_fill. apply pure_prim_step_beta. } simpl.

    iApply obs_refines_pure_l. { apply pure_prim_step_fill. apply (pure_prim_step_fill [AppLCtx _; AppLCtx _]). 
                                 apply (pure_prim_step_fill [AppRCtx _]). apply pure_prim_step_rec. } iModIntro.
    iApply obs_refines_pure_l. { apply pure_prim_step_fill. apply (pure_prim_step_fill [AppLCtx _; AppLCtx _]). apply pure_prim_step_beta. } iModIntro. simpl.
    iApply obs_refines_pure_l. { apply pure_prim_step_fill. apply (pure_prim_step_fill [AppLCtx _; AppLCtx _]). apply pure_prim_step_rec. } iModIntro. simpl.
    iApply obs_refines_pure_l. { apply pure_prim_step_fill. apply (pure_prim_step_fill [AppLCtx _]). apply pure_prim_step_beta. } iModIntro. simpl.
    iApply obs_refines_pure_l. { apply pure_prim_step_fill. apply (pure_prim_step_fill [AppLCtx _]). apply pure_prim_step_rec. } iModIntro. simpl.
    iApply obs_refines_pure_l. { apply pure_prim_step_fill. apply pure_prim_step_beta. } iModIntro. simpl.
    iApply obs_refines_pure_l. { apply pure_prim_step_fill. apply (pure_prim_step_fill [TryWithCtx _ _]). apply pure_prim_step_beta. } iModIntro. simpl.
    iApply obs_refines_pure_l. { apply pure_prim_step_fill. apply (pure_prim_step_fill [TryWithCtx _ _]). apply pure_prim_step_cont. } iModIntro. simpl.
    iApply obs_refines_pure_l. { apply pure_prim_step_fill. apply pure_prim_step_try_with_val. } iModIntro. simpl.
    iApply obs_refines_pure_l. { apply pure_prim_step_fill. apply pure_prim_step_beta. } iModIntro. simpl.

    iApply obs_refines_pure_r; [apply TCEq_eq; by apply fill_not_eff| |].
    { apply pure_prim_step_fill. apply (pure_prim_step_fill [AppLCtx _; AppLCtx _]). 
      apply (pure_prim_step_fill [AppRCtx _]). apply pure_prim_step_rec. }
    iApply obs_refines_pure_r; [apply TCEq_eq; by apply fill_not_eff| |].
    { apply pure_prim_step_fill. apply (pure_prim_step_fill [AppLCtx _; AppLCtx _]). apply pure_prim_step_beta. }
    iApply obs_refines_pure_r; [apply TCEq_eq; by apply fill_not_eff| |].
    { apply pure_prim_step_fill. apply (pure_prim_step_fill [AppLCtx _; AppLCtx _]). apply pure_prim_step_rec. } simpl.
    iApply obs_refines_pure_r; [apply TCEq_eq; by apply fill_not_eff| |].
    { apply pure_prim_step_fill. apply (pure_prim_step_fill [AppLCtx _]). apply pure_prim_step_beta. } simpl.
    iApply obs_refines_pure_r; [apply TCEq_eq; by apply fill_not_eff| |].
    { apply pure_prim_step_fill. apply (pure_prim_step_fill [AppLCtx _]). apply pure_prim_step_rec. }
    iApply obs_refines_pure_r; [apply TCEq_eq; by apply fill_not_eff| |].
    { apply pure_prim_step_fill. apply pure_prim_step_beta. }
    iApply obs_refines_pure_r; [apply TCEq_eq; by apply fill_not_eff| |].
    { apply pure_prim_step_fill. apply (pure_prim_step_fill [TryWithCtx _ _]). apply pure_prim_step_beta. } simpl.
    iApply obs_refines_pure_r; [apply TCEq_eq; by apply fill_not_eff| |].
    { apply pure_prim_step_fill. apply (pure_prim_step_fill [TryWithCtx _ _]). apply pure_prim_step_cont. }
    iApply obs_refines_pure_r; [apply TCEq_eq; by apply fill_not_eff| |].
    { apply pure_prim_step_fill. apply pure_prim_step_try_with_val. }
    iApply obs_refines_pure_r; [apply TCEq_eq; by apply fill_not_eff| |].
    { apply pure_prim_step_fill. apply pure_prim_step_beta. } simpl.

    rewrite {1}/ectxRel_car //=.
    iDestruct "HKK" as "(HKK&_)".
    by iApply "HKK".
  Qed.


  Definition rand_eff (n : nat) : expr :=
    (let: "a" := rand #n in
     (do: #());;
     "a")%E.

  Definition eff_rand (n : nat) : expr :=
    let: "α" := alloc #n in 
    ((do: #());; rand ("α") #n)%E.

  Theorem rand_eff_refines_eff_rand (n : nat) :
    ⊢ rand_eff n <<{ ⟦ .< TUnit ; TUnit .> TNat ⟧ₑ [] }<< eff_rand n.
  Proof.
    iIntros. unfold rand_eff, eff_rand.
    iIntros (K K') "HKK". rewrite obs_refines_eq.
    iIntros (ε) "Hj". iIntros "Herr". iIntros (Hpos).
    iApply spec_update_ewp.
    tp_alloctape as α "Htape". tp_pures.
    (* assert (fill K' (do: #();; (rand #lbl:α #n)%E) = fill ([AppRCtx (λ:<>, rand #lbl:α #n)%E] ++ K') (do:#())) as HAHH.
        { simpl. done. } *)
    iMod (step_pure  with "[$Hj]") as "Hj"; [apply I| |].
    { apply (@pure_eff (AppRCtx _)). apply AppRCtx_neutral. }
    rewrite app_nil_l.
    iModIntro.
    iApply (ewp_pure_bind ([AppRCtx _] ++ K)). { done. }
    iApply (ewp_couple_rand_tape with "[$Htape]"); [eauto|done|iModIntro].
    iIntros (m) "(Htape & %Hlt)". simpl.

    iApply ewp_pure_step. { apply pure_prim_step_fill. apply (pure_prim_step_fill [AppLCtx _]). apply pure_prim_step_rec. }
    iApply ewp_pure_step. { apply pure_prim_step_fill. apply pure_prim_step_beta. }
    simpl.
    iApply ewp_pure_step. { apply pure_prim_step_fill. apply (pure_prim_step_fill [AppRCtx _]).
                            apply pure_prim_step_do. }
    iApply ewp_pure_step. { apply pure_prim_step_fill. apply pure_prim_step_eff. apply AppRCtx_neutral. }
    rewrite app_nil_l.
    iApply fupd_ewp.
    iMod (inv_alloc (nroot.@"tape") _ with "[Htape]") as "#Hinv". { iNext. iApply "Htape". }
    iModIntro.
        
    rewrite {1}/ectxRel_car //=.
    iDestruct "HKK" as "(_&HKK)".
    rewrite obs_refines_eq.
    iApply ("HKK" with "[][$Hj][$Herr]"); [|done].
    iApply (eff_refines_intro _ _ _ #() #() [AppRCtx _] [AppRCtx _]); [done|done|eauto|].
    iModIntro.
    iIntros (w w') "Hww !>". simpl.
    simpl. clear Hpos ε K K'.
    iIntros (K K') "HKK".
    rewrite obs_refines_eq.
    iIntros (ε) "Hj". iIntros "Herr". iIntros (Hpos).
    iApply spec_update_ewp. tp_pures.
    iModIntro.
    iApply ewp_pure_step. { apply pure_prim_step_fill. apply (pure_prim_step_fill [AppLCtx _]).
                            apply pure_prim_step_rec. }
    iApply ewp_pure_step. { apply pure_prim_step_fill. apply pure_prim_step_beta. } simpl.
    iApply (ewp_pure_bind K). { done. }
    iApply fupd_ewp.
    iInv (nroot.@"tape") as "Htape" "Hclose".
    
    
  Admitted.
    
    
End eff_rand_ordering.

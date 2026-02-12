From iris.proofmode Require Import base tactics classes.
From clutch.prob_eff_lang.probblaze Require Import logic proofmode spec_rules.

 Lemma rel_bind_unsound `{!probblazeRGS Σ}k1 k2 e1 e2 X Y R :
   iThy_le X Y -∗
   REL e1 ≤ e2 <|X|> {{ (λ v1 v2, REL fill k1 v1 ≤ fill k2 v2 <|Y|> {{R}} )}} -∗
   REL fill k1 e1 ≤ fill k2 e2 <|Y|> {{R}}.
 Proof. Admitted.

 Section implementation.

   Definition handler1 op (e : expr) : expr :=
     handle: e with
     | effect op "p", "k" as multi => "k" #()%V
     | return "v" => "v"
   end.

   Definition handler2 op (e : expr) : expr :=
     handle: e with 
     | effect op "p", "k" as multi => "k" "p"
     | return "v" => "v"
   end.

 End implementation.

 Section verification.
   Context `{!probblazeRGS Σ}.
   Context `{op : label}.

   Program Definition T1 : iThy Σ := λ e1 e2, (λne Q,
      ∃ p1 p2 : val, ⌜ e1 = do: op p1 ⌝%E ∗ ⌜ e2 = (do: op p2) ⌝%E ∗ Q #()%V #()%V)%I.
   Next Obligation. solve_proper. Qed.
   
   Lemma unsound_bind :
     ⊢ REL (handler1 op (handler2 op (do: op #1))) ≤ (handler1 op (handler2 op (do: op #2))) <|iThyBot|> {{ (λ v1 v2, ⌜v1 = v2⌝) }}.
   Proof.
     (* Uncomment the following to see why this lemma should fail *)
     (* iApply (rel_bind [HandleCtx _ _ _ _ _] [HandleCtx _ _ _ _ _]); first iApply iThy_le_refl.
        rel_pures_l; first set_solver. rel_pures_r; first set_solver.
        iModIntro. simpl. rel_pures_l. rel_pures_r. iModIntro. iPureIntro. *)
     iApply (rel_exhaustion [HandleCtx _ _ _ _ _] [HandleCtx _ _ _ _ _] _ _ T1 _ (λ v1 v2, ⌜v1 = v2⌝)%I); last first. 
     - iSplit.
       + iIntros (?? ->). rel_pures_l. rel_pures_r. iPureIntro; done.
       + iIntros (???) "(%&%&->&->&HQ) #Hkont //=".
         rel_pures_l; first set_solver.
         rel_pures_r; first set_solver. iPureIntro; done.
     - iApply (rel_bind_unsound [HandleCtx _ _ _ _ _] [HandleCtx _ _ _ _ _]); first iApply iThy_le_refl.
       iApply (rel_introduction _ _ (λ v1 v2, ⌜ v1 = #()%V ⌝ ∗ ⌜ v2 = #()%V ⌝)%I).
       + iExists #1, #2. repeat (iSplit; try iPureIntro; try done). 
       + iIntros "!# !> % % (-> & ->)". iApply rel_value. simpl.
         rel_pures_l. rel_pures_r. done.
   Qed.

 End verification.
       

From clutch.prob_eff_lang.probblaze Require Import logic notation.
From iris.proofmode Require Import base proofmode classes.
From clutch.prob_eff_lang.probblaze.examples.DH_KE Require Import valgroup.

Import valgroup_tactics.

Section definitions.

Definition mut_handler_constructor : val :=
  λ: "h1" "h2",
    rec: "mhandler" "f" :=
    (* instantiate each handler-branch with the mutually recursive handler *)
    let: "mh1" := "h1" "mhandler" in 
    (* handle: handle: f with ... with ... *)
    "mh1" (λ: <>, "h2" "f").

(* a mutually recursive handler, handling s with h *)
Definition mut_handler (s : label) (h : expr) : val :=
  λ: "mhandler" "f",
    handle: "f" #()%V with
    | effect s "x", "k" as multi => "mhandler" (λ: <>, (λ: "x" "k", h)%V "x" "k")
    | return "y" => "y"
    end.

Definition handle_with (s : label) (h : expr) : val :=
  λ: "f",
     handle: "f" #()%V with
     | effect s "x", "k" as multi => (λ: "x" "k", h)%V "x" "k"
     | return "y" => "y"
     end.

Definition handle_with_deep (s : label)  (h : expr) : val :=
  λ: "f",
     handle: "f" #()%V with
     | effect s "x", rec "k" as multi => (λ: "x" "k", h)%V "x" "k"
     | return "y" => "y"
     end.

Definition comp_handler (s1 s2 : label) (h1 h2 : expr) : val :=
  λ: "f", 
    handle: handle: "f" #()%V with 
  | effect s2 "x", "k" as multi=> (λ: "x" "k", h2)%V "x" "k"
  | return "y" => "y"
  end with 
  | effect s1 "x", "k" as multi => (λ: "x" "k", h1)%V "x" "k"
  | return "y" => "y"
  end. 

End definitions.

Section theories.
Context {sim f p : label}.
Context `{probblazeRGS Σ}.
(* The types used in the signatures *)
Context {Pp Pr Ip Ir Sp Sr : (val → val → iProp Σ)}.

(* the signature of T *)
Program Definition client : iThy Σ := (λ e1 e2, λne Q,
                                    ∃ v1 v2 : val, Pp v1 v2 ∗ 
                                             (⌜ e1 = do: p v1 ⌝%E ∗
                                             ⌜ e2 = do: p v2 ⌝%E ∗
                                             □ (∀ w1 w2, Pr w1 w2 -∗ Q w1 w2)))%I.
Next Obligation. solve_proper. Qed.

Program Definition ideal : iThy Σ := (λ e1 e2, λne Q,
                                           ∃ v1 v2 : val, Ip v1 v2 ∗
                                                          (⌜ e1 = do: f v1 ⌝%E ∗
                                                           ⌜ e2 = do: f v2 ⌝%E ∗
                                                           □ (∀ w1 w2, Ir w1 w2 -∗ Q w1 w2)))%I.
Next Obligation. solve_proper. Qed.

Program Definition simulator : iThy Σ := (λ e1 e2, λne Q,
                                           ∃ v1 v2 : val, Sp v1 v2 ∗
                                                          (⌜ e1 = do: sim v1 ⌝%E ∗
                                                           ⌜ e2 = do: sim v2 ⌝%E ∗
                                                           □ (∀ w1 w2, Sr w1 w2 -∗ Q w1 w2)))%I.
Next Obligation. solve_proper. Qed.

End theories. 


Section proofs.
  Context {sim f p : label}.
  Context `{probblazeRGS Σ}.
  (* The types used in the signatures *)
  Context {Pp Pr Ip Ir Sp Sr : (val → val → iProp Σ)}.

  Lemma composition_mut_handler h1 h2 h3 (f1 f2 : val) R :
    
    (* sim and f has to appear to avoid f1 and f2 to interfer with the protocol *)
    BREL f1 #()%V ≤ f2 #()%V <| [([p],[p], @client p Σ Pp Pr);([sim;f],[sim;f],⊥)] |> {{ R }} -∗

    □ (∀ k1' k2' v1 v2, Pp v1 v2 -∗ (* adding the payload to the context *)
                        (* adding the continuation to the context *)
                        (∀ w1 w2, Pr w1 w2 -∗ BREL fill k1' w1 ≤ fill k2' w2 <| [([p],[p], @client p Σ Pp Pr);([sim;f],[sim;f],⊥)] |> {{ R }}) -∗
                        BREL val_subst "k" (KontV k1') (val_subst "x" v1 h3) 
                          ≤ val_subst "k" (KontV k2') (val_subst "x" v2 h3) <| [([sim;f],[sim;f], @ideal f Σ Ip Ir); ([p],[p],⊥)] |> {{ R }}) -∗

    □ (∀ k1 k2 v1 v2, Ip v1 v2 -∗
                      (∀ w1 w2, Ir w1 w2 -∗ BREL fill k1 w1 ≤ fill k2 w2 <| [([sim;f],[sim;f], @ideal f Σ Ip Ir);([p],[p],⊥)] |> {{ R }}) -∗ 
                      BREL val_subst "k" (KontV k1) (val_subst "x" v1 h2) 
                        ≤ val_subst "k" (KontV k2) (val_subst "x" v2 h2)
                        <| [([sim;f],[sim;f],@simulator sim Σ Sp Sr);([p],[p],⊥)] |> {{ R }}) -∗

    □ (∀ k1 k2 v1 v2, Sp v1 v2 -∗
                      (∀ w1 w2, Sr w1 w2 -∗ BREL fill k1 w1 ≤ fill k2 w2 <| [([sim;f],[sim;f], @simulator sim Σ Sp Sr);([p],[p],⊥)] |> {{ R }}) -∗
                      BREL val_subst "k" (KontV k1) (val_subst "x" v1 h1) ≤
                        val_subst "k" (KontV k2) (val_subst "x" v2 h1) <| [([sim;f],[sim;f], @ideal f Σ Ip Ir);([p],[p],⊥)] |> {{ R }}) -∗

    BREL mut_handler_constructor (mut_handler sim h1) (handle_with f h2) (λ: <>, handle_with p h3 f1)%V ≤
      mut_handler_constructor (mut_handler sim h1) (comp_handler f p h2 h3) f2 <|[([sim;f], [sim;f], ⊥);([p],[p],⊥)]|> {{ R }}.
  Proof.
    unfold mut_handler_constructor, mut_handler, handle_with, comp_handler, handle_with_deep.
    iIntros (* (Hch1 Hch2 Hch3) *) "Hff #Hh3 #Hh2 #Hh1". brel_pures.
    
    iApply brel_introduction_mono. { iApply to_iThy_le_intro'. apply submseteq_swap. }
    iApply (brel_exhaustion_abs (f1 #()%V) (f2 #()%V) with "Hff"); [set_solver|set_solver|].
    iSplit.
    { iModIntro; iIntros (??) "HR". brel_pures. iModIntro. by brel_pures. }
    iIntros (????? Hk1' Hk2') "!# (%&%&HPp&->&->&#HPpQ) #Hkont". simpl.
    brel_pures.
    1,2: apply neutral_ectx; set_solver.
    iDestruct ("Hh3" with "[$]") as "Hh3rel".
    
    iApply brel_introduction_mono. { iApply to_iThy_le_intro'. apply submseteq_swap. }
    iApply (brel_exhaustion_abs _ _ [HandleCtx _ _ _ _ _; HandleCtx _ _ _ _ _] [HandleCtx _ _ _ _ _; HandleCtx _ _ _ _ _] with "[Hh3rel]"); [set_solver|set_solver| |].
    { iApply "Hh3rel". iIntros (??) "HPr". iApply "Hkont". by iApply "HPpQ". }
    iSplit; [iModIntro; iIntros (??) "HR"; by brel_pures|].
    iIntros (????? Hk1'h3 Hk2'h3) "!# (%&%&HIp&->&->&#HIpQ) #HkontH3". simpl.
    brel_pures.
    1,2: apply neutral_ectx; set_solver.
  
    clear Hk1'h3 Hk2'h3.
    iRevert "HkontH3 HIpQ".
    iLöb as "IH" forall (v0 v3 k1'0 k2'0 Q0). iIntros "#Hkonth3 #HIpQ".
    iDestruct ("Hh2" with "[$]") as "Hh2rel".
    
    iApply (brel_exhaustion _ _ [HandleCtx _ _ _ _ _] [HandleCtx _ _ _ _ _] with "[Hh2rel]"); [set_solver|set_solver| |].
    { iApply "Hh2rel". iIntros (??) "HIr". iApply "Hkonth3". by iApply "HIpQ". }
    iSplit; [iModIntro; iIntros (??) "HR"; by brel_pures|].
    iIntros (????? Hkh2 Hkh2') "!# (%&%&HSp&->&->&#HSpQ) #Hkonth2". simpl.
    brel_pures.
    1,2: apply neutral_ectx; set_solver.
      
    iDestruct ("Hh1" with "[$]") as "Hh1rel".
    iApply (brel_exhaustion_abs (val_subst "k" (KontV k1'1) (val_subst "x" v4 h1))
                            (val_subst "k" (KontV k2'1) (val_subst "x" v5 h1)) with "[Hh1rel]"); [set_solver|set_solver| |].
    { iApply "Hh1rel". iIntros (??) "HSr". iApply "Hkonth2". by iApply "HSpQ". }
    iSplit; [iModIntro; iIntros (??) "HR"; by brel_pures|].
    iIntros (????? Hkh1 Hkh1') "!# (%&%&HIp&->&->&#HIpQ2) #Hkonth1". simpl.
    iApply brel_learn. iIntros "(%Hdistinctl&%Hdistinctr) #Hvalid".
    brel_pures.
    1 : apply neutral_ectx; set_solver.
    { simpl. apply not_elem_of_cons. split; last (apply neutral_ectx; set_solver).
      unfold distinct_l in Hdistinctl. unfold labels_l in Hdistinctl. simpl in Hdistinctl. 
      apply NoDup_cons_1_2 in Hdistinctl. apply NoDup_cons_1_1 in Hdistinctl. 
      intros Heq. apply list_elem_of_singleton in Heq. done. }
    iApply ("IH" with "HIp"). 
    2 : iExact "HIpQ2".
    
    iIntros (??) "!# HQ". simpl.
    iDestruct ("Hkonth1" with "HQ") as "Hcont".

    iApply (brel_bind'' [] [HandleCtx _ _ _ _ _] [([sim;f],[sim;f],@ideal f _ _ _ )]).
    3 : { iApply to_iThy_le_refl. }
    1,2: set_solver.
    rewrite -(to_iThyIfMonoMS [([sim;f], [sim;f],ideal)]).
    iApply (brel_mono with "[][$Hcont]").
    1 : { iSplit; last (iSplit; iModIntro).
          - iApply iThy_le_trans; last iApply iThy_le_to_iThy_1. iApply iThy_le_submseteq. 
            apply submseteq_swap. 
          - iIntros "Hv". iApply valid_to_iThy_bot. iApply "Hvalid".
          - iIntros "_". iPureIntro. apply distinct_to_iThy_bot. by split. }

    simpl. iIntros (??) "!# HR". by brel_pures. 
  Qed. 

End proofs.    
               

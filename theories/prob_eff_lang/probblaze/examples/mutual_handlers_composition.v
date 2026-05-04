From clutch.prob_eff_lang.probblaze Require Import logic notation sem_types sem_def proofmode.
From iris.proofmode Require Import base proofmode classes.
From clutch.prob_eff_lang.probblaze.examples.DH_KE Require Import valgroup.

Import valgroup_tactics.

Section definitions.

Definition mut_handler_constructor : val :=
  λ: "h1" "h2",
    rec: "mhandler" "f" :=
    (* instantiate the first handler-branch with the mutually recursive handler *)
    let: "mh1" := "h1" "mhandler" in 
    (* handle: handle: f with ... with ... *)
    "mh1" (λ: <>, "h2" "f").

Definition mut_mut_handler_constructor : val :=
  λ: "mhandler1" "h1" "h2",
     let: "mh2" := "h2" "mhandler1" in
      (mut_handler_constructor "h1") "mh2". 

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

Definition handle_withV (s : label) (h : expr): val :=
  λ: "mhandler", λ: "f",
    handle: "f" #()%V with 
  | effect s "x", "k" as multi => "mhandler" (λ: "x" "k", h)%V "x" "k"
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

Definition mut_mut_full sim1 hsim1 sim2 hsim2 f hf : val :=
  rec: "mhandler1" "f" :=
    let: "mh" :=
      (λ: "mhandler1", (rec: "mhandler2" "f" :=
                          handle: 
                          handle: "f" #()%V with
                       | effect sim2 "x", "k" as multi=> "mhandler1" (λ: <>, (λ: "x" "k", hsim2)%V "x" "k")
                       | return "y" => "y"
                        end with
                       | effect sim1 "x", "k" as multi => "mhandler2" (λ: <>, (λ: "x" "k", hsim1)%V "x" "k")
                       | return "y" => "y"
                        end))%V "mhandler1" in
    let: "handler" := (λ: "f", handle: "f" #()%V with
                      | effect f "x", "k" as multi=> (λ: "x" "k", hf)%V "x" "k"
                      | return "y" => "y"
                       end )%V in
     "mh" (λ: <>, "handler" "f").


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
  Context {sim p : label}.
  Context `{probblazeRGS Σ}.
  (* The types used in the signatures *)
  Context {Pp Pr Ip Ir Sp Sr : (val → val → iProp Σ)}.

  Lemma composition_mut_handler_1 h1 h2 h3 f (f1 f2 : val) R :
    
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

  Lemma composition_mut_handler_2 f h (g g' : val) (c1 c2 : val) R: 
    □ (BREL c1 #()%V ≤ c2 #()%V <| [([p],[p],@client p Σ Pp Pr)] |> {{ R }}) -∗

    □ (∀ f1 f2 : val, BREL f1 #()%V ≤ f2 #()%V <| [([p],[p],@client p Σ Pp Pr); ([f],[f], @ideal f Σ Ip Ir)] |> {{ R }} -∗
                      BREL g f1 ≤ g' f2 <| [([sim],[sim], @simulator sim Σ Sp Sr)] |> {{ R }}) -∗
    
    □ (∀ k1 k2 v1 v2, Sp v1 v2 -∗
                      (∀ w1 w2, Sr w1 w2 -∗ BREL fill k1 w1 ≤ fill k2 w2 <| [([sim],[sim], @simulator sim Σ Sp Sr)] |> {{ R }}) -∗
                      BREL val_subst "k" (KontV k1) (val_subst "x" v1 h) ≤
                        val_subst "k" (KontV k2) (val_subst "x" v2 h) <| [([f],[f], @ideal f Σ Ip Ir)] |> {{ R }}) -∗

    BREL mut_handler_constructor (mut_handler sim h) g c1 ≤ mut_handler_constructor (mut_handler sim h) g' c2 <| [([sim],[sim], ⊥)] |> {{ R }}.
  Proof. 
    iIntros "#Hcc #Hgg #Hh".
    unfold mut_handler_constructor, mut_handler. 
    brel_pures.
    iApply (brel_exhaustion (g c1) (g' c2)); [set_solver|set_solver| |].
    { iApply "Hgg". iApply brel_introduction_mono; [iApply to_iThy_le_intro' | iExact "Hcc"]. constructor; apply submseteq_nil_l. }
    iSplit; [iModIntro; iIntros (??) "HR"; by brel_pures|].
    
    iLöb as "IH".

    iIntros (?????) "!# %Hk1 %Hk2 (%&%&HSp&->&->&#HSrQ) #Hkont1".
    brel_pures.
    1,2 : apply neutral_ectx; set_solver.
    iApply (brel_exhaustion (g _) (g' _) with "[HSp]"); [set_solver|set_solver| |].
    { iApply "Hgg". brel_pures. iApply brel_introduction_mono; [iApply to_iThy_le_intro'; by apply submseteq_cons|].  
      iApply ("Hh" with "HSp"). iIntros (??) "HSr". 
      iApply brel_introduction_mono; [iApply to_iThy_le_intro'; apply submseteq_skip; apply submseteq_nil_l|]. 
      iApply "Hkont1". by iApply "HSrQ". }
    iSplit; [iModIntro; iIntros (??) "HR"; by brel_pures|].
    iExact "IH".
  Qed. 

  Lemma composition_mut_handler_3 sim1 sim2 Sp1 Sr1 Sp2 Sr2 (f : label) hf hsim1 hsim2  (c1 c2 : val) (R : val → val → iProp Σ) :
    let IT := @ideal f Σ Ip Ir in
    BREL c1 #()%V ≤ c2 #()%V <| [([f], [f], IT)] |> {{ R }} -∗

     □ (∀ k1' k2' v1 v2, Ip v1 v2 -∗ (* adding the payload to the context *)
                        (* adding the continuation to the context *)
                        (∀ w1 w2, Ir w1 w2 -∗ BREL fill k1' w1 ≤ fill k2' w2 <| [([f],[f],IT);([sim1;sim2],[sim1;sim2], @simulator sim1 Σ Sp1 Sr1)] |> {{ R }}) -∗
                        BREL val_subst "k" (KontV k1') (val_subst "x" v1 hf) 
                          ≤ val_subst "k" (KontV k2') (val_subst "x" v2 hf) <| [([sim1;sim2],[sim1;sim2], @simulator sim2 Σ Sp2 Sr2)(* ; ([p],[p],⊥) *)] |> {{ R }}) -∗

     □ (∀ k1' k2' v1 v2, Sp2 v1 v2 -∗ (* adding the payload to the context *)
                         (* adding the continuation to the context *)
                         (∀ w1 w2, Sr2 w1 w2 -∗ BREL fill k1' w1 ≤ fill k2' w2 <| [([sim1;sim2],[sim1;sim2],@simulator sim2 Σ Sp2 Sr2);([f],[f],⊥)] |> {{ R }}) -∗
                         BREL val_subst "k" (KontV k1') (val_subst "x" v1 hsim2) 
                           ≤ val_subst "k" (KontV k2') (val_subst "x" v2 hsim2) <| [([f],[f], IT); ([sim1;sim2],[sim1;sim2],@simulator sim1 Σ Sp1 Sr1)] |> {{ R }}) -∗
    
     □ (∀ k1' k2' v1 v2, Sp1 v1 v2 -∗ (* adding the payload to the context *)
                         (* adding the continuation to the context *)
                         (∀ w1 w2, Sr1 w1 w2 -∗ BREL fill k1' w1 ≤ fill k2' w2 <| [([sim1],[sim1],@simulator sim1 Σ Sp1 Sr1)] |> {{ R }}) -∗
                         BREL val_subst "k" (KontV k1') (val_subst "x" v1 hsim1) 
                           ≤ val_subst "k" (KontV k2') (val_subst "x" v2 hsim1) <| [([sim2],[sim2],@simulator sim2 Σ Sp2 Sr2)] |> {{ R }}) -∗

    BREL mut_handler_constructor (mut_handler sim1 hsim1) (mut_handler_constructor (mut_handler sim2 hsim2) (handle_with f hf)) c1 ≤
         (mut_mut_full sim1 hsim1 sim2 hsim2 f hf) c2  <| [([f],[f], ⊥);([sim1;sim2],[sim1;sim2],⊥)] |> {{ R }}.
  Proof.    
    iIntros (IT) "Hcc #Hhf #Hhsim2 #Hhsim1".
    unfold mut_handler_constructor, mut_handler, handle_with, mut_mut_handler_constructor, mut_mut_full.
    brel_pures_l. brel_pures_r. 

    iApply (brel_exhaustion_abs (c1 #()%V) (c2 #()%V) with "[Hcc]"); [set_solver|set_solver| |].
    { iApply (brel_introduction_mono [([f],[f],IT)] [([f],[f],IT);([sim1;sim2],[sim1;sim2],⊥)]). 
      - iApply to_iThy_le_intro'. constructor. apply submseteq_nil_l.
      - iExact "Hcc". }
    iSplit; [iModIntro; iIntros (??) "HR"; by brel_pures|]. 
    iLöb as "IHhf".
    iIntros (?????) "!# %Hk1 %Hk2 (%&%&HIp&->&->&#HIrQ) #Hkont1". 
    brel_pures. 
    1,2 : apply neutral_ectx; set_solver.
    
    iApply brel_introduction_mono. { iApply to_iThy_le_intro'; apply submseteq_swap. }
    iApply (brel_exhaustion (val_subst "k" (KontV k1') (val_subst "x" v1 hf)) (val_subst "k" (KontV k2') (val_subst "x" v2 hf)) with "[HIp]"); [set_solver|set_solver| |].
    { iDestruct ("Hhf" with "HIp") as "Hkont". 
      iApply brel_introduction_mono. { iApply to_iThy_le_intro'; apply submseteq_skip; apply submseteq_nil_l. }
      iApply "Hkont". iIntros (??) "HIr". 
      iApply (brel_introduction_mono [([f], [f], IT); ([sim1; sim2], [sim1; sim2], ⊥)]). { admit. }
      iApply "Hkont1". by iApply "HIrQ". }
    iSplit; [iModIntro; iIntros (??) "HR"; by brel_pures|]. 
    iLöb as "IHsim2".
    iIntros (?????) "!# %Hk1' %Hk2' (%&%&HSp&->&->&#HSrQ) #Hkont2". 
    brel_pures. 
    1,2 : apply neutral_ectx; set_solver.
  Admitted. 
    (* iApply (brel_exhaustion _ _ [HandleCtx _ _ _ _ _; HandleCtx _ _ _ _ _] [HandleCtx _ _ _ _ _; HandleCtx _ _ _ _ _ ; HandleCtx _ _ _ _ _] with "[HSp]"); [set_solver|set_solver| |].
       { iApply brel_introduction_mono. { iApply to_iThy_le_intro'; apply submseteq_swap; done. }
         iApply (brel_exhaustion _ _ [HandleCtx _ _ _ _ _] [HandleCtx _ _ _ _ _] _ _ _ _ R with "[HSp]"); [set_solver|set_solver| |].
         { iDestruct ("Hhsim2" with "HSp") as "Hkont". iApply "Hkont". iIntros (??) "HSr". iApply "Hkont2". by iApply "HSrQ". }
         iSplit; [iModIntro; iIntros (??) "HR"; by brel_pures|]. 
         iIntros (?????) "!# %Hk1'' %Hk2'' (%&%&HIp2&->&->&#HIrQ2) #Hkont2'". simpl.
         brel_pures. 
         1,2 : apply neutral_ectx; set_solver.
         iApply brel_introduction_mono. 
         { iSplit.
           - iApply iThy_le_to_iThy_2.
           - iSplit; iModIntro; [iApply valid_submseteq|iIntros (Hd);iPureIntro; revert Hd; apply distinct_submseteq]; apply submseteq_cons; done. }
         iDestruct ("Hhf" with "HIp2") as "Hkont". iApply "Hkont". *)
      

End proofs.    
               

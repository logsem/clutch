From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Import ghost_var.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode spec_rules spec_ra notation class_instances.

Section implementation.

  Definition n : nat := 1234.

  Definition sample : expr := λ: <>, rand #n.
  Definition samplelbl α : expr := λ: <>, (rand(α) #n).

  Definition Send (e : expr) := InjL e.
  Definition Recv (e : expr) := InjR e.
  Definition SendV (v : val) := InjLV v.
  Definition RecvV (v : val) := InjRV v.
  Definition bob := InjLV #()%V.
  Definition alice := InjRV #()%V.
  Definition pow : expr := rec: "pow" "b" "e" := if: "e" = #0 then #1 else "b" * ("pow" "b" ("e" - #1)).
  Definition modn : expr := rec: "mod" "a" := if: "a" < #n then "a" else "mod" ("a" - #n).

  Definition F_AUTH (channel : label) f : expr :=
    let: "m1" := ref NONE in
    let: "m2" := ref NONE in

    handle: f with
    | effect channel "message", rec "k" =>
        match: "message" with
        | InjL "payload" =>
            let, ("m", "dst") := "payload" in
            match: "dst" with
              InjL <> => match: !"m1" with
                         NONE => "m1" <- SOME "m";; do: channel (Send ("m", "dst"))
                       | SOME "x" => "k" #()%V 
                       end
            | InjR <> => match: !"m2" with
                          NONE => "m2" <- SOME "m";; do: channel (Send ("m", "dst"))
                        | SOME "x" => "k" #()%V 
                        end
            end
        | InjR "from" =>
            let: "r" := do: channel (Recv "from") in
             match: "r" with
               NONE => "k" NONE
             | SOME "x" => match: "from" with
                             InjL <> => match: !"m2" with
                                          NONE => "k" NONE
                                        | SOME "m" => "k" "m"
                                        end
                           | InjR <> => match: !"m1" with
                                          NONE => "k" NONE
                                        | SOME "m" => "k" "m"
                                        end
                           end
             end
        end
     | return "y" => #()%V end.


  Definition F_KE (getKey channel : label) f : expr :=
    let: "key" := (sample #()%V) in

    handle: f with
    | effect getKey "p", rec "k" =>
        match: "p" with
          InjL <> =>
            (do: channel Send (#0, bob));;
            let: "r" := do: channel Recv bob in
            match: "r" with
              NONE => "k" NONE
            | SOME "w" => "k" (SOME "key")
            end
        | InjR <> =>
            (do: channel Send (#0, alice));;
            let: "r" := do: channel Recv alice in
            match: "r" with
              NONE => "k" NONE
            | SOME "w" => "k" (SOME "key")
            end
       end
    | return "y" => "y" end.


  Definition DH_KE (getKey channel : label) (g : nat) f : expr :=
    let: "α" := alloc #n in           
    handle: f with
    | effect getKey "p", rec "k" =>
        match: "p" with
          InjL <> =>
            let: "a" := samplelbl "α" #()%V in
            let: "gA" := modn (pow #g "a") in
            (do: channel (Send ("gA", bob)));;
            let: "r" := do: channel (Recv bob) in
            match: "r" with
              NONE => "k" NONE
            | SOME "gB" =>
                let: "key" := modn (pow "gB" "a") in
                "k" (SOME "key")
            end
       | InjR <> =>
           let: "b" := sample #()%V in
            let: "gB" := modn (pow #g "b") in
            (do: channel (Send ("gB", alice)));;
            let: "r" := do: channel (Recv alice) in
            match: "r" with
              NONE => "k" NONE
            | SOME "gA" =>
                let: "key" := modn (pow "gA" "b") in
                "k" (SOME "key")
            end
       end
   | return "y" => "y" end.



  Definition DH_SIM (channel : label) (g : nat) (f : expr) : expr :=
      handle: f with
    | effect channel "payload", rec "k" =>
        match: "payload" with
        | InjL "payload" =>
            let, ("m", "dst") := "payload" in
            match: "dst" with
              InjL <> => let: "c" := sample #()%V in
                         let: "gC" := modn (pow #g "c") in
                         (do: channel (Send ("gC", bob)));;
                         "k" #()%V
            | InjR <> => let: "c" := sample #()%V in
                         let: "gC" := modn (pow #g "c") in
                         (do: channel (Send ("gC", alice)));;
                         "k" #()%V
            end
        | InjR "from" =>
            let: "r" := do: channel (Recv "from") in
             match: "r" with
               NONE => "k" NONE
             | SOME "x" => "k" (SOME #0)
             end
        end
    | return "y" => "y" end.

  Definition C (getKey channel : label) (g : nat) (DH : nat → expr) (f : expr) : expr :=
    let, ("ga", "gb", "gc") := (DH g) in

    handle: f with
    | effect getKey "p", rec "k" =>
        match: "p" with
          InjL <> =>
            (do: channel (Send ("ga", bob)));;
            let: "r" := (do: channel (Recv bob)) in
            match: "r" with
              NONE => "k" NONE
            | SOME "w" => "k" (SOME "gc")
            end
        | InjR <> =>
            (do: channel (Send ("gb", alice)));;
            let: "r" := (do: channel (Recv alice)) in
            match: "r" with
              NONE => "k" NONE
            | SOME "w" => "k" (SOME "gc")
            end
        end
    | return "y" => "y" end.

  Definition DH_real (g: nat) : expr :=
    let: "a" := sample #()%V in
    let: "b" := sample #()%V in
    (modn (pow #g "a"), modn (pow #g "b"), modn (pow #g ("a"*"b"))).

  Definition DH_rand (g : nat): expr :=
    let: "a" := sample #()%V in
    let: "b" := sample #()%V in
    let: "c" := sample #()%V in
    (modn (pow #g "a"), modn (pow #g "b"), modn (pow #g "c")).

End implementation.

Section handlee_verification.
  Context `{!probblazeRGS Σ, !ghost_varG Σ nat}.
  Context (channel1 channel2 getKey1 getKey2 : label).

  Program Definition GetKey1 : iThy Σ :=
    λ e1 e2, (λne Q,
                ⌜ e1 = do: getKey1 (InjL #()%V) ⌝%E ∗
                ⌜ e2 = do: getKey2 (InjL #()%V) ⌝%E ∗
                 □ (Q NONEV NONEV ∗ ∀ key, Q (SOMEV #key) (SOMEV #key) )
             )%I.
  Next Obligation. solve_proper. Qed.
    
  Program Definition SendBob : iThy Σ :=
    λ e1 e2, (λne Q,
                ∃ m : nat, 
                  ⌜ e1 = do: channel1 (SendV (#m, bob)) ⌝%E ∗
                  ⌜ e2 = do: channel2 (SendV (#m, bob)) ⌝%E ∗
                  □ Q (Val #()%V) (Val #()%V)
             )%I. 
  Next Obligation. solve_proper. Qed.

  Program Definition RecvBob : iThy Σ :=
    λ e1 e2, (λne Q,
                ⌜ e1 = do: channel1 (RecvV bob) ⌝%E ∗
                ⌜ e2 = do: channel2 (RecvV bob) ⌝%E ∗
                □ ((∀ gB : nat, ∃ a m, ⌜ (gB ^ a) `mod` DH_channel.n = m ⌝%nat  -∗
                                       Q (SOME #gB) (SOME #gB)) ∧ Q NONE NONE)
                  )%I.
  Next Obligation. solve_proper. Qed.
  
  Definition T : iThy Σ := iThyTraverse [getKey1] [getKey2] GetKey1.
  Definition X : iThy Σ := iThyTraverse [channel1] [channel2] (iThySum (SendBob) (RecvBob)).


  Lemma pow_rel (g n : nat) :
    ⊢ REL pow #g #n ≤ pow #g #n <|iThyBot|> {{ (λ v1 v2, ⌜ v1 = #(g ^ n)%nat ⌝ ∗ ⌜ v2 = #(g ^ n)%nat ⌝) }}.
  Admitted.

  (* Show this later with the actual m *)
  Lemma pow_un (g n : nat ) :
    ∃ m : nat, PureExec True m (pow #g #n) (#(g ^ n)).
  Admitted.

  Lemma modn_rel (m : nat) :
    ⊢ REL modn #m ≤ modn #m <|iThyBot|> {{ (λ v1 v2, ⌜ v1 = #(m `mod` n)%nat ⌝ ∗ ⌜ v2 = #(m `mod` n)%nat ⌝) }}.
  Admitted.

  Lemma modn_un (m : nat) :
    ∃ s, PureExec True s (modn #m) (#(m `mod` n)). 
  Admitted.

  Lemma modn_pow_un (g m : nat) :
    ∃ s, PureExec True s (modn (pow #g #m)) (#((g ^ m) `mod` n)%nat).
  Proof.
    pose proof (pow_un g m) as (s1 & Hpow).
    pose proof (modn_un (g ^ m)) as (s2 & Hmod).
    exists (s1 + s2)%nat.
  Admitted.
      
  Lemma DH_KE_C_DH_real (g : nat) f1 f2:
    (∀ s n, val_subst s n f1 = f1) →
           (∀ s n, val_subst s n f2 = f2) →
           REL f1 ≤ f2 <|T|> {{ (λ v1 v2, ⌜v1 = #()%V⌝ ∧ ⌜v2 = #()%V⌝) }} -∗
           REL DH_KE getKey1 channel1 g f1 ≤ C getKey2 channel2 g DH_real f2 <|X|> {{ (λ v1 v2, ⌜ v1 = v2 ⌝) }}.
  Proof.
    iIntros (Hf1closed Hf2closed) "Hff".
    unfold C. unfold DH_real.
    unfold DH_KE.
    iApply rel_alloctape_l. iIntros (α) "!> Hα".
    iDestruct "Hα" as (ns) "(%Hf & Hα)". apply map_eq_nil in Hf. simplify_eq.
    iApply rel_couple_TU; [done|]. iFrame. simpl. iIntros (a) "Hα".
    iApply rel_randU_empty_r. iIntros (b Hltb).
    do 3 rel_pure_r.
    fold modn pow.
    pose proof (modn_pow_un g (a * b)) as (s1 & Hstep1).
    pose proof (modn_pow_un g b) as (s2 & Hstep2).
    pose proof (modn_pow_un g a) as (s3 & Hstep3).
    iApply (rel_pure_step_r' _ _ (
                let: "ga" := (#(g ^ a `mod` n)%nat, #(g ^ b `mod` n)%nat, #(g ^ (a * b) `mod`n)%nat) in
                let: "gb" := Snd (Fst "ga") in
                let: "gc" := Snd "ga" in
                let: "ga" := Fst (Fst "ga") in
                handle: f2 with
              | effect getKey2 "p", rec "k" =>
                  match: "p" with
                    InjL <> => (do: channel2 Send ("ga", bob));; let: "r" := do: channel2 Recv bob in match: "r" with InjL <> => "k" (InjL #()%V) | InjR "w" => "k" (InjR "gc") end
                                                                             | InjR <> => (do: channel2 Send ("gb", alice));; let: "r" := do: channel2 Recv alice in match: "r" with InjL <> => "k" (InjL #()%V) | InjR "w" => "k" (InjR "gc") end
                                                                                                                                            end
                                                                                                                                          | return "y" => "y"
                                                                                                                                            end)%E
              True s1); [admit|done|].
    rel_pures_r. rel_pures_l. fold modn pow.
    do 3 rewrite Hf2closed. rewrite Hf1closed. clear Hf2closed. clear Hf1closed.
    iApply (rel_exhaustion [_] [_] _ _ with "[$]").
    iSplit; [iIntros (v1 v2) "(-> & ->)"; rel_pures_l; by rel_pures_r|].
    iIntros (e1 e2 ?)
      "[%e1' [%e2' [%k1 [%k2 [%S
        (-> & %Hk1 & -> & %Hk2 & (-> & -> & (Hnone & Hsome)) & #HQ)
       ]]]]] #Hk".
    do 2 rel_pures_l; [apply Hk1; set_solver|].
    do 2rel_pures_r; [apply Hk2; set_solver|].
    iAssert (α ↪N (n; [fin_to_nat a]))%I with "[Hα]" as "Hα".
    { iExists [a]. simpl. iFrame. done. }
    iApply rel_rand_l.
    iFrame. iIntros "!>Hα %Hlt". fold modn pow.
    do 2rel_pure_l.
    unshelve iApply (rel_pure_step_l' _
                (let: "gA" := #(g ^ a `mod` n)%nat in
     (do: channel1 InjL ("gA", bob));; 
     let: "r" := do: channel1 InjR bob in
     match: "r" with
       InjL <> => 
         KontV
           (HandleCtx getKey1
              (λ: "p" "k",
                 match: "p" with
                   InjL <> =>
                     let: "a" := #()%V;; rand(#lbl:α) #n in
                     let: "gA" := (rec: "mod" "a" := if: "a" < #n then "a" else "mod" ("a" - #n))
                                    ((rec: "pow" "b" "e" :=
                                        if: "e" = #0 then #1 else "b" * "pow" "b" ("e" - #1)) #g "a") in
                     (do: channel1 InjL ("gA", bob));; 
                     let: "r" := do: channel1 InjR bob in
                     match: "r" with
                       InjL <> => "k" (InjL #()%V)
                     | InjR "gB" =>
                       let: "key" := (rec: "mod" "a" := if: "a" < #n then "a" else "mod" ("a" - #n))
                                       ((rec: "pow" "b" "e" :=
                                           if: "e" = #0 then #1 else "b" * "pow" "b" ("e" - #1)) "gB"
                                          "a") in "k" (InjR "key")
                     end
                 | InjR <> =>
                   let: "b" := #()%V;; rand #n in
                   let: "gB" := (rec: "mod" "a" := if: "a" < #n then "a" else "mod" ("a" - #n))
                                  ((rec: "pow" "b" "e" :=
                                      if: "e" = #0 then #1 else "b" * "pow" "b" ("e" - #1)) #g "b") in
                   (do: channel1 InjL ("gB", alice));; 
                   let: "r" := do: channel1 InjR alice in
                   match: "r" with
                     InjL <> => "k" (InjL #()%V)
                   | InjR "gA" =>
                     let: "key" := (rec: "mod" "a" := if: "a" < #n then "a" else "mod" ("a" - #n))
                                     ((rec: "pow" "b" "e" :=
                                         if: "e" = #0 then #1 else "b" * "pow" "b" ("e" - #1)) "gA"
                                        "b") in "k" (InjR "key")
                   end
                 end) (λ: "y", "y") :: k1) (InjL #()%V)
     | InjR "gB" =>
       let: "key" := (rec: "mod" "a" := if: "a" < #n then "a" else "mod" ("a" - #n))
                       ((rec: "pow" "b" "e" := if: "e" = #0 then #1 else "b" * "pow" "b" ("e" - #1))
                          "gB" #a) in
       KontV
         (HandleCtx getKey1
            (λ: "p" "k",
               match: "p" with
                 InjL <> =>
                   let: "a" := #()%V;; rand(#lbl:α) #n in
                   let: "gA" := (rec: "mod" "a" := if: "a" < #n then "a" else "mod" ("a" - #n))
                                  ((rec: "pow" "b" "e" :=
                                      if: "e" = #0 then #1 else "b" * "pow" "b" ("e" - #1)) #g "a") in
                   (do: channel1 InjL ("gA", bob));; 
                   let: "r" := do: channel1 InjR bob in
                   match: "r" with
                     InjL <> => "k" (InjL #()%V)
                   | InjR "gB" =>
                     let: "key" := (rec: "mod" "a" := if: "a" < #n then "a" else "mod" ("a" - #n))
                                     ((rec: "pow" "b" "e" :=
                                         if: "e" = #0 then #1 else "b" * "pow" "b" ("e" - #1)) "gB"
                                        "a") in "k" (InjR "key")
                   end
               | InjR <> =>
                 let: "b" := #()%V;; rand #n in
                 let: "gB" := (rec: "mod" "a" := if: "a" < #n then "a" else "mod" ("a" - #n))
                                ((rec: "pow" "b" "e" :=
                                    if: "e" = #0 then #1 else "b" * "pow" "b" ("e" - #1)) #g "b") in
                 (do: channel1 InjL ("gB", alice));; 
                 let: "r" := do: channel1 InjR alice in
                 match: "r" with
                   InjL <> => "k" (InjL #()%V)
                 | InjR "gA" =>
                   let: "key" := (rec: "mod" "a" := if: "a" < #n then "a" else "mod" ("a" - #n))
                                   ((rec: "pow" "b" "e" :=
                                       if: "e" = #0 then #1 else "b" * "pow" "b" ("e" - #1)) "gA" "b") in
                   "k" (InjR "key")
                 end
               end) (λ: "y", "y") :: k1) (InjR "key")
     end)
                _ True); [done|admit|done|].
    iIntros "!>".
    rel_pures_l. fold modn pow.
    
    iApply (rel_bind' [_] [_]); [iApply traversable_iThyTraverse|].
    iApply rel_introduction'.
    iExists _, _, [], [], _. do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
    iSplitL; [|by iIntros "!>" (??) "H"; iApply "H"].
    iLeft.
    iExists _. do 2 (iSplit; try (iPureIntro; done)). iModIntro.
    iApply rel_value. rel_pures_l. rel_pures_r.

    iApply (rel_bind' [_] [_]); [iApply traversable_iThyTraverse|].
    iApply rel_introduction'.
    iExists _, _, [], [], _. do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
    iSplitL; [|by iIntros "!>" (??) "H"; iApply "H"].
    iRight.
    do 2 (iSplit; try (iPureIntro; done)). iModIntro.
    iSplit.
    2 : { rel_pures_l. rel_pures_r. iModIntro. rel_pures_l. rel_pures_r.
          iDestruct ("HQ" with "HSNone") as "HQNone".
          iDestruct ("Hk" with "HQNone") as "HkNone".
          iApply ("IH" with "HkNone").
          admit. }

    iIntros (gB). iExists a, (g ^ (a * b) `mod`n)%nat. iIntros (Hgba).
    rel_pures_l. rel_pures_r. iModIntro.
    do 5 rel_pure_l. fold modn pow.
    unshelve iApply (rel_pure_step_l' _ (let: "key" := #(gB ^ a `mod` n)%nat in
     KontV
       (HandleCtx getKey1
          (λ: "p" "k",
             match: "p" with
               InjL <> =>
                 let: "a" := #()%V;; rand(#lbl:α) #n in
                 let: "gA" := modn (pow #g "a") in
                 (do: channel1 InjL ("gA", bob));; 
                 let: "r" := do: channel1 InjR bob in match: "r" with InjL <> => "k" (InjL #()%V) | InjR "gB" => let: "key" := modn (pow "gB" "a") in "k" (InjR "key") end
             | InjR <> =>
               let: "b" := #()%V;; rand #n in
               let: "gB" := modn (pow #g "b") in
               (do: channel1 InjL ("gB", alice));; 
               let: "r" := do: channel1 InjR alice in match: "r" with InjL <> => "k" (InjL #()%V) | InjR "gA" => let: "key" := modn (pow "gA" "b") in "k" (InjR "key") end
                             end) (λ: "y", "y") :: k1) (InjR "key"))%E _ True);[done|admit|done|].
    iModIntro. rewrite Hgba.
    rel_pures_l. rel_pures_r. cdone. 
  Admitted. 
     
    
  Lemma DH_KE_DH_SIM_F_KE (g : nat) f1 f2:
    (∀ s n, val_subst s n f1 = f1) →
           (∀ s n, val_subst s n f2 = f2) →
    REL f1 ≤ f2 <|T|> {{ (λ v1 v2, ⌜v1 = #()%V⌝ ∧ ⌜v2 = #()%V⌝) }} -∗
    REL DH_KE getKey1 channel1 g f1 ≤ DH_SIM channel2 g (F_KE getKey2 channel2 f2) <|X|> {{ (λ v1 v2, ⌜ v1 = v2 ⌝) }}.
  Proof.
    iIntros (Hf1closed Hf2closed) "Hff".
    unfold F_KE. unfold DH_SIM. unfold sample.
    rel_pures_r.

    iApply rel_randU_empty_r. iIntros (m Hlt).
    iApply fupd_rel.
    iMod (ghost_var_alloc m) as (γ) "Hm". iModIntro.
    
    rel_pures_r. rewrite Hf2closed.
    iApply (rel_exhaustion [_] [_; _] with "Hff").
    iSplit; [iIntros (v1 v2) "(-> & ->)"; rel_pures_l; by rel_pures_r|].
    iIntros (e1 e2 Q) "(-> & -> & #HQ) #HKont".
    rel_pures_l; first set_solver.
    rel_pures_r; first set_solver.
    
    iApply rel_couple_rand_rand; [done|]. iIntros (a).
    iApply fupd_rel.
    iMod (ghost_var_alloc a) as (γ') "Ha".
    iModIntro.

    do 2rel_pure_l. do 2rel_pure_r.
    iApply (rel_bind [_; _] [_; _] _ _ iThyBot); [iApply traversable_bot | iApply iThy_le_bot | ].
    iApply rel_wand; [iApply pow_rel|].
    iIntros (v1 v2) "!> (-> & ->)".
    iApply (rel_bind [_] [_]); [iApply traversable_bot| iApply iThy_le_bot| ].
    iApply rel_wand; [iApply modn_rel|].
    iIntros (v1 v2) "!> (-> & ->)". 
    rel_pures_l. rel_pures_r.
    iApply (rel_bind' [_] [_]); first admit.
    iApply rel_introduction; [|by iIntros (s1 s2) "!>!> ?"].
    iLeft.
    iExists ((g ^ a) `mod` DH_channel.n)%nat. simpl. do 2 (iSplit; try (iPureIntro; done)).
    iModIntro.
    iApply rel_value.
    rel_pures_l.
    rel_pures_r; [set_solver| ].

    iApply (rel_bind' [_] [_]); first admit.
    iApply rel_introduction; [|by iIntros (s1 s2) "!>!> ?"].
    iRight. do 2 (iSplit; try (iPureIntro; done)).
    iModIntro.
    iSplit.
    - iIntros (gB).
      (* iExists a, m. *)
      rel_pures_r. rel_pures_l. iModIntro.
      do 10 rel_pure_r. do 4 rel_pure_r.
      rel_pures_r. do 5rel_pure_l.
      iApply (rel_bind' [_;_]); first admit.
      pose proof (pow_un gB a) as (s & Hstep).
      iApply (rel_pure_step_l' _ _ _ True s); [done | ].
      iIntros "!>". clear s Hstep.
      iApply rel_value.
      iApply (rel_bind' [_]); first admit.
      pose proof (modn_un (gB ^ a)) as (s & Hstep).
      iApply rel_pure_step_l'; [done|].
      iIntros "!>". clear s Hstep.
      iApply rel_value.
      rel_pures_l. iPureIntro. f_equal. admit.
    - rel_pures_r. rel_pures_l. iModIntro.
      rel_pures_r. rel_pures_l. done.
  Admitted.

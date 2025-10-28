From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Import ghost_var.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode spec_rules spec_ra notation.

Section implementation.

  Definition n : nat := 1234.

  Definition sample : expr := λ: <>, rand #n.

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
    handle: f with
    | effect getKey "p", rec "k" =>
        match: "p" with
          InjL <> =>
            let: "a" := sample #()%V in
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

End implementation.

Section handlee_verification.
  Context `{!probblazeRGS Σ, !ghost_varG Σ nat}.
  Context (channel1 channel2 getKey1 getKey2 : label).

  Program Definition GetKey1 : iThy Σ :=
    λ e1 e2, (λne Q,
                ⌜ e1 = do: getKey1 (InjL #()%V) ⌝%E ∗
                ⌜ e2 = do: getKey2 (InjL #()%V) ⌝%E ∗
                □ Q (Val #()%V) (Val #()%V)
             )%I.
  Next Obligation. solve_proper. Qed.
    
  Program Definition SendBob : iThy Σ :=
    λ e1 e2, (λne Q,
                ∃ m : nat,(*  ∃ γ : gname,
                     ghost_var γ (1/2) m ∗ *)
                  ⌜ e1 = do: channel1 (SendV (#m, bob)) ⌝%E ∗
                  ⌜ e2 = do: channel2 (SendV (#m, bob)) ⌝%E ∗
                  □ Q (Val #()%V) (Val #()%V)
             )%I. 
  Next Obligation. solve_proper. Qed.

  Program Definition RecvBob : iThy Σ :=
    λ e1 e2, (λne Q,
                ⌜ e1 = do: channel1 (RecvV bob) ⌝%E ∗
                ⌜ e2 = do: channel2 (RecvV bob) ⌝%E ∗
                □ ((∀ gB : nat, (* ∃ a m γ γ', ⌜ (gB ^ a) `mod` DH_channel.n = m ⌝ ∗ ghost_var γ (1/2) a ∗ ghost_var γ' (1/2) m -∗ *)
                                       Q (SOME #gB) (SOME #gB)) ∧ Q NONE NONE)
                  )%I.
  Next Obligation. solve_proper. Qed.
  
  Definition T : iThy Σ := GetKey1.
  Definition X : iThy Σ := iThySum (SendBob) (RecvBob).


  Lemma pow_rel (g n : nat) :
    ⊢ REL pow #g #n ≤ pow #g #n <|iThyBot|> {{ (λ v1 v2, ⌜ v1 = #(g ^ n)%nat ⌝ ∗ ⌜ v2 = #(g ^ n)%nat ⌝) }}.
  Admitted.

  (* Show this later with the actual m *)
  Lemma pow_un (g n : nat ) :
    ∃ m : nat, PureExec True m (pow #g #n) (#(g ^ n)%nat).
  Admitted.

  Lemma modn_rel (m : nat) :
    ⊢ REL modn #m ≤ modn #m <|iThyBot|> {{ (λ v1 v2, ⌜ v1 = #(m `mod` n)%nat ⌝ ∗ ⌜ v2 = #(m `mod` n)%nat ⌝) }}.
  Admitted.

  Lemma modn_un (m : nat) :
    ∃ s, PureExec True s (modn #m) (#(m `mod` n)%nat). 
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

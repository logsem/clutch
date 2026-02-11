(* ask.v *)

From iris.proofmode Require Import base tactics classes.
From clutch.prob_eff_lang.probblaze Require Import logic proofmode  spec_rules.


(* A sanity check from blaze. The example is using BREL, which can handle labels *)
(* Notice how a new label is allocated and a iThyBot is added to the iLblThy L   *)
(* This can always be added. At brel_exhaustion in run_ask_handler_refines       *)
(* the iThyBot is replaced with the theory AskT                                  *)
(* ============================================================================= *)
(* Implementation. *)

Section implementation.

  Definition run_ask_handler (ask : eff_val) (e : expr) (x : expr) : expr :=
    handle: e with
    | effect ask <>, rec "k" as multi => "k" x
    | return "z" => "z"
    end.

  Definition run_ask : val := λ: "x" "main",
    effect "ask"
    run_ask_handler "ask" ("main" (λ: <>, do: "ask" #()%V)) "x".

End implementation.


Section verification.
  Context `{!probblazeRGS Σ}.

  Definition both_int (x : Z) (v1 v2 : val) : iProp Σ :=
    ⌜ v1 = #x ⌝ ∗ ⌜ v2 = #x ⌝.

  Program Definition AskT (ask : label) (x : Z) : iThy Σ :=
    λ e1 e2, λne Q,
      (⌜ e1 = do: ask #()%V ⌝%E ∗ ⌜ e2 = #x ⌝ ∗ □ Q #x #x)%I.
  Next Obligation. solve_proper. Qed.

  Lemma run_ask_handler_refines (ask : label) (x : Z) L R e1 e2 :
    BREL e1 ≤ e2 <|([ask], [], AskT ask x) :: L|> {{R}} -∗
    BREL run_ask_handler ask e1 #x ≤ e2 <|([ask], [], iThyBot) :: L|> {{R}}.
  Proof.
    iLöb as "IH" forall (e1 e2).
    iIntros "He". rewrite /run_ask_handler.
    iApply (brel_exhaustion _ _ [_] with "He"); try done.
    iSplit; [by iIntros "!> %% HR"; by brel_pures_l|].
    iIntros "!> %k1 %k2 %%% %Hk1 %Hk2 (-> & -> & #HQ) #Hk".
    brel_pures_l. { by apply Hk1; apply elem_of_list_singleton. }
    iApply "IH". by iApply "Hk".
  Qed.

  Lemma run_ask_refines (main1 main2 : val) (x : Z) L R :
    (∀ (ask1 ask2 : val) M,
      □ BREL ask1 #()%V ≤ ask2 #()%V <|M|> {{both_int x}} -∗
      BREL main1 ask1 ≤ main2 ask2 <|M ++ L|> {{R}}
    ) -∗
    BREL run_ask #x main1 ≤ main2 (λ: <>, #x) <|L|> {{R}}.
  Proof.
    iIntros "Hmain".
    rewrite /run_ask. brel_pures_l. brel_pures_r.
    iApply brel_new_theory.
    iApply brel_effect_l. iIntros "!> %ask Hask !>".
    iApply (brel_add_label_l with "Hask"). brel_pures_l.
    iApply run_ask_handler_refines.
    iApply ("Hmain" $! _ _ [([ask], [], AskT ask x)]).
    iIntros "!>". brel_pures_l. brel_pures_r.
    iApply brel_introduction'. { apply elem_of_cons. by left. }
    iExists (do: ask #()%V)%E, #x, [], [], _.
    do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
    iSplit; [|by iIntros "!> %% H"; iApply "H"].
    do 2 (iSplit; [done|]). by iModIntro; iApply brel_value.
  Qed.

End verification.

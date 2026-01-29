From iris.proofmode Require Import base tactics classes.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode spec_rules spec_ra notation.

Section implementation.

  Definition whileE (get : expr) (set : expr) : expr :=
    (rec: "while" <> :=
       if: get #(()%V) < #0 then #(()%V) else
         set (get #(()%V) - rand #1%nat);; "while" #(()%V)
    ) #(()%V).

  Definition countdown : val := λ: "get" "set",
                                  "set" #10;; whileE "get" "set".
                                                       
  Definition get (timer : label) : val := λ: <>,
    do: timer (InjL #()%V).

  Definition set (timer : label) : val := λ: "y",
    do: timer (InjR "y").

  Definition run_st_passing_handler (timer : eff_val) (e : expr) (init : expr) : expr :=
    handle: e with
    | effect timer "request", rec "k"  => λ: "x",
        match: "request" with
          InjL <>  => "k" "x" "x"
        | InjR "y" => "k" #()%V "y"
        end
    | return "y" => λ: <>, "y"
    end init.

  Definition run_st_passing (timer : eff_val) : val := λ: "init" "main",
                                                         run_st_passing_handler timer ("main" #()%V) "init".

End implementation.

Section handlee_verification.
  Context `{!probblazeRGS Σ} `{!frac_cell Σ}.
  Context (timer : label).

  Program Definition Read (l : loc) : iThy Σ := λ e1 e2, (λne Q,
    ∃ (x : Z),
    l ↦ₛ{# 1/2} #x ∗
    ⌜ e1 = do: timer (InjLV #()%V) ⌝%E ∗
    ⌜ e2 = ! #l ⌝%E ∗
    □ (l ↦ₛ{# 1/2} #x -∗ Q #x #x)
  )%I.
  Next Obligation. solve_proper. Qed.

  Program Definition Write (l : loc) : iThy Σ := λ e1 e2, (λne Q,
    ∃ (x y : Z),
    l ↦ₛ{# 1/2} #x ∗
    ⌜ e1 = do: timer (InjRV #y) ⌝%E ∗
    ⌜ e2 = (#l <- #y)%E ⌝ ∗
    □ (l ↦ₛ{# 1/2} #y -∗ Q #()%V #()%V)
  )%I.
  Next Obligation. solve_proper. Qed.

  Definition Timer l : iThy Σ := iThySum (Read l) (Write l).

  Lemma while_refines (l : loc) (x : Z) :
    l ↦ₛ{# 1/2} #x -∗
    REL whileE (get timer) (set timer) ≤
        whileE (λ: <>, ! #l)%V (λ: "y", #l <- "y")%V
        <|iThyTraverse [timer] [] (Timer l)|>
        {{ (λ v1 v2, ⌜ v1 = v2 ⌝)}}.
  Proof.
    rewrite /whileE /get /set.
    iIntros "Hl". 
    rel_pure_l. rel_pure_r.
    iLöb as "IH" forall (x).
    rel_pures_l. rel_pures_r.
    iApply (rel_bind' [_; BinOpLCtx _ _] [_; BinOpLCtx _ _]).
    { by iApply traversable_iThyTraverse; apply _. }
    iApply rel_introduction'.
    iExists _, _, [], [], _.
    do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
    iSplitL; [|by iIntros "!>" (??) "H"; iApply "H"].
    iLeft. iFrame. do 2 (iSplit; [done|]).
    iIntros "!> Hl". iApply rel_value.
    rel_pures_l. rel_pures_r.
    case_eq (decide (x < 0)%Z).
    - intros Hneg Hdec. rewrite bool_decide_eq_true_2; [|done].
      rel_pures_l. rel_pures_r. by auto.
    - intros Hnneg Hdec. rewrite bool_decide_eq_false_2; [|done].
      rel_pures_l. rel_pures_r.
      iApply rel_couple_rand_rand; [done|simpl; iIntros (n)]. (* rand_rand coupling *)
      rel_pures_l. rel_pures_r.
      iApply (rel_bind' [_; _; BinOpLCtx _ _] [_; _; BinOpLCtx _ _]).
      { by iApply traversable_iThyTraverse; apply _. }
      iApply rel_introduction'.
      iExists _, _, [], [], _.
      do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
      iSplitL; [|by iIntros "!>" (??) "H"; iApply "H"].
      iLeft. iFrame. do 2 (iSplit; [done|]).
      iIntros "!> Hl". iApply rel_value.
      rel_pures_l. rel_pures_r.
      iApply (rel_bind' [_] [_]).
      { by iApply traversable_iThyTraverse; apply _. }
      iApply rel_introduction'.
      iExists _, _, [], [], _.
      do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
      iSplitL; [|by iIntros "!>" (??) "H"; iApply "H"].
      iRight. iFrame. iExists (x - n)%Z. do 2 (iSplit; [done|]).
      iIntros "!> Hl". iApply rel_value.
      do 2 rel_pure_l. do 2 rel_pure_r.
      by iApply ("IH" with "Hl").
  Qed.

  Lemma countdown_refines (l : loc) (x : Z) :
    l ↦ₛ{# 1 / 2} #x -∗
    REL countdown (get timer) (set timer) ≤
        countdown (λ: <>, ! #l)%V (λ: "y", #l <- "y")%V
        <|iThyTraverse [timer] [] (Timer l)|>
        {{ (λ v1 v2, ⌜ v1 = v2 ⌝) }}.
  Proof.
    iIntros "Hl". rewrite /countdown /get /set.
    rel_pures_l. rel_pures_r.
    iApply rel_introduction'.
    iExists (do: timer (InjRV #10%Z))%E, (#l <- #10%Z)%E.
    iExists [AppRCtx _], [AppRCtx _], _.
    do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
    iSplitL; [|by iIntros "!>" (??) "H"; iApply "H"].
    iRight. iExists x, 10%Z. iFrame.
    do 2 (iSplit; [done|]).
    iIntros "!> Hl".
    do 2 rel_pure_l.
    do 2 rel_pure_r.
    iApply (while_refines with "Hl").
  Qed.

End handlee_verification.

Section implementation2.

  Definition whileE2 (get : expr) (decrease : expr) : expr :=
    (rec: "while" <> :=
       if: get #(()%V) < #0 then #(()%V) else
         decrease #()%V ;; "while" #(()%V)
    ) #(()%V).

  Definition countdown2 : val := λ: "get" "set" "decrease" ,
                                  "set" #10;; whileE2 "get" "decrease".
                                                       
  Definition get2 (timer : label) : val := λ: <>,
    do: timer (InjL #()%V).

  Definition set2 (timer : label) : val := λ: "y",
    do: timer (InjR (InjR "y")).
                                              
  Definition decrease2 (timer : label) : val := λ: <>,
    do: timer (InjR (InjL #()%V)). 

  Definition run_st_passing_handler2 (timer : eff_val) (e : expr) (init : expr) : expr :=
    handle: e with
    | effect timer "request", rec "k"  => λ: "x",
        match: "request" with
          InjL <>  => "k" "x" "x"
        | InjR "y" =>
            match: "y" with
              InjL <> => "k" #()%V ("x" - rand #1)
            | InjR "z" => "k" #()%V "z"
            end
        end
    | return "y" => λ: <>, "y"
    end init.

  Definition run_st_passing2 (timer : eff_val) : val := λ: "init" "main",
                                                          run_st_passing_handler2 timer ("main" #()%V) "init".

  Definition run_spec2 : val := λ: "init" "main",
    let: "r" := ref "init" in
    let: "get" := λ: <>, !"r" in
    let: "set" := λ: "y", "r" <- "y" in
    let: "decrease" := λ: <>, "r" <- !"r" - rand #1 in
    "main" "get" "set" "decrease".

  
End implementation2.

Section handlee_verification2.
  Context `{!probblazeRGS Σ} `{!frac_cell Σ}.
  Context (timer : label).

  Program Definition Read2 (l : loc) : iThy Σ := λ e1 e2, (λne Q,
    ∃ (x : Z),
    l ↦ₛ{# 1/2} #x ∗
    ⌜ e1 = do: timer (InjLV #()%V) ⌝%E ∗
    ⌜ e2 = ! #l ⌝%E ∗
    □ (l ↦ₛ{# 1/2} #x -∗ Q #x #x)
  )%I.
  Next Obligation. solve_proper. Qed.

  Program Definition Write2 (l : loc) : iThy Σ := λ e1 e2, (λne Q,
    ∃ (x y : Z),
    l ↦ₛ{# 1/2} #x ∗
    ⌜ e1 = do: timer (InjRV (InjRV #y)) ⌝%E ∗
    ⌜ e2 = (#l <- #y)%E ⌝ ∗
    □ (l ↦ₛ{# 1/2} #y -∗ Q #()%V #()%V)
  )%I.
  Next Obligation. solve_proper. Qed.


  Program Definition Decrease2 (l : loc) : iThy Σ := λ e1 e2, (λne Q,
   ∃ (x : Z),
     l ↦ₛ{# 1/2} #x ∗
     ⌜ e1 = do: timer (InjRV (InjLV #()%V)) ⌝%E ∗
     ⌜ e2 = (#l <- ! #l - rand #1)%E ⌝ ∗
     □ (∀ n, l ↦ₛ{# 1/2} #(x - n) -∗ Q #()%V #()%V)
       )%I.
  Next Obligation. solve_proper. Qed.

  Definition Timer2 l : iThy Σ := iThySum (Read2 l) (iThySum (Write2 l) (Decrease2 l)).

   Lemma while_refines2 (l : loc) (x : Z) :
    l ↦ₛ{# 1/2} #x -∗
    REL whileE2 (get2 timer) (decrease2 timer) ≤
        whileE2 (λ: <>, ! #l)%V (λ: <>, #l <- ! #l - rand #1)%V
        <|iThyTraverse [timer] [] (Timer2 l)|>
        {{ (λ v1 v2, ⌜ v1 = v2 ⌝)}}.
   Proof.
     rewrite /whileE2 /get2 /decrease2.
     iIntros "Hl". 
     rel_pure_l. rel_pure_r.
     iLöb as "IH" forall (x).
     rel_pures_l. rel_pures_r.
     iApply (rel_bind' [_; BinOpLCtx _ _] [_; BinOpLCtx _ _]).
     { by iApply traversable_iThyTraverse; apply _. }
     iApply rel_introduction'.
     iExists _, _, [], [], _.
     do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
     iSplitL; [| by iIntros "!>" (??) "?"].
     iLeft. iFrame. do 2 (iSplit; [done|]).
     iIntros "!> Hl". iApply rel_value.
     rel_pure_l. rel_pure_r.
     case_eq (decide (x < 0)%Z); iIntros (Hneq Hdec).
     - rewrite bool_decide_eq_true_2; [|done].
       rel_pures_l. rel_pures_r. done.
     - rewrite bool_decide_eq_false_2; [|done].
       rel_pures_l. rel_pures_r.
       iApply (rel_bind' [_] [_]).
       { by iApply traversable_iThyTraverse; apply _. }
       iApply rel_introduction'.
       iExists _, _, [], [], _.
       do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
       iSplitL; [| by iIntros "!>" (??) "?"].
       iRight. iRight.
       iFrame. do 2 (iSplit; [done|]).
       iIntros "!>" (n) "Hl".
       iApply rel_value.
       do 2 (rel_pure_l; rel_pure_r).
       by iApply "IH".
   Qed.

    Lemma countdown_refines2 (l : loc) (x : Z) :
    l ↦ₛ{# 1 / 2} #x -∗
    REL countdown2 (get2 timer) (set2 timer) (decrease2 timer) ≤
        countdown2 (λ: <>, ! #l)%V (λ: "y", #l <- "y")%V (λ: <>, #l <- ! #l - rand #1)%V
        <|iThyTraverse [timer] [] (Timer2 l)|>
        {{ (λ v1 v2, ⌜ v1 = v2 ⌝) }}.
  Proof.
    iIntros "Hl". rewrite /countdown2 /get2 /set2 /decrease2.
    rel_pures_l. rel_pures_r.
    iApply rel_introduction'.
    iExists (do: timer (InjRV (InjRV #10%Z)))%E, (#l <- #10%Z)%E.
    iExists [AppRCtx _], [AppRCtx _], _.
    do 2 (iSplit; [done|]; iSplit; [iPureIntro; apply _|]).
    iSplitL; [|by iIntros "!>" (??) "H"; iApply "H"].
    iRight. iLeft. iExists x, 10%Z. iFrame.
    do 2 (iSplit; [done|]).
    iIntros "!> Hl". simpl.
    do 2 rel_pure_l.
    do 2 rel_pure_r.
    iApply (while_refines2 with "Hl").
  Qed.
  

End handlee_verification2.

Section handler_verification.
  Context `{!probblazeRGS Σ}.
  Context (timer : label).

  Lemma run_st_passing_handler_refines2 (l : loc) (e1 e2 : expr) (init : Z) :
    l ↦ₛ{# 1/2} #init -∗
    REL e1 ≤ e2 <|iThyTraverse [timer] [] (Timer2 timer l)|> {{ (λ v1 v2, ⌜ v1 = v2 ⌝) }} -∗
    REL run_st_passing_handler2 timer e1 #init ≤ e2
        <|iThyBot|>
        {{ (λ v1 v2, ⌜ v1 = v2 ⌝) }}.
  Proof.
    iIntros "Hl He".
    iLöb as "IH" forall (e1 e2 init).
    rewrite /run_st_passing_handler2.
    iApply (rel_exhaustion [_; _] [] with "He").
    iSplit; [by iIntros (??) "->"; rel_pures_l|].
    clear e1 e2. iIntros (e1 e2 ?)
      "[%e1' [%e2' [%k1 [%k2 [%S
        (-> & %Hk1 & -> & %Hk2 & [HRead|[HWrite |Hdecrease]] & #HQ)
       ]]]]] #Hk".
    - iDestruct "HRead" as "[%x [Hl'  (-> & -> & #HS)]]".
      iDestruct (ghost_map_elem_agree with "Hl Hl'") as "->".
  (*     rel_pures_l. { apply Hk1. set_solver. }
         iApply (rel_load_r with "Hl"). iIntros "Hl".
         iApply ("IH" with "Hl").
         iApply "Hk". iApply "HQ". by iApply ("HS" with "Hl'").
       - iDestruct "HWrite" as "[%x [%y [Hl' (-> & -> & #HS)]]]".
         iDestruct (ghost_map_elem_combine with "Hl Hl'") as "[Hl ->]".
         rewrite dfrac_op_own Qp.half_half.
         iApply (rel_store_r with "Hl"). iIntros "Hl".
         iEval (rewrite -Qp.half_half) in "Hl".
         iDestruct (ghost_map_elem_fractional with "Hl") as "[Hl Hl']".
         rel_pures_l. { apply Hk1. set_solver. }
         iApply ("IH" with "Hl").
         iApply "Hk". iApply "HQ". by iApply ("HS" with "Hl'").
       - iDestruct "Hdecrease" as "[%x [Hl' (-> & -> & #HS)]]".
         iDestruct (ghost_map_elem_combine with "Hl Hl'") as "[Hl ->]".
         rewrite dfrac_op_own Qp.half_half.
         rel_pures_l. { apply Hk1. set_solver. }
         iApply rel_couple_rand_rand; [done|].
         iIntros (n). rewrite fill_app. simpl.
         iApply (rel_load_r with "Hl"). iIntros "Hl". rewrite fill_app. simpl.
         rel_pure_r. rel_pures_l.
         iApply (rel_store_r with "Hl").
         iIntros "Hl".
         iEval (rewrite -Qp.half_half) in "Hl".
         iDestruct (ghost_map_elem_fractional with "Hl") as "[Hl Hl']".
         iApply ("IH" with "Hl").
         iApply "Hk". iApply "HQ". by iApply "HS".
     Qed. *)
  Admitted.

  Lemma run_st_passing_refines l (main1 : val) (main2 : expr) (init : Z) :
    l ↦ₛ{# 1/2} #init -∗
    REL main1 #()%V ≤ main2 <|iThyTraverse [timer] [] (Timer2 timer l)|> {{ (λ v1 v2, ⌜ v1 = v2 ⌝)}} -∗
    REL run_st_passing2 timer #init main1 ≤ main2 <|iThyBot|> {{ (λ v1 v2, ⌜ v1 = v2 ⌝)}}.
  Proof.
    iIntros "Hl Hmain". rewrite /run_st_passing2. rel_pures_l.
    by iApply (run_st_passing_handler_refines2 with "Hl Hmain").
  Qed.

  Lemma run_st_passing_refines_run_spec (init : Z) :
    let e1 := run_st_passing2 timer #init (λ: <>, countdown2 (get2 timer) (set2 timer) (decrease2 timer))%V in
    let e2 := run_spec2 #init countdown2 in
    ⊢ REL e1 ≤ e2 <|iThyBot|> {{ (λ v1 v2, ⌜ v1 = v2 ⌝) }}.
  Proof.
    iIntros (e1 e2). rewrite /e1 /e2 /run_st_passing2 /run_spec2.
    rel_pures_l. rel_pures_r. iApply rel_alloc_r. iIntros (l) "Hl". rel_pures_r.
    iEval (rewrite -Qp.half_half) in "Hl".
    iDestruct (ghost_map_elem_fractional with "Hl") as "[Hl Hl']".
    iApply (run_st_passing_handler_refines2 with "Hl'").
    by iApply (countdown_refines2 with "Hl").
  Qed.

End handler_verification.

From iris.base_logic Require Export na_invariants.
From clutch.prelude Require Import tactics.
From clutch.common Require Import inject.
From clutch.prob Require Import differential_privacy.
From clutch.diffpriv Require Import adequacy diffpriv proofmode derived_laws.
From clutch.diffpriv.examples Require Import sparse_vector_technique.
From clutch.prob_lang.gwp Require Import gen_weakestpre arith list.




Definition list_count : val :=
  λ: "p" "l", list_length (list_filter "p" "l").

Definition data : list Z := [25; 30; 31; 22; 40; 35; 29; 29; 31; 30]%Z.

(* TODO move to theories/prob_lang/notation.v *)
Notation "e1 <= e2" := (BinOp LeOp e1%E e2%E) : expr_scope.
Notation "e1 ≤ e2" := (BinOp LeOp e1%E e2%E) : expr_scope.

Definition adaptive : val :=
  λ:"data",
  let: "εₛ" := #2 in
  let: "εₗ" := #10 in
  let: "b" := ref #20 in
  let: "counts" := ref [] in

  (* Count the first predicate. This will consume either 2 or 12 credits.
     In either case we know we have enough budget, so we skip the check here.  *)
  let: "count_exact_1" := list_count (λ:"x", "x" < #30) "data" in
  let: "count_coarse_1" := Laplace "εₛ" #10 "count_exact_1" in
  (* Consume 2 credits. *)
  "b" <- ! "b" -  "εₛ" ;;
  "counts" <- ("count_coarse_1" :: !"counts") ;;
  (* If the test succeeds, we consume another 10 credits. *)
  (if: #5 < "count_coarse_1" then
    let: "count_precise_1" := Laplace "εₗ" #10 "count_exact_1" in
    let: "_" := "b" <- ! "b" -  "εₗ" in
    "counts" <- "count_precise_1" :: !"counts"
   else #()) ;;
  (* We have either 18 or 8 credits left. *)

  let: "count_exact_2" := list_count (λ:"x", "x" < #32) "data" in
  let: "count_coarse_2" := Laplace "εₛ" #10 "count_exact_2" in
  (* We still have enough credits for the second coarse count. *)
  let: "_" := "b" <- ! "b" -  "εₛ" in
  "counts" <- ("count_coarse_2" :: !"counts") ;;
  (if: #5 < "count_coarse_2" then
     (* We can only afford a second precise count if the first count was below the threshold. *)
     if: "εₗ" <= !"b" then
       let: "count_precise_2" := Laplace "εₗ" #10 "count_exact_2" in
       let: "_" := "b" <- ! "b" -  "εₗ" in
       "counts" <- "count_precise_2" :: !"counts"
     else #()
   else #()) ;;

  !"counts"
.



Definition predicates : list (Z → bool) := [λ x, bool_decide (x < 30) ; λ x, bool_decide (30 <= x) ; λ x, bool_decide (x `rem` 2 = 0)]%Z.
Definition vpredicates : val :=
  SOMEV ((λ:"x", "x" < #30)
         , SOMEV ((λ:"x", #30 <= "x")
                  , SOMEV ((λ:"x", "x" `rem` #2 = #0), NONEV))).

Definition create_odometer : val :=
  λ:"budget",
  let: "budget_spent" := ref #0 in
  let: "get_spent" := λ:<>, !"budget_spent" in
  let: "try_spend" :=
    λ:"ε", if: "budget" < !"budget_spent" + "ε" then
             #false
           else
             ("budget_spent" <- !"budget_spent" + "ε" ;;
              #true) in
  ("get_spent", "try_spend").

Definition iter_adaptive : val :=
  λ:"threshold" "budget" "data",
    let: "counts" := ref [] in
    let, ("get_spent", "try_spend") := create_odometer "budget" in
  list_iter
    (λ:"pred",
      let: "count" := list_count "pred" "data" in
      if: "try_spend" "ε_coarse" then
        let: "count_coarse" := Laplace "ε_coarse" "den" "count" in
        "counts" <- "count_coarse" :: !"counts" ;;
        if: "threshold" < "count_coarse" then
          if: "try_spend" "ε_precise" then
            let: "count_precise" := Laplace "ε_precise" "den" "count" in
            "counts" <- "count_precise" :: !"counts"
          else #()
        else #()
      else #()
    )
    "data".

(* Instead of just tracking the budget spent, we instead provide a function
   that takes a thunk and runs it if there's enough budget left. *)
Definition create_filter : val :=
  λ:"budget",
  let: "budget_remaining" := ref "budget" in
  let: "try_run" :=
    λ:"ε" "f", if: !"budget_remaining" < "ε" then
             NONE
           else
             ("budget_remaining" <- !"budget_remaining" - "ε" ;;
              SOME ("f" #())) in
  "try_run".

Definition laplace : val :=
  λ:"eps" "mean", Laplace (Fst "eps") (Snd "eps") "mean".

(* TODO add counts to the tail of the list. doesn't matter for privacy but more intuitive. *)
(* TODO can't tell which count came from which predicate. uncomment the bit with the index reference *)
Definition iter_adaptive_acc : val :=
  λ:"ε_coarse" "ε_precise" "den"
    "threshold" "budget" "predicates" "data",
    let: "counts" := ref [] in
    (* let: "index" := ref #0 in *)
    let: "try_run" := create_filter "budget" in
    list_iter
      (λ:"pred",
        let: "count" := list_count "pred" "data" in
        "try_run" "ε_coarse"
          (λ:<>,
             let: "count_coarse" := Laplace "ε_coarse" "den" "count" in
             "counts" <- (
                          (* !"index", *)
                            "count_coarse") :: !"counts" ;;

             if: "threshold" < "count_coarse" then
               "try_run" "ε_precise"
                 (λ:<>,
                    let: "count_precise" := Laplace "ε_precise" "den" "count" in
                    "counts" <- (
                                 (* !"index", *)
                                   "count_precise") :: !"counts")
             else #())
        (*
 ;;
"index" <- !"index" + #1 *)
      )
      "predicates" ;;
    ! "counts".

(* We could factor out the common code between the two successive calls to try_run; not sure that simplifies anything though. *)
(* let: "f" := λ:"count" "ε" "_",
                let: "count_noisy" := Laplace "ε" "den" "count" in
                "counts" <- "count_noisy" :: !"counts" ;;
                "count_noisy"
   in
   "try_run" "ε_coarse"
     (λ:<>, let: "count_noisy" = "f" "ε_coarse" #() in
        if: "threshold" < "count_noisy" then
          "try_run" ("f" "ε_precise")) *)

(* Simpler variant of iter_adaptive_acc. Budget/epsilons are pairs of integers (needs variant of privacy filter). *)
Definition map_adaptive_acc_terse_both : val :=
  λ: "eps_coarse" "eps_precise" "threshold" "budget" "predicates" "data" ,
  let: "try_run" := create_filter "budget" in
  list_map
    (λ: "pred" ,
      let: "count_exact" := list_count "pred" "data" in
      let: "g" := λ:<> , laplace "eps_precise" "count_exact" in
      let: "f" := λ:<> ,
        let: "count_coarse" := laplace "eps_coarse" "count_exact" in
        let: "count_precise" :=
          if: "threshold" < "count_coarse" then
            "try_run" "eps_precise" "g"
          else NONE in
        ("count_coarse", "count_precise")
      in
      "try_run" "eps_coarse" "f")
      "predicates" .


#[local] Open Scope Z.

Section adaptive.
  Context `{!diffprivGS Σ}.

  Lemma create_filter_private K budget den (_ : 0 <= budget) (_ : 0 < den) :
    {{{ ↯m (IZR budget / IZR den) ∗ ⤇ fill K ((of_val create_filter) #budget) }}}
      create_filter #budget
      {{{ try_run, RET try_run;
           ∃ (try_run' : val) l l' budget_remaining,
             ⌜ 0 <= budget_remaining ⌝ ∗
               ↯m (IZR budget_remaining / IZR den) ∗
             l ↦ #budget_remaining ∗
             l' ↦ₛ #budget_remaining ∗
             ⤇ fill K try_run' ∗
             (∀ (ε : Z) K (f f' : val) (budget_remaining : Z) I_f,
                 ⌜ 0 <= ε ⌝ →
                 {{{
                       (* f has to be "ε-private" (although we don't even have adjacent data here) and preserve some invariant.
                          f itself may also rely on having access to the resources required for running try_run. *)
                       (∀ K (budget_remaining' : Z),
                           {{{ ↯m (IZR ε / IZR den) ∗
                               ⤇ fill K ((of_val f') #()) ∗
                               I_f ∗
                               ↯m (IZR budget_remaining' / IZR den) ∗
                               l ↦ #budget_remaining' ∗
                               l' ↦ₛ #budget_remaining'
                           }}}
                             (of_val f) #()
                             {{{ v, RET v; ⤇ fill K (of_val v) ∗ I_f
                                           ∗ ∃ (budget_remaining'' : Z),
                                               ↯m (IZR budget_remaining'' / IZR den) ∗
                                               l ↦ #budget_remaining'' ∗
                                               l' ↦ₛ #budget_remaining''
                       }}})
                       ∗
                         (* and we need the resources that try_run depends on *)
                         ↯m (IZR budget_remaining / IZR den) ∗
                       l ↦ #budget_remaining ∗
                       l' ↦ₛ #budget_remaining ∗
                       I_f ∗
                       ⤇ fill K (try_run' #ε f')
                 }}}
                   ((of_val try_run) #ε f : expr)
                   {{{ v, RET v;
                       (* we get equal results *)
                       ⤇ fill K (of_val v) ∗
                       I_f ∗
                       (* and we get back the resources required for try_run *)
                       ∃ budget_remaining,
                         ↯m (IZR budget_remaining / IZR den) ∗
                         l ↦ #budget_remaining ∗
                         l' ↦ₛ #budget_remaining
             }}})
      }}}.
  Proof with (tp_pures ; wp_pures).
    iIntros "% (ε & rhs) Hpost". rewrite /create_filter...
    tp_alloc as budget_r "budget_r" ; wp_alloc budget_l as "budget_l"...
    iModIntro. iApply "Hpost". iExists _,_,_,_ ; iFrame. iSplit => //.
    iIntros "* % !> * (f_dp & ε & budget_l & budget_r & I_f & rhs) Hpost"... tp_load ; wp_load...
    case_bool_decide as h... 1: iApply "Hpost" ; iFrame ; done.
    assert (ε <= budget_remaining) as h' by lia.
    iDestruct (ecm_split (IZR ε / IZR den)%R (IZR (budget_remaining - ε) / IZR den)%R with "[ε]") as "[ε εrem]".
    1,2: repeat real_solver_partial ; qify_r ; zify_q ; lia.
    1: iApply ecm_eq ; [|iFrame].
    1: { rewrite minus_IZR ; field. intro F. assert (den ≠ 0) as hh by lia. apply hh.
         by apply eq_IZR. }

    tp_load ; wp_load... tp_store ; wp_store...
    tp_bind (f' _) ; wp_bind (f _).
    iApply ("f_dp" with "[$rhs $ε $I_f $budget_l $budget_r $εrem]").
    simpl. iNext. iIntros "* [??]"... iApply "Hpost".
    iFrame. done.
  Qed.

  (* We can make the resources that try_run depends on abstract. *)
  Lemma create_filter_private' K budget den (_ : 0 <= budget) (_ : 0 < den) :
    {{{ ↯m (IZR budget / IZR den) ∗ ⤇ fill K ((of_val create_filter) #budget) }}}
      create_filter #budget
      {{{ try_run, RET try_run;
           ∃ (try_run' : val) (TRY_RUN : iProp Σ),
             ⤇ fill K try_run' ∗
             TRY_RUN ∗
             (∀ (ε : Z) K (f f' : val) I_f,
                 ⌜ 0 <= ε ⌝ →
                 {{{
                       (* f has to be "ε-private" (although we don't even have adjacent data here) and preserve some invariant.
                          f itself may also rely on having access to the resources required for running try_run. *)
                       (∀ K,
                           {{{ ↯m (IZR ε / IZR den) ∗ ⤇ fill K ((of_val f') #()) ∗ I_f ∗ TRY_RUN }}}
                             (of_val f) #()
                             {{{ v, RET v; ⤇ fill K (of_val v) ∗ I_f ∗ TRY_RUN
                       }}})
                       ∗
                         ⤇ fill K (try_run' #ε f') ∗
                       I_f ∗
                       (* and we need the resources that try_run depends on *)
                       TRY_RUN
                 }}}
                   ((of_val try_run) #ε f : expr)
                   {{{ v, RET v;
                       (* we get equal results *)
                       ⤇ fill K (of_val v) ∗
                       I_f ∗
                       (* and we get back the resources required for try_run *)
                       TRY_RUN
             }}})
      }}}.
  Proof with (tp_pures ; wp_pures).
    iIntros "% (ε & rhs) Hpost".
    iApply (create_filter_private with "[$]") => //.
    iNext. iIntros "% (% & % & % & % & % & ε & l & l' & rhs & #h)".
    iApply "Hpost".
    set (inv := (∃ budget_remaining,
                  ↯m (IZR budget_remaining / IZR den) ∗
                  l ↦ #budget_remaining ∗
                  l' ↦ₛ #budget_remaining)%I).
    iExists _,inv. iFrame.
    iIntros "* % !> * (#f_dp & rhs & I_f & TRY_RUN) Hpost"...
    iDestruct "TRY_RUN" as "(% & ε & l & l')".
    iApply ("h" $! ε _ f f' budget_remaining0 I_f with "[] [-Hpost] [Hpost]") => // ; iFrame.
    iIntros "* % !> (ε & rhs & if & εrem & l & l') Hpost".
    iApply ("f_dp" with "[-Hpost]") ; iFrame.
  Qed.

  Definition is_predicate {A} `[Inject A val] (pred : A -> bool) (vpred : val) : iProp Σ :=
    ∀ x, {{{ True }}} vpred (inject x) {{{ w, RET w; ⌜w = (inject (pred x))⌝ }}}.

  Definition is_spec_predicate {A} `[Inject A val] (pred : A -> bool) (vpred : val) : iProp Σ :=
    ∀ x, G{{{ True }}} vpred (inject x) @ gwp_spec ; ⊤ {{{ w, RET w; ⌜w = (inject (pred x))⌝ }}}.

  Fixpoint is_predicate_list {A} `[Inject A val] (l : list (A -> bool)) (v : val) : iProp Σ :=
    match l with
    | [] => ⌜v = NONEV⌝
    | pred::l' => ∃ vpred vl',
    ⌜v = SOMEV (vpred, vl')⌝ 
     ∗ is_predicate pred vpred ∗ is_spec_predicate pred vpred ∗ is_predicate_list l' vl' end.


  Lemma filter_sens (P : Z → bool) (f : val) :
    (∀ (x : Z),
        {{{ True }}}
          f (inject x)
          {{{ w, RET w; ⌜w = inject (P x)⌝ }}})
    -∗
    (∀ (x : Z),
        G{{{ True }}}
          f (inject x) @ gwp_spec ; ⊤
          {{{ w, RET w; ⌜w = inject (P x)⌝ }}})
    -∗
    hoare_sensitive (list_filter f) 1 (dlist Z) (dlist Z).
  Proof.
    iIntros "* #Hf #Hf'".
    iIntros (?) "* !> * rhs HΦ".
    simpl.
    iPoseProof (gwp_list_filter (g:=gwp_spec) _ x' f (inject x') _
                  (λ v, ⌜is_list (filter P x') v⌝)%I with "[] []") as "hh'" => // ; [iSplit|..].
    1: { iIntros (??) "!> * _ h". by iApply "Hf'". }
    1: iPureIntro ; apply is_list_inject.
    1: done.
    { simpl. iIntros. done. }
    simpl. iMod ("hh'" with "rhs") as "(% & rhs & %)".
    iApply (gwp_list_filter (g:=gwp_wpre) _ x f (inject x) _ _ %I with "[Hf] [HΦ rhs]") => //.
    1: iSplit.
    1: { iIntros (??) "!> * _ h". by iApply "Hf". }
    1: iPureIntro ; apply is_list_inject.
    1: done.
    simpl. iNext. iIntros. iApply "HΦ".
    iExists (filter P x), (filter P x').
    repeat iSplit ; iFrame ; try iPureIntro.
    - apply is_list_inject => //.
    - assert (v = (examples.list.inject_list (filter P x'))) as -> => //.
      apply is_list_inject => //.
    - rewrite Rmult_1_l. apply IZR_le.
      apply list_filter_bound.
  Qed.


  Lemma length_sens :
    ⊢ hoare_sensitive list_length 1 (dlist Z) dZ.
  Proof.
    iIntros (?) "* !> * rhs HΦ".
    simpl.

    iMod (gwp_list_length (g:=gwp_spec) _ x' (inject x')
                  (λ v, ⌜v = #(List.length x')⌝)%I with "[] [] [rhs]") as "(% & rhs & %)" => //.
    1: iPureIntro ; by apply is_list_inject.
    { simpl. iIntros. subst. done. }
    iApply (gwp_list_length (g:=gwp_wpre) _ x (inject x) with "[] [HΦ rhs]") => //.
    1: iPureIntro ; by apply is_list_inject.
    simpl. iNext. iIntros. iApply "HΦ". iExists (length x),(length x'). simplify_eq.
    repeat iSplit ; iFrame ; iPureIntro => //. rewrite Rmult_1_l.
    rewrite Rabs_Zabs.
    (* Set Printing Coercions. *)
    qify_r ; zify_q. ring_simplify.
    apply list_length_bound.    
  Qed. 

  Lemma wp_adaptive (ds1 ds2 : list Z) dsv1 dsv2 K :
    is_list ds1 dsv1 →
    is_list ds2 dsv2 →
    list_dist ds1 ds2 <= 1 →
    ↯m (IZR 20 / IZR 10) -∗
    ⤇ fill K (adaptive dsv2) -∗
    WP adaptive dsv1 {{ v, ⤇ fill K (of_val v) }}.
  Proof with (tp_pures ; wp_pures).
    iIntros "* % %". iIntros "%adj". iIntros "ε rhs". rewrite /adaptive/list_count...
    tp_alloc as b_r "b_r". wp_alloc b_l as "b_l"...
    tp_alloc as counts_r "counts_r". wp_alloc counts_l as "counts_l"...
    tp_bind (list_filter _ _).
    wp_bind (list_filter _ _).
    replace dsv1 with (inject ds1).
    2: symmetry ; by apply is_list_inject.
    replace dsv2 with (inject ds2).
    2: symmetry ; by apply is_list_inject.
    wp_apply (wp_wand with "[rhs]").
    { iApply (filter_sens $! _ _ _ _ _ with "rhs"). iNext. iIntros. done. }
    simpl.
    iIntros "% (%ds_f1_l&%ds_f1_r&->&rhs&%d_out)".
    tp_bind (list_length _).
    wp_bind (list_length _).
    wp_apply (wp_wand with "[rhs]").
    { iApply (length_sens $! _ _ _ _ with "rhs"). iNext. iIntros. done. }
    simpl.
    iIntros "% (%len_f_l&%len_f_r&->&rhs&%d_out')"...

    tp_bind (Laplace _ _ _).
    wp_bind (Laplace _ _ _).
    iDestruct (ecm_split (IZR 2 / IZR 10)%R (IZR 18 / IZR 10)%R with "[ε]") as "[εₛ ε]".
    1,2: real_solver. 1: iApply ecm_eq ; [|iFrame] ; real_solver.

    assert (Z.abs (len_f_l - len_f_r) <= 1).
    {
      assert (Rabs (IZR (len_f_l - len_f_r)) <= 1)%R as h.
      2:{ rewrite -abs_IZR in h. apply le_IZR. done. }
      etrans. 2: replace 1%R with (IZR 1%Z) by auto ; apply IZR_le ; apply adj.
      etrans. 1: eassumption. rewrite Rmult_1_l.
      etrans. 1: eassumption. rewrite Rmult_1_l.
      done. 
    }
    iApply (hoare_couple_laplace _ _ 0 with "[$rhs εₛ]") => //.
    1: lra. { rewrite Rmult_1_l. done. }
    iNext. iIntros (count_coarse_1) "rhs" ; simpl... rewrite Z.add_0_r.
    tp_load ; wp_load ; tp_pures ; tp_store ; wp_store...
    rewrite /list_cons.
    tp_load ; wp_load ; tp_pures ; tp_store ; wp_store...
    case_bool_decide as cc1...

    - tp_bind (Laplace _ _ _).
      wp_bind (Laplace _ _ _).
      iDestruct (ecm_split (IZR 10 / IZR 10)%R (IZR 8 / IZR 10)%R with "[ε]") as "[εₗ ε]".
      1,2: real_solver. 1: iApply ecm_eq ; [|iFrame] ; real_solver.
      iApply (hoare_couple_laplace _ _ 0 with "[$rhs $εₗ]") => //.
      1,2: lra.
      iNext. iIntros (count_precise_1) "rhs" ; simpl... rewrite Z.add_0_r.
      tp_load ; wp_load ; tp_pures ; tp_store ; wp_store...
      tp_load ; wp_load ; tp_pures ; tp_store ; wp_store...

      tp_bind (list_filter _ _).
      wp_bind (list_filter _ _).
      replace dsv1 with (inject ds1).
      2: symmetry ; by apply is_list_inject.
      replace dsv2 with (inject ds2).
      2: symmetry ; by apply is_list_inject.
      wp_apply (wp_wand with "[rhs]").
      { iApply (filter_sens $! _ _ _ _ _ with "rhs"). iNext. iIntros. done. }
      simpl.
      iIntros "% (%ds_f2_l&%ds_f2_r&->&rhs&%d_out2)".
      tp_bind (list_length _).
      wp_bind (list_length _).
      wp_apply (wp_wand with "[rhs]").
      { iApply (length_sens $! _ _ _ _ with "rhs"). iNext. iIntros. done. }
      simpl.
      iIntros "% (%len_f2_l&%len_f2_r&->&rhs&%d_out2')"...

      assert (Z.abs (len_f2_l - len_f2_r) <= 1).
      {
        assert (Rabs (IZR (len_f2_l - len_f2_r)) <= 1)%R as h.
        2:{ rewrite -abs_IZR in h. apply le_IZR. done. }
        etrans. 2: replace 1%R with (IZR 1%Z) by auto ; apply IZR_le ; apply adj.
        etrans. 1: eassumption. rewrite Rmult_1_l.
        etrans. 1: eassumption. rewrite Rmult_1_l.
        done.
      }

      tp_bind (Laplace _ _ _).
      wp_bind (Laplace _ _ _).
      iDestruct (ecm_split (IZR 2 / IZR 10)%R (IZR 6 / IZR 10)%R with "[ε]") as "[εₛ ε]".
      1,2: real_solver. 1: iApply ecm_eq ; [|iFrame] ; real_solver.
      iApply (hoare_couple_laplace _ _ 0 with "[$rhs $εₛ]") => //.
      1,2: lra.
      iNext. iIntros (count_coarse_2) "rhs" ; simpl... rewrite Z.add_0_r.
      tp_load ; wp_load ; tp_pures ; tp_store ; wp_store...
      tp_load ; wp_load ; tp_pures ; tp_store ; wp_store...
      case_bool_decide as cc2... 2: tp_load ; wp_load ; done.

      tp_load ; wp_load... tp_load ; wp_load ; done.

    - tp_bind (list_filter _ _).
      wp_bind (list_filter _ _).
      replace dsv1 with (inject ds1).
      2: symmetry ; by apply is_list_inject.
      replace dsv2 with (inject ds2).
      2: symmetry ; by apply is_list_inject.
      wp_apply (wp_wand with "[rhs]").
      { iApply (filter_sens $! _ _ _ _ with "rhs"). iNext. iIntros. done. }
      simpl.
      iIntros "% (%ds_f2_l&%ds_f2_r&->&rhs&%d_out2)".
      tp_bind (list_length _).
      wp_bind (list_length _).
      wp_apply (wp_wand with "[rhs]").
      { iApply (length_sens $! _ _ _ _ with "rhs"). iNext. iIntros. done. }
      simpl.
      iIntros "% (%len_f2_l&%len_f2_r&->&rhs&%d_out2')"...

      assert (Z.abs (len_f2_l - len_f2_r) <= 1).
      {
        assert (Rabs (IZR (len_f2_l - len_f2_r)) <= 1)%R as h.
        2:{ rewrite -abs_IZR in h. apply le_IZR. done. }
        etrans. 2: replace 1%R with (IZR 1%Z) by auto ; apply IZR_le ; apply adj.
        etrans. 1: eassumption. rewrite Rmult_1_l.
        etrans. 1: eassumption. rewrite Rmult_1_l.
        done.
      }

      tp_bind (Laplace _ _ _).
      wp_bind (Laplace _ _ _).
      iDestruct (ecm_split (IZR 2 / IZR 10)%R (IZR 16 / IZR 10)%R with "[ε]") as "[εₛ ε]".
      1,2: real_solver. 1: iApply ecm_eq ; [|iFrame] ; real_solver.
      iApply (hoare_couple_laplace _ _ 0 with "[$rhs $εₛ]") => //.
      1,2: lra.
      iNext. iIntros (count_coarse_2) "rhs" ; simpl... rewrite Z.add_0_r.
      tp_load ; wp_load ; tp_pures ; tp_store ; wp_store...
      tp_load ; wp_load ; tp_pures ; tp_store ; wp_store...
      case_bool_decide as cc2... 2: tp_load ; wp_load ; done.

      tp_load ; wp_load...

      tp_bind (Laplace _ _ _).
      wp_bind (Laplace _ _ _).
      iDestruct (ecm_split (IZR 10 / IZR 10)%R (IZR 6 / IZR 10)%R with "[ε]") as "[εₗ ε]".
      1,2: real_solver. 1: iApply ecm_eq ; [|iFrame] ; real_solver.
      iApply (hoare_couple_laplace _ _ 0 with "[$rhs $εₗ]") => //.
      1,2: lra.
      iNext. iIntros (count_precise_2) "rhs" ; simpl... rewrite Z.add_0_r.
      tp_load ; wp_load ; tp_pures ; tp_store ; wp_store...
      tp_load ; wp_load ; tp_pures ; tp_store ; wp_store...

      tp_load ; wp_load ; done.

      Unshelve. all: try lra.
      1: exact (λ x : Z, bool_decide (x < 30)).
      3,6: exact (λ x : Z, bool_decide (x < 32)).
      { iIntros "* !> * _ HΦ"... case_bool_decide as h ; by iApply "HΦ". }
      { iIntros "* !> * ? HΦ". gwp_pures. case_bool_decide as h ; by iApply "HΦ". }
      { iIntros "* !> * _ HΦ"... case_bool_decide as h ; by iApply "HΦ". }
      { iIntros "* !> * ? HΦ". gwp_pures. case_bool_decide as h ; by iApply "HΦ". }
      { iIntros "* !> * _ HΦ"... case_bool_decide as h ; by iApply "HΦ". }
      { iIntros "* !> * ? HΦ". gwp_pures. case_bool_decide as h ; by iApply "HΦ". }
  Qed.

Definition iter_adaptive_acc_simple_unrolled : val :=
  λ:"ε_coarse" "den" "budget" "pred" "data",
    let: "counts" := ref [] in
    let: "try_run" := create_filter "budget" in

    let: "count" := list_count "pred" "data" in
    "try_run" "ε_coarse"
      (λ:<>,
         let: "count_coarse" := Laplace "ε_coarse" "den" "count" in
         "counts" <- "count_coarse" :: !"counts") ;;

    (* let: "count" := list_count (λ:"x", #30 ≤ "x") "data" in
       "try_run" "ε_coarse"
         (λ:<>,
            let: "count_coarse" := Laplace "ε_coarse" "den" "count" in
            "counts" <- "count_coarse" :: !"counts") ;; *)

    ! "counts".


(* No conditional nested call, just iterate through predicates until the budget is gone. *)
Definition iter_adaptive_acc_simple : val :=
  λ:"ε_coarse" "den" "budget" "predicates" "data",
    let: "counts" := ref [] in
    let: "try_run" := create_filter "budget" in
    list_iter
      (λ:"pred",
        let: "count" := list_count "pred" "data" in
        "try_run" "ε_coarse"
          (λ:<>,
             let: "count_coarse" := Laplace "ε_coarse" "den" "count" in
             "counts" <- "count_coarse" :: !"counts"))
      "predicates" ;;
    ! "counts".

Lemma vpreds_is_predicate_list : ⊢ is_predicate_list predicates vpredicates.
  Proof.
    simpl. repeat (iExists _,_ ; repeat iSplitR => //).
    - iIntros (??) "!> _ HΦ". wp_pures.
      iApply "HΦ". iPureIntro. simpl. repeat f_equal.       
    - iIntros (??) "!> _ HΦ". gwp_pures.
      iApply "HΦ". iPureIntro. simpl. repeat f_equal. 
    - iIntros (??) "!> _ HΦ". wp_pures.
      iApply "HΦ". iPureIntro. simpl. repeat f_equal.
    - iIntros (??) "!> _ HΦ". gwp_pures.
      iApply "HΦ". iPureIntro. simpl. repeat f_equal. 
    - iIntros (??) "!> _ HΦ". wp_pures.
      iApply "HΦ". iPureIntro. simpl. repeat f_equal.
      do 2 case_bool_decide; simplify_eq=>//.
      exfalso; apply H. f_equal. rewrite H0. done. 
    - iIntros (??) "!> _ HΦ". gwp_pures.
      iApply "HΦ". iPureIntro. simpl. repeat f_equal.
      do 2 case_bool_decide; simplify_eq=>//.
      exfalso; apply H. f_equal. rewrite H0. done. 
  Qed.

  Lemma wp_iter_adaptive_acc_simple_unrolled (ε_coarse den budget : Z)
    (ds1 ds2 : list Z) dsv1 dsv2 K (pred : (Z -> bool)) (vpred : val)
    (_ : 0 < ε_coarse) (_ : 0 < den) (_ : 0 <= budget)
    :
    is_list ds1 dsv1 →
    is_list ds2 dsv2 →
    (* neighbour ds1 ds2 → *)
    list_dist ds1 ds2 <= 1 →
    is_predicate pred vpred -∗
    is_spec_predicate pred vpred -∗
    ↯m (IZR budget / IZR den) -∗
    ⤇ fill K (iter_adaptive_acc_simple_unrolled #ε_coarse #den #budget vpred dsv2) -∗
    WP iter_adaptive_acc_simple_unrolled #ε_coarse #den #budget vpred dsv1
      {{ v, ⤇ fill K (of_val v) }}.
  Proof with (tp_pures ; wp_pures).
    iIntros "* % %". iIntros "%adj". iIntros "#is_pred #is_spec_pred ε rhs". rewrite /iter_adaptive_acc_simple_unrolled...
    tp_alloc as counts_r "counts_r" ; wp_alloc counts_l as "counts_l"...
    tp_bind (create_filter _). wp_bind (create_filter _).
    iApply (create_filter_private _ _ den with "[$ε $rhs]") => //.
    iIntros "!> * (%&%&%&%&%&budget&l&l'&rhs&run_dp)"...

       rewrite /adaptive/list_count /=...
       tp_bind (list_filter _ _).
       wp_bind (list_filter _ _).
       replace dsv1 with (inject ds1).
       2: symmetry ; by apply is_list_inject.
       replace dsv2 with (inject ds2).
       2: symmetry ; by apply is_list_inject.
       wp_apply (wp_wand with "[rhs]").
       { iApply (filter_sens with "[//] [//] [] rhs").
         - iPureIntro; lra. 
         - iIntros "!> % h" ; iExact "h".
       }
       simpl.
       iIntros "% (%ds_f1_l&%ds_f1_r&->&rhs&%d_out)".
       tp_bind (list_length _).
       wp_bind (list_length _).
       wp_apply (wp_wand with "[rhs]").
       { iApply (length_sens $! _ _ _ _ with "rhs"). iNext. iIntros. iClear "is_pred is_spec_pred". done. }
       simpl.
       iIntros "% (%len_f_l&%len_f_r&->&rhs&%d_out')"...
       tp_bind (try_run' _ _) ; wp_bind (try_run _ _).
       set (I := (∃ counts, counts_r ↦ₛ counts ∗ counts_l ↦ counts)%I).
       iApply ("run_dp" $! _ _ _ _ _ I with "[] [-]") => // ; iFrame. 1: iPureIntro ; lia.
       - iIntros "* % !> (eps & rhs & I & l & l') Hpost"...
         tp_bind (Laplace _ _ _).
         wp_bind (Laplace _ _ _).
         assert (Z.abs (len_f_l - len_f_r) <= 1).
         {
           assert (Rabs (IZR (len_f_l - len_f_r)) <= 1)%R as h.
           2:{ rewrite -abs_IZR in h. apply le_IZR. done. }
           etrans. 2: replace 1%R with (IZR 1%Z) by auto ; apply IZR_le ; apply adj.
           etrans. 1: eassumption. rewrite Rmult_1_l.
           etrans. 1: eassumption. rewrite Rmult_1_l.
           done.
         }
         iApply (hoare_couple_laplace _ _ 0 with "[$rhs $eps]") => //.
         2: lra.
         { epose proof (IZR_lt 0 ε_coarse _) => //.
           epose proof (IZR_lt 0 den _) => //.
           apply Rcomplements.Rdiv_lt_0_compat => //. }
         iNext. iIntros (count_precise_2) "rhs" ; simpl... rewrite Z.add_0_r.
         iDestruct "I" as "(% & ? & ?)". rewrite /list_cons.
         tp_load ; wp_load ; tp_pures ; tp_store ; wp_store. iApply "Hpost". iFrame. done.

       - iNext. iIntros "* (?&(%&?&?)&(%&?&?&?))" => /=... tp_load ; wp_load. done.
         Unshelve. all: auto ; lra.
     Qed.

  Fixpoint is_list_HO (l : list val) (v : val) :=
    match l with
    | [] => v = NONEV
    | w::l' => ∃ lv, v = SOMEV (w, lv) ∧ is_list_HO l' lv
  end.

  Lemma wp_list_iter_invariant_HO' (Ψ: list val -> list val -> iProp Σ) E l (fv lv : val) lrest :
    (∀ lpre (w : val) lsuf,
        {{{ Ψ lpre (w :: lsuf) }}}
          fv w @ E
        {{{v, RET v; Ψ (lpre ++ [w]) lsuf }}}) -∗
    {{{ ⌜ is_list_HO l lv ⌝ ∗ Ψ lrest l }}}
      list_iter fv lv @ E
    {{{ RET #(); Ψ (lrest++l) [] }}}.
  Proof.
    rewrite /list_iter.
    iInduction l as [|a l'] "IH" forall (lv lrest).
    - iIntros "#Helem";
      iIntros (Φ') "!# (Hlist & HΨ) HΦ'";
      iDestruct "Hlist" as "%Hlist"; simpl in Hlist; subst; wp_pures.
      iApply "HΦ'".
      rewrite app_nil_r //.
    - iIntros "#Helem";
      iIntros (Φ') "!# (Hlist & HΨ) HΦ'".
      iDestruct "Hlist" as "%Hlist"; simpl in Hlist; subst; wp_pures.
      destruct Hlist as [lv' [Hlv Hlcoh]]; subst.
      wp_pures.
      wp_apply ("Helem" with "[$HΨ]").
      iIntros (v) "HΨ".
      do 2 wp_pure.
      iApply ("IH" $! lv' (lrest ++ [a]) with "[$Helem] [$HΨ //]").
      iModIntro.
      by rewrite -app_assoc.
  Qed.

  Lemma wp_list_iter_invariant_HO (Ψ: list val -> list val -> iProp Σ) E l (fv lv : val) :
    (∀ lpre (w : val) lsuf,
        {{{ Ψ lpre (w :: lsuf) }}}
          fv w @ E
        {{{v, RET v; Ψ (lpre ++ [w]) lsuf }}}) -∗
    {{{ ⌜ is_list_HO l lv ⌝ ∗ Ψ [] l }}}
      list_iter fv lv @ E
    {{{ RET #(); Ψ l [] }}}.
  Proof.
    replace l with ([]++l); last by apply app_nil_l.
    iApply wp_list_iter_invariant_HO'.
  Qed.


  Lemma wp_iter_adaptive_acc_simple (ε_coarse den budget : Z)
    (ds1 ds2 : list Z) dsv1 dsv2 K
    (predicates : list (Z -> bool))
    (lvpredicates : list val)
    (vpredicates : val)
    (_ : 0 < ε_coarse) (_ : 0 < den) (_ : 0 <= budget)
    :
    length predicates = length lvpredicates →
    is_list ds1 dsv1 →
    is_list ds2 dsv2 →
    list_dist ds1 ds2 <= 1 →
    ⌜is_list_HO lvpredicates vpredicates⌝ -∗
    ([∗ list] pred;vpred ∈ predicates;lvpredicates, is_predicate pred vpred ∗ is_spec_predicate pred vpred) -∗
    ↯m (IZR budget / IZR den) -∗
    ⤇ fill K (iter_adaptive_acc_simple #ε_coarse #den #budget vpredicates dsv2) -∗
    WP iter_adaptive_acc_simple #ε_coarse #den #budget vpredicates dsv1
      {{ v, ⤇ fill K (of_val v) }}.
  Proof with (tp_pures ; wp_pures).
    iIntros "%hlen * % %". iIntros "%adj".
    iIntros "%ho_pred #is_pred ε rhs".
    rewrite /iter_adaptive_acc_simple...
    tp_alloc as counts_r "counts_r" ; wp_alloc counts_l as "counts_l"...
    tp_bind (create_filter _). wp_bind (create_filter _).
    iApply (create_filter_private _ _ den with "[$ε $rhs]") => //.
    iIntros "!> * (%&%&%&%&%&budget&l&l'&rhs&#run_dp)"... simpl...
    tp_bind (list_iter _ _). wp_bind (list_iter _ _).
    iAssert (∃ counts budget_remaining,
                counts_l ↦ counts ∗ counts_r ↦ₛ counts ∗
                ↯m (IZR budget_remaining / IZR den) ∗
                    l ↦ #budget_remaining ∗ l' ↦ₛ #budget_remaining
            )%I with "[counts_l counts_r budget l l']" as "hh". 1: iFrame.
    iRevert (predicates vpredicates ho_pred hlen) "is_pred rhs".
    iInduction lvpredicates as [|vpred lvpredicates'] "IH" ;
      iIntros (predicates vpredicates ho_pred hlen) "#is_pred rhs".
    - rewrite ho_pred.
      rewrite /list_iter...
      iDestruct "hh" as "(%&%&?&?&?&?&?)".
      tp_load... wp_load. done.
    - simpl in ho_pred. destruct ho_pred as (vpredicates' & hpred & ho_pred). rewrite hpred.
      rewrite /list_iter...
      rewrite /adaptive/list_count /=...
      tp_bind (list_filter _ _).
      wp_bind (list_filter _ _).
      replace dsv1 with (inject ds1).
      2: symmetry ; by apply is_list_inject.
      replace dsv2 with (inject ds2).
      2: symmetry ; by apply is_list_inject.
      destruct predicates as [|pred predicates'] => //.
      wp_apply (wp_wand with "[rhs is_pred]").
      { iApply (filter_sens with "[] [] [] rhs"). 3: iPureIntro ; lra. 3: iIntros "!> % h" ; iExact "h".
        1,2: iDestruct (big_sepL2_cons_inv_l with "is_pred") as "(%&%&%&[? ?]&?)" ; simplify_eq ; done.
      }
      simpl. fold list_iter.
      iIntros "% (%ds_f1_l&%ds_f1_r&->&rhs&%d_out)".
      tp_bind (list_length _).
      wp_bind (list_length _).
      wp_apply (wp_wand with "[rhs]").
      { iApply (length_sens $! _ _ _ _ with "rhs"). iNext. iIntros "* H". iExact "H". }
      simpl.
      iIntros "% (%len_f_l&%len_f_r&->&rhs&%d_out')"...
      tp_bind (try_run' _ _) ; wp_bind (try_run _ _).
      set (I := (∃ counts, counts_r ↦ₛ counts ∗ counts_l ↦ counts)%I).
      iDestruct "hh" as "(%&%&?&?&?&?&?)".
      iApply ("run_dp" $! _ _ _ _ _ I with "[] [-]") => // ; iFrame. 1: iPureIntro ; lia.
      + iIntros "* % !> (eps & rhs & I & l & l') Hpost"...
        tp_bind (Laplace _ _ _).
        wp_bind (Laplace _ _ _).
        assert (Z.abs (len_f_l - len_f_r) <= 1).
        {
          assert (Rabs (IZR (len_f_l - len_f_r)) <= 1)%R as h.
          2:{ rewrite -abs_IZR in h. apply le_IZR. done. }
          etrans. 2: replace 1%R with (IZR 1%Z) by auto ; apply IZR_le ; apply adj.
          etrans. 1: eassumption. rewrite Rmult_1_l.
          etrans. 1: eassumption. rewrite Rmult_1_l.
          done.
        }
        iApply (hoare_couple_laplace _ _ 0 with "[$rhs $eps]") => //.
        1,2: repeat real_solver_partial.
        {
          epose proof (IZR_lt 0 ε_coarse _) => //.
          epose proof (IZR_lt 0 den _) => //.
          apply Rcomplements.Rdiv_lt_0_compat => //. }
        iNext. iIntros (count_precise_2) "rhs" ; simpl... rewrite Z.add_0_r.
        iDestruct "I" as "(% & ? & ?)". rewrite /list_cons.
        tp_load ; wp_load ; tp_pures ; tp_store ; wp_store. iApply "Hpost". iFrame. done.

         + iNext. iIntros "* (rhs&(%&counts_r&counts_l)&(%&budget&l&l'))" => /=...
           iApply ("IH" with "[$l $l' $counts_r $counts_l $budget] [] [] [] [$rhs]") => //.
           1: iPureIntro ; eauto.
           iModIntro. iDestruct "is_pred" as "[? ?]". done.
           Unshelve. all: auto ; lra.
     Qed.

Definition lvpredicates : list val :=
  [(λ:"x", "x" < #30) ; (λ:"x", #30 <= "x") ; (λ:"x", "x" `rem` #2 = #0)]%V.

Lemma foo : is_list_HO lvpredicates vpredicates.
  repeat (eexists ; split ; eauto).
Qed.

Lemma bar :
    ⊢ ([∗ list] pred;vpred ∈ predicates;lvpredicates, is_predicate pred vpred ∗ is_spec_predicate pred vpred).
repeat iSplit. 7: done.
    - iIntros (??) "!> _ HΦ". wp_pures.
      iApply "HΦ". iPureIntro. simpl. repeat f_equal. 
    - iIntros (??) "!> _ HΦ". gwp_pures.
      iApply "HΦ". iPureIntro. simpl. repeat f_equal. 
    - iIntros (??) "!> _ HΦ". wp_pures.
      iApply "HΦ". iPureIntro. simpl. repeat f_equal. 
    - iIntros (??) "!> _ HΦ". gwp_pures.
      iApply "HΦ". iPureIntro. simpl. repeat f_equal.
      
    - iIntros (??) "!> _ HΦ". wp_pures.
      case_decide.
      { rewrite !bool_decide_eq_true_2 //; [|by do 2 f_equal]. by iApply "HΦ". }
      rewrite !bool_decide_eq_false_2 //; [|by intros [=]]. by iApply "HΦ".
    - iIntros (??) "!> _ HΦ". gwp_pures.
      iApply "HΦ". iPureIntro. simpl. repeat f_equal.
      case_decide; simplify_eq /=.      
      { rewrite !bool_decide_eq_true_2 //. }      
      rewrite !bool_decide_eq_false_2 //.
      intros ?. apply H. do 2 f_equal. done.
  Qed.

  Lemma wp_iter_adaptive_acc_simple_app (ε_coarse den budget : Z)
    (ds1 ds2 : list Z) dsv1 dsv2 K
    (_ : 0 < ε_coarse) (_ : 0 < den) (_ : 0 <= budget)
    :
    is_list ds1 dsv1 →
    is_list ds2 dsv2 →
    list_dist ds1 ds2 <= 1 →
    ↯m (IZR budget / IZR den) -∗
    ⤇ fill K (iter_adaptive_acc_simple #ε_coarse #den #budget vpredicates dsv2) -∗
    WP iter_adaptive_acc_simple #ε_coarse #den #budget vpredicates dsv1
      {{ v, ⤇ fill K (of_val v) }}.
  Proof with (tp_pures ; wp_pures).
    iIntros "%hlen * % % ε rhs".
    iApply (wp_iter_adaptive_acc_simple with "[] [] ε rhs") ; last first.
    1: iApply bar. 1: iPureIntro ; apply foo. all: eauto.
  Qed.

  (* This is the spec one would want for iter_adaptive_acc, proven from the not-abstracted spec for the privacy filter. *)
  Lemma wp_iter_adaptive_acc (ε_coarse ε_precise den threshold budget : Z)
    (ds1 ds2 : list Z) dsv1 dsv2 K
    (predicates : list (Z -> bool))
    (lvpredicates : list val)
    (vpredicates : val)
    (_ : 0 < ε_coarse) (_ : 0 < ε_precise) (_ : 0 < den) (_ : 0 <= budget)
    :
    length predicates = length lvpredicates →
    is_list ds1 dsv1 →
    is_list ds2 dsv2 →
    list_dist ds1 ds2 <= 1 →
    ⌜is_list_HO lvpredicates vpredicates⌝ -∗
    ([∗ list] pred;vpred ∈ predicates;lvpredicates, is_predicate pred vpred ∗ is_spec_predicate pred vpred) -∗
    ↯m (IZR budget / IZR den) -∗
    ⤇ fill K (iter_adaptive_acc #ε_coarse #ε_precise #den #threshold #budget vpredicates dsv2) -∗
    WP iter_adaptive_acc #ε_coarse #ε_precise #den #threshold #budget vpredicates dsv1
      {{ v, ⤇ fill K (of_val v) }}.
  Proof with (tp_pures ; wp_pures).
    iIntros "%hlen * % %". iIntros "%adj".
    iIntros "%ho_pred #is_pred ε rhs".
    rewrite /iter_adaptive_acc...
    tp_alloc as counts_r "counts_r" ; wp_alloc counts_l as "counts_l"...
    tp_bind (create_filter _). wp_bind (create_filter _).
    iApply (create_filter_private _ _ den with "[$ε $rhs]") => //.
    iIntros "!> * (%&%&%&%&%&budget&l&l'&rhs&#run_dp)"... simpl...
    tp_bind (list_iter _ _). wp_bind (list_iter _ _).
    set (Inv := (∃ counts (budget_remaining : Z),
                counts_l ↦ counts ∗ counts_r ↦ₛ counts ∗
                ↯m (IZR budget_remaining / IZR den) ∗
                    l ↦ #budget_remaining ∗ l' ↦ₛ #budget_remaining
            )%I).
    iAssert Inv with "[counts_l counts_r budget l l']" as "hh". 1: iFrame.
    iRevert (predicates vpredicates ho_pred hlen) "is_pred rhs".
    iInduction lvpredicates as [|vpred lvpredicates'] "IH" ;
      iIntros (predicates vpredicates ho_pred hlen) "#is_pred rhs".
    - rewrite ho_pred.
      rewrite /list_iter...
      iDestruct "hh" as "(%&%&?&?&?&?&?)".
      tp_load... wp_load. done.
    - simpl in ho_pred. destruct ho_pred as (vpredicates' & hpred & ho_pred). rewrite hpred.
      rewrite /list_iter...
      rewrite /adaptive/list_count /=...
      tp_bind (list_filter _ _).
      wp_bind (list_filter _ _).
      replace dsv1 with (inject ds1).
      2: symmetry ; by apply is_list_inject.
      replace dsv2 with (inject ds2).
      2: symmetry ; by apply is_list_inject.
      destruct predicates as [|pred predicates'] => //.
      wp_apply (wp_wand with "[rhs is_pred]").
      { iApply (filter_sens with "[] [] [] rhs"). 3: iPureIntro ; lra. 3: iIntros "!> % h" ; iExact "h".
        1,2: iDestruct (big_sepL2_cons_inv_l with "is_pred") as "(%&%&%&[? ?]&?)" ; simplify_eq ; done.
      }
      simpl. fold list_iter.
      iIntros "% (%ds_f1_l&%ds_f1_r&->&rhs&%d_out)".
      tp_bind (list_length _).
      wp_bind (list_length _).
      wp_apply (wp_wand with "[rhs]").
      { iApply (length_sens $! _ _ _ _ with "rhs"). iNext. iIntros "* H". iApply "H". }
      simpl.
      iIntros "% (%len_f_l&%len_f_r&->&rhs&%d_out')"...
      tp_bind (try_run' _ _) ; wp_bind (try_run _ _).
      set (I := (∃ counts,
                    counts_r ↦ₛ counts ∗ counts_l ↦ counts
                )%I).
      (* set (I := (∃ counts budget_remaining,
                       counts_l ↦ counts ∗ counts_r ↦ₛ counts ∗
                       ↯m (IZR budget_remaining / IZR den) ∗
                       l ↦ #budget_remaining ∗ l' ↦ₛ #budget_remaining
                   )%I). *)
      (* set (I := Inv). *)
      iDestruct "hh" as "(%&%&counts_l&counts_r&?&?&?)".
      iApply ("run_dp" $! _ _ _ _ _ I with "[] [-]"). 1: iPureIntro ; lia.
      + iFrame. iIntros "* % !> (eps & rhs & I & εrem & l & l') Hpost"...
        tp_bind (Laplace _ _ _).
        wp_bind (Laplace _ _ _).
        assert (Z.abs (len_f_l - len_f_r) <= 1).
        {
          assert (Rabs (IZR (len_f_l - len_f_r)) <= 1)%R as h.
          2:{ rewrite -abs_IZR in h. apply le_IZR. done. }
          etrans. 2: replace 1%R with (IZR 1%Z) by auto ; apply IZR_le ; apply adj.
          etrans. 1: eassumption. rewrite Rmult_1_l.
          etrans. 1: eassumption. rewrite Rmult_1_l.
          done.
        }
        iApply (hoare_couple_laplace _ _ 0 with "[$rhs $eps]") => //.
        1,2: repeat real_solver_partial.
        {
          epose proof (IZR_lt 0 ε_coarse _) => //.
          epose proof (IZR_lt 0 den _) => //.
          apply Rcomplements.Rdiv_lt_0_compat => //. }
        iNext. iIntros (count_precise_1) "rhs" ; simpl... rewrite Z.add_0_r.
        iDestruct "I" as "(% & counts_r & counts_l)". rewrite /list_cons.
        tp_load ; wp_load ; tp_pures ; tp_store ; wp_store...
        case_bool_decide as hthresh...
        2: iApply "Hpost" ; by iFrame.

        tp_bind (try_run' _ _) ; wp_bind (try_run _ _).

        (* set (I := (∃ counts, counts_r ↦ₛ counts ∗ counts_l ↦ counts)%I). *)
        (* iDestruct "hh" as "(%&%&?&?&?&?&?)". *)
        iApply ("run_dp" $! _ _ _ _ _ I with "[] [-Hpost]"). 1: iPureIntro ; lia.

        * iFrame.
          iIntros "* % !> (eps & rhs & I & εrem & l & l') Hpost"...
          tp_bind (Laplace _ _ _).
          wp_bind (Laplace _ _ _).
          assert (Z.abs (len_f_l - len_f_r) <= 1).
          {
            assert (Rabs (IZR (len_f_l - len_f_r)) <= 1)%R as h.
            2:{ rewrite -abs_IZR in h. apply le_IZR. done. }
            etrans. 2: replace 1%R with (IZR 1%Z) by auto ; apply IZR_le ; apply adj.
            etrans. 1: eassumption. rewrite Rmult_1_l.
            etrans. 1: eassumption. rewrite Rmult_1_l.
            done.
          }
          iApply (hoare_couple_laplace _ _ 0 with "[$rhs $eps]") => //.
          1,2: repeat real_solver_partial.
          {
            epose proof (IZR_lt 0 ε_coarse _) => //.
            epose proof (IZR_lt 0 den _) => //.
            apply Rcomplements.Rdiv_lt_0_compat => //. apply IZR_lt. done. }
          iNext. iIntros (count_precise_2) "rhs" ; simpl... rewrite Z.add_0_r.
          iDestruct "I" as "(% & ? & ?)". rewrite /list_cons...
          tp_load ; wp_load ; tp_pures ; tp_store ; wp_store.
          iApply "Hpost" ; by iFrame.

        * iIntros "!> **". iApply "Hpost". iFrame.

      + iNext. iIntros "* (rhs&(%&counts_r&counts_l)&(%&budget&l&l'))" => /=...
        iApply ("IH" with "[$l $l' $counts_r $counts_l $budget] [] [] [] [$rhs]") => //.
        1: iPureIntro ; eauto.
        iModIntro. iDestruct "is_pred" as "[? ?]". done.
        Unshelve. all: auto ; lra.
  Qed.

  (* This is the spec one would want for iter_adaptive_acc, proven from the abstracted spec for the privacy filter. *)
  Lemma wp_iter_adaptive_acc' (ε_coarse ε_precise den threshold budget : Z)
    (ds1 ds2 : list Z) dsv1 dsv2 K
    (predicates : list (Z -> bool))
    (lvpredicates : list val)
    (vpredicates : val)
    (_ : 0 < ε_coarse) (_ : 0 < ε_precise) (_ : 0 < den) (_ : 0 <= budget)
    :
    length predicates = length lvpredicates →
    is_list ds1 dsv1 →
    is_list ds2 dsv2 →
    list_dist ds1 ds2 <= 1 →
    ⌜is_list_HO lvpredicates vpredicates⌝ -∗
    ([∗ list] pred;vpred ∈ predicates;lvpredicates, is_predicate pred vpred ∗ is_spec_predicate pred vpred) -∗
    ↯m (IZR budget / IZR den) -∗
    ⤇ fill K (iter_adaptive_acc #ε_coarse #ε_precise #den #threshold #budget vpredicates dsv2) -∗
    WP iter_adaptive_acc #ε_coarse #ε_precise #den #threshold #budget vpredicates dsv1
      {{ v, ⤇ fill K (of_val v) }}.
  Proof with (tp_pures ; wp_pures).
    iIntros "%hlen * % %". iIntros "%adj".
    iIntros "%ho_pred #is_pred ε rhs".
    rewrite /iter_adaptive_acc...
    tp_alloc as counts_r "counts_r" ; wp_alloc counts_l as "counts_l"...
    tp_bind (create_filter _). wp_bind (create_filter _).
    iApply (create_filter_private' _ _ den with "[$ε $rhs]") => //.
    iIntros "!> * (%&%&rhs&TRY_RUN&#run_dp)"... simpl...
    tp_bind (list_iter _ _). wp_bind (list_iter _ _).
    set (Inv := (∃ counts, counts_l ↦ counts ∗ counts_r ↦ₛ counts)%I).
    iAssert Inv with "[counts_l counts_r]" as "hh". 1: iFrame.
    iRevert (predicates vpredicates ho_pred hlen) "is_pred rhs".
    iInduction lvpredicates as [|vpred lvpredicates'] "IH" ;
      iIntros (predicates vpredicates ho_pred hlen) "#is_pred rhs".
    - rewrite ho_pred.
      rewrite /list_iter...
      iDestruct "hh" as "(%&?&?)".
      tp_load... wp_load. done.
    - simpl in ho_pred. destruct ho_pred as (vpredicates' & hpred & ho_pred). rewrite hpred.
      rewrite /list_iter...
      rewrite /adaptive/list_count /=...
      tp_bind (list_filter _ _).
      wp_bind (list_filter _ _).
      replace dsv1 with (inject ds1).
      2: symmetry ; by apply is_list_inject.
      replace dsv2 with (inject ds2).
      2: symmetry ; by apply is_list_inject.
      destruct predicates as [|pred predicates'] => //.
      wp_apply (wp_wand with "[rhs is_pred]").
      { iApply (filter_sens with "[] [] [] rhs"). 3: iPureIntro ; lra. 3: iIntros "!> % h" ; iExact "h".
        all: iDestruct (big_sepL2_cons_inv_l with "is_pred") as "(%&%&%&[? ?]&?)" ; simplify_eq ; done. }
      simpl. fold list_iter.
      iIntros "% (%ds_f1_l&%ds_f1_r&->&rhs&%d_out)".
      tp_bind (list_length _).
      wp_bind (list_length _).
      wp_apply (wp_wand with "[rhs]").
      { iApply (length_sens $! _ _ _ _ with "rhs"). iNext. iIntros "* H". iApply "H". }
      simpl.
      iIntros "% (%len_f_l&%len_f_r&->&rhs&%d_out')"...
      tp_bind (try_run' _ _) ; wp_bind (try_run _ _).
      set (I := (∃ counts, counts_r ↦ₛ counts ∗ counts_l ↦ counts)%I).
      iDestruct "hh" as "(%&counts_l&counts_r)".
      iApply ("run_dp" $! _ _ _ _ I with "[] [-]"). 1: iPureIntro ; lia.
      + iFrame. iIntros "* % !> (eps & rhs & I & TRY_RUN) Hpost"...
        tp_bind (Laplace _ _ _).
        wp_bind (Laplace _ _ _).
        assert (Z.abs (len_f_l - len_f_r) <= 1).
        {
          assert (Rabs (IZR (len_f_l - len_f_r)) <= 1)%R as h.
          2:{ rewrite -abs_IZR in h. apply le_IZR. done. }
          etrans. 2: replace 1%R with (IZR 1%Z) by auto ; apply IZR_le ; apply adj.
          etrans. 1: eassumption. rewrite Rmult_1_l.
          etrans. 1: eassumption. rewrite Rmult_1_l.
          done.
        }
        iApply (hoare_couple_laplace _ _ 0 with "[$rhs $eps]") => //.
        1,2: repeat real_solver_partial.
        {
          epose proof (IZR_lt 0 ε_coarse _) => //.
          epose proof (IZR_lt 0 den _) => //.
          apply Rcomplements.Rdiv_lt_0_compat => //. }
        iNext. iIntros (count_precise_1) "rhs" ; simpl... rewrite Z.add_0_r.
        iDestruct "I" as "(% & counts_r & counts_l)". rewrite /list_cons.
        tp_load ; wp_load ; tp_pures ; tp_store ; wp_store...
        case_bool_decide as hthresh...
        2: iApply "Hpost" ; by iFrame.
        tp_bind (try_run' _ _) ; wp_bind (try_run _ _).
        iApply ("run_dp" $! _ _ _ _ I with "[] [-Hpost]"). 1: iPureIntro ; lia.
        * iFrame.
          iIntros "* % !> (eps & rhs & I & TRY_RUN) Hpost"...
          tp_bind (Laplace _ _ _).
          wp_bind (Laplace _ _ _).
          assert (Z.abs (len_f_l - len_f_r) <= 1).
          {
            assert (Rabs (IZR (len_f_l - len_f_r)) <= 1)%R as h.
            2:{ rewrite -abs_IZR in h. apply le_IZR. done. }
            etrans. 2: replace 1%R with (IZR 1%Z) by auto ; apply IZR_le ; apply adj.
            etrans. 1: eassumption. rewrite Rmult_1_l.
            etrans. 1: eassumption. rewrite Rmult_1_l.
            done.
          }
          iApply (hoare_couple_laplace _ _ 0 with "[$rhs $eps]") => //.
          1,2: repeat real_solver_partial.
          {
            epose proof (IZR_lt 0 ε_coarse _) => //.
            epose proof (IZR_lt 0 den _) => //.
            apply Rcomplements.Rdiv_lt_0_compat => //. apply IZR_lt. done. }
          iNext. iIntros (count_precise_2) "rhs" ; simpl... rewrite Z.add_0_r.
          iDestruct "I" as "(% & ? & ?)". rewrite /list_cons...
          tp_load ; wp_load ; tp_pures ; tp_store ; wp_store.
          iApply "Hpost" ; by iFrame.

        * iIntros "!> **". iApply "Hpost". iFrame.

      + iNext. iIntros "* (rhs&(%&counts_r&counts_l)&TRY_RUN)" => /=...
        iApply ("IH" with "TRY_RUN [counts_r counts_l] [] [] [] [rhs]") => // ; iFrame.
        1: iPureIntro ; eauto.
        iModIntro. iDestruct "is_pred" as "[? ?]". done.
        Unshelve. all: auto ; lra.
  Qed.

  (* apply the general iter spec for some concrete predicates *)
  Lemma wp_iter_adaptive_acc_app (ε_coarse ε_precise den threshold budget : Z)
    (ds1 ds2 : list Z) dsv1 dsv2 K
    (_ : 0 < ε_coarse) (_ : 0 < ε_precise) (_ : 0 < den) (_ : 0 <= budget)
    :
    is_list ds1 dsv1 →
    is_list ds2 dsv2 →
    list_dist ds1 ds2 <= 1 →
    ↯m (IZR budget / IZR den) -∗
    ⤇ fill K (iter_adaptive_acc #ε_coarse #ε_precise #den #threshold #budget vpredicates dsv2) -∗
    WP iter_adaptive_acc #ε_coarse #ε_precise #den #threshold #budget vpredicates dsv1
      {{ v, ⤇ fill K (of_val v) }}.
  Proof with (tp_pures ; wp_pures).
    iIntros "%hlen * % % ε rhs".
    iApply (wp_iter_adaptive_acc' with "[] [] ε rhs") ; last first.
    1: iApply bar. 1: iPureIntro ; apply foo. all: eauto.
  Qed.

End adaptive.

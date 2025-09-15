(** * Counter example of presampling on the RHS *)
From Coquelicot Require Import Lub Rbar Lim_seq.
From clutch.con_prob_lang Require Import lub_termination.
From clutch.foxtrot Require Import foxtrot.
From clutch.foxtrot.lib Require Import diverge nodet.

Set Default Proof Using "Type*".

Definition prog0 : expr:=  #().
Definition prog1 : expr :=
  if:  nodet #() = rand #1  then #() else diverge #().
Definition prog2 : expr :=
  let: "α":=alloc #1 in 
  if:  (rand("α") #1 )= nodet #() then #() else diverge #().
Definition prog3 : expr :=
  if: rand #1 = #1 then #() else diverge #().

Lemma prog0_termination σ : Rbar_le 1%R (lub_termination_prob prog0 σ).
Proof.
  rewrite /lub_termination_prob.
  pose proof Lub_Rbar_correct (termination_prob' prog0 σ) as H.
  rewrite /is_lub_Rbar in H.
  destruct H as [H _].
  apply H.
  rewrite /termination_prob'.
  eexists ( (_;(_,(_;(_;(_;_)))))).
  simpl.
  rewrite /prog0.
  rewrite /termination_prob.
  erewrite sch_lim_exec_final; first apply dret_mass.
  done.
  Unshelve.
  - apply unit.
  - done.
  - apply {|scheduler_f := λ _, dzero|}.
  - simpl.
    by rewrite /TapeOblivious.
Qed.

Section counterexample.
  Context `{H:!foxtrotGS Σ}.

  Definition unsound_presample_RHS N z E α ns:= 
    TCEq N (Z.to_nat z) →
    {{{ α ↪ₛN (N; ns)  }}}
      rand #z @ E
      {{{ (n : nat), RET #n; α ↪ₛN (N; ns ++ [n]) ∗  ⌜ n ≤ N ⌝ }}}.

  
End counterexample.

Lemma presample_RHS_is_unsound σ :
  (∀ `{H: foxtrotGS Σ} N z E α ns, unsound_presample_RHS (H:= H)N z E α ns) ->
  Rbar_le 1 (lub_termination_prob prog3 σ).
Proof.
  etrans; first apply prog0_termination.
  instantiate (1:=σ).
  trans (lub_termination_prob prog1 σ); last trans (lub_termination_prob prog2 σ). 
  - replace (lub_termination_prob prog1 σ) with (Rbar_plus (lub_termination_prob prog1 σ) 0); last first; first by rewrite Rbar_plus_0_r.
    eapply (foxtrot_adequacy (#[foxtrotΣ]) (λ _ _, True)); first done.
    iIntros (?) "_ Hspec".
    rewrite /prog1/prog0.
    tp_bind 0%nat (rand _)%E.
    iMod (pupd_rand with "[$]") as "(%n&Hspec&%)".
    simpl.
    tp_bind 0%nat (nodet #())%E.
    iMod (tp_nodet _ _ _ n with "[$]").
    simpl.
    tp_pures 0%nat.
    { solve_vals_compare_safe. }
    rewrite bool_decide_eq_true_2; last done.
    tp_pures 0%nat.
    wp_pures.
    by iFrame.
  - replace (lub_termination_prob prog2 σ) with (Rbar_plus (lub_termination_prob prog2 σ) 0); last first; first by rewrite Rbar_plus_0_r.
    eapply (foxtrot_adequacy (#[foxtrotΣ]) (λ _ _, True)); first done.
    iIntros (?) "_ Hspec".
    rewrite /prog1/prog2.
    tp_bind 0%nat (alloc _)%E.
    iMod (pupd_alloc_tape with "[$]") as "(%&Htape&Hspec)".
    simpl.
    tp_pures 0%nat.
    unfold unsound_presample_RHS in *.
    wp_bind (rand _)%E.
    wp_apply (H with "[$]").
    iIntros (n) "[Htape %]".
    simpl.
    tp_bind 0%nat (nodet #())%E.
    iMod (tp_nodet _ _ _ n with "[$]").
    simpl.
    tp_bind 0%nat (rand(_) #1)%E.
    iMod (pupd_rand_tape with "[$][$]") as "(Htape&Hspec)".
    simpl.
    tp_pures 0%nat.
    { solve_vals_compare_safe. }
    rewrite bool_decide_eq_true_2; last done.
    tp_pures 0%nat.
    wp_apply (wp_nodet); first done.
    iIntros.
    wp_pures.
    case_bool_decide; wp_pures.
    + by iFrame.
    + wp_apply wp_diverge; first done.
      by iIntros.
  - replace (lub_termination_prob prog3 σ) with (Rbar_plus (lub_termination_prob prog3 σ) 0); last first; first by rewrite Rbar_plus_0_r.
    eapply (foxtrot_adequacy (#[foxtrotΣ]) (λ _ _, True)); first done.
    iIntros (?) "_ Hspec".
    rewrite /prog3/prog2.
    wp_alloctape α as "Hα".
    wp_pures.
    simpl.
    wp_apply (wp_nodet); first done.
    iIntros (n) "_".
    destruct n as [|[|n]].
    + tp_bind 0%nat (rand _)%E.
      iMod (pupd_couple_tape_rand _ (λ x, if bool_decide (x<=1)%nat then 1-x else x)%nat with "[$][$]") as "(%n&Htape&Hspec&%)".
      { intros. case_bool_decide; lia. }
      simpl.
      wp_randtape.
      case_bool_decide; last lia.
      wp_pures.
      case_bool_decide.
      * tp_pures 0%nat; first solve_vals_compare_safe. simplify_eq.
        rewrite bool_decide_eq_true_2; last (f_equal; lia).
        tp_pures 0%nat. wp_pures. by iFrame.
      * wp_pures. wp_apply wp_diverge; first done.
        by iIntros.
    + tp_bind 0%nat (rand _)%E.
      iMod (pupd_couple_tape_rand _  with "[$][$]") as "(%n&Htape&Hspec&%)".
      { done. }
      simpl.
      wp_randtape.
      wp_pures.
      tp_pures 0%nat; first solve_vals_compare_safe.
      case_bool_decide.
      * tp_pures 0%nat. simplify_eq. rewrite bool_decide_eq_true_2; last (repeat f_equal; lia).
        wp_pures. by iFrame.
      * wp_pures. rewrite bool_decide_eq_false_2; first (wp_pures; wp_apply wp_diverge; first done; by iIntros).
        intro .
        simplify_eq. 
    + tp_bind 0%nat (rand _)%E.
      iMod (pupd_couple_tape_rand _  with "[$][$]") as "(%x&Htape&Hspec&%)".
      { done. }
      wp_randtape.
      wp_pures.
      rewrite bool_decide_eq_false_2.
      * wp_pures; wp_apply wp_diverge; first done; by iIntros.
      * intro . simplify_eq. lia.
        Unshelve.
        -- apply le_dec.
        -- split.
           ++ intros ???.
              repeat case_bool_decide; lia.
           ++ intros y.
              destruct (decide (y<=1)).
              ** exists (1-y). rewrite bool_decide_eq_true_2; lia.
              ** exists y. rewrite bool_decide_eq_false_2; lia.
Qed. 

  
(* Lemma prog3_termination σ : Rbar_le (lub_termination_prob prog3 σ) (1/2)%R. *)
(* Proof. *)
(*   rewrite /lub_termination_prob. *)
(*   pose proof Lub_Rbar_correct (termination_prob' prog3 σ) as H. *)
(*   rewrite /is_lub_Rbar in H. *)
(*   destruct H as [_ H]. *)
(*   apply H. *)
(*   rewrite /termination_prob'. *)
(*   rewrite /is_ub_Rbar. *)
(*   intros r. *)
(*   elim. *)
(*   intros [x[ζ[x1[x2[sch t]]]]]. *)
(*   simpl. *)
(*   rewrite /termination_prob. *)
(*   intros <-. *)
(*   rewrite sch_lim_exec_Sup_seq. *)
(*   apply Rbar_le_fin; first lra. *)
(*   apply upper_bound_ge_sup. *)
(*   assert (forall n ζ e σ v r, *)
(*             to_val e = None -> *)
(*             (0<=r)%R ->  *)
(*             (forall n' ζ', SeriesC (λ '(e', σ', efs), prim_step e σ (e', σ', efs) * sch_exec sch n' (ζ', (e'::efs, σ')) v)<=r)%R-> *)
(*             (sch_exec sch n (ζ, ([e], σ)) v <= r%nat)%R) as K. *)
(*   { intros n. induction n as [|n IHn]; intros; first by (simpl; case_match). *)
(*     simpl. *)
(*     case_match; first done. *)
(*     rewrite /sch_step/step/=. *)
(*     rewrite H3. *)
(*     rewrite {1 2}/dbind/dbind_pmf{1 2}/pmf. *)
(*     setoid_rewrite <-SeriesC_scal_r.  *)
(*     (* rewrite fubini_pos_seriesC'. *) *)
(*     admit. } *)
(*   assert (∀ n ζ σ v, (sch_exec sch n (ζ, ([diverge #()], σ)) v <= 0)%R) as Hdiverge. *)
(*   { admit. } *)
(*   intros n. *)
(*   replace ((SeriesC (sch_exec sch n (ζ, ([prog3], σ))))) with ((SeriesC (λ v, if bool_decide (v= #()) then sch_exec sch n (ζ, ([prog3], σ)) #() else 0))); last first. *)
(*   { apply SeriesC_ext. *)
    
(*     intros v. case_bool_decide; first (by subst). *)
(*     symmetry. *)
(*     apply Rle_antisym; last done. *)
(*     apply K; [done|done|]. *)
(*     clear n ζ. *)
(*     intros n ζ. *)
(*     rewrite /prog3. *)
(*     eassert ((if: (rand #1) = #1 then #() else diverge #())%E = fill _ (rand #1)).  *)
(*     { by instantiate (1:= (BinOpLCtx _ _)::(IfCtx _ _)::[]). } *)
(*     rewrite H1. *)
(*     rewrite fill_dmap; last done. *)
(*     simpl. *)
(*     rewrite head_prim_step_eq/=. *)
(*     rewrite dmap_comp. *)
(*     assert (SeriesC *)
(*      (λ '(e', σ', efs), *)
(*         dmap *)
(*           (con_language.fill_lift' (fill [BinOpLCtx EqOp #1; IfCtx #() (diverge #())]) *)
(*            ∘ λ n0 : fin (S (Z.to_nat 1)), (Val #n0, σ, [])) (dunifP (Z.to_nat 1)) ( *)
(*             e', σ', efs) * sch_exec sch n (ζ, (e' :: efs, σ')) v) = *)
(*             SeriesC *)
(*               (λ x, *)
(*                  if bool_decide (x ∈ [((if: #1=#1 then #() else diverge #())%E, σ, []); ((if: #0=#1 then #() else diverge #())%E, σ, [])]) then *)
(*                  let '(e', σ', efs) := x in *)
(*                  dmap *)
(*                    (con_language.fill_lift' (fill [BinOpLCtx EqOp #1; IfCtx #() (diverge #())]) *)
(*                       ∘ λ n0 : fin (S (Z.to_nat 1)), (Val #n0, σ, [])) (dunifP (Z.to_nat 1)) ( *)
(*                      e', σ', efs) * sch_exec sch n (ζ, (e' :: efs, σ')) v *)
(*                                              else 0 *)
(*               ) *)
              
(*            )%R as K'; last rewrite K'. *)
(*     { *)
(*       apply SeriesC_ext. *)
(*       intros [[??]]. *)
(*       case_bool_decide; first done. *)
(*       replace (dmap _ _ _) with 0%R; first lra. *)
(*       symmetry. *)
(*       apply dmap_elem_ne. *)
(*       - intros ??.  simpl. intros. by simplify_eq. *)
(*       - intros [x'[H' ?]]. *)
(*         simpl in *. *)
(*         simplify_eq. *)
(*         pose proof fin_to_nat_lt x'. *)
(*         destruct (fin_to_nat x') as [|[|]]; last lia; set_solver. *)
(*     } *)
(*     rewrite SeriesC_list; last first. *)
(*     { apply NoDup_cons; split; first set_solver. *)
(*       apply NoDup_singleton. *)
(*     } *)
(*     simpl. *)
(*     replace (sch_exec sch _ _ _) with 0%R; first replace (sch_exec sch _ _ _) with 0%R; first lra; symmetry. *)
(*     - apply Rle_antisym; last done. *)
(*       apply K; [done|done|]. *)
(*       clear n ζ K'. *)
(*       intros n ζ. *)
(*       eassert ((if: #0 = #1 then #() else diverge #())%E = fill _ (#0=#1)).  *)
(*       { by instantiate (1:= (IfCtx _ _)::[]). } *)
(*       rewrite H2. *)
(*       rewrite fill_dmap; last done. *)
(*       simpl. *)
(*       rewrite head_prim_step_eq/=. *)
(*       rewrite dmap_dret. *)
(*       assert (SeriesC *)
(*      (λ '(e', σ', efs), *)
(*         dret (con_language.fill_lift' (fill [IfCtx #() (diverge #())]) (Val #false, σ, [])) (e', σ', efs) * *)
(*           sch_exec sch n (ζ, (e' :: efs, σ')) v) = *)
(*               SeriesC (λ x, *)
(*                          if bool_decide (x = (con_language.fill_lift' (fill [IfCtx #() (diverge #())]) (Val #false, σ, []))) then  *)
(*                          let '(e', σ', efs) := x in  *)
(*         dret (con_language.fill_lift' (fill [IfCtx #() (diverge #())]) (Val #false, σ, [])) (e', σ', efs) * *)
(*           sch_exec sch n (ζ, (e' :: efs, σ')) v else 0) *)
(*              )%R as Hrewrite'; last rewrite Hrewrite'. *)
(*       { apply SeriesC_ext. *)
(*         intros [[??]]. *)
(*         case_bool_decide; first done. *)
(*         rewrite dret_0; first lra. done. *)
(*       } *)
(*       rewrite SeriesC_singleton_dependent. *)
(*       simpl. *)
(*       rewrite dret_1_1; last done. *)
(*       rewrite Rmult_1_l. *)
(*       apply K; [done|done|]. *)
(*       clear n ζ Hrewrite'. *)
(*       intros n ζ. *)
(*       rewrite head_prim_step_eq/=. *)
(*       assert (SeriesC *)
(*       (λ '(e', σ', efs), *)
(*         dret (diverge #(), σ, []) (e', σ', efs) * sch_exec sch n (ζ, (e' :: efs, σ')) v) = *)
(*               SeriesC  (λ x, *)
(*                           if bool_decide (x = (diverge #(), σ, [])) then *)
(*                           let '(e', σ', efs) := x in *)
(*                           dret (diverge #(), σ, []) (e', σ', efs) * sch_exec sch n (ζ, (e' :: efs, σ')) v else 0) )%R as Hrewrite'; last rewrite Hrewrite'. *)
(*       { apply SeriesC_ext. *)
(*         intros [[??]]. *)
(*         case_bool_decide; first done. *)
(*         rewrite dret_0; first lra. done. *)
(*       } *)
(*       rewrite SeriesC_singleton_dependent. *)
(*       simpl. *)
(*       rewrite dret_1_1; last done. *)
(*       rewrite Rmult_1_l. *)
(*       apply Hdiverge. *)
(*     - apply Rle_antisym; last done. *)
(*       apply K; [done|done|]. *)
(*       clear n ζ K'. *)
(*       intros n ζ. *)
(*       eassert ((if: #1 = #1 then #() else diverge #())%E = fill _ (#1=#1)).  *)
(*       { by instantiate (1:= (IfCtx _ _)::[]). } *)
(*       rewrite H2. *)
(*       rewrite fill_dmap; last done. *)
(*       simpl. *)
(*       rewrite head_prim_step_eq/=. *)
(*       rewrite dmap_dret. *)
(*       assert (SeriesC *)
(*      (λ '(e', σ', efs), *)
(*         dret (con_language.fill_lift' (fill [IfCtx #() (diverge #())]) (Val #true, σ, [])) (e', σ', efs) * *)
(*           sch_exec sch n (ζ, (e' :: efs, σ')) v) = *)
(*               SeriesC (λ x, *)
(*                          if bool_decide (x = (con_language.fill_lift' (fill [IfCtx #() (diverge #())]) (Val #true, σ, []))) then  *)
(*                          let '(e', σ', efs) := x in  *)
(*         dret (con_language.fill_lift' (fill [IfCtx #() (diverge #())]) (Val #true, σ, [])) (e', σ', efs) * *)
(*           sch_exec sch n (ζ, (e' :: efs, σ')) v else 0) *)
(*              )%R as Hrewrite'; last rewrite Hrewrite'. *)
(*       { apply SeriesC_ext. *)
(*         intros [[??]]. *)
(*         case_bool_decide; first done.  *)
(*         rewrite dret_0; first lra. done. *)
(*       } *)
(*       rewrite SeriesC_singleton_dependent. *)
(*       simpl. *)
(*       rewrite dret_1_1; last done. *)
(*       rewrite Rmult_1_l. *)
(*       apply K; [done|done|]. *)
(*       clear n ζ Hrewrite'. *)
(*       intros n ζ. *)
(*       rewrite head_prim_step_eq/=. *)
(*       assert (SeriesC *)
(*       (λ '(e', σ', efs), *)
(*         dret (Val #(), σ, []) (e', σ', efs) * sch_exec sch n (ζ, (e' :: efs, σ')) v) = *)
(*               SeriesC  (λ x, *)
(*                           if bool_decide (x = (Val #(), σ, [])) then *)
(*                           let '(e', σ', efs) := x in *)
(*                           dret (Val #(), σ, []) (e', σ', efs) * sch_exec sch n (ζ, (e' :: efs, σ')) v else 0) )%R as Hrewrite'; last rewrite Hrewrite'. *)
(*       { apply SeriesC_ext. *)
(*         intros [[??]]. *)
(*         case_bool_decide; first done. *)
(*         rewrite dret_0; first lra. done. *)
(*       } *)
(*       rewrite SeriesC_singleton_dependent. *)
(*       simpl. *)
(*       rewrite dret_1_1; last done. *)
(*       rewrite Rmult_1_l. *)
(*       erewrite sch_exec_is_final; last done. *)
(*       by rewrite dret_0. *)
(*   } *)
(*   rewrite SeriesC_singleton. *)
(*   rewrite /prog3. *)
(*   apply rbar_le_rle. *)
(*   apply K; [done|lra|]. *)
(*   clear n ζ. *)
(*   intros n ζ. *)
(*   eassert ((if: (rand #1) = #1 then #() else diverge #())%E = fill _ (rand #1)).  *)
(*   { by instantiate (1:= (BinOpLCtx _ _)::(IfCtx _ _)::[]). } *)
(*   rewrite H0. *)
(*   rewrite fill_dmap; last done. *)
(*   simpl. *)
(*   rewrite head_prim_step_eq/=. *)
(*   rewrite dmap_comp. *)
(*   assert (SeriesC *)
(*             (λ '(e', σ', efs), *)
(*                dmap *)
(*                  (con_language.fill_lift' (fill [BinOpLCtx EqOp #1; IfCtx #() (diverge #())]) *)
(*                     ∘ λ n0 : fin (S (Z.to_nat 1)), (Val #n0, σ, [])) (dunifP (Z.to_nat 1)) ( *)
(*                    e', σ', efs) * sch_exec sch n (ζ, (e' :: efs, σ')) #()) = *)
(*           SeriesC *)
(*             (λ x, *)
(*                if bool_decide (x ∈ [((if: #1=#1 then #() else diverge #())%E, σ, []); ((if: #0=#1 then #() else diverge #())%E, σ, [])]) then *)
(*                  let '(e', σ', efs) := x in *)
(*                  dmap *)
(*                    (con_language.fill_lift' (fill [BinOpLCtx EqOp #1; IfCtx #() (diverge #())]) *)
(*                       ∘ λ n0 : fin (S (Z.to_nat 1)), (Val #n0, σ, [])) (dunifP (Z.to_nat 1)) ( *)
(*                      e', σ', efs) * sch_exec sch n (ζ, (e' :: efs, σ')) #() *)
(*                else 0 *)
(*             ) *)
            
(*          )%R as K'; last rewrite K'. *)
(*   { *)
(*     apply SeriesC_ext. *)
(*     intros [[??]]. *)
(*     case_bool_decide; first done. *)
(*     replace (dmap _ _ _) with 0%R; first lra. *)
(*     symmetry. *)
(*     apply dmap_elem_ne. *)
(*     - intros ??.  simpl. intros. by simplify_eq. *)
(*     - intros [x'[H' ?]]. *)
(*       simpl in *. *)
(*       simplify_eq. *)
(*       pose proof fin_to_nat_lt x'. *)
(*       destruct (fin_to_nat x') as [|[|]]; last lia; set_solver. *)
(*   } *)
(*   rewrite SeriesC_list; last first. *)
(*   { apply NoDup_cons; split; first set_solver. *)
(*     apply NoDup_singleton. *)
(*   } *)
(*   simpl. *)
(*   trans (dmap *)
(*      (con_language.fill_lift' (fill [BinOpLCtx EqOp #1; IfCtx #() (diverge #())]) *)
(*       ∘ λ n0 : fin (S (Z.to_nat 1)), (Val #n0, σ, [])) (dunifP (Z.to_nat 1)) *)
(*      ((if: #1 = #1 then #() else diverge #())%E, σ, []) * *)
(*    1 + *)
(*    (dmap *)
(*       (con_language.fill_lift' (fill [BinOpLCtx EqOp #1; IfCtx #() (diverge #())]) *)
(*        ∘ λ n0 : fin (S (Z.to_nat 1)), (Val #n0, σ, [])) (dunifP (Z.to_nat 1)) *)
(*       ((if: #0 = #1 then #() else diverge #())%E, σ, []) * *)
(*       sch_exec sch n (ζ, ([(if: #0 = #1 then #() else diverge #())%E], σ)) #() + 0))%R. *)
(*   { apply Rplus_le_compat; try done. *)
(*     apply Rmult_le_compat; done. *)
(*   } *)
(*   replace (sch_exec sch _ _ _) with 0%R; try symmetry. *)
(*   { erewrite !dmap_elem_eq. *)
(*     - rewrite /dunifP/dunif/pmf/=. lra. *)
(*     - intros ??. simpl. *)
(*       intros. by simplify_eq. *)
(*     - simpl. by instantiate (1:=0%fin). *)
(*     - intros ??. intros. by simplify_eq. *)
(*     - simpl. by instantiate (1:=1%fin). *)
(*   }  *)
(*   apply Rle_antisym; last done. *)
(*   apply K; [done|lra|]. *)
(*   clear n ζ K'. *)
(*   intros n ζ. *)
(*   eassert ((if: #0 = #1 then #() else diverge #())%E = fill _ (#0=#1)).  *)
(*   { by instantiate (1:= (IfCtx _ _)::[]). } *)
(*   rewrite H1. *)
(*   rewrite fill_dmap; last done. *)
(*   simpl. *)
(*   rewrite head_prim_step_eq/=. *)
(*   rewrite dmap_dret. *)
(*   assert (SeriesC *)
(*             (λ '(e', σ', efs), *)
(*                dret (con_language.fill_lift' (fill [IfCtx #() (diverge #())]) (Val #false, σ, [])) (e', σ', efs) * *)
(*                  sch_exec sch n (ζ, (e' :: efs, σ')) #()) = *)
(*           SeriesC (λ x, *)
(*                      if bool_decide (x = (con_language.fill_lift' (fill [IfCtx #() (diverge #())]) (Val #false, σ, []))) then  *)
(*                        let '(e', σ', efs) := x in  *)
(*                        dret (con_language.fill_lift' (fill [IfCtx #() (diverge #())]) (Val #false, σ, [])) (e', σ', efs) * *)
(*                          sch_exec sch n (ζ, (e' :: efs, σ')) #() else 0) *)
(*          )%R as Hrewrite'; last rewrite Hrewrite'. *)
(*   { apply SeriesC_ext. *)
(*     intros [[??]]. *)
(*     case_bool_decide; first done. *)
(*     rewrite dret_0; first lra. done. *)
(*   } *)
(*   rewrite SeriesC_singleton_dependent. *)
(*   simpl. *)
(*   rewrite dret_1_1; last done. *)
(*   rewrite Rmult_1_l. *)
(*   apply K; [done|lra|]. *)
(*   clear n ζ Hrewrite'. *)
(*   intros n ζ. *)
(*   rewrite head_prim_step_eq/=. *)
(*   assert (SeriesC *)
(*             (λ '(e', σ', efs), *)
(*                dret (diverge #(), σ, []) (e', σ', efs) * sch_exec sch n (ζ, (e' :: efs, σ')) #()) = *)
(*           SeriesC  (λ x, *)
(*                       if bool_decide (x = (diverge #(), σ, [])) then *)
(*                         let '(e', σ', efs) := x in *)
(*                         dret (diverge #(), σ, []) (e', σ', efs) * sch_exec sch n (ζ, (e' :: efs, σ')) #() else 0) )%R as Hrewrite'; last rewrite Hrewrite'. *)
(*   { apply SeriesC_ext. *)
(*     intros [[??]]. *)
(*     case_bool_decide; first done. *)
(*     rewrite dret_0; first lra. done. *)
(*   } *)
(*   rewrite SeriesC_singleton_dependent. *)
(*   simpl. *)
(*   rewrite dret_1_1; last done. *)
(*   rewrite Rmult_1_l. *)
(*   apply Hdiverge. *)
(* Admitted.  *)


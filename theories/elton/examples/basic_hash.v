From iris.base_logic.lib Require Import token.
From clutch.elton Require Import elton hash. 
Set Default Proof Using "Type*".

(** https://github.com/proof-ladders/protocol-ladder/blob/main/Notes/main.pdf
    Basic Hash  *)

Lemma INR_div_pos x y: (0<=INR x/INR y)%R.
Proof.
  destruct y.
  { simpl. rewrite Rdiv_0_r. lra. }
  rewrite Rdiv_def.
  apply Rcomplements.Rle_div_r.
  - apply Rlt_gt.
    apply lt_0_INR; lia.
  - rewrite Rmult_0_l.
    replace 0%R with (INR 0) by done. 
    apply le_INR.
    lia.
Qed.

Section prog.
  Variable tag_range:nat.
  Variable nonce_range:nat.
  Variable val_size: nat.
  Variable tries: nat.

  Definition prog : expr :=
    λ: "A",
      let: "hashf" := init_hash val_size #() in
      let: "pair" := rand #((tag_range+1)*(tag_range+1)-1) in
      let: "b" := rand #1 in
      let: "T1" := "pair" `quot` #(tag_range+1) in
      let: "T2" := "b" * "T1" + (#1-"b") * ("pair" `rem` #(tag_range+1)) in
      let: "n1" := rand #nonce_range in
      (* Pay error for n2 to avoid colliding with n1*) 
      let: "n2" := rand #nonce_range in
      let: "h1" := "hashf" ("n1"*#(tag_range+1) +"T1") in 
      let: "h2" := "hashf" ("n2"*#(tag_range+1) +"T2") in
      
      let: "i" := ref #tries in
      let: "hashf'" :=
        (λ: "x", if: ! "i" = #0
                 then NONE
                 else "i" <- ! "i" - #1;; SOME ("hashf" "x") ) in

      let: "g" := "A" ("n1", "h1") ("n2", "h2") "hashf'" in
      "g" = "b". 

  Definition prog' : expr :=
    λ: "A",
      let: "hashf" := init_hash val_size #() in
      let: "pair" := drand #((tag_range+1)*(tag_range+1)-1) in
      let: "b" := drand #1 in
      let: "T1" := "pair" `quot` #(tag_range+1) in
      let: "T2" := "b" * "T1" + (#1-"b") * ("pair" `rem` #(tag_range+1)) in
      let: "n1" := rand #nonce_range in
      let: "n2" := rand #nonce_range in
      let: "h1" := "hashf" ("n1"*#(tag_range+1) +"T1") in 
      let: "h2" := "hashf" ("n2"*#(tag_range+1) +"T2") in
      
      let: "i" := ref #tries in
      let: "hashf'" :=
        (λ: "x", if: ! "i" = #0
                 then NONE
                 else "i" <- ! "i" - #1;; SOME ("hashf" "x") ) in

      let: "g" := "A" ("n1", "h1") ("n2", "h2") "hashf'"  in
      "g" = "b".
  
  (* Context `{eltonGS Σ}. *)

  Lemma basic_hash_game A:
    ∅ ⊢ₜ A : ((TInt* TInt) → (TInt* TInt) → (TInt → (TUnit+TInt))  → TInt) ->
             pgl (lim_exec ((prog A), {|heap:=∅; urns:= ∅|})) (λ v, v=#false)
               (1/2 + 1/(nonce_range +1 )%nat + (2*(tries)%nat)/(tag_range+1)%nat).
  Proof.
    intros Htyped.
    destruct (decide (2*(tries)<tag_range+1)) as [initial_ineq|]; last first.
    {
      apply pgl_1.
      apply Rle_plus_r; last first.
      - apply Rle_plus_r; last lra. apply Rdiv_INR_ge_0.
      - apply Rcomplements.Rle_div_r; first (apply Rlt_gt; apply lt_0_INR; lia).
        rewrite Rmult_1_l.
        replace 2%R with (INR 2) by done.
        rewrite -mult_INR.
        apply le_INR.
        lia.
    }
    eapply (elton_adequacy_remove_drand (#[eltonΣ; tokenΣ]) (prog' A)).
    { simpl; by erewrite typed_remove_drand_expr. }
    { apply Rplus_le_le_0_compat; last real_solver.
      apply Rplus_le_le_0_compat; first lra. apply Rdiv_INR_ge_0. }
    rewrite /prog'.
    iIntros (? Φ).
    iModIntro.
    iIntros "Herr HΦ".
    
    iPoseProof (typed_safe _ [] _ Htyped) as "H".
    wp_bind (A).
    iApply (pgl_wp_wand); first done.
    iIntros (?) "#Hinterp".
    simpl.
    wp_pures.

    
    wp_apply (wp_init_hash); first done.
    iIntros (f) ">Hf".
    wp_pures.
    
    wp_apply (wp_drand_thunk _ _ _ _ _ (True)).
    { rewrite rupd_unseal/rupd_def.
      iIntros (?) "$".
      iPureIntro.
      intros.
      simpl.
      eexists _; split; first done.
      f_equal.
      f_equal.
      instantiate (1:=(tag_range+1) *(tag_range+1)-1).
      lia. }
      iIntros (l) "[_ Hl]".
      rewrite Nat2Z.id.
      wp_pures.

    wp_apply (wp_drand_thunk _ _ _ _ _ (True)).
    { rewrite rupd_unseal/rupd_def.
      iIntros (?) "$".
      iPureIntro.
      intros.
      simpl.
      eexists _; split; first done.
      f_equal.
      f_equal.
      instantiate (1:=1).
      lia. }
      iIntros (b) "[_ Hb]".
      rewrite Nat2Z.id.
      wp_pures.

      wp_apply wp_rand; first done.
      iIntros (n1) "_".
      wp_pures.

      iDestruct (ec_split with "[$]") as "[Herr1 Herr2]"; [|real_solver|].
      { apply Rplus_le_le_0_compat; real_solver. }

      
      iDestruct (ec_split with "[$Herr1]") as "[Herr1 Herr1']"; [real_solver..|].

      wp_apply (wp_couple_rand_adv_comp' _ _ _ _ (λ x, if bool_decide (x = n1) then nnreal_one else nnreal_zero)with "[$Herr1']").
      { intros. case_bool_decide; simpl; lra. }
      { rewrite SeriesC_scal_l. rewrite SeriesC_singleton.
        rewrite Rmult_1_r.
        rewrite S_INR. by rewrite plus_INR. 
      }
      iIntros (n2) "Herr1'".
      case_bool_decide as nonce_neq; first (by iDestruct (ec_contradict with "[$Herr1']") as "[]").
      wp_pures.
      iClear "Herr1'".

      iMod (ec_zero) as "Hzero".
      wp_apply (wp_insert_new _ _ _ _ _ _ (λ _, 0)%R True with "[$Hf $Hzero]").
      { done. }
      { by intros. }
      { right. apply SeriesC_0. intros. lra. }
      { iModIntro. rewrite dom_empty_L. by rewrite big_sepS_empty. }
      iIntros (h1) "(Hf&_)".
      wp_pures.

      iMod (ec_zero) as "Hzero".
      wp_apply (wp_insert_new _ _ _ _ _ _ (λ _, 0)%R ((l↪ _) ∗ (b↪ _)) with "[$Hf $Hzero $Hl $Hb]").
      { done. }
      { by intros. }
      { right. apply SeriesC_0. intros. lra. }
      { iModIntro.
        rewrite insert_empty.
        rewrite dom_singleton_L.
        iApply big_sepS_intro.
        iModIntro.
        iIntros (?) "%Hlookup'".
        iIntros "[Hl Hb]".

        rewrite rupd_unseal/rupd_def.
        iIntros  (?) "[? Hu]". iSplit; last iFrame.
        iDestruct (ghost_map_lookup with "Hu [$Hb]") as "%Hlookup_b".
        iDestruct (ghost_map_lookup with "Hu [$Hl]") as "%Hlookup_l".
        iPureIntro.
        intros.
        exists false. split => //.
        eapply urns_f_distr_lookup in Hlookup_l ; last done.
        2:{ admit. }
        eapply urns_f_distr_lookup in Hlookup_b ; last done.
        2:{ admit. }
        destruct Hlookup_l as (?&Hsome_l&Hin).
        destruct Hlookup_b as (?&Hsome_b&Hin').
        simpl.
        rewrite Hsome_l Hsome_b. simpl.
        set_unfold in Hlookup'. simplify_eq.
        simpl. rewrite Hsome_l. simpl. f_equal.
        case_bool_decide as hh ; try done. exfalso.
        clear -hh nonce_neq Hin Hin'.
        simpl in Hin'.
        set_unfold in Hin'.
        set_unfold in Hin.
        destruct Hin as [? [? []]]. simplify_eq.

        opose proof (Zdiv_mod_unique (tag_range+1) n1 n2
                       (x `quot` (tag_range + 1))
                       (x1 * x `quot` (tag_range + 1) + (1 - x1) * x `rem` (tag_range + 1))
                       _ _) as h.
        - apply Zabs_ind ; intros ; try lia. split.
          + apply Z.quot_pos ; lia.
          + apply Z.quot_lt_upper_bound ; lia.
        - apply Zabs_ind ; intros ; try lia. split.
          + apply Z.add_nonneg_nonneg ; apply Z.mul_nonneg_nonneg ; try lia.
            * apply Z.quot_pos ; lia.
            * apply Z.rem_nonneg ; lia.
          +
            destruct!/=.
            * rewrite Z.mul_0_l Z.add_0_l. rewrite Z.sub_0_r Z.mul_1_l.
              apply Z.rem_bound_pos_pos ; lia.
            * rewrite Z.mul_1_l Z.sub_diag Z.mul_0_l Z.add_0_r.
              apply Z.quot_lt_upper_bound ; lia.
        - apply nonce_neq.
          unshelve epose proof (h _) as [] ; last by simplify_eq.
          lia.
      }
      iIntros (h2) "(Hf&(Hl&Hb)&_)".
      wp_pures.

      wp_alloc lt as "Hr".
      wp_pures.
  (*
    Let k1 = l/S tag_range and k2 = l%S tag_range
     Here h1 is storing h (n1 || k1)
     Here h2 is storing either h (n2 || k1) or (n2 || l%k2)

     Let s1 be the range of values k1 can be, similarly be s2.
     This means initially s1 and s2 = {0, ... , tag_range}
     Initially the urn l is storing s1 ** s2,
     where (x ** y) is a set of all elements (a*S tag_range + b) for all a in x, b in y

     Now each time the adversary queries the hash, say with input i,
     let i' = i%(S tag_range), we pay errors to ensure i' is not stored in s1 or s2
     This way, i is never (n1||k1) or (n2||k2)

     The adversary gets "tries" attempt, and a 1/2 chance to get the b correct

     Hence the error is 2*(tries)/(S tag_range) + 1/2
   *)
      assert (gset Z -> gset Z -> gset Z ) as setprod.
      1: admit.
      set (n1_b_n2_T2 := ((n2 * (tag_range + 1))%Z +ᵥ
               ((LitLbl b *ᵥ QuotOp' (LitLbl l) (tag_range + 1)%Z) +ᵥ
                ((1%Z -ᵥ LitLbl b) *ᵥ RemOp' (LitLbl l) (tag_range + 1)%Z)))%V).
      set (n1_T1 := ((n1 * (tag_range + 1))%Z +ᵥ
                  QuotOp' (LitLbl l) (tag_range + 1)%Z)%V).

      iMod (token_alloc) as (γ) "Htoken".

      set (inv :=
  ( ∃ (tries':nat) (m:gmap Z nat) (x y : fin (S val_size)),
             hashfun val_size f (<[n1_b_n2_T2:=fin_to_nat x]> (<[n1_T1:=fin_to_nat y]> (kmap (λ x, LitInt (x)) m)))∗
             lt ↦ #tries' ∗ (⌜(tries'<=tries)%nat ⌝) ∗
             ∃ (s1 s2 : gset Z),
               ⌜∀ x : Z, x ∈ s1 -> (n1 * (tag_range + 1) + x ∉ ((dom m) : gset _))%Z⌝ ∗
               (* morally, depends on b which one we need; we'll just keep both. *)
               ⌜∀ x : Z, x ∈ s1 -> (n2 * (tag_range + 1) + x ∉ ((dom m) : gset _))%Z⌝ ∗
               ⌜∀ x : Z, x ∈ s2 -> (n2 * (tag_range + 1) + x ∉ ((dom m) : gset _))%Z⌝ ∗

                     ⌜∀ x : Z, x ∈ s1 -> 0 <= x <= tag_range⌝%Z ∗ ⌜∀ x : Z, x ∈ s2 -> 0 <= x <= tag_range⌝%Z ∗

                     ⌜s1 ≠ ∅⌝ ∗ ⌜s2 ≠ ∅⌝ ∗
                     l↪ urn_unif (setprod s1  s2)∗
                     ↯ (tries' / size s1) ∗ ↯ (tries' / size s2) ∗
                     ⌜(S tag_range - (tries - tries')) <= size s1⌝ ∗
                     ⌜(S tag_range - (tries - tries')) <= size s2⌝ ∗
                   ((
                     b ↪ urn_unif (list_to_set (Z.of_nat <$> seq 0 2)) ∗
                     ↯ (1/2)
                    ) ∨ ((token γ) ∗ ∃ (b_resolved : nat), ⌜b_resolved <= 1⌝ ∗ b ↪ urn_unif {[Z.of_nat b_resolved]}) )
               )%I).
      iMod (inv_alloc (nroot) _ inv with "[-]") as "#Hinv".
      {
        iNext. iExists _,_,_,_. iFrame "Hr".
        instantiate (1 := ∅). rewrite kmap_empty. iFrame "Hf".
        iSplit => //. iExists _,_.
  Abort.

  (*     iAssert (∃s, l↪urn_unif s ∗ ⌜size s = S secret_range⌝)%I with "[$Hl]" as "H'". *)
  (*     { iPureIntro. *)
  (*       rewrite size_list_to_set. *)
  (*       - rewrite length_fmap length_seq. lia. *)
  (*       - apply NoDup_fmap; last apply NoDup_seq. *)
  (*         apply Nat2Z.inj'. *)
  (*     } *)
  (*     iDestruct "H'" as "(%s&Hl&%Hsize)". *)
  (*     iMod (token_alloc) as (γ) "Htoken". *)
  (*   iMod (inv_alloc (nroot) _ *)
  (*           ( ∃ (tries':nat) (m:gmap Z _), *)
  (*               hashfun val_size f (<[LitLbl l:=fin_to_nat secret]> (kmap (λ x, LitInt (x)) m))∗ *)
  (*               lt ↦ #tries' ∗ (⌜(tries'<=tries)%nat ⌝) ∗ *)
  (*               ∃ (s':gset Z), *)
  (*                 ⌜s' ## ((dom m):gset _)⌝ ∗ *)
  (*                 ⌜s'≠∅⌝ ∗ *)
  (*                 l↪ urn_unif (s')∗ *)
  (*               (( *)
  (*                    (⌜∀ x y, m!!x=Some y -> y≠ fin_to_nat secret⌝) ∗ *)
  (*                    ↯ ((tries'+1)/(val_size +1)%nat) ∗ *)
  (*                    ↯ ((tries'+1)%nat / size s') ∗ *)
  (*                    ⌜secret_range + 1  + tries' - tries <=size s'⌝  *)
  (*                )∨ (token γ)) *)
  (*           )%I *)
  (*          with "[Herr1 Herr2 Hf Hr Hl]") as "#Hinv". *)
  (*   { iNext. iFrame "Hr". *)
  (*     iExists ∅. *)
  (*     rewrite kmap_empty. *)
  (*     iFrame. *)
  (*     iSplit; first done. *)
  (*     repeat iSplit; last iLeft; iFrame. *)
  (*     - iPureIntro. rewrite dom_empty. set_solver. *)
  (*     - iPureIntro. *)
  (*       intros ->. *)
  (*       rewrite size_empty in Hsize. lia. *)
  (*     - rewrite Hsize. rewrite S_INR plus_INR. *)
  (*       replace 1%R with (INR 1) by done. *)
  (*       rewrite Rdiv_def. rewrite plus_INR. simpl. *)
  (*       iFrame.  *)
  (*       repeat iSplit. *)
  (*       + iPureIntro. *)
  (*         intros. simplify_map_eq. *)
  (*       + iPureIntro. lia. *)
  (*   } *)
    
  (*   wp_bind (v _)%E. *)
  (*   rewrite refines_eq /refines_def. *)
  (*   simpl. *)
  (*   iApply (pgl_wp_wand); first iApply "Hinterp". *)
  (*   { iModIntro. *)
  (*     iIntros (?) "[%guess ->]". *)
  (*     rewrite refines_eq/refines_def. *)
  (*     wp_pures. *)
  (*     iInv "Hinv" as ">(%tries'&%m&Hf&Hl&%& (%s'&%Hdisjoint&%Hnonempty&Hurn &Hor))" "Hclose". *)
  (*     wp_load. *)
  (*     wp_pures. *)
  (*     case_bool_decide. *)
  (*     - wp_pures. *)
  (*       iMod ("Hclose" with "[-]"); first by iFrame. *)
  (*       iModIntro. *)
  (*       iExists _. iLeft. by iSplit. *)
  (*     - wp_pures. *)
  (*       wp_load.  *)
  (*       wp_pures. *)
  (*       wp_store. *)
  (*       iDestruct "Hor" as "[Hor|Hor]". *)
  (*       + (** normal case *) *)
  (*         destruct (decide (guess ∈ (( (dom m)):gset _))) as [Hlookup|]. *)
  (*         { (** it has been queried before *) *)
  (*           rewrite elem_of_dom in Hlookup. *)
  (*           destruct Hlookup. *)
            
  (*           wp_apply (wp_hashfun_prev _ _ _ _ _ _ guess (l↪ _) with "[$Hurn $Hf]"). *)
  (*           - done. *)
  (*           - simplify_map_eq. *)
  (*             erewrite lookup_kmap_Some; first naive_solver. *)
  (*             intros ???. by simplify_eq. *)
  (*           - iSplit. *)
  (*             + iModIntro. *)
  (*               iIntros. *)
  (*               rewrite rupd_unseal/rupd_def. *)
  (*               iIntros  (?) "[? Hu]". iSplit; last iFrame. *)
  (*               iDestruct (ghost_map_lookup with "Hu [$]") as "%Hlookup". *)
  (*               iPureIntro. *)
  (*               intros. simpl. case_bool_decide; naive_solver. *)
  (*             + iModIntro. *)
  (*               iApply big_sepS_intro. *)
  (*               iModIntro. *)
  (*               setoid_rewrite elem_of_difference. *)
  (*               iIntros (?) "[%Hlookup' %]". *)
  (*               iIntros "?". *)
  (*               rewrite rupd_unseal/rupd_def. *)
  (*               iIntros  (?) "[? Hu]". iSplit; last iFrame. *)
  (*               iDestruct (ghost_map_lookup with "Hu [$]") as "%Hlookup". *)
  (*               iPureIntro. *)
  (*               intros. *)
  (*               eapply urns_f_distr_lookup in Hlookup; last done; last done. *)
  (*               destruct Hlookup as (?&Hsome&Hin). *)
  (*               eexists _; split; last done. *)
  (*               simpl. *)
  (*               rewrite elem_of_dom in Hlookup'. *)
  (*               destruct Hlookup' as [? Hlookup']. *)
  (*               rewrite lookup_insert_Some in Hlookup'. *)
  (*               destruct!/=. *)
  (*               * rewrite Hsome/=. rewrite bool_decide_eq_false_2; first done. *)
  (*                 intros ?. simplify_eq. *)
  (*                 apply Hdisjoint in Hin. *)
  (*                 apply Hin. *)
  (*                 rewrite elem_of_dom. naive_solver. *)
  (*               * rename select (kmap _ _ !! _ = _) into K1. *)
  (*                 apply lookup_kmap_Some in K1; last (intros ???; by simplify_eq). *)
  (*                 destruct!/=. rewrite bool_decide_eq_false_2; first done. *)
  (*                 intros ?. simplify_eq. *)
  (*                 set_unfold. simplify_eq. *)
  (*           - iIntros "[Hf Hu]". *)
  (*             wp_pures. *)
  (*             iMod ("Hclose" with "[Hl Hf Hu Hor]"). *)
  (*             { iNext. *)
  (*               iFrame "Hf Hu". *)
  (*               replace (Z.of_nat _ -_)%Z with (Z.of_nat (tries' - 1)); last first.  *)
  (*               { assert (tries' ≠ 0)%nat; last lia. *)
  (*                 by intros ->. *)
  (*               } *)
  (*               iFrame "Hl". *)
  (*               repeat iSplit. *)
  (*               - iPureIntro; lia. *)
  (*               - done. *)
  (*               - done. *)
  (*               - iLeft. *)
  (*                 iDestruct "Hor" as "(%&Herr&Herr'&%)". *)
  (*                 repeat iSplit. *)
  (*                 + done. *)
  (*                 + iSplitL "Herr"; last repeat iSplit. *)
  (*                   * iApply (ec_weaken with "[$]"). *)
  (*                     replace 1%R with (INR 1) by done. *)
  (*                     rewrite -!plus_INR. *)
  (*                     split; first apply INR_div_pos. *)
  (*                     rewrite !Rdiv_def. *)
  (*                     apply Rmult_le_compat_r. *)
  (*                     -- rewrite -Rdiv_1_l. *)
  (*                        apply Rdiv_INR_ge_0. *)
  (*                     -- apply le_INR. lia. *)
  (*                   * iApply (ec_weaken with "[$]"). *)
  (*                     split; first apply INR_div_pos. *)
  (*                     rewrite !Rdiv_def. *)
  (*                     apply Rmult_le_compat_r. *)
  (*                     -- rewrite -Rdiv_1_l. *)
  (*                        apply Rdiv_INR_ge_0. *)
  (*                     -- apply le_INR. lia. *)
  (*                   * iPureIntro. lia. *)
  (*             } *)
  (*             iModIntro. *)
  (*             iExists _. iRight. *)
  (*             iSplit; first done. *)
  (*             by iExists _. *)
  (*         } *)
  (*         (** Not queries before *) *)
  (*         iDestruct "Hor" as "(%&Herr1&Herr2&%)". *)
  (*         assert (tries' ≠ 0). *)
  (*         { intros ?. simplify_eq. } *)
  (*         iAssert (pupd ∅ ∅ (∃s'', ⌜ s'' ⊆ s' ⌝ ∗ ⌜ s''≠∅⌝ ∗ *)
  (*                                  l ↪ urn_unif s'' ∗ ⌜guess∉ s''⌝ ∗ *)
  (*                                  ⌜size s'<=size s''+1⌝ ∗ *)
  (*                                  ↯ ((tries'-1+1)%nat/size s'') *)
  (*                 ))%I with "[Hurn Herr2]" as ">H'". *)
  (*         { destruct (decide (guess ∈ s')); last first. *)
  (*          - iModIntro. *)
  (*            iFrame. *)
  (*            repeat iSplit; try done. *)
  (*            + iPureIntro; lia. *)
  (*            + iApply (ec_weaken with "[$]"). *)
  (*              split. *)
  (*              * apply INR_div_pos. *)
  (*              * rewrite !Rdiv_def. *)
  (*                apply Rmult_le_compat_r. *)
  (*                -- rewrite -Rdiv_1_l. apply Rdiv_INR_ge_0. *)
  (*                -- apply le_INR. lia. *)
  (*          - assert (0<= (tries'-1+1)%nat/(size s' -1)%nat)%R as err_ineq. *)
  (*            { apply INR_div_pos. } *)
  (*            iAssert (⌜2<=size s'⌝)%I as "%". *)
  (*            { destruct (size s') as [|[|]]eqn:Hcontra; last (iPureIntro; lia). *)
  (*              - apply size_empty_inv in Hcontra. *)
  (*                by rewrite leibniz_equiv_iff in Hcontra. *)
  (*              - iDestruct (ec_contradict with "[$]") as "[]". *)
  (*                simpl. *)
  (*                rewrite Rdiv_1_r. *)
  (*                replace 1%R with (INR 1) by done. *)
  (*                apply le_INR. lia. *)
  (*            } *)
  (*            iMod (pupd_partial_resolve_urn _ _ (λ x, if bool_decide (x=({[guess]} : gset _)) then nnreal_one else mknonnegreal _ err_ineq) _ _ (({[guess]} ::(s'∖{[guess]}) ::[]): list (gset _)) with "[$][$]") as "H'". *)
  (*            + done. *)
  (*            + simpl. *)
  (*              rewrite union_empty_r_L. *)
  (*              rewrite -union_difference_L; first done. *)
  (*              set_solver. *)
  (*            + repeat setoid_rewrite NoDup_cons. *)
  (*              repeat split; last by apply NoDup_nil. *)
  (*              -- set_unfold. *)
  (*                 intros ?. destruct!/=. set_solver. *)
  (*              -- set_solver. *)
  (*            + set_unfold. *)
  (*              intros ?. *)
  (*              destruct!/=. *)
  (*              rename select (_=_∖_) into Hcontra. *)
  (*              apply (f_equal size) in Hcontra. *)
  (*              rewrite size_empty size_difference in Hcontra; last set_solver. *)
  (*              rewrite size_singleton in Hcontra. lia. *)
  (*            + intros. *)
  (*              set_unfold. *)
  (*              destruct!/=; set_solver. *)
  (*            + rewrite SeriesC_list; last first. *)
  (*              { repeat setoid_rewrite NoDup_cons. *)
  (*                repeat split; last by apply NoDup_nil. *)
  (*                - set_unfold. *)
  (*                  intros ?. destruct!/=. set_solver. *)
  (*                - set_solver. } *)
  (*              Local Opaque size. *)
  (*              simpl. *)
  (*              rewrite bool_decide_eq_true_2; last done. *)
  (*              rewrite Rmult_1_l size_singleton. *)
  (*              rewrite bool_decide_eq_false_2; last set_solver. *)
  (*              rewrite Rplus_0_r. *)
  (*              simpl. *)
  (*              rewrite size_difference; last set_solver. *)
               
  (*              replace (_-_+_) with tries' by lia. *)
  (*              rewrite !Rdiv_def. *)
  (*              apply Rmult_le_compat_r. *)
  (*              * rewrite -Rdiv_1_l. *)
  (*                apply Rdiv_INR_ge_0. *)
  (*              * rewrite size_singleton. *)
  (*                rewrite plus_INR. *)
  (*                simpl. *)
  (*                rewrite Rmult_assoc. *)
  (*                rewrite (Rmult_comm (/ _)%R). *)
  (*                assert ((size s' - 1)%nat */(size s' -1)%nat=1)%R as ->; last lra. *)
  (*                rewrite -Rdiv_def. *)
  (*                rewrite Rdiv_diag; first done. *)
  (*                rewrite minus_INR; last lia. *)
  (*                simpl. *)
  (*                assert (INR (size s') ≠ 1)%R; last lra. *)
  (*                replace 1%R with (INR 1) by done. *)
  (*                apply not_INR. lia.  *)
  (*            + eexists (Rmax _ _). *)
  (*              intros. *)
  (*              case_bool_decide. *)
  (*              -- apply Rmax_l. *)
  (*              -- apply Rmax_r. *)
  (*            + iDestruct "H'" as "(%&Herr&Hurn &%)". *)
  (*              set_unfold. *)
  (*              destruct!/=. *)
  (*              * rewrite bool_decide_eq_true_2; last done. *)
  (*                by iDestruct (ec_contradict with "[$]") as "[]". *)
  (*              * rewrite bool_decide_eq_false_2; last set_solver. *)
  (*                iFrame. *)
  (*                iModIntro. *)
  (*                repeat iSplit; try iPureIntro. *)
  (*                -- set_solver. *)
  (*                -- intros Hcontra. *)
  (*                   apply (f_equal size) in Hcontra. *)
  (*                   rewrite size_empty size_difference in Hcontra; last set_solver. *)
  (*                   rewrite size_singleton in Hcontra. lia. *)
  (*                -- set_solver. *)
  (*                -- rewrite size_difference; last set_solver. *)
  (*                   rewrite size_singleton. lia. *)
  (*                -- iApply (ec_eq with "[$]"). *)
  (*                   simpl. rewrite size_difference; last set_solver. *)
  (*                   by rewrite size_singleton. *)
  (*         } *)
  (*         iDestruct "H'" as "(%s''&%&%&Hurn&%Hnotin&%Hsize'&Herr2)". *)
  (*         replace (_/_)%R with (((tries'-1)%nat+1)/(val_size+1)%nat+1/(val_size+1)%nat)%R; last first. *)
  (*         { rewrite -Rdiv_plus_distr. f_equal. f_equal. *)
  (*           rewrite minus_INR; last lia. *)
  (*           simpl. *)
  (*           lra.  *)
  (*         } *)
  (*         iDestruct (ec_split with "[$]") as "[Herr1 Herr1']". *)
  (*         { replace 1%R with (INR 1) by done. rewrite -plus_INR. *)
  (*           apply INR_div_pos. *)
  (*         } *)
  (*         { replace 1%R with (INR 1) by done. apply INR_div_pos. } *)
  (*         wp_apply (wp_insert_new _ _ _ _ _ _ (λ x, if bool_decide (x= secret) then nnreal_one else nnreal_zero)%R (l↪ _) with "[$Hf $Herr1' $Hurn]"). *)
  (*         * done. *)
  (*         * intros. case_bool_decide; simpl; lra. *)
  (*         * rewrite SeriesC_scal_l. *)
  (*           rewrite SeriesC_singleton. *)
  (*           rewrite Rmult_1_r. *)
  (*           rewrite S_INR. *)
  (*           by rewrite plus_INR. *)
  (*         * iModIntro. *)
  (*           iApply big_sepS_intro. *)
  (*           iModIntro. *)
  (*           iIntros (?) "%Hlookup'". *)
  (*           iIntros "?". *)
  (*           rewrite rupd_unseal/rupd_def. *)
  (*           iIntros  (?) "[? Hu]". iSplit; last iFrame. *)
  (*           iDestruct (ghost_map_lookup with "Hu [$]") as "%Hlookup". *)
  (*           iPureIntro. *)
  (*           intros. *)
  (*           eapply urns_f_distr_lookup in Hlookup; last done; last done. *)
  (*           destruct Hlookup as (?&Hsome&Hin). *)
  (*           eexists _; split; last done. *)
  (*           simpl. *)
  (*           rewrite elem_of_dom in Hlookup'. *)
  (*           destruct Hlookup' as [? Hlookup']. *)
  (*           rewrite lookup_insert_Some in Hlookup'. *)
  (*           destruct!/=. *)
  (*           -- rewrite Hsome/=. rewrite bool_decide_eq_false_2; first done. *)
  (*              intros ?. simplify_eq. *)
  (*           -- rename select (kmap _ _ !! _ = _) into K1. *)
  (*              apply lookup_kmap_Some in K1; last (intros ???; by simplify_eq). *)
  (*              destruct!/=. rewrite bool_decide_eq_false_2; first done. *)
  (*              intros ?. simplify_eq. *)
  (*              rename select (m!!_=Some _) into Hcontra. *)
  (*              apply elem_of_dom_2 in Hcontra. *)
  (*              set_solver. *)
  (*         * iIntros (?) "(Hf&Hurn&Herr)". *)
  (*           case_bool_decide. *)
  (*           { by iDestruct (ec_contradict with "[$]") as "[]". } *)
  (*           wp_pures. *)
  (*           iMod ("Hclose" with "[-Herr]"). *)
  (*           { iNext. *)
  (*             replace (Z.of_nat _ - _)%Z with (Z.of_nat (tries'-1)) by lia. *)
  (*             iFrame "Hl". iFrame "Hurn". *)
  (*             iExists _. *)
  (*             erewrite kmap_insert; last (intros ???; by simplify_eq). *)
  (*             rewrite insert_commute; last done. *)
  (*             iFrame. *)
  (*             repeat iSplit; last iLeft; repeat iSplit. *)
  (*             - iPureIntro; lia. *)
  (*             - iPureIntro. set_unfold. set_solver. *)
  (*             - done. *)
  (*             - iPureIntro. *)
  (*               intros ?? Hlookup'. *)
  (*               apply lookup_insert_Some in Hlookup'. *)
  (*               destruct!/=. *)
  (*               + intros Hcontra. *)
  (*                 by apply fin_to_nat_inj in Hcontra. *)
  (*               + naive_solver. *)
  (*             - rewrite (plus_INR (_-_)). iFrame. *)
  (*               iPureIntro. lia. *)
  (*           } *)
  (*           iExists _. iModIntro. *)
  (*           iRight. *)
  (*           iSplit; first done. *)
  (*           by iExists _. *)
  (*       + (** token case, its a weird case *) *)
  (*         assert (tries' ≠ 0). *)
  (*         { intros ->. simplify_eq. } *)
  (*         iMod (ec_zero) as "Herr". *)
  (*         iMod (pupd_resolve_urn _ _ (λ _, nnreal_zero) with "[$][$]") as "(%&_&Hurn&%)". *)
  (*         * done. *)
  (*         * rewrite SeriesC_0; first lra. *)
  (*           intros. *)
  (*           by case_bool_decide. *)
  (*         * naive_solver. *)
  (*         * destruct (decide (guess ∈ dom m)) as [Hlookup|]. *)
  (*           (** queried before *) *)
  (*           { rewrite elem_of_dom in Hlookup. *)
  (*             destruct Hlookup. *)
  (*             wp_apply (wp_hashfun_prev _ _ _ _ _ _ guess (l↪ _) with "[$Hurn $Hf]"). *)
  (*             - done. *)
  (*             - rewrite lookup_insert_Some. right. split; first done. *)
  (*               erewrite lookup_kmap_Some; last (intros ???; by simplify_eq). *)
  (*               naive_solver. *)
  (*             - iSplit. *)
  (*               + iModIntro. *)
  (*                 iIntros. *)
  (*                 rewrite rupd_unseal/rupd_def. *)
  (*                 iIntros  (?) "[? Hu]". iSplit; last iFrame. *)
  (*                 iDestruct (ghost_map_lookup with "Hu [$]") as "%Hlookup". *)
  (*                 iPureIntro. *)
  (*                 intros. simpl. case_bool_decide; naive_solver. *)
  (*               + iModIntro. *)
  (*                 iApply big_sepS_intro. *)
  (*                 iModIntro. *)
  (*                 setoid_rewrite elem_of_difference. *)
  (*                 iIntros (?) "[%Hlookup' %]". *)
  (*                 iIntros "?". *)
  (*                 rewrite rupd_unseal/rupd_def. *)
  (*                 iIntros  (?) "[? Hu]". iSplit; last iFrame. *)
  (*                 iDestruct (ghost_map_lookup with "Hu [$]") as "%Hlookup". *)
  (*                 iPureIntro. *)
  (*                 intros. *)
  (*                 eapply urns_f_distr_lookup in Hlookup; last done; last done. *)
  (*                 destruct Hlookup as (?&Hsome&Hin). *)
  (*                 eexists _; split; last done. *)
  (*                 simpl. *)
  (*                 rewrite elem_of_dom in Hlookup'. *)
  (*                 destruct Hlookup' as [? Hlookup']. *)
  (*                 rewrite lookup_insert_Some in Hlookup'. *)
  (*                 destruct!/=. *)
  (*                 * rewrite Hsome/=. rewrite bool_decide_eq_false_2; first done. *)
  (*                   intros ?. simplify_eq. *)
  (*                   set_unfold. destruct!/=. *)
  (*                   eapply Hdisjoint; first done. *)
  (*                   setoid_rewrite elem_of_dom. naive_solver. *)
  (*                 * rename select (kmap _ _ !! _ = _) into K1. *)
  (*                   apply lookup_kmap_Some in K1; last (intros ???; by simplify_eq). *)
  (*                   destruct!/=. rewrite bool_decide_eq_false_2; first done. *)
  (*                   intros ?. simplify_eq. *)
  (*                   set_unfold. simplify_eq.  *)
  (*             - iIntros "[Hf Hurn]". *)
  (*               wp_pures. *)
  (*               iMod ("Hclose" with "[-]"). *)
  (*               { iNext. *)
  (*                 replace (Z.of_nat _ - _)%Z with (Z.of_nat (tries' - 1)) by lia. *)
  (*                 iFrame "Hl Hf Hurn". *)
  (*                 repeat iSplit; last iRight; last iFrame; iPureIntro.  *)
  (*                 - lia. *)
  (*                 - set_solver. *)
  (*                 - done.  *)
  (*               } *)
  (*               iModIntro. *)
  (*               iExists _. iRight. *)
  (*               iSplit; first done. *)
  (*               by iExists _. *)
  (*           } *)
  (*           destruct (decide (guess = x)). *)
  (*           { (** guess is x*) *)
  (*             wp_apply (wp_hashfun_prev _ _ _ _ _ _ (LitLbl l) (l↪ _) with "[$Hurn $Hf]"). *)
  (*             - done. *)
  (*             - rewrite lookup_insert_Some. naive_solver. *)
  (*             - iSplit. *)
  (*               + iModIntro. *)
  (*                 iIntros. *)
  (*                 rewrite rupd_unseal/rupd_def. *)
  (*                 iIntros  (?) "[? Hu]". iSplit; last iFrame. *)
  (*                 iDestruct (ghost_map_lookup with "Hu [$]") as "%Hlookup". *)
  (*                 iPureIntro. *)
  (*                 intros. simpl. *)
  (*                 eapply urns_f_distr_lookup in Hlookup; last done; last done. *)
  (*                 destruct Hlookup as (?&Hsome&Hin). *)
  (*                 eexists _; split; last done. *)
  (*                 rewrite Hsome. simpl. *)
  (*                 set_unfold. destruct!/=. *)
  (*                 by case_bool_decide.  *)
  (*               + iModIntro. *)
  (*                 iApply big_sepS_intro. *)
  (*                 iModIntro. *)
  (*                 setoid_rewrite elem_of_difference. *)
  (*                 iIntros (?) "[%Hlookup' %]". *)
  (*                 iIntros "?". *)
  (*                 rewrite rupd_unseal/rupd_def. *)
  (*                 iIntros  (?) "[? Hu]". iSplit; last iFrame. *)
  (*                 iDestruct (ghost_map_lookup with "Hu [$]") as "%Hlookup". *)
  (*                 iPureIntro. *)
  (*                 intros. *)
  (*                 eapply urns_f_distr_lookup in Hlookup; last done; last done. *)
  (*                 destruct Hlookup as (?&Hsome&Hin). *)
  (*                 eexists _; split; last done. *)
  (*                 simpl. *)
  (*                 rewrite elem_of_dom in Hlookup'. *)
  (*                 destruct Hlookup' as [? Hlookup']. *)
  (*                 rewrite lookup_insert_Some in Hlookup'. *)
  (*                 destruct!/=. *)
  (*                 * rewrite Hsome/=. rewrite bool_decide_eq_false_2; first done. *)
  (*                   intros ?. simplify_eq. *)
  (*                   set_unfold. destruct!/=. *)
  (*                 * rename select (kmap _ _ !! _ = _) into K1. *)
  (*                   apply lookup_kmap_Some in K1; last (intros ???; by simplify_eq). *)
  (*                   destruct!/=. rewrite bool_decide_eq_false_2; first done. *)
  (*                   intros ?. simplify_eq. *)
  (*                   set_unfold. simplify_eq.  *)
  (*                   eapply Hdisjoint; first done. *)
  (*                   setoid_rewrite elem_of_dom. naive_solver. *)
  (*             - iIntros "[Hf Hurn]". *)
  (*               wp_pures. *)
  (*               iMod ("Hclose" with "[-]"). *)
  (*               { iNext. *)
  (*                 replace (Z.of_nat _ - _)%Z with (Z.of_nat (tries' - 1)) by lia. *)
  (*                 iFrame "Hl Hf Hurn". *)
  (*                 repeat iSplit; last iRight; last iFrame; iPureIntro.  *)
  (*                 - lia. *)
  (*                 - set_solver. *)
  (*                 - done.  *)
  (*               } *)
  (*               iModIntro. *)
  (*               iExists _. iRight. *)
  (*               iSplit; first done. *)
  (*               by iExists _. *)
  (*             } *)
  (*             (** guess is not queried before *) *)
  (*             iMod (ec_zero) as "Herr". *)
  (*           wp_apply (wp_insert_new _ _ _ _ _ _ (λ x, nnreal_zero)%R (l↪ _) with "[$Hf $Herr $Hurn]"). *)
  (*           -- done. *)
  (*           -- naive_solver. *)
  (*           -- rewrite SeriesC_0; first done. *)
  (*              intros. simpl. lra. *)
  (*           -- iModIntro. *)
  (*              iApply big_sepS_intro. *)
  (*              iModIntro. *)
  (*              iIntros (?) "%Hlookup'". *)
  (*              iIntros "?". *)
  (*              rewrite rupd_unseal/rupd_def. *)
  (*              iIntros  (?) "[? Hu]". iSplit; last iFrame. *)
  (*              iDestruct (ghost_map_lookup with "Hu [$]") as "%Hlookup". *)
  (*              iPureIntro. *)
  (*              intros. *)
  (*              eapply urns_f_distr_lookup in Hlookup; last done; last done. *)
  (*              destruct Hlookup as (?&Hsome&Hin). *)
  (*              eexists _; split; last done. *)
  (*              simpl. *)
  (*              rewrite elem_of_dom in Hlookup'. *)
  (*              destruct Hlookup' as [? Hlookup']. *)
  (*              rewrite lookup_insert_Some in Hlookup'. *)
  (*              destruct!/=. *)
  (*              ++ rewrite Hsome/=. rewrite bool_decide_eq_false_2; first done. *)
  (*                 intros ?. simplify_eq. *)
  (*                 set_unfold. destruct!/=. *)
  (*              ++ rename select (kmap _ _ !! _ = _) into K1. *)
  (*                 apply lookup_kmap_Some in K1; last (intros ???; by simplify_eq). *)
  (*                 destruct!/=. rewrite bool_decide_eq_false_2; first done. *)
  (*                 set_unfold. simplify_eq. *)
  (*                 rename select (_∉dom _) into Hcontra. *)
  (*                 rewrite elem_of_dom in Hcontra. *)
  (*                 intros ?. simplify_eq. naive_solver. *)
  (*           -- iIntros (?) "(Hf&Hurn&_)". *)
  (*              wp_pures. *)
  (*              iMod ("Hclose" with "[-]"). *)
  (*              { iNext. *)
  (*                replace (Z.of_nat _ - _)%Z with (Z.of_nat (tries' - 1)) by lia. *)
  (*                iExists _, _. *)
  (*                erewrite kmap_insert; last (intros ???; by simplify_eq). *)
  (*                rewrite insert_commute; last done.  *)
  (*                iFrame "Hl Hurn Hf". *)
  (*                repeat iSplit; last iRight; last iFrame; iPureIntro.  *)
  (*                - lia. *)
  (*                - set_solver. *)
  (*                - done.  *)
  (*              } *)
  (*              iModIntro. *)
  (*              iExists _. iRight. *)
  (*              iSplit; first done. *)
  (*              by iExists _. *)
  (*   } *)
  (*   (** * Final bit *) *)
  (*   iIntros (f') "#Hinterp'". *)
  (*   wp_bind (f' _)%E. *)
  (*   rewrite refines_eq /refines_def. *)
  (*   iApply (pgl_wp_wand); first iApply "Hinterp'". *)
  (*   { iExists (nat_to_fin (fin_to_nat_lt _)). by rewrite fin_to_nat_to_fin. } *)
  (*   iIntros (?) "[%guess ->]". *)
  (*   wp_pures.  *)
  (*   iInv "Hinv" as ">(%tries'&%m&Hf&Hl&%& (%s'&%Hdisjoint&%Hnonempty&Hurn &Hor))" "Hclose". *)
  (*   iDestruct ("Hor") as "[Hor|Htoken']"; last first. *)
  (*   { iCombine "Htoken" "Htoken'" gives "[]". } *)
  (*   iDestruct "Hor" as "(%Hnotin&Herr&Herr'&%H1)". *)
  (*   assert (is_valid_urn (urn_unif s')). *)
  (*   { simpl. *)
  (*     intros ->. *)
  (*     rewrite size_empty in H1. lia. *)
  (*   } *)

    
  (*   destruct (decide (guess ∈ dom m)) as [Hlookup|]. *)
  (*     -- (** Return something hashed before *) *)
  (*       rewrite elem_of_dom in Hlookup. *)
  (*       destruct Hlookup. *)
        
  (*       wp_apply (wp_hashfun_prev _ _ _ _ _ _ guess (l↪ _) with "[$Hurn $Hf]"). *)
  (*       ++ done. *)
  (*       ++ simplify_map_eq. *)
  (*          erewrite lookup_kmap_Some; first naive_solver. *)
  (*          intros ???. by simplify_eq. *)
  (*       ++ iSplit. *)
  (*          ** iModIntro. *)
  (*             iIntros. *)
  (*             rewrite rupd_unseal/rupd_def. *)
  (*             iIntros  (?) "[? Hu]". iSplit; last iFrame. *)
  (*             iDestruct (ghost_map_lookup with "Hu [$]") as "%Hlookup". *)
  (*             iPureIntro. *)
  (*             intros. simpl. case_bool_decide; naive_solver. *)
  (*          ** iModIntro. *)
  (*             iApply big_sepS_intro. *)
  (*             iModIntro. *)
  (*             setoid_rewrite elem_of_difference. *)
  (*             iIntros (?) "[%Hlookup' %]". *)
  (*             iIntros "?". *)
  (*             rewrite rupd_unseal/rupd_def. *)
  (*             iIntros  (?) "[? Hu]". iSplit; last iFrame. *)
  (*             iDestruct (ghost_map_lookup with "Hu [$]") as "%Hlookup". *)
  (*             iPureIntro. *)
  (*             intros. *)
  (*             eapply urns_f_distr_lookup in Hlookup; last done; last done. *)
  (*             destruct Hlookup as (?&Hsome&Hin). *)
  (*             eexists _; split; last done. *)
  (*             simpl. *)
  (*             rewrite elem_of_dom in Hlookup'. *)
  (*             destruct Hlookup' as [? Hlookup']. *)
  (*             rewrite lookup_insert_Some in Hlookup'. *)
  (*             destruct!/=. *)
  (*             --- rewrite Hsome/=. rewrite bool_decide_eq_false_2; first done. *)
  (*                 intros ?. simplify_eq. *)
  (*                 apply Hdisjoint in Hin. *)
  (*                 apply Hin. *)
  (*                 rewrite elem_of_dom. naive_solver. *)
  (*             --- rename select (kmap _ _ !! _ = _) into K1. *)
  (*                 apply lookup_kmap_Some in K1; last (intros ???; by simplify_eq). *)
  (*                 destruct!/=. rewrite bool_decide_eq_false_2; first done. *)
  (*                 intros ?. simplify_eq. *)
  (*                 set_unfold. simplify_eq. *)
  (*       ++ iIntros "[Hf Hu]". *)
  (*          wp_pures. *)
  (*          rewrite bool_decide_eq_false_2; last first. *)
  (*          { intros ?. simplify_eq. *)
  (*            naive_solver. *)
  (*          } *)
  (*          iMod ("Hclose" with "[Htoken Hl Hf Hu]"). *)
  (*          { iNext. *)
  (*            iFrame "Hl Hf Hu". *)
  (*            repeat iSplit; try done. *)
  (*            by iRight.  *)
  (*          } *)
  (*          by iApply "HΦ". *)
  (*     -- iAssert (pupd ∅ ∅ (∃s'', ⌜ s'' ⊆ s' ⌝ ∗ ⌜ s''≠∅⌝ ∗ *)
  (*                                 l ↪ urn_unif s'' ∗ ⌜guess∉ s''⌝ *)
  (*                ))%I with "[Herr' Hurn]" as ">H'". *)
  (*        { destruct (decide (guess ∈ s')); last first. *)
  (*          - iModIntro. *)
  (*            iFrame. *)
  (*            iPureIntro. simpl in *. naive_solver. *)
  (*          - iMod (pupd_resolve_urn _ _ (λ x, if bool_decide (x=guess) then nnreal_one else nnreal_zero) with "[$][$]") as "(%&?&?&%)". *)
  (*            + done. *)
  (*            + erewrite (SeriesC_ext _ (λ x, if bool_decide (x=guess) then nnreal_one else nnreal_zero)); last first. *)
  (*              -- intros. *)
  (*                 case_bool_decide as H3; first by case_bool_decide. *)
  (*                 rewrite bool_decide_eq_false_2; first done. *)
  (*                 intros ->. apply H3. set_solver. *)
  (*              -- rewrite SeriesC_singleton. *)
  (*                 simpl. *)
  (*                 rewrite !Rdiv_def. *)
  (*                 apply Rmult_le_compat_r. *)
  (*                 ++ rewrite -Rdiv_1_l. *)
  (*                    apply Rdiv_INR_ge_0. *)
  (*                 ++ replace 1%R with (INR 1) by done. *)
  (*                    apply le_INR. *)
  (*                    lia. *)
  (*            + exists 1. *)
  (*              intros. *)
  (*              case_bool_decide; simpl; lra. *)
  (*            + case_bool_decide. *)
  (*              * by iDestruct (ec_contradict with "[$]") as "[]". *)
  (*              * iFrame. *)
  (*                iModIntro. *)
  (*                iPureIntro. *)
  (*                set_solver.        *)
  (*        } *)
  (*        iDestruct "H'" as "(%s''&%&%&Hurn &%)". *)
  (*        wp_apply (wp_insert_new _ _ _ _ _ _ (λ x, if bool_decide (x= secret) then nnreal_one else nnreal_zero)%R (l↪ _) with "[$Hf $Herr $Hurn]"). *)
  (*        ++ done. *)
  (*        ++ intros. case_bool_decide; simpl; lra. *)
  (*        ++ rewrite SeriesC_scal_l. rewrite SeriesC_singleton. *)
  (*           rewrite Rmult_1_r. *)
  (*           rewrite S_INR. *)
  (*           replace 1%R with (INR 1) by done. *)
  (*           rewrite -!plus_INR. *)
  (*           simpl. *)
  (*           rewrite !Rdiv_def. *)
  (*           apply Rmult_le_compat_r. *)
  (*           ** rewrite -Rdiv_1_l. *)
  (*              apply Rdiv_INR_ge_0. *)
  (*           ** replace 1%R with (INR 1) by done. *)
  (*              apply le_INR. *)
  (*              lia. *)
  (*        ++ iModIntro. *)
  (*           iApply big_sepS_intro. *)
  (*           iModIntro. *)
  (*           iIntros (?) "%Hlookup'". *)
  (*           iIntros "?". *)
  (*           rewrite rupd_unseal/rupd_def. *)
  (*           iIntros  (?) "[? Hu]". iSplit; last iFrame. *)
  (*           iDestruct (ghost_map_lookup with "Hu [$]") as "%Hlookup". *)
  (*           iPureIntro. *)
  (*           intros. *)
  (*           eapply urns_f_distr_lookup in Hlookup; last done; last done. *)
  (*           destruct Hlookup as (?&Hsome&Hin). *)
  (*           eexists _; split; last done. *)
  (*           simpl. *)
  (*           rewrite elem_of_dom in Hlookup'. *)
  (*           destruct Hlookup' as [? Hlookup']. *)
  (*           rewrite lookup_insert_Some in Hlookup'. *)
  (*           destruct!/=. *)
  (*           ** rewrite Hsome/=. *)
  (*              rewrite bool_decide_eq_false_2; first done. *)
  (*              intros ?. simplify_eq. *)
  (*           ** rename select (kmap _ _ !!_=_) into Hlookup'. *)
  (*              apply lookup_kmap_Some in Hlookup'; last (intros ???; by simplify_eq). *)
  (*              destruct!/=. *)
  (*              rewrite bool_decide_eq_false_2; first done. *)
  (*              intros ?. simplify_eq. *)
  (*              rename select (m!!_=Some _) into Hcontra. *)
  (*              apply elem_of_dom_2 in Hcontra. *)
  (*              set_solver. *)
  (*        ++ iIntros (?) "(Hf&Hurn &Herr)". *)
  (*           case_bool_decide. *)
  (*           { by iDestruct (ec_contradict with "[$]") as "[]". } *)
  (*           wp_pures. *)
  (*           iMod ("Hclose" with "[-HΦ]"). *)
  (*           { iNext. *)
  (*             iFrame "Hl". *)
  (*             rewrite insert_commute; last done. *)
  (*             iExists _. *)
  (*             erewrite kmap_insert; first iFrame "Hf"; last (intros ???; by simplify_eq). *)
  (*             iSplit; first done. *)
  (*             iFrame "Hurn". *)
  (*             repeat iSplit; last by iRight. *)
  (*             - iPureIntro. *)
  (*               set_solver. *)
  (*             - done. *)
  (*           } *)
  (*           iApply "HΦ". *)
  (*           iModIntro. *)
  (*           iPureIntro. *)
  (*           split; first done. *)
  (*           rewrite bool_decide_eq_false_2; first done. *)
  (*           intros ?. simplify_eq. *)
  (* Qed. *)
        
End prog.

From iris.base_logic.lib Require Import token.
From clutch.elton Require Import elton hash
  (* examples.finset_bijection examples.gset_bij_lift *).
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

  Definition prog_two_urns : expr :=
    λ: "A",
      let: "hashf" := init_hash val_size #() in
      let: "b" := rand #1 in
      let: "T1" := rand #(tag_range) in
      let: "T2" := "b" * "T1" + (#1-"b") * rand #(tag_range) in
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

  Definition prog_two_urns_delayed : expr :=
    λ: "A",
      let: "hashf" := init_hash val_size #() in
      let: "b" := drand #1 in
      let: "T1" := drand #(tag_range) in
      let: "T2" := "b" * "T1" + (#1-"b") * drand #(tag_range) in
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


  (* Definition zedprod_inv (N : Z) (Npos : (0 < N)%Z) (s : gset (fin ((Z.to_nat N) * (Z.to_nat N))))
       : prodset (fin (Z.to_nat N)) (fin (Z.to_nat N))
       := FS_bij ((gset_bij_lift (finset_bij_fun N Npos)) s).

     Definition zedprod (N : Z) (Npos : (0 < N)%Z) (s1_s2 : prodset (fin (Z.to_nat N)) (fin (Z.to_nat N)))
       : gset (fin ((Z.to_nat N) * (Z.to_nat N)))
       := (gset_bij_lift (f_inv $ finset_bij_fun N Npos)) (FS_bij_inv s1_s2).

     #[local] Instance zedprod_inv_inj {N : Z} {h : (0 < N)%Z} : Inj eq eq (zedprod_inv N h).
     unfold zedprod_inv.
     eapply (compose_inj eq eq eq _ FS_bij) ;
       try apply _. apply FS_bij_TC.
     Defined.

     #[local] Instance zedprod_inv_surj {N : Z} {h : (0 < N)%Z} : Surj eq (zedprod_inv N h).
     unfold zedprod_inv.
     eapply (compose_surj eq _ FS_bij) ;
       try apply _. apply FS_bij_TC.
     Defined.


     #[local] Instance zedprod_bij {N : Z} {h : (0 < N)%Z} : Inj eq eq (zedprod N h).
     unfold zedprod.
     eapply compose_inj.
     intros ?? heq.

     apply _.
     #[local] Instance zedprod_bij {N : Z} {h : 0 < N} : Bij (zedprod N h).
     rewrite /zedprod. split ; apply _. *)


  Lemma basic_hash_game_two_urns A:
    ∅ ⊢ₜ A : ((TInt* TInt) → (TInt* TInt) → (TInt → (TUnit+TInt))  → TInt) ->
             pgl (lim_exec ((prog_two_urns A), {|heap:=∅; urns:= ∅|})) (λ v, v=#false)
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
    eapply (elton_adequacy_remove_drand (#[eltonΣ; tokenΣ]) (prog_two_urns_delayed A)).
    { simpl; by erewrite typed_remove_drand_expr. }
    { apply Rplus_le_le_0_compat; last real_solver.
      apply Rplus_le_le_0_compat; first lra. apply Rdiv_INR_ge_0. }
    rewrite /prog_two_urns_delayed.
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
      instantiate (1:=1).
      lia. }
      iIntros (b) "[_ Hb]".
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
      instantiate (1:=(tag_range)).
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
      instantiate (1:=(tag_range)).
      lia. }
      iIntros (l') "[_ Hl']".
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
      wp_apply (wp_insert_new _ _ _ _ _ _ (λ _, 0)%R ((l↪ _) ∗ (l'↪ _) ∗ (b↪ _)) with "[$Hf $Hzero $Hl $Hl' $Hb]").
      { done. }
      { by intros. }
      { right. apply SeriesC_0. intros. lra. }
      { iModIntro.
        rewrite insert_empty.
        rewrite dom_singleton_L.
        iApply big_sepS_intro.
        iModIntro.
        iIntros (?) "%Hlookup'".
        iIntros "[Hl [Hl' Hb]]".

        rewrite rupd_unseal/rupd_def.
        iIntros  (?) "[? Hu]". iSplit; last iFrame.
        iDestruct (ghost_map_lookup with "Hu [$Hb]") as "%Hlookup_b".
        iDestruct (ghost_map_lookup with "Hu [$Hl]") as "%Hlookup_l".
        iDestruct (ghost_map_lookup with "Hu [$Hl']") as "%Hlookup_l'".
        iPureIntro.
        intros.
        exists false. split => //.
        eapply urns_f_distr_lookup in Hlookup_l ; last done.
        2:{ simpl. set_solver. }
        eapply urns_f_distr_lookup in Hlookup_l' ; last done.
        2:{ simpl. set_solver. }
        eapply urns_f_distr_lookup in Hlookup_b ; last done.
        2:{ simpl. set_solver. }
        destruct Hlookup_l as (?&Hsome_l&Hin).
        destruct Hlookup_l' as (?&Hsome_l'&Hin_l').
        destruct Hlookup_b as (?&Hsome_b&Hin').
        simpl.
        rewrite Hsome_l Hsome_l' Hsome_b. simpl.
        set_unfold in Hlookup'. simplify_eq.
        simpl. rewrite Hsome_l. simpl. f_equal.
        case_bool_decide as hh ; try done. exfalso.
        clear -hh nonce_neq Hin Hin' Hin_l'.
        simpl in Hin'.
        set_unfold in Hin'.
        set_unfold in Hin.
        set_unfold in Hin_l'.
        destruct Hin as [? [? []]]. simplify_eq.
        destruct Hin_l' as [? [? []]]. simplify_eq.

        opose proof (Zdiv_mod_unique (tag_range+1) n1 n2
                       (x)
                       (x2 * x + (1 - x2) * x0)
                       _ _) as h.

        - apply Zabs_ind ; intros ; try lia.
        - apply Zabs_ind ; intros ; try lia.
        - apply nonce_neq.
          unshelve epose proof (h _) as [] ; last by simplify_eq.
          lia.
      }
      iIntros (h2) "(Hf&(Hl&Hl'&Hb)&_)".
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
      (* set (ff (x y : Z) := (x * tag_range + y)%Z).
         set (f' := (λ (xy : Z * Z), ff xy.1 xy.2)).
         set (g (s1 s2 : gset Z) := (cprod s1 s2 : gset (Z * Z))).
         set (h := set_map (A := (Z*Z)) (B := Z)
                     (C := gset (Z*Z))
                     (D := gset Z)
                      f').
         set (setprod (s1 s2 : gset Z) := h (g s1 s2)).
         set (n1_b_n2_T2 := ((n2 * (tag_range + 1))%Z +ᵥ
                  ((LitLbl b *ᵥ QuotOp' (LitLbl l) (tag_range + 1)%Z) +ᵥ
                   ((1%Z -ᵥ LitLbl b) *ᵥ RemOp' (LitLbl l) (tag_range + 1)%Z)))%V).
         set (n1_T1 := ((n1 * (tag_range + 1))%Z +ᵥ
                     QuotOp' (LitLbl l) (tag_range + 1)%Z)%V). *)

      iMod (token_alloc) as (γ) "Htoken".

      set (n1_b_n2_T2 := ((n2 * (tag_range + 1))%Z +ᵥ
               ((LitLbl b *ᵥ LitLbl l) +ᵥ ((1%Z -ᵥ LitLbl b) *ᵥ LitLbl l')))%V).
      set (n1_T1 := ((n1 * (tag_range + 1))%Z +ᵥ LitLbl l)%V).
      set (inv :=
  ( ∃ (tries':nat) (m:gmap Z nat) (x y : fin (S val_size)),
             hashfun val_size f (<[n1_b_n2_T2:=fin_to_nat x]> (<[n1_T1:=fin_to_nat y]> (kmap (λ x, LitInt (x)) m)))∗
             lt ↦ #tries' ∗ (⌜(tries'<=tries)%nat ⌝) ∗
             ∃ (s : gset Z),
               ⌜∀ x : Z, x ∈ s -> (n1 * (tag_range + 1) + x ∉ ((dom m) : gset _))%Z⌝ ∗
               ⌜∀ x : Z, x ∈ s -> (n2 * (tag_range + 1) + x ∉ ((dom m) : gset _))%Z⌝ ∗

               ⌜∀ x : Z, x ∈ s -> 0 <= x <= tag_range⌝%Z ∗
                 ⌜s ≠ ∅⌝ ∗
                     (* l↪ urn_unif (setprod s1  s2)∗ *)
                     l↪ urn_unif s ∗
                     l'↪ urn_unif s ∗
                     ↯ (tries' / size s) ∗ ↯ (tries' / size s) ∗
                     ⌜(S tag_range - (tries - tries')) <= size s⌝ ∗
                   ((
                     b ↪ urn_unif (list_to_set (Z.of_nat <$> seq 0 2)) ∗
                     ↯ (1/2)
                    ) ∨ ((token γ) ∗ ∃ (b_resolved : nat), ⌜b_resolved <= 1⌝ ∗ b ↪ urn_unif {[Z.of_nat b_resolved]}) )
               )%I).
      iMod (inv_alloc (nroot) _ inv with "[-Htoken HΦ]") as "#Hinv".
      {
        iNext. iExists _,_,_,_. iFrame "Hr".
        instantiate (1 := ∅). rewrite kmap_empty. iFrame "Hf".
        iSplit => //.
        iFrame.
        rewrite -Rplus_diag.
        rewrite Rdiv_plus_distr.
        iDestruct (ec_split with "[$]") as "[??]".
        1, 2: apply INR_div_pos.
        rewrite size_list_to_set; last apply NoDup_fmap; [|apply Nat2Z.inj'|apply NoDup_seq].
        rewrite length_fmap length_seq. 
        rewrite -(Nat.add_1_r tag_range).
        iFrame.
        repeat iSplit; last (iLeft; iFrame); iPureIntro.
        - set_solver.
        - set_solver.
        - intros ?.
          rewrite elem_of_list_to_set list_elem_of_fmap.
          setoid_rewrite elem_of_seq.
          intros. destruct!/=. lia.
        - replace (tag_range+1)%nat with (S tag_range) by lia.
          simpl.
          set_solver.
        - lia. 
      }

    wp_bind (v _)%E.
    rewrite refines_eq /refines_def.
    simpl.
    iApply (pgl_wp_wand); first iApply "Hinterp".
    { iExists _, _. iSplit; first done.
      iSplit; by iExists _. }
    iIntros "%v' #Hv'".
    wp_bind (v' _)%E.
    rewrite refines_eq /refines_def.
    iApply (pgl_wp_wand); first iApply "Hv'".
    { iExists _, _. iSplit; first done.
      iSplit; by iExists _. }
    iIntros "%v'' #Hv''".
    wp_bind (v'' _)%E.
    rewrite refines_eq /refines_def.
    iApply (pgl_wp_wand); first iApply "Hv''".
    (* this is the actual interesting bit *)
    {
      iClear "H Hinterp Hv' Hv''".
      iModIntro.
      iIntros (?) "[%guess ->]".
      rewrite refines_eq/refines_def.
      wp_pures.
      iInv "Hinv" as ">(%tries'&%m&%x&%y&Hf&Hlt&%Htries& (%s'&%Hdisjoint1&%Hdisjoint2&%Hrange&%Hnonempty&Hurn&Hurn'&Herr&Herr'&%tries_range&Hor))" "Hclose".
      wp_load.
      wp_pures.
      case_bool_decide.
      - wp_pures.
        iMod ("Hclose" with "[-]"); first by iFrame.
        iModIntro.
        iExists _. iLeft. by iSplit.
      - wp_pures.
        wp_load.
        wp_pures.
        wp_store.
        iDestruct "Hor" as "[[Hb Herr'']|Hor]".
        +
          (** * Start of first case of disjunction *)
          destruct (decide (guess ∈ (( (dom m)):gset _))) as [Hlookup|].
          { (** it has been queried before *)
            rewrite elem_of_dom in Hlookup.
            destruct Hlookup as [m_guess H_m_guess].
            wp_apply (wp_hashfun_prev _ _ _ _ _ _ guess (l ↪ _ ∗ l' ↪ _ ∗ b ↪ _) with "[$Hurn $Hf $Hurn' $Hb]").
            - done.
            - simplify_map_eq.
              erewrite lookup_kmap_Some; first naive_solver.
              intros ???. by simplify_eq.
            - iSplit.
              + iModIntro.
                iIntros "(?&?&?)".
                rewrite rupd_unseal/rupd_def.
                iIntros (?) "[? Hu]". iSplit; last iFrame.
                iDestruct (ghost_map_lookup with "Hu [$]") as "%Hlookup".
                iPureIntro.
                intros. simpl. case_bool_decide; naive_solver.
              + iModIntro.
                iApply big_sepS_intro.
                iModIntro.
                setoid_rewrite elem_of_difference.
                iIntros (?) "[%Hlookup' %]".
                iIntros "(Hl&Hl'&Hb)".
                rewrite rupd_unseal/rupd_def.
                iIntros  (?) "[? Hu]". iSplit; last iFrame.
                iDestruct (ghost_map_lookup with "Hu [$Hl]") as "%Hlookup_l".
                iDestruct (ghost_map_lookup with "Hu [$Hl']") as "%Hlookup_l'".
                iDestruct (ghost_map_lookup with "Hu [$Hb]") as "%Hlookup_b".
                iPureIntro.
                intros.
                eapply urns_f_distr_lookup in Hlookup_l; last done; last done.
                eapply urns_f_distr_lookup in Hlookup_l'; last done; last done.
                eapply urns_f_distr_lookup in Hlookup_b; last done; last done.
                destruct Hlookup_l as (?&Hsome_l&Hin_l).
                destruct Hlookup_l' as (?&Hsome_l'&Hin_l').
                destruct Hlookup_b as (?&Hsome_b&Hin_b).
                eexists _; split; last done.
                simpl.
                rewrite elem_of_dom in Hlookup'.
                destruct Hlookup' as [? Hlookup'].
                rewrite lookup_insert_Some in Hlookup'.
                rewrite lookup_insert_Some in Hlookup'.
                destruct!/=.
                * rewrite Hsome_l Hsome_l' Hsome_b/=. rewrite bool_decide_eq_false_2 ; first done.
                  (* guess ∈ dom m *)
                  (* both x1 and x2 are in s' *)
                  (* but that contradiction Hdisjoint2. *)
                  intros ?. simplify_eq.
                  set_unfold in Hin_b. destruct!/=.
                  -- eapply Hdisjoint2.
                     1: apply Hin_l'.
                     rewrite elem_of_dom.
                     eexists.
                     erewrite <- H_m_guess.
                     repeat f_equal. lia.
                  -- eapply Hdisjoint2.
                     1: apply Hin_l.
                     rewrite elem_of_dom.
                     eexists.
                     erewrite <- H_m_guess.
                     repeat f_equal. lia.
                * rewrite Hsome_l.
                  simpl.
                  rewrite bool_decide_eq_false_2 ; first done.
                  intros ?. simplify_eq.
                  eapply Hdisjoint1.
                     1: apply Hin_l.
                     rewrite elem_of_dom.
                     eexists.
                     erewrite <- H_m_guess.
                     repeat f_equal.
                * simpl.
                  rename select (kmap _ _ !! _ = _) into K1.
                  apply lookup_kmap_Some in K1; last (intros ???; by simplify_eq).
                  destruct!/=. rewrite bool_decide_eq_false_2; first done.
                  intros ?. simplify_eq.
                  set_unfold. simplify_eq.
            - iIntros "(?&?&?&?)". wp_pures.
              iMod ("Hclose" with "[-]").
              2: iExists _; iModIntro ; iPureIntro ; right ; naive_solver.
              iNext. rewrite /inv.
              assert ((tries' ≠ 0)%nat). 1: intros -> ; naive_solver.
              replace (Z.of_nat tries' - 1)%Z with (Z.of_nat (tries' - 1)). 2: lia.
              iFrame "Hlt".
              iFrame.
              repeat iSplit.
              1: iPureIntro ; lia.
              1: iPureIntro ; done.
              1: iPureIntro ; done.
              1: iPureIntro ; done.
              1: iPureIntro ; done.
              iSplitL "Herr".
              1: { iApply (ec_weaken with "[$]").
                   split; first apply INR_div_pos.
                   rewrite !Rdiv_def.
                   apply Rmult_le_compat_r.
                   - rewrite -Rdiv_1_l.
                     apply Rdiv_INR_ge_0.
                   - apply le_INR. lia. 
              }
              iSplitL "Herr'".
              1: { iApply (ec_weaken with "[$]").
                   split; first apply INR_div_pos.
                   rewrite !Rdiv_def.
                   apply Rmult_le_compat_r.
                   - rewrite -Rdiv_1_l.
                     apply Rdiv_INR_ge_0.
                   - apply le_INR. lia. 
              }
              iSplit.
              1: iPureIntro ; lia.
              iLeft. iFrame.
          }
          (* [guess] has not been queried before (the interesting part: pay to avoid) *)
          pose proof (Z_div_mod_eq_full guess (tag_range + 1)) as guess_part. rewrite guess_part.
          set (guess_rem := (guess `mod` (tag_range + 1))%Z).
          set (guess_quot := ((tag_range + 1) * guess `div` (tag_range + 1))%Z).
          fold guess_rem guess_quot in guess_part.

          assert (tries' ≠ 0).
          { intros ?. simplify_eq. }
          (* We can update the urns from s' to s'' and ensure that [ guess_rem ∉ s'' ]. *)
          (* That assumption allows us to update the hash function map [m] such that TODO *)
          (* [ m[guess] := z ] for some [ z : fin (S val_size) ], and the two *)
          (* disjointness conditions are maintained, i.e., *)
          (* [ ∀ x ∈ s'', n1 * (tag_range+1) + x ∉ dom m ] *)
          (* in particular, [ guess ∉ dom m ] since [ guess = guess_quot + guess_rem ] *)

          iAssert (pupd ∅ ∅ (∃s'', ⌜ s'' ⊆ s' ⌝ ∗ ⌜ s''≠∅⌝ ∗
                                   l ↪ urn_unif s'' ∗
                                   l' ↪ urn_unif s'' ∗
                                   ⌜guess_rem ∉ s''⌝%Z ∗
                                   ⌜size s'<=size s''+1⌝ ∗
                                   ↯ ((tries'-1)%nat/size s'') ∗
                                   ↯ ((tries'-1)%nat/size s'')
                  ))%I with "[Hurn Herr Hurn' Herr']" as ">H_l".
          { destruct (decide (guess `mod` (tag_range + 1) ∈ s')%Z); last first.
           - iModIntro.
             iFrame.
             repeat iSplit; try done.
             + iPureIntro; lia.
             + iSplitL "Herr".
               {
               iApply (ec_weaken with "[$]").
               split.
               * apply INR_div_pos.
               * rewrite !Rdiv_def.
                 apply Rmult_le_compat_r.
                 -- rewrite -Rdiv_1_l. apply Rdiv_INR_ge_0.
                 -- apply le_INR. lia.
               }
               {
               iApply (ec_weaken with "[$]").
               split.
               * apply INR_div_pos.
               * rewrite !Rdiv_def.
                 apply Rmult_le_compat_r.
                 -- rewrite -Rdiv_1_l. apply Rdiv_INR_ge_0.
                 -- apply le_INR. lia.
               }
           - assert (0<= (tries'-1)%nat/(size s' -1)%nat)%R as err_ineq.
             { apply INR_div_pos. }
             iAssert (⌜2<=size s'⌝)%I as "%".
             { destruct (size s') as [|[|]]eqn:Hcontra; last (iPureIntro; lia).
               - apply size_empty_inv in Hcontra.
                 by rewrite leibniz_equiv_iff in Hcontra.
               - iDestruct (ec_contradict with "[$]") as "[]".
                 simpl.
                 rewrite Rdiv_1_r.
                 replace 1%R with (INR 1) by done.
                 apply le_INR. lia.
             }
             iMod (pupd_partial_resolve_urn _ _ (λ x, if bool_decide (x=({[guess_rem]} : gset _)) then nnreal_one else mknonnegreal _ err_ineq) _ _ (({[guess_rem]} ::(s'∖{[guess_rem]}) ::[]): list (gset _)) with "[$Herr] [$Hurn]")%Z as "H'".
             + done.
             + simpl.
               rewrite union_empty_r_L.
               rewrite -union_difference_L; first done.
               set_solver.
             + repeat setoid_rewrite NoDup_cons.
               repeat split; last by apply NoDup_nil.
               -- set_unfold.
                  intros ?. destruct!/=. set_solver.
               -- set_solver.
             + set_unfold.
               intros ?.
               destruct!/=.
               rename select (_=_∖_) into Hcontra.
               apply (f_equal size) in Hcontra.
               rewrite size_empty size_difference in Hcontra; last set_solver.
               rewrite size_singleton in Hcontra. lia.
             + intros.
               set_unfold.
               destruct!/=; set_solver.
             + rewrite SeriesC_list; last first.
               { repeat setoid_rewrite NoDup_cons.
                 repeat split; last by apply NoDup_nil.
                 - set_unfold.
                   intros ?. destruct!/=. set_solver.
                 - set_solver. }
               Local Opaque size.
               simpl.
               rewrite bool_decide_eq_true_2; last done.
               rewrite Rmult_1_l size_singleton.
               rewrite bool_decide_eq_false_2; last set_solver.
               rewrite Rplus_0_r.
               simpl.
               rewrite size_difference; last set_solver.

               (* replace (_-_+_) with tries' by lia. *)
               rewrite !Rdiv_def.
               apply Rmult_le_compat_r.
               * rewrite -Rdiv_1_l.
                 apply Rdiv_INR_ge_0.
               * rewrite size_singleton.
                 (* rewrite plus_INR. *)
                 simpl.
                 rewrite Rmult_assoc.
                 rewrite (Rmult_comm (/ _)%R).
                 rewrite minus_INR. 2: lia.
                 assert ((size s' - 1)%nat */(size s' -1)%nat=1)%R as -> ; simpl ; last lra.
                 rewrite -Rdiv_def.
                 rewrite Rdiv_diag; first done.
                 rewrite minus_INR; last lia.
                 simpl.
                 assert (INR (size s') ≠ 1)%R; last lra.
                 replace 1%R with (INR 1) by done.
                 apply not_INR. lia.
             + eexists (Rmax _ _).
               intros.
               case_bool_decide.
               -- apply Rmax_l.
               -- apply Rmax_r.
             +
               iDestruct "H'" as "(%&Herr&Hurn &%h3)".
               set_unfold in h3.
               destruct!/=.
               * rewrite bool_decide_eq_true_2; last done.
                 by iDestruct (ec_contradict with "[$]") as "[]".
               * rewrite bool_decide_eq_false_2; last set_solver.
{
                 iMod (pupd_partial_resolve_urn _ _ (λ x, if bool_decide (x=({[guess_rem]} : gset _)) then nnreal_one else mknonnegreal _ err_ineq) _ _ (({[guess_rem]} ::(s'∖{[guess_rem]}) ::[]): list (gset _)) with "[$Herr'] [$Hurn']")%Z as "H'".

             + done.
             + simpl.
               rewrite union_empty_r_L.
               rewrite -union_difference_L; first done.
               set_solver.
             + repeat setoid_rewrite NoDup_cons.
               repeat split; last by apply NoDup_nil.
               -- set_unfold.
                  intros ?. destruct!/=. set_solver.
               -- set_solver.
             + set_unfold.
               intros ?.
               destruct!/=.
               rename select (_=_∖_) into Hcontra.
               apply (f_equal size) in Hcontra.
               rewrite size_empty size_difference in Hcontra; last set_solver.
               rewrite size_singleton in Hcontra. lia.
             + intros.
               set_unfold.
               destruct!/=; set_solver.
             + rewrite SeriesC_list; last first.
               { repeat setoid_rewrite NoDup_cons.
                 repeat split; last by apply NoDup_nil.
                 - set_unfold.
                   intros ?. destruct!/=. set_solver.
                 - set_solver. }
               Local Opaque size.
               simpl.
               rewrite bool_decide_eq_true_2; last done.
               rewrite Rmult_1_l size_singleton.
               rewrite bool_decide_eq_false_2; last set_solver.
               rewrite Rplus_0_r.
               simpl.
               rewrite size_difference; last set_solver.

               (* replace (_-_+_) with tries' by lia. *)
               rewrite !Rdiv_def.
               apply Rmult_le_compat_r.
               * rewrite -Rdiv_1_l.
                 apply Rdiv_INR_ge_0.
               * rewrite size_singleton.
                 (* rewrite plus_INR. *)
                 simpl.
                 rewrite Rmult_assoc.
                 rewrite (Rmult_comm (/ _)%R).
                 rewrite minus_INR. 2: lia.
                 assert ((size s' - 1)%nat */(size s' -1)%nat=1)%R as -> ; simpl ; last lra.
                 rewrite -Rdiv_def.
                 rewrite Rdiv_diag; first done.
                 rewrite minus_INR; last lia.
                 simpl.
                 assert (INR (size s') ≠ 1)%R; last lra.
                 replace 1%R with (INR 1) by done.
                 apply not_INR. lia.
             + eexists (Rmax _ _).
               intros.
               case_bool_decide.
               -- apply Rmax_l.
               -- apply Rmax_r.
             + iDestruct "H'" as "(%&Herr'&Hurn' &%h3)".
               set_unfold in h3.
               destruct!/=.
               * rewrite bool_decide_eq_true_2; last done.
                 by iDestruct (ec_contradict with "[$]") as "[]".
               * rewrite bool_decide_eq_false_2 ; last set_solver.
                 iFrame.
                 simpl.
                 iModIntro.
                 repeat iSplit; try iPureIntro.
                 -- set_solver.
                 -- intros Hcontra.
                    apply (f_equal size) in Hcontra.
                    rewrite size_empty size_difference in Hcontra; last set_solver.
                    rewrite size_singleton in Hcontra. lia.
                 -- set_solver.
                 -- rewrite size_difference; last set_solver.
                    rewrite size_singleton. lia.
                 -- iSplitL "Herr".
                    ++ iApply (ec_eq with "[$]").
                       simpl. rewrite size_difference; last set_solver.
                       by rewrite size_singleton.
                    ++ iApply (ec_eq with "[$]").
                       simpl. rewrite size_difference; last set_solver.
                       by rewrite size_singleton.
          }
          }
          iDestruct "H_l" as "(%&%&%&H_l&H_l'&%&%&Herr&Herr')".

          iMod (ec_zero) as "Hzero".
          wp_apply (wp_insert_new _ _ _ _ _ _
                      (λ x, nnreal_zero)%R
                      (l↪ _ ∗ l' ↪ _ ∗ b ↪ _) with "[$Hf $H_l $H_l' $Hb Hzero]").
          1: done.
          1: done.
          1: { right. apply SeriesC_0. simpl. intros. lra. }
          1: { iFrame.
               iModIntro.
               iApply big_sepS_intro.
               iModIntro.
               iIntros (?) "%Hlookup'".
               iIntros "[Hl [Hl' Hb]]".

               rewrite rupd_unseal/rupd_def.
               iIntros  (?) "[? Hu]". iSplit; last iFrame.
               iDestruct (ghost_map_lookup with "Hu [$Hb]") as "%Hlookup_b".
               iDestruct (ghost_map_lookup with "Hu [$Hl]") as "%Hlookup_l".
               iDestruct (ghost_map_lookup with "Hu [$Hl']") as "%Hlookup_l'".
               iPureIntro.
               intros.
               exists false. split => //.
               eapply urns_f_distr_lookup in Hlookup_l ; last done.
               2:{ simpl. set_solver. }
               eapply urns_f_distr_lookup in Hlookup_l' ; last done.
               2:{ simpl. set_solver. }
               eapply urns_f_distr_lookup in Hlookup_b ; last done.
               2:{ simpl. set_solver. }
               destruct Hlookup_l as (?&Hsome_l&Hin).
               destruct Hlookup_l' as (?&Hsome_l'&Hin_l').
               destruct Hlookup_b as (?&Hsome_b&Hin').
               simpl.
               rewrite !dom_insert in Hlookup'.
               set_unfold in Hlookup'.
               rewrite elem_of_dom in Hlookup'.
               destruct Hlookup' as [->|[->|[]]].
               - simpl. rewrite Hsome_l Hsome_l' Hsome_b; simpl.
                 rewrite bool_decide_eq_false_2; first done.
                 rewrite /guess_quot.
                 rewrite (Z.mul_comm _ (_+_)%Z).
                 intros Hcontra.
                 simplify_eq.
                 apply Zdiv_mod_unique in Hcontra; last first. 
                 + apply Zabs_ind; intros; try lia.
                   rewrite /guess_rem.
                   split; apply Z_mod_lt; lia.
                 + apply Zabs_ind; intros; try lia.
                   simpl in Hin'.
                   set_unfold in Hin'.
                   destruct!/=.
                   * replace (_+_)%Z with x2 by lia.
                     unshelve epose proof Hrange x2 _; last lia.
                     set_solver.
                   * replace (_+_)%Z with x1 by lia.
                     unshelve epose proof Hrange x1 _; last lia.
                     set_solver.
                 + rename select (guess_rem∉_) into Hcontra'.
                   apply Hcontra'.
                   destruct Hcontra as [Hcontra1 Hcontra2].
                   destruct!/=.
                   set_unfold in Hin'.
                   destruct!/=.
                   * rewrite -Hcontra2. by replace (_+_)%Z with x2 by lia.
                   * rewrite -Hcontra2. by replace (_+_)%Z with x1 by lia.
               - simpl. rewrite Hsome_l. simpl.
                 rewrite bool_decide_eq_false_2; first done.
                 rewrite /guess_quot.
                 rewrite (Z.mul_comm _ (_+_)%Z).
                 intros Hcontra.
                 simplify_eq.
                 apply Zdiv_mod_unique in Hcontra; last first. 
                 + apply Zabs_ind; intros; try lia.
                   rewrite /guess_rem.
                   split; apply Z_mod_lt; lia.
                 + apply Zabs_ind; intros; try lia.
                   unshelve epose proof Hrange x1 _; last lia.
                   set_solver.
                 + destruct!/=.
               - rename select (kmap _ _ !! _ = _) into K1.
                 apply lookup_kmap_Some in K1; last (intros ???; by simplify_eq).
                 destruct!/=. rewrite bool_decide_eq_false_2; first done.
                 rewrite -guess_part.
                 intros ?.  simplify_eq.
                 rename select (_∉dom _) into Hcontra.
                 apply Hcontra.
                 rewrite elem_of_dom. eexists _. naive_solver.
               
          }
          rewrite -guess_part.
          iIntros (v0) "[Hf [(Hl&Hl'&Hb) _]]".
          wp_pures.
          iMod ("Hclose" with "[-]"); last first.
          1:{ iModIntro. iExists _. iRight. iSplit; first done. by iExists _. }
          iNext.
          iExists _, (<[guess:=fin_to_nat v0]> m), _, _.
          replace (Z.of_nat _ -1)%Z with (Z.of_nat (tries' - 1)) by lia.
          iFrame "Hl Hl' Herr Herr' Hlt".
          setoid_rewrite kmap_insert; last (intros ???; simplify_eq; lia).
          rewrite (insert_insert _ n1_T1).
          case_match; first done. 
          rewrite (insert_insert _ n1_b_n2_T2 guess).
          case_match; first done. 
          iFrame "Hf".
          repeat iSplit; last (iLeft; iFrame); iPureIntro; try lia.
          1:  { intros.
                rewrite dom_insert.
                intros Hcontra.
                set_unfold in Hcontra.
                destruct!/=; last naive_solver.
                rewrite guess_part in Hcontra.
                rewrite /guess_quot in Hcontra.
                rewrite (Z.mul_comm _ (_+_)%Z) in Hcontra.
                 apply Zdiv_mod_unique in Hcontra; last first. 
                 + apply Zabs_ind; intros; try lia.
                   rewrite /guess_rem.
                   split; apply Z_mod_lt; lia.
                 + apply Zabs_ind; intros; try lia.
                   unshelve epose proof Hrange x0 _; last lia.
                   set_solver.
                 + destruct!/=.
          }
          1:  { intros.
                rewrite dom_insert.
                intros Hcontra.
                set_unfold in Hcontra.
                destruct!/=; last naive_solver.
                rewrite guess_part in Hcontra.
                rewrite /guess_quot in Hcontra.
                rewrite (Z.mul_comm _ (_+_)%Z) in Hcontra.
                 apply Zdiv_mod_unique in Hcontra; last first. 
                 + apply Zabs_ind; intros; try lia.
                   rewrite /guess_rem.
                   split; apply Z_mod_lt; lia.
                 + apply Zabs_ind; intros; try lia.
                   unshelve epose proof Hrange x0 _; last lia.
                   set_solver.
                 + destruct!/=.
          }
          1:{ intros.
              apply Hrange. set_solver.
          }
          done.
          
        (** * End of first case of disjunction *)
        +
          (** * Start of second case of disjunction *)
          iDestruct "Hor" as "(Htoken & (%b_resolved & %Hbineq & Hb))".
          destruct (decide (guess ∈ (( (dom m)):gset _))) as [Hlookup|].
          { (** it has been queried before *)
            rewrite elem_of_dom in Hlookup.
            destruct Hlookup as [m_guess H_m_guess].
            wp_apply (wp_hashfun_prev _ _ _ _ _ _ guess (l ↪ _ ∗ l' ↪ _ ∗ b ↪ _) with "[$Hurn $Hf $Hurn' $Hb]").
            - done.
            - simplify_map_eq.
              erewrite lookup_kmap_Some; first naive_solver.
              intros ???. by simplify_eq.
            - iSplit.
              + iModIntro.
                iIntros "(?&?&?)".
                rewrite rupd_unseal/rupd_def.
                iIntros (?) "[? Hu]". iSplit; last iFrame.
                iDestruct (ghost_map_lookup with "Hu [$]") as "%Hlookup".
                iPureIntro.
                intros. simpl. case_bool_decide; naive_solver.
              + iModIntro.
                iApply big_sepS_intro.
                iModIntro.
                setoid_rewrite elem_of_difference.
                iIntros (?) "[%Hlookup' %]".
                iIntros "(Hl&Hl'&Hb)".
                rewrite rupd_unseal/rupd_def.
                iIntros  (?) "[? Hu]". iSplit; last iFrame.
                iDestruct (ghost_map_lookup with "Hu [$Hl]") as "%Hlookup_l".
                iDestruct (ghost_map_lookup with "Hu [$Hl']") as "%Hlookup_l'".
                iDestruct (ghost_map_lookup with "Hu [$Hb]") as "%Hlookup_b".
                iPureIntro.
                intros.
                eapply urns_f_distr_lookup in Hlookup_l; last done; last done.
                eapply urns_f_distr_lookup in Hlookup_l'; last done; last done.
                eapply urns_f_distr_lookup in Hlookup_b; last done; last done.
                destruct Hlookup_l as (?&Hsome_l&Hin_l).
                destruct Hlookup_l' as (?&Hsome_l'&Hin_l').
                destruct Hlookup_b as (?&Hsome_b&Hin_b).
                eexists _; split; last done.
                simpl.
                rewrite elem_of_dom in Hlookup'.
                destruct Hlookup' as [? Hlookup'].
                rewrite lookup_insert_Some in Hlookup'.
                rewrite lookup_insert_Some in Hlookup'.
                destruct!/=.
                * rewrite Hsome_l Hsome_l' Hsome_b/=. rewrite bool_decide_eq_false_2 ; first done.
                  (* guess ∈ dom m *)
                  (* both x1 and x2 are in s' *)
                  (* but that contradiction Hdisjoint2. *)
                  intros ?. simplify_eq.
                  set_unfold in Hin_b. subst.
                  destruct b_resolved as [|[|]]; last lia.
                  -- eapply Hdisjoint2.
                     1: apply Hin_l'.
                     rewrite elem_of_dom.
                     eexists.
                     erewrite <- H_m_guess.
                     repeat f_equal. lia.
                  -- eapply Hdisjoint2.
                     1: apply Hin_l.
                     rewrite elem_of_dom.
                     eexists.
                     erewrite <- H_m_guess.
                     repeat f_equal. lia.
                * rewrite Hsome_l.
                  simpl.
                  rewrite bool_decide_eq_false_2 ; first done.
                  intros ?. simplify_eq.
                  eapply Hdisjoint1.
                     1: apply Hin_l.
                     rewrite elem_of_dom.
                     eexists.
                     erewrite <- H_m_guess.
                     repeat f_equal.
                * simpl.
                  rename select (kmap _ _ !! _ = _) into K1.
                  apply lookup_kmap_Some in K1; last (intros ???; by simplify_eq).
                  destruct!/=. rewrite bool_decide_eq_false_2; first done.
                  intros ?. simplify_eq.
                  set_unfold. simplify_eq.
            - iIntros "(?&?&?&?)". wp_pures.
              iMod ("Hclose" with "[-]").
              2: iExists _; iModIntro ; iPureIntro ; right ; naive_solver.
              iNext. rewrite /inv.
              assert ((tries' ≠ 0)%nat). 1: intros -> ; naive_solver.
              replace (Z.of_nat tries' - 1)%Z with (Z.of_nat (tries' - 1)). 2: lia.
              iFrame "Hlt".
              iFrame.
              repeat iSplit.
              1: iPureIntro ; lia.
              1: iPureIntro ; done.
              1: iPureIntro ; done.
              1: iPureIntro ; done.
              1: iPureIntro ; done.
              iSplitL "Herr".
              1: { iApply (ec_weaken with "[$]").
                   split; first apply INR_div_pos.
                   rewrite !Rdiv_def.
                   apply Rmult_le_compat_r.
                   - rewrite -Rdiv_1_l.
                     apply Rdiv_INR_ge_0.
                   - apply le_INR. lia. 
              }
              iSplitL "Herr'".
              1: { iApply (ec_weaken with "[$]").
                   split; first apply INR_div_pos.
                   rewrite !Rdiv_def.
                   apply Rmult_le_compat_r.
                   - rewrite -Rdiv_1_l.
                     apply Rdiv_INR_ge_0.
                   - apply le_INR. lia. 
              }
              iSplit.
              1: iPureIntro ; lia.
              iRight. by iFrame.
          }
          (* [guess] has not been queried before (the interesting part: pay to avoid) *)
          pose proof (Z_div_mod_eq_full guess (tag_range + 1)) as guess_part. rewrite guess_part.
          set (guess_rem := (guess `mod` (tag_range + 1))%Z).
          set (guess_quot := ((tag_range + 1) * guess `div` (tag_range + 1))%Z).
          fold guess_rem guess_quot in guess_part.

          assert (tries' ≠ 0).
          { intros ?. simplify_eq. }
          (* We can update the urns from s' to s'' and ensure that [ guess_rem ∉ s'' ]. *)
          (* That assumption allows us to update the hash function map [m] such that TODO *)
          (* [ m[guess] := z ] for some [ z : fin (S val_size) ], and the two *)
          (* disjointness conditions are maintained, i.e., *)
          (* [ ∀ x ∈ s'', n1 * (tag_range+1) + x ∉ dom m ] *)
          (* in particular, [ guess ∉ dom m ] since [ guess = guess_quot + guess_rem ] *)

          iAssert (pupd ∅ ∅ (∃s'', ⌜ s'' ⊆ s' ⌝ ∗ ⌜ s''≠∅⌝ ∗
                                   l ↪ urn_unif s'' ∗
                                   l' ↪ urn_unif s'' ∗
                                   ⌜guess_rem ∉ s''⌝%Z ∗
                                   ⌜size s'<=size s''+1⌝ ∗
                                   ↯ ((tries'-1)%nat/size s'') ∗
                                   ↯ ((tries'-1)%nat/size s'')
                  ))%I with "[Hurn Herr Hurn' Herr']" as ">H_l".
          { destruct (decide (guess `mod` (tag_range + 1) ∈ s')%Z); last first.
           - iModIntro.
             iFrame.
             repeat iSplit; try done.
             + iPureIntro; lia.
             + iSplitL "Herr".
               {
               iApply (ec_weaken with "[$]").
               split.
               * apply INR_div_pos.
               * rewrite !Rdiv_def.
                 apply Rmult_le_compat_r.
                 -- rewrite -Rdiv_1_l. apply Rdiv_INR_ge_0.
                 -- apply le_INR. lia.
               }
               {
               iApply (ec_weaken with "[$]").
               split.
               * apply INR_div_pos.
               * rewrite !Rdiv_def.
                 apply Rmult_le_compat_r.
                 -- rewrite -Rdiv_1_l. apply Rdiv_INR_ge_0.
                 -- apply le_INR. lia.
               }
           - assert (0<= (tries'-1)%nat/(size s' -1)%nat)%R as err_ineq.
             { apply INR_div_pos. }
             iAssert (⌜2<=size s'⌝)%I as "%".
             { destruct (size s') as [|[|]]eqn:Hcontra; last (iPureIntro; lia).
               - apply size_empty_inv in Hcontra.
                 by rewrite leibniz_equiv_iff in Hcontra.
               - iDestruct (ec_contradict with "[$]") as "[]".
                 simpl.
                 rewrite Rdiv_1_r.
                 replace 1%R with (INR 1) by done.
                 apply le_INR. lia.
             }
             iMod (pupd_partial_resolve_urn _ _ (λ x, if bool_decide (x=({[guess_rem]} : gset _)) then nnreal_one else mknonnegreal _ err_ineq) _ _ (({[guess_rem]} ::(s'∖{[guess_rem]}) ::[]): list (gset _)) with "[$Herr] [$Hurn]")%Z as "H'".
             + done.
             + simpl.
               rewrite union_empty_r_L.
               rewrite -union_difference_L; first done.
               set_solver.
             + repeat setoid_rewrite NoDup_cons.
               repeat split; last by apply NoDup_nil.
               -- set_unfold.
                  intros ?. destruct!/=. set_solver.
               -- set_solver.
             + set_unfold.
               intros ?.
               destruct!/=.
               rename select (_=_∖_) into Hcontra.
               apply (f_equal size) in Hcontra.
               rewrite size_empty size_difference in Hcontra; last set_solver.
               rewrite size_singleton in Hcontra. lia.
             + intros.
               set_unfold.
               destruct!/=; set_solver.
             + rewrite SeriesC_list; last first.
               { repeat setoid_rewrite NoDup_cons.
                 repeat split; last by apply NoDup_nil.
                 - set_unfold.
                   intros ?. destruct!/=. set_solver.
                 - set_solver. }
               Local Opaque size.
               simpl.
               rewrite bool_decide_eq_true_2; last done.
               rewrite Rmult_1_l size_singleton.
               rewrite bool_decide_eq_false_2; last set_solver.
               rewrite Rplus_0_r.
               simpl.
               rewrite size_difference; last set_solver.

               (* replace (_-_+_) with tries' by lia. *)
               rewrite !Rdiv_def.
               apply Rmult_le_compat_r.
               * rewrite -Rdiv_1_l.
                 apply Rdiv_INR_ge_0.
               * rewrite size_singleton.
                 (* rewrite plus_INR. *)
                 simpl.
                 rewrite Rmult_assoc.
                 rewrite (Rmult_comm (/ _)%R).
                 rewrite minus_INR. 2: lia.
                 assert ((size s' - 1)%nat */(size s' -1)%nat=1)%R as -> ; simpl ; last lra.
                 rewrite -Rdiv_def.
                 rewrite Rdiv_diag; first done.
                 rewrite minus_INR; last lia.
                 simpl.
                 assert (INR (size s') ≠ 1)%R; last lra.
                 replace 1%R with (INR 1) by done.
                 apply not_INR. lia.
             + eexists (Rmax _ _).
               intros.
               case_bool_decide.
               -- apply Rmax_l.
               -- apply Rmax_r.
             +
               iDestruct "H'" as "(%&Herr&Hurn &%h3)".
               set_unfold in h3.
               destruct!/=.
               * rewrite bool_decide_eq_true_2; last done.
                 by iDestruct (ec_contradict with "[$]") as "[]".
               * rewrite bool_decide_eq_false_2; last set_solver.
{
                 iMod (pupd_partial_resolve_urn _ _ (λ x, if bool_decide (x=({[guess_rem]} : gset _)) then nnreal_one else mknonnegreal _ err_ineq) _ _ (({[guess_rem]} ::(s'∖{[guess_rem]}) ::[]): list (gset _)) with "[$Herr'] [$Hurn']")%Z as "H'".

             + done.
             + simpl.
               rewrite union_empty_r_L.
               rewrite -union_difference_L; first done.
               set_solver.
             + repeat setoid_rewrite NoDup_cons.
               repeat split; last by apply NoDup_nil.
               -- set_unfold.
                  intros ?. destruct!/=. set_solver.
               -- set_solver.
             + set_unfold.
               intros ?.
               destruct!/=.
               rename select (_=_∖_) into Hcontra.
               apply (f_equal size) in Hcontra.
               rewrite size_empty size_difference in Hcontra; last set_solver.
               rewrite size_singleton in Hcontra. lia.
             + intros.
               set_unfold.
               destruct!/=; set_solver.
             + rewrite SeriesC_list; last first.
               { repeat setoid_rewrite NoDup_cons.
                 repeat split; last by apply NoDup_nil.
                 - set_unfold.
                   intros ?. destruct!/=. set_solver.
                 - set_solver. }
               Local Opaque size.
               simpl.
               rewrite bool_decide_eq_true_2; last done.
               rewrite Rmult_1_l size_singleton.
               rewrite bool_decide_eq_false_2; last set_solver.
               rewrite Rplus_0_r.
               simpl.
               rewrite size_difference; last set_solver.

               (* replace (_-_+_) with tries' by lia. *)
               rewrite !Rdiv_def.
               apply Rmult_le_compat_r.
               * rewrite -Rdiv_1_l.
                 apply Rdiv_INR_ge_0.
               * rewrite size_singleton.
                 (* rewrite plus_INR. *)
                 simpl.
                 rewrite Rmult_assoc.
                 rewrite (Rmult_comm (/ _)%R).
                 rewrite minus_INR. 2: lia.
                 assert ((size s' - 1)%nat */(size s' -1)%nat=1)%R as -> ; simpl ; last lra.
                 rewrite -Rdiv_def.
                 rewrite Rdiv_diag; first done.
                 rewrite minus_INR; last lia.
                 simpl.
                 assert (INR (size s') ≠ 1)%R; last lra.
                 replace 1%R with (INR 1) by done.
                 apply not_INR. lia.
             + eexists (Rmax _ _).
               intros.
               case_bool_decide.
               -- apply Rmax_l.
               -- apply Rmax_r.
             + iDestruct "H'" as "(%&Herr'&Hurn' &%h3)".
               set_unfold in h3.
               destruct!/=.
               * rewrite bool_decide_eq_true_2; last done.
                 by iDestruct (ec_contradict with "[$]") as "[]".
               * rewrite bool_decide_eq_false_2 ; last set_solver.
                 iFrame.
                 simpl.
                 iModIntro.
                 repeat iSplit; try iPureIntro.
                 -- set_solver.
                 -- intros Hcontra.
                    apply (f_equal size) in Hcontra.
                    rewrite size_empty size_difference in Hcontra; last set_solver.
                    rewrite size_singleton in Hcontra. lia.
                 -- set_solver.
                 -- rewrite size_difference; last set_solver.
                    rewrite size_singleton. lia.
                 -- iSplitL "Herr".
                    ++ iApply (ec_eq with "[$]").
                       simpl. rewrite size_difference; last set_solver.
                       by rewrite size_singleton.
                    ++ iApply (ec_eq with "[$]").
                       simpl. rewrite size_difference; last set_solver.
                       by rewrite size_singleton.
          }
          }
          iDestruct "H_l" as "(%&%&%&H_l&H_l'&%&%&Herr&Herr')".

          iMod (ec_zero) as "Hzero".
          wp_apply (wp_insert_new _ _ _ _ _ _
                      (λ x, nnreal_zero)%R
                      (l↪ _ ∗ l' ↪ _ ∗ b ↪ _) with "[$Hf $H_l $H_l' $Hb Hzero]").
          1: done.
          1: done.
          1: { right. apply SeriesC_0. simpl. intros. lra. }
          1: { iFrame.
               iModIntro.
               iApply big_sepS_intro.
               iModIntro.
               iIntros (?) "%Hlookup'".
               iIntros "[Hl [Hl' Hb]]".

               rewrite rupd_unseal/rupd_def.
               iIntros  (?) "[? Hu]". iSplit; last iFrame.
               iDestruct (ghost_map_lookup with "Hu [$Hb]") as "%Hlookup_b".
               iDestruct (ghost_map_lookup with "Hu [$Hl]") as "%Hlookup_l".
               iDestruct (ghost_map_lookup with "Hu [$Hl']") as "%Hlookup_l'".
               iPureIntro.
               intros.
               exists false. split => //.
               eapply urns_f_distr_lookup in Hlookup_l ; last done.
               2:{ simpl. set_solver. }
               eapply urns_f_distr_lookup in Hlookup_l' ; last done.
               2:{ simpl. set_solver. }
               eapply urns_f_distr_lookup in Hlookup_b ; last done.
               2:{ simpl. set_solver. }
               destruct Hlookup_l as (?&Hsome_l&Hin).
               destruct Hlookup_l' as (?&Hsome_l'&Hin_l').
               destruct Hlookup_b as (?&Hsome_b&Hin').
               simpl.
               rewrite !dom_insert in Hlookup'.
               set_unfold in Hlookup'.
               rewrite elem_of_dom in Hlookup'.
               destruct Hlookup' as [->|[->|[]]].
               - simpl. rewrite Hsome_l Hsome_l' Hsome_b; simpl.
                 rewrite bool_decide_eq_false_2; first done.
                 rewrite /guess_quot.
                 rewrite (Z.mul_comm _ (_+_)%Z).
                 intros Hcontra.
                 simplify_eq.
                 apply Zdiv_mod_unique in Hcontra; last first. 
                 + apply Zabs_ind; intros; try lia.
                   rewrite /guess_rem.
                   split; apply Z_mod_lt; lia.
                 + apply Zabs_ind; intros; try lia.
                   simpl in Hin'.
                   set_unfold in Hin'.
                   rewrite Hin'.
                   destruct b_resolved as [| [|]]; last lia.
                   * replace (_+_)%Z with x2 by lia.
                     unshelve epose proof Hrange x2 _; last lia.
                     set_solver.
                   * replace (_+_)%Z with x1 by lia.
                     unshelve epose proof Hrange x1 _; last lia.
                     set_solver.
                 + rename select (guess_rem∉_) into Hcontra'.
                   apply Hcontra'.
                   destruct Hcontra as [Hcontra1 Hcontra2].
                   destruct!/=.
                   set_unfold in Hin'.
                   destruct!/=.
                   destruct b_resolved as [| [|]]; last lia.
                   * rewrite -Hcontra2. by replace (_+_)%Z with x2 by lia.
                   * rewrite -Hcontra2. by replace (_+_)%Z with x1 by lia.
               - simpl. rewrite Hsome_l. simpl.
                 rewrite bool_decide_eq_false_2; first done.
                 rewrite /guess_quot.
                 rewrite (Z.mul_comm _ (_+_)%Z).
                 intros Hcontra.
                 simplify_eq.
                 apply Zdiv_mod_unique in Hcontra; last first. 
                 + apply Zabs_ind; intros; try lia.
                   rewrite /guess_rem.
                   split; apply Z_mod_lt; lia.
                 + apply Zabs_ind; intros; try lia.
                   unshelve epose proof Hrange x1 _; last lia.
                   set_solver.
                 + destruct!/=.
               - rename select (kmap _ _ !! _ = _) into K1.
                 apply lookup_kmap_Some in K1; last (intros ???; by simplify_eq).
                 destruct!/=. rewrite bool_decide_eq_false_2; first done.
                 rewrite -guess_part.
                 intros ?.  simplify_eq.
                 rename select (_∉dom _) into Hcontra.
                 apply Hcontra.
                 rewrite elem_of_dom. eexists _. naive_solver.
               
          }
          rewrite -guess_part.
          iIntros (v0) "[Hf [(Hl&Hl'&Hb) _]]".
          wp_pures.
          iMod ("Hclose" with "[-]"); last first.
          1:{ iModIntro. iExists _. iRight. iSplit; first done. by iExists _. }
          iNext.
          iExists _, (<[guess:=fin_to_nat v0]> m), _, _.
          replace (Z.of_nat _ -1)%Z with (Z.of_nat (tries' - 1)) by lia.
          iFrame "Hl Hl' Herr Herr' Hlt".
          setoid_rewrite kmap_insert; last (intros ???; simplify_eq; lia).
          rewrite (insert_insert _ n1_T1).
          case_match; first done. 
          rewrite (insert_insert _ n1_b_n2_T2 guess).
          case_match; first done. 
          iFrame "Hf".
          repeat iSplit; last (iRight; by iFrame); iPureIntro; try lia.
          1:  { intros.
                rewrite dom_insert.
                intros Hcontra.
                set_unfold in Hcontra.
                destruct!/=; last naive_solver.
                rewrite guess_part in Hcontra.
                rewrite /guess_quot in Hcontra.
                rewrite (Z.mul_comm _ (_+_)%Z) in Hcontra.
                 apply Zdiv_mod_unique in Hcontra; last first. 
                 + apply Zabs_ind; intros; try lia.
                   rewrite /guess_rem.
                   split; apply Z_mod_lt; lia.
                 + apply Zabs_ind; intros; try lia.
                   unshelve epose proof Hrange x0 _; last lia.
                   set_solver.
                 + destruct!/=.
          }
          1:  { intros.
                rewrite dom_insert.
                intros Hcontra.
                set_unfold in Hcontra.
                destruct!/=; last naive_solver.
                rewrite guess_part in Hcontra.
                rewrite /guess_quot in Hcontra.
                rewrite (Z.mul_comm _ (_+_)%Z) in Hcontra.
                 apply Zdiv_mod_unique in Hcontra; last first. 
                 + apply Zabs_ind; intros; try lia.
                   rewrite /guess_rem.
                   split; apply Z_mod_lt; lia.
                 + apply Zabs_ind; intros; try lia.
                   unshelve epose proof Hrange x0 _; last lia.
                   set_solver.
                 + destruct!/=.
          }
          1:{ intros.
              apply Hrange. set_solver.
          }
          done.
          
        (** * End of second case of disjunction *)
         }

    iIntros "% (%guess & ->)". wp_pure. wp_pure.
    rewrite -(fill_empty (_=_)).
    iApply (pgl_wp_bind).
    wp_pures. simpl.
    iInv "Hinv" as ">(%&%&%&%&?&?&?&%&?&?&?&?&?&?&?&?&?&[[b err] | (Htoken' & ?) ])" "Hclose" ; last first.
    1: iDestruct (token_exclusive with "[$][$]") as "[]".
    iMod (pupd_resolve_urn _ _ (λ x, if bool_decide (x=guess) then nnreal_one else nnreal_zero) with "[$err][$b]") as "(%&?&Hurn&%)".
    { simpl. set_solver. }
    1: {
      rewrite size_list_to_set; last apply NoDup_fmap; [|apply Nat2Z.inj'|apply NoDup_seq].
      rewrite length_fmap length_seq.
      replace (INR 2) with 2%R by done.
      rewrite !Rdiv_def.
      apply Rmult_le_compat_r; first lra.
      trans (SeriesC (λ x, if bool_decide (x=guess) then 1 else 0)).
      - apply SeriesC_le.
        + intros.
          split; repeat case_bool_decide; simpl; lra.
        + apply ex_seriesC_singleton.
      - by rewrite SeriesC_singleton. 
      
    }
    1: exists 1 ; intros ; case_bool_decide ; simpl ; try lra.
    case_bool_decide ; first by iDestruct (ec_contradict with "[$]") as "[]".
        iApply (wp_value_promotion _ false (b↪ _) with "[Hurn]").
        * rewrite rupd_unseal/rupd_def.
          iIntros  (?) "[? Hu]". iSplit; last iFrame.
          iDestruct (ghost_map_lookup with "Hu [$]") as "%Hlookup".
          iPureIntro.
          intros.
          eapply urns_f_distr_lookup in Hlookup; last done; last done.
          destruct Hlookup as (?&Hsome&Hin).
          simpl.
          rewrite Hsome.
          simpl.
          rewrite bool_decide_eq_false_2; first naive_solver.
          set_unfold.
          destruct!/=. intros ?. simplify_eq.
        * iIntros "Hurn".
          wp_pures.
          iMod ("Hclose" with "[-HΦ]").
          { iNext.
            iFrame.
            iRight. iFrame.
            iExists (Z.to_nat x0). repeat iSplit; try done.
            - iPureIntro.
              rename select (_∈_) into H'.
              simpl in H'; set_unfold in H'.
              destruct!/=; lia.
            - rename select (_∈_) into H'.
              simpl in H'; set_unfold in H'.
              destruct!/=; simpl; iFrame.
          }
          by iApply "HΦ".


  Qed.
End prog.

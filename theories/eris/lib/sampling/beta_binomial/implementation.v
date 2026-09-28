From clutch.eris Require Import eris.
From clutch.eris.lib.sampling.bernoulli Require Import interface.
From clutch.eris.lib.sampling.beta_binomial Require Import interface beta_tapes.
From clutch.eris.lib.sampling Require Import utils.

Section Polya.
  
  Context `{!bernoulli_spec bernoulli balloc}.

   #[local] Ltac done ::= solve[
      lia |
      lra |
      nra |
      tactics.done |
      auto
     ].
  
  Section PolyaImpl.
   
    Definition sub_loc_fail : val := λ: "α" "i" "j", "α" ("i" + #1) "j".
    
    Definition sub_loc_success : val := λ: "α" "i" "j", "α" ("i" + #1) ("j" + #1).  

    Definition polya : val :=
        rec: "polya" "α" "red" "black" "n" :=
        if: "n" = #0 then #0
        else
          let: "x" := bernoulli ("α" #0 #0) "red" ("red" + "black" - #1)  in
          if: "x" = #1 
          then #1 + "polya" (sub_loc_success "α") ("red" + #1) "black" ("n" - #1)
          else "polya" (sub_loc_fail "α") "red" ("black" + #1) ("n" - #1).
    
    Definition polyalloc_row : val :=
      rec: "polyalloc_row" "red" "black" "n" :=
        if: "n" = #0 then (λ: "x", "x")
        else
          let: "α0" := balloc "red" ("red" + "black" - #1) in
          let: "α" := "polyalloc_row" "red" ("black" + #1) ("n" - #1) in
          (λ: "i",
             if: "i" = #0
             then "α0"
             else "α" ("i" - #1)
          ).
    
    Definition polyalloc : val :=
        rec: "polyalloc" "red" "black" "n" :=
        if: "n" = #0 then (λ: "x", "x")
        else
          let: "αr" := polyalloc_row "red" "black" "n" in
          let: "α" := "polyalloc" ("red" + #1) "black" ("n" - #1) in
          (λ: "i" "j",
             if: "j" = #0
             then "αr" "i"
             else "α" ("i" - #1) ("j" - #1))
    .

    Definition loc_unit : val := λ: "i" "j", #().

  End PolyaImpl.

  Section PolyaInst.
    
    Context `{!erisGS Σ}.
    Set Default Proof Using "Type*".
    
    Definition is_loc_unit (n : nat) (α : val) : iProp Σ :=
      □ (∀ (i : fin n) (j : fin (S i)), WP α #i #j [{ v, ⌜v = #()⌝ }])%I.

    Lemma loc_unit_is_unit : ∀ (n : nat), ⊢ is_loc_unit n loc_unit.
    Proof.
      iIntros (n i j).
      iModIntro.
      unfold loc_unit.
      by wp_pures.
    Qed.

    Lemma sub_loc_fail_unit : ∀ (n : nat) (α : val), is_loc_unit (S n) α -∗ WP sub_loc_fail α [{ β, is_loc_unit n β }].
    Proof.
      iIntros (n α) "#Hα".
      unfold sub_loc_fail.
      wp_pures.
      iModIntro.
      iIntros (i j).
      iModIntro.
      wp_pures.
      rewrite -(Nat2Z.inj_add _ 1) Nat.add_1_r (fin_S_inj_to_nat _ j).
      wp_apply ("Hα" $! (FS i)).
    Qed.

    Lemma sub_loc_success_unit : ∀ (n : nat) (α : val), is_loc_unit (S n) α -∗ WP sub_loc_success α [{ β, is_loc_unit n β }].
    Proof.
      iIntros (n α) "#Hα".
      unfold sub_loc_success.
      wp_pures.
      iModIntro.
      iIntros (i j).
      iModIntro.
      wp_pures.
      rewrite -!(Nat2Z.inj_add _ 1) !Nat.add_1_r.
      wp_apply ("Hα" $! (FS i) (FS j)).
    Qed.

    Lemma polya_0_b (black n : nat) (α : val) :
      (black > 0)%nat →
      [[{is_loc_unit n α}]]
        polya α #0 #black #n
      [[{RET #0; True}]].
    Proof.
      iInduction n as [|n] "IH" forall (black α).
      - iIntros "%Hb %Φ #Hα HΦ".
        unfold polya.
        wp_pures.
        by iApply "HΦ".
      - iIntros "%Hb %Φ #Hα HΦ".
        unfold polya.
        wp_pures.
        fold polya.
        rewrite Z.add_0_l.
        replace (black - 1)%Z with ((black - 1)%nat : Z) by lia.
        wp_bind (α _ _)%E.
        wp_apply tgl_wp_wand_r.
        iSplitR; first wp_apply ("Hα" $! 0%fin 0%fin).
        iIntros (?) "->".
        wp_apply (bernoulli_0 with "[$]") as "_".
        wp_pures.
        replace (S n - 1)%Z with (n : Z) by lia.
        rewrite Z.add_1_r -Nat2Z.inj_succ.
        wp_bind (sub_loc_fail α).
        wp_apply tgl_wp_wand_r.
        iSplitR; first by wp_apply sub_loc_fail_unit.
        iIntros (β) "#Hβ".
        wp_apply "IH"; done.
    Qed.

    Lemma polya_r_0 (red n : nat) (α : val):
      (red > 0)%nat →
      [[{is_loc_unit n α}]]
        polya α #red #0 #n
      [[{RET #n; True}]].
    Proof.
      iInduction n as [|n] "IH" forall (red α).
      - iIntros "%Hr %Φ #Hα HΦ".
        unfold polya.
        wp_pures.
        by iApply "HΦ".
      - iIntros "%Hr %Φ #Hα HΦ".
        unfold polya.
        wp_pures.
        fold polya.
        destruct red; first lia.
        replace (S red + 0 - 1)%Z with (red : Z) by lia.
        wp_bind (α _ _).
        wp_apply tgl_wp_wand_r.
        iSplitR; first wp_apply ("Hα" $! 0%fin 0%fin).
        iIntros (?) "->".
        wp_apply (bernoulli_1 with "[$]") as "_".
        wp_pures.
        replace (S n - 1)%Z with (n : Z) by lia.
        rewrite Z.add_1_r -Nat2Z.inj_succ.
        wp_bind (sub_loc_success α).
        wp_apply tgl_wp_wand_r.
        iSplitR; first by wp_apply sub_loc_success_unit.
        iIntros (β) "#Hβ".
        wp_apply "IH" as (_) ""; [done..|].
        wp_pures.
        rewrite Z.add_1_l -Nat2Z.inj_succ.
        iApply ("HΦ" with "[$]").
    Qed.
    
    #[local] Open Scope R.
    Lemma polya_spec (red black n : nat) (E : fin (S n) → R) (α : val) (ε : R) :
      (red + black > 0)%nat →
      (∀ k, E k >= 0) →
      ε = (SeriesC (λ (k : fin (S n)), Beta_prob red black n k * E k )%R) →
      [[{
        ↯ ε ∗
        is_loc_unit n α
      }]]
      polya α #red #black #n
      [[{
        (v : fin (S n)), RET #v; 
        ↯ (E v)
      }]].
    Proof.
      iIntros (H_red_black_gt_0 HE_nonneg Heq Φ) "[Herr #Hα] HΦ".
      destruct (decide (red = 0)%nat) as [-> | Hr_not_0].
      {
        rewrite Series_fin_first in Heq.
        subst.
        iPoseProof (ec_split with "Herr") as "[Herr _]".
        { add_hint Beta_prob_pos. real_solver. }
        { add_hint Beta_prob_pos.
          apply SeriesC_ge_0' => k. real_solver. }
        rewrite /Beta_prob Choose_n_0 !Beta_0_l.
        wp_apply polya_0_b as "_" => //.
        iApply ("HΦ" $! 0%fin with "[Herr]").
        iApply (ec_eq with "Herr") => //=.
      }
      destruct (decide (black = 0)%nat) as [-> | Hb_not_0].
      {
         (* !fin_to_nat_to_fin Choose_n_n Nat.sub_diag !Beta_0_r Rmult_1_l Rdiv_diag // Rmult_1_l *)
        rewrite Series_fin_last in Heq.
        subst.
        iPoseProof (ec_split with "Herr") as "[_ Herr]".
        { add_hint Beta_prob_pos.
          apply SeriesC_ge_0' => k. real_solver. }
        { add_hint Beta_prob_pos. real_solver. }
        wp_apply polya_r_0 as "_" => //.
        assert (n = (fin_to_nat (nat_to_fin (Nat.lt_succ_diag_r n)))) as Heqn by rewrite fin_to_nat_to_fin //.
        rewrite ->Heqn at 3.
        iApply ("HΦ" with "[Herr]").
        rewrite /Beta_prob !fin_to_nat_to_fin Choose_n_n Nat.sub_diag !Beta_0_r.
        iApply (ec_eq with "Herr") => //=.
      }
      (* It is easier to prove with E : nat → R, as induction on R can mess with the types, but still requiring E : fin (S n) → R can be interesting, to discuss *)
      rename E into E', HE_nonneg into HE'_nonneg, Heq into Heq'.
      pose E k := if Nat.lt_dec k (S n) is left pf
                  then E' (((Fin.of_nat_lt pf)))
                  else 1%R.
      assert (HE_nonneg : ∀ k : nat, E k >= 0).
      { move=>k. unfold E. real_solver. }
      iAssert (∀ v : fin (S n), ↯ (E v) -∗ Φ #v)%I with "[HΦ]" as "HΦ".
      { iIntros "%v Herr".
        unfold E.
        iApply "HΦ".
        destruct (Nat.lt_dec v (S n)); last cred_contra.
        rewrite nat_to_fin_to_nat //. }
      assert (ε = SeriesC (λ x : fin (S n), Choose n x * Beta (x + red) (n - x + black) / Beta red black * E x)) as Heq. {
        rewrite Heq'.
        apply SeriesC_ext => k.
        simpl_expr.
        pose proof (fin_to_nat_lt k).
        unfold E.
        destruct (Nat.lt_dec k (S n)); last lia.
        rewrite nat_to_fin_to_nat //. }
      clearbody E.
      clear Heq' E' HE'_nonneg.

      (* Here starts the proof *)
      iInduction n as [|n] "IH" forall (E HE_nonneg red α Hr_not_0 black Hb_not_0 ε H_red_black_gt_0 Heq Φ).
      - unfold polya. wp_pures.
        rewrite SeriesC_finite_foldr /= in Heq.
        rewrite Choose_n_0 Rmult_1_l in Heq.
        add_hint Beta_pos.
        rewrite Rdiv_diag in Heq; last real_solver.
        rewrite Rplus_0_r Rmult_1_l in Heq.
        rewrite Heq.
        iApply ("HΦ" $! 0%fin with "[$Herr]").
      - wp_rec. wp_pures.
        rewrite -Nat2Z.inj_add.
        rewrite Beta_sum_split in Heq; [|done..].
        match type of Heq with 
        | _ = (_ * ?A) + (_ * ?B) => 
          set ε2 := A;
          set ε1 := B;
          fold ε1 ε2 in Heq
        end.
        replace ((red + black)%nat - 1)%Z with ((red + black - 1)%nat : Z) by lia.
        wp_bind (α _ _).
        wp_apply tgl_wp_wand_r.
        iSplitR; first wp_apply ("Hα" $! 0%fin 0%fin).
        iIntros (?) "->".
        wp_apply (twp_bernoulli_scale _ _ ε ε1 ε2 with "Herr") as "% [[-> Herr]| [-> Herr]]".
        { lia. }
        { unfold ε1. 
          apply SeriesC_ge_0, ex_seriesC_finite => k.
          add_hint Beta_prob_pos.
          real_solver. }
        { unfold ε2. 
          apply SeriesC_ge_0, ex_seriesC_finite => k.
          add_hint Beta_prob_pos.
          real_solver. }
        { assert (INR red + INR black ≠ 0). 
          { rewrite -plus_INR. change 0 with (INR 0).
            apply not_INR.
            lia. }
          replace (S (red + black - 1))%nat with (red + black)%nat by lia.
          rewrite Heq Rplus_comm (Rmult_comm ε2 _) (Rmult_comm ε1 _) plus_INR.
          simpl_expr.
          rewrite Rmult_plus_distr_l.
          simpl_expr. }
        + wp_pures.
          rewrite Z.add_1_r -Nat2Z.inj_succ.
          rewrite Z.sub_1_r (Nat2Z.inj_succ n) Z.pred_succ.
          wp_bind (sub_loc_fail α).
          wp_apply tgl_wp_wand_r.
          iSplitR; first by wp_apply sub_loc_fail_unit.
          iIntros (β) "#Hβ".
          wp_apply ("IH" $! E HE_nonneg with "[] [] [] [] Hβ Herr") as "%v [%Hv_le_n Herr]".
          { iPureIntro. lia. }
          { iPureIntro. lia. }
          { iPureIntro. lia. }
          { iPureIntro. subst ε1.
            apply SeriesC_ext => k.
            rewrite fin_S_inj_to_nat //. }
          rewrite fin_S_inj_to_nat.
          iApply ("HΦ" with "[$Herr]").
        + wp_pures.
          rewrite Z.add_1_r -Nat2Z.inj_succ.
          rewrite Z.sub_1_r (Nat2Z.inj_succ n) Z.pred_succ.
          wp_bind (sub_loc_success α).
          wp_apply tgl_wp_wand_r.
          iSplitR; first by wp_apply sub_loc_success_unit.
          iIntros (β) "#Hβ".
          wp_apply ("IH" $! (E ∘ S) with "[] [] [] [] [] Hβ Herr") as "%v Herr".
          { real_solver. }
          { iPureIntro. lia. }
          { iPureIntro. lia. }
          { iPureIntro. lia. }
          { iPureIntro. subst ε2.
            apply SeriesC_ext => k.
            fold (Beta_prob (S red) black n k).
            simpl_expr. }
          wp_pures.
          rewrite Z.add_1_l -Nat2Z.inj_succ.
          rewrite -fin_to_nat_FS.
          iApply ("HΦ" with "[Herr]").
          rewrite fin_to_nat_FS //.
    Qed.
      
    Definition is_abs_loc (n : nat) (α : val) (Δ : triangle loc n) : iProp Σ :=
      □ (∀ (i : fin n) (j : fin (S i)), WP α #i #j [{ v, ⌜v = #lbl:(triangle_get Δ i j)⌝ }])%I.

    Definition is_abs_row (n : nat) (α : val) (r : fin_list loc n) : iProp Σ :=
      □ (∀ (i : fin n), WP α #i [{ v, ⌜v = #lbl:(fin_list_get r i)⌝ }]).
   
    Definition own_top_list
      {n : nat}
      (p q : nat)
      (αs : fin_list loc n)
      (ls : fin_list (list (fin 2)) n)
      :=
      ([∗ list] i ∈ fin_enum n,
           own_bernoulli_tape
             (fin_list_get αs i)
             p
             (q + i)%nat
             (fin_list_get ls i)
      )%I.

    Definition own_bottom_list
      {n : nat}
      (p q : nat)
      (αs : fin_list loc n)
      (ls : fin_list (list (fin 2)) n)
      :=
      ([∗ list] i ∈ fin_enum n,
           own_bernoulli_tape
             (fin_list_get αs i)
             (p + i)%nat
             (q + i)%nat
             (fin_list_get ls i)
      )%I.
    
    Definition own_trig
      {n : nat}
      (p q : nat)
      (Δ : triangle loc n)
      (τ : β_tape n)
      :=
      ([∗ list] i ∈ fin_enum n,
         [∗ list] j ∈ fin_enum (S i),
           own_bernoulli_tape
             (triangle_get Δ i j)
             (p + j)%nat
             (q + i)
             (triangle_get τ i j)
      )%I.
    
    Lemma own_trig_split_top_1
      {n : nat}
      (p q : nat)
      (Δ : triangle loc (S n))
      (τ : β_tape (S n)) :
      own_trig p q Δ τ -∗
      own_trig (S p) (S q) (triangle_remove_top Δ) (triangle_remove_top τ) ∗
      own_top_list p q (triangle_top Δ) (triangle_top τ).
    Proof.
      iIntros "Hτ".
      unfold own_trig at 1.
      simpl.
      rewrite big_sepL_sep.
      iDestruct "Hτ" as "([Hhd _]  & Htltop & Htl)".
      iSplitL "Htl".
      { do 2 setoid_rewrite big_sepL_fmap.
        erewrite big_opL_ext; first done.
        move=>_ i _ /=.
        simpl.
        rewrite Nat.add_1_r Nat.add_succ_r Nat.add_0_r.
        f_equal.
        apply big_opL_ext.
        move=>_ j _ /=.
        rewrite Nat.add_succ_r //.
      }
      unfold own_top_list.
      rewrite big_sepL_cons.
      fold fin_enum.
      rewrite !Nat.add_0_r !triangle_get_top.
      iFrame.
      #[local] Opaque triangle_get triangle_top fin_list_get.
      erewrite big_opL_ext; first done.
      move=>_ i _ /=.
      rewrite !triangle_get_top //.
    Qed.
    
    Lemma own_trig_split_top_2
      {n : nat}
      (p q : nat)
      (Δ : triangle loc (S n))
      (τ : β_tape (S n)) :
      own_trig (S p) (S q) (triangle_remove_top Δ) (triangle_remove_top τ) ∗
      own_top_list p q (triangle_top Δ) (triangle_top τ) -∗
      own_trig p q Δ τ.
    Proof.
      iIntros "[Hτ Htop]".
      unfold own_trig at 2.
      simpl.
      rewrite big_sepL_sep.
      unfold own_top_list.
      simpl.
      iDestruct "Htop" as "[Hhd Htltop]".
      iSplitL "Hhd".
      { rewrite !Nat.add_0_r !triangle_get_top //. }
      iSplitL "Htltop".
      {
        erewrite big_opL_ext; first done.
        move=>_ i _ /=.
        rewrite !triangle_get_top Nat.add_0_r //.
      }
      do 2 setoid_rewrite big_sepL_fmap.
      erewrite big_opL_ext; first done.
      move=>_ i _ /=.
      simpl.
      rewrite Nat.add_1_r Nat.add_succ_r Nat.add_0_r.
      f_equal.
      apply big_opL_ext.
      move=>_ j _ /=.
      rewrite Nat.add_succ_r //.
    Qed.
    
    Lemma own_trig_split_top
      {n : nat}
      (p q : nat)
      (Δ : triangle loc (S n))
      (τ : β_tape (S n)) :
      own_trig p q Δ τ ⊣⊢
      own_trig (S p) (S q) (triangle_remove_top Δ) (triangle_remove_top τ) ∗
      own_top_list p q (triangle_top Δ) (triangle_top τ).
    Proof.
      iSplit.
      - iApply own_trig_split_top_1.
      - iApply own_trig_split_top_2.
    Qed.

    Lemma own_trig_split_bottom_1
      {n : nat}
      (p q : nat)
      (Δ : triangle loc (S n))
      (τ : β_tape (S n)) :
      own_trig p q Δ τ -∗
      own_trig p (S q) (triangle_remove_bottom Δ) (triangle_remove_bottom τ) ∗
      own_bottom_list p q (triangle_bottom Δ) (triangle_bottom τ).
    Proof.
      iIntros "Hτ".
      unfold own_trig at 1.
      erewrite big_opL_ext; last first.
      {
        move=>? i ?.
        rewrite fin_enum_split //.
      }
      setoid_rewrite big_sepL_app.
      rewrite big_sepL_sep.
      setoid_rewrite big_sepL_singleton.
      iDestruct "Hτ" as "([_ Hτ] & Hbot)".
      iSplitL "Hτ".
      { do 2 setoid_rewrite big_sepL_fmap.
        fold fin_enum.
        erewrite big_opL_ext; first done.
        move=>_ i _ /=.
        simpl.
        rewrite !Nat.add_succ_r !Nat.add_0_r.
        rewrite -!triangle_get_remove_bottom //.
        f_equal. 
        apply big_opL_ext.
        move=>_ j _ /=.
        rewrite -!fin_S_inj_to_nat !triangle_get_remove_bottom //.
      } 
      unfold own_bottom_list.
      erewrite big_opL_ext; first done.
      move=>_ i _ /=.
      rewrite !fin_to_nat_to_fin !triangle_get_bottom //.
    Qed.

    Lemma own_trig_split_bottom_2
      {n : nat}
      (p q : nat)
      (Δ : triangle loc (S n))
      (τ : β_tape (S n)) :
      own_trig p (S q) (triangle_remove_bottom Δ) (triangle_remove_bottom τ) ∗
      own_bottom_list p q (triangle_bottom Δ) (triangle_bottom τ) -∗
      own_trig p q Δ τ.
    Proof.
      iIntros "[Hτ Hbot]".
      unfold own_trig at 2.
      erewrite big_opL_ext; last first.
      {
        move=>? i ?.
        rewrite fin_enum_split //.
      }
      setoid_rewrite big_sepL_app.
      rewrite big_sepL_sep.
      setoid_rewrite big_sepL_singleton.
      iSplitL "Hτ".
      { setoid_rewrite big_sepL_fmap.
        simpl.
        iSplitR; first done.
        setoid_rewrite big_sepL_fmap.
        erewrite big_opL_ext; first done.
        move=>_ i _ /=.
        simpl.
        rewrite !Nat.add_succ_r !Nat.add_0_r.
        rewrite -!triangle_get_remove_bottom //.
        f_equal. 
        apply big_opL_ext.
        move=>_ j _ /=.
        rewrite -!fin_S_inj_to_nat !triangle_get_remove_bottom //.
      } 
      unfold own_bottom_list.
      erewrite big_opL_ext; first done.
      move=>_ i _ /=.
      rewrite !fin_to_nat_to_fin !triangle_get_bottom //.
    Qed.
    
    Lemma own_trig_split_bottom
      {n : nat}
      (p q : nat)
      (Δ : triangle loc (S n))
      (τ : β_tape (S n)) :
      own_trig p q Δ τ ⊣⊢
      own_trig p (S q) (triangle_remove_bottom Δ) (triangle_remove_bottom τ) ∗
      own_bottom_list p q (triangle_bottom Δ) (triangle_bottom τ).
    Proof.
      iSplit.
      - iApply own_trig_split_bottom_1.
      - iApply own_trig_split_bottom_2.
    Qed.
    
    Lemma own_trig_glue_top
      {n : nat}
      (p q : nat)
      (Δ : triangle loc n)
      (τ : β_tape n)
      (αs : fin_list loc (S n))
      (ls : fin_list (list (fin 2)) (S n)) :
      own_trig (S p) (S q) Δ τ ∗
      own_top_list p q αs ls ⊣⊢
      own_trig p q (triangle_glue_top Δ αs) (triangle_glue_top τ ls).
    Proof.
      rewrite -{1}(triangle_top_glue Δ αs) -{1}(triangle_top_glue τ ls)
              -{1}(triangle_remove_glue_top Δ αs) -{1}(triangle_remove_glue_top τ ls).
      remember (triangle_glue_top Δ αs) as Δ'.
      remember (triangle_glue_top τ ls) as τ'.
      rewrite own_trig_split_top.
      iSplit;
        iIntros "[Hτ Hl]";
        iFrame.
    Qed.

    Lemma own_trig_glue_top_1
      {n : nat}
      (p q : nat)
      (Δ : triangle loc n)
      (τ : β_tape n)
      (αs : fin_list loc (S n))
      (ls : fin_list (list (fin 2)) (S n)) :
      own_trig (S p) (S q) Δ τ ∗
      own_top_list p q αs ls -∗
      own_trig p q (triangle_glue_top Δ αs) (triangle_glue_top τ ls).
    Proof.
      iApply (bi.equiv_entails_1_1 _ _ (own_trig_glue_top _ _ _ _ _ _)).
    Qed.

    Lemma own_trig_glue_top_2
      {n : nat}
      (p q : nat)
      (Δ : triangle loc n)
      (τ : β_tape n)
      (αs : fin_list loc (S n))
      (ls : fin_list (list (fin 2)) (S n)) :
      own_trig p q (triangle_glue_top Δ αs) (triangle_glue_top τ ls) -∗
      own_trig (S p) (S q) Δ τ ∗
      own_top_list p q αs ls.
    Proof.
      iApply (bi.equiv_entails_1_2 _ _ (own_trig_glue_top _ _ _ _ _ _)).
    Qed.
    
    Lemma own_trig_glue_bottom
      {n : nat}
      (p q : nat)
      (Δ : triangle loc n)
      (τ : β_tape n)
      (αs : fin_list loc (S n))
      (ls : fin_list (list (fin 2)) (S n)) :
      own_trig p (S q) Δ τ ∗
      own_bottom_list p q αs ls ⊣⊢
      own_trig p q (triangle_glue_bottom Δ αs) (triangle_glue_bottom τ ls).
    Proof.
      rewrite -{1}(triangle_bottom_glue Δ αs) -{1}(triangle_bottom_glue τ ls)
              -{1}(triangle_remove_glue_bottom Δ αs) -{1}(triangle_remove_glue_bottom τ ls).
      rewrite own_trig_split_bottom //.
    Qed.

    Lemma own_trig_glue_bottom_1
      {n : nat}
      (p q : nat)
      (Δ : triangle loc n)
      (τ : β_tape n)
      (αs : fin_list loc (S n))
      (ls : fin_list (list (fin 2)) (S n)) :
      own_trig p (S q) Δ τ ∗
      own_bottom_list p q αs ls -∗
      own_trig p q (triangle_glue_bottom Δ αs) (triangle_glue_bottom τ ls).
    Proof.
      iApply (bi.equiv_entails_1_1 _ _ (own_trig_glue_bottom _ _ _ _ _ _)).
    Qed.

    Lemma own_trig_glue_bottom_2
      {n : nat}
      (p q : nat)
      (Δ : triangle loc n)
      (τ : β_tape n)
      (αs : fin_list loc (S n))
      (ls : fin_list (list (fin 2)) (S n)) :
      own_trig p q (triangle_glue_bottom Δ αs) (triangle_glue_bottom τ ls) -∗
      own_trig p (S q) Δ τ ∗
      own_bottom_list p q αs ls.
    Proof.
      iApply (bi.equiv_entails_1_2 _ _ (own_trig_glue_bottom _ _ _ _ _ _)).
    Qed.
    
    Lemma own_top_list_split_1
      {n : nat}
      (p q : nat)
      (αs : fin_list loc (S n))
      (ls : fin_list (list (fin 2)) (S n)) :
      own_top_list p q αs ls -∗
      own_bernoulli_tape (fin_list_head αs) p q (fin_list_head ls) ∗
      own_top_list p (S q) (fin_list_tail αs) (fin_list_tail ls).
    Proof.
      iIntros "[Hh Hτ]".
      fold fin_enum.
      iSplitL "Hh".
      - rewrite Nat.add_0_r //.
      - rewrite big_sepL_fmap.
        erewrite big_opL_ext; first done.
        move=>_ i _ /=.
        rewrite Nat.add_succ_r !fin_list_get_FS //.
    Qed.

     Lemma own_top_list_split_2
      {n : nat}
      (p q : nat)
      (αs : fin_list loc (S n))
      (ls : fin_list (list (fin 2)) (S n)) :
      own_bernoulli_tape (fin_list_head αs) p q (fin_list_head ls) ∗
      own_top_list p (S q) (fin_list_tail αs) (fin_list_tail ls) -∗
      own_top_list p q αs ls.
    Proof.
      iIntros "[Hh Hτ]".
      fold fin_enum.
      iSplitL "Hh".
      - rewrite Nat.add_0_r //.
      - rewrite big_sepL_fmap.
        erewrite big_opL_ext; first done.
        move=>_ i _ /=.
        rewrite Nat.add_succ_r !fin_list_get_FS //.
    Qed.

    Lemma own_top_list_split
      {n : nat}
      (p q : nat)
      (αs : fin_list loc (S n))
      (ls : fin_list (list (fin 2)) (S n)) :
      own_top_list p q αs ls ⊣⊢
      own_bernoulli_tape (fin_list_head αs) p q (fin_list_head ls) ∗
      own_top_list p (S q) (fin_list_tail αs) (fin_list_tail ls).
    Proof.
      iSplit.
      - iApply own_top_list_split_1.
      - iApply own_top_list_split_2.
    Qed.

    Lemma own_top_list_cons
      {n : nat}
      (p q : nat)
      (α : loc)
      (l : list (fin 2))
      (αs : fin_list loc n)
      (ls : fin_list (list (fin 2)) n) :
      own_bernoulli_tape α p q l ∗
      own_top_list p (S q) αs ls ⊣⊢
      own_top_list p q (fin_cons α αs) (fin_cons l ls).
    Proof.
      rewrite -{1}(fin_list_head_cons α αs)
              -{1}(fin_list_head_cons l ls)
              -{1}(fin_list_tail_cons α αs)
              -{1}(fin_list_tail_cons l ls).
      rewrite own_top_list_split //.
    Qed.

    Lemma own_top_list_cons_1
      {n : nat}
      (p q : nat)
      (α : loc)
      (l : list (fin 2))
      (αs : fin_list loc n)
      (ls : fin_list (list (fin 2)) n) :
      own_bernoulli_tape α p q l ∗
      own_top_list p (S q) αs ls -∗
      own_top_list p q (fin_cons α αs) (fin_cons l ls).
    Proof.
      iApply (bi.equiv_entails_1_1 _ _ (own_top_list_cons _ _ _ _ _ _)).
    Qed.

    Lemma own_top_list_cons_2
      {n : nat}
      (p q : nat)
      (α : loc)
      (l : list (fin 2))
      (αs : fin_list loc n)
      (ls : fin_list (list (fin 2)) n) :
      own_top_list p q (fin_cons α αs) (fin_cons l ls) -∗
      own_bernoulli_tape α p q l ∗
      own_top_list p (S q) αs ls.
    Proof.
      iApply (bi.equiv_entails_1_2 _ _ (own_top_list_cons _ _ _ _ _ _)).
    Qed.

     
    Lemma own_bottom_list_split_1
      {n : nat}
      (p q : nat)
      (αs : fin_list loc (S n))
      (ls : fin_list (list (fin 2)) (S n)) :
      own_bottom_list p q αs ls -∗
      own_bernoulli_tape (fin_list_head αs) p q (fin_list_head ls) ∗
      own_bottom_list (S p) (S q) (fin_list_tail αs) (fin_list_tail ls).
    Proof.
      iIntros "[Hh Hτ]".
      fold fin_enum.
      iSplitL "Hh".
      - rewrite !Nat.add_0_r //.
      - rewrite big_sepL_fmap.
        erewrite big_opL_ext; first done.
        move=>_ i _ /=.
        rewrite !Nat.add_succ_r !fin_list_get_FS //.
    Qed.

     Lemma own_bottom_list_split_2
      {n : nat}
      (p q : nat)
      (αs : fin_list loc (S n))
      (ls : fin_list (list (fin 2)) (S n)) :
      own_bernoulli_tape (fin_list_head αs) p q (fin_list_head ls) ∗
      own_bottom_list (S p) (S q) (fin_list_tail αs) (fin_list_tail ls) -∗
      own_bottom_list p q αs ls.
    Proof.
      iIntros "[Hh Hτ]".
      fold fin_enum.
      iSplitL "Hh".
      - rewrite !Nat.add_0_r //.
      - rewrite big_sepL_fmap.
        erewrite big_opL_ext; first done.
        move=>_ i _ /=.
        rewrite !Nat.add_succ_r !fin_list_get_FS //.
    Qed.

    Lemma own_bottom_list_split
      {n : nat}
      (p q : nat)
      (αs : fin_list loc (S n))
      (ls : fin_list (list (fin 2)) (S n)) :
      own_bottom_list p q αs ls ⊣⊢
      own_bernoulli_tape (fin_list_head αs) p q (fin_list_head ls) ∗
      own_bottom_list (S p) (S q) (fin_list_tail αs) (fin_list_tail ls).
    Proof.
      iSplit.
      - iApply own_bottom_list_split_1.
      - iApply own_bottom_list_split_2.
    Qed.

    Lemma own_bottom_list_cons
      {n : nat}
      (p q : nat)
      (α : loc)
      (l : list (fin 2))
      (αs : fin_list loc n)
      (ls : fin_list (list (fin 2)) n) :
      own_bernoulli_tape α p q l ∗
      own_bottom_list (S p) (S q) αs ls ⊣⊢
      own_bottom_list p q (fin_cons α αs) (fin_cons l ls).
    Proof.
      rewrite -{1}(fin_list_head_cons α αs)
              -{1}(fin_list_head_cons l ls)
              -{1}(fin_list_tail_cons α αs)
              -{1}(fin_list_tail_cons l ls).
      rewrite own_bottom_list_split //.
    Qed.

    Lemma own_bottom_list_cons_1
      {n : nat}
      (p q : nat)
      (α : loc)
      (l : list (fin 2))
      (αs : fin_list loc n)
      (ls : fin_list (list (fin 2)) n) :
      own_bernoulli_tape α p q l ∗
      own_bottom_list (S p) (S q) αs ls -∗
      own_bottom_list p q (fin_cons α αs) (fin_cons l ls).
    Proof.
      iApply (bi.equiv_entails_1_1 _ _ (own_bottom_list_cons _ _ _ _ _ _)).
    Qed.

    Lemma own_bottom_list_cons_2
      {n : nat}
      (p q : nat)
      (α : loc)
      (l : list (fin 2))
      (αs : fin_list loc n)
      (ls : fin_list (list (fin 2)) n) :
      own_bottom_list p q (fin_cons α αs) (fin_cons l ls) -∗
      own_bernoulli_tape α p q l ∗
      own_bottom_list (S p) (S q) αs ls.
    Proof.
      iApply (bi.equiv_entails_1_2 _ _ (own_bottom_list_cons _ _ _ _ _ _)).
    Qed.

    
    Lemma own_trig_1
      (p q : nat)
      (αs : fin_list loc 1)
      (ls : fin_list (list (fin 2)) 1) :
      own_trig p q (trig_snoc trig_nil αs) (trig_snoc trig_nil ls)
      ⊣⊢ own_bernoulli_tape (fin_list_head αs) p q (fin_list_head ls).
    Proof.
      inv_fin_list αs => α αs.
      inv_fin_list αs.
      inv_fin_list ls => l ls.
      inv_fin_list ls.
      unfold own_trig.
      rewrite !big_sepL_singleton !Nat.add_0_r //.
    Qed.

    Definition own_polya_tape
      {n : nat}
      (red black : nat)
      (Δ : triangle loc n)
      (l : list (fin (S n)))
      := (∃ (lτ : list (fin_list (fin 2) n)),
             own_trig red (red + black - 1) Δ (β_fold lτ) ∗ ⌜l = fin_list_fin_2_sum <$> lτ⌝
         )%I.
    
    Lemma polyalloc_row_spec :
      ∀ (n red black : nat), (0 < red + black)%nat →
      ⊢ WP polyalloc_row #red #black #n
          [{α, ∃ (r : fin_list loc n), is_abs_row n α r ∗ own_top_list red (red + black - 1) r β_empty_list }].
    Proof.
      iIntros (n).
      iInduction (n) as [|n] "IH"; iIntros (red black sum_red_black_pos); unfold polyalloc_row.
      - wp_pures.
        iModIntro.
        iExists fin_nil.
        iSplit.
        { iIntros (i). inv_fin i. }
        by unfold own_top_list.
      - wp_pures.
        rewrite -Nat2Z.inj_add -(Nat2Z.inj_sub _ 1); last lia.
        wp_apply (twp_bernoulli_alloc with "[$]") as (α) "Hα".
        fold polyalloc_row.
        wp_pures.
        rewrite -(Nat2Z.inj_add _ 1) -(Nat2Z.inj_sub _ 1); last lia.
        rewrite /= Nat.sub_0_r.
        wp_bind (polyalloc_row _ _ _)%E.
        wp_apply tgl_wp_wand_r.
        iSplitR "Hα"; first (wp_apply "IH"; iPureIntro; lia).
        iIntros (v) "(%r & #Hrow & Htop)".
        wp_pures.
        iModIntro.
        iExists (fin_cons α r).
        iSplitL "Hrow".
        + iIntros (i).
          inv_fin i=>[|i].
          { iModIntro.
            by wp_pures.
          }
          iModIntro.
          wp_pures.
          rewrite -(Nat2Z.inj_sub _ 1); last lia.
          rewrite /= Nat.sub_0_r fin_list_get_cons_S //.
        + rewrite Nat.add_assoc Nat.add_sub.
          iApply own_top_list_cons_1.
          replace (S (red + black - 1))%nat with (red + black)%nat by lia.
          iFrame.
    Qed.
      
    Lemma polyalloc_spec_trig :
      ∀ (n red black : nat), (0 < red + black)%nat →
      ⊢ WP polyalloc #red #black #n
          [{α, ∃ (Δ : triangle loc n), is_abs_loc n α Δ ∗ own_trig red (red + black - 1) Δ β_empty }].
    Proof.
      iIntros (n).
      iInduction (n) as [|n] "IH"; iIntros (red black sum_red_black_pos); unfold polyalloc.
      - wp_pures.
        iExists trig_nil.
        iModIntro.
        iSplit.
        { iIntros (i). inv_fin i. }
        by unfold own_trig.
      - wp_pures.
        fold polyalloc.
        wp_bind (polyalloc_row _ _ _)%E.
        wp_apply tgl_wp_wand_r.
        iSplitL; first by wp_apply polyalloc_row_spec.
        iIntros (v) "(%r & #Hrow & Hown)".
        wp_pures.
        rewrite -(Nat2Z.inj_add _ 1) -(Nat2Z.inj_sub _ 1); last lia.
        rewrite /= Nat.sub_0_r.
        wp_bind (polyalloc _ _ _)%E.
        wp_apply tgl_wp_wand_r.
        iSplitR "Hown"; first (wp_apply "IH"; iPureIntro; lia).
        iIntros (w) "(%Δ & #Hloc & HΔ)".
        wp_pures.
        iModIntro.
        iExists (triangle_glue_top Δ r).
        iSplitR "Hown HΔ".
        + iIntros (i j).
          iModIntro.
          inv_fin j=>[|j]; wp_pures.
          { rewrite triangle_get_top triangle_top_glue //. }
          inv_fin i=>[|i] j; first inv_fin j.
          rewrite -!(Nat2Z.inj_sub _ 1) /=; [|lia..].
          rewrite /= !Nat.sub_0_r triangle_get_remove_top triangle_remove_glue_top //.
        + rewrite Nat.add_1_r /= Nat.sub_0_r.
          iApply own_trig_split_top_2.
          rewrite triangle_remove_glue_top trig_const_remove_top triangle_top_glue trig_const_top.
          replace (S (red + black - 1))%nat with (red + black)%nat by lia.
          iFrame.
    Qed.

    Lemma polyalloc_spec :
      ∀ (n red black : nat), (0 < red + black)%nat →
      ⊢ WP polyalloc #red #black #n
          [{α, ∃ (Δ : triangle loc n), is_abs_loc n α Δ ∗ own_polya_tape red black Δ [] }].
    Proof.
      iIntros (n red black sum_red_black_pos).
      wp_apply tgl_wp_wand_r.
      iSplitL; first by wp_apply polyalloc_spec_trig.
      iIntros (v) "(%Δ & Hloc & HΔ)".
      iExists Δ.
      iFrame.
      unfold own_polya_tape.
      iExists [].
      by iFrame.
    Qed.
   
    Lemma own_top_list_presample :
      ∀ (e : expr) (p q n : nat) (ε : R) (D : fin 2 → R)
        (αs : fin_list loc (S n))
        (ls : fin_list (list (fin 2)) (S n))
        (Φ : val → iProp Σ),
      (p ≤ q + 1)%nat →
      (0 <= D 0%fin) →
      (0 <= D 1%fin) →
      (D 0%fin * (1 - p / (q + 1)) + D 1%fin * (p / (q + 1))  = ε) →
      to_val e = None →
      ↯ ε ∗
      own_top_list p q αs ls ∗
      (∀ (i : fin 2),
         ↯ (D i) ∗
         own_top_list p q αs (β_list_hsup_first ls i) -∗
         WP e [{ v, Φ v }]
      ) ⊢ WP e [{ v, Φ v }].
    Proof.
      iIntros (e p q n ε D αs ls Φ p_le_Sq D0_pos D1_pos D_sum e_not_val) "(Herr & Hαs & Hnext)".
      iPoseProof (own_top_list_split_1 with "Hαs") as "[Hα Hαs]".
      wp_apply (twp_presample_bernoulli_adv_comp _ _ _ _ _ _ _ D with "[$Herr $Hα Hαs Hnext]"); try done.
      { move=>i.
        inv_fin i=>[//|i].
        inv_fin i=>[//|i].
        inv_fin i.
      } 
      iIntros (i) "[Herr Hα]".
      wp_apply "Hnext".
      iFrame.
      iPoseProof (own_top_list_cons_1 with "[$Hα $Hαs]") as "Hαs".
      rewrite -fin_list_cons_head_tail //.
    Qed.

    Lemma own_trig_presample_0_q :
      ∀ (e : expr) (q n : nat)
        (Δ : triangle loc n)
        (τ : β_tape n)
        (Φ : val → iProp Σ),
      to_val e = None →
      own_trig 0 q Δ τ ∗
        ( own_trig 0 q Δ (β_hsup τ (fin_list_const (0%fin : fin 2))) -∗
          WP e [{ v, Φ v }])
        ⊢ WP e [{ v, Φ v }].
    Proof.
      iIntros (e q n).
      iInduction (n) as [|n] "IH" forall (q);
        iIntros (Δ τ Φ e_not_val) "[HΔ Hnext]".
      { wp_apply "Hnext".
        by unfold own_trig.
      }
      iPoseProof (own_trig_split_bottom_1 with "HΔ") as "[HΔ Hα]".
      iPoseProof (own_bottom_list_split_1 with "Hα") as "[Hh Hα]".
      iMod ec_zero as "Herr".
      set (d (i : fin 2) := match i with
                  | 0%fin => 0%R
                  | _ => 1%R
                  end).
      wp_apply (twp_presample_bernoulli_adv_comp _ _ _ _ _ _ _ d with "[$Hh $Herr Hα HΔ Hnext]"); first lia; try done.
      { move=>i.
        inv_fin i=>[|i] /=; lra.
      }
      { rewrite /= Rmult_0_l Rdiv_0_l Rmult_0_r Rplus_0_r //. }
      iIntros (i) "[Herr Htape]".
      inv_fin i=>[| i] /=; last first.
      { iPoseProof (ec_contradict with "[$Herr]") as "HFalse"; first lra.
        iDestruct "HFalse" as "[]".
      }
      iClear (d) "Herr".
      wp_apply "IH"; try done.
      iFrame.
      iIntros "HΔ".
      wp_apply "Hnext".
      rewrite {4}(triangle_glue_remove_bottom Δ).
      iApply own_trig_glue_bottom_1.
      iFrame.
      iApply own_bottom_list_split_2.
      iFrame.
    Qed.

    Lemma own_trig_presample_Sq_q :
      ∀ (e : expr) (q n : nat)
        (Δ : triangle loc n)
        (τ : β_tape n)
        (Φ : val → iProp Σ),
      to_val e = None →
      own_trig (S q) q Δ τ ∗
        ( own_trig (S q) q Δ (β_hsup τ (fin_list_const (1%fin : fin 2))) -∗
          WP e [{ v, Φ v }])
        ⊢ WP e [{ v, Φ v }].
    Proof.
      iIntros (e q n).
      iInduction (n) as [|n] "IH" forall (q);
        iIntros (Δ τ Φ e_not_val) "[HΔ Hnext]".
      { wp_apply "Hnext".
        by unfold own_trig.
      }
      iPoseProof (own_trig_split_top_1 with "HΔ") as "[HΔ Hα]".
      iPoseProof (own_top_list_split_1 with "Hα") as "[Hh Hα]".
      iMod ec_zero as "Herr".
      set (d (i : fin 2) := match i with
                  | 0%fin => 1%R
                  | _ => 0%R
                  end).
      wp_apply (twp_presample_bernoulli_adv_comp _ _ _ _ _ _ _ d with "[$Hh $Herr Hα HΔ Hnext]"); first lia; try done.
      { move=>i.
        inv_fin i=>[|i] /=; lra.
      }
      { pose proof (pos_INR q).
        rewrite S_INR /= Rmult_0_l Rmult_1_l Rplus_0_r Rdiv_diag; last lra.
        apply Rminus_diag.
      } 
      iIntros (i) "[Herr Htape]".
      inv_fin i=>[| i] /=.
      { iPoseProof (ec_contradict with "[$Herr]") as "HFalse"; first lra.
        iDestruct "HFalse" as "[]".
      }
      inv_fin i=>[|i]; last inv_fin i.
      iClear (d) "Herr".
      wp_apply "IH"; try done.
      iFrame.
      iIntros "HΔ".
      wp_apply "Hnext".
      rewrite {4}(triangle_glue_remove_top Δ).
      iApply own_trig_glue_top_1.
      iFrame.
      iApply own_top_list_split_2.
      iFrame.
    Qed.
    
    Lemma own_trig_presample :
      ∀ (e : expr) (p q n : nat) (ε : R)
        (D : fin (S n) → R)
        (Δ : triangle loc n)
        (τ : β_tape n)
        (Φ : val → iProp Σ),
      (p ≤ q + 1)%nat →
      to_val e = None →
      (∀ (i : fin (S n)), 0 <= D i) →
      SeriesC (λ (i : fin (S n)), Beta_prob p (q + 1 - p)%nat n i * D i) = ε →
      ↯ ε ∗
      own_trig p q Δ τ ∗
      (∀ (i : fin_list (fin 2) n),
         ↯ (D (fin_list_fin_2_sum i)) ∗
         own_trig p q Δ (β_hsup τ i) -∗
         WP e [{ v, Φ v }]
      ) ⊢ WP e [{ v, Φ v }].
    Proof.
      iIntros (e p q n).
      destruct (decide (0 < p)%nat); last first.
      {
        replace p with 0%nat by lia.
        clear.
        iIntros (ε D Δ τ Φ p_le_Sq e_not_val D_pos D_sum) "(Herr & HΔ & Hnext)".
        rewrite -D_sum Series_fin_first {1}/Beta_prob Choose_n_0 !Beta_0_l Rdiv_1_r !Rmult_1_l.
        iPoseProof (ec_split with "Herr") as "[Herr _]"; first apply D_pos.
        { apply SeriesC_ge_0'=>i.
          apply Rmult_le_pos; last apply D_pos.
          apply Beta_prob_pos.
        }
        wp_apply own_trig_presample_0_q; try done.
        iFrame.
        iIntros "HΔ".
        wp_apply "Hnext".
        iFrame.
        rewrite fin_list_fin_2_sum_const_0_eq_0 //.
      }
      destruct (decide (p < q + 1)%nat); last first.
      {
        iIntros (ε D Δ τ Φ p_le_Sq e_not_val D_pos D_sum) "(Herr & HΔ & Hnext)".
        rewrite -D_sum Series_fin_last {2}/Beta_prob fin_to_nat_to_fin Nat.sub_diag Choose_n_n.
        replace p with (q + 1)%nat by lia.
        rewrite Nat.sub_diag !Beta_0_r Rdiv_1_r !Rmult_1_l.
        iPoseProof (ec_split with "Herr") as "[_ Herr]"; try apply D_pos.
        { apply SeriesC_ge_0'=>i.
          apply Rmult_le_pos; last apply D_pos.
          apply Beta_prob_pos.
        }
        wp_apply own_trig_presample_Sq_q; try done.
        rewrite Nat.add_1_r.
        iFrame.
        iIntros "HΔ".
        wp_apply "Hnext".
        iFrame.
        rewrite fin_list_fin_2_sum_const_1_eq_max.
        iApply (ec_eq with "Herr").
        f_equal.
        destruct (decide (nat_to_fin (Nat.lt_succ_diag_r n) = fin_max n))
          as [-> | contra]; first done.
        pose proof (fin_to_nat_lt (fin_max n)).
        assert (nat_to_fin H ≠ nat_to_fin (Nat.lt_succ_diag_r n)) as contra'.
        {
          move=>ntf_eq.
          apply contra.
          rewrite -ntf_eq nat_to_fin_to_nat //.
        }
        contradict contra'.
        pose proof (fin_max_to_nat n) as fin_max_nat.
        symmetry in fin_max_nat.
        destruct fin_max_nat.
        apply nat_to_fin_proof_ext.
      }
      assert (0 < p < q + 1)%nat as p_bounds by lia.
      iIntros (ε D Δ τ Φ p_le_Sq).
      clear p_le_Sq.
      iRevert (ε D Δ τ Φ p_bounds).
      clear.
      iInduction (n) as [|n] "IH" forall (p q);
       iIntros (ε D Δ τ Φ p_bounds e_not_val D_pos D_sum) "(Herr & HΔ & Hnext)".
      - inv_triangle Δ.
        inv_triangle τ.
        simpl.
        wp_apply ("Hnext" $! fin_nil with "[Herr $HΔ]").
        rewrite SeriesC_finite_foldr /= Beta_prob_0_0 Rmult_1_l Rplus_0_r in D_sum.
        by subst.
      - rewrite Beta_sum_split in D_sum; try lia.
        match type of D_sum with
        | _ * ?d1 + _ * ?d0 = _ => set (d (i : fin 2) := match i with
                                                         | 0%fin => d0
                                                         | _ => d1
                                                         end)
        end.
        assert (∀ (i : fin 2), 0 <= d i).
        {
          move=>i.
          inv_fin i=>[|i]; apply SeriesC_ge_0'.
          - move=>k.
            apply Rmult_le_pos; first apply Beta_prob_pos.
            apply D_pos.
          - move=>k.
            apply Rmult_le_pos; first apply Beta_prob_pos.
            apply D_pos.
        }

        assert (d 0%fin * (1 - p / (q + 1)) + d 1%fin * (p / (q + 1)) = ε).
        { rewrite -D_sum /= -plus_INR.
          replace (p + (q + 1 - p))%nat with (q + 1)%nat by lia.
          replace ((q + 1 - p)%nat / (q + 1)%nat : R)%nat with (1 - p / (q + 1)); last first.
          {
            rewrite minus_INR; last lia.
            rewrite Rdiv_minus_distr Rdiv_diag; last first.
            { rewrite Nat.add_1_r. apply INR_S_not_0. }
            rewrite plus_INR //.
          }
          rewrite !plus_INR /=.
          lra.
        }
   
        destruct n.
        { inv_triangle τ => τ lτ.
          inv_triangle Δ => Δ lΔ.
          inv_triangle τ.
          inv_triangle Δ.
          rewrite own_trig_1.
          wp_apply (twp_presample_bernoulli_adv_comp _ _ _ _ _ _ _ d with "[$HΔ $Herr Hnext]") as (i) "[Herr Hα]"; first lia; try done.
          wp_apply ("Hnext" $! (fin_cons i fin_nil)).
         full_inv_fin; rewrite /= SeriesC_finite_foldr.
          - rewrite /= Beta_prob_0_0 Rmult_1_l Rplus_0_r own_trig_1.
            iFrame.
          - rewrite /= Beta_prob_0_0 Rmult_1_l Rplus_0_r own_trig_1.
            iFrame.
       }
       iPoseProof (own_trig_split_top with "HΔ") as "[HΔ Hα]".
       wp_apply (own_top_list_presample _ _ _ _ _ d with "[$Hα $Herr HΔ Hnext]"); try done.
       iIntros (i) "[Herr Hα]".
       full_inv_fin.
        + iPoseProof (own_trig_glue_top_1 with "[$Hα $HΔ]") as "HΔ".
          rewrite -triangle_glue_remove_top.
          iPoseProof (own_trig_split_bottom with "HΔ") as "[HΔ Hα]".
          rewrite !triangle_remove_bottom_glue_top !triangle_bottom_glue_top
                  -triangle_remove_top_bottom β_list_hsup_first_fin_tail
                  -triangle_top_remove_bottom -triangle_glue_remove_top.
          wp_apply ("IH" $! _ _ _ (D ∘ fin_S_inj) with "[] [] [] [] [$HΔ Hα Hnext $Herr]") as (i) "[Herr HΔ]"; try (done || real_solver).
          { iPureIntro. lia. }
          { iPureIntro.
            simpl.
            apply SeriesC_ext.
            move=>i //.
            repeat f_equal.
            lia.
          } 
          wp_apply ("Hnext" $! (fin_cons 0%fin i)).
          iFrame.
          cbv [β_list_hsup_first].
          rewrite fin_list_head_cons triangle_top_bottom_first.
          iPoseProof (own_trig_glue_bottom_1 with "[$Hα $HΔ]") as "HΔ".
          rewrite -triangle_glue_remove_bottom.
          simpl.
          cbv [β_list_hsup_first].
          rewrite !triangle_bottom_split_cons //.
        + wp_apply ("IH" $! _ _ _ (D ∘ FS) with "[] [] [] [] [$HΔ Hα Hnext Herr]"); try (done || real_solver).
          { iPureIntro. lia. }
          iFrame.
          iIntros (i) "[Herr HΔ]".
          wp_apply ("Hnext" $! (fin_cons 1%fin i)).
          iPoseProof (own_trig_glue_top_1 with "[$Hα $HΔ]") as "HΔ".
          rewrite -triangle_glue_remove_top (fin_list_fin_2_sum_S _ (fin_cons 1%fin i)) /= fin_succ_inj.
          iFrame.
    Qed.

    Lemma own_polya_presample :
      ∀ (e : expr) (red black n : nat) (ε : R)
        (D : fin (S n) → R)
        (Δ : triangle loc n)
        (l : list (fin (S n)))
        (Φ : val → iProp Σ),
      (0 < red + black)%nat →
      to_val e = None →
      (∀ (i : fin (S n)), 0 <= D i) →
      SeriesC (λ (i : fin (S n)), Beta_prob red black n i * D i) = ε →
      ↯ ε ∗
      own_polya_tape red black Δ l ∗
      (∀ (i : fin (S n)),
         ↯ (D i) ∗ own_polya_tape red black Δ (l ++ [i]) -∗
         WP e [{ v, Φ v }]
      ) ⊢ WP e [{ v, Φ v }].
    Proof.
      iIntros (e red black n ε D Δ l Φ sum_red_black_pos e_not_val D_bounds D_sum) "(Herr & (%lτ & Hτ & %sum_lτ) & Hnext)".
      wp_apply (own_trig_presample _ _ _ _ _ D with "[$Hτ $Herr Hnext]") as (i) "[Herr Hτ]"; try done.
      { rewrite -D_sum.
        apply SeriesC_ext.
        move=>i.
        repeat f_equal.
        lia.
      } 
      rewrite β_hsup_fold.
      wp_apply "Hnext".
      iFrame.
      iPureIntro.
      rewrite fmap_app sum_lτ //.
    Qed.

    Lemma is_abs_loc_sub_loc_fail :
      ∀ (n : nat) (Δ : triangle loc (S n)) (α : val),
      [[{ is_abs_loc (S n) α Δ }]]
        sub_loc_fail α
        [[{ β, RET β; is_abs_loc n β (triangle_remove_bottom Δ)}]].
    Proof.
      iIntros (n Δ α Φ) "#Hα HΦ".
      unfold sub_loc_fail.
      wp_pures.
      iModIntro.
      iApply "HΦ".
      iModIntro.
      iIntros (i j).
      wp_pures.
      rewrite -(Nat2Z.inj_add _ 1) Nat.add_1_r.
      iSpecialize ("Hα" $! (FS i) (fin_S_inj j)).
      rewrite -fin_S_inj_to_nat triangle_get_remove_bottom //.
    Qed.

     Lemma is_abs_loc_sub_loc_success :
      ∀ (n : nat) (Δ : triangle loc (S n)) (α : val),
      [[{ is_abs_loc (S n) α Δ }]]
        sub_loc_success α
        [[{ β, RET β; is_abs_loc n β (triangle_remove_top Δ)}]].
    Proof.
      iIntros (n Δ α Φ) "#Hα HΦ".
      unfold sub_loc_success.
      wp_pures.
      iModIntro.
      iApply "HΦ".
      iModIntro.
      iIntros (i j).
      wp_pures.
      rewrite -!(Nat2Z.inj_add _ 1) !Nat.add_1_r.
      iApply ("Hα" $! (FS i) (FS j)).
    Qed.
    
    Lemma twp_polya_trig_load :
      ∀ (red black n : nat)
        (α : val)
        (Δ : triangle loc n)
        (τ : β_tape n)
        (i : fin_list (fin 2) n),
      (0 < red + black)%nat →
      [[{ own_trig red (red + black - 1) Δ (β_push τ i) ∗ is_abs_loc n α Δ }]]
        polya α #red #black #n
      [[{ RET #(fin_list_fin_2_sum i); own_trig red (red + black - 1) Δ τ }]].
    Proof.
      iIntros (red black n).
      iInduction (n) as [|n] "IH" forall (red black);
        iIntros (α Δ τ i sum_red_black_pos Φ) "[Htape #Hloc] HΦ".
      - inv_fin_list i.
        unfold polya.
        wp_pures.
        by iApply "HΦ".
      - inv_fin_list i=>hi ti.
        unfold polya.
        wp_pures.
        fold polya.
        wp_bind (α _ _).
        wp_apply tgl_wp_wand_r.
        iSplitR; first (wp_apply ("Hloc" $! 0%fin 0%fin)).
        iIntros (?) "->".
        inv_fin hi=>[|hi]; last inv_fin hi=>[|hi]; last inv_fin hi.
        + rewrite β_push_0_split {2}(triangle_glue_remove_bottom Δ).
          iPoseProof (own_trig_glue_bottom_2 with "Htape") as "[Htape Hbot]".
          iPoseProof (own_bottom_list_split_1 with "Hbot") as "[Hhead Hbot]".
          rewrite triangle_get_top fin_list_get_0 triangle_top_bottom_first
                                   -Nat2Z.inj_add -(Nat2Z.inj_sub _ 1)
          ; last lia.
          wp_apply (twp_bernoulli_tape with "Hhead") as "Hhead".
          wp_pures.
          rewrite -(Nat2Z.inj_add _ 1) -(Nat2Z.inj_sub _ 1); last lia.
          rewrite /= Nat.sub_0_r.
          wp_apply (is_abs_loc_sub_loc_fail n Δ α with "Hloc") as (β) "#Hβ".
          wp_apply ("IH" $! _ _ _ _ _ _ with "[] [Htape] [HΦ Hhead Hbot]") as "Htape"; first (iPureIntro; lia).
          { rewrite Nat.add_assoc Nat.add_sub.
            replace (S (red + black - 1)) with (red + black)%nat by lia.
            iFrame.
            iApply "Hβ".
          }
          rewrite fin_list_fin_2_sum_S -fin_S_inj_to_nat.
          iApply "HΦ".
          iPoseProof (own_bottom_list_split_2 with "[$Hhead $Hbot]") as "Hbot".
          rewrite Nat.add_assoc Nat.add_sub_swap; last lia.
          rewrite Nat.add_1_r.
          iApply own_trig_split_bottom_2.
          iFrame.
        + rewrite β_push_1_split {2}(triangle_glue_remove_top Δ).
          iPoseProof (own_trig_glue_top_2 with "Htape") as "[Htape Hbot]".
          iPoseProof (own_top_list_split_1 with "Hbot") as "[Hhead Hbot]".
          rewrite triangle_get_top fin_list_get_0
                  -Nat2Z.inj_add -(Nat2Z.inj_sub _ 1)
          ; last lia.
          wp_apply (twp_bernoulli_tape with "Hhead") as "Hhead".
          wp_pures.
          rewrite -(Nat2Z.inj_add _ 1) -(Nat2Z.inj_sub _ 1); last lia.
          rewrite /= Nat.sub_0_r.
          wp_apply (is_abs_loc_sub_loc_success n Δ α with "Hloc") as (β) "#Hβ".
          wp_apply ("IH" $! _ _ _ _ _ _ with "[] [Htape] [HΦ Hhead Hbot]") as "Htape"; first (iPureIntro; lia).
          { rewrite -(Nat.add_assoc) (Nat.add_comm 1 black) Nat.add_assoc Nat.add_sub.
            replace (S (red + black - 1)) with (red + black)%nat by lia.
            rewrite Nat.add_1_r.
            iFrame.
            iApply "Hβ".
          }
          rewrite fin_list_fin_2_sum_S /= fin_succ_inj.
          wp_pures.
          rewrite -(Nat2Z.inj_add 1 _).
          iApply "HΦ".
          iModIntro.
          iPoseProof (own_top_list_split_2 with "[$Hhead $Hbot]") as "Hbot".
          rewrite Nat.add_1_r.
          iApply own_trig_split_top_2.
          replace (S (red + black - 1)) with (S red + black - 1)%nat by lia.
          iFrame.
    Qed.

    Lemma twp_polya_tape :
      ∀ (red black n : nat)
        (α : val)
        (Δ : triangle loc n)
        (l : list (fin (S n)))
        (i : fin (S n)),
      (0 < red + black)%nat →
      [[{ own_polya_tape red black Δ (i::l) ∗ is_abs_loc n α Δ }]]
        polya α #red #black #n
      [[{ RET #i; own_polya_tape red black Δ l }]].
    Proof.
      iIntros (red black n α Δ l i sum_red_black_pos Φ) "[(%lτ & Hτ & %sum_lτ) Hα] HΦ".
      destruct lτ; first discriminate.
      injection sum_lτ as -> ->.
      simpl.
      wp_apply (twp_polya_trig_load with "[$Hτ $Hα]") as "Hτ"; first assumption.
      iApply "HΦ".
      by iFrame.
    Qed.

  End PolyaInst.
  
  #[global] Instance BetaOfBernoulli : beta_binomial_spec polya polyalloc.
  Proof.
    refine (BetaSpec _ _ (triangle loc) (λ _ _ red black n, @own_polya_tape _ _ n red black) (λ _ _ n, flip (is_abs_loc n)) (const loc_unit) _ _ (@own_polya_presample) (@twp_polya_tape)).
    - iIntros (Σ erisGS0 red black n D ε sum_red_black_pos D_pos D_sum Φ) "Herr HΦ".
      wp_apply (polya_spec with "[$Herr]"); try (done || real_solver).
      iApply loc_unit_is_unit.
    - iIntros (Σ erisGS0 red black n sum_red_black_pos Φ) "Hnext HΦ".
      wp_apply tgl_wp_wand_r.
      iSplitR; first by wp_apply polyalloc_spec.
      iIntros (α) "(%Δ & Hα & HΔ)".
      iApply "HΦ".
      iFrame.
  Qed.
End Polya.                        

#[global] Opaque polya polyalloc loc_unit.

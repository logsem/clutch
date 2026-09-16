From clutch.prob_eff_lang.probblaze.typing Require Import interp types.
From clutch.prob_eff_lang.probblaze Require Import logic sem_types sem_sig sem_row mode sem_def sem_env.

Section aux_lemma.
  Context `{!probblazeRGS Σ}.
 Lemma arr_extend_D ρ' D η μ δ ξ : 
     erase_ctx δ ξ D -∗ distinct' (iLblSig_to_iLblThy (interp._row η μ δ ρ' ξ)) -∗
     logic.valid (iLblSig_to_iLblThy (interp._row η μ δ ρ' ξ)) -∗
     erase_ctx δ ξ (le.update_disj_ctx ρ' D).
  Proof.
    iIntros "#HD #Hd #Hv".
    iDestruct (erase_ctx_row_to_disj_ctx η μ δ ξ ρ' with "[$Hv $Hd]")
      as "#Hrow".
    rewrite /erase_ctx /le.update_disj_ctx /le.merge_ctx.
    iIntros "!#" (s ss js ρ0 Hlk Hc Ha).
    apply lookup_union_with_Some in Hlk as [(Hlk1&Hlk2) | [(Hlk1&Hlk2) | Hb]].
    (* [row_to_disj_ctx ρ'] only: discharge directly from [Hrow]. *)
    1: by iApply ("Hrow" $! s ss js ρ0 with "[//] [//] [//]").
    (* [D] only: discharge directly from [HD]. *)
    1: by iApply ("HD" $! s ss js ρ0 with "[//] [//] [//]").
    (* Both: the merged entry has [ss = ss1 ∪ ss2], [js = js1 ∪ js2].  Every
       concrete name / row variable of [ρ0] lands in one of the two summands,
       so freshness of [(δ !!! s)] against [ρ0] is reconstructed element-wise
       from the per-side facts [Hm1] ([Hrow]) and [Hm2] ([HD]). *)
    destruct Hb as ([ss1 js1] & [ss2 js2] & Hlk1 & Hlk2 & Heq).
    simpl in Heq. injection Heq as <- <-.
    iAssert (⌜∀ ρa, le.conc_sigs ρa ⊆ ss1 → le.abst_sigs ρa ⊆ js1 →
      (δ !!! s).1 ∉ row_labels_l ρa ξ δ
      ∧ (δ !!! s).2 ∉ row_labels_r ρa ξ δ⌝)%I as %Hm1.
    { iIntros (ρa Hca Haa).
      iDestruct ("Hrow" $! s ss1 js1 ρa with "[//] [//] [//]")
        as "(_ & _ & %Hfl & %Hfr)".
      iPureIntro; split; assumption. }
    iAssert (⌜∀ ρa, le.conc_sigs ρa ⊆ ss2 → le.abst_sigs ρa ⊆ js2 →
      (δ !!! s).1 ∉ row_labels_l ρa ξ δ
      ∧ (δ !!! s).2 ∉ row_labels_r ρa ξ δ⌝)%I as %Hm2.
    { iIntros (ρa Hca Haa).
      iDestruct ("HD" $! s ss2 js2 ρa with "[//] [//] [//]")
        as "(_ & _ & %Hfl & %Hfr)".
      iPureIntro; split; assumption. }
    (* Ownership does not depend on [ρ0]; read it off [D] at the empty row. *)
    assert (Hc0 : le.conc_sigs RNil ⊆ ss2)
      by (cbn [le.conc_sigs]; multiset_solver).
    assert (Ha0 : le.abst_sigs RNil ⊆ js2)
      by (cbn [le.abst_sigs]; set_solver).
    iDestruct ("HD" $! s ss2 js2 RNil with "[//] [//] [//]")
      as "(#Hown1 & #Hown2 & _)".
    iSplit; [iApply "Hown1"|].
    iSplit; [iApply "Hown2"|].
    iSplit.
    - iPureIntro.
      intros Hin. rewrite row_labels_l_split elem_of_app in Hin.
      destruct Hin as [Hn | Hvr].
      + rewrite /name_labels_l list_elem_of_fmap in Hn.
        destruct Hn as (t & Heqt & Ht). apply gmultiset_elem_of_elements in Ht.
        assert (Htu : t ∈ ss1 ∪ ss2)
          by (eapply gmultiset_elem_of_subseteq; eauto).
        apply gmultiset_elem_of_union in Htu as [Ht1 | Ht2].
        * assert (Hp1 : le.conc_sigs (RCons (SSig t TBot TBot) RNil) ⊆ ss1)
            by (cbn [le.conc_sigs le.eff_name_from_sig]; multiset_solver).
          assert (Hp2 : le.abst_sigs (RCons (SSig t TBot TBot) RNil) ⊆ js1)
            by (cbn [le.abst_sigs]; set_solver).
          destruct (Hm1 _ Hp1 Hp2) as [Hnl _].
          apply Hnl. cbn [row_labels_l le.eff_name_from_sig].
          rewrite Heqt. apply list_elem_of_here.
        * assert (Hp1 : le.conc_sigs (RCons (SSig t TBot TBot) RNil) ⊆ ss2)
            by (cbn [le.conc_sigs le.eff_name_from_sig]; multiset_solver).
          assert (Hp2 : le.abst_sigs (RCons (SSig t TBot TBot) RNil) ⊆ js2)
            by (cbn [le.abst_sigs]; set_solver).
          destruct (Hm2 _ Hp1 Hp2) as [Hnl _].
          apply Hnl. cbn [row_labels_l le.eff_name_from_sig].
          rewrite Heqt. apply list_elem_of_here.
      + destruct (elem_of_var_labels_l_mono ρ0 ρ0 ξ _ (reflexivity _) Hvr)
          as (i & Hi & Hl).
        assert (Hiu : i ∈ js1 ∪ js2) by (eapply elem_of_weaken; eauto).
        apply elem_of_union in Hiu as [Hi1 | Hi2].
        * assert (Hp1 : le.conc_sigs (RVar i) ⊆ ss1)
            by (cbn [le.conc_sigs]; multiset_solver).
          assert (Hp2 : le.abst_sigs (RVar i) ⊆ js1)
            by (cbn [le.abst_sigs]; set_solver).
          destruct (Hm1 _ Hp1 Hp2) as [Hnl _].
          apply Hnl. cbn [row_labels_l]. exact Hl.
        * assert (Hp1 : le.conc_sigs (RVar i) ⊆ ss2)
            by (cbn [le.conc_sigs]; multiset_solver).
          assert (Hp2 : le.abst_sigs (RVar i) ⊆ js2)
            by (cbn [le.abst_sigs]; set_solver).
          destruct (Hm2 _ Hp1 Hp2) as [Hnl _].
          apply Hnl. cbn [row_labels_l]. exact Hl.
    - iPureIntro.
      intros Hin. rewrite row_labels_r_split elem_of_app in Hin.
      destruct Hin as [Hn | Hvr].
      + rewrite /name_labels_r list_elem_of_fmap in Hn.
        destruct Hn as (t & Heqt & Ht). apply gmultiset_elem_of_elements in Ht.
        assert (Htu : t ∈ ss1 ∪ ss2)
          by (eapply gmultiset_elem_of_subseteq; eauto).
        apply gmultiset_elem_of_union in Htu as [Ht1 | Ht2].
        * assert (Hp1 : le.conc_sigs (RCons (SSig t TBot TBot) RNil) ⊆ ss1)
            by (cbn [le.conc_sigs le.eff_name_from_sig]; multiset_solver).
          assert (Hp2 : le.abst_sigs (RCons (SSig t TBot TBot) RNil) ⊆ js1)
            by (cbn [le.abst_sigs]; set_solver).
          destruct (Hm1 _ Hp1 Hp2) as [_ Hnr].
          apply Hnr. cbn [row_labels_r le.eff_name_from_sig].
          rewrite Heqt. apply list_elem_of_here.
        * assert (Hp1 : le.conc_sigs (RCons (SSig t TBot TBot) RNil) ⊆ ss2)
            by (cbn [le.conc_sigs le.eff_name_from_sig]; multiset_solver).
          assert (Hp2 : le.abst_sigs (RCons (SSig t TBot TBot) RNil) ⊆ js2)
            by (cbn [le.abst_sigs]; set_solver).
          destruct (Hm2 _ Hp1 Hp2) as [_ Hnr].
          apply Hnr. cbn [row_labels_r le.eff_name_from_sig].
          rewrite Heqt. apply list_elem_of_here.
      + destruct (elem_of_var_labels_r_mono ρ0 ρ0 ξ _ (reflexivity _) Hvr)
          as (i & Hi & Hl).
        assert (Hiu : i ∈ js1 ∪ js2) by (eapply elem_of_weaken; eauto).
        apply elem_of_union in Hiu as [Hi1 | Hi2].
        * assert (Hp1 : le.conc_sigs (RVar i) ⊆ ss1)
            by (cbn [le.conc_sigs]; multiset_solver).
          assert (Hp2 : le.abst_sigs (RVar i) ⊆ js1)
            by (cbn [le.abst_sigs]; set_solver).
          destruct (Hm1 _ Hp1 Hp2) as [_ Hnr].
          apply Hnr. cbn [row_labels_r]. exact Hl.
        * assert (Hp1 : le.conc_sigs (RVar i) ⊆ ss2)
            by (cbn [le.conc_sigs]; multiset_solver).
          assert (Hp2 : le.abst_sigs (RVar i) ⊆ js2)
            by (cbn [le.abst_sigs]; set_solver).
          destruct (Hm2 _ Hp1 Hp2) as [_ Hnr].
          apply Hnr. cbn [row_labels_r]. exact Hl.
  Qed.

End aux_lemma.

Section compatiblity.
  Context `{!probblazeRGS Σ}.
  
  Lemma sig_le_eff D α α' β β' s : 
   sem_ty_le D α α' -∗ sem_ty_le D β' β -∗ sem_sig_le D (SSig s α β) (SSig s α' β').
  Proof. 
    iIntros "#Hα #Hβ !# %%%% #HD".
    iApply sig_le_eff; iIntros (αs) "!#"; [by iApply "Hα"|by iApply "Hβ"].
  Qed. 
  
  Lemma row_le_RNil D b :
    ⊢ sem_row_le D b RNil RNil.
  Proof. 
    iIntros (????) "!# #He". 
    iSplit; last iApply row_le_refl; by destruct b.
  Qed. 

  Lemma row_le_RVar D b i :
    ⊢ sem_row_le D b (RVar i) (RVar i).
  Proof. 
    iIntros (????) "!# #He". 
    iSplit; last iApply row_le_refl; by destruct b.
  Qed. 

  Lemma row_le_RExtend D b σ ρ : 
    ⊢ sem_row_le D b ρ (RCons σ ρ).
  Proof. 
    iIntros (????) "!# #He". 
    iSplit; last iApply row_le_cons_extend; destruct b; try done; iPureIntro; split;
    solve_submseteq.
  Qed. 

  Lemma row_le_RSwap D b σ σ' ρ :
    ⊢ sem_row_le D b (RCons σ (RCons σ' ρ)) (RCons σ' (RCons σ ρ)).
  Proof. 
    iIntros (????) "!# #He". 
    iSplit.
    - iPureIntro; destruct b; try done; split; solve_submseteq.
    - iApply row_le_swap_second.
  Qed. 

  Lemma row_le_RCons D b σ σ' ρ ρ' :
    sem_sig_le D σ σ' -∗
    sem_row_le D false ρ ρ' -∗
    sem_row_le D b (RCons σ ρ) (RCons σ' ρ').
  Proof. 
    iIntros "#Hsig #Hrow %%%% !# #HD".
    unshelve iDestruct ("Hsig" with "HD") as "(%Hsig&_)"; [done|done|].
    rewrite !sig_labels_eff_name in Hsig. 
    unshelve iDestruct ("Hrow" with "HD") as "(%Hlabel&Hrow')"; [done|done|].
    destruct Hlabel as [Hll Hlr].
    iSplit.
    - iPureIntro; destruct b; try done; split.
      + rewrite //= Hsig; by apply submseteq_skip.
      + rewrite //= Hsig; by apply submseteq_skip.
    - iApply row_le_cons_comp.
      + by rewrite !labels_l_interp_row. 
      + by rewrite !labels_r_interp_row. 
      + by iApply "Hsig".
      + by iApply "Hrow'".
  Qed. 
    
  Lemma row_le_RUnion D b ρ1 ρ2 ρ1' ρ2' :
    sem_row_le D false ρ1 ρ1' -∗
      sem_row_le D false ρ2 ρ2' -∗
      sem_row_le D b (ρ1 ∪ᵣ ρ2)%ty (ρ1' ∪ᵣ ρ2')%ty.
  Proof. 
    iIntros "#Hrow1 #Hrow2 %%%% !# #HD".
    unshelve iDestruct ("Hrow1" with "HD") as "(%Hl1&Hrow1')"; [done|done|].
    destruct Hl1 as [Hll1 Hlr1].
    unshelve iDestruct ("Hrow2" with "HD") as "(%Hl2&Hrow2')"; [done|done|].
    destruct Hl2 as [Hll2 Hlr2].
    iSplit.
    - iPureIntro; destruct b; try done.
      split; simpl; by apply submseteq_app.
    - iApply row_le_union'.
      + by rewrite !labels_l_interp_row. 
      + by rewrite !labels_l_interp_row. 
      + by rewrite !labels_r_interp_row. 
      + by rewrite !labels_r_interp_row. 
      + by iApply "Hrow1'".
      + by iApply "Hrow2'".
  Qed. 

  Lemma row_le_RErase D s ss js ρ :
    ⌜D !! s = Some (ss, js)⌝ -∗
    ⌜le.conc_sigs ρ ⊆ ss⌝ -∗
    ⌜le.abst_sigs ρ ⊆ js⌝ -∗
    sem_row_le D true (RCons (SAbs s) ρ) ρ.
  Proof. 
    iIntros (Hin Hcnc Habs ????) "!# #HD".
    iSplit; first done.
    iDestruct ("HD" $! s ss js ρ with "[//] [//] [//]")
      as "(Hl1 & Hl2 & %Hnl & %Hnr)".
    iApply row_le_erase; by rewrite ?labels_l_interp_row ?labels_r_interp_row.
  Qed. 

  Lemma row_le_RTrans D b ρ1 ρ2 ρ3 :
    sem_row_le D b ρ1 ρ2 -∗
    sem_row_le D b ρ2 ρ3 -∗
    sem_row_le D b ρ1 ρ3.
  Proof. 
    iIntros "#Hrow1 #Hrow2 %%%% !# #HD".
    unshelve iDestruct ("Hrow1" with "HD") as "(%Hl1&Hrow1')"; [done|done|].
    unshelve iDestruct ("Hrow2" with "HD") as "(%Hl2&Hrow2')"; [done|done|].
    iSplit.
    - iPureIntro; destruct b; first done.
      destruct Hl1 as [Hll1 Hlr1].
      destruct Hl2 as [Hll2 Hlr2]. 
      split; by eapply submseteq_trans.
    - by iApply row_le_trans.
  Qed. 

  Lemma row_le_RFlipNil D b m :
    ⊢ sem_row_le D b (¡[ m] RNil) RNil.
  Proof. 
    iIntros (????) "!# #HD".
    iSplit; first (by destruct b).
    iApply row_le_mfbang_elim_nil.
  Qed. 

  Lemma row_le_RFlipCons D b m σ ρ :
    ⊢ sem_row_le D b (¡[ m] (RCons σ ρ)) (RCons (SFlip m σ) (¡[ m] ρ)).
  Proof. 
    iIntros (????) "!# #HD".
    iSplit; first (by destruct b).
    iApply row_le_mfbang_dist_cons.
  Qed. 

  Lemma row_le_RFlipUnion D b m ρ1 ρ2 :
    ⊢ sem_row_le D b (¡[ m] (ρ1 ∪ᵣ ρ2)%ty) (¡[ m] ρ1 ∪ᵣ ¡[ m] ρ2)%ty.
  Proof. 
    iIntros (????) "!# #HD".
    iSplit; first (by destruct b).
    iApply row_le_flip_union.
  Qed. 
  
  Lemma row_le_RFlipElim D b ρ :
    ⊢ sem_row_le D b (¡[ types.MS] ρ) ρ.
  Proof. 
    iIntros (????) "!# #HD".
    iSplit; first (by destruct b).
    iApply row_le_mfbang_elim_ms.
  Qed. 

  Lemma row_le_RFlipIntro D b ρ m :
    ⊢ sem_row_le D b ρ (¡[ m] ρ).
  Proof. 
    iIntros (????) "!# #HD".
    iSplit; first (by destruct b).
    iApply row_le_mfbang_intro.
  Qed. 

  Lemma row_le_RFlipIdemp1 D b ρ m :
    ⊢ sem_row_le D b (¡[ m] (¡[ m] ρ)) (¡[ m] ρ).
  Proof. 
    iIntros (????) "!# #HD".
    iSplit; first (by destruct b).
    iApply row_le_mfbang_idemp.
  Qed. 

  Lemma row_le_RFlipIdemp2 D b ρ m :
    ⊢ sem_row_le D b (¡[ m] ρ) (¡[ m] (¡[ m] ρ)).
  Proof. 
    iIntros (????) "!# #HD".
    iSplit; first (by destruct b).
    iApply row_le_mfbang_intro.
  Qed. 

  Lemma row_le_RFlipComp D b ρ ρ' m m' :
    sem_mode_le m m' -∗
    sem_row_le D b ρ' ρ -∗
    sem_row_le D b (¡[ m'] ρ') (¡[ m] ρ).
  Proof. 
    iIntros "#Hmode #Hrow %%%% !# #HD".
    unshelve iDestruct ("Hrow" with "HD") as "(%Hl&Hrow')"; [done|done|].
    iSplit.
    - iPureIntro; destruct b; first done.
      destruct Hl as [Hll Hlr].
      split; by eapply submseteq_trans.
    - by iApply row_le_mfbang_comp.
  Qed. 

  Lemma ty_le_TArrow D b α α' β β' ρ ρ' :
    let D' := le.update_disj_ctx ρ' D in
    sem_ty_le D' α' α -∗
    sem_ty_le D' β β' -∗
    sem_row_le D' b ρ ρ' -∗
    sem_ty_le D (α -{ ρ }-∘ β) (α' -{ ρ' }-∘ β').
  Proof. 
    iIntros (?) "#Hty1 #Hty2 #Hrow %%%% !# #HD".
    iIntros (??) "!# Hτ1 % % Hα". iApply brel_learn. 
    iIntros "#Hd #Hv".
    iRevert (w1 w2) "Hα".
    iRevert (v1 v2) "Hτ1". 
    iApply bi.intuitionistically_elim.
    iDestruct (arr_extend_D with "[$HD]") as "#HD'".
    iSpecialize ("HD'" with "Hd Hv"). 
    iApply ty_le_arr.
    - iDestruct ("Hrow" with "HD'") as "(_&$)".
    - by iApply "Hty1". 
    - by iApply "Hty2".
  Qed. 

  Lemma ty_le_TForall D α β :
    sem_ty_le D α β -∗
    sem_ty_le D (∀T: α) (∀T: β).
  Proof. 
    iIntros "#Hty %%%% !# #HD"; iApply ty_le_type_forall; iIntros (α'); by iApply "Hty".
  Qed. 

  Lemma ty_le_MForall D α β :
    sem_ty_le D α β -∗
    sem_ty_le D (∀M: α) (∀M: β).
  Proof. 
    iIntros "#Hty %%%% !# #HD"; iApply ty_le_mode_forall; iIntros (m); by iApply "Hty".
  Qed. 

  Lemma ty_le_TBangNat D m :
     ⊢ sem_ty_le D ℕ (![ m] ℕ).
  Proof. 
    iIntros (????) "!# #HD".
    iIntros "!#" (v1 v2) "#Hnat". rewrite /sem_ty_mbang.
    iApply bi.intuitionistically_intuitionistically_if. by iModIntro.
  Qed. 

  Lemma ty_le_TNat_TInt D :
    ⊢ sem_ty_le D ℕ ℤ.
  Proof. 
    iIntros (????) "!# #HD".
    iIntros "!#" (v1 v2) "Hnat". iDestruct "Hnat" as (n) "[-> ->]".
    by iExists (Z.of_nat n). 
  Qed. 

End compatiblity.

Section fundamental_subtyping.
  Context `{!probblazeRGS Σ}. 

  Theorem fundamental_mode (m m' : vmode) :
    (⊢ₗ m ≤M m') → ⊢ @sem_mode_le Σ m m'.
  Proof.
    intros Hm. induction Hm; iIntros "!# %". 
    - iApply mode_le_OS.
    - iApply mode_le_MS.
    - iApply mode_le_trans.
      + iApply IHHm1.
      + iApply IHHm2.
    - iApply mode_le_refl.
  Qed.


  Theorem fundamental_sig D σ σ' :
    D ⊢ₗ σ ≤S σ' → ⊢ sem_sig_le D σ σ'
    with fundamental_row D ρ ρ' b :
      D ⊢ₗ ρ ≤R ρ' @ b → ⊢ sem_row_le D b ρ ρ'
      with fundamental_type D α β :
        D ⊢ₗ α ≤T β → ⊢ sem_ty_le D α β.
  Proof. 
    - induction 1; iIntros (????) "!# He".
      + iApply sig_le_eff; last done; by iApply fundamental_type. 
      + iApply sig_le_mfbang_intro.
      + iApply sig_le_mfbang_elim_ms.
      + iApply sig_le_mfbang_idemp.
      + iApply sig_le_mfbang_intro.
      + iApply sig_le_mfbang_comp. 
        * by iApply fundamental_mode. 
        * by iApply fundamental_sig.
    - induction 1. 
      + iApply row_le_RNil. 
      + iApply row_le_RVar.
      + iApply row_le_RExtend.
      + iApply row_le_RSwap.
      + iApply row_le_RCons.
        * by iApply fundamental_sig.
        * by iApply fundamental_row.
      + iApply row_le_RUnion; by iApply fundamental_row.
      + by iApply row_le_RErase. 
      + iApply row_le_RTrans; by iApply fundamental_row.
      + iApply row_le_RFlipNil.
      + iApply row_le_RFlipCons.
      + iApply row_le_RFlipUnion.
      + iApply row_le_RFlipElim.
      + iApply row_le_RFlipIntro.
      + iApply row_le_RFlipIdemp1.
      + iApply row_le_RFlipIdemp2.
      + iApply row_le_RFlipComp.
        * by iApply fundamental_mode.
        * by iApply fundamental_row.
    - induction 1.  
      + iIntros (????) "!# #HD"; iApply ty_le_refl.
      + iIntros (????) "!# #HD"; iApply ty_le_trans; by iApply fundamental_type.
      + iIntros (????) "!# #HD"; iApply ty_le_bot.
      + by iIntros (????) "!# #HD !# % % _".
      + by iApply ty_le_TArrow; last by iApply fundamental_row. 
      + iIntros (????) "!# #HD"; iApply ty_le_ref; by iApply fundamental_type.
      + by iApply ty_le_TForall.
      + by iApply ty_le_MForall.
      + iIntros (????) "!# #HD"; iApply ty_le_prod; by iApply fundamental_type.
      + iIntros (????) "!# #HD"; iApply ty_le_sum; by iApply fundamental_type.
      + iIntros (????) "!# #HD"; iApply ty_le_mbang_intro_bool.
      + iIntros (????) "!# #HD"; iApply ty_le_mbang_intro_unit.
      + iIntros (????) "!# #HD"; iApply ty_le_mbang_intro_int.
      + iApply ty_le_TBangNat.
      + iIntros (????) "!# #HD"; iApply ty_le_mbang_intro_top.
      + iIntros (????) "!# #HD"; iApply ty_le_mbang_intro_os.
      + iIntros (????) "!# #HD"; iApply ty_le_mbang_idemp.
      + iIntros (????) "!# #HD"; iApply ty_le_mbang_elim.
      + iIntros (????) "!# #HD"; iApply ty_le_mbang_elim.
      + iIntros (????) "!# #HD"; iApply ty_le_mbang_comp.
        * by iApply fundamental_mode.
        * by iApply fundamental_type.
      + iIntros (????) "!# #HD"; iApply ty_le_type_forall_mbang.
      + iIntros (????) "!# #HD"; iApply ty_le_mbang_type_forall.
      + iIntros (????) "!# #HD"; iApply ty_le_row_forall_mbang.
      + iIntros (????) "!# #HD"; iApply ty_le_mbang_row_forall.
      + iApply ty_le_TNat_TInt.
  Qed. 
  
  Lemma multi_ty_sound (τ : type) :
    le.MultiT τ → ∀ η μ δ ξ, MultiT (interp._ty η μ δ τ ξ).
  Proof.
    intros H ????. unfold le.MultiT in H. eapply fundamental_type in H.
    constructor.
    iApply H. iApply erase_ctx_empty.
  Qed.

  (* Soundness of [le.MultiC]: a syntactically multi context interprets to
     a semantic [MultiE].  Forall-lift of [multi_ty_sound]. *)
  Lemma multi_env_sound (Γ : ctx) :
    le.MultiC Γ → ∀ η μ δ ξ, MultiE (interp._env η μ δ ξ Γ).
  Proof.
    intros Hm η μ δ ξ. induction Γ as [|[x τ] Γ' IH]; simpl.
    - apply multi_env_nil.
    - apply Forall_cons in Hm as [Hτ HΓ'].
      apply multi_env_cons; first by apply IH.
      by apply multi_ty_sound.
  Qed.

  (* Soundness of [le._mode_type]: note [m m⪯T τ] forces [m ∈ {OS, MS}]. *)
  Lemma mode_type_sound (m : vmode) (τ : type) :
    m m⪯T τ → ∀ η μ δ ξ, (interp._mode μ m) ₘ⪯ₜ (interp._ty η μ δ τ ξ).
  Proof.
    intros Hm η μ δ ξ. inv Hm; simpl.
    - apply mode_type_sub_os.
    - apply mode_type_sub_multi_ty. by apply multi_ty_sound.
  Qed.

  (* Soundness of [le._mode_ctx]: a syntactic mode-context judgement
     interprets to a semantic mode-env-subtyping. *)
  Lemma mode_env_sound (m : vmode) (Γ : ctx) :
    m m⪯C Γ → ∀ η μ δ ξ, (interp._mode μ m) ₘ⪯ₑ (interp._env η μ δ ξ Γ).
  Proof.
    intros Hm η μ δ ξ. induction Hm as [m'|m' x τ Γ' Hτ HΓ' IH]; simpl.
    - apply mode_env_sub_nil.
    - destruct x as [|s]; simpl.
      + apply IH.
      + apply mode_env_sub_cons; first apply IH.
        by apply mode_type_sound.
  Qed.

  Lemma once_row_sound (ρ : row) :
    le.OnceR ρ → ∀ η μ δ ξ, OnceR (interp._row η μ δ ρ ξ).
  Proof.
    intros [b0 Hle] η0 μ0 ξ0. constructor.
    iPoseProof (fundamental_row _ _ _ _ Hle) as "H".
    iPoseProof erase_ctx_empty as "Hctx".
    iDestruct ("H" with "Hctx") as "(_&$)".
  Qed.

  (* Soundness of [le._row_type]: turns [ρ R⪯T τ] into the semantic         *)
  (* [RowTypeSub] typeclass.  The [Multi_le] case is fully proved (via      *)
  (* [multi_ty_sound] + the existing [row_type_sub_multi_ty] instance); the *)
  (* [Once_le] case is sound modulo [once_row_sound] above. *)
  Lemma row_type_sub_sound (ρ : row) (τ : type) :
    ρ R⪯T τ → ∀ η μ δ ξ,
        RowTypeSub (interp._row η μ δ ρ ξ) (interp._ty η μ δ τ ξ).
  Proof.
    intros Hsub η0 μ0 δ0 ξ0. destruct Hsub as [ρ' τ' Honce | ρ' τ' Hmulti].
    - apply row_type_sub_once.
      by apply (once_row_sound _ Honce).
    - pose proof (multi_ty_sound _ Hmulti η0 μ0 δ0 ξ0) as Hm.
      by apply row_type_sub_multi_ty.
  Qed.

  (* Soundness of [le._row_ctx]: turns [ρ R⪯C Γ] into the semantic          *)
  (* [RowEnvSub] typeclass.  Mirrors [mode_env_sound]: induction on the     *)
  (* derivation, [Nil] via [row_env_sub_nil], [Cons] via [row_env_sub_cons] *)
  (* fed by [row_type_sub_sound].  The [BAnon] binder leaves [Γ] unchanged. *)
  Lemma row_env_sub_sound (ρ : row) (Γ : ctx) :
    ρ R⪯C Γ → ∀ η μ δ ξ,
        RowEnvSub (interp._row η μ δ ρ ξ) (interp._env η μ δ ξ Γ).
  Proof.
    intros Hsub η0 μ0 δ0 ξ0.
    induction Hsub as [ρ'|ρ' x τ Γ' Hτ HΓ' IH]; simpl.
    - apply row_env_sub_nil.
    - destruct x as [|s]; simpl.
      + apply IH.
      + apply row_env_sub_cons; first apply IH.
        by apply (row_type_sub_sound _ _ Hτ).
  Qed.

  (* Soundness of context subtyping [le._ctx].  The syntactic [D ⊢ₗ Γ ≤C Γ']
     interprets to an [env_le] between the pointwise-interpreted contexts.
     [le._ctx] recurses on [Γ'], so we induct on [Γ']: the [[]] case is the
     unconditional [env_le_nil]; the cons case uses [env_le_bring_forth] to
     surface the matched entry [(x,t')] out of [Γ = pre ++ (x,t') :: post],
     [env_le_cons] with [ty_le_sound] on the head and the IH on the tail
     (both under the [erase_ctx] bundle), combined by [env_le_trans]. *)
  Lemma ctx_le_sound (D : le.disj_ctx) (Γ Γ' : ctx) :
    D ⊢ₗ Γ ≤C Γ' → ⊢ sem_env_le D Γ Γ'.
  Proof.
    revert Γ. induction Γ' as [|[x t] Γ'_tail IH];
      iIntros (Γ Hle) "!# %%%% #HD".
    - iApply env_le_nil.
    - simpl in Hle.
      destruct Hle as (t' & pre & post & -> & Ht & Htail).
      (* [(x,t')] sits at position [length pre] in the interpreted [Γ]. *)
      assert (Hnth : nth_error ((λ '(s, τ), (s, interp._ty η μ δ τ ξ))
                                  <$> (pre ++ (x, t') :: post))
                       (length pre) = Some (x, interp._ty η μ δ t' ξ)).
      { rewrite fmap_app /=. rewrite (nth_error_app2 _ _ (n := length pre)).
        { rewrite length_fmap Nat.sub_diag //. }
        rewrite length_fmap //. }
      (* Deleting it leaves the interpretation of [pre ++ post]. *)
      assert (Hdel : list_delete (length pre)
                       ((λ '(s, τ), (s, interp._ty η μ δ τ ξ))
                          <$> (pre ++ (x, t') :: post))
                     = (λ '(s, τ), (s, interp._ty η μ δ τ ξ)) <$> (pre ++ post)).
      { rewrite !fmap_app /=.
        rewrite -(length_fmap (λ '(s, τ), (s, interp._ty η μ δ τ ξ)) pre).
        apply delete_middle. }
      simpl.
      iApply (env_le_trans _ ((x, interp._ty η μ δ t' ξ)
                                :: ((λ '(s, τ), (s, interp._ty η μ δ τ ξ)) <$> (pre ++ post)))).
      + rewrite -Hdel.
        iApply (env_le_bring_forth _ (length pre) x (interp._ty η μ δ t' ξ) Hnth).
      + iApply env_le_cons.
        * iApply (IH _ Htail with "HD").
        * by iApply fundamental_type.  
  Qed.

End fundamental_subtyping.

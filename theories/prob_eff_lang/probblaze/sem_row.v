
(* sem_row.v *)

(* This file contains the definition of semantic rows. *)

From iris.proofmode Require Import base proofmode.
From iris.algebra Require Import ofe gmap.
From iris.base_logic Require Export iprop upred invariants.

(* Local imports *)
From clutch.prob_eff_lang.probblaze Require Import logic notation sem_def mode sem_sig.

(* Nil Row *)
Program Definition sem_row_nil {Σ} : sem_row Σ := @SemRow Σ ⊥ _ (* _ *). 
Next Obligation. iIntros (?????) "?". iIntros (???) "(%Hcontra & _)". by apply elem_of_nil in Hcontra. Qed.
(* Next Obligation. iIntros (????) "(%l1 & %l2 & %X & %Hcontra & ?)". by apply elem_of_nil in Hcontra. Qed. *)

Global Instance sem_row_bottom {Σ} : Bottom (sem_row Σ) := sem_row_nil.

(* Cons Row *)
Program Definition sem_row_cons {Σ} : sem_sig Σ -d> sem_row Σ -d> sem_row Σ :=
    λ σ ρ, 
      (@SemRow Σ ((([(sem_sig_labels Σ σ).1], [(sem_sig_labels Σ σ).2]), sem_sig_later σ) :: (sem_row_car ρ)) _ (* _ *) ) .
              (* (λ e1 e2, λne Φ, ∃ (op' : label) (v1 v2 : val), 
                              ⌜ e1 = (do: op' v1)%E ⌝ ∗ ⌜ e2 = (do: op' v2)%E ⌝ ∗
                               if decide (op = op') then 
                                 ▷ ((pmono_prot_car σ) v1 v2 Φ)
                               else
                                 (pmono_prot_car (sem_row_car ρ)) (do: op' v1)%E (do: op' v2)%E Φ)%I) _). *)
Next Obligation.
  intros ???. iIntros (????) "#H1 % % % (%Hin & H2)". iSplit; first done.
  iDestruct "H2" as "(%&%&%&%&%&->&%&->&%&Hσ&#Hcont)".
  iExists _,_,_,_,_. repeat (iSplit; first done).
  iIntros (??) "!# HS". iApply "H1". by iApply "Hcont".
Qed. 
(* Next Obligation.
     iIntros (????????) "H". 
     iDestruct (to_iThy_cons with "H") as "H". 
     iDestruct "H" as "[(%&%&%&%&%&->&%&->&%&Hσ&#Hcont)|(%&%&%&%&%&%&%&%&%&->&%&->&%&Hσ&#Hcont)]".
     - destruct σ. iDestruct sem_sig_prop as "H1". iExists _, _, op1, op2.
       
       iDestruct ("H1" with "Hσ") as "H". d
       iDestruct ("H1" with "Hσ") as (??) "H". iExists op0, op3, v1,v2.
       iDestruct "H" as "(-> & ->)". done.
     - apply in_iLblSig in H as (X' & ->).
       iDestruct (sem_sig_prop with "Hσ") as (op3 op4 v1 v2) "(-> & ->)".
       iExists _,_,_,_,_,_. done.
   Qed. *)

#[refine] Definition sem_row_later {Σ} (ρ : sem_row Σ) : sem_row Σ :=
  @SemRow Σ (map (λ '((ls1, ls2), σ), (ls1, ls2, sem_sig_later σ)) (sem_row_car ρ)) _.
Proof.
  iIntros (????) "#HPP %%% (%&HX)".
  iSplit; [done|]. 
  iDestruct "HX" as "(%&%&%&%&%&->&%&->&%&HX&#Hcont)".
  iExists _,_,_,_,_. repeat (iSplit; first done).
  iIntros (??) "!# HS". iApply "HPP". by iApply "Hcont".
Defined.

Lemma iLblSig_to_iLblThy_nil {Σ}: 
  @iLblSig_to_iLblThy Σ [] = []. 
Proof.
  done.
Qed. 

Lemma map_list_contractive {A B : ofe} (f : A → B) : Contractive f → Contractive (map f).
Proof.
  intros Hf ? l k Hlk. apply list_dist_Forall2.
  apply Forall2_fmap_2. generalize dependent k. induction l; intros k Hlk.
  - destruct k.
    + done.
    + destruct n.
      * admit.
      * assert (n < S n) as Hlt by lia.
        apply Hlk in Hlt. inversion Hlt.
  - destruct k. 
    + destruct n.
      * admit.
      * assert (n < S n) as Hlt by lia.
        apply Hlk in Hlt. inversion Hlt.
    + apply Forall2_cons_2.
      * f_contractive. by inversion Hlk.
      * apply IHl. inversion Hlk. 
        constructor. intros m Hm. 
        apply dist_later_lt in Hm. by inversion Hm.
Admitted.


Program Definition iThy_later {Σ} : iThy Σ -n> iThy Σ := λne T, λ e e', λne ψ, (▷ T e e' ψ)%I.
Next Obligation.
  intros. intros ψ ψ' Hne. rewrite Hne. done.
Qed.
Next Obligation.
  intros. intros T T' Hne. intros e e' ψ.
  simpl. by rewrite (Hne e e' ψ).
Qed.

Instance iThy_later_contractive {Σ} : Contractive (@iThy_later Σ).
Proof.
  unfold iThy_later. simpl.
  intros ? T T' ?.
  intros e e' ?. simpl.
  f_contractive.
  rewrite (H e e' _).
  done.
Qed.

(* Definition sem_sig_later {Σ} : sem_sig Σ -n> sem_sig Σ.
   Proof.
     unshelve econstructor.
     - intros []. unshelve econstructor.
       + destruct sem_sig_car.
         exists (iThy_later pmono_prot_car).
         rewrite /pers_mono.
         iIntros (????) "#H H'".
         rewrite /iThy_later. simpl. iNext.
         iApply pmono_prot_prop => //.
       + exact sem_sig_labels.
       + destruct sem_sig_car.
         iIntros "?".

   Next Obligation.
     intros. intros ψ ψ' Hne. rewrite Hne. done.
   Qed.
   Next Obligation.
     intros. intros T T' Hne. intros e e' ψ.
     simpl. by rewrite (Hne e e' ψ).
   Qed. *)


(* Definition sem_row_rec1 {Σ} (R : sem_row Σ → sem_row Σ) (rec : sem_row Σ) : sem_row Σ.
     (* morally: ▷ (R rec)) *)
     unshelve econstructor.
     -
       set (X := R rec).
       set (X_sig := sem_row_car X).
       opose proof (sem_row_car X) as X_sig'.
       rewrite /iLblSig in X_sig'.
       assert (sem_sig Σ → sem_sig Σ).
       {
         clear.
         refine ((λ sg, _)).
         destruct sg.
         destruct sem_sig_car.
         assert (iThy Σ).
         {
           intros e e'. unshelve refine (λne ψ, _)%I.
           1: exact (▷ ψ e e')%I. Show Proof.

           intros. intros ???.

   (* Unset Printing Notations.
      Set Printing All. *)
   unfold dist in H.
   unfold discrete_funO in H.
   unfold discrete_fun in H. unfold ofe_dist in H.
   unfold discrete_fun_dist in H.
   unfold dist in H.
   unfold discrete_funO in H.
   unfold discrete_fun in H. unfold ofe_dist in H.
   unfold discrete_fun_dist in H.
   unfold ofe_dist in H.
   unfold reverse_coercion in H.
   unfold ofe_dist in H.
   rewrite H.
    done.
   Show Proof.
         }
         set (pmono_prot_car_later' := (λ e e' φ, ▷ (φ e e'))%I :
                expr -d> expr -d> (expr -d> expr -d> iProp Σ) -d> iProp Σ).
         assert (Contractive pmono_prot_car_later').
         { subst pmono_prot_car_later'. simpl. solve_contractive. }
         set (sem_sig_car_later := {| pmono_prot_car := pmono_prot_car_later' ;
                                     pmono_prot_prop := pmono_prot_prop |}).
         eexists {| sem_sig_car :=  |}.
       }
       set (sig_later :=
              (λ '(lbls, lbls', sig), (sem_sig_prop _ sig))%I
              : (list label * list label * sem_sig Σ) -> _).
       set (x := later <$> )
     fixpoint R. *)

Program Definition iThy_later {Σ} (X : iThy Σ) : iThy Σ := (λ e1 e2, λne Q, ▷ X e1 e2 Q)%I.
Next Obligation. solve_proper. Qed.

Global Instance iThy_later_contractive {Σ} : Contractive (@iThy_later Σ).
Admitted.

Definition iLblThy_later {Σ} (L : iLblThy Σ) : iLblThy Σ := map (λ '((ls1,ls2), X), ((ls1, ls2), iThy_later X)) L.

Lemma sem_row_later_iLblThy_later {Σ} ρ : iLblSig_to_iLblThy (sem_row_later ρ) = @iLblThy_later Σ (iLblSig_to_iLblThy ρ).
Proof.
  destruct ρ. 
  induction sem_row_car.
  - done.
  - simpl. destruct a as ((ls1,ls2), σ).
    unfold sem_sig_later. 
Admitted.

Global Instance iLblSig_to_iLblThy_ne {Σ} : NonExpansive (@iLblSig_to_iLblThy Σ).
Admitted.

Global Instance sem_row_later_contractive {Σ} : Contractive (@sem_row_later Σ). 
Proof. 
  (* intros n l k Hdist . unfold sem_rowO. simpl. unfold ofe_dist. unfold sem_row_dist. simpl.
     destruct l, k. unfold dist. rewrite !sem_row_later_iLblThy_later.
     apply map_list_contractive.
     - intros ????. destruct x as ((xs1 & xs2) & X). 
       destruct y as ((ys1&ys2) &Y). f_equiv.
       + admit.
       + f_contractive. by destruct H. 
     - apply Build_dist_later. intros m Hm.
       f_equiv. by apply Hdist. *)
Admitted. 

Definition sem_row_rec_pre {Σ} (R : sem_row Σ -n> sem_row Σ) (ρ : sem_row Σ) : sem_row Σ :=
  sem_row_later (R ρ).
Global Instance sem_row_rec_pre_contractive {Σ} (R : sem_row Σ -n> sem_row Σ) : Contractive (sem_row_rec_pre R).
Proof.
  intros ??? Hdist. apply sem_row_later_contractive. 
  apply ne_dist_later; last done. solve_proper.
Qed.

Definition sem_row_rec' {Σ} (R : sem_row Σ -n> sem_row Σ) : sem_row Σ := fixpoint (sem_row_rec_pre R).

Global Instance sem_row_rec_pre_ne {Σ} : ∀ n, Proper (@dist _ _ ofe_mor_dist n ==> @dist _ _ discrete_fun_dist n) (@sem_row_rec_pre Σ).
Proof.
  solve_proper.
Qed.

(* Recursive Row *)
Definition sem_row_rec {Σ} (R : sem_row Σ → sem_row Σ) `{Contractive R} : sem_row Σ :=
  fixpoint R.

Lemma sem_row_rec_unfold {Σ} (R : sem_row Σ → sem_row Σ) `{Contractive R} :
  sem_row_rec R ≡ R (sem_row_rec R).
Proof. rewrite /sem_row_rec {1} fixpoint_unfold //. Qed.

(* Lemma sem_row_rec_unfold_iThy {Σ} (R : sem_row Σ → sem_row Σ) `{Contractive R} e1 e2 Φ:
     pmono_prot_car (sem_row_car (sem_row_rec R)) e1 e2 Φ ≡ pmono_prot_car (sem_row_car (R (sem_row_rec R))) e1 e2 Φ.
   Proof. f_equiv. apply non_dep_fun_equiv.  apply non_dep_fun_equiv. rewrite {1}sem_row_rec_unfold //. Qed. *)

(* Flip-Bang Row *)
(* This is essentially to_iThyIfMono *)
Definition iThyIfMono_iLblSig {Σ} (m: mode) (L : iLblSig Σ) : iLblSig Σ :=
  (map (λ '(l1s, l2s, X), (l1s, l2s, sem_sig_flip_mbang m X)) L).
  
Program Definition sem_row_flip_mbang {Σ} (m : mode) (ρ : sem_row Σ) : sem_row Σ := 
  @SemRow Σ (iThyIfMono_iLblSig m ρ) _ (* _ *).
Next Obligation.
  iIntros (???????) "#HΦ".
  iIntros (???) "($ & H2)".
  iDestruct "H2" as "(%&%&%&%&%&->&%&->&%&Hσ&#Hcont)".
  iExists _,_,_,_,_. repeat (iSplit; first done).
  iIntros (??) "!# HS". iApply "HΦ". by iApply "Hcont".
Qed.
(* Next Obligation.
     iIntros (??????) "Hρ".
     simpl. iDestruct "Hρ" as (????????? -> ? -> ?) "(HX & #Hcont)".
     apply in_iLblSig in H as (X' & ->).
     iDestruct (sem_sig_prop with "HX") as (op3 op4 v1 v2) "(-> & ->)".
     iExists _,_,_,_,_,_. done.
   Qed. *)
(* Notations. *)
Notation "⟨⟩" := (sem_row_nil) : sem_row_scope.
Notation "σ · ρ" := (sem_row_cons (* opσ.1.1 opσ.1.2 *) σ ρ) (at level 80, right associativity) : sem_row_scope.
Notation "¡[ m ] ρ" := (sem_row_flip_mbang m ρ) (at level 10) : sem_row_scope.
Notation "¡ ρ" := (sem_row_flip_mbang OS ρ) (at level 10) : sem_row_scope.
Notation "'μᵣ' θ , ρ " := (sem_row_rec (λ θ, ρ%R)) (at level 50) : sem_row_scope.

Section row_properties.
  (* TODO: finish proofs in this section *)
  Global Instance sem_row_cons_ne {Σ} (* op op' *) : NonExpansive2 (@sem_row_cons Σ (* op op' *)).
  Proof. 
  (*   intros ???????. f_equiv. apply non_dep_fun_dist.
       simpl. do 2 f_equiv; apply non_dep_fun_dist; by f_equiv.  
     Qed. *)
  Admitted. 
  Global Instance sem_row_cons_Proper {Σ} (* op op' *): Proper ((≡) ==> (≡) ==> (≡)) (@sem_row_cons Σ (* op op' *)).
  Proof. apply ne_proper_2. apply _. Qed.
  
  Global Instance sem_row_cons_contractive {Σ} (* op *) n : Proper (dist_later n ==> dist n ==> dist n) (@sem_row_cons Σ (* op *)).
  Proof. 
    intros ??????. rewrite /sem_row_cons. 
    (* intros ???????. rewrite /sem_row_cons. 
       intros ?. simpl. do 6 f_equiv; first f_contractive; f_equiv; apply non_dep_fun_dist; by f_equiv. *)
  Admitted.
  Global Instance sem_row_flip_mbang_ne {Σ} m : NonExpansive (@sem_row_flip_mbang Σ m).
  (* Proof. intros ?????. rewrite /sem_row_flip_mbang. intros ?. simpl. 
            do 2 f_equiv. apply non_dep_fun_dist; by f_equiv. Qed. *)
  Admitted.
  Global Instance sem_row_flip_bang_Proper {Σ} m : Proper ((≡) ==> (≡)) (@sem_row_flip_mbang Σ m).
  Proof. apply ne_proper. apply _. Qed.
  
  Global Instance sem_row_flip_mbang_rec_contractive {Σ} m (R : sem_row Σ -d> sem_row Σ) `{Contractive R} : 
    Contractive (λ θ, sem_row_flip_mbang m (R θ)).
  Proof.
  (*   intros ??????. rewrite /sem_row_flip_mbang. simpl.
       do 4 f_equiv. apply non_dep_fun_dist. by apply Contractive0.
     Qed.  *)
  Admitted. 
    
End row_properties.

Section once_row.

  (* Once Constraint *)
  
  Class OnceR `{probblazeRGS Σ} (ρ : sem_row Σ) := {
    row_le_mfbang_elim : (⊢ (¡ ρ%R) ≤ᵣ ρ%R)
  }.

  
  Lemma iThyIfMono_iLblSig_to_iThyIfMono {Σ} (m : mode) (ρ : sem_row Σ) :
    iLblSig_to_iLblThy (sem_row_flip_mbang m ρ) = to_iThyIfMono m (iLblSig_to_iLblThy ρ).
  Proof.
    unfold iLblSig_to_iLblThy.
    destruct ρ as [l Hmono Hprop].
    induction l; first done. 
    simpl. destruct a as [[l1s l2s] σ]. rewrite IHl; last done.
    - iIntros (????) "#H1 % % % (%Hin & H2)". iSplit; first done.
      iPoseProof Hmono as "Hmcons".
      iDestruct ("Hmcons" $! v1 v2 Φ Φ' with "H1") as "HΨ".
      iAssert (⌜(l1s0, l2s0, X) ∈ iLblSig_to_iLblThy ((l1s, l2s, σ) :: l)⌝ ∗ iThyTraverse l1s0 l2s0 X v1 v2 Φ)%I with "[H2]" as "Htemp".
      { iSplit; last done. iPureIntro. by apply list_elem_of_further. }
      iDestruct ("HΨ" with "Htemp") as "(% & $)".
    (* - iIntros (???) "HΦ".
         iPoseProof Hprop as "Hprop". 
         iAssert (to_iThy (iLblSig_to_iLblThy ((l1s, l2s, σ) :: l)) e1 e2 Φ) with "[HΦ]" as "HΦ".
         { iDestruct "HΦ" as (????) "HΦ". iExists _,_,_. iSplit; [iPureIntro; by apply list_elem_of_further |done]. }
         iDestruct ("Hprop" with "HΦ") as "HΦ". done. *)
  Qed. 

  Definition mono_prot_on_prop {Σ} (Ψ : sem_row Σ) (P : iProp Σ) : iProp Σ :=
    □ (∀ e1 e2 Φ, (to_iThy (iLblSig_to_iLblThy Ψ)) e1 e2 Φ -∗ P -∗ (to_iThy (iLblSig_to_iLblThy Ψ)) e1 e2 (λ w1 w2, Φ w1 w2 ∗ P))%I.

  Lemma mono_prot_on_prop_monotonic {Σ} (σ : sem_row Σ) : 
    (⊢ ∀ P, mono_prot_on_prop σ P) ↔ MonoProt (to_iThy (iLblSig_to_iLblThy σ)).
  Proof.
    split.
    - iIntros (H). constructor. iIntros (v1 v2 Φ Φ') "Hpost HΨ".
      iDestruct (H with "HΨ Hpost") as "H".
      iDestruct "H" as (????) "H".
      iDestruct (sem_row_mono with "[] [H]") as "H"; try by iFrame.
      iIntros "!# % % [HΦ HPost]". by iApply "HPost".
    - iIntros (H) "%P %v1 %v2 %Φ !# Hσ HP". inv H.
      iApply (monotonic_prot with "[HP] Hσ"). iIntros (??) "$ //".
  Qed.

  Global Instance monoprot_once `{probblazeRGS Σ} (ρ : sem_row Σ) `{! OnceR ρ } : MonoProt (to_iThy (iLblSig_to_iLblThy ρ)).
  Proof.
    apply mono_prot_on_prop_monotonic. iIntros (????) "!# HΨ HP".
    inv OnceR0. iDestruct row_le_mfbang_elim0 as "(H1 & H2)".
    iApply "H1".
    rewrite (iThyIfMono_iLblSig_to_iThyIfMono OS).
    iApply iThy_le_to_iThy_to_iThyIfMono.
    iFrame. iIntros "!> %% $".
  Qed.
End once_row.

Section row_sub_typing.
  Context `{probblazeRGS Σ}.
  (* Subtyping on Rows *)
  
  Lemma row_le_refl (ρ : sem_row Σ) :
    ⊢ ρ ≤ᵣ ρ.
  Proof. iApply to_iThy_le_refl. Qed.
  
  Lemma row_le_trans (ρ₁ ρ₂ ρ₃ : sem_row Σ) :
    ρ₁ ≤ᵣ ρ₂ -∗ 
    ρ₂ ≤ᵣ ρ₃ -∗
    ρ₁ ≤ᵣ ρ₃.
  Proof. iApply to_iThy_le_trans. Qed.
  
  Lemma row_le_nil (ρ : sem_row Σ) : 
    ⊢ ⟨⟩ ≤ᵣ ρ.
  Proof. iApply to_iThy_le_bot. Qed.

  Lemma valid_cons_singleton (* (op1 op2 : label)  *)(σ : sem_sig Σ) (ρ : sem_row Σ) :
    ⊢  logic.valid (iLblSig_to_iLblThy (sem_row_cons (* op1 op2 *) σ ρ)) ∗-∗ is_label (sem_sig_labels Σ σ).1 DfracDiscarded ∗ spec_labels_frag (sem_sig_labels Σ σ).2 DfracDiscarded ∗ (logic.valid (iLblSig_to_iLblThy ρ)).
  Proof.                                                                                    
    iSplit.
    - iIntros "#Hvalid".
      unfold logic.valid. simpl.
      repeat iSplit.
      3 : iApply valid_l_submseteq; last iDestruct "Hvalid" as "($&_)"; rewrite labels_l_cons; apply submseteq_cons; done.
      3 : iApply valid_r_submseteq; last iDestruct "Hvalid" as "(_&$)"; rewrite labels_r_cons; apply submseteq_cons; done.
      + iDestruct "Hvalid" as "(Hl & _)". unfold valid_l. simpl. iDestruct "Hl" as "($&_)".
      + iDestruct "Hvalid" as "(_ & Hr)". unfold valid_r. simpl. iDestruct "Hr" as "($&_)".
    - iIntros "(#Hl1 & #Hl2 & #(Hvalidl & Hvalidr))".
      iFrame "#". simpl. done.
  Qed. 

  (* additional assumptions required analogously to the boolean in TES *)
  (* row_le(false) adds the first two assumptions in the semantic model  *)
  (* the justification is that the only way to add signatures to the left is by using the ERASE rule (adding ⊥) *)
  (* but then you can't use the cons rule afterwards (due to the boolean flag) *)
  Lemma row_le_cons_comp (ρ ρ' : sem_row Σ) (* (op op' : label)  *)(σ σ' : sem_sig Σ) :
    labels_l (iLblSig_to_iLblThy ρ) ⊆+ labels_l (iLblSig_to_iLblThy ρ') →
    labels_r (iLblSig_to_iLblThy ρ) ⊆+ labels_r (iLblSig_to_iLblThy ρ') →
    σ ≤ₛ σ' -∗ ρ ≤ᵣ ρ' -∗ sem_row_cons (* op op' *) σ ρ ≤ᵣ sem_row_cons (* op op' *) σ' ρ'.
  Proof.
    unfold row_le; unfold sem_row_cons. simpl.
    iIntros "%Hsub %Hsub' #(%Hlabels&Hσσ') #Hρρ'". rewrite Hlabels.
    iSplit; last iSplit.
    { iApply iThy_le_trans; first iApply iThy_le_to_iThy_sum.
      iApply iThy_le_trans; last iApply iThy_le_sum_to_iThy.
      iApply iThy_le_sum_map; last (iDestruct "Hρρ'" as "($&_)"). 
      iIntros (???) "!# (%&%&%&%&%&$&$&$&$&(%&%&%Heq1&%Heq2&Hσ)&$)". iExists _,_. rewrite -Hlabels. do 2 (iSplit; [done|]). by iApply "Hσσ'". }
    { iModIntro. iApply valid_submseteq'; by constructor. }
    { iIntros "!# %Hd"; iPureIntro. eapply distinct_submseteq'; last done; by constructor. }
  Qed. 
 
  (* Lemma row_le_erase (op1 op2 : label) (ρ : sem_row Σ) :
       op1 ∉ labels_l (iLblSig_to_iLblThy ρ) →
       op2 ∉ labels_r (iLblSig_to_iLblThy ρ) → 
       ⊢ sem_row_cons op1 op2 ⊥ ρ ≤ᵣ ρ.
     Proof.
       iIntros (Hl Hr).
       unfold row_le. simpl.
       iSplit; last iSplit.
       - iApply iThy_le_trans; first iApply iThy_le_to_iThy_sum.
         iApply iThy_le_trans; last iApply iThy_le_sum_bot_l.
         iApply iThy_le_sum_l.
         iIntros (???) "!# (%&%&%&%&%&%&%&%&%&(%&%&%&%&%&$&H')&H)". 
       - iModIntro. iApply valid_submseteq'.
         + unfold labels_l. simpl. *)
      
  
  Lemma row_le_swap_second (σ σ' : sem_sig Σ) (ρ : sem_row Σ) : 
    ⊢ σ · σ' · ρ ≤ᵣ σ' · σ · ρ. 
  Proof.
    iApply to_iThy_le_intro'. simpl. unfold sem_row_cons. apply submseteq_swap.
  Qed. 
  
  (* Corollary row_le_swap_third (op1 op1' op1'' op2 op2' op2'' : label) (σ σ' σ'' : sem_sig Σ) (ρ : sem_row Σ) : 
       ⊢ (op1, op2,  σ) · (op1', op2', σ') · (op1'', op2'', σ'') · ρ ≤ᵣ (op1'', op2'', σ'') · (op1, op2, σ) · (op1', op2', σ') · ρ. 
     Proof.
       iApply to_iThy_le_intro'. simpl. apply submseteq_swap.
       iApply row_le_trans; first iApply row_le_cons_comp; try (by iApply row_le_swap_second); last iApply sig_le_refl.
       - simpl.
     Qed.
     Admitted. *)
  
  (* Corollary row_le_swap_fourth {Σ} (op op' op'' op''' : label) (σ σ' σ'' σ''': sem_sig Σ) (ρ : sem_row Σ) : 
       op ≠ op' → op ≠ op'' → op ≠ op''' → op' ≠ op'' → op' ≠ op''' → op'' ≠ op''' → 
       ⊢ (op, σ) · (op', σ') · (op'', σ'') · (op''', σ''') · ρ ≤ᵣ 
         (op''', σ''') · (op, σ) · (op', σ') · (op'', σ'') · ρ.
     Proof. 
       iIntros (??????). 
       iApply row_le_trans; first iApply row_le_cons_comp; [iApply sig_le_refl|by iApply row_le_swap_third|].
       by iApply row_le_swap_second.
     Qed. *)
  
  Lemma row_le_rec_unfold (R : sem_row Σ → sem_row Σ) `{Contractive R} :
    ⊢ (μᵣ θ, R θ) ≤ᵣ R (μᵣ θ, R θ).
  Proof. rewrite {1} sem_row_rec_unfold //. iApply row_le_refl. Qed.
  
  Lemma row_le_rec_fold (R : sem_row Σ → sem_row Σ) `{ Contractive R }:
    ⊢ R (μᵣ θ, R θ) ≤ᵣ (μᵣ θ, R θ).
  Proof. rewrite - {1} sem_row_rec_unfold. iApply row_le_refl. Qed.

  Lemma row_le_mfbang_intro (m : mode) (ρ : sem_row Σ) :
    ⊢ ρ ≤ᵣ ¡[ m ] ρ. 
  Proof.
    rewrite /sem_row_flip_mbang. unfold row_le. simpl.
    iSplit.
    - iIntros (???) "!#". case m; last first.
      { rewrite iThyIfMono_iLblSig_to_iThyIfMono. rewrite to_iThyIfMonoMS. iIntros "$". }
      rewrite iThyIfMono_iLblSig_to_iThyIfMono.
      iIntros "(%&%&%&%Hin&Ht)". iExists _,_, (iThyMono X).
      iSplit.
      { iPureIntro. induction (iLblSig_to_iLblThy ρ); first by apply elem_of_nil in Hin.
        simpl. destruct a as [[l1s' l2s'] X']. apply elem_of_cons in Hin as [Hin| Hin].
        - simplify_eq. apply list_elem_of_here.
        - apply IHi in Hin. by apply list_elem_of_further. }
      iDestruct "Ht" as (?????->?->?) "(HX & #Hcont)".
      iExists _,_,_,_,_. repeat (iSplit; first done).
      iSplitL; last iFrame "#".
      iExists S. iSplitL; first iFrame.
      iIntros (??) "!> $".
    - iSplit.
      + iIntros "!# H". iApply valid_to_iThyIfMono. by rewrite -iThyIfMono_iLblSig_to_iThyIfMono.
      + iIntros "!# %Hd". iPureIntro. erewrite distinct_to_iThyIfMono. by rewrite -iThyIfMono_iLblSig_to_iThyIfMono.
  Qed.

  Lemma row_le_mfbang_elim_ms (ρ : sem_row Σ) :
    ⊢ ¡[MS] ρ ≤ᵣ ρ. 
  Proof. 
    rewrite /sem_row_flip_mbang. unfold row_le. simpl.
    rewrite iThyIfMono_iLblSig_to_iThyIfMono. rewrite to_iThyIfMonoMS.
    iApply to_iThy_le_refl.
  Qed. 
    
  Lemma row_le_mfbang_comp m m' (ρ ρ' : sem_row Σ) :
    m' ≤ₘ m -∗ ρ ≤ᵣ ρ' -∗
    (¡[m] ρ) ≤ᵣ (¡[m'] ρ').
  Proof. 
    iIntros "#Hlem #Hleσ". destruct m.
    - iDestruct (mode_le_OS_inv with "Hlem") as "->".
      rewrite /row_le /sem_row_flip_mbang /tc_opaque. 
      rewrite !iThyIfMono_iLblSig_to_iThyIfMono.
      iSplit.
      { iIntros (???) "!# H". iApply iThy_le_to_iThy_to_iThyIfMono.
        iDestruct (iThy_le_to_iThyIfMono_to_iThy with "H") as "H".
        iApply (iThy_le_iThyIfMono with "[][$H]").
        iDestruct "Hleσ" as "($ & _)". }
      iSplit.
      + iIntros "!# H". iDestruct (valid_to_iThyIfMono with "H") as "H".
        iDestruct "Hleσ" as "(_&Hleσ&_)". iDestruct ("Hleσ" with "H") as "H". by iDestruct (valid_to_iThyIfMono with "H") as "$".
      + iIntros "!# Hd". iDestruct "Hleσ" as "(_&_&Hleσ)". unfold distinct'. repeat rewrite -distinct_to_iThyIfMono. by iApply "Hleσ".
    - iApply row_le_trans; first iApply row_le_mfbang_elim_ms. 
      iApply row_le_trans; first iApply (row_le_mfbang_intro m').
      rewrite /row_le /sem_row_flip_mbang /tc_opaque.
      rewrite !iThyIfMono_iLblSig_to_iThyIfMono.
      iSplit.
      { iIntros (???) "!# H". iApply iThy_le_to_iThy_to_iThyIfMono.
        iDestruct (iThy_le_to_iThyIfMono_to_iThy with "H") as "H".
        iApply (iThy_le_iThyIfMono with "[][$H]").
        iDestruct "Hleσ" as "($ & _)". }
       iSplit.
      + iIntros "!# H". iDestruct (valid_to_iThyIfMono with "H") as "H".
        iDestruct "Hleσ" as "(_&Hleσ&_)". iDestruct ("Hleσ" with "H") as "H". by iDestruct (valid_to_iThyIfMono with "H") as "$".
      + iIntros "!# Hd". iDestruct "Hleσ" as "(_&_&Hleσ)". unfold distinct'. repeat rewrite -distinct_to_iThyIfMono. by iApply "Hleσ".
  Qed. 
  
  Lemma row_le_mfbang_dist_cons m σ (ρ : sem_row Σ) :
    ⊢ ¡[ m ] (σ · ρ) ≤ᵣ (¡[ m ] σ)%S · (¡[ m ] ρ).
  Proof.
    unfold row_le. simpl.
    rewrite iThyIfMono_iLblSig_to_iThyIfMono. 
    iSplit; last first.
    - iSplit; [|iIntros "!> %Hd"; iPureIntro].
  Admitted. 
  
  Global Instance row_cons_once (ρ : sem_row Σ) (σ : sem_sig Σ) `{! OnceS σ, ! OnceR ρ } :
    OnceR (σ · ρ)%R.
  Proof.
    constructor. inv OnceS0. inv OnceR0. simpl.
    iSplit; last iSplit.
    { iApply iThy_le_trans; first iApply iThy_le_to_iThy_sum. simpl.
      iApply iThy_le_trans; last iApply iThy_le_sum_to_iThy. simpl.
      iApply iThy_le_sum_map.
      - iIntros (???) "!# (%&%&%&%&%&$&$&$&$&H&$)".
        iDestruct sig_le_mfbang_elim as "(?&H')".
        (* Morally we want iDestruct (sig_mbang_later $ with "H") as "H". but it has to be adapted a little bit *) 
        (* by iApply "H'". *) admit.
      - by iDestruct row_le_mfbang_elim0 as "($&_&_)". }
    { iIntros "!# H". rewrite iThyIfMono_iLblSig_to_iThyIfMono. by rewrite <-valid_to_iThyIfMono. }
    { iIntros "!# H". rewrite iThyIfMono_iLblSig_to_iThyIfMono. iDestruct "H" as "%Hdistinct". iPureIntro. by rewrite <-distinct_to_iThyIfMono. }
  Admitted. 

  Lemma row_le_mfbang_idemp m (ρ : sem_row Σ) :
    ⊢ (¡[ m ] (¡[ m ] ρ)) ≤ᵣ ((¡[ m ] ρ)).
  Proof.
    case m; last apply row_le_mfbang_elim_ms.
    unfold row_le. simpl.
    iSplit.
    - rewrite !iThyIfMono_iLblSig_to_iThyIfMono. 
      iIntros (???) "!# (%&%&%&%Hin&HX)".
      iInduction (iLblSig_to_iLblThy ρ) as [|a i] "IH";  first by apply elem_of_nil in Hin.
      destruct a as [[l1s' l2s'] X']. apply elem_of_cons in Hin as [Hin| Hin].
      + iExists l1s', l2s', (iThyMono X').
        iSplit; last first.
        { simplify_eq. simpl.
          iDestruct "HX" as (?????->?->?) "((% & (% & (HX' & Hcont)) & H3) & #H1)".
          iExists _,_,_,_,_. repeat (iSplit; first done).
          iSplitL; last done.
          iExists Q'0. iFrame. iIntros (??) "!> HQ'0". iApply "H3". by iApply "Hcont". }
        iPureIntro.
        simplify_eq. simpl. apply list_elem_of_here.
      + iDestruct ("IH" $! Hin) as "IH'".
        iDestruct ("IH'" with "HX") as "Hi".
        iDestruct "Hi" as (???) "(%Hin' & HX)".
        iExists  l1s0, l2s0, X0. iFrame.
        iPureIntro. set_solver. 
    - iSplit; iModIntro.
      + rewrite !iThyIfMono_iLblSig_to_iThyIfMono. rewrite -!valid_to_iThyIfMono. iIntros "$".
      + rewrite !iThyIfMono_iLblSig_to_iThyIfMono. unfold distinct'. rewrite -!distinct_to_iThyIfMono. iIntros "$".
  Qed. 

  Global Instance row_fbang_once (ρ : sem_row Σ) : OnceR (¡ ρ)%R.
  Proof. constructor. iApply row_le_mfbang_idemp. Qed.
  
  Lemma row_le_mfbang_comm m m' (ρ : sem_row Σ) :
    ⊢ (¡[ m ] (¡[ m' ] ρ)) ≤ᵣ (¡[ m' ] (¡[ m ] ρ)).
  Proof. 
    destruct m, m'.
    - iApply row_le_refl.
    - iApply row_le_trans; first iApply row_le_mfbang_comp.
      { iApply mode_le_refl. }
      { iApply row_le_mfbang_elim_ms. }
      iApply row_le_mfbang_intro.
    - iApply row_le_trans; first iApply row_le_mfbang_elim_ms.
      iApply row_le_mfbang_comp; first iApply mode_le_refl. iApply row_le_mfbang_intro.
    - iApply row_le_refl.
  Qed.

 
  Lemma row_le_mfbang_elim_nil m :
     ⊢ ¡[m] ⟨⟩%R ≤ᵣ (⟨⟩%R : sem_row Σ).
  Proof. 
    destruct m; simpl; last iApply row_le_mfbang_elim_ms.
    iApply to_iThy_le_bot.
  Qed.
  
  Global Instance row_nil_once : OnceR (⟨⟩ : sem_row Σ)%R.
  Proof. constructor. iApply row_le_mfbang_elim_nil. Qed.
  
  Lemma row_le_mfbang_elim_rec (m : mode) (R : sem_row Σ → sem_row Σ) `{ Contractive R }: 
    (∀ θ, ¡[ m ] (R θ) ≤ᵣ (R θ)) -∗ ¡[ m ] (μᵣ θ, R θ) ≤ᵣ (μᵣ θ, R θ).
  Proof. 
    iIntros "Hle". destruct m; last iApply row_le_mfbang_elim_ms.
    rewrite sem_row_rec_unfold. iApply "Hle".
  Qed.
  
  Global Instance row_rec_once (R : sem_row Σ → sem_row Σ) `{Contractive R} :
    (∀ θ, OnceR (R θ)) → OnceR (μᵣ θ, R θ)%R.
  Proof.
    intros Hle. constructor. 
    iApply row_le_mfbang_elim_rec. iIntros (θ). 
    destruct (Hle θ). iApply row_le_mfbang_elim0.
  Qed.

End row_sub_typing.

Section row_type_sub.

  (* Substructurality relation on rows wrt to types and environments *)
    
  Class RowTypeSub {Σ} (ρ : sem_row Σ) (τ : sem_ty Σ) := {
    row_type_sub : ⊢ (∀ v1 v2, mono_prot_on_prop ρ (τ v1 v2))
  }.
 
  Global Instance row_type_sub_once `{probblazeRGS Σ} (ρ : sem_row Σ) (τ : sem_ty Σ) `{! OnceR ρ} : RowTypeSub ρ τ.
  Proof.
    constructor.
    iIntros (w1 w2 v1 v2 Φ) "!# Hρ Hτ".
    iApply (monotonic_prot v1 v2 Φ (λ w1' w2', Φ w1' w2' ∗ τ w1 w2)%I with "[Hτ] Hρ").
    iIntros "% % $ //".
  Qed.
  
End row_type_sub.
Section row_env_sub.

  Class RowEnvSub {Σ} (ρ : sem_row Σ) (Γ : env Σ) := {
    row_env_sub : ⊢ (∀ γ, mono_prot_on_prop ρ (Γ ⊨ₑ γ))
  }.
  
  Global Instance row_env_sub_once `{probblazeRGS Σ} (ρ : sem_row Σ) (Γ : env Σ) `{! OnceR ρ} : RowEnvSub ρ Γ.
  Proof.
    constructor.
    iIntros (γ v1 v2 Φ) "!# Hρ HΓ".
    iApply (monotonic_prot v1 v2 Φ (λ w1' w2', Φ w1' w2' ∗ Γ ⊨ₑ γ)%I with "[HΓ] Hρ").
    iIntros "% % $ //".
  Qed.
  
End row_env_sub.

(* Notations *)
Notation "ρ ᵣ⪯ₑ Γ" := (RowEnvSub ρ%R Γ%T) (at level 80).
Notation "ρ ᵣ⪯ₜ τ" := (RowTypeSub ρ%R τ%T)%I (at level 80).


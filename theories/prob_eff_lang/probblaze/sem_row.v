
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
      (@SemRow Σ ((([(sem_sig_labels Σ σ).1], [(sem_sig_labels Σ σ).2]), σ) :: (sem_row_car ρ)) _ (* _ *) ) .
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

Lemma map_list_contractive {A B : ofe} (f : A → B) : ∀ n, 1 ≤ n → Proper (dist_later n ==> dist n) f → Proper (dist_later n ==> dist n) (map f).
Proof.
  intros n Hlt Hf l k Hlk. apply list_dist_Forall2.
  apply Forall2_fmap_2. destruct n; first inversion Hlt. 
  generalize dependent k. induction l; intros k Hlk.
  - destruct k; first done.
    apply Hlk in Hlt. inversion Hlt.
  - destruct k.
    + apply Hlk in Hlt. inversion Hlt.
    + apply Forall2_cons_2.
      * f_contractive. by inversion Hlk.
      * apply IHl. inversion Hlk. 
        constructor. intros m Hm. 
        apply dist_later_lt in Hm. by inversion Hm.
Qed.


(* Program Definition iThy_later {Σ} (l1 l2 : label) : sem_sig Σ -n> iThy Σ := λne T, λ e e', λne ψ, (∃ v1 v2, ⌜e = do: l1 v1⌝%E ∗ ⌜e' = do: l2 v2⌝%E ∗  ▷ ((pmono_prot_car T) e e' ψ))%I.
   Next Obligation.
     intros. intros ψ ψ' Hne. do 6 f_equiv. rewrite Hne. done.
   Qed.
   Next Obligation.
     intros. intros T T' Hne. intros e e' ψ.
     simpl. 
     do 6 f_equiv. destruct Hne.
     by rewrite (Hne e e' ψ).
   Qed.
   
   Instance iThy_later_contractive {Σ} (l1 l2 : label) : Contractive (@iThy_later Σ l1 l2).
   Proof.
     unfold iThy_later. simpl.
     intros ? T T' ?.
     intros e e' ?. simpl.
     do 6 f_equiv.
     f_contractive.
     rewrite (H e e' _).
     done.
   Qed. *)

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

(* Definition iLblThy_later {Σ} (L : iLblSig Σ) : iLblThy Σ := map (λ '((ls1,ls2), X), ((ls1, ls2), iThy_later (@sem_sig_labels Σ X).1 (@sem_sig_labels Σ X).2 X)) L.
   
   (* Lemma sem_row_shape X ρ : X :: ρ → ∃ σ, X = ((sem_sig_labels σ).1, (sem_sig_labels σ).2, σ). *)
                                                                                      
   
   Lemma sem_row_later_iLblThy_later {Σ} ρ : iLblSig_to_iLblThy (sem_row_later ρ) = @iLblThy_later Σ ρ.
   Admitted.
   (* Proof.
        destruct ρ. 
        induction sem_row_car.
        - done.
        - unfold sem_row_later. unfold sem_sig_later. rewrite iLblSig_to_iLblThy_proj.
          simpl. destruct a as ((ls1,ls2), σ). unfold pmono_prot_car. simpl.
          f_equiv.
          + f_equiv.   admit.
          + unshelve eapply IHsem_row_car.
            admit.
      Admitted. *)
   
   (* Global Instance iLblSig_to_iLblThy_ne {Σ} : NonExpansive (@iLblSig_to_iLblThy Σ).
      Admitted. *)
   
   Global Instance sem_row_later_contractive {Σ} : Contractive (@sem_row_later Σ). 
   Proof. 
     intros n l k Hlater. destruct n; first done.
   (*   assert (n < S n)%nat as Heq by lia.
        apply Hlater in Heq.
        destruct n.
        - unfold dist,sem_row_dist,listO,ofe_dist,list_dist in *. apply list_dist_Forall2.
          
      
          
        unfold sem_rowO. simpl. unfold ofe_dist. unfold sem_row_dist. simpl.
        destruct l, k. unfold dist. (* rewrite !sem_row_later_iLblThy_later. *)
        destruct n; first done.
        apply map_list_contractive; first lia.
        - intros ???. destruct x as ((xs1 & xs2) & X). 
          destruct y as ((ys1&ys2) &Y). f_equiv.
          + assert (n < S n) as Hlt by lia.  apply H in Hlt. 
            by inversion Hlt.
          + destruct X. destruct Y.
            assert (n < S n) as Hlt by lia.
            apply H in Hlt.
            inversion Hlt. simpl in *. 
            unfold dist,sem_sigO,ofe_dist,sem_sig_dist in H1. admit.
        - apply Build_dist_later. intros m Hm. 
          apply Hdist in Hm.
          unfold dist,sem_row_dist in Hm.
      p    
          by apply Hdist.
      Qed. *)
   Admitted.  *)

(* Definition sem_row_rec_pre {Σ} (R : sem_row Σ -n> sem_row Σ) (ρ : sem_row Σ) : sem_row Σ :=
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
   Proof. rewrite /sem_row_rec {1} fixpoint_unfold //. Qed. *)

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
(* Notation "'μᵣ' θ , ρ " := (sem_row_rec (λ θ, ρ%R)) (at level 50) : sem_row_scope. *)

Section row_properties.
  (* TODO: finish proofs in this section *)
  Global Instance sem_row_cons_ne {Σ} (* op op' *) : NonExpansive2 (@sem_row_cons Σ (* op op' *)).
  Proof.
    (* Now provable: the [sem_sig] dist tracks labels (car-dist ∧ labels-eq)
       and the [sem_row] dist is the list dist of the [iLblSig_to_iLblThy]
       image, whose head reads both the labels and [sem_sig_car] of σ.  The
       label-equality conjunct closes the discrete head-label components; the
       car-dist conjunct closes the [sem_sig_car] component; [Hρ] is exactly
       the tail dist. *)
    intros n σ1 σ2 [Hcar Hlbl] ρ1 ρ2 Hρ.
    unfold sem_row_cons, dist, ofe_dist, sem_rowO, sem_row_dist; simpl.
    rewrite Hlbl. f_equiv; [| exact Hρ].
    apply pair_ne; [done|]. exact Hcar.
  Qed.
  Global Instance sem_row_cons_Proper {Σ} (* op op' *): Proper ((≡) ==> (≡) ==> (≡)) (@sem_row_cons Σ (* op op' *)).
  Proof. apply ne_proper_2. apply _. Qed.

  (* UNUSED: not referenced anywhere outside this definition (verified by
     grep over theories/prob_eff_lang/).  It was added together with the
     [sem_sig_later] head to make [sem_row_cons] contractive in σ for the
     never-instantiated recursive-row fixpoint [sem_row_rec]/[RRec]
     (commented out in interp.v).  With the plain σ head, [sem_row_cons] is
     genuinely NOT contractive in σ (no guarding later); since the instance
     is unused and now vacuous, it is left Admitted. *)
  Global Instance sem_row_cons_contractive {Σ} (* op *) n : Proper (dist_later n ==> dist n ==> dist n) (@sem_row_cons Σ (* op *)).
  Proof.
    intros ??????. rewrite /sem_row_cons.
    (* intros ???????. rewrite /sem_row_cons.
       intros ?. simpl. do 6 f_equiv; first f_contractive; f_equiv; apply non_dep_fun_dist; by f_equiv. *)
  Admitted.
  Global Instance sem_row_flip_mbang_ne {Σ} m : NonExpansive (@sem_row_flip_mbang Σ m).
  Proof.
    intros n ρ1 ρ2 Hρ.
    unfold dist, sem_row_dist. simpl.
    unfold dist, sem_row_dist in Hρ. simpl in Hρ.
    enough (H : iLblSig_to_iLblThy (¡[m] ρ1)%R = to_iThyIfMono m (iLblSig_to_iLblThy ρ1) ∧
                iLblSig_to_iLblThy (¡[m] ρ2)%R = to_iThyIfMono m (iLblSig_to_iLblThy ρ2)).
    { unfold ofe_dist, sem_rowO, sem_row_dist; simpl.
      destruct H as [-> ->]. by apply to_iThyIfMono_ne. }
    split.
    all: rewrite /sem_row_flip_mbang /iLblSig_to_iLblThy /iThyIfMono_iLblSig
           /to_iThyIfMono !map_map;
         f_equal; extensionality x; by destruct x as [[? ?] ?].
  Qed.
  Global Instance sem_row_flip_bang_Proper {Σ} m : Proper ((≡) ==> (≡)) (@sem_row_flip_mbang Σ m).
  Proof. apply ne_proper. apply _. Qed.
  
  Global Instance sem_row_flip_mbang_rec_contractive {Σ} m (R : sem_row Σ -d> sem_row Σ) `{Contractive R} : 
    Contractive (λ θ, sem_row_flip_mbang m (R θ)).
  Proof.
    intros n x y Hxy. apply sem_row_flip_mbang_ne. by apply Contractive0.
  Qed.

    
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
      iIntros (???) "!# (%&%&%&%&%&$&$&$&$&Hσ&$)". by iApply "Hσσ'". }
    { iModIntro. iApply valid_submseteq'; by constructor. }
    { iIntros "!# %Hd"; iPureIntro. eapply distinct_submseteq'; last done; by constructor. }
  Qed.

  (* Extend a row on the head: the underlying row [ρ] is below [σ · ρ].
     The semantic counterpart of [le.RExtend_le].  Pure sub-multiset
     argument: [iLblThy ρ ⊆+ head :: iLblThy ρ]. *)
  Lemma row_le_cons_extend (σ : sem_sig Σ) (ρ : sem_row Σ) :
    ⊢ ρ ≤ᵣ σ · ρ.
  Proof.
    unfold row_le, sem_row_cons. simpl.
    iApply to_iThy_le_intro'. simpl.
    apply submseteq_cons. reflexivity.
  Qed.

  (* Erase a freshly-allocated bottom signature from the head of a row.
     The [is_label]/[spec_labels_frag] premises discharge the [valid]
     obligation (the head op1/op2 are extra labels on the left row); the
     [∉] premises discharge [distinct'] (NoDup of the head labels).  With
     the plain σ head (sem_row.v:23, no [sem_sig_later]), the head iThy_le
     obligation is the trivial erasure of the [sem_sig_bottom] protocol
     (whose body is [False]) -- no [▷ False] to discharge. *)
  Lemma row_le_erase (op1 op2 : label) (ρ : sem_row Σ) :
    op1 ∉ labels_l (iLblSig_to_iLblThy ρ) →
    op2 ∉ labels_r (iLblSig_to_iLblThy ρ) →
    is_label op1 DfracDiscarded -∗
    spec_labels_frag op2 DfracDiscarded -∗
    sem_row_cons (sem_sig_bottom op1 op2) ρ ≤ᵣ ρ.
  Proof.
    iIntros (Hl Hr) "#Hlbl1 #Hlbl2".
    unfold row_le, sem_row_cons. simpl.
    iSplit; last iSplit.
    - iApply iThy_le_trans; first iApply iThy_le_to_iThy_sum.
      iApply iThy_le_trans; last iApply iThy_le_sum_bot_l.
      iApply iThy_le_sum_l.
      iIntros (e1 e2 Q) "!# Ht".
      rewrite /iThyTraverse /=.
      iDestruct "Ht" as (e1' e2' k1 k2 S) "(%&%&%&%&Hbot&_)".
      simpl. iDestruct "Hbot" as (αs v1 v2) "(%&%&Hfalse&_)".
      done.
    - iModIntro. iIntros "Hvalid".
      unfold logic.valid. simpl.
      iDestruct "Hvalid" as "(Hvl & Hvr)".
      unfold valid_l, valid_r, labels_l, labels_r. simpl.
      iFrame "Hvl Hvr Hlbl1 Hlbl2".
    - iModIntro. iIntros "%Hd". iPureIntro.
      unfold distinct, distinct_l, distinct_r, labels_l, labels_r in *. simpl.
      destruct Hd as (Hdl & Hdr).
      split; apply NoDup_cons_2; assumption.
  Qed.


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
  
  (* Lemma row_le_rec_unfold (R : sem_row Σ → sem_row Σ) `{Contractive R} :
       ⊢ (μᵣ θ, R θ) ≤ᵣ R (μᵣ θ, R θ).
     Proof. rewrite {1} sem_row_rec_unfold //. iApply row_le_refl. Qed.
     
     Lemma row_le_rec_fold (R : sem_row Σ → sem_row Σ) `{ Contractive R }:
       ⊢ R (μᵣ θ, R θ) ≤ᵣ (μᵣ θ, R θ).
     Proof. rewrite - {1} sem_row_rec_unfold. iApply row_le_refl. Qed. *)

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
    iApply to_iThy_le_refl.
  Qed.
  
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
        by iApply "H'".
      - by iDestruct row_le_mfbang_elim0 as "($&_&_)". }
    { iIntros "!# H". rewrite iThyIfMono_iLblSig_to_iThyIfMono. by rewrite <-valid_to_iThyIfMono. }
    { iIntros "!# H". rewrite iThyIfMono_iLblSig_to_iThyIfMono. iDestruct "H" as "%Hdistinct". iPureIntro. by rewrite <-distinct_to_iThyIfMono. }
  Qed. 

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
  
  (* Lemma row_le_mfbang_elim_rec (m : mode) (R : sem_row Σ → sem_row Σ) `{ Contractive R }: 
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
     Qed. *)

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

Section sem_row_union. 
  Context `{probblazeRGS Σ}.

  Lemma iLblSig_to_iLblThy_app ρ ρ' : iLblSig_to_iLblThy (ρ ++ ρ') = iLblSig_to_iLblThy ρ ++ (@iLblSig_to_iLblThy Σ ρ'). 
  Proof. 
    induction ρ; first done.
    simpl. by rewrite IHρ.
  Qed.                      

  Program Definition sem_row_union (ρ ρ' : sem_row Σ) : sem_row Σ :=
    SemRow ((sem_row_car ρ) ++ (sem_row_car ρ')) _.  
  Next Obligation.                            
    iIntros (ρ ρ' ????) "#Hww % % % (%Hin & Hx)".
    iSplit; first done.
    rewrite iLblSig_to_iLblThy_app in Hin. 
    apply elem_of_app in Hin as [Hin | Hin];
    iPoseProof (sem_row_mono Σ _) as "H";
      iDestruct ("H" with "[][Hx]") as "(_&$)"; try done;
      iSplit; done.
  Qed. 

  Global Instance sem_row_union_ne n : Proper (dist n ==> dist n ==> dist n) sem_row_union.
  Proof.
    intros ρ1 ρ1' Heq1 ρ2 ρ2' Heq2.
    unfold sem_row_union.
    unfold dist, sem_row_dist, ofe_dist.
    simpl. unfold sem_row_dist.
    rewrite iLblSig_to_iLblThy_proj iLblSig_to_iLblThy_proj.
    rewrite !iLblSig_to_iLblThy_app.
    f_equiv.
    - exact Heq1.
    - exact Heq2.
  Qed.

  (* [valid]/[distinct] decompose over [iLblThy] append. *)
  Lemma valid_app (L M : iLblThy Σ) :
    logic.valid (L ++ M) ⊣⊢ logic.valid L ∗ logic.valid M.
  Proof.
    rewrite /logic.valid /valid_l /valid_r /labels_l /labels_r
            !fmap_app !concat_app.
    rewrite !big_sepL_app. iSplit; iIntros "[[$$][$$]]".
  Qed.

  Lemma distinct_app_iff (L M : iLblThy Σ) :
    distinct (L ++ M) → distinct L ∧ distinct M.
  Proof.
    rewrite /distinct /distinct_l /distinct_r /labels_l /labels_r
            !fmap_app !concat_app.
    intros [Hl%NoDup_app Hr%NoDup_app].
    split; split; tauto.
  Qed.

  (* Union monotonicity, with the cross-disjointness premise supplied as
     two LABEL sub-multiset facts (one per side).  These let us derive
     [distinct (ρ1 ++ ρ2)] (the LARGER, left rows) from
     [distinct (ρ1' ++ ρ2')] via [distinct_submseteq'] — exactly the gap
     left [admit]ed in [row_le_union].  Used by the [RUnion_le] case of
     [interp.subtyping_sound_all], where the sub-multiset facts come from
     label-monotonicity of [≤R] along the [@false] row premises
     ([interp.row_le_false_labels_l]/[_r]). *)
  Lemma row_le_union' (ρ1 ρ2 ρ1' ρ2' : sem_row Σ) :
    labels_l (iLblSig_to_iLblThy ρ1) ⊆+ labels_l (iLblSig_to_iLblThy ρ1') →
    labels_l (iLblSig_to_iLblThy ρ2) ⊆+ labels_l (iLblSig_to_iLblThy ρ2') →
    labels_r (iLblSig_to_iLblThy ρ1) ⊆+ labels_r (iLblSig_to_iLblThy ρ1') →
    labels_r (iLblSig_to_iLblThy ρ2) ⊆+ labels_r (iLblSig_to_iLblThy ρ2') →
    ρ1 ≤ᵣ ρ1' -∗ ρ2 ≤ᵣ ρ2' -∗
    sem_row_union ρ1 ρ2 ≤ᵣ sem_row_union ρ1' ρ2'.
  Proof.
    iIntros (Hl1 Hl2 Hr1 Hr2).
    unfold row_le, sem_row_union. simpl.
    rewrite !iLblSig_to_iLblThy_app.
    iIntros "#(Hthy1 & Hvl1 & Hd1) #(Hthy2 & Hvl2 & Hd2)".
    iSplit; last iSplit.
    - iApply iThy_le_trans; first iApply iThy_le_to_iThy_app_inv.
      iApply iThy_le_trans; last iApply iThy_le_to_iThy_app.
      by iApply (iThy_le_sum_map with "Hthy1 Hthy2").
    - iIntros "!# Hv".
      iDestruct (valid_app with "Hv") as "[Hva Hvb]".
      iApply valid_app; iSplitL "Hva"; [by iApply "Hvl1"|by iApply "Hvl2"].
    - iIntros "!# %Hd".
      iPureIntro. rewrite /distinct'.
      eapply (distinct_submseteq'
                _ (iLblSig_to_iLblThy ρ1' ++ iLblSig_to_iLblThy ρ2'));
        [| |exact Hd].
      + rewrite !labels_l_app. by apply submseteq_app.
      + rewrite !labels_r_app. by apply submseteq_app.
  Qed.

  (* FLIP distributes over UNION at the level of underlying theory lists:
     [iThyIfMono_iLblSig] is a [map], and [sem_row_union] is an [app], so
     the two sides have LITERALLY equal carriers ([map_app]).  Used by the
     [RFlipUnion_le] case of [interp.subtyping_sound_all]. *)
  Lemma iLblSig_to_iLblThy_flip_union (m : mode) (ρ1 ρ2 : sem_row Σ) :
    iLblSig_to_iLblThy (sem_row_flip_mbang m (sem_row_union ρ1 ρ2))
    = iLblSig_to_iLblThy
        (sem_row_union (sem_row_flip_mbang m ρ1) (sem_row_flip_mbang m ρ2)).
  Proof.
    rewrite !iThyIfMono_iLblSig_to_iThyIfMono.
    unfold sem_row_union. rewrite !iLblSig_to_iLblThy_app.
    rewrite !iThyIfMono_iLblSig_to_iThyIfMono.
    unfold to_iThyIfMono. by rewrite map_app.
  Qed.

  Lemma row_le_flip_union (m : mode) (ρ1 ρ2 : sem_row Σ) :
    ⊢ sem_row_flip_mbang m (sem_row_union ρ1 ρ2)
        ≤ᵣ sem_row_union (sem_row_flip_mbang m ρ1) (sem_row_flip_mbang m ρ2).
  Proof.
    rewrite /row_le /tc_opaque.
    rewrite iLblSig_to_iLblThy_flip_union.
    iApply to_iThy_le_refl.
  Qed.

End sem_row_union.

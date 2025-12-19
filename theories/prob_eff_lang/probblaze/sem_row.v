
(* sem_row.v *)

(* This file contains the definition of semantic rows. *)

From iris.proofmode Require Import base tactics.
From iris.algebra Require Import ofe gmap.
From iris.base_logic Require Export iprop upred invariants.

(* Local imports *)
From clutch.prob_eff_lang.probblaze Require Import logic notation sem_def mode sem_sig.

(* Nil Row *)
Program Definition sem_row_nil {Σ} : sem_row Σ := @SemRow Σ ⊥ _ _. 
Next Obligation. iIntros (?????) "? (%l1 & %l2 & %X & %Hcontra & ?)". by apply elem_of_nil in Hcontra. Qed.
Next Obligation. iIntros (????) "(%l1 & %l2 & %X & %Hcontra & ?)". by apply elem_of_nil in Hcontra. Qed.

Global Instance sem_row_bottom {Σ} : Bottom (sem_row Σ) := sem_row_nil.
(* TODO: update to use iLblThy s.t. we can use BREL *)
(* Cons Row *)
Program Definition sem_row_cons {Σ} (op1 op2 : label) : sem_sig Σ -d> sem_row Σ -d> sem_row Σ :=
    λ σ ρ, (@SemRow Σ ((([op1], [op2]), σ) :: (sem_row_car ρ)) _ _ ) .
              (* (λ e1 e2, λne Φ, ∃ (op' : label) (v1 v2 : val), 
                              ⌜ e1 = (do: op' v1)%E ⌝ ∗ ⌜ e2 = (do: op' v2)%E ⌝ ∗
                               if decide (op = op') then 
                                 ▷ ((pmono_prot_car σ) v1 v2 Φ)
                               else
                                 (pmono_prot_car (sem_row_car ρ)) (do: op' v1)%E (do: op' v2)%E Φ)%I) _). *)
Next Obligation.
  intros ?????. iIntros (????) "#H1 H2". iApply to_iThy_cons. iDestruct (to_iThy_cons with "H2") as "H2".
  iDestruct "H2" as "[(%&%&%&%&%&->&%&->&%&Hσ&#Hcont)|(%&%&%&%&%&%&%&%&%&->&%&->&%&Hσ&#Hcont)]"; [iLeft|iRight].
  - iExists _,_,_,_,_. do 4 (iSplit; [iPureIntro;done|]). iFrame.
    iModIntro. iIntros (??) "HS". iDestruct ("Hcont" with "HS") as "HΦ".
    by iApply "H1".
  - simpl. iExists _,_,_. iFrame. iSplit; [iPureIntro; done|].
    iExists _,_. do 4 (iSplit;[iPureIntro;done|]).
    iIntros "!# % % HS". iDestruct ("Hcont" with "HS") as "HΦ".
    by iApply "H1".
Qed.
Next Obligation.
  iIntros (????????) "H". 
  iDestruct (to_iThy_cons with "H") as "H". 
  iDestruct "H" as "[(%&%&%&%&%&->&%&->&%&Hσ&#Hcont)|(%&%&%&%&%&%&%&%&%&->&%&->&%&Hσ&#Hcont)]".
  - destruct σ. iDestruct sem_sig_prop as "H1". iExists _, _.
    iDestruct ("H1" with "Hσ") as (????) "H". iExists op0, op3, v1,v2.
    iDestruct "H" as "(-> & ->)". done.
  - apply in_iLblSig in H as (X' & ->).
    iDestruct (sem_sig_prop with "Hσ") as (op3 op4 v1 v2) "(-> & ->)".
    iExists _,_,_,_,_,_. done.
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

(* TODO: does this hold? What if I forget the sem_sig structure? *)
(* Lemma iThyIfMono_iLblSigMS {Σ} (L : iLblSig Σ) : 
     iThyIfMono_iLblSig MS L = L.
   Proof.
     (* induction L as [|((?,?),?)]; [done|rewrite //= IHL].
        unfold sem_sig_flip_mbang. simpl. done.
          destruct L.
        by induction L as [|((?,?),?)]; [|rewrite //= IHL]. Q. *)
   Admitted.  *)
  
Program Definition sem_row_flip_mbang {Σ} (m : mode) (ρ : sem_row Σ) : sem_row Σ := 
  @SemRow Σ (iThyIfMono_iLblSig m ρ) _ _.
Next Obligation.
  iIntros (???????) "#HΦ Hσ". 
  iDestruct "Hσ" as (????????? -> ? -> ?) "(HX & #Hcont)".
  iExists _, _, _. iFrame. iSplit; [iPureIntro;done|].
  iExists _,_. repeat (iSplit; [iPureIntro; done|]).
  iIntros (??) "!# HS". iApply "HΦ". by iApply "Hcont".
Qed.
Next Obligation.
  iIntros (??????) "Hρ".
  simpl. iDestruct "Hρ" as (????????? -> ? -> ?) "(HX & #Hcont)".
  apply in_iLblSig in H as (X' & ->).
  iDestruct (sem_sig_prop with "HX") as (op3 op4 v1 v2) "(-> & ->)".
  iExists _,_,_,_,_,_. done.
Qed.
(* Notations. *)
Notation "⟨⟩" := (sem_row_nil) : sem_row_scope.
Notation "opσ · ρ" := (sem_row_cons opσ.1.1 opσ.1.2 opσ.2 ρ) (at level 80, right associativity) : sem_row_scope.
Notation "¡[ m ] ρ" := (sem_row_flip_mbang m ρ) (at level 10) : sem_row_scope.
Notation "¡ ρ" := (sem_row_flip_mbang OS ρ) (at level 10) : sem_row_scope.
Notation "'μᵣ' θ , ρ " := (sem_row_rec (λ θ, ρ%R)) (at level 50) : sem_row_scope.

Section row_properties.
  (* TODO: finish proofs in this section *)
  Global Instance sem_row_cons_ne {Σ} op : NonExpansive2 (@sem_row_cons Σ op).
  Proof. 
  (*   intros ???????. rewrite /sem_row_cons. 
       intros ??. simpl. do 2 f_equiv; apply non_dep_fun_dist; by f_equiv.  
     Qed. *)
  Admitted. 
  Global Instance sem_row_cons_Proper {Σ} op : Proper ((≡) ==> (≡) ==> (≡)) (@sem_row_cons Σ op).
  Proof. apply ne_proper_2. apply _. Qed.
  
  Global Instance sem_row_cons_contractive {Σ} op n : Proper (dist_later n ==> dist n ==> dist n) (@sem_row_cons Σ op).
  Proof. 
  (*   intros ???????. rewrite /sem_row_cons. 
       intros ?. simpl. do 6 f_equiv; first f_contractive; f_equiv; apply non_dep_fun_dist; by f_equiv.
     Qed. *)
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

  Lemma iLblSig_car_thing {Σ} (ρ : iLblSig Σ) :
   ∃ ρ' : iLblThy Σ, iLblSig_to_iLblThy ρ = ρ'
  Proof.
    simpl. done.
  Qed. 
    
  (* TODO: This should be provable, but the records and coercions are annoying*)
  Lemma iThyIfMono_iLblSig_to_iThyIfMono {Σ} (m : mode) (ρ : sem_row Σ) :
    iLblSig_to_iLblThy (sem_row_flip_mbang m ρ) = to_iThyIfMono m (iLblSig_to_iLblThy ρ).
  Proof.
    unfold iLblSig_to_iLblThy.
    (* case m; last first.
       { rewrite to_iThyIfMonoMS. unfold sem_row_flip_mbang. destruct ρ. simpl. rewrite (iThyIfMono_iLblSigMS ρ). *)
    destruct ρ as [l Hmono Hprop].
    induction l; first done. intros.
    simpl. destruct a as [[l1s l2s] σ]. rewrite IHl; last done.
    - iIntros (????) "#HΦ HlΨ".
      iPoseProof Hmono as "Hmcons".
      iDestruct "HlΨ" as (l1s' l2s' X) "(%Hin & HXΦ)".
      (* iExists _,_,_. iSplit; first done. *)
      iDestruct ("Hmcons" with "HΦ") as "HΨ".
      iAssert (to_iThy (iLblSig_to_iLblThy ((l1s,l2s,σ) :: l)) v1 v2 Φ) with "[HXΦ]" as "Htemp".
      { iExists _,_,_. iSplit; [iPureIntro; by apply elem_of_list_further|]. done. }
      iDestruct ("HΨ" with "Htemp") as "HΦ'".
      iDestruct "HΦ'" as (l1s'' l2s'' X') "H".
      iExists _,_,_.
  Admitted.         

  Definition mono_prot_on_prop {Σ} (Ψ : sem_row Σ) (P : iProp Σ) : iProp Σ :=
    □ (∀ e1 e2 Φ, (to_iThy (iLblSig_to_iLblThy Ψ)) e1 e2 Φ -∗ P -∗ (to_iThy (iLblSig_to_iLblThy Ψ)) e1 e2 (λ w1 w2, Φ w1 w2 ∗ P))%I.

  Lemma mono_prot_on_prop_monotonic {Σ} (σ : sem_row Σ) : 
    (⊢ ∀ P, mono_prot_on_prop σ P) ↔ MonoProt (to_iThy (iLblSig_to_iLblThy σ)).
  Proof.
    split.
    - iIntros (H). constructor. iIntros (v1 v2 Φ Φ') "Hpost HΨ".
      iDestruct (H with "HΨ Hpost") as "H".
      iApply (sem_row_mono _ σ with "[] H").
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

  (* TODO: figure out how to extend sem_rows *)
  Lemma row_le_cons_comp (ρ ρ' : sem_row Σ) (op op' : label) (σ σ' : sem_sig Σ) : 
    σ ≤ₛ σ' -∗ ρ ≤ᵣ ρ' -∗ sem_row_cons op op' σ ρ ≤ᵣ sem_row_cons op op' σ' ρ'.
    (* (((op, op'), σ) ⋅ ρ) ≤ᵣ ((op, op'), σ') · ρ'. *)
  Proof.
    iIntros "#Hσσ' #Hρρ'". (* rewrite /sem_row_cons /=. *)
    unfold row_le. simpl.
    iSplit.
    - admit.
    - iDestruct "Hρρ'" as "(_&#(#Hvalid & #Hdistinct))".
      iSplit.
      + iModIntro. iIntros "#H".
        iDestruct (valid_submseteq with "H") as "Hρ'".
        { instantiate (1 := iLblSig_to_iLblThy ρ').
          apply submseteq_cons. set_solver. }
        iDestruct ("Hvalid" with "Hρ'") as "Hρ".
        iSplit.
        * iDestruct "H" as "(H1 & H2)". unfold valid_l.
          admit.
        * admit.
      + admit.
    (* iIntros (???) "!# (% & % & % & % & % & % & -> & -> & H)".
       iExists op', v1', v2'; do 2 (iSplit; first done).
       destruct (decide (op = op')); first (by iApply "Hσσ'"). 
       by iApply "Hρρ'". *)
  Admitted. 
  
  Lemma row_le_swap_second `{probblazeRGS Σ} (op1 op1' op2 op2' : label) (σ σ' : sem_sig Σ) (ρ : sem_row Σ) : 
    op1 ≠ op1' →
    op2 ≠ op2' →
    ⊢ (op1, op2, σ) · (op1', op2', σ') · ρ ≤ᵣ (op1', op2', σ') · (op1, op1', σ) · ρ. 
  Proof. 
    iIntros (Hneq). rewrite /sem_row_cons /=.
    (* iIntros (???) "!# (%op'' & %v1'' & %v2'' & %Heq1 & %Heq2 & H)". simpl.
       destruct (decide (op = op'')) as [->|].
       - iExists op'', v1'', v2''. do 2 (iSplit; first done).
         rewrite decide_False; last done.
         iExists op'', v1'', v2''; do 2 (iSplit; first done).
         rewrite decide_True //.
       - iDestruct "H" as "(%op''' & %v1''' & %v2''' & %Heq1' & %Heq2' & H)".
         destruct (decide (op' = op''')) as [->|].
         + iExists op'', v1'', v2''; do 2 (iSplit; first done).
           simplify_eq. rewrite decide_True //.
         + iExists op''', v1'', v2''; do 2 (iSplit; first by simplify_eq).
           simplify_eq. rewrite decide_False //.
           iExists op''', v1''', v2'''. do 2 (iSplit; first done).
           rewrite decide_False //.
     Qed. *)
  Admitted. 
  
  Corollary row_le_swap_third `{probblazeRGS Σ} (op1 op1' op1'' op2 op2' op2'' : label) (σ σ' σ'' : sem_sig Σ) (ρ : sem_row Σ) : 
    op1 ≠ op1' → op1' ≠ op1'' → op1'' ≠ op1 →
    op2 ≠ op2' → op2' ≠ op2'' → op2'' ≠ op2 →
    ⊢ (op1, op2,  σ) · (op1', op2', σ') · (op1'', op2'', σ'') · ρ ≤ᵣ (op1'', op2'', σ'') · (op1, op2, σ) · (op1', op2', σ') · ρ. 
  Proof. 
    (* iIntros (??????). 
       iApply row_le_trans; first iApply row_le_cons_comp; [iApply sig_le_refl|by iApply row_le_swap_second|].
       by iApply row_le_swap_second.
     Qed. *)
  Admitted.
  
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
        - simplify_eq. apply elem_of_list_here.
        - apply IHi in Hin. by apply elem_of_list_further. }
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
  
  Lemma row_le_mfbang_dist_cons `{probblazeRGS Σ} op1 op2 m σ (ρ : sem_row Σ) :
    ⊢ ¡[ m ] ((op1, op2, σ) · ρ) ≤ᵣ (op1, op2, ¡[ m ] σ)%S · (¡[ m ] ρ).
  Proof. 
  (*   rewrite /sem_row_flip_mbang. iIntros (???) "!# H". simpl.
       destruct m; simpl; [|done]. 
       iDestruct "H" as (Q') "((%op' & %v1' & %v2' & -> & -> & H) & Hpost)".
       iExists op', v1', v2'. do 2 (iSplit; first done).
       destruct (decide (op = op')); first iNext; iExists Q'; iFrame. 
     Qed. *)
  Admitted. 
  
  Global Instance row_cons_once `{probblazeRGS Σ} (ρ : sem_row Σ) op1 op2 (σ : sem_sig Σ) `{! OnceS σ, ! OnceR ρ } :
    OnceR ((op1, op2, σ) · ρ)%R.
  Proof.
    constructor. inv OnceS0. inv OnceR0.
    (* iApply row_le_trans; first iApply row_le_mfbang_dist_cons.
       iApply row_le_cons_comp; [iApply sig_le_mfbang_elim|iApply row_le_mfbang_elim0].
     Qed. *)
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
        simplify_eq. simpl. apply elem_of_list_here.
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

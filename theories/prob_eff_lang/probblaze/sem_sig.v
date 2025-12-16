(* sem_sig.v *)

(* This file contains the definition of semantic signatures. *)

From iris.proofmode Require Import base tactics.
From iris.algebra Require Import ofe list.
From iris.base_logic Require Export iprop upred invariants.

From clutch.prob_eff_lang.probblaze Require Import logic sem_def syntax semantics mode notation.

(* Universally Quantified Effect Signature *)
(* TODO: generalize αs to a list of types -- in affect they use a tele *)
Program Definition sem_sig_eff {Σ} {αs : sem_ty Σ} : (sem_ty Σ -d> sem_ty Σ) -d> (sem_ty Σ -d> sem_ty Σ) -d> sem_sig Σ :=
  λ A B,
  (@SemSig Σ (@PMonoProt Σ (λ e1 e2, λne Φ, ∃ αs, ∃ (op1 op2 : label) v1 v2, ⌜ e1 = (do: op1 (Val v1))%E ⌝ ∗ ⌜ e2 = (do: op2 (Val v2))%E ⌝ ∗  A αs v1 v2 
                                               ∗ □ (∀ w1 w2, ∃ v1 v2, ⌜ w1 = Val v1 ⌝ ∗ ⌜ w2 = Val v2 ⌝ ∗ B αs v1 v2 -∗ Φ w1 w2))%I _) _).
Next Obligation.
  iIntros (??????????). repeat f_equiv.
Qed.
Next Obligation.
  iIntros (????????) "#HΦ Hσ".
  f_equal /=. iDestruct "Hσ" as (αs' op1' op2' v1' v2' -> ->) "(HA & #Hσ)". iExists _, _, _,_,_.
  do 2 (iSplit; try done). iFrame "HA".
  iModIntro. iIntros (??). iDestruct ("Hσ" $! w1 w2) as (v1 v2) "HB". iExists _, _.
  iIntros "H". iApply "HΦ". by iApply "HB".
Qed.
Next Obligation.
  iIntros (???????) "(%&%&%&%&%&->&->&_)". iExists _,_,_,_. iSplit; iPureIntro; reflexivity.
Qed. 

(* Flip-Bang Signature *)
Program Definition sem_sig_flip_mbang {Σ} (m : mode) (σ : sem_sig Σ) : sem_sig Σ := @SemSig Σ (@PMonoProt Σ (iThyIfMono m σ) _) _.
Next Obligation.
  iIntros (???????) "#HΦ Hσ". 
  destruct m.
  - simpl. iDestruct "Hσ" as (Q) "(Hσ & HQ)".
    iExists _. iFrame. iNext.
    iIntros (??) "Q". iApply "HΦ". by iApply "HQ".
  - simpl. by iApply (pmono_prot_prop with "[][$Hσ]").
Qed.
Next Obligation.
  iIntros (???). destruct m; simpl.
  - iIntros (???) "(% & H & _)". destruct σ. iDestruct sem_sig_prop as "H1". by iApply "H1".
  - iIntros (???) "H". destruct σ. iDestruct sem_sig_prop as "H1". by iApply "H1".
Qed.                                                           
(* TODO: Import the rest from sem_sig *)

(* (* Notations. *)
   Notation "'∀ₛ..' tt , κ ⇒ ι" := 
     (sem_sig_eff (λ tt, κ%T) (λ tt, ι%T))
     (at level 80, tt binder, κ at next level, ι at next level, right associativity,
      format "'[ ' '∀ₛ..'  tt ,  κ  ⇒  ι  ']'") : sem_sig_scope.
   
   Notation "'∀ₛ' x .. y , κ ⇒ ι" := 
     (sem_sig_eff 
     (@tele_app ((TeleS (λ x, .. (TeleS (λ y, TeleO)) ..))) (sem_ty _) (λ x, .. (λ y, κ%T) ..)) 
     (@tele_app ((TeleS (λ x, .. (TeleS (λ y, TeleO)) ..))) (sem_ty _) (λ x, .. (λ y, ι%T) ..))) 
     (at level 80, x binder, y binder, κ at next level, ι at next level, right associativity,
      format "'[ ' '∀ₛ' x .. y ,  κ  ⇒  ι  ']'") : sem_sig_scope. *)

Notation "κ ⇒ ι" := 
  (@sem_sig_eff _ _ (λ _, κ%T) (λ _, ι%T))
  (at level 80, right associativity,
   format "'[ ' κ  ⇒  ι  ']'") : sem_sig_scope.

Notation "¡[ m ] σ" := (sem_sig_flip_mbang m σ) (at level 10) : sem_sig_scope.
Notation "¡ σ" := (sem_sig_flip_mbang OS σ) (at level 10) : sem_sig_scope.

Notation "κ '=[' m ']=>' ι" := 
  (sem_sig_flip_mbang m (@sem_sig_eff _ _ (λ _, κ%T) (λ _, ι%T)))
  (at level 80, right associativity,
   format "'[ ' κ  =[ m ]=>  ι  ']'") : sem_sig_scope.

(* Notation "'∀ₛ..' tt , κ '=[' m ']=>' ι" := 
     (sem_sig_flip_mbang m (sem_sig_eff (λ tt, κ%T) (λ tt, ι%T)))
     (at level 80, tt binder, κ at next level, ι at next level,  right associativity,
      format "'[ ' '∀ₛ..'  tt ,  κ  =[ m ]=>  ι  ']'") : sem_sig_scope.
   
   Notation "'∀ₛ' x .. y , κ '=[' m ']=>' ι" := 
     (sem_sig_flip_mbang m (
       (sem_sig_eff 
       (@tele_app ((TeleS (λ x, .. (TeleS (λ y, TeleO)) ..))) (sem_ty _) (λ x, .. (λ y, κ%T) ..)) 
       (@tele_app ((TeleS (λ x, .. (TeleS (λ y, TeleO)) ..))) (sem_ty _) (λ x, .. (λ y, ι%T) ..))))) 
     (at level 80, x binder, y binder, κ at next level, ι at next level, right associativity,
      format "'[ ' '∀ₛ' x .. y ,  κ  =[ m ]=>  ι  ']'") : sem_sig_scope. *)


Section sig_properties.

Global Instance sem_sig_eff_ne2 {Σ} {αs : sem_ty Σ} :
  NonExpansive2 (@sem_sig_eff Σ αs).
Proof.
Admitted. 

Global Instance sem_sig_eff_ne {Σ} {αs : sem_ty Σ} A :
  NonExpansive (@sem_sig_eff Σ αs A).
Proof. iIntros (????). by f_equiv. Qed.

Global Instance sem_sig_eff_alt_ne {Σ} {αs : sem_ty Σ} :
  NonExpansive (@sem_sig_eff Σ αs).
Proof. iIntros (?????). by f_equiv. Qed.

(* Global Instance sem_sig_eff_pers_mono_prot {Σ} {αs : sem_ty Σ} A B :
     PersMonoProt (@sem_sig_eff Σ αs A B).
   Proof. constructor. iApply pmono_prot_prop. Qed. *)

(* Lemma upcl_sem_sig_eff {Σ} {TT : tele} A B v Φ :
     iEff_car (upcl MS (@sem_sig_eff Σ TT A B)) v Φ ⊣⊢
       (∃.. αs, ∃ a, ⌜ a = v ⌝ ∗ (A αs a) ∗ □ (∀ b, (B αs b) -∗ Φ b))%I.
   Proof.
     assert (Hequiv: iEff_car (upcl MS (sem_sig_eff A B)) v Φ ≡ iEff_car (sem_sig_eff A B) v Φ).
     { f_equiv. apply non_dep_fun_equiv. by rewrite pers_upcl_id. }
     rewrite Hequiv. by apply sem_sig_eff_eq.
   Qed. *)

Global Instance sem_sig_flip_mbang_mono_prot {Σ} σ :
  MonoProt (@sem_sig_flip_mbang Σ OS σ).
Proof.
  constructor.
  iIntros (????) "HΦimp (%&H&Himp)".
  iExists _.  iFrame. iIntros (??) "!> HQ".
  iDestruct ("Himp" with "HQ") as "HΦ".
  by iApply "HΦimp".
Qed. 

Global Instance sem_sig_flip_mbang_ne {Σ} m : NonExpansive (@sem_sig_flip_mbang Σ m).
Proof.
(*   rewrite /sem_sig_flip_mbang. 
     intros ???????.
     apply non_dep_fun_dist. 
     intros ?. 
     apply non_dep_fun_dist.
     destruct m; simpl.
     - admit.
     - apply non_dep_fun_dist.
     by apply iEff_car_ne.
   Qed. *)
Admitted.
Global Instance sem_sig_flip_mbang_proper {Σ} m : Proper ((≡) ==> (≡)) (@sem_sig_flip_mbang Σ m).
Proof. apply ne_proper. apply _. Qed.

(* Global Instance sem_sig_eff_mbang_ne2 {Σ} {TT : tele} m :
     NonExpansive2 (λ A B, @sem_sig_flip_mbang Σ m (@sem_sig_eff Σ TT A B)).
   Proof.
     iIntros (???????). by repeat f_equiv.
   Qed. *)

End sig_properties.

Section once_sig.

  (* Once Constraint *)

  Class OnceS {Σ} (σ : sem_sig Σ) := {
    sig_le_mfbang_elim : (⊢ (¡ σ) ≤ₛ σ)
  }.

End once_sig.

Section sig_sub_typing.

  (* Subtyping on Signatures *)
  (* TODO: finish lemmas in here *)
  
  Lemma sig_le_refl {Σ} (σ : sem_sig Σ) : ⊢ σ ≤ₛ σ.
  Proof. iApply iThy_le_refl. Qed.
  
  Lemma sig_le_trans {Σ} (σ₁ σ₂ σ₃: sem_sig Σ) : 
      σ₁ ≤ₛ σ₂ -∗
      σ₂ ≤ₛ σ₃ -∗
      σ₁ ≤ₛ σ₃. 
  Proof. 
    iIntros "#Hp₁₂ #Hp₂₃"; rewrite /sig_le /tc_opaque. 
    iApply iThy_le_trans; [iApply "Hp₁₂"|iApply "Hp₂₃"].
  Qed.
  
  (* Lemma sig_le_eff {Σ} {TT : tele} (ι₁ ι₂ κ₁ κ₂ : tele_arg TT → sem_ty Σ) :
       □ (∀.. α, (ι₁ α) ≤ₜ (ι₂ α)) -∗
       □ (∀.. α, (κ₂ α) ≤ₜ (κ₁ α)) -∗
       (∀ₛ.. α , ι₁ α ⇒ κ₁ α) ≤ₛ (∀ₛ.. α , ι₂ α ⇒ κ₂ α).
     Proof.
       iIntros "#Hι₁₂ #Hκ₂₁". 
       iIntros (v Φ) "!#".
       rewrite !sem_sig_eff_eq.
       iIntros "(%α & %w & <- & Hι₁ & HκΦ₁)".
       iExists α, w; iSplitR; first done.
       iSplitL "Hι₁".
       { iApply ("Hι₁₂" with "Hι₁"). }
       simpl. iDestruct "HκΦ₁" as "#HκΦ₁".
       iIntros "!# %b Hκ₂". iApply "HκΦ₁".
       iApply ("Hκ₂₁" with "Hκ₂").
     Qed. *)
  
  Lemma sig_le_mfbang_intro {Σ} m (σ : sem_sig Σ) :
    ⊢ σ ≤ₛ (¡[ m ] σ).
  Proof.
    rewrite /sem_sig_flip_mbang. 
    iIntros (v1 v2 Φ) "!# Hσ". destruct m; try done; simpl.
    iExists Φ. iFrame. iNext. iIntros "% % $".
  Qed.
  
  Lemma sig_le_mfbang_elim_ms {Σ} (σ : sem_sig Σ) :
    ⊢ (¡[ MS ] σ) ≤ₛ σ.
  Proof.
    rewrite /sem_sig_flip_mbang. 
    iIntros (v1 v2 Φ)"!#". simpl. iIntros "$". 
  Qed.
  
  Lemma sig_le_mfbang_comp {Σ} (m m' : mode) (σ σ' : sem_sig Σ) :
    m' ≤ₘ m -∗ σ ≤ₛ σ' -∗ 
    (¡[ m ] σ) ≤ₛ (¡[ m' ] σ').
  Proof.
    iIntros "#Hlem #Hleσ". destruct m.
    - iDestruct (mode_le_OS_inv with "Hlem") as "->".
      rewrite /sig_le /sem_sig_flip_mbang /tc_opaque. simpl.
      by iApply iThy_le_iThyMono.
    - iApply sig_le_trans; first iApply sig_le_mfbang_elim_ms. 
      iApply sig_le_trans; first iApply (sig_le_mfbang_intro m').
      rewrite /sig_le /sem_sig_flip_mbang /tc_opaque.
      by iApply iThy_le_iThyIfMono.
  Qed.
  
  Lemma sig_le_mfbang_idemp {Σ} m (σ : sem_sig Σ) :
    ⊢ (¡[ m ] (¡[ m ] σ)) ≤ₛ ((¡[ m ] σ)).
  Proof.
    iIntros (v1 v2 Φ) "!# H". rewrite /sem_sig_flip_mbang /=.
    destruct m;[|done].
    simpl. iDestruct "H" as (Q') "(H & HQ')". iDestruct "H" as (Q'') "(H & HQ'')".
    iExists Q''. iFrame. iIntros "!> % % HQ". iApply "HQ'". by iApply "HQ''".
  Qed.       

  Global Instance sig_fbang_once_sig {Σ} (σ : sem_sig Σ) : OnceS (¡ σ)%S.
  Proof. constructor. iIntros. iApply sig_le_mfbang_idemp. Qed.

  (* Global Instance sig_eff_os_once {TT : tele} {Σ} (A B : tele_arg TT → sem_ty Σ) :
       OnceS (∀ₛ.. αs , (A αs) =[ OS ]=> (B αs))%S.
     Proof. apply _. Qed. *)
  
  Lemma sig_le_mfbang_comm {Σ} m m' (σ : sem_sig Σ) :
    ⊢ (¡[ m ] (¡[ m' ] σ)) ≤ₛ (¡[ m' ] (¡[ m ] σ)).
  Proof. 
    destruct m, m'.
    - iApply sig_le_refl.
    - iApply sig_le_trans; first iApply sig_le_mfbang_comp.
      { iApply mode_le_refl. }
      { iApply sig_le_mfbang_elim_ms. }
      iApply sig_le_mfbang_intro.
    - iApply sig_le_trans; first iApply sig_le_mfbang_elim_ms.
      iApply sig_le_mfbang_comp; first iApply mode_le_refl. 
      iApply sig_le_mfbang_intro.
    - iApply sig_le_refl.
  Qed.
  
  (* Corollary sig_le_eff_mode {Σ} {TT : tele} (ι κ : tele_arg TT → sem_ty Σ) :
       ⊢ (∀ₛ.. α , ι α =[ MS ]=> κ α) ≤ₛ (∀ₛ.. α , ι α =[ OS ]=> κ α).
     Proof. 
       iApply sig_le_mfbang_comp; first iApply mode_le_MS. 
       iApply sig_le_refl. 
     Qed. *)

End sig_sub_typing.

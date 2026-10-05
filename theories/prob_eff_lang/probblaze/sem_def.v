(* sem_def.v *)

(* This file contains the definition of types, signatures, rows, environments and relations. *)

From iris.proofmode Require Import base proofmode classes.
From iris.algebra Require Import list ofe gmap.

From clutch.prob_eff_lang.probblaze Require Import logic notation.

(* -------------------------------------------------------------------------- *)
(** Inhabited. *)
(** OFE Structure. *)
Canonical Structure modeO := leibnizO mode.
Global Instance mode_inhabited : Inhabited mode := populate MS.

(** * Semantic Types. *)

(* We equip sem_ty with the OFE structure val -d> iPropO
 * which is the OFE of non-dependently-typed functions over a discrete domain *)
Definition sem_ty Σ := (val -d> val -d> iPropO Σ)%type.

Declare Scope sem_ty_scope.
Delimit Scope sem_ty_scope with T.

(* Monotonic Protocol. *)
  Class MonoProt {Σ} (Ψ : iThy Σ) := {
    monotonic_prot e1 e2 Φ Φ' :
      (∀ e1' e2', Φ e1' e2' -∗ Φ' e1' e2') -∗ Ψ e1 e2 Φ -∗ Ψ e1 e2 Φ'
  }.

(** * Persistently Monotonic Protocols. *)
(** Persistently Monotonic Protocols are defined using a record, which bundles an iThy theory
[pmono_prot_car : iThy Σ] together with a proof of it being persistently monotonic. *)

Definition pers_mono {Σ} (Ψ : iThy Σ) : iProp Σ :=
  (∀ (v1 v2 : expr) (Φ Φ' : expr → expr → iPropI Σ),
      □ (∀ w1 w2 : expr, Φ w1 w2 -∗ Φ' w1 w2) -∗ Ψ v1 v2 Φ -∗ Ψ v1 v2 Φ')%I.

Record pmono_prot Σ := PMonoProt {
  pmono_prot_car :> iThy Σ;
  pmono_prot_prop : ⊢ pers_mono pmono_prot_car
}.
Arguments PMonoProt {_} _%_I {_}.
Arguments pmono_prot_car {_} _ : simpl never.

(** * The COFE structure on pmono protocols *)
Section pmono_prot_cofe.
  Context {Σ : gFunctors}.

  Instance pmono_prot_equiv : Equiv (pmono_prot Σ) := λ Ψ1 Ψ2, pmono_prot_car Ψ1 ≡ pmono_prot_car Ψ2.
  Instance pmono_prot_dist : Dist (pmono_prot Σ) := λ n Ψ1 Ψ2, pmono_prot_car Ψ1 ≡{n}≡ pmono_prot_car Ψ2.
  Lemma pmono_prot_ofe_mixin : OfeMixin (pmono_prot Σ).
  Proof. by apply (iso_ofe_mixin pmono_prot_car). Qed.
  Canonical Structure pmono_protO := Ofe (pmono_prot Σ) pmono_prot_ofe_mixin.

  (* TODO: Move to another file *)
  Lemma non_dep_fun_dist A B x (f f' : A -d> B) n : 
    f ≡{n}≡ f' → (f x)≡{n}≡(f' x).
  Proof. intros H. f_equiv. Qed.
  Lemma non_dep_fun_equiv A B x (f f' : A -d> B) : 
    f ≡ f' → f x ≡ f' x.
  Proof. intros H. f_equiv. Qed.

  Global Instance pmono_prot_cofe : Cofe pmono_protO.
  Proof.
    apply (iso_cofe_subtype' (λ Ψ, ⊢ pers_mono Ψ)
      (@PMonoProt _) pmono_prot_car)=> //.
    - by intros [].
    - apply bi.limit_preserving_emp_valid.
      intros ????. rewrite /pers_mono.
      do 10 f_equiv; apply non_dep_fun_dist;
      by apply (non_dep_fun_dist _  _ a x y). 
  Qed.

  Global Program Instance pmono_prot_inhabited : Inhabited (pmono_prot Σ) := 
    populate (PMonoProt inhabitant).
  Next Obligation.
    rewrite /pers_mono /inhabitant /=. iIntros (????) "_ _ //".
  Qed.

  Global Instance pmono_prot_car_ne n : Proper (dist n ==> dist n) pmono_prot_car.
  Proof. by intros Ψ1 Ψ2 ?. Qed.
  Global Instance pmono_prot_car_proper : Proper ((≡) ==> (≡)) (@pmono_prot_car Σ).
  Proof. by intros Ψ1 Ψ2 ?. Qed.

  Global Instance pmono_prot_ne n Ψ : Proper ((λ _ _, True) ==> dist n) (@PMonoProt Σ Ψ).
  Proof. intros P1 P2 _ ?. apply non_dep_fun_dist. rewrite /pmono_prot_car //. Qed.
  Global Instance pmono_prot_proper Ψ : Proper ((λ _ _, True) ==> (≡)) (@PMonoProt Σ Ψ).
  Proof. intros P1 P2 _ ?. apply non_dep_fun_equiv. rewrite /pmono_prot_car //. Qed.

  Global Program Instance pmono_prot_bottom : Bottom (pmono_prot Σ) := @PMonoProt Σ iThyBot _.
  Next Obligation. rewrite /pers_mono. iIntros (????) "_ [] //". Qed.

End pmono_prot_cofe.

Lemma pmono_prot_equivI {Σ} (Ψ1 Ψ2 : pmono_prot Σ) :
  Ψ1 ≡ Ψ2 ⊢@{iProp Σ} (pmono_prot_car Ψ1) ≡ (pmono_prot_car Ψ2).
Proof. iIntros "H". by iRewrite "H". Qed.

Lemma pmono_prot_iEff_equivI {Σ} (Ψ1 Ψ2 : pmono_prot Σ) :
  Ψ1 ≡ Ψ2 ⊢@{iProp Σ} ∀ v1 v2 Φ, (pmono_prot_car Ψ1) v1 v2 Φ ≡ (pmono_prot_car Ψ2) v1 v2 Φ.
Proof.
  iIntros "H % % %". iPoseProof (pmono_prot_equivI with "H") as "HH".
  iPoseProof (discrete_fun_equivI (pmono_prot_car Ψ1) (pmono_prot_car Ψ2)) as "HH2".
  iDestruct "HH2" as "[HH2f _]". iSpecialize ("HH2f" with "HH").
  iSpecialize ("HH2f" $! v1).
  iPoseProof (discrete_fun_equivI (pmono_prot_car Ψ1 v1) (pmono_prot_car Ψ2 v1)) as "HH3".
  iDestruct "HH3" as "[HH3f _]". iSpecialize ("HH3f" with "HH2f").
  iSpecialize ("HH3f" $! v2).
  iPoseProof (ofe_morO_equivI (pmono_prot_car Ψ1 v1 v2) (pmono_prot_car Ψ2 v1 v2)) as "HH4".
  iDestruct "HH4" as "[HH4f _]". iSpecialize ("HH4f" with "HH3f").
  iSpecialize ("HH4f" $! Φ). iApply "HH4f".
Qed.

Lemma pmono_prot_distI {Σ} (Ψ1 Ψ2 : iThy Σ) (P1 : ⊢ pers_mono Ψ1) (P2 : ⊢ pers_mono Ψ2) n :
  Ψ1 ≡{n}≡ Ψ2 → (@PMonoProt Σ Ψ1 P1) ≡{n}≡ (@PMonoProt Σ Ψ2 P2).
Proof. intros H. done. Qed.

Arguments pmono_protO : clear implicits.

(** * Semantic Effect Signatures. *)

Definition sem_sig_val_prop {Σ} (labels : (label * label)) (Ψ : iThy Σ) : iProp Σ := 
  (∀ (e1 e2 : expr) Φ, Ψ e1 e2 Φ -∗ (let (op1,op2) := labels in ∃ (v1 v2 : val), ⌜ e1 = (do: op1 v1)%E ⌝ ∗ ⌜ e2 = (do: op2 v2)%E ⌝)).

Record sem_sig Σ := SemSig {
                        sem_sig_car :> pmono_prot Σ;
                        sem_sig_labels : (label * label);
                          }.
Arguments SemSig {_} {_} _%_I.
Arguments sem_sig_car {_} _ : simpl never.
Declare Scope sem_sig_scope.
Delimit Scope sem_sig_scope with S.

Section sem_sig_cofe.
  Context {Σ : gFunctors}.

  Instance sem_sig_equiv : Equiv (sem_sig Σ) := λ σ1 σ2, sem_sig_car σ1 ≡ sem_sig_car σ2 ∧ (sem_sig_labels Σ σ1) = (sem_sig_labels Σ σ2).
  Instance sem_sig_dist : Dist (sem_sig Σ) := λ n σ1 σ2, sem_sig_car σ1 ≡{n}≡ sem_sig_car σ2 
                                                         ∧ (sem_sig_labels Σ σ1) = (sem_sig_labels Σ σ2).
  Lemma sem_sig_ofe_mixin : OfeMixin (sem_sig Σ).
  Proof.
    apply (iso_ofe_mixin
      (A := prodO (pmono_protO Σ) (leibnizO (label * label)))
      (λ σ : sem_sig Σ, (sem_sig_car σ, sem_sig_labels _ σ))).
    all: reflexivity.
  Qed.
  Canonical Structure sem_sigO := Ofe (sem_sig Σ) sem_sig_ofe_mixin.
  Global Instance sem_sig_cofe : Cofe sem_sigO.
  Proof.
    apply (iso_cofe
      (A := prodO (pmono_protO Σ) (leibnizO (label * label)))
      (B := sem_sigO)
      (λ p, @SemSig Σ p.1 p.2)
      (λ σ : sem_sig Σ, (sem_sig_car σ, sem_sig_labels _ σ))).
    1: reflexivity.
    intros x; split; reflexivity.
  Qed.
 
  Global Program Instance sem_sig_inhabited : Inhabited (sem_sig Σ) := 
    populate (@SemSig Σ ⊥ _ ).
  Next Obligation. split; apply label_inhabited. Qed.
    
  Global Instance sem_sig_car_ne n : Proper (dist n ==> dist n) sem_sig_car.
  Proof. by intros ?? [? ?]. Qed.
  Global Instance sem_sig_car_proper : Proper ((≡) ==> (≡)) (@sem_sig_car Σ).
  Proof. by intros ?? [? ?]. Qed.
 
End sem_sig_cofe.

  
(** * Semantic Effect Row. *)
Definition iLblSig Σ : Type := list (list label * list label * sem_sig Σ).

Definition iLblSig_to_iLblThy {Σ} (s : iLblSig Σ) : iLblThy Σ :=
  map (fun '(l1, l2, ss) => (l1, l2, pmono_prot_car (sem_sig_car ss))) s.

Lemma in_iLblSig {Σ} (s : iLblSig Σ) (X : iThy Σ) l1s l2s:
  (l1s, l2s, X) ∈ iLblSig_to_iLblThy s → ∃ ss : sem_sig Σ, X = ss.
Proof. 
  induction s.
  - intros. by apply elem_of_nil in H.
  - intros. 
    apply elem_of_cons in H as [H | H]; [|by apply IHs].
    destruct a. destruct p. inversion H. eexists. done.
Qed.

Instance iLblSig_bot {Σ} : Bottom (iLblSig Σ) := [].

Definition sem_row_val_prop {Σ} (Ψ : iLblSig Σ) : iProp Σ := 
  ∀ (e1 e2 : expr) Φ, (to_iThy (iLblSig_to_iLblThy Ψ)) e1 e2 Φ -∗ ∃ k1 k2 (op1 op2 : label) (v1 v2 : val), ⌜ e1 = fill k1 (do: op1 v1)%E ⌝ ∗ ⌜ e2 = fill k2 (do: op2 v2)%E ⌝.

(* Semantic effect rows are also defined as persistently monotonic protocols 
   with the additional requirement that it can only be called with effect values of the form (effect op, v'). 
   Thus effect rows can be seen as morphisms from operations to sem_sig.
 *)

Definition pers_mono_row {Σ} (Ψ : iLblThy Σ) : iProp Σ :=
  (∀ (v1 v2 : expr) (Φ Φ' : expr → expr → iPropI Σ),
      □ (∀ w1 w2 : expr, Φ w1 w2 -∗ Φ' w1 w2) -∗ ∀ l1s l2s X, (⌜ (l1s, l2s, X) ∈ Ψ ⌝ ∗ iThyTraverse l1s l2s X v1 v2 Φ) -∗ (⌜ (l1s, l2s, X) ∈ Ψ ⌝ ∗ iThyTraverse l1s l2s X v1 v2 Φ'))%I.

Record sem_row Σ := SemRow {
                        sem_row_car :> iLblSig Σ;
                        sem_row_mono : ⊢ pers_mono_row (iLblSig_to_iLblThy sem_row_car);
}.
Arguments SemRow {_} _%_I.
Arguments sem_row_car {_} _ : simpl never.

Lemma iLblSig_to_iLblThy_proj {Σ} c Hpersc :
  iLblSig_to_iLblThy {| sem_row_car := c; sem_row_mono := Hpersc |} = @iLblSig_to_iLblThy Σ c. 
Proof. 
  done.
Qed. 

(** * The COFE structure on semantic rows *)
Section sem_row_cofe.
  Context {Σ : gFunctors}.

  Instance sem_row_equiv : Equiv (sem_row Σ) := λ ρ1 ρ2, iLblSig_to_iLblThy (sem_row_car ρ1) ≡ iLblSig_to_iLblThy (sem_row_car ρ2).
  Instance sem_row_dist : Dist (sem_row Σ) := λ n ρ1 ρ2, iLblSig_to_iLblThy (sem_row_car ρ1) ≡{n}≡ iLblSig_to_iLblThy (sem_row_car ρ2).
  Instance iLblSig_equiv : Equiv (iLblSig Σ) := λ ρ1 ρ2, iLblSig_to_iLblThy ρ1 ≡ iLblSig_to_iLblThy ρ2.
  Instance iLblSig_dist : Dist (iLblSig Σ) := λ n ρ1 ρ2, iLblSig_to_iLblThy ρ1 ≡{n}≡ iLblSig_to_iLblThy ρ2.

  Lemma iLblSig_ofe_mixin : OfeMixin (iLblSig Σ).
  Proof.
    by apply (iso_ofe_mixin iLblSig_to_iLblThy). 
  Qed.

  Canonical Structure iLblSigO := Ofe (iLblSig Σ) iLblSig_ofe_mixin.
  Instance iLblSig_cofe : Cofe iLblSigO.
  Proof.
    apply (iso_cofe
      (A := listO
        (prodO (prodO (listO labelO) (listO labelO)) (pmono_protO Σ)))
      (B := iLblSigO)
      (map (λ '(l1, l2, p), (l1, l2, @SemSig Σ p inhabitant)))
      (map (λ '(l1, l2, ss), (l1, l2, sem_sig_car ss)))).
    - intros n y1 y2.
      unfold dist, iLblSig_dist.
      change (ofe_dist iLblSigO n y1 y2)
        with (iLblSig_to_iLblThy y1 ≡{n}≡ iLblSig_to_iLblThy y2).
      rewrite !list_dist_Forall2.
      unfold iLblSig_to_iLblThy.
      setoid_rewrite list_dist_Forall2.
      generalize dependent y2.
      induction y1 as [|[[a1 a2] s1] y1 IH]; intros [|[[b1 b2] s2] y2].
      1: (split; intros _; constructor).
      1: (split; intros H; inversion H).
      1: (split; intros H; inversion H).
      simpl. rewrite !Forall2_cons. rewrite (IH y2). reflexivity.
    - intros x.
      induction x as [|[[l1 l2] p] x IH]; [done|].
      simpl. rewrite IH. reflexivity.
  Qed.
  
  Lemma sem_row_ofe_mixin : OfeMixin (sem_row Σ).
  Proof. by apply (iso_ofe_mixin sem_row_car). Qed.
  Canonical Structure sem_rowO := Ofe (sem_row Σ) sem_row_ofe_mixin.
  Global Instance sem_row_cofe : Cofe sem_rowO.
  Proof.
    assert (Hgen : ∀ L : iLblThy Σ, ⊢ pers_mono_row L).
    { iIntros (L v1 v2 Φ Φ') "#H1". iIntros (l1s l2s X) "[%Hin H2]".
      iSplitR; first done.
      rewrite /iThyTraverse /=.
      iDestruct "H2" as (e1' e2' k1 k2 S) "(->&%&->&%&HX&#Hcont)".
      iExists e1', e2', k1, k2, S. iFrame "HX".
      iSplit; first done. iSplit; first done.
      iSplit; first done. iSplit; first done.
      iModIntro. iIntros (s1 s2) "HS". iApply "H1". by iApply "Hcont". }
    apply (iso_cofe_subtype' (λ Ψ, ⊢ pers_mono_row (iLblSig_to_iLblThy Ψ))
      (λ Ψ HΨ, @SemRow Σ Ψ HΨ) sem_row_car).
    - intros y. apply Hgen.
    - intros n y1 y2. reflexivity.
    - intros x Hx. reflexivity.
    - apply Build_LimitPreserving; intros; apply Hgen.
  Qed.

  Global Program Instance sem_row_inhabited : Inhabited (sem_row Σ) := 
    populate (@SemRow Σ ⊥ _ (* _ *)).
  Next Obligation. iIntros (????) "?". iIntros (???) "(%Hcontra & _)". by apply elem_of_nil in Hcontra. Qed.

  Global Instance sem_row_car_ne n : Proper (dist n ==> dist n) sem_row_car.
  Proof. by intros Ψ1 Ψ2 ?. Qed.
  Global Instance sem_row_car_proper : Proper ((≡) ==> (≡)) (@sem_row_car Σ).
  Proof. by intros Ψ1 Ψ2 ?. Qed.
  
  Global Instance sem_row_ne n Ψ : Proper ((λ _ _, True) ==> dist n) (@SemRow Σ Ψ).
  Proof. intros P1 P2 _. unfold dist, sem_row_dist; simpl; reflexivity. Qed.
  Global Instance sem_row_proper Ψ : Proper ((λ _ _, True) ==> (≡)) (@SemRow Σ Ψ).
  Proof. intros P1 P2 _. unfold equiv, sem_row_equiv; simpl; reflexivity. Qed.

End sem_row_cofe.

Declare Scope sem_row_scope.
Delimit Scope sem_row_scope with R.

(** The Type Environment  *)

Global Instance elem_binder_string : (ElemOf binder (list string)) | 10 := 
  (λ b xs, match b with
              BAnon => False%type
            | BNamed x => x ∈ xs
           end).

Definition cons_maybe {A} (x : binder * A) (xs : list (string * A)) : list (string * A) :=
  match x with
    (BAnon, _) => xs
  | (BNamed x', a) => (x',a) :: xs
  end.
Infix "::?" := cons_maybe (at level 60, right associativity) : list_scope.


Definition env Σ := (list (string * sem_ty Σ)).

Declare Scope sem_env_scope.
Delimit Scope sem_env_scope with EN.

(** The domain of the environment. *)
Definition env_dom {Σ} (Γ : env Σ) : list string := (map fst Γ).
Global Opaque env_dom.

Fixpoint env_sem_typed {Σ} (Γ : env Σ) (γ : gmap string (val*val)) : iProp Σ :=
  match Γ with
   | [] => emp
    | (x,A) :: Γ' => (∃ v1 v2, ⌜ γ !! x = Some (v1, v2) ⌝ ∗ A v1 v2) ∗ 
                     env_sem_typed Γ' γ
  end.

Notation "Γ ⊨ₑ γ" := (env_sem_typed Γ γ) (at level 70).

Global Instance env_sem_typed_into_exist {Σ} x τ (Γ : env Σ) γ : 
  IntoExist ((x, τ) :: Γ ⊨ₑ γ) (λ vv, ⌜ γ !! x = Some vv ⌝ ∗ τ vv.1 vv.2 ∗ Γ ⊨ₑ γ)%I (to_ident_name vv).
Proof.
  rewrite /IntoExist /=. iIntros "[(% & % & Hrw & Hτ) HΓ]". 
  iExists (v1,v2). iFrame.
Qed.

Global Instance env_sem_typed_from_exist {Σ} x τ (Γ : env Σ) γ: 
  FromExist ((x, τ) :: Γ ⊨ₑ γ) (λ vv, ⌜ γ !! x = Some vv ⌝ ∗ τ vv.1 vv.2 ∗ Γ ⊨ₑ γ)%I .
Proof.
  rewrite /FromExist /=. iIntros "[% (Hrw & Hτ & HΓ)]".
  iFrame.   rewrite -(surjective_pairing x0). iFrame.
Qed.

Global Opaque env_sem_typed.
(* Sub-typing and relations *)

(* Relation on mode *)
Definition mode_le {Σ} (m m' : modeO) : iProp Σ := 
  (m ≡ m' ∨ m' ≡ MS)%I.

Definition ty_le {Σ} (A B : sem_ty Σ) := tc_opaque (□ (∀ v1 v2, A v1 v2 -∗ B v1 v2))%I.
Global Instance ty_le_persistent {Σ} τ τ' :
  Persistent (@ty_le Σ τ τ').
Proof.
  unfold ty_le, tc_opaque. apply _.
Qed.

Definition sig_le {Σ} (σ σ' : sem_sig Σ) := tc_opaque (⌜ sem_sig_labels Σ σ = sem_sig_labels Σ σ' ⌝ ∗ iThy_le σ σ')%I.
Global Instance sig_le_persistent {Σ} σ σ' :
  Persistent (@sig_le Σ σ σ').
Proof.
  unfold sig_le, tc_opaque. apply _.
Qed.


Definition row_le `{probblazeRGS Σ} (ρ ρ' : sem_row Σ) := tc_opaque (to_iThy_le (iLblSig_to_iLblThy ρ) (iLblSig_to_iLblThy ρ'))%I.

Global Instance row_le_persistent `{probblazeRGS Σ} ρ ρ' :
  Persistent (row_le ρ ρ').
Proof.
  unfold row_le, tc_opaque. apply _.
Qed.

Definition env_le {Σ} (Γ₁ Γ₂ : env Σ) :=
  tc_opaque (□ (∀ γ,  Γ₁ ⊨ₑ γ -∗  Γ₂ ⊨ₑ γ))%I.
Global Instance env_le_persistent {Σ} (Γ Γ' : env Σ) :
  Persistent (env_le Γ Γ').
Proof.
  unfold env_le, tc_opaque. apply _.
Qed.

Notation "m '≤ₘ' m'" := (mode_le m m') (at level 98).
Notation "m '≤ₘ@{' Σ '}' m'" := (@mode_le Σ m m') (at level 98).
Notation "τ '≤ₜ' κ" := (ty_le τ%T κ%T) (at level 98).
Notation "τ '≤ₜ@{' Σ '}' κ" := (@ty_le Σ τ%T κ%T) (at level 98).
Notation "σ '≤ₛ' σ'" := (sig_le σ%S σ'%S) (at level 98).
Notation "σ '≤ₛ@{' Σ '}' σ'" := (@sig_le Σ σ%S σ'%S) (at level 98).
Notation "ρ '≤ᵣ' ρ'" := (row_le ρ%R ρ'%R) (at level 98).
Notation "ρ '≤ᵣ@{' Σ '}' ρ'" := (@row_le Σ ρ%R ρ'%R) (at level 98).
Notation "Γ₁ '≤ₑ' Γ₂" := (env_le Γ₁%EN Γ₂%EN) (at level 98).
Notation "Γ₁ '≤ₑ@{' Σ '}' Γ₂" := (@env_le Σ Γ₁%EN Γ₂%EN) (at level 98).

Global Instance mode_le_ne {Σ} :
  NonExpansive2 (@mode_le Σ).
Proof. intros ???????. rewrite /mode_le. by repeat f_equiv. Qed.

Global Instance mode_le_proper {Σ} :
  Proper ((≡) ==> (≡) ==> (≡)) (@mode_le Σ).
Proof. apply ne_proper_2. apply _. Qed.

Global Instance ty_le_ne {Σ} :
  NonExpansive2 (@ty_le Σ).
Proof.
  intros n τ κ Hequiv τ' κ' Hequiv'. 
  rewrite /ty_le /tc_opaque. repeat f_equiv; by apply non_dep_fun_dist.
Qed.

Global Instance ty_le_proper {Σ} :
  Proper ((≡) ==> (≡) ==> (≡)) (@ty_le Σ).
Proof. apply ne_proper_2. apply _. Qed.

Global Instance sig_le_ne {Σ} :
  NonExpansive2 (@sig_le Σ).
Proof.
  intros n σ₁ σ₂ Hequiv σ₁' σ₂' Hequiv'.
  rewrite /sig_le /tc_opaque.
  destruct Hequiv as [Hcar Hlbl]. destruct Hequiv' as [Hcar' Hlbl']. f_equiv.
  - rewrite Hlbl Hlbl'. done.
  - by apply iThy_le_ne.
Qed.

Global Instance sig_le_proper {Σ} :
  Proper ((≡) ==> (≡) ==> (≡)) (@sig_le Σ).
Proof. apply ne_proper_2. apply _. Qed. 

Global Instance row_le_ne `{probblazeRGS Σ} :
  NonExpansive2 (row_le).
Proof.
  intros n ρ₁ ρ₂ Hequiv ρ₁' ρ₂' Hequiv'.
  rewrite /row_le /tc_opaque. unfold to_iThy_le. do 2 f_equiv.
  - apply to_iThy_ne, Hequiv.
  - apply to_iThy_ne, Hequiv'.
  - f_equiv. f_equiv.
    + apply valid_ne, Hequiv'.
    + apply valid_ne, Hequiv.
  - f_equiv. f_equiv.
    + apply distinct'_ne, Hequiv'.
    + apply distinct'_ne, Hequiv.
Qed.

Global Instance row_le_proper `{probblazeRGS Σ} :
  Proper ((≡) ==> (≡) ==> (≡)) (row_le).
Proof. apply ne_proper_2. apply _. Qed.

  

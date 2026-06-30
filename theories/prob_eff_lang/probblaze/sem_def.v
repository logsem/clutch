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

(* ADAPATED *)
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
                            (* sem_sig_prop : ⊢ sem_sig_val_prop sem_sig_labels (pmono_prot_car sem_sig_car); *)
                          }.
Arguments SemSig {_} {_} _%_I (* {_} *).
Arguments sem_sig_car {_} _ : simpl never.
Declare Scope sem_sig_scope.
Delimit Scope sem_sig_scope with S.

Section sem_sig_cofe.
  Context {Σ : gFunctors}.

  Instance sem_sig_equiv : Equiv (sem_sig Σ) := λ σ1 σ2, sem_sig_car σ1 ≡ sem_sig_car σ2.
  Instance sem_sig_dist : Dist (sem_sig Σ) := λ n σ1 σ2, sem_sig_car σ1 ≡{n}≡ sem_sig_car σ2.
  Lemma sem_sig_ofe_mixin : OfeMixin (sem_sig Σ).
  Proof. by apply (iso_ofe_mixin sem_sig_car). Qed.
  Canonical Structure sem_sigO := Ofe (sem_sig Σ) sem_sig_ofe_mixin.
  Global Instance sem_sig_cofe : Cofe sem_sigO.
  Proof.
    (* apply (iso_cofe_subtype' (λ Ψ, ⊢ sem_row_val_prop (to_iThy Ψ)) (@SemRow _ _) sem_row_car)=> //.
       - by intros [].
       - apply bi.limit_preserving_emp_valid.
         intros ????. rewrite /sem_row_val_prop. 
         do 6 f_equiv. apply non_dep_fun_dist.  *)
  Admitted.
 
  Global Program Instance sem_sig_inhabited : Inhabited (sem_sig Σ) := 
    populate (@SemSig Σ ⊥ _ ).
  Next Obligation. split; apply label_inhabited. Qed.
    
  Global Instance sem_sig_car_ne n : Proper (dist n ==> dist n) sem_sig_car.
  Proof. by intros Ψ1 Ψ2 ?. Qed.
  Global Instance sem_sig_car_proper : Proper ((≡) ==> (≡)) (@sem_sig_car Σ).
  Proof. by intros Ψ1 Ψ2 ?. Qed.
 
End sem_sig_cofe.

  
(** * Semantic Effect Row. *)

(* Record iLblSig Σ := LblSig {
     iLblSig_car :>
       list (list label * list label * sem_sig Σ)
                         }.
   Arguments LblSig {_} _%_I.
   Arguments iLblSig_car {_} _ : simpl never. *)
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
    
(* Coercion iLblSig_to_iLblThy : iLblSig >-> iLblThy. *)

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
                        (* sem_row_prop : ⊢ sem_row_val_prop sem_row_car *)
}.
Arguments SemRow {_} _%_I (* {_} *).
Arguments sem_row_car {_} _ : simpl never.

(** * The COFE structure on semantic rows *)
(* TODO: proof COFE structure of sem_row *)
Section sem_row_cofe.
  Context {Σ : gFunctors}.

  Global Instance sem_row_equiv : Equiv (sem_row Σ) := λ ρ1 ρ2, iLblSig_to_iLblThy (sem_row_car ρ1) ≡ iLblSig_to_iLblThy (sem_row_car ρ2).
  Global Instance sem_row_dist : Dist (sem_row Σ) := 
    λ n ρ1 ρ2, 
      match n with
      | 0 => True
      | S m => iLblSig_to_iLblThy (sem_row_car ρ1) ≡{n}≡ iLblSig_to_iLblThy (sem_row_car ρ2)
      end.
  Global Instance iLblSig_equiv : Equiv (iLblSig Σ) := λ ρ1 ρ2, iLblSig_to_iLblThy ρ1 ≡ iLblSig_to_iLblThy ρ2.
  Global Instance iLblSig_dist : Dist (iLblSig Σ) := 
    λ n ρ1 ρ2, 
      match n with
      | 0 => True
      | S m => (iLblSig_to_iLblThy ρ1) ≡{n}≡ (iLblSig_to_iLblThy ρ2)
      end. 

  Global Instance iLblSig_to_iLblThy_proper : Proper ((≡) ==> (≡)) iLblSig_to_iLblThy.
  Proof. solve_proper. Qed.

  Lemma iLblSig_to_iLblThy_ne_1 : ∀ n, 1 ≤ n → Proper (dist n ==> dist n) iLblSig_to_iLblThy.
  Proof.
    intros ? Hlt X Y Heq.
    destruct n; first inversion Hlt.
    done.
  Qed. 

  Lemma iLblSig_ofe_mixin : OfeMixin (iLblSig Σ).
  Proof.
    split.
    - intros ??. split; intros Heq.
      + intros ?. unfold dist, iLblSig_dist.
        destruct n; first done.
        by apply listO.
      + apply listO.
        intros n. 
        set (m := n `max` 1).
        specialize Heq with m. 
        unfold dist,iLblSig_dist in Heq. 
        assert (∃ m', m = S m') as (m'&Hm). 
        { destruct n; eexists; unfold m; [by rewrite Nat.max_0_l|by rewrite Nat.max_l; last lia]. }
        rewrite Hm in Heq.
        eapply dist_le; first done.
        rewrite -Hm. apply Nat.le_max_l.
    - intros n. split.
      + intros ?. destruct n; first done. by apply listO. 
      + intros ?? Heq. 
        unfold dist, iLblSig_dist in *. destruct n; done. 
      + intros ??? Heq1 Heq2. unfold dist, iLblSig_dist in *. 
        destruct n; first done.
        eapply transitivity; done.
    - intros n m ?? Heq Hlt.
      destruct n.
      + apply SIdx.le_0_r in Hlt. by subst. 
      + destruct m; first done.
        by eapply dist_le.
  Qed.
  
  Canonical Structure iLblSigO := Ofe (iLblSig Σ) iLblSig_ofe_mixin.
 
  Lemma sem_row_ofe_mixin : OfeMixin (sem_row Σ).
  Proof. by apply (iso_ofe_mixin sem_row_car). Qed.
  Canonical Structure sem_rowO := Ofe (sem_row Σ) sem_row_ofe_mixin.
  
   Lemma iLblSig_to_iLblThy_proj c Hpersc :
       iLblSig_to_iLblThy {| sem_row_car := c; sem_row_mono := Hpersc |} = @iLblSig_to_iLblThy Σ c. 
  Proof. 
    done.
  Qed. 
   
  Lemma iLblSig_to_iLblThy_tail_comm (ρ : iLblSig Σ) : 
    iLblSig_to_iLblThy (tail ρ) = tail (@iLblSig_to_iLblThy Σ ρ).
  Proof. 
    by destruct ρ.
  Qed. 

  Lemma sem_row_car_proj c Hpersc : 
    @sem_row_car Σ {| sem_row_car := c; sem_row_mono := Hpersc |} = c. 
  Proof. done. Qed.

  Lemma sem_row_car_ne_1 : 
    ∀ n, 1 ≤ n → Proper (dist n ==> list_dist n) sem_row_car.
  Proof.
    intros ? Hlt X Y Heq.
    destruct n; first inversion Hlt. 
    unfold dist,sem_row_dist,list_dist in *.
    generalize dependent (sem_row_car Y). clear Y.
    induction (sem_row_car X) as [| ((xs1,xs2),x) xs] => Y Heq;
    destruct Y as [| ((ys1,ys2),y) ys]; first done; inversion Heq; subst.
    constructor.
    - done.
    - by apply IHxs.
  Qed. 

  Lemma iLblSig_to_iLblThy_nil (ρ : sem_row Σ): 
    iLblSig_to_iLblThy ρ = [] → sem_row_car ρ = [].
  Proof.
    intros. destruct ρ.
    rewrite sem_row_car_proj. rewrite iLblSig_to_iLblThy_proj in H. destruct sem_row_car0; done.
  Qed.   
  Lemma iLblSig_to_iLblThy_nil_sig (ρ : iLblSig Σ): 
    iLblSig_to_iLblThy ρ = [] → ρ = [].
  Proof.
    by destruct ρ.    
  Qed.    

  Program Definition sem_row_tail_chain (c : chain sem_rowO) : chain (listO (prodO (prodO (listO labelO) (listO labelO)) (sem_sig Σ))) := 
    {| chain_car := λ i, sem_row_car (c (i + 1%nat)%nat) |}.
  Next Obligation.
    intros c n m Hlt. simpl.
    assert (chain_car c (m + 1)%nat ≡{(n + 1)%nat}≡ chain_car c (n + 1)%nat) as Heq.
    { apply chain_cauchy. simpl in *. lia. }
    unfold dist, sem_row_dist in Heq. assert ((n + 1)%nat = S n) as HSn by lia.
    rewrite HSn in Heq.
    eapply dist_le in Heq; [|apply Nat.le_succ_diag_r]. 
    rewrite HSn.
    generalize dependent (sem_row_car (chain_car c (S n))).
    induction (sem_row_car (chain_car c (m + 1)%nat)) as [|((ls1,ls2), x) xs IH] => Y Heq;
        destruct Y as [|((ls1',ls2'),y) ys]; first done; inversion Heq.
    subst. 
    by constructor; last by apply IH.
  Qed. 

  Program Definition sem_row_list_bchain {n} (c : bchain sem_rowO n) : bchain (listO (prodO (prodO (listO labelO) (listO labelO)) (sem_sig Σ))) n := 
    {| bchain_car := 
        λ i Hlt, match n with
                 | 0 => sem_row_car (c i Hlt)
                 | 1%nat => sem_row_car (c i Hlt)
                 | S (S n') =>  
                     match i with
                     | 0 => sem_row_car (c 1%nat _)
                     | S i' => sem_row_car (c i Hlt)
                     end 
                 end |}.
  Next Obligation.
    intros n c m Hlt n' <- _. simpl; lia.
  Qed.
  Next Obligation.
    simpl. intros n c m p Hm Hp Hlt.
    destruct n; first inversion Hm.
    destruct n.
    { assert (p = m) as -> by lia. f_equiv. by assert (Hp = Hm) as -> by apply make_proof_irrel. }
    destruct p.
    { assert (m = 0%nat) as -> by lia. f_equiv. by assert (Hp = Hm) as -> by apply make_proof_irrel. }
    destruct m.
    { assert (bchain_car _ c (S p) Hp ≡{ 1%nat }≡ bchain_car _ c 1%nat (sem_row_list_bchain_obligation_1 (S (S n)) c 0%nat Hm n eq_refl eq_refl)) as Heq.
      - apply bchain_cauchy; simpl; lia.
      - apply sem_row_car_ne_1 in Heq; last done.
        eapply dist_le; first done; simpl; lia. }
    apply sem_row_car_ne_1; first lia.
    apply bchain_cauchy; simpl; lia.
  Qed.   
  
  (* Lemma compl_tail_chain c : compl (sem_row_tail_chain c) = sem_row_car (compl c). *)
  
  Global Instance default_head_ne (x : list label * list label * iThy Σ) : NonExpansive (default x ∘ head).
  Proof. solve_contractive. Qed.

  (* Global Instance default_head_lbl_ne (x : list label * list label * sem_sig Σ) : NonExpansive (default x ∘ head ∘ sem_row_car).
     Proof. Admitted.
     (*   intros ? X Y Heq. simpl. 
          destruct X, Y. rewrite !sem_row_car_proj.
          destruct sem_row_car0, sem_row_car1.
          - done.
          - simpl. unfold dist,prodO, ofe_dist. admit.
          - admit.
          - simpl. unfold dist, sem_row_dist in Heq. 
        Admitted.  *) *)
    
  Program Definition tail_sem_row:= λne ρ, @SemRow Σ (tail (sem_row_car ρ)) _.
  Next Obligation.
    intros ρ. 
    iIntros (????) "#H1 % % % (%Hin & H2)". iSplit; first done.
    iDestruct "H2" as "(%&%&%&%&%&->&%&->&%&Hσ&#Hcont)".
    iExists _,_,_,_,_. repeat (iSplit; first done).
    iIntros (??) "!# HS". iApply "H1". by iApply "Hcont".
  Qed. 
  Next Obligation.
    intros ? X Y Heq.
    unfold dist, sem_rowO in *. destruct n; first done.
    unfold ofe_dist, sem_row_dist. 
    rewrite !iLblSig_to_iLblThy_proj. 
    rewrite !iLblSig_to_iLblThy_tail_comm. by f_equiv.
  Qed. 

  #[refine] Fixpoint sem_row_compl_go (c1 : iLblSig Σ) (c : chain sem_rowO) : sem_rowO :=
    match c1 with
    | [] => @SemRow Σ [] _
    | x :: cs => @SemRow Σ (compl (chain_map (default x ∘ head) (sem_row_tail_chain c)) ::
                              sem_row_car (sem_row_compl_go cs (chain_map tail_sem_row c))) _
    end.
  Proof.
    - iIntros (????) "_ %%% (%Hcontra&_)". inversion Hcontra.
    - iIntros (????) "#H1 % % % (%Hin & H2)". iSplit; first done.
      iDestruct "H2" as "(%&%&%&%&%&->&%&->&%&Hσ&#Hcont)".
      iExists _,_,_,_,_. repeat (iSplit; first done).
      iIntros (??) "!# HS". iApply "H1". by iApply "Hcont".
  Defined. 
  
  #[refine] Fixpoint sem_row_lbcompl_go  (c1 : iLblSig Σ) {n} Hn (c : bchain sem_rowO n) : sem_rowO :=
    match c1 with
    | [] => @SemRow Σ [] _
    | x :: cs => @SemRow Σ (lbcompl Hn (bchain_map (default x ∘ head) (sem_row_list_bchain c)) ::
                              sem_row_car (sem_row_lbcompl_go cs Hn (bchain_map tail_sem_row c))) _
    end.
  Proof.
    - iIntros (????) "_ %%% (%Hcontra&_)". inversion Hcontra.
    - iIntros (????) "#H1 % % % (%Hin & H2)". iSplit; first done.
      iDestruct "H2" as "(%&%&%&%&%&->&%&->&%&Hσ&#Hcont)".
      iExists _,_,_,_,_. repeat (iSplit; first done).
      iIntros (??) "!# HS". iApply "H1". by iApply "Hcont".
  Defined. 

  Lemma n_Sm_SSn m n : (S m < n)%nat → ∃ n', n = S (S n').
  Proof.
    intros H. 
    destruct n as [|n]; [lia|].
    destruct n as [|n']; [lia|].
    by exists n'.
  Qed.

  Global Program Instance sem_row_cofe : Cofe sem_rowO := {
  compl c := sem_row_compl_go (sem_row_car (c 1%nat)) c;
  lbcompl n Hn c := sem_row_lbcompl_go (sem_row_car (c 1%nat _)) Hn c
}.
  Next Obligation. 
    intros n Hlm Hbc. 
    apply SIdx.limit_gt_S; first done.
    by apply SIdx.limit_lt_0.
  Qed. 
  Next Obligation.
    intros n c; simpl. destruct n; first done.
    assert (c 1%nat ≡{1%nat}≡ c (S n)) as Hc1. 
    { symmetry. apply chain_cauchy. rewrite -SIdx.succ_le_mono. apply SIdx.le_0_l. }
    unfold dist,sem_rowO,ofe_dist,sem_row_dist in Hc1.
    revert Hc1. generalize (c 1%nat)=> c1. revert c.
    destruct c1 as (c1&Hpersc1). 
    rewrite iLblSig_to_iLblThy_proj sem_row_car_proj. clear Hpersc1.
    induction c1 as [|x c1 IH]=> c Hc1 /=.
    (* c 1 is [] *)
    { inversion Hc1; simplify_eq. unfold dist, sem_rowO, ofe_dist, sem_row_dist. by rewrite -H. } 
    unfold dist, sem_rowO, ofe_dist, sem_row_dist in *.
    simpl in *. 

    apply symmetry, cons_dist_eq in Hc1 as (x' & xs' & Hx & Hc1 & Hcn). 
    rewrite Hcn. f_equiv.
    - transitivity ((default x (head (sem_row_car (chain_car c (S (n)))))).1.1,
                      (default x (head (sem_row_car (chain_car c (S (n)))))).1.2,
                        pmono_prot_car (sem_sig_car (default x (head (sem_row_car (chain_car c (S (n)))))).2)).
      { etransitivity.  
        - by rewrite !conv_compl.
        - simpl. f_equiv; do 5 f_equiv; (eapply sem_row_car_ne_1; first lia); by (rewrite chain_cauchy; last (simpl; lia)). }
      rewrite /chain_map //=. destruct x' as ((ls1, ls2), X). 
      destruct (sem_row_car (c (S n))) as [|((ls1', ls2'), X') cs]; first inversion Hcn. simpl in Hcn.
      inversion Hcn. simplify_eq. done.
    - rewrite IH /chain_map /= ?Hcn //;  rewrite iLblSig_to_iLblThy_proj iLblSig_to_iLblThy_tail_comm Hcn //=.
  Qed. 
  Next Obligation.
    intros n Hn c m Hm; simpl. destruct m; first done.
    assert (1%nat < n)%sidx as Hlt. { eapply Nat.le_lt_trans; last done. lia. }
    assert (c 1%nat (sem_row_cofe_obligation_1 n Hn) ≡{1%nat}≡ c (S m) Hm) as Hc1. 
    { symmetry. apply bchain_cauchy. rewrite -SIdx.succ_le_mono. apply SIdx.le_0_l. }
    unfold dist,sem_rowO,ofe_dist,sem_row_dist in Hc1.
    revert Hc1. generalize (c 1%nat (sem_row_cofe_obligation_1 n Hn))=> c1. revert c.
    destruct c1 as (c1&Hpersc1). 
    rewrite iLblSig_to_iLblThy_proj. rewrite sem_row_car_proj. clear Hpersc1.
    induction c1 as [|x c1 IH]=> c Hc1 /=.
    (* c 1 is [] *)
    { inversion Hc1; simplify_eq. unfold dist, sem_rowO, ofe_dist, sem_row_dist. by rewrite -H. } 
    unfold dist, sem_rowO, ofe_dist, sem_row_dist in *.
    simpl in *.
    
    apply symmetry, cons_dist_eq in Hc1 as (x' & xs' & Hx & Hc1 & Hcn). 
    rewrite Hcn. f_equiv.
    - unshelve rewrite !conv_lbcompl; try done.
      rewrite /bchain_map //=. destruct x' as ((ls1, ls2), X).
      destruct (sem_row_car (c (S m) Hm)) as [|((ls1', ls2'), X') cs]; first inversion Hcn. 
      inversion Hcn. simplify_eq.
      assert (∃ n', n = S (S n')) as (n'&->) by (eapply n_Sm_SSn; done). 
      simpl. done.
    - rewrite IH /chain_map /= ?Hcn //;  rewrite iLblSig_to_iLblThy_proj iLblSig_to_iLblThy_tail_comm Hcn //=.
  Qed.
  (* Sorry about the proof *)
  Next Obligation.
    intros n Hn c1 c2 m Hc; simpl.    
    specialize (Hc _ (sem_row_cofe_obligation_1 n Hn)) as Heq.
    move: Heq. generalize (c1 1%nat (sem_row_cofe_obligation_1 n Hn)) as c0 => c0.
    generalize (c2 1%nat (sem_row_cofe_obligation_1 n Hn)) as d0 => d0 Heq.
    destruct m; first done. 
    unfold dist, sem_rowO, ofe_dist,sem_row_dist in Heq.
    unfold dist,listO,ofe_dist,list_dist in Heq. 
    destruct d0. rewrite sem_row_car_proj.
    rewrite iLblSig_to_iLblThy_proj in Heq. clear sem_row_mono0.
    generalize dependent sem_row_car0. 
    generalize dependent c1. generalize dependent c2.
    induction (sem_row_car c0) => c2 c1 Hc d0 Heq.
    - apply Forall2_nil_inv_l in Heq as Hnil.
      apply iLblSig_to_iLblThy_nil_sig in Hnil as ->.
      done.
    - apply Forall2_cons_inv_l in Heq as (a'&i'&Heq&Hforall&Hd0).
      unfold dist,sem_rowO,ofe_dist,sem_row_dist. simpl in *.
      destruct d0; first inversion Hd0.
      simpl. f_equiv. 
      + f_equiv.
        * f_equiv.
          -- apply lbcompl_ne => γ Hγ //=.
             do 3 f_equiv.
             ++ inversion Hd0.  destruct a,p. destruct p,p0. rewrite -H0 in Heq. done.
             ++ f_equiv.
                destruct n.
                ** apply sem_row_car_ne_1; first lia.
                   specialize Hc with (p := γ) (Hp := Hγ).
                   destruct (c1 γ Hγ), (c2 γ Hγ). 
                   unfold dist, sem_rowO, ofe_dist, sem_row_dist in *.
                   rewrite !iLblSig_to_iLblThy_proj.
                   rewrite !iLblSig_to_iLblThy_proj in Hc.
                   clear sem_row_mono0 sem_row_mono1.
                   generalize dependent sem_row_car1.
                   induction sem_row_car0;intros sem_row_car1 Hc; destruct sem_row_car1; first done.
                   --- inversion Hc.
                   --- inversion Hc.
                   --- simpl in Hc. constructor.
                       +++ inversion Hc. destruct a0, p0. destruct p1, p0. done.
                       +++ apply IHsem_row_car0. inversion Hc. done.
                **  destruct n.
                    --- apply sem_row_car_ne_1; first lia.
                        specialize Hc with (p := γ) (Hp := Hγ).
                        destruct (c1 γ Hγ), (c2 γ Hγ). 
                        unfold dist, sem_rowO, ofe_dist, sem_row_dist in *.
                        rewrite !iLblSig_to_iLblThy_proj.
                        rewrite !iLblSig_to_iLblThy_proj in Hc.
                        clear sem_row_mono0 sem_row_mono1.
                        generalize dependent sem_row_car1.
                        induction sem_row_car0;intros sem_row_car1 Hc; destruct sem_row_car1; first done; inversion Hc.
                        subst. constructor.
                        *** destruct a0, p0. destruct p1, p0. done.
                        *** apply IHsem_row_car0. done.
                    --- destruct γ.
                        +++ apply sem_row_car_ne_1; first lia.
                            set (Hp1 := (sem_row_list_bchain_obligation_1 (S (S n)) c1 O Hγ n (@eq_refl nat (S (S n))) (@eq_refl nat O))).
                            set (Hp2 := (sem_row_list_bchain_obligation_1 (S (S n)) c2 O Hγ n (@eq_refl nat (S (S n))) (@eq_refl nat O))).
                            assert (Hp1 = Hp2) as -> by (apply make_proof_irrel).
                            apply Hc.
                        +++ apply sem_row_car_ne_1; first lia.
                            apply Hc.
          -- apply lbcompl_ne => γ Hγ //=.
             do 3 f_equiv.
             ++ inversion Hd0.  destruct a,p. destruct p,p0. rewrite -H0 in Heq. done.
             ++ f_equiv.
                destruct n.
                ** apply sem_row_car_ne_1; first lia.
                   specialize Hc with (p := γ) (Hp := Hγ).
                   destruct (c1 γ Hγ), (c2 γ Hγ). 
                   unfold dist, sem_rowO, ofe_dist, sem_row_dist in *.
                   rewrite !iLblSig_to_iLblThy_proj.
                   rewrite !iLblSig_to_iLblThy_proj in Hc.
                   clear sem_row_mono0 sem_row_mono1.
                   generalize dependent sem_row_car1.
                   induction sem_row_car0;intros sem_row_car1 Hc; destruct sem_row_car1; first done.
                   --- inversion Hc.
                   --- inversion Hc.
                   --- simpl in Hc. constructor.
                       +++ inversion Hc. destruct a0, p0. destruct p1, p0. done.
                       +++ apply IHsem_row_car0. inversion Hc. done.
                **  destruct n.
                    --- apply sem_row_car_ne_1; first lia.
                        specialize Hc with (p := γ) (Hp := Hγ).
                        destruct (c1 γ Hγ), (c2 γ Hγ). 
                        unfold dist, sem_rowO, ofe_dist, sem_row_dist in *.
                        rewrite !iLblSig_to_iLblThy_proj.
                        rewrite !iLblSig_to_iLblThy_proj in Hc.
                        clear sem_row_mono0 sem_row_mono1.
                        generalize dependent sem_row_car1.
                        induction sem_row_car0;intros sem_row_car1 Hc; destruct sem_row_car1; first done; inversion Hc.
                        subst. constructor.
                        *** destruct a0, p0. destruct p1, p0. done.
                        *** apply IHsem_row_car0. done.
                    --- destruct γ.
                        +++ apply sem_row_car_ne_1; first lia.
                            set (Hp1 := (sem_row_list_bchain_obligation_1 (S (S n)) c1 O Hγ n (@eq_refl nat (S (S n))) (@eq_refl nat O))).
                            set (Hp2 := (sem_row_list_bchain_obligation_1 (S (S n)) c2 O Hγ n (@eq_refl nat (S (S n))) (@eq_refl nat O))).
                            assert (Hp1 = Hp2) as -> by apply make_proof_irrel.
                            apply Hc.
                        +++ apply sem_row_car_ne_1; first lia.
                            apply Hc.

        * do 2 f_equiv. apply lbcompl_ne => γ Hγ.
          simpl.
          do 2 f_equiv.
          -- inversion Hd0. destruct a,p. destruct p,p0. rewrite -H0 in Heq.
             done.
          -- f_equiv.
             destruct n.
             ++ apply sem_row_car_ne_1; first lia.
                specialize Hc with (p := γ) (Hp := Hγ).
                destruct (c1 γ Hγ), (c2 γ Hγ). 
                unfold dist, sem_rowO, ofe_dist, sem_row_dist in *.
                rewrite !iLblSig_to_iLblThy_proj.
                rewrite !iLblSig_to_iLblThy_proj in Hc.
                clear sem_row_mono0 sem_row_mono1.
                generalize dependent sem_row_car1.
                induction sem_row_car0;intros sem_row_car1 Hc; destruct sem_row_car1; first done.
                ** inversion Hc.
                ** inversion Hc.
                ** simpl in Hc. constructor.
                   --- inversion Hc. destruct a0, p0. destruct p1, p0. done.
                   --- apply IHsem_row_car0. inversion Hc. done.
             ++ destruct n.
                ** apply sem_row_car_ne_1; first lia.
                   specialize Hc with (p := γ) (Hp := Hγ).
                   destruct (c1 γ Hγ), (c2 γ Hγ). 
                   unfold dist, sem_rowO, ofe_dist, sem_row_dist in *.
                   rewrite !iLblSig_to_iLblThy_proj.
                   rewrite !iLblSig_to_iLblThy_proj in Hc.
                   clear sem_row_mono0 sem_row_mono1.
                   generalize dependent sem_row_car1.
                   induction sem_row_car0;intros sem_row_car1 Hc; destruct sem_row_car1; first done; inversion Hc.
                   subst. constructor.
                   +++ destruct a0, p0. destruct p1, p0. done.
                   +++ apply IHsem_row_car0. done.
                ** destruct γ.
                   --- apply sem_row_car_ne_1; first lia.
                       set (Hp1 := (sem_row_list_bchain_obligation_1 (S (S n)) c1 O Hγ n (@eq_refl nat (S (S n))) (@eq_refl nat O))).
                       set (Hp2 := (sem_row_list_bchain_obligation_1 (S (S n)) c2 O Hγ n (@eq_refl nat (S (S n))) (@eq_refl nat O))).
                       assert (Hp1 = Hp2) as -> by apply make_proof_irrel.
                       apply Hc.
                   --- apply sem_row_car_ne_1; first lia.
                       apply Hc.
      + apply IHi.
        * intros γ Hγ. rewrite /bchain_map //=. 
          unfold dist,sem_rowO,ofe_dist,sem_row_dist. 
          rewrite !iLblSig_to_iLblThy_proj.
          rewrite !iLblSig_to_iLblThy_tail_comm.
          f_equiv. 
          apply iLblSig_to_iLblThy_ne_1; first lia.
          apply Hc.
        * simpl in Hd0. inversion Hd0. rewrite H1. apply Hforall.
  Qed.

  Global Program Instance sem_row_inhabited : Inhabited (sem_row Σ) := 
    populate (@SemRow Σ ⊥ _ (* _ *)).
  Next Obligation. iIntros (????) "?". iIntros (???) "(%Hcontra & _)". by apply elem_of_nil in Hcontra. Qed.

  Global Instance sem_row_car_ne n : Proper (dist n ==> dist n) sem_row_car.
  Proof. by intros Ψ1 Ψ2 ?. Qed.
  Global Instance sem_row_car_proper : Proper ((≡) ==> (≡)) (@sem_row_car Σ).
  Proof. by intros Ψ1 Ψ2 ?. Qed.
  
  (* Global Instance sem_row_ne n Ψ : Proper ((λ _ _, True) ==> dist n) (@SemRow Σ Ψ).
     Proof. intros P1 P2 _ ?. apply non_dep_fun_dist. rewrite /sem_row_car //. Qed.
     Global Instance sem_row_proper Ψ : Proper ((λ _ _, True) ==> (≡)) (@SemRow Σ Ψ).
     Proof. intros P1 P2 _ ?. apply non_dep_fun_equiv. rewrite /sem_row_car //. Qed. *)

End sem_row_cofe.

Declare Scope sem_row_scope.
Delimit Scope sem_row_scope with R.

(* TODO: import the rest of sem_def from Affect *)

(** The Type Environment

The type environment is represented as a list.
Due to the requirement that a type environment Γ is env_sem_typed,
we can utilize the separation logic's disjointness to argue about
variables occurring twice in the environment.

Thus if we have a `env_sem_typed Γ γ` assumption and
the same variable occurs twice in Γ we get that:

∙ They cannot be of the same non-persistent type (e.g. ref nat):
  So if we have `env_typed (l : ref nat; l : ref nat) γ`,  
  since the variables l are the same, we would have
  that l, v ∈ γ, and that  ref nat ⊨ v ∗  ref nat ⊨ v
  But that means we would need to provide that l ↦ w ∗ l ↦ w
  which would be impossible.

∙ If they have the same type which is a persistent type (e.g. nat):
  Then it is fine, in fact it must be allowed to allow for Multi types

∙ If they don't have the same type:
  Then `γ` would still have only 1 value for the variable `l` so
  it would be impossible to provide env_sem_typed proof.
*)

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
  rewrite /sig_le /tc_opaque. f_equiv; last by apply iThy_le_ne.
Admitted.

Global Instance sig_le_proper {Σ} :
  Proper ((≡) ==> (≡) ==> (≡)) (@sig_le Σ).
Proof. apply ne_proper_2. apply _. Qed. 

Global Instance row_le_ne `{probblazeRGS Σ} :
  NonExpansive2 (row_le).
Proof.
  intros n ρ₁ ρ₂ Hequiv ρ₁' ρ₂' Hequiv'.
  rewrite /row_le /tc_opaque. unfold to_iThy_le. do 4 f_equiv; try done.
Admitted.

Global Instance row_le_proper `{probblazeRGS Σ} :
  Proper ((≡) ==> (≡) ==> (≡)) (row_le).
Proof. apply ne_proper_2. apply _. Qed.

  

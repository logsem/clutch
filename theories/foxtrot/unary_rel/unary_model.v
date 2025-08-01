(** A unary logical relation for System F_mu_ref_fork with tapes *)
(** Files mostly copied from the binary_rel directory *)
From iris.base_logic Require Export na_invariants.
From iris.proofmode Require Import proofmode.
From clutch.common Require Import con_language con_ectxi_language locations.
From clutch.prelude Require Import properness.
From clutch.con_prob_lang Require Import notation lang.
From clutch.foxtrot Require Import weakestpre primitive_laws proofmode.

Definition logN : namespace := nroot .@ "logN".

(** We use foxtrotGS directly, instead of creating a new typeclass, since they are the same *)
(* Class foxtrotRGS Σ := FoxtrotRGS { *)
(*                         foxtrotRGS_foxtrotGS :: foxtrotGS Σ; *)
(*                         (* foxtrotRGS_na_invG :: na_invG Σ; *) *)
(*                         (* foxtrotRGS_nais : na_inv_pool_name; *) *)
(*                       }. *)

(** Semantic intepretation of types *)
Record lrel Σ := LRel {
                     lrel_car :> val → iProp Σ;
                     lrel_persistent v1 : Persistent (lrel_car v1)
                   }.
Arguments LRel {_} _ {_}.
Arguments lrel_car {_} _ _ : simpl never.
Declare Scope lrel_scope.
Bind Scope lrel_scope with lrel.
Delimit Scope lrel_scope with lrel.
Global Existing Instance lrel_persistent.


(* The COFE structure on semantic types *)
Section lrel_ofe.
  Context `{Σ : gFunctors}.

  Global Instance lrel_equiv : Equiv (lrel Σ) := λ A B, ∀ w1, A w1 ≡ B w1.
  Global Instance lrel_dist : Dist (lrel Σ) := λ n A B, ∀ w1, A w1 ≡{n}≡ B w1.
  Lemma lrel_ofe_mixin : OfeMixin (lrel Σ).
  Proof. by apply (iso_ofe_mixin (lrel_car : lrel Σ → (val  -d> iPropO Σ))). Qed.
  Canonical Structure lrelC := Ofe (lrel Σ) lrel_ofe_mixin.

  Global Instance lrel_cofe : Cofe lrelC.
  Proof.
    apply (iso_cofe_subtype' (λ A : val -d> iPropO Σ,
      ∀ w1, Persistent (A w1)) (@LRel _) lrel_car)=>//.
    - apply _.
    - apply limit_preserving_forall=> w1.
      (* apply limit_preserving_forall=> w2. *)
      apply bi.limit_preserving_Persistent.
      intros n P Q HPQ. apply (HPQ w1).
  Qed.

  Global Instance lrel_inhabited : Inhabited (lrel Σ) := populate (LRel inhabitant).

  Global Instance lrel_car_ne n : Proper (dist n ==> (=) ==> dist n) lrel_car.
  Proof. by intros A A' ? w1 w2 <-. Qed.
  Global Instance lrel_car_proper : Proper ((≡) ==> (=)  ==> (≡)) lrel_car.
  Proof. solve_proper_from_ne. Qed.
End lrel_ofe.

Arguments lrelC : clear implicits.

Canonical Structure ectx_itemO := leibnizO ectx_item.

(* Definition na_ownP `{!foxtrotRGS Σ} := na_own foxtrotRGS_nais. *)
(* Definition na_invP `{!foxtrotRGS Σ} := na_inv foxtrotRGS_nais. *)
(* Definition na_closeP `{!foxtrotRGS Σ} P N E := (▷ P ∗ na_ownP (E ∖ ↑N) ={⊤}=∗ na_ownP E)%I. *)

Section semtypes.
  Context `{!foxtrotGS Σ}.

  Implicit Types e : expr.
  Implicit Types E : coPset.
  Implicit Types A B : lrel Σ.

  Set Primitive Projections.

  (** Technically this is NOT a refinement, 
      but I cannot come up with a better verb for this unary logical relation
      And not too keep to rename all the lemmas
   *)
  Definition refines_def (e : expr) (A : lrel Σ)
    : iProp Σ :=
    WP e {{ A }}.

  Definition refines_aux : seal refines_def. Proof. by eexists. Qed.
  Definition refines := unseal refines_aux.
  Definition refines_eq : refines = refines_def := seal_eq refines_aux.

  Global Instance refines_ne n :
    Proper ((=) ==> (dist n) ==> (dist n)) (refines).
  Proof. rewrite refines_eq /refines_def. solve_proper. Qed.

  Global Instance refines_proper :
    Proper ((=) ==> (≡) ==> (≡)) (refines).
  Proof. solve_proper_from_ne. Qed.

  Definition lrel_unit : lrel Σ := LRel (λ w1, ⌜ w1 = #() ⌝%I).
  Definition lrel_bool : lrel Σ := LRel (λ w1, ∃ b : bool, ⌜ w1 = #b ⌝)%I.
  Definition lrel_nat : lrel Σ := LRel (λ w1, ∃ n : nat, ⌜ w1 = #n ⌝)%I.
  Definition lrel_int : lrel Σ := LRel (λ w1, ∃ n : Z, ⌜ w1 = #n ⌝)%I.

  Definition lrel_arr (A1 A2 : lrel Σ) : lrel Σ := LRel (λ w1,
    □ ∀ v1, A1 v1 -∗ WP (App w1 v1) {{ A2 }})%I.

  Definition lrel_ref (A : lrel Σ) : lrel Σ := LRel (λ w1,
    ∃ l1: loc, ⌜w1 = #l1⌝ ∧
      inv (logN .@ (l1)) (∃ v1 , l1 ↦ v1 ∗ A v1))%I.

  (* Both tapes are empty and are sampled from the same distribution *)
  Definition lrel_tape : lrel Σ := LRel (λ w1,
    ∃ (α1 : loc) (N: nat), ⌜w1 = #lbl:α1⌝  ∧
      inv (logN .@ (α1)) (α1 ↪ (N; [])))%I.

  Definition lrel_prod (A B : lrel Σ) : lrel Σ := LRel (λ w1,
    ∃ v1 v1', ⌜w1 = (v1,v1')%V⌝  ∧
        A v1 ∗ B v1')%I.

  Definition lrel_sum (A B : lrel Σ) : lrel Σ := LRel (λ w1,
    ∃ v1, (⌜w1 = InjLV v1⌝ ∧ A v1)
          ∨  (⌜w1 = InjRV v1⌝ ∧ B v1))%I.

  Definition lrel_rec1 (C : lrelC Σ -n> lrelC Σ) (rec : lrel Σ) : lrel Σ :=
    LRel (λ w1, ▷ C rec w1)%I.
  Global Instance lrel_rec1_contractive C : Contractive (lrel_rec1 C).
  Proof.
    intros n. intros P Q HPQ.
    unfold lrel_rec1. intros w1. rewrite {1 4}/lrel_car /=.
    f_contractive. f_equiv. by apply C.
  Qed.

  Definition lrel_rec (C : lrelC Σ -n> lrelC Σ) : lrel Σ := fixpoint (lrel_rec1 C).

  Definition lrel_exists (C : lrel Σ → lrel Σ) : lrel Σ := LRel (λ w1,
    ∃ A, C A w1)%I.

  Definition lrel_forall (C : lrel Σ → lrel Σ) : lrel Σ := LRel (λ w1,
    ∀ A : lrel Σ, (lrel_arr lrel_unit (C A))%lrel w1)%I.

  Definition lrel_true : lrel Σ := LRel (λ w1, True)%I.

  (** The lrel constructors are non-expansive *)
  Global Instance lrel_prod_ne n : Proper (dist n ==> dist n ==> dist n) lrel_prod.
  Proof. solve_proper. Qed.

  Global Instance lrel_sum_ne n : Proper (dist n ==> dist n ==> dist n) lrel_sum.
  Proof. solve_proper. Qed.

  Global Instance lrel_arr_ne n : Proper (dist n ==> dist n ==> dist n) (lrel_arr).
  Proof. solve_proper. Qed.

  Global Instance lrel_rec_ne n : Proper (dist n ==> dist n)
       (lrel_rec : (lrelC Σ -n> lrelC Σ) -> lrelC Σ).
  Proof.
    intros F F' HF.
    unfold lrel_rec, lrel_car.
    apply fixpoint_ne=> X w1.
    unfold lrel_rec1, lrel_car. cbn.
    f_equiv.
    apply lrel_car_ne; eauto.
  Qed.

  Lemma lrel_rec_unfold (C : lrelC Σ -n> lrelC Σ) : lrel_rec C ≡ lrel_rec1 C (lrel_rec C).
  Proof. apply fixpoint_unfold. Qed.

End semtypes.

(** Nice notations *)
Notation "()" := lrel_unit : lrel_scope.
Infix "→" := (lrel_arr ⊤) : lrel_scope.
Notation "A1 → A2" := (lrel_arr A1 A2) : lrel_scope.
Infix "*" := lrel_prod : lrel_scope.
Infix "+" := lrel_sum : lrel_scope.
Notation "'ref' A" := (lrel_ref A) : lrel_scope.
Notation "∃ A1 .. An , C" :=
  (lrel_exists (λ A1, .. (lrel_exists (λ An, C%lrel)) ..)) : lrel_scope.
Notation "∀ A1 .. An , C" :=
  (lrel_forall (λ A1, .. (lrel_forall (λ An, C%lrel)) ..)) : lrel_scope.

(* Section semtypes_properties. *)
(*   Context `{!foxtrotGS Σ}. *)

  (* (* The reference type relation is functional and injective. *)
  (*    Thanks to Amin. *) *)
  (* Lemma interp_ref_funct E (A : lrel Σ) (l l1 l2 : loc) : *)
  (*   ↑logN ⊆ E → *)
  (*   (ref A)%lrel #l #l1 ∗ (ref A)%lrel #l #l2 *)
  (*   ={E}=∗ ⌜l1 = l2⌝. *)
  (* Proof. *)
  (*   iIntros (?) "[Hl1 Hl2] /=". *)
  (*   iDestruct "Hl1" as (l' l1') "[% [% #Hl1]]". simplify_eq. *)
  (*   iDestruct "Hl2" as (l l2') "[% [% #Hl2]]". simplify_eq. *)
  (*   destruct (decide (l1' = l2')) as [->|?]; eauto. *)
  (*   iInv (logN.@(l, l1')) as (? ?) "[>Hl ?]" "Hcl". *)
  (*   iInv (logN.@(l, l2')) as (? ?) "[>Hl' ?]" "Hcl'". *)
  (*   simpl. iExFalso. *)
  (*   iDestruct (ghost_map_elem_valid_2 with "Hl Hl'") as %[Hfoo _]. *)
  (*   compute in Hfoo. eauto. *)
  (* Qed. *)

  (* Lemma interp_ref_inj E (A : lrel Σ) (l l1 l2 : loc) : *)
  (*   ↑logN ⊆ E → *)
  (*   (ref A)%lrel #l1 #l ∗ (ref A)%lrel #l2 #l *)
  (*   ={E}=∗ ⌜l1 = l2⌝. *)
  (* Proof. *)
  (*   iIntros (?) "[Hl1 Hl2] /=". *)
  (*   iDestruct "Hl1" as (l1' l') "[% [% #Hl1]]". simplify_eq. *)
  (*   iDestruct "Hl2" as (l2' l) "[% [% #Hl2]]". simplify_eq. *)
  (*   destruct (decide (l1' = l2')) as [->|?]; eauto. *)
  (*   iInv (logN.@(l1', l)) as (? ?) "(? & >Hl & ?)" "Hcl". *)
  (*   iInv (logN.@(l2', l)) as (? ?) "(? & >Hl' & ?)" "Hcl'". *)
  (*   simpl. iExFalso. *)
  (*   iDestruct (ghost_map_elem_valid_2 with "Hl Hl'") as %[Hfoo <-]. *)
  (*   compute in Hfoo. eauto. *)
  (* Qed. *)

  (* Lemma interp_tape_funct E (l l1 l2 : loc) : *)
  (*   ↑logN ⊆ E → *)
  (*   lrel_tape #lbl:l #lbl:l1 ∗ lrel_tape #lbl:l #lbl:l2 *)
  (*   ={E}=∗ ⌜l1 = l2⌝. *)
  (* Proof. *)
  (*   iIntros (?) "[Hl1 Hl2] /=". *)
  (*   iDestruct "Hl1" as (l' l1' n1) "[% [% #Hl1]]". simplify_eq. *)
  (*   iDestruct "Hl2" as (l l2' n2) "[% [% #Hl2]]". simplify_eq. *)
  (*   destruct (decide (l1' = l2')) as [->|?]; eauto. *)
  (*   iInv (logN.@(l, l1')) as "[>Hl ?]" "Hcl". *)
  (*   iInv (logN.@(l, l2')) as "[>Hl' ?]" "Hcl'". *)
  (*   simpl. iExFalso. *)
  (*   iDestruct (ghost_map_elem_valid_2 with "Hl Hl'") as %[Hfoo _]. *)
  (*   compute in Hfoo. eauto. *)
  (* Qed. *)

  (* Lemma interp_tape_inj E (A : lrel Σ) (l l1 l2 : loc) : *)
  (*   ↑logN ⊆ E → *)
  (*   lrel_tape #lbl:l1 #lbl:l ∗ lrel_tape #lbl:l2 #lbl:l *)
  (*   ={E}=∗ ⌜l1 = l2⌝. *)
  (* Proof. *)
  (*   iIntros (?) "[Hl1 Hl2] /=". *)
  (*   iDestruct "Hl1" as (l1' l' n1) "[% [% #Hl1]]". simplify_eq. *)
  (*   iDestruct "Hl2" as (l2' l n2) "[% [% #Hl2]]". simplify_eq. *)
  (*   destruct (decide (l1' = l2')) as [->|?]; eauto. *)
  (*   iInv (logN.@(l1', l)) as "(? & >Hl)" "Hcl". *)
  (*   iInv (logN.@(l2', l)) as "(? & >Hl')" "Hcl'". *)
  (*   simpl. iExFalso. *)
  (*   iDestruct (ghost_map_elem_valid_2 with "Hl Hl'") as "[%Hfoo _]". *)
  (*   compute in Hfoo. eauto. *)
  (* Qed. *)

(* End semtypes_properties. *)

(* Notation "'REL' e1 '<<' e2 '@' E ':' A" := *)
(*   (refines E e1%E e2%E (A)%lrel) *)
(*   (at level 100, E at next level, e1, e2 at next level, *)
(*    A at level 200, *)
(*    format "'[hv' 'REL'  e1  '/' '<<'  '/  ' e2  '@'  E  :  A ']'"). *)
Notation "'REL' e1 ':' A" :=
  (refines e1 A )%I
  (at level 100, e1 at next level, 
   A at level 200,
   format "'[hv' 'REL'  e1  :  A ']'").

(** Properties of the relational interpretation *)
Section related_facts.
  Context `{!foxtrotGS Σ}.
  Implicit Types e : expr.


  Lemma fupd_refines e A :
    (|={⊤}=> refines e A) -∗ refines e A.
  Proof.
    rewrite refines_eq /refines_def.
    by iIntros ">H". 
  Qed.

  Global Instance elim_fupd_refines p e P A :
   ElimModal True p false (|={⊤}=> P) P
     (refines e A) (refines e A).
  Proof.
    rewrite /ElimModal. intros _.
    iIntros "[HP HI]". iApply fupd_refines.
    destruct p; simpl; rewrite ?bi.intuitionistically_elim;
    iMod "HP"; iModIntro; by iApply "HI".
  Qed.
  
  (* Lemma fupd_refines E1 E2 e t A : *)
  (*   (|={E1, E2}=> refines E2 e t A) -∗ refines E1 e t A. *)
  (* Proof. *)
  (*   rewrite refines_eq /refines_def. *)
  (*   iIntros "H". iIntros (K j) "Hr /=". *)
  (*   iMod "H" as "H". iApply ("H" with "Hr"). *)
  (* Qed. *)

  (* Global Instance elim_fupd_refines p E1 E2 e t P A : *)
  (*  ElimModal True p false (|={E1, E2}=> P) P *)
  (*    (refines E1 e t A) (refines E2 e t A). *)
  (* Proof. *)
  (*   rewrite /ElimModal. intros _. *)
  (*   iIntros "[HP HI]". iApply fupd_refines. *)
  (*   destruct p; simpl; rewrite ?bi.intuitionistically_elim; *)
  (*   iMod "HP"; iModIntro; by iApply "HI". *)
  (* Qed. *)

  Global Instance elim_bupd_logrel p e P A :
   ElimModal True p false (|==> P) P
     (refines e A) (refines e A).
  Proof.
    rewrite /ElimModal (bupd_fupd ⊤).
    apply: elim_fupd_refines.
  Qed.

  (* This + elim_modal_timless_bupd' is useful for stripping off laters of timeless propositions. *)
  (* Global Instance is_except_0_logrel E e t A : *)
  (*   IsExcept0 (refines E e t A). *)
  (* Proof. *)
  (*   rewrite /IsExcept0. iIntros "HL". *)
  (*   iApply fupd_refines. by iMod "HL". *)
  (* Qed. *)

End related_facts.

Section monadic.
  Context `{!foxtrotGS Σ}.
  Implicit Types e : expr.

  Lemma refines_bind K A A' e :
    (REL e : A) -∗
    (∀ v , A v -∗
      REL fill K (of_val v) : A') -∗
    REL fill K e : A'.
  Proof.
    iIntros "Hm Hf".
    rewrite refines_eq /refines_def.
    (* iIntros (K'' j) "Hjis /=". *)
    (* rewrite -fill_app. *)
    (* iSpecialize ("Hm" $! (K' ++ K'') with "[$Hjis]"). *)
    (* (* iMod "Hm". *) *)
    (* (* iModIntro.  *) *)
    iApply wp_bind.
    iApply (wp_wand with "Hm").
    iApply "Hf".
  Qed.

  (* Lemma refines_ret_na E e1 e2 v1 v2 (A : lrel Σ) : *)
  (*   IntoVal e1 v1 → *)
  (*   IntoVal e2 v2 → *)
  (*   (na_ownP E ={⊤}=∗ na_ownP ⊤ ∗ A v1 v2) -∗ *)
  (*   REL e1 << e2 @ E : A. *)
  (* Proof. *)
  (*   rewrite /IntoVal. *)
  (*   rewrite refines_eq /refines_def. *)
  (*   iIntros (<-<-) "HFA". iIntros (K j) "HK/=". *)
  (*   iMod ("HFA" with "Hnais") as "[HF HA]". *)
  (*   iApply wp_value. iExists _. iFrame. *)
  (* Qed. *)

  (* Lemma refines_ret_na' E e1 e2 v1 v2 (A : lrel Σ) : *)
  (*   IntoVal e1 v1 → *)
  (*   IntoVal e2 v2 → *)
  (*   (|={⊤}=> na_ownP (⊤ ∖ E) ∗ A v1 v2) -∗ *)
  (*   REL e1 << e2 @ E : A. *)
  (* Proof. *)
  (*   rewrite /IntoVal. *)
  (*   rewrite refines_eq /refines_def. *)
  (*   iIntros (<-<-) "HFA". iIntros (K j) "Hjis /=". *)
  (*   iMod "HFA" as "[HF HA]". *)
  (*   iApply wp_value. iExists _. iFrame. *)
  (*   assert (E ## (⊤ ∖ E)) as H by set_solver. *)
  (*   iPoseProof (na_own_union _ _ _ H with "[$HF $Hnais]") as "HL". *)
  (*   assert ((E ∪ (⊤ ∖ E)) = ⊤) as ->. 2: iFrame. *)
  (*   rewrite union_comm_L. *)
  (*   rewrite difference_union_L. *)
  (*   set_solver. *)
  (* Qed. *)

  Lemma refines_ret e1 v1 (A : lrel Σ) :
    IntoVal e1 v1 →
    (|={⊤}=> A v1) -∗
    REL e1 : A.
  Proof.
    rewrite /IntoVal.
    rewrite refines_eq /refines_def.
    iIntros. subst.
    simpl. by wp_pures.
  Qed.


End monadic.

Ltac unfold_rel := rewrite refines_eq /refines_def.

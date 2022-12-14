(** A binary logical relation for System F_mu_ref with tapes *)
From iris.base_logic Require Import na_invariants.
From iris.proofmode Require Import proofmode.
From self.prelude Require Import properness.
From self.prob_lang Require Import notation spec_ra primitive_laws.

Definition logN : namespace := nroot .@ "logN".

Class prelogrelGS Σ := PrelogrelGS {
    prelogrelGS_prelocGS :> prelocGS Σ;
    prelogrelGS_na_invG :> na_invG Σ;
    prelogrelGS_nais : na_inv_pool_name;
}.

(** Semantic intepretation of types *)
Record lrel Σ := LRel {
  lrel_car :> val → val → iProp Σ;
  lrel_persistent v1 v2 : Persistent (lrel_car v1 v2)
}.
Arguments LRel {_} _%I {_}.
Arguments lrel_car {_} _ _ _ : simpl never.
Declare Scope lrel_scope.
Bind Scope lrel_scope with lrel.
Delimit Scope lrel_scope with lrel.
Global Existing Instance lrel_persistent.

(* The COFE structure on semantic types *)
Section lrel_ofe.
  Context `{Σ : gFunctors}.

  Global Instance lrel_equiv : Equiv (lrel Σ) := λ A B, ∀ w1 w2, A w1 w2 ≡ B w1 w2.
  Global Instance lrel_dist : Dist (lrel Σ) := λ n A B, ∀ w1 w2, A w1 w2 ≡{n}≡ B w1 w2.
  Lemma lrel_ofe_mixin : OfeMixin (lrel Σ).
  Proof. by apply (iso_ofe_mixin (lrel_car : lrel Σ → (val -d> val -d> iPropO Σ))). Qed.
  Canonical Structure lrelC := Ofe (lrel Σ) lrel_ofe_mixin.

  Global Instance lrel_cofe : Cofe lrelC.
  Proof.
    apply (iso_cofe_subtype' (λ A : val -d> val -d> iPropO Σ,
      ∀ w1 w2, Persistent (A w1 w2)) (@LRel _) lrel_car)=>//.
    - apply _.
    - apply limit_preserving_forall=> w1.
      apply limit_preserving_forall=> w2.
      apply bi.limit_preserving_Persistent.
      intros n P Q HPQ. apply (HPQ w1 w2).
  Qed.

  Global Instance lrel_inhabited : Inhabited (lrel Σ) := populate (LRel inhabitant).

  Global Instance lrel_car_ne n : Proper (dist n ==> (=) ==> (=) ==> dist n) lrel_car.
  Proof. by intros A A' ? w1 w2 <- ? ? <-. Qed.
  Global Instance lrel_car_proper : Proper ((≡) ==> (=) ==> (=) ==> (≡)) lrel_car.
  Proof. solve_proper_from_ne. Qed.
End lrel_ofe.

Arguments lrelC : clear implicits.

(* Canonical Structure ectx_itemO := leibnizO ectx_item. *)

Section semtypes.
  Context `{!prelogrelGS Σ}.

  Implicit Types e : expr.
  Implicit Types E : coPset.
  Implicit Types A B : lrel Σ.

  Set Primitive Projections.

  Definition refines_def (E : coPset) (e : expr) (e' : expr) (A : lrel Σ)
    : iProp Σ :=
    (∀ K, refines_right K e' -∗
          na_own prelogrelGS_nais ⊤ -∗
          |={E,⊤}=> WP e {{ v, ∃ v', refines_right K (of_val v')
                                     ∗ na_own prelogrelGS_nais ⊤
                                     ∗ A v v' }})%I.

  Definition refines_aux : seal refines_def. Proof. by eexists. Qed.
  Definition refines := unseal refines_aux.
  Definition refines_eq : refines = refines_def := seal_eq refines_aux.

  Global Instance refines_ne E n :
    Proper ((=) ==> (=) ==> (dist n) ==> (dist n)) (refines E).
  Proof. rewrite refines_eq /refines_def. solve_proper. Qed.

  Global Instance refines_proper E  :
    Proper ((=) ==> (=) ==> (≡) ==> (≡)) (refines E).
  Proof. solve_proper_from_ne. Qed.

  Definition lrel_unit : lrel Σ := LRel (λ w1 w2, ⌜ w1 = #() ∧ w2 = #() ⌝%I).
  Definition lrel_bool : lrel Σ := LRel (λ w1 w2, ∃ b : bool, ⌜ w1 = #b ∧ w2 = #b ⌝)%I.
  Definition lrel_int : lrel Σ := LRel (λ w1 w2, ∃ n : Z, ⌜ w1 = #n ∧ w2 = #n ⌝)%I.

  Definition lrel_arr (A1 A2 : lrel Σ) : lrel Σ := LRel (λ w1 w2,
    □ ∀ v1 v2, A1 v1 v2 -∗ refines ⊤ (App w1 v1) (App w2 v2) A2)%I.

  Definition lrel_ref (A : lrel Σ) : lrel Σ := LRel (λ w1 w2,
    ∃ l1 l2: loc, ⌜w1 = #l1⌝ ∧ ⌜w2 = #l2⌝ ∧
      inv (logN .@ (l1,l2)) (∃ v1 v2, l1 ↦ v1 ∗ l2 ↦ₛ v2 ∗ A v1 v2))%I.

  Definition lrel_tape : lrel Σ := LRel (λ w1 w2,
    ∃ α1 α2 : loc, ⌜w1 = #lbl:α1⌝ ∧ ⌜w2 = #lbl:α2⌝ ∧
      inv (logN .@ (α1, α2)) (∃ bs, α1 ↪ bs ∗ α2 ↪ₛ bs))%I.

  Definition lrel_prod (A B : lrel Σ) : lrel Σ := LRel (λ w1 w2,
    ∃ v1 v2 v1' v2', ⌜w1 = (v1,v1')%V⌝ ∧ ⌜w2 = (v2,v2')%V⌝ ∧
        A v1 v2 ∗ B v1' v2')%I.

  Definition lrel_sum (A B : lrel Σ) : lrel Σ := LRel (λ w1 w2,
    ∃ v1 v2, (⌜w1 = InjLV v1⌝ ∧ ⌜w2 = InjLV v2⌝ ∧ A v1 v2)
          ∨  (⌜w1 = InjRV v1⌝ ∧ ⌜w2 = InjRV v2⌝ ∧ B v1 v2))%I.

  Definition lrel_rec1 (C : lrelC Σ -n> lrelC Σ) (rec : lrel Σ) : lrel Σ :=
    LRel (λ w1 w2, ▷ C rec w1 w2)%I.
  Global Instance lrel_rec1_contractive C : Contractive (lrel_rec1 C).
  Proof.
    intros n. intros P Q HPQ.
    unfold lrel_rec1. intros w1 w2. rewrite {1 4}/lrel_car /=.
    f_contractive. f_equiv. by apply C.
  Qed.

  Definition lrel_rec (C : lrelC Σ -n> lrelC Σ) : lrel Σ := fixpoint (lrel_rec1 C).

  Definition lrel_exists (C : lrel Σ → lrel Σ) : lrel Σ := LRel (λ w1 w2,
    ∃ A, C A w1 w2)%I.

  Definition lrel_forall (C : lrel Σ → lrel Σ) : lrel Σ := LRel (λ w1 w2,
    ∀ A : lrel Σ, (lrel_arr lrel_unit (C A))%lrel w1 w2)%I.

  Definition lrel_true : lrel Σ := LRel (λ w1 w2, True)%I.

  (** The lrel constructors are non-expansive *)
  Global Instance lrel_prod_ne n : Proper (dist n ==> dist n ==> dist n) lrel_prod.
  Proof. solve_proper. Qed.

  Global Instance lrel_sum_ne n : Proper (dist n ==> dist n ==> dist n) lrel_sum.
  Proof. solve_proper. Qed.

  Global Instance lrel_arr_ne n : Proper (dist n ==> dist n ==> dist n) lrel_arr.
  Proof. solve_proper. Qed.

  Global Instance lrel_rec_ne n : Proper (dist n ==> dist n)
       (lrel_rec : (lrelC Σ -n> lrelC Σ) -> lrelC Σ).
  Proof.
    intros F F' HF.
    unfold lrel_rec, lrel_car.
    apply fixpoint_ne=> X w1 w2.
    unfold lrel_rec1, lrel_car. cbn.
    f_equiv.
    apply lrel_car_ne; eauto.
  Qed.

  Lemma lrel_rec_unfold (C : lrelC Σ -n> lrelC Σ) : lrel_rec C ≡ lrel_rec1 C (lrel_rec C).
  Proof. apply fixpoint_unfold. Qed.

End semtypes.

(** Nice notations *)
Notation "()" := lrel_unit : lrel_scope.
Infix "→" := lrel_arr : lrel_scope.
Infix "*" := lrel_prod : lrel_scope.
Infix "+" := lrel_sum : lrel_scope.
Notation "'ref' A" := (lrel_ref A) : lrel_scope.
Notation "∃ A1 .. An , C" :=
  (lrel_exists (λ A1, .. (lrel_exists (λ An, C%lrel)) ..)) : lrel_scope.
Notation "∀ A1 .. An , C" :=
  (lrel_forall (λ A1, .. (lrel_forall (λ An, C%lrel)) ..)) : lrel_scope.

Section semtypes_properties.
  Context `{!prelogrelGS Σ}.

  (* The reference type relation is functional and injective.
     Thanks to Amin. *)
  Lemma interp_ref_funct E (A : lrel Σ) (l l1 l2 : loc) :
    ↑logN ⊆ E →
    (ref A)%lrel #l #l1 ∗ (ref A)%lrel #l #l2
    ={E}=∗ ⌜l1 = l2⌝.
  Proof.
    iIntros (?) "[Hl1 Hl2] /=".
    iDestruct "Hl1" as (l' l1') "[% [% #Hl1]]". simplify_eq.
    iDestruct "Hl2" as (l l2') "[% [% #Hl2]]". simplify_eq.
    destruct (decide (l1' = l2')) as [->|?]; eauto.
    iInv (logN.@(l, l1')) as (? ?) "[>Hl ?]" "Hcl".
    iInv (logN.@(l, l2')) as (? ?) "[>Hl' ?]" "Hcl'".
    simpl. iExFalso.
    iDestruct (ghost_map_elem_valid_2 with "Hl Hl'") as %[Hfoo _].
    compute in Hfoo. eauto.
  Qed.

  Lemma interp_ref_inj E (A : lrel Σ) (l l1 l2 : loc) :
    ↑logN ⊆ E →
    (ref A)%lrel #l1 #l ∗ (ref A)%lrel #l2 #l
    ={E}=∗ ⌜l1 = l2⌝.
  Proof.
    iIntros (?) "[Hl1 Hl2] /=".
    iDestruct "Hl1" as (l1' l') "[% [% #Hl1]]". simplify_eq.
    iDestruct "Hl2" as (l2' l) "[% [% #Hl2]]". simplify_eq.
    destruct (decide (l1' = l2')) as [->|?]; eauto.
    iInv (logN.@(l1', l)) as (? ?) "(? & >Hl & ?)" "Hcl".
    iInv (logN.@(l2', l)) as (? ?) "(? & >Hl' & ?)" "Hcl'".
    simpl. iExFalso.
    iDestruct (ghost_map_elem_valid_2 with "Hl Hl'") as %[Hfoo <-].
    compute in Hfoo. eauto.
  Qed.

  Lemma interp_tape_funct E (l l1 l2 : loc) :
    ↑logN ⊆ E →
    lrel_tape #lbl:l #lbl:l1 ∗ lrel_tape #lbl:l #lbl:l2
    ={E}=∗ ⌜l1 = l2⌝.
  Proof.
    iIntros (?) "[Hl1 Hl2] /=".
    iDestruct "Hl1" as (l' l1') "[% [% #Hl1]]". simplify_eq.
    iDestruct "Hl2" as (l l2') "[% [% #Hl2]]". simplify_eq.
    destruct (decide (l1' = l2')) as [->|?]; eauto.
    iInv (logN.@(l, l1')) as (?) "[>Hl ?]" "Hcl".
    iInv (logN.@(l, l2')) as (?) "[>Hl' ?]" "Hcl'".
    simpl. iExFalso.
    iDestruct (ghost_map_elem_valid_2 with "Hl Hl'") as %[Hfoo _].
    compute in Hfoo. eauto.
  Qed.

  Lemma interp_tape_inj E (A : lrel Σ) (l l1 l2 : loc) :
    ↑logN ⊆ E →
    lrel_tape #lbl:l1 #lbl:l ∗ lrel_tape #lbl:l2 #lbl:l
    ={E}=∗ ⌜l1 = l2⌝.
  Proof.
    iIntros (?) "[Hl1 Hl2] /=".
    iDestruct "Hl1" as (l1' l') "[% [% #Hl1]]". simplify_eq.
    iDestruct "Hl2" as (l2' l) "[% [% #Hl2]]". simplify_eq.
    destruct (decide (l1' = l2')) as [->|?]; eauto.
    iInv (logN.@(l1', l)) as (?) "(? & >Hl)" "Hcl".
    iInv (logN.@(l2', l)) as (?) "(? & >Hl')" "Hcl'".
    simpl. iExFalso.
    iDestruct (ghost_map_elem_valid_2 with "Hl Hl'") as %[Hfoo <-].
    compute in Hfoo. eauto.
  Qed.

End semtypes_properties.

(* Notation "'REL' e1 '<<' e2 '@' E ':' A" := *)
(*   (refines E e1%E (inl e2%E) (A)%lrel) *)
(*   (at level 100, E at next level, e1, e2 at next level, *)
(*    A at level 200, *)
(*    format "'[hv' 'REL'  e1  '/' '<<'  '/  ' e2  '@'  E  :  A ']'"). *)
(* Notation "'REL' e1 '<<' e2 ':' A" := *)
(*   (refines ⊤ e1%E (inl e2%E) (A)%lrel) *)
(*   (at level 100, e1, e2 at next level, *)
(*    A at level 200, *)
(*    format "'[hv' 'REL'  e1  '/' '<<'  '/  ' e2  :  A ']'"). *)
(* Notation "'REL' e1 '<<{' id '}' '_' ':' A" := *)
(*   (refines ⊤ e1%E (in_2 id) (A)%lrel) *)
(*   (at level 100, e1 at next level, *)
(*   A at level 200, *)
(*   format "'[hv' 'REL'  e1  '/' '<<{' id '}' '/  '  '_'  :  A ']'"). *)
(* Notation "'REL' e1 '<<{' id '}' '_' '@' E ':' A" := *)
(*   (refines E e1%E (in_2 id) (A)%lrel) *)
(*   (at level 100, E at next level, e1 at next level, *)
(*   A at level 200, *)
(*   format "'[hv' 'REL'  e1  '/' '<<{' id '}' '/  '  '_'  '@'  E  ':'  A ']'"). *)
(* (￣～￣;)  OOF *)
Notation "'REL' e1 '<<' e2 '@' E ':' A" :=
  (refines E e1%E e2%E (A)%lrel)
  (at level 100, E at next level, e1, e2 at next level,
   A at level 200,
   format "'[hv' 'REL'  e1  '/' '<<'  '/  ' e2  '@'  E  :  A ']'").
Notation "'REL' e1 '<<' t ':' A" :=
  (refines ⊤ e1%E t%E (A)%lrel)
  (at level 100, e1, t at next level,
   A at level 200,
   format "'[hv' 'REL'  e1  '/' '<<'  '/  ' t  :  A ']'").

(** Properties of the relational interpretation *)
Section related_facts.
  Context `{!prelogrelGS Σ}.
  Implicit Types e : expr.

  (* PGH: the following three lemmas don't apply to notion of refinement as
  they are tied to the notion of refinement with external linearization points
  developed in Sec. 7.2 of https://www.cs.au.dk/~birke/papers/mpmc-queue.pdf *)
  (* Lemma refines_split E e e' A : *)
  (*   (∀ k, refines_right k e' -∗ REL e <<{k} _ @ E : A) -∗ *)
  (*   REL e << e' @ E : A. *)
  (* Proof. *)
  (*   iIntros "H". *)
  (*   rewrite refines_eq /refines_def. *)
  (*   iIntros (k) "He'". *)
  (*   iSpecialize ("H" $! k with "He'"). *)
  (*   by iApply "H". *)
  (* Qed. *)

  (* Lemma refines_combine E e e' A k : *)
  (*   (REL e << e' @ E : A) -∗ *)
  (*   refines_right k e' -∗ *)
  (*   REL e <<{k} _ @ E : A. *)
  (* Proof. *)
  (*   iIntros "H1 H2". *)
  (*   rewrite refines_eq /refines_def. *)
  (*   iIntros (j) "%". *)
  (*   iApply "H1". by destruct k; simplify_eq/=. *)
  (* Qed. *)

  (* Lemma refines_left_fupd E e k A : *)
  (*   (REL e <<{k} _ @ E : A) ={E,⊤}=∗ REL e <<{k} _ @ ⊤ : A. *)
  (* Proof. *)
  (*   rewrite refines_eq /refines_def. *)
  (*   iIntros "H". simpl. *)
  (*   iSpecialize ("H" $! k with "[%//]"). *)
  (*   iMod "H" as "H". iModIntro. *)
  (*   iIntros (j) "->". done. *)
  (* Qed. *)

  (* We need this to be able to open and closed invariants in front of logrels *)
  Lemma fupd_refines E1 E2 e t A :
    (|={E1, E2}=> refines E2 e t A) -∗ refines E1 e t A.
  Proof.
    rewrite refines_eq /refines_def.
    iIntros "H". iIntros (j) "Hr /=".
    iMod "H" as "H". iApply ("H" with "Hr").
  Qed.

  Global Instance elim_fupd_refines p E1 E2 e t P A :
   (* DF: look at the booleans here *)
   ElimModal True p false (|={E1,E2}=> P) P
     (refines E1 e t A) (refines E2 e t A).
  Proof.
    rewrite /ElimModal. intros _.
    iIntros "[HP HI]". iApply fupd_refines.
    destruct p; simpl; rewrite ?bi.intuitionistically_elim;
    iMod "HP"; iModIntro; by iApply "HI".
  Qed.

  Global Instance elim_bupd_logrel p E e t P A :
   ElimModal True p false (|==> P) P
     (refines E e t A) (refines E e t A).
  Proof.
    rewrite /ElimModal (bupd_fupd E).
    apply: elim_fupd_refines.
  Qed.

  (* This + elim_modal_timless_bupd' is useful for stripping off laters of timeless propositions. *)
  Global Instance is_except_0_logrel E e t A :
    IsExcept0 (refines E e t A).
  Proof.
    rewrite /IsExcept0. iIntros "HL".
    iApply fupd_refines. by iMod "HL".
  Qed.
End related_facts.

Section monadic.
  Context `{!prelogrelGS Σ}.
  Implicit Types e : expr.

  Lemma refines_bind K K' E A A' e e' :
    (REL e << e' @ E : A) -∗
    (∀ v v', A v v' -∗
      REL fill K (of_val v) << (fill K' (of_val v')) : A') -∗
    REL fill K e << fill K' e' @ E : A'.
  Proof.
    iIntros "Hm Hf".
    rewrite refines_eq /refines_def /refines_right.
    iIntros (j) "(#Hs & Hj) Hnais /=".
    rewrite -fill_app.
    iMod ("Hm" $! (K' ++ j) with "[$Hs $Hj] Hnais") as "Hm".
    iModIntro. iApply wp_bind.
    iApply (wp_wand with "Hm").
    iIntros (v). iDestruct 1 as (v') "[Hj [Hnais HA]]".
    rewrite fill_app.
    iSpecialize ("Hf" with "HA").
    iMod ("Hf" $! j with "Hj Hnais") as "$".
  Qed.

  Lemma refines_ret E e1 e2 v1 v2 (A : lrel Σ) :
    IntoVal e1 v1 →
    IntoVal e2 v2 →
    (|={E,⊤}=> A v1 v2) -∗ REL e1 << e2 @ E : A.
  Proof.
    rewrite /IntoVal.
    rewrite refines_eq /refines_def.
    iIntros (<-<-) "HA". iIntros (j) "Hj Hnais /=".
    iMod "HA" as "HA". iModIntro.
    iApply wp_value. iExists _. by iFrame.
  Qed.

End monadic.

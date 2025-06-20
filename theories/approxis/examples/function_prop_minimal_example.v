From clutch.approxis Require Import approxis map.

Set Default Proof Using "Type*".

Section defs.

  Variable foo : val.

  Definition eager_exec : expr :=
    let: "x" := foo #0 in
    "x".
  
  Definition lazy_exec : val :=
    λ: <>, foo #0.

  Section proofs.
    Context `{!approxisRGS Σ}.

    Variable H : ⊢ refines top foo foo (lrel_int → lrel_int).

    Lemma lazy_eager : ⊢ REL eager_exec << lazy_exec : () → lrel_int.
    Proof. rewrite /eager_exec/lazy_exec.
      rel_pures_l; rel_pures_r.
      rel_bind_l (foo _).
      Fail rel_bind_r (foo _).
      (* Cannot use the semantic typing assumption
        because reducing foo #0 is not the next step on the RHS,
        we're stuck ↯ *)
    Abort.

    Section Determinism.

    (* easy case : determinism *)

    (* TODO move these definition outside of a context containing an instance of
      approxis, to make them general *)

    Definition det_val_fun (f : val) (f_sem : Z -> Z) : Prop :=
      ∀ {Σ : gFunctors} {approxisRGS0 : approxisRGS Σ} (E : coPset)
      (K : list (ectxi_language.ectx_item prob_ectxi_lang))
      (n : Z) (e : expr) (A : lrel Σ),
      (refines E (fill K (#(f_sem n))) e A ⊢ refines E (fill K (f #n)) e A) ∧
      (refines E e (fill K (#(f_sem n))) A ⊢ refines E e (fill K (f #n)) A).

    Definition det_val_rel (f : val) : Prop :=
      ∀ {Σ : gFunctors} {approxisRGS0 : approxisRGS Σ} (E : coPset)
      (K : list (ectxi_language.ectx_item prob_ectxi_lang))
      (n : Z) (e : expr) (A : lrel Σ), ∃ (m : Z),
      (refines E (fill K (#(m))) e A ⊢ refines E (fill K (f #n)) e A) ∧
      (refines E e (fill K (#(m))) A ⊢ refines E e (fill K (f #n)) A).

    Definition val1 : val := λ: "v", "v" + #1.

    Lemma det_val_rel1 : det_val_rel val1.
    Proof. rewrite /det_val_rel. intros *. eexists. split;
      iIntros "H";
      rewrite /val1; rel_pures_l; rel_pures_r; iApply "H".
    Qed.

    Lemma det_val_fun1 : det_val_fun val1 (fun n => (n+1)%Z).
    Proof. rewrite /det_val_fun. intros *. split;
      iIntros "H";
      rewrite /val1; rel_pures_l; rel_pures_r; iApply "H".
    Qed.

    End Determinism.

    Section LocalRef.

    Fixpoint ForallSep {A} (P : A → iProp Σ) (l : list A) : (iProp Σ) := match l with
      | [] => True
      | h :: t => P h ∗ (ForallSep P t)
    end.

    Fixpoint ForallSep2 {Σ A B} (P : A → B → iProp Σ) (l1 : list A) (l2 : list B) : (iProp Σ) :=
    match l1, l2 with
      | [], [] => True
      | h1 :: t1, h2 :: t2 => P h1 h2 ∗ (ForallSep2 P t1 t2)
      | _, _ => False
    end.

    Fixpoint ForallSep3 {Σ A B C} (P : A → B → C → iProp Σ) (l1 : list A) (l2 : list B) (l3 : list C) : (iProp Σ) :=
    match l1, l2, l3 with
      | [], [], [] => True
      | h1 :: t1, h2 :: t2, h3 :: t3 => P h1 h2 h3 ∗ (ForallSep3 P t1 t2 t3)
      | _, _, _ => False
    end.

    Definition iterable_local_refs (f : val) (Nref : nat) : Prop :=
      ∀ {Σ : gFunctors} {approxisRGS0 : approxisRGS Σ} (E : coPset)
      (K : list (ectxi_language.ectx_item prob_ectxi_lang))
      (n : Z) (e : expr) (A : lrel Σ), ∃ (v : val),
      ((∀ (ll : list loc) (lv : list val),
        ⌜length ll = Nref⌝ -∗ ForallSep2 (fun l v => l ↦ v) ll lv -∗ (refines E (fill K v) e A))
      ⊢ (refines E (fill K (f #n)) e A)) ∧
      ((∀ (ll : list loc) (lv : list val),
        ⌜length ll = Nref⌝ -∗ ForallSep2 (fun l v => l ↦ₛ v) ll lv -∗ (refines E e (fill K v) A))
      ⊢ (refines E e (fill K (f #n)) A)).

    Definition val2 : val :=
      λ: "v",
        let: "x" := ref #0 in
        "x" <- !"x" + "v";;
        ! "x".

    Search list (iProp _).

    Lemma iterable2 : iterable_local_refs val2 1.
    Proof. rewrite /iterable_local_refs. intros *.
      eexists. split. 1:{
      iIntros "H".
      rewrite /val2. rel_pures_l.
      rel_alloc_l x as "Hx". rel_pures_l.
      rel_load_l. rel_pures_l; rel_store_l. rel_pures_l.
      rel_load_l. replace (0+n)%Z with n%Z by lia.
      Unshelve. 2:{ exact #n. }
      iApply "H".
      - iPureIntro. Unshelve. 2 : { exact [ x ]. }
        1 : done. exact [ #n ].
      - simpl. iFrame.
      }
      iIntros "H".
      rewrite /val2. rel_pures_r.
      rel_alloc_r x as "Hx". rel_pures_r.
      rel_load_r. rel_pures_r; rel_store_r. rel_pures_r.
      rel_load_r. replace (0+n)%Z with n%Z by lia.
      iApply "H".
      - iPureIntro. Unshelve. 2 : { exact [ x ]. }
        1 : done. exact [ #n ].
      - simpl. iFrame.
    Qed.
    
    End LocalRef.

    Section RandCouple.
    
    Fixpoint init_tapes (lN : list nat) (e : expr) : expr := match lN with
      | [] => e
      | h :: t => let: "_fresh_" := alloc #h in (init_tapes t e) (* change for an actually fresh name *)
    end.

    Definition potential_coupling := True.

    Definition val3 (l : list loc) : val := match l with
      | [ι] => λ: "v", "v" + rand(#lbl:ι) #10
      | _ => λ: <>, #()
    end.

    Definition foo1 : val := λ: <>, rand("i") #10.

    Definition alloc_before_f (f : val) (ι : loc) : expr := prob_lang.subst "i" #lbl:ι f.

    Definition foo2 : expr := let: "i" := alloc #10 in λ: <>, rand("i") #10.

    Lemma test (ι ι' : loc) : ι ↪N (10;[]) ∗ ι' ↪N (10;[])
      ⊢ refines ⊤ (alloc_before_f foo1 ι) (alloc_before_f foo1 ι') ().
    Proof. rewrite /alloc_before_f/foo1.
      rel_pures_l; rel_pures_r. simpl.
    Abort.

    Lemma test' :
      ⊢ refines ⊤ foo2 foo2 ().
    Proof. rewrite /foo2.
      rel_alloctape_l ι as "Hι". rel_pures_l.
      rel_alloctape_r ι' as "Hι'". rel_pures_r.
    Admitted.

    Lemma test'' : ⊢ refines ⊤ (let: "i" := alloc #10 in foo1) (let: "i" := alloc #10 in foo1) ().
    Proof. rewrite /alloc_before_f/foo1. rel_alloctape_l i as "Hi".
      rel_alloctape_r i' as "Hi'".
      rel_pures_l; rel_pures_r.
    Abort.
    
    Definition couplable_rand (f : list loc -> val) (C : lrel Σ) (lN : list nat) : Prop :=
      ∀ {Σ : gFunctors} {approxisRGS0 : approxisRGS Σ} (E : coPset)
      (K : list (ectxi_language.ectx_item prob_ectxi_lang))
      (n : Z) (e : list loc -> expr) (A : lrel Σ) (lιl lιr : list loc),
      (ForallSep2 (fun i n => i ↪N (n;[])) lιl lN ∗ ForallSep2 (fun i n => i ↪ₛN (n;[])) lιr lN ∗
        ∀ (v : val) (H : ⊢ C v v) (llrand : list (list nat)),
          (ForallSep3 (fun i l n => i ↪ₛN (n;l)) lιr llrand lN ∗
          ((ForallSep3 (fun i l n => i ↪ₛN (n;l)) lιr llrand lN) -∗
          (∀ (E' : coPset) (K' : list (ectxi_language.ectx_item prob_ectxi_lang))
            (e' : expr) (B : lrel Σ),
            (refines E' e' (fill K' v) B) -∗ (refines E' e' (fill K' ((f lιr) #n)) B)))) -∗
          (refines E (fill K v) (e lιr) A))
      ⊢ (refines E (fill K (f lιl #n)) (e lιr) A).
(*
    Definition couplable_rand_simple (f : expr -> val) (N : nat) : Prop := 
      ∀ {Σ : gFunctors} {approxisRGS0 : approxisRGS Σ} (E : coPset)
      (K : list (ectxi_language.ectx_item prob_ectxi_lang))
      (n : Z) (e : expr -> expr) (e' : expr) (A : lrel Σ) (ι ι' : loc),
      (ι ↪N (N; []) ∗ ι' ↪ₛN (N; []) ∗
        ∀ (v : val) (lr : list nat),
         (ι' ↪ₛN (N; lr) ∗
          (ι' ↪ₛN (N; lr) -∗ (refines E e' (fill K v) A) -∗ (refines E e' (fill K ((f #lbl:ι') #n)) A))) -∗
          (refines E (fill K v) (e #lbl:ι') A))
      ⊢ (refines E (fill K (f #lbl:ι #n)) (e #lbl:ι') A).*)
    
    Lemma iterable_val3 : couplable_rand val3 lrel_int [10].
    Proof with rel_pures_l; rel_pures_r. rewrite /couplable_rand. intros *.
      iIntros "[Hι [Hι' H]]".
      rewrite /val3...
      iPoseProof (ec_zero) as "Hec".
      iMod "Hec".
      destruct lιl as [|hιl tιl]; last destruct tιl as [|hιl' tιl];
      destruct lιr as [|hιr tιr]; try destruct tιr as [|hιr' tιr]; simpl;
      try done; try (iDestruct "Hι" as "[_ Hι]"; done); try (iDestruct "Hι'" as "[_ Hι']"; done).
      iDestruct "Hι" as "[Hι _]"; iDestruct "Hι'" as "[Hι' _]".


      rel_apply (refines_couple_TT_err 10 10); try lia.
      { Unshelve. 6:{ exact 0%R. } 1: { lra. } all: shelve. }
      iFrame.
      iIntros (r) "[Hι [Hι' %Hrbound]]". simpl...
      rel_apply refines_randT_l; iFrame.
      iModIntro. iIntros "Hι _"...
      rel_apply "H".
      Unshelve. 3:{ exact [[r]]. } 1 : shelve. simpl. iFrame.
      iIntros "[Hι' _]%E' %K'  %e' %B H"...
      rel_apply (refines_randT_r with "Hι'").
      iIntros "Hι' _"... rel_apply "H".
      Unshelve.
      iPureIntro. iStartProof. iExists _. done.
    Qed.

    End RandCouple.

  Variable foo' : list loc -> val.
  Variable l : list nat.
  Variable test : couplable_rand foo' lrel_int l.

  Axiom foo_sem_typed : forall (li : list loc) (H : length li = length l),
    ⊢ REL (foo' li) << (foo' li) : lrel_int → lrel_int.
    (* It appears to be useless now, with the couplable assumpion *)

  Definition eager_exec' (li : list loc) : expr :=
    let: "x" := foo' li #0 in
    λ: <>, "x".
  
  Definition lazy_exec' (li : list loc) : expr :=
    let: "x" := ref NONEV in
    λ: <>, match: ! "x" with
      | NONE => let: "n_v" := foo' li #0 in "x" <- SOME "n_v";; "n_v"
      | SOME "v" => "v"
    end.

  Lemma lazy_eager' (li li' : list loc) :
    ForallSep2 (fun i n => i ↪N (n;[])) li l ∗ ForallSep2 (fun i n => i ↪ₛN (n;[])) li' l
    ⊢ REL (eager_exec' li) << lazy_exec'  li' : () → lrel_int.
  Proof with rel_pures_l; rel_pures_r. rewrite /eager_exec'. iIntros "[Hi Hi']".
    rel_bind_l (foo' _ _).
    iPoseProof (test _ _ ⊤ [AppRCtx (λ: "x" <>, "x")] 0 lazy_exec') as "H". rel_apply "H".
    iClear "H". iFrame. iIntros (v Hsemtyped llrand) "[Hι' Hiter]".
    rel_pures_l. rewrite /lazy_exec'.
    rel_alloc_r x as "Hx"...
    set (P := (
      (  x ↦ₛ NONEV
      ∗ (ForallSep3 (λ (i : loc) (l0 : list nat) (n : nat), i↪ₛN(n;l0)) li' llrand l)
      ∗ (ForallSep3
        (λ (i : loc) (l0 : list nat) (n : nat),
        i↪ₛN(n;l0)) li' llrand l -∗
        ∀ (E' : coPset) (K' : list ectx_item) (e' : expr) (B : lrel Σ),
        (REL e' << fill K' v @ E' : B) -∗
        REL e' << fill K' (foo' li' #0%nat) @ E' : B)) ∨
        x ↦ₛ SOMEV v
    )%I).
    rel_apply (refines_na_alloc P (nroot.@"lazyeager_exec")).
    iSplitL; first iLeft; iFrame.
    iIntros "#Inv".
    rel_arrow_val.
    iIntros (v1 v2 [eq1 eq2]); subst.
    rel_apply refines_na_inv; iSplitL; first iAssumption.
    iIntros "[[[Hx [Hi H]]|Hx] Hclose]";
    replace (0)%Z with (Z.of_nat 0)%Z by lia; rel_pures_l; rel_pures_r; rel_load_r...
    - iPoseProof ("H" with "Hi") as "H". rel_bind_r (foo' _ _). 
      rel_apply "H"... rel_store_r... rel_apply refines_na_close; iFrame.
      rel_values.
    - rel_apply refines_na_close; iFrame.
      rel_values.
  Qed.
      

  End proofs.


End defs.

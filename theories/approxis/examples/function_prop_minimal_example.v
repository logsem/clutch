From clutch.approxis Require Import approxis map.

Set Default Proof Using "Type*".

Section motivating_example.

  Variable foo : val.

  Definition eager_exec : expr :=
    let: "x" := foo #0 in
    λ: <>, "x".
  
  Definition lazy_exec : expr :=
    let: "x" := ref NONE in
    λ: <>, match: !"x" with
      | NONE => let: "v" := foo #0 in "x" <- "v";; "v"
      | SOME "v" => "v"
    end.

  Section proofs.
    (* a motivating example *)
    Context `{!approxisRGS Σ}.

    Variable H : ⊢ refines top foo foo (lrel_int → lrel_int).

    Lemma lazy_eager : ⊢ REL eager_exec << lazy_exec : () → lrel_int.
    Proof. rewrite /eager_exec/lazy_exec.
      rel_alloc_r x as "Hx".
      rel_pures_l; rel_pures_r.
      rel_bind_l (foo _).
      Fail rel_bind_r (foo _).
      (* Cannot use the semantic typing assumption
        because reducing foo #0 is not the next step on the RHS,
        we're stuck ↯ *)
    Abort.
    
  End proofs.

  (* Hence, the semantic typing assumption is not enough, we need something stronger *)
End motivating_example.


Section rules.
  Context `{!approxisRGS Σ}.

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

  Section deterministic.

    Definition det_val_fun (f : val) (f_sem : Z -> Z) : Prop :=
      ∀ (E : coPset)
      (K : list (ectxi_language.ectx_item prob_ectxi_lang))
      (n : Z) (e : expr) (A : lrel Σ),
      (refines E (fill K (#(f_sem n))) e A ⊢ refines E (fill K (f #n)) e A) ∧
      (refines E e (fill K (#(f_sem n))) A ⊢ refines E e (fill K (f #n)) A).

    Definition det_val_rel (f : val) : Prop :=
      ∀ (E : coPset)
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

  End deterministic.

  Section LocalRef.

    Definition iterable_local_refs (f : val) (Nref : nat) : Prop :=
      ∀ (E : coPset)
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

    Definition potential_coupling (f : list loc -> val) (n : Z) (v : val) (lιr : list loc) (llrand : list (list nat)) (lN : list nat) : iProp Σ :=
      ForallSep3 (fun i l n => (i ↪ₛN (n;l))%I) lιr llrand lN ∗
      ((ForallSep3 (fun i l n => (i ↪ₛN (n;l))%I) lιr llrand lN) -∗
       (∀ (E' : coPset) (K' : list (ectxi_language.ectx_item prob_ectxi_lang)) (e' : expr) (B : lrel Σ),
          (refines E' e' (fill K' v) B) -∗ (refines E' e' (fill K' ((f lιr) #n)) B))).

    Definition couplable_rand (f : list loc -> val) (C : lrel Σ) (lN : list nat) : Prop :=
      ∀ (E : coPset)
      (K : list (ectxi_language.ectx_item prob_ectxi_lang))
      (n : Z) (e : list loc -> expr) (A : lrel Σ) (lιl lιr : list loc),
      (ForallSep2 (fun i n => i ↪N (n;[])) lιl lN ∗ ForallSep2 (fun i n => i ↪ₛN (n;[])) lιr lN ∗
        ∀ (v : val) (H : ⊢ C v v) (llrand : list (list nat)),
          potential_coupling f n v lιr llrand lN -∗
          (refines E (fill K v) (e lιr) A))
      ⊢ (refines E (fill K (f lιl #n)) (e lιr) A).
    
    Definition val3 (l : list loc) : val := match l with
      | [ι] => λ: "v", "v" + rand(#lbl:ι) #10
      | _ => λ: <>, #()
    end.

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

  Section opaque_example.

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
    About couplable_rand.
    iPoseProof (test with "[Hi Hi']") as "H"; last iAssumption. iFrame. iIntros (v Hsemtyped llrand) "[Hι' Hiter]".
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
  
End opaque_example.

End rules.

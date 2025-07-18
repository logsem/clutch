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

  (* Hence, the semantic typing assumption is not enough,
    we need something stronger *)
End motivating_example.

Section defs.

  Fixpoint ForallSep {Σ} {A} (P : A → iProp Σ)
    (l : list A) : (iProp Σ) := match l with
    | [] => True
    | h :: t => P h ∗ (ForallSep P t)
  end.

  Fixpoint ForallSep2 {Σ A B} (P : A → B → iProp Σ)
    (l1 : list A) (l2 : list B) : (iProp Σ) :=
  match l1, l2 with
    | [], [] => True
    | h1 :: t1, h2 :: t2 => P h1 h2 ∗ (ForallSep2 P t1 t2)
    | _, _ => False
  end.

  Fixpoint ForallSep3 {Σ A B C} (P : A → B → C → iProp Σ)
    (l1 : list A) (l2 : list B) (l3 : list C) : (iProp Σ) :=
  match l1, l2, l3 with
    | [], [], [] => True
    | h1 :: t1, h2 :: t2, h3 :: t3 => P h1 h2 h3 ∗ (ForallSep3 P t1 t2 t3)
    | _, _, _ => False
  end.

  Lemma ForallSep_Forall : ∀ {Σ} {A} P l,
    @ForallSep Σ A (λ x, ⌜P x⌝) l ⊣⊢ ⌜Forall P l⌝.
  Proof. intros *. apply bi.equiv_entails. split.
    - iIntros "H". iInduction l as [|h t] "IHt".
      + iPureIntro; done.
      + simpl. iDestruct "H" as "[%Hhead Htail]".
        iPoseProof ("IHt" with "Htail") as "%H".
        iPureIntro. constructor; assumption.
    - iInduction l as [|h t] "IHt"; iIntros "%H".
      + done.
      + simpl. inversion H; subst. iSplit.
        * iPureIntro; assumption.
        * iApply "IHt". iPureIntro; assumption.
  Qed.

  Lemma ForallSep_Forall2 : ∀ {Σ} {A B} P l1 l2,
    @ForallSep2 Σ A B (λ x y, ⌜P x y⌝) l1 l2 ⊣⊢ ⌜Forall2 P l1 l2⌝.
  Proof. (* TODO *)
  Abort.  

  Lemma ForallSep_Forall3 : ∀ {Σ} {A B C} P l1 l2 l3,
    @ForallSep3 Σ A B C (λ x y z, ⌜P x y z⌝) l1 l2 l3 ⊣⊢ ⌜Forall3 P l1 l2 l3⌝.
  Proof. (* TODO *)
  Abort.

  (* We could probably add a restrictive syntactic typing that
    entails each property here. E.g. a syntactically typed
    term containing no mmemory manipulation nor random sampling
    would be deterministic. *)

  Definition iter_appl_expr (e : expr) (args : list val) : expr :=
    fold_left (λ e arg, App e (Val arg)) args e.
  
  Fixpoint type_of_list_type (As : list Set) : Set := match As with
    | [] => unit
    | A::t => A * (type_of_list_type t)
  end.

  (* FIXME probleme typechecking abstract types etc *)
  Fail Fixpoint iter_appl {As : list Set} {B : Set}
    (f_sem : (fold_right (λ A B : Set, A → B) B As))
    (args : type_of_list_type As) : B := match As with
    | [] => f_sem
    | A::t => (@iter_appl t B (f_sem (fst args)) (snd args))
  end.

  (** Example to display why local state should work *)
  (* in the following, capture is avoided by autosubst *)

  Definition counter : expr :=
    let: "x" := ref #0 in
    λ: <>, !"x";; "x" <- !"x" + #1.

  Definition counter_client (e : expr) : expr :=
    let: "cnt" := counter in
    e.

  (* So, in fact, when we declare some references before providing
    package/library functions, the refs declared should stay local
    to the functions of the package/library and opaque outside *)
End defs.

Section rules.
  Context `{!approxisRGS Σ}.

  Section deterministic.

    (*
    Definition det_val_fun {A : Type} {As : list Type}
      (f : expr) (f_sem : list val -> val)
      (types : list (lrel Σ)) : Prop :=
      ∀ (E : coPset)
      (K : list (ectxi_language.ectx_item prob_ectxi_lang))
      (args : list val) (e : expr) (A : lrel Σ),
      ForallSep2 (fun x T => (lrel_car T) x x) args types ⊢
      (refines E (fill K (f_sem args)) e A -∗
        refines E (fill K (iter_appl_expr f args)) e A) ∧
      (refines E e (fill K (f_sem args)) A -∗
        refines E e (fill K (iter_appl_expr f args)) A).
    *)
    
    (* Check [nat : Type] : list Type. *)(*
    Print Inject.
    Definition det_val_fun {As : list Type} {B : Type} (rel_types : list (lrel Σ))
      (to_vals : ∀ A, A ∈ As → Inject A val)
      (to_val_ret : B → val)
      (f : expr) (f_sem : (fold_right (λ A B : Type, A → B) B As)) :=
      ∀ (E : coPset)
      (K : list (ectxi_language.ectx_item prob_ectxi_lang))
      (args : ∀ A, A ∈ As → A) (e : expr) (A : lrel Σ),
      ForallSep2 (λ A Arel, ∀ x : A,
          (lrel_car Arel)
          ((inject (to_vals A _)) x) ((inject (to_vals A _)) x))As rel_types
      ⊢ True.
      (refines E (fill K (to_val (fold_right (λ f x, f x) f_sem args))) e A
        -∗ refines E (fill K (iter_appl_expr f args)) e A) ∧
      (refines E e (fill K (to_val (fold_right (λ f x, f x) f_sem args))) A
        -∗ refines E e (fill K (iter_appl_expr f args)) A).*)

    Definition to_val_type_rel {A : Type}
      (Arel : lrel Σ) (to_val : A → val) : iProp Σ :=
      ∀ x : A, (lrel_car Arel) (to_val x) (to_val x).

    Definition det_val_fun1 {A B : Type} (Alrel Blrel : lrel Σ)
      (to_valA : A → val) (* (of_valA : val → option A) *)
      (to_valB : B → val) (* (of_valB : val → option B) *)
      (f : expr) (f_sem : A → B) :=
      ∀ (E : coPset)
      (K : list (ectxi_language.ectx_item prob_ectxi_lang))
      (arg : A) (e : expr) (T : lrel Σ),
      to_val_type_rel Alrel to_valA ∗
      to_val_type_rel Blrel to_valB ⊢
      (refines E (fill K (to_valB (f_sem arg))) e T
        -∗ refines E (fill K (f (to_valA arg))) e T) ∧
      (refines E e (fill K (to_valB (f_sem arg))) T
        -∗ refines E e (fill K (f (to_valA arg))) T).

    Definition det_val_fun (f : expr) (f_sem : list val -> val)
      (types : list (lrel Σ)) : Prop :=
      ∀ (E : coPset)
      (K : list (ectxi_language.ectx_item prob_ectxi_lang))
      (args : list val) (e : expr) (A : lrel Σ),
      ForallSep2 (fun x T => (lrel_car T) x x) args types ⊢
      (refines E (fill K (f_sem args)) e A -∗
        refines E (fill K (iter_appl_expr f args)) e A) ∧
      (refines E e (fill K (f_sem args)) A -∗
        refines E e (fill K (iter_appl_expr f args)) A).

    Definition det_val_rel (f : expr) (types : list (lrel Σ)) : Prop :=
      ∀ (E : coPset)
      (K : list (ectxi_language.ectx_item prob_ectxi_lang))
      (args : list val) (e : expr) (A : lrel Σ),
      ForallSep2 (fun x T => (lrel_car T) x x) args types ⊢
      ∃ (v : val),
      (refines E (fill K v) e A -∗
        refines E (fill K (iter_appl_expr f args)) e A) ∧
      (refines E e (fill K v) A -∗
        refines E e (fill K (iter_appl_expr f args)) A).
    
    Theorem det_val_fun_rel : forall e f_sem types, det_val_fun e f_sem types ->
      det_val_rel e types.
    Proof. intros *.
      rewrite /det_val_fun/det_val_rel. intro H.
      intros *. iIntros "H".
      pose proof (H E K args e0 A) as H'.
      iExists (f_sem args).
      iPoseProof (H' with "H") as "G". iApply "G".
    Qed.
    
    Definition val1 : val := λ: "v", "v" + #1.

    Lemma det_val_rel1 : det_val_rel val1 [lrel_int].
    Proof. rewrite /det_val_rel. intros *.
      iIntros "Htypes".
      destruct args as [|x t]; try destruct t as [|h t];
      simpl; try (try iDestruct "Htypes" as "[_ contra]";
        iExFalso; iAssumption).
      iDestruct "Htypes" as "[Hrel _]".
      iDestruct "Hrel" as (n) "[%eq1 %eq2]".
      iExists _.
      iSplit; iIntros "H";
      subst;
      rewrite /val1; rel_pures_l; rel_pures_r;
      iApply "H".
    Qed.

    Definition val1_sem (n : Z) : Z := n + 1.

    Theorem det_fun_val1 :
      @det_val_fun1 Z Z lrel_int lrel_int (λ x, #x) (λ x, #x) val1 val1_sem.
    Proof. rewrite /det_val_fun1.
      intros *. iIntros "[#HrelA #HrelB]". iSplit; iIntros "H";
        rewrite /val1; rel_pures_l; rel_pures_r; rewrite /val1_sem; rel_apply "H".
    Qed.

    (* PROBLEM : hard to write functions from `val` to `val`...
    Lemma det_val_fun1 : det_val_fun val1 (fun n => (n+1)%Z).
    Proof. rewrite /det_val_fun. intros *. split;
      iIntros "H";
      rewrite /val1; rel_pures_l; rel_pures_r; iApply "H".
    Qed.*) 

  End deterministic.

  Section LocalRef.

    Definition iterable_local_refs (f : val) (Nref : nat) : Prop :=
      ∀ (E : coPset)
      (K : list (ectxi_language.ectx_item prob_ectxi_lang))
      (n : Z) (e : expr) (A : lrel Σ), ∃ (v : val),
      ((∀ (ll : list loc) (lv : list val),
        ⌜length ll = Nref⌝ -∗ ForallSep2 (fun l v => l ↦ v) ll lv -∗
          (refines E (fill K v) e A))
      ⊢ (refines E (fill K (f #n)) e A)) ∧
      ((∀ (ll : list loc) (lv : list val),
        ⌜length ll = Nref⌝ -∗ ForallSep2 (fun l v => l ↦ₛ v) ll lv -∗
          (refines E e (fill K v) A))
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
    
    Definition potential_coupling (f : val) (n : Z) (v : val) : iProp Σ :=
       (∀ (E' : coPset) (K' : list (ectxi_language.ectx_item prob_ectxi_lang))
        (e' : expr) (B : lrel Σ),
          (refines E' e' (fill K' v) B) -∗ (refines E' e' (fill K' (f #n)) B)).

    Definition couplable (f : list loc -> val)
      (C : lrel Σ) (lN : list nat) : Prop :=
      ∀ (E : coPset)
      (K : list (ectxi_language.ectx_item prob_ectxi_lang))
      (n : Z) (e : list loc -> expr) (A : lrel Σ) (lιl lιr : list loc),
      (ForallSep2 (fun i n => i ↪N (n;[])) lιl lN) ∗
      (ForallSep2 (fun i n => i ↪ₛN (n;[])) lιr lN) ∗
      (∀ (v : val), C v v -∗
          potential_coupling (f lιr) n v -∗
          (refines E (fill K v) (e lιr) A))
      ⊢ (refines E (fill K (f lιl #n)) (e lιr) A).
    
    Definition val3 (l : list loc) : val := match l with
      | [ι] => λ: "v", "v" + rand(#lbl:ι) #10
      | _ => λ: <>, #()
    end.

    Lemma iterable_val3 : couplable val3 lrel_int [10].
    Proof with rel_pures_l; rel_pures_r. rewrite /couplable. intros *.
      iIntros "[Hι [Hι' H]]".
      rewrite /val3...
      iPoseProof (ec_zero) as "Hec".
      iMod "Hec".
      destruct lιl as [|hιl tιl]; last destruct tιl as [|hιl' tιl];
      destruct lιr as [|hιr tιr]; try destruct tιr as [|hιr' tιr]; simpl;
      try done; try (iDestruct "Hι" as "[_ Hι]"; done);
        try (iDestruct "Hι'" as "[_ Hι']"; done).
      iDestruct "Hι" as "[Hι _]"; iDestruct "Hι'" as "[Hι' _]".
      rel_apply (refines_couple_TT_err 10 10); try lia.
      { Unshelve. 6:{ exact 0%R. } 1: { lra. } all: shelve. }
      iFrame.
      iIntros (r) "[Hι [Hι' %Hrbound]]". simpl...
      rel_apply refines_randT_l; iFrame.
      iModIntro. iIntros "Hι _"...
      rel_apply "H"; first (iExists _; done).
      rewrite /potential_coupling.
      iIntros (E' K' e' B) "H"...
      rel_apply (refines_randT_r with "Hι'").
      iIntros "Hι' _"... rel_apply "H".
    Qed.

  End RandCouple.

  Section opaque_example.

  Variable foo' : list loc -> val.
  Variable l : list nat.
  Variable test : couplable foo' lrel_int l.

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
    ForallSep2 (fun i n => i ↪N (n;[])) li l ∗
      ForallSep2 (fun i n => i ↪ₛN (n;[])) li' l
    ⊢ REL (eager_exec' li) << lazy_exec'  li' : () → lrel_int.
  Proof with rel_pures_l; rel_pures_r. rewrite /eager_exec'. iIntros "[Hi Hi']".
    rel_bind_l (foo' _ _).
    iPoseProof (test with "[Hi Hi']") as "H"; last iAssumption. iFrame.
    iIntros (v) "#Hsemtyped Hpotential".
    rel_pures_l. rewrite /lazy_exec'.
    rel_alloc_r x as "Hx"...
    set (P := (
       (x ↦ₛ NONEV
      ∗ potential_coupling (foo' li') 0 v) ∨
        x ↦ₛ SOMEV v
    )%I).
    rel_apply (refines_na_alloc P (nroot.@"lazyeager_exec")).
    iSplitL; first iLeft; iFrame.
    iIntros "#Inv".
    rel_arrow_val.
    iIntros (v1 v2 [eq1 eq2]); subst.
    rel_apply refines_na_inv; iSplitL; first iAssumption.
    iIntros "[[[Hx Hpotential]|Hx] Hclose]";
    replace (0)%Z with (Z.of_nat 0)%Z by lia;
    rel_pures_l; rel_pures_r; rel_load_r...
    - rel_apply "Hpotential"...
      rel_store_r... rel_apply refines_na_close; iFrame.
      rel_values.
    - rel_apply refines_na_close; iFrame.
      rel_values.
  Qed.
  
  End opaque_example.

  Definition eager_exec'3 := eager_exec' val3.
  Definition lazy_exec'3 := lazy_exec' val3.

  Lemma lazy_eager'3coucou (i i' : loc) :
    i ↪N (10;[]) ∗ i' ↪ₛN (10;[])
    ⊢ REL (eager_exec'3 [i]) << lazy_exec'3 [i'] : () → lrel_int.
  Proof. iIntros "[Hi Hi']".
    rel_apply (lazy_eager' val3 [10] iterable_val3).
    iFrame.
  Qed.

  Section package.
    (* Attempt to formalize a well-formed package,
      that may initialize some references, tapes, etc
      before providing several functions *)

    (*
      A package is:
      - An expression `package`, possibly with side effects, reducing
        to a value `package_initialized` (this reduction is the
        _initialization_ of the package) together with
      - getters; a given getter, let's say `getter_i`,
        applied to `package_initialized`, reduces to
        a value `f_i` such that
      - under some assumptions, provide a value having
        some properties, that need to be declared with
        the package.
      - Additionally, even though a package can take account
        for locations declared during the initialization, it
        doesn't track (for now) new locations allocated
        during the execution of a `f_i`.
        E.g.
        ```
        let: "x" := ref 0 in
        (λ: <>, !"x", λ: <>, incr "x")
        ```
        corresponds perfectly to a package where the class will
        be useful, but the class won't be able to correctly
        encompass the behavior of the following program:
        ```
        let: "x" := ref 0 in
        (λ: <>, !"x", λ: <>, let "y" := ref 0 in incr "x")
        ```
    *)

    Context `{!approxisRGS Σ}.

    Definition ForallIndex {A : Type} (P : nat → A → Prop) (l : list A) : Prop :=
      (fix ForallIndexAux (A : Type) i P (l : list A) : Prop :=
        match l with
          | [] => True
          | [a] => P i a
          | a :: (_ :: _) as t => P i a ∧ ForallIndexAux A (S i) P t
        end) A 0 P l.
    
    Definition ForallIndex2 {A B : Type} (P : nat → A → B → Prop)
      (l1 : list A) (l2 : list B) : Prop :=
      (fix ForallIndexAux2 (A B : Type) i P (l1 : list A) (l2 : list B) : Prop :=
        match l1, l2 with
          | [], [] => True
          | [a], [b] => P i a b
          | a :: (_ :: _) as t1, b :: (_ :: _) as t2
            => P i a b ∧ ForallIndexAux2 A B (S i) P t1 t2
          | _, _ => False
        end) A B 0 P l1 l2.
    
    Definition ForallIndex3 {A B C : Type} (P : nat → A → B → C → Prop)
      (l1 : list A) (l2 : list B) (l3 : list C) : Prop :=
      (fix ForallIndexAux3 (A B C : Type) i P
        (l1 : list A) (l2 : list B) (l3 : list C) : Prop :=
        match l1, l2, l3 with
          | [], [], [] => True
          | [a], [b], [c] => P i a b c
          | a :: (_ :: _) as t1, b :: (_ :: _) as t2, c :: (_ :: _) as t3
            => P i a b c ∧ ForallIndexAux3 A B C (S i) P t1 t2 t3
          | _, _, _ => False
        end) A B C 0 P l1 l2 l3.

    Fixpoint list_full_of {X} (n : nat) (x : X) : list X := match n with
      | S n' => x :: list_full_of n' x
      | O => []
    end.

    (* [n_0, ..., n_(i-1), ...] ~~> [n_0, ...,n_(i-1) + 1, ...]*)
    Fixpoint next_package_state (i : nat) (ns : list nat) : list nat :=
      match i, ns with
        | _, [] => []
        | O, h :: t => (S h) :: t
        | S i', h :: t => h :: (next_package_state i' t)
      end.

    Definition package_function_spec
      {P_l P_r : list nat → list loc → iProp Σ}
      {P_lr : list nat → list nat → list loc → list loc → iProp Σ}
      {R_l R_r : list nat → list val → val → iProp Σ}
      {lls rls : list loc}
      (lrel_args : list (lrel Σ)) (lrel_return : lrel Σ)
      (method : list loc → val) (i : nat) : Prop :=
        ∀ (args : list val),
            (* left execution *)
            ∀ (ns : list nat) K e E (A : lrel Σ),
              Forall2 (λ arg t, ⊢ (lrel_car t) arg arg) args lrel_args →
              (P_l ns lls ⊢
                (∃ v,
                  (R_l ns args v ∗ P_l (next_package_state i ns) lls
                    -∗ refines E (fill K (Val v)) e A)
                  -∗ refines E (fill K (iter_appl_expr (method lls) args)) e A))
            (* right execution *)
          ∧ ∀ (ms : list nat) K e E (A : lrel Σ),
              Forall2 (λ arg t, ⊢ (lrel_car t) arg arg) args lrel_args →
              (P_r ms rls ⊢
                (∃ v,
                  (R_r ms args v ∗ P_l (next_package_state i ms) rls
                    -∗ refines E e (fill K (Val v)) A)
                  -∗ refines E e (fill K (iter_appl_expr (method rls) args)) A))
            (* for an execution on both sides, we can use
              a semantic typing assumption *)
          ∧ ∀ (ns ms : list nat) (𝒩 : namespace) (P : iProp Σ),
              (∃ Q, P ⊣⊢ (P_lr ns ms lls rls) ∗ Q) →
              (na_invP 𝒩 P
              ⊢ refines top (method lls) (method rls)
                (fold_right (λ A B : lrel Σ, (A → B)%lrel) lrel_return lrel_args)).

    Definition initialized_package
      {P_l P_r : list nat → list loc → iProp Σ}
      {P_lr : list nat → list nat → list loc → list loc → iProp Σ}
      {R_l R_r : list nat → list val → val → iProp Σ}
      (lrel_car_argss : list (list (lrel Σ))) (lrel_car_returns : list (lrel Σ))
      (lls rls : list loc) (getters : list val) (package_initialized : list loc → val) :=
      @ForallIndex3 val (list (lrel Σ)) (lrel Σ)
        (λ i getter lrel_car_args lrel_car_return,
          (∃ (method : list loc → val),
          (* A getter provides a value v... *)
              (∀ K e E A,
                 (refines E (fill K (Val (method lls))) e A
                ⊢ refines E (fill K (getter (package_initialized lls))) e A)
              ∧  (refines E e (fill K (method rls)) A
                ⊢ refines E e (fill K (getter (package_initialized rls))) A))
              ∧ @package_function_spec P_l P_r P_lr R_l R_r
                  lls rls lrel_car_args lrel_car_return method i))
        getters lrel_car_argss lrel_car_returns.
    
    Class PACKAGE_PARAMS (N_functions : nat) (*(N_loc : nat)*) := {
        n_arg : list nat
      ; n_arg_len : length n_arg = N_functions
      ; P_l   : list nat → list loc → iProp Σ
        (* property on the LHS, needed and obtained
          by running one of the values of the package *)
      ; P_r   : list nat → list loc → iProp Σ
        (* idem, on the RHS *)
      ; P_lr  : list nat → list nat → list loc → list loc → iProp Σ
      ; P_rem : list nat → list nat → list loc → list loc → iProp Σ
      (* properties got on the return value of each method *)
      ; Rval_l : list nat → list val → val → iProp Σ
      ; Rval_r : list nat → list val → val → iProp Σ
        (* to replace with semantic type of each method*)
      ; Plr_l_r : ∀ ns ms lls rls,
          P_lr ns ms lls rls ⊣⊢
          P_l ns lls ∗ P_r ms rls ∗ P_rem ns ms lls rls : Prop
        (* ...then I wonder if P_lr is really needed *)
    }.

    Class PACKAGE_STRUCT (N_functions : nat) := {
        package : expr
      ; getters : list val
      ; len_getters : length getters = N_functions
    }.

    Class PACKAGE `{package_struct : !PACKAGE_STRUCT N_functions}
      {package_params : PACKAGE_PARAMS N_functions} := {
        lrel_car_return : list (lrel Σ)
      ; lrel_car_args : list (list (lrel Σ))
      ; lrel_car_args_len : Forall2 (λ lrel_args n_args,
        length lrel_args = n_args) lrel_car_args n_arg
      ; rel_init : ⊢ (∀ K e E A,
          ∃ (package_initialized : list loc → val) (lls rls : list loc),
              P_l (list_full_of N_functions 0) lls
            ∗ P_r (list_full_of N_functions 0) rls
            ∗ ⌜@initialized_package
                P_l P_r P_lr
                Rval_l Rval_r
                lrel_car_args lrel_car_return
                lls rls
                getters package_initialized⌝
            ∗  ⌜refines E (fill K (Val (package_initialized lls))) e A
              ⊢ refines E (fill K package) e A⌝
            ∧  ⌜refines E e (fill K (Val (package_initialized rls))) A
              ⊢ refines E e (fill K package) A⌝)%I
    }.

    Lemma package_getter_valid_index `{!PACKAGE_STRUCT n} {i : nat} (Hltin : i < n)
      : i < length getters.
    Proof. rewrite len_getters. apply Hltin. Qed.
  End package.

End rules.  

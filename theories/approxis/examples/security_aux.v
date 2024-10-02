From clutch.prob_lang.typing Require Import tychk.
From clutch.approxis Require Import approxis map list option LR_tac.
Set Default Proof Using "Type*".

Definition lrel_int_bounded {Σ} min max : lrel Σ := LRel (λ w1 w2, ∃ k : Z, ⌜ w1 = #k ∧ w2 = #k ∧ min <=k ∧ k <= max ⌝)%Z%I.

Module LR_bounded.
  Import Ltac2 Ltac2.Printf.
  Export LR_tac.

  Ltac2 bounded x :=
    let s := constr:(append "(%" ($x ++ "&->&->&%" ++ $x ++ "_min&%" ++ $x ++ "_max)")) in
    eval vm_compute in $s.

  Ltac2 Set pattern_of_lr2 as previous :=
    fun lr (xs : constr list) =>
      lazy_match! lr with
      | lrel_int_bounded _ _ => bounded (get_head_name xs)
      | _ => previous lr xs
      end.

  Ltac2 int_bounded_intro (typ : constr) xs k :=
    printf "entering int_bounded_intro, typ: %t" typ ;
    lazy_match! typ with
    | lrel_int_bounded _ _ =>
        printf "found `lrel_int_bounded`, done" ;
        Some (bounded (get_head_name xs))
    | _ => None
    end.
  Ltac2 Set Basic.lrintro_tacs as prev := fun () => FMap.add "int_bounded" int_bounded_intro (prev ()).

  Ltac2 int_bounded_val typ k :=
    printf "entering int_bounded_val, typ: %t" typ ;
    lazy_match! typ with
    | (lrel_car (lrel_int_bounded _ _) ?v1 ?v2) =>
        printf "found `lrel_int_bounded %t %t`, trying lia" v1 v2 ;
        ltac1:(iExists _ ; iPureIntro ; (intuition lia || eauto)) ; Progressed
    | _ => Stuck
    end.
  Ltac2 Set Basic.rel_val_tacs as prev := fun () => FMap.add "int_bounded" int_bounded_val (prev ()).

  (* Ltac2 Set rel_vals as previous :=
       fun lr =>
         lazy_match! lr with
         | (_ _ (lrel_int_bounded _ _) _ _) =>
             ltac1:(iExists _ ; iPureIntro ; intuition lia)
         | _ => previous lr
         end. *)

End LR_bounded.

Export LR_bounded.

Definition TList α := (μ: (ref (() + α * #0)))%ty.
Fact init_list_typed α : ⊢ᵥ init_list : (() → TList α).
Proof. rewrite /init_list /TList. type_val 1. constructor. tychk. Qed.

Definition TMap k v : type := ref (TList (k * v)).
Fact init_map_typed k v : ⊢ᵥ init_map : (() → TMap k v).
Proof. rewrite /init_map /TMap. type_val 1. constructor. tychk.
       apply init_list_typed.
Qed.

Definition find_list : val :=
  (rec: "find" "h" "k" :=
     match: ! (rec_unfold "h") with
       NONE => NONE
     | SOME "p" =>
         let: "kv" := Fst "p" in
         let: "next" := Snd "p" in
         if: (Fst "kv") = "k" then SOME (Snd "kv") else "find" "next" "k"
     end).

Definition type_closed a := ∀ f, (a = a.[f])%ty.

Fact find_list_typed A B : type_closed A → type_closed B → UnboxedType A → ⊢ᵥ find_list : (TList (A * B) → A → TOption B).
Proof.
  intros A_closed B_closed A_unboxed.
  rewrite /find_list. type_val 1.
  type_expr 3 ; try by tychk.
  2: {
    type_expr 5.
    2: tychk. 2: tychk.
    eapply UnboxedEq_typed.
    1: apply A_unboxed.
    1,2: tychk.
  }
  Unshelve.
  2: exact TUnit.
  - set (α := (A * B)%ty).
    set (unfolded := (ref (() + α * TList α))%ty).
    assert (unfolded = ((ref (() + α * #0))%ty).[(μ: (ref (() + α * #0)))%ty/]) as ->.
    { simpl. rewrite /unfolded.
      rewrite /α /TList.
      by rewrite -A_closed -B_closed.
    }
    eapply TUnfold ; tychk.
Qed.

Fact get_typed A B :
  type_closed A → type_closed B → UnboxedType A →
  ⊢ᵥ get : (TMap A B → A → TOption B)%ty.
Proof. intros. rewrite /get. tychk. by apply find_list_typed. Qed.

Fact set_typed A B :
  type_closed A → type_closed B →
  ⊢ᵥ set : (TMap A B → A → B → TUnit)%ty.
Proof.
  intros HA HB.
  rewrite /set. tychk.
  rewrite /cons_list. type_val 2.
  rewrite /TList.
  constructor.
  simpl. tychk.
  simplify_map_eq.
  f_equal.
  by rewrite -HA -HB.
Qed.


Fact nat_to_fin_list (MAX : nat) (l:list nat):
  (∀ x, x ∈ l -> (x < S MAX)%nat) ->
  ∃ l': (list (fin (S MAX))), fin_to_nat <$> l' = l.
Proof.
  clear.
  induction l as [|a l'].
  - intros. exists []. naive_solver.
  - intros. set_unfold.
    assert (a<S MAX) as H' by naive_solver.
    unshelve epose proof IHl' _ as [l ?]; first naive_solver.
    exists (nat_to_fin H'::l).
    simpl.
    repeat f_equal; last done.
    by rewrite fin_to_nat_to_fin.
Qed.

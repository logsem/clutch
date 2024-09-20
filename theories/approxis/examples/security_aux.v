From clutch.prob_lang.typing Require Import tychk.
From clutch.approxis Require Import approxis map list.
(* From clutch.approxis.examples Require Import prf symmetric prf_cpa. *)
Set Default Proof Using "Type*".

Definition TOption (T : type) : type := (TUnit + T)%ty.
Definition lrel_option {Σ} (A : lrel Σ) := (() + A)%lrel.

Definition opt_mult : val :=
  λ:"opt",
    match: "opt" with
    | NONE => NONE
    | SOME "vopt" =>
        match: "vopt" with
        | NONE => NONE
        | SOME "v" => SOME "v"
        end
    end.

Fact opt_mult_typed (A : type) : (⊢ᵥ opt_mult : (TOption (TOption A) → TOption A)%ty).
Proof.
  rewrite /opt_mult. tychk.
Qed.

Definition opt_mult_poly : val :=
  Λ: λ:"opt",
    match: "opt" with
    | NONE => NONE
    | SOME "vopt" =>
        match: "vopt" with
        | NONE => NONE
        | SOME "v" => SOME "v"
        end
    end.

Fact opt_mult_poly_typed : (⊢ᵥ opt_mult_poly : ∀: (TOption (TOption #0) → TOption #0)%ty).
Proof.
  rewrite /opt_mult_poly. constructor. tychk.
Qed.

Fact opt_mult_poly_sem_typed `{!approxisRGS Σ} :
  ⊢ (∀ A : lrel Σ, lrel_option (lrel_option A) → lrel_option A)%lrel
      opt_mult_poly opt_mult_poly.
Proof.
  replace (∀ A : lrel Σ, lrel_option (lrel_option A) → lrel_option A)%lrel
    with (interp (∀: TOption (TOption #0) → TOption #0) []) by easy.
  iApply fundamental_val.
  rewrite /opt_mult_poly. constructor. tychk.
Qed.


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

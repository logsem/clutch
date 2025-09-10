From clutch.prob_lang Require Import typing.tychk.
From clutch.approxis Require Import approxis map list security_aux option.
From clutch.approxis Require Export bounded_oracle.
Set Default Proof Using "Type*".

(* Right-associative tuples. Alas, this breaks Coq's built-in tuple notation. *)
(* Notation "( e1 ; e2 )" := (Pair e1 e2) : expr_scope.
   Notation "( e1 ; e2 ; .. ; en' ; en )" := (Pair e1 (Pair e2 .. (Pair en' en) ..)) : expr_scope.
   Notation "( e1 ; e2 )" := (PairV e1 e2) : val_scope.
   Notation "( e1 ; e2 ; .. ; en' ; en )" := (PairV e1 (PairV e2 .. (PairV en' en) ..)) : val_scope. *)

Class PRG_params :=
  { card_input : nat
  ; card_extension : nat
  ; prg_params : val := (#card_input, #card_extension) }.

Definition TInput := TNat.
Definition TExtension := TNat.
Definition TOutput := (TNat * TNat)%ty.
Definition T_PRG_params := (TInput * TExtension)%ty.

Definition get_param_card_input : val := λ:"prg_params", Fst "prg_params".
Definition get_param_card_extension : val := λ:"prg_params", Snd "prg_params".

Class PRG `{PRG_params} :=
  { prg : val
  (* ; rand_output : val *)
  ; prg_scheme : val := (prg_params, prg)%V
  }.

Definition TPRG : type := () → TOutput.
Definition T_PRG_scheme := (T_PRG_params * TPRG)%ty.

Definition T_PRG_Adv := ((() → (TOption TOutput)) → TBool)%ty.

Definition get_params : val := λ:"prg_scheme", Fst "prg_scheme".
Definition get_card_input : val := λ:"prg_scheme", Fst (Fst "prg_scheme").
Definition get_card_extension : val := λ:"prg_scheme", Snd (Fst "prg_scheme").
Definition get_prg : val := λ:"prg_scheme", Snd "prg_scheme".

(* An idealised random generator. *)
Definition random_generator : val :=
  λ: "card_input" "card_extension",
    λ: "x",
      (rand (#1 ≪ "card_input" - #1),
      rand (#1 ≪ "card_extension" - #1)).

(** PRG security definitions using the variant of q_calls with explicit bounds
    checks in the code. **)
Module bounds_check.
  Section bounds_check.

    (* Context `{PRG_scheme : PRG}. *)

    (* Variable Input Extension : nat.

     Let prg PRG_scheme : expr := Fst (Snd PRF_scheme).
     Let rand_output PRF_scheme : expr := Snd (Snd PRF_scheme). *)

    (* Let q_calls := q_calls (card_input PRG_scheme). *)

    Definition PRG_real_rand : val :=
      λ:"b" "adv" "PRG_scheme" "Q",
        let: "input" := get_card_input "PRG_scheme" in
        let: "prg_key_b" :=
          if: "b" then
            λ: <>, (get_prg "PRG_scheme") (rand "input")
          else
            random_generator (get_card_input "PRG_scheme") (get_card_extension "PRG_scheme") in
        let: "oracle" := q_calls (get_card_input "PRG_scheme") "Q" "prg_key_b" in
        let: "b'" := "adv" "oracle" in
        "b'".
  
  End bounds_check.
End bounds_check.

Section prg_lrel.
  Context `{PRG_params : PRG}.

  Definition lrel_input {Σ} : lrel Σ := lrel_int_bounded 0 card_input.
  Definition lrel_output {Σ} : lrel Σ := lrel_int_bounded 0 (card_input + card_extension).
  Definition lrel_prg `{!approxisRGS Σ} : lrel Σ := lrel_input → lrel_output.

  Definition lrel_PRG_Adv `{!approxisRGS Σ} := ((lrel_input → (lrel_option lrel_output)) → lrel_bool)%lrel.

End prg_lrel.
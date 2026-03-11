From iris.base_logic.lib Require Import token.
From Stdlib Require Import ZArith Znumtheory.
From clutch.elton Require Import elton.
From clutch.elton Require Import map.
Set Default Proof Using "Type*".

Section prog.
  Variable p:nat.
  Variable tries:nat.
  Context (Hprime : prime p).

  Definition zmod : val :=
    λ: "a", "a" `rem` #p.


  (** Note the higher-order reference *)
  Definition arr_new : val :=
    (λ: <>,
       ref (#0, init_map #())).

  Definition arr_push : val :=
    λ: "arr" "v",
      let: "pair" := !"arr" in
      let: "len"  := Fst "pair" in
      let: "m" := Snd "pair" in
      set "m" "len" "v";;
      "arr" <- ("len"+#1, "m");;
      "len".

  Definition arr_get : val :=
    λ: "arr" "i",
      let: "pair" := !"arr" in
      let: "m" := Snd "pair" in
      get "m" "i".

  Definition arr_len : val :=
    λ: "arr",
      let: "pair" := !"arr" in
      Fst ("pair").

  Definition try_spend : val :=
    λ: "budget" <>,
      let: "rem" := !"budget" in
      if: "rem" ≤ #0
      then #false
      else "budget" <- "rem" - #1;; #true.

  (** group operations *)

  (** group_mul st h1 h2 — costs 1 query.
    Returns SOME handle on success, NONEV if budget exhausted
    or either handle is invalid. *)
  Definition group_mul : val :=
    λ: "arr" "f" "h1" "h2",
      if: "f" #() 
      then
        let: "e1" := arr_get "arr" "h1" in
        let: "e2" := arr_get "arr" "h2" in
        match: "e1" with
          NONE => NONEV
        | SOME "a" =>
            match: "e2" with
              NONE => NONEV
            | SOME "b" =>
                SOME (arr_push "arr" (zmod ("a" + "b")))
            end
        end
      else NONEV.

  (** group_inv st h — costs 1 query. *)
  Definition group_inv : val :=
    λ: "arr" "f" "h",
      if: "f"
      then
        let: "e" := arr_get "arr" "h" in
        match: "e" with
          NONE => NONEV
        | SOME "a" =>
            SOME (arr_push "arr" (zmod (#p-"a")))
        end
      else NONEV.

  (** group_eq st h1 h2 — costs 1 query. *)
  Definition group_eq : val :=
    λ: "arr" "f" "h1" "h2",
      if: "f" #()
      then
        let: "e1" := arr_get "arr" "h1" in
        let: "e2" := arr_get "arr" "h2" in
        match: "e1" with
          NONE => NONEV
        | SOME "a" =>
            match: "e2" with
              NONE => NONEV
            | SOME "b" =>
                SOME ("a" = "b")
            end
        end
      else NONEV.

  Definition dlog_game : val :=
    λ: "adv",
      let: "x" := rand ("p" - #1) in
      let: "arr" := arr_new #() in

      let: "zero" := "arr_push" "arr" #1 in
      let: "one" := "arr_push" "arr" "x" in
      
      let: "budget" := ref #tries in
      let: "f" := try_spend "budget" in
      let: "mul" :=  group_mul "arr" "f" in
      let: "inv" := group_inv "arr" "f" in
      let: "eq"  := group_eq "arr" "f" in

      let: "all" := ("zero", "one", "mul", "inv", "eq") in
      
      (* Adversary receives handles and closures, not arr. *)
      let: "guess" := "adv" "all" in
      "guess" = "x".
  
End prog.

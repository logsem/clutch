(* A UC inspired security proof of Diffie-Hellman key exchange involving
   reasoning about lazy/eager sampling. *)

From stdpp Require Import namespaces.
From clutch.prob_lang Require Import spec_ra notation proofmode primitive_laws lang.
From clutch.logrel Require Import model rel_rules rel_tactics adequacy.

From clutch.typing Require Import types contextual_refinement soundness.
From clutch.prelude Require Import base.
Set Default Proof Using "Type*".

Section dhke.

Parameter exp : expr.
Parameter modulo : expr.
Parameter g : expr.
Parameter p : expr.
Parameter mult : expr.
Parameter inv : expr.

#[local] Infix "^^" := exp (at level 35) : expr_scope.
#[local] Infix "**" := mult (at level 40) : expr_scope.
#[local] Notation "--" := inv : expr_scope.
#[local] Infix "%%" := modulo (at level 65) : expr_scope.




Definition F_AUTH : expr := λ:<>,
  let: "l" := ref NONE in
  let: "flag" := ref #false in
  let: "read" := (λ:<>, if: (!"flag") then !"l" else NONE) in
  let: "write" := (λ:"v", if: (!"l" = NONE) then "l" <- SOME "v" else #()) in
  let: "enable" := (λ:"f", if: "f" !"l" then "flag" <- #true else #()) in
  ("read", "write", "enable").

Definition alice_r (sendA recvB : expr) : expr :=
  λ:<>,
  let: "a" := flip #() in
  let: "A" := modulo (exp g "a") p in
  sendA "A" ;;
  λ:<>,
    let: "B" := recvB #() in
    match: "B" with
    | NONE => #()
    | SOME "B" =>
        let: "s_a" := modulo (exp "B" "a") p in
        "s_a"
    end.

Definition bob_r (recvA sendB : expr) : expr :=
  λ:<>,
    let: "A" := recvA #() in
    match: "A" with
    | NONE => #()
    | SOME "A" =>
        let: "b" := flip #() in
        let: "B" := (exp "g" "b") p in
        sendB "B";;
        let: "s_b" := modulo (exp "A" "b") p in
        "s_b"
    end.

(* let (recvA, sendA, enableA) = F_AUTH () in *)
(* let (recvB, sendB, enableB) = F_AUTH () in *)
(* (alice sendA recvB, bob recvA sendB, enableA, enableB) *)

Definition alice_i (s sendA recvB : expr) : expr :=
  λ:<>, sendA #() ;;
  λ:<>, match: recvB #() with
        | NONE => #()
        | SOME "_" => s
    end.

Definition bob_i (s sendB recvA : expr) : expr :=
  λ:<>, match: recvA #() with
        | NONE => #()
        | SOME "_" =>   λ:<>, sendB #() ;; s
    end.



Definition keygen : expr :=
  λ:<>, let: "sk" := flip #() in
    let: "pk" := g ^^ "sk" in
    ("pk", "sk").

Definition enc : expr :=
  λ: "pk", λ: "m",
    let: "y" := flip #() in
    (g ^^ "y", "pk" ^^ "y" * "m").

Definition dec : expr :=
  λ:"sk", λ:"c",
    let: "c1" := Fst "c" in
    let: "c2" := Snd "c" in
    "c1" ** ("c2" ^^ (-- "sk")).

Definition DH_real pk_loc sk_loc : expr :=
  λ:<>,
    let: "a" := flip #() in
    let: "b" := flip #() in
    pk_loc <- (g ^^ "a") ;;
    sk_loc <- "a" ;;
    (g^^"a", (g^^"b", g^^("a" ** "b"))).

Definition DH_rnd pk_loc sk_loc : expr :=
  λ:<>,
    let: "a" := flip #() in
    let: "b" := flip #() in
    let: "c" := flip #() in
    pk_loc <- (g ^^ "a") ;;
    sk_loc <- "a" ;;
    (g^^"a", (g^^"b", g^^("c"))).

Definition Aux_getpk_id pk_loc : expr :=
  λ:<>, !pk_loc.

Definition abort : expr := (rec: "f" "x" := "f" "x") #().
Definition assert b : expr := if: b then #() else abort.

Definition Aux_challenge_id' (pk_loc query : expr) : expr :=
  let: "counter_loc" := ref #0 in
  λ:"m",
    let: "count" := !"counter_loc" in
    assert "count" = #0 ;;
    "counter_loc" <- #1 ;;
    let: "pk_c" := query #() in
    let: "c" := Snd "pk_c" in
    (Fst "c", "m" ** (Snd "c")).

Definition Aux pk_loc query :=
  (Aux_getpk_id pk_loc, Aux_challenge_id' pk_loc query).

(* Lemma ots_real_vs_rnd_equiv_true pk_loc sk_loc : *)
(*   ⊢ REL Aux pk_loc sk_loc DH_real << ots_real_vs_rnd #true *)
(*     : () → lrel_bool. *)

End dhke.

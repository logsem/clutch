From iris.base_logic.lib Require Import token.
From Stdlib Require Import ZArith Znumtheory.
From clutch.elton Require Import elton.
From clutch.elton Require Import map.
Set Default Proof Using "Type*".

Open Scope Z_scope.

Theorem mod_mult_inverse_unique :
  forall p : Z,
    prime p ->
    forall a b : Z,
      0 < a < p ->
      0 <= b < p ->
      exists! x : Z,
        0 <= x < p /\ (a * x) mod p = b mod p.
Proof.
  intros p Hprime a b Ha Hb.
  assert (Hp_pos : p > 0) by (destruct Hprime; lia).
  assert (Hp_neq0 : p ≠ 0) by lia.
  assert (Hndiv : ~ (p | a)).
  { intros [k Hk]. destruct Ha as [Ha1 Ha2].
    destruct (Z.eq_dec k 0) as [->|Hk0].
    - lia.
    - assert (Z.abs (p * k) >= p) by (rewrite Z.abs_mul; nia).
      lia. }
  assert (Hrel : rel_prime p a) by (apply prime_rel_prime; auto).
  assert (Hrel' : rel_prime a p) by (apply rel_prime_sym; auto).
  destruct (rel_prime_bezout p a Hrel) as [u v Hbez].
  exists ((v * b) mod p).
  unfold unique. split.
  - split.
    + apply Z_mod_lt. lia.
    + rewrite Zmult_mod.
      rewrite Zmod_mod.
      rewrite <- Zmult_mod.
      replace (a * (v * b)) with ((v * a) * b) by ring.
      assert (Hva : v * a = 1 - u * p) by lia.
      rewrite Hva.
      replace ((1 - u * p) * b) with (b + (- u * b) * p) by ring.
      rewrite Z_mod_plus_full.
      rewrite (Zmod_small b p); lia.
  - intros x' [Hx'_range Hx'_eq].
    assert (Hwit_eq : (a * ((v * b) mod p)) mod p = b mod p).
    { rewrite Zmult_mod. rewrite Zmod_mod. rewrite <- Zmult_mod.
      replace (a * (v * b)) with ((v * a) * b) by ring.
      assert (Hva : v * a = 1 - u * p) by lia.
      rewrite Hva.
      replace ((1 - u * p) * b) with (b + (- u * b) * p) by ring.
      rewrite Z_mod_plus_full.
      rewrite (Zmod_small b p); lia. }
    assert (Hx'_eq' : (a * x') mod p = (a * ((v * b) mod p)) mod p).
    { rewrite Hx'_eq. symmetry. exact Hwit_eq. }
    assert (Hdiff : (a * x' - a * ((v * b) mod p)) mod p = 0).
    { rewrite Zminus_mod.
      rewrite Hx'_eq'.
      rewrite Z.sub_diag.
      reflexivity. }
    assert (Hdiv : (p | a * (x' - (v * b) mod p))).
    { apply Zmod_divides in Hdiff; auto.
      destruct Hdiff as [c Hc].
      exists c.
      replace (a * (x' - (v * b) mod p)) with (a * x' - a * ((v * b) mod p)) by ring.
      lia. }
    assert (Hdiv2 : (p | x' - (v * b) mod p)).
    { apply Gauss with a; auto. }
    destruct Hdiv2 as [k Hk].
    assert (Hx_range : 0 <= (v * b) mod p < p) by (apply Z_mod_lt; lia).
    destruct (Z.eq_dec k 0) as [->|Hk0].
    + lia.
    + exfalso.
      assert (Z.abs (x' - (v * b) mod p) >= p).
      { rewrite Hk. rewrite Z.abs_mul.
        assert (Z.abs p = p) by lia.
        rewrite H. nia. }
      lia.
Qed.

Close Scope Z_scope.

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

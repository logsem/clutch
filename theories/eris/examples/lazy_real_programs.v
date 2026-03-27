From clutch.prob_lang Require Import lang notation.

(** Programs for lazy real number sampling *)

Definition get_chunk : val :=
  λ: "α" "chnk",
    match: !"chnk" with
    | NONE =>
        let: "b" := rand("α") #1 in
        let: "next" := ref NONEV in
        let: "val" := ("b", "next") in
        "chnk" <- SOME "val";;
        "val"
    | SOME "val" => "val"
    end.

Definition cmpZ : val :=
  λ: "z1" "z2",
    if: "z1" < "z2" then #(-1)
    else
      if: "z2" < "z1" then #1
      else #0.

Definition cmp_list : val :=
  rec: "cmp_list" "α1" "cl1" "α2" "cl2" :=
    let: "c1n" := get_chunk "α1" "cl1" in
    let: "c2n" := get_chunk "α2" "cl2" in
    let: "res" := cmpZ (Fst "c1n") (Fst "c2n") in
    if: "res" = #0 then
      "cmp_list" "α1" (Snd "c1n") "α2" (Snd "c2n")
    else
      "res".

Definition init : val :=
  λ: <>,
    let: "hd" := ref NONEV in
    let: "α" := alloc #1 in
    ("α", "hd").

Definition cmp : val :=
  λ: "lz1" "lz2",
    (* We short-circuit if the two locations are physically equal to avoid forcing sampling *)
    if: Snd "lz1" = Snd "lz2" then
      #0
    else
      cmp_list (Fst "lz1") (Snd "lz1") (Fst "lz2") (Snd "lz2").

Definition get_bit : val :=
  rec: "force" "lazyR" "n" :=
    let: "cn" := get_chunk (Fst "lazyR") (Snd "lazyR") in
    if: ("n" ≤ #0)
      then (Fst "cn")
      else "force" ((Fst "lazyR"), (Snd "cn")) ("n" - #1).

Definition get_bits : val :=
  rec: "force" "lazyR" "digitsLeft" "approxSoFar" :=
    let: "cn" := get_chunk (Fst "lazyR") (Snd "lazyR") in
    if: ("digitsLeft" = #0)
      then "approxSoFar"
      else "force" ((Fst "lazyR"), (Snd "cn")) ("digitsLeft" - #1) (#2 * "approxSoFar" + (Fst "cn")).

(** Computable real arithmetic programs *)

Definition VDiv4Rounded : val :=
  λ: "z", (("z" `quot` #4) + (("z" `rem` #4) `quot` #2)).

Definition R_ofZ : val :=
  λ: "vZ",
    λ: "prec", ("vZ" ≫ "prec").

Definition R_mulPow : val :=
  λ: "f" "vZ",
    λ: "prec", "f" ("vZ" + "prec").

Definition R_plus : val :=
  λ: "f" "g",
    λ: "prec", VDiv4Rounded ("f" ("prec" - #2) + "g" ("prec" - #2)).

Definition R_neg : val :=
  λ: "f",
    λ: "prec", #(- 1) * "f" "prec".

Definition R_ofUnif : val :=
  λ: "v",
    λ: "prec", if: (#0 ≤ "prec") then #0 else  get_bits "v" (#(-1) * "prec") #0.

Definition R_cmp : val :=
  rec: "cmp" "x" "y" "n" :=
    let: "cx" := "x" "n" in
    let: "cy" := "y" "n" in
    if: ("cx" + #2 < "cy") then #(-1) else
    if: ("cy" + #2 < "cx") then #(1) else
    "cmp" "x" "y" ("n" - #1).

Definition ToLazyReal : val :=
  λ: "e",
    let: "U" := R_ofUnif (Snd (Snd "e")) in
    let: "Z" := R_ofZ (Fst (Snd "e")) in
    let: "ZU" := R_plus "U" "Z" in
    if: (Fst "e" = #1) then R_neg "ZU" else "ZU".

Definition lazy_real_cdf_checker (sampler : expr) (B C : Z) : expr :=
  let: "sample" := sampler in
  let: "num" := R_ofZ #B in
  let: "bound" := R_mulPow "num" #C in
  R_cmp "sample" "bound" #0%nat.

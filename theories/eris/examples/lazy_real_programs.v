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

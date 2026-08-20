(**
  The FLDR sampler as a [prob_lang] program.

  Every function here mirrors, one for one, a definition in [model.v], so that
  the refinement proof is a direct correspondence rather than a re-derivation:

    [fldr_weight_sum]   ~ [model.weight_sum]
    [fldr_width]        ~ [model.dyadic_width]
    [fldr_extend]       ~ [model.extended_weights]
    [fldr_one_row]      ~ [model.one_row]
    [fldr_shift]        ~ [model.shift_weights]
    [fldr_rows]         ~ [model.rows_lsb] / [model.ddg_table]
    [fldr_walk]         ~ [walk.walk]
    [fldr_sample]       ~ the rejection loop

  Preprocessing is executable and takes the weight vector as input: no table
  is supplied as a trusted parameter.
*)

From clutch.eris Require Import eris.
From clutch.eris.lib Require Import list.
From clutch.eris.lib.sampling Require Import utils distr_impl.
From clutch.eris.lib.sampling.fldr Require Import model.

#[local] Open Scope R.

Section FldrImpl.

  (** ** Preprocessing *)

  (** Sum of the weight vector. *)
  Definition fldr_weight_sum : val :=
    λ: "ws", list_fold (λ: "acc" "w", "acc" + "w") #0 "ws".

  (** Smallest [k] with [2 ^ k >= m], i.e. [Nat.log2_up m]. *)
  Definition fldr_width : val :=
    rec: "width" "m" "pow" "k" :=
      if: "m" ≤ "pow" then "k" else "width" "m" (#2 * "pow") ("k" + #1).

  (** Extend the weights with the rejection weight [2 ^ k - m]. *)
  (** [2 ^ k]. *)
  Definition fldr_pow2 : val :=
    rec: "pow2" "k" := if: "k" = #0 then #1 else #2 * ("pow2" ("k" - #1)).

  Definition fldr_extend : val :=
    λ: "ws" "den" "m", list_append "ws" (list_cons ("den" - "m") list_nil).

  (** Pair each weight with its label. *)
  Definition fldr_index : val :=
    λ: "ws", list_mapi (λ: "i" "w", ("i", "w")) "ws".

  (** The labels whose current bit is set: one DDG row, LSB first. *)
  Definition fldr_one_row : val :=
    λ: "iws",
      list_map (λ: "iw", Fst "iw")
        (clutch.eris.lib.list.list_filter (λ: "iw", (Snd "iw") `rem` #2 = #1) "iws").

  (** Drop the bit just consumed. *)
  Definition fldr_shift : val :=
    λ: "iws", list_map (λ: "iw", (Fst "iw", (Snd "iw") `quot` #2)) "iws".

  (** [k] rows, least significant bit first. *)
  Definition fldr_rows_lsb : val :=
    rec: "rows" "fuel" "iws" :=
      if: "fuel" = #0 then list_nil else
      list_cons (fldr_one_row "iws") ("rows" ("fuel" - #1) (fldr_shift "iws")).

  (** The DDG table: most significant bit first. *)
  Definition fldr_table : val :=
    λ: "ws",
      let: "m" := fldr_weight_sum "ws" in
      let: "k" := fldr_width "m" #1 #0 in
      let: "den" := fldr_pow2 "k" in
      let: "ext" := fldr_extend "ws" "den" "m" in
      list_rev (fldr_rows_lsb "k" (fldr_index "ext")).

  (** ** The online walk

    One proposal round.  [c] is the DDG counter.  Each step reads one fair bit
    from tape ["α"], sets [c' := 2c + b], returns the leaf [nth c' row] when
    the row holds it, and otherwise carries [c' - |row|] into the next row. *)
  Definition fldr_walk : val :=
    rec: "walk" "α" "rows" "c" :=
      match: "rows" with
        NONE => NONE
      | SOME "p" =>
          let: "row" := Fst "p" in
          let: "rest" := Snd "p" in
          let: "b" := rand("α") #1 in
          let: "c'" := #2 * "c" + "b" in
          let: "h" := list_length "row" in
          if: "c'" < "h"
          then list_nth "row" "c'"
          else "walk" "α" "rest" ("c'" - "h")
      end.

  (** ** The rejection loop

    Labels [0 .. n-1] are accepted; label [n] is the rejection label and
    restarts the round.  An exhausted table also restarts, which cannot happen
    on a full table but keeps the program total. *)
  Definition fldr_loop : val :=
    rec: "loop" "α" "rows" "n" :=
      match: fldr_walk "α" "rows" #0 with
        NONE => "loop" "α" "rows" "n"
      | SOME "i" => if: "i" < "n" then "i" else "loop" "α" "rows" "n"
      end.

  (** ** Top level

    Preprocess the weights, then sample.  The public entry point takes only
    the weight vector.  This mirrors the [if (x->n == 1) return 0;] guard in
    the reference FLDR implementations by Saad, Freer, Rinard and Mansinghka
    (C: [src/c/fldr.c:82], Python: [src/python/fldr.py] in
    [github.com/probcomp/fast-loaded-dice-roller]).  The DDG construction
    writes each extended weight in binary using [dyadic_width ws] bits.  If a
    single weight equals [denominator ws = 2 ^ dyadic_width ws], its expansion
    in that many bits is all zeros, so the table carries no labels at all
    (for example, [ddg_table [1] = []], [ddg_table [2] = [[]]], and
    [ddg_table [4] = [[]; []]]) and the rejection loop never terminates.
    With strictly positive weights and [2 <= length ws], every weight satisfies
    [w_i <= weight_sum ws - (length ws - 1) < weight_sum ws <= denominator ws],
    so the table is well formed; [length ws = 1] is the only remaining case
    and this guard handles it. *)
  Definition fldr_tape : val :=
    λ: "α" "ws",
      let: "n" := list_length "ws" in
      if: "n" = #1 then #0 else
      let: "rows" := fldr_table "ws" in
      fldr_loop "α" "rows" "n".

  Definition fldr : val := λ: "ws", fldr_tape #() "ws".

  Definition fldr_alloc : val := λ: <>, alloc #1.

End FldrImpl.

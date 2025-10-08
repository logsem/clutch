From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt RInt_analysis AutoDerive.
From clutch.eris Require Import infinite_tape.
From clutch.eris.examples Require Import lazy_real.
Set Default Proof Using "Type*".
#[local] Open Scope R.

(* Lazy reals, encompassing both randmized and non-randomized reals.

  Representation:
    refine : val
    expected to behave as Z -> Z

    Given that refine is a function, we allow it to manage any internal caching.
    This implementation then will not cache internal results (additions, etc).

  Combinators
     of_int
     of_unif
     add
     compare gt/lt
     negate
     multiply by integer
     divide by 2

  Probabilities over these things?
    Can't really talk about probabilities in general since that statment
    All the above distributions except of_int make sense to me
    Sadly, no PDF for the dirac measure.
    Probably not too bad to define

    Inductive SymPDF (T : Type) :=
    | det (x : T)
    | pdf (μ : T → R).

    Define a little calulus on these that includes all of the above operations

    is_distributed_as {HasExpectedValue T} : expr → SymPDF T -> iProp Σ
    (is_distributed_as e (det x)) := wp e { x }
    (is_distributed_as e (pdf μ)) := ↯ (E_μ [F]) -∗ wp e { r, ↯ (F r) }

  Alternate (Minimal set of R operations in order to implement Karney's algorithm)
    of_unif
    addZ
    mulZ
    cmp

  In this setting mulZ reduces to addZ!
*)

(* Thanks Approxis (TODO: Move to common?) *)
Definition Zpow : val :=
  rec: "pow" "x" "y" := if: "y" ≤ #0%nat then #(1%nat) else "x" * ("pow" "x" ("y" - #1)).

(* Constant functions at integer Z. *)
Definition R_ofZ : val :=
  λ: "vZ",
    λ: "prec", "vZ" * (Zpow #2 "prec").

(* Given two values that behave as (Z → Z), compare them starting from 0. *)
Definition R_cmp : val :=
  λ: "v1" "v2",
  (rec: "cmp_loop" "prec" :=
     let: "z1" := "v1" "prec" in
     let: "z2" := "v2" "prec" in
     if:      "z1" < "z2" then #(-1)
     else if: "z2" < "z1" then #1
                          else "cmp_loop" ("prec" + #1))
  "cmp_loop" #0.

Definition R_addZ : val :=
  λ: "vR" "vZ",
    λ: "prec", (R_ofZ "vZ" "prec") + ("vR" "prec").

(* TODO *)
Definition R_addR : val :=
  λ: "vR1 vR2" ,
    λ: "prec",
      let: "z1" := "vR1" ("prec" + #1) in
      let: "z2" := "vR2" ("prec" + #1) in
      ("z1" + "z2") ≫ #1.

Definition R_neg : val :=
  λ: "vR",
    λ: "prec",  #(-1) * ("vR" "prec").

Definition Z_sgn : val :=
  λ: "vZ", if: "vZ" < #0 then #(-1) else #1.

Definition Z_abs : val :=
  λ: "vZ", (Z_sgn "vZ") * "vZ".

(* Multiplication by repeated addition *)
Definition R_mulZ_nonneg : val :=
  λ: "vR",
    (rec: "loop_pos" "i" :=
       if: "i" = #0
         then R_ofZ #0
         else R_addR "vR" ("loop_pos" ("i" - #1)))
    "loop_pos".

Definition R_mulZ : val :=
  λ: "vR" "z", (Z_sgn "vZ") * R_mulZ_nonneg "vR" (Z_abs "z").

(* Likely some off-by-ones. *)
Definition R_ofRand : val :=
  (rec: "loop" "α" "chnk" "prec" :=
     if: "prec" = #0
       then
         #0
       else
         let: "V" := get_chunk "α" "chnk" in
         let: "r" := "loop" "α" (Snd "V") ("prec" - #1) in
         (Fst "V") * (Zpow #2 "prec") + "r").


(* Specify that a value behaves like a particular function Z → Z
   Then, specify that it behaves like a real number similarly to lazy_real
      R as Z -> Z functions *)

Context `{!erisGS Σ}.

Definition BehavesAsSequence (v : val) (f : nat → Z) E (I : iProp Σ) : iProp Σ :=
  (∀ (prec : nat), I -∗ WP (v #prec) @ E {{ fun zv => ⌜zv = #(f prec)⌝ ∗ I }})%I.

(* Can I prove this using chunk_and_tape_seq for lazy_real? *)
(* It is the case for I = True and the constatnt real... *)

(* Convert between bitstreams and partial power streams

   Partial power streams are how I implemented the above, because they are way easier
   for aruthmetic operations. The way to convert them is to get the n'th digit of the binary
   expansion.

    PPS to BS doesn't really make sense outside of the interval [0, 1].


    This might be easier to specify using the CReal-like interval spec (which works
    on PPS on any range natively) and then prove that the BitStream representation plus a
    lazy_real predicate satisfies that.  *)
Definition BS_to_PPS (bs : nat → (fin 2)) : nat → Z. Admitted.
Definition PPS_to_BS (ps : nat → Z) : nat → (fin 2). Admitted.

(* TODO: the seq_to_bin_R thing only works *)
Definition BehavesAsLazyReal (v : val) (r : R) E (I : iProp Σ) : iProp Σ :=
  ∃ (z : R) (f : nat → (fin 2)),
    ⌜ r = seq_bin_to_R f ⌝ ∗ □ (BehavesAsSequence v (BS_to_PPS f) E I).

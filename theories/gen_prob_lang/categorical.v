(** A fully general N-weight categorical (bin-weight) [SampleFamily] for the
    generic probabilistic language [gen_prob_lang] (interface in [lang.v]).

    [bin_weight_family]: parameter is a list of [nat] weights [ws : list nat],
    output is the chosen bin index [nat]; bin [i] is chosen with probability
    [ws_i / Σ ws].  The family is TOTAL over all [list nat].

    The mass-1 obligation is discharged for free by building the categorical as
    a [dmap] over a uniform distribution: with [total := list_sum ws] and a
    function mapping [k ∈ [0, total)] onto bin indices so that exactly [ws_i]
    values of [k] land in bin [i], the resulting distribution inherits its mass
    from [dunifP].  The degenerate all-zero / empty case ([total = 0]) gives
    [dunifP 0] (uniform over [fin 1]) mapping everything to bin [0]: still a
    valid distribution, no special-casing needed.

    The 2-bin case [ws = [w1; w2]] reproduces the bin-weight coin (bin [0] is
    chosen with probability [w1 / (w1 + w2)]). *)
From Stdlib Require Import Reals Psatz ZArith.
From stdpp Require Import gmap fin countable list.
From clutch.prob Require Import distribution.
From clutch.gen_prob_lang Require Import lang.
From iris.prelude Require Import options.

#[local] Open Scope R.

(* ------------------------------------------------------------------ *)
(* The bin-index function: maps [k ∈ [0, Σ ws)] onto a bin index.      *)
(* Exactly [ws_i] consecutive values of [k] map to bin [i].            *)
(* ------------------------------------------------------------------ *)
Fixpoint bin_index (ws : list nat) (k : nat) : nat :=
  match ws with
  | [] => 0%nat
  | w :: ws' => if (k <? w)%nat then 0%nat else S (bin_index ws' (k - w))
  end.

(* ------------------------------------------------------------------ *)
(* The categorical distribution as a [dmap] over [dunifP (Σ ws - 1)].   *)
(* ------------------------------------------------------------------ *)
Definition categorical (ws : list nat) : distr nat :=
  dmap (λ k : fin (S (Nat.pred (list_sum ws))), bin_index ws (fin_to_nat k))
       (dunifP (Nat.pred (list_sum ws))).

(* ------------------------------------------------------------------ *)
(* Encoding/decoding of the [list nat] parameter as a right-nested      *)
(* [PairV] chain terminated by [LitV LitUnit].                          *)
(* ------------------------------------------------------------------ *)
Fixpoint encode_ws (ws : list nat) : val :=
  match ws with
  | [] => LitV LitUnit
  | w :: ws' => PairV (LitV (LitInt (Z.of_nat w))) (encode_ws ws')
  end.

Fixpoint decode_ws (v : val) : option (list nat) :=
  match v with
  | LitV LitUnit => Some []
  | PairV (LitV (LitInt w)) rest => (λ l, Z.to_nat w :: l) <$> decode_ws rest
  | _ => None
  end.

Lemma decode_encode_ws (ws : list nat) : decode_ws (encode_ws ws) = Some ws.
Proof.
  induction ws as [|w ws' IH]; simpl; [done|].
  rewrite Nat2Z.id IH. done.
Qed.

(* ------------------------------------------------------------------ *)
(* The bin-weight categorical [SampleFamily].                           *)
(* ------------------------------------------------------------------ *)
Definition bin_weight_family : SampleFamily.
Proof.
  refine {| sf_param := list nat; sf_param_eqdec := _; sf_param_count := _;
            sf_out := nat; sf_out_eqdec := _; sf_out_count := _;
            sf_inj := (λ n, LitV (LitInt (Z.of_nat n))); sf_inj_inj := _;
            sf_param_of_val := decode_ws;
            sf_param_to_val := encode_ws; sf_roundtrip := _;
            sf_sample := categorical;
            sf_mass := _;
            sf_supp := (λ _ _, True);
            sf_supp_spec := _ |}; try exact _.
  - intros ?? [= ?%Nat2Z.inj]. by f_equal.
  - exact decode_encode_ws.
  - intros ws. unfold categorical. rewrite dmap_mass. apply dunifP_mass.
  - by intros ws n _.
Defined.

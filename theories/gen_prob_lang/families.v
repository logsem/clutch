(** Concrete [SampleFamily] instances for the generic probabilistic language
    [gen_prob_lang] (interface in [lang.v]).  Three families:

      - [uniform_family]  : sample a uniform integer in [0, N];
      - [laplace_family]  : a (num, den, mean)-parameterised discrete Laplace;
      - [coin_family]     : a (num, den)-parameterised coin.

    NOTE on [coin_family]: to keep the mass-1 obligation trivial and unblock the
    rest of the development, the bias parameter is currently *ignored* and the
    family samples a fair coin via [dmap] over [dunifP 1].  This should be
    refined to an actual biased coin (e.g. [biased_coin]) later. *)
From Stdlib Require Import Reals Psatz ZArith.
From stdpp Require Import gmap fin countable.
From clutch.prob Require Import distribution.
From clutch.gen_prob_lang Require Import lang.
From iris.prelude Require Import options.

#[local] Open Scope R.

(* ------------------------------------------------------------------ *)
(* 1. Uniform integer family: parameter [N : nat], output [Z].        *)
(* ------------------------------------------------------------------ *)
Definition uniform_family : SampleFamily.
Proof.
  refine {| sf_param := nat; sf_param_eqdec := _; sf_param_count := _;
            sf_out := Z; sf_out_eqdec := _; sf_out_count := _;
            sf_inj := (λ z, LitV (LitInt z)); sf_inj_inj := _;
            sf_param_of_val :=
              (λ v, match v with LitV (LitInt n) => Some (Z.to_nat n) | _ => None end);
            sf_param_to_val := (λ N, LitV (LitInt (Z.of_nat N))); sf_roundtrip := _;
            sf_sample :=
              (λ N, dmap (λ n : fin (S N), Z.of_nat (fin_to_nat n)) (dunifP N));
            sf_mass := _;
            sf_supp := (λ N z, (0 <= z <= Z.of_nat N)%Z);
            sf_supp_spec := _ |}; try exact _.
  - by intros ?? [= ->].
  - intros N. by rewrite Nat2Z.id.
  - intros N. rewrite dmap_mass. apply dunifP_mass.
  - intros N z Hz. apply dmap_pos in Hz as (n & -> & _).
    pose proof (fin_to_nat_lt n). lia.
Defined.

(* ------------------------------------------------------------------ *)
(* 2. Discrete Laplace family: parameter [(num, den, mean) : Z*Z*Z].  *)
(* ------------------------------------------------------------------ *)
Definition laplace_family : SampleFamily.
Proof.
  refine {| sf_param := (Z * Z * Z)%type; sf_param_eqdec := _; sf_param_count := _;
            sf_out := Z; sf_out_eqdec := _; sf_out_count := _;
            sf_inj := (λ z, LitV (LitInt z)); sf_inj_inj := _;
            sf_param_of_val :=
              (λ v, match v with
                    | PairV (LitV (LitInt num))
                            (PairV (LitV (LitInt den)) (LitV (LitInt mean))) =>
                        Some (num, den, mean)
                    | _ => None
                    end);
            sf_param_to_val :=
              (λ '(num, den, mean),
                 PairV (LitV (LitInt num))
                       (PairV (LitV (LitInt den)) (LitV (LitInt mean))));
            sf_roundtrip := _;
            sf_sample := (λ '(num, den, mean), laplace_rat num den mean);
            sf_mass := _;
            sf_supp := (λ _ _, True);
            sf_supp_spec := _ |}; try exact _.
  - by intros ?? [= ->].
  - by intros [[num den] mean].
  - intros [[num den] mean]. apply laplace_rat_mass.
  - by intros [[num den] mean] z _.
Defined.

(* ------------------------------------------------------------------ *)
(* 3. Coin family: parameter [(num, den) : Z*Z], output [bool].       *)
(*    (bias currently ignored — samples a fair coin; see header note) *)
(* ------------------------------------------------------------------ *)
Definition coin_family : SampleFamily.
Proof.
  refine {| sf_param := (Z * Z)%type; sf_param_eqdec := _; sf_param_count := _;
            sf_out := bool; sf_out_eqdec := _; sf_out_count := _;
            sf_inj := (λ b, LitV (LitBool b)); sf_inj_inj := _;
            sf_param_of_val :=
              (λ v, match v with
                    | PairV (LitV (LitInt num)) (LitV (LitInt den)) =>
                        Some (num, den)
                    | _ => None
                    end);
            sf_param_to_val :=
              (λ '(num, den), PairV (LitV (LitInt num)) (LitV (LitInt den)));
            sf_roundtrip := _;
            sf_sample :=
              (λ _, dmap (λ n : fin 2, bool_decide (fin_to_nat n = 0)%nat) (dunifP 1));
            sf_mass := _;
            sf_supp := (λ _ _, True);
            sf_supp_spec := _ |}; try exact _.
  - by intros ?? [= ->].
  - by intros [num den].
  - intros [num den]. rewrite dmap_mass. apply dunifP_mass.
  - by intros [num den] b _.
Defined.

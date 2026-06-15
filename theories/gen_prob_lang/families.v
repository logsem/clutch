(** Concrete [SampleFamily] instances for the generic probabilistic language
    [gen_prob_lang] (interface in [lang.v]).  Four families:

      - [uniform_family]  : sample a uniform integer in [0, N];
      - [laplace_family]  : a (num, den, mean)-parameterised discrete Laplace;
      - [coin_family]     : a (w1, w2)-bin-weight coin (P(true) = w2/(w1+w2));
      - [RR_coin]         : a (num, den)-parameterised randomised-response coin
                            with bias exp(ε)/(exp(ε)+1) for ε = num/den. *)
From Stdlib Require Import Reals Psatz ZArith.
From stdpp Require Import gmap fin countable.
From clutch.prob Require Import distribution exponential expmech trunc_laplace.
From clutch.gen_prob_lang Require Import lang znoise inject.
From clutch.gen_prob_lang.typing Require Import types.
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
Definition laplace_family : SampleFamily := mkZNoise laplace_rat laplace_rat_mass.

(** One-sided exponential noise family — same [(num,den,mean)] interface and
    [Z] outcomes as [laplace_family], but sampling the one-sided exponential
    ([exp_rat]) instead of the Laplace.  This is the new noise distribution for
    the exponential-mechanism report-noisy-max; adding it costs exactly this one
    [SampleFamily] (the payoff of the generalization). *)
Definition exp_family : SampleFamily := mkZNoise exp_rat exp_rat_mass.

(** TRUNCATED discrete Laplace family — sampling the bounded-support truncated
    discrete Laplace [trunc_lap_rat A] (see [prob/trunc_laplace.v]).  Unlike a
    [mkZNoise] family, the truncation half-width [A] is a genuine RUNTIME sample
    parameter (the FOURTH [Z] alongside [num]/[den]/[loc]), chosen at sample time
    rather than being a Coq-level family index — hence the family is built with
    [mkZNoise4] over the parameter [(A, num, den, loc) : Z*Z*Z*Z].

    The mass obligation of [mkZNoise4] is TOTAL: [SeriesC = 1] must hold for ALL
    parameters, but [trunc_lap_rat_mass] needs [0 <= A].  We clamp the half-width
    to [Z.max 0 A], which is always [>= 0] (so [trunc_lap_rat_mass] applies via
    [Z.le_max_l]); at any runtime [A >= 0] the clamp is the identity
    ([Z.max 0 A = A]), so the family's sample IS [trunc_lap_rat A …].  This is the
    noise distribution whose per-distance coupling is the EXACT group-bound
    [(s·ε, δ₁·grp ε s)] profile, validating the metric approximate-DP definition. *)
Definition trunc_laplace_family : SampleFamily :=
  mkZNoise4 (fun A num den loc => trunc_lap_rat (Z.max 0 A) num den loc)
            (fun A num den loc =>
               trunc_lap_rat_mass (Z.max 0 A) num den loc (Z.le_max_l 0 A)).

(* ------------------------------------------------------------------ *)
(* 2b. Discrete exponential-mechanism family: parameter                *)
(*     [(num, den, scores) : Z*Z*list Z], output [Z] (the chosen       *)
(*     index).  Samples index [i ∝ exp((num/den)·scoreᵢ)] via [expmech].*)
(*                                                                     *)
(*     Unlike the noise families, the parameter carries a *list* of    *)
(*     scores, so the [val] (de)serialisation goes through the         *)
(*     [Inject_list] instance: [sf_param_to_val] uses [inject] to       *)
(*     encode [scores], and [val_to_listZ] is the matching inverse      *)
(*     parser for the cons-cell representation                          *)
(*     ([InjLV #()] for [], [InjRV (#x, rest)] for [x :: rest]).        *)
(* ------------------------------------------------------------------ *)

(** Inverse of [inject : list Z → val] (the [Inject_list] instance),
    matching its cons-cell representation: [[] ↦ InjLV #()] and
    [x :: xs ↦ InjRV (#x, ⟨xs⟩)].  Total ([None] off the image). *)
Fixpoint val_to_listZ (v : val) : option (list Z) :=
  match v with
  | InjLV (LitV LitUnit) => Some []
  | InjRV (PairV (LitV (LitInt x)) rest) =>
      (λ xs, x :: xs) <$> val_to_listZ rest
  | _ => None
  end.

(** [val_to_listZ] inverts [inject] on every score vector. *)
Lemma val_to_listZ_inject (scores : list Z) :
  val_to_listZ (inject scores) = Some scores.
Proof.
  induction scores as [|x xs IH]; simpl; [reflexivity|]. rewrite IH. reflexivity.
Qed.

Definition expmech_family : SampleFamily.
Proof.
  refine {| sf_param := (Z * Z * list Z)%type;
            sf_param_eqdec := _; sf_param_count := _;
            sf_out := Z; sf_out_eqdec := _; sf_out_count := _;
            sf_inj := (λ z, LitV (LitInt z)); sf_inj_inj := _;
            sf_param_of_val :=
              (λ v, match v with
                    | PairV (LitV (LitInt num)) (PairV (LitV (LitInt den)) lv) =>
                        (λ scores, (num, den, scores)) <$> val_to_listZ lv
                    | _ => None
                    end);
            sf_param_to_val :=
              (λ '(num, den, scores),
                 PairV (LitV (LitInt num))
                       (PairV (LitV (LitInt den)) (inject scores)));
            sf_roundtrip := _;
            sf_sample := (λ '(num, den, scores), expmech num den scores);
            sf_mass := _;
            sf_supp := (λ _ _, True);
            sf_supp_spec := _ |}; try exact _.
  - by intros ?? [= ->].
  - intros [[num den] scores]. rewrite val_to_listZ_inject. reflexivity.
  - intros [[num den] scores]. apply expmech_mass.
  - by intros [[num den] scores] z _.
Defined.

(* ------------------------------------------------------------------ *)
(* Helper lemmas for the coin families.                                *)
(* ------------------------------------------------------------------ *)

(** Bin-weight bias [w2 / (w1 + w2)] is always a valid probability.
    When [w1 = w2 = 0] this is [0 / 0 = 0], still in [0, 1]. *)
Lemma weight_coin_valid (w1 w2 : nat) : (0 <= INR w2 / INR (w1 + w2) <= 1)%R.
Proof.
  destruct (Nat.eq_dec (w1 + w2) 0)%nat as [Hz | Hnz].
  - assert (w1 = 0 /\ w2 = 0)%nat as [-> ->] by lia. simpl.
    unfold Rdiv. rewrite Rmult_0_l. lra.
  - assert (0 < INR (w1 + w2))%R as Hpos by (apply lt_0_INR; lia).
    split.
    + apply Rcomplements.Rdiv_le_0_compat; [apply pos_INR | lra].
    + apply (Rcomplements.Rdiv_le_1 (INR w2) (INR (w1 + w2)) Hpos).
      rewrite plus_INR. pose proof (pos_INR w1). lra.
Qed.

(** Randomised-response bias [exp(ε) / (exp(ε) + 1)] is always a valid
    probability, for any rational [ε = num / den]. *)
Lemma rr_bias_valid (num den : Z) :
  (0 <= exp (IZR num / IZR den) / (exp (IZR num / IZR den) + 1) <= 1)%R.
Proof.
  set (e := exp (IZR num / IZR den)).
  pose proof (exp_pos (IZR num / IZR den)) as He. fold e in He.
  split.
  - apply Rcomplements.Rdiv_le_0_compat; lra.
  - apply (Rcomplements.Rdiv_le_1 e (e + 1)); lra.
Qed.

(** [biased_coin] is a probability distribution (total mass 1). *)
Lemma biased_coin_mass r (P : (0 <= r <= 1)%R) :
  SeriesC (biased_coin r P) = 1.
Proof.
  rewrite SeriesC_bool /pmf /= /biased_coin_pmf. lra.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. Bin-weight coin family: parameter [(w1, w2) : nat*nat],          *)
(*    output [bool], with P(true) = w2 / (w1 + w2).                    *)
(* ------------------------------------------------------------------ *)
Definition coin_family : SampleFamily.
Proof.
  refine {| sf_param := (nat * nat)%type; sf_param_eqdec := _; sf_param_count := _;
            sf_out := bool; sf_out_eqdec := _; sf_out_count := _;
            sf_inj := (λ b, LitV (LitBool b)); sf_inj_inj := _;
            sf_param_of_val :=
              (λ v, match v with
                    | PairV (LitV (LitInt w1)) (LitV (LitInt w2)) =>
                        Some (Z.to_nat w1, Z.to_nat w2)
                    | _ => None
                    end);
            sf_param_to_val :=
              (λ '(w1, w2),
                 PairV (LitV (LitInt (Z.of_nat w1))) (LitV (LitInt (Z.of_nat w2))));
            sf_roundtrip := _;
            sf_sample :=
              (λ '(w1, w2),
                 biased_coin (INR w2 / INR (w1 + w2)) (weight_coin_valid w1 w2));
            sf_mass := _;
            sf_supp := (λ _ _, True);
            sf_supp_spec := _ |}; try exact _.
  - by intros ?? [= ->].
  - intros [w1 w2]. by rewrite !Nat2Z.id.
  - intros [w1 w2]. apply biased_coin_mass.
  - by intros [w1 w2] b _.
Defined.

(* ------------------------------------------------------------------ *)
(* 4. Randomised-response coin family: parameter [(num, den) : Z*Z],   *)
(*    output [bool], with P(true) = exp(ε)/(exp(ε)+1), ε = num/den.    *)
(*                                                                     *)
(*    [RR_coin] is the noisy-bit *source*; the (num/den)-DP guarantee  *)
(*    is proved later at the example level over [coin ⊕ b] (i.e. a     *)
(*    plain-coin sample combined with an in-program XOR design).       *)
(* ------------------------------------------------------------------ *)
Definition RR_coin : SampleFamily.
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
              (λ '(num, den),
                 biased_coin
                   (exp (IZR num / IZR den) / (exp (IZR num / IZR den) + 1))
                   (rr_bias_valid num den));
            sf_mass := _;
            sf_supp := (λ _ _, True);
            sf_supp_spec := _ |}; try exact _.
  - by intros ?? [= ->].
  - by intros [num den].
  - intros [num den]. apply biased_coin_mass.
  - by intros [num den] b _.
Defined.

(* ------------------------------------------------------------------ *)
(* Resolving [SampleIn D S] instances.                                 *)
(* ------------------------------------------------------------------ *)

(** Resolution mode: [SampleIn D S] is resolved by the NAMED family [D] (which
    must be known), recovering the signature [S] as output.  This lets surface
    notations like [Laplace] — whose [Sample] index is [sample_idx (D := D)] in a
    signature-independent [expr] — recover [S] (hence the concrete index) from
    the unique [SampleIn D _] instance of the ambient development, with no [S]
    annotation at the use site. *)
#[global] Hint Mode SampleIn ! - : typeclass_instances.

(** [solve_SampleIn] discharges a goal [SampleIn D S] for a concrete signature
    [S] by searching for the index at which the named family [D] occurs (up to a
    small bound).  Use as [#[global] Instance : SampleIn D S := ltac:(solve_SampleIn).] *)
Ltac solve_SampleIn :=
  first
    [ refine {| sample_idx := 0 |}; reflexivity
    | refine {| sample_idx := 1 |}; reflexivity
    | refine {| sample_idx := 2 |}; reflexivity
    | refine {| sample_idx := 3 |}; reflexivity
    | refine {| sample_idx := 4 |}; reflexivity
    | refine {| sample_idx := 5 |}; reflexivity
    | refine {| sample_idx := 6 |}; reflexivity
    | refine {| sample_idx := 7 |}; reflexivity
    | fail "solve_SampleIn: family not found in signature within index bound 7" ].

(* ------------------------------------------------------------------ *)
(* Typing rules: each family brings its own [SampleTyping] instance.    *)
(* Providing the instance (and having the family in the signature) is   *)
(* exactly what enables the [Sample]/[AllocSampleTape] typing rules for *)
(* it — see [typed]/[fundamental] in the logical relation.              *)
(* ------------------------------------------------------------------ *)

(** Uniform: [TNat → TInt]. *)
#[global] Instance SampleTyping_uniform : SampleTyping uniform_family TNat TInt.
Proof.
  split.
  - constructor.
  - intros v [n ->]. eexists. reflexivity.
  - intros o. exists o. reflexivity.
Qed.

(** Every [mkZNoise] noise family reads a [(num, den, mean)] triple of type
    [TInt * (TInt * TInt)] and outputs an integer. *)
Lemma SampleTyping_mkZNoise sample mass :
  SampleTyping (mkZNoise sample mass) (TInt * (TInt * TInt)) TInt.
Proof.
  split.
  - repeat constructor.
  - intros v (v1 & v2 & -> & [num ->] & (v3 & v4 & -> & [den ->] & [mean ->])).
    eexists. reflexivity.
  - intros o. exists o. reflexivity.
Qed.

#[global] Instance SampleTyping_laplace :
  SampleTyping laplace_family (TInt * (TInt * TInt)) TInt := SampleTyping_mkZNoise _ _.
#[global] Instance SampleTyping_exp :
  SampleTyping exp_family (TInt * (TInt * TInt)) TInt := SampleTyping_mkZNoise _ _.

(** The truncated Laplace reads a fourth [Z] (the half-width), of type
    [TInt * (TInt * (TInt * TInt))]. *)
Lemma SampleTyping_mkZNoise4 sample mass :
  SampleTyping (mkZNoise4 sample mass) (TInt * (TInt * (TInt * TInt))) TInt.
Proof.
  split.
  - repeat constructor.
  - intros v (v1 & v2 & -> & [a ->] & (v3 & v4 & -> & [b ->] & (v5 & v6 & -> & [c ->] & [d ->]))).
    eexists. reflexivity.
  - intros o. exists o. reflexivity.
Qed.

#[global] Instance SampleTyping_trunc_laplace :
  SampleTyping trunc_laplace_family (TInt * (TInt * (TInt * TInt))) TInt
  := SampleTyping_mkZNoise4 _ _.

(** Coins output a boolean from a pair of integer weights: [TInt*TInt → TBool]. *)
#[global] Instance SampleTyping_coin : SampleTyping coin_family (TInt * TInt) TBool.
Proof.
  split.
  - repeat constructor.
  - intros v (v1 & v2 & -> & [a ->] & [b ->]). eexists. reflexivity.
  - intros o. exists o. reflexivity.
Qed.

#[global] Instance SampleTyping_RR_coin : SampleTyping RR_coin (TInt * TInt) TBool.
Proof.
  split.
  - repeat constructor.
  - intros v (v1 & v2 & -> & [a ->] & [b ->]). eexists. reflexivity.
  - intros o. exists o. reflexivity.
Qed.

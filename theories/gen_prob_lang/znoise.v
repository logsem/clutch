(** [mkZNoise]: a smart constructor for the "Z-noise" [SampleFamily]s used by the
    differential-privacy mechanisms (discrete Laplace, one-sided exponential,
    Gumbel, …).  They ALL share the same interface — parameter
    [(num, den, mean) : Z*Z*Z], outcome [Z], injection [LitV ∘ LitInt], the
    standard [(num,den,mean) ↔ PairV] value encoding, and full support — and
    differ ONLY in the sampler [sample : Z → Z → Z → distr Z].

    Defining each family through [mkZNoise] makes [sf_out (mkZNoise …) = Z] and the
    other projections hold DEFINITIONALLY.  That is what lets a single generic
    report-noisy-max development (whose argmax uses [list_Z_max] over the [Z]
    outcomes) be written over an abstract [mkZNoise sample mass] and instantiated
    per noise distribution — with NO [sf_out = Z] transport. *)
From Stdlib Require Import Reals.
From stdpp Require Import gmap fin countable.
From clutch.prob Require Import distribution.
From clutch.gen_prob_lang Require Import lang.
From iris.prelude Require Import options.

Definition mkZNoise (sample : Z → Z → Z → distr Z)
    (mass : ∀ num den mean, (SeriesC (sample num den mean) = 1)%R) : SampleFamily.
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
            sf_sample := (λ '(num, den, mean), sample num den mean);
            sf_mass := _;
            sf_supp := (λ _ _, True);
            sf_supp_spec := _ |}; try exact _.
  - by intros ?? [= ->].
  - by intros [[num den] mean].
  - intros [[num den] mean]. apply mass.
  - by intros [[num den] mean] z _.
Defined.

(** The defining projections reduce definitionally — this is the whole point. *)
Lemma mkZNoise_out sample mass : sf_out (mkZNoise sample mass) = Z.
Proof. reflexivity. Qed.

Lemma mkZNoise_inj sample mass (z : Z) :
  sf_inj (mkZNoise sample mass) z = LitV (LitInt z).
Proof. reflexivity. Qed.

Lemma mkZNoise_param_to_val sample mass (num den mean : Z) :
  sf_param_to_val (mkZNoise sample mass) (num, den, mean)
  = PairV (LitV (LitInt num)) (PairV (LitV (LitInt den)) (LitV (LitInt mean))).
Proof. reflexivity. Qed.

Lemma mkZNoise_sample sample mass (num den mean : Z) :
  sf_sample (mkZNoise sample mass) (num, den, mean) = sample num den mean.
Proof. reflexivity. Qed.

(** [mkZNoise4]: the same smart constructor ONE SAMPLE PARAMETER WIDER.  The
    parameter is [(a, b, c, d) : Z*Z*Z*Z], encoded as the nested value
    [PairV #a (PairV #b (PairV #c #d))]; everything else (outcome [Z], injection
    [LitV ∘ LitInt], full support, definitional projections) mirrors [mkZNoise]
    exactly.  This lets a noise family carry a fourth RUNTIME [Z] parameter — e.g.
    the truncated discrete Laplace's truncation half-width [A] (see
    [families.v.trunc_laplace_family]) — chosen at sample time rather than being a
    Coq-level family index. *)
Definition mkZNoise4 (sample : Z → Z → Z → Z → distr Z)
    (mass : ∀ a b c d, (SeriesC (sample a b c d) = 1)%R) : SampleFamily.
Proof.
  refine {| sf_param := (Z * Z * Z * Z)%type; sf_param_eqdec := _; sf_param_count := _;
            sf_out := Z; sf_out_eqdec := _; sf_out_count := _;
            sf_inj := (λ z, LitV (LitInt z)); sf_inj_inj := _;
            sf_param_of_val :=
              (λ v, match v with
                    | PairV (LitV (LitInt a))
                            (PairV (LitV (LitInt b))
                                   (PairV (LitV (LitInt c)) (LitV (LitInt d)))) =>
                        Some (a, b, c, d)
                    | _ => None
                    end);
            sf_param_to_val :=
              (λ '(a, b, c, d),
                 PairV (LitV (LitInt a))
                       (PairV (LitV (LitInt b))
                              (PairV (LitV (LitInt c)) (LitV (LitInt d)))));
            sf_roundtrip := _;
            sf_sample := (λ '(a, b, c, d), sample a b c d);
            sf_mass := _;
            sf_supp := (λ _ _, True);
            sf_supp_spec := _ |}; try exact _.
  - by intros ?? [= ->].
  - by intros [[[a b] c] d].
  - intros [[[a b] c] d]. apply mass.
  - by intros [[[a b] c] d] z _.
Defined.

(** The defining projections of [mkZNoise4] reduce definitionally too. *)
Lemma mkZNoise4_out sample mass : sf_out (mkZNoise4 sample mass) = Z.
Proof. reflexivity. Qed.

Lemma mkZNoise4_inj sample mass (z : Z) :
  sf_inj (mkZNoise4 sample mass) z = LitV (LitInt z).
Proof. reflexivity. Qed.

Lemma mkZNoise4_param_to_val sample mass (a b c d : Z) :
  sf_param_to_val (mkZNoise4 sample mass) (a, b, c, d)
  = PairV (LitV (LitInt a))
          (PairV (LitV (LitInt b)) (PairV (LitV (LitInt c)) (LitV (LitInt d)))).
Proof. reflexivity. Qed.

Lemma mkZNoise4_sample sample mass (a b c d : Z) :
  sf_sample (mkZNoise4 sample mass) (a, b, c, d) = sample a b c d.
Proof. reflexivity. Qed.
